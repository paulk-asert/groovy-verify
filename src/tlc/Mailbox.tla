SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in
compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
(Text before the MODULE banner is ignored by the TLA+ parser.)

---------------------------- MODULE Mailbox ----------------------------
\* Phase 289's ACTOR MAILBOX KNOT as a TLA+ state machine, and it is at this rung deliberately.
\*
\* Fray was tried first and was the wrong tool, which is what makes the pairing here worth stating. The
\* property is "a sender blocked on a full mailbox is eventually released, because the handler drains it" --
\* a LIVENESS property under a fair scheduler, not deadlock-freedom. A controlled scheduler exploring
\* adversarial interleavings can simply never run the handler, and that is starvation, not deadlock. TLA+
\* says exactly this with `WF_vars`, so the question can be posed properly instead of approximated.
\*
\* Mapping to `knot()` / `fedFirst()`:
\*   box      messages queued in the bounded mailbox      (withBoundedMailbox(Cap, Overflow.BLOCK))
\*   busy     the handler holds a message and is blocked on the gate   (the handler's gate.first())
\*   gate     items buffered in the channel the handler reads          (AsyncChannel gate)
\*   sent[s]  how many messages sender s has got away     (worker.send(..) -- BLOCKS when box is full)
\*   fed      how many values have been put on the gate   (gate.send(0))
\*   FeedFirst  TRUE = feed the handler before the burst (the repair); FALSE = the knot
\*
\* `Senders` is a SET, so the same spec answers the question Phase 300 withholds at rung 1: with more than
\* one method sending to the same actor, this method's burst is no longer the whole count, so the checker
\* declines to claim. Here the siblings really do interleave, exhaustively.

EXTENDS Naturals

CONSTANTS Senders,      \* the set of independent sending processes
          Burst,        \* messages each sender sends
          Cap,          \* mailbox bound; a send blocks while box = Cap
          Feeds,        \* values placed on the gate (one per message, or the handler cannot finish)
          FeedFirst     \* is the gate fed before the burst?
ASSUME Cap \in (Nat \ {0})
ASSUME FeedFirst \in BOOLEAN

VARIABLES sent, fed, box, busy, gate
vars == <<sent, fed, box, busy, gate>>

Init == /\ sent = [s \in Senders |-> 0]
        /\ fed = 0 /\ box = 0 /\ busy = FALSE /\ gate = 0

AllSent == \A s \in Senders : sent[s] = Burst

----------------------------------------------------------------------------
\* A send is enabled only while the mailbox has room -- this IS Overflow.BLOCK, and the only send in
\* groovy.concurrent besides a rendezvous channel that blocks its sender.
Send(s) == /\ sent[s] < Burst
           /\ box < Cap
           /\ (FeedFirst => fed = Feeds)          \* the repair: nothing is sent until the gate is fed
           /\ box' = box + 1
           /\ sent' = [sent EXCEPT ![s] = @ + 1]
           /\ UNCHANGED <<fed, busy, gate>>

Feed == /\ fed < Feeds
        /\ (~FeedFirst => AllSent)                \* the knot: the gate is fed only after the whole burst
        /\ gate' = gate + 1 /\ fed' = fed + 1
        /\ UNCHANGED <<sent, box, busy>>

\* The handler takes one message out of the box and is then blocked on the gate -- so one message is in
\* flight ON TOP of the Cap the box holds, which is why the (Cap+2)-th send is the one that waits.
Take == /\ ~busy /\ box > 0
        /\ box' = box - 1 /\ busy' = TRUE
        /\ UNCHANGED <<sent, fed, gate>>

Read == /\ busy /\ gate > 0
        /\ gate' = gate - 1 /\ busy' = FALSE
        /\ UNCHANGED <<sent, fed, box>>

Done        == AllSent /\ fed = Feeds /\ box = 0 /\ ~busy
Terminating == Done /\ UNCHANGED vars       \* finishing is not a stuck state

Next     == (\E s \in Senders : Send(s)) \/ Feed \/ Take \/ Read \/ Terminating
Fairness == /\ \A s \in Senders : WF_vars(Send(s))
            /\ WF_vars(Feed) /\ WF_vars(Take) /\ WF_vars(Read)
Spec     == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
TypeOK == /\ sent \in [Senders -> 0 .. Burst]
          /\ fed \in 0 .. Feeds
          /\ box \in 0 .. Cap
          /\ busy \in BOOLEAN
          /\ gate \in 0 .. Feeds

\* SAFETY -- the bound is never exceeded, however many senders interleave. This is the half Phase 300
\* declines to claim at rung 1 once more than one method can send to the actor.
Bounds == box <= Cap

\* LIVENESS -- the property Fray could not pose. Under weak fairness every message is eventually taken
\* and handled, so every blocked sender is eventually released and the network finishes.
Progress == <>Done
=============================================================================
