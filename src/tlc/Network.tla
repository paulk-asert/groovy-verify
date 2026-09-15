SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in
compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
(Text before the MODULE banner is ignored by the TLA+ parser.)

---------------------------- MODULE Network ----------------------------
\* The Kerridge gallery's DEADLOCK EXERCISE as a TLA+ state machine: two processes joined by two
\* channels, each reading from the other before it writes.
\*
\* Rung 1 refutes this at COMPILE time, and does so STRUCTURALLY -- it builds the wait-for order and
\* shows it is not well-founded, naming the cycle. That is a different argument from "no interleaving
\* reaches a stuck state", so TLC here is a genuinely independent oracle rather than the same argument
\* run again: it enumerates every interleaving and looks for a state with no successor.
\*
\* The second half is the one the sequential checker cannot state at all. Phase 255 certifies liveness
\* *under weak fairness* -- an assumption written in prose there, and `WF_vars` here, which is TLA+'s
\* own vocabulary for it. So the fairness assumption rung 1 makes is checked, not just declared.
\*
\* Mapping to `deadlockExercise()` / its primed repair:
\*   aToB, bToA    the two AsyncChannels, modelled by OCCUPANCY (content is irrelevant to blocking)
\*   pcA, pcB      each process's position in its own two-step program
\*   Primed        TRUE  = process A sends before it reads (the repair the books teach)
\*                 FALSE = both processes read first        (the student mistake)

EXTENDS Naturals

CONSTANTS Cap,          \* channel capacity: a send blocks when the channel holds Cap items
          Primed        \* does A prime the cycle with a send before it reads?
ASSUME Cap \in (Nat \ {0})
ASSUME Primed \in BOOLEAN

VARIABLES pcA,          \* "s1" -> "s2" -> "done"
          pcB,
          aToB,         \* items buffered in the A->B channel
          bToA          \* items buffered in the B->A channel

vars == <<pcA, pcB, aToB, bToA>>

Init == /\ pcA = "s1" /\ pcB = "s1"
        /\ aToB = 0    /\ bToA = 0

----------------------------------------------------------------------------
\* Process A, in both spellings. A send is enabled while the channel has room; a receive is enabled
\* only once the channel holds something -- which is the whole of what makes the cycle possible.

ASendFirst  == /\ Primed  /\ pcA = "s1" /\ aToB < Cap
               /\ aToB' = aToB + 1 /\ pcA' = "s2" /\ UNCHANGED <<bToA, pcB>>
AReadSecond == /\ Primed  /\ pcA = "s2" /\ bToA > 0
               /\ bToA' = bToA - 1 /\ pcA' = "done" /\ UNCHANGED <<aToB, pcB>>

AReadFirst  == /\ ~Primed /\ pcA = "s1" /\ bToA > 0
               /\ bToA' = bToA - 1 /\ pcA' = "s2" /\ UNCHANGED <<aToB, pcB>>
ASendSecond == /\ ~Primed /\ pcA = "s2" /\ aToB < Cap
               /\ aToB' = aToB + 1 /\ pcA' = "done" /\ UNCHANGED <<bToA, pcB>>

AStep == ASendFirst \/ AReadSecond \/ AReadFirst \/ ASendSecond

\* Process B always reads before it writes -- it is A alone that the repair changes.
BRead == /\ pcB = "s1" /\ aToB > 0
         /\ aToB' = aToB - 1 /\ pcB' = "s2" /\ UNCHANGED <<bToA, pcA>>
BSend == /\ pcB = "s2" /\ bToA < Cap
         /\ bToA' = bToA + 1 /\ pcB' = "done" /\ UNCHANGED <<aToB, pcA>>

BStep == BRead \/ BSend

\* Both finished: stutter, so that ordinary TERMINATION is not itself reported as a stuck state.
\* Only a state where a process still has work to do but nothing is enabled is a deadlock.
Terminating == /\ pcA = "done" /\ pcB = "done" /\ UNCHANGED vars

Next     == AStep \/ BStep \/ Terminating
Fairness == WF_vars(AStep) /\ WF_vars(BStep)
Spec     == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
TypeOK == /\ pcA \in {"s1", "s2", "done"}
          /\ pcB \in {"s1", "s2", "done"}
          /\ aToB \in 0 .. Cap
          /\ bToA \in 0 .. Cap

\* SAFETY -- no channel ever holds more than its capacity: the bound a blocking send enforces.
Bounds == (aToB <= Cap) /\ (bToA <= Cap)

\* LIVENESS -- under weak fairness, both processes finish. This is Phase 255's assumption stated in
\* the tool's own vocabulary: rung 1 assumes a process whose next operation is enabled eventually
\* takes it, and WF_vars is exactly that assumption.
Progress == <>(pcA = "done" /\ pcB = "done")
=============================================================================
