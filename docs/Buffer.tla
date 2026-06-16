SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in
compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
(Text before the MODULE banner is ignored by the TLA+ parser.)

---------------------------- MODULE Buffer ----------------------------
\* The producer/consumer buffer from README's §VII capstone, as a TLA+ state machine.
\*
\* This is "the other half" that the groovy-verify checker deliberately does NOT do.
\* The checker proves the LOCAL, sequential obligations of a rely/guarantee argument:
\* each thread, run under an ASSUMED rely, stays in bounds and leaks nothing. Here we
\* drop the assumption and let TLC explore EVERY interleaving of the two threads, so the
\* rely stops being an assumption and becomes a theorem about the peer's action (see
\* RelyProd / RelyCons below).
\*
\* Mapping to `class Buffer`:
\*   head, tail        the shared read/write pointers (the @Invariant's variables)
\*   data[i]           the payload stored in slot i           (values[i])
\*   dlvl[i]           slot i's TRUE data secrecy: High = a raw secret, Low = declassified
\*   PosLabel(i)       the value-dependent positional label   (level(i, head, tail))
\*   leaked            set once a High datum reaches the public sink (deliver)
\*
\* The data secrecy `dlvl` is what `Declassify.to('Low', secret)` flips Low; the positional
\* label is the *promise* `level` makes. RegionSound ties them: every slot the label calls
\* Low really holds Low data. That is exactly the array secure-update invariant the checker
\* discharges at `tail = tail + 1`.

EXTENDS Naturals, Sequences

CONSTANTS Cap,          \* capacity: slots are indexed 0 .. Cap-1
          Data          \* set of payload values (content is irrelevant to safety; keep it small)
ASSUME Cap \in (Nat \ {0})

Idx      == 0 .. Cap - 1
Lvls     == {"Low", "High"}
Leq(a, b) == (a = "Low") \/ (b = "High")     \* the lattice order == our leq()

VARIABLES head,         \* consumer read pointer   (shared)
          tail,         \* producer write pointer   (shared)
          data,         \* [Idx -> Data]  the stored payloads
          dlvl,         \* [Idx -> Lvls]  each slot's true data secrecy
          leaked        \* BOOLEAN  has the public sink ever observed a High datum?

vars == <<head, tail, data, dlvl, leaked>>

\* The positional label, derived (not stored): level(i, head, tail) = (head <= i < tail) ? Low : High
PosLabel(i) == IF (head <= i) /\ (i < tail) THEN "Low" ELSE "High"

Init ==
  /\ head = 0
  /\ tail = 0
  /\ data = [i \in Idx |-> CHOOSE d \in Data : TRUE]
  /\ dlvl = [i \in Idx |-> "High"]      \* slots start un-declassified
  /\ leaked = FALSE

\* PRODUCER  -- @Requires(tail < Cap), @UnderRely('Producer'): declassify, write, advance tail.
\* Touches neither head nor the sink -> this action IS the consumer's rely (rCons / gProd).
Produce(secret) ==
  /\ tail < Cap
  /\ data'  = [data EXCEPT ![tail] = secret]
  /\ dlvl'  = [dlvl EXCEPT ![tail] = "Low"]      \* Declassify.to('Low', secret): the slot's data becomes Low
  /\ tail'  = tail + 1                            \* old.tail now ENTERS the Low region
  /\ UNCHANGED <<head, leaked>>

\* The LEAK variant: skip the declassification, expose a raw secret. Flipping Produce -> ProduceLeak
\* (via BuggySpec) makes TLC exhibit the leak as an actual interleaved trace -- the same refutation
\* the checker gives at `tail++`, here played out step by step.
ProduceLeak(secret) ==
  /\ tail < Cap
  /\ data'  = [data EXCEPT ![tail] = secret]
  /\ dlvl'  = [dlvl EXCEPT ![tail] = "High"]     \* NO declassify
  /\ tail'  = tail + 1
  /\ UNCHANGED <<head, leaked>>

\* CONSUMER  -- @Requires(head < tail), @UnderRely('Consumer'): read values[head], deliver it, advance head.
\* Touches neither tail nor the slots -> this action IS the producer's rely (rProd / gCons).
Consume ==
  /\ head < tail
  /\ leaked' = (leaked \/ (dlvl[head] = "High"))  \* deliver(values[head]) into the public (Low) sink
  /\ head'   = head + 1
  /\ UNCHANGED <<tail, data, dlvl>>

\* This is a one-shot (non-wrapping) buffer: once all Cap slots are produced and consumed it is
\* finished. `Done` is the conventional terminating-spec self-loop -- it lets the final state stutter
\* so TLC does not report the graceful end as a deadlock.
Done == (head = Cap) /\ (tail = Cap) /\ UNCHANGED vars

Next      == (\E s \in Data : Produce(s))     \/ Consume \/ Done
NextBuggy == (\E s \in Data : ProduceLeak(s)) \/ Consume \/ Done

Fairness  == WF_vars(Consume) /\ WF_vars(\E s \in Data : Produce(s))

Spec      == Init /\ [][Next]_vars      /\ Fairness
BuggySpec == Init /\ [][NextBuggy]_vars /\ Fairness

----------------------------------------------------------------------------
\* SAFETY -- the two obligations the checker proves, here as TLC invariants.

TypeOK ==
  /\ head \in 0 .. Cap
  /\ tail \in 0 .. Cap
  /\ data \in [Idx -> Data]
  /\ dlvl \in [Idx -> Lvls]
  /\ leaked \in BOOLEAN

Bounds      == (0 <= head) /\ (head <= tail) /\ (tail <= Cap)   \* the bounded-buffer @Invariant
RegionSound == \A i \in head .. (tail - 1) : dlvl[i] = "Low"    \* every Low-region slot really holds Low data
NoLeak      == leaked = FALSE                                   \* the public sink never saw a secret

----------------------------------------------------------------------------
\* THE CRUX -- the rely is not assumed here; it is a checked property of the PEER's action.
\* In the checker, produce() is verified *assuming* rProd (the consumer keeps tail). TLC instead
\* enumerates all interleavings and confirms the consumer's action really does keep tail fixed:

RelyProd == [][ Consume => (tail' = tail) ]_vars                       \* rProd: tail == old.tail
RelyCons == [][ (\E s \in Data : Produce(s)) => (head' = head /\ tail' >= tail) ]_vars   \* rCons / gProd

----------------------------------------------------------------------------
\* LIVENESS -- a property the sequential checker cannot even express (@Decreases is per-call
\* termination, not system progress). Once n items are produced, n are eventually consumed.

Progress == \A n \in 1 .. Cap : (tail >= n) ~> (head >= n)
=============================================================================
