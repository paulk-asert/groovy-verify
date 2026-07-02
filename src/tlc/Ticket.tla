SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in
compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
(Text before the MODULE banner is ignored by the TLA+ parser.)

---------------------------- MODULE Ticket ----------------------------
\* Leino's ticket system for mutual exclusion (KRML260, "Modeling Concurrency in Dafny"), as a TLA+
\* state machine. This is the rung-2 companion to the groovy-verify proof (rung 1).
\*
\* groovy-verify (rung 1) SMT-proves, symbolically, over a bounded (enum {A, B}) process set:
\*   - safety / mutual exclusion + the strengthened invariant `valid`   (Phases 170-172)
\*   - the ranking function and bounded bypass                          (Phases 171-172)
\*   - the fair-schedule eventually-eats                                (Phases 173-175, N = 2 only)
\* It CANNOT (yet) reach the fair-schedule liveness beyond two processes: the <= 1 measure bound is what
\* lets the proof avoid an unbounded trace loop, so N > 2 needs machinery it does not have.
\*
\* TLC (rung 2) does the complementary work: it enumerates EVERY interleaving of the abstract state
\* machine for a small finite N, so it (a) independently confirms mutual exclusion and the SAME `valid`
\* invariant the proof uses are true on every reachable state -- validating that the frame / fairness
\* facts the proof *assumes* really are consequences of the transition system -- and (b) checks the
\* fair-schedule eventually-eats at N = 3, the general-N reach rung 1 can't make.
\*
\* This is Leino's Model 2 (Section 7.2): state as (ticket, serving, cs, t); each atomic event a
\* two-state action. cs[p] is p's control state; t[p] the ticket it holds.

EXTENDS Naturals

CONSTANTS P                       \* the set of processes (Leino's `type Process`)
CState == {"Thinking", "Hungry", "Eating"}

VARIABLES ticket,                 \* the dispenser: next ticket to hand out
          serving,                \* the "serving" display: whose ticket is being served
          cs,                     \* [P -> CState]  each process's control state
          t                       \* [P -> Nat]     the ticket each process holds (relevant when != Thinking)
vars == <<ticket, serving, cs, t>>

Init ==
  /\ ticket  = 0
  /\ serving = 0
  /\ cs = [p \in P |-> "Thinking"]
  /\ t  = [p \in P |-> 0]

\* Request(p): a thinking process grabs the current ticket and advances the dispenser (groovy-verify Request).
Request(p) ==
  /\ cs[p] = "Thinking"
  /\ t'      = [t EXCEPT ![p] = ticket]
  /\ ticket' = ticket + 1
  /\ cs'     = [cs EXCEPT ![p] = "Hungry"]
  /\ UNCHANGED serving

\* Enter(p): a hungry process whose ticket is up enters the critical section (groovy-verify Enter,
\* then-branch). Modelled as enabled only when t[p] = serving -- the "wait until" is the action simply
\* not being enabled, so no busy-wait stutter action is needed.
Enter(p) ==
  /\ cs[p] = "Hungry"
  /\ t[p] = serving
  /\ cs' = [cs EXCEPT ![p] = "Eating"]
  /\ UNCHANGED <<ticket, serving, t>>

\* Leave(p): the eating process advances the display and returns to thinking (groovy-verify Leave).
Leave(p) ==
  /\ cs[p] = "Eating"
  /\ serving' = serving + 1
  /\ cs'      = [cs EXCEPT ![p] = "Thinking"]
  /\ UNCHANGED <<ticket, t>>

\* THE BUG: a dispenser that fails to advance -- two processes can draw the SAME ticket, so uniqueness
\* fails and, with it, mutual exclusion. This is the TLC twin of groovy-verify's "drop the uniqueness
\* conjunct" refutation (Phase 170); under BuggySpec, TLC exhibits two processes Eating at once as a
\* concrete interleaved trace.
RequestBad(p) ==
  /\ cs[p] = "Thinking"
  /\ t'  = [t EXCEPT ![p] = ticket]
  /\ cs' = [cs EXCEPT ![p] = "Hungry"]
  /\ UNCHANGED <<ticket, serving>>

Next      == \E p \in P : Request(p)    \/ Enter(p) \/ Leave(p)
NextBuggy == \E p \in P : RequestBad(p) \/ Enter(p) \/ Leave(p)

\* Fair scheduling (Leino's FairSchedule): a process that can enter or leave is not ignored forever.
\* Weak fairness suffices -- a hungry-and-served process's Enter, and an eating process's Leave, each
\* stay continuously enabled once enabled (mutual exclusion is what guarantees the Enter's stability).
Fairness  == \A p \in P : WF_vars(Enter(p)) /\ WF_vars(Leave(p))

Spec      == Init /\ [][Next]_vars      /\ Fairness
BuggySpec == Init /\ [][NextBuggy]_vars /\ Fairness

\* State-space bound for TLC: tickets grow without bound as processes cycle, so cap the dispenser. The
\* progress actions (Enter/Leave) never increase `ticket`, so this bound does not cut off any hungry
\* process's route to the critical section -- liveness stays meaningful under it.
TicketBound == ticket <= 4

----------------------------------------------------------------------------
\* SAFETY

TypeOK ==
  /\ ticket  \in Nat
  /\ serving \in Nat
  /\ cs \in [P -> CState]
  /\ t  \in [P -> Nat]

\* THE safety property: at most one process eating (Leino's MutualExclusion lemma; groovy-verify Phase 170).
MutualExclusion == \A p, q \in P : (cs[p] = "Eating" /\ cs[q] = "Eating") => (p = q)

\* The strengthened invariant groovy-verify proves inductive (`valid`): the dispenser never falls behind
\* the display; every held ticket lies in [serving, ticket); non-thinking processes hold distinct tickets;
\* an eating process holds exactly `serving`. TLC confirms it on EVERY reachable state -- so the invariant
\* the proof leans on is corroborated by exhaustive enumeration, not just shown inductive.
Valid ==
  /\ serving <= ticket
  /\ \A p \in P : cs[p] # "Thinking" => (serving <= t[p] /\ t[p] < ticket)
  /\ \A p, q \in P : (p # q /\ cs[p] # "Thinking" /\ cs[q] # "Thinking") => (t[p] # t[q])
  /\ \A p \in P : cs[p] = "Eating" => (t[p] = serving)

----------------------------------------------------------------------------
\* LIVENESS: a hungry process eventually eats (groovy-verify Phases 174-175, there only for N = 2).
\* TLC checks it here for N = 3 under weak-fair scheduling -- the general-N reach the proof can't yet make.
Liveness == \A p \in P : (cs[p] = "Hungry") ~> (cs[p] = "Eating")
=============================================================================
