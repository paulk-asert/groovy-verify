<!--
 Licensed to the Apache Software Foundation (ASF) under one
 or more contributor license agreements.  See the NOTICE file
 distributed with this work for additional information
 regarding copyright ownership.  The ASF licenses this file
 to you under the Apache License, Version 2.0 (the
 "License"); you may not use this file except in compliance
 with the License.  You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing,
 software distributed under the License is distributed on an
 "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 KIND, either express or implied.  See the License for the
 specific language governing permissions and limitations
 under the License.
-->

# JIRA draft — ChannelSelect output guards: claimable SEND offers (the arbitrated mixed choice)

A draft for Paul to file; nothing has been filed. The observations behind it are runnable:
[`repro/MixedChoiceRepro.groovy`](MixedChoiceRepro.groovy), identical on 6.0.0-beta-3 and on the
6.0.0-SNAPSHOT carrying GROOVY-12320.

## Improvement: `ChannelSelect` offers that can SEND

**Summary.** `ChannelSelect` (GROOVY-12320) selects among *receives*: input guards. A process therefore
cannot say "I will send `ping`, **or** take `pong` if my peer sends first" — the *mixed choice* of the
session-type and CSP literature. occam banned output guards because arbitrating them needs a commit
protocol (Buckley & Silberschatz, *An effective implementation for the generalized input-output construct
of CSP*, TOPLAS 1983); JCSP's `Alternative` kept the same restriction. GROOVY-12320 already built half of
the machinery a modern runtime needs to lift it: the claim-based receive (`receiveIfUnclaimed`). This
proposes the other half: a send offer that can be claimed or retired, so a select over mixed offers
commits **exactly one**.

**Proposed API** (names illustrative):

```groovy
import static groovy.concurrent.ChannelSelect.*

def r = await offers(send(ping, i), receive(pong)).select()
if (r.index == 0) { /* my open committed: continue the ping branch */ }
else              { /* my peer's open won: r.value is the pong opener */ }
```

- `send(chan, value)` / `send(chan, Supplier<V>)` — an offer to transfer `value` into `chan`.
- `receive(chan)` — today's input guard, unchanged.
- `select()` commits exactly one offer of this select: a send offer commits when a matching receive (or a
  peer's receive **offer**) claims it; committing any offer atomically retires this select's others —
  two-phase: offers are registered claimable, a claim tentatively pairs, the pair commits only if both
  sides' claims still stand, else both retire and rescan.
- Policies compose: `fair()` / `random()` order the scan over offers exactly as GROOVY-12320 does over
  branches.
- A committed send behaves exactly like `chan.send(v)`; a retired one has NO effect on the channel — no
  buffered residue, mirroring the claim-based receive's "losers untouched".

**Why the buffered workaround is not one.** With buffered channels each peer can just `send` its opener
unconditionally — but then *both* sends succeed, and each peer reads the other's opener as "your choice":
one session, two peers on different branches, each sure of its own (experiment 1; the session-type
literature's classic coherence failure). Making one peer the designated opener works (experiment 2 — and
groovy-verify certifies exactly that shape), but it is priority, not a race. Two polite peers that only
offer to receive never start at all (experiment 3). A one-line CAS shows the semantics wanted: 1000 racing
trials, exactly one branch committed in every one, zero double-commits, zero non-commits (experiment 4) —
that claim, run inside the select over the channel's own machinery, is this proposal.

**Observed (both runtimes, `MixedChoiceRepro.groovy`):**

1. Both peers open: both buffered sends succeed; left continues down the PONG branch while right continues
   down the PING branch — the collision.
2. One initiator: the mixed choice degenerates to that peer's choice — works today, and is the shape the
   static checker (groovy-verify Phase 267) certifies; a racing pair it refuses with the collision named.
3. Both polite: `select().orTimeoutMillis(500)` times out — nobody opens.
4. The CAS claim: 1000/1000 trials commit exactly one branch (963/37 and 961/39 splits across runs).

**Relation to GROOVY-12320.** Same design centre: selection must not disturb what it does not take.
12320 made the *receive* side claimable (losers untouched, all-closed fails fast, `fair()`/`random()`).
Send offers are the symmetric completion; with them, `ChannelSelect` reaches parity with the generalized
CSP alternative — and a compile-time session checker can certify the racing mixed choice instead of
refusing it (its refusal message already points here).
