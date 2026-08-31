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

FILED AND FIXED as GROOVY-12323 (fix version 6.0.0-beta-4): the API landed as this draft's v1 verbatim —
`offers(send(chan, v), receive(chan)).select()`, no Supplier form, explicit `Result.isSend()`/`getValue()`,
closed-channel send offers in the fast-fail, `fair()`/`random()` over offers. Verified against the local
6.0.0-SNAPSHOT: 2000 RACED rendezvous mixed-choice trials commit exactly one branch every time (a genuine
185/1815 split, zero collisions, zero hangs); the buffered collision reproduces through the new API exactly
as the coherence caveat states; a retired send leaves no residue; a held `fair()` over offers is 50/50.
The draft stays as the record behind Phases 267/268. The observations behind it are runnable:
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

- `send(chan, value)` — an offer to transfer `value` into `chan`. (No `Supplier<V>` form in v1: the
  commit happens under the channel lock, so a supplier would run user code under that lock or be
  pre-evaluated, defeating its purpose — the value is required up front.)
- `receive(chan)` — today's input guard, unchanged.
- `select()` commits exactly one offer of this select; committing any offer atomically retires the others.
- `Result` defines its send-commit shape explicitly: `getValue()` (the sent value, or null) and a
  branch-kind accessor (`isSend()`), rather than callers inferring from the index.
- A send offer to a CLOSED channel fails that branch and counts toward the all-closed
  `ChannelClosedException` fast-fail, mirroring the receive behaviour.
- Policies compose: `fair()` / `random()` order the scan over offers exactly as GROOVY-12320 does over
  branches.
- A committed send behaves exactly like `chan.send(v)`; a retired one has NO effect on the channel — no
  buffered residue, mirroring the claim-based receive's "losers untouched".

**The real work: a revertible claim.** GROOVY-12320 built the easy half, and this should be said plainly.
A claimable *receive* never needs pairing — the claim is tested when a value is provably present under a
single channel lock. A send offer meeting a receive offer is a genuine TWO-party commit across two selects'
claims, and the current irreversible boolean claim (`Winner.claim`, an `AtomicBoolean`) cannot express it:
claim yourself first and a failed CAS on the peer leaves you committed with no transfer (and no guaranteed
rescan — plain receivers withdraw lock-free from the `ConcurrentLinkedDeque`); claim the peer first and a
failed CAS on yourself has committed the peer to a transfer that never happens. The claim must become a
three-state machine — OPEN → PENDING(owner) → COMMITTED, with PENDING revertible and pending acquisition
ordered/tie-broken against livelock between symmetric peers: Buckley–Silberschatz's actual protocol.
Every existing claim site then speaks that machine (the receive path, `deliverToWaitingReceiver`,
`drainBufferToReceivers`, and `Winner.cancel`, whose CAS-based timeout/cancel race is currently
load-bearing — the "holding the claim, this cannot fail" invariant). `waitingSenders` (a plain
`ArrayDeque` whose removal takes the channel lock) needs the same lock-free-withdrawal treatment as
receivers, or a losing send offer withdrawn from inside a winning channel's delivery hits exactly the
cross-channel-lock deadlock the class comment warns about. The alternative discipline is Go's — lock all
member channels in a global order during the scan, so the active party self-commits and one CAS on the
parked peer suffices — but this class deliberately rejected multi-channel locking (that is why
`waitingReceivers` became a `ConcurrentLinkedDeque`). Contained to two classes either way; it needs
jcstress-grade stress testing, not just unit tests.

**The coherence caveat, stated up front.** Arbitration restores SESSION coherence only where a send cannot
complete unilaterally — that is, over RENDEZVOUS (capacity-0) channels, which `DefaultAsyncChannel(0)`
already supports (empirically: a capacity-0 `send` returns a pending promise that completes exactly when a
receiver takes it — repro experiment 5). Run the mixed choice over buffered channels with the proposed API
and both send offers find buffer space, commit under only their own select's claim, and the experiment-1
collision reproduces exactly, through the new feature. Each select's claim arbitrates within that select;
coherence BETWEEN two selects comes only from the rendezvous itself. Go has the identical property — its
mixed-choice idioms use unbuffered channels. Send offers on buffered channels remain meaningful (a
space-driven select: "send when room frees, or take from the other branch") — they just do not give
cross-select session coherence, and the docs should say so, or the collision will be filed as a bug against
the new feature. groovy-verify's checker will certify the racing mixed choice only over capacity-0 opener
channels for the same reason.

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

**Relation to GROOVY-12320 — and to the class's own stated model.** Same design centre: selection must
not disturb what it does not take. 12320 made the *receive* side claimable (losers untouched, all-closed
fails fast, `fair()`/`random()`); send offers are its completion — the harder half. And the precedent is
closer to home than occam: `ChannelSelect`'s own javadoc cites Go's `select` as its inspiration, and Go's
`select` supports send cases — so this completes parity with the class's stated model, not just with the
generalized CSP alternative. The occam/JCSP ban on output guards was motivated by DISTRIBUTED commit cost
(Buckley–Silberschatz 1983); in shared memory that cost does not apply, and Go proved the construct
tractable there. With it, a compile-time session checker can certify the racing mixed choice (over
rendezvous channels) instead of refusing it — its refusal message already points here. Timing is worth
weighing: `ChannelSelect` is `@since 6.0.0` and still in beta, so landing the API surface before GA (even
`@Incubating`) avoids a 6.x addition — against which sits the protocol risk, since the claim state-machine
touches invariants already shipped in beta; if it slips past GA it remains additive and safe in 6.x.
