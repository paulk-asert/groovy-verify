<!--
  SPDX-License-Identifier: Apache-2.0

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-->

# JIRA drafts — groovy.concurrent.ChannelSelect (Groovy 6.0.0-beta-3)

Two issues: a Bug for the behaviour observed in `repro/ChannelSelectRepro.groovy`, and an Improvement
(fair selection) that builds on the Bug's fix. FILED AND FIXED as one issue, GROOVY-12320 (PR #2846, fix version
6.0.0-beta-4): claim-based `select()`, `fair()` (rotating, on a held instance) and `random()`,
`ChannelClosedException` when every branch is closed. The drafts stay as the record behind Phases 256/257.

---

## Issue 1 — Bug

**Summary:** ChannelSelect.select() consumes from losing branches: reorders their elements, leaks a pending
receiver per select, and never completes when every branch is closed

**Type:** Bug  **Priority:** Major
**Affects Version/s:** 6.0.0-beta-3 (also beta-2; `select()` is unchanged between them)
**Component/s:** runtime (groovy.concurrent)

**Description**

`ChannelSelect.select()` is implemented by racing a real `receive()` on every branch and completing with the
first one to deliver:

```java
for (int i = 0; i < channels.size(); i++) {
    ch.receive().toCompletableFuture().whenComplete((value, error) -> {
        if (error != null) return;
        if (won.compareAndSet(false, true)) winner.complete(new Result(index, value));
        else ((AsyncChannel<Object>) ch).send(value);   // "Re-send the consumed value back to avoid message loss"
    });
}
```

Because losing branches genuinely dequeue, three things follow. Each is reproduced by the attached script
(`ChannelSelectRepro.groovy`, run with the 6.0.0-beta-3 distribution; output quoted verbatim).

1. **A losing branch's element order is broken.** The consumed element is put back with `send`, i.e. at the
   *back* of the queue (the Javadoc acknowledges "may reorder values within a channel"). Observed: `b` holding
   `[b1, b2]`, one select over `[a, b]` that `a` wins — `b` then delivers `[b2, b1]`. For a multiplexer over two
   busy inputs this happens on nearly every iteration, so a consumer of a contended branch sees a permutation
   of what was sent. A channel's FIFO contract should not depend on whether someone else selected over it.

2. **Every select leaves a pending receiver on each branch that was empty at the time.** Those receivers are
   never cancelled: when the branch later gets an element, each stale receiver in turn takes it and re-sends
   it (the `else` path above). Observed: 1000 selects over `[busy, quiet]` with `quiet` always empty leave
   **1000 entries in `DefaultAsyncChannel.waitingReceivers`** on `quiet`; a single subsequent `quiet.send(42)`
   is then **taken and re-sent 1000 times** before it settles in the buffer (pending receivers drop from 1000
   to 0, `bufferedSize` ends at 1). In a long-lived server whose branches are unevenly busy this is unbounded
   growth on every quiet branch, plus a hidden O(n) bounce per element.

3. **A select over channels that are all closed and drained never completes.** A closed-and-drained branch
   completes its receive exceptionally, which the callback ignores (`if (error != null) return;`); nothing
   completes `winner` once every branch has failed. Observed: `await ChannelSelect.from(c1, c2).select()
   .orTimeoutMillis(500)` with both channels closed and empty → `TimeoutException`. A
   `ChannelClosedException` would be the consistent outcome (that is what `receive()` itself does).

**Steps to reproduce**

```groovy
import groovy.concurrent.*
import static org.apache.groovy.runtime.async.AsyncSupport.*

// (1) reordering
def a = AsyncChannel.<String>create(4), b = AsyncChannel.<String>create(4)
a.send('a1'); b.send('b1'); b.send('b2')
await ChannelSelect.from(a, b).select()                 // a wins
assert [await(b.receive()), await(b.receive())] == ['b1', 'b2']   // FAILS: [b2, b1]

// (2) pending receivers accumulate on a losing branch
def busy = AsyncChannel.<Integer>create(4), quiet = AsyncChannel.<Integer>create(4)
1000.times { busy.send(it); await ChannelSelect.from(busy, quiet).select() }
def f = quiet.class.getDeclaredField('waitingReceivers'); f.accessible = true
assert f.get(quiet).size() == 0                         // FAILS: 1000

// (3) all branches closed: never completes
def c1 = AsyncChannel.<Integer>create(1), c2 = AsyncChannel.<Integer>create(1)
c1.close(); c2.close()
await ChannelSelect.from(c1, c2).select().orTimeoutMillis(500)   // TimeoutException, not ChannelClosedException
```

**Expected**

- A select takes exactly one element, from exactly one branch; the other branches are untouched (order and
  contents preserved, nothing registered on them after the select completes).
- A select over channels that are all closed and drained fails with `ChannelClosedException`.

**Proposed fix**

Select by *claim*, not by consumption — the discipline of JCSP's `Alternative` (enable guards, wait, disable,
commit to one), expressed in the channel's delivery path:

- Add a package-private `Awaitable<T> receiveIf(AtomicBoolean claim)` to `DefaultAsyncChannel`. At the moment
  the channel is about to hand an element to that receiver (under its lock), it first does
  `claim.compareAndSet(false, true)`; if that fails, the element stays in the buffer and the receiver is
  discarded. `select()` shares one `claim` across its branches, so exactly one branch dequeues, losers never
  touch their buffers (fixes 1), and pending losers are dropped at claim time rather than left to bounce
  (fixes 2).
- Count closed-and-drained failures in the callback; when they reach the branch count, complete `winner`
  exceptionally with `ChannelClosedException` (fixes 3).

**Attachments:** `ChannelSelectRepro.groovy` (full script with the four experiments and its output)

---

## Issue 2 — Improvement

**Summary:** ChannelSelect: offer a fair (rotating-priority) selection policy; document that select() is
priority-by-list-order

**Type:** Improvement  **Priority:** Major
**Affects Version/s:** 6.0.0-beta-3
**Component/s:** runtime (groovy.concurrent)
**Depends on:** Issue 1 (claim-based selection makes the policy well-defined)

**Description**

When several branches are ready at the time of the call, `select()` always takes the lowest index: each
ready branch's `receive()` completes synchronously inside the registration loop, in list order. Observed with
both branches pre-filled, 100 selects over `[a, b]`: index 0 wins 100/100; over `[b, a]`: index 0 wins
100/100 again. So today's `select()` is a *priority* select (JCSP's `priSelect()`), which is a fine policy but
an undocumented one, and the only one.

For CSP-style servers and multiplexers this matters: a branch listed after one whose producer never blocks
(a busy generator) is never taken — the classic starvation the JCSP/occam teaching literature avoids with
`fairSelect()`. There is currently no way to write a fair server on `groovy.concurrent`.

**Proposal**

```groovy
ChannelSelect.from(a, b).select()          // unchanged: priority by list order — document it as such
ChannelSelect.from(a, b).fair().select()   // rotating priority
```

`fair()` keeps a per-instance cursor; each `select()` polls the branches starting at `last + 1` (under the
shared claim of Issue 1, so "ready" is tested without consuming) before registering the remaining
receivers, then records the index taken. A branch that is ready is therefore tried first at least once
every N calls, so no continuously-ready branch can starve the others. Without Issue 1, `fair()` can only
rotate the tie-break among branches that happen to be ready at call time, which is weaker and still leaks.

Optionally, `priority()` as an explicit alias of today's behaviour, so both policies are spelled out at the
call site, as in JCSP.

**Motivation**

`groovy.concurrent` replaces an LGPL JCSP substrate for a body of teaching material (Kerridge, *Using
Concurrency and Parallelism Effectively*) whose networks are `fairSelect`-based servers. With Issue 1 and a
`fair()` policy those networks are expressible; without them a multiplexer over two busy inputs starves the
second, and a server over several clients serves the first-listed client preferentially and may never
serve the others depending on timing.
