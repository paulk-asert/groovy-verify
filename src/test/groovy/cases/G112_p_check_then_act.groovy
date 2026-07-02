/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package cases

import static cases.CaseDsl.*

/** 'P-check-then-act' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G112_p_check_then_act {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Check-then-act, the rung-1 boundary sharpened: a bounded counter whose `if (count < 1) count = count + 1` keeps `count <= 1` SEQUENTIALLY — groovy-verify proves the @Invariant (a wrong bound `<= 0` refutes) — yet is NOT thread-safe (two threads both pass the guard → count == 2, which jcstress\'s BoundedCounterJCStress catches, ~5 in 7 billion). The verifier reasons above the JMM, so it proves the SAME invariant for the racy and the @WithWriteLock-fixed version; only the structural rung tells them apart. A verified-sequential invariant that concurrency breaks — rung 1\'s documented scope, not unsoundness.'

    static final List<Map> CASES = [
        // String-contract prototype: the Java-friendly `verification.@Requires/@Ensures/@Decreases('…')` (a String
        // is a legal Java annotation value where a closure is not), captured into the SAME reparse→prove pipeline.
        // A recursive Java-style method verifies inductively from String contracts, and a wrong @Ensures refutes.
        // Dining philosophers, the thread-local half (the structural half is the Fray rung — see CONCURRENCY.md).
        // Deadlock-freedom by *resource hierarchy*: if every philosopher acquires its two forks in increasing
        // global index order, the wait-for graph is acyclic ⇒ no deadlock. groovy-verify proves that LOCAL
        // ordering discipline (pure int arithmetic, fully in-fragment) and pinpoints exactly which philosopher
        // breaks it under the naive scheme.
        // Check-then-act, the rung-1 boundary: a bounded counter whose `if (count < 1) count = count + 1` is
        // SEQUENTIALLY correct — groovy-verify proves `@Invariant({ count <= 1 })` is preserved — yet not thread-safe
        // (two threads can both pass the guard → count == 2, which BoundedCounterJCStress observes). The verifier
        // reasons above the JMM, so it proves the SAME invariant for the racy and the @WithWriteLock-fixed version;
        // only the structural rung tells them apart. (See concurrent/BoundedCounter, examples/concurrency.md.)
        [group: 'P-check-then-act', name: 'bounded counter: sequential invariant verifies', ok: true,
         src: tc('''@Invariant({ count <= 1 })
             class C {
                 int count = 0
                 void tryIncrement() { if (count < 1) count = count + 1 }
             }''')],
        [group: 'P-check-then-act', name: 'wrong bound (count <= 0) refutes', expect: 'invariant',
         src: tc('''@Invariant({ count <= 0 })
             class C {
                 int count = 0
                 void tryIncrement() { if (count < 1) count = count + 1 }
             }''')],
        [group: 'P-check-then-act', name: 'the @WithWriteLock fix proves the SAME invariant (lock transparent)', ok: true,
         src: tc('''@Invariant({ count <= 1 })
             class C {
                 int count = 0
                 @groovy.transform.WithWriteLock
                 void tryIncrement() { if (count < 1) count = count + 1 }
             }''')],
        // AtomicInteger modelled as an int cell: get() reads, incrementAndGet() writes — the SAME sequential
        // invariant proof as the plain-int counter (atomicity is rung-1-transparent).
        [group: 'P-check-then-act', name: 'AtomicInteger: get()/incrementAndGet() invariant verifies', ok: true,
         src: tc('''@Invariant({ count.get() <= 1 })
             class C {
                 private final java.util.concurrent.atomic.AtomicInteger count = new java.util.concurrent.atomic.AtomicInteger(0)
                 void tryIncrement() { if (count.get() < 1) count.incrementAndGet() }
             }''')],
        [group: 'P-check-then-act', name: 'AtomicInteger: wrong bound (get() <= 0) refutes', expect: 'invariant',
         src: tc('''@Invariant({ count.get() <= 0 })
             class C {
                 private final java.util.concurrent.atomic.AtomicInteger count = new java.util.concurrent.atomic.AtomicInteger(0)
                 void tryIncrement() { if (count.get() < 1) count.incrementAndGet() }
             }''')],
        [group: 'P-check-then-act', name: 'AtomicInteger: set(x) write tracked by the invariant', expect: 'invariant',
         src: tc('''@Invariant({ count.get() <= 1 })
             class C {
                 private final java.util.concurrent.atomic.AtomicInteger count = new java.util.concurrent.atomic.AtomicInteger(0)
                 void bump() { count.set(2) }
             }''')],
        [group: 'P-check-then-act', name: 'AtomicInteger: compareAndSet(0,1) preserves the bound', ok: true,
         src: tc('''@Invariant({ count.get() <= 1 })
             class C {
                 private final java.util.concurrent.atomic.AtomicInteger count = new java.util.concurrent.atomic.AtomicInteger(0)
                 void tryIncrement() { if (count.get() < 1) count.compareAndSet(0, 1) }
             }''')],
        [group: 'P-check-then-act', name: 'AtomicInteger: addAndGet over-shoots the bound (refutes)', expect: 'invariant',
         src: tc('''@Invariant({ count.get() <= 1 })
             class C {
                 private final java.util.concurrent.atomic.AtomicInteger count = new java.util.concurrent.atomic.AtomicInteger(0)
                 void tryIncrement() { if (count.get() < 1) count.addAndGet(5) }
             }''')],
    ]
}
