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

/** 'P153 async-await' — 15 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G258_p153_async_await {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Groovy 6 async/await: a safe async closure (a pure value) is driven synchronously, so `await (async { e })` reads out `e` and the functional contract proves (compute), a bug after the await refutes (computeBuggy), and chained awaits thread the value (computeTwice). Awaitable.all (multi-arg await) gathers tasks into a value list to combine (a wrong total refutes). delay is a no-op (timing not modelled) and orTimeoutMillis is transparent (the deadline assumed away). The racing Awaitable.any/first are modelled as a nondeterministic choice over the task values (an if/else over the winner — the spec must hold for every winner, a hedged same-value race is determinate); the value-or-fallback completeOnTimeoutMillis and an opaque parameter Awaitable skip loudly. A combined example fans out tasks over symbolic inputs, pauses with delay, gathers with all, and combines — verifying (a+1)+(b+1)+(c+1) (a wrong combination refutes).'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- Groovy 6 async/await (the bmc4j Work.kt approach, native syntax) ----------
        // A *safe* async closure (one that returns a pure value, the discipline the async docs prescribe) is
        // observationally just its value driven synchronously, so `await (async { e })` reads out `e`. We prove the
        // functional contract and *assume* the structural (scheduling) half — the async sibling of the lock/agent
        // examples. `async`/`await` lower to AsyncSupport.async/await calls the reader recognises.
        [group: 'P153 async-await', name: 'await an async value (compute)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == (x + 1) * 2 })
                        static int compute(int x) {
                            def fa = async { x + 1 }
                            int a = await fa
                            return a * 2
                        }
                    }''')],
        // Soundness: a logic bug AFTER the await (off by one) is caught — the bmc4j computeBuggy.
        [group: 'P153 async-await', name: 'a bug after the await refutes (computeBuggy)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == (x + 1) * 2 })
                        static int compute(int x) {
                            def fa = async { x + 1 }
                            int a = await fa
                            return a * 2 + 1
                        }
                    }''')],
        // Inline: `await async { e }` with no intermediate local.
        [group: 'P153 async-await', name: 'inline await of a fresh async', ok: true,
         src: tc('''class C {
                        @Ensures({ result == x + 2 })
                        static int incTwice(int x) {
                            int a = await async { x + 1 }
                            return a + 1
                        }
                    }''')],
        // Two awaits in sequence — the value threads through (computeTwice).
        [group: 'P153 async-await', name: 'two awaits in sequence (computeTwice)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == x + 2 })
                        static int computeTwice(int x) {
                            def fa = async { x + 1 }
                            int a = await fa
                            def fb = async { a + 1 }
                            int b = await fb
                            return b
                        }
                    }''')],
        // Boundary: awaiting a *parameter* Awaitable (no visible async source) isn't a safe-value read-out — the
        // verifier can't see what it resolves to, so it skips loudly rather than guess.
        [group: 'P153 async-await', name: 'awaiting an opaque parameter skips', expect: 'outside fragment',
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == 42 })
                     static int run(Awaitable<Integer> task) {
                         int a = await task
                         return a
                     }
                 }'''],
        // Awaitable.all (multi-arg await) — gather independent tasks into a value list, then combine. Sound because
        // `all` waits for every task, so the gathered list is order-independent. (`def r` + element casts because the
        // multi-arg await is typed List<Object>; the verifier folds r[i] to the i-th task's value via the list factory.)
        [group: 'P153 async-await', name: 'gather all then combine (await all)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 6 })
                        static int sumThree() {
                            def r = await(async { 1 }, async { 2 }, async { 3 })
                            return ((int) r[0]) + ((int) r[1]) + ((int) r[2])
                        }
                    }''')],
        // Soundness: a wrong total over the gathered values refutes.
        [group: 'P153 async-await', name: 'wrong gathered total refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 7 })
                        static int sumThree() {
                            def r = await(async { 1 }, async { 2 }, async { 3 })
                            return ((int) r[0]) + ((int) r[1]) + ((int) r[2])
                        }
                    }''')],
        // delay is a non-blocking pause: no value, no state effect — a no-op for a logic proof (timing isn't modelled).
        [group: 'P153 async-await', name: 'await delay is a no-op', ok: true,
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == x + 1 })
                     static int f(int x) {
                         await Awaitable.delay(10)
                         return x + 1
                     }
                 }'''],
        // orTimeoutMillis is transparent under the *completion* assumption — the deadline is the structural half we
        // assume away (like mutual exclusion for locks), so the awaited value is the task's value.
        [group: 'P153 async-await', name: 'orTimeoutMillis is transparent (completion assumed)', ok: true,
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == (x + 1) * 2 })
                     static int g(int x) {
                         def fa = async { x + 1 }
                         int a = await Awaitable.orTimeoutMillis(fa, 1000)
                         return a * 2
                     }
                 }'''],
        // Boundary: the FALLBACK form completeOnTimeoutMillis(task, fallback, ms) returns the value OR the fallback —
        // genuinely nondeterministic (did it beat the clock?) — so it is NOT unwrapped and skips loudly.
        [group: 'P153 async-await', name: 'completeOnTimeoutMillis (value-or-fallback) skips', expect: 'outside fragment',
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == (x + 1) * 2 })
                     static int h(int x) {
                         def fa = async { x + 1 }
                         int a = await Awaitable.completeOnTimeoutMillis(fa, 0, 1000)
                         return a * 2
                     }
                 }'''],
        // Awaitable.any / first race: the winner is one of the task values (nondeterministic) — an if/else over an
        // unknown selector. A spec that holds for EVERY possible winner verifies (here 1 or 2, whichever wins).
        [group: 'P153 async-await', name: 'racing any verifies when the spec covers every winner', ok: true,
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == 1 || result == 2 })
                     static int race() {
                         def x = await Awaitable.any(async { 1 }, async { 2 })
                         return (int) x
                     }
                 }'''],
        // Soundness: a spec that only holds for ONE winner refutes — the other task might win (the scheduler picks).
        [group: 'P153 async-await', name: 'racing any refutes a spec that misses a winner', expect: 'Cannot prove postcondition',
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == 1 })
                     static int race() {
                         def x = await Awaitable.any(async { 1 }, async { 2 })
                         return (int) x
                     }
                 }'''],
        // Hedged: when every task computes the SAME value, the winner is irrelevant — the result is determinate.
        [group: 'P153 async-await', name: 'hedged first (same value) is determinate', ok: true,
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == 42 })
                     static int hedged(int x) {
                         def y = await Awaitable.first(async { 42 }, async { 42 })
                         return (int) y
                     }
                 }'''],
        // Putting it together: fan out independent tasks over the inputs, a no-op delay, gather with `all`, combine —
        // the gather threads the SYMBOLIC task values (a+1, b+1, c+1), not just constants.
        [group: 'P153 async-await', name: 'fan out, delay, gather, combine', ok: true,
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == (a + 1) + (b + 1) + (c + 1) })
                     static int gather(int a, int b, int c) {
                         def t1 = async { a + 1 }
                         def t2 = async { b + 1 }
                         def t3 = async { c + 1 }
                         await Awaitable.delay(5)
                         def r = await(t1, t2, t3)
                         return ((int) r[0]) + ((int) r[1]) + ((int) r[2])
                     }
                 }'''],
        // Soundness: a wrong combination (dropping one task's +1) refutes.
        [group: 'P153 async-await', name: 'wrong combination of gathered tasks refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'import groovy.concurrent.Awaitable\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class C {
                     @Ensures({ result == (a + 1) + (b + 1) + c })
                     static int gather(int a, int b, int c) {
                         def t1 = async { a + 1 }
                         def t2 = async { b + 1 }
                         def t3 = async { c + 1 }
                         await Awaitable.delay(5)
                         def r = await(t1, t2, t3)
                         return ((int) r[0]) + ((int) r[1]) + ((int) r[2])
                     }
                 }'''],
    ]
}
