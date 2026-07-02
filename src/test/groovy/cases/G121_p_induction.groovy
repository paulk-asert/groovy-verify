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

/** 'P-induction' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G121_p_induction {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Recursive methods proven by induction via @Decreases (factorial grows >= linearly; the recursive call is the inductive hypothesis).'

    static final List<Map> CASES = [

        // ---------- Inductive proof helper (README Act 1): a recursive method's own @Ensures is the
        // induction hypothesis at the recursive call. A recursive factorial proves it grows at least
        // linearly (fact(n) >= n). The exponential bound fact(n) >= 2^(n-1) needs the nonlinear step
        // n*fact(n-1) >= 2*fact(n-1) and times out under NIA (soft "could not decide", never a false pass).
        [group: 'P-induction', name: 'recursive factorial grows at least linearly (fact(n) >= n)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result >= n })
                        @Decreases({ n })
                        static int fact(int n) {
                            if (n <= 1) return 1
                            int rest = fact(n - 1)
                            return n * rest
                        }
                    }''')],
        // A self/contracted call inside a return expression is hoisted to an implicit single-assignment
        // local (bound by the callee's @Ensures), so the recursive call no longer needs hand-hoisting.
        // (1) compound return `n * fact(n-1)` — the form that previously needed two lines.
        [group: 'P-induction', name: 'compound return n * fact(n-1) (call hoisted)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result >= n })   // factorial grows at least linearly — proven by induction on n
                        @Decreases({ n })
                        static int fact(int n) {
                            if (n <= 1) return 1
                            return n * fact(n - 1)   // the recursive call's @Ensures is the induction hypothesis
                        }
                    }''')],
        // (2) bare tail return `return helper(n-1, next)` — the @TailRecursive accumulator shape.
        [group: 'P-induction', name: 'bare tail return: accumulator helper (call hoisted)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && acc >= 1 })
                        @Ensures({ result >= acc })
                        @Decreases({ n })
                        static long factHelper(long n, long acc) {
                            if (n <= 1) return acc
                            long next = n * acc
                            return factHelper(n - 1, next)
                        }
                    }''')],
        // Soundness: hoisting the call must NOT suppress the base-case check. A false @Ensures still
        // refutes — f(0) returns 0, not >= 1 — despite the recursive return path being modelled.
        [group: 'P-induction', name: 'hoisted bare return: false postcondition still refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 1 })
                        @Decreases({ n })
                        static int f(int n) {
                            if (n <= 0) return 0
                            return f(n - 1)
                        }
                    }''')],
        // Soundness: the callee's @Requires is still discharged at the call site. f(n-2) breaks
        // @Requires({ n >= 0 }) when n == 1 (f(-1)), so the method must refute on the precondition.
        [group: 'P-induction', name: 'hoisted bare return: callee precondition still enforced',
         expect: 'precondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ n })
                        static int f(int n) {
                            if (n <= 0) return 0
                            return f(n - 2)
                        }
                    }''')],
        // @TailRecursive interaction: the transform rewrites the body to a loop and renames variables
        // in place at SEMANTIC_ANALYSIS. ContractExpansionTransform deep-clones the CONVERSION snapshot
        // for @TailRecursive methods so the author's recursive body survives, and the bare tail call is
        // hoisted (Phase 92) — so the inductive accumulator contract verifies on the recursive form,
        // while @TailRecursive independently makes it stack-safe at runtime.
        [group: 'P-induction', name: '@TailRecursive accumulator verifies on the recursive form', ok: true,
         src: tc('''class C {
                        @groovy.transform.TailRecursive
                        @Requires({ n >= 0 && acc >= 1 })
                        @Ensures({ result >= acc })
                        @Decreases({ n })
                        static long factHelper(long n, long acc) {
                            if (n <= 1) return acc
                            long next = n * acc
                            return factHelper(n - 1, next)
                        }
                    }''')],
        // Soundness: the deep-cloned snapshot must not let a false @Ensures slip through — base case
        // returns acc, not acc+1, so it still refutes.
        [group: 'P-induction', name: '@TailRecursive false postcondition still refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @groovy.transform.TailRecursive
                        @Requires({ n >= 0 && acc >= 1 })
                        @Ensures({ result >= acc + 1 })
                        @Decreases({ n })
                        static long factHelper(long n, long acc) {
                            if (n <= 1) return acc
                            long next = n * acc
                            return factHelper(n - 1, next)
                        }
                    }''')],

        // Soundness of the deep-cloned snapshot's implicit safety obligations: a @TailRecursive method
        // that dereferences an unguarded receiver / indexes an unchecked array must still refute (the
        // clone's variable nodes carry a self-accessedVariable so the deref-site fires; bounds are
        // structural). Without these the clone would silently verify code that NPEs / overruns.
        [group: 'P-induction', name: '@TailRecursive unguarded receiver deref still refutes', ok: false, expect: 'NullPointer',
         src: tc('''class C {
                        @groovy.transform.TailRecursive
                        @Requires({ n >= 0 })
                        @Decreases({ n })
                        static int f(int n, String s) {
                            if (n <= 0) return s.length()
                            return f(n - 1, s)
                        }
                    }''')],
        [group: 'P-induction', name: '@TailRecursive unguarded array access still refutes', ok: false, expect: 'IndexOutOfBounds',
         src: tc('''class C {
                        @groovy.transform.TailRecursive
                        @Requires({ n >= 0 })
                        @Decreases({ n })
                        static int f(int n, int[] a) {
                            if (n <= 0) return a[0]
                            return f(n - 1, a)
                        }
                    }''')],
        [group: 'P-induction', name: '@TailRecursive divide-by-zero still refutes', ok: false, expect: 'Division by zero',
         src: tc('''class C {
                        @groovy.transform.TailRecursive
                        @Requires({ n >= 0 })
                        @Decreases({ n })
                        static int f(int n, int d) {
                            if (n <= 0) return 100.intdiv(d)
                            return f(n - 1, d)
                        }
                    }''')],
        // The braced base-case return (`if (n<=1) { return acc }`) is the user-level workaround that
        // makes groovy-contracts' @Ensures fire at RUNTIME under @TailRecursive (its per-return wrap finds
        // the block-wrapped return); it also verifies at COMPILE time here (the cloner recurses into the
        // block) — so braces + the deep-clone give both halves of the dual-tenet.
        [group: 'P-induction', name: '@TailRecursive braced base-case return verifies', ok: true,
         src: tc('''class C {
                        @groovy.transform.TailRecursive
                        @Requires({ n >= 0 && acc >= 1 })
                        @Ensures({ result >= acc })
                        @Decreases({ n })
                        static long factHelper(long n, long acc) {
                            if (n <= 1) {
                                return acc
                            }
                            long next = n * acc
                            return factHelper(n - 1, next)
                        }
                    }''')],
    ]
}
