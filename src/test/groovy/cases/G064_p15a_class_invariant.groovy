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

/** 'P15a class-invariant' — 9 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G064_p15a_class_invariant {

    static final List<Map> CASES = [

        // ---------- Phase 15a (step 3): class @Invariant — entry-assume + exit-prove ----------
        // Entry-assume: the class invariant gives a fact the @Ensures otherwise can't show.
        [group: 'P15a class-invariant', name: 'invariant assumed at entry', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        @Ensures({ result >= 0 })
                        int get() { count }
                    }''')],
        // Exit-prove (void, invariant-only): the mutator preserves the invariant.
        [group: 'P15a class-invariant', name: 'invariant preserved by inc', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        void inc() { count = count + 1 }
                    }''')],
        // Exit-prove (refuted): a mutator that can drop count below zero violates the invariant.
        [group: 'P15a class-invariant', name: 'invariant broken by dec refuted',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        void dec() { count = count - 1 }
                    }''')],
        // The @Requires guard plus the entry-assumed invariant together establish the exit obligation.
        [group: 'P15a class-invariant', name: 'guarded dec preserves invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        @Requires({ count > 0 })
                        void dec() { count = count - 1 }
                    }''')],
        // Step 4 — the class invariant `n <= a.length` lets `a[i]` inside a counted loop verify
        // without restating the bound in @Requires on every method. The implicit-obligation pass
        // sees the invariant alongside the loop's @Invariant when discharging the index check.
        [group: 'P15a class-invariant', name: 'loop body uses class invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ a != null && 0 <= n && n <= a.length })
                    class C { int[] a; int n
                        int sum() {
                            int s = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { s = s + a[i]; i = i + 1 }
                            return s
                        }
                    }''')],
        // Step 5 — an invariant whose body is outside the encoder fragment (a {@code split} call,
        // which returns an array — list-from-string is structurally invasive and not yet wired)
        // is dropped with a single "Skipped class invariant" diagnostic at the method level.
        // Verification continues for everything else.
        [group: 'P15a class-invariant', name: 'unmodelled invariant skipped',
         expect: 'Skipped class invariant',
         src: tc('''@groovy.contracts.Invariant({ name.split(",").length > 0 })
                    class C { String name
                        int n() { 0 }
                    }''')],
        // Step 6 — a child inherits the parent's class invariant (AND-conjoined). The child's
        // inc() must hold both clauses at exit: `count >= 0` (parent) and `count <= max` (child).
        // Without the parent clause inherited, the verifier would have no way to know count stays
        // non-negative after the increment — so this case is the end-to-end proof that the super-
        // walk wired in step 2 flows through to the discharge sites.
        // NB: both classes carry @TypeChecked — the extension is not inherited by subclasses, so annotating
        // only the parent (the bare tc() form) would leave the child's methods unverified (a vacuous pass).
        [group: 'P15a class-invariant', name: 'parent invariant inherited', ok: true,
         src: HDR + """
@groovy.contracts.Invariant({ count >= 0 })
@TypeChecked(extensions = 'verification.VerifyChecker')
class P { int count }
@groovy.contracts.Invariant({ count <= max })
@TypeChecked(extensions = 'verification.VerifyChecker')
class C extends P {
    int max
    @Requires({ count < max })
    void inc() { count = count + 1 }
}
"""],
        // The non-vacuity proof: a child mutator that respects ONLY its own concerns breaks the *inherited*
        // `count >= 0`, and the conjoined invariant refutes (counterexample count=0).
        [group: 'P15a class-invariant', name: 'child breaking inherited invariant refutes', ok: false, expect: 'Cannot prove class invariant',
         src: HDR + """
@groovy.contracts.Invariant({ count >= 0 })
@TypeChecked(extensions = 'verification.VerifyChecker')
class P { int count }
@groovy.contracts.Invariant({ count <= max })
@TypeChecked(extensions = 'verification.VerifyChecker')
class C extends P {
    int max
    void dec() { count = count - 1 }
}
"""],
        // Step 7 — a static method on an @Invariant class is not subject to the invariant
        // (no `this`). The method verifies even though its body would violate the invariant if
        // applied as an exit obligation — confirming the isStatic() skip in beforeVisitMethod.
        [group: 'P15a class-invariant', name: 'static method skips invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        static int twice(int x) { x + x }
                    }''')],
    ]
}
