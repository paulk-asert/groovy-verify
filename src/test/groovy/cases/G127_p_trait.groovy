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

/** 'P-trait' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G127_p_trait {

    static final List<Map> CASES = [
        // ---------- Phase 121: traits ----------
        // A trait's class @Invariant is collected along the `implements` axis (walkClassInvariants walks
        // interfaces) and enforced on every implementing class's own methods — the same monitor-invariant proof
        // as inheritance, one axis over. A trait property (`count`) is woven onto the implementer as a field, so
        // an implementing method that breaks the trait invariant refutes:
        [group: 'P-trait', name: 'trait @Invariant enforced on implementing method (refutes)', ok: false, expect: 'Cannot prove class invariant',
         src: HDR + """
@groovy.contracts.Invariant({ count >= 0 })
trait Counting { int count }
@TypeChecked(extensions = 'verification.VerifyChecker')
class C implements Counting {
    void dec() { count = count - 1 }
}
"""],
        // With a guard the implementing method preserves the trait invariant.
        [group: 'P-trait', name: 'trait @Invariant preserved by guarded implementing method', ok: true,
         src: HDR + """
@groovy.contracts.Invariant({ count >= 0 })
trait Counting { int count }
@TypeChecked(extensions = 'verification.VerifyChecker')
class C implements Counting {
    @Requires({ count > 0 })
    void dec() { count = count - 1 }
}
"""],
        // An implementing method gets full functional verification over the woven trait field, with the trait
        // invariant in force.
        [group: 'P-trait', name: 'implementing method functional proof over trait field', ok: true,
         src: HDR + """
@groovy.contracts.Invariant({ count >= 0 })
trait Counting { int count }
@TypeChecked(extensions = 'verification.VerifyChecker')
class C implements Counting {
    @Requires({ count >= 0 })
    @Ensures({ result == count + 1 })
    int next() { count + 1 }
}
"""],
        // Phase 122 — a trait's *concrete default method* is now verified too: its CONVERSION-snapshot body is
        // recovered, the woven `((FieldHelper) $self).Trait__f$get()/$set(v)` accessors are rewritten back to
        // plain field reads/writes, and the result is checked in the implementing class's context. So a trait
        // default method's @Ensures proves...
        [group: 'P-trait', name: 'trait default-method @Ensures is verified (proven)', ok: true,
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
trait Clamp {
    @Ensures({ result >= 0 })
    int nonNeg(int x) { x < 0 ? 0 : x }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class C implements Clamp { }
"""],
        // ...and a FALSE @Ensures on a trait default method refutes (caught via the implementer).
        [group: 'P-trait', name: 'false @Ensures on a trait default method refutes', ok: false, expect: 'Cannot prove postcondition',
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
trait Clamp {
    @Ensures({ result >= 1 })
    int nonNeg(int x) { x < 0 ? 0 : x }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class C implements Clamp { }
"""],
        // The full wrap-around counter: the trait owns the state, a wrapping `inc` (9 -> 0), a `getCount`, and
        // the invariant `count in 0..9`; the implementing class adds a wrapping `dec` (0 -> 9). BOTH the trait's
        // `inc` and the class's `dec` are proven to preserve the inherited invariant.
        [group: 'P-trait', name: 'wrap-around counter: trait inc + class dec both preserve invariant', ok: true,
         src: HDR + """
@groovy.contracts.Invariant({ 0 <= count && count <= 9 })
trait Counter {
    int count
    int getCount() { count }
    void inc() { count = (count == 9 ? 0 : count + 1) }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class WrapCounter implements Counter {
    void dec() { count = (count == 0 ? 9 : count - 1) }
}
"""],
        // A trait `inc` that forgets to wrap breaks the invariant at count == 9 — now caught (not skipped).
        [group: 'P-trait', name: 'non-wrapping trait inc breaks the invariant (refutes)', ok: false, expect: 'Cannot prove class invariant',
         src: HDR + """
@groovy.contracts.Invariant({ 0 <= count && count <= 9 })
trait Counter {
    int count
    void inc() { count = count + 1 }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class WrapCounter implements Counter { }
"""],
    ]
}
