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

/** 'P131 dimensions' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G005_p131_dimensions {

    static final List<Map> CASES = [

        // ---------- Phase 131: JSR 385 dimensional analysis (C₀ — dimension-only) ----------
        // (The non-null @Requires isolate the dimensional property from the orthogonal null-deref obligation
        // the receiver would otherwise trigger — real code gets both checks; here we exercise dimensions.)
        // The blog's `div` extension: length / time IS velocity (1,0,-1), so the cast verifies.
        [group: 'P131 dimensions', name: 'length/time as Quantity<Speed> verifies', ok: true,
         src: HDR + UOM + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ q != null && t != null }) static Quantity<Speed> v(Quantity<Length> q, Quantity<Time> t) { q.divide(t) as Quantity<Speed> } }'],
        // The multiply typo: length * time is (1,0,1) — NOT velocity — so the cast refutes (the unchecked-cast bug).
        [group: 'P131 dimensions', name: 'length*time as Quantity<Speed> refutes', expect: 'Dimensional mismatch',
         src: HDR + UOM + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ q != null && t != null }) static Quantity<Speed> v(Quantity<Length> q, Quantity<Time> t) { q.multiply(t) as Quantity<Speed> } }'],
        // length / time² = acceleration (1,0,-2) verifies (composition through two divides).
        [group: 'P131 dimensions', name: 'length/time/time as Quantity<Acceleration> verifies', ok: true,
         src: HDR + UOM + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ q != null && t != null }) static Quantity<Acceleration> a(Quantity<Length> q, Quantity<Time> t) { q.divide(t).divide(t) as Quantity<Acceleration> } }'],
        // length*length is Area (2,0,0); casting it to Volume (3,0,0) refutes.
        [group: 'P131 dimensions', name: 'length*length as Quantity<Volume> refutes', expect: 'Dimensional mismatch',
         src: HDR + UOM + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ a != null && b != null }) static Quantity<Volume> bad(Quantity<Length> a, Quantity<Length> b) { a.multiply(b) as Quantity<Volume> } }'],
        // length*length as Area verifies.
        [group: 'P131 dimensions', name: 'length*length as Quantity<Area> verifies', ok: true,
         src: HDR + UOM + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ a != null && b != null }) static Quantity<Area> area(Quantity<Length> a, Quantity<Length> b) { a.multiply(b) as Quantity<Area> } }'],
        // Scalar multiply keeps the dimension: a length times a number is still a length.
        [group: 'P131 dimensions', name: 'length * scalar stays Length', ok: true,
         src: HDR + UOM + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ q != null }) static Quantity<Length> scale(Quantity<Length> q) { q.multiply(2) as Quantity<Length> } }'],
    ]
}
