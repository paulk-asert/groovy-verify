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

/** 'Dafny port' — 9 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G201_dafny_port {

    static final List<Map> CASES = [

        // ---------- Dafny ports — canonical tutorial / VSComp examples (external corpus) ----------
        // SumMax (VSComp 2010, Problem 1; Leino): compute sum and max in one pass and prove the
        // NONLINEAR bound `sum <= N * max`. The whole proof rides on the NIA loop invariant
        // `sum <= i * max` (Phase 48). Dafny's `returns (sum, max)` is a NAMED tuple, so the faithful
        // Groovy is the map-as-named-tuple idiom (Phase 83): `return [sum: …, max: …]` with
        // `result.sum` / `result.max` — self-documenting where positional `result.v1` / `result.v2`
        // aren't. With the return type declared `Map<String, Integer>`, the map values read back as
        // `Integer` inside the @Ensures closure (GROOVY-12071 restored the closure's generic types), so the
        // arithmetic `n * max` and the `<=` type-check with NO cast. Different shape from below_zero (a sum
        // biconditional) and max_element (a witnessed extremum): an INEQUALITY relating two running aggregates.
        [group: 'Dafny port', name: 'SumMax (VSComp10 P1): sum <= n*max', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && a.length == n && (0..<n).every { a[it] >= 0 } })
                       @Ensures({ result.sum <= n * result.max })
                       static Map<String, Integer> sumMax(int[] a, int n) {
                           int sum = 0, max = 0, i = 0
                           @Invariant({ 0 <= i && i <= n && sum <= i * max })
                           @Decreases({ n - i })
                           while (i < n) {
                               if (max < a[i]) max = a[i]
                               sum += a[i]
                               i++
                           }
                           [sum: sum, max: max]
                       }
                   }''')],
        // A wrong bound (`sum <= (n-1)*max`) refutes — the NIA invariant proves only the true bound.
        [group: 'Dafny port', name: 'SumMax wrong bound refutes', expect: 'fails on: sumMax(new int[0], 0)',
         src: tc('''class C {
                       @Requires({ 0 <= n && a.length == n && (0..<n).every { a[it] >= 0 } })
                       @Ensures({ result.sum <= (n - 1) * result.max })
                       static Map<String, Integer> sumMax(int[] a, int n) {
                           int sum = 0, max = 0, i = 0
                           @Invariant({ 0 <= i && i <= n && sum <= i * max })
                           @Decreases({ n - i })
                           while (i < n) {
                               if (max < a[i]) max = a[i]
                               sum += a[i]
                               i++
                           }
                           [sum: sum, max: max]
                       }
                   }''')],
        // Find (linear search, Dafny tutorial): the "not present => forall a[k] != key" spec — binary
        // search's postcondition WITHOUT sortedness, so it isolates exactly what binary search adds. The
        // in-loop early `return i` (Phase 49b) witnesses the found case; the invariant carries the
        // universal to the `return -1` path; preservation extends (0..<i) to (0..<i+1) in one
        // instantiation (no transitivity).
        [group: 'Dafny port', name: 'Find (linear search): index<0 => no element equals key', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 ==> result < a.length && a[result] == key })
                       @Ensures({ result < 0 ==> (0..<a.length).every { a[it] != key } })
                       static int find(int[] a, int key) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length && (0..<i).every { a[it] != key } })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               if (a[i] == key) return i
                               i = i + 1
                           }
                           return -1
                       }
                   }''')],
        // Claiming the found index holds a DIFFERENT key refutes (the early-return binds result = i with
        // a[i] == key, so a[result] != key is false on that path).
        [group: 'Dafny port', name: 'Find wrong found-claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Ensures({ result >= 0 ==> result < a.length && a[result] != key })
                       static int find(int[] a, int key) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length && (0..<i).every { a[it] != key } })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               if (a[i] == key) return i
                               i = i + 1
                           }
                           return -1
                       }
                   }''')],
        // BinarySearch (Dafny tutorial) — the VERBATIM textbook shape, `else return mid` inside the loop,
        // verifies END TO END: both postcondition directions, the excluded-region universal preserved
        // across the narrowing, every `a[mid]` bound, and termination. Sortedness is the NATIVE
        // `a.isSorted()` (Groovy 6 GDK; native int[]/long[] overloads) — it lowers to the same
        // flat multi-pattern axiom as `Sorted.ascending(a)`. Three fixes made it reachable: (1) that
        // multi-pattern axiom (deterministic gap fact), (2) a dischargeRegion fix so an obligation nested
        // in an `else if` keeps the `int mid = …` binding (the spurious mid=-1 IOOBE), and (3) Phase 49c —
        // lifting a `return` nested in a tail if/else chain into the top-level early-exit shape Phase 49b
        // handles. Matches Dafny's source structurally.
        [group: 'Dafny port', name: 'BinarySearch (textbook return mid): both directions + bounds + termination', ok: true,
         src: tc('''class C {
                       @Requires({ a.isSorted() })
                       @Ensures({ result < 0 ==> (0..<a.length).every { a[it] != value } })
                       @Ensures({ result >= 0 ==> result < a.length && a[result] == value })
                       static int binarySearch(int[] a, int value) {
                           int low = 0, high = a.length
                           @Invariant({ 0 <= low && low <= high && high <= a.length &&
                                        (0..<low).every { a[it] != value } && (high..<a.length).every { a[it] != value } })
                           @Decreases({ high - low })
                           while (low < high) {
                               int mid = low + (high - low).intdiv(2)
                               if (a[mid] < value) low = mid + 1
                               else if (value < a[mid]) high = mid
                               else return mid
                           }
                           return -1
                       }
                   }''')],
        // Drop the sortedness precondition and the proof genuinely fails — preservation refutes (without
        // `Sorted` the excluded-region invariant is not preserved by the narrowing). Confirms the proof
        // actually rests on sortedness, not luck.
        [group: 'Dafny port', name: 'BinarySearch without sortedness refutes',
         expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                       @Ensures({ result < 0 ==> (0..<a.length).every { a[it] != value } })
                       static int binarySearch(int[] a, int value) {
                           int low = 0, high = a.length
                           @Invariant({ 0 <= low && low <= high && high <= a.length &&
                                        (0..<low).every { a[it] != value } && (high..<a.length).every { a[it] != value } })
                           @Decreases({ high - low })
                           while (low < high) {
                               int mid = low + (high - low).intdiv(2)
                               if (a[mid] < value) low = mid + 1
                               else if (value < a[mid]) high = mid
                               else return mid
                           }
                           return -1
                       }
                   }''')],
        // The in-loop `return mid` genuinely exits with a[mid]==value: claiming the found index holds a
        // DIFFERENT value refutes (the lifted early-exit's @Ensures is checked on its own path).
        [group: 'Dafny port', name: 'BinarySearch wrong found-claim refutes', expect: 'Cannot prove',
         src: tc('''class C {
                       @Requires({ a.isSorted() })
                       @Ensures({ result >= 0 ==> a[result] != value })
                       static int binarySearch(int[] a, int value) {
                           int low = 0, high = a.length
                           @Invariant({ 0 <= low && low <= high && high <= a.length &&
                                        (0..<low).every { a[it] != value } && (high..<a.length).every { a[it] != value } })
                           @Decreases({ high - low })
                           while (low < high) {
                               int mid = low + (high - low).intdiv(2)
                               if (a[mid] < value) low = mid + 1
                               else if (value < a[mid]) high = mid
                               else return mid
                           }
                           return -1
                       }
                   }''')],
        // Focused regression for the dischargeRegion nested-`else if` fix: an index obligation in the
        // else-if condition must see a `mid` declared before the if. Before the fix this false-positived
        // a spurious IndexOutOfBounds (mid havoced → mid=-1).
        [group: 'Dafny port', name: 'nested else-if index obligation sees prior mid (no false IOOBE)', ok: true,
         src: tc('''class C {
                       static int f(int[] a, int value) {
                           int low = 0, high = a.length
                           @Invariant({ 0 <= low && low <= high && high <= a.length })
                           @Decreases({ high - low })
                           while (low < high) {
                               int mid = low + (high - low).intdiv(2)
                               if (a[mid] < value) low = mid + 1
                               else if (value < a[mid]) high = mid
                               else low = high
                           }
                           return low
                       }
                   }''')],
        // Phase 49c boundary: a `return` nested in an if/else chain that is NOT in tail position (a
        // statement follows it in the body) is out of the slice's scope — it skips LOUDLY rather than
        // being mis-modelled. The desugar only lifts a tail-position chain.
        [group: 'Dafny port', name: 'non-tail nested return skips loudly (honest)',
         expect: 'unsupported statement ReturnStatement',
         src: tc('''class C {
                       @Ensures({ result >= -1 })
                       static int f(int[] a, int value) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               if (a[i] == value) { if (i >= 0) return i }
                               i = i + 1
                           }
                           return -1
                       }
                   }''')],
    ]
}
