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

/**
 * 'P333 int-range loop locals' — a loop VC reads a loop-written local at an arbitrary iteration as a fresh value
 * constrained only by the invariant, and only parameters and fields carried the JVM range (Phase 44c). So the solver
 * could answer with k = 2147483648, which no int holds: a false refutation of a true claim, and a repro nobody can
 * run. Every free value of an int or long param, field or local, on first mint or havoc, is now bounded to its type's
 * range (Encoder.assumeIntegralRange).
 */
class G377_p333_int_range_locals {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 333 int-range loop locals: an int or long local written by a loop is read at an arbitrary iteration as a fresh value, and that value is now bounded to the JVM range of its declared type, as parameters and fields already were. A claim that holds for every int (result <= Integer.MAX_VALUE) no longer refutes with k = 2147483648, and a counterexample for a wrong claim names a value an int can hold.'

    static final List<Map> CASES = [

        // The post-loop state: k is havocked to "anything with k >= 0", which used to include 2147483648.
        [group: 'P333 int-range loop locals', name: 'a loop-written int is in range after the loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result <= Integer.MAX_VALUE })
                        static int f(int n) {
                            int k = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && k >= 0 })
                            @Decreases({ n - i })
                            while (i < n) { k = k + 2; i = i + 1 }
                            return k
                        }
                    }''')],
        // An in-body exit reads k at some iteration.
        [group: 'P333 int-range loop locals', name: 'a loop-written int is in range at an in-body return', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result <= Integer.MAX_VALUE })
                        static int f(int n) {
                            int k = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && k >= 0 })
                            @Decreases({ n - i })
                            while (i < n) { if (k > 5) return k; k = k + 1; i = i + 1 }
                            return 0
                        }
                    }''')],
        // long locals get the 64-bit range.
        [group: 'P333 int-range loop locals', name: 'a loop-written long is in range after the loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result <= Long.MAX_VALUE })
                        static long f(int n) {
                            long k = 0L
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && k >= 0 })
                            @Decreases({ n - i })
                            while (i < n) { k = k + 2; i = i + 1 }
                            return k
                        }
                    }''')],
        // The bound is a fact, not a proof: a wrong claim still refutes.
        [group: 'P333 int-range loop locals', name: 'a wrong bound on a loop-written int still refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result < 1000 })
                        static int f(int n) {
                            int k = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && k >= 0 })
                            @Decreases({ n - i })
                            while (i < n) { k = k + 2; i = i + 1 }
                            return k
                        }
                    }''')],
        // The allocate bump loop without its slack bound: the index refutation now names an in-range k
        // (it used to report k = 2147483650).
        [group: 'P333 int-range loop locals', name: 'an out-of-bounds counterexample names an in-range index',
         expect: 'Possible IndexOutOfBoundsException', refute: 'k = 214748',
         src: tc('''class C {
                        @Requires({ a != null && left >= 0 })
                        static void bump(int[] a, int left) {
                            int k = 0
                            @Invariant({ 0 <= k && 0 <= left })
                            @Decreases({ left })
                            while (left > 0) { a[k] = a[k] + 1; k = k + 1; left = left - 1 }
                        }
                    }''')],
    ]
}
