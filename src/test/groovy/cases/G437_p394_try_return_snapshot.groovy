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
 * 'P394 try-return snapshot' — a return inside a try evaluates its value before the finally runs, so a finally that
 * writes what it reads doesn't change what is returned (`int k = n; try { return k } finally { k = 0 }` returns n).
 * Phase 389 skipped that shape loudly; the value is now snapshotted into a temporary before the finally, and that is
 * what the method returns — for an int-like value, which the path's temporary holds.
 */
class G437_p394_try_return_snapshot {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 394: a try's return value is snapshotted before a finally that writes what it reads, so the postcondition sees the value returned (int-like values)."

    static final String POST = "Cannot prove postcondition of f"

    static final List<Map> CASES = [

        // Before: `'finally' writes what the try's return reads` — a loud skip.
        [group: "P394 try-return snapshot", name: "the value a return read is kept through a finally that writes it",
         ok: true,
         src: tc('''class A {
                            @Ensures({ result == n })
                            static int f(int n) {
                                int k = n
                                try {
                                    return k
                                } finally {
                                    k = 0
                                }
                            }
                        }''')],

        [group: "P394 try-return snapshot", name: "… so a claim about the finally's write refutes",
         expect: [POST, "fails on: f("],
         src: tc('''class A {
                            @Ensures({ result == 0 })
                            static int f(int n) {
                                int k = n
                                try {
                                    return k
                                } finally {
                                    k = 0
                                }
                            }
                        }''')],

        [group: "P394 try-return snapshot", name: "… an expression over it too",
         ok: true,
         src: tc('''class A {
                            @Ensures({ result == n + 1 })
                            static int f(int n) {
                                int k = n
                                try {
                                    return k + 1
                                } finally {
                                    k = k * 5
                                }
                            }
                        }''')],

        [group: "P394 try-return snapshot", name: "… a long",
         ok: true,
         src: tc('''class A {
                            @Ensures({ result == n })
                            static long f(long n) {
                                long k = n
                                try {
                                    return k
                                } finally {
                                    k = 0L
                                }
                            }
                        }''')],

        // The path's temporary is an Int: a boolean, String or collection snapshot isn't taken.
        [group: "P394 try-return snapshot", name: "a non-integer return value still skips loudly",
         expect: ["'finally' writes what the try's return reads, a value that isn't an integer"],
         src: tc('''class A {
                            @Ensures({ result })
                            static boolean f() {
                                boolean k = true
                                try {
                                    return k
                                } finally {
                                    k = false
                                }
                            }
                        }''')],
    ]
}
