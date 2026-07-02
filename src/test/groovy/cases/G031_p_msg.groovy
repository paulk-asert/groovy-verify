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

/** 'P-msg' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G031_p_msg {

    static final List<Map> CASES = [
        // PROBE-msg (Step 2 — Smith's producer/consumer info-flow, sequential/atomic, on SCALAR messages). The
        // §III mechanics assembled into one producer/consumer narrative: declassify (§III-E) to produce a Low
        // message, a public Low sink, and the secure-update (§III-A) when the control that classifies a message
        // flips. (The array buffer of messages is the deferred extension — info-flow Γ is scalar/name-based today.)
        [group: 'P-msg', name: 'produce: declassify a secret, then deliver it (verifies)', ok: true,
         src: tc('''class Messages {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void consume(@Label('Low') int msg) { }
                        static void produce(@Label('High') int secret) {
                            int msg = Declassify.to('Low', secret)   // §III-E controlled release → msg is Low
                            consume(msg)                             // Low → Low public sink: verifies
                        }
                    }''')],
        [group: 'P-msg', name: 'leak: deliver a secret without declassifying (refutes)', expect: 'information leak',
         src: tc('''class Messages {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void consume(@Label('Low') int msg) { }
                        static void leak(@Label('High') int secret) {
                            consume(secret)                          // High → Low sink: REFUTES
                        }
                    }''')],
        // §III-A secure-update: `released` controls a message's classification (Low once released, else High).
        // Flipping `released` to true while the message may still be secret drops its classification — refutes.
        [group: 'P-msg', name: 'secure-update: publishing an unreleased (secret) message refutes', expect: 'information leak',
         src: tc('''class Messages {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L level(boolean released) { released ? L.Low : L.High }
                        static void publish(boolean released, @Label(by = 'level') int msg) {
                            released = true                          // declassify-by-flag bug: REFUTES
                        }
                    }''')],
        // Raising a message's classification (released := false) is always secure. Verifies.
        [group: 'P-msg', name: 'secure-update: re-securing a message verifies', ok: true,
         src: tc('''class Messages {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L level(boolean released) { released ? L.Low : L.High }
                        static void hide(boolean released, @Label(by = 'level') int msg) {
                            released = false
                        }
                    }''')],
    ]
}
