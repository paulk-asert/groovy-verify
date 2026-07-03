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

/** 'P193 catch-covered obligations' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G270_p193_catch_covered {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An implicit obligation inside a try whose handler covers its exception type is defined behaviour, not a bug: the throw transfers to the modelled catch path, so the obligation is suppressed (the old "fails on f(0)" refutation was factually wrong — f(0) returns the handler value). Curated and conservative: only exact types, their JDK supertypes (IllegalArgumentException over NumberFormatException; RuntimeException/Exception/Throwable), and only for sites inside the try block — a wrong-type handler, a handler-body obligation, or code after the try still refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 193: obligations covered by a matching catch ----------
        // THE canonical Java pattern: parseInt with the NumberFormatException handled. The Phase 47e
        // parse obligation used to refute this ("fails on p(null)") — but p never throws; it returns -1.
        [group: 'P193 catch-covered obligations', name: 'parseInt with NFE handled compiles clean', ok: true,
         src: tc('''class C {
             static int p(String s) {
                 try {
                     return Integer.parseInt(s)
                 } catch (NumberFormatException e) {
                     return -1
                 }
             }
         }''')],
        // Division with ArithmeticException handled — the obligation is the handler's whole purpose.
        [group: 'P193 catch-covered obligations', name: 'intdiv with ArithmeticException handled compiles clean', ok: true,
         src: tc('''class C {
             static int d(int n) {
                 try {
                     return 100.intdiv(n)
                 } catch (ArithmeticException e) {
                     return 0
                 }
             }
         }''')],
        // A JDK supertype covers: NumberFormatException <: IllegalArgumentException.
        [group: 'P193 catch-covered obligations', name: 'IllegalArgumentException covers the parse obligation', ok: true,
         src: tc('''class C {
             static int p(String s) {
                 try {
                     return Integer.parseInt(s)
                 } catch (IllegalArgumentException e) {
                     return -1
                 }
             }
         }''')],
        // A null dereference with the NPE handled.
        [group: 'P193 catch-covered obligations', name: 'deref with NPE handled compiles clean', ok: true,
         src: tc('''class C {
             static int len(String s) {
                 try {
                     return s.length()
                 } catch (NullPointerException e) {
                     return -1
                 }
             }
         }''')],
        // TEETH: a handler of the WRONG type covers nothing — the divide obligation still refutes
        // (an ArithmeticException would fly past a catch (NullPointerException)).
        [group: 'P193 catch-covered obligations', name: 'wrong-type handler does not suppress', expect: 'Division by zero',
         src: tc('''class C {
             static int d(int n) {
                 try {
                     return 100.intdiv(n)
                 } catch (NullPointerException e) {
                     return 0
                 }
             }
         }''')],
        // TEETH: an obligation in the HANDLER body is not inside the try — it still refutes.
        [group: 'P193 catch-covered obligations', name: 'handler-body obligation still fires', expect: 'Division by zero',
         src: tc('''class C {
             static int d(int n) {
                 try {
                     return n + 1
                 } catch (ArithmeticException e) {
                     return 100.intdiv(n)
                 }
             }
         }''')],
        // TEETH: position containment — the same obligation AFTER the try/catch still refutes.
        [group: 'P193 catch-covered obligations', name: 'obligation after the try still fires', expect: 'Division by zero',
         src: tc('''class C {
             static int d(int n) {
                 try {
                     if (n > 7) return 7
                 } catch (ArithmeticException e) {
                     return 0
                 }
                 return 100.intdiv(n)
             }
         }''')],
    ]
}
