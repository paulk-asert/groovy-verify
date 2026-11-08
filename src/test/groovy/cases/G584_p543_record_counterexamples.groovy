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

/** 'P543 record counterexamples' — Phase 543: a record parameter's int and boolean components, as the method reads
 *  them, are shown in a counterexample (`r.n = -1`), and the failing call builds the record with its canonical
 *  constructor (`f(new R(-1, 0))`) when every component is an int or a boolean. A class parameter's fields have shown
 *  since Phase 436; a record's showed nothing, and its call was never built. */
class G584_p543_record_counterexamples {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A record parameter\'s int and boolean components appear in the counterexample, and the failing call builds the record.'

    static String rec(String body, String record = 'record R(int n, int m) {}') {
        HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\nclass A {\n" + body.stripIndent() + "}\n" + record + '\n'
    }

    static final String G = 'P543 record counterexamples'

    static final List<Map> CASES = [
        [group: G, name: 'a component the method reads is in the counterexample, and the call builds the record',
         expect: ['Cannot prove postcondition of f', 'counterexample: r.n = -1', 'fails on: f(new R(-1, 0))'],
         src: rec('''
            @Requires({ r != null })
            @Ensures({ result == 1 })
            static int f(R r) {
                if (r.n < 0) return 0
                return 1
            }
            ''')],
        [group: G, name: 'two components, one pinned by the precondition',
         expect: ['counterexample: r.m = 4, r.n = 0', 'fails on: f(new R(0, 4))'],
         src: rec('''
            @Requires({ r != null && r.m > 3 })
            @Ensures({ result == 1 })
            static int f(R r) {
                if (r.n < r.m) return 0
                return 1
            }
            ''')],
        [group: G, name: 'a boolean component',
         expect: ['counterexample: r.on = true', 'fails on: f(new R(0, true))'],
         src: rec('''
            @Requires({ r != null })
            @Ensures({ result == 1 })
            static int f(R r) {
                if (r.on) return 0
                return 1
            }
            ''', 'record R(int n, boolean on) {}')],
        [group: G, name: 'records compared whole: the call builds the model\'s two values, not zeros',
         expect: ['fails on: f(new R(0, 0), new R(2, 0))'],
         src: rec('''
            @Requires({ r != null && s != null })
            @Ensures({ result == 1 })
            static int f(R r, R s) {
                if (r != s) return 0
                return 1
            }
            ''')],
        [group: G, name: 'a reassigned parameter: no component shown (a read is of the new value), the call built from the entry value',
         expect: ['fails on: f(new R(-2, 0))'], refute: 'r.n =',
         src: rec('''
            @Requires({ r != null })
            @Ensures({ result == 1 })
            static int f(R r) {
                r = new R(r.n + 1, 0)
                if (r.n < 0) return 0
                return 1
            }
            ''')],
        [group: G, name: 'a String component: the int one shown, no call (the model doesn\'t say which String fails)',
         expect: ['counterexample: r.n = -1'], refute: 'fails on:',
         src: rec('''
            @Requires({ r != null })
            @Ensures({ result == 1 })
            static int f(R r) {
                if (r.n < 0) return 0
                return 1
            }
            ''', 'record R(int n, String s) {}')],
        [group: G, name: 'a Pekko handler\'s message: the reply diagnostic names the path by its value',
         expect: ['onAdd may return without a reply on message.replyTo (pekko pack)', 'counterexample: message.n = -1, total = 0'],
         src: G582_p541_pekko_reply.tally(G582_p541_pekko_reply.REPLIES.replace('            message.replyTo.tell(-1)\n', ''))],
    ]
}
