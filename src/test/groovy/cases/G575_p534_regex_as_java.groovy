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

/** 'P534 regex as Java decides it' — Phase 534: {@code s.matches(re)} / {@code s ==~ re} as {@code java.util.regex}
 *  decides it. Each literal case's expected Java answer was measured with {@code Pattern.matches}; a "wrong answer"
 *  case claims the other one and must not verify. */
class G575_p534_regex_as_java {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Regex matches as Java decides them: escapes, line terminators, code points, \\b, (?i), (?s), \\Q…\\E, lazy quantifiers; the rest skips.'

    static final List<Map> CASES = [

        // ---------- line terminators and code points ----------
        [group: 'P534 regex as Java decides it', name: '\'\\n\' ~ \'.\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\n'.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\n\' ~ \'.\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\n'.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\x85\' ~ \'.\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u0085'.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\u2028\' ~ \'.\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u2028'.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\U0001f600\' ~ \'.\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\ud83d\\ude00'.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\U0001f600\' ~ \'.\': the wrong answer, false', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\ud83d\\ude00'.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\U0001f600\' ~ \'..\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\ud83d\\ude00'.matches('..') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\U0001f600\' ~ \'..\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\ud83d\\ude00'.matches('..') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\n\' ~ \'[^a]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\n'.matches('[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\n\' ~ \'\\\\S\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\n'.matches('\\\\S') ? 1 : 0 }
                    }''')],

        // ---------- escapes ----------
        [group: 'P534 regex as Java decides it', name: '\'t\' ~ \'\\\\t\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 't'.matches('\\\\t') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'t\' ~ \'\\\\t\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 't'.matches('\\\\t') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\t\' ~ \'\\\\t\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u0009'.matches('\\\\t') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\n\' ~ \'\\\\n\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\n'.matches('\\\\n') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'f\' ~ \'\\\\f\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'f'.matches('\\\\f') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'e\' ~ \'\\\\e\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'e'.matches('\\\\e') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\x1b\' ~ \'\\\\e\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u001b'.matches('\\\\e') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'x41\' ~ \'\\\\x41\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'x41'.matches('\\\\x41') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'\\\\x41\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'A'.matches('\\\\x41') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'u0041\' ~ \'\\\\u0041\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'u0041'.matches('\\\\u0041') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'\\\\u0041\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'A'.matches('\\\\u0041') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\' ~ \'\\\\a\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a'.matches('\\\\a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\x07\' ~ \'\\\\a\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u0007'.matches('\\\\a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'cA\' ~ \'\\\\cA\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'cA'.matches('\\\\cA') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\x01\' ~ \'\\\\cA\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u0001'.matches('\\\\cA') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'\\\\0101\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'A'.matches('\\\\0101') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\x08\' ~ \'\\\\010\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u0008'.matches('\\\\010') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'\\\\x{41}\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'A'.matches('\\\\x{41}') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a.b\' ~ \'a\\\\.b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a.b'.matches('a\\\\.b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'axb\' ~ \'a\\\\.b\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'axb'.matches('a\\\\.b') ? 1 : 0 }
                    }''')],

        // ---------- classes ----------
        [group: 'P534 regex as Java decides it', name: '\'d\' ~ \'[\\\\d]\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'd'.matches('[\\\\d]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'d\' ~ \'[\\\\d]\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'd'.matches('[\\\\d]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'5\' ~ \'[\\\\d]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '5'.matches('[\\\\d]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'x\' ~ \'[\\\\w]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'x'.matches('[\\\\w]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\\\\' ~ \'[\\\\^]\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\\\'.matches('[\\\\^]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'^\' ~ \'[\\\\^]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '^'.matches('[\\\\^]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\']\' ~ \'[\\\\]]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { ']'.matches('[\\\\]]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\x0b\' ~ \'\\\\s\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u000b'.matches('\\\\s') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'-\' ~ \'[a-]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '-'.matches('[a-]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\xe9\' ~ \'\\\\w\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u00e9'.matches('\\\\w') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\u0660\' ~ \'\\\\d\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u0660'.matches('\\\\d') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\xa0\' ~ \'\\\\s\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u00a0'.matches('\\\\s') ? 1 : 0 }
                    }''')],

        // ---------- quoting, lazy and groups ----------
        [group: 'P534 regex as Java decides it', name: '\'a.b\' ~ \'\\\\Qa.b\\\\E\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a.b'.matches('\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'Qa.bE\' ~ \'\\\\Qa.b\\\\E\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'Qa.bE'.matches('\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'a\\\\Qb\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ab'.matches('a\\\\Qb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aaa\' ~ \'a*?\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'aaa'.matches('a*?') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aaa\' ~ \'a+?a\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'aaa'.matches('a+?a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aa\' ~ \'a{1,2}?a\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'aa'.matches('a{1,2}?a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\' ~ \'(?:a)\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a'.matches('(?:a)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'(?<x>a)b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ab'.matches('(?<x>a)b') ? 1 : 0 }
                    }''')],

        // ---------- anchors ----------
        [group: 'P534 regex as Java decides it', name: '\'a\\n\' ~ \'a$\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'a\\n'.matches('a$') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\' ~ \'^$\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { ''.matches('^$') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\' ~ \'a|^b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a'.matches('a|^b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'b\' ~ \'a|^b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'b'.matches('a|^b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\' ~ \'a$|b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a'.matches('a$|b') ? 1 : 0 }
                    }''')],

        // ---------- word boundaries ----------
        [group: 'P534 regex as Java decides it', name: '\'cat\' ~ \'\\\\bcat\\\\b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'cat'.matches('\\\\bcat\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'cat\' ~ \'\\\\bcat\\\\b\': the wrong answer, false', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'cat'.matches('\\\\bcat\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a cat b\' ~ \'.*\\\\bcat\\\\b.*\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a cat b'.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'concat\' ~ \'.*\\\\bcat\\\\b.*\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'concat'.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'concat\' ~ \'.*\\\\bcat\\\\b.*\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'concat'.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'cats\' ~ \'.*\\\\bcat\\\\b.*\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'cats'.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'cat!\' ~ \'cat\\\\b!\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'cat!'.matches('cat\\\\b!') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'a\\\\Bb\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ab'.matches('a\\\\Bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a b\' ~ \'a\\\\B b\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'a b'.matches('a\\\\B b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\' ~ \'\\\\b\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { ''.matches('\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\' ~ \'\\\\B\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { ''.matches('\\\\B') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\' ~ \'\\\\b\\\\ba\\\\b\\\\b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a'.matches('\\\\b\\\\ba\\\\b\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\' ~ \'\\\\b\\\\Ba\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'a'.matches('\\\\b\\\\Ba') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'a\\\\b\\\\Bb\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'ab'.matches('a\\\\b\\\\Bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a-b\' ~ \'a\\\\b-\\\\bb\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a-b'.matches('a\\\\b-\\\\bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'_x\' ~ \'\\\\b_x\\\\b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '_x'.matches('\\\\b_x\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'a\\\\b|b\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'ab'.matches('a\\\\b|b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\xe9\' ~ \'\\\\b.\\\\b\': Java: true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u00e9'.matches('\\\\b.\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\xe9\' ~ \'\\\\B.\\\\B\': Java: false', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u00e9'.matches('\\\\B.\\\\B') ? 1 : 0 }
                    }''')],

        // ---------- flags ----------
        [group: 'P534 regex as Java decides it', name: '\'aB\' ~ \'a(?i)b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'aB'.matches('a(?i)b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ABC\' ~ \'(?i)abc\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ABC'.matches('(?i)abc') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ABC\' ~ \'(?i)abc\': the wrong answer, false', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'ABC'.matches('(?i)abc') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aBc\' ~ \'a(?i)bc\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'aBc'.matches('a(?i)bc') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'Abc\' ~ \'a(?i)bc\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'Abc'.matches('a(?i)bc') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'Abc\' ~ \'a(?i)bc\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'Abc'.matches('a(?i)bc') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aBC\' ~ \'a(?i:b)c\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'aBC'.matches('a(?i:b)c') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aBc\' ~ \'a(?i:b)c\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'aBc'.matches('a(?i:b)c') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'AB\' ~ \'(?i)a(?-i)b\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'AB'.matches('(?i)a(?-i)b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'Ab\' ~ \'(?i)a(?-i)b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'Ab'.matches('(?i)a(?-i)b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'Q\' ~ \'(?i)[a-z]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'Q'.matches('(?i)[a-z]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'[\' ~ \'(?i)[Z-a]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '['.matches('(?i)[Z-a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'z\' ~ \'(?i)[Z-a]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'z'.matches('(?i)[Z-a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'(?i)[Z-a]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'A'.matches('(?i)[Z-a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'B\' ~ \'(?i)[Z-a]\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'B'.matches('(?i)[Z-a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'B\' ~ \'(?i)[Z-a]\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'B'.matches('(?i)[Z-a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'(?i)[^a]\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'A'.matches('(?i)[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'(?i)[^a]\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'A'.matches('(?i)[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'B\' ~ \'(?i)[^a]\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'B'.matches('(?i)[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\xc9\' ~ \'(?i)\\xe9\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u00c9'.matches('(?i)\\u00e9') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'K\' ~ \'(?i)\\\\x6b\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'K'.matches('(?i)\\\\x6b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\u212a\' ~ \'(?i)k\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u212a'.matches('(?i)k') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\u212a\' ~ \'(?i)k\': the wrong answer, true', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u212a'.matches('(?i)k') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'AB\' ~ \'(a(?i)b)|c\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'AB'.matches('(a(?i)b)|c') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'C\' ~ \'a(?i)b|c\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'C'.matches('a(?i)b|c') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aC\' ~ \'(a(?i)b)c\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'aC'.matches('(a(?i)b)c') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aBC\' ~ \'(a(?i)b)c\': Java: false', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'aBC'.matches('(a(?i)b)c') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\n\' ~ \'(?s).\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\n'.matches('(?s).') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\n\' ~ \'(?s:.)\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\n'.matches('(?s:.)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'\\na\' ~ \'(?s:.).\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\na'.matches('(?s:.).') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A.B\' ~ \'(?i)\\\\Qa.b\\\\E\': Java: true', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'A.B'.matches('(?i)\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],

        // ---------- outside the fragment ----------
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'a^b\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'ab'.matches('a^b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'a$b\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'ab'.matches('a$b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\\n\' ~ \'a$\\n\': Java: true', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'a\\n'.matches('a$\\n') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'pL\' ~ \'\\\\pL\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'pL'.matches('\\\\pL') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'\\\\A\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'A'.matches('\\\\A') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'z\' ~ \'\\\\z\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'z'.matches('\\\\z') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'Z\' ~ \'\\\\Z\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'Z'.matches('\\\\Z') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'G\' ~ \'\\\\G\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'G'.matches('\\\\G') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aa\' ~ \'(a)\\\\1\': Java: true', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'aa'.matches('(a)\\\\1') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'h\' ~ \'\\\\h\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'h'.matches('\\\\h') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'v\' ~ \'\\\\v\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'v'.matches('\\\\v') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'R\' ~ \'\\\\R\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'R'.matches('\\\\R') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'&\' ~ \'[a&&b]\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '&'.matches('[a&&b]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'8\' ~ \'\\\\N{DIGIT EIGHT}\': Java: true', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '8'.matches('\\\\N{DIGIT EIGHT}') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\' a\' ~ \' \\\\b\\\\B?a\': Java: true', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { ' a'.matches(' \\\\b\\\\B?a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'aaa\' ~ \'a*+a\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'aaa'.matches('a*+a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'(?=a)ab\': Java: true', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ab'.matches('(?=a)ab') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'(?>a)b\': Java: true', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ab'.matches('(?>a)b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'(^a)b\': Java: true', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ab'.matches('(^a)b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'A\' ~ \'(?u)a\': Java: false', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'A'.matches('(?u)a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'0\' ~ \'\\\\0\': a malformed pattern (throws)', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '0'.matches('\\\\0') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'b\' ~ \'[z-a]\': a malformed pattern (throws)', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'b'.matches('[z-a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'a\' ~ \'a{2,1}\': a malformed pattern (throws)', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'a'.matches('a{2,1}') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '\'ab\' ~ \'a\\\\Eb\': a malformed pattern (throws)', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'ab'.matches('a\\\\Eb') ? 1 : 0 }
                    }''')],

        // ---------- a String parameter ----------
        // A code-point atom is exact over non-surrogate BMP strings; outside that the match is Java's (an unknown
        // predicate), and a failure resting on such a string names no call.
        [group: 'P534 regex as Java decides it', name: 'a parameter matching . has length 1: false (an emoji has 2), no call named',
         expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with a surrogate or supplementary character'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s != null && s.matches('.') })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.length() }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter matching a.b is not a, newline, b', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.matches('a.b') })
                        @Ensures({ result })
                        static boolean f(String s) { s != 'a\\nb' }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter matching \\\\t is a tab', ok: true,
         src: tc('''class C {
                        @Ensures({ result })
                        static boolean f(String s) { !(s != null && s.matches('\\\\t')) || s == '\\t' }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '(?i)yes has length 3', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s ==~ /(?i)yes/ })
                        @Ensures({ result == 3 })
                        static int f(String s) { s.length() }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '(?i)yes need not be yes: refuted with a run',
         expect: ['Cannot prove postcondition', 'fails on: f("'],
         src: tc('''class C {
                        @Requires({ s != null && s ==~ /(?i)yes/ })
                        @Ensures({ result })
                        static boolean f(String s) { s == 'yes' }
                    }''')],
        [group: 'P534 regex as Java decides it', name: '(?i)[a-c]{2} has length 2', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.matches('(?i)[a-c]{2}') })
                        @Ensures({ result == 2 })
                        static int f(String s) { s.length() }
                    }''')],
        // \b is exact over ASCII strings only (JDK 19 made its word characters ASCII; before, isLetterOrDigit): a
        // true claim over all strings isn't proved, and no call is named
        [group: 'P534 regex as Java decides it', name: '\\\\bcat\\\\b is cat: not proved past ASCII, no call named',
         expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with a non-ASCII character'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s != null && s.matches('\\\\bcat\\\\b') })
                        @Ensures({ result })
                        static boolean f(String s) { s == 'cat' }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a word-bounded cat in a lower-case ASCII parameter is not concat', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.matches('[a-z ]*') && s.matches('.*\\\\bcat\\\\b.*') })
                        @Ensures({ result })
                        static boolean f(String s) { s != 'concat' && s != 'cats' }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a quantified . over a list (the unknown is a predicate of the element)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.every { it != null && it.matches('.') } })
                        @Ensures({ result })
                        static boolean f(List<String> xs) { true }
                    }''')],

        // ---------- the same forms over a parameter pinned by @Requires (the translation, not Pattern.matches) ----------
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'.\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'.\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\r\' ~ \'.\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\r' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\r\' ~ \'.\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\r' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\x85\' ~ \'.\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\u0085' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\x85\' ~ \'.\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\u0085' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\u2028\' ~ \'.\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\u2028' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\u2028\' ~ \'.\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\u2028' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a\' ~ \'.\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a\' ~ \'.\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\xe9\' ~ \'.\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\u00e9' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\xe9\' ~ \'.\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\u00e9' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\U0001f600\' ~ \'.\': Java\'s answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\ud83d\\ude00' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\U0001f600\' ~ \'.\': the wrong answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\ud83d\\ude00' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\U0001f600\' ~ \'..\': Java\'s answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\ud83d\\ude00' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('..') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\U0001f600\' ~ \'..\': the wrong answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\ud83d\\ude00' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('..') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a.b\' ~ \'\\\\Qa.b\\\\E\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a.b' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a.b\' ~ \'\\\\Qa.b\\\\E\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a.b' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'Qa.bE\' ~ \'\\\\Qa.b\\\\E\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'Qa.bE' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'Qa.bE\' ~ \'\\\\Qa.b\\\\E\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'Qa.bE' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'[^a]\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'[^a]\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'\\\\D\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\D') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'\\\\D\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\D') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'\\\\S\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\S') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'\\\\S\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\S') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a b\' ~ \'a\\\\b b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a b' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\b b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a b\' ~ \'a\\\\b b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a b' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\b b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cat\' ~ \'\\\\bcat\\\\b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'cat' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\bcat\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cat\' ~ \'\\\\bcat\\\\b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'cat' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\bcat\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a cat b\' ~ \'.*\\\\bcat\\\\b.*\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a cat b' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a cat b\' ~ \'.*\\\\bcat\\\\b.*\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a cat b' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'concat\' ~ \'.*\\\\bcat\\\\b.*\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'concat' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'concat\' ~ \'.*\\\\bcat\\\\b.*\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'concat' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cats\' ~ \'.*\\\\bcat\\\\b.*\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'cats' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cats\' ~ \'.*\\\\bcat\\\\b.*\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'cats' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('.*\\\\bcat\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cat!\' ~ \'cat\\\\b!\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'cat!' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('cat\\\\b!') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cat!\' ~ \'cat\\\\b!\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'cat!' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('cat\\\\b!') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\Bb\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\Bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\Bb\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\Bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a b\' ~ \'a\\\\B b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a b' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\B b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a b\' ~ \'a\\\\B b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a b' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\B b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\' ~ \'\\\\b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\' ~ \'\\\\b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\' ~ \'\\\\B\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\B') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\' ~ \'\\\\B\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\B') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a\' ~ \'\\\\b\\\\ba\\\\b\\\\b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\b\\\\ba\\\\b\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a\' ~ \'\\\\b\\\\ba\\\\b\\\\b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\b\\\\ba\\\\b\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a\' ~ \'\\\\b\\\\Ba\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\b\\\\Ba') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a\' ~ \'\\\\b\\\\Ba\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\b\\\\Ba') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\b\\\\Bb\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\b\\\\Bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\b\\\\Bb\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\b\\\\Bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \' a\' ~ \' \\\\b\\\\B?a\': Java\'s answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ s == ' a' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches(' \\\\b\\\\B?a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \' a\' ~ \' \\\\b\\\\B?a\': the wrong answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ s == ' a' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches(' \\\\b\\\\B?a') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a-b\' ~ \'a\\\\b-\\\\bb\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'a-b' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\b-\\\\bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a-b\' ~ \'a\\\\b-\\\\bb\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'a-b' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\b-\\\\bb') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'_x\' ~ \'\\\\b_x\\\\b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '_x' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\b_x\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'_x\' ~ \'\\\\b_x\\\\b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '_x' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\b_x\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'\\xe9\' ~ \'\\\\b.\\\\b\': Java\'s answer (JDK-dependent: false from JDK 19)', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u00e9'.matches('\\\\b.\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'\\xe9\' ~ \'\\\\b.\\\\b\': the wrong answer (JDK-dependent: false from JDK 19)', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u00e9'.matches('\\\\b.\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\xe9\' ~ \'\\\\b.\\\\b\': Java\'s answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\u00e9' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\b.\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\xe9\' ~ \'\\\\b.\\\\b\': the wrong answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\u00e9' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\b.\\\\b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'\\xe9\' ~ \'\\\\B.\\\\B\': Java\'s answer (JDK-dependent)', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\u00e9'.matches('\\\\B.\\\\B') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'\\xe9\' ~ \'\\\\B.\\\\B\': the wrong answer (JDK-dependent)', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\u00e9'.matches('\\\\B.\\\\B') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\xe9\' ~ \'\\\\B.\\\\B\': Java\'s answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\u00e9' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('\\\\B.\\\\B') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\xe9\' ~ \'\\\\B.\\\\B\': the wrong answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == '\\u00e9' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('\\\\B.\\\\B') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a \\xe9\' ~ \'a\\\\b.*\': Java\'s answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == 'a \\u00e9' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'a \\xe9\' ~ \'a\\\\b.*\': the wrong answer', expect: ['Cannot prove postcondition', 'no failing call: the failure rests on a string with'], refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s == 'a \\u00e9' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\b.*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'A\' ~ \'(?i)[^a]\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'A' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('(?i)[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'A\' ~ \'(?i)[^a]\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'A' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('(?i)[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'B\' ~ \'(?i)[^a]\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'B' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('(?i)[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'B\' ~ \'(?i)[^a]\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'B' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('(?i)[^a]') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'(?s).\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('(?s).') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'(?s).\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('(?s).') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'(?s:.)\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('(?s:.)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\n\' ~ \'(?s:.)\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\n' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('(?s:.)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\na\' ~ \'(?s:.).\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == '\\na' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('(?s:.).') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'\\na\' ~ \'(?s:.).\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == '\\na' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('(?s:.).') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'A.B\' ~ \'(?i)\\\\Qa.b\\\\E\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'A.B' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('(?i)\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'A.B\' ~ \'(?i)\\\\Qa.b\\\\E\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'A.B' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('(?i)\\\\Qa.b\\\\E') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\b|b\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('a\\\\b|b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'ab\' ~ \'a\\\\b|b\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s == 'ab' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('a\\\\b|b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal "\'7" ~ \'\\\\0477\': Java\'s answer', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { '\\'7'.matches('\\\\0477') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal "\'7" ~ \'\\\\0477\': the wrong answer', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { '\\'7'.matches('\\\\0477') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'cat\' ~ \'(\\\\bcat)\': Java\'s answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'cat'.matches('(\\\\bcat)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'cat\' ~ \'(\\\\bcat)\': the wrong answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'cat'.matches('(\\\\bcat)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cat\' ~ \'(\\\\bcat)\': Java\'s answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ s == 'cat' })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches('(\\\\bcat)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a parameter \'cat\' ~ \'(\\\\bcat)\': the wrong answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ s == 'cat' })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.matches('(\\\\bcat)') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'abb\' ~ \'\\\\Qab\\\\E*\': Java\'s answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'abb'.matches('\\\\Qab\\\\E*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'abb\' ~ \'\\\\Qab\\\\E*\': the wrong answer', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'abb'.matches('\\\\Qab\\\\E*') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'ab\' ~ \'(?<a-b>a)b\': claim 0 (it throws)', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { 'ab'.matches('(?<a-b>a)b') ? 1 : 0 }
                    }''')],
        [group: 'P534 regex as Java decides it', name: 'a literal \'ab\' ~ \'(?<a-b>a)b\': claim 1 (it throws)', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { 'ab'.matches('(?<a-b>a)b') ? 1 : 0 }
                    }''')],
        // Each pattern has its own unknown predicate outside the guard: with one shared, '..' true and '.' false would
        // exclude every string past the BMP and prove a length an emoji plus a letter breaks
        [group: 'P534 regex as Java decides it', name: 'two code-point patterns outside the guard are independent', expect: 'Cannot prove postcondition', refute: 'fails on',
         src: tc('''class C {
                        @Requires({ s != null && s.matches('..') && !s.matches('.') })
                        @Ensures({ result == 2 })
                        static int f(String s) { s.length() }
                    }''')],
    ]
}
