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
 * 'P403 overrides in other files of the compilation' — the instance-method half of Phase 402. A call on an instance
 * receiver whose class sits in another file was already framed like a same-file one (its body, its contract, and the
 * open-world rule for a class a subclass compiled elsewhere may extend). But where the world IS closed — a sealed class,
 * or `closedWorld: true` — the search for the overrides a virtual call may dispatch to looked only in the caller's own
 * file: `Sub extends Counter` in `Sub.groovy`, overriding `bump()` to write `other`, went unseen, so `c.bump()` was
 * framed by `Counter.bump()` alone and `c.other == 5` "survived" it (`f(new Sub(other: 5))` returns 99). Unsound. The
 * searches for overrides, subtypes and their fields now span every class of the compilation.
 */
class G445_p403_overrides_in_other_files {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 403: the overrides a virtual call may dispatch to are searched across every file of the compilation, so a sealed class's permitted subclass, or a closed world's subclass, in another file frames the call and bounds its value (soundness fix)."

    static final String COUNTER = '''class Counter {
    int count
    int other
    void bump() { count = count + 1 }
    int get() { 1 }
}
'''

    static final String SEALED = '''sealed class Counter permits Sub {
    int count
    int other
    void bump() { count = count + 1 }
    int get() { 1 }
}
'''

    static final String SUB = '''class Sub extends Counter {
    void bump() { other = 99 }
    int get() { 2 }
}
'''

    static final String FINAL_SUB = '''final class Sub extends Counter {
    void bump() { other = 99 }
    int get() { 2 }
}
'''

    static final String FRAMED = '''class A {
                        @Requires({ c != null && c.other == 5 })
                        @Ensures({ result == 5 })
                        static int f(Counter c) {
                            c.bump()
                            return c.other
                        }
                    }'''

    static final String VALUED = '''class A {
                        @Requires({ c != null })
                        @Ensures({ result == 1 })
                        static int f(Counter c) {
                            c.get()
                        }
                    }'''

    static final List<Map> CASES = [

        // Unsound before: proved — Sub.groovy's override of bump() was no part of the call's frame
        [group: "P403 overrides in other files of the compilation", name: "a closed world's override in another file frames the call",
         expect: ["Cannot prove postcondition of f", "c.other (after a call)"],
         extraSources: ['Counter.groovy': COUNTER, 'Sub.groovy': SUB],
         src: tcw(FRAMED)],

        // … with the base class here and only the subclass elsewhere
        [group: "P403 overrides in other files of the compilation", name: "… the base class beside the caller, the override in another file",
         expect: ["Cannot prove postcondition of f", "c.other (after a call)"],
         extraSources: ['Sub.groovy': SUB],
         src: tcw(FRAMED + '\n' + COUNTER)],

        // Unsound before: a sealed class closes the world by itself, and its permitted subclass was in another file
        [group: "P403 overrides in other files of the compilation", name: "a sealed class's permitted subclass in another file",
         expect: ["Cannot prove postcondition of f", "c.other (after a call)"],
         extraSources: ['Counter.groovy': SEALED, 'Sub.groovy': FINAL_SUB],
         src: tc(FRAMED)],

        // A guard, not a fix: the value path refused this before too (Sub.get() returns 2) — it now asks the same search
        [group: "P403 overrides in other files of the compilation", name: "an override in another file bounds the call's value",
         expect: "Cannot prove postcondition of f",
         extraSources: ['Counter.groovy': SEALED, 'Sub.groovy': FINAL_SUB],
         src: tc(VALUED)],

        // Precision kept: with no override anywhere in the compilation, the body is still the call's frame and value
        [group: "P403 overrides in other files of the compilation", name: "with no override in the compilation, the body still frames and values the call",
         ok: true, extraSources: ['Counter.groovy': COUNTER],
         src: tcw(FRAMED + '\n' + VALUED.replace('class A', 'class B'))],
    ]
}
