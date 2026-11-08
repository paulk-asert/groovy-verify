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
 * 'P544 closure bodies' — a closure's body runs when the closure is called, as a path of its own. Found probing the
 * Pekko functional style, whose handlers are closures. Two silent holes: an {@code assert} inside a closure was never
 * checked (the value-flow pass collected asserts at the method's level only), and a call's precondition inside one
 * was checked in the state where the closure is written (Phase 372's havoc reached the implicit obligations, not this
 * pass). And the closure's own locals, guards and early returns were unknown at its sites: `{ int n = c + 1; g(n) }`
 * showed `n = 0`, failing on a call that doesn't fail. Each pass now walks a closure's body from the state where it
 * is written, then the havoc of what may have changed by the time it runs, then its own statements.
 */
class G585_p544_closure_bodies {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 544: a closure body is checked as a path of its own, from where the closure is written through the havoc of what may change before it runs; its asserts are checked, its calls\' preconditions read the state it runs in, and its locals and guards hold at its sites.'

    static final String G = 'P544 closure bodies'

    /** A class with {@code g}, needing a positive argument, and {@code body}. */
    static String withG(String body) {
        tc("""class C {
    @Requires({ k > 0 })
    static int g(int k) { k }

${body}
}""")
    }

    static final String IN_CLOSURE = 'no failing call: the failure is inside a closure'

    static final List<Map> CASES = [
        // ---------- an assert inside a closure: never checked before ----------
        // Before: compiled cleanly. The first call fails its assert.
        [group: G, name: 'an assert inside a closure is checked', expect: ['Assertion may not hold: (c < 0)', 'counterexample: c = 0', IN_CLOSURE],
         refute: 'fails on',
         src: withG('''    static void f(int c) {
        3.times { assert c < 0 }
    }''')],
        // Before: compiled cleanly.
        [group: G, name: 'one in a closure returned to run later too', expect: ['Assertion may not hold: (c < 0)', IN_CLOSURE],
         src: withG('''    static Closure f(int c) {
        return { -> assert c < 0 }
    }''')],
        [group: G, name: 'one that holds verifies', ok: true,
         src: withG('''    @Requires({ c >= 0 })
    static void f(int c) {
        3.times { assert c >= 0 }
    }''')],
        [group: G, name: 'the closure\'s own guard holds at its assert', ok: true,
         src: withG('''    static void f(int c) {
        3.times { if (c > 0) assert c >= 1 }
    }''')],
        [group: G, name: 'an assert in a closure nested in another is skipped, loudly',
         expect: 'Skipped assertion safety check (it is inside a closure whose body the verifier can\'t follow as a path',
         src: withG('''    static void f(int c) {
        2.times { 3.times { assert c < 0 } }
    }''')],
        [group: G, name: 'one in a method outside the value-flow fragment is skipped, loudly, as before',
         expect: 'Skipped assertion safety check (the method body is outside the value-flow fragment',
         src: withG('''    static Closure f(int c) {
        return { -> int n = c + 1; assert n > c }
    }''')],

        // ---------- a call's precondition: read in the state the closure runs in ----------
        // Before: compiled cleanly. r() calls g(0).
        [group: G, name: 'a stored closure called after a write: the precondition reads the value then',
         expect: ['Cannot prove precondition of g at this call site', 'd (when the closure runs) = 0', IN_CLOSURE], refute: 'fails on',
         src: withG('''    static int f() {
        int d = 1
        Closure<Integer> r = { -> g(d) }
        d = 0
        r()
    }''')],
        // Before: compiled cleanly. The second call is g(0).
        [group: G, name: 'a closure that writes what its call reads',
         expect: ['Cannot prove precondition of g at this call site', 'd (when the closure runs) = 0'],
         src: withG('''    static void f() {
        int d = 1
        3.times { g(d); d-- }
    }''')],

        // ---------- the closure's own path ----------
        // Before: `counterexample: c = 0, n = 0` and `fails on: f(0)`, a call that doesn't fail.
        [group: G, name: 'a local the closure declares holds at its call', ok: true,
         src: withG('''    @Requires({ c >= 0 })
    static void f(int c) {
        3.times { int n = c + 1; g(n) }
    }''')],
        [group: G, name: '… in a stored closure too', ok: true,
         src: withG('''    @Requires({ c >= 0 })
    static void f(int c) {
        Closure r = { -> int n = c + 1; g(n) }
        r()
    }''')],
        // Before: `counterexample: c = 0`, `fails on: f(0)`.
        [group: G, name: 'an early return in the closure guards what follows it', ok: true,
         src: withG('''    static void f(int c) {
        3.times { if (c <= 0) return; g(c) }
    }''')],
        // Before: `Division by zero … n (when the closure runs) = 0`.
        [group: G, name: 'an implicit obligation sees the closure\'s local', ok: true,
         src: withG('''    @Requires({ c >= 0 })
    static int f(int c) {
        int s = 0
        3.times { int n = c + 1; s = 100.intdiv(n) }
        s
    }''')],
        [group: G, name: 'a closure in an && keeps its left operand', ok: true,
         src: withG('''    static boolean f(List<Integer> xs) {
        xs != null && (0..<3).every { int i -> xs.size() >= 0 }
    }''')],
        [group: G, name: '… and without it, refuted', expect: ['Possible NullPointerException', IN_CLOSURE],
         src: withG('''    static boolean f(List<Integer> xs) {
        (0..<3).every { int i -> xs.size() >= 0 }
    }''')],
        [group: G, name: 'a local that does break the precondition: refuted',
         expect: ['Cannot prove precondition of g at this call site', 'counterexample: c = 0', IN_CLOSURE],
         src: withG('''    @Requires({ c >= 0 })
    static void f(int c) {
        3.times { int n = c - 1; g(n) }
    }''')],
    ]
}
