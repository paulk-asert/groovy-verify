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
 * 'P547 false failing calls' — Phase 547: two ways a `fails on:` line named a call that doesn't fail, found probing the
 * Pekko guardian side (a guardian held in a local). Both rest on a value no run is known to produce. (A) The region
 * replay, stopping at a call it can't frame whose value is assigned (`Object g = mk()`), labelled the havoc after it
 * 'after a loop', the one label that keeps the call. (B) A call's reference result whose nullity its contract never
 * mentions was a free flag the model could set, unmarked.
 */
class G588_p547_false_failing_calls {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 547: a failure resting on the value after an assigned call the replay can\'t frame, or on a call\'s null its contract never mentions, names no failing call: no run is known to reach it.'

    static final String G = 'P547 false failing calls'

    static String r(String body) { tc("class R {\n${body}\n}") }

    static final String NPE = 'Possible NullPointerException'
    static final String HAVOC = 'no failing call: the failure rests on what a statement writes inside it'
    static final String NULL_NOTE = 'no failing call: the failure rests on sb(…) returning null, which its contract doesn\'t rule out but no run is known to do — an @Ensures({ result != null }) on sb would settle it'

    static final List<Map> CASES = [
        // ---------- (A) after an assigned call the replay can't frame ----------
        // Before: `fails on: run()`; sb returns a new StringBuilder, so run() never fails.
        [group: G, name: 'a value after an assigned call the replay can\'t frame names no call',
         expect: [NPE, 'obligation: b != null', HAVOC], refute: 'fails on',
         src: r('''    static Object mk() { java.util.UUID.randomUUID() }
    static StringBuilder sb(Object o) { new StringBuilder() }
    static void run() {
        Object g = mk()
        StringBuilder b = sb(g)
        b.append('x')
    }''')],
        // Before: `fails on: run(-2147483648)`.
        [group: G, name: '… with a parameter too', expect: [NPE, HAVOC], refute: 'fails on',
         src: r('''    static Object mk() { java.util.UUID.randomUUID() }
    static StringBuilder sb(Object o) { new StringBuilder() }
    static void run(int n) {
        Object g = mk()
        StringBuilder b = sb(g)
        b.append('x')
    }''')],
        [group: G, name: 'as a bare statement it already named none', expect: [NPE, HAVOC], refute: 'fails on',
         src: r('''    static Object mk() { java.util.UUID.randomUUID() }
    static StringBuilder sb(Object o) { new StringBuilder() }
    static void run() {
        mk()
        StringBuilder b = sb('k')
        b.append('x')
    }''')],

        // ---------- (B) a null its contract never mentions ----------
        // Before: `counterexample: b = 0, …` and `fails on: run()`.
        [group: G, name: 'a call\'s null its contract never mentions names no call, and says how to settle it',
         expect: [NPE, NULL_NOTE], refute: 'fails on',
         src: r('''    static StringBuilder sb(Object o) { new StringBuilder() }
    static void run() {
        StringBuilder b = sb(new Object())
        b.append('x')
    }''')],
        [group: G, name: '… which the @Ensures it suggests does', ok: true,
         src: r('''    @Ensures({ result != null })
    static StringBuilder sb(Object o) { new StringBuilder() }
    static void run() {
        StringBuilder b = sb(new Object())
        b.append('x')
    }''')],
        [group: G, name: 'a contract that promises null keeps its failing call: every run gets it',
         expect: [NPE, 'fails on: run()'],
         src: r('''    @Ensures({ result == null })
    static StringBuilder sb(Object o) { null }
    static void run() {
        StringBuilder b = sb(new Object())
        b.append('x')
    }''')],

        // ---------- where it was found ----------
        // Before: `fails on: run()`; ActorSystem.create never returns null.
        [group: G, name: 'a Pekko guardian held in a local, built by a user method', expect: [NPE, 'obligation: system != null', HAVOC],
         refute: 'fails on',
         src: HDR + 'import org.apache.pekko.actor.typed.*\nimport org.apache.pekko.actor.typed.javadsl.*\n' +
             "@TypeChecked(extensions = 'verification.VerifyChecker')\nclass R {\n" + '''    static Behavior<String> mk() { Behaviors.<String> empty() }
    static void run() {
        Behavior<String> g = mk()
        var system = ActorSystem.create(g, 'hello')
        system.tell('a')
    }''' + "\n}"],
    ]
}
