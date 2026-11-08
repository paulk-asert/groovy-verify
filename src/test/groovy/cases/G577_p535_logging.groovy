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

/** 'P535 logging calls' — Phase 535: a call on a logger (slf4j, java.util.logging, System.Logger, log4j2,
 *  commons-logging) changes nothing the program reads, so it no longer pushes a method outside the fragment: as a
 *  statement, in a loop, after a loop, and in the guarded form Groovy's @Slf4j / @Log write
 *  ({@code log.isInfoEnabled() ? log.info("…") : null}). It is a trusted fact, ledgered, and taken only where the
 *  logger can't reach the program's state: arguments whose toString() is the JDK's (constants, immutable values, a
 *  GString of those, a Level constant), an effect-free receiver, a library logger not implemented in the unit. A
 *  level check ({@code isDebugEnabled()}) is an unknown boolean, so a refutation resting on it names no call.
 *  A statement-position ternary is now an if/else in general. */
class G577_p535_logging {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Logging calls change nothing the program reads: slf4j, JUL, @Slf4j/@Log guards, in and after loops; mutable arguments still skip; a statement ternary is an if/else.'

    static final String SLF = 'import org.slf4j.Logger\nimport org.slf4j.LoggerFactory\n'
    static final String PK = 'import org.apache.pekko.actor.typed.*\nimport org.apache.pekko.actor.typed.javadsl.*\n' +
        'import org.apache.pekko.actor.typed.javadsl.ActorContext\n'
    static String t(String imports, String body) {
        HDR + imports + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + body.stripIndent()
    }

    static final List<Map> CASES = [
        // ---------- the shapes that verify ----------
        [group: 'P535 logging calls', name: 'an slf4j logger field: info(String)', ok: true,
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; log.info('bumped') }
                    }''')],
        [group: 'P535 logging calls', name: 'a placeholder argument of an immutable type', ok: true,
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; log.debug('bumped to {}', count) }
                    }''')],
        [group: 'P535 logging calls', name: '@Slf4j with a GString: the guarded call it writes', ok: true,
         src: t('', '''@groovy.util.logging.Slf4j
                    class C {
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; log.info("bumped to $count") }
                    }''')],
        [group: 'P535 logging calls', name: '@Log (java.util.logging) with a GString', ok: true,
         src: t('', '''@groovy.util.logging.Log
                    class C {
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; log.info("bumped to $count") }
                    }''')],
        [group: 'P535 logging calls', name: 'an explicit isDebugEnabled() guard', ok: true,
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; if (log.isDebugEnabled()) log.debug('bumped') }
                    }''')],
        [group: 'P535 logging calls', name: 'a logger reached through library getters (Pekko\'s getContext().getLog())', ok: true,
         src: t(PK, '''class Bot extends AbstractBehavior<String> {
                        int count
                        private Bot(ActorContext<String> context) { super(context) }
                        @Override
                        Receive<String> createReceive() { newReceiveBuilder().onMessage(String, this::onMsg).build() }
                        @Ensures({ count == old.count + 1 })
                        private Behavior<String> onMsg(String m) {
                            count++
                            getContext().getLog().info('got one')
                            return this
                        }
                    }''')],
        [group: 'P535 logging calls', name: 'logging inside a loop', ok: true,
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            int c = 0
                            @Invariant({ 0 <= i && i <= n && c == i })
                            @Decreases({ n - i })
                            for (int i = 0; i < n; i++) {
                                c++
                                log.debug('step {}', i)
                            }
                            return c
                        }
                    }''')],
        [group: 'P535 logging calls', name: '@Slf4j GString inside a loop', ok: true,
         src: t('', '''@groovy.util.logging.Slf4j
                    class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            int c = 0
                            @Invariant({ 0 <= i && i <= n && c == i })
                            @Decreases({ n - i })
                            for (int i = 0; i < n; i++) {
                                c++
                                log.debug("step $i")
                            }
                            return c
                        }
                    }''')],
        [group: 'P535 logging calls', name: 'logging inside an inner loop', ok: true,
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            int c = 0
                            @Invariant({ 0 <= i && i <= n && c == i })
                            @Decreases({ n - i })
                            for (int i = 0; i < n; i++) {
                                @Invariant({ 0 <= j && j <= 1 })
                                @Decreases({ 1 - j })
                                for (int j = 0; j < 1; j++) {
                                    log.trace('inner {}', j)
                                }
                                c++
                            }
                            return c
                        }
                    }''')],
        [group: 'P535 logging calls', name: 'logging after a loop', ok: true,
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            int c = 0
                            @Invariant({ 0 <= i && i <= n && c == i })
                            @Decreases({ n - i })
                            for (int i = 0; i < n; i++) {
                                c++
                            }
                            log.info('done')
                            return c
                        }
                    }''')],
        [group: 'P535 logging calls', name: 'a caller of a method that only logs', ok: true,
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        final void note() { log.info('noted') }
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; note() }
                    }''')],
        [group: 'P535 logging calls', name: 'an index check after a guarded log', ok: true,
         src: t('', '''@groovy.util.logging.Slf4j
                    class C {
                        @Requires({ a != null && 0 <= i && i < a.length })
                        static void put(int[] a, int i) { log.info("at $i"); a[i] = 1 }
                    }''')],

        // ---------- refutations ----------
        [group: 'P535 logging calls', name: 'a wrong claim past a log call refutes, with its call',
         expect: ['Cannot prove postcondition', 'fails on: inc()'],
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 2 })
                        void inc() { count++; log.info('bumped') }
                    }''')],
        [group: 'P535 logging calls', name: 'a wrong claim past an @Slf4j GString refutes, with its call',
         expect: ['Cannot prove postcondition', 'fails on: inc()'],
         src: t('', '''@groovy.util.logging.Slf4j
                    class C {
                        int count
                        @Ensures({ count == old.count + 2 })
                        void inc() { count++; log.info("bumped to $count") }
                    }''')],
        [group: 'P535 logging calls', name: 'an effect under a level check: the refutation names no call',
         expect: ['Cannot prove postcondition', 'no failing call: the failure rests on isDebugEnabled'],
         refute: 'fails on',
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; if (log.isDebugEnabled()) count++ }
                    }''')],
        [group: 'P535 logging calls', name: '… and the level check is not taken as always on',
         expect: 'Cannot prove postcondition',
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 2 })
                        void inc() { count++; if (log.isDebugEnabled()) count++ }
                    }''')],
        [group: 'P535 logging calls', name: 'a guarded arm that writes is not a log statement',
         expect: 'Cannot prove postcondition',
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count })
                        void f() { log.isDebugEnabled() ? count++ : null }
                    }''')],

        // ---------- what stays outside: loud skips ----------
        [group: 'P535 logging calls', name: 'an object argument (its toString may run program code) skips',
         expect: ['Skipped verification of postcondition for inc', "is passed 'this', which it may write"],
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; log.info('state {}', this) }
                    }''')],
        [group: 'P535 logging calls', name: 'a GString interpolating an object skips',
         expect: 'Skipped verification of postcondition for inc',
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; log.info("state $this") }
                    }''')],
        [group: 'P535 logging calls', name: 'a Throwable argument skips',
         expect: 'Skipped verification of postcondition for inc',
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; log.warn('oops', new RuntimeException('x')) }
                    }''')],
        [group: 'P535 logging calls', name: 'a receiver built by a call of this unit skips',
         expect: 'Skipped verification of postcondition for inc',
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        Logger logger() { count = 0; log }
                        @Ensures({ count == old.count + 1 })
                        void inc() { count++; logger().info('bumped') }
                    }''')],
        [group: 'P535 logging calls', name: 'a logger type implemented in the unit is not trusted',
         expect: 'Skipped verification of postcondition for onMsg',
         src: t(PK + SLF, '''class Bot extends AbstractBehavior<String> {
                        int count
                        private Bot(ActorContext<String> context) { super(context) }
                        @Override
                        Receive<String> createReceive() { newReceiveBuilder().onMessage(String, this::onMsg).build() }
                        @Ensures({ count == old.count + 1 })
                        private Behavior<String> onMsg(String m) {
                            count++
                            getContext().getLog().info('got one')
                            return this
                        }
                    }
                    abstract class Sneaky implements Logger { }''')],

        // ---------- the statement-position ternary, in general ----------
        [group: 'P535 logging calls', name: 'a statement ternary runs only the arm its condition picks', ok: true,
         src: tc('''class C {
                        int count
                        @Ensures({ count == old.count + (b ? 1 : 0) })
                        void inc(boolean b) { b ? count++ : null }
                    }''')],
        [group: 'P535 logging calls', name: '… and a wrong claim about it refutes',
         expect: ['Cannot prove postcondition', 'fails on: inc(false)'],
         src: tc('''class C {
                        int count
                        @Ensures({ count == old.count + 1 })
                        void inc(boolean b) { b ? count++ : null }
                    }''')],
        [group: 'P535 logging calls', name: 'a boolean call as a statement ternary\'s condition is a condition, not a cast',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        int count
                        @Requires({ xs != null })
                        @Ensures({ count == old.count })
                        void f(List<Integer> xs) { xs.isEmpty() ? count++ : null }
                    }''')],
        [group: 'P535 logging calls', name: 'a statement ternary choosing between two contracted calls', ok: true,
         src: tc('''class C {
                        int count
                        @Modifies({ this.count })
                        @Ensures({ count == old.count + 1 })
                        void up() { count++ }
                        @Modifies({ this.count })
                        @Ensures({ count == old.count - 1 })
                        void down() { count-- }
                        @Ensures({ count == old.count + (b ? 1 : -1) })
                        void step(boolean b) { b ? up() : down() }
                    }''')],
        [group: 'P535 logging calls', name: '… and a wrong claim about it refutes on the arm it misses',
         expect: ['Cannot prove postcondition', 'fails on: step(false)'],
         src: tc('''class C {
                        int count
                        @Modifies({ this.count })
                        @Ensures({ count == old.count + 1 })
                        void up() { count++ }
                        @Modifies({ this.count })
                        @Ensures({ count == old.count - 1 })
                        void down() { count-- }
                        @Ensures({ count == old.count + 1 })
                        void step(boolean b) { b ? up() : down() }
                    }''')],
        [group: 'P535 logging calls', name: 'a level check guarding a call that writes is not a log statement',
         expect: 'Cannot prove postcondition',
         src: t(SLF, '''class C {
                        private static final Logger log = LoggerFactory.getLogger(C)
                        int count
                        @Modifies({ this.count })
                        @Ensures({ count == old.count + 1 })
                        void up() { count++ }
                        @Ensures({ count == old.count })
                        void f() { log.isDebugEnabled() ? up() : null }
                    }''')],
    ]
}
