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

/** 'P-blog-actors' — the examples of the "Using Apache Pekko actors and Groovy 6 actors" blog post
 *  (groovy-website: site/src/site/blog/groovy-pekko-gpars.adoc), pinned so the post's quoted diagnostic can't drift.
 *  The post's mailbox-deadlock example is already case G339 ('P289 actor mailbox', knot). */
class G576_blog_actors {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The actor blog post\'s @ActiveObject bot: a class invariant over a handler, refuted until a late greeting is ignored.'

    static final List<Map> CASES = [
        [group: 'P-blog-actors', name: 'the bot\'s counter can pass its maximum: invariant refuted at greeted\'s exit',
         expect: ['Cannot prove class invariant of greeted holds at method exit',
                  'invariant: (((max >= 1) && (0 <= greetingCounter)) && (greetingCounter <= max))',
                  'counterexample: greetingCounter = 1, max = 1',
                  'fails on: greeted("")'],
         src: tc('''@groovy.transform.ActiveObject
                    @Invariant({ max >= 1 && 0 <= greetingCounter && greetingCounter <= max })
                    class HelloWorldBot {
                        private final int max
                        private int greetingCounter

                        @Requires({ max >= 1 })
                        HelloWorldBot(int max) { this.max = max }

                        @groovy.transform.ActiveMethod(blocking = false)
                        void greeted(String whom) {
                            greetingCounter++
                        }
                    }''')],
        [group: 'P-blog-actors', name: 'the bot ignores a late greeting: invariant proved', ok: true,
         src: tc('''@groovy.transform.ActiveObject
                    @Invariant({ max >= 1 && 0 <= greetingCounter && greetingCounter <= max })
                    class HelloWorldBot {
                        private final int max
                        private int greetingCounter

                        @Requires({ max >= 1 })
                        HelloWorldBot(int max) { this.max = max }

                        @groovy.transform.ActiveMethod(blocking = false)
                        void greeted(String whom) {
                            if (greetingCounter == max) return  // a late greeting: ignore it
                            greetingCounter++
                        }
                    }''')],
    ]
}
