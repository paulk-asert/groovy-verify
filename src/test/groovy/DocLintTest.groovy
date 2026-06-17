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
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.assertEquals

/**
 * The CI enforcement of the doc/data drift lints {@link DocLint} reports. {@code ./gradlew docLint} is the
 * human-readable report; this fails {@code check} the moment any drift appears, so the single source of truth
 * ({@link VerifyHarness#CASES} and the engine sources) can't silently fall out of sync with the docs.
 *
 *   • every test group carries a one-line capability description (Harvester.GROUP_DESC)
 *   • every fenced groovy block in the docs is linked to a case, exempted, or a verbatim substring of some case —
 *     and every doclint:case link still matches its case (comments included)
 *   • every verification/*.groovy engine source is named in ARCHITECTURE.md
 */
class DocLintTest {

    @Test
    void everyTestGroupHasACapabilityDescription() {
        assertEquals(0, DocLint.lintGroupDescriptions(), 'test groups are missing a Harvester.GROUP_DESC entry')
    }

    @Test
    void everyDocSnippetTracksTheSuite() {
        assertEquals(0, DocLint.lintSnippets(),
            'a doc code block is unaccounted-for, or a doclint:case link has drifted from its test')
    }

    @Test
    void everyEngineSourceIsInTheArchitectureMap() {
        assertEquals(0, DocLint.lintArchitecture(), 'a verification/*.groovy source is not referenced in ARCHITECTURE.md')
    }
}
