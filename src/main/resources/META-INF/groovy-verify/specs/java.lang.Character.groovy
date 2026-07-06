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

// External-specification skeleton (Phase 218c): trusted contracts for java.lang.Character.
// These are PARTIAL specs by design: the predicates are Unicode-aware (isDigit accepts Arabic-Indic
// digits, etc.), so total contracts are outside the fragment. Each stated fact is true over the
// ASCII ranges it names — everything else stays honestly opaque. Conditions use the `('0' as char)`
// code-point idiom the encoder folds to ints.
package java.lang

import groovy.contracts.Ensures
import groovy.transform.Pure

class Character {

    @Pure
    @Ensures({ ((c >= ('0' as char) && c <= ('9' as char)) ==> result) &&
               (((c >= ('a' as char) && c <= ('z' as char)) || (c >= ('A' as char) && c <= ('Z' as char))) ==> !result) })
    static boolean isDigit(char c) {}

    @Pure
    @Ensures({ ((c >= ('A' as char) && c <= ('Z' as char)) ==> result) &&
               (((c >= ('a' as char) && c <= ('z' as char)) || (c >= ('0' as char) && c <= ('9' as char))) ==> !result) })
    static boolean isUpperCase(char c) {}

    @Pure
    @Ensures({ ((c >= ('a' as char) && c <= ('z' as char)) ==> result) &&
               (((c >= ('A' as char) && c <= ('Z' as char)) || (c >= ('0' as char) && c <= ('9' as char))) ==> !result) })
    static boolean isLowerCase(char c) {}

    // ASCII case-shift facts: the ±32 code-point distance, identity outside the shifted range.
    @Pure
    @Ensures({ ((c >= ('a' as char) && c <= ('z' as char)) ==> result == c - 32) &&
               ((c >= ('A' as char) && c <= ('Z' as char)) ==> result == c) &&
               ((c >= ('0' as char) && c <= ('9' as char)) ==> result == c) })
    static char toUpperCase(char c) {}

    @Pure
    @Ensures({ ((c >= ('A' as char) && c <= ('Z' as char)) ==> result == c + 32) &&
               ((c >= ('a' as char) && c <= ('z' as char)) ==> result == c) &&
               ((c >= ('0' as char) && c <= ('9' as char)) ==> result == c) })
    static char toLowerCase(char c) {}
}
