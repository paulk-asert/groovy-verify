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
package fixture

/**
 * Phase 363 — a "library" class for the override cases: compiled with the test sources, so a case's own source
 * extends a PRECOMPILED class, as a later unit extends a library's. Not checked itself; its contracts, when a
 * case gives it any, come from a skeleton the case supplies (the harness `specs:` / `relied:` keys).
 */
class LibCounter {
    int count
    int log
    void incr() { count = count + 1 }
    int get() { count }
    int size() { count }
    void fill(int[] a) { if (a != null && a.length > 0) a[0] = 9 }
}
