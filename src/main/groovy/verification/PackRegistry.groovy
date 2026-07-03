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
package verification

import groovy.transform.CompileStatic

/**
 * Loads the {@link EncodingPack}s visible on the compile classpath, once per JVM, in deterministic
 * (name-sorted) order. A provider that fails to load is reported to stderr and skipped — a broken pack
 * jar should degrade that pack's vocabulary to the ordinary loud "outside fragment" skips, not brick the
 * whole compilation.
 *
 * <p><b>Selection knob</b>: {@code VERIFY_PACKS} (env var, or the {@code verify.packs} system property,
 * which wins) — {@code none} disables every pack, a comma-separated list of pack names keeps only those
 * ({@code VERIFY_PACKS=jsr385-units}). Unset = all discovered packs. A deselected pack's vocabulary
 * degrades to the ordinary loud skips — a diagnostic bisection tool, in the {@code VERIFY_*} knob family
 * (see TOOLING.md); it never changes what a proof means, only which recognisers run.
 */
@CompileStatic
class PackRegistry {

    private static volatile List<EncodingPack> loaded

    static List<EncodingPack> packs() {
        List<EncodingPack> ps = loaded
        if (ps == null) {
            synchronized (PackRegistry) {
                ps = loaded
                if (ps == null) {
                    List<EncodingPack> out = new ArrayList<EncodingPack>()
                    try {
                        Iterator<EncodingPack> it = ServiceLoader.load(EncodingPack, EncodingPack.classLoader).iterator()
                        while (it.hasNext()) {
                            try { out.add(it.next()) }
                            catch (Throwable t) { System.err.println("verification: skipping unloadable EncodingPack: ${t}") }
                        }
                    } catch (Throwable t) {
                        System.err.println("verification: EncodingPack discovery failed: ${t}")
                    }
                    String sel = System.getProperty('verify.packs', System.getenv('VERIFY_PACKS') ?: '').trim()
                    if (sel) {
                        if (sel == 'none') {
                            out.clear()
                        } else {
                            Set<String> keep = new HashSet<String>(sel.split(',')*.trim().findAll { it })
                            out.removeAll { EncodingPack p -> !keep.contains(p.name()) }
                        }
                    }
                    out.sort { EncodingPack a, EncodingPack b -> (a.name() ?: '') <=> (b.name() ?: '') }
                    loaded = ps = Collections.unmodifiableList(out)
                }
            }
        }
        ps
    }
}
