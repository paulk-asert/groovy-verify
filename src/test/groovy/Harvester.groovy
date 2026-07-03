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
import groovy.json.JsonOutput

/**
 * SKETCH — harvest the proof-capability corpus + catalog from {@link VerifyHarness#CASES}, the single source of
 * truth, for AI-agent discoverability. A pure projection: the outcome is read from each case's declared spec
 * ({@code ok} / {@code expect} / {@code refute}), which CI already proves matches reality — so this runs in
 * milliseconds with no Z3. (A {@code -verify} mode could instead run {@code VerifyHarness.compile} to attach the
 * real counterexample text; left as the production refinement.)
 *
 * Produces two artifacts under the output dir (default {@code build/harvest}):
 *   • corpus.jsonl  — one record per case: {id, group, name, outcome, annotations, diagnostic, source}
 *   • catalog.json  — per-capability (group) aggregation, for the agent "what can it prove" manifest
 *
 * Run: {@code ./gradlew harvest}   (freshness check: {@code ./gradlew harvest --args='<dir> -check'})
 */
class Harvester {

    /** Contract / checker annotations recognised in a snippet — the authoring vocabulary the agent must learn. */
    static final List<String> ANNOS = ['Requires', 'Ensures', 'Invariant', 'Decreases', 'Modifies', 'SelfEnsures',
        'Label', 'Declassify', 'Reducer', 'Associative', 'Monadic', 'Rely', 'Guarantee', 'UnderRely', 'CheckOverflow']

    /** group → one-line capability description, aggregated from each case file's co-located
     *  {@code DESCRIPTION} constant (cases/G*.groovy) — the description lives beside the cases it
     *  describes, and this map is a pure projection (DocLint asserts every group has one). */
    static final Map<String, String> GROUP_DESC = collectGroupDescriptions()

    private static Map<String, String> collectGroupDescriptions() {
        Map<String, String> out = new LinkedHashMap<String, String>()
        VerifyHarness.caseClasses().each { Class c ->
            List<Map> cs = (List<Map>) c.CASES
            // a file without a DESCRIPTION just doesn't contribute a key — DocLint then names the
            // missing group cleanly, rather than this projection crashing on the property read
            if (c.metaClass.hasProperty(c, 'DESCRIPTION')) out[(String) cs[0].group] = (String) c.DESCRIPTION
        }
        out
    }

    static String slug(String s) { s.toLowerCase().replaceAll(/[^a-z0-9]+/, '-').replaceAll(/(^-|-$)/, '') }

    static List<String> annotationsIn(String src) { ANNOS.findAll { src =~ ('@' + it + /\b/) }.sort() }

    /** Outcome from the case's declared spec (CI-proven to match reality), not by re-running the solver. */
    static Map outcomeOf(Map c) {
        if (c.ok == true) return [outcome: 'verifies', diagnostic: null]
        String exp = (c.expect ?: '').toString()
        boolean skip = exp.toLowerCase().contains('skip') || exp.toLowerCase().contains('outside fragment')
        [outcome: skip ? 'skips' : 'refutes', diagnostic: exp ?: null]
    }

    static void main(String[] args) {
        File outDir = new File(args && args[0] && args[0] != '-check' ? args[0] : 'build/harvest')
        boolean checkMode = args.contains('-check')
        File work = checkMode ? File.createTempDir('harvest', '') : outDir
        work.mkdirs()

        def corpus = new StringBuilder()
        def byGroup = new LinkedHashMap<String, List>()
        VerifyHarness.CASES.eachWithIndex { Map c, int i ->
            Map o = outcomeOf(c)
            Map rec = [
                id         : slug((String) c.group) + '/' + slug((String) c.name),
                group      : c.group,
                name       : c.name,
                outcome    : o.outcome,
                annotations: annotationsIn((String) c.src),
                diagnostic : o.diagnostic,
                source     : c.src,
            ]
            corpus.append(JsonOutput.toJson(rec)).append('\n')
            byGroup.computeIfAbsent((String) c.group, { [] }) << rec
        }
        new File(work, 'corpus.jsonl').text = corpus.toString()

        // Pack provenance: capability groups an EncodingPack claims as its corpus (catalog attribution —
        // an agent reading the manifest sees which capabilities are pluggable-domain vs core).
        Map<String, String> packOfGroup = [:]
        verification.PackRegistry.packs().each { p -> p.corpusGroups().each { g -> packOfGroup[g] = p.name() } }

        def catalog = byGroup.collect { String g, List recs ->
            [ group           : g,
              description     : GROUP_DESC[g],                       // null ⇒ flagged by the cross-check lint
              examples        : recs.size(),
              verifies        : recs.count { it.outcome == 'verifies' },
              refutes         : recs.count { it.outcome == 'refutes' },
              skips           : recs.count { it.outcome == 'skips' },
              annotations     : recs.collectMany { it.annotations }.unique().sort(),
              canonicalVerify : recs.find { it.outcome == 'verifies' }?.id,
              canonicalRefute : recs.find { it.outcome == 'refutes' }?.id,
            ] + (packOfGroup.containsKey(g) ? [pack: packOfGroup[g]] : [:])   // only pack-claimed groups carry the key
        }.sort { it.group }
        new File(work, 'catalog.json').text = JsonOutput.prettyPrint(JsonOutput.toJson(catalog)) + '\n'

        if (checkMode) {
            // Freshness gate (CI): regenerate to a temp dir, diff against the committed copies, fail on drift.
            boolean drift = false
            ['catalog.json', 'corpus.jsonl'].each { String f ->
                File committed = new File(outDir, f), fresh = new File(work, f)
                if (!committed.exists() || committed.text != fresh.text) {
                    drift = true; println "  STALE: ${outDir}/${f} differs from a fresh harvest — run `./gradlew harvest`"
                }
            }
            work.deleteDir()
            if (drift) System.exit(1)
            println "harvest artifacts are up to date."
            return
        }
        int v = catalog.sum { it.verifies } ?: 0, r = catalog.sum { it.refutes } ?: 0, s = catalog.sum { it.skips } ?: 0
        println "harvested ${VerifyHarness.CASES.size()} cases (${v} verify / ${r} refute / ${s} skip), " +
                "${catalog.size()} capability groups -> ${outDir}/{catalog.json, corpus.jsonl}"
    }
}
