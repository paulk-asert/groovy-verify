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

/**
 * SKETCH — the four drift lints that keep the hand-maintained docs honest against the single source of truth
 * ({@link VerifyHarness#CASES} and the codebase). This entry point is the human-readable REPORT; the same four
 * lints are asserted by {@link DocLintTest} inside `check`/CI, so drift fails the build.
 *
 *   1. group-descriptions — every CASES group has a one-line capability description (a co-located DESCRIPTION in its cases/G*.groovy file, aggregated by Harvester.GROUP_DESC)
 *   2. snippets-as-tests  — every fenced ```groovy block in the docs appears as a CASES source (can't silently break)
 *   3. architecture-map   — every file named in ARCHITECTURE.md exists; every verification/*.groovy is mapped
 *   4. pack-corpora       — every EncodingPack's declared corpus groups exist in CASES (provenance can't rot)
 *
 * Run: {@code ./gradlew docLint}
 */
class DocLint {

    static String norm(String s) { s.replaceAll(/\s+/, ' ').trim() }

    /** id → whitespace-normalised case source, for the doclint:case link check. Comments are kept: teaching
     *  comments live in the test source (the single source of truth), so the doc must reproduce them faithfully. */
    static Map<String, String> caseSourcesById() {
        Map<String, String> m = [:]
        VerifyHarness.CASES.each { Map c ->
            m[Harvester.slug((String) c.group) + '/' + Harvester.slug((String) c.name)] = norm((String) c.src)
        }
        m
    }

    // 1 ─ every test group has a capability description (the one manual enrichment).
    static int lintGroupDescriptions() {
        Set<String> groups = new TreeSet<String>(VerifyHarness.CASES.collect { (String) it.group })
        def missing = groups.findAll { !Harvester.GROUP_DESC.containsKey(it) }.toList()
        println "\n[1] group descriptions — ${groups.size() - missing.size()}/${groups.size()} groups described"
        if (missing) println "    MISSING (${missing.size()}): " + missing.take(8).join(', ') + (missing.size() > 8 ? ', …' : '')
        missing.size()
    }

    // 2 ─ every fenced groovy block in the docs is accounted for. Three dispositions, by preceding marker:
    //       <!-- doclint:case ID --> → LINKED to that specific case: the block (ignoring only the surrounding
    //                                  @TypeChecked/class wrapper, via substring) must match case ID's source —
    //                                  comments included, since teaching comments live in the test. The block
    //                                  keeps its terse hand-written form; this pins it to one test and fails on
    //                                  any divergence. Non-destructive — nothing is rewritten.
    //       <!-- doclint:ignore … --> → exempt illustrative fragment (genuinely doc-only).
    //       > blockquoted ```groovy   → exposition by authorial intent (desugaring / "generated code" asides); exempt.
    //       (no marker)              → weak check: must appear as a substring of *some* CASES source.
    static int lintSnippets() {
        List<String> corpus = VerifyHarness.CASES.collect { norm((String) it.src) }
        Map<String, String> byId = caseSourcesById()
        int blocks = 0, unmatched = 0, exempt = 0, quoted = 0, linked = 0, linkBroken = 0
        def examples = [], broken = []
        def docFiles = ['README.md', 'FRAGMENT.md', 'CAPABILITIES.md', 'ARCHITECTURE.md', 'CONCURRENCY.md', 'TOOLING.md', 'PACKS.md']
        File examplesDir = new File('examples')   // the split-out galleries (examples/*.md, examples/**/examples.md)
        if (examplesDir.isDirectory()) examplesDir.eachFileRecurse { File ff -> if (ff.name.endsWith('.md')) docFiles << ff.path }
        docFiles.each { String f ->
            File doc = new File(f); if (!doc.exists()) return
            (doc.text =~ /(?s)(<!--\s*doclint:(ignore|case)(?:\s+([^\s>]+))?[^>]*-->\s*\n)?```groovy\n(.*?)```/).each { m ->
                String marker = m[2], id = m[3], raw = m[4] as String   // type | id | body
                String body = norm(raw)
                if (body.length() < 40) return                          // skip one-liners / trivially short blocks
                if (raw.readLines().find { it.trim() }?.trim()?.startsWith('>')) { quoted++; return }  // blockquoted exposition
                if (marker == 'ignore') { exempt++; return }            // explicitly exempted illustrative fragment
                if (marker == 'case') {                                 // linked to a specific case
                    linked++
                    String src = byId[id]
                    if (src == null)              { linkBroken++; broken << "${f}: unknown case id '${id}'" }
                    else if (!src.contains(body)) { linkBroken++; broken << "${f}: '${id}' — block diverges from its case" }
                    return
                }
                blocks++                                                // unmarked — weak "appears somewhere" check
                if (!corpus.any { it.contains(body) }) {
                    unmatched++
                    if (examples.size() < 5) examples << "${f}: ${raw.readLines().find { it.trim() }?.trim()?.take(70)}"
                }
            }
        }
        println "\n[2] snippets-as-tests — ${blocks - unmatched}/${blocks} unmarked blocks found in CASES; " +
                "${linked - linkBroken}/${linked} doclint:case links intact; ${exempt} exempted; ${quoted} blockquoted-exposition"
        if (linkBroken) { println "    BROKEN LINKS (${linkBroken}):"; broken.each { println "      ${it}" } }
        if (unmatched)  { println "    UNMARKED & UNMATCHED (${unmatched}) — link with <!-- doclint:case ID --> or exempt with <!-- doclint:ignore -->:"; examples.each { println "      ${it}" } }
        unmatched + linkBroken
    }

    // 4 ─ every EncodingPack's declared corpus groups actually exist in CASES — the pack's provenance
    //     claim (catalog.json `pack:` attribution) can't silently rot when a group is renamed/removed.
    static int lintPackCorpora() {
        Set<String> groups = new HashSet<String>(VerifyHarness.CASES.collect { (String) it.group })
        List<String> broken = []
        verification.PackRegistry.packs().each { p ->
            p.corpusGroups().each { g -> if (!groups.contains(g)) broken << "${p.name()}: '${g}'" }
        }
        println "\n[4] pack corpora — ${verification.PackRegistry.packs().size()} packs, ${broken.size()} broken group claims"
        if (broken) println "    BROKEN (${broken.size()}): " + broken.join(', ')
        broken.size()
    }

    // 3 ─ ARCHITECTURE.md names real files, and every engine source is mapped.
    static int lintArchitecture() {
        File arch = new File('ARCHITECTURE.md')
        if (!arch.exists()) { println "\n[3] architecture-map — ARCHITECTURE.md missing"; return 1 }
        String text = arch.text
        File srcDir = new File('src/main/groovy/verification')
        List<String> sources = srcDir.listFiles().findAll { it.name.endsWith('.groovy') }.collect { it.name - '.groovy' }.sort()
        // a source is "mapped" if its class name appears in backticks anywhere in the doc
        List<String> unmapped = sources.findAll { !(text =~ ('`' + java.util.regex.Pattern.quote(it) + '`')) }
        println "\n[3] architecture-map — ${sources.size() - unmapped.size()}/${sources.size()} engine sources mapped"
        if (unmapped) println "    UNMAPPED (${unmapped.size()}): " + unmapped.join(', ')
        unmapped.size()
    }

    // 5 ─ every SHIPPED external-spec skeleton parses and carries at least one contract — a malformed
    //     spec file is silent trust loss (the registry caches the miss and callers quietly lose the
    //     obligation/assumption), so it is drift, not a runtime error.
    static int lintTrustedSpecs() {
        File dir = new File('src/main/resources/META-INF/groovy-verify/specs')
        List<File> files = (dir.listFiles() ?: new File[0]).findAll { it.name.endsWith('.groovy') }
        List<String> broken = []
        int methods = 0
        files.each { File f ->
            String fqn = f.name - '.groovy'
            def cn = verification.SpecRegistry.parseForLint(f.getText('UTF-8'), fqn)
            if (cn == null) { broken << "${f.name}: does not parse"; return }
            int contracted = cn.methods.count { m ->
                verification.SpecRegistry.hasContractText(m) } as int
            if (contracted == 0) broken << "${f.name}: no contracted methods"
            methods += contracted
        }
        // in-place spec-only contracts in the corpus are inventoried too (report-only count) —
        // the upstream spelling since Phase 224: woven = false, direct = false
        int inPlace = new File('src/test/groovy/cases').listFiles()
            .findAll { it.name.endsWith('.groovy') }
            .sum { File f -> f.text.count('direct = false') } as int
        println "\n[5] trusted inventory — ${files.size()} shipped spec file(s), ${methods} contracted method(s); " +
            "${inPlace} in-place trusted contract(s) in the corpus; ${broken.size()} broken"
        if (broken) println "    BROKEN (${broken.size()}): " + broken.join(', ')
        broken.size()
    }

    static void main(String[] args) {
        println '── DocLint (human-readable report; DocLintTest asserts the same lints inside `check`/CI) ' + ('─' * 8)
        int total = lintGroupDescriptions() + lintSnippets() + lintArchitecture() + lintPackCorpora() + lintTrustedSpecs()
        println "\n${'═' * 70}\nTotal drift findings: ${total}  (report-only; not failing the build)"
    }
}
