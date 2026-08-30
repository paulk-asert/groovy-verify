/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package verification

/**
 * Phase 270 — a `@Protocol` exported as REAL Scribble, the notation the multiparty-session-type tools read
 * (Scribble-Java; nuScr, the actively maintained OCaml core). The mapping, stated honestly:
 * <ul>
 *   <li>a message `label: from -> to` becomes `label() from A to B;` — the payload is left empty: our label
 *       IS the channel and the payload type is the channel's element type, a deliberate divergence;</li>
 *   <li>`loop { … }` becomes `rec Xn { …; continue Xn; }` — Scribble's `rec` repeats FOREVER unless a choice
 *       exits, where our `loop` is a Kleene star (zero or more, exit any time): the exported protocol is the
 *       ω-iteration of ours, the closest standard spelling;</li>
 *   <li>`choice at R { } or { }` is Scribble's own construct, verbatim;</li>
 *   <li>`par { } and { }` is Scribble-Java syntax (nuScr's fragment may reject it — that is the gate's
 *       finding to report, not ours to hide);</li>
 *   <li>a MIXED choice (no deciding role, Phase 267) is OUTSIDE standard Scribble: refused with the reason —
 *       which is itself the precise statement of where this ladder stepped past the standard fragment.</li>
 * </ul>
 * `main(outDir)` writes the curated corpus (the gallery's protocols) as `.scr` files for the `nuscrCheck`
 * gradle task, which cross-checks them with `nuscr` when the binary is installed.
 */
class ScribbleExport {

    /** The protocol as standard Scribble, or null with the reasons in {@code errors}. */
    static String export(String name, String protocolText, List<String> errors) {
        SessionChecker.G g = SessionChecker.parse(protocolText, errors)
        if (!errors.isEmpty()) return null
        Set<String> roles = new LinkedHashSet<String>()
        collectRoles(g, roles)
        StringBuilder out = new StringBuilder()
        out.append("global protocol ${name}(")
        out.append(roles.collect { "role ${it}" }.join(', '))
        out.append(') {\n')
        int[] recNo = [0]
        if (!render(g, out, '    ', recNo, errors)) return null
        out.append('}\n')
        out.toString()
    }

    private static void collectRoles(SessionChecker.G g, Set<String> out) {
        if (g instanceof SessionChecker.Msg) { out.add(g.from); out.add(g.to) }
        else if (g instanceof SessionChecker.Seq) g.items.each { collectRoles(it, out) }
        else if (g instanceof SessionChecker.Loop) collectRoles(g.body, out)
        else if (g instanceof SessionChecker.Choice) { if (g.at != null) out.add(g.at); g.branches.each { collectRoles(it, out) } }
        else if (g instanceof SessionChecker.Par) g.parts.each { collectRoles(it, out) }
    }

    private static boolean render(SessionChecker.G g, StringBuilder out, String pad, int[] recNo, List<String> errors) {
        if (g instanceof SessionChecker.Msg) {
            out.append(pad).append("${g.chan}() from ${g.from} to ${g.to};\n")
            return true
        }
        if (g instanceof SessionChecker.Seq) {
            for (SessionChecker.G x : g.items) if (!render(x, out, pad, recNo, errors)) return false
            return true
        }
        if (g instanceof SessionChecker.Loop) {
            String label = "X${++recNo[0]}"
            out.append(pad).append("rec ${label} {\n")
            if (!render(g.body, out, pad + '    ', recNo, errors)) return false
            out.append(pad).append("    continue ${label};\n")
            out.append(pad).append('}\n')
            return true
        }
        if (g instanceof SessionChecker.Choice) {
            if (g.at == null) {
                errors.add("a mixed choice (branches opened by different roles) is outside standard Scribble — " +
                    'the fragment boundary Phase 267 stepped past; nothing standard to export')
                return false
            }
            for (int i = 0; i < g.branches.size(); i++) {
                out.append(pad).append(i == 0 ? "choice at ${g.at} {\n" : '} or {\n')
                if (!render(g.branches.get(i), out, pad + '    ', recNo, errors)) return false
            }
            out.append(pad).append('}\n')
            return true
        }
        if (g instanceof SessionChecker.Par) {
            for (int i = 0; i < g.parts.size(); i++) {
                out.append(pad).append(i == 0 ? 'par {\n' : '} and {\n')
                if (!render(g.parts.get(i), out, pad + '    ', recNo, errors)) return false
            }
            out.append(pad).append('}\n')
            return true
        }
        errors.add('an unknown protocol node — nothing to export')
        false
    }

    /** The curated corpus: the gallery's protocols, by name. The mixed choice is here deliberately — its
     *  refusal note documents the fragment boundary mechanically. */
    static final Map<String, String> CORPUS = [
        ReqReply: 'loop { request: client -> server; reply: server -> client }',
        PrimedRing: 'ab: a -> b; loop { bc: b -> c; ca: c -> a; ab: a -> b }',
        CalcChoice: 'loop { choice at client { add: client -> server; sum: server -> client } or { neg: client -> server; res: server -> client } }',
        FairServerPar: 'par { loop { reqA: clientA -> server; replyA: server -> clientA } } and { loop { reqB: clientB -> server; replyB: server -> clientB } }',
        MixedPingPong: 'loop { choice { ping: left -> right } or { pong: right -> left } }',
    ].asImmutable()

    /** Writes the corpus to {@code args[0]}: `.scr` per exportable protocol, `.outside-standard.txt` per refusal. */
    static void main(String[] args) {
        File dir = new File(args ? args[0] : 'build/scribble')
        dir.mkdirs()
        CORPUS.each { name, text ->
            List<String> errors = []
            String scr = export(name, text, errors)
            if (scr != null) {
                new File(dir, "${name}.scr").text = scr
                println "exported ${name}.scr"
            } else {
                new File(dir, "${name}.outside-standard.txt").text = errors.join('\n') + '\n'
                println "outside the standard fragment: ${name} — ${errors.join('; ')}"
            }
        }
    }
}
