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

import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.CastExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.DoWhileStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ForStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.ast.stmt.WhileStatement
import org.codehaus.groovy.syntax.Types

/**
 * Phase 263 — SESSION TYPES for a channel network (slice 23 of the SEQ/PAR ladder).
 *
 * A {@code @Protocol} is a GLOBAL type in the multiparty-session-type sense (Honda–Yoshida–Carbone; the
 * Scribble notation): a sequence of messages {@code label: from -> to} — the label is the channel the message
 * travels on — with {@code loop { … }} and {@code choice at role { … } or { … }}. It is PROJECTED onto each
 * role (a message becomes {@code !c} for its sender, {@code ?c} for its receiver, nothing for the rest; a
 * choice at S is S's own selection and, for another role, an external choice its branches must let it tell
 * apart by their first message to it — or be identical for it), giving each role a LOCAL type, a regular
 * language over channel ops. Each PROCESS — the main body, each {@code async} arm — is bound to a role by
 * the channel ends it uses, its control flow is read as an automaton over the same ops (sends, receives,
 * drains, ALTs as choices, loops as stars, ifs as unions), and CONFORMANCE is language inclusion: the process
 * never performs an op its local type does not allow next, and never ends where the protocol continues. A
 * violation is reported with the trace that reaches it. The check is structural (no solver): what the
 * protocol adds to the ladder is ORDER across the whole conversation — the deadlock, liveness and value
 * certificates of the other rungs stand on their own.
 *
 * Phase 264 — PARALLEL COMPOSITION, {@code par { … } and { … }}: independent sub-sessions interleaved (their
 * channels disjoint), projected as the SHUFFLE of the parts' projections. The fair server is exactly this —
 * not a choice one role makes, but two request–reply sessions interleaved at the server — and its ALT is one
 * conformant implementation of the shuffle; a cross-wired reply falls outside it, with its trace.
 *
 * Phase 271 — the RACING mixed choice, CERTIFIED: on a runtime carrying GROOVY-12323's arbitrated select,
 * two initiators are coherent when every one of them opens ONLY through {@code offers(send(…), receive(…))
 * .select()} — never a bare send — and every opener channel is RENDEZVOUS ({@code AsyncChannel.create(0)}):
 * a buffered send offer commits unilaterally against buffer space and the collision reproduces through the
 * API (the caveat GROOVY-12323 documents), so the capacity is part of the certificate. Anything less is
 * refused with the exact missing piece.
 *
 * Phase 267 — MIXED CHOICE, {@code choice { … } or { … }} with no {@code at}: branches opened by different
 * roles — the race. Projection is the mixed union for an opener; but local conformance famously stops
 * implying global coherence there (each peer can conform alone while together they collide), so the checker
 * adds the missing half: a COHERENCE check across the bound processes. Two peers that can both SEND their
 * openers are a collision — buffered sends both succeed and the peers proceed down different branches, and
 * no output guards exist to arbitrate a race (the reason occam banned them; groovy.concurrent's ALT has
 * input guards only) — refused, both named. Exactly one initiator: the mixed choice DEGENERATES to a choice
 * at that role, certified silently. None: the conversation can never take it, said.
 */
class SessionChecker {

    // ── the global type ────────────────────────────────────────────────────────────────────────
    static class G {}
    static class Msg extends G { String chan, from, to }
    static class Seq extends G { List<G> items = [] }
    static class Loop extends G { G body }
    static class Choice extends G { String at; List<G> branches = [] }
    static class Par extends G { List<G> parts = [] }                       // Phase 264 — independent sub-sessions, interleaved

    // ── a local type / a process: NFAs over op labels ("!c", "?c"), ε = '' ─────────────────────
    static class Nfa {
        int n = 0
        final Map<Integer, List<Object[]>> edges = [:]        // state → [label, target, line]
        int newState() { edges.put(n, []); n++ }
        void edge(int from, String label, int to, int line = -1) { edges.get(from).add([label, to, line] as Object[]) }
    }
    /** A fragment: entry state, exit state (null when the fragment never exits — a `while (true)`). */
    static class Frag { int in; Integer out }

    // ── entry ──────────────────────────────────────────────────────────────────────────────────

    /** Findings as [message, anchor]; empty when every process conforms. */
    static List<Object[]> check(String methodName, String text, BlockStatement body, Set<String> chans, boolean arbitrated = false) {
        List<Object[]> out = []
        List<String> errors = []
        G global = parse(text, errors)
        if (!errors.isEmpty()) {
            for (String e : errors) out.add([Reporter.formatProtocolSkipped(methodName, e), body] as Object[])
            return out
        }
        Set<String> roles = new LinkedHashSet<String>()
        collectRoles(global, roles)
        Set<String> protoChans = new LinkedHashSet<String>()
        collectChans(global, protoChans)
        for (String c : protoChans) if (!chans.contains(c)) { out.add([Reporter.formatProtocolSkipped(methodName, "message '${c}' names no channel variable of the method"), body] as Object[]); return out }
        // local types
        Map<String, Nfa> local = [:]
        Map<String, Frag> localFrag = [:]
        Map<String, Set<String>> roleSends = [:], roleRecvs = [:]
        for (String r : roles) {
            List<String> perr = []
            Nfa nfa = new Nfa()
            Frag f = project(global, r, nfa, perr)
            if (!perr.isEmpty()) { for (String e : perr) out.add([Reporter.formatProtocolSkipped(methodName, e), body] as Object[]); return out }
            local.put(r, nfa); localFrag.put(r, f)
            Set<String> s = new LinkedHashSet<String>(), q = new LinkedHashSet<String>()
            alphabet(nfa, s, q)
            if (s.isEmpty() && q.isEmpty()) { out.add([Reporter.formatProtocolSkipped(methodName, "role '${r}' takes part in no message"), body] as Object[]); return out }
            roleSends.put(r, s); roleRecvs.put(r, q)
        }
        // processes
        List<Object[]> procs = processes(body)            // [name, statements, anchor]
        Map<String, Object[]> bound = [:]                 // role → [name, nfa, frag, anchor, sends, recvs]
        List<Object[]> unbound = []
        Map<Object, OpInfo> opInfoOf = new IdentityHashMap<Object, OpInfo>()
        for (Object[] p : procs) {
            Nfa pn = new Nfa()
            OpInfo oi = new OpInfo()
            Frag pf = processAutomaton((List<Statement>) p[1], pn, chans, oi)
            for (List<Object[]> es : pn.edges.values()) for (Object[] e : es) {   // bare sends = '!' edges not from an offers-select
                String l = (String) e[0]
                if (l.startsWith('!') && !oi.offerSends.contains(l.substring(1))) oi.bareSends.add(l.substring(1))
            }
            opInfoOf.put(p, oi)
            Set<String> s = new LinkedHashSet<String>(), q = new LinkedHashSet<String>()
            alphabet(pn, s, q)
            if (s.isEmpty() && q.isEmpty()) continue                                 // no channel traffic: no role
            String role = roles.find { String r -> roleSends.get(r) == s && roleRecvs.get(r) == q }
            if (role == null) { unbound.add([p, pn, pf, s, q] as Object[]); continue }
            if (bound.containsKey(role)) { out.add([Reporter.formatProtocolViolation(methodName, role, "two processes play it — ${bound.get(role)[0]} and ${p[0]}"), (ASTNode) p[2]] as Object[]); return out }
            bound.put(role, [p[0], pn, pf, p[2], s, q, opInfoOf.get(p)] as Object[])
        }
        // Phase 267 — a mixed choice lets a conformant process use a strict SUBSET of its role's alphabet (the
        // branch it never takes): bind the leftovers where the subset fits exactly one free role.
        for (Iterator<Object[]> it = unbound.iterator(); it.hasNext(); ) {
            Object[] u = it.next()
            Set<String> s = (Set<String>) u[3], q = (Set<String>) u[4]
            List<String> fits = new ArrayList<String>(roles.findAll { String r -> !bound.containsKey(r) && roleSends.get(r).containsAll(s) && roleRecvs.get(r).containsAll(q) })
            if (fits.size() != 1) continue
            Object[] p = (Object[]) u[0]
            bound.put(fits.get(0), [p[0], u[1], u[2], p[2], s, q, opInfoOf.get(p)] as Object[])
            it.remove()
        }
        for (Object[] u : unbound) {
            Object[] p = (Object[]) u[0]
            out.add([Reporter.formatProtocolViolation(methodName, null, "${p[0]} plays no role of the protocol — it sends on ${u[3]} and receives from ${u[4]}, which is no role's projection"), (ASTNode) p[2]] as Object[])
        }
        for (String r : roles) if (!bound.containsKey(r)) out.add([Reporter.formatProtocolViolation(methodName, r, "no process plays it (a process that sends on ${roleSends.get(r)} and receives from ${roleRecvs.get(r)})"), body] as Object[])
        if (!out.isEmpty()) return out
        // Phase 267 — coherence of every MIXED choice: at most one bound process may be able to SEND an opener
        List<Choice> mixed = []
        collectMixed(global, mixed)
        for (Choice c : mixed) {
            List<Object[]> openers = []                                          // [role, chan]
            for (G br : c.branches) { Msg m = firstMsg(br); if (m != null && !openers.any { Object[] o -> o[0] == m.from && o[1] == m.chan }) openers.add([m.from, m.chan] as Object[]) }
            List<Object[]> initiators = openers.findAll { Object[] o -> Object[] b = bound.get((String) o[0]); b != null && ((Set<String>) b[4]).contains((String) o[1]) }
            if (initiators.size() > 1 && arbitrated) {
                // Phase 271 — the RACING mixed choice: certified iff every initiator opens ONLY through the
                // arbitrated select and every opener channel is rendezvous (capacity-0).
                Set<String> rendezvous = rendezvousChans(body, chans)
                List<String> why = []
                for (Object[] o : initiators) {
                    OpInfo oi = (OpInfo) bound.get((String) o[0])[6]
                    String chan = (String) o[1]
                    if (oi == null || oi.bareSends.contains(chan)) why.add("${bound.get((String) o[0])[0]} (role '${o[0]}') opens '${chan}' with a bare send — un-arbitrated; open it inside offers(send(${chan}, …), …)".toString())
                    else if (!oi.offerSends.contains(chan)) why.add("${bound.get((String) o[0])[0]} (role '${o[0]}') does not open '${chan}' through an arbitrated select".toString())
                    else if (!rendezvous.contains(chan)) why.add("'${chan}' is a buffered channel — a buffered send offer commits unilaterally against buffer space and the collision reproduces through the API (GROOVY-12323's documented caveat): the racing openers must be rendezvous, AsyncChannel.create(0)".toString())
                }
                if (why.isEmpty()) continue                        // certified: the race is arbitrated — silent
                out.add([Reporter.formatProtocolViolation(methodName, null,
                    "the mixed choice has two initiators and the race is not certifiable as written — ${why.join('; ')}"), body] as Object[])
            } else if (initiators.size() > 1) {
                String detail = initiators.collect { Object[] o -> "${bound.get((String) o[0])[0]} (role '${o[0]}') can send '${o[1]}'" }.join(' and ')
                out.add([Reporter.formatProtocolViolation(methodName, null,
                    "the mixed choice has two initiators — ${detail}. Each conforms alone; together they collide: " +
                    "buffered sends both succeed and the peers proceed down different branches. No output guards " +
                    "exist to arbitrate a race (the reason occam banned them; ChannelSelect offers input guards " +
                    "only) — give the choice to one role, or see the upstream proposal for claimable send offers " +
                    "(repro/GROOVY-MixedChoice-jira-draft.md: the two-phase commit GROOVY-12320's claim machinery half-built)"), body] as Object[])
            } else if (initiators.isEmpty()) {
                out.add([Reporter.formatProtocolViolation(methodName, null,
                    "no process opens the mixed choice — none of them sends ${openers.collect { Object[] o -> "'" + o[1] + "'" }.join(' or ')}, so the conversation can never take it"), body] as Object[])
            }
            // exactly one initiator: the mixed choice degenerates to a choice at that role — certified silently
        }
        if (!out.isEmpty()) return out
        // conformance
        for (String r : roles) {
            Object[] b = bound.get(r)
            String v = conforms((Nfa) b[1], (Frag) b[2], local.get(r), localFrag.get(r))
            if (v != null) out.add([Reporter.formatProtocolViolation(methodName, r, "${b[0]} ${v}"), (ASTNode) b[3]] as Object[])
        }
        out
    }

    /** Phase 271 — channel vars declared `AsyncChannel.create(0)`: rendezvous, the only coherent racing openers.
     *  Phase 272 shares it: on a rendezvous channel a SEND blocks until its receive, so the wait-for graph
     *  needs the same set (one source, not a facsimile). */
    static Set<String> rendezvousChans(BlockStatement body, Set<String> chans) {
        final Set<String> out = new LinkedHashSet<String>()
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression && chans.contains(((VariableExpression) de.leftExpression).name)) {
                    Expression r = strip(de.rightExpression)
                    String mn = r instanceof MethodCallExpression ? ((MethodCallExpression) r).methodAsString :
                                (r instanceof StaticMethodCallExpression ? ((StaticMethodCallExpression) r).method : null)
                    Expression ra = r instanceof MethodCallExpression ? ((MethodCallExpression) r).arguments :
                                    (r instanceof StaticMethodCallExpression ? ((StaticMethodCallExpression) r).arguments : null)
                    if (mn == 'create' && ra instanceof TupleExpression && ((TupleExpression) ra).expressions.size() == 1) {
                        Expression cap = strip(((TupleExpression) ra).expressions.get(0))
                        if (cap instanceof ConstantExpression && ((ConstantExpression) cap).value == 0) out.add(((VariableExpression) de.leftExpression).name)
                    }
                }
                super.visitDeclarationExpression(de)
            }
        })
        out
    }

    private static void collectMixed(G g, List<Choice> out) {
        if (g instanceof Seq) for (G x : ((Seq) g).items) collectMixed(x, out)
        else if (g instanceof Loop) collectMixed(((Loop) g).body, out)
        else if (g instanceof Par) for (G x : ((Par) g).parts) collectMixed(x, out)
        else if (g instanceof Choice) {
            Choice c = (Choice) g
            Set<String> openers = new LinkedHashSet<String>()
            for (G br : c.branches) { Msg m = firstMsg(br); if (m != null) openers.add(m.from); collectMixed(br, out) }
            if (c.at == null && openers.size() > 1) out.add(c)
        }
    }

    // ── parser ─────────────────────────────────────────────────────────────────────────────────

    private static List<String> tokens(String text) {
        String noComments = text.replaceAll(/\/\/[^\n]*/, ' ')
        List<String> out = []
        java.util.regex.Matcher m = (noComments =~ /->|[{}:;]|[A-Za-z_\$][A-Za-z0-9_\$]*|\S/)
        while (m.find()) out.add(m.group())
        out
    }

    static G parse(String text, List<String> errors) {
        List<String> t = tokens(text ?: '')
        int[] pos = [0]
        G g = parseSeq(t, pos, errors, false)
        if (errors.isEmpty() && pos[0] < t.size()) errors.add("unexpected '${t[pos[0]]}' in the protocol".toString())
        g
    }

    private static G parseSeq(List<String> t, int[] pos, List<String> errors, boolean inBlock) {
        Seq seq = new Seq()
        while (pos[0] < t.size() && errors.isEmpty()) {
            String tok = t[pos[0]]
            if (tok == ';') { pos[0]++; continue }
            if (tok == '}') { if (inBlock) return seq; errors.add("unexpected '}' in the protocol"); return seq }
            if (tok == 'loop') {
                pos[0]++
                if (!expect(t, pos, '{', errors)) return seq
                Loop l = new Loop(); l.body = parseSeq(t, pos, errors, true)
                if (!expect(t, pos, '}', errors)) return seq
                seq.items.add(l); continue
            }
            if (tok == 'par') {                                            // Phase 264 — par { … } and { … }
                pos[0]++
                Par par = new Par()
                while (true) {
                    if (!expect(t, pos, '{', errors)) return seq
                    par.parts.add(parseSeq(t, pos, errors, true))
                    if (!expect(t, pos, '}', errors)) return seq
                    if (pos[0] < t.size() && t[pos[0]] == 'and') { pos[0]++; continue }
                    break
                }
                if (par.parts.size() < 2) { errors.add("a par needs at least two parts ('… } and { …')"); return seq }
                Map<String, Integer> where = [:]
                for (int pi = 0; pi < par.parts.size(); pi++) {
                    Set<String> cs = new LinkedHashSet<String>()
                    collectChans(par.parts.get(pi), cs)
                    for (String c : cs) {
                        if (where.containsKey(c) && where.get(c) != pi) { errors.add("the parts of a par must not share a channel ('${c}' is in two — independent sub-sessions only)".toString()); return seq }
                        where.put(c, pi)
                    }
                }
                seq.items.add(par); continue
            }
            if (tok == 'choice') {
                pos[0]++
                Choice c = new Choice()
                if (pos[0] < t.size() && t[pos[0]] == 'at') {                  // Phase 267 — `at` optional: without it, a MIXED choice
                    pos[0]++
                    if (pos[0] >= t.size()) { errors.add("a role is expected after 'choice at'"); return seq }
                    c.at = t[pos[0]++]
                }
                while (true) {
                    if (!expect(t, pos, '{', errors)) return seq
                    c.branches.add(parseSeq(t, pos, errors, true))
                    if (!expect(t, pos, '}', errors)) return seq
                    if (pos[0] < t.size() && t[pos[0]] == 'or') { pos[0]++; continue }
                    break
                }
                if (c.branches.size() < 2) { errors.add("a choice needs at least two branches ('… } or { …')"); return seq }
                seq.items.add(c); continue
            }
            // label : from -> to
            if (pos[0] + 4 < t.size() + 1 && t.size() >= pos[0] + 5 && t[pos[0] + 1] == ':' && t[pos[0] + 3] == '->') {
                Msg m = new Msg(); m.chan = t[pos[0]]; m.from = t[pos[0] + 2]; m.to = t[pos[0] + 4]
                pos[0] += 5
                if (m.from == m.to) { errors.add("message '${m.chan}' goes from '${m.from}' to itself".toString()); return seq }
                seq.items.add(m); continue
            }
            errors.add("cannot read the protocol at '${tok}' (expected 'label: from -> to', 'loop { … }' or 'choice at role { … } or { … }')".toString())
            return seq
        }
        if (inBlock && errors.isEmpty()) errors.add("a '}' is missing in the protocol")
        seq
    }

    private static boolean expect(List<String> t, int[] pos, String tok, List<String> errors) {
        if (pos[0] < t.size() && t[pos[0]] == tok) { pos[0]++; return true }
        errors.add("'${tok}' expected in the protocol${pos[0] < t.size() ? " at '" + t[pos[0]] + "'" : ' at its end'}".toString())
        false
    }

    private static void collectRoles(G g, Set<String> out) {
        if (g instanceof Msg) { out.add(((Msg) g).from); out.add(((Msg) g).to) }
        else if (g instanceof Seq) for (G x : ((Seq) g).items) collectRoles(x, out)
        else if (g instanceof Loop) collectRoles(((Loop) g).body, out)
        else if (g instanceof Choice) { if (((Choice) g).at != null) out.add(((Choice) g).at); for (G x : ((Choice) g).branches) collectRoles(x, out) }
        else if (g instanceof Par) for (G x : ((Par) g).parts) collectRoles(x, out)
    }

    private static void collectChans(G g, Set<String> out) {
        if (g instanceof Msg) out.add(((Msg) g).chan)
        else if (g instanceof Seq) for (G x : ((Seq) g).items) collectChans(x, out)
        else if (g instanceof Loop) collectChans(((Loop) g).body, out)
        else if (g instanceof Choice) for (G x : ((Choice) g).branches) collectChans(x, out)
        else if (g instanceof Par) for (G x : ((Par) g).parts) collectChans(x, out)
    }

    /** The first message of a global type, or null when it starts with nothing (empty). */
    private static Msg firstMsg(G g) {
        if (g instanceof Msg) return (Msg) g
        if (g instanceof Seq) { for (G x : ((Seq) g).items) { Msg m = firstMsg(x); if (m != null) return m } ; return null }
        if (g instanceof Loop) return firstMsg(((Loop) g).body)
        if (g instanceof Choice) return firstMsg(((Choice) g).branches.get(0))
        if (g instanceof Par) return firstMsg(((Par) g).parts.get(0))
        null
    }

    // ── projection (Thompson construction straight into the role's NFA) ────────────────────────

    static Frag project(G g, String role, Nfa nfa, List<String> errors) {
        if (g instanceof Msg) {
            Msg m = (Msg) g
            String label = m.from == role ? '!' + m.chan : (m.to == role ? '?' + m.chan : null)
            int a = nfa.newState()
            if (label == null) return frag(a, a)
            int b = nfa.newState(); nfa.edge(a, label, b)
            return frag(a, b)
        }
        if (g instanceof Seq) {
            int a = nfa.newState(); int cur = a
            for (G x : ((Seq) g).items) {
                Frag f = project(x, role, nfa, errors)
                nfa.edge(cur, '', f.in)
                if (f.out == null) return frag(a, null)
                cur = f.out
            }
            return frag(a, cur)
        }
        if (g instanceof Loop) {
            Frag body = project(((Loop) g).body, role, nfa, errors)
            int a = nfa.newState(), b = nfa.newState()
            nfa.edge(a, '', body.in); nfa.edge(a, '', b)
            if (body.out != null) nfa.edge(body.out, '', a)
            return frag(a, b)
        }
        if (g instanceof Choice) {
            Choice c = (Choice) g
            Set<String> openers = new LinkedHashSet<String>()
            for (G br : c.branches) {
                Msg m = firstMsg(br)
                if (m == null) { errors.add("a branch of the choice${c.at == null ? '' : " at '" + c.at + "'"} is empty".toString()); return frag(nfa.newState(), null) }
                openers.add(m.from)
                if (c.at != null && m.from != c.at) { errors.add("in a choice at '${c.at}' every branch must begin with a message from '${c.at}' — here '${m.chan}: ${m.from} -> ${m.to}' (branches opened by different roles are a MIXED choice: write it without 'at' and the coherence check decides)".toString()); return frag(nfa.newState(), null) }
            }
            if ((c.at == null ? !openers.contains(role) : role != c.at)) {     // Phase 267 — an opener's projection is the mixed union
                // an external choice: the branches must be told apart by the first message to this role, or be the same for it
                List<Set<String>> firsts = []
                List<String> shapes = []
                for (G br : c.branches) { firsts.add(firstOpsFor(br, role)); shapes.add(shape(br, role)) }
                boolean same = shapes.every { String s -> s == shapes[0] }
                boolean distinct = firsts.every { Set<String> f -> !f.isEmpty() && f.every { String l -> l.startsWith('?') } } &&
                    firsts.collect { Set<String> f -> f }.flatten().size() == new HashSet<String>(firsts.flatten() as List<String>).size()
                if (!same && !distinct) {
                    errors.add("role '${role}' cannot tell the branches of the choice${c.at == null ? '' : " at '" + c.at + "'"} apart (each branch must begin, for '${role}', with a receive on a different channel, or be the same for it)".toString())
                    return frag(nfa.newState(), null)
                }
                if (same) return project(c.branches.get(0), role, nfa, errors)
            }
            int a = nfa.newState(), b = nfa.newState()
            boolean anyOut = false
            for (G br : c.branches) {
                Frag f = project(br, role, nfa, errors)
                nfa.edge(a, '', f.in)
                if (f.out != null) { nfa.edge(f.out, '', b); anyOut = true }
            }
            return frag(a, anyOut ? b : null)
        }
        if (g instanceof Par) {                                            // Phase 264 — the shuffle of the parts
            List<Frag> fs = []
            for (G part : ((Par) g).parts) fs.add(project(part, role, nfa, errors))
            if (!errors.isEmpty()) return frag(nfa.newState(), null)
            return shuffle(fs, nfa)
        }
        frag(nfa.newState(), null)
    }

    /**
     * Phase 264 — the SHUFFLE of independent fragments (channels disjoint): a product automaton over tuples of
     * per-part states, any part free to take its next step. Regular, so the same inclusion check decides.
     */
    private static Frag shuffle(List<Frag> fs, Nfa nfa) {
        Map<String, Integer> ids = [:]
        List<int[]> todo = []
        Closure<Integer> stateOf = { int[] tuple ->
            String k = tuple.toList().join(',')
            Integer id = ids.get(k)
            if (id == null) { id = nfa.newState(); ids.put(k, id); todo.add(tuple.clone()) }
            id
        }
        int[] start = fs.collect { Frag f -> f.in } as int[]
        int inState = stateOf(start)
        Integer outState = null
        boolean allOut = fs.every { Frag f -> f.out != null }
        while (!todo.isEmpty()) {
            int[] tuple = todo.remove(0)
            int from = stateOf(tuple)
            if (allOut && (0..<fs.size()).every { int i -> tuple[i] == (int) fs.get(i).out }) {
                if (outState == null) outState = nfa.newState()
                nfa.edge(from, '', (int) outState)
            }
            for (int i = 0; i < fs.size(); i++) {
                for (Object[] e : nfa.edges.get(tuple[i])) {
                    int[] next = tuple.clone(); next[i] = (int) e[1]
                    nfa.edge(from, (String) e[0], stateOf(next), e[2] == null ? -1 : (int) e[2])
                }
            }
        }
        frag(inState, outState)
    }

    private static Frag frag(int a, Integer b) { Frag f = new Frag(); f.in = a; f.out = b; f }

    /** The op labels a global type can begin with, for a role. */
    private static Set<String> firstOpsFor(G g, String role) {
        Nfa n = new Nfa(); Frag f = project(g, role, n, [])
        Set<Integer> cl = closure(n, [f.in] as Set<Integer>)
        Set<String> out = new LinkedHashSet<String>()
        for (int s : cl) for (Object[] e : n.edges.get(s)) if (e[0] != '') out.add((String) e[0])
        out
    }

    /** A canonical text of a global type's projection onto a role (for "the same for it"). */
    private static String shape(G g, String role) {
        if (g instanceof Msg) { Msg m = (Msg) g; return m.from == role ? "!${m.chan}" : (m.to == role ? "?${m.chan}" : '') }
        if (g instanceof Seq) return ((Seq) g).items.collect { G x -> shape(x, role) }.join('')
        if (g instanceof Loop) return "(${shape(((Loop) g).body, role)})*"
        if (g instanceof Choice) return '(' + ((Choice) g).branches.collect { G x -> shape(x, role) }.join('|') + ')'
        if (g instanceof Par) return 'par(' + ((Par) g).parts.collect { G x -> shape(x, role) }.join('&') + ')'
        ''
    }

    private static void alphabet(Nfa n, Set<String> sends, Set<String> recvs) {
        for (List<Object[]> es : n.edges.values()) for (Object[] e : es) {
            String l = (String) e[0]
            if (l.startsWith('!')) sends.add(l.substring(1)) else if (l.startsWith('?')) recvs.add(l.substring(1))
        }
    }

    // ── processes: the main body and each async arm ────────────────────────────────────────────

    private static List<Object[]> processes(BlockStatement body) {
        List<Object[]> out = []
        out.add(['the main body', body.statements, body] as Object[])
        int armNo = 0
        for (Statement st : body.statements) {
            ClosureExpression cl = armOf(st)
            if (cl != null && cl.code instanceof BlockStatement) { armNo++; out.add(["the async arm at line ${st.lineNumber}".toString(), ((BlockStatement) cl.code).statements, st] as Object[]) }
        }
        out
    }

    private static ClosureExpression armOf(Statement st) {
        if (!(st instanceof ExpressionStatement)) return null
        Expression e = ((ExpressionStatement) st).expression
        if (e instanceof DeclarationExpression) e = strip(((DeclarationExpression) e).rightExpression)
        else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) e = strip(((BinaryExpression) e).rightExpression)
        Expression args = null
        if (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString == 'async') args = ((MethodCallExpression) e).arguments
        else if (e instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) e).method == 'async') args = ((StaticMethodCallExpression) e).arguments
        if (!(args instanceof ArgumentListExpression)) return null
        List<Expression> a = ((ArgumentListExpression) args).expressions
        (a.size() == 1 && a.get(0) instanceof ClosureExpression) ? (ClosureExpression) a.get(0) : null
    }

    private static Expression strip(Expression e) {
        Expression x = e
        while (x instanceof CastExpression) x = ((CastExpression) x).expression
        x
    }

    // ── a process's control flow as an automaton over its channel ops ──────────────────────────

    /** Phase 271 — how a process sends: bare `c.send(v)` vs inside an arbitrated offers-select. */
    static class OpInfo { final Set<String> bareSends = [] as Set; final Set<String> offerSends = [] as Set }

    private static Frag processAutomaton(List<Statement> stmts, Nfa n, Set<String> chans, OpInfo info) {
        Map<String, List<String>> held = [:]                    // held select var → its branches ('?c' / '!c' labels)
        seqFrag(stmts, n, chans, held, info)
    }

    private static Frag seqFrag(List<Statement> stmts, Nfa n, Set<String> chans, Map<String, List<String>> held, OpInfo info) {
        int a = n.newState(); int cur = a
        List<Statement> list = new ArrayList<Statement>(stmts)
        int i = 0
        while (i < list.size()) {
            Statement st = list.get(i)
            Frag f = null
            String altVar = altResultVar(st, chans, held)
            if (altVar != null) {
                // the ALT and the guarded blocks `if (r.index == k)` that follow it at this level: a branch each
                List<String> branches = altBranches(st, chans, held)
                Map<Integer, Statement> guarded = [:]
                int j = i + 1
                while (j < list.size()) {
                    Integer k = guardedIndex(list.get(j), altVar)
                    if (k != null) { guarded.put(k, ((IfStatement) list.get(j)).ifBlock); list.remove(j); continue }
                    if (opFree(list.get(j), chans)) { j++; continue }          // `int q = (int) r.value` between the ALT and its guards
                    break
                }
                int ca = n.newState(), cb = n.newState()
                for (int k = 0; k < branches.size(); k++) {
                    int s1 = n.newState()
                    String label = branches.get(k)
                    if (label.startsWith('!') && info != null) info.offerSends.add(label.substring(1))   // Phase 271
                    n.edge(ca, label, s1, st.lineNumber)
                    Statement gb = guarded.get(k)
                    if (gb != null) {
                        Frag gf = seqFrag(gb instanceof BlockStatement ? ((BlockStatement) gb).statements : [gb], n, chans, held, info)
                        n.edge(s1, '', gf.in)
                        if (gf.out != null) n.edge(gf.out, '', cb)
                    } else n.edge(s1, '', cb)
                }
                f = frag(ca, cb)
            } else f = stmtFrag(st, n, chans, held, info)
            i++
            if (f == null) continue
            n.edge(cur, '', f.in)
            if (f.out == null) return frag(a, null)
            cur = f.out
        }
        frag(a, cur)
    }

    /** A plain statement with no channel op in it (a local computation between an ALT and its guarded blocks). */
    private static boolean opFree(Statement st, Set<String> chans) {
        if (!(st instanceof ExpressionStatement)) return false
        opsOf(((ExpressionStatement) st).expression, chans, 0).isEmpty()
    }

    private static Frag stmtFrag(Statement st, Nfa n, Set<String> chans, Map<String, List<String>> held, OpInfo info) {
        if (st instanceof BlockStatement) return seqFrag(((BlockStatement) st).statements, n, chans, held, info)
        if (st instanceof IfStatement) {
            IfStatement is = (IfStatement) st
            Frag t = seqFrag(is.ifBlock instanceof BlockStatement ? ((BlockStatement) is.ifBlock).statements : [is.ifBlock], n, chans, held, info)
            Frag e = (is.elseBlock == null || is.elseBlock instanceof EmptyStatement) ? frag(n.newState(), null) :
                seqFrag(is.elseBlock instanceof BlockStatement ? ((BlockStatement) is.elseBlock).statements : [is.elseBlock], n, chans, held, info)
            if (is.elseBlock == null || is.elseBlock instanceof EmptyStatement) { int s = n.newState(); e = frag(s, s) }
            int a = n.newState(), b = n.newState()
            n.edge(a, '', t.in); n.edge(a, '', e.in)
            boolean any = false
            if (t.out != null) { n.edge(t.out, '', b); any = true }
            if (e.out != null) { n.edge(e.out, '', b); any = true }
            return frag(a, any ? b : null)
        }
        if (st instanceof ForStatement) {
            ForStatement fs = (ForStatement) st
            Expression coll = strip(fs.collectionExpression)
            if (coll instanceof VariableExpression && chans.contains(((VariableExpression) coll).name)) {   // a drain: (?c body)*
                int a = n.newState(), b = n.newState(), s1 = n.newState()
                n.edge(a, '?' + ((VariableExpression) coll).name, s1, st.lineNumber)
                Frag body = seqFrag(fs.loopBlock instanceof BlockStatement ? ((BlockStatement) fs.loopBlock).statements : [fs.loopBlock], n, chans, held, info)
                n.edge(s1, '', body.in)
                if (body.out != null) n.edge(body.out, '', a)
                n.edge(a, '', b)
                return frag(a, b)
            }
            return star(seqFrag(fs.loopBlock instanceof BlockStatement ? ((BlockStatement) fs.loopBlock).statements : [fs.loopBlock], n, chans, held, info), n, true)
        }
        if (st instanceof WhileStatement) {
            WhileStatement ws = (WhileStatement) st
            Expression g = ws.booleanExpression.expression
            boolean forever = g instanceof ConstantExpression && ((ConstantExpression) g).value == true
            return star(seqFrag(ws.loopBlock instanceof BlockStatement ? ((BlockStatement) ws.loopBlock).statements : [ws.loopBlock], n, chans, held, info), n, !forever)
        }
        if (st instanceof DoWhileStatement) {
            DoWhileStatement ds = (DoWhileStatement) st
            Frag once = seqFrag(ds.loopBlock instanceof BlockStatement ? ((BlockStatement) ds.loopBlock).statements : [ds.loopBlock], n, chans, held, info)
            Frag rest = star(seqFrag(ds.loopBlock instanceof BlockStatement ? ((BlockStatement) ds.loopBlock).statements : [ds.loopBlock], n, chans, held, info), n, true)
            if (once.out == null) return once
            n.edge(once.out, '', rest.in)
            return frag(once.in, rest.out)
        }
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            // a held select: `alt = ChannelSelect.from(a, b)[.fair()]`
            if (e instanceof DeclarationExpression && ((DeclarationExpression) e).leftExpression instanceof VariableExpression) {
                List<String> br = selectChainBranches(((DeclarationExpression) e).rightExpression, chans)?.collect { '?' + it }
                if (br == null) br = offersBranches(strip(((DeclarationExpression) e).rightExpression), chans)   // Phase 271
                if (br != null) { held.put(((VariableExpression) ((DeclarationExpression) e).leftExpression).name, br); int s = n.newState(); return frag(s, s) }
            }
            List<Object[]> ops = opsOf(e, chans, st.lineNumber)
            int a = n.newState(); int cur = a
            for (Object[] op : ops) { int s = n.newState(); n.edge(cur, (String) op[0], s, (int) op[1]); cur = s }
            return frag(a, cur)
        }
        int s = n.newState()
        frag(s, s)
    }

    private static Frag star(Frag body, Nfa n, boolean exits) {
        int a = n.newState(), b = n.newState()
        n.edge(a, '', body.in)
        if (body.out != null) n.edge(body.out, '', a)
        if (exits) { n.edge(a, '', b); return frag(a, b) }
        frag(a, null)
    }

    /** The ops of an expression in evaluation order: receives inside it first, then a top-level send. */
    private static List<Object[]> opsOf(Expression e, Set<String> chans, int line) {
        final List<Object[]> out = []
        e.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                super.visitMethodCallExpression(m)
                Expression r = strip(m.objectExpression)
                if (r instanceof VariableExpression && chans.contains(((VariableExpression) r).name)) {
                    String c = ((VariableExpression) r).name
                    if ((m.methodAsString == 'first' || m.methodAsString == 'receive') && noArgs(m)) out.add(['?' + c, line] as Object[])
                    else if (m.methodAsString == 'send') out.add(['!' + c, line] as Object[])   // a BARE send (opInfo marks it at the call site)
                }
            }
            @Override void visitClosureExpression(ClosureExpression c) { }          // not this process's flow
        })
        out
    }

    private static boolean noArgs(MethodCallExpression m) {
        !(m.arguments instanceof TupleExpression) || ((TupleExpression) m.arguments).expressions.isEmpty()
    }

    /** `Result r = await <select>` → r, else null. */
    private static String altResultVar(Statement st, Set<String> chans, Map<String, List<String>> held) {
        if (!(st instanceof ExpressionStatement)) return null
        Expression e = ((ExpressionStatement) st).expression
        if (!(e instanceof DeclarationExpression) || !(((DeclarationExpression) e).leftExpression instanceof VariableExpression)) return null
        altBranches(st, chans, held) == null ? null : ((VariableExpression) ((DeclarationExpression) e).leftExpression).name
    }

    private static List<String> altBranches(Statement st, Set<String> chans, Map<String, List<String>> held) {
        Expression rhs = strip(((DeclarationExpression) ((ExpressionStatement) st).expression).rightExpression)
        Expression sel = awaited(rhs)
        if (!(sel instanceof MethodCallExpression) || ((MethodCallExpression) sel).methodAsString != 'select') return null
        Expression recv = strip(((MethodCallExpression) sel).objectExpression)
        if (recv instanceof VariableExpression && held.containsKey(((VariableExpression) recv).name)) return held.get(((VariableExpression) recv).name)
        List<String> from = selectChainBranches(recv, chans)
        if (from != null) return from.collect { '?' + it }
        offersBranches(recv, chans)                              // Phase 271 — GROOVY-12323's arbitrated select
    }

    /** Phase 271 — `ChannelSelect.offers(send(a, v), receive(b))[…]` → mixed labels ['!a', '?b'], else null. */
    private static List<String> offersBranches(Expression e, Set<String> chans) {
        Expression x = strip(e)
        while (x instanceof MethodCallExpression && (((MethodCallExpression) x).methodAsString == 'fair' || ((MethodCallExpression) x).methodAsString == 'random')) x = strip(((MethodCallExpression) x).objectExpression)
        Expression args = null
        if (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'offers') args = ((MethodCallExpression) x).arguments
        else if (x instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) x).method == 'offers') args = ((StaticMethodCallExpression) x).arguments
        if (!(args instanceof TupleExpression)) return null
        List<String> out = []
        for (Expression a : ((TupleExpression) args).expressions) {
            Expression o = strip(a)
            String kind = o instanceof MethodCallExpression ? ((MethodCallExpression) o).methodAsString :
                          (o instanceof StaticMethodCallExpression ? ((StaticMethodCallExpression) o).method : null)
            Expression oa = o instanceof MethodCallExpression ? ((MethodCallExpression) o).arguments :
                            (o instanceof StaticMethodCallExpression ? ((StaticMethodCallExpression) o).arguments : null)
            if (!(kind in ['send', 'receive']) || !(oa instanceof TupleExpression) || ((TupleExpression) oa).expressions.isEmpty()) return null
            Expression c = strip(((TupleExpression) oa).expressions.get(0))
            if (!(c instanceof VariableExpression) || !chans.contains(((VariableExpression) c).name)) return null
            out.add((kind == 'send' ? '!' : '?') + ((VariableExpression) c).name)
        }
        out.isEmpty() ? null : out
    }

    private static Expression awaited(Expression e) {
        Expression args = null
        if (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString == 'await') args = ((MethodCallExpression) e).arguments
        else if (e instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) e).method == 'await') args = ((StaticMethodCallExpression) e).arguments
        if (!(args instanceof TupleExpression) || ((TupleExpression) args).expressions.size() != 1) return null
        strip(((TupleExpression) args).expressions.get(0))
    }

    /** `ChannelSelect.from(a, b)[.fair()|.random()]` → [a, b], else null. */
    private static List<String> selectChainBranches(Expression e, Set<String> chans) {
        Expression x = strip(e)
        while (x instanceof MethodCallExpression && (((MethodCallExpression) x).methodAsString == 'fair' || ((MethodCallExpression) x).methodAsString == 'random')) x = strip(((MethodCallExpression) x).objectExpression)
        Expression args = null
        if (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'from') args = ((MethodCallExpression) x).arguments
        else if (x instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) x).method == 'from') args = ((StaticMethodCallExpression) x).arguments
        if (!(args instanceof TupleExpression)) return null
        List<String> out = []
        for (Expression a : ((TupleExpression) args).expressions) {
            Expression v = strip(a)
            if (!(v instanceof VariableExpression) || !chans.contains(((VariableExpression) v).name)) return null
            out.add(((VariableExpression) v).name)
        }
        out.isEmpty() ? null : out
    }

    /** `if (r.index == k) { … }` with no else → k, else null. */
    private static Integer guardedIndex(Statement st, String altVar) {
        if (!(st instanceof IfStatement)) return null
        IfStatement is = (IfStatement) st
        if (is.elseBlock != null && !(is.elseBlock instanceof EmptyStatement)) return null
        Expression g = strip(is.booleanExpression.expression)
        if (!(g instanceof BinaryExpression) || ((BinaryExpression) g).operation.type != Types.COMPARE_EQUAL) return null
        Expression l = strip(((BinaryExpression) g).leftExpression), r = strip(((BinaryExpression) g).rightExpression)
        boolean onIndex = l instanceof PropertyExpression && ((PropertyExpression) l).propertyAsString == 'index' &&
            strip(((PropertyExpression) l).objectExpression) instanceof VariableExpression && ((VariableExpression) strip(((PropertyExpression) l).objectExpression)).name == altVar
        if (!onIndex || !(r instanceof ConstantExpression) || !(((ConstantExpression) r).value instanceof Number)) return null
        ((Number) ((ConstantExpression) r).value).intValue()
    }

    // ── conformance: L(process) ⊆ L(local type) ────────────────────────────────────────────────

    private static Set<Integer> closure(Nfa n, Set<Integer> states) {
        Set<Integer> out = new HashSet<Integer>(states)
        List<Integer> todo = new ArrayList<Integer>(states)
        while (!todo.isEmpty()) {
            int s = todo.remove(0)
            for (Object[] e : n.edges.get(s)) if (e[0] == '' && out.add((Integer) e[1])) todo.add((Integer) e[1])
        }
        out
    }

    private static Set<Integer> step(Nfa n, Set<Integer> states, String label) {
        Set<Integer> out = new HashSet<Integer>()
        for (int s : states) for (Object[] e : n.edges.get(s)) if (e[0] == label) out.add((Integer) e[1])
        closure(n, out)
    }

    private static String pretty(String label) {
        label.startsWith('!') ? "sends on '${label.substring(1)}'" : "receives from '${label.substring(1)}'"
    }

    /** null when the process conforms; else what it does that the protocol does not allow, with its trace. */
    private static String conforms(Nfa p, Frag pf, Nfa l, Frag lf) {
        // product search: (process state, local DFA state = set of NFA states), with parents for the trace
        Map<String, Object[]> seen = [:]                       // key → [pState, lSet, parentKey, label]
        List<Object[]> todo = []
        Set<Integer> l0 = closure(l, [lf.in] as Set<Integer>)
        Set<Integer> p0 = closure(p, [pf.in] as Set<Integer>)
        for (int ps : p0) { String k = ps + '|' + l0.sort().join(','); if (!seen.containsKey(k)) { seen.put(k, [ps, l0, null, null] as Object[]); todo.add(seen.get(k)) } }
        while (!todo.isEmpty()) {
            Object[] cur = todo.remove(0)
            int ps = (int) cur[0]; Set<Integer> ls = (Set<Integer>) cur[1]
            String curKey = ps + '|' + ls.sort().join(',')
            // the process may end here (an exit state): the protocol must be able to end too
            if (pf.out != null && ps == (int) pf.out && lf.out != null && !ls.contains((int) lf.out)) {
                return "ends (${trace(seen, curKey)}) where the protocol still expects it to ${expectedText(l, ls)}".toString()
            }
            for (Object[] e : p.edges.get(ps)) {
                String label = (String) e[0]
                int to = (int) e[1]
                if (label == '') {
                    String k = to + '|' + ls.sort().join(',')
                    if (!seen.containsKey(k)) { seen.put(k, [to, ls, curKey, null] as Object[]); todo.add(seen.get(k)) }
                    continue
                }
                Set<Integer> next = step(l, ls, label)
                if (next.isEmpty()) {
                    String tr = trace(seen, curKey)
                    return "${pretty(label)} (line ${e[2]})${tr.isEmpty() ? '' : ' after ' + tr} where the protocol expects it to ${expectedText(l, ls)}".toString()
                }
                for (int q : closure(p, [to] as Set<Integer>)) {
                    String k = q + '|' + next.sort().join(',')
                    if (!seen.containsKey(k)) { seen.put(k, [q, next, curKey, label] as Object[]); todo.add(seen.get(k)) }
                }
            }
        }
        null
    }

    private static String expectedText(Nfa l, Set<Integer> ls) {
        Set<String> labels = new LinkedHashSet<String>()
        for (int s : ls) for (Object[] e : l.edges.get(s)) if (e[0] != '') labels.add(pretty((String) e[0]))
        labels.isEmpty() ? 'end' : labels.join(' or ')
    }

    private static String trace(Map<String, Object[]> seen, String key) {
        List<String> ops = []
        String k = key
        int guard = 0
        while (k != null && guard++ < 10000) {
            Object[] node = seen.get(k)
            if (node[3] != null) ops.add(0, pretty((String) node[3]))
            k = (String) node[2]
        }
        ops.isEmpty() ? '' : "it ${ops.join(', then ')}".toString()
    }
}
