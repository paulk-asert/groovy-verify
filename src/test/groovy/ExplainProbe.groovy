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
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.IntExpr
import com.microsoft.z3.Params
import com.microsoft.z3.Solver
import com.microsoft.z3.Status
import groovy.transform.CompileStatic

/**
 * PROTOTYPE — the "explain a positive result" path (the one harvestable idea from Lohika: make a verification
 * say *why*, not just ✓). Stands in for one method's obligations rather than wiring the whole encoder: it models,
 * faithfully in the real Z3, the facts in scope for
 *
 *     {@code @Requires({ a != null && i >= 0 && i < a.length && i != 7 })}
 *     {@code static int get(int[] a, int i) { a[i] }}
 *
 * and asks, per body obligation, which of those clauses the proof actually *used*. One clause ({@code i != 7})
 * is deliberately redundant, to show the hygiene signal. Run: {@code ./gradlew explainProbe}
 *
 * <p>It runs the question two ways, to contrast the route that killed v1 with the route that revives it:
 * <ul>
 *   <li><b>unsat-core (v1)</b> — Z3's native core via {@code assertAndTrack} + {@code unsat_core=true}. Correct
 *       here, but {@code unsat_core=true} is a genuinely <i>weaker</i> solver mode: the FP / quantifier / string /
 *       set / map proofs that need the full solver stopped closing in it, so v1 could only ever explain the
 *       linear-integer / boolean fragment. That weakening was the blocker.</li>
 *   <li><b>ablation (v2)</b> — a plain, <i>full-strength</i> solver, minimised by drop-one-and-re-prove: a fact is
 *       load-bearing iff removing it makes the proof fail. It <i>never</i> sets {@code unsat_core=true}, so it
 *       covers the WHOLE fragment; the cost is O(n) re-proofs per goal, irrelevant in interactive use. This is the
 *       route an eventual {@code VERIFY_EXPLAIN} would take.</li>
 * </ul>
 *
 * <p>Both paths are pure downstream read-outs over an already-decided proof — separate solver instances over the
 * same facts. That is what makes the feature OFF-byte-identical by construction (the main proof solver is never
 * touched, never weakened) and unable to change a verify/refute. Incomplete fact capture fails <i>closed</i>:
 * {@link #proves} returns false → "no explanation", never a wrong one.
 */
@CompileStatic
class ExplainProbe {

    /** A fact in scope: its display label, the SMT constraint, and whether it's an author clause (vs a structural axiom). */
    static class Clause {
        String id; String label; BoolExpr constraint; boolean authored
    }

    static Clause clause(String id, String label, BoolExpr c, boolean authored) {
        Clause cl = new Clause(); cl.id = id; cl.label = label; cl.constraint = c; cl.authored = authored; cl
    }

    static void main(String[] args) {
        Context ctx = new Context()
        IntExpr i = (IntExpr) ctx.mkIntConst('i')
        IntExpr len = (IntExpr) ctx.mkIntConst('len')          // a.length
        BoolExpr aNonNull = ctx.mkBoolConst('aNonNull')        // models `a != null`

        List<Clause> facts = [
            clause('req_nonnull', '@Requires  a != null',     aNonNull,                                  true),
            clause('req_lo',      '@Requires  i >= 0',         ctx.mkGe(i, ctx.mkInt(0)),                 true),
            clause('req_hi',      '@Requires  i < a.length',   ctx.mkLt(i, len),                          true),
            clause('req_ne7',     '@Requires  i != 7',         ctx.mkNot(ctx.mkEq(i, ctx.mkInt(7))),      true),
            clause('ax_len',      'axiom      a.length >= 0',  ctx.mkGe(len, ctx.mkInt(0)),               false),
        ]

        // The two implicit obligations the body `a[i]` raises.
        LinkedHashMap<String, BoolExpr> goals = [:]
        goals['a[i]  — index in bounds']   = (BoolExpr) ctx.mkAnd(ctx.mkGe(i, ctx.mkInt(0)), ctx.mkLt(i, len))
        goals['a[i]  — receiver non-null'] = aNonNull

        // Strategy A — native unsat core (v1). Needs the weaker `unsat_core=true` mode.
        int[] solvesA = [0]
        runStrategy('unsat-core (v1 — weaker solver mode)', facts, goals) { List<Clause> fs, BoolExpr g ->
            solvesA[0] += 1
            proveAndCore(ctx, fs, g)
        }
        println "    [${solvesA[0]} solve(s), all in unsat_core mode]"

        // Strategy B — ablation (v2). Plain full-strength solver, drop-one-and-re-prove.
        int[] solvesB = [0]
        runStrategy('ablation (v2 — full-strength, drop-one)', facts, goals) { List<Clause> fs, BoolExpr g ->
            proveAndAblate(ctx, fs, g, solvesB)
        }
        println "    [${solvesB[0]} solve(s), none in unsat_core mode — full solver throughout]"

        println '\n' + ('─' * 60)
        println 'what this shows for an eventual VERIFY_EXPLAIN:'
        println '  • both paths agree (req_lo, req_hi, req_nonnull load-bearing; i != 7 is not),'
        println '    but ablation reaches the answer with the FULL solver — never the weaker mode'
        println '    that lost v1 the FP / quantifier / string proofs.'
        println '  • each explanation is a separate downstream solve over the same facts → OFF is'
        println '    byte-identical by construction, and EXPLAIN cannot change a verify/refute.'
        println '  • incomplete fact capture fails closed: proves()==false → "no explanation".'
        ctx.close()
    }

    /** Run one explanation strategy over every goal and print its per-obligation cores + aggregate hygiene. */
    static void runStrategy(String title, List<Clause> facts,
                            LinkedHashMap<String, BoolExpr> goals, Closure<Set<String>> coreFn) {
        println '\n── explain: ' + title + ' ' + ('─' * Math.max(4, 50 - title.length()))
        Set<String> everUsed = new LinkedHashSet<String>()
        goals.each { String name, BoolExpr goal ->
            Set<String> core = coreFn.call(facts, goal)
            if (core == null) {
                println "\n✓ ${name}\n    (proof not reproducible from captured facts — no explanation available)"
                return
            }
            everUsed.addAll(core)
            printExplain(name, facts, core)
        }
        // Aggregate hygiene: an authored clause in NO core across all obligations was never load-bearing.
        List<Clause> dead = facts.findAll { it.authored && !everUsed.contains(it.id) }
        if (dead) {
            println '\nspec hygiene:'
            dead.each {
                String pred = it.label.replaceFirst(/@Requires\s+/, '')
                println "  • ${pred} — not load-bearing for any proof here (still enforced at runtime; may matter to callers)"
            }
        }
    }

    /** v1 — discharge {@code goal} by refutation against the tracked facts; return the ids Z3 reports in the
     *  unsat core. Requires the weaker {@code unsat_core=true} solver mode. */
    static Set<String> proveAndCore(Context ctx, List<Clause> facts, BoolExpr goal) {
        Solver s = ctx.mkSolver()
        Params p = ctx.mkParams(); p.add('unsat_core', true); s.setParameters(p)
        facts.each { s.assertAndTrack(it.constraint, ctx.mkBoolConst(it.id)) }
        s.add((BoolExpr) ctx.mkNot(goal))   // the negated goal is always needed — not tracked
        Set<String> core = new LinkedHashSet<String>()
        if (s.check() == Status.UNSATISFIABLE) for (Expr e : s.getUnsatCore()) core.add(e.toString())
        core
    }

    /** v2 — prove {@code goal} at FULL strength (no unsat_core mode), then find the load-bearing facts by
     *  drop-one-and-re-prove: a fact is load-bearing iff removing it makes the proof fail. Returns the
     *  load-bearing ids, or {@code null} if the proof doesn't even close with every fact present (→ "no
     *  explanation"). {@code solveCount[0]} is incremented per solve so the caller can show the O(n) cost.
     *
     *  Drop-one yields the <i>individually necessary</i> clauses — exactly the redundant-clause hygiene signal
     *  (here, that {@code i != 7} carries no weight). A true minimal unsat subset needs more when two clauses are
     *  each independently sufficient (drop-one would call both unnecessary); the canonical case has no such
     *  overlap, and the eventual feature can escalate to a full MUS pass only when it matters. */
    static Set<String> proveAndAblate(Context ctx, List<Clause> facts, BoolExpr goal, int[] solveCount) {
        if (!proves(ctx, facts, goal, solveCount)) return null     // can't reproduce the proof → no explanation
        Set<String> needed = new LinkedHashSet<String>()
        for (Clause f : facts) {
            List<Clause> without = facts.findAll { it.id != f.id }
            if (!proves(ctx, without, goal, solveCount)) needed.add(f.id)   // removing f broke it → load-bearing
        }
        needed
    }

    /** A fresh, full-strength solver (no params, no tracking): assert every fact + the negated goal; UNSAT means
     *  the goal is proved. This is the same solver shape the engine uses for the real proof — never weakened. */
    static boolean proves(Context ctx, List<Clause> facts, BoolExpr goal, int[] solveCount) {
        solveCount[0] += 1
        Solver s = ctx.mkSolver()
        facts.each { s.add(it.constraint) }
        s.add((BoolExpr) ctx.mkNot(goal))
        s.check() == Status.UNSATISFIABLE
    }

    static void printExplain(String obligation, List<Clause> facts, Set<String> core) {
        println "\n✓ ${obligation}"
        println '    proved using:'
        facts.findAll { core.contains(it.id) }.each { println "      ${it.label}" }
        List<Clause> unused = facts.findAll { it.authored && !core.contains(it.id) }
        if (unused) {
            println '    not load-bearing for this obligation:'
            unused.each { println "      ${it.label}" }
        }
    }
}
