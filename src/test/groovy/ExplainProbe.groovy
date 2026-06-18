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
 * PROTOTYPE — the "explain a positive result" path via Z3 unsat cores (the one harvestable idea from Lohika:
 * make a verification say *why*, not just ✓). Stands in for one method's obligations rather than wiring the
 * whole encoder: it models, faithfully in the real Z3, the facts in scope for
 *
 *     {@code @Requires({ a != null && i >= 0 && i < a.length && i != 7 })}
 *     {@code static int get(int[] a, int i) { a[i] }}
 *
 * and asks, per body obligation, which of those clauses the proof actually *used* (the unsat core). One clause
 * ({@code i != 7}) is deliberately redundant, to show the hygiene signal. Run: {@code ./gradlew explainProbe}
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
        goals['a[i]  — index in bounds']  = (BoolExpr) ctx.mkAnd(ctx.mkGe(i, ctx.mkInt(0)), ctx.mkLt(i, len))
        goals['a[i]  — receiver non-null'] = aNonNull

        println '── explain (unsat-core) prototype ' + ('─' * 40)
        Set<String> everUsed = new LinkedHashSet<String>()
        goals.each { String name, BoolExpr goal ->
            Set<String> core = proveAndCore(ctx, facts, goal)
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
        ctx.close()
    }

    /** Discharge {@code goal} by refutation against the tracked facts; return the fact-ids Z3 reports in the unsat core. */
    static Set<String> proveAndCore(Context ctx, List<Clause> facts, BoolExpr goal) {
        Solver s = ctx.mkSolver()
        Params p = ctx.mkParams(); p.add('unsat_core', true); s.setParameters(p)
        facts.each { s.assertAndTrack(it.constraint, ctx.mkBoolConst(it.id)) }
        s.add((BoolExpr) ctx.mkNot(goal))   // the negated goal is always needed — not tracked
        Set<String> core = new LinkedHashSet<String>()
        if (s.check() == Status.UNSATISFIABLE) for (Expr e : s.getUnsatCore()) core.add(e.toString())
        core
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
