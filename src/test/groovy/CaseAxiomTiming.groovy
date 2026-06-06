import com.microsoft.z3.*
import groovy.transform.CompileStatic

@CompileStatic
class CaseAxiomTiming {

    static void main(String[] args) {
        // Scenarios:
        //   "literal-only"     — pin "Hello"'s upper/lower forms, check Hello.upper == "hello" (UNSAT).
        //   "+ length axioms"  — add length-preservation universals.
        //   "+ all 6 axioms"   — add idempotence and cascade too (what Phase 47g started with).
        //   "+ symbolic len"   — check symbolic s.upper.length == s.length under length axiom.
        runScenario('literal-only', false, false)
        runScenario('+ length axioms only (2)', true, false)
        runScenario('+ all 6 axioms', true, true)
        runScenarioSymbolicLength()
    }

    static void runScenario(String name, boolean lengthAxioms, boolean allAxioms) {
        Context ctx = new Context()
        Solver solver = ctx.mkSolver()
        Params p = ctx.mkParams()
        p.add('timeout', 60000)   // 60 seconds — we want to see how long it actually takes.
        solver.setParameters(p)

        Sort strSort = ctx.mkStringSort()
        FuncDecl up = ctx.mkFuncDecl('toUpper$', [strSort] as Sort[], strSort)
        FuncDecl lo = ctx.mkFuncDecl('toLower$', [strSort] as Sort[], strSort)

        // Pin literal "Hello", "HELLO", "hello".
        Expr lHello = ctx.mkString('Hello')
        Expr lHELLO = ctx.mkString('HELLO')
        Expr lhello = ctx.mkString('hello')
        solver.add(ctx.mkEq(ctx.mkApp(up, lHello), lHELLO))
        solver.add(ctx.mkEq(ctx.mkApp(lo, lHello), lhello))
        solver.add(ctx.mkEq(ctx.mkApp(up, lHELLO), lHELLO))
        solver.add(ctx.mkEq(ctx.mkApp(lo, lHELLO), lhello))
        solver.add(ctx.mkEq(ctx.mkApp(up, lhello), lHELLO))
        solver.add(ctx.mkEq(ctx.mkApp(lo, lhello), lhello))

        if (lengthAxioms) {
            // ∀s. length(toUpper(s)) == length(s)
            Expr s = ctx.mkConst('q$s1', strSort)
            Expr applyUp = ctx.mkApp(up, s)
            BoolExpr lenUp = ctx.mkEq(ctx.mkLength((Expr) applyUp), ctx.mkLength((Expr) s))
            solver.add((BoolExpr) ctx.mkForall([s] as Expr[], lenUp, 1,
                [ctx.mkPattern(applyUp)] as Pattern[], (Expr[]) null,
                (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))

            Expr applyLo = ctx.mkApp(lo, s)
            BoolExpr lenLo = ctx.mkEq(ctx.mkLength((Expr) applyLo), ctx.mkLength((Expr) s))
            solver.add((BoolExpr) ctx.mkForall([s] as Expr[], lenLo, 1,
                [ctx.mkPattern(applyLo)] as Pattern[], (Expr[]) null,
                (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
        }

        if (allAxioms) {
            // Idempotence + cascade.
            Expr s = ctx.mkConst('q$s2', strSort)
            Expr applyUp = ctx.mkApp(up, s)
            Expr applyLo = ctx.mkApp(lo, s)
            Expr applyUpUp = ctx.mkApp(up, applyUp)
            solver.add((BoolExpr) ctx.mkForall([s] as Expr[], ctx.mkEq(applyUpUp, applyUp), 1,
                [ctx.mkPattern(applyUpUp)] as Pattern[], (Expr[]) null,
                (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
            Expr applyLoLo = ctx.mkApp(lo, applyLo)
            solver.add((BoolExpr) ctx.mkForall([s] as Expr[], ctx.mkEq(applyLoLo, applyLo), 1,
                [ctx.mkPattern(applyLoLo)] as Pattern[], (Expr[]) null,
                (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
            Expr applyUpLo = ctx.mkApp(up, applyLo)
            solver.add((BoolExpr) ctx.mkForall([s] as Expr[], ctx.mkEq(applyUpLo, applyUp), 1,
                [ctx.mkPattern(applyUpLo)] as Pattern[], (Expr[]) null,
                (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
            Expr applyLoUp = ctx.mkApp(lo, applyUp)
            solver.add((BoolExpr) ctx.mkForall([s] as Expr[], ctx.mkEq(applyLoUp, applyLo), 1,
                [ctx.mkPattern(applyLoUp)] as Pattern[], (Expr[]) null,
                (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
        }

        // The conjecture mirrors the verifier path: assert NEG of the postcondition. The
        // postcondition is {@code result == "hello"} where result = {@code toUpper("Hello")}.
        // NEG: {@code toUpper("Hello") != "hello"}. Expecting SAT (any model where the
        // pinned upper form "HELLO" appears and "hello" is "hello" suffices).
        solver.add((BoolExpr) ctx.mkNot(ctx.mkEq(ctx.mkApp(up, lHello), lhello)))

        long start = System.nanoTime()
        Status status = solver.check()
        long elapsed = (long)((System.nanoTime() - start) / 1_000_000L)

        println "${name}: status=${status} time=${elapsed}ms"
        ctx.close()
    }

    static void runScenarioSymbolicLength() {
        // The OTHER timeout case: s.toUpperCase().length() == s.length() under length axiom.
        Context ctx = new Context()
        Solver solver = ctx.mkSolver()
        Params p = ctx.mkParams()
        p.add('timeout', 60000)
        solver.setParameters(p)

        Sort strSort = ctx.mkStringSort()
        FuncDecl up = ctx.mkFuncDecl('toUpper$', [strSort] as Sort[], strSort)

        // Length axiom.
        Expr q = ctx.mkConst('q$s', strSort)
        Expr applyUp = ctx.mkApp(up, q)
        BoolExpr lenUp = ctx.mkEq(ctx.mkLength((Expr) applyUp), ctx.mkLength((Expr) q))
        solver.add((BoolExpr) ctx.mkForall([q] as Expr[], lenUp, 1,
            [ctx.mkPattern(applyUp)] as Pattern[], (Expr[]) null,
            (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))

        // Conjecture negation: there exists s with length(toUpper(s)) != length(s).
        Expr s = ctx.mkConst('s', strSort)
        Expr applyUpS = ctx.mkApp(up, s)
        solver.add((BoolExpr) ctx.mkNot(ctx.mkEq(ctx.mkLength((Expr) applyUpS), ctx.mkLength((Expr) s))))

        long start = System.nanoTime()
        Status status = solver.check()
        long elapsed = (long)((System.nanoTime() - start) / 1_000_000L)

        println "symbolic length-preservation: status=${status} time=${elapsed}ms"
        ctx.close()
    }
}
