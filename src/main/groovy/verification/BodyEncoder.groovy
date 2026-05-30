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
import groovy.transform.TupleConstructor
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.EmptyExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Types

/** A guard fact harvested from an enclosing {@code if} on a path. */
@CompileStatic
@TupleConstructor
class Guard {
    Expression cond
    boolean positive
}

/** A single-assignment step on a path: {@code name == rhs}. */
@CompileStatic
@TupleConstructor
class Assign {
    String name
    Expression rhs
}

/**
 * One straight-line execution path through a method body: an ordered
 * list of {@link Guard}/{@link Assign} steps and the expression whose
 * value the method returns on this path.
 */
@CompileStatic
class Path {
    final List<Object> steps = []
    Expression result
}

/** Result of walking a statement list: terminated paths plus fall-through paths. */
@CompileStatic
class WalkResult {
    final List<Path> terminated = []
    final List<Path> live = []
}

/** Raised when the body uses a construct outside the v2a fragment. */
@CompileStatic
class UnsupportedConstructException extends RuntimeException {
    UnsupportedConstructException(String message) { super(message) }
}

/**
 * Enumerates the execution paths of a method body for postcondition
 * checking. Rather than the SSA-store-with-merge the roadmap sketches,
 * this forks at each {@code if} and threads a per-path step list, so no
 * join-point merge (and no {@code ite}) is ever needed: each path is
 * straight-line by construction. Path count is exponential in the
 * number of branches — fine for small methods, and the caller can cap
 * it. Anything outside the supported fragment raises
 * {@link UnsupportedConstructException}, which the checker turns into a
 * loud "skipped postcondition" rather than a silent pass.
 *
 * Supported (v2a): blocks, {@code if}/{@code else}, single-assignment
 * local declarations and assignments, explicit {@code return}, and the
 * Groovy implicit return (the trailing expression of the body or of a
 * branch in tail position). Loops, switch, try/catch, re-assignment and
 * multi-variable declarations are deliberately out of scope.
 */
@CompileStatic
class BodyEncoder {

    static List<Path> enumeratePaths(Statement body) {
        WalkResult r = walkStatements(asList(body), [new Path()] as List<Path>, true)
        if (!r.live.isEmpty()) {
            throw new UnsupportedConstructException(
                "method may complete without returning a value on some path")
        }
        if (r.terminated.isEmpty()) {
            throw new UnsupportedConstructException("no return path found")
        }
        return r.terminated
    }

    private static WalkResult walkStatements(List<Statement> stmts,
                                             List<Path> incoming,
                                             boolean tailContext) {
        WalkResult res = new WalkResult()
        List<Path> current = new ArrayList<Path>(incoming)
        if (stmts.isEmpty()) {
            res.live.addAll(current)
            return res
        }
        for (int i = 0; i < stmts.size(); i++) {
            Statement s = stmts.get(i)
            boolean tail = tailContext && (i == stmts.size() - 1)
            List<Path> next = new ArrayList<Path>()
            for (Path p : current) {
                WalkResult r = walkOne(s, p, tail)
                res.terminated.addAll(r.terminated)
                next.addAll(r.live)
            }
            current = next
            if (current.isEmpty()) break  // everything returned; rest is dead code
        }
        res.live.addAll(current)
        return res
    }

    private static WalkResult walkOne(Statement s, Path prefix, boolean tail) {
        WalkResult res = new WalkResult()

        if (s instanceof BlockStatement) {
            return walkStatements(asList(s), [prefix] as List<Path>, tail)
        }

        if (s instanceof ReturnStatement) {
            Path np = copy(prefix)
            np.result = ((ReturnStatement) s).expression
            res.terminated.add(np)
            return res
        }

        if (s instanceof IfStatement) {
            IfStatement ifs = (IfStatement) s
            Expression cond = ifs.booleanExpression

            Path pThen = copy(prefix)
            pThen.steps.add(new Guard(cond, true))
            WalkResult rThen = walkStatements(asList(ifs.ifBlock), [pThen] as List<Path>, tail)
            res.terminated.addAll(rThen.terminated)
            res.live.addAll(rThen.live)

            Statement elseBlk = ifs.elseBlock
            boolean hasElse = elseBlk != null && !(elseBlk instanceof EmptyStatement)
            Path pElse = copy(prefix)
            pElse.steps.add(new Guard(cond, false))
            if (hasElse) {
                WalkResult rElse = walkStatements(asList(elseBlk), [pElse] as List<Path>, tail)
                res.terminated.addAll(rElse.terminated)
                res.live.addAll(rElse.live)
            } else if (tail) {
                throw new UnsupportedConstructException(
                    "'if' in return position needs an 'else' branch (line ${ifs.lineNumber})")
            } else {
                res.live.add(pElse)  // false path falls through to following statements
            }
            return res
        }

        if (s instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) s).expression

            if (e instanceof DeclarationExpression) {
                DeclarationExpression de = (DeclarationExpression) e
                if (!(de.leftExpression instanceof VariableExpression)) {
                    throw new UnsupportedConstructException(
                        "multi-variable declaration unsupported (line ${s.lineNumber})")
                }
                String name = ((VariableExpression) de.leftExpression).name
                Expression rhs = de.rightExpression
                if (rhs == null || rhs instanceof EmptyExpression) {
                    throw new UnsupportedConstructException(
                        "uninitialised local '${name}' (line ${s.lineNumber})")
                }
                Path np = copy(prefix)
                ensureSingleAssign(np, name)
                np.steps.add(new Assign(name, rhs))
                if (tail) {
                    np.result = new VariableExpression(name)
                    res.terminated.add(np)
                } else {
                    res.live.add(np)
                }
                return res
            }

            if (e instanceof BinaryExpression &&
                ((BinaryExpression) e).operation.type == Types.ASSIGN) {
                BinaryExpression be = (BinaryExpression) e
                if (!(be.leftExpression instanceof VariableExpression)) {
                    throw new UnsupportedConstructException(
                        "assignment to a non-variable target (line ${s.lineNumber})")
                }
                String name = ((VariableExpression) be.leftExpression).name
                Path np = copy(prefix)
                ensureSingleAssign(np, name)
                np.steps.add(new Assign(name, be.rightExpression))
                if (tail) {
                    np.result = be.leftExpression
                    res.terminated.add(np)
                } else {
                    res.live.add(np)
                }
                return res
            }

            // A plain expression is only meaningful as the implicit return.
            if (tail) {
                Path np = copy(prefix)
                np.result = e
                res.terminated.add(np)
                return res
            }
            throw new UnsupportedConstructException(
                "statement with no modelled effect (line ${s.lineNumber})")
        }

        throw new UnsupportedConstructException(
            "unsupported statement ${s.class.simpleName} (line ${s.lineNumber})")
    }

    private static void ensureSingleAssign(Path p, String name) {
        for (Object step : p.steps) {
            if (step instanceof Assign && ((Assign) step).name == name) {
                throw new UnsupportedConstructException(
                    "re-assignment of '${name}' (v2a supports single-assignment locals only)")
            }
        }
    }

    private static Path copy(Path p) {
        Path n = new Path()
        n.steps.addAll(p.steps)
        n.result = p.result
        return n
    }

    private static List<Statement> asList(Statement s) {
        if (s == null) return Collections.<Statement> emptyList()
        if (s instanceof BlockStatement) {
            return new ArrayList<Statement>(((BlockStatement) s).statements)
        }
        return [s] as List<Statement>
    }
}
