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
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ClassCodeVisitorSupport
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.control.SourceUnit

/**
 * One fact harvested from an enclosing {@code if} statement.
 * {@code inThenBranch == true}  → the condition holds.
 * {@code inThenBranch == false} → the negation of the condition holds.
 */
@CompileStatic
@TupleConstructor
class IfFact {
    Expression condition
    boolean inThenBranch
}

/**
 * Walks a method body once and records, for every call expression,
 * the chain of enclosing {@code if} statements with their branch
 * polarity. Used by {@link VerifyChecker} to assemble path conditions
 * at call sites without needing parent pointers on AST nodes.
 *
 * This is the "what facts hold here?" oracle. Loops and try/catch
 * are not yet modeled — extending to {@code while}/{@code for} is a
 * straightforward next step (push the loop guard as a fact in the
 * body, with the catch that it's only conjectural across iterations
 * unless we have an {@code @Invariant}).
 */
@CompileStatic
class PathFacts extends ClassCodeVisitorSupport {

    final Map<ASTNode, List<IfFact>> factsForCall = new IdentityHashMap<>()
    private final Deque<IfFact> stack = new ArrayDeque<>()

    @Override
    void visitIfElse(IfStatement ifs) {
        // Visit the condition itself with the OUTER fact stack — a
        // call inside the condition doesn't get to assume the condition.
        ifs.booleanExpression?.visit(this)

        if (ifs.ifBlock != null) {
            stack.push(new IfFact(ifs.booleanExpression, true))
            try { ifs.ifBlock.visit(this) } finally { stack.pop() }
        }
        if (ifs.elseBlock != null) {
            stack.push(new IfFact(ifs.booleanExpression, false))
            try { ifs.elseBlock.visit(this) } finally { stack.pop() }
        }
    }

    private void recordFacts(ASTNode node) {
        factsForCall.put(node, new ArrayList<IfFact>(stack))
    }

    @Override
    void visitMethodCallExpression(MethodCallExpression mce) {
        recordFacts(mce)
        super.visitMethodCallExpression(mce)
    }

    @Override
    void visitStaticMethodCallExpression(StaticMethodCallExpression smce) {
        recordFacts(smce)
        super.visitStaticMethodCallExpression(smce)
    }

    /** Look up facts for a given call. Empty list = unconditional context. */
    List<IfFact> factsAt(ASTNode call) {
        List<IfFact> r = factsForCall.get(call)
        return r != null ? r : Collections.<IfFact>emptyList()
    }

    @Override
    protected SourceUnit getSourceUnit() { null }
}
