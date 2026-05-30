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
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.control.SourceUnit
import org.codehaus.groovy.transform.ASTTransformation
import org.codehaus.groovy.transform.GroovyASTTransformation

/**
 * Captures the source text of a {@code @Requires(\{...\})} closure
 * body at producer-compile-time and stores it as the annotation's
 * {@code contract} string member.
 *
 * Why this is needed: by the time the consumer's type-checking
 * extension fires, the {@code value} member has been rewritten from
 * a {@link ClosureExpression} into a {@link
 * org.codehaus.groovy.ast.expr.ClassExpression} pointing at a
 * synthetic closure class. The closure's body AST is gone. Its
 * source text, however, can be captured here and serialised through
 * the annotation. {@link VerifyChecker} re-parses the string via
 * {@code AstBuilder.buildFromString}.
 *
 * Runs at SEMANTIC_ANALYSIS, before the static type checker runs at
 * INSTRUCTION_SELECTION — early enough that the closure expression is
 * still present, late enough that {@code .text} resolution works on
 * sub-expressions.
 */
@CompileStatic
@GroovyASTTransformation(phase = CompilePhase.SEMANTIC_ANALYSIS)
class RequiresTransformation implements ASTTransformation {

    @Override
    void visit(ASTNode[] nodes, SourceUnit source) {
        if (nodes == null || nodes.length < 2) return
        if (!(nodes[0] instanceof AnnotationNode)) return

        AnnotationNode anno = (AnnotationNode) nodes[0]
        // Defensive: only act on our own annotation.
        if (anno.classNode?.name != 'verification.Requires') return

        Expression valueMember = anno.getMember('value')
        if (!(valueMember instanceof ClosureExpression)) return

        ClosureExpression closure = (ClosureExpression) valueMember
        String contractText = closureBodyText(closure)
        if (contractText) {
            anno.setMember('contract', new ConstantExpression(contractText))
        }
    }

    private static String closureBodyText(ClosureExpression closure) {
        Statement code = closure.code
        if (code == null) return ""
        if (code instanceof BlockStatement) {
            BlockStatement bs = (BlockStatement) code
            List<String> parts = []
            for (Statement s : bs.statements) {
                if (s instanceof ExpressionStatement) {
                    parts.add(((ExpressionStatement) s).expression.text)
                } else {
                    parts.add(s.text)
                }
            }
            return parts.join('; ')
        }
        return code.text ?: ""
    }
}
