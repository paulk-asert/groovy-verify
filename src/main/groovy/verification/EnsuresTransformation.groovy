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
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.expr.ClassExpression
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
 * Captures the {@code @Ensures(\{...\})} closure body's source text into
 * the annotation's {@code contract} member, then *replaces* the closure
 * value with a harmless {@code Object} class literal.
 *
 * The second step is what distinguishes this from
 * {@link RequiresTransformation}. A method carrying {@code @Ensures}
 * must be {@code @TypeChecked} (that is how {@link VerifyChecker}'s
 * {@code afterVisitMethod} hook fires on it), and the static type
 * checker would otherwise visit the contract closure and reject
 * {@code result} and the formal-parameter names as undeclared
 * variables. Removing the closure here, at SEMANTIC_ANALYSIS, leaves
 * nothing for INSTRUCTION_SELECTION's type checker to choke on — the
 * re-parseable contract text lives on in the {@code contract} member.
 */
@CompileStatic
@GroovyASTTransformation(phase = CompilePhase.SEMANTIC_ANALYSIS)
class EnsuresTransformation implements ASTTransformation {

    @Override
    void visit(ASTNode[] nodes, SourceUnit source) {
        if (nodes == null || nodes.length < 2) return
        if (!(nodes[0] instanceof AnnotationNode)) return

        AnnotationNode anno = (AnnotationNode) nodes[0]
        if (anno.classNode?.name != 'verification.Ensures') return

        Expression valueMember = anno.getMember('value')
        if (!(valueMember instanceof ClosureExpression)) return

        ClosureExpression closure = (ClosureExpression) valueMember
        String contractText = closureBodyText(closure)
        if (contractText) {
            // Replace the closure with the captured text plus a neutral
            // class literal, so the type checker never sees the closure.
            anno.members.put('contract', new ConstantExpression(contractText))
            anno.members.put('value', new ClassExpression(ClassHelper.OBJECT_TYPE))
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
