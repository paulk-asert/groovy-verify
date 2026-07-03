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
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.stmt.Statement

/**
 * The curated <b>checker</b> surface a pack's per-method pass ({@link EncodingPack#checkMethod}) programs
 * against — the checker-side sibling of {@link TheoryApi} (which serves the per-VC <i>encoder</i>).
 * Implemented by {@code VerifyChecker}. A checker pass is pure AST analysis over one method — no SMT
 * session exists in this context; a pass that needs solving belongs in the encoder hooks instead.
 *
 * <p>Deliberately tiny, grown demand-driven like every SPI surface here: diagnostics emission, the
 * clean-body read (the CONVERSION snapshot, before groovy-contracts' instrumentation — never read
 * {@code node.code} directly for analysis), and STC's inferred-type query.
 */
@CompileStatic
interface CheckerApi {

    /** Emit a compile error positioned at {@code at} — the pack pass's refutation/diagnostic channel.
     *  Message conventions: see the engine's own diagnostics (obligation-style text, honest skips). */
    void reportError(String message, ASTNode at)

    /** The method's clean body — the CONVERSION-phase snapshot when present (before groovy-contracts'
     *  injected instrumentation), else the live code; null when the method has no body. */
    Statement cleanBody(MethodNode node)

    /** The static type checker's inferred (or declared) type for an expression — the checker-context
     *  twin of the encoder-side type queries. */
    ClassNode inferredTypeOf(Expression e)
}
