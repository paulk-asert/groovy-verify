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
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.control.SourceUnit
import org.codehaus.groovy.control.messages.SyntaxErrorMessage
import org.junit.jupiter.api.Test
import verification.ContractExpansionTransform

import static org.junit.jupiter.api.Assertions.*

/**
 * Contract text is captured verbatim by slicing the author's source (power-assert's {@code SourceText}),
 * never by reconstructing it from the AST. The captured string is re-parsed downstream by
 * {@code SpecRegistry} to be encoded, so it has to round-trip — and {@code Expression.getText()} does not:
 * {@code ConstantExpression.getText()} is {@code value.toString()}, so the string literal {@code 'x'} comes
 * back as bare {@code x}, which re-parses cleanly as a <em>variable reference</em>. That is a different
 * predicate, verified silently — the one failure a verifier must never have.
 *
 * On real source the slice always succeeds (0 of 3479 captures across the suite fall through), so this
 * pins the unreachable branch: when the slice cannot be taken, capture fails loudly instead of quietly
 * substituting a reconstruction.
 */
class ContractCaptureTest {

    @Test
    void unsliceableExpressionIsReportedRatherThanReconstructed() {
        SourceUnit su = SourceUnit.create('probe.groovy', 'class C { }')

        // A string literal with no source position: the slice cannot be taken. Reconstructing it would
        // yield bare `x` (quotes dropped) — the silent-wrong-predicate case this branch exists to prevent.
        ConstantExpression noPosition = new ConstantExpression('x')
        assertEquals('x', noPosition.text, 'precondition: getText() drops the quotes, hence the loud failure')

        String captured = ContractExpansionTransform.verbatimText(noPosition, su)

        assertNull(captured, 'a failed capture must not fall back to a lossy AST reconstruction')
        assertEquals(1, su.errorCollector.errorCount, 'a failed capture must be reported, not swallowed')
        String msg = ((SyntaxErrorMessage) su.errorCollector.getError(0)).cause.message
        assertTrue(msg.contains('could not capture the verbatim source'), "unexpected message: $msg")
    }
}
