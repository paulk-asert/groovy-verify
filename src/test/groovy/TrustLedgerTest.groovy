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
import org.junit.jupiter.api.Test
import verification.SpecRegistry
import verification.TrustLedger

import static org.junit.jupiter.api.Assertions.*

/** Phase 216 — the trusted-spec ledger: recording, containment, and the lint-facing parse helpers. */
class TrustLedgerTest {

    @Test
    void externalSpecConsumptionIsLedgered() {
        String src = cases.CaseDsl.tc('''class C {
            @Requires({ a != Integer.MIN_VALUE })
            @Ensures({ result >= 0 })
            static int f(int a) { return Math.abs(a) }
        }''')
        new GroovyClassLoader().parseClass(src, 'LedgerCase.groovy')
        assertTrue(SpecRegistry.consumed().contains('java.lang.Math#abs/1'),
            'consuming Math.abs must record the spec in SpecRegistry.consumed()')
        assertTrue(TrustLedger.entries().any { it.contains('java.lang.Math#abs/1') },
            'the trusted ledger must carry the external-spec consumption')
        assertTrue(TrustLedger.summary().contains('external spec'),
            'the summary line must break out external specs')
    }

    @Test
    void inPlaceTrustedContractIsLedgered() {
        String src = cases.CaseDsl.tc('''class C {
            @ThrowsIf(value = { s == null }, exception = NullPointerException, woven = false, direct = false)
            static Object parse(Object s) { return helper(s) }
            static Object helper(Object s) { s }
        }''')
        new GroovyClassLoader().parseClass(src, 'LedgerCase2.groovy')
        assertTrue(TrustLedger.entries().any { it.startsWith('[in-place @ThrowsIf]') && it.contains('#parse') },
            'a trusted @ThrowsIf must appear in the ledger with its owning method')
    }

    /** Phase 291 — VERIFY_TRUST=report prints each trusted fact a class relied on, on stdout, as it finishes the class. */
    @Test
    void reportModePrintsEachTrustedFact() {
        String prior = TrustLedger.mode
        PrintStream out = System.out
        ByteArrayOutputStream buf = new ByteArrayOutputStream()
        TrustLedger.mode = 'report'
        System.setOut(new PrintStream(buf, true, 'UTF-8'))
        try {
            new GroovyClassLoader().parseClass(cases.CaseDsl.tc('''class C {
                @ThrowsIf(value = { s == null }, exception = NullPointerException, woven = false, direct = false)
                static Object parse(Object s) { return helper(s) }
                static Object helper(Object s) { s }
            }'''), 'LedgerCase3.groovy')
        } finally {
            System.setOut(out)
            TrustLedger.mode = prior
            TrustLedger.drainPending()
        }
        String printed = buf.toString('UTF-8')
        assertTrue(printed.contains('trusted: [in-place @ThrowsIf] C#parse'),
            "report mode must print the trusted fact, got: ${printed}")
    }

    @Test
    void unknownTrustModeIsOff() {
        assertNull(TrustLedger.normaliseMode('warn'), 'only report / deny switch surfacing on')
        assertEquals('deny', TrustLedger.normaliseMode(' DENY '))
    }

    @Test
    void malformedSpecTextIsContained() {
        assertNull(SpecRegistry.parseForLint('class {{{ not groovy', 'x.y.Z'),
            'a malformed spec must parse to null, never throw')
    }
}
