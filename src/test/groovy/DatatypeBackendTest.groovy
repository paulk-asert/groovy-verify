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
import verification.Z3Backend
import verification.SmtSession
import verification.CheckResult

import static org.junit.jupiter.api.Assertions.assertEquals

/**
 * Phase M-A — the N-constructor datatype backend, exercised directly (no encoder dependency yet). A two-case
 * {@code Maybe = Some(value) | None} datatype must give the case-analysis theorems by construction.
 */
class DatatypeBackendTest {

    @Test
    void maybeDatatypeRoundTrips() {
        Z3Backend backend = new Z3Backend()
        SmtSession s = backend.session()
        try {
            Object V = s.declareSort('Object')
            s.datatypeSort('Maybe', [
                ['Some', [['value', V] as Object[]]] as Object[],
                ['None', []] as Object[]
            ])
            Object v = s.varOfSort('v', V)
            Object someV = s.datatypeConstruct('Maybe', 'Some', [v])
            Object none = s.datatypeConstruct('Maybe', 'None', [])

            // All four datatype theorems at once: assert the negation of the conjunction, expect UNSAT (VERIFIED).
            Object goal = s.and([
                s.eq(s.datatypeSelect('Maybe', 'Some', 'value', someV), v),   // content(Some(v)) == v
                s.datatypeRecognize('Maybe', 'Some', someV),                  // is$Some(Some(v))
                s.datatypeRecognize('Maybe', 'None', none),                   // is$None(None)
                s.not(s.eq(someV, none)),                                     // Some(v) != None
            ])
            s.assertExpr(s.not(goal))
            assertEquals(CheckResult.Status.VERIFIED, s.check().status)
        } finally {
            s.close()
        }
    }

    /**
     * Phase M-B — the {@code null}-collapse seed. On one {@code Some} element, Vavr-style {@code map} keeps
     * {@code Some(g(x))} while Optional-style {@code map} collapses to {@code None} when {@code g(x)} is the null
     * value. So *when {@code g(x)} is null*, the two diverge ({@code Some(null) != None}) — exactly the point at
     * which Optional's functor-composition law breaks. A valid implication, by datatype distinctness + null$.
     */
    @Test
    void optionalNullCollapseDivergesFromVavrMap() {
        Z3Backend backend = new Z3Backend()
        SmtSession s = backend.session()
        try {
            Object V = s.declareSort('Object')
            s.datatypeSort('Maybe', [
                ['Some', [['value', V] as Object[]]] as Object[],
                ['None', []] as Object[]
            ])
            Object nul = s.nullValue(V)
            Object x = s.varOfSort('x', V)
            Object gx = s.applyUF('apply$g', [x], V)
            Object someGx = s.datatypeConstruct('Maybe', 'Some', [gx])
            Object none = s.datatypeConstruct('Maybe', 'None', [])

            Object vavrMap = someGx                                  // Vavr: always Some(g(x))
            Object optMap = s.ite(s.eq(gx, nul), none, someGx)       // Optional: collapse null to None

            // g(x) == null$  ⟹  vavrMap != optMap   (Some(null) != None)
            Object goal = s.implies(s.eq(gx, nul), s.not(s.eq(vavrMap, optMap)))
            s.assertExpr(s.not(goal))
            assertEquals(CheckResult.Status.VERIFIED, s.check().status)
        } finally {
            s.close()
        }
    }
}
