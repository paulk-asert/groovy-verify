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
import tech.units.indriya.quantity.Quantities

import static javax.measure.MetricPrefix.CENTI
import static javax.measure.MetricPrefix.KILO
import static org.junit.jupiter.api.Assertions.assertEquals
import static systems.uom.common.USCustomary.FOOT
import static systems.uom.common.USCustomary.INCH
import static systems.uom.common.USCustomary.MILE
import static systems.uom.common.USCustomary.YARD
import static tech.units.indriya.unit.Units.METRE

/**
 * Phase 132 — pin the value/scale engine's trusted unit-scale constants (the {@code BASE_UNIT_SCALE} /
 * {@code PREFIX_SCALE} tables in {@code Encoder}, which it reads by simple name) against what the JSR 385
 * reference implementation actually computes. The engine never runs these conversions — it asserts the scale
 * from its table — so this test is the honesty check: if a library updates a unit's definition (e.g. an
 * international vs US-survey mile), the table goes stale and this fails, rather than the engine silently
 * proving a value the runtime contradicts.
 */
class UnitScaleTest {

    private static BigDecimal metres(Number value, javax.measure.Unit unit) {
        new BigDecimal(Quantities.getQuantity(value, unit).to(METRE).value.toString())
    }

    @Test
    void trustedScalesMatchTheLibrary() {
        assertEquals(0, metres(1, METRE).compareTo(new BigDecimal('1')))              // base: 1 m
        assertEquals(0, metres(1, KILO(METRE)).compareTo(new BigDecimal('1000')))     // KILO  = 1000
        assertEquals(0, metres(1, CENTI(METRE)).compareTo(new BigDecimal('0.01')))    // CENTI = 0.01
        assertEquals(0, metres(1, MILE).compareTo(new BigDecimal('1609.344')))        // international mile
        assertEquals(0, metres(1, YARD).compareTo(new BigDecimal('0.9144')))          // international yard
        assertEquals(0, metres(1, FOOT).compareTo(new BigDecimal('0.3048')))          // international foot
        assertEquals(0, metres(1, INCH).compareTo(new BigDecimal('0.0254')))          // international inch
    }
}
