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
import tech.units.indriya.quantity.Quantities

import javax.measure.Quantity
import javax.measure.quantity.Length
import javax.measure.quantity.Mass
import javax.measure.quantity.Time
import javax.measure.quantity.Speed

import static javax.measure.MetricPrefix.KILO
import static tech.units.indriya.unit.Units.GRAM
import static tech.units.indriya.unit.Units.METRE
import static tech.units.indriya.unit.Units.SECOND
import static tech.units.indriya.unit.Units.METRE_PER_SECOND
import static systems.uom.common.USCustomary.MILE

/**
 * A deliberately tiny units DSL — just the few suffixes groovy-verify's experimental DSL reader recognises.
 * `1.km` reads as `getKm(1)`, building a real JSR 385 quantity; `a + b` routes to the {@code plus} extension
 * ({@code a.add(b)}), and `d / s` to {@code div} (which casts the erased product to {@code Quantity<Speed>}).
 * The verifier never compiles against this class — it recognises the DSL sugar by name.
 */
class UomExtensions {
    static Quantity<Length> getM(Number n)    { Quantities.getQuantity(n, METRE) }
    static Quantity<Length> getKm(Number n)   { Quantities.getQuantity(n, KILO(METRE)) }
    static Quantity<Length> getMile(Number n) { Quantities.getQuantity(n, MILE) }
    static Quantity<Mass>    getKg(Number n)   { Quantities.getQuantity(n, KILO(GRAM)) }
    static Quantity<Time>    getS(Number n)    { Quantities.getQuantity(n, SECOND) }
    static Quantity<Speed>   getMps(Number n)   { Quantities.getQuantity(n, METRE_PER_SECOND) }   // a Speed literal: 1.mps

    static <Q extends Quantity<Q>> Quantity<Q> plus(Quantity<Q> a, Quantity<Q> b)  { a.add(b) }
    static <Q extends Quantity<Q>> Quantity<Q> minus(Quantity<Q> a, Quantity<Q> b) { a.subtract(b) }

    // Length / Time → Speed. `multiply`/`divide` return the erased `Quantity<?>`, so the result kind is a cast the
    // type system can't check — exactly the spot groovy-verify's dimension reader (`/` subtracts exponents) covers.
    static Quantity<Speed> div(Quantity<Length> q, Quantity<Time> divisor) { q.divide(divisor) as Quantity<Speed> }
}
