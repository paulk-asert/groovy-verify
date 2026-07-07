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

// External-specification skeleton (Phase 227): PACK-DECLARED contracts for javax.measure.Quantity —
// owned by the jsr385-units pack (UnitsPack.specFqns), so deselecting the pack via VERIFY_PACKS also
// deselects these. Deliberately THIN: only the contract-shaped rim (nullity facts). The semantics —
// dimension algebra, SI magnitudes, scale — are pack THEORY, inexpressible as parameter closures;
// the exceptional surface (to() throwing on incommensurable dimensions) is likewise unstatable as an
// honest arm, so none is shipped (no false iffs).
package javax.measure

import groovy.contracts.Ensures
import groovy.transform.Pure

class Quantity {

    @Pure
    @Ensures({ result != null })
    Object getValue() {}

    @Pure
    @Ensures({ result != null })
    Object getUnit() {}
}
