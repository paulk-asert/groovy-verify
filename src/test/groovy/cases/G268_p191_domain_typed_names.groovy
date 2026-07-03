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
package cases

import static cases.CaseDsl.*

/** 'P191 domain-typed names' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G268_p191_domain_typed_names {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Domain-typed names the packs cannot resolve stay honest: a Quantity parameter (or a local bound from one) skips loudly — never modelled as an int shadow — while a comparison over unresolvable quantity-typed operands is claimed as untranslatable rather than left to the scalar path (whose model would not carry compareTo value-equality or the cross-kind UnconvertibleException); a local aliased from a claimable construction still verifies through the value-source scope hook.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — units/records: no grid-executable runtime arm'

    static final List<Map> CASES = [

        // ---------- Phase 191: domain-typed names outside the packs' reach stay loud ----------
        // A Quantity PARAMETER copied into a local: its magnitude/unit is unknown, so the value read-out
        // is outside the fragment — the postcondition skips loudly (and the deref obligations still fire:
        // f(null) genuinely throws). The P900 probe pinned this path before it became a case.
        [group: 'P191 domain-typed names', name: 'quantity parameter via local skips the postcondition', expect: 'Skipped verification of postcondition for f',
         src: HDR + UOM + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 5.0 })\n' +
              '          static BigDecimal f(Quantity<Length> q) { def d = q\n' +
              '              d.to(METRE).getValue() as BigDecimal } }'],
        // TEETH for the Phase 191 translateBinary claim: two parameter quantities compared through locals.
        // Before the fix the generic scalar path modelled x and y as int shadows and REFUTED `!result`
        // ("counterexample: a = 0, b = 0") — a model that carries neither compareTo value-equality nor the
        // cross-kind throw. The pack now claims the comparison as untranslatable → the loud skip.
        [group: 'P191 domain-typed names', name: 'unresolvable quantity comparison skips, never int-shadows', expect: "(x == y)' is outside fragment",
         src: HDR + UOM + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ !result })\n' +
              '          static boolean f(Quantity<Length> a, Quantity<Length> b) { def x = a\n' +
              '              def y = b\n' +
              '              x == y } }'],
        // The throwing shape: comparing quantities of DIFFERENT kinds throws UnconvertibleException at
        // runtime, so neither polarity may be proved or refuted for unresolvable operands — skip.
        [group: 'P191 domain-typed names', name: 'cross-kind quantity comparison skips (runtime throws)', expect: "(x == b)' is outside fragment",
         src: HDR + UOM + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ !result })\n' +
              '          static boolean f(Quantity<Length> a, Quantity<Mass> b) { def x = a\n' +
              '              x == b } }'],
        // A derived-but-unresolvable local (built FROM a parameter): still outside the fragment, still loud.
        [group: 'P191 domain-typed names', name: 'local derived from a quantity parameter skips', expect: 'Skipped verification of postcondition for g',
         src: HDR + UOM + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result >= 0.0 })\n' +
              '          static BigDecimal g(Quantity<Length> q) { def d = q.to(METRE)\n' +
              '              d.getValue() as BigDecimal } }'],
        // The scope hook's verify side: a local aliased from a CLAIMABLE construction (claimsValueSource →
        // registerSourceAlias) resolves through the pack's readers — 1 km IS 1000 m, value-equality.
        [group: 'P191 domain-typed names', name: 'local from claimable construction verifies equality', ok: true,
         src: HDR + UOM + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result })\n' +
              '          static boolean h() { def d = Quantities.getQuantity(1, KILO(METRE))\n' +
              '              d == Quantities.getQuantity(1000, METRE) } }'],
    ]
}
