<!--
  SPDX-License-Identifier: Apache-2.0

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-->

# Encoding packs

> **Experimental.** The SPI is young (Phases 187–190) and grown demand-driven; expect it to move.

An **encoding pack** teaches the verifier a *library or domain vocabulary* — a spec-helper family, JSR 385
quantities, a money or time library — from outside the core engine. The boundary is principled:

> **Packs model libraries; the core models the language.**

Ints, arrays, operators, closures, collections, and `String` theory are the language — they live in the
`Encoder`. `Quantities.getQuantity(1, KILO(METRE))` is a library's vocabulary — it lives in a pack. The three
in-tree packs are the references: [`NumberTheoryPack`](src/main/groovy/verification/NumberTheoryPack.groovy)
(the minimal shape — call recognisers + recurrence axioms, extended in Phase 204 with the Bézout
coefficient witnesses), [`UnitsPack`](src/main/groovy/verification/UnitsPack.groovy) (the full surface —
properties, operators, expression claims, value-source aliasing, a checker pass, curated tables), and
[`CombinatoricsPack`](src/main/groovy/verification/CombinatoricsPack.groovy) (factorial and the Pascal-rule
binomial — the first **two-argument** primitive, and a worked warning about axiom domain guards: its refute
twins caught an unguarded-base inconsistency during development).

## The shape of a pack

A pack implements [`EncodingPack`](src/main/groovy/verification/EncodingPack.groovy) and is discovered via
`ServiceLoader` — one line in `META-INF/services/verification.EncodingPack` on the *compile* classpath (the
same mechanism that registers the contract transform). Packs run in name-sorted order at fixed slots in the
encoder's dispatch; the `VERIFY_PACKS` knob (see [TOOLING.md](TOOLING.md)) selects or disables them per run.

Every recogniser follows the engine's **tri-state convention**:

| return | meaning |
|---|---|
| `TheoryApi.NO_MATCH` | my guard didn't fire — try the next pack, then the built-in handlers |
| `null` | *matched, but honestly untranslatable* — abort the whole dispatch; the obligation surfaces as a loud "outside fragment" skip |
| anything else | the SMT handle of the translated expression — final |

The distinction between `NO_MATCH` and `null` is load-bearing: returning `null` where you mean `NO_MATCH`
silences other handlers; returning `NO_MATCH` where you mean `null` lets a later handler mis-translate a
value you know is yours (that is what `claimsExpression` exists to prevent — see below).

### Surfaces

| `EncodingPack` method | fires on | example (UnitsPack) |
|---|---|---|
| `translateCall(api, mce, m, recv, args)` | a method call | `X.getValue()` → SI magnitude / unit scale |
| `translateProperty(api, pe, obj, prop)` | a property read (after the core's carrier/record branches) | `X.value` |
| `translateBinary(api, be, opType)` | a binary expression, at the domain-comparison slot | quantity `==` / `!=` |
| `claimsExpression(e)` *(static context)* | scalar classifiers asking "is this value yours?" | `quantity / quantity` is `Quantity.divide` — no Real classification, no divide-by-zero obligation |
| `claimsValueSource(api, e)` | the checker deciding whether to alias a scalar-handle-less name to its construction expression (read it back via `api.sourceAlias(name)`) | a Quantity-typed local / `result` |
| `checkMethod(api, node)` | once per method: a pure-AST **checker pass** with diagnostics — no SMT (programs against `CheckerApi`: `reportError`, `cleanBody`, `inferredTypeOf`); best-effort, contained per pack | the C₀ kind-vector check of `as Quantity<K>` casts |
| `resolveDynamicProperty(receiverType, pexp, enclosingClass)` | **STC time** (Phase 209): an unresolved property `@TypeChecked` would reject — return the type to store, or null to decline | `n.fizzBuzz` backed by a visible `metaClass` registration (MetaProgrammingPack) |
| `resolveDynamicMethod(receiverType, name, argTypes, enclosingClass, enclosingClosure)` | **STC time** (Phase 209): a missing method — return a synthetic `MethodNode` with the resolved signature, or null | `Integer.multiply(String)` from `Integer.metaClass.multiply = { String s -> … }` |
| `corpusGroups()` | provenance: the case groups that pin this pack | `['P131 dimensions', 'P132 unit scale']` |
| `specFqns()` | the external-spec skeletons the pack's jar ships (Phase 227): declaring them gates them on the pack's enablement (`VERIFY_PACKS` deselection deselects the specs), puts each under the trusted-inventory lint (must parse + carry contracts; classpath duplicates are drift), and adds `packSpecs` catalog provenance | `['javax.measure.Quantity']` |

The two `resolveDynamic*` surfaces are the **STC companion half**: they run inside the type checker
(before any encoding), and they are the narrow gate through which slim dynamic-Groovy support returns to
the `@TypeChecked` world. The obligation is absolute: **a pack may only bless what it can also faithfully
model** (or whose model refuses loudly) — a blessing without a model is how silent unsoundness starts.
The `MetaProgrammingPack` is the reference: same-class-visible `ExpandoMetaClass` registrations, typed
from the registered closure's own signature and modelled by inlining that closure at each use site. The same discipline covers **pack-declared specs** (`specFqns()`): a pack may only *spec* what is
provably true of the library — packs model what contracts *cannot* say (theory: dimension algebra,
scale arithmetic), spec skeletons say what they can (nullity, ranges, exceptional arms) — and the
runtime rung's grid cross-checks apply to pack-shipped specs unchanged.

All but `translateCall` have no-op defaults — implement what your domain needs. The encoder-facing hooks
receive `TheoryApi` (a live SMT session per VC); `checkMethod` receives `CheckerApi` (diagnostics + AST
queries, no session) — a pass that needs solving belongs in the encoder hooks instead.

### The facade

Packs program against [`TheoryApi`](src/main/groovy/verification/TheoryApi.groovy) only — never the
`Encoder` (whose internals carry no stability promise). It provides: the `SmtSession` (sorts, literals,
term builders, `assertExpr`, quantifiers with triggers, and **`applyUF(name, args, sort)`** — the generic
named-UF creator that makes bespoke backend methods unnecessary), `translate` / `translateInSort` /
`asRealValue` for sub-expressions, `axiomsOnce(key)` (the per-VC mint-once gate for defining axioms),
`sourceAlias(name)`, and the `receiverIsClass` helper covering the three receiver spellings a static
helper arrives in (unresolved import / re-parsed FQN / resolved `ClassExpression`). Missing something?
That's a facade-growth conversation, not a reason to reach around it.

## The obligations

A pack's lowerings and axioms are **trusted like the engine's own** — a wrong axiom makes the verifier
unsound for everyone. The project's discipline therefore applies to packs verbatim:

1. **Verify + refute, per capability.** Every recogniser needs a case that *proves* through it **and a
   deliberately-broken twin that refutes** — a capability that only ever verifies is indistinguishable from
   a vacuous pass (this catches wrong axioms, wrong guards, and wrong tri-state usage alike). Declare the
   groups in `corpusGroups()`: they become the pack's `catalog.json` provenance, and the doc-drift lint
   fails the build if a claimed group stops existing.
2. **Loud skips at the boundary.** Anything your domain can't model must return `null` (or emit nothing and
   let the core skip) — never a silently-weak translation. "Sound within the fragment, loudly unsound
   outside it" is the whole posture.
3. **Namespace your UF symbols** (`fib$`, `units$…`) — they share one solver namespace with user variables,
   other packs, and the VC cache.
4. **Keep runtime semantics paired.** A spec helper the user writes in contracts (`Fib.of(i)`) should also
   be a real, executable class, so unproven obligations still degrade to groovy-contracts runtime checks —
   the graceful-degradation story packs must not break.

## What packs cannot do (yet)

Deliberately outside the SPI, pending their own design work: **normalizer rewrites** and
**counterexample rendering**. Each is added when a pack demonstrably needs it — the same slice discipline
as the engine.

**Scope collection** was investigated (Phase 191) and deliberately *not* grown: the checker's collection
walks are already units-agnostic — a pack participates through `claimsValueSource` (locals and `result`
alias to their construction; read back via `sourceAlias`), and probing the suspected gaps showed the
remaining dishonesty was pack-side (a `translateBinary` `NO_MATCH` that let the scalar path int-shadow
unresolvable quantity comparisons — fixed in the pack, pinned by `P191 domain-typed names`). A
declared-type claim (`claimsType`) stays deferred until a pack demonstrably needs one.

## Worked minimum

A one-vocabulary pack, end to end:

<!-- doclint:ignore PACKS.md SPI illustration — a minimal hypothetical pack, not a shipped case -->
```groovy
@CompileStatic
class ParityPack implements EncodingPack {
    String name() { 'parity' }
    List<String> corpusGroups() { ['P-parity'] }        // the verify+refute cases that pin it

    Object translateCall(TheoryApi api, MethodCallExpression mce, String m,
                         Expression recv, List<Expression> args) {
        if (m == 'of' && args.size() == 1 && TheoryApi.receiverIsClass(recv, 'Parity')) {
            Object k = api.translate(args.get(0))
            if (k == null) return null                   // matched, untranslatable → loud skip
            if (api.axiomsOnce('parity.of')) {
                SmtSession s = api.session
                // ∀k. parity$(k) == k - 2*(k div 2), triggered on parity$(k)
                Object b = s.boundIntVar('parity$k')
                Object term = s.applyUF('parity$', [b], s.intSort())
                s.assertExpr(s.forall([b],
                    s.eq(term, s.minus(b, s.times(s.intLit(2L), s.intDiv(b, s.intLit(2L))))), [term]))
            }
            return api.session.applyUF('parity$', [k], api.session.intSort())
        }
        TheoryApi.NO_MATCH
    }
}
```

Plus: the runtime `Parity` helper class, the `META-INF/services` line, and the `P-parity` verify/refute
cases. That is the whole contract.
