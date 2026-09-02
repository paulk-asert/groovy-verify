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

# Architecture

A map of the codebase for someone who just cloned it: where the code is, how the
pieces fit at compile time, and the load-bearing design choices. For *what* it
proves and *why*, see [README.md](README.md); for the increment-by-increment
history, [ROADMAP.md](ROADMAP.md).

## The compile-time pipeline

groovy-verify runs entirely at the **consumer's compile time**, interleaved with
groovy-contracts across Groovy's compile phases. Nothing runs at the consumer's
*runtime* — that half is groovy-contracts' executable contract checks.

1. **`CONVERSION`** — `ContractExpansionTransform`, a *global* AST transform, runs
   first. It captures the **verbatim contract source text** (`@Requires` /
   `@Ensures` / `@Decreases` / `@Modifies`, and class-level `@Invariant`) into
   `ContractSource` / `ClassInvariantSource` carriers, takes **clean-body
   snapshots** (`ORIGINAL_BODY_KEY`), and stashes **loop specs**
   (`LOOP_SPEC_KEY`) onto node metadata. It also synthesises `$rely$Role`
   rely-steps for `@UnderRely` and desugars `@SelfEnsures`.
2. **`SEMANTIC_ANALYSIS`** — groovy-contracts (also a global transform) erases the
   contract closures into generated closure classes and weaves the runtime
   checks.
3. **Type checking** — `@TypeChecked(extensions = 'verification.VerifyChecker')`
   fires `VerifyChecker`, which reads the captured metadata, lowers each
   obligation to SMT through `Encoder` → `SmtSession`, discharges it with Z3, and
   reports counterexamples through `Reporter`.
4. **`INSTRUCTION_SELECTION`** — groovy-contracts mutates the *live* method bodies
   (prepending `old = …`, wrapping in `try`/`catch`, appending the postcondition
   assert) — which is precisely *why* step 1 snapshotted the clean body.

**The capture-before-erasure ordering is the load-bearing choice.** The contract
closure must be read while it is still an intact `ClosureExpression`; groovy-contracts
erases it during its `SEMANTIC_ANALYSIS` global pass, and global transforms in that
phase run before any collector expansion or local transform — so the only place
guaranteed to see the intact closure *ahead* of groovy-contracts is the earlier
`CONVERSION` phase, which only global transforms can occupy. The verifier therefore
always reasons about the **author's** contract and the **clean** body, never the
groovy-contracts-rewritten forms. (Verbatim text comes from power-assert's
`SourceText`, so the captured string is byte-for-byte the author's source.)

## Components

| File | Role |
|---|---|
| `VerifyChecker` | the `@TypeChecked` extension; call-site, body, loop & implicit checks, annotation-law synthesis (`@Reducer` / `@Monadic`), the information-flow noninterference walk (`@Label`), Bean Validation (`jakarta` / `javax.validation`) constraints read as preconditions (Phase 128), and the SEQ/PAR ladder passes (Phases 240–245: PAR interference over fork-join windows, channel-end linearity, channel element contracts, the network wait-for/well-foundedness analysis with close/drain discipline, and guarantee-conformance twins) |
| `Encoder` | Groovy expression → SMT (the fragment lives here); method-call translation dispatches through an ordered registry of ~30 per-domain `tmc*` handlers (see the `NO_MATCH` convention at `translateMethodCall`) — a new call recognizer is one handler + one registry line |
| `SharedSend` / `SharedReceive` | Phase 284 — the DECLARED relaxation of channel-end linearity: JCSP's `any2one` / `one2any` as annotations on a channel declaration. Declared and never inferred, so undeclared sharing keeps refusing; the declaration costs the positional model (said at the channel) and keeps the element contract and deadlock-freedom |
| `ChannelDesugar` | the channel/dataflow DESUGARING half, split out of `VerifyChecker` when that class reached 15.5k lines: static AST-to-AST rewriting only — dataflow variables (Phase 118), the async-channel pipeline (Phase 119), symbolic and bounded streaming (Phases 248/251), the looping ALT, and the guarded ALT's index (Phase 275) — with no dependence on the checker's mutable per-method state, which is why it separates cleanly. The passes that *report* on these rewrites stay in `VerifyChecker` |
| `TypeEnvironment` | the per-method name → type scope the `Encoder` translates under (set/list/map element types; enum/decimal/FP/boolean/tuple/carrier/`Function`/atomic names), built by `VerifyChecker` per verification context and passed whole — named fields in place of the historical ~17 positional constructor parameters |
| `ContractNormalizer` | canonicalises a freshly re-parsed contract expression against the owning method's signature before the encoder sees it — the one home for pre-resolution parse shapes (currently: the SAM call-operator shorthand `f(x)` → `f.apply(x)`, including inside quantifier closure bodies, and the `values().length`/`.size()` enum-count fold); wired into `VerifyChecker.contractAstFor`, the loop-contract capture, and `classInvariantTexts`; also the shared derivation of `Function`-formal return types and enum domain sizes |
| `EncodingPack` / `TheoryApi` / `PackRegistry` | the **extensible-encodings SPI** (experimental): a pack contributes a library/domain vocabulary from outside the core (packs model *libraries*; the core models the *language*). Surfaces: call, property, and binary-operator recognisers, an expression-claim predicate (keeps scalar classifiers off pack-domain values), a value-source claim (lets the checker alias a scalar-handle-less name to its construction), and a per-method checker pass (`checkMethod`). `TheoryApi` is the curated encoder facade (session, translate/`translateInSort`/`asRealValue`, `axiomsOnce`, `sourceAlias`, the tri-state `NO_MATCH` convention shared with the built-in registry); `PackRegistry` discovers packs via `ServiceLoader` (`META-INF/services/verification.EncodingPack`) |
| `CheckerApi` | the checker-side sibling of `TheoryApi`: the curated surface a pack's per-method **checker pass** (`EncodingPack.checkMethod` — pure AST analysis + diagnostics, no SMT) programs against — `reportError`, `cleanBody` (the CONVERSION snapshot), `inferredTypeOf`; implemented by `VerifyChecker`, dispatched best-effort with per-pack containment |
| `NumberTheoryPack` | the first pack and the reference shape: `Fib`/`Trib`/`Tetra`/`Gcd`/`Lcm` spec helpers lowered to their axiomatised primitives (`fib$` … `lcm$`) through `TheoryApi` + the generic `applyUF` — the bespoke per-function backend methods are retired |
| `CombinatoricsPack` | the third pack (math-comp `binomial.v` inspired): `Fact.of(n)` and `Binom.of(n, k)` — the first **two-argument** spec primitive (`binom$` under Pascal's rule via the generic n-ary `applyUF`); domain-guarded axioms (the refute twins caught an unguarded-base inconsistency during development) |
| `MetaProgrammingPack` | the fourth pack (Phase 209, experimental): runtime metaprogramming, statically modelled — a same-class-visible `ExpandoMetaClass` registration (`Integer.metaClass.getFizzBuzz = { … }` / operator `multiply = { String s -> … }`) is TYPED by the pack's **STC-companion half** (`resolveDynamicProperty`/`resolveDynamicMethod` — the registration write, `delegate` arithmetic inside the closure, and the use sites all resolve under `@TypeChecked`) and MODELLED by inlining the registered closure at each use site in the String sort, out-of-sort arms as a sound opaque `meta$other$…(recv)` value; no visible registration → still a compile error (the gate is evidence-backed) |
| *(upstream)* `groovy.contracts.ThrowsIf` | the exceptional-contract annotation family — prototyped here (Phases 213/214), upstreamed as GROOVY-12135, and consumed directly since Phase 224 (the in-tree `verification.ThrowsIf` is retired; groovy-contracts owns the weaving and the `checked` runtime iff). Per-arm modes in upstream spelling: woven (guard generated upstream — must-throw by construction, the verifier proves only-when over the body), woven=false (body-implemented; the full iff proved, `Objects.requireNonNull` modelled), woven=false+direct=false (spec-only — the old `trusted`: vacuity-checked, caller-assumed, rung-monitored). `ContractExpansionTransform` retains only the bare-closure normalisation; the rung reads the upstream annotation reflectively and promotes justified throws to positive cross-validations |
| `SpecRegistry` | the external-specification registry (Phase 215): lazy, index-free discovery of Groovy spec skeletons at `META-INF/groovy-verify/specs/<fqn>.groovy` (`VERIFY_SPECS` dir override), parsed AST-only to CONVERSION with `ContractExpansionTransform` applied manually — the cached MethodNodes flow through the ordinary contract machinery (requires = call-site obligation via `onMethodSelection`; ensures = assumption via `resolveContractedCallee`'s fallback). All entries trusted by definition; consumption recorded via `consumed()` for the ledger |
| `TrustLedger` | the trusted-spec ledger (Phase 216): one deduplicated inventory of every fact assumed without proof — in-place spec-only `@ThrowsIf` arms (`woven = false, direct = false`) and external-spec registry consumption — printed beside the harness perf line, exposed via `entries()`/`summary()`, and backed by DocLint's `[5] trusted inventory` lint (a malformed shipped spec is silent trust loss, asserted as drift in `check`) |
| `UnitsPack` | the JSR 385 / units-of-measurement domain (Phases 131–160) as a pack — the migration that grew the SPI to its full surface set: `getValue()` (call), `.value` (property), quantity `==`/`!=` (binary), the quantity-expression claim (a `quantity / quantity` is `Quantity.divide`, not decimal division), the value-source claim behind quantity-local/`result` aliasing, and the C₀ kind-vector checker pass (dimension-checking `as Quantity<K>` casts, via `checkMethod`); the readers, the curated unit/prefix/DSL-suffix tables, and the kind table live wholly inside the pack |
| `BodyEncoder` / `LoopEncoder` | path enumeration & symbolic execution for `@Ensures`/loops |
| `PureEvaluator` | closed pure-function evaluation & fuel-bounded unfolding — the normalise-then-SMT accelerator (Phase 8a) |
| `Forall` | the `Forall.range(lo, hi){…}` bounded-quantifier helper (the native GDK `every`/`any` idioms are the preferred surface) |
| `ServedWithin` / `DeliveredWithin` | Phases 265/266 — the quantitative bound claims: `@ServedWithin(n)` certifies one ALT against a held `fair()`'s rotation arithmetic (n >= branches); `@DeliveredWithin(n, from, to)` sums the head-of-line hop costs through the scanned stages (worst simple path decides), each refuted with its own arithmetic or the unbounded hop's reason |
| `Protocol` / `SessionChecker` | Phase 263/269 — the `@Protocol` global type, written as a Groovy closure (labels are messages, `>>` sender to receiver, command-chain combinators; harvested pre-STC by ContractExpansionTransform and rendered to canonical text) or as `text = '''…'''`; parsed, projected onto each role as a Thompson NFA over channel ops, each process's control flow read as an automaton over the same ops, conformance decided by inclusion on the product with the local type's subset-DFA, violations reported with their trace; `par { … } and { … }` projects as the shuffle of independent sub-sessions (Phase 264); a mixed `choice` (no `at`) projects as the opener's union with a cross-process coherence check — one initiator, or a racing pair certified over GROOVY-12323's arbitrated select with rendezvous openers (Phases 267/271); structural, no solver |
| `ScribbleExport` | Phase 270 — the `@Protocol` global type emitted as real Scribble (`rec/continue`, `choice at`, Scribble-Java `par`; a mixed choice refused as outside the standard fragment); `main` writes the curated corpus for the `nuscrCheck` oracle task |
| `ChannelGhosts` | Phase 259 — verification ghosts on channels as Groovy extension properties (registered via `META-INF/groovy/org.codehaus.groovy.runtime.ExtensionModule`) so a spec closure type-checks: `c.taken`, the elements the enclosing loop has taken from `c` so far, rewritten by the checker to the loop's taken-ghost, and `c.sent` (Phase 260), the elements its process has sent, rewritten to the producer's shadow list; executing either throws |
| `Sets` / `Sorted` / `Fib` / `Trib` / `Tetra` / `Gcd` / `Lcm` / `Bezout` / `Fact` / `Binom` | runtime-executable spec helpers the encoder recognises, each lowered to an axiomatised primitive — `Sets.boundedBy`/`boundedCount` (cardinality), `Sorted.ascending`/etc. (the flat two-variable sortedness axiom, also reached via the native `xs.isSorted()`), `Fib.of(i)` (Fibonacci), `Trib.of(i)` (tribonacci/`fibfib`), `Tetra.of(i)` (tetranacci/`fib4`), `Gcd.of(a, b)` (Euclid), `Lcm.of(a, b)` (least common multiple, via the gcd identity), `Bezout.u/v(m, n)` (the Bézout coefficients, Phase 204), `Fact.of(n)` / `Binom.of(n, k)` (factorial and Pascal-rule binomial, the combinatorics pack) |
| `PathFacts` | enclosing-`if` path conditions per expression site |
| `ContractTester` | the bounded property-based fallback (Phase 62): runs the executable contract over a small integer grid when the solver returns *UNKNOWN*, reporting a `fails on:` repro |
| `CheckOverflow` | the opt-in `@CheckOverflow` annotation that turns on 32-bit integer-overflow obligations (Phase 44) |
| `Label` / `Declassify` | the `@Label('level')` / `@Label(by = 'm')` security classification (constant or value-dependent) on a parameter / method result / sink, and `Declassify.to(level, expr)` for explicit controlled release — driving the information-flow noninterference check over a user-defined lattice (Phase L1) |
| `Rely` / `Guarantee` / `UnderRely` | `@Rely('T')` / `@Guarantee('T')` two-state predicates over shared state; the verifier auto-discharges the §IV rely/guarantee *compatibility* lemmas (reflexive/transitive relies, `G_i ⟹ R_j`). `@UnderRely('T')` then runs a method's body under that rely: `ContractExpansionTransform` synthesises a rely-step from the `@Rely('T')` predicate and frames every shared access (straight-line, branches, and loop bodies via the `LoopEncoder` call-handler), so each thread's *code* is proven to uphold its rely — both §IV halves (Phase L1). `@Guarantee('T')` on a *body* method additionally declares **conformance** (Phase 244): the method's own-step transition (env step stripped) is proved against the `T` guarantee predicate on a synthesised twin, and — in conformance-adopting classes — a rely with no peer guarantee reports as unbacked |
| `ContractExpansionTransform` / `ContractSource` / `ClassInvariantSource` / `SelfEnsures` / `UnderRely` | global CONVERSION transform capturing verbatim contract text (`requires`/`ensures`/`decreases`/`modifies`, and a class-level `invariant`) + clean body snapshots onto the runtime carriers the checker re-parses; also desugars `@SelfEnsures` into a captured `@Ensures({ result == <verbatim body> })` so a self-specifying body is written once, and for `@UnderRely('Role')` synthesises a `$rely$Role` rely-step from the class's `@Rely('Role')` predicate (frame + `old`-rewritten ensures + class invariant) and prepends the call before the snapshot (prototypes) |
| `Requires` / `Ensures` / `Decreases` (String-valued) | the Java-friendly twins of groovy-contracts' closure annotations — the condition is a `String` (`@Requires('x >= 0')`), a *legal Java annotation value* where a closure is not, so a `.java` file can carry them (javac-built as inert metadata) and be verified by compiling the same source as Groovy. `ContractExpansionTransform` captures the String into the same `ContractSource` text the checker re-parses, and the `findRequires` / `findEnsures` gates recognise them alongside the closure forms. Loop-free / recursive methods only — Java forbids annotating a statement, so per-loop invariants are out of reach (prototype) |
| `SmtBackend` / `Z3Backend` | the solver seam (`SmtBackend.session()` → `SmtSession`) and its z3-turnkey implementation — which also serves the `VERIFY_EXPLAIN` ablation (drop-one re-prove in fresh full-strength solvers) and the `VERIFY_DUMP_SMT` SMT-LIB2 emission (Phase 127) |
| `Reporter` | OpenJML-style diagnostics with inline counterexamples, plus the opt-in diagnostic knobs `VERIFY_REFUTATION` / `VERIFY_SUGGEST` / `VERIFY_EXPLAIN` / `VERIFY_DUMP_SMT` (Phase 127) |

## The solver seam

`Encoder` is written against the `SmtBackend` / `SmtSession` interface; `Z3Backend`
(via the z3-turnkey distribution, native libs bundled) is the only concrete binding,
so an alternative solver is a drop-in. Z3 runs at the consumer's compile time; the
project is otherwise pure-Groovy. (`VERIFY_DUMP_SMT` emits each query as a standalone
SMT-LIB2 benchmark for piping to another solver — the cheap, measured precursor to ever
swapping the binding, since the encoder is Z3-tuned.)

## Metadata handoff

The two phases communicate through node metadata keyed by string constants on
`ContractExpansionTransform`, so `VerifyChecker` reads the *captured* forms rather
than the live (rewritten) AST:

- `ORIGINAL_BODY_KEY` — the clean postcondition-body snapshot the checker enumerates
  return paths over, instead of `method.getCode()` (which groovy-contracts mutates).
- `LOOP_SPEC_KEY` — the `LoopSpec` (guard / body / invariants / variant) captured on
  an annotated loop before groovy-contracts injects invariant asserts into the live
  body; also where the opt-in loop-invariant *inference* attaches a synthesised
  invariant.

Contract *text* is re-parsed from the `ContractSource` / `ClassInvariantSource`
carriers (a clean `CONVERSION` AST), immune to the resolution and rewrites later
phases apply to the live closure.
