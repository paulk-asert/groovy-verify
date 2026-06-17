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
| `VerifyChecker` | the `@TypeChecked` extension; call-site, body, loop & implicit checks, annotation-law synthesis (`@Reducer` / `@Monadic`), and the information-flow noninterference walk (`@Label`) |
| `Encoder` | Groovy expression → SMT (the fragment lives here) |
| `BodyEncoder` / `LoopEncoder` | path enumeration & symbolic execution for `@Ensures`/loops |
| `PureEvaluator` | closed pure-function evaluation & fuel-bounded unfolding — the normalise-then-SMT accelerator (Phase 8a) |
| `Forall` | the `Forall.range(lo, hi){…}` bounded-quantifier helper (the native GDK `every`/`any` idioms are the preferred surface) |
| `Sets` / `Sorted` / `Fib` / `Trib` / `Tetra` / `Gcd` / `Lcm` | runtime-executable spec helpers the encoder recognises, each lowered to an axiomatised primitive — `Sets.boundedBy`/`boundedCount` (cardinality), `Sorted.ascending`/etc. (the flat two-variable sortedness axiom, also reached via the native `xs.isSorted()`), `Fib.of(i)` (Fibonacci), `Trib.of(i)` (tribonacci/`fibfib`), `Tetra.of(i)` (tetranacci/`fib4`), `Gcd.of(a, b)` (Euclid), `Lcm.of(a, b)` (least common multiple, via the gcd identity) |
| `PathFacts` | enclosing-`if` path conditions per expression site |
| `ContractTester` | the bounded property-based fallback (Phase 62): runs the executable contract over a small integer grid when the solver returns *UNKNOWN*, reporting a `fails on:` repro |
| `CheckOverflow` | the opt-in `@CheckOverflow` annotation that turns on 32-bit integer-overflow obligations (Phase 44) |
| `Label` / `Declassify` | the `@Label('level')` / `@Label(by = 'm')` security classification (constant or value-dependent) on a parameter / method result / sink, and `Declassify.to(level, expr)` for explicit controlled release — driving the information-flow noninterference check over a user-defined lattice (Phase L1) |
| `Rely` / `Guarantee` / `UnderRely` | `@Rely('T')` / `@Guarantee('T')` two-state predicates over shared state; the verifier auto-discharges the §IV rely/guarantee *compatibility* lemmas (reflexive/transitive relies, `G_i ⟹ R_j`). `@UnderRely('T')` then runs a method's body under that rely: `ContractExpansionTransform` synthesises a rely-step from the `@Rely('T')` predicate and frames every shared access (straight-line, branches, and loop bodies via the `LoopEncoder` call-handler), so each thread's *code* is proven to uphold its rely — both §IV halves (Phase L1) |
| `ContractExpansionTransform` / `ContractSource` / `ClassInvariantSource` / `SelfEnsures` / `UnderRely` | global CONVERSION transform capturing verbatim contract text (`requires`/`ensures`/`decreases`/`modifies`, and a class-level `invariant`) + clean body snapshots onto the runtime carriers the checker re-parses; also desugars `@SelfEnsures` into a captured `@Ensures({ result == <verbatim body> })` so a self-specifying body is written once, and for `@UnderRely('Role')` synthesises a `$rely$Role` rely-step from the class's `@Rely('Role')` predicate (frame + `old`-rewritten ensures + class invariant) and prepends the call before the snapshot (prototypes) |
| `SmtBackend` / `Z3Backend` | the solver seam (`SmtBackend.session()` → `SmtSession`) and its z3-turnkey implementation |
| `Reporter` | OpenJML-style diagnostics with inline counterexamples |

## The solver seam

`Encoder` is written against the `SmtBackend` / `SmtSession` interface; `Z3Backend`
(via the z3-turnkey distribution, native libs bundled) is the only concrete binding,
so an alternative solver is a drop-in. Z3 runs at the consumer's compile time; the
project is otherwise pure-Groovy.

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
