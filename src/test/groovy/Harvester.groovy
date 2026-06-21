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
import groovy.json.JsonOutput

/**
 * SKETCH — harvest the proof-capability corpus + catalog from {@link VerifyHarness#CASES}, the single source of
 * truth, for AI-agent discoverability. A pure projection: the outcome is read from each case's declared spec
 * ({@code ok} / {@code expect} / {@code refute}), which CI already proves matches reality — so this runs in
 * milliseconds with no Z3. (A {@code -verify} mode could instead run {@code VerifyHarness.compile} to attach the
 * real counterexample text; left as the production refinement.)
 *
 * Produces two artifacts under the output dir (default {@code build/harvest}):
 *   • corpus.jsonl  — one record per case: {id, group, name, outcome, annotations, diagnostic, source}
 *   • catalog.json  — per-capability (group) aggregation, for the agent "what can it prove" manifest
 *
 * Run: {@code ./gradlew harvest}   (freshness check: {@code ./gradlew harvest --args='<dir> -check'})
 */
class Harvester {

    /** Contract / checker annotations recognised in a snippet — the authoring vocabulary the agent must learn. */
    static final List<String> ANNOS = ['Requires', 'Ensures', 'Invariant', 'Decreases', 'Modifies', 'SelfEnsures',
        'Label', 'Declassify', 'Reducer', 'Associative', 'Monadic', 'Rely', 'Guarantee', 'UnderRely', 'CheckOverflow']

    /**
     * The ONE manual enrichment: a one-line capability description per test group. The cross-check lint
     * (DocLint) fails the build for any group missing here, so it can't silently fall out of sync. (In
     * production this is better as a `description:` field on each group in CASES, or a co-located data file.)
     */
    static final Map<String, String> GROUP_DESC = [
        'Dafny port'                  : "Ported Dafny benchmark proofs (VSComp10 SumMax, linear search): sum <= n*max, find returns the matching index or none.",
        'GROOVY-12071'                : "Generic-typed tuple slots / map values / list elements keep their declared type in a contract, so arithmetic on them needs no cast (GROOVY-12071).",
        'HE013 gcd'                   : "HumanEval 013 — Euclid's gcd via the Gcd.of(a,b) recurrence helper; the iterative loop proves equal to the spec.",
        'HE045 triangle_area'         : "HumanEval 045 — triangle area a*h/2 in IEEE-754 FP: exact doctest, finiteness, and positive-sides ⇒ result >= 0.",
        'HE071 triangle_area'         : "HumanEval 071 — squared Heron area (sqrt-free, exact integers): the triangle inequality makes s-a non-negative, a valid triangle's squared area is non-negative or -1, an incomplete validity check refutes, and the int product overflows under @CheckOverflow.",
        'HE072 will_it_fly'           : "HumanEval 072 — a list flies iff it is a palindrome and its sum <= w: a loop-built flag equals the content quantifier (0..<n).every { q[it]==q[n-1-it] }, an ends-only check refutes, the combined palindrome+sum proof, and forgetting the palindrome half refutes.",
        'HE042 incr_list'             : "HumanEval 042 — element-wise map: build a list whose every element is the input + 1, with a per-element @Ensures over the returned list; forgetting the +1 refutes.",
        'HE152 compare'               : "HumanEval 152 — element-wise over two lists: each output is the absolute difference |game[i]-guess[i]| (abs as the body's conditional); the signed difference (no abs) refutes.",
        'HE062 derivative'            : "HumanEval 062 — index-weighted map: a polynomial's coefficients become [c1*1, c2*2, ...] (size n-1), each output the next coefficient times its power; using the index instead of the power refutes.",
        'HE052 below_threshold'       : "HumanEval 052 — boolean predicate over a list: true iff every element is below t; the early return-false witnesses the negated quantifier, and an off-by-one (<= t) refutes.",
        'HE009 rolling_max'           : "HumanEval 009 — running maximum into a returned list: the implied monotone+dominates characterisation (each output >= its element and non-decreasing) verifies; returning the input unchanged refutes on a descending list.",
        'HE085 add'                   : "HumanEval 085 — conditional accumulator: summing the even-valued elements at odd indices keeps the running sum even (a parity invariant); claiming the sum is odd refutes.",
        'HE121 solution'              : "HumanEval 121 — conditional accumulator: summing the odd-valued elements at even indices over a non-negative list stays >= 0 (a sign invariant); a strict > 0 claim refutes since the sum can be zero.",
        'HE043 pairs_sum_to_zero'     : "HumanEval 043 — is there a pair summing to zero: the nested-existential biconditional verifies via a seen.contains rewrite (the Verus break is unsupported) and a 'no pair so far' invariant; an always-true checker refutes on the empty list.",
        'P153 async-await'            : "Groovy 6 async/await: a safe async closure (a pure value) is driven synchronously, so `await (async { e })` reads out `e` and the functional contract proves (compute), a bug after the await refutes (computeBuggy), chained awaits thread the value (computeTwice), and an opaque parameter Awaitable skips.",
        'HumanEval port'              : "Faithful Verus-HumanEval ports (strlen, get_positive, is_prime) with the functional @Ensures the originals omit.",
        'NNDOC'                       : "The README @NonNull lifecycle example, composed under NullChecker + VerifyChecker.",
        'NNFIELD'                     : "A class @Invariant that a field is non-null: established by the constructor, broken by an unguarded ctor or a nulling method (refutes).",
        'Native isSorted'             : "The native xs.isSorted() / .sorted predicate yields the sortedness gap fact (a[i] <= a[j] for i<j) for arrays and lists.",
        'P decl forms'                : "Local declaration forms def / var / val are interchangeable in the fragment.",
        'P expr inc/dec'              : "Side-effecting ++ / -- in expression position (x = i++, x = ++i) hoist to the old/new value plus the increment.",
        'P regex matches'             : "A .matches postcondition is proven from a matches precondition; a wrong character-class claim refutes.",
        'P-array'                     : "Information-flow over an array's value-dependent positional label (the §VII buffer): the consumable region is Low; reading the High region or advancing tail over a secret refutes.",
        'P-arrayelem'                 : "int[] element values appear in counterexamples, and an element-wise refutation names the offending slot.",
        'P-call-frame'                : "A @Modifies call havocs un-pinned fields; a rely-step's @Ensures re-establishes the obligation, a weakened rely no longer does.",
        'P-carrier'                   : "A single-value @Monadic wrapper carrier round-trips (new Res(m.v) == m); distinct carriers are not forced equal.",
        'P-counter'                   : "A monotone-counter rely/guarantee: an observed lower bound persists across interference; a non-monotonic rely drops it.",
        'P-fizzbuzz'                  : "Element-wise FizzBuzz array-fill correctness; an off-by-one surfaces the offending element value.",
        'P-fourchecker'               : "One Maybe class under four checkers (Null/Monadic/Purity/Verify) with a live DO-comprehension: Vavr-style auto-proves the laws, Optional-style refutes functor composition.",
        'P-hof'                       : "A java.util.function.Function's apply is an uninterpreted congruent function: f(a)==f(a) proves, f(a)==f(b) refutes.",
        'P-incdec'                    : "A side-effecting array index a[i] = ++i / a[i] = i++ snapshots the index and proves bounds; a wrong claim refutes.",
        'P-induction'                 : "Recursive methods proven by induction via @Decreases (factorial grows >= linearly; the recursive call is the inductive hypothesis).",
        'P-inheritance'               : "A super.m() call assumes the parent's postcondition and must satisfy the parent's precondition.",
        'P-lcm'                       : "Least common multiple via Lcm.of(a,b): the identity lcm*gcd == a*b proves symbolically and literals unfold via Euclid.",
        'P-libmonad'                  : "Real library monad shapes (Vavr Option, Functional Java Option, java.util.Optional): the five monad/functor laws prove, Optional refutes functor composition.",
        'P-lsp'                       : "Behavioural subtyping (Liskov): an override may weaken @Requires / strengthen @Ensures, never the reverse — strengthening refutes with a witness.",
        'P-maybe'                     : "A two-case Some|None @Monadic carrier: Vavr-style auto-proves all laws, Optional-style (@NonNull content) auto-refutes functor composition.",
        'P-monadauto'                 : "@Monadic alone synthesises and proves the monad/functor laws for a modellable carrier; an unmodellable shape is left alone.",
        'P-monadlaw'                  : "The monad laws hand-written (left/right identity, associativity) prove; a wrong bind equation refutes.",
        'P-msg'                       : "Scalar producer/consumer information flow: declassify-then-deliver verifies; delivering an unreleased secret, or a secure-update that publishes one, refutes.",
        'P-multichecker'              : "RegexChecker (pattern syntax) + VerifyChecker (match semantics) compose on the same .matches, each on its own concern.",
        'P-nonnull'                   : "An explicit result != null postcondition proven from a non-null parameter/literal; an unconstrained param refutes.",
        'P-reducer'                   : "@Reducer / @Associative auto-prove a combiner's monoid laws (associativity + identity); @Associative on subtraction refutes.",
        'P-rely-step'                 : "A hand-written rely-step (@Modifies + @Ensures over old) survives interleaving; a weakened rely no longer protects the read.",
        'P-rg-guarantee'              : "A standalone @Guarantee predicate proves (and a violation refutes), including after a rely-call.",
        'P-ring'                      : "The merged Buffer flagship: both §IV rely/guarantee halves on one class (compatibility lemmas + @UnderRely-framed bodies), including rely-steps inside loop bodies.",
        'P-seqconcat'                 : "Straight-line String concatenation in contracts/bodies; an inline string combiner proves, a combiner call in return position skips honestly.",
        'P-shift-power'               : "A shift equals a power of two (1 << n == 2 ** n); an off-by-one is caught.",
        'P-strcat'                    : "String concatenation is associative but not commutative (proven via void/boolean law lemmas on the str.++ monoid).",
        'P-trait'                     : "A trait's @Invariant and contracted default methods are verified on every implementing class.",
        'P-vf-field'                  : "Field self-increment / const-write in a body, tracked in SSA, checked against an assert (true proves, false refutes).",
        'P-vii'                       : "The §VII capstone: information flow × rely/guarantee on one buffer verifies; a producer leaking a secret under R/G still refutes. A Lincheck-ready variant keeps the rely-stable @Requires (proof goes through, the runtime guard is dead under it) while a live runtime empty/full guard makes the same source thread-safe to call.",
        'P1 bounds'                   : "An array index is in bounds only under a guard / @Requires; an unguarded index refutes (IndexOutOfBounds).",
        'P1 division'                 : "A divisor/modulus obligation: guarded verifies, unguarded refutes (divide-by-zero).",
        'jakarta validation'          : "Jakarta/javax Bean Validation numeric constraints (@Positive/@Min/@Max/…) read as method-entry preconditions; contradictory ones are flagged vacuous.",
        'nonnull param'               : "A @NonNull-style annotation (NullChecker / Checker Framework / JSR-305 vocabulary) on a reference parameter is read as a non-null precondition, discharging a deref or apply the unannotated form could not.",
        'P131 dimensions'             : "JSR 385 dimensional analysis: a Quantity's kind (its [Length,Mass,Time] exponent vector) is propagated through multiply/divide and checked against the cast/return kind — the result-kind the generic type can't infer.",
        'P132 unit scale'             : "JSR 385 value/scale: a Quantity built from known units (getQuantity/prefixes/add/to) has its SI magnitude recovered, so getValue() in a named unit verifies exactly and a wrong-unit extraction refutes (the Mars scale bug).",
        'P133 record ctor'            : "A single-component record is modelled as a one-constructor datatype, so `new R(v).f == v` round-trips (the canonical-constructor gap, closed for records) — enabling a bespoke, self-contained value type (e.g. a units Length) to verify; richer forms (operators, carrier locals) skip gracefully.",
        'P142 multi-record'           : "A multi-component record is a one-constructor N-field datatype (the TupleN analogue), so `new R(a,b).f` round-trips — enabling a dimension-carrying Quantity(value, L, M, T) whose multiply scales the value and composes the exponent vector, the full dimensional algebra in one type.",
        'P142c conversion'            : "In-record unit conversion: a factory (km) and accessor (inKm) are scale arithmetic on the component, so the round-trip `km(2).inKm() == 2` and record equality `km(1) == metres(1000)` verify, a wrong factor refutes, and a cross-class `Length.km(2)` resolves.",
        'P143 decimal div'            : "BigDecimal division is modelled soundly: a terminating divisor (only the prime factors 2 and 5, e.g. /1000) is exact in Groovy so it verifies (the unit-conversion read-out), a wrong factor refutes, and a non-terminating divisor (Groovy rounds) skips loudly rather than prove a runtime-false fact.",
        'P144 carrier replay'         : "A carrier-returning contracted call (a factory like Quantity.km(1), or a routed operator) is modelled in the precondition-check's prefix replay, not havoced to an Int — so factory-built operands feed a guarded operator (Quantity.km(1) + Quantity.mile(1) == 2609.344 in metres), the dimension guard fires across the replay, and a wrong total refutes.",
        'P145 carrier chain'          : "A carrier-returning call is a value in expression position, not only a local-assignment RHS, so a single-expression chain resolves: Quantity.km(1).plus(Quantity.mile(1)) == 2609.344 in metres (receiver and argument are both factory calls), the fluent twin of the JSR 385 example — the guarded .plus precondition still discharges over the real argument (a wrong total refutes the postcondition, a mismatched dimension refutes the guard).",
        'P146 chain read-out'         : "A component read on a chain result — Quantity.km(1).plus(Quantity.mile(1)).value — reads the SI magnitude straight off the chain (the terminal step of the JSR-385 shape), proving 2609.344 as a BigDecimal with no intermediate locals. Each maximal carrier call is hoisted to a temp local so the .value read resolves; it composes with decimal arithmetic and works as a local RHS, and a wrong magnitude refutes.",
        'P147 units-as-data'          : "A unit is itself a Unit(scale, l, m, t) record value and Quantity.of(v, unit) a factory reading its fields, so the literal JSR 385 shape verifies on the bespoke type with no new engine code: Quantity.of(1, Unit.kilo(Unit.metre())).plus(Quantity.of(1, Unit.mile())).value == 2609.344 (a metric prefix is a Unit->Unit factory). A wrong total refutes the postcondition and a length-plus-mass refutes the dimension guard.",
        'P1 null'                     : "A dereference needs a non-null guard or @Requires; an unguarded deref refutes (NPE).",
        'P10 instance'                : "Instance methods with field reads/writes and parameter contracts verify (getter, mutator).",
        'P100 string next'            : "A user String.next() example over A..Z proves the letter-advance; stepping off the range refutes.",
        'P101 range non-null'         : "A range-membership fact implies non-null (deref ok with no guard); the same under || does not, so an NPE is still flagged.",
        'P102 switch expr'            : "A switch expression (arrow form, int/String/range labels) folds to an ite-chain; an unmatched case or a false branch claim refutes.",
        'P103 mask-as-mod'            : "Bit-masking modelled as modular arithmetic (round-up-to-16 via &; parity x & 1 in {0,1}); a soundness boundary at INT_MIN refutes.",
        'P104 OpenJML'                : "OpenJML's max-by-elimination: the result indexes a maximum; a false min-claim refutes.",
        'P105 string-seq'             : "A read-only per-character loop with a quantified invariant over s.charAt(i) (e.g. all-lowercase); a too-strong char bound refutes.",
        'P106 char-seq'               : "Building a char[] buffer char-by-char (the Int-element-array route for string construction), e.g. functional ChangeCase; a wrong-char claim refutes.",
        'P107 ring-buffer'            : "A ring buffer as a mutable data structure: enqueue/dequeue preserve the class @Invariant under @Modifies framing; an over-strong frame refutes. Both the non-wrapping bounded queue and the WRAPPING circular (modulo) ring verify — `items[t % capacity]` is proven in bounds — so the circular shape is no harder for the fragment.",
        'P149 null-return'            : "A reference-typed method that returns null on a path (e.g. a bounded queue's Integer poll() → null when empty) still verifies its @Invariant / @Ensures over other state: result binds as null, so result == null proves and result != null refutes. This lets the exact SpscBuffer.groovy source verify under groovy-verify (SpscBufferVerifyTest).",
        'P108 content-index'          : "A content-dependent index a[b[k]] (gather / histogram) bounds against a value-range invariant inside the loop; a missing range refutes.",
        'P109 nested-return'          : "A nested (doubly-looped) search that returns a witness on a match verifies, and the in-body return's @Ensures is checked.",
        'P11 old'                     : "old(...) snapshots pre-state field and array contents, so a mutator's post/pre delta is checked; a wrong delta refutes.",
        'P110 tuple-exit'             : "A Tuple returned from a mid-loop early-exit (return Tuple.tuple(i,j)); a wrong slot order refutes.",
        'P111 Duplets-totality'       : "The FoVeOOS Duplets challenge proven total — a real duplet is returned (the sentinel fall-through is infeasible under the existential precondition).",
        'P112 dupletExcept'           : "The dupletExcept variant proven total; without the existential precondition it refutes.",
        'P113 interproc-tuple'        : "A tuple-returning call bound to a local whose slots carry the callee's @Ensures into the caller's body (the interprocedural-tuple case).",
        'P114 records'                : "A record's components read like final fields in contracts, and a record may carry its own contracts; a wrong component refutes.",
        'P115 monitor-invariant'      : "Lock transforms (@WithWriteLock / @Synchronized) are transparent, so the class @Invariant is the monitor invariant each critical section preserves (e.g. balance >= 0).",
        'P116 monoid'                 : "A two-checker compile (CombinerChecker + VerifyChecker) over a real injectParallel site: the shape is checked and the monoid laws + reduce==sum proven.",
        'P117 agent-invariant'        : "An Agent/actor's class @Invariant is the serialized monitor invariant each handler preserves (bounded-buffer occupancy); an unguarded add refutes.",
        'P118 dataflow'               : "A single-assignment dataflow network desugars to SSA and proves its computed value (a+b); a wrong value refutes.",
        'P119 channels'               : "A channel pipeline collapses to function composition (FIFO assumed) and proves the per-element transform; a wrong transform refutes.",
        'P123 interface contracts'    : "An interface method's @Requires/@Ensures is inherited by every implementer — the contract-inheritance walk traverses implemented interfaces, not just the superclass.",
        'P124 BigInteger'             : "BigInteger maps to Z3's unbounded Int sort exactly (no width/overflow): values flow as Int and a literal (42g) folds; a literal wider than 64 bits skips loudly.",
        'P125 complement & ushr'      : "Bitwise complement ~x (the exact Int identity -x-1) and the unsigned/logical right shift x>>>1 (via the 32-bit bit-vector, always non-negative — unlike the arithmetic >>).",
        'P12 perm'                    : "Permutation reasoning via element multiplicity: a swap preserves the multiset, a copy is not a permutation, insertion sort permutes.",
        'P13 frame'                   : "A @Modifies frame is checked: an honest frame verifies, an undeclared write refutes.",
        'P14 sort'                    : "Insertion sort proven sorted AND a permutation at once; a no-op sort cannot claim sorted.",
        'P15a class-invariant'        : "A class @Invariant is assumed on method entry and checked preserved on exit; a mutator that breaks it refutes.",
        'P15b ctor-invariant'         : "A constructor must establish the class @Invariant (not assume it); a ctor leaving it false refutes.",
        'P16 sets'                    : "Finite Set membership: x in s / !in, and an assumed membership entails membership.",
        'P17 maps'                    : "Finite Map lookup/store (m[k], put): a put stores the value and adds the key.",
        'P18 reachability'            : "A DFS's visited set grows monotonically and covers the target node (fuel- and cardinality-bounded).",
        'P19 cardinality'             : "Set cardinality: a full bounded set covers its domain; coverage needs the bound; size <= n.",
        'P20 bcount'                  : "The bounded-count law 0 <= bcount(s,k) <= k; a full domain gives bcount==k, over-counting breaks the bound.",
        'P21 bcount law'              : "The per-mutation count law: a fresh in-domain add increments the count, a non-fresh or out-of-domain add does not.",
        'P22 full-char'               : "count==k iff every domain node is in the set (the cardinality characterisation of full coverage).",
        'P23 completeness'            : "A DFS closure invariant: closed ⇒ every successor is covered; marking a node breaks closure at the boundary.",
        'P24 call-site'               : "A callee's precondition is discharged at the call site against the post-mutation state.",
        'P25 recursive-defs'          : "Recursively-defined reachability/bcount proven by induction over the defining equation; a wrong bound refutes.",
        'P26 frontier'                : "A DFS establishes its closure via a frontier/stack invariant.",
        'P27 non-int domains'         : "String-element sets: literal membership round-trips, distinct literals are not collapsed.",
        'P28 enum.values'             : "enum.values().length / .size() folds to the enum's value count in a body; a wrong count refutes.",
        'P29 enum-sets'               : "A finite-state-machine's reachable states as an enum/ordinal set: full coverage entails every state, partial coverage cannot.",
        'P30 subset'                  : "containsAll as subset: subset entails membership transfer (and reflexivity); membership without subset refutes — for enum-element sets.",
        'P31 int-subset'              : "The same subset reasoning for Int-element sets under Sets.boundedBy.",
        'P32 containsValue/equals'    : "Map.containsValue for enum-keyed maps (key-pinned value), and map equality.",
        'P33 union/intersect'         : "Inline set algebra membership: union is a disjunction, intersection a conjunction of operand memberships.",
        'P35 materialised set'        : "A materialised set Set u = a op b mints u as a first-class set whose membership follows the iff axiom.",
        'P35b set return'             : "Returning a set-algebra result (a & b, a | b, a.or(b)) as a Set.",
        'P36 nested map<set>'         : "Nested Map<K,Set<V>> reads: x in m[k] / m[k].contains / m[k].containsAll round-trip; distinct keys do not leak membership.",
        'P37 element null'            : "List element nullability: an unguarded xs[i].method() refutes; a @Requires xs[i]!=null or an if-guard verifies.",
        'P38 factory'                 : "Immutable factories (List.of / [a,b,c]) peephole-fold .size()/.contains/.get(literal) to ground terms.",
        'P38b factory local'          : "The factory folds lift across a local binding (xs = List.of(...); xs.size()).",
        'P38c immutable'              : "Factory edge cases: Set.of with duplicate literals skips the fold, unmodifiable wrappers are transparent.",
        'P38c projection'             : "Map.of(...).keySet()/.values().contains folds.",
        'P38c symbolic i'             : "A factory container indexed by a symbolic i in range folds; without the bound it refutes.",
        'P39 idioms'                  : "Collection accessor idioms are equated: xs.get(i)===xs[i], xs.first()/head()===xs[0].",
        'P4 contains'                 : "An assumed .contains entails contains; an unproven one refutes.",
        'P4 cross-boundary'           : "A guard / enclosing @Requires proves a callee argument non-null across the call; a possibly-null arg refutes.",
        'P4 equals'                   : "x.equals(y) is equated with ==; a missing assumption refutes.",
        'P4 isEmpty'                  : "isEmpty() is equated with size()==0.",
        'P4 size'                     : "A @Requires bound on .size() verifies an index.",
        'P40 list mutation'           : "xs.add(v): size grows by one and the new last element is v; a wrong delta refutes.",
        'P41 list bcount'             : "xs.add(v) raises xs.count(v) by one and leaves count(w) unchanged for w != v.",
        'P42 mutation replay'         : "After xs.add, an in-bounds read (xs[size-1]) passes the implicit bounds check.",
        'P43 field bounds'            : "A field-collection removeLast/first needs a size guard; unguarded refutes.",
        'P44 overflow'                : "Opt-in @CheckOverflow: arithmetic must stay in 32-bit range — bounded inputs verify, an unguarded increment refutes.",
        'P44c width overflow'         : "Width-aware overflow: long n+1 verifies under a 64-bit bound (no spurious 32-bit refute) but refutes at the 64-bit boundary.",
        'P45 cross-class'             : "A foreign class's @Invariant is assumed at entry when reasoning across classes; a stronger claim refutes.",
        'P46 fib4'                    : "HumanEval 046 — tetranacci (fib4) via the Tetra.of(i) recurrence helper; the iterative version proves equal to the spec.",
        'P46a string preds'           : "String predicates (startsWith/endsWith/contains) as uninterpreted Bool functions; a contract assumption flows, and contains routes to the string (not list) predicate.",
        'P46b string length'          : "String .length()/.size() pinned for literals and equated; a wrong literal length refutes.",
        'P46c string axioms'          : "String length axioms: non-negativity, startsWith implies a length bound, a too-short string never starts with a longer prefix.",
        'P46d in-loop guards'         : "An in-loop if / && guard discharges a list-element deref obligation; an unguarded in-loop deref refutes.",
        'P46e charAt'                 : "Literal s.charAt(i) folds (first/last position); a wrong literal refutes.",
        'P47 string theory'           : "Z3's native string theory: prefixof implies equal chars, distinct literals are theory-distinct, literal concat folds.",
        'P47b replace/indexOf'        : "Literal String.replace / indexOf fold (single occurrence, no-op on absent).",
        'P47c regex'                  : "Literal regex .matches: exact match verifies, wrong string refutes, dot matches a single position.",
        'P47d regex extras'           : "Regex character classes \\d+ / \\w+ match/reject digit and alphanumeric strings.",
        'P47e int/string'             : "Integer.toString / String.valueOf / Integer.parseInt fold for literals.",
        'P47f weak ops'               : "replaceAll as a weak-axiom op: no-op on absent, length preserved under equal-length swap, unprovable under unequal-length.",
        'P47g case'                   : "Literal toUpperCase/toLowerCase fold; a wrong-case literal refutes.",
        'P47h gstring'                : "GString interpolation folds for String/int literal holes (single and multiple).",
        'P47i reverse'                : "Literal String.reverse folds and a palindrome reverses to itself; a wrong reversal refutes.",
        'P47j ==~'                    : "Groovy's ==~ match operator reflects the match and is equivalent to .matches; a false claim refutes.",
        'P48 NIA'                     : "Nonlinear integer arithmetic via Z3's NIA solver: multiplication commutativity, positive product, non-negative square.",
        'P49 prefix-exits'            : "Early returns in a loop's prefix region (before the loop) are verified per path; a postcondition violation on an exit refutes.",
        'P49b in-body exits'          : "An if(cond) return e at the top of a loop body is verified on its own path; preservation holds on the no-exit path.",
        'P50 groovy div/mod'          : "Groovy-faithful % (sign of dividend) and intdiv (truncate toward zero); a claim that % is always non-negative refutes.",
        'P51 sum'                     : "A list sum aggregation carried by a loop invariant (s == xs[0..<i].sum()), via base/step axioms.",
        'P52 below_zero'              : "HumanEval 003 below_zero — the full biconditional: result iff some prefix sum is negative.",
        'P53 product'                 : "A product aggregation via the inject(1){a,x->a*x} fold (and the inject(0) sum fold).",
        'P54 int-string signs'        : "A negative Integer.toString is non-empty (a claim that it isEmpty refutes).",
        'P55 fib'                     : "HumanEval 055 — Fibonacci via the Fib.of(i) recurrence helper; the iterative version proves equal to the spec.",
        'P56 max'                     : "max_element/min_element as a witnessed extremum (bounds every element AND is achieved by one); returning a[0] refutes.",
        'P57 implies'                 : "Logical implication ==> / .implies(): modus ponens proves, an implication without its antecedent refutes.",
        'P57 monotonic'               : "HumanEval 057 monotonic — a list is all-non-decreasing OR all-non-increasing (a disjunctive ∀∀ spec via dual existential flags).",
        'P58 spaceship'               : "The spaceship <=> as a three-way comparator (-1/0/1 = Integer.compareTo); a contract over it verifies.",
        'P59 for-loop'                : "A classic for(init;cond;update) loop with @Invariant/@Decreases verifies bounds + postcondition; a missing precondition refutes.",
        'P5a short-circuit'           : "A short-circuit && / || guard protects accesses in its right operand; an unguarded access still refutes.",
        'P5a value-flow'              : "An index constrained by a prior assignment (or an aliased index under a guard) is verified; an unconstrained one refutes.",
        'P5b loop-fused'              : "An in-loop array index is verified from the invariant (and refuted when unbounded); the post-loop index too.",
        'P6 in-loop store'            : "An in-loop array store (zero-fill) preserves a quantified invariant; a store that breaks it refutes.",
        'P6 quantifiers'              : "A bounded forall assumed in a precondition entails an instance; sortedness entails adjacent order.",
        'P6 store'                    : "After an array store, the stored element reads back; a wrong store value refutes.",
        'P60 max/min'                 : "result == a.max()/a.min() as the witnessed-extremum spec; returning a[0] refutes.",
        'P61 decimal'                 : "The / operator is exact BigDecimal/Real division (a/2 == 2.5), contrasted with intdiv.",
        'P62 pbt'                     : "When the solver returns UNKNOWN, a bounded property-based pass refutes by testing and reports a fails-on repro (or bails to could-not-decide).",
        'P63 fibfib'                  : "HumanEval 063 — tribonacci (fibfib) via the Trib.of(i) recurrence helper; the iterative version proves equal to the spec.",
        'P63 for-in'                  : "A for(x in xs) / Java-style for(:) loop desugars to the indexed while-machinery (the index is hidden, the loop variable keeps its name).",
        'P64 loop-stable req'         : "Only loop-stable @Requires facts are carried into a loop; a precondition over modified state is soundly dropped.",
        'P65 per-element inv'         : "A for-in invariant referencing the loop variable x is a per-element check (verified with x = xs[idx] under the index bound).",
        'P66 repeated contracts'      : "Multiple @Requires (all assumed) and multiple @Ensures (all proven) on one method.",
        'P67 decimal negation'        : "BigDecimal unary minus / negative literals verify.",
        'P68 financial'               : "Conservation proofs: a transfer loses no money, a salami-slice skim is caught, interest credits every cent.",
        'P69 sum-under-store'         : "N-account conservation via old.bal.sum() across an array store; a skim fails the build (could not decide).",
        'P7 induction'                : "A recursive method (sumUp) proven by induction; a non-decreasing or too-strong claim refutes.",
        'P7 inter-proc'               : "A callee's @Ensures is assumed and @Requires discharged at the call site (contract, not body).",
        'P7 lemmas'                   : "A void recursive method as a reusable lemma (e.g. sortedness transitivity), proven once and applied by calling it.",
        'P7 recursive sort'           : "A recursive insertion sort proven sorted; an intervening store / missing insert refutes.",
        'P70 decimal sum'             : "List<BigDecimal> sum and N-account conservation via old.bal.sum(); a skim fails the build.",
        'P71 soundness'               : "Soundness anchors: a boolean field write is tracked (no crash), a vacuous precondition is flagged.",
        'P73 floating point'          : "IEEE-754 vs exact: BigDecimal 0.1+0.2==0.3 but double 0.1d+0.2d != 0.3d (claiming == refutes).",
        'P74 range bounds'            : "Range.containsWithinBounds as a pure bounds check over all range forms (step ignored).",
        'P75 streams'                 : "Bounded infinite-stream every/any over Stream.iterate(...).limit(n): a literal limit unrolls, a property of every element proves by induction, a witness for any.",
        'P76 decimal max/min'         : "List<BigDecimal> max/min as a witnessed extremum (bounds every element, achieved by one).",
        'P77 fp arrays'               : "double[] element predicates ride the FP theory: every>=0 ⇒ xs[0]>=0, but every>0 does not prove >=1 (FP), and sorted-adjacent holds.",
        'P78 int[] return'            : "An int[] return accepts a coerced [a,b] / new int[]{a,b} with constant-index result[k] and .length; a wrong length refutes.",
        'P78 list return'             : "A list-literal return binds result for constant-index result[k] (HumanEval 008 sum_product); a wrong element claim refutes.",
        'P79 tuples'                  : "Tuple/TupleN fixed-arity typed products with .vN slot access (and first/second/size), heterogeneous slots.",
        'P80 tuple params'            : "A tuple parameter's slots are read in the contract/body (homogeneous and heterogeneous).",
        'P81 tuple eq'                : "Component-wise tuple equality: equal constructed tuples prove equal, unequal refute.",
        'P82 nested'                  : "Nested tuples: .v1.v2 slot access in a body (and via a local).",
        'P83 named-map'               : "Groovy's map-as-named-tuple return (return [sum: s]; result.sum); a wrong value refutes.",
        'P84 map params'              : "A named-map parameter's values are read via property/subscript and used in body arithmetic.",
        'P85 compound assign'         : "Compound assignment += -= *= /= %= in straight-line and loop bodies.",
        'P86 inc/dec'                 : "Pre/post ++ / -- as statements in straight-line code.",
        'P88 do-while'                : "A do-while is B; while(G) B — the invariant is established AFTER the mandatory first iteration (modelling it as a plain while was unsound).",
        'P88b do-while early-return'  : "A do-while with an in-body early return: the first-iteration exit is checked from the entry state (not the not-yet-established invariant).",
        'P89 field-write'             : "A field write is seen through the same / an aliased reference, and not through a non-aliased one (refutes).",
        'P89 ref-identity'            : "Reference identity (a.is(b) / a===b) ⇒ the two handles' fields coincide; no identity ⇒ they need not (refutes).",
        'P8a eval'                    : "A closed (ground) call to a contract-free pure function is evaluated to a literal in contracts/bodies; a wrong value refutes.",
        'P8a folding'                 : "Closed nonlinear products / folded indices are evaluated and bounds-checked.",
        'P8a unfold'                  : "A non-recursive pure helper is inlined (ternary to ite), a recursive one unfolded under the path constraint.",
        'P9 any'                      : "A bounded existential (range.any / xs.any) proves membership at a valid index.",
        'P9 diagnostics'              : "Diagnostics echo the developer's spelling — .size() vs .length — rather than a normalised form.",
        'P9 native quantifiers'       : "The native GDK every/any (range-exclusive, indices, element-wise) entail an instance.",
        'P9 repro'                    : "A refuted obligation reconstructs a concrete failing call (bounds / division / null argument).",
        'P90 swap'                    : "A parallel swap (a,b)=[b,a] / array swap snapshots the RHS before any write; without a bounds @Requires it flags OOB.",
        'P91 nested'                  : "A loop nested inside another (matrix sum, n*n / n*m double loops) with scalar accumulators.",
        'P93 power'                   : "The ** operator via an axiomatised pow primitive: a literal exponent folds and the doubling recurrence proves for symbolic n (a false value soft-fails).",
        'P93b power axioms'           : "Literal 2 ** k unfolds to its value (and base case 2 ** 0 == 1); a wrong value refutes.",
        'P97 safe-nav non-null'       : "Safe navigation ?. lets a precondition prove a deref; the same under || does not (still flags NPE).",
        'P98 elvis'                   : "The Elvis operator n ?: 5 takes n when truthy else the default; a false claim refutes.",
        'P99 range membership'        : "The in operator over an integer range (i in 1..3, exclusive ..<) gives bounds facts.",
        'PL-assert'                   : "A bare Groovy assert is discharged at compile time: a false constant refutes, one provable from @Requires verifies.",
        'PL-infer'                    : "Loop-invariant inference for a bare counter loop (opt-in VerifyChecker(inferLoops: true)) proves array bounds with no @Invariant.",
        'PL-selfensures'              : "@SelfEnsures derives result == <body> from an expression body, so a self-specifying method is written once (and reads as a @Reducer/combiner equation).",
        'PL-truth'                    : "Groovy truth in @Ensures({ result }): a non-empty String is truthy (verifies), empty is falsy (refutes).",
        'PL0 lattice'                 : "A user-defined security lattice proven well-formed: leq a partial order, join/meet the lub/glb; a non-transitive order refutes.",
        'PL1 infoflow'                : "Information-flow noninterference over static @Label levels: High→Low refutes (leak), Low→Low and High→High verify.",
        'PL1 rg'                      : "Rely/guarantee compatibility lemmas: each rely reflexive/transitive, every guarantee implies every other thread's rely; a non-implying guarantee refutes.",
        'Pvoid induction'             : "A void self-inductive lemma (2 ** n >= 1) proves genuinely; an over-claim (>= 2) is caught at the base case.",
        'Pvoid lemma'                 : "A false void @Ensures (over state or a param) refutes rather than passing vacuously.",
        'README counter'              : "The README Counter without a @Requires refutes at construction.",
        'README examples'             : "Assorted README examples (nested-loop count, two-cursor array copy, set-merge union).",
        'Sorted helper'               : "The Sorted.ascending/strictlyAscending helper yields the sortedness gap fact (a[i] <=/< a[j] for i<j); no sortedness ⇒ the fact refutes.",
        'bitwise'                     : "Bitwise/shift operators: a literal shift is arithmetic (x<<1==x*2, x>>1==x.intdiv(2) for x>=0).",
        'boxed & list'                : "Integer (boxed) scalar postconditions and Integer[] sorted-difference reasoning.",
        'nested static (GROOVY-12066)': "A static nested class's @Invariant is established by its constructor (GROOVY-12066); unestablished refutes.",
        'regression @Ensures'         : "Regression anchors for @Ensures (max verifies, maxBuggy refutes).",
        'regression @Requires'        : "Regression anchors for @Requires (good literal call verifies, bad refutes).",
        'regression loop'             : "A regression anchor for loop verification (countUp).",
        'set algebra'                 : "Int-element set algebra membership: x in (a-b) / (a^b) follows from operand memberships.",
        'sized int[]'                 : "A sized allocation new int[n] is a fresh zero-filled array (length==n, unwritten elements read 0).",
    ]

    static String slug(String s) { s.toLowerCase().replaceAll(/[^a-z0-9]+/, '-').replaceAll(/(^-|-$)/, '') }

    static List<String> annotationsIn(String src) { ANNOS.findAll { src =~ ('@' + it + /\b/) }.sort() }

    /** Outcome from the case's declared spec (CI-proven to match reality), not by re-running the solver. */
    static Map outcomeOf(Map c) {
        if (c.ok == true) return [outcome: 'verifies', diagnostic: null]
        String exp = (c.expect ?: '').toString()
        boolean skip = exp.toLowerCase().contains('skip') || exp.toLowerCase().contains('outside fragment')
        [outcome: skip ? 'skips' : 'refutes', diagnostic: exp ?: null]
    }

    static void main(String[] args) {
        File outDir = new File(args && args[0] && args[0] != '-check' ? args[0] : 'build/harvest')
        boolean checkMode = args.contains('-check')
        File work = checkMode ? File.createTempDir('harvest', '') : outDir
        work.mkdirs()

        def corpus = new StringBuilder()
        def byGroup = new LinkedHashMap<String, List>()
        VerifyHarness.CASES.eachWithIndex { Map c, int i ->
            Map o = outcomeOf(c)
            Map rec = [
                id         : slug((String) c.group) + '/' + slug((String) c.name),
                group      : c.group,
                name       : c.name,
                outcome    : o.outcome,
                annotations: annotationsIn((String) c.src),
                diagnostic : o.diagnostic,
                source     : c.src,
            ]
            corpus.append(JsonOutput.toJson(rec)).append('\n')
            byGroup.computeIfAbsent((String) c.group, { [] }) << rec
        }
        new File(work, 'corpus.jsonl').text = corpus.toString()

        def catalog = byGroup.collect { String g, List recs ->
            [ group           : g,
              description     : GROUP_DESC[g],                       // null ⇒ flagged by the cross-check lint
              examples        : recs.size(),
              verifies        : recs.count { it.outcome == 'verifies' },
              refutes         : recs.count { it.outcome == 'refutes' },
              skips           : recs.count { it.outcome == 'skips' },
              annotations     : recs.collectMany { it.annotations }.unique().sort(),
              canonicalVerify : recs.find { it.outcome == 'verifies' }?.id,
              canonicalRefute : recs.find { it.outcome == 'refutes' }?.id,
            ]
        }.sort { it.group }
        new File(work, 'catalog.json').text = JsonOutput.prettyPrint(JsonOutput.toJson(catalog)) + '\n'

        if (checkMode) {
            // Freshness gate (CI): regenerate to a temp dir, diff against the committed copies, fail on drift.
            boolean drift = false
            ['catalog.json', 'corpus.jsonl'].each { String f ->
                File committed = new File(outDir, f), fresh = new File(work, f)
                if (!committed.exists() || committed.text != fresh.text) {
                    drift = true; println "  STALE: ${outDir}/${f} differs from a fresh harvest — run `./gradlew harvest`"
                }
            }
            work.deleteDir()
            if (drift) System.exit(1)
            println "harvest artifacts are up to date."
            return
        }
        int v = catalog.sum { it.verifies } ?: 0, r = catalog.sum { it.refutes } ?: 0, s = catalog.sum { it.skips } ?: 0
        println "harvested ${VerifyHarness.CASES.size()} cases (${v} verify / ${r} refute / ${s} skip), " +
                "${catalog.size()} capability groups -> ${outDir}/{catalog.json, corpus.jsonl}"
    }
}
