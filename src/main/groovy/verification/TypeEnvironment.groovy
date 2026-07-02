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
package verification

import groovy.transform.CompileStatic
import groovy.transform.MapConstructor
import org.codehaus.groovy.ast.ClassNode

/**
 * The per-method <b>name → type scope</b> the {@link Encoder} translates under: which names are sets /
 * lists / maps (and of what element types), which are enum- or decimal- or FP-sorted scalars, which are
 * tuples, carriers, {@code Function}s, atomics, and so on. {@code VerifyChecker} populates one of these
 * per verification context (from the method's signature and body scan) and hands it to the encoder whole.
 *
 * <p>Historically these travelled as ~17 positional constructor parameters — several of the same type
 * ({@code Map<String, ClassNode>}), so a silently swapped pair type-checked fine — and every new scope
 * fact rippled a signature change through the construction. Now a new fact is one named field here, one
 * assignment in {@code Encoder}'s constructor, and one entry at the build site.
 *
 * <p>All fields are <b>final</b> and default to <b>empty</b> collections (never null); construction is
 * by named arguments via {@code @MapConstructor(noArg = true)}, whose {@code @NamedParam} metadata lets
 * the static compiler check every key and value type at the call site (a misspelled field or wrong-typed
 * value is a compile error, same as the setter route). Finality pins the <i>references</i>, not the
 * contents: the checker may keep enriching a map (e.g. registering a carrier type discovered mid-walk)
 * and a live encoder is intended to see it, exactly as with the old parameter threading.
 */
@CompileStatic
@MapConstructor(noArg = true)
class TypeEnvironment {

    /** Set-typed names → element type (Phase 16/27). */
    final Map<String, ClassNode> setElementTypes = new HashMap<String, ClassNode>()

    /** Map-typed names → {@code [keyType, valueType]} (Phase 17/27). */
    final Map<String, ClassNode[]> mapTypes = new HashMap<String, ClassNode[]>()

    /** List-typed names → element type. */
    final Map<String, ClassNode> listElementTypes = new HashMap<String, ClassNode>()

    /** Scalar names → declared type, for sort dispatch (enum / decimal / boolean / int-like). */
    final Map<String, ClassNode> scalarTypes = new HashMap<String, ClassNode>()

    /** Enum-sorted names → the enum's constant count, for the domain-closure axiom (Phase L0). */
    final Map<String, Integer> enumDomainSizes = new HashMap<String, Integer>()

    /** {@code Map<K, Set<V>>}-typed names → inner set element type (Phase 36). */
    final Map<String, ClassNode> nestedSetValueTypes = new HashMap<String, ClassNode>()

    /** Names known to be lists (list vs array subscript dispatch). */
    final Set<String> listNames = new HashSet<String>()

    /** Object-typed (reference) parameters → declared type, for the nullity oracle. */
    final Map<String, ClassNode> objectParams = new LinkedHashMap<String, ClassNode>()

    /** Names of boolean-sorted locals. */
    final Set<String> booleanLocals = new HashSet<String>()

    /** Names carried in the Real sort — {@code BigDecimal} params/locals (Phase 61). */
    final Set<String> decimalNames = new HashSet<String>()

    /** FP-sorted names → is-double (true) vs is-float (false) (Phase 73/77). */
    final Map<String, Boolean> fpNames = new HashMap<String, Boolean>()

    /** Tuple-typed params AND tuple locals bound to tuple-returning calls → tuple type (Phases 79/113). */
    final Map<String, ClassNode> tupleParams = new LinkedHashMap<String, ClassNode>()

    /** Equational combiners visible to the method, {@code name/arity} → {@code [formalNames, E]} (Phase 116). */
    final Map<String, Object[]> combiners = new LinkedHashMap<String, Object[]>()

    /** Wrapper/two-case/record carrier types in scope, by simple name (Phases 134/138/150). */
    final Map<String, ClassNode> carrierTypes = new HashMap<String, ClassNode>()

    /** {@code Function}-typed names → declared return type (2nd generic), for {@code f.apply}'s range (Phases 133/173). */
    final Map<String, ClassNode> functionReturnTypes = new HashMap<String, ClassNode>()

    /** Names modelled as atomic int cells — {@code AtomicInteger}/{@code AtomicLong} fields (Phase 162). */
    final Set<String> atomicNames = new HashSet<String>()
}
