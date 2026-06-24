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
import org.codehaus.groovy.control.MultipleCompilationErrorsException

import java.lang.reflect.Method
import java.lang.reflect.Modifier
import java.lang.reflect.ParameterizedType

/**
 * The <b>runtime rung</b> (Slice 1 — Tier A): a differential soundness oracle.
 *
 * <p>groovy-verify's central claim is "sound within the fragment". groovy.contracts annotations are <i>also</i>
 * runtime assertions, so we recompile each {@code ok:true} case with the VerifyChecker extension stripped but
 * groovy-contracts live, run the method over an input grid, and let the contract check itself. A
 * {@code PreconditionViolation} means the input was out of domain (discard); any other contract violation or a
 * raw safety exception under an in-domain input is a divergence between proof and runtime.
 *
 * <p>The first run taught us the divergences are <b>not all verifier faults</b> — they fall into crisp
 * categories, several of which are groovy-contracts' own runtime quirks or test-harness limits, not unsoundness.
 * So this rung <i>categorises</i> rather than blindly fails: it hard-fails only on an <b>unexplained postcondition
 * refutation</b> (the real soundness signal), and reports every other category for triage.  ./gradlew runtimeRung
 */
class RuntimeRung {

    static final int MAX_COMBOS = 256

    /** Cases outside Slice-1 scope: their contract isn't a grid-executable runtime assertion (census Tier C). */
    static boolean tierC(String src) {
        src =~ /javax\.measure|tech\.units|systems\.uom|\bQuantity\b|\brecord\s/ ||   // units / records
        src =~ /\basync\b|\bawait\b|Awaitable|@Rely|@Guarantee|@UnderRely/ ||         // concurrency
        src =~ /@Label|Declassify\.to|\bLabel\(/ ||                                    // info-flow (not a runtime contract)
        src =~ /import\s+verification\.(Requires|Ensures|Decreases)\b/ ||             // String-form contracts: verify-only, no groovy-contracts runtime arm to cross-validate against
        src =~ /@Monadic|@Reducer|@Associative|java\.util\.function|\.apply\(/        // abstract-carrier laws
    }

    /** Drop the VerifyChecker @TypeChecked extension — compile verifier-off, groovy-contracts still fires. */
    static String stripVerifier(String src) {
        src.replace("(extensions = 'verification.VerifyChecker(inferLoops: true)')", '')
           .replace("(extensions = 'verification.VerifyChecker')", '')
           .replaceAll(/,?\s*'verification\.VerifyChecker(\(inferLoops: true\))?'/, '')
    }

    // ---- input grids by type (no null: a typed reference param is assumed non-null by the verifier) ----------
    static List ints  = [0, 1, 2, 3, 5, -1, -2, 10]
    static List longs = [0L, 1L, 2L, 5L, -1L]
    static List makeIntArr() { [new int[0], [0] as int[], [1, 2, 3] as int[], [3, 1, 2] as int[], [-1, 0, 5] as int[]] }
    static List makeIntList() { [[], [0], [1, 2, 3], [3, 1, 2], [-1, 0, 5]] }
    static List makeIntSet() { [[] as Set, [1] as Set, [0, 1, 2] as Set] }
    // Map<Integer,Integer> family — keys overlap the int grid (0,1,2,3,5) so `m.containsKey(k)` lands both ways.
    static List makeIntMap() { [[:], [0: 0], [1: 2, 3: 4], [0: 1, 2: 3, 5: 7], [1: 1, 2: 2]] }

    static List valuesFor(Class t, java.lang.reflect.Type generic) {
        if (t == int || t == Integer) return new ArrayList(ints)
        if (t == long || t == Long) return new ArrayList(longs)
        if (t == boolean || t == Boolean) return [true, false]
        if (t == double || t == Double) return [0.0d, 1.0d, 2.5d, -1.5d]
        if (t == float || t == Float) return [0.0f, 1.0f, -1.5f]
        if (t == BigDecimal) return [0, 1, 2, -1].collect { it as BigDecimal } + [new BigDecimal('2.5')]
        if (t == char || t == Character) return [('a' as char), ('z' as char), ('A' as char), (' ' as char), ('0' as char)]
        if (t == String) return ['', 'a', 'abc', 'Hello']
        if (t == int[]) return makeIntArr()
        if (List.isAssignableFrom(t)) return (elementIsInteger(generic) || rawOrObject(generic)) ? makeIntList() : null
        if (Set.isAssignableFrom(t)) return (elementIsInteger(generic) || rawOrObject(generic)) ? makeIntSet() : null
        if (Map.isAssignableFrom(t)) return (mapIsIntInt(generic) || rawOrObject(generic)) ? makeIntMap() : null   // Map<Integer,Integer> only; String/Enum-keyed & nested deferred
        return null   // Tuple, enum, custom class, double[] … — deferred past Slice 1
    }
    static boolean elementIsInteger(java.lang.reflect.Type g) {
        (g instanceof ParameterizedType) && ((ParameterizedType) g).actualTypeArguments.toList() == [Integer]
    }
    static boolean mapIsIntInt(java.lang.reflect.Type g) {
        (g instanceof ParameterizedType) && ((ParameterizedType) g).actualTypeArguments.toList() == [Integer, Integer]
    }
    static boolean rawOrObject(java.lang.reflect.Type g) { !(g instanceof ParameterizedType) }

    // ---- respect non-runtime-enforced precondition annotations (Jakarta / @NonNull) by construction ----------
    static List filterByAnnotations(List values, java.lang.annotation.Annotation[] anns) {
        Set<String> names = anns.collect { it.annotationType().simpleName } as Set
        List out = new ArrayList(values)
        if (['NonNull', 'NotNull', 'Nonnull', 'NotEmpty'].any { names.contains(it) }) out = out.findAll { it != null }
        if (names.contains('NotEmpty')) out = out.findAll { sizeOf(it) > 0 }
        if (names.contains('Positive')) out = out.findAll { it instanceof Number && (it as long) > 0 }
        if (names.contains('PositiveOrZero')) out = out.findAll { it instanceof Number && (it as long) >= 0 }
        if (names.contains('Negative')) out = out.findAll { it instanceof Number && (it as long) < 0 }
        if (names.contains('NegativeOrZero')) out = out.findAll { it instanceof Number && (it as long) <= 0 }
        anns.each { a ->
            String n = a.annotationType().simpleName
            if (n == 'Min') { long v = attr(a, 'value') as long; out = out.findAll { it instanceof Number && (it as long) >= v } }
            if (n == 'Max') { long v = attr(a, 'value') as long; out = out.findAll { it instanceof Number && (it as long) <= v } }
            if (n == 'Size') { long mn = attr(a, 'min') as long, mx = attr(a, 'max') as long; out = out.findAll { it != null && sizeOf(it) >= mn && sizeOf(it) <= mx } }
        }
        out
    }
    static int sizeOf(v) {
        if (v == null) return -1
        if (v instanceof CharSequence) return v.length()
        if (v.getClass().isArray()) return java.lang.reflect.Array.getLength(v)
        if (v instanceof Collection) return v.size()
        return -1
    }
    static Object attr(java.lang.annotation.Annotation a, String name) {
        try { a.annotationType().getMethod(name).invoke(a) } catch (ignored) { 0L }
    }

    static boolean isPrecondition(Throwable t) {
        for (Throwable c = t; c != null; c = c.cause) if (c.getClass().simpleName == 'PreconditionViolation') return true
        false
    }
    static boolean isContractsViolation(Throwable t) {
        for (Throwable c = t; c != null; c = c.cause) if (c.getClass().name.startsWith('org.apache.groovy.contracts.')) return true
        false
    }

    static List<Method> targetMethods(Class cls) {
        def skip = ['getMetaClass', 'setMetaClass', 'invokeMethod', 'getProperty', 'setProperty', 'main',
                    '$getStaticMetaClass', 'getStaticMetaClass'] as Set
        cls.declaredMethods.findAll { Method m ->
            Modifier.isStatic(m.modifiers) && Modifier.isPublic(m.modifiers) && !m.synthetic && !m.bridge &&
                !m.name.contains('$') && !skip.contains(m.name)
        }
    }

    static Map exercise(Method m, String src) {
        def perParam = []
        boolean ungen = false
        def seeds = seedGrids(src, m)   // #1 — contract-derived in-domain seeds, by param index
        m.parameterTypes.eachWithIndex { Class t, int i ->
            def vals = valuesFor(t, m.genericParameterTypes[i])
            if (vals == null) {
                if (seeds[i]) { perParam << seeds[i]; return }   // ungeneratable type, but the @Requires pins a witness
                ungen = true; return
            }
            def list = filterByAnnotations(vals, m.parameterAnnotations[i])
            perParam << (seeds[i] ? (seeds[i] + list) : list)    // prepend the seed so it's tried within MAX_COMBOS
        }
        if (ungen) return [kind: 'excluded-type', detail: m.parameterTypes.find { valuesFor(it, null) == null }?.simpleName]
        List<List> combos = perParam.isEmpty() ? [[]] : perParam.combinations()
        if (combos.size() > MAX_COMBOS) combos = combos.take(MAX_COMBOS)
        int inDomain = 0
        for (args in combos) {
            try {
                // Fresh map per combo: a mutating `put` must not leak into the next combo's grid value (arrays/
                // lists reuse their objects too, but corroborate relies on in-place mutation for post-state, so we
                // clone only here in `exercise`, and pass the pristine originals to corroborate via argsList).
                m.invoke(null, freshCombo(args)); inDomain++
            } catch (java.lang.reflect.InvocationTargetException ite) {
                Throwable cause = ite.cause ?: ite
                if (isPrecondition(cause)) continue
                return [kind: 'signal', cause: cause, args: render(args), argsList: new ArrayList(args)]
            } catch (Throwable other) {
                return [kind: 'signal', cause: other, args: render(args), argsList: new ArrayList(args)]
            }
        }
        inDomain > 0 ? [kind: 'validated'] : [kind: 'needseed']
    }

    /** Clone mutable map args so a per-combo invocation can't mutate the shared grid value. */
    static Object[] freshCombo(List args) { args.collect { it instanceof Map ? new LinkedHashMap((Map) it) : it } as Object[] }

    // ---- #1: contract-derived seeds (the jqwik-#486 idea, scoped) -----------------------------------------------
    // The fixed grid never lands in-domain for a structural precondition (`s.startsWith("foo")`, `a.length > 5`,
    // `n == -7`, `s in 'A'..'Z'`). Parse the @Requires and synthesise a *witness* input for the simple shapes, so
    // the contract finally runs. SAFETY: a seed is only a candidate — if it's wrong, groovy-contracts throws a
    // PreconditionViolation and it's discarded, exactly like a grid value. A seeder can never manufacture a
    // divergence; the worst case is the case stays `needseed`, as it is today. So this is strictly additive.

    /** Every @Requires closure body in the source, conjoined (loose: not method-anchored — a mismatched seed is
     *  matched by param name+type per method and, if it doesn't fit, is harmlessly discarded). */
    static String allRequires(String src) {
        List<String> parts = []; int from = 0
        while (true) {
            int idx = src.indexOf('@Requires', from); if (idx < 0) break
            int brace = src.indexOf('{', idx); if (brace < 0) break
            parts << braceBody(src, brace).trim(); from = brace + 1
        }
        parts.join(' && ')
    }

    /** Split a predicate into top-level `&&` conjuncts (ignoring `&&` nested in (), {}, []). */
    static List<String> splitConj(String text) {
        List<String> out = []; int d = 0; StringBuilder cur = new StringBuilder()
        for (int i = 0; i < text.length(); i++) {
            char ch = text.charAt(i)
            if (ch == '(' as char || ch == '{' as char || ch == '[' as char) d++
            else if (ch == ')' as char || ch == '}' as char || ch == ']' as char) d--
            if (d == 0 && ch == '&' as char && i + 1 < text.length() && text.charAt(i + 1) == ('&' as char)) {
                String s = cur.toString().trim(); if (s) out << s; cur = new StringBuilder(); i++; continue
            }
            cur.append(ch)
        }
        String last = cur.toString().trim(); if (last) out << last
        out
    }

    static Map<Integer, List> seedGrids(String src, Method m) {
        Map<Integer, List> out = [:]
        String req = allRequires(src); if (!req) return out
        def names = paramNamesFor(src, m.name); if (names == null || names.size() != m.parameterCount) return out
        List<String> conj = splitConj(req)
        names.eachWithIndex { String nm, int i ->
            def seed = seedForParam((String) nm, m.parameterTypes[i], m.genericParameterTypes[i], conj)
            if (seed != null) out[i] = [seed]
        }
        out
    }

    static Object coerceNum(BigDecimal v, Class t) {
        if (t == int || t == Integer) return v.intValue()
        if (t == long || t == Long) return v.longValue()
        if (t == double || t == Double) return v.doubleValue()
        if (t == float || t == Float) return v.floatValue()
        v
    }

    /** A witness value for {@code name} of type {@code t} satisfying the recognised conjuncts, or null. The
     *  {@code generic} type gates element-typed seeds: a {@code List<String>} must NOT be seeded with an Integer
     *  list (that would satisfy a structural `size() > 0` precondition but run with wrong-typed elements). */
    static Object seedForParam(String name, Class t, java.lang.reflect.Type generic, List<String> conj) {
        String q = java.util.regex.Pattern.quote(name)
        // ---- scalar numerics: `name <op> literal` ----
        if (t in [int, Integer, long, Long, double, Double, float, Float, BigDecimal]) {
            for (String c : conj) {
                def mt = (c =~ /^\s*${q}\s*(==|>=|<=|>|<)\s*(-?\d+(?:\.\d+)?)\s*$/)
                if (mt.find()) {
                    BigDecimal k = new BigDecimal(mt.group(2)); String op = mt.group(1)
                    BigDecimal v = op == '>' ? k + 1 : (op == '<' ? k - 1 : k)
                    return coerceNum(v, t)
                }
            }
            return null
        }
        // ---- String ----
        if (t == String) {
            for (String c : conj) {                                            // range: `s in 'A'..'Z'`
                def r = (c =~ /\b${q}\s+in\s+'(.)'\s*\.\.\s*'(.)'/); if (r.find()) return r.group(1)
                def eq = (c =~ /\b${q}\s*==\s*"([^"]*)"/);            if (eq.find()) return eq.group(1)
            }
            String prefix = '', suffix = '', contains = ''; int minLen = 0; Map<Integer, Character> chars = [:]; boolean any = false
            for (String c : conj) {
                def sw = (c =~ /\b${q}\??\.startsWith\(\s*"([^"]*)"/); if (sw.find()) { prefix = sw.group(1); any = true }
                def ew = (c =~ /\b${q}\??\.endsWith\(\s*"([^"]*)"/);   if (ew.find()) { suffix = ew.group(1); any = true }
                def ct = (c =~ /\b${q}\??\.contains\(\s*"([^"]*)"/);   if (ct.find()) { contains = ct.group(1); any = true }
                def ln = (c =~ /\b${q}\??\.length\(\)\s*(==|>=|>|<=|<)\s*(\d+)/)
                if (ln.find()) { int k = ln.group(2) as int; minLen = Math.max(minLen, ln.group(1) == '>' ? k + 1 : k); any = true }
                def ca = (c =~ /\b${q}\??\.charAt\(\s*(\d+)\s*\)\s*==\s*(\d+)/)
                if (ca.find()) { chars[ca.group(1) as int] = (char) (ca.group(2) as int); any = true }
            }
            if (!any) return null
            StringBuilder sb = new StringBuilder(prefix)
            if (contains && sb.indexOf(contains) < 0) sb.append(contains)
            if (suffix && !sb.toString().endsWith(suffix)) sb.append(suffix)
            while (sb.length() < minLen) sb.append('x' as char)
            chars.each { Integer idx, Character ch -> while (sb.length() <= idx) sb.append('x' as char); sb.setCharAt(idx, ch) }
            return sb.toString()
        }
        // ---- int[] / List<Integer>: length + element-pin constraints (Integer-element only — see generic gate) ----
        if (t == int[] || (List.isAssignableFrom(t) && (elementIsInteger(generic) || rawOrObject(generic)))) {
            int minLen = 0; Map<Integer, Integer> elems = [:]; boolean any = false
            for (String c : conj) {
                def ln = (c =~ /\b${q}\.(?:length|size\(\))\s*(==|>=|>|<=|<)\s*(\d+)/)
                if (ln.find()) { int k = ln.group(2) as int; minLen = Math.max(minLen, ln.group(1) == '>' ? k + 1 : k); any = true }
                def el = (c =~ /\b${q}\[\s*(\d+)\s*\]\s*==\s*(-?\d+)/)
                if (el.find()) { elems[el.group(1) as int] = el.group(2) as int; any = true }
            }
            if (!any) return null
            int len = Math.max(minLen, elems.keySet().isEmpty() ? 0 : (elems.keySet().max() + 1))
            if (len == 0) return null
            int[] arr = new int[len]; elems.each { Integer idx, Integer v -> arr[idx] = v }
            return (t == int[]) ? arr : (arr as List)
        }
        null
    }

    static String render(List args) {
        '(' + args.collect { it == null ? 'null' : (it.getClass().isArray() ? (it as List).toString() : it.toString()) }.join(', ') + ')'
    }

    // ---- Slice 2: corroboration — don't trust groovy-contracts' eval; re-check the spec on the real value -----

    /** Known, triaged proof-vs-runtime divergences (group::name → reason). A NEW confirmed one fails the run. */
    static final Map<String, String> KNOWN_DIVERGENCES = [
        // (the matrix-sum [].sum()==null divergence is now caught by the verifier itself — it refuses the bare
        //  `.sum()` empty edge — so it is no longer an ok:true case the rung sees)
        'P expr inc/dec::a[i] = i++ stores old value at old index':
            'eval order (GROOVY-12097): Groovy evaluates the a[i] subscript AFTER the increment; the verifier models the documented JLS left-to-right order — a known Groovy runtime bug, not a verifier flaw',
        'P expr inc/dec::dst[i] = src[++i] (read before pre) snapshots and verifies':
            'eval order (GROOVY-12097): Groovy evaluates the subscript AFTER the pre-increment; the verifier models the JLS left-to-right order — same root cause as a[i]=i++',
    ]

    static boolean isPostOrInvariant(Throwable t) {
        for (Throwable c = t; c != null; c = c.cause) if (c.getClass().simpleName in ['PostconditionViolation', 'ClassInvariantViolation']) return true
        false
    }

    /** For the contracts-off compile: also drop @TypeChecked, else the now-unrewritten contract closures
     *  (which reference `result`) fail static type-checking. Dynamic Groovy leaves them inert. */
    static String contractsOffSrc(String src) { src.replaceAll(/@TypeChecked(\s*\([^)]*\))?/, '') }

    static GroovyClassLoader offLoader() {
        def cfg = new org.codehaus.groovy.control.CompilerConfiguration()
        cfg.disabledGlobalASTTransformations = ['org.apache.groovy.contracts.ast.GContractsASTTransformation',
            'org.apache.groovy.contracts.ast.ClosureExpressionEvaluationASTTransformation',
            'org.apache.groovy.contracts.ast.MethodVariantInheritanceASTTransformation'] as Set
        new GroovyClassLoader(RuntimeRung.classLoader, cfg)
    }

    static String braceBody(String s, int braceIdx) {
        int d = 0
        for (int i = braceIdx; i < s.length(); i++) {
            char c = s.charAt(i)
            if (c == '{' as char) d++
            else if (c == '}' as char) { d--; if (d == 0) return s.substring(braceIdx + 1, i) }
        }
        s.substring(braceIdx + 1)
    }
    static int methodDeclIndex(String src, String method) {
        def m = (src =~ /(?:static\s+)[\w\[\]<>.,?\s]+?\b${java.util.regex.Pattern.quote(method)}\s*\(/)
        m.find() ? m.start() : -1
    }
    static List paramNamesFor(String src, String method) {
        def m = (src =~ /(?:static\s+)[\w\[\]<>.,?\s]+?\b${java.util.regex.Pattern.quote(method)}\s*\(([^)]*)\)/)
        if (!m.find()) return null
        String p = ((String) m.group(1)).trim()
        p ? splitTopLevel(p).collect { it.trim().split(/\s+/)[-1].replaceAll(/\W/, '') } : []
    }

    /** Split a parameter list on top-level commas only — a `Map<Integer, Integer>`'s inner comma must not split it. */
    static List<String> splitTopLevel(String p) {
        List<String> out = []; int depth = 0; StringBuilder cur = new StringBuilder()
        for (int i = 0; i < p.length(); i++) {
            char c = p.charAt(i)
            if (c == '<' as char) depth++
            else if (c == '>' as char) depth--
            if (c == ',' as char && depth == 0) { out << cur.toString(); cur = new StringBuilder() }
            else cur.append(c)
        }
        if (cur.length()) out << cur.toString()
        out
    }
    static String ensuresBodyFor(String src, String method) {
        int mi = methodDeclIndex(src, method); if (mi < 0) return null
        int last = src.substring(0, mi).lastIndexOf('@Ensures')
        if (last < 0) return null
        int brace = src.indexOf('{', last)
        (brace < 0 || brace > mi) ? null : braceBody(src, brace)
    }

    /** verdict: 'confirmed' (verifier proof refuted on the real value), 'gc-quirk' (value satisfies spec —
     *  groovy-contracts mis-evaluated), or 'uncorroborated' (spec not independently evaluable here). */
    static Map corroborate(String src, Method m, List args) {
        def names = paramNamesFor(src, m.name)
        String ens = ensuresBodyFor(src, m.name)
        if (ens == null || ens.contains('old') || names == null || names.size() != args.size())
            return [verdict: 'uncorroborated', why: 'no @Ensures / old-state / param-name mismatch']
        def R
        try {
            def ldr = offLoader(); ldr.parseClass(contractsOffSrc(src), 'Off.groovy')
            def off = ldr.loadedClasses.collect { it.declaredMethods.find { it.name == m.name && it.parameterCount == m.parameterCount } }.find { it }
            if (off == null) return [verdict: 'uncorroborated', why: 'no contracts-off method']
            R = off.invoke(null, args as Object[])
        } catch (Throwable t) { return [verdict: 'uncorroborated', why: 'body threw raw: ' + (t.cause ?: t).class.simpleName] }
        def b = new Binding(); b.setVariable('result', R)
        names.eachWithIndex { n, i -> b.setVariable((String) n, args[i]) }
        try {
            def ok = new GroovyShell(b).evaluate(VerifyHarness.HDR + '\n(' + ens + ')')
            [verdict: ok ? 'gc-quirk' : 'confirmed', value: R]
        } catch (Throwable t) { [verdict: 'uncorroborated', why: 'spec eval threw: ' + (t.cause ?: t).class.simpleName] }
    }

    /** Bucket a divergence: `review` = needs human eyes; `unknown` = genuinely uncategorised (fails the run). */
    static Map category(String src, Throwable cause) {
        def names = []
        for (Throwable c = cause; c != null; c = c.cause) names << c.getClass().simpleName
        def has = { String s -> names.contains(s) }
        boolean incDec = (src =~ /\+\+|--/) && (src =~ /\[/)        // inc/dec used with an array subscript
        if (cause instanceof StackOverflowError || has('StackOverflowError'))
            return [cat: 'helper-depth: uncontracted recursion called out of its domain (harness limit, not a proof)', review: false]
        if (has('MissingPropertyException') || has('MissingMethodException'))
            return [cat: 'verifier-DSL helper not runtime-evaluable (e.g. Sets.boundedBy in a @Requires) — contract cannot be run, not a proof gap', review: false]
        if (has('LoopVariantViolation') || has('LoopInvariantViolation'))
            return [cat: 'gc-loop-check: groovy-contracts runtime @Decreases/@Invariant mechanism (separate from the verifier)', review: false]
        if (incDec)
            return [cat: 'increment-subscript eval order: Groovy evaluates a[i]=++i AFTER the increment, verifier snapshots before — a genuine verifier-vs-Groovy divergence (REVIEW with Paul)', review: true]
        if (has('PostconditionViolation') || has('ClassInvariantViolation')) {
            if (src =~ /\.sum\(\)/)
                return [cat: 'empty-aggregate: Groovy [].sum() is null (not 0) at the empty edge — verifier models it 0; documented Groovy quirk', review: false]
            // groovy-contracts itself mis-evaluates some postconditions (e.g. `max` returns 1,2,5 correctly yet gc
            // reports `result>=a && result>=b` violated): a bare violation is NOT conclusively a verifier bug.
            return [cat: 'POSTCONDITION REFUTED — needs corroboration: groovy-contracts runtime eval is itself imperfect (Slice 2: re-check the value against the spec independently before calling it a verifier bug)', review: true]
        }
        if (has('UnsupportedOperationException'))
            return [cat: 'partial-extremum: a.max()/a.min() on an empty array throws — verifier proves the spec without a non-empty precondition (well-definedness gap)', review: true]
        if (has('ArrayIndexOutOfBoundsException'))
            return [cat: 'array-edge / correlated-input: empty array in a range spec, or independent multi-param grid violated a size relation', review: false]
        return [cat: 'OTHER — uncategorised exception: ' + names.take(2).join(' <- '), review: true, unknown: true]
    }

    static void selfTest() {
        def gcl = new GroovyClassLoader()
        Class st = gcl.parseClass(VerifyHarness.HDR +
            'class ST { @Requires({ x > 0 }) @Ensures({ result == 1 }) static int f(int x) { x } }', 'ST.groovy')
        def f = st.declaredMethods.find { it.name == 'f' }
        boolean pre = false, post = false
        try { f.invoke(null, -1) } catch (e) { pre = isPrecondition(e.cause ?: e) }
        try { f.invoke(null, 2) } catch (e) { post = isContractsViolation(e.cause ?: e) && !isPrecondition(e.cause ?: e) }
        if (!pre || !post) {
            System.err.println "FATAL: groovy-contracts runtime assertions are NOT live (pre=$pre post=$post) — aborting."
            System.exit(2)
        }
    }

    /** Guard the corroboration logic: a wrong body must corroborate 'confirmed', a right one 'gc-quirk'. */
    static void corroborateSelfTest() {
        String wrong = VerifyHarness.HDR + 'class C { @Ensures({ result == x }) static int f(int x) { x + 1 } }'
        String right = VerifyHarness.HDR + 'class C { @Ensures({ result == x }) static int f(int x) { x } }'
        def ldr = offLoader(); ldr.parseClass(contractsOffSrc(wrong), 'CW.groovy')
        def mf = ldr.loadedClasses.collect { it.declaredMethods.find { it.name == 'f' } }.find { it }
        def vWrong = corroborate(wrong, (Method) mf, [2])
        def vRight = corroborate(right, (Method) mf, [2])
        if (vWrong.verdict != 'confirmed' || vRight.verdict != 'gc-quirk') {
            System.err.println "FATAL: corroboration logic broken (wrong=${vWrong.verdict}, right=${vRight.verdict}) — aborting."
            System.exit(2)
        }
    }

    static void main(String[] args) {
        println '── Runtime rung (Slice 2 — Tier A differential soundness oracle, with corroboration) ' + ('─' * 4)
        selfTest()
        corroborateSelfTest()
        println 'self-test OK: contract assertions fire at runtime, and corroboration distinguishes confirmed vs quirk.\n'

        def proven = VerifyHarness.CASES.findAll { it.ok == true }
        int cleanValidated = 0, needseed = 0, exTierC = 0, exCompile = 0, exNoMethod = 0, exType = 0, validatedStrong = 0
        def buckets = new TreeMap<String, List>()   // category -> [ "[group] name · method(args)" ]
        def reviewCats = [] as Set
        boolean anyUnknown = false

        proven.each { Map c ->
            String src = stripVerifier((String) c.src)
            if (tierC(src)) { exTierC++; return }
            // an inline `assert <cond>` is a runtime-active logical check too (Groovy asserts are on by default),
            // so it counts as a postcondition oracle alongside @Ensures / @Invariant.
            boolean strong = src.contains('@Ensures') || src.contains('@Invariant') || (src =~ /\bassert\s/)
            def gcl = new GroovyClassLoader()
            List<Class> classes
            try {
                gcl.parseClass(src, 'Case.groovy')
                classes = gcl.loadedClasses.findAll { !it.name.contains('$') && !it.isInterface() && !it.isAnnotation() }
            } catch (MultipleCompilationErrorsException ignored) { exCompile++; return }
            catch (Throwable ignored) { exCompile++; return }
            def methods = classes.collectMany { targetMethods(it) }
            if (methods.isEmpty()) { exNoMethod++; return }

            boolean anyValidated = false, anySeed = false, anyType = false, signalled = false
            for (Method m : methods) {
                def r = exercise(m, src)
                if (r.kind == 'signal') {
                    Throwable cause = (Throwable) r.cause
                    String label = "[${c.group}] ${c.name} · ${m.name}${r.args}"
                    if (isPostOrInvariant(cause)) {
                        def cor = corroborate(src, m, (List) r.argsList)
                        if (cor.verdict == 'gc-quirk') {           // value satisfies the spec — verifier is correct
                            anyValidated = true
                            buckets.computeIfAbsent('recovered: groovy-contracts mis-evaluated the postcondition, but the real value satisfies the spec — verifier correct (corroborated)', { [] }) << "${label}  → result=${cor.value}"
                            continue
                        }
                        if (cor.verdict == 'confirmed') {
                            String key = "${c.group}::${c.name}".toString()
                            if (KNOWN_DIVERGENCES.containsKey(key)) {     // already triaged — catalogued, not pending review
                                String b = "known divergence (allowlisted): ${KNOWN_DIVERGENCES[key]}".toString()
                                buckets.computeIfAbsent(b, { [] }) << label
                            } else {
                                buckets.computeIfAbsent('CONFIRMED proof-vs-runtime divergence (corroborated, NOT allowlisted) — verifier proved a postcondition that is false on the real value', { [] }) << "${label}  → result=${cor.value}".toString()
                                anyUnknown = true
                            }
                            signalled = true; break
                        }
                        // uncorroborated
                        String b = "postcondition violation, not self-corroborable (${cor.why})".toString()
                        buckets.computeIfAbsent(b, { [] }) << label; reviewCats << b
                        signalled = true; break
                    }
                    def cat = category(src, cause)
                    buckets.computeIfAbsent(cat.cat, { [] }) << label
                    if (cat.review) reviewCats << cat.cat
                    if (cat.unknown) anyUnknown = true
                    signalled = true
                    break
                } else if (r.kind == 'validated') anyValidated = true
                else if (r.kind == 'needseed') anySeed = true
                else if (r.kind == 'excluded-type') anyType = true
            }
            if (signalled) { /* counted in a bucket */ }
            else if (anyValidated) { cleanValidated++; if (strong) validatedStrong++ }
            else if (anySeed) needseed++
            else if (anyType) exType++
        }

        int diverged = 0; buckets.each { k, v -> diverged += v.size() }
        println "PROVEN cases examined         : ${proven.size()}"
        println "  ✓ cleanly cross-validated   : ${cleanValidated}   (${validatedStrong} with an @Ensures/@Invariant/assert postcondition oracle; rest exercise implicit-safety)"
        println "  ~ diverged (categorised)    : ${diverged}"
        println "  · needs seed (Tier B)       : ${needseed}   (grid never satisfied the @Requires precondition)"
        println "  · excluded — Tier C         : ${exTierC}   (units/records, concurrency, info-flow, abstract-carrier laws)"
        println "  · excluded — compile-off    : ${exCompile}   (won't compile without the extension)"
        println "  · excluded — type/no-method : ${exType + exNoMethod}"
        println()
        println "DIVERGENCES by category (proof vs groovy-contracts runtime) — ⚑ = needs human review:"
        buckets.each { cat, list ->
            println "\n  ▶ (${list.size()}) ${reviewCats.contains(cat) ? '⚑ ' : ''}${cat}"
            list.take(4).each { println "        ${it}" }
            if (list.size() > 4) println "        … +${list.size() - 4} more"
        }
        println()
        println "Headline: ${cleanValidated}/${proven.size() - exTierC - exType - exNoMethod - exCompile} runnable proofs cross-validated clean; " +
                "${buckets.values().sum { it.size() } ?: 0} diverged across ${buckets.size()} categories (${reviewCats.size()} need review)."
        if (anyUnknown) {
            println '✗ A NEW corroborated proof-vs-runtime divergence surfaced (not in KNOWN_DIVERGENCES): the verifier ' +
                    'proved a postcondition that is false on the real computed value. Triage, then fix or allowlist.'
            System.exit(1)
        }
        println '✓ No new confirmed divergence. Postcondition violations were corroborated against the real value: ' +
                'groovy-contracts mis-evaluations were recovered (verifier correct), and the known divergences are allowlisted with reasons.'
    }
}
