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

import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.runtime.InvokerHelper
import org.junit.jupiter.api.Test
import verification.SpecRegistry
import verification.VerifyChecker

import java.lang.reflect.InvocationTargetException
import java.lang.reflect.Method
import java.lang.reflect.Modifier
import java.time.LocalDate
import java.time.LocalTime

import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * Phase 367 — the trusted base, audited against the real JDK. Every shipped skeleton under
 * {@code META-INF/groovy-verify/specs/} is assumed by the verifier and never proved, as are the method-name tables
 * the frame inference reads (a "pure read" writes nothing, a "fresh result" aliases nothing, a "pure static class"
 * writes none of its arguments). A wrong entry is silently unsound wherever it is used. This runs each against the
 * runtime it describes, on edge-heavy inputs: a spec's @Requires selects the inputs, its @ThrowsIf arms are checked
 * in their stated direction (iff, or sufficient), its @Ensures on every normal return, and its frame (@Pure, or
 * @Modifies) against the arguments' and receiver's contents before and after.
 */
class SpecAuditTest {

    static final File SPEC_DIR = new File('src/main/resources/META-INF/groovy-verify/specs')

    // ── inputs ────────────────────────────────────────────────────────────────────────────────────────────────

    static final List<Integer> INTS = [Integer.MIN_VALUE, Integer.MIN_VALUE + 1, -1000, -33, -32, -7, -2, -1, 0, 1, 2, 3,
                                      7, 31, 32, 33, 48, 57, 65, 97, 1000, 0x10FFFF, 0x110000, Integer.MAX_VALUE - 1,
                                      Integer.MAX_VALUE]
    static final List<Long> LONGS = INTS.collect { it as long } + [Long.MIN_VALUE, Long.MIN_VALUE + 1, (long) Integer.MIN_VALUE - 1,
                                     (long) Integer.MAX_VALUE + 1, Long.MAX_VALUE - 1, Long.MAX_VALUE]
    static final List<Character> CHARS = ('09azAZ' + '@[`{/: éÉßÿİı٠०ǅⅠＡ')
        .toList().collect { it as char }
    static final List<String> STRINGS = [null, '', 'a', 'abc', 'aXa', '-12', '0', '2147483648', '9223372036854775808', 'x1', ' 7']
    static final List<Object> OBJECTS = [null, 0, 1, 2, 1L, 'a', 'b']
    static final List<List> LISTS = [[], [1], [1, 2, 3], [3, 1, 2], [2, 2, 1], [1, 1L, 2], [1L], [-5, 0, 5], ['a', 'b']]
    static final List<int[]> INT_ARRAYS = [[] as int[], [1] as int[], [1, 2, 3] as int[], [1, 1, 2] as int[],
                                          [3, 1, 2] as int[], [-3, 0, 4] as int[]]

    static List<Object> values(ClassNode t) {
        if (t.isArray()) return t.componentType.nameWithoutPackage == 'int' ? INT_ARRAYS.collect { it.clone() } : null
        String elem = t.genericsTypes ? t.genericsTypes[0].type.nameWithoutPackage : null
        switch (t.nameWithoutPackage) {
            case 'int': return INTS
            case 'Integer': return INTS + [null]
            case 'long': return LONGS
            case 'Long': return LONGS + [null]
            case 'char': return CHARS
            case 'boolean': return [true, false]
            case 'String': return STRINGS
            case 'Object': return OBJECTS
            case 'List': case 'Collection':
                // a formal with a type argument is a claim over exactly those elements (Phase 367)
                if (elem == 'Integer') return LISTS.findAll { it.every { e -> e instanceof Integer } }.collect { new ArrayList(it) }
                if (elem == 'Long') return LISTS.collect { new ArrayList(it.findAll { e -> e instanceof Number }.collect { e -> e as long }) }
                return LISTS.collect { new ArrayList(it) }
            default: return null
        }
    }

    /** Inputs a signature's own types can't describe: the units library's (Number, Unit) behind an (Object, Object) skeleton. */
    static List<List> overrideInputs(String fqn, String name) {
        if (fqn == 'tech.units.indriya.quantity.Quantities' && name == 'getQuantity') {
            def units = Class.forName('tech.units.indriya.unit.Units')
            return [[1, 0, -3, 0.5G, 2.5d, null], [units.METRE, units.SECOND, units.KILOGRAM]]
        }
        null
    }

    static List<Class> overrideSignature(String fqn, String name) {
        fqn == 'tech.units.indriya.quantity.Quantities' && name == 'getQuantity' ? [Number, Class.forName('javax.measure.Unit')] : null
    }

    /** A value as a report shows it: its type where Groovy's own rendering would hide it (`1L`, `'a'`, `0.5G`). */
    static String show(Object v) {
        if (v instanceof Long) return "${v}L"
        if (v instanceof Character) return "'${v}' (\\u${String.format('%04x', (int) (char) v)})"
        if (v instanceof BigDecimal) return "${v}G"
        if (v instanceof List) return '[' + v.collect { show(it) }.join(', ') + ']'
        if (v?.getClass()?.isArray()) return Arrays.toString(v)
        InvokerHelper.inspect(v)
    }

    static List<Object> receivers(String fqn) {
        switch (fqn) {
            case 'java.lang.String': return ['', 'a', 'abc', 'hello world', 'aXa', '😀x']
            case 'java.time.LocalDate': return [LocalDate.of(2024, 1, 1), LocalDate.of(2024, 12, 31), LocalDate.of(2023, 2, 28),
                                                LocalDate.of(2024, 2, 29), LocalDate.MIN, LocalDate.MAX]
            case 'java.time.LocalTime': return [LocalTime.MIN, LocalTime.MAX, LocalTime.NOON, LocalTime.of(23, 59, 59)]
            case 'java.util.List': return LISTS.collect { new ArrayList(it) } + [[null, 1], List.of(1, 2)]
            case 'javax.measure.Quantity':
                def units = Class.forName('tech.units.indriya.unit.Units')
                def qs = Class.forName('tech.units.indriya.quantity.Quantities')
                return [qs.getQuantity(1, units.METRE), qs.getQuantity(0.5G, units.SECOND), qs.getQuantity(-3, units.KILOGRAM)]
            default: return null
        }
    }

    static Object snapshot(Object v) {
        if (v instanceof int[]) return ((int[]) v).clone()
        if (v instanceof Object[]) return ((Object[]) v).clone()
        if (v instanceof char[]) return ((char[]) v).clone()
        if (v instanceof byte[]) return ((byte[]) v).clone()
        if (v instanceof List) return new ArrayList((List) v)
        if (v instanceof Set) return new LinkedHashSet((Set) v)
        if (v instanceof Map) return new LinkedHashMap((Map) v)
        if (v instanceof StringBuilder) return v.toString()
        v
    }

    static boolean same(Object before, Object after) {
        if (after instanceof StringBuilder) return before == after.toString()
        if (before instanceof List && after instanceof List) return before == after   // element-wise, Groovy equality
        before == after || (before?.getClass()?.isArray() && after?.getClass()?.isArray() && Arrays.deepEquals([before] as Object[], [after] as Object[]))
    }

    // ── contract evaluation ───────────────────────────────────────────────────────────────────────────────────

    /** A contract's free names: the formals, `result`, `old` — and, for an instance spec, the receiver's own members. */
    static class Env extends GroovyObjectSupport {
        Map<String, Object> vars
        Object self
        Object getProperty(String n) {
            if (vars.containsKey(n)) return vars[n]
            if (self != null) return InvokerHelper.getProperty(self, n)
            throw new MissingPropertyException(n, Env)
        }
        Object invokeMethod(String n, Object args) {
            if (self != null) return InvokerHelper.invokeMethod(self, n, args)
            throw new MissingMethodException(n, Env, args as Object[])
        }
    }

    static final GroovyShell SHELL = new GroovyShell()
    static final Map<String, Closure> COMPILED = [:]

    static boolean holds(String text, Map<String, Object> vars, Object self) {
        Closure c = COMPILED.computeIfAbsent(text) { String t -> (Closure) SHELL.evaluate("return { -> ${t} }") }
        Closure k = (Closure) c.clone()
        k.delegate = new Env(vars: vars, self: self)
        k.resolveStrategy = Closure.DELEGATE_FIRST
        k.call() as boolean
    }

    static String contractText(MethodNode m, String kind) {
        AnnotationNode cs = m.annotations.find { it.classNode.nameWithoutPackage == 'ContractSource' }
        Object v = cs?.getMember(kind)
        v instanceof ConstantExpression && ((ConstantExpression) v).value ? (String) ((ConstantExpression) v).value : null
    }

    /** The @ThrowsIf arms as [text, exhaustive, exception], the condition sliced from the skeleton's own source. */
    static List<Map> throwsArms(MethodNode m, List<String> lines) {
        m.annotations.findAll { it.classNode.nameWithoutPackage == 'ThrowsIf' }.collect { AnnotationNode an ->
            ClosureExpression ce = (ClosureExpression) an.getMember('value')
            Object ex = an.getMember('exhaustive')
            boolean exhaustive = !(ex instanceof ConstantExpression && ((ConstantExpression) ex).value == false)
            String exc = an.getMember('exception').text.replaceFirst(/^.*\./, '')
            [text: slice(lines, ce).trim().replaceFirst(/^\{/, '').replaceFirst(/\}$/, ''), exhaustive: exhaustive, exception: exc]
        }
    }

    static String slice(List<String> lines, ClosureExpression ce) {
        if (ce.lineNumber == ce.lastLineNumber) return lines[ce.lineNumber - 1].substring(ce.columnNumber - 1, ce.lastColumnNumber - 1)
        StringBuilder sb = new StringBuilder(lines[ce.lineNumber - 1].substring(ce.columnNumber - 1))
        for (int i = ce.lineNumber; i < ce.lastLineNumber - 1; i++) sb.append('\n').append(lines[i])
        sb.append('\n').append(lines[ce.lastLineNumber - 1].substring(0, ce.lastColumnNumber - 1))
        sb.toString()
    }

    static Set<String> frameNames(MethodNode m) {
        String t = contractText(m, 'modifies')
        if (t == null) return null
        t.replaceAll(/[\[\]\s]/, '').split(',').findAll().collect { it.replaceFirst(/^this\./, '') } as Set
    }

    static Class<?> javaType(ClassNode t) {
        if (t.isArray()) return java.lang.reflect.Array.newInstance(javaType(t.componentType), 0).getClass()
        switch (t.nameWithoutPackage) {
            case 'int': return int
            case 'long': return long
            case 'char': return char
            case 'boolean': return boolean
            case 'double': return double
            case 'String': return String
            case 'Object': return Object
            case 'List': return List
            case 'Collection': return Collection
            case 'Integer': return Integer
            case 'Long': return Long
            default:
                for (String pkg : ['', 'java.lang.', 'java.util.']) {
                    try { return Class.forName(t.name.contains('.') ? t.name : pkg + t.name) } catch (ClassNotFoundException ignored) { }
                }
                return Object
        }
    }

    static List<List> product(List<List> domains, int cap) {
        List<List> out = [[]]
        for (List d : domains) {
            List<List> next = []
            for (List p : out) for (Object v : d) { next << (p + [v]); if (next.size() >= cap) break }
            out = next
        }
        out
    }

    // ── 1. the shipped skeletons ──────────────────────────────────────────────────────────────────────────────

    @Test
    void everyShippedSpecHoldsOnTheRuntimeItDescribes() {
        List<String> failures = []
        int methods = 0, runs = 0
        SPEC_DIR.listFiles().findAll { it.name.endsWith('.groovy') }.sort { it.name }.each { File f ->
            String fqn = f.name - '.groovy'
            Class<?> cls
            try { cls = Class.forName(fqn) } catch (ClassNotFoundException e) { failures << "${fqn}: class not on the classpath"; return }
            String text = f.text
            List<String> lines = text.readLines()
            ClassNode cn = SpecRegistry.parseForLint(text, fqn)
            assert cn != null : "${fqn}: the skeleton doesn't parse"
            for (MethodNode m : cn.methods) {
                if (m.name.startsWith('$') || m.name == '<clinit>') continue
                methods++
                Method jm
                List<Class> skTypes = m.parameters.collect { javaType(it.type) }
                try {
                    jm = cls.getMethod(m.name, skTypes as Class[])
                } catch (NoSuchMethodException e) {
                    jm = null
                }
                if (jm == null && overrideSignature(fqn, m.name) != null) jm = cls.getMethod(m.name, overrideSignature(fqn, m.name) as Class[])
                if (jm == null) {
                    // the runtime method a skeleton's (narrower, or Object-widened) formals describe: the one of that
                    // name and arity, unique among those the skeleton's types fit (or alone of its arity)
                    List<Method> cands = cls.methods.findAll { it.name == m.name && it.parameterCount == m.parameters.length }
                    List<Method> fit = cands.findAll { c -> (0..<skTypes.size()).every { i -> c.parameterTypes[i].isAssignableFrom(boxed(skTypes[i])) || c.parameterTypes[i] == skTypes[i] } }
                    jm = fit.size() == 1 ? fit[0] : cands.size() == 1 ? cands[0] : null
                    if (jm == null) { failures << "${fqn}#${m.name}: no runtime method the skeleton's signature names"; continue }
                }
                boolean isStatic = Modifier.isStatic(jm.modifiers)
                if (isStatic != m.isStatic()) failures << "${fqn}#${m.name}: the skeleton's static-ness differs from the runtime's"
                List<List> domains = overrideInputs(fqn, m.name) ?: m.parameters.collect { values(it.type) }
                if (domains.any { it == null }) { failures << "${fqn}#${m.name}: no input generator for ${m.parameters*.type*.name}"; continue }
                List<Object> selves = isStatic ? [null] : receivers(fqn)
                if (selves == null) { failures << "${fqn}#${m.name}: no receiver generator"; continue }
                String req = contractText(m, 'requires'), ens = contractText(m, 'ensures')
                List<Map> arms = throwsArms(m, lines)
                Set<String> frame = SpecRegistry.isPure(m) ? ([] as Set) : frameNames(m)
                Set<String> methodFailures = new LinkedHashSet<String>()
                for (Object self0 : selves) for (List args0 : product(domains, 4000)) {
                    List args = args0.collect { snapshot(it) }   // a fresh copy per run: the callee may write it
                    Object self = snapshot(self0)
                    Map<String, Object> pre = [:]
                    m.parameters.eachWithIndex { p, i -> pre[p.name] = args[i] }
                    String at = "${fqn}#${m.name}(${args0.collect { show(it) }.join(', ')})" + (self != null ? " on ${show(self)}" : '')
                    try {
                        if (req != null && !holds(req, pre, self)) continue
                    } catch (Throwable ignored) { continue }   // a precondition that can't be evaluated selects nothing
                    runs++
                    Map<String, Object> old = pre.collectEntries { k, v -> [k, snapshot(v)] }
                    Object oldSelf = snapshot(self)
                    Map<Map, Boolean> armHeld = arms.collectEntries { a ->
                        boolean h
                        try { h = holds((String) a.text, pre, self) } catch (Throwable e) { h = false }
                        [a, h]
                    }
                    Object result = null
                    Throwable thrown = null
                    try {
                        result = jm.invoke(self, args as Object[])
                    } catch (InvocationTargetException e) {
                        thrown = e.cause
                    } catch (IllegalArgumentException e) {
                        runs--; continue   // an input the runtime signature doesn't take (the Object-widened skeleton)
                    }
                    for (Map a : arms) {
                        boolean isIt = thrown != null && (thrown.class.simpleName == a.exception ||
                            ([thrown.class] + (thrown.class.superclass ? ancestors(thrown.class) : [])).any { it.simpleName == a.exception })
                        if (armHeld[a] && !isIt) methodFailures << "@ThrowsIf { ${a.text} } held but ${a.exception} wasn't thrown: ${at}" +
                            (thrown ? " (threw ${thrown.class.simpleName})" : " (returned ${InvokerHelper.inspect(result)})")
                        if (a.exhaustive && !armHeld[a] && isIt) methodFailures << "@ThrowsIf { ${a.text} } is exhaustive, but ${a.exception} was thrown with it false: ${at}"
                    }
                    if (thrown == null && ens != null) {
                        Map<String, Object> post = new LinkedHashMap<String, Object>(pre)
                        post.result = result
                        post.old = old
                        boolean ok
                        try { ok = holds(ens, post, self) } catch (Throwable e) { ok = false }
                        if (!ok) methodFailures << "@Ensures { ${ens} } is false: ${at} returned ${show(result)}"
                    }
                    if (frame != null) {
                        m.parameters.eachWithIndex { p, i ->
                            if (!frame.contains(p.name) && !same(old[p.name], args[i])) methodFailures << "the frame omits '${p.name}', which ${at} changed"
                            // Phase 229 — a framed collection keeps its size (callers rely on it)
                            if (frame.contains(p.name) && old[p.name] instanceof Collection && ((Collection) old[p.name]).size() != ((Collection) args[i]).size()) {
                                methodFailures << "'${p.name}' changed size, which a framed collection's caller assumes it doesn't: ${at}"
                            }
                        }
                        if (self != null && !same(oldSelf, self)) methodFailures << "the frame omits the receiver, which ${at} changed"
                    }
                }
                failures.addAll(methodFailures.take(3))
            }
        }
        println "Phase 367 spec audit: ${methods} methods, ${runs} runs, ${failures.size()} failures"
        assertTrue(failures.isEmpty(), 'The shipped specs disagree with the runtime:\n  ' + failures.join('\n  '))
    }

    static Class boxed(Class c) {
        [(int): Integer, (long): Long, (char): Character, (boolean): Boolean, (double): Double].get(c) ?: c
    }

    static List<Class> ancestors(Class c) {
        List<Class> out = []
        for (Class k = c.superclass; k != null; k = k.superclass) out << k
        out
    }

    // ── 2. the method-name tables ─────────────────────────────────────────────────────────────────────────────

    static List<Object> sampleReceivers() {
        [new ArrayList([3, 1, 2]), new LinkedList([3, 1, 2]), new LinkedHashSet([3, 1, 2]), new TreeSet([3, 1, 2]),
         new LinkedHashMap([b: 2, a: 1]), new TreeMap([b: 2, a: 1]), 'cab', [3, 1, 2] as int[], [3, 1, 2] as Integer[],
         new StringBuilder('cab'), Optional.of(3), 5, 5L, 2.5G, 7G, 'a' as char, [1, [2, 3]], new ArrayDeque([3, 1, 2]),
         [3, 1, 2].iterator()]
    }

    static List<List> sampleArgs() {
        [[], [0], [1], [2], [-1], ['a'], [[1]], [[1, 2] as Set], [{ it }], [{ a, b -> a }], [{ a, b -> a <=> b } as Comparator],
         [0, 1], [1, 2], [0, 0], [[], { it }], [new ArrayList(), { it }], [new LinkedHashMap(), { [it, it] }], [new Integer[3]],
         [1, { it }], [true], [false], [String], [List]]
    }

    /** Names on the read lists whose MUTATING overload the inference is known to tell apart (Phase 365). */
    static final Set<String> READ_EXEMPT = ['collect', 'collectEntries', 'collectMany', 'collectNested', 'toArray'] as Set

    @Test
    void readNamesWriteNothing() {
        Set<String> reads = new TreeSet<String>(VerifyChecker.LOOP_PURE_READS + VerifyChecker.INFER_PURE_READS)
        List<String> failures = []
        for (String name : reads) {
            for (Object r0 : sampleReceivers()) for (List a0 : sampleArgs()) {
                Object r = r0 instanceof Iterator ? [3, 1, 2].iterator() : snapshot(r0)
                if (r0 instanceof StringBuilder) r = new StringBuilder(r0.toString())
                List args = a0.collect { it instanceof Collection || it?.getClass()?.isArray() ? snapshot(it) : it }
                if (READ_EXEMPT.contains(name) && args.any { it instanceof Collection || it instanceof Map || it?.getClass()?.isArray() }) continue
                if (VerifyChecker.WRITING_ARITY.get(name) == args.size()) continue   // the writing overload, which the inference excludes
                Object rBefore = r instanceof Iterator ? null : snapshot(r)
                List aBefore = args.collect { snapshot(it) }
                try {
                    Object out = InvokerHelper.invokeMethod(r, name, args as Object[])
                    if (out instanceof Iterator || out instanceof java.util.stream.BaseStream) continue
                } catch (Throwable ignored) {
                    continue   // no such overload, or it rejected the input: either way, nothing ran to write
                }
                String at = "${r0.getClass().simpleName}.${name}(${a0.collect { it instanceof Closure ? '{…}' : InvokerHelper.inspect(it) }.join(', ')})"
                if (r instanceof Iterator) {
                    // an iterator's read advances it; the inference reads `it.next()` as a receiver write anyway
                } else if (!same(rBefore, r)) failures << "${at} changed its receiver to ${InvokerHelper.inspect(r)}"
                args.eachWithIndex { a, i -> if (!same(aBefore[i], a)) failures << "${at} changed its argument ${i} to ${InvokerHelper.inspect(a)}" }
            }
        }
        println "Phase 367 read-name audit: ${reads.size()} names, ${failures.size()} failures"
        assertTrue(failures.isEmpty(), 'Names on the pure-read lists that write:\n  ' + failures.unique().take(40).join('\n  '))
    }

    @Test
    void freshResultsShareNothing() {
        List<String> failures = []
        for (String name : new TreeSet<String>(VerifyChecker.FRESH_RESULT_METHODS)) {
            for (Object r0 : sampleReceivers()) for (List a0 : sampleArgs()) {
                if (r0 instanceof Iterator) continue
                Object r = r0 instanceof StringBuilder ? new StringBuilder(r0.toString()) : snapshot(r0)
                List args = a0.collect { it instanceof Collection || it?.getClass()?.isArray() ? snapshot(it) : it }
                // the collector overloads return the collector they're handed: the alias analysis excludes them
                if (name in READ_EXEMPT && args.any { it instanceof Collection || it instanceof Map || it?.getClass()?.isArray() }) continue
                Object out
                try { out = InvokerHelper.invokeMethod(r, name, args as Object[]) } catch (Throwable ignored) { continue }
                String at = "${r0.getClass().simpleName}.${name}(${a0.collect { it instanceof Closure ? '{…}' : InvokerHelper.inspect(it) }.join(', ')})"
                if (out == null || !(out instanceof Collection || out instanceof Map || out.getClass().isArray() || out instanceof StringBuilder)) continue
                if (out.is(r) || args.any { out.is(it) }) { failures << "${at} returned its receiver or an argument itself"; continue }
                // a view: writing the result writes the receiver
                Object rBefore = snapshot(r)
                try {
                    if (out instanceof List && !((List) out).isEmpty()) ((List) out).set(0, 99)
                    else if (out instanceof Map && !((Map) out).isEmpty()) ((Map) out).put(((Map) out).keySet().first(), 99)
                    else if (out instanceof int[] && ((int[]) out).length > 0) ((int[]) out)[0] = 99
                    else if (out instanceof Object[] && ((Object[]) out).length > 0) ((Object[]) out)[0] = 99
                    else if (out instanceof Collection) ((Collection) out).clear()
                } catch (Throwable ignored) {
                    continue   // an unmodifiable result can't be written through
                }
                if (!same(rBefore, r)) failures << "${at} returned a view: writing it changed the receiver"
            }
        }
        println "Phase 367 fresh-result audit: ${failures.size()} failures"
        assertTrue(failures.isEmpty(), 'Fresh-result names that share state:\n  ' + failures.unique().take(40).join('\n  '))
    }

    // ── 3. the pure static classes ────────────────────────────────────────────────────────────────────────────

    static List<Object> staticSamples(Class<?> t) {
        if (t == int || t == Integer) return [0, 1, 2]
        if (t == long || t == Long) return [0L, 1L]
        if (t == char || t == Character) return ['a' as char]
        if (t == boolean || t == Boolean) return [true]
        if (t == double || t == Double) return [0.5d]
        if (t == float || t == Float) return [0.5f]
        if (t == short || t == Short) return [1 as short]
        if (t == byte || t == Byte) return [1 as byte]
        if (t == String || t == CharSequence) return ['abc']
        if (t == char[]) return [['a', 'b', 'c', 'd'] as char[]]
        if (t == int[]) return [[3, 1, 2, 0] as int[]]
        if (t == long[]) return [[3L, 1L, 2L, 0L] as long[]]
        if (t == byte[]) return [[3, 1, 2, 0] as byte[]]
        if (t == Object[]) return [['x', 'y'] as Object[]]
        if (t == String[]) return [['x', 'y'] as String[]]
        if (t == CharSequence[]) return [['x', 'y'] as CharSequence[]]
        if (t == Object) return ['x']
        if (t == Iterable || t == Collection || t == List) return [new ArrayList(['x', 'y'])]
        if (t == Map) return [new LinkedHashMap([a: 'b'])]
        if (t == StringBuilder || t == StringBuffer || t == Appendable) return [new StringBuilder('ab')]
        null
    }

    static boolean mutableValue(Object v) {
        v != null && (v.getClass().isArray() || v instanceof Collection || v instanceof Map || v instanceof Appendable)
    }

    @Test
    void pureStaticClassesWriteNoArgument() {
        List<String> failures = []
        Set<String> classes = new TreeSet<String>(VerifyChecker.PURE_STATIC_CLASSES + VerifyChecker.INFER_PURE_STATIC_CLASSES)
        for (String fqn : classes) {
            Class<?> cls
            try { cls = Class.forName(fqn) } catch (Throwable ignored) { continue }   // a bare simple-name alias
            for (Method jm : cls.methods) {
                if (!Modifier.isStatic(jm.modifiers) || jm.isSynthetic()) continue
                List<List> domains = jm.parameterTypes.collect { staticSamples(it) }
                if (domains.any { it == null }) continue
                if (!domains.any { List d -> d.any { mutableValue(it) } }) continue   // nothing mutable to write (not flatten: it opens arrays)
                for (List a0 : product(domains, 16)) {
                    List args = a0.collect { mutableValue(it) ? (it instanceof StringBuilder ? new StringBuilder(it.toString()) : snapshot(it)) : it }
                    List before = args.collect { snapshot(it) }
                    try { jm.invoke(null, args as Object[]) } catch (Throwable ignored) { }
                    args.eachWithIndex { a, i ->
                        if (mutableValue(a) && !same(before[i], a) && !VerifyChecker.STATIC_ARG_WRITERS.contains(fqn + '#' + jm.name)) {
                            failures << "${cls.simpleName}.${jm.name}(${jm.parameterTypes*.simpleName.join(', ')}) writes its argument ${i}"
                        }
                    }
                }
            }
        }
        println "Phase 367 pure-static audit: ${classes.size()} classes, ${failures.size()} failures"
        assertTrue(failures.isEmpty(), 'Pure static classes whose methods write an argument:\n  ' + failures.unique().join('\n  '))
    }

    // ── 5. Phase 370 — the calls whose throw is their purpose ────────────────────────────────────────────────────

    /** Each exempt name is a shipped skeleton with @ThrowsIf arms: a renamed or dropped spec can't leave an entry that
     *  quietly exempts some other call. */
    @Test
    void throwingGuardsNameSpecsThatThrow() {
        List<String> failures = []
        for (String key : new TreeSet<String>(VerifyChecker.THROWING_GUARDS)) {
            String fqn = key.substring(0, key.indexOf('#')), name = key.substring(key.indexOf('#') + 1)
            File f = new File(SPEC_DIR, fqn + '.groovy')
            ClassNode cn = f.exists() ? SpecRegistry.parseForLint(f.text, fqn) : null
            List<MethodNode> ms = cn == null ? [] : cn.methods.findAll { it.name == name }
            if (ms.isEmpty()) failures << "${key}: no shipped skeleton"
            else if (ms.every { SpecRegistry.throwsIfArms(it).isEmpty() }) failures << "${key}: no @ThrowsIf arm"
        }
        assertTrue(failures.isEmpty(), 'THROWING_GUARDS entries that exempt nothing real:\n  ' + failures.join('\n  '))
    }
}
