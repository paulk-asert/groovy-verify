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
import org.codehaus.groovy.control.messages.ExceptionMessage
import org.codehaus.groovy.control.messages.SyntaxErrorMessage
import org.codehaus.groovy.runtime.InvokerHelper
import org.junit.jupiter.api.Test

import java.lang.reflect.InvocationTargetException
import java.lang.reflect.Method

import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * Phase 368 — the encoder's built-in semantics, audited against the runtime. Most of what the verifier assumes about
 * Groovy is not in a skeleton but in the encoder's own translations: `%` and `intdiv` on negatives, overflow, shifts,
 * ranges, Groovy truth, list/array/string methods and their edge cases. Each translation is a claim about the runtime
 * that nothing checked. For every probe expression and every point of an edge-value grid this runs the expression (a
 * plain `@TypeChecked` method, no checker) for its value V, then asks the verifier, pinned to that point by
 * `@Requires`, to prove `result != V`: a proof is the encoder believing a value the runtime doesn't produce — unsound.
 * Its twin `result == V` should prove (a refutation is a disagreement, reported as precision); and where the runtime
 * throws, the verifier must say something about the method.
 */
class EncoderAuditTest {

    // ── the grid ──────────────────────────────────────────────────────────────────────────────────────────────

    static final Map<String, List<Object>> DOMAIN = [
        'int'          : [-7, -2, -1, 0, 1, 2, 3, 7, 31, 32, 33, Integer.MAX_VALUE, Integer.MIN_VALUE],
        'int2'         : [-3, -1, 0, 1, 2, 7, 32],
        'long'         : [-7L, -1L, 0L, 3L, (long) Integer.MAX_VALUE + 1, Long.MAX_VALUE, Long.MIN_VALUE],
        'List<Integer>': [[], [5], [3, -1, 2], [2, 2, 7], [-4, -9]],
        'int[]'        : [[] as int[], [5] as int[], [3, -1, 2] as int[], [2, 2, 7] as int[]],
        'String'       : ['', 'a', 'Ab', 'hello', 'lol'],
        'boolean'      : [true, false],
    ]

    /** [name, params (name → domain key), return type, expression]. */
    static final List<List> PROBES = [
        // integer arithmetic and its wrap
        ['add', [x: 'int', y: 'int2'], 'int', 'x + y'],
        ['sub', [x: 'int', y: 'int2'], 'int', 'x - y'],
        ['mul', [x: 'int', y: 'int2'], 'int', 'x * y'],
        ['neg', [x: 'int'], 'int', '-x'],
        ['inc', [x: 'int'], 'int', 'x + 1'],
        ['rem', [x: 'int', y: 'int2'], 'int', 'x % y'],
        ['mod', [x: 'int', y: 'int2'], 'int', 'x.mod(y)'],
        ['intdiv', [x: 'int', y: 'int2'], 'int', 'x.intdiv(y)'],
        ['divTrunc', [x: 'int', y: 'int2'], 'int', '(x / y) as int'],
        ['javaDiv', [x: 'int', y: 'int2'], 'int', 'Math.floorDiv(x, y)'],
        ['floorMod', [x: 'int', y: 'int2'], 'int', 'Math.floorMod(x, y)'],
        ['absM', [x: 'int'], 'int', 'Math.abs(x)'],
        ['absG', [x: 'int'], 'int', 'x.abs()'],
        ['sq', [x: 'int'], 'long', '(x as long) * x'],
        ['wideMul', [x: 'int', y: 'int2'], 'long', '(x as long) * y'],
        ['pow2', [x: 'int'], 'long', '(x ** 2) as long'],
        ['shl', [x: 'int'], 'int', 'x << 1'],
        ['shl33', [x: 'int'], 'int', 'x << 33'],
        ['shr', [x: 'int'], 'int', 'x >> 1'],
        ['ushr', [x: 'int'], 'int', 'x >>> 1'],
        ['shrN', [x: 'int', y: 'int2'], 'int', 'x >> y'],
        ['and', [x: 'int', y: 'int2'], 'int', 'x & y'],
        ['or', [x: 'int', y: 'int2'], 'int', 'x | y'],
        ['xor', [x: 'int', y: 'int2'], 'int', 'x ^ y'],
        ['not', [x: 'int'], 'int', '~x'],
        ['lAdd', [l: 'long'], 'long', 'l + 1L'],
        ['lMul', [l: 'long'], 'long', 'l * 2L'],
        ['lNarrow', [l: 'long'], 'int', '(int) l'],
        ['lRem', [l: 'long', y: 'int2'], 'long', 'l % y'],
        ['lIntdiv', [l: 'long'], 'long', 'l.intdiv(2L)'],
        // comparisons and helpers
        ['cmp', [x: 'int', y: 'int2'], 'int', 'Integer.compare(x, y)'],
        ['ship', [x: 'int', y: 'int2'], 'int', 'x <=> y'],
        ['max', [x: 'int', y: 'int2'], 'int', 'Math.max(x, y)'],
        ['min', [x: 'int', y: 'int2'], 'int', 'Math.min(x, y)'],
        ['signum', [x: 'int'], 'int', 'Integer.signum(x)'],
        ['tern', [x: 'int', y: 'int2'], 'int', 'x > y ? x : y'],
        ['eqInt', [x: 'int', y: 'int2'], 'boolean', 'x == y'],
        ['truthInt', [x: 'int'], 'boolean', 'x as boolean'],
        ['elvisInt', [x: 'int'], 'int', 'x ?: 5'],
        ['asStr', [x: 'int'], 'String', 'x as String'],
        ['asStrLen', [x: 'int'], 'int', '(x as String).length()'],
        ['lsLastOrNot', [xs: 'List<Integer>'], 'boolean', 'xs.isEmpty() || xs.last() > 0'],
        // ranges
        ['inRange', [x: 'int'], 'boolean', 'x in 0..5'],
        ['inHalf', [x: 'int'], 'boolean', 'x in 0..<5'],
        ['inRev', [x: 'int'], 'boolean', 'x in 5..0'],
        ['inNeg', [x: 'int'], 'boolean', 'x in -3..-1'],
        ['rangeSize', [x: 'int2'], 'int', '(0..x).size()'],
        ['halfSize', [x: 'int2'], 'int', '(0..<x).size()'],
        ['revSize', [x: 'int2'], 'int', '(x..0).size()'],
        ['rangeSum', [x: 'int2'], 'int', '(0..<x).sum() as int'],
        ['rangeContains', [x: 'int2', y: 'int2'], 'boolean', '(0..<x).contains(y)'],
        // lists
        ['lsSize', [xs: 'List<Integer>'], 'int', 'xs.size()'],
        ['lsEmpty', [xs: 'List<Integer>'], 'boolean', 'xs.isEmpty()'],
        ['lsTruth', [xs: 'List<Integer>'], 'boolean', 'xs as boolean'],
        ['lsSum', [xs: 'List<Integer>'], 'Integer', 'xs.sum() as Integer'],
        ['lsSumInit', [xs: 'List<Integer>'], 'int', 'xs.sum(0) as int'],
        ['lsSumC', [xs: 'List<Integer>'], 'Integer', 'xs.sum { it * 2 } as Integer'],
        ['lsMax', [xs: 'List<Integer>'], 'Integer', 'xs.max()'],
        ['lsMin', [xs: 'List<Integer>'], 'Integer', 'xs.min()'],
        ['lsCount', [xs: 'List<Integer>'], 'int', 'xs.count(2) as int'],
        ['lsCountC', [xs: 'List<Integer>'], 'int', 'xs.count { it > 0 } as int'],
        ['lsContains', [xs: 'List<Integer>'], 'boolean', 'xs.contains(2)'],
        ['lsIn', [xs: 'List<Integer>'], 'boolean', '2 in xs'],
        ['lsIndexOf', [xs: 'List<Integer>'], 'int', 'xs.indexOf(2)'],
        ['lsLastIndexOf', [xs: 'List<Integer>'], 'int', 'xs.lastIndexOf(2)'],
        ['lsEvery', [xs: 'List<Integer>'], 'boolean', 'xs.every { it > 0 }'],
        ['lsAny', [xs: 'List<Integer>'], 'boolean', 'xs.any { it > 2 }'],
        ['lsAt0', [xs: 'List<Integer>'], 'Integer', 'xs[0]'],
        ['lsAtNeg', [xs: 'List<Integer>'], 'Integer', 'xs[-1]'],
        ['lsAt5', [xs: 'List<Integer>'], 'Integer', 'xs[5]'],
        ['lsGet0', [xs: 'List<Integer>'], 'Integer', 'xs.get(0)'],
        ['lsFirst', [xs: 'List<Integer>'], 'Integer', 'xs.first()'],
        ['lsLast', [xs: 'List<Integer>'], 'Integer', 'xs.last()'],
        ['lsFindAll', [xs: 'List<Integer>'], 'int', 'xs.findAll { it > 0 }.size()'],
        ['lsCollectSum', [xs: 'List<Integer>'], 'int', 'xs.collect { it * 2 }.sum(0) as int'],
        ['lsPlus', [xs: 'List<Integer>'], 'int', '(xs + [9]).size()'],
        ['lsTake', [xs: 'List<Integer>'], 'int', 'xs.take(2).size()'],
        ['lsDrop', [xs: 'List<Integer>'], 'int', 'xs.drop(1).size()'],
        ['lsSorted0', [xs: 'List<Integer>'], 'Integer', 'xs.toSorted()[0]'],
        ['lsIndices', [xs: 'List<Integer>'], 'int', 'xs.indices.size()'],
        ['lsFind', [xs: 'List<Integer>'], 'Integer', 'xs.find { it > 1 }'],
        ['lsFindIndexOf', [xs: 'List<Integer>'], 'int', 'xs.findIndexOf { it > 1 }'],
        ['lsInject', [xs: 'List<Integer>'], 'int', 'xs.inject(0) { int acc, int v -> acc + v }'],
        ['lsElvis', [xs: 'List<Integer>'], 'int', '(xs ?: [1, 1]).size()'],
        ['lsSorted', [xs: 'List<Integer>'], 'boolean', 'xs.isSorted()'],
        // arrays
        ['arLen', [a: 'int[]'], 'int', 'a.length'],
        ['arSize', [a: 'int[]'], 'int', 'a.size()'],
        ['arAt0', [a: 'int[]'], 'int', 'a[0]'],
        ['arAtNeg', [a: 'int[]'], 'int', 'a[-1]'],
        ['arSum', [a: 'int[]'], 'int', 'a.sum()'],
        ['arMax', [a: 'int[]'], 'int', 'a.max()'],
        ['arCount', [a: 'int[]'], 'int', 'a.count(2) as int'],
        ['arEvery', [a: 'int[]'], 'boolean', 'a.every { it > 0 }'],
        ['arAny', [a: 'int[]'], 'boolean', 'a.any { it > 2 }'],
        ['arToList', [a: 'int[]'], 'int', 'a.toList().size()'],
        ['arContains', [a: 'int[]'], 'boolean', 'a.contains(2)'],
        ['arTruth', [a: 'int[]'], 'boolean', 'a as boolean'],
        ['arSorted', [a: 'int[]'], 'boolean', 'a.isSorted()'],
        // strings
        ['sLen', [s: 'String'], 'int', 's.length()'],
        ['sSize', [s: 'String'], 'int', 's.size()'],
        ['sEmpty', [s: 'String'], 'boolean', 's.isEmpty()'],
        ['sTruth', [s: 'String'], 'boolean', 's as boolean'],
        ['sCharAt', [s: 'String'], 'char', 's.charAt(0)'],
        ['sAt0', [s: 'String'], 'String', 's[0]'],
        ['sAtNeg', [s: 'String'], 'String', 's[-1]'],
        ['sSub1', [s: 'String'], 'String', 's.substring(1)'],
        ['sSub02', [s: 'String'], 'String', 's.substring(0, 2)'],
        ['sIndexOf', [s: 'String'], 'int', "s.indexOf('l')"],
        ['sLastIndexOf', [s: 'String'], 'int', "s.lastIndexOf('l')"],
        ['sContains', [s: 'String'], 'boolean', "s.contains('l')"],
        ['sStarts', [s: 'String'], 'boolean', "s.startsWith('A')"],
        ['sEnds', [s: 'String'], 'boolean', "s.endsWith('l')"],
        ['sUpper', [s: 'String'], 'String', 's.toUpperCase()'],
        ['sLower', [s: 'String'], 'String', 's.toLowerCase()'],
        ['sReverse', [s: 'String'], 'String', 's.reverse()'],
        ['sTimes', [s: 'String'], 'String', 's * 2'],
        ['sConcatLen', [s: 'String'], 'int', '(s + s).length()'],
        ['sCount', [s: 'String'], 'int', "s.count('l')"],
        ['sTake', [s: 'String'], 'String', 's.take(2)'],
        ['sDrop', [s: 'String'], 'String', 's.drop(1)'],
        ['sEq', [s: 'String'], 'boolean', "s == 'Ab'"],
        ['sElvis', [s: 'String'], 'String', "s ?: 'z'"],
        ['sCmp', [s: 'String'], 'int', "Integer.signum(s <=> 'b')"],
        ['sRepl', [s: 'String'], 'String', "s.replace('l', 'L')"],
        ['sTrimLen', [s: 'String'], 'int', 's.trim().length()'],
        // booleans
        ['bNot', [b: 'boolean', x: 'int2'], 'boolean', '!b || x > 0'],
        ['bXor', [b: 'boolean', x: 'int2'], 'boolean', 'b ^ (x > 0)'],
        ['bImpl', [b: 'boolean', x: 'int2'], 'boolean', 'b ==> (x > 0)'],
    ]

    // ── literals ──────────────────────────────────────────────────────────────────────────────────────────────

    static String lit(Object v, String type) {
        if (v == null) return 'null'
        if (v instanceof Long || type == 'long') return "${v}L"
        if (v instanceof Integer && v == Integer.MIN_VALUE) return 'Integer.MIN_VALUE'
        if (v instanceof Long && v == Long.MIN_VALUE) return 'Long.MIN_VALUE'
        if (v instanceof Character) return "('${esc(v.toString())}' as char)"
        if (v instanceof String) return "'${esc((String) v)}'"
        v.toString()
    }

    static String esc(String s) { s.replace('\\', '\\\\').replace("'", "\\'") }

    /** `@Requires` pinning one parameter to one grid value. */
    static String pin(String name, String key, Object v) {
        switch (key) {
            case 'int': case 'int2':
                return v == Integer.MIN_VALUE ? "${name} == Integer.MIN_VALUE" : "${name} == ${v}"
            case 'long':
                return v == Long.MIN_VALUE ? "${name} == Long.MIN_VALUE" : "${name} == ${v}L"
            case 'boolean': return v ? name : "!${name}"
            case 'String': return "${name} != null && ${name} == '${esc((String) v)}'"
            case 'List<Integer>':
                List l = (List) v
                return (["${name} != null", "${name}.size() == ${l.size()}"] + l.withIndex().collect { e, i -> "${name}[${i}] == ${e}" }).join(' && ')
            case 'int[]':
                int[] a = (int[]) v
                return (["${name} != null", "${name}.length == ${a.length}"] + (0..<a.length).collect { i -> "${name}[${i}] == ${a[i]}" }).join(' && ')
        }
        throw new IllegalArgumentException(key)
    }

    static String javaParam(String key) { key == 'int2' ? 'int' : key }

    static List<List> points(Map<String, String> params) {
        List<List> out = [[]]
        params.values().each { String key -> out = out.collectMany { List p -> DOMAIN[key].collect { p + [it] } } }
        out
    }

    // ── compile / run ─────────────────────────────────────────────────────────────────────────────────────────

    static final String HDR = 'import groovy.transform.TypeChecked\nimport groovy.contracts.*\n'

    /** [line, message] for each error; an empty list for a clean compile. */
    static List<List> compileErrors(String name, String src) {
        // every method's verdict is needed: the default tolerance stops collecting after 10 errors
        def cfg = new org.codehaus.groovy.control.CompilerConfiguration()
        cfg.tolerance = 1_000_000
        def gcl = new GroovyClassLoader(Thread.currentThread().contextClassLoader, cfg)
        try {
            gcl.parseClass(src, "${name}.groovy")
            return []
        } catch (MultipleCompilationErrorsException e) {
            return e.errorCollector.errors.collect { err ->
                if (err instanceof SyntaxErrorMessage) return [err.cause.line, err.cause.message]
                if (err instanceof ExceptionMessage) return [-1, "${err.cause.class.simpleName}: ${err.cause.message}".toString()]
                [-1, err.toString()]
            }
        } finally {
            try { gcl.close() } catch (ignored) { }
        }
    }

    static Class runnable(String probe, Map<String, String> params, String ret, String expr) {
        String sig = params.collect { n, k -> "${javaParam(k)} ${n}" }.join(', ')
        String src = HDR + "@TypeChecked\nclass Run_${probe} {\n    static ${ret} run(${sig}) { ${expr} }\n}\n"
        new GroovyClassLoader(Thread.currentThread().contextClassLoader).parseClass(src, "Run_${probe}.groovy")
    }

    static Object copy(Object v) {
        v instanceof int[] ? ((int[]) v).clone() : v instanceof List ? new ArrayList((List) v) : v
    }

    static String show(Object v) {
        if (v instanceof int[]) return Arrays.toString((int[]) v)
        if (v instanceof Long) return "${v}L"
        InvokerHelper.inspect(v)
    }

    // ── the audit ─────────────────────────────────────────────────────────────────────────────────────────────

    /** One probe audited: each grid point's verdicts, as [kind, at, v, thrown, mine (its diagnostics)]. Null when the
     *  probe doesn't compile as plain Groovy. Under {@code overflow}, the class carries {@code @CheckOverflow}. */
    static List<Map> auditProbe(List probe, boolean overflow, List<String> crashes) {
        String pname = probe[0]
        Map<String, String> params = (Map<String, String>) probe[1]
        String ret = probe[2], expr = probe[3]
        Class run
        try { run = runnable(pname, params, ret, expr) } catch (Throwable t) { crashes << "${pname}: doesn't compile as plain Groovy (${t.message?.readLines()?.first()})"; return null }
        Method m = run.methods.find { it.name == 'run' }
        String sig = params.collect { n, k -> "${javaParam(k)} ${n}" }.join(', ')
        String cls = "Audit_${pname}${overflow ? '' : '_math'}"
        StringBuilder src = new StringBuilder(HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            (overflow ? '@verification.CheckOverflow\n' : '\n') + "final class ${cls} {\n")
        int line = 5
        Map<Integer, String> lineOwner = [:]   // each of a method's lines → its name
        List<Map> rows = []
        points(params).eachWithIndex { List pt, int i ->
            Object v
            Throwable thrown = null
            try { v = m.invoke(null, pt.collect { copy(it) } as Object[]) } catch (InvocationTargetException e) { thrown = e.cause }
            String req = params.keySet().withIndex().collect { n, j -> "(${pin(n, params[n], pt[j])})" }.join(' && ')
            String at = "${expr} at ${params.keySet().withIndex().collect { n, j -> "${n} = ${show(pt[j])}" }.join(', ')}"
            for (String kind : (thrown == null ? ['ne', 'eq'] : ['throws'])) {
                String mn = "${kind}_${i}"
                String ens = kind == 'ne' ? "\n    @Ensures({ result != ${lit(v, ret)} })" : kind == 'eq' ? "\n    @Ensures({ result == ${lit(v, ret)} })" : ''
                src.append("    @Requires({ ${req} })${ens}\n    static ${ret} ${mn}(${sig}) {\n        ${expr}\n    }\n")
                int span = ens ? 5 : 4                // the method's lines: @Requires, [@Ensures], signature, body, }
                (1..span).each { lineOwner[line + it] = mn }
                line += span
                rows << [mn: mn, kind: kind, at: at, v: v, thrown: thrown, expr: expr, point: i]
            }
        }
        src.append('}\n')
        List<List> errs = compileErrors(cls, src.toString())
        File dump = new File("build/encoder-audit/${cls}.txt")
        dump.parentFile.mkdirs()
        dump.text = src.toString() + '\n// ── errors ──\n' + errs.collect { "// ${it[0]}: ${it[1].readLines().first()}" }.join('\n')
        errs.findAll { it[0] == -1 }.each { crashes << "${pname}: ${it[1].readLines().first()}" }
        for (Map r : rows) {
            String mn = r.mn
            r.mine = errs.findAll { e -> lineOwner[(Integer) e[0]] == mn || (e[1] =~ /of ${mn}\b|for ${mn}\b/) }.collect { (String) it[1] }
        }
        rows
    }

    /** The audit's thousands of point-VCs aren't corpus work: run {@code body} with the solver counters PerfBudget
     *  asserts (over the whole test JVM) restored afterwards, so the corpus budget measures what it always has. */
    static void offBudget(Closure body) {
        List<String> names = ['vcHits', 'vcMisses', 'solverMs', 'solverMsPeak', 'unknowns', 'slowChecks']
        Map<String, Long> before = names.collectEntries { [(it): ((java.util.concurrent.atomic.AtomicLong) verification.Z3Backend."$it").get()] }
        try {
            body()
        } finally {
            names.each { ((java.util.concurrent.atomic.AtomicLong) verification.Z3Backend."$it").set(before[it]) }
        }
    }

    static boolean postProved(Map r) { !((List<String>) r.mine).any { it.contains('postcondition') || it.contains('Skipped') } }

    @Test
    void theEncoderAgreesWithTheRuntime() {
        List<String> unsound = [], unsoundLoud = [], silentThrows = [], disagreements = [], crashes = []
        int checked = 0, provedTrue = 0, skipped = 0
        offBudget { PROBES.each { List probe ->
            // under @CheckOverflow: the default math-int model is a documented assumption (README, Phase 44), so the
            // claim audited here is the strong one — the JVM's wrap, which @CheckOverflow is to make an obligation
            List<Map> rows = auditProbe(probe, true, crashes)
            if (rows == null) return
            for (Map r : rows) {
                List<String> mine = (List<String>) r.mine
                if (r.kind == 'ne') {
                    checked++
                    if (mine.any { it.contains('Skipped') && it.contains('postcondition') }) skipped++
                    else if (postProved(r) && mine.isEmpty()) unsound << "the encoder proves `${r.expr}` != ${show(r.v)}, which it is: ${r.at}"
                    else if (postProved(r)) unsoundLoud << "the encoder proves `${r.expr}` != ${show(r.v)} (beside '${mine.first().replaceFirst(/^\[Static type checking\] - /, '').take(70)}'): ${r.at}"
                } else if (r.kind == 'eq') {
                    if (postProved(r)) provedTrue++
                    else if (mine.any { it.contains('Cannot prove postcondition') }) disagreements << "can't prove `${r.expr}` == ${show(r.v)}: ${r.at}"
                } else if (mine.isEmpty()) {
                    silentThrows << "${r.at} throws ${r.thrown.class.simpleName}, and the verifier says nothing"
                }
            }
        } }
        println "Phase 368 encoder audit: ${PROBES.size()} probes, ${checked} points, ${provedTrue} values proved, ${skipped} skipped (outside the fragment)"
        println "  wrong values proved beside another warning: ${unsoundLoud.size()}"
        unsoundLoud.take(80).each { println "    ${it}" }
        println "  wrong values proved silently: ${unsound.size()}"
        println "  disagreements (precision): ${disagreements.size()}"
        disagreements.take(60).each { println "    ${it}" }
        println "  runtime throws the verifier is silent on: ${silentThrows.size()}"
        silentThrows.take(60).each { println "    ${it}" }
        println "  crashes: ${crashes.size()}"
        crashes.unique().take(30).each { println "    ${it}" }
        assertTrue(crashes.isEmpty(), "Probes that crashed:\n  " + crashes.unique().join('\n  '))
        assertTrue(unsound.isEmpty(), "The encoder proves values the runtime doesn't produce:\n  " + unsound.join('\n  '))
    }

    /** The probes whose value can wrap: the default model's only stated divergence from the JVM is there. */
    static final Set<String> ARITHMETIC = ['add', 'sub', 'mul', 'neg', 'inc', 'intdiv', 'divTrunc', 'sq', 'wideMul', 'pow2', 'shl',
                                           'shl33', 'lAdd', 'lMul', 'lNarrow', 'absM', 'absG', 'rangeSum', 'mod', 'rem', 'lRem'] as Set

    /**
     * Without {@code @CheckOverflow} integers are mathematical (README, Phase 44): a wrong value proved silently is
     * acceptable exactly where the JVM wraps — where the {@code @CheckOverflow} twin of the same point reports an
     * overflow. Anything else is a divergence the documented assumption doesn't cover.
     */
    @Test
    void theDefaultModelDivergesOnlyWhereTheJvmWraps() {
        List<String> crashes = [], unexplained = []
        int wraps = 0
        offBudget { PROBES.findAll { it[0] in ARITHMETIC }.each { List probe ->
            List<Map> math = auditProbe(probe, false, crashes)
            List<Map> checked = auditProbe(probe, true, crashes)
            if (math == null || checked == null) return
            Map<String, Map> twin = checked.collectEntries { [(it.mn): it] }
            for (Map r : math) {
                if (r.kind != 'ne' || !postProved(r) || !((List) r.mine).isEmpty()) continue
                Map t = twin[r.mn]
                if (t != null && ((List<String>) t.mine).any { it.contains('overflow') }) wraps++
                else unexplained << "the math-int model proves `${r.expr}` != ${show(r.v)}, which it is, with no overflow to explain it: ${r.at}"
            }
        } }
        println "Phase 368 default-model audit: ${wraps} wrong values proved where the JVM wraps (the stated assumption), ${unexplained.size()} unexplained"
        assertTrue(crashes.isEmpty(), "Probes that crashed:\n  " + crashes.unique().join('\n  '))
        assertTrue(unexplained.isEmpty(), "The default model diverges from the JVM beyond overflow:\n  " + unexplained.join('\n  '))
    }
}
