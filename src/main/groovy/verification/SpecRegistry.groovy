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
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.ModuleNode
import org.codehaus.groovy.control.CompilationUnit
import org.codehaus.groovy.control.CompilerConfiguration
import org.codehaus.groovy.control.Phases
import org.codehaus.groovy.control.SourceUnit

import java.util.concurrent.ConcurrentHashMap

/**
 * Phase 215 — the <b>external-specification registry</b>: JML's {@code .jml} idea in the project's own
 * dialect. A spec file is an ordinary Groovy <i>skeleton</i> — the target class re-declared with
 * groovy-contracts annotations and empty method bodies:
 *
 * <pre>
 *   // META-INF/groovy-verify/specs/java.lang.Math.groovy
 *   package java.lang
 *   class Math {
 *       {@literal @}Pure
 *       {@literal @}Requires({ a > Integer.MIN_VALUE })
 *       {@literal @}Ensures({ (a >= 0 ==> result == a) && (a < 0 ==> result == -a) })
 *       static int abs(int a) {}
 *   }
 * </pre>
 *
 * <p><b>Discovery</b> is lazy and index-free: the first lookup of an FQN tries exactly one classpath
 * resource, {@code META-INF/groovy-verify/specs/&lt;fqn&gt;.groovy} (a {@code VERIFY_SPECS} /
 * {@code -Dverify.specs} directory overrides it, JML-specspath-style, for local iteration). Being under
 * {@code META-INF/} the skeletons are resources to every build tool — never compiled as production code
 * — while remaining syntactically ordinary Groovy.
 *
 * <p><b>Parsing</b> stops at the {@code CONVERSION} phase (AST only — no static type checking, no
 * class generation, no clash with the real class), then runs {@link ContractExpansionTransform}
 * manually so the skeleton's methods carry {@code @ContractSource} exactly as user code does. The
 * cached {@link MethodNode}s then flow through the ordinary contract machinery: a spec'd method's
 * {@code @Requires} becomes an <b>obligation at every call site</b>, its {@code @Ensures} is
 * <b>assumed</b> for the call's result.
 *
 * <p><b>Trust posture</b>: every registry spec is trusted by definition — nobody proves the JDK's
 * bodies. Consumption is recorded (see {@link #consumed}) for the trusted-spec ledger.
 */
@CompileStatic
class SpecRegistry {

    private static final Object MISS = new Object()
    private static final Map<String, Object> CACHE = new ConcurrentHashMap<String, Object>()
    private static final Set<String> CONSUMED = ConcurrentHashMap.newKeySet()

    /** Node metadata key marking a MethodNode as registry-sourced (a trusted skeleton). */
    public static final String SPEC_KEY = 'verification.spec'

    /**
     * The spec'd MethodNode for {@code fqn#name/arity}, or null. Lazy-loads and caches per FQN.
     * {@code paramTypeNames} (the resolved target's parameter type simple names) disambiguates JDK
     * overloads — {@code abs(int)} vs {@code abs(double)}; without it, the skeleton method is returned
     * only when it is the UNIQUE (name, arity) match (an ambiguous overload set declines, so an int
     * spec can never be mis-applied to the FP overload).
     */
    static MethodNode lookup(String fqn, String name, int arity, List<String> paramTypeNames = null) {
        if (fqn == null || name == null) return null
        Object entry = CACHE.computeIfAbsent(fqn, { String k -> (load(k) ?: MISS) as Object })
        if (!(entry instanceof ClassNode)) return null
        List<MethodNode> byArity = ((ClassNode) entry).getMethods(name).findAll { it.parameters.length == arity }
        MethodNode m
        if (paramTypeNames != null) {
            m = byArity.find { MethodNode c ->
                List<String> specTypes = c.parameters.collect { simpleTypeName(it.type.name) }
                specTypes == paramTypeNames.collect { simpleTypeName(it) }
            }
        } else {
            m = byArity.size() == 1 ? byArity.get(0) : null
        }
        if (m != null) {
            m.putNodeMetaData(SPEC_KEY, Boolean.TRUE)
            CONSUMED.add("${fqn}#${name}/${arity}".toString())
            TrustLedger.record('external spec', "${fqn}#${name}/${arity}".toString(),
                'registry skeleton (META-INF/groovy-verify/specs)')
        }
        m
    }

    private static String simpleTypeName(String n) {
        String s = n.contains('.') ? n.substring(n.lastIndexOf('.') + 1) : n
        // box/unbox pairs are one type for matching purposes
        switch (s) {
            case 'Integer': return 'int'
            case 'Long': return 'long'
            case 'Double': return 'double'
            case 'Float': return 'float'
            case 'Boolean': return 'boolean'
            case 'Character': return 'char'
            case 'Short': return 'short'
            case 'Byte': return 'byte'
            default: return s
        }
    }

    /** The trusted-spec ledger: every {@code fqn#name/arity} this JVM's compilations consumed. */
    static Set<String> consumed() { Collections.unmodifiableSet(CONSUMED) }

    /** Test hook: drop all cached parses (spec files edited under a live daemon). */
    static void reset() { CACHE.clear(); CONSUMED.clear() }

    /** Lint-facing: parse spec TEXT exactly as {@link #lookup} would (no cache); null on failure. */
    static ClassNode parseForLint(String text, String fqn) {
        try {
            Object r = parse(text, fqn)
            r instanceof ClassNode ? (ClassNode) r : null
        } catch (Throwable ignored) { null }
    }

    /** Lint-facing: true when CET captured at least one contract text on the method — or the method
     *  carries a @ThrowsIf arm (exceptional-only specs are real specs, not lint drift). */
    static boolean hasContractText(MethodNode m) {
        m.getAnnotations().any { it.classNode.nameWithoutPackage in ['ContractSource', 'ThrowsIf', 'ThrowsIfConditions'] }
    }

    private static ClassNode load(String fqn) {
        String text = specText(fqn)
        if (text == null) return null
        parse(text, fqn)
    }

    private static ClassNode parse(String text, String fqn) {
        try {
            CompilerConfiguration cfg = new CompilerConfiguration()
            // AST only: no gc weaving, no STC, no codegen — and CET applied manually below, so the
            // global-transform pipeline's behaviour here is deliberate rather than phase-dependent.
            cfg.disabledGlobalASTTransformations = [
                'verification.ContractExpansionTransform',
                'org.apache.groovy.contracts.ast.GContractsASTTransformation',
                'org.apache.groovy.contracts.ast.ClosureExpressionEvaluationASTTransformation',
                'org.apache.groovy.contracts.ast.MethodVariantInheritanceASTTransformation'] as Set
            CompilationUnit cu = new CompilationUnit(cfg)
            SourceUnit su = cu.addSource('spec$' + fqn.replace('.', '_') + '.groovy', text)
            cu.compile(Phases.CONVERSION)
            ModuleNode module = su.AST
            if (module == null) return null
            ClassNode cn = module.classes.find { it.name == fqn } ?: (module.classes ? module.classes[0] : null)
            if (cn == null) return null
            new ContractExpansionTransform().visit([module] as ASTNode[], su)   // attach @ContractSource
            cn
        } catch (Throwable ignored) {
            null   // a malformed spec file must never break the consuming compile; the miss is cached
        }
    }

    private static String specText(String fqn) {
        String dir = System.getProperty('verify.specs', System.getenv('VERIFY_SPECS'))
        if (dir != null && !dir.isEmpty()) {
            File f = new File(dir, fqn + '.groovy')
            if (f.isFile()) return f.getText('UTF-8')
        }
        String res = 'META-INF/groovy-verify/specs/' + fqn + '.groovy'
        ClassLoader tccl = Thread.currentThread().contextClassLoader
        URL u = (tccl != null ? tccl.getResource(res) : null) ?: SpecRegistry.classLoader.getResource(res)
        u != null ? u.getText('UTF-8') : null
    }
}
