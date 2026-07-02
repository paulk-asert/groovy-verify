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

/** 'PL1 infoflow' — 37 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G242_pl1_infoflow {

    static final List<Map> CASES = [
        // ---------- Phase L1 — information-flow noninterference (static labels), Smith §III ----------
        // Slice 1 builds on the PL0 lattice: a method whose result carries an @Label classification, with
        // @Label-tagged parameters as sources. For each `return e`, the verifier discharges the no-leak
        // obligation leq(ΓE(e), L(result)) over the class's own leq/join — so a High parameter reaching a
        // Low result refutes ("information leak"), while a Low→Low flow proves. Static labels / straight-line
        // returns only; locals, branches (PC), arrays and value-dependent labels are later slices.
        // The lattice the class carries (Low ⊑ High), shared by every PL1 case below.
        [group: 'PL1 infoflow', name: 'Low source → Low result verifies (no leak)', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int pass(@Label('Low') int pub, @Label('High') int secret) { return pub }
                    }''')],
        // The headline: a High parameter returned where the result is classified Low — refuted.
        [group: 'PL1 infoflow', name: 'High source → Low result refuted (leak caught)', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int leak(@Label('Low') int pub, @Label('High') int secret) { return secret }
                    }''')],
        // A High result accepts anything (High is the top): High source → High result verifies.
        [group: 'PL1 infoflow', name: 'High source → High result verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('High')
                        static int hi(@Label('High') int secret) { return secret }
                    }''')],
        // Compound source: join of operand levels. `pub + secret` is High (Low ⊔ High), so a Low result refutes.
        [group: 'PL1 infoflow', name: 'join of sources (pub + secret) → Low result refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int combine(@Label('Low') int pub, @Label('High') int secret) { return pub + secret }
                    }''')],
        // Loud-skip soundness: a return drawing on an unlabelled source is not silently passed — it is skipped.
        [group: 'PL1 infoflow', name: 'unlabelled source skips loudly (not a silent pass)', expect: 'Skipped information-flow check',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int unlabelled(int x) { return x }
                    }''')],

        // ----- Slice 1b — Γ threaded through local assignments -----
        // The headline 1b case: a High value laundered through a local is still High at the Low result — caught.
        [group: 'PL1 infoflow', name: '1b: High via local (int t = secret; return t) refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int launder(@Label('High') int secret) { int t = secret; return t }
                    }''')],
        // A Low value through a local stays Low → verifies.
        [group: 'PL1 infoflow', name: '1b: Low via local verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int via(@Label('Low') int pub) { int t = pub; return t }
                    }''')],
        // Reassignment: Γ reflects the *current* contents — t is overwritten with a Low value before return, so
        // the earlier High assignment does not leak. (Last write wins on a straight-line path.)
        [group: 'PL1 infoflow', name: '1b: reassignment to Low before return verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int over(@Label('Low') int pub, @Label('High') int secret) {
                            int t = secret
                            t = pub
                            return t
                        }
                    }''')],
        // Chained locals + join: u = t (High) then return combined with a Low local → still High, refuted.
        [group: 'PL1 infoflow', name: '1b: chained local + join (return u + pub) refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int chain(@Label('Low') int pub, @Label('High') int secret) {
                            int t = secret
                            int u = t
                            return u + pub
                        }
                    }''')],

        // ----- Slice 1c — program-counter label / implicit flow -----
        // THE IMPLICIT-FLOW HEADLINE: assigning a Low value to t under a branch on a High secret raises t to High
        // (its value now reveals which branch ran). Returning t at a Low result refutes — no explicit High value
        // is ever assigned to the result, yet the leak is caught via the PC. No literals needed.
        [group: 'PL1 infoflow', name: '1c: implicit flow (assign under secret branch) refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int implicit(@Label('High') boolean secret,
                                            @Label('Low') int a, @Label('Low') int b) {
                            int t = a
                            if (secret) t = a else t = b   // t now reveals `secret`…
                            return t   // REFUTED — though only Low values are ever assigned
                        }
                    }''')],
        // A return *inside* a branch on a secret leaks the guard (which branch ran), even returning a Low value.
        [group: 'PL1 infoflow', name: '1c: return inside secret branch refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int branchReturn(@Label('High') boolean secret,
                                                @Label('Low') int a, @Label('Low') int b) {
                            if (secret) return a else return b
                        }
                    }''')],
        // PRECISION (no false positive): branching on a secret but returning a Low value that does NOT depend on
        // the branch is secure — the PC is scoped to the if, so post-branch code does not inherit it.
        [group: 'PL1 infoflow', name: '1c: PC scoped — low value after secret branch verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int scoped(@Label('High') boolean secret, @Label('Low') int pub) {
                            int t = pub
                            if (secret) { int dummy = pub }
                            return t
                        }
                    }''')],
        // A branch on a *public* guard does not raise the PC: returning a value set under it stays Low → verifies.
        [group: 'PL1 infoflow', name: '1c: branch on public guard does not raise PC', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int pubGuard(@Label('Low') boolean flag,
                                            @Label('Low') int a, @Label('Low') int b) {
                            int t = a
                            if (flag) t = a else t = b
                            return t
                        }
                    }''')],
        // ----- Loops — the Γ-invariant is inferred over the finite level lattice -----
        // A loop that only moves Low data keeps t Low across iterations → verifies (the loop is handled, not skipped).
        [group: 'PL1 infoflow', name: 'loop: Low-only loop verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int loopy(@Label('Low') int pub) {
                            int t = pub
                            for (int i = 0; i < 3; i++) { t = pub }
                            return t
                        }
                    }''')],
        // A loop that pulls a High value into t raises t to High for all iterations → the later return refutes.
        [group: 'PL1 infoflow', name: 'loop: High pulled in raises the loop variable (refuted)', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int loopy(@Label('Low') int pub, @Label('High') int secret) {
                            int t = pub
                            while (t > 0) { t = secret }
                            return t
                        }
                    }''')],
        // A while-countdown over Low data (with arithmetic) stays Low → verifies. Exercises a literal in the body.
        [group: 'PL1 infoflow', name: 'loop: countdown stays Low verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int countdown(@Label('Low') int n) {
                            int t = n
                            while (t > 0) { t = t - 1 }
                            return t
                        }
                    }''')],
        // Implicit flow through a loop: looping on a secret condition and writing t inside raises t (the number
        // of iterations reveals the secret) → refuted via the loop PC.
        [group: 'PL1 infoflow', name: 'loop: implicit flow via secret loop guard (refuted)', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int countSecret(@Label('High') int secret, @Label('Low') int pub) {
                            int t = pub
                            int s = secret
                            while (s > 0) { t = pub; s = s - 1 }
                            return t
                        }
                    }''')],
        // Loud-skip: a for-each over a collection is still outside the fragment (element labels not modelled).
        [group: 'PL1 infoflow', name: 'loop: for-each over a collection skips loudly', expect: 'Skipped information-flow check',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int eachLoop(@Label('Low') int pub, List<Integer> xs) {
                            int t = pub
                            for (x in xs) { t = pub }
                            return t
                        }
                    }''')],

        // ----- Control-variable / secure-update (Smith §III-A) -----
        // `data`'s classification is Low when authed, else High (value-dependent). `authed` is therefore a
        // CONTROL variable. Flipping it to `true` makes L(data) == Low — but data may still hold High data (when
        // it was unauthenticated), so the classification dropped below the held level. REFUTED at the assignment:
        // the "declassify-by-flag" bug — making a field public while it still holds a secret.
        [group: 'PL1 infoflow', name: 'secure-update: flipping the flag public refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L classifyData(boolean authed) { authed ? L.Low : L.High }
                        static void declassify(boolean authed, @Label(by = 'classifyData') int data) {
                            authed = true   // REFUTED — L(data) becomes Low, but data may hold High
                        }
                    }''')],
        // The opposite update — making the classification MORE secret (authed := false ⇒ L(data) == High) — is
        // always secure: whatever data holds is below High. Verifies.
        [group: 'PL1 infoflow', name: 'secure-update: raising the classification verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L classifyData(boolean authed) { authed ? L.Low : L.High }
                        static void protect(boolean authed, @Label(by = 'classifyData') int data) {
                            authed = false
                        }
                    }''')],
        // Assigning a *non*-control variable triggers no secure-update obligation (and no false alarm): `other`
        // is read by no classification, so flipping it is fine.
        [group: 'PL1 infoflow', name: 'secure-update: assigning a non-control variable is fine', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L classifyData(boolean authed) { authed ? L.Low : L.High }
                        static void f(boolean authed, boolean other, @Label(by = 'classifyData') int data) {
                            other = true
                        }
                    }''')],

        // ----- Declassification — explicit, auditable controlled release (Smith §III-E) -----
        // The password-checker: releasing the single equality *bit* (correct/incorrect) is permitted — but only
        // through an explicit Declassify marker. `Declassify.to('Low', password == guess)` releases it at Low, so
        // the Low-classified result verifies. Every release is greppable and reviewable in the source.
        [group: 'PL1 infoflow', name: 'declassify: password check releases the equality bit (verifies)', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static boolean check(@Label('High') int password, @Label('Low') int guess) {
                            return Declassify.to('Low', password == guess)   // release one bit — verified
                        }
                    }''')],
        // The SAME method *without* the declassification marker leaks — `password == guess` carries High → refuted.
        // Declassification is required and explicit, not implicit.
        [group: 'PL1 infoflow', name: 'declassify: equality bit without the marker refutes', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static boolean check(@Label('High') int password, @Label('Low') int guess) {
                            return password == guess
                        }
                    }''')],
        // Declassification into a cross-class sink: explicitly release a derived value at Low into the log.
        [group: 'PL1 infoflow', name: 'declassify: release into a sink verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void audit(@Label('High') int secret, @Label('Low') int pub) {
                            Audit.log(Declassify.to('Low', secret == pub))
                        }
                    }
                    class Audit {
                        static void log(@Label('Low') boolean x) { }
                    }''')],
        // Soundness control: declassifying to 'High' does NOT launder a secret to a Low result — releasing the
        // secret at High still exceeds the Low classification → refuted. The marker releases at the *named* level,
        // it is not a blanket downgrade.
        [group: 'PL1 infoflow', name: 'declassify: releasing at High still refutes a Low result', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        @Label('Low')
                        static int passthrough(@Label('High') int secret) {
                            return Declassify.to('High', secret)
                        }
                    }''')],

        // ----- Interprocedural slice — labels cross method boundaries into a sink parameter -----
        // THE SINK HEADLINE (the SQL-injection / log-a-secret shape): a High value passed to a method whose
        // parameter is classified Low refutes — the leak is at the *call*, not a return. `leak` itself is void
        // and has no labelled result; it is in the analysis purely because it carries a labelled source.
        [group: 'PL1 infoflow', name: 'interproc: High arg → Low sink parameter refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void sink(@Label('Low') int x) { }     // a public sink
                        static void leak(@Label('High') int secret) { sink(secret) }
                    }''')],
        // A Low argument into the same Low sink is fine.
        [group: 'PL1 infoflow', name: 'interproc: Low arg → Low sink verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void sink(@Label('Low') int x) { }
                        static void send(@Label('Low') int pub) { sink(pub) }
                    }''')],
        // Launder through a local, then into the sink — still High at the boundary, refuted (1b + interproc).
        [group: 'PL1 infoflow', name: 'interproc: laundered local into Low sink refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void sink(@Label('Low') int x) { }
                        static void leak(@Label('High') int secret) { int t = secret; sink(t) }
                    }''')],
        // Implicit flow into a sink: a Low value passed to a Low sink *under a secret branch* leaks (the call
        // happening reveals the branch) — refuted via the PC (1c + interproc).
        [group: 'PL1 infoflow', name: 'interproc: implicit flow into sink (call under secret branch) refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void sink(@Label('Low') int x) { }
                        static void cond(@Label('High') boolean secret, @Label('Low') int pub) {
                            if (secret) sink(pub)
                        }
                    }''')],
        // An unlabelled argument to a labelled sink is not silently passed — it skips loudly.
        [group: 'PL1 infoflow', name: 'interproc: unlabelled arg to Low sink skips loudly', expect: 'Skipped information-flow check',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void sink(@Label('Low') int x) { }
                        static void pass(@Label('Low') int pub, int other) { sink(other) }
                    }''')],

        // ----- Cross-class sinks — the sink lives in another class (the library-call shape) -----
        // THE CROSS-CLASS HEADLINE: a High value into a Low sink parameter of *another* class refutes. The caller
        // C carries the lattice + the labelled source; the sink class Audit just declares the @Label parameter
        // (it isn't @TypeChecked, only resolved). Audit.log(secret) → REFUTED at the call.
        [group: 'PL1 infoflow', name: 'cross-class: High arg → Low sink in another class refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void leak(@Label('High') int secret) { Audit.log(secret) }
                    }
                    class Audit {
                        static void log(@Label('Low') int x) { }
                    }''')],
        // A Low value into the same cross-class sink verifies.
        [group: 'PL1 infoflow', name: 'cross-class: Low arg → Low sink verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static void send(@Label('Low') int pub) { Audit.log(pub) }
                    }
                    class Audit {
                        static void log(@Label('Low') int x) { }
                    }''')],
        // Instance receiver of a known object-parameter type: log.write(secret) where `log` is a Logger param —
        // resolved via the receiver's declared type, refuted just the same.
        [group: 'PL1 infoflow', name: 'cross-class: instance sink via typed receiver refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        void leak(Logger log, @Label('High') int secret) { log.write(secret) }
                    }
                    class Logger {
                        void write(@Label('Low') int x) { }
                    }''')],

        // ----- Value-dependent classifications — L(x) depends on program state (Smith §III-A) -----
        // The "beyond taint" capability: `data`'s classification is given by classifyData(authed) — Low when
        // authenticated, High otherwise. Releasing it *under the authentication guard* is secure (there
        // L(data) == Low), so this verifies. The discharge assumes the path condition `authed`.
        [group: 'PL1 infoflow', name: 'value-dependent: release under the guard verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L classifyData(boolean authed) { authed ? L.Low : L.High }   // value-dependent classification
                        @Label('Low')
                        static int get(boolean authed, @Label(by = 'classifyData') int data,
                                       @Label('Low') int fallback) {
                            if (authed) return data   // VERIFIED — under the check, L(data) == Low
                            return fallback
                        }
                    }''')],
        // The same value released WITHOUT the guard refutes — when !authed, L(data) is High and the result is
        // Low. The counterexample is the unauthenticated state (authed = false). This is what taint cannot
        // express: a classification that depends on state.
        [group: 'PL1 infoflow', name: 'value-dependent: release without the guard refuted', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L classifyData(boolean authed) { authed ? L.Low : L.High }
                        @Label('Low')
                        static int get(boolean authed, @Label(by = 'classifyData') int data) {
                            return data
                        }
                    }''')],
        // Value-dependent into a cross-class sink, under the guard — secure.
        [group: 'PL1 infoflow', name: 'value-dependent: release into sink under guard verifies', ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L classifyData(boolean authed) { authed ? L.Low : L.High }
                        static void serve(boolean authed, @Label(by = 'classifyData') int data) {
                            if (authed) Audit.log(data)
                        }
                    }
                    class Audit {
                        static void log(@Label('Low') int x) { }
                    }''')],
        // The wrong guard does not help: guarding on an unrelated condition leaves L(data) able to be High → refuted.
        [group: 'PL1 infoflow', name: 'value-dependent: wrong guard does not declassify (refuted)', expect: 'information leak',
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        static L classifyData(boolean authed) { authed ? L.Low : L.High }
                        @Label('Low')
                        static int get(boolean authed, boolean other, @Label(by = 'classifyData') int data) {
                            if (other) return data
                            return data
                        }
                    }''')],
    ]
}
