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

/**
 * Minimal SMT backend surface — just enough for the spike's
 * linear-integer + boolean fragment. The one implementation is
 * {@link Z3Backend}; the seam exists so {@link Encoder} can be written
 * against an interface rather than Z3 types directly.
 *
 * The fragment is deliberately small: integer variables, integer
 * literals, +/-/*-by-literal, comparisons, boolean and/or/not.
 * Anything else surfaces through {@link Encoder} as a
 * "fragment-not-supported" warning before it reaches the backend.
 */
@CompileStatic
interface SmtBackend {

    /** Opens a fresh assertion context. Caller must close(). */
    SmtSession session()
}

@CompileStatic
interface SmtSession extends AutoCloseable {

    /** Declare an integer variable; returns a backend-specific handle. */
    Object intVar(String name)

    /** Build expressions. Args are handles previously returned by this session. */
    Object intLit(long n)
    Object plus(Object a, Object b)
    Object minus(Object a, Object b)
    Object times(Object a, Object b)
    Object neg(Object a)

    Object eq(Object a, Object b)
    Object ne(Object a, Object b)
    Object lt(Object a, Object b)
    Object le(Object a, Object b)
    Object gt(Object a, Object b)
    Object ge(Object a, Object b)

    Object and(List<Object> xs)
    Object or(List<Object> xs)
    Object not(Object x)
    Object implies(Object a, Object b)

    Object boolLit(boolean b)

    /** Assert a boolean expression. */
    void assertExpr(Object boolExpr)

    /**
     * Check the current assertion set. Returns:
     *   - VERIFIED if UNSAT (i.e. the property holds)
     *   - REFUTED with a counterexample if SAT
     *   - UNKNOWN if the solver gave up / timed out
     *
     * NOTE: the caller asserts the *negation* of what they want to
     * prove. SAT means the negation has a model, i.e. the property
     * fails on that model.
     */
    CheckResult check()

    @Override
    void close()
}

@CompileStatic
class CheckResult {
    enum Status { VERIFIED, REFUTED, UNKNOWN }
    Status status
    /** Variable name -> concrete value, populated only on REFUTED. */
    Map<String, Long> counterexample = [:]
    /** Free-text reason, populated on UNKNOWN. */
    String reason

    static CheckResult verified() {
        new CheckResult(status: Status.VERIFIED)
    }
    static CheckResult refuted(Map<String, Long> ce) {
        new CheckResult(status: Status.REFUTED, counterexample: ce)
    }
    static CheckResult unknown(String why) {
        new CheckResult(status: Status.UNKNOWN, reason: why)
    }
}
