/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package verification

import java.lang.annotation.Documented
import java.lang.annotation.ElementType
import java.lang.annotation.Retention
import java.lang.annotation.RetentionPolicy
import java.lang.annotation.Target

/**
 * Phase 265 — STARVATION-FREEDOM IN THE LARGE, as a claim: every ready branch of the method's ALT is
 * served within {@code value} selects. Certified only where the selection policy's arithmetic gives the
 * bound — a HELD {@code fair()} select over k branches takes every ready branch within k selects, so the
 * claim holds iff {@code value >= k}; refuted with the policy's own reason everywhere else (priority: no
 * bound at all for a branch behind an always-ready one; {@code fair()} on a fresh instance: no rotation
 * state; {@code random()}: fair in expectation only; the racing select before GROOVY-12320: losers
 * re-sent). "Eventually" is the weak-fairness certificate of Phases 255/257; this is the QUANTITATIVE half.
 */
@Retention(RetentionPolicy.SOURCE)
@Target([ElementType.METHOD])
@Documented
@interface ServedWithin {
    int value()
}
