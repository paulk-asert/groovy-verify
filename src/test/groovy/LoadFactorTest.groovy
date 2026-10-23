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
import org.junit.jupiter.api.Test
import verification.VerifyChecker

/** Phase 383 — the per-check budget's load factor: within [1, 4], forced or off by the documented switches. */
class LoadFactorTest {

    private static double with(Map<String, String> props, Closure<Double> body) {
        Map<String, String> prev = props.collectEntries { k, v -> [k, System.getProperty(k)] }
        try {
            props.each { k, v -> v == null ? System.clearProperty(k) : System.setProperty(k, v) }
            body()
        } finally {
            prev.each { k, v -> v == null ? System.clearProperty(k) : System.setProperty(k, v) }
        }
    }

    @Test
    void theFactorIsWithinOneAndFour() {
        double f = with(['verify.z3.loadFactor': null, 'verify.z3.loadScaling': null]) { VerifyChecker.loadFactor() }
        assert f >= 1.0d && f <= 4.0d
    }

    @Test
    void aForcedFactorIsClamped() {
        assert with(['verify.z3.loadFactor': '2.5']) { VerifyChecker.loadFactor() } == 2.5d
        assert with(['verify.z3.loadFactor': '9']) { VerifyChecker.loadFactor() } == 4.0d
        assert with(['verify.z3.loadFactor': '0.2']) { VerifyChecker.loadFactor() } == 1.0d
    }

    @Test
    void scalingCanBeTurnedOff() {
        assert with(['verify.z3.loadScaling': 'false', 'verify.z3.loadFactor': '3']) { VerifyChecker.loadFactor() } == 1.0d
    }
}
