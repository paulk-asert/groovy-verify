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

/** 'P-ring' — 19 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G033_p_ring {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The merged Buffer flagship: both §IV rely/guarantee halves on one class (compatibility lemmas + @UnderRely-framed bodies), including rely-steps inside loop bodies.'

    static final List<Map> CASES = [
        // The README flagship `Buffer` — keep in sync with the rely/guarantee subsection. ONE class drives BOTH
        // halves of §IV: the @Rely/@Guarantee predicates discharge the compatibility lemmas, AND the same @Rely
        // predicates synthesise the rely-steps for read()/write() (via @UnderRely), each proven free of
        // out-of-bounds access. One vocabulary (Producer/Consumer), one class.
        [group: 'P-ring', name: 'merged buffer: both §IV halves on one class (README flagship)', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                       int head
                       int tail
                       int[] values
                       @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail
                       }
                       @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail && oldHead <= head
                       }
                       @Requires({ head < tail })
                       @UnderRely('Consumer')
                       int read() {
                           int v = values[head]
                           head = head + 1
                           return v
                       }
                       @Requires({ tail < values.length })
                       @UnderRely('Producer')
                       void write(int x) {
                           values[tail] = x
                           tail = tail + 1
                       }
                   }''')],
        // Loop-body placement: a rely-step INSIDE a loop body is framed per iteration (LoopEncoder call-handler), so
        // a loop verifies under the environment's interference. Summing the first k elements under a rely where the
        // writer keeps head and only grows tail: the loop invariant `k <= tail` is rely-stable (tail only grows), so
        // values[j] (j < k <= tail <= length) stays in bounds across iterations.
        [group: 'P-ring', name: 'rely-step inside loop body verifies', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head == old.head && old.tail <= tail && tail <= values.length })
                       void relyWriter() {}
                       @Requires({ 0 <= k && k <= tail })
                       int sumFirst(int k) {
                           int sum = 0
                           int j = 0
                           @Invariant({ 0 <= j && j <= k && k <= tail && tail <= values.length })
                           @Decreases({ k - j })
                           while (j < k) {
                               relyWriter()
                               sum = sum + values[j]
                               j = j + 1
                           }
                           return sum
                       }
                   }''')],
        // Auto loop-body placement: @UnderRely + a loop whose body reads a shared field — the transform inserts the
        // rely-step INSIDE the loop body (per iteration), no hand-writing. Summing a window [head, head+n): the loop
        // invariant `head + n <= tail` is rely-stable (writer keeps head, grows tail), so values[head+i] is in bounds.
        [group: 'P-ring', name: 'auto rely-step placed inside loop body verifies', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ 0 <= n && head + n <= tail })
                       @UnderRely('Writer')
                       int sumWindow(int n) {
                           int sum = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && head + n <= tail && tail <= values.length })
                           @Decreases({ n - i })
                           while (i < n) {
                               sum = sum + values[head + i]    // reads head (framed) → rely-step auto-inserted before
                               i = i + 1
                           }
                           return sum
                       }
                   }''')],
        // Limitation: a loop body that WRITES a framed field gets a post-write invariant assert (the masking fix),
        // which the loop fragment doesn't model — so such a loop loud-skips (honest, not silent). Flips to a real
        // verify when the LoopEncoder learns to discharge an assert in the loop body.
        // A loop body that WRITES a framed field now verifies: the post-write invariant assert is discharged in the
        // loop (under the loop invariant + guard + replayed body), then assumed for the rest of the iteration.
        [group: 'P-ring', name: 'loop body with framed write verifies (in-loop assert discharge)', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ head < tail })
                       @UnderRely('Writer')
                       void consumeOne() {
                           int done = 0
                           @Invariant({ 0 <= done && done <= 1 && 0 <= head && head <= tail && tail <= values.length })
                           @Decreases({ 1 - done })
                           while (done < 1) {
                               head = head + 1
                               done = done + 1
                           }
                       }
                   }''')],
        // Soundness — masking INSIDE a loop: a transient invariant violation between two shared writes (with a
        // rely-step inserted between them) must refute. Preservation alone would miss it (the loop invariant holds
        // at the body's end, head == 0), but the in-loop post-write assert catches head = tail + 1 at the write.
        [group: 'P-ring', name: 'transient invariant violation inside a loop refutes', expect: 'Assertion may not hold',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ head < tail })
                       @UnderRely('Writer')
                       void loopMask() {
                           int done = 0
                           @Invariant({ 0 <= done && done <= 1 && 0 <= head && head <= tail && tail <= values.length })
                           @Decreases({ 1 - done })
                           while (done < 1) {
                               head = tail + 1
                               head = 0
                               done = done + 1
                           }
                       }
                   }''')],
        // Soundness of loop-body framing: a loop invariant that is NOT rely-stable must refute. Here `tail == t0`
        // claims tail is constant, but the rely lets the writer grow tail — so the rely-step's havoc inside the
        // loop breaks the invariant and preservation fails. (Without framing the loop would have loud-skipped or,
        // worse, silently "preserved" the false invariant since this thread never touches tail.)
        [group: 'P-ring', name: 'non-rely-stable loop invariant refutes', expect: 'invariant',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head == old.head && old.tail <= tail && tail <= values.length })
                       void relyWriter() {}
                       @Requires({ 0 <= k && k <= tail })
                       int badInvariant(int k) {
                           int j = 0
                           int t0 = tail
                           @Invariant({ 0 <= j && j <= k && tail == t0 })
                           @Decreases({ k - j })
                           while (j < k) {
                               relyWriter()
                               j = j + 1
                           }
                           return j
                       }
                   }''')],
        // P-ring: a complete CONCURRENT bounded buffer — reader AND writer each proven free of OUT-OF-BOUNDS
        // access, a real memory-safety property (not an abstract assert). The class @Invariant bounds the buffer
        // (head <= tail <= capacity). Each side's rely is the *other side's guarantee*: the reader relies on the
        // writer keeping `head` and only growing `tail` within capacity; the writer relies on the reader keeping
        // `tail` and only advancing `head`. Given that, `values[head]`/`values[tail]` are in bounds despite the
        // concurrent peer, and each method preserves the invariant. Composes fix-b (head++/tail++ SSA),
        // call-framing (the rely-step havoc+assume), array bounds, and the class invariant. (Engine-coverage form
        // with hand-written @Modifies/@Ensures rely-steps; the README flagship uses the @UnderRely-synthesised form
        // above.)
        [group: 'P-ring', name: 'concurrent bounded buffer: reader + writer both in bounds', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values

                       @Modifies({ [this.head, this.tail] })       // the writer's guarantee, the reader's rely
                       @Ensures({ head == old.head && old.tail <= tail && tail <= values.length })
                       void relyOnWriter() {}
                       @Modifies({ [this.head, this.tail] })       // the reader's guarantee, the writer's rely
                       @Ensures({ tail == old.tail && old.head <= head && head <= tail })
                       void relyOnReader() {}

                       @Requires({ head < tail })                  // an element is available to read
                       int read() {
                           relyOnWriter()                          // a concurrent write may have happened
                           int v = values[head]                    // PROVEN in bounds: 0 <= head < values.length
                           head = head + 1
                           return v
                       }
                       @Requires({ tail < values.length })         // room to append
                       void write(int x) {
                           relyOnReader()                          // a concurrent read may have happened
                           values[tail] = x                        // PROVEN in bounds: 0 <= tail < values.length
                           tail = tail + 1
                       }
                   }''')],
        // Weaken the reader's rely — drop `head == old.head`, so the writer could move the read pointer past the
        // buffer — and the read is no longer provably safe: it refutes with an out-of-bounds counterexample.
        [group: 'P-ring', name: 'weak rely allows out-of-bounds read', expect: 'bounds',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ old.tail <= tail && tail <= values.length })   // dropped head == old.head
                       void relyOnWriter() {}

                       @Requires({ head < tail })
                       int read() {
                           relyOnWriter()
                           int v = values[head]
                           head = head + 1
                           return v
                       }
                   }''')],
        // Orchestration: @UnderRely is the DECLARATIVE rely-step — the transform prepends the relyOnWriter() call,
        // so the body is pure logic, yet it verifies identically to the hand-written form (read is in bounds).
        [group: 'P-ring', name: 'concurrent read in bounds via @UnderRely', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head == old.head && old.tail <= tail && tail <= values.length })
                       void relyOnWriter() {}

                       @Requires({ head < tail })
                       @UnderRely('relyOnWriter')
                       int read() {
                           int v = values[head]              // no hand-written relyOnWriter() call
                           head = head + 1
                           return v
                       }
                   }''')],
        // …and it stays sound: a weak rely via @UnderRely still refutes the out-of-bounds read.
        [group: 'P-ring', name: '@UnderRely weak rely allows out-of-bounds read', expect: 'bounds',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ old.tail <= tail && tail <= values.length })   // dropped head == old.head
                       void relyOnWriter() {}

                       @Requires({ head < tail })
                       @UnderRely('relyOnWriter')
                       int read() {
                           int v = values[head]
                           head = head + 1
                           return v
                       }
                   }''')],
        // Synthesis: NO hand-written rely-step method. @UnderRely('Writer') finds the @Rely('Writer') predicate
        // and the transform synthesises the rely-step ($rely$Writer) — @Modifies [head,tail] + @Ensures (predicate
        // with oldX→old.field, conjoined with the class invariant). The read still verifies in bounds.
        [group: 'P-ring', name: 'rely-step synthesised from @Rely predicate', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ head < tail })
                       @UnderRely('Writer')
                       int read() {
                           int v = values[head]              // no rely-step method, no rely call — both synthesised
                           head = head + 1
                           return v
                       }
                   }''')],
        // Multi-access placement: a body with SEVERAL shared accesses (not one atomic critical section). The
        // transform inserts a rely-step before EACH access to head — so the environment is modelled between them,
        // not just at entry — and all reads still verify in bounds (the writer keeps head across every step).
        [group: 'P-ring', name: 'multi-access body: rely-step before each shared read', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ head < tail })
                       @UnderRely('Writer')
                       int readTwice() {
                           int a = values[head]              // shared read 1 (rely-step before)
                           int b = values[head]              // shared read 2 (another rely-step before)
                           return a + b
                       }
                   }''')],
        // Soundness — masking: a write that TRANSIENTLY breaks the invariant, followed by another shared op (so a
        // rely-step is inserted between them), must still refute. Without the post-write invariant assertion the
        // following rely-step would re-assume the invariant — modelling the environment as "repairing" the broken
        // state — and the violation would be silently masked. The synthesised `assert <invariant>` after the write
        // closes that hole.
        [group: 'P-ring', name: 'transient invariant violation between shared writes refutes', expect: 'Assertion may not hold',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ head < tail })
                       @UnderRely('Writer')
                       void sneaky() {
                           head = tail + 1               // breaks the invariant (head > tail) — TRANSIENTLY
                           head = 0                      // …then "repairs" head, but a rely-step ran in between
                       }
                   }''')],
        // Nested control flow: a shared access INSIDE an if-branch is instrumented (a rely-step before the `if`
        // for the guard, and before the access inside the branch). With `head < tail` guaranteed by the guard, the
        // read is in bounds. (Placement recurses into branches, not just the top-level statement list.)
        [group: 'P-ring', name: 'nested if-branch shared read is in bounds', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @UnderRely('Writer')
                       int readIfAvailable() {
                           if (head < tail) {            // guard references shared state → rely-step before the if
                               int v = values[head]      // shared read inside the branch → rely-step before it
                               head = head + 1
                               return v
                           }
                           return -1
                       }
                   }''')],
        // …and the branch's access is genuinely checked: a `head <= tail` guard admits head == tail == capacity, so
        // the in-branch read refutes out-of-bounds (the rely inside the branch doesn't paper over it).
        [group: 'P-ring', name: 'nested if-branch unsafe read refutes', expect: 'bounds',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @UnderRely('Writer')
                       int readWrong() {
                           if (head <= tail) {           // <= admits head == tail (== capacity) → out of bounds
                               int v = values[head]
                               return v
                           }
                           return -1
                       }
                   }''')],
        // A body whose write BREAKS the invariant must refute: the synthesised post-write invariant assertion fires
        // (head > tail), so the violation is caught at the write rather than masked or only seen at exit.
        [group: 'P-ring', name: 'invariant-breaking write refutes', expect: 'Assertion may not hold',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ head < tail })
                       @UnderRely('Writer')
                       void breakIt() { head = tail + 1 }     // head > tail violates the class invariant
                   }''')],
        // …and a weak @Rely predicate (drop head == oldHead) synthesises a rely that no longer protects the read.
        [group: 'P-ring', name: 'synthesised weak @Rely allows out-of-bounds read', expect: 'bounds',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Rely('Writer')
                       static boolean rWriter(int oldHead, int oldTail, int head, int tail) {
                           oldHead <= head && oldTail <= tail
                       }
                       @Requires({ head < tail })
                       @UnderRely('Writer')
                       int read() {
                           int v = values[head]
                           head = head + 1
                           return v
                       }
                   }''')],
        // Symmetric: weaken the writer's rely — drop `tail == old.tail`, so the reader could move the write
        // pointer past capacity — and the append refutes with an out-of-bounds counterexample.
        [group: 'P-ring', name: 'weak rely allows out-of-bounds write', expect: 'bounds',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Ring {
                       int head
                       int tail
                       int[] values
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ old.head <= head && head <= tail })   // dropped tail == old.tail
                       void relyOnReader() {}

                       @Requires({ tail < values.length })
                       void write(int x) {
                           relyOnReader()
                           values[tail] = x
                           tail = tail + 1
                       }
                   }''')],

        [group: 'P-ring', name: 'README flagship: rely/guarantee Buffer (read + write)', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })   // the bounded-buffer invariant
class Buffer {
    int head, tail
    int[] values

    @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) {
        head == oldHead && oldTail <= tail       // the producer keeps my read pointer, only grows the buffer
    }
    @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) {
        head == oldHead && oldTail <= tail       // I never move head; I only append
    }
    @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) {
        tail == oldTail                          // the consumer keeps my write pointer
    }
    @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) {
        tail == oldTail && oldHead <= head       // I never move tail; I only advance head
    }

    @Requires({ head < tail })                   // an element is available
    @UnderRely('Consumer')                       // run under the consumer's rely (rCons) — synthesised + framed
    int read() {
        int v = values[head]                     // ← PROVEN in bounds despite the concurrent producer
        head = head + 1
        return v
    }
    @Requires({ tail < values.length })          // room to append
    @UnderRely('Producer')                       // run under the producer's rely (rProd)
    void write(int x) {
        values[tail] = x                         // ← PROVEN in bounds despite the concurrent consumer
        tail = tail + 1
    }
}''')],
    ]
}
