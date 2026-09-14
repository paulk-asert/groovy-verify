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
import org.junit.jupiter.api.Test
import verification.ScribbleExport

import static org.junit.jupiter.api.Assertions.assertEquals
import static org.junit.jupiter.api.Assertions.assertNull
import static org.junit.jupiter.api.Assertions.assertTrue

/** Phase 270 — the Scribble exporter: golden outputs for the standard fragment, refusals for what is beyond it. */
class ScribbleExportTest {

    @Test
    void requestReplyLoopBecomesRecContinue() {
        List<String> errors = []
        String scr = ScribbleExport.export('ReqReply', ScribbleExport.CORPUS.ReqReply, errors)
        assertEquals([], errors)
        assertEquals('''global protocol ReqReply(role client, role server) {
    rec X1 {
        request() from client to server;
        reply() from server to client;
        continue X1;
    }
}
''', scr)
    }

    @Test
    void choiceAtIsScribbleVerbatim() {
        List<String> errors = []
        String scr = ScribbleExport.export('CalcChoice', ScribbleExport.CORPUS.CalcChoice, errors)
        assertEquals([], errors)
        assertEquals('''global protocol CalcChoice(role client, role server) {
    rec X1 {
        choice at client {
            add() from client to server;
            sum() from server to client;
            continue X1;
        } or {
            neg() from client to server;
            res() from server to client;
            continue X1;
        }
    }
}
''', scr)
    }

    @Test
    void parUsesScribbleJavaSyntax() {
        List<String> errors = []
        String scr = ScribbleExport.export('FairServerPar', ScribbleExport.CORPUS.FairServerPar, errors)
        assertEquals([], errors)
        assertEquals('''global protocol FairServerPar(role clientA, role server, role clientB) {
    par {
        rec X1 {
            reqA() from clientA to server;
            replyA() from server to clientA;
            continue X1;
        }
    } and {
        rec X2 {
            reqB() from clientB to server;
            replyB() from server to clientB;
            continue X2;
        }
    }
}
''', scr)
    }

    @Test
    void thePrimedRingKeepsItsPrimingFirst() {
        List<String> errors = []
        String scr = ScribbleExport.export('PrimedRing', ScribbleExport.CORPUS.PrimedRing, errors)
        assertEquals([], errors)
        assertTrue(scr.startsWith('''global protocol PrimedRing(role a, role b, role c) {
    ab() from a to b;
    rec X1 {'''))
    }

    /** Phase 293 — an actor role exports as an ordinary Scribble role, its literal messages as ordinary labels. */
    @Test
    void anActorRoleIsAnOrdinaryScribbleRole() {
        List<String> errors = []
        String scr = ScribbleExport.export('ActorConnection', ScribbleExport.CORPUS.ActorConnection, errors)
        assertEquals([], errors)
        assertEquals('''global protocol ActorConnection(role client, role gate) {
    login() from client to gate;
    auth_ok() from client to gate;
    rec X1 {
        cmd() from client to gate;
        continue X1;
    }
}
''', scr)
    }

    /** Phase 295 — an actor that REPLIES is still an ordinary Scribble role: its reply is a message from it. */
    @Test
    void anActorsReplyIsAnOrdinaryScribbleMessage() {
        List<String> errors = []
        String scr = ScribbleExport.export('ActorKeyValue', ScribbleExport.CORPUS.ActorKeyValue, errors)
        assertEquals([], errors)
        assertEquals('''global protocol ActorKeyValue(role client, role gate) {
    rec X1 {
        choice at client {
            get() from client to gate;
            value() from gate to client;
            continue X1;
        } or {
            put() from client to gate;
            ok() from gate to client;
            continue X1;
        }
    }
}
''', scr)
    }

    /** Phase 293 — `connect` is a Scribble reserved word (measured with nuscr): refused with a note naming it,
     *  rather than exported as a file nuScr cannot parse. */
    @Test
    void aReservedWordLabelIsRefusedNotExportedBroken() {
        List<String> errors = []
        String scr = ScribbleExport.export('Docs', 'connect: client -> gate; auth_ok: client -> gate', errors)
        assertNull(scr)
        assertTrue(errors.any { it.contains("'connect' is a reserved word in Scribble") }, "got: ${errors}")
    }

    @Test
    void aMixedChoiceIsRefusedAsOutsideStandardScribble() {
        List<String> errors = []
        String scr = ScribbleExport.export('MixedPingPong', ScribbleExport.CORPUS.MixedPingPong, errors)
        assertNull(scr)
        assertTrue(errors.any { it.contains('outside standard Scribble') })
    }
}
