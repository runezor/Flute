
// Copyright (c) 2021 Jonathan Woodruff
//
// All rights reserved.
//
// This software was developed by SRI International and the University of
// Cambridge Computer Laboratory (Department of Computer Science and
// Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
// DARPA SSITH research programme.
//
// This work was supported by NCSC programme grant 4212611/RFA 15971 ("SafeBet").
//
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

import DReg::*;
import ConfigReg::*;
import RegFile::*;
import Vector::*;
import MEM::*;
import FIFOF::*;

typedef struct {
    ky key;
    ix index;
} MapKeyIndex#(type ky, type ix) deriving(Bits, Eq, FShow);
typedef struct {
    ky key;
    vl value;
} MapKeyValue#(type ky, type vl) deriving(Bits, Eq, FShow);
typedef struct {
    ky key;
    ix index;
    vl value;
} MapKeyIndexValue#(type ky, type ix, type vl) deriving(Bits, Eq, FShow);

// Type parameters are for index and key (which together are the "address"),
// the value stored in the map, and the associativity of the storage.
interface Map#(type ky, type ix, type vl, numeric type as);
    method Action update(MapKeyIndex#(ky,ix) key, vl value);
    method Action updateWithFunc(MapKeyIndex#(ky,ix) ki, vl value, function vl up(vl old_v, vl new_v), Bool insert);
    method Maybe#(vl) lookup(MapKeyIndex#(ky,ix) lookup_key);
    method Action clear;
    method Bool clearDone;
endinterface

module mkMapLossy#(vl default_value)(Map#(ky,ix,vl,as)) provisos (
Bits#(ky,ky_sz), Bits#(vl,vl_sz), Eq#(ky), Arith#(ky),
Bounded#(ix), Literal#(ix), Bits#(ix, ix_sz),
Bitwise#(ix), Eq#(ix), Arith#(ix));
    Vector#(as, RegFile#(ix, MapKeyValue#(ky,vl))) mem
        <- replicateM(mkRegFileWCF(0, maxBound));
    Reg#(Bit#(TLog#(as))) wayNext <- mkReg(0);
    Integer a = valueof(as);

    Reg#(Bool) clearReg <- mkReg(False);
    Reg#(ix) clearCount <- mkReg(0);
    PulseWire didUpdate <- mkPulseWire;
    rule doClear(clearReg && !didUpdate);
        for (Integer i = 0; i < a; i = i + 1) mem[i].upd(clearCount, unpack(0));
        clearCount <= clearCount + 1;
        if (clearCount == ~0) clearReg <= False;
    endrule

    function Action doUpdate(MapKeyIndex#(ky,ix) ki, vl value, function vl up(vl old_v, vl new_v), Bool insert);
    action
        Bool found = False;
        Bit#(TLog#(as)) way = wayNext;
        vl old_value = default_value;
        if (a > 1) begin
            for (Integer i = 0; i < a; i = i + 1) begin
                MapKeyValue#(ky,vl) entry = mem[i].sub(ki.index);
                if (entry.key == ki.key) begin
                    found = True;
                    way = fromInteger(i);
                    old_value = entry.value;
                end
            end
        end
        if (found || insert) mem[way].upd(ki.index, MapKeyValue{key: ki.key, value: up(old_value, value)});
        wayNext <= (wayNext == fromInteger(a-1)) ? 0: wayNext + 1;
        didUpdate.send;
    endaction
    endfunction

    function vl returnNew(vl old_v, vl new_v) = new_v;
    method Action update(MapKeyIndex#(ky,ix) ki, vl value) = doUpdate(ki, value, returnNew, True);
    method Action updateWithFunc(MapKeyIndex#(ky,ix) ki, vl value, function vl up(vl old_v, vl new_v), Bool insert) =
        doUpdate(ki, value, up, insert);

    method Maybe#(vl) lookup(MapKeyIndex#(ky,ix) lu);
        Maybe#(vl) ret = Invalid;
        for (Integer i = 0; i < a; i = i + 1) begin
            let rd = mem[i].sub(lu.index);
            if (rd.key == lu.key && !clearReg) ret = Valid(rd.value);
        end
        return ret;
    endmethod
    method clear if (!clearReg) = clearReg._write(True);
    method clearDone = !clearReg;
endmodule

interface MapSplit#(type ky, type ix, type vl, numeric type as);
    method Action update(MapKeyIndex#(ky,ix) key, vl value);
    method Action lookupStart(MapKeyIndex#(ky,ix) lookup_key);
    method Maybe#(vl) lookupRead;
    method Action clear;
    method Bool clearDone;
endinterface

module mkMapLossyBRAM(MapSplit#(ky,ix,vl,as)) provisos (
Bits#(ky,ky_sz), Bits#(vl,vl_sz), Eq#(ky), Arith#(ky),
Bounded#(ix), Literal#(ix), Bits#(ix, ix_sz),
Bitwise#(ix), Eq#(ix), Arith#(ix), PrimIndex#(ix, a__));
    Vector#(as, MEM#(ix, Maybe#(MapKeyValue#(ky,vl)))) mem <- replicateM(mkMEMCore);
    Vector#(as, MEM#(ix, Maybe#(ky))) updateKeys <- replicateM(mkMEMCore);
    Reg#(MapKeyIndex#(ky,ix)) lookupReg <- mkConfigReg(unpack(0));
    RWire#(MapKeyIndex#(ky,ix)) lookupWire <- mkRWire;
    FIFOF#(void) clearReqQ <- mkUGFIFOF1;
    Reg#(Maybe#(MapKeyIndexValue#(ky,ix,vl))) updateReg <- mkReg(Invalid);
    Reg#(Bool)                                updateRegFresh <- mkDReg(False);
    RWire#(MapKeyIndexValue#(ky,ix,vl)) updateWire <- mkRWire;
    Reg#(Bit#(TLog#(as))) wayNext <- mkConfigReg(0);
    Integer a = valueof(as);

    Reg#(ix) clearIx <- mkConfigReg(0);
    (* fire_when_enabled, no_implicit_conditions *)
    rule updateCanonClear;
        if (clearReqQ.notEmpty) begin
            for (Integer i = 0; i < a; i = i + 1) mem[i].write(clearIx, Invalid);
            for (Integer i = 0; i < a; i = i + 1) updateKeys[i].write(clearIx, Invalid);
            clearIx <= clearIx + 1;
            if (clearIx == ~0) clearReqQ.deq;
        end else if (updateReg matches tagged Valid .u &&& updateRegFresh) begin
            Bit#(TLog#(as)) way = wayNext;
            for (Integer i = 0; i < a; i = i + 1)
                if (updateKeys[i].read.peek() matches tagged Valid .k &&& u.key == k)
                    way = fromInteger(i);
            // Always write to both the main memory bank and the copy used for updates.
            $display("MapUpdate - index: %x, key: %x, value: %x, way: %x",
                     u.index, u.key, u.value, way);
            mem[way].write(u.index, Valid(MapKeyValue{key: u.key, value: u.value}));
            updateKeys[way].write(u.index, Valid(u.key));
            wayNext <= (wayNext == fromInteger(a-1)) ? 0 : (wayNext + 1);
        end
        MapKeyIndex#(ky,ix) ki = fromMaybe(lookupReg, lookupWire.wget);
        for (Integer i = 0; i < a; i = i + 1) mem[i].read.put(ki.index);
        lookupReg <= ki;
    endrule

    rule writeUpdateReg;
        ix updateIdx = (fromMaybe(?,updateReg)).index;
        if (clearReqQ.notEmpty) updateReg <= Invalid;
        else if (updateWire.wget matches tagged Valid .uw) begin
            updateReg <= Valid(uw);
            updateRegFresh <= True;
            updateIdx = uw.index;
        end
        for (Integer i = 0; i < a; i = i + 1) updateKeys[i].read.put(updateIdx);
    endrule

    method Action update(MapKeyIndex#(ky,ix) ki, vl value);
        updateWire.wset(MapKeyIndexValue{key: ki.key, index: ki.index, value: value});
    endmethod
    method Action lookupStart(MapKeyIndex#(ky,ix) ki);
        lookupWire.wset(ki);
        $display("MapLookup - index: %x, key: %x",
                 ki.index, ki.key);
    endmethod
    method Maybe#(vl) lookupRead;
        Maybe#(vl) readVal = Invalid;
        if (!clearReqQ.notEmpty) begin
            for (Integer i = 0; i < a; i = i + 1) begin
                if (mem[i].read.peek() matches tagged Valid .r &&& lookupReg.key == r.key)
                    readVal = Valid(r.value);
            end
        end
        if (updateReg matches tagged Valid .u &&& lookupReg.index == u.index && lookupReg.key == u.key)
            readVal = Valid(u.value);
        return readVal;
    endmethod
    method Action clear;
        if (clearReqQ.notFull) clearReqQ.enq(?);
    endmethod
    method clearDone = !clearReqQ.notEmpty;
endmodule
