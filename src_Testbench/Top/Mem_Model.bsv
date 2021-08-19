// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved
//-
// RVFI_DII modifications:
//     Copyright (c) 2018 Peter Rugg
//     All rights reserved.
//
//     This software was developed by SRI International and the University of
//     Cambridge Computer Laboratory (Department of Computer Science and
//     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
//     DARPA SSITH research programme.
//-

package Mem_Model;

// ================================================================
// A simulation model of external DRAM memory.
// Uses a register file to model memory.

// ================================================================
// BSV library imports

import  RegFile      :: *;
import  Vector       :: *;
import  FIFOF        :: *;
import  GetPut       :: *;
import  ClientServer :: *;
import  Memory       :: *;

// ----------------
// BSV additional libs

import Cur_Cycle  :: *;
import GetPut_Aux :: *;

// ================================================================
// Project imports

import Mem_Controller :: *;
`ifdef RVFI_DII
import RVFI_DII :: *;
`endif

// ================================================================
// Mem Model interface

interface Mem_Model_IFC;
   // The read/write interface
   interface  MemoryServer #(Bits_per_Raw_Mem_Addr, Bits_per_Raw_Mem_Word)  mem_server;
endinterface

typedef 'h4000_0000 Bytes_Per_Mem;
`ifdef RVFI_DII
typedef 'h0000_0000 Zeroed_0_start;
typedef RVFI_DII_Mem_Size Zeroed_0_end;
typedef 'h3f00_0000 Zeroed_1_start;
typedef 'h3fff_ff00 Zeroed_1_end;
typedef 32 Num_regs;
`endif

// ================================================================
// Mem Model implementation


(* synthesize *)
module mkMem_Model (Mem_Model_IFC);
   Mem_Model_Gen_IFC#( Bits_per_Raw_Mem_Addr, Bits_per_Raw_Mem_Word
`ifdef RVFI_DII
                     , Zeroed_0_start, Zeroed_0_end
                     , Zeroed_1_start, Zeroed_1_end
`endif
                     ) mem_model
      <- mkMem_Model_General (valueOf (Bytes_Per_Mem));
   interface mem_server = mem_model.mem_server;
endmodule

interface Mem_Model_Gen_IFC #( numeric type addr_
                             , numeric type word_
`ifdef RVFI_DII
                             , numeric type zeroed_0_start_
                             , numeric type zeroed_0_end_
                             , numeric type zeroed_1_start_
                             , numeric type zeroed_1_end_
`endif
                             );
   interface MemoryServer #( addr_, word_) mem_server;
endinterface

// Raw_Mem_Addr -> Bit #(addr_)
module mkMem_Model_General #(Integer size)
                            (Mem_Model_Gen_IFC #( addr_, word_
`ifdef RVFI_DII
                                                , zeroed_0_start_, zeroed_0_end_
                                                , zeroed_1_start_, zeroed_1_end_
`endif
                                                ))
                             provisos ( Add#(a__, 5, addr_));

   Integer verbosity = 1;    // 0 = quiet; 1 = verbose

   //Raw_Mem_Addr alloc_size = fromInteger(valueOf(TDiv#(TMul#(size,8), word_))); //(raw mem words)
   Bit #(addr_) alloc_size = fromInteger (size * 8 / valueOf (word_) - 1);

`ifdef RVFI_DII
   Integer num_regs = valueOf (Num_regs);
   Bit #(addr_) zeroed_0_start = fromInteger(valueOf(TDiv#(zeroed_0_start_, TDiv#(word_, 8))));
   Bit #(addr_) zeroed_0_end   = fromInteger(valueOf(TDiv#(zeroed_0_end_, TDiv#(word_, 8))));
   Bit #(addr_) zeroed_1_start = fromInteger(valueOf(TDiv#(zeroed_1_start_, TDiv#(word_, 8))));
   Bit #(addr_) zeroed_1_end   = fromInteger(valueOf(TDiv#(zeroed_1_end_, TDiv#(word_, 8))));

   RegFile #(Bit #(addr_), Bit #(word_)) rf <- mkRegFile (0, alloc_size);
   //zeroes register allows quick resetting of memory. If bit of zeroes is 0 then corresponding entry of rf is 0.
   //Reg#(Bit#(TDiv#(TSub#(zeroed_0_end_, zeroed_0_start_), TDiv#(word_, 8)))) zeroes_0 <- mkReg(0);
   //Reg#(Bit#(TDiv#(TSub#(zeroed_1_end_, zeroed_1_start_), TDiv#(word_, 8)))) zeroes_1 <- mkReg(0);
   Vector #(32, Reg #(Bit #(TDiv #(TDiv #(TSub #(zeroed_0_end_, zeroed_0_start_), TDiv #(word_, 8)), Num_regs)))) v_zeroes_0 = newVector;
   Vector #(32, Reg #(Bit #(TDiv #(TDiv #(TSub #(zeroed_1_end_, zeroed_1_start_), TDiv #(word_, 8)), Num_regs)))) v_zeroes_1 = newVector;
   for (Integer i = 0; i < num_regs; i = i+1) begin
      v_zeroes_0[i] <- mkReg (0);
      v_zeroes_1[i] <- mkReg (0);
   end
   Integer addr_offset = log2 (num_regs);

`else
   RegFile #(Bit #(addr_), Bit #(word_)) rf <- mkRegFileLoad ("Mem.hex", 0, alloc_size - 1);
`endif

   FIFOF #(MemoryResponse #(word_))  f_raw_mem_rsps <- mkFIFOF;

   // ----------------------------------------------------------------
   // INTERFACE

   interface MemoryServer mem_server;
      interface Put request;
	 method Action put (MemoryRequest  #(addr_, word_) req);
	    if (req.address >= alloc_size) begin
	       $display ("%0d: ERROR: Mem_Model.request.put: addr 0x%0h >= size 0x%0h (num raw-mem words)",
			 cur_cycle, req.address, alloc_size);
	       //$finish (1);    // Assertion failure: address out of bounds
	    end
	    else if (req.write) begin
`ifdef RVFI_DII
            let z0_reg_addr = (req.address - zeroed_0_start) >> addr_offset;
            let z1_reg_addr = (req.address - zeroed_1_start) >> addr_offset;
            Bit #(TLog #(Num_regs)) z0_vector_addr = truncate (req.address - zeroed_0_start);
            Bit #(TLog #(Num_regs)) z1_vector_addr = truncate (req.address - zeroed_1_start);
            if (req.address >= zeroed_0_start && req.address < zeroed_0_end && v_zeroes_0[z0_vector_addr][z0_reg_addr] == 0) begin
                v_zeroes_0[z0_vector_addr][z0_reg_addr] <= 1;
                //v_zeroes_0[req.address - zeroed_0_start] <= 1;
                if (verbosity != 0) begin
                   $display ("    data unzeroed in z0, vec addr: ", fshow (z0_vector_addr), "  reg addr: ", fshow (z0_reg_addr));
                end
            end
            if (req.address >= zeroed_1_start && req.address < zeroed_1_end && v_zeroes_1[z1_vector_addr][z1_reg_addr] == 0) begin
                v_zeroes_1[z1_vector_addr][z1_reg_addr] <= 1;
                //v_zeroes_1[req.address - zeroed_1_start] <= 1;
                if (verbosity != 0) begin
                   $display ("    data unzeroed in z1, vec addr: ", fshow (z1_vector_addr), "  reg addr: ", fshow (z1_reg_addr));
                end
            end
`endif
            rf.upd (req.address, req.data);
	       if (verbosity != 0)
		  $display ("%0d: Mem_Model write [0x%0h] <= 0x%0h", cur_cycle, req.address, req.data);
	    end
	    else begin
	       let x = rf.sub (req.address);
`ifdef RVFI_DII
           $display("req addr: ", fshow(req.address), ", zeroed_0_start: ", fshow(zeroed_0_start), ", zeroed_1_start: ", fshow(zeroed_1_start));
           let z0_reg_addr = (req.address - zeroed_0_start) >> addr_offset;
           let z1_reg_addr = (req.address - zeroed_1_start) >> addr_offset;
           Bit #(TLog #(Num_regs)) z0_vector_addr = truncate (req.address - zeroed_0_start);
           Bit #(TLog #(Num_regs)) z1_vector_addr = truncate (req.address - zeroed_1_start);
           if (req.address < zeroed_0_end && req.address >= zeroed_0_start && v_zeroes_0[z0_vector_addr][z0_reg_addr] == 0) begin
              x = 0;
              if (verbosity != 0) begin
                 $display ("    data zeroed by z0, vec addr: ", fshow (z0_vector_addr), "  reg addr: ", fshow (z0_reg_addr));
              end
           end
           if (req.address < zeroed_1_end && req.address >= zeroed_1_start && v_zeroes_1[z1_vector_addr][z1_reg_addr] == 0) begin
              x = 0;
              if (verbosity != 0) begin
                 $display ("    data zeroed by z1, vec addr: ", fshow (z1_vector_addr), "  reg addr: ", fshow (z1_reg_addr));
              end
           end
`endif
	       let rsp = MemoryResponse {data: x};
	       f_raw_mem_rsps.enq (rsp);
	       if (verbosity != 0)
		  $display ("%0d: Mem_Model read  [0x%0h] => 0x%0h", cur_cycle, req.address, x);
	    end
	 endmethod
      endinterface

      interface Get response = toGet (f_raw_mem_rsps);
   endinterface
endmodule

// ================================================================

endpackage
