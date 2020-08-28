// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

//-
// AXI (user fields) modifications:
//     Copyright (c) 2019 Alexandre Joannou
//     Copyright (c) 2019 Peter Rugg
//     Copyright (c) 2019 Jonathan Woodruff
//     All rights reserved.
//
//     This software was developed by SRI International and the University of
//     Cambridge Computer Laboratory (Department of Computer Science and
//     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
//     DARPA SSITH research programme.
//-

package Boot_ROM;

// ================================================================
// This package implements a slave IP that is a RISC-V boot ROM of
// 1024 32b locations.
// - Ignores all writes, always responsing OKAY
// - Assumes all reads are 4-byte aligned requests for 4-bytes

// ================================================================

export Boot_ROM_IFC (..), mkBoot_ROM;

// ================================================================
// BSV library imports

import ConfigReg :: *;

// ----------------
// BSV additional libs

import Cur_Cycle  :: *;
import GetPut_Aux :: *;
import Semi_FIFOF :: *;
import AXI4       :: *;
import SourceSink :: *;

// ================================================================
// Project imports

import Fabric_Defs :: *;
import SoC_Map     :: *;

// ================================================================
// Include the auto-generated BSV-include file with the ROM function

`ifdef RV32
`include  "fn_read_ROM_RV32.bsvi"
`endif

`ifdef RV64
`include  "fn_read_ROM_RV64.bsvi"
`endif

// ================================================================
// Interface

interface Boot_ROM_IFC;
   // set_addr_map should be called after this module's reset
   method Action set_addr_map (Fabric_Addr addr_base, Fabric_Addr addr_lim);
   // Main Fabric Reqs/Rsps
   interface AXI4_Slave #(Wd_SId, Wd_Addr, Wd_Data_Periph, 0, 0, 0, 0, 0)
      slave;
endinterface

// ================================================================

(* synthesize *)
module mkBoot_ROM (Boot_ROM_IFC);

   // Verbosity: 0: quiet; 1: reads/writes
   Integer verbosity = 0;

   Reg #(Bool) rg_module_ready <- mkReg (False);

   Reg #(Fabric_Addr)  rg_addr_base <- mkRegU;
   Reg #(Fabric_Addr)  rg_addr_lim  <- mkRegU;

   // ----------------
   // Connector to fabric

   let slavePortShim <- mkAXI4ShimFF;

   // ----------------

   function Bool fn_addr_is_aligned (Fabric_Addr addr, AXI4_Size arsize);
      if      (arsize == 1)  return True;
      else if (arsize == 2)  return (addr [0] == 1'b_0);
      else if (arsize == 4)  return (addr [1:0] == 2'b_00);
      else if (arsize == 8)  return (addr [2:0] == 3'b_000);
      else return False;
   endfunction

   function Bool fn_addr_is_in_range (Fabric_Addr base, Fabric_Addr addr, Fabric_Addr lim);
      return ((base <= addr) && (addr < lim));
   endfunction

   function Bool fn_addr_is_ok (Fabric_Addr base, Fabric_Addr addr, Fabric_Addr lim, AXI4_Size arsize);
      return (   fn_addr_is_aligned (addr, arsize)
	      && fn_addr_is_in_range (base, addr, lim));
   endfunction

   // ================================================================
   // BEHAVIOR

   // ----------------------------------------------------------------
   // Handle fabric read requests

   rule rl_process_rd_req (rg_module_ready);
      let rda <- get(slavePortShim.master.ar);

      // Byte offset, aligned to 4-byte boundary
      let byte_offset = ((rda.araddr - rg_addr_base) & (~ 'h_3));

      AXI4_Resp  rresp  = OKAY;
      Bit #(64)  data64 = 0;

      if (! fn_addr_is_ok (rg_addr_base, rda.araddr, rg_addr_lim, rda.arsize)) begin
	 rresp = SLVERR;
	 $display ("%0d: ERROR: Boot_ROM.rl_process_rd_req: unrecognized or misaligned addr",
		   cur_cycle);
	 $display ("    ", fshow (rda));
      end
      else if (byte_offset [2] == 1'b_0) begin
	 // Addr is in lower 4-bytes of 8-byte word
	 Bit #(32) d0 = fn_read_ROM_0 (byte_offset);
	 Bit #(32) d1 = fn_read_ROM_4 (byte_offset + 4);
	 data64 = { d1, d0 };
      end
      else begin
	 // Addr is in upper 4-bytes of 8-byte word
	 Bit #(32) d1 = fn_read_ROM_4 (byte_offset);
	 if (valueOf (Wd_Data) == 32)
	    data64 = { 0, d1 };
	 else if (valueOf (Wd_Data) == 64)
	    data64 = { d1, 0 };
      end


      Bit #(Wd_Data_Periph) rdata  = truncate (data64);
      AXI4_RFlit#(Wd_SId, Wd_Data_Periph, 0) rdr = AXI4_RFlit {rid:   rda.arid,
			      rdata: rdata,
			      rresp: rresp,
			      rlast: True,
			      ruser: 0};
      slavePortShim.master.r.put(rdr);

      if (verbosity > 0) begin
	 $display ("%0d: Boot_ROM.rl_process_rd_req: ", cur_cycle);
	 $display ("        ", fshow (rda));
	 $display ("     => ", fshow (rdr));
      end
   endrule

   // ----------------------------------------------------------------
   // Handle fabric write requests: ignore all of them (this is a ROM)

   rule rl_process_wr_req (rg_module_ready);
      let wra <- get(slavePortShim.master.aw);
      let wrd <- get(slavePortShim.master.w);

      AXI4_Resp  bresp = OKAY;
      if (! fn_addr_is_ok (rg_addr_base, wra.awaddr, rg_addr_lim, wra.awsize)) begin
	 bresp = SLVERR;
	 $display ("%0d: ERROR: Boot_ROM.rl_process_wr_req: unrecognized or misaligned addr",
		   cur_cycle);
	 $display ("    ", fshow (wra));
      end

      AXI4_BFlit#(Wd_SId, 0) wrr = AXI4_BFlit {bid:   wra.awid,
			                       bresp: bresp,
			                       buser: 0};
      slavePortShim.master.b.put(wrr);

      if (verbosity > 0) begin
	 $display ("%0d: Boot_ROM.rl_process_wr_req; ignoring all writes", cur_cycle);
	 $display ("        ", fshow (wra));
	 $display ("        ", fshow (wrd));
	 $display ("     => ", fshow (wrr));
      end
   endrule

   // ================================================================
   // INTERFACE

   // set_addr_map should be called after this module's reset
   method Action  set_addr_map (Fabric_Addr addr_base, Fabric_Addr addr_lim);
      if (valueOf (Wd_Data_Periph) == 32) begin
	 if (addr_base [1:0] != 0)
	    $display ("%0d: WARNING: Boot_ROM.set_addr_map: addr_base 0x%0h is not 4-Byte-aligned",
		      cur_cycle, addr_base);

	 if (addr_lim [1:0] != 0)
	    $display ("%0d: WARNING: Boot_ROM.set_addr_map: addr_lim 0x%0h is not 4-Byte-aligned",
		      cur_cycle, addr_lim);
      end
      else if (valueOf (Wd_Data_Periph) == 64) begin
	 if (addr_base [2:0] != 0)
	    $display ("%0d: WARNING: Boot_ROM.set_addr_map: addr_base 0x%0h is not 4-Byte-aligned",
		      cur_cycle, addr_base);

	 if (addr_lim [2:0] != 0)
	    $display ("%0d: WARNING: Boot_ROM.set_addr_map: addr_lim 0x%0h is not 4-Byte-aligned",
		      cur_cycle, addr_lim);
      end

      rg_addr_base    <= addr_base;
      rg_addr_lim     <= addr_lim;
      rg_module_ready <= True;
      slavePortShim.clear;
      if (verbosity > 0) begin
	 $display ("%0d: Boot_ROM.set_addr_map: base 0x%0h lim 0x%0h", cur_cycle, addr_base, addr_lim);
      end
   endmethod

   // Main Fabric Reqs/Rsps
   interface  slave = slavePortShim.slave;
endmodule

// ================================================================

endpackage
