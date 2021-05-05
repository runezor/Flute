// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved.

// Near_Mem_IFC is an abstraction of two alternatives: caches or TCM
// (TCM = Tightly Coupled Memory).  Both are memories that are
// 'near' the CPU (1-cycle access in common case).

// On the CPU side it directly services instruction fetches and DMem
// reads and writes.

// On the Fabric side it has one or two Client sub-interfaces and a
// Server sub-interface.  The Client sub-interfaces are used to
// pass-through, to the fabric, I/O requests, cache-fill/ writeback
// requests, and any other memory requests outside the designated
// address range of Near_Mem.  There are two Client interfaces to
// accommodate IMem and DMem requests concurrently.

// This implementation of Near_Mem contains an ICache and a DCache
//        Fabric-side Server interface is not used (no back door to caches).

package Near_Mem_Caches;

// ================================================================
// BSV lib imports

import ConfigReg    :: *;
import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import Connectable  :: *;

// ----------------
// BSV additional libs

import Cur_Cycle  :: *;
import GetPut_Aux :: *;

// ================================================================
// Project imports

import ISA_Decls        :: *;
import Near_Mem_IFC     :: *;
import MMU_Cache_Common :: *;
import MMU_Cache        :: *;
import AXI4             :: *;
import Fabric_Defs      :: *;

`ifdef INCLUDE_DMEM_SLAVE
import MMU_Cache_Arbiter           :: *;
import AXI4_Lite_MMU_Cache_Adapter :: *;
`endif

// System address map and pc_reset value
import SoC_Map :: *;

// ================================================================
// Exports

export mkNear_Mem;

// ================================================================
// The module

// Module state
typedef enum {STATE_RESET, STATE_RESETTING, STATE_READY } State
deriving (Bits, Eq, FShow);

(* synthesize *)
module mkNear_Mem (Near_Mem_IFC);

   Reg #(Bit #(4)) cfg_verbosity <- mkConfigReg (2);
   Reg #(State)    rg_state      <- mkReg (STATE_READY);

   // ----------------
   // System address map and pc reset value
   SoC_Map_IFC  soc_map  <- mkSoC_Map;

   // Reset response queue
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   MMU_ICache_IFC  icache <- mkMMU_ICache;
   MMU_DCache_IFC  dcache <- mkMMU_DCache;
`ifdef INCLUDE_DMEM_SLAVE
   MMU_Cache_Arbiter_IFC #(2, Wd_MId_2x3) dcache_arbiter <- mkMMU_Cache_Arbiter (dcache);
   dcache = dcache_arbiter.v_from_masters [0];

   AXI4_Lite_MMU_Cache_Adapter_IFC dmem_slave_adapter <- mkAXI4_Lite_MMU_Cache_Adapter(dcache_arbiter.v_from_masters [1]);
`endif

   // ----------------------------------------------------------------
   // BEHAVIOR

   // ----------------
   // Reset
   // This reset state machine operates on external soft-reset request.

   rule rl_reset (rg_state == STATE_RESET);
      icache.server_reset.request.put (?);
      dcache.server_reset.request.put (?);
      rg_state <= STATE_RESETTING;

      if (cfg_verbosity > 1)
	 $display ("%0d: Near_Mem.rl_reset", cur_cycle);
   endrule

   rule rl_reset_complete (rg_state == STATE_RESETTING);
      let _dummy1 <- icache.server_reset.response.get;
      let _dummy2 <- dcache.server_reset.response.get;

      f_reset_rsps.enq (?);
      rg_state <= STATE_READY;

      if (cfg_verbosity > 1)
	 $display ("%0d: Near_Mem.rl_reset_complete", cur_cycle);
   endrule

   // ----------------
   // SFENCE_VMA

`ifdef ISA_PRIV_S
   FIFOF #(Token) f_sfence_vma_reqs <- mkFIFOF;
   FIFOF #(Token) f_sfence_vma_rsps <- mkFIFOF;

   rule rl_sfence_vma;
      let tok <- pop (f_sfence_vma_reqs);
      icache.tlb_flush;
      dcache.tlb_flush;
      f_sfence_vma_rsps.enq (tok);
   endrule
`endif

   // ----------------------------------------------------------------
   // INTERFACE

   // Reset
   interface Server server_reset;
      interface Put request;
	 method Action put (Token t) if (rg_state == STATE_READY);
	    rg_state <= STATE_RESET;
	 endmethod
      endinterface

      interface Get response;
	 method ActionValue #(Token) get ();
	    let rsp <- pop (f_reset_rsps);
	    return rsp;
	 endmethod
      endinterface
   endinterface

   // ----------------
   // IMem

   // CPU side
   interface IMem_IFC imem;
      // CPU side: IMem request
      method Action  req (Bit #(3) f3,
			  WordXL addr,
			  // The following  args for VM
			  Priv_Mode  priv,
			  Bit #(1)   sstatus_SUM,
			  Bit #(1)   mstatus_MXR,
			  WordXL     satp
`ifdef RVFI_DII
            , Dii_Id seq_req
`endif
      );    // { VM_Mode, ASID, PPN_for_page_table }
	 icache.req (CACHE_LD, f3, True,
`ifdef ISA_A
		     ?,
`endif
		     addr, tuple2 (False, ?), priv, sstatus_SUM, mstatus_MXR, satp);
      endmethod
      method Action commit = icache.commit;

      // CPU side: IMem response
      method Bool     valid          = icache.valid;
      method Bool     is_i32_not_i16 = True;
      method WordXL   pc             = icache.addr;
`ifdef RVFI_DII
      method Tuple2#(Instr,Dii_Id) instr =
         tuple2 (truncate (tpl_2 (icache.cword)), 0);
`else
      method Instr    instr          = truncate (tpl_2 (icache.cword));
`endif
      method Bool     exc            = icache.exc;
      method Exc_Code exc_code       = icache.exc_code;
      method WordXL   tval           = icache.addr;

`ifdef PERFORMANCE_MONITORING
      method EventsCache events = icache.events;
`endif
   endinterface

   // Fabric side
   interface imem_master = icache.mem_master;

   // ----------------
   // DMem

   // CPU side
   interface DMem_IFC dmem;
      // CPU side: DMem request
      method Action  req (CacheOp op,
			  Bit #(3) f3,
              Bool is_unsigned,
`ifdef ISA_A
			  Bit #(5) amo_funct5,
`endif
			  Addr addr,
              Tuple2#(Bool, Bit #(128)) store_value,
			  // The following  args for VM
			  Priv_Mode  priv,
			  Bit #(1)   sstatus_SUM,
			  Bit #(1)   mstatus_MXR,
			  WordXL     satp);    // { VM_Mode, ASID, PPN_for_page_table }
	 dcache.req (op, f3, is_unsigned,
`ifdef ISA_A
		     amo_funct5,
`endif
		     addr, store_value, priv, sstatus_SUM, mstatus_MXR, satp);
      endmethod
      method Action commit = dcache.commit;

      // CPU side: DMem response
      method Bool       valid      = dcache.valid;
      method Tuple2#(Bool, Bit #(128))  word128     = dcache.cword;
`ifdef ISA_A
      method Bit #(128)  st_amo_val = tpl_2(dcache.st_amo_val);
`endif
      method Bool       exc        = dcache.exc;
      method Exc_Code   exc_code   = dcache.exc_code;

`ifdef PERFORMANCE_MONITORING
      method EventsCache events = dcache.events;
`endif
   endinterface

   // Fabric side
   interface mem_master = dcache.mem_master;

`ifdef INCLUDE_DMEM_SLAVE
   interface dmem_slave = dmem_slave_adapter.from_master;
`endif

   // ----------------
   // FENCE.I: flush both ICache and DCache

   interface Server server_fence_i;
      interface Put request;
	 method Action put (Token t);
	    icache.server_flush.request.put (?);
	    dcache.server_flush.request.put (?);
	 endmethod
      endinterface
      interface Get response;
	 method ActionValue #(Token) get;
	    let ti <- icache.server_flush.response.get;
	    let td <- dcache.server_flush.response.get;
	    return ?;
	 endmethod
      endinterface
   endinterface

   // ----------------
   // FENCE: flush DCache

   interface Server server_fence;
      interface Put request;
	 method Action put (Fence_Ordering t);
	    dcache.server_flush.request.put (?);
	 endmethod
      endinterface
      interface Get response;
	 method ActionValue #(Token) get;
	    let td <- dcache.server_flush.response.get;
	    return ?;
	 endmethod
      endinterface
   endinterface

   // ----------------
   // SFENCE_VMA: flush TLBs

`ifdef ISA_PRIV_S
   interface Server sfence_vma_server = toGPServer (f_sfence_vma_reqs, f_sfence_vma_rsps);
`endif

   // ----------------------------------------------------------------
   // Interface to 'coherent DMA' port of optional L2 cache
   // Tied off: no L2 cache in WT_L1

   interface dma_server = culDeSac;

   // ----------------------------------------------------------------
   // Misc. control and status

   // ----------------
   // For ISA tests: watch memory writes to <tohost> addr

`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Bit #(64) tohost_addr);
      dcache.set_watch_tohost (watch_tohost, tohost_addr);
   endmethod

   method Bit #(64) mv_tohost_value = dcache.mv_tohost_value;
`endif

   // Inform core that DDR4 has been initialized and is ready to accept requests
   method Action ma_ddr4_ready;
      icache.ma_ddr4_ready;
      dcache.ma_ddr4_ready;
   endmethod

   // Misc. status; 0 = running, no error
   method Bit #(8) mv_status;
      return dcache.mv_status;
   endmethod

endmodule

// ================================================================

endpackage: Near_Mem_Caches
