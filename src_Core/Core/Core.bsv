// Copyright (c) 2018-2020 Bluespec, Inc. All Rights Reserved.

//-
// AXI (user fields) + CHERI modifications:
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

package Core;

// ================================================================
// This package defines:
//     Core_IFC
//     mkCore #(Core_IFC)
//
// mkCore instantiates:
//     - mkCPU (the RISC-V CPU)
//     - mkNear_Mem_IO_AXI4
//     - mkPLIC_16_2_7
//     - mkTV_Encode          (Tandem-Verification logic, optional: INCLUDE_TANDEM_VERIF)
//     - mkDebug_Module       (RISC-V Debug Module, optional: INCLUDE_GDB_CONTROL)
// and connects them all up.

// ================================================================
// BSV library imports

import Vector        :: *;
import FIFOF         :: *;
import GetPut        :: *;
import ClientServer  :: *;
import Connectable   :: *;

// ----------------
// BSV additional libs

import Cur_Cycle  :: *;
import GetPut_Aux :: *;
import Routable   :: *;
import AXI4       :: *;

`ifdef INCLUDE_DMEM_SLAVE
import AXI4Lite :: *;
`endif

`ifdef ISA_CHERI
`ifndef NO_TAG_CACHE
import TagControllerAXI :: *;
`endif
`endif

// ================================================================
// Project imports

// Main fabric
import Fabric_Defs  :: *;    // for Wd_Id, Wd_Addr, Wd_Data...
import SoC_Map      :: *;

`ifdef INCLUDE_GDB_CONTROL
import Debug_Module     :: *;
`endif

import Core_IFC          :: *;
import CPU_IFC           :: *;
import CPU               :: *;

import Near_Mem_IO_AXI4  :: *;
import PLIC              :: *;
import PLIC_16_2_7       :: *;

`ifdef INCLUDE_TANDEM_VERIF
import TV_Info   :: *;
import TV_Encode :: *;
`endif

// TV_Taps needed when both GDB_CONTROL and TANDEM_VERIF are present
`ifdef INCLUDE_GDB_CONTROL
import TV_Taps :: *;
`endif

`ifdef PERFORMANCE_MONITORING
import PerformanceMonitor :: *;
import Monitored :: *;
import AXI4_Events_BitVectorable_Instance :: *; // the lesser evil
`endif

// ================================================================
// The Core module

(* synthesize *)
module mkCore (Core_IFC #(N_External_Interrupt_Sources));

   // ================================================================
   // STATE

   // System address map
   SoC_Map_IFC  soc_map  <- mkSoC_Map;

   // The CPU
   CPU_IFC  cpu <- mkCPU;
   let cpu_imem = cpu.imem_master;
   //AXI4_Shim#(5,64,64,0,1,0,0,1) delay_shim <- mkAXI4ShimSizedFIFOF4; // Prevent a combinatorial path after the icache
   AXI4_Shim#(5,64,64,0,1,0,0,1) delay_shim <- mkAXI4ShimSizedFIFOF4; // Prevent a combinatorial path after the icache
   mkConnection(delay_shim.slave, cpu_imem);
   let imem_master = extendIDFields(zeroMasterUserFields(delay_shim.master), 0);

`ifdef PERFORMANCE_MONITORING
   Vector #(7, Bit #(1)) tag_cache_evts = replicate (0);
   Vector #(7, Bit #(1)) tag_cache_master_evts = replicate (0);
`endif
   // set the appropriate axi4_mem_shim_{master, slave} ifc
`ifdef ISA_CHERI
`ifdef NO_TAG_CACHE
   // CHERI, export the tags on the interface
   let axi4_mem_shim <- mkAXI4Shim;
`ifdef PERFORMANCE_MONITORING
`define TAG_CACHE_EVENTS_EXTERNAL
   Wire #(Vector #(7, Bit #(1))) w_tag_cache_master_evts <- mkBypassWire ();
   tag_cache_master_evts = w_tag_cache_master_evts;
`endif
`else
   // CHERI, handle tags internally with a tagController
   let axi4_mem_shim <- mkTagControllerAXI;
`ifdef PERFORMANCE_MONITORING
   tag_cache_evts = axi4_mem_shim.events;
`endif
`endif
`else
   // No CHERI, no tags
   let axi4_mem_shim <- mkAXI4Shim;
`endif
   let axi4_mem_shim_slave  = axi4_mem_shim.slave;
   let axi4_mem_shim_master = axi4_mem_shim.master;

`ifdef PERFORMANCE_MONITORING
   let axi4_mem_shim_slave_monitor <- monitorAXI4_Slave (axi4_mem_shim_slave);
   axi4_mem_shim_slave = axi4_mem_shim_slave_monitor.ifc;
`ifdef ISA_CHERI
`ifndef NO_TAG_CACHE
   let axi4_mem_shim_master_monitor <- monitorAXI4_Master (axi4_mem_shim_master);
   axi4_mem_shim_master = axi4_mem_shim_master_monitor.ifc;
   tag_cache_master_evts = to_vector (axi4_mem_shim_master_monitor.events);
`endif
`endif
`endif

   // Near_Mem_IO
   Near_Mem_IO_AXI4_IFC  near_mem_io <- mkNear_Mem_IO_AXI4;

`ifdef DETERMINISTIC_TIMING
   (*no_implicit_conditions, fire_when_enabled*)
   rule rl_connect_minstret;
     near_mem_io.give_minstret(cpu.take_minstret);
   endrule
`endif

   // PLIC (Platform-Level Interrupt Controller)
   PLIC_IFC_16_2_7  plic <- mkPLIC_16_2_7;

   // Reset requests from SoC and responses to SoC
   // 'Bool' is 'running' state
   FIFOF #(Bool) f_reset_reqs <- mkFIFOF;
   FIFOF #(Bool) f_reset_rsps <- mkFIFOF;

`ifdef INCLUDE_TANDEM_VERIF
   // The TV encoder transforms Trace_Data structures produced by the CPU and DM
   // into encoded byte vectors for transmission to the Tandem Verifier
   TV_Encode_IFC tv_encode <- mkTV_Encode;
`endif

`ifdef INCLUDE_GDB_CONTROL
   // Debug Module
   Debug_Module_IFC  debug_module <- mkDebug_Module;
`endif

   // ================================================================
   // RESET
   // There are two sources of reset requests to the CPU: externally
   // from the SoC and, optionally, the DM.  When both requestors are
   // present (i.e., DM is present), we merge the reset requests into
   // the CPU, and we remember which one was the requestor in
   // f_reset_requestor, so that we know whome to respond to.

   Bit #(1) reset_requestor_dm  = 0;
   Bit #(1) reset_requestor_soc = 1;
`ifdef INCLUDE_GDB_CONTROL
   FIFOF #(Bit #(1)) f_reset_requestor <- mkFIFOF;
`endif

   PulseWire soc_reset_fired <- mkPulseWire();
   // Reset-hart0 request from SoC
   rule rl_cpu_hart0_reset_from_soc_start;
      let running <- pop (f_reset_reqs);

      cpu.hart0_server_reset.request.put (running);    // CPU
      near_mem_io.server_reset.request.put (?);        // Near_Mem_IO
      plic.server_reset.request.put (?);               // PLIC

`ifdef ISA_CHERI
`ifdef NO_TAG_CACHE
   axi4_mem_shim.clear;
`else
   //axi4_mem_shim.clear; XXX Temporarily do not clear the tag cache to avoid hanging on pending transactions
`endif
`else
   axi4_mem_shim.clear;
`endif

      soc_reset_fired.send();
`ifdef INCLUDE_GDB_CONTROL
      // Remember the requestor, so we can respond to it
      f_reset_requestor.enq (reset_requestor_soc);
`endif
      $display ("%0d: Core.rl_cpu_hart0_reset_from_soc_start", cur_cycle);
   endrule

`ifdef INCLUDE_GDB_CONTROL
   // Reset-hart0 from Debug Module
   rule rl_cpu_hart0_reset_from_dm_start if (!soc_reset_fired);
      let running <- debug_module.hart0_reset_client.request.get;

      cpu.hart0_server_reset.request.put (running);    // CPU
      near_mem_io.server_reset.request.put (?);        // Near_Mem_IO
      plic.server_reset.request.put (?);               // PLIC

      // Remember the requestor, so we can respond to it
      f_reset_requestor.enq (reset_requestor_dm);
      $display ("%0d: Core.rl_cpu_hart0_reset_from_dm_start", cur_cycle);
   endrule
`endif

   rule rl_cpu_hart0_reset_complete;
      let running <- cpu.hart0_server_reset.response.get;      // CPU
      let rsp2    <- near_mem_io.server_reset.response.get;    // Near_Mem_IO
      let rsp3    <- plic.server_reset.response.get;           // PLIC

      near_mem_io.set_addr_map (rangeBase(soc_map.m_near_mem_io_addr_range),
			        rangeTop(soc_map.m_near_mem_io_addr_range));

      plic.set_addr_map (rangeBase(soc_map.m_plic_addr_range),
			 rangeTop(soc_map.m_plic_addr_range));

      Bit #(1) requestor = reset_requestor_soc;
`ifdef INCLUDE_GDB_CONTROL
      requestor <- pop (f_reset_requestor);
      if (requestor == reset_requestor_dm)
	 debug_module.hart0_reset_client.response.put (running);
`endif
      if (requestor == reset_requestor_soc)
	 f_reset_rsps.enq (running);

      $display ("%0d: Core.rl_cpu_hart0_reset_complete", cur_cycle);
   endrule

   // ================================================================
   // Direct DM-to-CPU connections

`ifdef INCLUDE_GDB_CONTROL
   // DM to CPU connections for run-control and other misc requests
   mkConnection (debug_module.hart0_client_run_halt, cpu.hart0_server_run_halt);
   mkConnection (debug_module.hart0_get_other_req,   cpu.hart0_put_other_req);
`endif

   // ================================================================
   // Other CPU/DM/TV connections
   // (depends on whether DM, TV or both are present)

`ifdef INCLUDE_GDB_CONTROL

`ifdef INCLUDE_TANDEM_VERIF
   // Create a tap for DM's memory-writes to the bus, and merge-in the trace data.
   DM_Mem_Tap_IFC dm_mem_tap <- mkDM_Mem_Tap;
   mkConnection (debug_module.master, dm_mem_tap.slave);
   let dm_master_local = dm_mem_tap.master;
`else
   let dm_master_local = debug_module.master;
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // BEGIN SECTION: GDB and TV
   // ----------------------------------------------------------------
   // DM and TV both present. We instantiate 'taps' into connections
   // where the DM writes CPU GPRs, CPU FPRs, CPU CSRs, and main memory,
   // in order to produce corresponding writes for the Tandem Verifier.
   // Then, we merge the Trace_Data from these three taps with the
   // Trace_Data produced by the CPU.

   FIFOF #(Trace_Data) f_trace_data_merged <- mkFIFOF;

   // Connect merged trace data to trace encoder
   mkConnection (toGet (f_trace_data_merged), tv_encode.trace_data_in);

   // Merge-in CPU's trace data.
   // This is equivalent to:  mkConnection (cpu.trace_data_out, toPut (f_trace_data_merged))
   // but using a rule allows us to name it in scheduling attributes.
   rule merge_cpu_trace_data;
      let tmp <- cpu.trace_data_out.get;
      f_trace_data_merged.enq (tmp);
   endrule

   rule merge_dm_mem_trace_data;
      let tmp <- dm_mem_tap.trace_data_out.get;
      f_trace_data_merged.enq (tmp);
   endrule

   // Create a tap for DM's GPR writes to the CPU, and merge-in the trace data.
   DM_GPR_Tap_IFC  dm_gpr_tap_ifc <- mkDM_GPR_Tap;
   mkConnection (debug_module.hart0_gpr_mem_client, dm_gpr_tap_ifc.server);
   mkConnection (dm_gpr_tap_ifc.client, cpu.hart0_gpr_mem_server);

   rule merge_dm_gpr_trace_data;
      let tmp <- dm_gpr_tap_ifc.trace_data_out.get;
      f_trace_data_merged.enq (tmp);
   endrule

`ifdef ISA_F
   // Create a tap for DM's FPR writes to the CPU, and merge-in the trace data.
   DM_FPR_Tap_IFC  dm_fpr_tap_ifc <- mkDM_FPR_Tap;
   mkConnection (debug_module.hart0_fpr_mem_client, dm_fpr_tap_ifc.server);
   mkConnection (dm_fpr_tap_ifc.client, cpu.hart0_fpr_mem_server);

   rule merge_dm_fpr_trace_data;
      let tmp <- dm_fpr_tap_ifc.trace_data_out.get;
      f_trace_data_merged.enq (tmp);
   endrule
`endif

   // Create a tap for DM's CSR writes, and merge-in the trace data.
   DM_CSR_Tap_IFC  dm_csr_tap <- mkDM_CSR_Tap;
   mkConnection(debug_module.hart0_csr_mem_client, dm_csr_tap.server);
   mkConnection(dm_csr_tap.client, cpu.hart0_csr_mem_server);

`ifdef ISA_F
   (* descending_urgency = "merge_dm_fpr_trace_data, merge_dm_gpr_trace_data" *)
`endif
   (* descending_urgency = "merge_dm_gpr_trace_data, merge_dm_csr_trace_data" *)
   (* descending_urgency = "merge_dm_csr_trace_data, merge_dm_mem_trace_data" *)
   (* descending_urgency = "merge_dm_mem_trace_data, merge_cpu_trace_data"    *)
   rule merge_dm_csr_trace_data;
      let tmp <- dm_csr_tap.trace_data_out.get;
      f_trace_data_merged.enq(tmp);
   endrule

   // END SECTION: GDB and TV
`else
   // for ifdef INCLUDE_TANDEM_VERIF
   // ----------------------------------------------------------------
   // BEGIN SECTION: GDB and no TV

   // Connect DM's GPR interface directly to CPU
   mkConnection (debug_module.hart0_gpr_mem_client, cpu.hart0_gpr_mem_server);

`ifdef ISA_F
   // Connect DM's FPR interface directly to CPU
   mkConnection (debug_module.hart0_fpr_mem_client, cpu.hart0_fpr_mem_server);
`endif

   // Connect DM's CSR interface directly to CPU
   mkConnection (debug_module.hart0_csr_mem_client, cpu.hart0_csr_mem_server);

   // END SECTION: GDB and no TV
`endif
   // for ifdef INCLUDE_TANDEM_VERIF

`else
   // for ifdef INCLUDE_GDB_CONTROL
   // BEGIN SECTION: no GDB

   // No DM, so 'DM bus master' is dummy
   let dm_master_local = culDeSac;

`ifdef INCLUDE_TANDEM_VERIF
   // ----------------------------------------------------------------
   // BEGIN SECTION: no GDB, TV

   // Connect CPU's TV out directly to TV encoder
   mkConnection (cpu.trace_data_out, tv_encode.trace_data_in);
   // END SECTION: no GDB, TV
`endif
`endif
   // for ifdef INCLUDE_GDB_CONTROL

   // ================================================================
   // Connect the local 2x3 fabric

   // Masters on the local 2x3 fabric
   //Vector#(Num_Masters_2x3,
   Vector#(Num_Masters_2x4,
           //AXI4_Master#( Wd_MId_2x3, Wd_Addr, Wd_Data
           AXI4_Master#( Wd_MId_2x4, Wd_Addr, Wd_Data
                       , Wd_AW_User, Wd_W_User, Wd_B_User
                       , Wd_AR_User, Wd_R_User)) master_vector = newVector;
   //Vector#(Num_Masters_2x3, Near_Mem_Fabric_IFC) master_vector = newVector;
   master_vector[cpu_dmem_master_num]         = cpu.mem_master;
   master_vector[debug_module_sba_master_num] = dm_master_local;

   // Slaves on the local 2x3 fabric
   // default slave is forwarded out directly to the Core interface
   //Vector#(Num_Slaves_2x3,
   Vector#(Num_Slaves_2x4,
           //AXI4_Slave#( Wd_SId_2x3, Wd_Addr, Wd_Data
           AXI4_Slave#( Wd_SId_2x4, Wd_Addr, Wd_Data
                      , Wd_AW_User, Wd_W_User, Wd_B_User
                      , Wd_AR_User, Wd_R_User)) slave_vector = newVector;
   slave_vector[default_slave_num]     = axi4_mem_shim_slave;
   slave_vector[near_mem_io_slave_num] = zeroSlaveUserFields (near_mem_io.axi4_slave);
   slave_vector[plic_slave_num]        = zeroSlaveUserFields (plic.axi4_slave);
   slave_vector[tcm_slave_num]         = cpu.dma_server;

   //function Vector#(Num_Slaves_2x3, Bool) route_2x3 (Bit#(Wd_Addr) addr);
   function Vector#(Num_Slaves_2x4, Bool) route_2x4 (Bit#(Wd_Addr) addr);
      //Vector#(Num_Slaves_2x3, Bool) res = replicate(False);
      Vector#(Num_Slaves_2x4, Bool) res = replicate(False);
      if (inRange(soc_map.m_near_mem_io_addr_range, addr))
        res[near_mem_io_slave_num] = True;
      else if (inRange(soc_map.m_plic_addr_range, addr))
        res[plic_slave_num] = True;
      else if (inRange(soc_map.m_tcm_addr_range, addr))
        res[tcm_slave_num] = True;
      else
        res[default_slave_num] = True;
      Bit #(24) topBits = truncateLSB(addr); //XXX TODO Tag controller masks to 40 bits
      if (topBits != 0) res = replicate(False);
      return res;
   endfunction

   mkAXI4Bus (route_2x4, master_vector, slave_vector);

   // ================================================================
   // Connect interrupt lines from near_mem_io and PLIC to CPU

   rule rl_relay_sw_interrupts;    // from Near_Mem_IO (CLINT)
      Bool x <- near_mem_io.get_sw_interrupt_req.get;
      cpu.software_interrupt_req (x);
      // $display ("%0d: Core.rl_relay_sw_interrupts: relaying: %d", cur_cycle, pack (x));
   endrule

   rule rl_relay_timer_interrupts;    // from Near_Mem_IO (CLINT)
      Bool x <- near_mem_io.get_timer_interrupt_req.get;
      cpu.timer_interrupt_req (x);

      // $display ("%0d: Core.rl_relay_timer_interrupts: relaying: %d", cur_cycle, pack (x));
   endrule

   rule rl_relay_external_interrupts;    // from PLIC
      Bool meip = plic.v_targets [0].m_eip;
      cpu.m_external_interrupt_req (meip);

      Bool seip = plic.v_targets [1].m_eip;
      cpu.s_external_interrupt_req (seip);

      // $display ("%0d: Core.rl_relay_external_interrupts: relaying: %d", cur_cycle, pack (x));
   endrule

   // ================================================================
   // Connect performance events from axi4_mem_shim to CPU

`ifdef PERFORMANCE_MONITORING
   rule rl_relay_external_events;
      Vector #(7, Bit #(1)) slave_events = to_vector (axi4_mem_shim_slave_monitor.events);
      // Append 3 7-bit vectors.  tag_cache_master_evts at index 0x0, slave_events at offset 0x7, and tag_cache_evts at offset 0xE.
      let events = append (tag_cache_evts, append (slave_events, tag_cache_master_evts));
      cpu.relay_external_events (to_large_vector (events));
   endrule
`endif

   // ================================================================
   // INTERFACE

   // ----------------------------------------------------------------
   // Soft reset

   interface Server  cpu_reset_server = toGPServer (f_reset_reqs, f_reset_rsps);

   // ----------------------------------------------------------------
   // AXI4 Fabric interfaces

   // IMem to Fabric master interface
   interface cpu_imem_master = imem_master;

   // DMem to Fabric master interface
   interface core_mem_master = axi4_mem_shim_master;

   // ----------------------------------------------------------------
   // Optional AXI4-Lite D-cache slave interface

`ifdef INCLUDE_DMEM_SLAVE
   interface AXI4Lite_Slave cpu_dmem_slave = cpu.dmem_slave;
`endif

   // ----------------------------------------------------------------
   // Interface to 'coherent DMA' port of optional L2 cache

   //interface AXI4_Slave_IFC  dma_server = cpu.dma_server;
   interface AXI4_Slave_IFC  dma_server = culDeSac;

   // ----------------------------------------------------------------
   // External interrupt sources

   interface core_external_interrupt_sources = plic.v_sources;

   // ----------------------------------------------------------------
   // Non-maskable interrupt request

   method Action nmi_req (Bool set_not_clear);
      cpu.nmi_req (set_not_clear);
   endmethod

   // ----------------------------------------------------------------
   // Optional TV interface

`ifdef INCLUDE_TANDEM_VERIF
   interface Get tv_verifier_info_get;
      method ActionValue #(Info_CPU_to_Verifier) get();
         match { .n, .v } <- tv_encode.tv_vb_out.get;
         return (Info_CPU_to_Verifier { num_bytes: n, vec_bytes: v });
      endmethod
   endinterface
`endif

`ifdef RVFI_DII
   interface Flute_RVFI_DII_Server rvfi_dii_server = cpu.rvfi_dii_server;
`endif

   // ----------------------------------------------------------------
   // Optional DM interfaces

`ifdef INCLUDE_GDB_CONTROL
   // ----------------
   // DMI (Debug Module Interface) facing remote debugger

   interface DMI  dm_dmi = debug_module.dmi;

   // ----------------
   // Facing Platform

   // Non-Debug-Module Reset (reset all except DM)
   interface Client ndm_reset_client = debug_module.ndm_reset_client;
`endif

   // ----------------
   // Debugging: performance monitoring events

`ifdef TAG_CACHE_EVENTS_EXTERNAL
   method Action send_tag_cache_master_events (Vector #(6, Bit #(1)) events);
      w_tag_cache_master_evts <= events;
   endmethod
`endif

   // ----------------------------------------------------------------
   // Misc. control and status

   // ----------------
   // Debugging: set core's verbosity

   method Action  set_verbosity (Bit #(4)  verbosity, Bit #(64)  logdelay);
      cpu.set_verbosity (verbosity, logdelay);
   endmethod

   // ----------------
   // For ISA tests: watch memory writes to <tohost> addr

`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Bit #(64) tohost_addr);
      cpu.set_watch_tohost (watch_tohost, tohost_addr);
   endmethod

   method Bit #(64) mv_tohost_value = cpu.mv_tohost_value;
`endif

   // Inform core that DDR4 has been initialized and is ready to accept requests
   method Action ma_ddr4_ready;
      cpu.ma_ddr4_ready;
   endmethod

   // Misc. status; 0 = running, no error
   method Bit #(8) mv_status;
      return cpu.mv_status;
   endmethod
endmodule: mkCore

(* synthesize *)
module mkCore_Synth (Core_IFC_Synth #(N_External_Interrupt_Sources));
   let core <- mkCore;
   let cpu_imem_master_synth <- toAXI4_Master_Synth (core.cpu_imem_master);
   let core_mem_master_synth <- toAXI4_Master_Synth (core.core_mem_master);
`ifdef INCLUDE_DMEM_SLAVE
   let cpu_dmem_slave_synth <- toAXI4Lite_Slave_Synth (core.cpu_dmem_slave);
`endif
   let dma_server_synth <- toAXI4_Slave_Synth (core.dma_server);

   interface cpu_reset_server = core.cpu_reset_server;
   interface cpu_imem_master = cpu_imem_master_synth;
   interface core_mem_master = core_mem_master_synth;
`ifdef INCLUDE_DMEM_SLAVE
   interface cpu_dmem_slave = cpu_dmem_slave_synth;
`endif
   interface dma_server = dma_server_synth;
   interface core_external_interrupt_sources = core.core_external_interrupt_sources;
   method nmi_req = core.nmi_req;
`ifdef INCLUDE_TANDEM_VERIF
   interface tv_verifier_info_get = core.tv_verifier_info_get;
`elsif RVFI_DII
   interface rvfi_dii_server = core.rvfi_dii_server;
`endif
`ifdef INCLUDE_GDB_CONTROL
   interface dm_dmi = core.dm_dmi;
   interface ndm_reset_client = core.ndm_reset_client;
`endif
`ifdef TAG_CACHE_EVENTS_EXTERNAL
   method send_tag_cache_master_events = core.send_tag_cache_master_events;
`endif
   method set_verbosity = core.set_verbosity;
`ifdef WATCH_TOHOST
   method set_watch_tohost = core.set_watch_tohost;
`endif
   method ma_ddr4_ready = core.ma_ddr4_ready;
   method mv_status = core.mv_status;
endmodule


// ================================================================
// 2x3 Fabric for this Core
// Masters: CPU DMem, Debug Module System Bus Access, External access

// ----------------
// Fabric port numbers for masters

Master_Num_2x3  cpu_dmem_master_num         = 0;
Master_Num_2x3  debug_module_sba_master_num = 1;

// ----------------
// Fabric port numbers for slaves

//Slave_Num_2x3  default_slave_num     = 0;
//Slave_Num_2x3  near_mem_io_slave_num = 1;
//Slave_Num_2x3  plic_slave_num        = 2;
Slave_Num_2x4  default_slave_num     = 0;
Slave_Num_2x4  near_mem_io_slave_num = 1;
Slave_Num_2x4  plic_slave_num        = 2;
Slave_Num_2x4  tcm_slave_num         = 3;

// ================================================================

endpackage
