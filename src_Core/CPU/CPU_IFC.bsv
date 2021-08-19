// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

//-
// RVFI_DII modifications:
//     Copyright (c) 2018 Jack Deeley
//     Copyright (c) 2018 Peter Rugg
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

package CPU_IFC;

// ================================================================
// BSV library imports

import GetPut       :: *;
import ClientServer :: *;
import AXI4         :: *;

// ================================================================
// Project imports

import ISA_Decls       :: *;

import AXI4_Types  :: *;
import Fabric_Defs :: *;
import Near_Mem_IFC :: *;    // For Wd_Id/Addr/Data/User_Dma

`ifdef INCLUDE_DMEM_SLAVE
import AXI4Lite_Types :: *;
`endif

`ifdef INCLUDE_GDB_CONTROL
import DM_CPU_Req_Rsp :: *;
`endif

`ifdef INCLUDE_TANDEM_VERIF
import Verifier  :: *;
import TV_Info         :: *;
import ISA_Decls       :: *;
`elsif RVFI
import Verifier  :: *;
import RVFI_DII    :: *;
`endif

import Fabric_Defs :: *;

`ifdef PERFORMANCE_MONITORING
import Vector :: *;

typedef 21 ExternalEvtCount;
`endif

// ================================================================
// CPU interface

interface CPU_IFC;
   // Reset
   interface Server #(Bool, Bool)  hart0_server_reset;

   // ----------------
   // SoC fabric connections

   // IMem to Fabric master interface
   interface AXI4_Master #( Wd_MId, Wd_Addr, Wd_Data
                          , Wd_AW_User, Wd_W_User, Wd_B_User
                          , Wd_AR_User, Wd_R_User)  imem_master;

   // DMem to Fabric master interface
   //interface AXI4_Master #( Wd_MId_2x3, Wd_Addr, Wd_Data
   //                       , Wd_AW_User, Wd_W_User, Wd_B_User
   //                       , Wd_AR_User, Wd_R_User)  mem_master;
   interface Near_Mem_Fabric_IFC mem_master;

   // ----------------------------------------------------------------
   // Optional AXI4-Lite D-cache slave interface

`ifdef INCLUDE_DMEM_SLAVE
   interface AXI4Lite_Slave #(Wd_Addr, Wd_Data, 0, 0, 0, 0, 0)  dmem_slave;
`endif

   // ----------------
   // Interface to 'coherent DMA' port of optional L2 cache

   interface AXI4_Slave #( Wd_SId_2x4, Wd_Addr, Wd_Data
                         , Wd_AW_User, Wd_W_User, Wd_B_User
                         , Wd_AR_User, Wd_R_User)  dma_server;

   // ----------------------------------------------------------------

   // External interrupts

   (* always_ready, always_enabled *)
   method Action  m_external_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action  s_external_interrupt_req (Bool set_not_clear);

   // ----------------
   // Software and timer interrupts (from Near_Mem_IO/CLINT)

   (* always_ready, always_enabled *)
   method Action  software_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action  timer_interrupt_req    (Bool set_not_clear);

   // ----------------
   // Non-maskable interrupt

   (* always_ready, always_enabled *)
   method Action  nmi_req (Bool set_not_clear);

`ifdef DETERMINISTIC_TIMING
   method Bit#(64) take_minstret;
`endif

   // ----------------
   // Optional interface to Tandem Verifier

`ifdef RVFI_DII
   interface Flute_RVFI_DII_Server rvfi_dii_server;
`else
`ifdef INCLUDE_TANDEM_VERIF
   interface Get #(Trace_Data)  trace_data_out;
`endif
`ifdef RVFI
   interface Get #(Trace_Data)  trace_data_out;
`endif
`endif

   // ----------------
   // Optional interface to Debug Module

`ifdef INCLUDE_GDB_CONTROL
   // run-control, other
   interface Server #(Bool, Bool)  hart0_server_run_halt;
   interface Put #(Bit #(4))       hart0_put_other_req;

   // GPR access
   interface Server #(DM_CPU_Req #(5,  XLEN), DM_CPU_Rsp #(XLEN)) hart0_gpr_mem_server;

`ifdef ISA_F
   // FPR access
   interface Server #(DM_CPU_Req #(5,  FLEN), DM_CPU_Rsp #(FLEN)) hart0_fpr_mem_server;
`endif

   // CSR access
   interface Server #(DM_CPU_Req #(12, XLEN), DM_CPU_Rsp #(XLEN)) hart0_csr_mem_server;
`endif

   // ----------------
   // External events to be monitored

`ifdef PERFORMANCE_MONITORING
   method Action relay_external_events (Vector #(ExternalEvtCount, Bit #(1)) external_evts);
`endif

   // ----------------------------------------------------------------
   // Misc. control and status

   // ----------------
   // Debugging: set core's verbosity

   method Action set_verbosity (Bit #(4)  verbosity, Bit #(64)  logdelay);

   // ----------------
   // For ISA tests: watch memory writes to <tohost> addr

`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Bit #(64) tohost_addr);
   method Bit #(64) mv_tohost_value;
`endif

   // Inform core that DDR4 has been initialized and is ready to accept requests
   method Action ma_ddr4_ready;

   // Misc. status; 0 = running, no error
   (* always_ready *)
   method Bit #(8) mv_status;

endinterface

// ================================================================

endpackage
