// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

//-
// CHERI modifications:
//     Copyright (c) 2019 Peter Rugg
//     All rights reserved.
//
//     This software was developed by SRI International and the University of
//     Cambridge Computer Laboratory (Department of Computer Science and
//     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
//     DARPA SSITH research programme.
//-

package CSR_RegFile_MSU;

// ================================================================
// CSR (Control and Status Register) Register File

// Supports Machine, User and Superviser CSRs.

// ================================================================
// Exports

export  CSR_Write_Result (..);
export  AccessPerms (..);
export  CSR_RegFile_IFC (..);
export  mkCSR_RegFile;

// ================================================================
// BSV library imports

import ConfigReg    :: *;
import RegFile      :: *;
import Vector       :: *;
import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;

// BSV additional libs

import GetPut_Aux :: *;

`ifdef PERFORMANCE_MONITORING
import PerformanceMonitor :: *;
`endif

// ================================================================
// Project imports

import ISA_Decls :: *;
import SoC_Map   :: *;

`ifdef INCLUDE_GDB_CONTROL
import DM_Common :: *;    // Debug Module defs
`endif

import CSR_MSTATUS :: *;
import CSR_MIP     :: *;
import CSR_MIE     :: *;

`ifdef ISA_CHERI
import CHERICap     :: *;
import CHERICC_Fat  :: *;
`endif

// ================================================================
// Writing a CSR can update multiple CSRs (e.g., writing
// FRM/FFLAGS/FCSR also updates MSTATUS.FS and MSTATUS.SD

typedef struct {
   WordXL           new_csr_value;
   Maybe #(WordXL)  m_new_csr_value2;
   }
CSR_Write_Result
deriving (Bits, FShow);

// ================================================================
// INTERFACE

typedef struct {
   Bool exists;
   Bool requires_asr;
}  AccessPerms deriving (Bits);

interface CSR_RegFile_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;

   // CSR read (w.o. side effect)
   (* always_ready *)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);
   (* always_ready *)
   method Maybe #(Word) read_csr_port2 (CSR_Addr csr_addr);
`ifdef ISA_CHERI
   (* always_ready *)
   method Maybe #(CapReg) read_scr (SCR_Addr scr_addr);
`endif

   // CSR read (w. side effect)
   (* always_ready *)
   method ActionValue #(Maybe #(Word)) mav_read_csr (CSR_Addr csr_addr);

   // CSR write (returning new value)
   (* always_ready *)
   method ActionValue #(CSR_Write_Result) mav_csr_write (CSR_Addr csr_addr, WordXL word);

`ifdef ISA_CHERI
   // SCR write (returning new value)
   (* always_ready *)
   method ActionValue #(CapReg) mav_scr_write (SCR_Addr scr_addr, CapReg cap);
`endif

`ifdef ISA_F
   // Read FRM
   (* always_ready *)
   method Bit #(3) read_frm;

   // Read FRM
   (* always_ready *)
   method Bit #(5) read_fflags;

   // Update FCSR.FFLAGS
   (* always_ready *)
   method Bit #(5) mv_update_fcsr_fflags (Bit #(5) flags);
   (* always_ready *)
   method Action ma_update_fcsr_fflags (Bit #(5) flags);

   // Update MSTATUS.FS
   (* always_ready *)
   method WordXL mv_update_mstatus_fs (Bit #(2) fs);
   (* always_ready *)
   method Action ma_update_mstatus_fs (Bit #(2) fs);
`endif

   // Read MISA
   (* always_ready *)
   method MISA read_misa;

   // Read MSTATUS
   (* always_ready *)
   method WordXL read_mstatus;

`ifdef ISA_PRIV_S
   // Read SSTATUS
   (* always_ready *)
   method WordXL read_sstatus;
`endif

`ifdef ISA_PRIV_U
   // Read USTATUS
   (* always_ready *)
   method WordXL read_ustatus;
`endif

   // Read SATP
   (* always_ready *)
   method WordXL read_satp;

   // CSR trap actions
   method ActionValue #(Trap_Info_CSR)
          csr_trap_actions (Priv_Mode  from_priv,
`ifdef ISA_CHERI
          CapPipe    pcc,
`else
			    Word       pc,
`endif
			    Bool       nmi,          // non-maskable interrupt
			    Bool       interrupt,    // other interrupt
`ifdef ISA_CHERI
          CHERI_Exc_Code cheri_exc_code,
          Bit#(6)        cheri_exc_reg,
`endif
			    Exc_Code   exc_code,
			    Word       xtval);

   // CSR RET actions (return from exception)
   method ActionValue #(Tuple3#(
`ifdef ISA_CHERI
                               CapPipe,
`else
                               Addr,
`endif
   Priv_Mode, Word)) csr_ret_actions (Priv_Mode from_priv);

   // Read MINSTRET
   (* always_ready *)
   method Bit #(64) read_csr_minstret;

   // Increment MINSTRET
   (* always_ready *)
   method Action csr_minstret_incr;

   // Read MCYCLE
   (* always_ready *)
   method Bit #(64) read_csr_mcycle;

   // Read MTIME
   (* always_ready *)
   method Bit #(64) read_csr_mtime;

`ifdef PERFORMANCE_MONITORING
   (* always_ready, always_enabled *)
   method Action send_performance_events (Vector #(No_Of_Evts, Bit #(Counter_Width)) evts);
`endif

   // Access permission
   (* always_ready *)
   method AccessPerms access_permitted_1 (Priv_Mode  priv, CSR_Addr  csr_addr, Bool  read_not_write);
   (* always_ready *)
   method AccessPerms access_permitted_2 (Priv_Mode  priv, CSR_Addr  csr_addr, Bool  read_not_write);
`ifdef ISA_CHERI
   (* always_ready *)
   method AccessPerms access_permitted_scr (Priv_Mode  priv, SCR_Addr  scr_addr, Bool  read_not_write);
`endif

   // Fault on reading counters?
   (* always_ready *)
   method Bool csr_counter_read_fault (Priv_Mode  priv, CSR_Addr  csr_addr);

   // Read MIP
   (* always_ready *)
   method WordXL csr_mip_read;

   // ----------------
   // Interrupts

   (* always_ready, always_enabled *)
   method Action m_external_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action s_external_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action timer_interrupt_req    (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action software_interrupt_req (Bool set_not_clear);

   (* always_ready *)
   method Maybe #(Exc_Code) interrupt_pending (Priv_Mode cur_priv);

   // WFI ignores mstatus ies and ideleg regs
   (* always_ready *)
   method Bool wfi_resume;

   // ----------------
   // Non-maskable interrupts

   (* always_ready, always_enabled *)
   method Action nmi_req (Bool set_not_clear);

   (* always_ready *)
   method Bool nmi_pending;

   // ----------------
   // Methods when Debug Module is present

`ifdef INCLUDE_GDB_CONTROL
   // Read dpcc
   method CapPipe read_dpcc ();

   // Update dpcc
   method Action write_dpcc (CapPipe pcc);

   // Break should enter Debug Mode
   method Bool dcsr_break_enters_debug (Priv_Mode cur_priv);

   // Read dcsr.step
   method Bool read_dcsr_step ();

   // Update 'cause' and 'priv' in DCSR
   (* always_ready *)
   method Action write_dcsr_cause_priv (DCSR_Cause  cause, Priv_Mode  priv);

`endif

   // ----------------
   // Debugging this module

   method Action debug;
endinterface

// ================================================================
// 'misa' specifying RSIC-V features implemented.

function MISA misa_reset_value;
   MISA ms = unpack (0);

`ifdef RV32
   ms.mxl = misa_mxl_32;
`elsif RV64
   ms.mxl = misa_mxl_64;
`elsif RV128
   ms.mxl = misa_mxl_128;
`else
   ms.mxl = misa_mxl_zero;
`endif

`ifdef ISA_PRIV_U
   // User Mode
   ms.u = 1'b1;
`ifdef ISA_N
   // User-level Interrupts
   ms.n = 1'b1;
`endif
`endif

`ifdef ISA_PRIV_S
   // Supervisor Mode
   ms.s = 1'b1;
`endif

   // Integer Base
   ms.i = 1'b1;

`ifdef ISA_M
   // Integer Multiply/Divide
   ms.m = 1'b1;
`endif

`ifdef ISA_F
   // Single- and Double-precision Floating Point
   ms.f = 1'b1;
`endif

`ifdef ISA_D
   ms.d = 1'b1;
`endif

`ifdef ISA_A
   // Atomic Memory Ops
   ms.a = 1'b1;
`endif

`ifdef ISA_C
   // Compressed Instructions
   ms.c = 1'b1;
`endif

   return ms;
endfunction

// ================================================================
// Major states of mkCSR_RegFile module

typedef enum { RF_RESET_START, RF_RUNNING } RF_State
deriving (Eq, Bits, FShow);

// ================================================================

`ifdef PERFORMANCE_MONITORING
(* synthesize *)
module mkPerfCountersFlute (PerfCounters_IFC #(No_Of_Ctrs, Counter_Width, Counter_Width, No_Of_Evts));
  PerfCounters_IFC #(No_Of_Ctrs, Counter_Width, Counter_Width, No_Of_Evts) perf_counters <- mkPerfCounters;
  return perf_counters;
endmodule
`endif

// ================================================================

(* synthesize *)
module mkCSR_RegFile (CSR_RegFile_IFC);

`ifdef RVFI_DII
   let mkCSRReg = mkReg (unpack (0));
`else
   let mkCSRReg = mkRegU;
`endif

   Reg #(Bit #(4)) cfg_verbosity <- mkConfigReg (0);
   Reg #(RF_State) rg_state      <- mkReg (RF_RESET_START);

   SoC_Map_IFC soc_map <- mkSoC_Map;

   // Reset
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   // CSRs
   // User-mode CSRs
`ifdef ISA_F
   Reg #(Bit #(5)) rg_fflags <- mkCSRReg;    // floating point flags
   Reg #(Bit #(3)) rg_frm    <- mkCSRReg;    // floating point rounding mode
`endif

   // Supervisor-mode CSRs
   Bit #(16)  sedeleg = 0;    // hardwired to 0
   Bit #(12)  sideleg = 0;    // hardwired to 0

`ifdef ISA_PRIV_S
   // sie     is a restricted view of mie
   // sip     is a restricted view of mip

   // scounteren hardwired to 0 for now

   Reg #(Word)       rg_sscratch  <- mkCSRReg;
   Reg #(MCause)     rg_scause    <- mkCSRReg;
`ifdef ISA_CHERI
   Reg #(XCCSR)      rg_sccsr     <- mkCSRReg;
   Reg #(CapReg)     rg_stcc      <- mkReg (nullCap);
   CapPipe           rg_stcc_unpacked = cast (rg_stcc);
   Reg #(CapReg)     rg_stdc      <- mkReg (nullCap);
   CapPipe           rg_stdc_unpacked = cast (rg_stdc);
   Reg #(CapReg)     rg_sscratchc <- mkReg (nullCap);
   CapPipe           rg_sscratchc_unpacked = cast (rg_sscratchc);
   Reg #(CapReg)     rg_sepcc     <- mkReg (nullCap);
   CapPipe           rg_sepcc_unpacked = cast (rg_sepcc);

   let               rg_stvec = word_to_mtvec (getOffset (rg_stcc_unpacked));
   let               rg_sepc  = getOffset (rg_sepcc_unpacked);
`else
   Reg #(MTVec)      rg_stvec     <- mkCSRReg;
   Reg #(Word)       rg_sepc      <- mkCSRReg;
`endif

   Reg #(Word)       rg_stval     <- mkCSRReg;
   Reg #(WordXL)     rg_satp      <- mkCSRReg;

   Reg #(Bit #(29))  rg_medeleg   <- mkCSRReg;    // TODO: also in M-U systems with user-level traps
   Reg #(Bit #(12))  rg_mideleg   <- mkCSRReg;    // TODO: also in M-U systems with user-level traps
`else
   Bit #(29)         rg_medeleg   = 0;
   Bit #(12)         rg_mideleg   = 0;
`endif

   // Machine-mode CSRs
   Word mvendorid   = 0;    // Not implemented
   Word marchid     = 0;    // Not implemented
   Word mimpid      = 0;    // Not implemented
   Word mhartid     = 0;

   CSR_MSTATUS_IFC  csr_mstatus <- mkCSR_MSTATUS (misa_reset_value);

   MISA              misa          =  misa_reset_value;
   CSR_MIE_IFC       csr_mie       <- mkCSR_MIE;
   CSR_MIP_IFC       csr_mip       <- mkCSR_MIP;

   Reg #(MCounteren) rg_mcounteren <- mkCSRReg;

   Reg #(Word)       rg_mscratch <- mkCSRReg;
   Reg #(MCause)     rg_mcause   <- mkCSRReg;
   Reg #(Word)       rg_mtval    <- mkCSRReg;

`ifdef ISA_CHERI
   Reg #(XCCSR)      rg_mccsr     <- mkCSRReg;
   Reg #(CapReg)     rg_mtcc      <- mkReg (nullCap);
   CapPipe           rg_mtcc_unpacked = cast (rg_mtcc);
   Reg #(CapReg)     rg_mtdc      <- mkReg (nullCap);
   CapPipe           rg_mtdc_unpacked = cast (rg_mtdc);
   Reg #(CapReg)     rg_mscratchc <- mkReg (nullCap);
   CapPipe           rg_mscratchc_unpacked = cast (rg_mscratchc);
   Reg #(CapReg)     rg_mepcc     <- mkReg (nullCap);
   CapPipe           rg_mepcc_unpacked = cast (rg_mepcc);

   let               rg_mtvec = word_to_mtvec (getOffset (rg_mtcc_unpacked));
   let               rg_mepc  = getOffset (rg_mepcc_unpacked);
`else
   Reg #(MTVec)      rg_mtvec    <- mkCSRReg;
   Reg #(Word)       rg_mepc     <- mkCSRReg;
`endif


   // RegFile #(Bit #(2), WordXL)  rf_pmpcfg   <- mkRegFileFull;
   // Vector #(16, Reg #(WordXL))  vrg_pmpaddr <- replicateM (mkCSRReg);

   // mcycle is needed even for user-mode RDCYCLE instruction
   // It can be updated by a CSR instruction (in Priv_M), and by the clock
   Reg #(Bit #(64))   rg_mcycle <- mkReg (0);
   RWire #(Bit #(64)) rw_mcycle <- mkRWire;    // Driven on CSRRx write to mcycle

   Reg #(Bit #(64))   rg_mtime <- mkReg (0);

   // minstret is needed even for user-mode RDINSTRET instructions
   // It can be updated by a CSR instruction (in Priv_M), and by retirement of any other instruction
   Reg #(Bit #(64))   rg_minstret      <- mkReg (0);    // Needed even for user-mode instrs
   RWire #(Bit #(64)) rw_minstret      <- mkRWire;      // Driven on CSRRx write to minstret
   PulseWire          pw_minstret_incr <- mkPulseWire;

`ifdef PERFORMANCE_MONITORING
   PerfCounters_IFC #(No_Of_Ctrs, Counter_Width, Counter_Width, No_Of_Evts)
      perf_counters <- mkPerfCountersFlute;

   let ctrs     = perf_counters.read_counters;
   let ctr_sels = perf_counters.read_ctr_sels;

   Reg #(Bit #(2))  rg_ctr_inhib_ir_cy <- mkReg (0);
   Wire #(Bit #(2)) w_ctr_inhib_ir_cy  <- mkWire;

   MCountinhibit ctr_inhibit = MCountinhibit {reserved:  ?,
					      hpm:       perf_counters.read_ctr_inhibit,
					      ir:        rg_ctr_inhib_ir_cy [1],
					      reserved2: ?,
					      cy:        rg_ctr_inhib_ir_cy [0]};
   CSR_Addr      no_of_ctrs  = fromInteger (valueOf (No_Of_Ctrs));
`else
   Vector #(0, ReadOnly #(Bit #(Counter_Width))) ctrs     = newVector;
   Vector #(0, ReadOnly #(Word))                 ctr_sels = newVector;

   MCountinhibit ctr_inhibit = word_to_mcountinhibit (0);
   CSR_Addr      no_of_ctrs  = 0;
`endif

   // Debug/Trace
   Reg #(WordXL)    rg_tselect <- mkCSRReg;
   Reg #(WordXL)    rg_tdata1  <- mkCSRReg;
   Reg #(WordXL)    rg_tdata2  <- mkCSRReg;
   Reg #(WordXL)    rg_tdata3  <- mkCSRReg;

   // Debug
   Reg #(Bit #(32)) rg_dcsr      <- mkCSRReg;    // Is 32b even in RV64
   Reg #(CapPipe)   rg_dpcc      <- mkCSRReg;
   Reg #(WordXL)    rg_dscratch0 <- mkCSRReg;
   Reg #(WordXL)    rg_dscratch1 <- mkCSRReg;

   // Non-maskable interrupt
   Reg #(Bool)    rg_nmi <- mkReg (False);
   Reg #(WordXL)  rg_nmi_vector <- mkCSRReg;

   // ================================================================
   // BEHAVIOR: RESET
   // Initialize some CSRs.

   rule rl_reset_start (rg_state == RF_RESET_START);
      // User-level CSRs
`ifdef ISA_F
      rg_fflags <= 0;
      rg_frm    <= 0;
`endif

      // Supervisor-level CSRs
`ifdef ISA_PRIV_S
`ifdef ISA_CHERI
      rg_stcc       <= soc_map.m_mtcc_reset_value;
      rg_stdc       <= nullCap;
      rg_sscratchc  <= nullCap;
      rg_sepcc      <= soc_map.m_mepcc_reset_value;
`else
      rg_stvec    <= word_to_mtvec (truncate (soc_map.m_mtvec_reset_value));
`endif
      rg_scause   <= word_to_mcause (0);    // Supposed to be the cause of the reset.
      rg_satp     <= 0;
      //rg_scounteren <= mcounteren_reset_value;
`endif

      // Machine-level CSRs
      csr_mstatus.reset (misa_reset_value);
      csr_mie.reset;
      csr_mip.reset;

`ifdef ISA_CHERI
      rg_mtcc       <= soc_map.m_mtcc_reset_value;
      rg_mtdc       <= nullCap;
      rg_mscratchc  <= nullCap;
      rg_mepcc      <= soc_map.m_mepcc_reset_value;
`else
      rg_mtvec      <= word_to_mtvec (truncate (soc_map.m_mtvec_reset_value));
`endif
      rg_mcause     <= word_to_mcause (0);    // Supposed to be the cause of the reset.
`ifdef ISA_PRIV_S
      rg_medeleg    <= 0;
      rg_mideleg    <= 0;
`endif
      rg_mcounteren <= mcounteren_reset_value;

      rg_tselect    <= 0;
      rg_tdata1     <= 0;    // ISA test rv64mi-p-breakpoint assumes reset value 0.

      rw_minstret.wset (0);

`ifdef INCLUDE_GDB_CONTROL
`ifdef ISA_CHERI
      rg_dpcc <= cast (soc_map.m_pcc_reset_value);
`else
      rg_dpc  <= truncate (soc_map.m_pc_reset_value);
`endif
      rg_dcsr <= zeroExtend ({4'h4,    // [31:28]  xdebugver
			      12'h0,   // [27:16]  reserved
			      1'h0,    // [15]     ebreakm
			      1'h0,    // [14]     reserved
			      1'h0,    // [13]     ebreaks
			      1'h0,    // [12]     ebreaku
			      1'h0,    // [11]     stepie
			      1'h0,    // [10]     stopcount
			      1'h0,    // [9]      stoptime
			      3'h0,    // [8:7]    cause    // WARNING: 0 is non-standard
			      1'h0,    // [5]      reserved
			      1'h1,    // [4]      mprven
			      1'h0,    // [3]      nmip    // non-maskable interrupt pending
			      1'h0,    // [2]      step
			      2'h3}    // [1:0]    prv (machine mode)
			     );
`endif

      // Non-maskable interrupts
      rg_nmi        <= False;
      rg_nmi_vector <= truncate (soc_map.m_nmivec_reset_value);

      rg_state <= RF_RUNNING;
   endrule

   // ================================================================
   // BEHAVIOR

   // ----------------------------------------------------------------
   // CYCLE counter

   (* no_implicit_conditions, fire_when_enabled *)
   rule rl_mcycle_incr;
      // Update due to CSRRx    TODO: fix this
      if (rw_mcycle.wget matches tagged Valid .v)
	 rg_mcycle <= v;

      // Update due to clock
      else if (! unpack (ctr_inhibit.cy))
	 rg_mcycle <= rg_mcycle + 1;
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule rl_mtime_incr;
`ifdef DETERMINISTIC_TIMING
      if (pw_minstret_incr)
`endif
	 rg_mtime <= rg_mtime + 1;
   endrule

   // ----------------------------------------------------------------
   // INSTRET

   (* descending_urgency = "rl_reset_start, rl_upd_minstret_csrrx" *)
   rule rl_upd_minstret_csrrx (rw_minstret.wget matches tagged Valid .v);
      rg_minstret <= v;
      // $display ("%0d: CSR_RegFile_UM.rl_upd_minstret_csrrx: new value is %0d", rg_mcycle, v);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule rl_upd_minstret_incr ((! isValid (rw_minstret.wget)) && pw_minstret_incr && (! unpack (ctr_inhibit.ir)));
      rg_minstret <= rg_minstret + 1;
      // $display ("%0d: CSR_RegFile_UM.rl_upd_minstret_incr: new value is %0d", rg_mcycle, rg_minstret + 1);
   endrule

   // ----------------------------------------------------------------
   // CTR INHIB
   // Must do it this roundabout way so that rules above aren't blocked by
   // fav_csr_write due to accessing both a wire (rw_minstret) and a reg (ctr_inhibit)
   // This way ctr_inhibit is not written in fav_csr_write

`ifdef PERFORMANCE_MONITORING
   rule rl_upd_ctr_inhib_csrrx;
      rg_ctr_inhib_ir_cy <= w_ctr_inhib_ir_cy;
   endrule
`endif

   // ----------------------------------------------------------------
   // Help functions for interface methods

   // ----------------
   // Test if CSR is supported

   function AccessPerms fv_csr_exists_and_asr (CSR_Addr csr_addr, Bool read_not_write);
      Bool exists = (   ((csr_addr_hpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31))
		     || ((csr_addr_mhpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31))
`ifdef RV32
		     || ((csr_addr_hpmcounter3h <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31h))
		     || ((csr_addr_mhpmcounter3h <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31h))
`endif
		     || ((csr_addr_mhpmevent3 <= csr_addr) && (csr_addr <= csr_addr_mhpmevent31))

		     // User mode csrs
`ifdef ISA_F
		     || (csr_addr == csr_addr_fflags)
		     || (csr_addr == csr_addr_frm)
		     || (csr_addr == csr_addr_fcsr)
`endif
		     || (csr_addr == csr_addr_cycle)
		     || (csr_addr == csr_addr_time)
		     || (csr_addr == csr_addr_instret)
`ifdef RV32
		     || (csr_addr == csr_addr_cycleh)
		     || (csr_addr == csr_addr_timeh)
		     || (csr_addr == csr_addr_instreth)
`endif

`ifdef ISA_PRIV_S
		     // Supervisor mode csrs
		     || (csr_addr == csr_addr_sstatus)
		     || (csr_addr == csr_addr_sedeleg)
		     || (csr_addr == csr_addr_sideleg)
		     || (csr_addr == csr_addr_sie)
		     || (csr_addr == csr_addr_stvec)
		     || (csr_addr == csr_addr_scounteren)

		     || (csr_addr == csr_addr_sscratch)
		     || (csr_addr == csr_addr_sepc)
		     || (csr_addr == csr_addr_scause)
		     || (csr_addr == csr_addr_stval)
		     || (csr_addr == csr_addr_sip)

		     || (csr_addr == csr_addr_satp)

		     || (csr_addr == csr_addr_medeleg)
		     || (csr_addr == csr_addr_mideleg)

`ifdef ISA_CHERI
		     || (csr_addr == csr_addr_sccsr)
`endif
`endif

		     // Machine mode csrs
		     || (csr_addr == csr_addr_mvendorid)
		     || (csr_addr == csr_addr_marchid)
		     || (csr_addr == csr_addr_mimpid)
		     || (csr_addr == csr_addr_mhartid)

		     || (csr_addr == csr_addr_mstatus)
		     || (csr_addr == csr_addr_misa)
		     || (csr_addr == csr_addr_mie)
		     || (csr_addr == csr_addr_mtvec)
		     || (csr_addr == csr_addr_mcounteren)

		     || (csr_addr == csr_addr_mscratch)
		     || (csr_addr == csr_addr_mepc)
		     || (csr_addr == csr_addr_mcause)
		     || (csr_addr == csr_addr_mtval)
		     || (csr_addr == csr_addr_mip)

`ifdef ISA_CHERI
		     || (csr_addr == csr_addr_mccsr)
`endif
		     // TODO: Phys Mem Protection regs
		     // (csr_addr == csr_pmpcfg0)
		     // (csr_addr == csr_pmpcfg1)
		     // (csr_addr == csr_pmpcfg2)
		     // (csr_addr == csr_pmpcfg3)

		     // (csr_addr == csr_pmpaddr0)
		     // (csr_addr == csr_pmpaddr1)
		     // (csr_addr == csr_pmpaddr2)
		     // (csr_addr == csr_pmpaddr3)
		     // (csr_addr == csr_pmpaddr4)
		     // (csr_addr == csr_pmpaddr5)
		     // (csr_addr == csr_pmpaddr6)
		     // (csr_addr == csr_pmpaddr7)
		     // (csr_addr == csr_pmpaddr8)
		     // (csr_addr == csr_pmpaddr9)
		     // (csr_addr == csr_pmpaddr10)
		     // (csr_addr == csr_pmpaddr11)
		     // (csr_addr == csr_pmpaddr12)
		     // (csr_addr == csr_pmpaddr13)
		     // (csr_addr == csr_pmpaddr14)
		     // (csr_addr == csr_pmpaddr15)

		     || (csr_addr == csr_addr_mcycle)
		     || (csr_addr == csr_addr_minstret)
`ifdef RV32
		     || (csr_addr == csr_addr_mcycleh)
		     || (csr_addr == csr_addr_minstreth)
`endif
		     || (csr_addr == csr_addr_mcountinhibit)

		     || (csr_addr == csr_addr_tselect)
		     || (csr_addr == csr_addr_tdata1)
		     || (csr_addr == csr_addr_tdata2)
		     || (csr_addr == csr_addr_tdata3)

`ifdef INCLUDE_GDB_CONTROL
		     || (csr_addr == csr_addr_dcsr)
		     || (csr_addr == csr_addr_dpc)
		     || (csr_addr == csr_addr_dscratch0)
		     || (csr_addr == csr_addr_dscratch1)
`endif
	 );
      Bool whitelisted =
                    (   (((csr_addr_hpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31)) && read_not_write)
`ifdef RV32
		     || (((csr_addr_hpmcounter3h <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31h)) && read_not_write)
`endif
`ifdef ISA_F
		     || (csr_addr == csr_addr_fflags)
		     || (csr_addr == csr_addr_frm)
		     || (csr_addr == csr_addr_fcsr)
`endif
		     || ((csr_addr == csr_addr_cycle) && read_not_write)
		     || ((csr_addr == csr_addr_time) && read_not_write)
		     || ((csr_addr == csr_addr_instret) && read_not_write)
`ifdef RV32
		     || ((csr_addr == csr_addr_cycleh) && read_not_write)
		     || ((csr_addr == csr_addr_timeh) && read_not_write)
		     || ((csr_addr == csr_addr_instreth) && read_not_write)
`endif
         );
      return AccessPerms {exists: exists, requires_asr: !whitelisted};
   endfunction: fv_csr_exists_and_asr

`ifdef ISA_CHERI
   function AccessPerms fv_scr_exists_and_asr (SCR_Addr scr_addr, Bool read_not_write);
     Bool exists = (   (scr_addr == scr_addr_PCC)
		    || (scr_addr == scr_addr_DDC)
`ifdef ISA_PRIV_S
		    || (scr_addr == scr_addr_STCC)
		    || (scr_addr == scr_addr_STDC)
		    || (scr_addr == scr_addr_SEPCC)
		    || (scr_addr == scr_addr_SScratchC)
`endif
		    || (scr_addr == scr_addr_MTCC)
		    || (scr_addr == scr_addr_MTDC)
		    || (scr_addr == scr_addr_MEPCC)
		    || (scr_addr == scr_addr_MScratchC)
         );

     Bool whitelisted =
		   (   (scr_addr == scr_addr_DDC)
         );

     return AccessPerms {exists: exists, requires_asr: !whitelisted};
   endfunction
`endif

`ifdef ISA_CHERI
   function Maybe #(CapReg) fv_scr_read (SCR_Addr scr_addr);
      Maybe #(CapReg) m_scr_value = tagged Invalid;

      case (scr_addr)
	 // PCC and DDC handled externally

`ifdef ISA_PRIV_S
	 scr_addr_STCC: m_scr_value = tagged Valid rg_stcc;
	 scr_addr_STDC: m_scr_value = tagged Valid rg_stdc;
	 scr_addr_SScratchC: m_scr_value = tagged Valid rg_sscratchc;
	 scr_addr_SEPCC: m_scr_value = tagged Valid rg_sepcc;
`endif

	 scr_addr_MTCC: m_scr_value = tagged Valid rg_mtcc;
	 scr_addr_MTDC: m_scr_value = tagged Valid rg_mtdc;
	 scr_addr_MScratchC: m_scr_value = tagged Valid rg_mscratchc;
	 scr_addr_MEPCC: m_scr_value = tagged Valid rg_mepcc;
      endcase

      return m_scr_value;
   endfunction
`endif

   // ----------------
   // CSR reads (no side effect)
   // Returns Invalid for invalid CSR addresses or access-mode violations

   function Maybe #(Word) fv_csr_read (CSR_Addr csr_addr);
      Maybe #(Word)  m_csr_value = tagged Invalid;

      if ((csr_addr_hpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31)) begin
	 let idx = csr_addr - csr_addr_hpmcounter3;
	 if (idx < no_of_ctrs) m_csr_value = tagged Valid (truncate (ctrs [idx]));
	 else m_csr_value = tagged Valid 0;
      end
`ifdef RV32
      else if ((csr_addr_hpmcounter3h <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31h)) begin
	 let idx = csr_addr - csr_addr_hpmcounter3h;
	 if (idx < no_of_ctrs) m_csr_value = tagged Valid (ctrs [idx][63:32]);
	 else m_csr_value = tagged Valid 0;
      end
`endif
      else if ((csr_addr_mhpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31)) begin
	 let idx = csr_addr - csr_addr_mhpmcounter3;
	 if (idx < no_of_ctrs) m_csr_value = tagged Valid (truncate (ctrs [idx]));
	 else m_csr_value = tagged Valid 0;
      end
`ifdef RV32
      else if ((csr_addr_mhpmcounter3h <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31h)) begin
	 let idx = csr_addr - csr_addr_mhpmcounter3h;
	 if (idx < no_of_ctrs) m_csr_value = tagged Valid (ctrs [idx][63:32]);
	 else m_csr_value = tagged Valid 0;
      end
`endif
      else if ((csr_addr_mhpmevent3 <= csr_addr) && (csr_addr <= csr_addr_mhpmevent31)) begin
	 let idx = csr_addr - csr_addr_mhpmevent3;
	 if (idx < no_of_ctrs) m_csr_value = tagged Valid (zeroExtend (ctr_sels [idx]));
	 else m_csr_value = tagged Valid 0;
      end
      else begin
	 case (csr_addr)
	    // User mode csrs
`ifdef ISA_F
	    csr_addr_fflags:   m_csr_value = tagged Valid ({ 0, rg_fflags });
	    csr_addr_frm:      m_csr_value = tagged Valid ({ 0, rg_frm });
	    csr_addr_fcsr:     m_csr_value = tagged Valid ({ 0, rg_frm, rg_fflags });
`endif
	    csr_addr_cycle:    m_csr_value = tagged Valid (truncate (rg_mcycle));
	    csr_addr_time:     m_csr_value = tagged Valid (truncate (rg_mtime));
	    csr_addr_instret:  m_csr_value = tagged Valid (truncate (rg_minstret));
`ifdef RV32
	    csr_addr_cycleh:   m_csr_value = tagged Valid (rg_mcycle   [63:32]);
	    csr_addr_timeh:    m_csr_value = tagged Valid (rg_mtime    [63:32]);
	    csr_addr_instreth: m_csr_value = tagged Valid (rg_minstret [63:32]);
`endif

`ifdef ISA_PRIV_S
	    // Supervisor mode csrs
	    csr_addr_sstatus:    m_csr_value = tagged Valid (csr_mstatus.mv_sstatus_read);
	    csr_addr_sedeleg:    m_csr_value = tagged Valid zeroExtend (sedeleg);
	    csr_addr_sideleg:    m_csr_value = tagged Valid zeroExtend (sideleg);
	    csr_addr_sie:        m_csr_value = tagged Valid (csr_mie.mv_sie_read);
	    csr_addr_stvec:      m_csr_value = tagged Valid (mtvec_to_word (rg_stvec));
	    csr_addr_scounteren: m_csr_value = tagged Valid 0;

	    csr_addr_sscratch:   m_csr_value = tagged Valid rg_sscratch;
	    csr_addr_sepc:       m_csr_value = tagged Valid ((misa.c == 1'b1) ? rg_sepc : (rg_sepc & (~ 2)));
	    csr_addr_scause:     m_csr_value = tagged Valid (mcause_to_word (rg_scause));
	    csr_addr_stval:      m_csr_value = tagged Valid rg_stval;
	    csr_addr_sip:        m_csr_value = tagged Valid (csr_mip.mv_sip_read);

`ifdef ISA_CHERI
	    csr_addr_sccsr:      m_csr_value = tagged Valid (capexc_to_xccsr (rg_sccsr));
`endif
	    csr_addr_satp:       m_csr_value = tagged Valid rg_satp;

	    csr_addr_medeleg:    m_csr_value = tagged Valid zeroExtend (rg_medeleg);
	    csr_addr_mideleg:    m_csr_value = tagged Valid zeroExtend (rg_mideleg);
`endif

	    // Machine mode csrs
	    csr_addr_mvendorid:  m_csr_value = tagged Valid mvendorid;
	    csr_addr_marchid:    m_csr_value = tagged Valid marchid;
	    csr_addr_mimpid:     m_csr_value = tagged Valid mimpid;
	    csr_addr_mhartid:    m_csr_value = tagged Valid mhartid;

	    csr_addr_mstatus:    m_csr_value = tagged Valid (csr_mstatus.mv_read);
	    csr_addr_misa:       m_csr_value = tagged Valid (misa_to_word (misa));
	    csr_addr_mie:        m_csr_value = tagged Valid (csr_mie.mv_read);
	    csr_addr_mtvec:      m_csr_value = tagged Valid (mtvec_to_word (rg_mtvec));
	    csr_addr_mcounteren: m_csr_value = tagged Valid (mcounteren_to_word (rg_mcounteren));

	    csr_addr_mscratch:   m_csr_value = tagged Valid rg_mscratch;
	    csr_addr_mepc:       m_csr_value = tagged Valid ((misa.c == 1'b1) ? rg_mepc : (rg_mepc & (~ 2)));
	    csr_addr_mcause:     m_csr_value = tagged Valid (mcause_to_word (rg_mcause));
	    csr_addr_mtval:      m_csr_value = tagged Valid rg_mtval;
	    csr_addr_mip:        m_csr_value = tagged Valid (csr_mip.mv_read);

`ifdef ISA_CHERI
	    csr_addr_mccsr:      m_csr_value = tagged Valid (capexc_to_xccsr (rg_mccsr));
`endif

	    // TODO: Phys Mem Protection regs
	    // csr_pmpcfg0:   m_csr_value = tagged Valid rf_pmpcfg.sub (0);
	    // csr_pmpcfg1:   m_csr_value = tagged Valid rf_pmpcfg.sub (1);
	    // csr_pmpcfg2:   m_csr_value = tagged Valid rf_pmpcfg.sub (2);
	    // csr_pmpcfg3:   m_csr_value = tagged Valid rf_pmpcfg.sub (3);

	    // csr_pmpaddr0:   m_csr_value = tagged Valid vrg_pmpaddr [0];
	    // csr_pmpaddr1:   m_csr_value = tagged Valid vrg_pmpaddr [1];
	    // csr_pmpaddr2:   m_csr_value = tagged Valid vrg_pmpaddr [2];
	    // csr_pmpaddr3:   m_csr_value = tagged Valid vrg_pmpaddr [3];
	    // csr_pmpaddr4:   m_csr_value = tagged Valid vrg_pmpaddr [4];
	    // csr_pmpaddr5:   m_csr_value = tagged Valid vrg_pmpaddr [5];
	    // csr_pmpaddr6:   m_csr_value = tagged Valid vrg_pmpaddr [6];
	    // csr_pmpaddr7:   m_csr_value = tagged Valid vrg_pmpaddr [7];
	    // csr_pmpaddr8:   m_csr_value = tagged Valid vrg_pmpaddr [8];
	    // csr_pmpaddr9:   m_csr_value = tagged Valid vrg_pmpaddr [9];
	    // csr_pmpaddr10:  m_csr_value = tagged Valid vrg_pmpaddr [10];
	    // csr_pmpaddr11:  m_csr_value = tagged Valid vrg_pmpaddr [11];
	    // csr_pmpaddr12:  m_csr_value = tagged Valid vrg_pmpaddr [12];
	    // csr_pmpaddr13:  m_csr_value = tagged Valid vrg_pmpaddr [13];
	    // csr_pmpaddr14:  m_csr_value = tagged Valid vrg_pmpaddr [14];
	    // csr_pmpaddr15:  m_csr_value = tagged Valid vrg_pmpaddr [15];

	    csr_addr_mcycle:    m_csr_value = tagged Valid (truncate (rg_mcycle));
	    csr_addr_minstret:  m_csr_value = tagged Valid (truncate (rg_minstret));
`ifdef RV32
	    csr_addr_mcycleh:   m_csr_value = tagged Valid (rg_mcycle [63:32]);
	    csr_addr_minstreth: m_csr_value = tagged Valid (rg_minstret [63:32]);
`endif

	    csr_addr_mcountinhibit: m_csr_value = tagged Valid (mcountinhibit_to_word (ctr_inhibit));

	    csr_addr_tselect:  m_csr_value = tagged Valid rg_tselect;
	    csr_addr_tdata1:   m_csr_value = tagged Valid rg_tdata1;
	    csr_addr_tdata2:   m_csr_value = tagged Valid rg_tdata2;
	    csr_addr_tdata3:   m_csr_value = tagged Valid rg_tdata3;

`ifdef INCLUDE_GDB_CONTROL
	    csr_addr_dcsr:       begin
				    Bit #(32) dcsr_nmip_mask = 'b_1000;
				    Bit #(32) dcsr = (rg_nmi
						      ? (rg_dcsr | dcsr_nmip_mask)
						      : (rg_dcsr & (~ dcsr_nmip_mask)));
				    m_csr_value = tagged Valid zeroExtend (dcsr);
				 end
	    csr_addr_dpc:        m_csr_value = tagged Valid getOffset (rg_dpcc);
	    csr_addr_dscratch0:  m_csr_value = tagged Valid rg_dscratch0;
	    csr_addr_dscratch1:  m_csr_value = tagged Valid rg_dscratch1;
`endif

	    default: m_csr_value = tagged Invalid;
	 endcase
      end

      return m_csr_value;
   endfunction: fv_csr_read

   // ----------------------------------------------------------------
   // CSR writes
   // Returns the "actual value written": many CSRs have WARL/WLRL semantics, i.e., the
   // value attempted to be written is transformed in an implementation-defined way into
   // a value actually written.  In the extreme case of CSRs with hardwired value, the
   // transformation is to ignore the attempted write-value and return the hardwired value.
   // The value returned is conceptually the value you'd read if you did a subsequent CSR read.

   function ActionValue #(CSR_Write_Result) fav_csr_write (CSR_Addr csr_addr, WordXL wordxl);
      actionvalue
	 Bool            success = True;
	 WordXL          new_csr_value  = ?;
	 Maybe #(WordXL) m_new_csr_value2 = tagged Invalid;

`ifdef PERFORMANCE_MONITORING
`ifdef RV32
	 if ((csr_addr_mhpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31)) begin
	    let new_value = { ctrs [csr_addr - csr_addr_mhpmcounter3][63:32], wordxl };
	    perf_counters.write_counter (csr_addr - csr_addr_mhpmcounter3, new_value);
	    new_csr_value = wordxl;
	 end
	 else if ((csr_addr_mhpmcounter3h <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31h)) begin
	    let new_value = { wordxl, ctrs [csr_addr - csr_addr_mhpmcounter3h][31:0] };
	    perf_counters.write_counter (csr_addr - csr_addr_mhpmcounter3h, new_value);
	    new_csr_value = wordxl;
	 end
`else
	 if ((csr_addr_mhpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31)) begin
	    perf_counters.write_counter (truncate (pack (csr_addr - csr_addr_mhpmcounter3)), wordxl);
	    new_csr_value = wordxl;
	 end
`endif
	 else if ((csr_addr_mhpmevent3 <= csr_addr) && (csr_addr <= csr_addr_mhpmevent31)) begin
	    Bit #(TLog #(No_Of_Evts)) new_val = truncate (wordxl);
	    perf_counters.write_ctr_sel (truncate (pack (csr_addr - csr_addr_mhpmevent3)), new_val);
	    new_csr_value = zeroExtend (new_val);
	 end
`else // !PERFORMANCE_MONITORING
	 if ((csr_addr_mhpmcounter3 <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31)) begin
	    new_csr_value = 0;    // hardwired
	 end
`ifdef RV32
	 else if ((csr_addr_mhpmcounter3h <= csr_addr) && (csr_addr <= csr_addr_mhpmcounter31h)) begin
	    new_csr_value = 0;    // hardwired
	 end
`endif
	 else if ((csr_addr_mhpmevent3 <= csr_addr) && (csr_addr <= csr_addr_mhpmevent31)) begin
	    new_csr_value = 0;    // hardwired
	 end
`endif // PERFORMANCE_MONITORING
	 else
	    case (csr_addr)
	       // User mode csrs
`ifdef ISA_F
	       csr_addr_fflags:     begin
				       new_csr_value = zeroExtend (wordxl [4:0]);
				       rg_fflags    <= wordxl [4:0];

				       // Update mstatus.fs to 'dirty'
				       let old_mstatus  = csr_mstatus.mv_read;
				       let new_mstatus1 = fv_assign_bits (old_mstatus,
									  fromInteger (mstatus_fs_bitpos),
									  fs_xs_dirty);
				       let new_mstatus2 <- csr_mstatus.mav_write (misa, new_mstatus1);
				       m_new_csr_value2 = tagged Valid new_mstatus2;
				    end
	       csr_addr_frm:        begin
				       new_csr_value = zeroExtend (wordxl [2:0]);
				       rg_frm       <= wordxl [2:0];

				       // Update mstatus.fs to 'dirty'
				       let old_mstatus  = csr_mstatus.mv_read;
				       let new_mstatus1 = fv_assign_bits (old_mstatus,
									  fromInteger (mstatus_fs_bitpos),
									  fs_xs_dirty);
				       let new_mstatus2 <- csr_mstatus.mav_write (misa, new_mstatus1);
				       m_new_csr_value2 = tagged Valid new_mstatus2;
				    end
	       csr_addr_fcsr:       begin
				       // Update fcsr itself
				       new_csr_value = zeroExtend (wordxl [7:0]);
				       rg_fflags    <= wordxl [4:0];
				       rg_frm       <= wordxl [7:5];

				       // Update mstatus.fs to 'dirty'
				       let old_mstatus  = csr_mstatus.mv_read;
				       let new_mstatus1 = fv_assign_bits (old_mstatus,
									 fromInteger (mstatus_fs_bitpos),
									 fs_xs_dirty);
				       let new_mstatus2 <- csr_mstatus.mav_write (misa, new_mstatus1);
				       m_new_csr_value2 = tagged Valid new_mstatus2;
				    end
`endif

`ifdef ISA_PRIV_S
	       csr_addr_sstatus:    begin
				       new_csr_value <- csr_mstatus.mav_sstatus_write (misa, wordxl);
				    end
	       csr_addr_sedeleg:    begin
				       new_csr_value = 0;               // Hardwired to 0 (no delegation)
				    end
	       csr_addr_sideleg:    begin
				       new_csr_value = 0;               // Hardwired to 0 (no delegation)
				    end
	       csr_addr_sie:        begin
				       new_csr_value <- csr_mie.mav_sie_write (misa, wordxl);
				    end
	       csr_addr_stvec:      begin
				       let stvec     = word_to_mtvec (wordxl);
				       new_csr_value = mtvec_to_word (stvec);
`ifdef ISA_CHERI
				       rg_stcc      <= cast (update_scr_via_csr (rg_stcc_unpacked, new_csr_value, False));
`else
				       rg_stvec     <= stvec;
`endif
				    end
	       csr_addr_scounteren: new_csr_value = 0;    // Hardwired to zero

	       csr_addr_sscratch:   begin
				       new_csr_value = wordxl;
				       rg_sscratch  <= new_csr_value;
				    end
	       csr_addr_sepc:       begin
`ifdef ISA_C
				       new_csr_value = (wordxl & (~ 1));    // sepc [0] always zero
`else
				       new_csr_value = (wordxl & (~ 3));    // sepc [1:0] always zero
`endif
`ifdef ISA_CHERI
				       rg_sepcc     <= cast (update_scr_via_csr (rg_sepcc_unpacked, new_csr_value, False));
`else
				       rg_sepc      <= new_csr_value;
`endif
				    end
	       csr_addr_scause:     begin
				       let mcause    = word_to_mcause (wordxl);
				       new_csr_value = mcause_to_word (mcause);
				       rg_scause    <= mcause;
				    end
	       csr_addr_stval:      begin
				       new_csr_value = wordxl;
				       rg_stval     <= new_csr_value;
				    end
	       csr_addr_sip:        begin
				       new_csr_value <- csr_mip.mav_sip_write (misa, wordxl);
				    end
	       csr_addr_satp:       begin
				       new_csr_value = wordxl;
				       rg_satp      <= new_csr_value;
				    end
	       csr_addr_medeleg:    begin
				       WordXL mask   = 'h_B3FF;  // 16 bits relevant and some are 0
`ifdef ISA_CHERI
`ifdef RV64
				       mask          = (mask | (1 << exc_code_LOAD_CAP_PAGE_FAULT));
				       mask          = (mask | (1 << exc_code_STORE_AMO_CAP_PAGE_FAULT));
`endif
				       mask          = (mask | (1 << exc_code_CHERI));
`endif
				       new_csr_value = (wordxl & mask);
				       rg_medeleg   <= truncate (new_csr_value);
				    end
	       csr_addr_mideleg:    begin
				       new_csr_value = (wordxl & 'h_0FFF);  // 12 bits relevant
				       rg_mideleg   <= truncate (new_csr_value);
				    end
`endif

	       // Machine mode
	       csr_addr_mvendorid:  new_csr_value = mvendorid;    // hardwired
	       csr_addr_marchid:    new_csr_value = marchid;      // hardwired
	       csr_addr_mimpid:     new_csr_value = mimpid;       // hardwired
	       csr_addr_mhartid:    new_csr_value = mhartid;      // hardwired
	       csr_addr_mstatus:    begin
				      new_csr_value <- csr_mstatus.mav_write (misa, wordxl);
				    end
	       csr_addr_misa:       begin
				       new_csr_value = misa_to_word (misa);
				    end
	       csr_addr_mie:        begin
				       new_csr_value <- csr_mie.mav_write (misa, wordxl);
				    end
	       csr_addr_mtvec:      begin
				       let mtvec     = word_to_mtvec (wordxl);
				       new_csr_value = mtvec_to_word (mtvec);
`ifdef ISA_CHERI
				       rg_mtcc      <= cast (update_scr_via_csr (rg_mtcc_unpacked, new_csr_value, False));
`else
				       rg_mtvec     <= mtvec;
`endif
				    end
	       csr_addr_mcounteren: begin
				       let mcounteren = word_to_mcounteren (wordxl);
				       new_csr_value  = mcounteren_to_word (mcounteren);
				       rg_mcounteren <= mcounteren;
				    end
	       csr_addr_mscratch:   begin
				       new_csr_value = wordxl;
				       rg_mscratch  <= new_csr_value;
				    end
	       csr_addr_mepc:       begin
`ifdef ISA_C
				       new_csr_value = (wordxl & (~ 1));    // mepc [0] always zero
`else
				       new_csr_value = (wordxl & (~ 3));    // mepc [1:0] always zero
`endif
`ifdef ISA_CHERI
				       rg_mepcc     <= cast (update_scr_via_csr (rg_mepcc_unpacked, new_csr_value, False));
`else
				       rg_mepc      <= new_csr_value;
`endif
				    end
	       csr_addr_mcause:     begin
				       let mcause    = word_to_mcause (wordxl);
				       new_csr_value = mcause_to_word (mcause);
				       rg_mcause    <= mcause;
				    end
	       csr_addr_mtval:      begin
				       new_csr_value = wordxl;
				       rg_mtval     <= new_csr_value;
				    end
	       csr_addr_mip:        begin
				       new_csr_value <- csr_mip.mav_write (misa, wordxl);
				    end
	       // TODO: PMPs
	       // csr_pmpcfg0:   rf_pmpcfg.upd (0, wordxl);
	       // csr_pmpcfg1:   rf_pmpcfg.upd (1, wordxl);
	       // csr_pmpcfg2:   rf_pmpcfg.upd (2, wordxl);
	       // csr_pmpcfg3:   rf_pmpcfg.upd (3, wordxl);

	       // csr_pmpaddr0:  vrg_pmpaddr [0] <= wordxl;
	       // csr_pmpaddr1:  vrg_pmpaddr [1] <= wordxl;
	       // csr_pmpaddr2:  vrg_pmpaddr [2] <= wordxl;
	       // csr_pmpaddr3:  vrg_pmpaddr [3] <= wordxl;
	       // csr_pmpaddr4:  vrg_pmpaddr [4] <= wordxl;
	       // csr_pmpaddr5:  vrg_pmpaddr [5] <= wordxl;
	       // csr_pmpaddr6:  vrg_pmpaddr [6] <= wordxl;
	       // csr_pmpaddr7:  vrg_pmpaddr [7] <= wordxl;
	       // csr_pmpaddr8:  vrg_pmpaddr [8] <= wordxl;
	       // csr_pmpaddr9:  vrg_pmpaddr [9] <= wordxl;
	       // csr_pmpaddr10: vrg_pmpaddr [10] <= wordxl;
	       // csr_pmpaddr11: vrg_pmpaddr [11] <= wordxl;
	       // csr_pmpaddr12: vrg_pmpaddr [12] <= wordxl;
	       // csr_pmpaddr13: vrg_pmpaddr [13] <= wordxl;
	       // csr_pmpaddr14: vrg_pmpaddr [14] <= wordxl;
	       // csr_pmpaddr15: vrg_pmpaddr [15] <= wordxl;

`ifdef RV32
	       csr_addr_mcycle:     begin
				       new_csr_value = wordxl;
				       rw_mcycle.wset ({ rg_mcycle   [63:32], wordxl });
				    end
	       csr_addr_minstret:   begin
				       new_csr_value = wordxl;
				       rw_minstret.wset ({ rg_minstret [63:32], wordxl });
				    end
	       csr_addr_mcycleh:    begin
				       new_csr_value = wordxl;
				       rw_mcycle.wset ({ wordxl, rg_mcycle   [31:0] });
				    end
	       csr_addr_minstreth:  begin
				       new_csr_value = wordxl;
				       rw_minstret.wset ({ wordxl, rg_minstret [31:0] });
				    end
`else
	       csr_addr_mcycle:     begin
				       new_csr_value = wordxl;
				       rw_mcycle.wset (new_csr_value);
				    end
	       csr_addr_minstret:   begin
				       new_csr_value = wordxl;
				       rw_minstret.wset (new_csr_value);
				    end
`endif
	       csr_addr_mcountinhibit: begin
`ifdef PERFORMANCE_MONITORING
				       let mcountinhibit = word_to_mcountinhibit (wordxl);
				       new_csr_value = mcountinhibit_to_word (mcountinhibit);

				       w_ctr_inhib_ir_cy <= { mcountinhibit.ir, mcountinhibit.cy };
				       perf_counters.write_ctr_inhibit (mcountinhibit.hpm);
`else
				       new_csr_value = 0;
`endif
				   end
	       csr_addr_tselect:   begin
				      // Until we implement trigger functionality,
				      // return tselect always contains 0
				      new_csr_value = 0;    // wordxl
				      rg_tselect   <= new_csr_value;
				   end
	       csr_addr_tdata1:    begin
				      // Until we implement trigger functionality,
				      // force 'type' field ([xlen-1:xlen-4]) to zero
				      // meaning: 'There is no trigger at this tselect'
				      new_csr_value = (wordxl & ('1 >> 4));
				      rg_tdata1    <= new_csr_value;
				   end
	       csr_addr_tdata2:    begin
				      new_csr_value = wordxl;
				      rg_tdata2    <= new_csr_value;
				   end
	       csr_addr_tdata3:    begin
				      new_csr_value = wordxl;
				      rg_tdata3    <= new_csr_value;
				   end

`ifdef INCLUDE_GDB_CONTROL
	       csr_addr_dcsr:       begin
				       Bit #(32) new_dcsr
				       = {rg_dcsr [31:28],   // xdebugver: read-only
					  rg_dcsr [27:16],   // reserved
					  wordxl  [15:12],   // ebreakm/s/u,
					  wordxl  [11:9],    // stepie, stopcount, stoptime
					  rg_dcsr [8:6],     // cause: read-only
					  rg_dcsr [5],       // reserved
					  wordxl  [4],       // mprvn
					  rg_dcsr [3],       // nmip: read-only
					  wordxl  [2],       // step
					  wordxl  [1:0]};    // prv
				       new_csr_value = zeroExtend (new_dcsr);
				       rg_dcsr      <= new_dcsr;
				    end
	       csr_addr_dpc:        begin
				       new_csr_value = wordxl;
				       rg_dpcc      <= setOffset (rg_dpcc, new_csr_value).value; // TODO unrepresentable?
				    end
	       csr_addr_dscratch0:  begin
				       new_csr_value = wordxl;
				       rg_dscratch0 <= new_csr_value;
				    end
	       csr_addr_dscratch1:  begin
				       new_csr_value = wordxl;
				       rg_dscratch1 <= new_csr_value;
				    end
`endif

	       default: success = False;
	    endcase

	 if ((! success) && (cfg_verbosity > 1))
	    $display ("%0d: ERROR: CSR-write addr 0x%0h val 0x%0h not successful", rg_mcycle,
		      csr_addr, wordxl);

	 return CSR_Write_Result {new_csr_value:    new_csr_value,
				  m_new_csr_value2: m_new_csr_value2};
      endactionvalue
   endfunction: fav_csr_write

`ifdef ISA_CHERI

   // ----------------------------------------------------------------
   // SCR writes

   function ActionValue #(CapReg) fav_scr_write (SCR_Addr scr_addr, CapReg cap);
      actionvalue
	 Bool    success = True;
	 CapReg  result  = nullCap;
	 CapPipe cap_unpacked = cast (cap);

	 case (scr_addr)
`ifdef ISA_PRIV_S
	    scr_addr_STCC: begin
	       let new_offset = mtvec_to_word (word_to_mtvec (getOffset (cap_unpacked)));
	       cap_unpacked = update_scr_via_csr (cap_unpacked, new_offset, False);
	       // This can be done much more efficiently by breaking into the compressed cap format
	       if (getBaseAlignment (cap_unpacked) == 0) begin
		  rg_stcc <= cast (cap_unpacked);
		  result = cast (cap_unpacked);
	       end
	    end
	    scr_addr_STDC: begin
	       rg_stdc <= cap;
	       result = cap;
	    end
	    scr_addr_SEPCC: begin
	       let new_offset = getOffset (cap_unpacked);
`ifdef ISA_C
	       Bool change_made = new_offset [0] != 1'b0;
	       new_offset [0] = 1'b0;
`else
	       Bool change_made = new_offset [1:0] != 2'b0;
	       new_offset [1:0] = 2'b0;
`endif
	       cap_unpacked = update_scr_via_csr (cap_unpacked, new_offset, (! change_made));
	       rg_sepcc <= cast (cap_unpacked);
	       result = cast (cap_unpacked);
	    end
	    scr_addr_SScratchC: begin
	       rg_sscratchc <= cap;
	       result = cap;
	    end
`endif
	    scr_addr_MTCC: begin
	       let new_offset = mtvec_to_word (word_to_mtvec (getOffset (cap_unpacked)));
	       cap_unpacked = update_scr_via_csr (cap_unpacked, new_offset, False);
	       // This can be done much more efficiently by breaking into the compressed cap format
	       if (getBaseAlignment (cap_unpacked) == 0) begin
		  rg_mtcc <= cast (cap_unpacked);
		  result = cast (cap_unpacked);
	       end
	    end
	    scr_addr_MTDC: begin
	       rg_mtdc <= cap;
	       result = cap;
	    end
	    scr_addr_MEPCC: begin
	       let new_offset = getOffset (cap_unpacked);
`ifdef ISA_C
	       Bool change_made = new_offset [0] != 1'b0;
	       new_offset [0] = 1'b0;
`else
	       Bool change_made = new_offset [1:0] != 2'b0;
	       new_offset [1:0] = 2'b0;
`endif
	       cap_unpacked = update_scr_via_csr (cap_unpacked, new_offset, (! change_made));
	       rg_mepcc <= cast (cap_unpacked);
	       result = cast (cap_unpacked);
	    end
	    scr_addr_MScratchC: begin
	       rg_mscratchc <= cap;
	       result = cap;
	    end
	    default: success = False;
	 endcase

	 if ((! success) && (cfg_verbosity > 1))
	    $display ("%0d: ERROR: SCR-write addr 0x%0h val ", rg_mcycle, scr_addr, fshow (cap), " not successful");

	 return result;
      endactionvalue
   endfunction: fav_scr_write

`endif

   // Access permission
   function AccessPerms fv_access_permitted (Priv_Mode  priv, CSR_Addr  csr_addr,  Bool read_not_write);
      AccessPerms access = fv_csr_exists_and_asr (csr_addr, read_not_write);    // Is this CSR implemented?

      Bool priv_ok = priv >= csr_addr [9:8];      // Accessible at current privilege?

      // TVM fault: cannot access SATP if MSTATUS.TVM is set
      Bool tvm_fault = ((csr_addr == csr_addr_satp) && (csr_mstatus.mv_read [mstatus_tvm_bitpos] == 1'b1));

      // TODO: MxDELEG fault: MIDELEG and MEDELEG do not exist in
      //     systems with only m_Priv and systems with m_Priv and u_Priv but
      //     without support for U-mode traps

      Bool rw_ok = (read_not_write || (csr_addr [11:10] != 2'b11));

      return AccessPerms {exists: access.exists && priv_ok && (! tvm_fault) && rw_ok, requires_asr: access.requires_asr};
   endfunction: fv_access_permitted

`ifdef ISA_CHERI
   // Access permission
   function AccessPerms fv_access_permitted_scr (Priv_Mode  priv, SCR_Addr  scr_addr,  Bool read_not_write);
      AccessPerms access  = fv_scr_exists_and_asr (scr_addr, read_not_write);    // Is this SCR implemented?

      Bool exists = access.exists;
      Bool priv_ok = priv >= scr_addr [4:3];
      Bool access_PCC = scr_addr == scr_addr_PCC; // Accesses to PCC that reach this point must be writes, so are illegal

      return AccessPerms {exists: access.exists && priv_ok && (! access_PCC), requires_asr: access.requires_asr};
   endfunction: fv_access_permitted_scr
`endif

   // ================================================================
   // For debugging

   function Action fa_show_trap_csrs (Priv_Mode priv,
				      WordXL ip, WordXL ie,
				      Bit #(29) edeleg, Bit #(12) ideleg,
				      MCause cause, WordXL status, MTVec tvec,
				      WordXL epc, WordXL tval);
      action
	 $write ("    priv %0d: ", priv);
	 $write (" ip: 0x%0h", ip);
	 $write (" ie: 0x%0h", ie);
	 $write (" edeleg: 0x%0h", edeleg);
	 $write (" ideleg: 0x%0h", ideleg);
	 $write (" cause:", fshow (cause));
	 $display ("");

	 $write ("        ");
	 $write (" status: 0x%0h", status);
	 $write (" tvec: 0x%0h", mtvec_to_word (tvec));
	 $write (" epc: 0x%0h", epc);
	 $write (" tval: 0x%0h", tval);
	 $display ("");
      endaction
   endfunction

   // ================================================================
   // INTERFACE

   // ----------------------------------------------------------------
   // Help functions for interface methods
`ifdef ISA_F
   function Bit #(5) fv_update_fcsr_fflags (Bit #(5) flags);
      return (rg_fflags | flags);
   endfunction
`endif

   function WordXL fv_update_mstatus_fs (Bit #(2) fs);
      let old_mstatus = csr_mstatus.mv_read;
      let new_mstatus = fv_assign_bits (old_mstatus, fromInteger (mstatus_fs_bitpos), fs);
      return csr_mstatus.mv_write (misa, new_mstatus);
   endfunction

   // ----------------------------------------------------------------
   // Reset
   interface Server server_reset;
      interface Put request;
	 method Action put (Token token);
	    rg_state <= RF_RESET_START;

	    // This response is placed here, and not in rl_reset_loop, because
	    // reset_loop can happen on power-up, where no response is expected.
	    f_reset_rsps.enq (?);
	 endmethod
      endinterface
      interface Get response;
	 method ActionValue #(Token) get if (rg_state == RF_RUNNING);
	    let token <- pop (f_reset_rsps);
	    return token;
	 endmethod
      endinterface
   endinterface

   // CSR read (w.o. side effect)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

   // CSR read (w.o. side effect)
   method Maybe #(Word) read_csr_port2 (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

`ifdef ISA_CHERI
   method Maybe #(CapReg) read_scr (SCR_Addr scr_addr);
      return fv_scr_read (scr_addr);
   endmethod
`endif

   // CSR read (w. side effect)
   method ActionValue #(Maybe #(Word)) mav_read_csr (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

   // CSR write
   method ActionValue #(CSR_Write_Result) mav_csr_write (CSR_Addr csr_addr, WordXL word);
      let result <- fav_csr_write (csr_addr, word);
      return result;
   endmethod

`ifdef ISA_CHERI
   // SCR write
   method ActionValue #(CapReg) mav_scr_write (SCR_Addr scr_addr, CapReg cap);
      let result <- fav_scr_write (scr_addr, cap);
      return result;
   endmethod
`endif

   // Read MISA
   method MISA read_misa;
      return misa;
   endmethod

`ifdef ISA_F
   // Read FCSR.FRM
   method Bit# (3) read_frm;
      return rg_frm;
   endmethod

   method Bit# (5) read_fflags;
      return rg_fflags;
   endmethod

   // Update FCSR.FFLAGS
   method Bit #(5) mv_update_fcsr_fflags (Bit #(5) flags);
      return fv_update_fcsr_fflags (flags);
   endmethod
   method Action ma_update_fcsr_fflags (Bit#(5) flags);
      rg_fflags <= fv_update_fcsr_fflags (flags);
   endmethod

   // Update MSTATUS.FS
   method WordXL mv_update_mstatus_fs (Bit #(2) fs);
      return fv_update_mstatus_fs (fs);
   endmethod

   method Action ma_update_mstatus_fs (Bit #(2) fs);
      let old_mstatus = csr_mstatus.mv_read;
      let new_mstatus = fv_assign_bits (old_mstatus, fromInteger (mstatus_fs_bitpos), fs);
      csr_mstatus.ma_write (misa, new_mstatus);
   endmethod
`endif

   // Read MSTATUS
   method WordXL read_mstatus;
      return  csr_mstatus.mv_read;
   endmethod

`ifdef ISA_PRIV_S
   // Read SSTATUS
   method WordXL read_sstatus;
      return  csr_mstatus.mv_sstatus_read;
   endmethod
`endif

`ifdef ISA_PRIV_U
   // Read USTATUS
   method WordXL read_ustatus;
      return  csr_mstatus.mv_ustatus_read;
   endmethod
`endif

   // Read SATP
   method WordXL read_satp;
`ifdef ISA_PRIV_S
      return  rg_satp;
`else
      return  ?;
`endif
   endmethod

   // CSR Trap actions
   method ActionValue #(Trap_Info_CSR)
	  csr_trap_actions (Priv_Mode  from_priv,
`ifdef ISA_CHERI
			    CapPipe    pcc,
`else
			    WordXL     pc,
`endif
			    Bool       nmi,          // non-maskable interrupt
			    Bool       interrupt,    // other interrupt
`ifdef ISA_CHERI
			    CHERI_Exc_Code cheri_exc_code,
			    Bit#(6)        cheri_exc_reg,
`endif
			    Exc_Code   exc_code,
			    WordXL     xtval);

      if (cfg_verbosity > 1) begin
	 $display ("%0d: CSR_Regfile.csr_trap_actions:", rg_mcycle);
	 $display ("    from priv %0d  pc 0x%0h  interrupt %0d  exc_code %0d  xtval 0x%0h",
		   from_priv,
`ifdef ISA_CHERI
		   getOffset (pcc),
`else
		   pc,
`endif
		   pack (interrupt), exc_code, xtval);
`ifdef ISA_PRIV_S
	 fa_show_trap_csrs (s_Priv_Mode, csr_mip.mv_read, csr_mie.mv_read, 0, 0, rg_scause,
			    csr_mstatus.mv_sstatus_read,
			    rg_stvec, rg_sepc, rg_stval);
`endif
	 fa_show_trap_csrs (m_Priv_Mode, csr_mip.mv_read, csr_mie.mv_read, rg_medeleg, rg_mideleg, rg_mcause,
			    csr_mstatus.mv_read,
			    rg_mtvec, rg_mepc, rg_mtval);
      end

      let new_priv    = (nmi
			 ? m_Priv_Mode
			 : fv_new_priv_on_exception (misa,
						     from_priv,
						     interrupt,
						     exc_code,
						     rg_medeleg,
						     rg_mideleg,
						     sedeleg,
						     sideleg));
      let new_mstatus  = fv_new_mstatus_on_exception (csr_mstatus.mv_read, from_priv, new_priv);
      let new_status  <- csr_mstatus.mav_write (misa, new_mstatus);

`ifdef ISA_CHERI
      let capexc = XCCSR {cheri_exc_reg: cheri_exc_reg, cheri_exc_code: cheri_exc_code};
      if (exc_code == exc_code_CHERI) xtval = capexc_to_xtval (capexc);
      let xtcc = ?;
`endif

      let  xcause      = (nmi
			  ? MCause {interrupt: 0, exc_code: 0 }
			  : MCause {interrupt: pack (interrupt), exc_code: exc_code});
      let  is_vectored = (rg_mtvec.mode == VECTORED);
      Addr exc_pc      = (extend (rg_mtvec.base)) << 2;

      if (nmi) begin
`ifdef ISA_CHERI
	 rg_mepcc   <= cast (pcc);
`else
	 rg_mepc    <= pc;
`endif
	 rg_mtval   <= xtval;
	 rg_mcause  <= xcause;
	 exc_pc      = rg_nmi_vector;
	 is_vectored = False;
      end
      else if (new_priv == m_Priv_Mode) begin
`ifdef ISA_CHERI
	 rg_mepcc   <= cast (pcc);
	 xtcc        = rg_mtcc_unpacked;
	 if (exc_code == exc_code_CHERI)
	    rg_mccsr <= capexc;
`else
	 rg_mepc    <= pc;
`endif
	 rg_mtval   <= xtval;
	 rg_mcause  <= xcause;
      end
`ifdef ISA_PRIV_S
      else if (new_priv == s_Priv_Mode) begin
`ifdef ISA_CHERI
	 rg_sepcc   <= cast (pcc);
	 xtcc        = rg_stcc_unpacked;
	 if (exc_code == exc_code_CHERI)
	    rg_sccsr <= capexc;
`else
	 rg_sepc    <= pc;
`endif
	 rg_scause  <= xcause;
	 rg_stval   <= xtval;

	 is_vectored = (rg_stvec.mode == VECTORED);
	 new_status  = fv_mstatus_to_sstatus (new_status);
	 exc_pc      = (extend (rg_stvec.base)) << 2;
      end
`endif
      // TODO: if (new_priv == u_Priv_Mode)

      // Adjust the exception PC if xTVEC mode bits so indicate
      Addr vector_offset = (extend (exc_code)) << 2;
      if (interrupt && is_vectored)
	 exc_pc = exc_pc + vector_offset;
      CapPipe exc_pcc  = setOffset (xtcc, exc_pc).value; // TODO representability check

      if (cfg_verbosity > 1) begin
	 $write ("    Return: new pc 0x%0h  ", exc_pc);
	 $write (" new mstatus:", fshow_mstatus (misa, new_status));
	 $write (" new xcause:", fshow (xcause));
	 $write (" new priv %0d", new_priv);
	 $display ("");
      end

      return (Trap_Info_CSR {
`ifdef ISA_CHERI
			 pcc      : cast (exc_pcc),             // New PCC
`else
			 pc       : exc_pc,                     // New PC
`endif
			 mstatus  : new_status,                 // New mstatus/sstatus/ustatus
			 mcause   : mcause_to_word  (xcause),   // New mcause
			 priv     : new_priv});                 // New priv
   endmethod: csr_trap_actions

   // CSR RET actions (return from exception)
   method ActionValue #(Tuple3 #(
`ifdef ISA_CHERI
				 CapPipe,
`else
				 Addr,
`endif
				 Priv_Mode, Word)) csr_ret_actions (Priv_Mode from_priv);
      match { .new_mstatus, .to_priv } = fv_new_mstatus_on_ret (misa, csr_mstatus.mv_read, from_priv);
      csr_mstatus.ma_write (misa, new_mstatus);
      CapPipe next_pcc = rg_mepcc_unpacked;
`ifdef ISA_PRIV_S
      if (from_priv != m_Priv_Mode)
	 next_pcc = rg_sepcc_unpacked;
`endif
      if (getKind (next_pcc) == SENTRY)
	 next_pcc = setKind (next_pcc, UNSEALED);
      return tuple3 (
`ifdef ISA_CHERI
		     next_pcc,
`else
		     next_pc,
`endif
		     to_priv, new_mstatus);
   endmethod

   // Read MINSTRET
   method Bit #(64) read_csr_minstret;
      return rg_minstret;
   endmethod

   // Increment MINSTRET
   method Action csr_minstret_incr;
      pw_minstret_incr.send;
   endmethod

   // Read MCYCLE
   method Bit #(64) read_csr_mcycle;
      return rg_mcycle;
   endmethod

   // Read MTIME
   method Bit #(64) read_csr_mtime;
      return rg_mtime;
   endmethod

`ifdef PERFORMANCE_MONITORING
   method Action send_performance_events (Vector #(No_Of_Evts, Bit #(Counter_Width)) evts);
      perf_counters.send_performance_events (evts);
   endmethod
`endif

`ifdef ISA_CHERI
   // Access permission
   method AccessPerms access_permitted_scr (Priv_Mode  priv, SCR_Addr  scr_addr,  Bool read_not_write);
      return fv_access_permitted_scr (priv, scr_addr, read_not_write);
   endmethod
`endif

   // Access permission
   method AccessPerms access_permitted_1 (Priv_Mode  priv, CSR_Addr  csr_addr,  Bool read_not_write);
      return fv_access_permitted (priv, csr_addr, read_not_write);
   endmethod

   method AccessPerms access_permitted_2 (Priv_Mode  priv, CSR_Addr  csr_addr,  Bool read_not_write);
      return fv_access_permitted (priv, csr_addr, read_not_write);
   endmethod

   // Fault on reading counters?
   // XXX: No scounteren implemented properly (and hardwired to 0 yet treated as all 1s)
   method Bool csr_counter_read_fault (Priv_Mode  priv, CSR_Addr  csr_addr);
      return (   ((priv == s_Priv_Mode) || (priv == u_Priv_Mode))
	      && (   ((csr_addr == csr_addr_cycle)   && (rg_mcounteren.cy == 0))
		  || ((csr_addr == csr_addr_time)    && (rg_mcounteren.tm == 0))
		  || ((csr_addr == csr_addr_instret) && (rg_mcounteren.ir == 0))
		  || (   (csr_addr_hpmcounter3  <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31)
		      && (rg_mcounteren.hpm [csr_addr - csr_addr_hpmcounter3] == 0))
`ifdef RV32
		  || (   (csr_addr_hpmcounter3h  <= csr_addr) && (csr_addr <= csr_addr_hpmcounter31h)
		      && (rg_mcounteren.hpm [csr_addr - csr_addr_hpmcounter3h] == 0))
`endif
		  ));
   endmethod

   // Read MIP
   method WordXL csr_mip_read;
      return csr_mip.mv_read;
   endmethod

   // Interrupts
   method Action m_external_interrupt_req (Bool set_not_clear);
      csr_mip.m_external_interrupt_req  (set_not_clear);
      if (cfg_verbosity > 1)
	 $display ("%0d: CSR_RegFile: m_external_interrupt_req: %x", rg_mcycle, set_not_clear);
   endmethod

   method Action s_external_interrupt_req (Bool set_not_clear);
      csr_mip.s_external_interrupt_req  (set_not_clear);
      if (cfg_verbosity > 1)
	 $display ("%0d: CSR_RegFile: s_external_interrupt_req: %x", rg_mcycle, set_not_clear);
   endmethod

   method Action timer_interrupt_req (Bool set_not_clear);
      csr_mip.timer_interrupt_req  (set_not_clear);
      if (cfg_verbosity > 1)
	 $display ("%0d: CSR_RegFile: timer_interrupt_req: %x", rg_mcycle, set_not_clear);
   endmethod

   method Action software_interrupt_req (Bool set_not_clear);
      csr_mip.software_interrupt_req (set_not_clear);
      if (cfg_verbosity > 1)
	 $display ("%0d: CSR_RegFile: software_interrupt_req: %x", rg_mcycle, set_not_clear);
   endmethod

   method Maybe #(Exc_Code) interrupt_pending (Priv_Mode cur_priv);
      return fv_interrupt_pending (misa,
				   csr_mstatus.mv_read,
				   csr_mip.mv_read,
				   csr_mie.mv_read,
				   rg_mideleg,
				   sideleg,
				   cur_priv);
   endmethod

   // WFI ignores mstatus ies and ideleg regs
   method Bool wfi_resume;
      WordXL mip = csr_mip.mv_read;
      WordXL mie = csr_mie.mv_read;
      return ((mip & mie) != 0);
   endmethod

   // ----------------
   // Non-maskable interrupts

   method Action nmi_req (Bool set_not_clear);
      rg_nmi <= set_not_clear;
   endmethod

   method Bool nmi_pending;
      return rg_nmi;
   endmethod

   // ----------------
   // Methods when Debug Module is present

`ifdef INCLUDE_GDB_CONTROL
   // Read dpcc
   method CapPipe read_dpcc ();
      return rg_dpcc;
   endmethod

   // Update dpcc
   method Action write_dpcc (CapPipe pcc);
      rg_dpcc <= pcc;
   endmethod

   // Break should enter Debug Mode
   method Bool dcsr_break_enters_debug (Priv_Mode cur_priv);
      return case (cur_priv)
		m_Priv_Mode: (rg_dcsr [15] == 1'b1);
		s_Priv_Mode: (rg_dcsr [13] == 1'b1);
		u_Priv_Mode: (rg_dcsr [12] == 1'b1);
	     endcase;
   endmethod

   // Read dcsr.step
   method Bool read_dcsr_step ();
      return unpack (rg_dcsr [2]);
   endmethod

   // Update 'cause' and 'priv' in DCSR
   method Action write_dcsr_cause_priv (DCSR_Cause  cause, Priv_Mode  priv);
      Bit #(3) b3 = pack (cause);
      rg_dcsr <= { rg_dcsr [31:9], b3, rg_dcsr [5:2], priv };
   endmethod

`endif

   // ----------------
   // Debugging this module

   method Action debug;
      $display ("mstatus = 0x%0h", csr_mstatus.mv_read);
`ifdef ISA_PRIV_S
      $display ("sstatus = 0x%0h", csr_mstatus.mv_sstatus_read);
`endif
      $display ("mip     = 0x%0h", csr_mip.mv_read);
`ifdef ISA_PRIV_S
      $display ("sip     = 0x%0h", csr_mip.mv_sip_read);
`endif
      $display ("mie     = 0x%0h", csr_mie.mv_read);
`ifdef ISA_PRIV_S
      $display ("sie     = 0x%0h", csr_mie.mv_sie_read);
`endif
   endmethod
endmodule

// ================================================================

endpackage
