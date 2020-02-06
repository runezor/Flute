// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package CPU_Globals;

// ================================================================
// Types common to multiple CPU stages,
// including types communicated from stage to stage.

// ================================================================
// BSV library imports

// None

// ----------------
// BSV additional libs

// None

// ================================================================
// Project imports

import ISA_Decls :: *;

`ifdef ISA_CHERI
import CHERICap :: *;
import CHERICC_Fat :: *;
`endif

import TV_Info   :: *;

// ================================================================
// Output status of each stage

// EMPTY:   Stage has nothing in its input register
// BUSY:    Stage has input, but output is not ready
// PIPE:    Stage has input; driving normal output for pipeline
// NONPIPE: (In some stages) Stage has input; driving output is handled specially
//                (such as traps, CSR access, ...)

typedef enum {OSTATUS_EMPTY,
	      OSTATUS_BUSY,
	      OSTATUS_PIPE,
	      OSTATUS_NONPIPE
   } Stage_OStatus
deriving (Eq, Bits, FShow);

// ================================================================
// Branch-prediction info

typedef Bit #(2)  Epoch;

// ================================================================
// Bypass information
// From later to earlier stages.

// For an instruction's Rd (output GPR), a stage may:
// - have no Rd output
// - have Rd output, Rd is known but RdVal unknown
// - have Rd output, Rd is known and RdVal is known
// Note: a bypass has to stall if Rd matches and RdVal is unknown

typedef enum { BYPASS_RD_NONE, BYPASS_RD, BYPASS_RD_RDVAL } Bypass_State
deriving (Eq, Bits, FShow);

// We do not bypass CSR values, since we stall on CSRRxy insructions.

typedef struct {
   Bypass_State  bypass_state;
   RegName       rd;
`ifdef ISA_CHERI
   CapPipe       rd_val;
`else
   Word          rd_val;
`endif
   } Bypass
deriving (Bits);

instance FShow #(Bypass);
   function Fmt fshow (Bypass x);
      let fmt0 = $format ("Bypass {");
      let fmt1 = ((x.bypass_state == BYPASS_RD_NONE)
		  ? $format ("Rd -")
		  : $format ("Rd %0d ", x.rd) + ((x.bypass_state == BYPASS_RD)
						 ? $format ("-")
						 : $format ("rd_val:", fshow(x.rd_val))));
      let fmt2 = $format ("}");
      return fmt0 + fmt1 + fmt2;
   endfunction
endinstance

`ifdef ISA_F
typedef struct {
   Bypass_State  bypass_state;
   RegName       rd;
   WordFL        rd_val;
   } FBypass
deriving (Bits);

instance FShow #(FBypass);
   function Fmt fshow (FBypass x);
      let fmt0 = $format ("FBypass {");
      let fmt1 = ((x.bypass_state == BYPASS_RD_NONE)
		  ? $format ("FRd -")
		  : $format ("FRd %0d ", x.rd) + ((x.bypass_state == BYPASS_RD)
						 ? $format ("-")
						 : $format ("frd_val:%h", x.rd_val)));
      let fmt2 = $format ("}");
      return fmt0 + fmt1 + fmt2;
   endfunction
endinstance
`endif

// ----------------
// Baseline bypass info

Bypass no_bypass = Bypass {bypass_state: BYPASS_RD_NONE,
			   rd: ?,
			   rd_val: ? };

`ifdef ISA_F
FBypass no_fbypass = FBypass {bypass_state: BYPASS_RD_NONE,
			      rd: ?,
			      rd_val: ? };
`endif

// ----------------
// Bypass functions for GPRs
// Returns '(busy, val)'
// 'busy' means that the RegName is valid and matches, but the value is not available yet

`ifdef ISA_CHERI
function Tuple2 #(Bool, CapPipe) fn_gpr_bypass (Bypass bypass, RegName rd, CapPipe rd_val);
`else
function Tuple2 #(Bool, Word) fn_gpr_bypass (Bypass bypass, RegName rd, Word rd_val);
`endif
   Bool busy = ((bypass.bypass_state == BYPASS_RD) && (bypass.rd == rd));
   let val = (  ((bypass.bypass_state == BYPASS_RD_RDVAL) && (bypass.rd == rd))
		 ? bypass.rd_val
		 : rd_val);
   return tuple2 (busy, val);
endfunction

`ifdef ISA_F
// FBypass functions for FPRs
// Returns '(busy, val)'
// 'busy' means that the RegName is valid and matches, but the value is not available yet

function Tuple2 #(Bool, WordFL) fn_fpr_bypass (FBypass bypass, RegName rd, WordFL rd_val);
   Bool busy = ((bypass.bypass_state == BYPASS_RD) && (bypass.rd == rd));
   WordFL val= (  ((bypass.bypass_state == BYPASS_RD_RDVAL) && (bypass.rd == rd))
		? bypass.rd_val
		: rd_val);
   return tuple2 (busy, val);
endfunction
`endif

`ifdef ISA_CHERI
typeclass PCC#(type t);
    function Exact#(t) setPC (t oldPCC, Addr newPC);
    function Addr getPC (t pcc);
    function Bool checkPreValid (t pcc);
    function Maybe#(CHERI_Exc_Code) checkValid (t pcc, Bit#(TAdd#(XLEN,1)) top, Bool is_i32_not_i16);
    function t fromCapReg(CapReg pcc);
    function CapReg toCapReg(t pcc);
endtypeclass

instance PCC#(CapPipe);
    function Exact#(CapPipe) setPC (CapPipe oldPCC, Addr newPC);
        return setOffset(oldPCC, newPC);
    endfunction
    function Addr getPC (CapPipe pcc);
        return getOffset(pcc);
    endfunction
    // Check if a PCC dereference is valid before the instruction len is known
    function Bool checkPreValid (CapPipe pcc);
        //TODO alignment checks?
        return  isValidCap(pcc)
             && !isSealed(pcc)
             && getHardPerms(pcc).permitExecute
             && isInBounds(pcc, False);
    endfunction
    function Maybe#(CHERI_Exc_Code) checkValid (CapPipe pcc, Bit#(TAdd#(XLEN,1)) top, Bool is_i32_not_i16);
        let toRet = Invalid;
        //TODO alignment checks?
        CapPipe ac = almightyCap;
        if (!isValidCap(pcc))
            toRet = Valid(exc_code_CHERI_Tag);
        else if (isSealed(pcc))
            toRet = Valid(exc_code_CHERI_Seal);
        else if (!getHardPerms(pcc).permitExecute)
            toRet = Valid(exc_code_CHERI_XPerm);
        else if (!isInBounds(pcc, False) || !isInBounds(setAddrUnsafe(pcc, getAddr(pcc) + (is_i32_not_i16 ? 4 : 2)), True))
            toRet = Valid(exc_code_CHERI_Length);
        return toRet;
    endfunction
    function CapPipe fromCapReg(CapReg pcc);
        return cast(pcc);
    endfunction
    function CapReg toCapReg(CapPipe pcc);
        return cast(pcc);
    endfunction
endinstance

typedef CapPipe PCC_T;

`endif

// ================================================================
// Trap information

typedef struct {
`ifdef ISA_CHERI
   PCC_T epcc;
   CHERI_Exc_Code cheri_exc_code;
   Bit#(6) cheri_exc_reg;
`else
   Addr      epc;
`endif
   Exc_Code  exc_code;
   Addr      tval;
   } Trap_Info_Pipe
deriving (Bits, FShow);

// ================================================================
// Output from Stage F

typedef struct {
   Stage_OStatus          ostatus;

   // feedforward data
   Data_StageF_to_StageD  data_to_stageD;
   } Output_StageF
deriving (Bits);

instance FShow #(Output_StageF);
   function Fmt fshow (Output_StageF x);
      Fmt fmt = $format ("Output_StageF");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY: fetch_addr:%h", x.data_to_stageD.fetch_addr);
      else if (x.ostatus == OSTATUS_NONPIPE)
	 fmt = fmt + $format (" NONPIPE: fetch_addr:%h [***** IMPOSSIBLE! *****]", x.data_to_stageD.fetch_addr);
      else
	 fmt = fmt + $format (" PIPE: ", fshow (x.data_to_stageD));
      return fmt;
   endfunction
endinstance
// ----------------
// Data_StageF_to_StageD

typedef struct {
   Addr       fetch_addr;
`ifdef ISA_CHERI
   Bool       refresh_pcc;
`endif
`ifdef RVFI_DII
   Dii_Id instr_seq;
`endif
   Epoch      epoch;              // Branch prediction epoch
   Priv_Mode  priv;               // Priv at which instr was fetched
   Bool       is_i32_not_i16;     // True if a regular 32b instr, not a compressed (16b) instr
   Bool       exc;                // True if exc in icache access
   Exc_Code   exc_code;
`ifdef ISA_CHERI
   CHERI_Exc_Code exc_code_cheri;
   Bit#(5)    cheri_exc_reg;
`endif
   WordXL     tval;               // Trap value; can be different from PC, with 'C' extension
   Instr      instr;              // Valid if no exception
   WordXL     pred_fetch_addr;    // Predicted next pc
   } Data_StageF_to_StageD
deriving (Bits);

instance FShow #(Data_StageF_to_StageD);
   function Fmt fshow (Data_StageF_to_StageD x);
      Fmt fmt = $format ("data_to_StageD {fetch_addr:%h  priv:%0d  epoch:%0d", x.fetch_addr, x.priv, x.epoch);
      if (x.exc)
	 fmt = fmt + $format ("  ", fshow_trap_Exc_Code (x.exc_code));
      else
	 fmt = fmt + $format ("  instr:%h  pred_fetch_addr:%h", x.instr, x.pred_fetch_addr);
      fmt = fmt + $format ("}");
      return fmt;
   endfunction
endinstance

// ================================================================
// Output from Stage D
// Just adds decoded instr info

typedef struct {
   Stage_OStatus          ostatus;

   // feedforward data
   Data_StageD_to_Stage1  data_to_stage1;
   } Output_StageD
deriving (Bits);

instance FShow #(Output_StageD);
   function Fmt fshow (Output_StageD x);
      Fmt fmt = $format ("Output_StageD");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY: fetch_addr:%h", x.data_to_stage1.fetch_addr);
      else if (x.ostatus == OSTATUS_NONPIPE)
	 fmt = fmt + $format (" NONPIPE: fetch_addr:%h [***** IMPOSSIBLE! *****]", x.data_to_stage1.fetch_addr);
      else
	 fmt = fmt + $format (" PIPE: ", fshow (x.data_to_stage1));
      return fmt;
   endfunction
endinstance

// ----------------
// Data_StageD_to_Stage1

typedef struct {
   Addr           fetch_addr;
`ifdef ISA_CHERI
   Bool           refresh_pcc;
`endif
`ifdef RVFI_DII
   Dii_Id instr_seq;
`endif
   Priv_Mode      priv;               // Priv at which instr was fetched
   Epoch          epoch;              // Branch prediction epoch

   Bool           is_i32_not_i16;     // True if a regular 32b instr, not a compressed (16b) instr

   Bool           exc;                // True if exc in icache access
   Exc_Code       exc_code;
   WordXL         tval;               // Trap value; can be different from PC, with 'C' extension
`ifdef ISA_CHERI
   CHERI_Exc_Code exc_code_cheri;
   Bit#(5)    cheri_exc_reg;
`endif

   Instr          instr;              // Valid if no exception
   Instr_C        instr_C;            // Valid if no exception; original compressed instruction
   WordXL         pred_fetch_addr;    // Predicted next pc
   Decoded_Instr  decoded_instr;
   } Data_StageD_to_Stage1
deriving (Bits);

instance FShow #(Data_StageD_to_Stage1);
   function Fmt fshow (Data_StageD_to_Stage1 x);
      Fmt fmt = $format ("data_to_Stage1 {pc:%0h  priv:%0d  epoch:%0d", x.fetch_addr, x.priv, x.epoch);
      if (x.exc)
	 fmt = fmt + $format ("  ", fshow_trap_Exc_Code (x.exc_code), " tval %0h", x.tval);
      else begin
	 if (x.is_i32_not_i16)
	    fmt = fmt + $format ("  instr_C:%0h", x.instr_C);
	 fmt = fmt + $format ("  instr:%0h  pred_fetch_addr:%0h", x.instr, x.pred_fetch_addr);
      end
      fmt = fmt + $format ("}");
      return fmt;
   endfunction
endinstance

// ================================================================
// Output from Stage 1

// Outputs from Stage1 to pipeline control
typedef enum {  CONTROL_DISCARD
	      , CONTROL_STRAIGHT
	      , CONTROL_BRANCH
	      , CONTROL_CSRR_W
`ifdef ISA_CHERI
        , CONTROL_CAPBRANCH
	      , CONTROL_SCR_W
`endif
	      , CONTROL_CSRR_S_or_C
	      , CONTROL_FENCE
	      , CONTROL_FENCE_I
	      , CONTROL_SFENCE_VMA
	      , CONTROL_MRET
	      , CONTROL_SRET
	      , CONTROL_URET
	      , CONTROL_WFI
	      , CONTROL_TRAP
   } Control
deriving (Eq, Bits, FShow);

typedef struct {
   Stage_OStatus          ostatus;

   Control                control;

   Trap_Info_Pipe         trap_info;

   // feedback
   Bool                   redirect;
`ifdef ISA_CHERI
   CapPipe                next_pcc;
`else
   WordXL                 next_pc;
`endif

   // feedforward data
   Data_Stage1_to_Stage2  data_to_stage2;
   } Output_Stage1
deriving (Bits);

instance FShow #(Output_Stage1);
   function Fmt fshow (Output_Stage1 x);
`ifdef ISA_CHERI
      let pc = getPC(x.data_to_stage2.pcc);
`else
      let pc = x.data_to_stage2.pc;
`endif
      Fmt fmt = $format ("Output_Stage1");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY pc:%h", pc);
      else begin
	 if (x.ostatus == OSTATUS_NONPIPE) begin
	    fmt = fmt + $format (" NONPIPE: pc:%h", pc);
	    fmt = fmt + $format (" ", fshow (x.control));
	    fmt = fmt + $format (" ", fshow (x.trap_info));
	 end
	 else
	    fmt = fmt + $format (" PIPE: ", fshow (x.control), " ", fshow (x.data_to_stage2));

	 if (x.redirect)
	    fmt = fmt + $format ("\n        redirect next_pc:%h", getPC(x.next_pcc));
      end
      return fmt;
   endfunction
endinstance

// ================================================================
// Data_Stage1_to_Stage2: Data output from Stage1 stage, input to DM stage

// Stage1 stage forwards, to DM, one of these 'opcodes'
// - ALU result (all non-mem, M and FD insructions)
// - DM request (Data Memory LD/ST/...)
// - Shifter Box request (SLL/SLLI, SRL/SRLI, SRA/SRAI)
// - MBox request (integer multiply/divide)
// - FDBox request (floating point ops)

typedef enum {  OP_Stage2_ALU         // Pass-through (non mem, M, FD, AMO)
	      , OP_Stage2_LD
	      , OP_Stage2_ST

`ifdef SHIFT_SERIAL
	      , OP_Stage2_SH
`endif

`ifdef ISA_M
	      , OP_Stage2_M
`endif

`ifdef ISA_A
	      , OP_Stage2_AMO
`endif

`ifdef ISA_F
	      , OP_Stage2_FD
`endif
`ifdef ISA_CHERI
              , OP_Stage2_TestSubset
   } Op_Stage2
deriving (Eq, Bits, FShow);

typedef struct {
`ifdef ISA_CHERI
`ifdef ISA_D
`ifdef RV32
`define FLOAT_BIGGER_THAN_INT
`endif
`endif
`ifdef FLOAT_BIGGER_THAN_INT
    Either#(CapPipe, WordFL) val;
`else
    CapPipe val;
`endif
`else
`ifdef ISA_D
    WordFL val;
`else
    WordXL val;
`endif
`endif
   } Pipeline_Val deriving (Bits, FShow);

`ifdef FLOAT_BIGGER_THAN_INT
   instance FShow#(Either#(a,b)) provisos (FShow#(a), FShow#(b));
       function fshow(x) = case (x) matches
                             tagged Left  .l: return fshow(l);
                             tagged Right .r: return fshow(r);
                           endcase;
   endinstance
`endif

`ifdef ISA_CHERI
`ifdef FLOAT_BIGGER_THAN_INT
    function Pipeline_Val embed_cap(CapPipe cap) = Pipeline_Val{val: Left(cap)};
    function CapPipe extract_cap(Pipeline_Val val) =
        case (val.val) matches
            tagged Left .cap: return cap;
            tagged Right .flt: return nullWithAddr(truncate(flt));
        endcase;
    function Pipeline_Val embed_flt(WordFL flt) = Pipeline_Val{val: Right(flt)};
    function WordFL extract_flt(Pipeline_Val val) = val.val.Right;
    function Pipeline_Val embed_int(WordXL num) = Pipeline_Val{val: Left(nullWithAddr(num))};
    function WordXL extract_int(Pipeline_Val val) = getAddr(val.val.Left);
`else
    function Pipeline_Val embed_cap(CapPipe cap) = Pipeline_Val{val: cap};
    function CapPipe extract_cap(Pipeline_Val val) = val.val;
`ifdef ISA_F
    function Pipeline_Val embed_flt(WordFL flt) = Pipeline_Val{val: nullWithAddr(zeroExtend(pack(flt)))};
    function WordFL extract_flt(Pipeline_Val val) = unpack(truncate(getAddr(val.val)));
`endif
    function Pipeline_Val embed_int(WordXL num) = Pipeline_Val{val: nullWithAddr(num)};
    function WordXL extract_int(Pipeline_Val val) = getAddr(val.val);
`endif
`else
`ifdef ISA_F
    function Pipeline_Val embed_cap(CapPipe cap) = Pipeline_Val{val: cap};
    function CapPipe extract_cap(Pipeline_Val val) = val.val;
    function Pipeline_Val embed_int(WordXL num) = Pipeline_Val{val: num};
    function WordXL extract_int(Pipeline_Val val) = val.val;
`else
    function Pipeline_Val embed_int(WordXL num) = Pipeline_Val{val: num};
    function WordXL extract_int(Pipeline_Val val) = val.val;
`endif
`endif

typedef struct {
   Priv_Mode  priv;
`ifdef ISA_CHERI
   PCC_T      pcc;
`else
   Addr       pc;
`endif
   Instr      instr;    // For debugging. Just funct3, funct7 are enough for
                        // functionality.
`ifdef RVFI_DII
   Dii_Id instr_seq;
`endif
   Op_Stage2  op_stage2;
   RegName    rd;
   Addr       addr;     // Branch, jump: newPC
                        // Mem ops and AMOs: mem addr

   Pipeline_Val val1;  // OP_Stage2_ALU: rd_val
                       // OP_Stage2_M and OP_Stage2_FD: arg1

   Pipeline_Val val2;  // OP_Stage2_ST: store-val;
                       // OP_Stage2_M and OP_Stage2_FD: arg2

`ifdef ISA_CHERI
   // Bounds check: if check_enable, will test
   // address_low >= authority.base && address_high <? authority.top (?: strictness determined by check_inclusive value TODO)
   // TODO behaviour if address_low > address_high?
   // Does not check that authority is tagged, so only generates
   // Bounds exceptions
   CapPipe    check_authority;
   Bit#(6)    check_authority_idx;
   Bit#(XLEN)     check_address_low;
   Bit#(TAdd#(XLEN,1))     check_address_high;
   Bool       check_enable;
   Bool check_inclusive;

   Bool       mem_allow_cap;
`endif

   Bit#(3)    mem_width_code;
   Bool       mem_unsigned;

`ifdef ISA_F
   Bool val1_flt_not_int;
   Bool val2_flt_not_int;
   WordFL     val3;     // OP_Stage2_FD: arg3
   Bool       rd_in_fpr;// The rd should update into FPR
   Bit #(3)   rounding_mode;    // rounding mode from fcsr_frm or instr.rm
`endif

`ifdef INCLUDE_TANDEM_VERIF
   Trace_Data  trace_data;
`endif
`ifdef RVFI
   Data_RVFI_Stage1 info_RVFI_s1;
`endif
   } Data_Stage1_to_Stage2
deriving (Bits);

`ifdef RVFI

typedef struct {
    Bit#(ILEN)  instr;
    // From decode
    Bit#(5)     rs1_addr;
    Bit#(5)     rs2_addr;
    Bit#(XLEN)  rs1_data;
    Bit#(XLEN)  rs2_data;
    Bit#(XLEN)  pc_rdata;
    // TODO: Exceptions?
    Bit#(XLEN)  pc_wdata;
    // TODO: Needs 0'ing when unused?
    Bit#(MEMWIDTH)  mem_wdata;

    // From ALU:
    Bit#(5)     rd_addr;
    // Might be killed by memory OPs.
    Bool        rd_alu;
    Bit#(XLEN)  rd_wdata_alu;

    Bit#(XLEN)  mem_addr;

} Data_RVFI_Stage1 deriving (Bits, Eq);


`endif

instance FShow #(Data_Stage1_to_Stage2);
   function Fmt fshow (Data_Stage1_to_Stage2 x);
`ifdef ISA_CHERI
      let pc = getPC(x.pcc);
`else
      let pc = x.pc;
`endif
      Fmt fmt =   $format ("data_to_Stage 2 {pc:%h  instr:%h  priv:%0d\n", pc, x.instr, x.priv);
      fmt = fmt + $format ("            op_stage2:", fshow (x.op_stage2), "  rd:%0d\n", x.rd);
`ifdef ISA_F
      fmt = fmt + $format ("            addr:%h  val1:%h  val2:%h  val3:%h}",
			   x.addr, x.val1, x.val2, x.val3);
`else
      fmt = fmt + $format ("            addr:%h  val1:%h  val2:%h}",
			   x.addr, x.val1, x.val2);
`endif
      return fmt;
   endfunction
endinstance

// ================================================================
// Output from Stage 2

typedef struct {
   Stage_OStatus          ostatus;
   Trap_Info_Pipe         trap_info;    // relevant if ostatus == OSTATUS_NONPIPE

`ifdef ISA_CHERI
   // Whether a capability bounds check succeeded
   Bool                   check_success;
`endif

   // feedback
   Bypass                 bypass;
`ifdef ISA_F
   FBypass                fbypass;
`endif

   // feedforward data
   Data_Stage2_to_Stage3  data_to_stage3;

   Trace_Data             trace_data;
   } Output_Stage2
deriving (Bits);

instance FShow #(Output_Stage2);
   function Fmt fshow (Output_Stage2 x);
      Fmt fmt = $format ("Output_Stage2");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY: pc:%0h", getPC(x.data_to_stage3.pcc));
      else if (x.ostatus == OSTATUS_NONPIPE) begin
	 fmt = fmt + $format (" NONPIPE: ") + fshow (x.trap_info);
	 fmt = fmt + $format (" ") + fshow (x.trap_info);
      end
      else
	 fmt = fmt + $format (" PIPE: ") + fshow (x.data_to_stage3);
      return fmt;
   endfunction
endinstance

// ================================================================
// Data communicated from stage 2 to stage 3

typedef struct {
   CapPipe     pcc;            // For debugging only
   Instr     instr;         // For debugging only
`ifdef RVFI_DII
   Dii_Id instr_seq;
`endif
   Priv_Mode priv;

   Bool      rd_valid;
   RegName   rd;

`ifdef RVFI
   Data_RVFI_Stage2 info_RVFI_s2;
`endif

`ifdef ISA_F
   Bool      upd_flags;
   Bool      rd_in_fpr;
   Bit #(5)  fpr_flags;
`endif
   Pipeline_Val rd_val;
   } Data_Stage2_to_Stage3
deriving (Bits);

`ifdef RVFI

typedef struct {
    Data_RVFI_Stage1    stage1;
    // Hard to know what was written as SC pretends to write "0" on failure
    // instead of actual untouched value. So, indicate wmask = 0 perhaps?

    Bit#(TDiv#(MEMWIDTH,8))       mem_rmask;
    Bit#(TDiv#(MEMWIDTH,8))       mem_wmask;

}   Data_RVFI_Stage2 deriving (Bits);

`endif

instance FShow #(Data_Stage2_to_Stage3);
   function Fmt fshow (Data_Stage2_to_Stage3 x);
      Fmt fmt =   $format ("data_to_Stage3 {pc:%h  instr:%h  priv:%0d\n", getPC(x.pcc), x.instr, x.priv);
      fmt = fmt + $format ("        rd_valid:", fshow (x.rd_valid));

`ifdef ISA_F
      if (x.upd_flags)
         fmt = fmt + $format ("  fflags: %05b", fshow (x.fpr_flags));

      if (x.rd_in_fpr)
         fmt = fmt + $format ("  frd:%0d  rd_val:%h\n", x.rd, x.rd_val);
      else
`endif
         fmt = fmt + $format ("  grd:%0d  rd_val:\n", x.rd, fshow(x.rd_val));
      return fmt;
   endfunction
endinstance

// ================================================================
// Output from Stage 3

typedef struct {
   Stage_OStatus  ostatus;
   Bypass         bypass;
`ifdef ISA_F
   FBypass        fbypass;
`endif
   } Output_Stage3
deriving (Bits);

instance FShow #(Output_Stage3);
   function Fmt fshow (Output_Stage3 x);
      Fmt fmt = $format ("Output_Stage3");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY");
      else if (x.ostatus == OSTATUS_PIPE)
	 fmt = fmt + $format (" PIPE");
      else if (x.ostatus == OSTATUS_NONPIPE)
	 fmt = fmt + $format (" NONPIPE");
      return fmt;
   endfunction
endinstance

// ================================================================

endpackage
