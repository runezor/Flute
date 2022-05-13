// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package CPU_StageD;

// ================================================================
// This is Stage D ("decode") of the "Flute_V3" CPU.

// ================================================================
// Exports

export
CPU_StageD_IFC (..),
mkCPU_StageD;

// ================================================================
// BSV library imports

import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import ConfigReg    :: *;
import V_Decoder    :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls        :: *;
import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;

`ifdef ISA_C
// 'C' extension (16b compressed instructions)
import CPU_Decode_C     :: *;
`endif

// ================================================================
// Interface

interface CPU_StageD_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_StageD out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Data_StageF_to_StageD  data_stageF_to_stageD);

   (* always_ready *)
   method Action set_full (Bool full);
endinterface

// ================================================================
// Implementation module

module mkCPU_StageD #(Bit #(4)  verbosity, MISA misa)
                    (CPU_StageD_IFC);

   FIFOF #(Token)  f_reset_reqs <- mkFIFOF;
   FIFOF #(Token)  f_reset_rsps <- mkFIFOF;

   Reg #(Bool)                   rg_full <- mkReg (False);
   Reg #(Data_StageF_to_StageD)  rg_data <- mkRegU;

   Bit #(2) xl = ((xlen == 32) ? misa_mxl_32 : misa_mxl_64);

   Instr instr = rg_data.instr;
   Instr instr_or_instr_C = instr;
`ifdef ISA_C
   Instr_C instr_C = instr [15:0];
   if (! rg_data.is_i32_not_i16) begin
      instr = fv_decode_C (misa, xl, rg_data.is_cap_mode, instr_C);
      instr_or_instr_C = zeroExtend(instr_C);
   end
`endif

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      f_reset_rsps.enq (?);
   endrule

   // ----------------
   // Combinational output function

   function Output_StageD fv_out;
      let decoded_instr = fv_decode (instr);
      let v_decoding = v_decode(instr);

      Output_StageD  output_stageD = ?;

      // This stage is empty
      if (! rg_full) begin
	 output_stageD.ostatus = OSTATUS_EMPTY;
      end
      else begin
	 output_stageD.ostatus        = OSTATUS_PIPE;
	 output_stageD.data_to_stage1 = Data_StageD_to_Stage1 {
                                                               fetch_addr:     rg_data.fetch_addr,
                                                               is_cap_mode:    rg_data.is_cap_mode,
`ifdef ISA_CHERI
                                                               refresh_pcc:    rg_data.refresh_pcc,
`endif
`ifdef RVFI_DII
                                                               instr_seq:      rg_data.instr_seq,
`endif
							       priv:           rg_data.priv,
							       epoch:          rg_data.epoch,
							       is_i32_not_i16: rg_data.is_i32_not_i16,
							       exc:            rg_data.exc,
							       exc_code:       rg_data.exc_code,
							       tval:           rg_data.tval,
							       instr:          instr,
							       instr_or_instr_C: instr_or_instr_C,
							       pred_fetch_addr:rg_data.pred_fetch_addr,
							       pred_is_cap_mode:rg_data.pred_is_cap_mode,
							       decoded_instr:  decoded_instr,
                            v_decoded:      v_decoding};
      end

      return output_stageD;
   endfunction: fv_out

   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_StageD out;
      return fv_out;
   endmethod

   method Action deq ();
      noAction;
   endmethod

   // ---- Input
   method Action enq (Data_StageF_to_StageD  data);
      rg_data <= data;
      if (verbosity > 1)
	 $display ("    CPU_StageD.enq (Data_StageF_to_StageD)");
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
endmodule

// ================================================================

endpackage
