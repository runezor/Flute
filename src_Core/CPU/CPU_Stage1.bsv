// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package CPU_Stage1;

// ================================================================
// This is Stage 1 of the "Flute" CPU.
// It contains the EX functionality.
// EX: "Execute"

// ================================================================
// Exports

export
CPU_Stage1_IFC (..),
mkCPU_Stage1;

// ================================================================
// BSV library imports

import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import ConfigReg    :: *;
import V_Decoder    :: *;
import V_ALU        :: *;
import V_isa        :: *;


// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls        :: *;
import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;
import GPR_RegFile      :: *;
`ifdef ISA_F
import FPR_RegFile      :: *;
`endif
import CSR_RegFile      :: *;
import EX_ALU_functions :: *;

`ifdef ISA_C
// 'C' extension (16b compressed instructions)
import CPU_Decode_C     :: *;
`endif

`ifdef ISA_CHERI
import CHERICap :: *;
import CHERICC_Fat :: *;
`endif

// ================================================================
// Interface

interface CPU_Stage1_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_Stage1 out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Data_StageD_to_Stage1  data);

   (* always_ready *)
   method Action set_full (Bool full);
endinterface

// ================================================================
// Spoofed ALU output, for overloading 
CF_Info cf_info_base = CF_Info {cf_op       : CF_None,
				from_PC     : ?,
				taken       : ?,
				fallthru_PC : ?,
				taken_PC    : ?};

ALU_Outputs alu_output_vector
= ALU_Outputs {control   : CONTROL_STRAIGHT,
	       exc_code  : exc_code_ILLEGAL_INSTRUCTION,
`ifdef ISA_CHERI
               cheri_exc_code: exc_code_CHERI_None,
               cheri_exc_reg:  ?,
`endif
               op_stage2 : OP_Stage2_ALU, //Just forwards results
               rd        : ?,
               addr      : ?,
               val1      : ?,
               val2      : ?,
	       val1_fast : ?,
	       val2_fast : ?,
`ifdef ISA_F
               fval1       : ?,
               fval2       : ?,
               fval3       : ?,
               rd_in_fpr   : False,
               rs_frm_fpr  : False,
               val1_frm_gpr: False,
               rm          : ?,
`endif
`ifdef ISA_CHERI
               cap_val1  : ?,
               cap_val2  : ?,
               val1_cap_not_int: False,
               val2_cap_not_int: False,

               pcc : ?,

               check_enable       : False,
               check_authority    : ?,
               check_authority_idx : ?,
               check_address_low  : ?,
               check_address_high : ?,
               check_inclusive    : ?,
               check_exact_enable : False,
`ifndef PERFORMANCE_MONITORING
               check_exact_success : ?,
`else
               check_exact_success : True,
               set_offset_in_bounds : True,
`endif

               mem_allow_cap      : False,
`endif

               mem_width_code     : ?,
               mem_unsigned       : False,

               cf_info     : cf_info_base

`ifdef INCLUDE_TANDEM_VERIF
             , trace_data: ?
`endif
                            };
   
// ================================================================
// Implementation module

module mkCPU_Stage1 #(Bit #(4)         verbosity,
		      GPR_RegFile_IFC  gpr_regfile,
		      Bypass           bypass_from_stage2,
		      Bypass           bypass_from_stage3,
`ifdef ISA_CHERI
                      PCC_T            fresh_pcc,
                      CapPipe          ddc,
`endif
`ifdef ISA_F
		      FPR_RegFile_IFC  fpr_regfile,
		      FBypass          fbypass_from_stage2,
		      FBypass          fbypass_from_stage3,
`endif
		      CSR_RegFile_IFC  csr_regfile,
		      Epoch            cur_epoch,
		      Priv_Mode        cur_priv)
                    (CPU_Stage1_IFC);

   FIFOF #(Token) f_reset_reqs <- mkFIFOF;
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

`ifdef ISA_CHERI
   Reg #(PCC_T) rg_pcc <- mkRegU;
   RWire#(PCC_T) rw_next_pcc <- mkRWire;
   RWire#(PCC_T) rw_fresh_pcc <- mkRWire;
`endif

   Reg #(Bool)                  rg_full        <- mkReg (False);
   Reg #(Data_StageD_to_Stage1) rg_stage_input <- mkRegU;

   MISA misa   = csr_regfile.read_misa;
   Bit #(2) xl = ((xlen == 32) ? misa_mxl_32 : misa_mxl_64);

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      f_reset_rsps.enq (?);
   endrule

   // ----------------
   // ALU

   let decoded_instr  = rg_stage_input.decoded_instr;
   let funct3         = decoded_instr.funct3;

   // Vector handling
   let v_instr = rg_stage_input.v_decoded;
   Bool is_vector_instr = True;
   Bool is_rd_vector = False;

   let rs1_addr = get_GPR_addr(decoded_instr.rs1);
   let rs2_addr = get_GPR_addr(decoded_instr.rs2);

   case (v_instr) matches                           // todo: Move inside ALU?
					tagged Invalid_V_instr .i: begin
						is_vector_instr = False;
					end
               tagged Load_V_instr .i: begin
                  rs1_addr = get_GPR_addr(i.rs1);
                  is_rd_vector = True;
               end
               tagged Store_V_instr .i: begin
                  rs1_addr = get_GPR_addr(i.rs1);
                  rs2_addr = get_vec_reg_addr(i.vs3);
                  is_rd_vector = False;
               end
					tagged Vsetvl_V_instr .i: begin
                  //No data fetching necessary
					end
					tagged Arith_V_instr .a: begin
                  case (a.load1) matches
                     tagged Payload_addr_GPR .r: begin
                        rs1_addr = get_GPR_addr(r.addr);
                     end
                     tagged Payload_addr_vec .r: begin
                        rs1_addr = get_vec_reg_addr(r.addr);
                     end
                  endcase
                  is_rd_vector = True;
						rs2_addr = get_vec_reg_addr(a.load2.addr);
					end
	endcase

   // Register rs1 read and bypass
   //Todo load immediate correctly
   //Todo clean up
   let rs1 = rs1_addr;
   let rs1_val = gpr_regfile.read_rs1 (rs1);
   match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
   match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);
   Bool rs1_busy = (busy1a || busy1b);
`ifdef ISA_CHERI
   CapPipe rs1_val_bypassed = ((rs1 == 0) ? nullCap : rs1b);
`else
   Word rs1_val_bypassed = ((rs1 == 0) ? 0 : rs1b);
`endif

   // Register rs2 read and bypass
   let rs2 = rs2_addr;
   let rs2_val = gpr_regfile.read_rs2 (rs2);
   match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
   match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);
   Bool rs2_busy = (busy2a || busy2b);
`ifdef ISA_CHERI
   CapPipe rs2_val_bypassed = ((rs2 == 0) ? nullCap : rs2b);
`else
   Word rs2_val_bypassed = ((rs2 == 0) ? 0 : rs2b);
`endif

`ifdef ISA_F
   // FP Register rs1 read and bypass
   let frs1_val = fpr_regfile.read_rs1 (rs1);
   match { .fbusy1a, .frs1a } = fn_fpr_bypass (fbypass_from_stage3, rs1, frs1_val);
   match { .fbusy1b, .frs1b } = fn_fpr_bypass (fbypass_from_stage2, rs1, frs1a);
   Bool frs1_busy = (fbusy1a || fbusy1b);
   WordFL frs1_val_bypassed = frs1b;

   // FP Register rs2 read and bypass
   let frs2_val = fpr_regfile.read_rs2 (rs2);
   match { .fbusy2a, .frs2a } = fn_fpr_bypass (fbypass_from_stage3, rs2, frs2_val);
   match { .fbusy2b, .frs2b } = fn_fpr_bypass (fbypass_from_stage2, rs2, frs2a);
   Bool frs2_busy = (fbusy2a || fbusy2b);
   WordFL frs2_val_bypassed = frs2b;

   // FP Register rs3 read and bypass
   let rs3 = get_GPR_addr(decoded_instr.rs3);
   let frs3_val = fpr_regfile.read_rs3 (rs3);
   match { .fbusy3a, .frs3a } = fn_fpr_bypass (fbypass_from_stage3, rs3, frs3_val);
   match { .fbusy3b, .frs3b } = fn_fpr_bypass (fbypass_from_stage2, rs3, frs3a);
   Bool frs3_busy = (fbusy3a || fbusy3b);
   WordFL frs3_val_bypassed = frs3b;
`endif

   // ALU function
   let alu_inputs = ALU_Inputs {cur_priv       : cur_priv,
`ifdef ISA_CHERI
				pcc            : rg_pcc,
				ddc            : ddc,
				pc             : getPC(rg_pcc),
`else
				pc             : rg_stage_input.pc,
`endif
				is_i32_not_i16 : rg_stage_input.is_i32_not_i16,
				instr          : rg_stage_input.instr,
`ifdef ISA_C
				instr_or_instr_C : rg_stage_input.instr_or_instr_C,
`endif
				decoded_instr  : rg_stage_input.decoded_instr,
`ifdef ISA_CHERI
				cap_rs1_val    : rs1_val_bypassed,
				cap_rs2_val    : rs2_val_bypassed,
				rs1_idx        : reg_addr_to_name(rs1),
				rs2_idx        : reg_addr_to_name(rs2),
				rs1_val        : getAddr(rs1_val_bypassed),
				rs2_val        : getAddr(rs2_val_bypassed),
`else
				rs1_val        : rs1_val_bypassed,
				rs2_val        : rs2_val_bypassed,
`endif
`ifdef ISA_F
				frs1_val       : frs1_val_bypassed,
				frs2_val       : frs2_val_bypassed,
				frs3_val       : frs3_val_bypassed,
				frm            : csr_regfile.read_frm,
`ifdef INCLUDE_TANDEM_VERIF
                                fflags         : csr_regfile.read_fflags,
`endif
`endif
				mstatus        : csr_regfile.read_mstatus,
				misa           : csr_regfile.read_misa };

   let alu_outputs = alu_output_vector;

   let rvfi_MWD_send_as_vec = False;
   let is_vsetvl_instr = False;
   let rd_addr = 0;
   let vsetvl_output = 0;
   Bit#(64) vec_mem_offset = 0;
   Bit#(64) rvfi_MWD_vec = 0;
   let overide_input_instr = False;
   Bit#(32) instr_override = 0;
   let vsew_r = csr_regfile.read_csr_port2(csr_addr_vl);
   let vec_wmask = ?;
   V_el_size vsew = ?;
   if (vsew_r matches tagged Valid .vsew_w) vsew = unpack(truncate(vsew_w));

   if (is_vector_instr) begin
      //Let's start by checking mstatus
      if (csr_regfile.read_mstatus[24:23]==0)
         //We only throw a trap in these cases, to match with spike
         case (v_instr) matches
               tagged Arith_V_instr .instr: begin
                  alu_outputs.control = CONTROL_TRAP; 
                  rvfi_MWD_send_as_vec = True; 
                  alu_outputs.rs_frm_fpr = False;
                  rd_addr = get_vec_reg_addr(instr.dest.addr);
               end
					tagged Vsetvl_V_instr .instr: begin
                  alu_outputs.control = CONTROL_TRAP; 
                  rvfi_MWD_send_as_vec = True; 
                  alu_outputs.rs_frm_fpr = False;
                  rd_addr = get_GPR_addr(instr.dest);
					end
         endcase
      else begin
         case (v_instr) matches
               tagged Arith_V_instr .instr: begin
                  Bit#(64) vs1 = getAddr(rs1_val_bypassed);
                  Bit#(64) vs2 = getAddr(rs2_val_bypassed);

                  //Bit#(128) vs1 = truncate(pack(rs1_val_bypassed));
                  //Bit#(128) vs2 = truncate(pack(rs2_val_bypassed));

                  let val = vector_compute(vs1, vs2, instr, vsew);
                  alu_outputs = alu_output_vector;
                  alu_outputs.val1 = val;
                  //alu_outputs.val1_cap_not_int = True;
                  //alu_outputs.cap_val1 = unpack(zeroExtend(pack(val)));
                  rd_addr = get_vec_reg_addr(instr.dest.addr);
               end
					tagged Vsetvl_V_instr .instr: begin
                  alu_outputs = alu_output_vector;
                  let vsew = instr.vsew;
                  alu_outputs.control   = CONTROL_CSRR_W;
                  //CSRR_W logic in Flute reads directly from the instruction, so we have to override it
                  instr_override[31:20] = csr_addr_vl;            //Sets csr address
                  instr_override[19:15] = zeroExtend(pack(vsew)); //Sets rs1 zeroExtend(pack(vsew))
                  instr_override[14:12] = f3_CSRRWI;              //Sets funct3
                  instr_override[11:7] = instr.dest;              //Sets rd
                  overide_input_instr = True;
                  is_vsetvl_instr = True;
                  vsetvl_output = 64>>(pack(vsew)+3);
                  rd_addr = get_GPR_addr(instr.dest);
					end
               tagged Load_V_instr .instr: begin
                  //Uses a standard load
                  Bool is_cap_mode = getFlags(toCapPipe(rg_pcc))[0] == 1;
                  alu_outputs = fv_vector_LD(instr.dest, rs1_val_bypassed, reg_addr_to_name(rs1_addr), ddc, is_cap_mode);
                  //Adds to the mem addr calculation to match with spike
                  vec_mem_offset = zeroExtend(8-(get_size_of_sew(vsew)>>3));
                  alu_outputs.cap_val2 = nullCap;
                  rd_addr = get_vec_reg_addr(instr.dest);
               end
               tagged Store_V_instr .instr: begin
                  //Uses a standard store
                  //And then send off vector thingy
                  Bool is_cap_mode = getFlags(toCapPipe(rg_pcc))[0] == 1;
                  alu_outputs = fv_vector_ST(rs1_val_bypassed, reg_addr_to_name(rs1_addr), rs2_val_bypassed, ddc, is_cap_mode);
                  alu_outputs.rd = 0;
                  //Adds to the mem addr calculation to match with spike
                  vec_mem_offset = zeroExtend(8-(get_size_of_sew(vsew)>>3));
                  vec_wmask = (1<<(1<<pack(vsew)))-1;//8: 1, 16: 11, 32: 1111, and so on

                  //Call fromCapMem to unpack into pipeline format
                  //Only fill the necessary fields
                  //Tocapmem, fromcapmem pdr32
                  //Unpack capability, fill extra fields with rubbish
                  //Or make pipelineval type a union

                  //vec_wmask = 64-1;
                  //Makes sure that MWD matches Spike


                  
                  rvfi_MWD_send_as_vec = True;
               end
	      endcase
      end
   end else begin
      alu_outputs = fv_ALU (alu_inputs);
      rd_addr = get_GPR_addr(alu_outputs.rd);
   end

   let fall_through_pc = getPC(rg_pcc) + (rg_stage_input.is_i32_not_i16 ? 4 : 2);

   let next_pc_local = ((alu_outputs.control == CONTROL_BRANCH)
		 ? alu_outputs.addr
		 : fall_through_pc);

   let next_pcc_local = ((alu_outputs.control == CONTROL_CAPBRANCH)
     ? alu_outputs.pcc
     : setPC(rg_pcc, next_pc_local).value); //TODO unrepresentable?

   let redirect = (alu_outputs.control == CONTROL_CAPBRANCH)
     ? (    {getAddr(toCapPipe(alu_outputs.pcc)), getFlags(toCapPipe(alu_outputs.pcc))[0]}
         != {rg_stage_input.pred_fetch_addr     , pack(rg_stage_input.pred_is_cap_mode)})
     : (next_pc_local != rg_stage_input.pred_fetch_addr - getPCCBase(rg_pcc));

`ifdef RVFI
   CapReg tmp_val2 = cast(alu_outputs.cap_val2);
   CapMem cap_val2 = cast(tmp_val2);
   let info_RVFI = Data_RVFI_Stage1 {
                       instr:          rg_stage_input.instr_or_instr_C,
                       rs1_addr:       reg_addr_to_rfvi_name(rs1),
                       rs2_addr:       reg_addr_to_rfvi_name(rs2),
`ifdef ISA_CHERI
                       rs1_data:       getAddr(rs1_val_bypassed),
                       rs2_data:       getAddr(rs2_val_bypassed),
`else
                       rs1_data:       rs1_val_bypassed,
                       rs2_data:       rs2_val_bypassed,
`endif
                       pc_rdata:       getPC(rg_pcc),
                       pc_wdata:       getPC(next_pcc_local),
`ifdef ISA_F
                       mem_wdata:      alu_outputs.rs_frm_fpr ? alu_outputs.fval2 : (rvfi_MWD_send_as_vec?truncate(get_last_vec_el_ze(zeroExtend(getAddr(rs2_val_bypassed)), vsew)):truncate(cap_val2)),
`else
                       mem_wdata:      truncate(cap_val2),
`endif
                       rd_addr:        reg_addr_to_rfvi_name(rd_addr),
                       rd_alu:         (alu_outputs.op_stage2 == OP_Stage2_ALU),
                       rd_wdata_alu:   alu_outputs.val1, //todo: Important 
                       mem_addr:       ((alu_outputs.op_stage2 == OP_Stage2_LD) || (alu_outputs.op_stage2 == OP_Stage2_ST)
`ifdef ISA_A
                                     || (alu_outputs.op_stage2 == OP_Stage2_AMO)
`endif
                       ) ? (is_vector_instr?alu_outputs.addr+vec_mem_offset:alu_outputs.addr) : 0};
`endif

   let data_to_stage2 = Data_Stage1_to_Stage2 {
`ifdef ISA_CHERI
                                               pcc:       rg_pcc,
`else
                                               pc:        rg_stage_input.pc,
`endif
					       instr         : overide_input_instr?instr_override:rg_stage_input.instr,
`ifdef RVFI_DII
                                               instr_seq     : rg_stage_input.instr_seq,
`endif
					       op_stage2     : alu_outputs.op_stage2,
					       rd            : rd_addr, 
					       addr          : alu_outputs.addr,
                                               mem_width_code: alu_outputs.mem_width_code,
                                               mem_unsigned  : alu_outputs.mem_unsigned,
`ifdef ISA_CHERI
                                               mem_allow_cap : alu_outputs.mem_allow_cap,
                                               val1          : alu_outputs.val1_cap_embed_cap ? embed_cap(alu_outputs.cap_val1): embed_int(alu_outputs.val1),
                                               val2          : alu_outputs.val2_cap_not_int ? embed_cap(alu_outputs.cap_val2): embed_int(alu_outputs.val2),
`else
                                               val1          : alu_outputs.val1,
                                               val2          : alu_outputs.val2,
`endif
                                               val1_fast     : alu_outputs.val1_fast,
                                               val2_fast     : alu_outputs.val2_fast,
`ifdef ISA_F
					       fval1         : alu_outputs.fval1,
					       fval2         : alu_outputs.fval2,
					       fval3         : alu_outputs.fval3,
					       rd_in_fpr     : alu_outputs.rd_in_fpr,
					       rs_frm_fpr    : alu_outputs.rs_frm_fpr,
					       val1_frm_gpr  : alu_outputs.val1_frm_gpr,
					       rounding_mode : alu_outputs.rm,
`endif
`ifdef ISA_CHERI
                                               check_enable       : alu_outputs.check_enable,
                                               check_inclusive    : alu_outputs.check_inclusive,
                                               check_authority    : alu_outputs.check_authority,
                                               check_authority_idx: alu_outputs.check_authority_idx,
                                               check_address_low  : alu_outputs.check_address_low,
                                               check_address_high : alu_outputs.check_address_high,
                                               check_exact_enable : alu_outputs.check_exact_enable,
                                               check_exact_success: alu_outputs.check_exact_success,
`ifdef PERFORMANCE_MONITORING
                                               set_offset_in_bounds : alu_outputs.set_offset_in_bounds,
`endif
`endif
`ifdef INCLUDE_TANDEM_VERIF
					       trace_data    : alu_outputs.trace_data,
`endif
`ifdef RVFI
                                               info_RVFI_s1  : info_RVFI,
`endif
					       priv          : cur_priv,
                      is_vec_store: rvfi_MWD_send_as_vec,
                      is_vsetvl_instr: is_vsetvl_instr,
                      vsetvl_output: vsetvl_output,
                      vec_wmask: vec_wmask };

`ifdef ISA_CHERI
   let fetch_exc = checkValid(rg_pcc, getTop(toCapPipe(rg_pcc)), rg_stage_input.is_i32_not_i16);
`endif

   // ----------------
   // Combinational output function

   function Output_Stage1 fv_out;
      Output_Stage1 output_stage1 = ?;

      // This stage is empty
      if (! rg_full) begin
	 output_stage1.ostatus = OSTATUS_EMPTY;
      end

      // Wrong branch-prediction epoch: discard instruction (convert into a NOOP)
      else if (rg_stage_input.epoch != cur_epoch) begin
	 output_stage1.ostatus = OSTATUS_PIPE;
	 output_stage1.control = CONTROL_DISCARD;

	 // For debugging only
	 let data_to_stage2 = Data_Stage1_to_Stage2 {
`ifdef ISA_CHERI
                                                     pcc:       rg_pcc,
`else
                                                     pc:        rg_stage_input.pc,
`endif
						     instr:     rg_stage_input.instr,
`ifdef RVFI_DII
                                                     instr_seq: rg_stage_input.instr_seq,
`endif
						     op_stage2: OP_Stage2_ALU,
						     rd:        0,
						     addr:      ?,
						     val1:      ?,
						     val2:      ?,
						     val1_fast: ?,
						     val2_fast: ?,
`ifdef ISA_F
						     fval1           : ?,
						     fval2           : ?,
						     fval3           : ?,
						     rd_in_fpr       : ?,
					             rs_frm_fpr      : ?,
					             val1_frm_gpr    : ?,
						     rounding_mode   : ?,
`endif
                                                     mem_unsigned  : ?,
                                                     mem_width_code: ?,
`ifdef ISA_CHERI
                                               mem_allow_cap      : False,
                                               check_enable       : False,
                                               check_inclusive    : ?,
                                               check_authority    : ?,
                                               check_authority_idx: ?,
                                               check_address_low  : ?,
                                               check_address_high : ?,
`endif
`ifdef INCLUDE_TANDEM_VERIF
						     trace_data: alu_outputs.trace_data,
`endif
`ifdef RVFI
                                                     info_RVFI_s1 : ?,
`endif
						     priv:      cur_priv
						     };

	 output_stage1.data_to_stage2 = data_to_stage2;
      end

`ifdef ISA_CHERI
      else if (isValid(fetch_exc)) begin
	 output_stage1.ostatus   = OSTATUS_NONPIPE;
	 output_stage1.control   = CONTROL_TRAP;
	 output_stage1.trap_info = Trap_Info_Pipe {
                exc_code: exc_code_CHERI,
                cheri_exc_code : fetch_exc.Valid,
                cheri_exc_reg : {1, scr_addr_PCC},
                epcc: rg_pcc,
                tval: rg_stage_input.tval};
	 output_stage1.data_to_stage2 = data_to_stage2;
      end
`endif

      // Stall if bypass pending for GPR rs1 or rs2
      else if (rs1_busy || rs2_busy) begin
	 output_stage1.ostatus = OSTATUS_BUSY;
      end

`ifdef ISA_F
      // Stall if bypass pending for FPR rs1, rs2 or rs3
      else if (frs1_busy || frs2_busy || frs3_busy) begin
	 output_stage1.ostatus = OSTATUS_BUSY;
      end
`endif

      // Trap on fetch-exception
      else if (rg_stage_input.exc) begin
	 output_stage1.ostatus   = OSTATUS_NONPIPE;
	 output_stage1.control   = CONTROL_TRAP;
	 output_stage1.trap_info = Trap_Info_Pipe {
                                              epcc: rg_pcc,
					      exc_code: rg_stage_input.exc_code,
                                              cheri_exc_code: ?,
                                              cheri_exc_reg: ?,
					      tval:     rg_stage_input.tval};
	 output_stage1.data_to_stage2 = data_to_stage2;
      end

      // ALU outputs: pipe (straight/branch)
      // and non-pipe (CSRR_W, CSRR_S_or_C, FENCE.I, FENCE, SFENCE_VMA, xRET, WFI, TRAP)
      else begin
	 let ostatus = (  (   (alu_outputs.control == CONTROL_STRAIGHT)
			   || (alu_outputs.control == CONTROL_BRANCH)
			   || (alu_outputs.control == CONTROL_CAPBRANCH))
			? OSTATUS_PIPE
			: OSTATUS_NONPIPE);

	 // Compute MTVAL in case of traps
	 let tval = 0;
	 if (alu_outputs.exc_code == exc_code_ILLEGAL_INSTRUCTION) begin
	    // The instruction
	    tval = zeroExtend(rg_stage_input.instr_or_instr_C);
	 end
	 else if (alu_outputs.exc_code == exc_code_INSTR_ADDR_MISALIGNED)
	    tval = alu_outputs.addr;                           // The branch target pc
	 else if (alu_outputs.exc_code == exc_code_BREAKPOINT)
`ifdef ISA_CHERI
	    tval = getPC(rg_pcc);                   // The faulting virtual address
`else
	    tval = rg_stage_input.pc;                          // The faulting virtual address
`endif

	 let trap_info = Trap_Info_Pipe {
                                    epcc: rg_pcc,
				    exc_code: alu_outputs.exc_code,
                                    cheri_exc_code: alu_outputs.cheri_exc_code,
                                    cheri_exc_reg: alu_outputs.cheri_exc_reg,
				    tval:     tval};

	 output_stage1.ostatus        = ostatus;
	 output_stage1.control        = alu_outputs.control;
	 output_stage1.trap_info      = trap_info;
	 output_stage1.redirect       = redirect;
`ifdef ISA_CHERI
         output_stage1.next_pcc       = next_pcc_local;
`else
	 output_stage1.next_pc        = next_pc_local;
`endif
	 output_stage1.cf_info        = alu_outputs.cf_info;
	 output_stage1.data_to_stage2 = data_to_stage2;
      end

      return output_stage1;
   endfunction: fv_out

   (* fire_when_enabled, no_implicit_conditions *)
   rule commit_pcc;
      let new_pcc = fromMaybe(fromMaybe(rg_pcc, rw_next_pcc.wget), rw_fresh_pcc.wget);
      rg_pcc <= new_pcc;
      if (verbosity > 1)
         $display ("    CPU_Stage1 PC: 0x%08h", new_pcc);
   endrule

   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_Stage1 out;
      return fv_out;
   endmethod

   method Action deq ();
      rw_next_pcc.wset(next_pcc_local);
   endmethod

   // ---- Input
   method Action enq (Data_StageD_to_Stage1  data);
      if (data.refresh_pcc) begin
         rw_fresh_pcc.wset(fresh_pcc);
      end
      rg_stage_input <= data;
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
endmodule

// ================================================================

endpackage
