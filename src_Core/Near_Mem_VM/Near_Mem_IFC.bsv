// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved.

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

// Near_Mem_IFC encapsulates the MMU and L1 cache.
// It is 'near' the CPU (1-cycle access in common case).

// On the CPU side it directly services instruction fetches and DMem
// reads and writes.

// On the Fabric side it has two Master sub-interfaces.
// One master sub-interface is used for instruction-memory access.
// The other master sub-interface is used for data-memory and I/O access.

// It can have various implementations:
//  - As an almost empty pass-through to the fabric
//  - As a cache (unified or separate I- and D-)
//        Fabric-side Server interface is not used (no back door to caches)
//  - As a TCM (Tightly-Coupled Memory)
//        Fabric-side IMem Client is not used (all fabric traffic is data or I/O mem)

package Near_Mem_IFC;

// ================================================================
// BSV lib imports

import GetPut       :: *;
import ClientServer :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;
import AXI4      :: *;

// ================================================================
// Project imports

import ISA_Decls :: *;

import Fabric_Defs :: *;

// ================================================================

interface Near_Mem_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;

   // ----------------
   // IMem

   // CPU side
   interface IMem_IFC  imem;

   // Fabric side
   interface AXI4_Master_Synth #(Wd_MId, Wd_Addr, Wd_Data,
                                 Wd_AW_User, Wd_W_User, Wd_B_User,
                                 Wd_AR_User, Wd_R_User) imem_master;

   // ----------------
   // DMem

   // CPU side
   interface DMem_IFC  dmem;

   // Fabric side
   interface AXI4_Master_Synth #(Wd_MId_2x3, Wd_Addr, Wd_Data,
                                 Wd_AW_User, Wd_W_User, Wd_B_User,
                                 Wd_AR_User, Wd_R_User) dmem_master;

   // ----------------
   // Fences

   interface Server #(Token, Token) server_fence_i;

   interface Server #(Fence_Ordering, Token) server_fence;

   // SFENCE_VMA
   method Action sfence_vma;
endinterface

// ================================================================
// Near_Mem opcodes

typedef enum {  CACHE_LD
	      , CACHE_ST
`ifdef ISA_A
	      , CACHE_AMO
`endif
   } CacheOp
deriving (Bits, Eq, FShow);

typedef 128 Cache_Data_Width;
`ifdef ISA_CHERI
typedef TDiv#(Cache_Data_Width, CLEN) Cache_Cap_Tag_Width;
typedef Tuple2#(Bit#(Cache_Cap_Tag_Width), Bit#(Cache_Data_Width)) Cache_Entry;
`else
typedef Tuple2#(Bit#(0), Bit#(Cache_Data_Width)) Cache_Entry;
`endif

// ================================================================
// IMem interface

interface IMem_IFC;
   // CPU side: IMem request
   (* always_ready *)
   method Action  req (Bit #(3) width_code,
		       WordXL addr,
		       // The following  args for VM
		       Priv_Mode  priv,
		       Bit #(1)   sstatus_SUM,
		       Bit #(1)   mstatus_MXR,
		       WordXL     satp
`ifdef RVFI_DII
             , UInt#(SEQ_LEN) seq_req
`endif
                              );    // { VM_Mode, ASID, PPN_for_page_table }

`ifdef ISA_CHERI
   (* always_ready *)  method Action commit;
`endif

   // CPU side: IMem response
   (* always_ready *)  method Bool     valid;
   (* always_ready *)  method Bool     is_i32_not_i16;
   (* always_ready *)  method WordXL   pc;
   (* always_ready *)  method
`ifdef RVFI_DII
                              Tuple2#(Instr, UInt#(SEQ_LEN)) instr;
`else
                              Instr    instr;
`endif
   (* always_ready *)  method Bool     exc;
   (* always_ready *)  method Exc_Code exc_code;
   (* always_ready *)  method WordXL   tval;        // can be different from PC
endinterface

// ================================================================
// DMem interface

interface DMem_IFC;
   // CPU side: DMem request
   (* always_ready *)
   method Action  req (CacheOp op,
		       Bit #(3) width_code,
               Bool is_unsigned,
`ifdef ISA_A
		       Bit #(7) amo_funct7,
`endif
		       WordXL addr,
		       Tuple2#(Bool, Bit #(128)) store_value,
		       // The following  args for VM
		       Priv_Mode  priv,
		       Bit #(1)   sstatus_SUM,
		       Bit #(1)   mstatus_MXR,
		       WordXL     satp);    // { VM_Mode, ASID, PPN_for_page_table }

`ifdef ISA_CHERI
   (* always_ready *)  method Action commit;
`endif

   // CPU side: DMem response
   (* always_ready *)  method Bool       valid;
   (* always_ready *)  method Tuple2#(Bool, Bit #(128))  word128;      // Load-value
   (* always_ready *)  method Bit #(128)  st_amo_val;  // Final store-value for ST, SC, AMO
                                                       // TODO this also needs tag?
   (* always_ready *)  method Bool       exc;
   (* always_ready *)  method Exc_Code   exc_code;
endinterface

// ================================================================
// Extract bytes from raw word read from near-mem.
// The bytes of interest are offset according to LSBs of addr.
// Arguments:
//  - a RISC-V LD/ST f3 value (encoding LB, LH, LW, LD, LBU, LHU, LWU)
//  - a byte-address
//  - a load-word (loaded from cache/mem)
// result:
//  - word with correct byte(s) shifted into LSBs and properly extended

//TODO make generic
function Tuple2#(Bool, Bit #(128)) fn_extract_and_extend_bytes (Bit #(3) width_code, Bool is_unsigned, WordXL byte_addr, Cache_Entry word128_tagged);
   Bit #(128) result    = 0;
   Bit #(4)  addr_lsbs = byte_addr [3:0];

   Bool tag = False;
   Bit #(128) word128 = tpl_2(word128_tagged);

   let u_s_extend = is_unsigned ? zeroExtend : signExtend;

   case (width_code)
      0: case (addr_lsbs)
		'h0: result = u_s_extend (word128 [ 7: 0]);
		'h1: result = u_s_extend (word128 [15: 8]);
		'h2: result = u_s_extend (word128 [23:16]);
		'h3: result = u_s_extend (word128 [31:24]);
		'h4: result = u_s_extend (word128 [39:32]);
		'h5: result = u_s_extend (word128 [47:40]);
		'h6: result = u_s_extend (word128 [55:48]);
		'h7: result = u_s_extend (word128 [63:56]);
		'h8: result = u_s_extend (word128 [71:64]);
		'h9: result = u_s_extend (word128 [79:72]);
		'ha: result = u_s_extend (word128 [87:80]);
		'hb: result = u_s_extend (word128 [95:88]);
		'hc: result = u_s_extend (word128 [103:96]);
		'hd: result = u_s_extend (word128 [111:104]);
		'he: result = u_s_extend (word128 [119:112]);
		'hf: result = u_s_extend (word128 [127:120]);
	     endcase

      1: case (addr_lsbs)
		'h0: result = u_s_extend (word128 [15: 0]);
		'h2: result = u_s_extend (word128 [31:16]);
		'h4: result = u_s_extend (word128 [47:32]);
		'h6: result = u_s_extend (word128 [63:48]);
		'h8: result = u_s_extend (word128 [79:64]);
		'ha: result = u_s_extend (word128 [95:80]);
		'hc: result = u_s_extend (word128 [111:96]);
		'he: result = u_s_extend (word128 [127:112]);
	     endcase

      2: case (addr_lsbs)
		'h0: result = u_s_extend (word128 [31: 0]);
		'h4: result = u_s_extend (word128 [63:32]);
		'h8: result = u_s_extend (word128 [95:64]);
		'hc: result = u_s_extend (word128 [127:96]);
	     endcase

      3: case (addr_lsbs)
		'h0: begin
           result = u_s_extend (word128 [63:0]);
`ifdef ISA_CHERI
           if (valueOf(CLEN) == 64) tag = tpl_1(word128_tagged)[0] == 1'b1;
`endif
         end
		'h8: begin
           result = u_s_extend (word128 [127:64]);
`ifdef ISA_CHERI
           if (valueOf(CLEN) == 64) tag = tpl_1(word128_tagged)[1] == 1'b1;
`endif
         end
	     endcase

      4: begin
            result = word128;
`ifdef ISA_CHERI
            tag = tpl_1(word128_tagged)[0] == 1'b1;
`endif
         end
   endcase
   return tuple2(tag, result);
endfunction

// ================================================================
// Extract bytes from word read from fabric.
// The bytes of interest are already in the LSBs of 'word',
// they just have to be suitably extended.
// Arguments:
//  - a RISC-V LD/ST f3 value (encoding LB, LH, LW, LD, LBU, LHU, LWU)
//  - a byte-address
//  - a load-word (loaded from fabric)
// result:
//  - word with correct byte(s), properly extended.

function Bit #(64) fn_extend_bytes (Bit #(3) f3, Bit #(64) word64);
   Bit #(64) result = 0;
   case (f3)
      f3_LB:  result = signExtend (word64 [ 7: 0]);
      f3_LBU: result = zeroExtend (word64 [ 7: 0]);

      f3_LH:  result = signExtend (word64 [15: 0]);
      f3_LHU: result = zeroExtend (word64 [15: 0]);

      f3_LW:  result = signExtend (word64 [31: 0]);
      f3_LWU: result = zeroExtend (word64 [31: 0]);

      f3_LD:  result = word64;
   endcase

   return result;
endfunction

// ================================================================
// Convert width of an address from PA to Fabric_Addr

function Fabric_Addr fn_PA_to_Fabric_Addr (PA pa);
   Bit #(TAdd #(Wd_Addr, PA_sz)) fa = zeroExtend (pa);
   Integer hi = valueOf (Wd_Addr) - 1;
   return fa [hi:0];
endfunction

// ================================================================

endpackage: Near_Mem_IFC
