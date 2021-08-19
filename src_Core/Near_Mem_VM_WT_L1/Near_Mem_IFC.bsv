// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved.

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

// ================================================================
// Project imports

import ISA_Decls :: *;

import MMU_Cache_Common :: *;
import AXI4             :: *;
import Fabric_Defs      :: *;
import Cache_Decls      :: *;

`ifdef PERFORMANCE_MONITORING
import PerformanceMonitor :: *;
`endif

`ifdef INCLUDE_DMEM_SLAVE
import AXI4Lite_Types :: *;
`endif

// ================================================================
// Near-Mem parameters (statically defined)

// Id of requestor for 'coherent DMA' port into (optional) L2 cache

typedef 6   Wd_Id_Dma;
typedef 64  Wd_Addr_Dma;
typedef 512 Wd_Data_Dma;
typedef 0   Wd_AW_User_Dma;
typedef 0   Wd_W_User_Dma;
typedef 0   Wd_B_User_Dma;
typedef 0   Wd_AR_User_Dma;
typedef 0   Wd_R_User_Dma;

// ================================================================

`ifdef PERFORMANCE_MONITORING
typedef struct {
   Bool evt_LD;
   Bool evt_LD_MISS;
   Bool evt_LD_MISS_LAT;
   Bool evt_ST;
   Bool evt_ST_MISS;     // Unimplemented
   Bool evt_ST_MISS_LAT; // Unimplemented
   Bool evt_AMO;
   Bool evt_AMO_MISS;
   Bool evt_AMO_MISS_LAT;
   Bool evt_TLB;
   Bool evt_TLB_MISS;     // Only leaf is stored in TLB thus a full
   Bool evt_TLB_MISS_LAT; // walk must happen every miss
   Bool evt_TLB_FLUSH;
   Bool evt_EVICT;
} EventsCache deriving (Bits, FShow);

instance BitVectorable #(EventsCache, 1, m) provisos (Bits #(EventsCache, m));
      function to_vector = struct_to_vector;
endinstance
`endif

interface Near_Mem_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;

   // ----------------
   // IMem

   // CPU side
   interface IMem_IFC  imem;

   // Fabric side
   interface AXI4_Master #( Wd_MId, Wd_Addr, Wd_Data
                          , Wd_AW_User, Wd_W_User, Wd_B_User
                          , Wd_AR_User, Wd_R_User) imem_master;

   // ----------------
   // DMem

   // CPU side
   interface DMem_IFC  dmem;

   // Fabric side
   interface Near_Mem_Fabric_IFC mem_master;

   // ----------------------------------------------------------------
   // Optional AXI4-Lite DMem slave interface

`ifdef INCLUDE_DMEM_SLAVE
   interface AXI4Lite_Slave #(Wd_Addr, Wd_Data, 0, 0, 0, 0, 0) dmem_slave;
`endif

   // ----------------
   // Fences

   interface Server #(Token, Token) server_fence_i;

   interface Server #(Fence_Ordering, Token) server_fence;

`ifdef ISA_PRIV_S
   interface Server #(Token, Token) sfence_vma_server;
`endif

   // ----------------------------------------------------------------
   // Interface to 'coherent DMA' port of optional L2 cache

   interface AXI4_Slave #( Wd_SId_2x4, Wd_Addr, Wd_Data
                         , Wd_AW_User, Wd_W_User, Wd_B_User
                         , Wd_AR_User, Wd_R_User)  dma_server;

   // ----------------------------------------------------------------
   // Misc. control and status

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

typedef TDiv#(Bits_per_CWord, CLEN) Cache_Cap_Tag_Width;
typedef Tuple2#(Bit#(Cache_Cap_Tag_Width), CWord) Cache_Entry;

// ================================================================
// Cache flush specs

Bit #(1) flush_to_invalid = 0;
Bit #(1) flush_to_clean   = 1;

// ================================================================
// IMem interface

interface IMem_IFC;
   // CPU side: IMem request
   (* always_ready *)
   method Action  req (Bit #(3) f3,
		       WordXL addr
`ifdef ISA_PRIV_S
		       // The following  args for VM
		       ,Priv_Mode  priv,
		       Bit #(1)   sstatus_SUM,
		       Bit #(1)   mstatus_MXR,
		       WordXL     satp
`endif
`ifdef RVFI_DII
             , Dii_Id seq_req
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
                              Tuple2#(Instr, Dii_Id) instr;
`else
                              Instr    instr;
`endif
   (* always_ready *)  method Bool     exc;
   (* always_ready *)  method Exc_Code exc_code;
   (* always_ready *)  method WordXL   tval;        // can be different from PC

`ifdef PERFORMANCE_MONITORING
   method EventsCache events;
`endif
endinterface

// ================================================================
// DMem interface

interface DMem_IFC;
   // CPU side: DMem request
   (* always_ready *)
   method Action  req (CacheOp op,
		       Bit #(3) f3,
               Bool is_unsigned,
`ifdef ISA_A
		       Bit #(5) amo_funct5,
`endif
		       Addr addr,
               Tuple2#(Bool, Bit #(128)) store_value
`ifdef ISA_PRIV_S
		       // The following  args for VM
		       ,Priv_Mode  priv,
		       Bit #(1)   sstatus_SUM,
		       Bit #(1)   mstatus_MXR,
		       WordXL     satp
`endif
                       );    // { VM_Mode, ASID, PPN_for_page_table }
   (* always_ready *)  method Action commit;

   // CPU side: DMem response
   (* always_ready *)  method Bool       valid;
   (* always_ready *)  method Tuple2#(Bool, Bit #(128))  word128;      // Load-value
   (* always_ready *)  method Bit #(128)  st_amo_val;  // Final store-value for ST, SC, AMO
   (* always_ready *)  method Bool       exc;
   (* always_ready *)  method Exc_Code   exc_code;

`ifdef PERFORMANCE_MONITORING
   method EventsCache events;
`endif
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
function Tuple2#(Bool, Bit #(128)) fn_extract_and_extend_bytes (Bit #(3) f3, Bool is_unsigned, WordXL byte_addr, Cache_Entry word128_tagged);
   Bit #(64)  result_lo  = 0;
   Bit #(64)  result_hi  = 0;
   Bit #(4)  addr_lsbs = byte_addr [3:0];

   Bool tag = False;
   Bit #(128) word128 = tpl_2(word128_tagged);

   let u_s_extend = is_unsigned ? zeroExtend : signExtend;

   case (f3)
      0: case (addr_lsbs)
		'h0: result_lo = u_s_extend (word128 [ 7: 0]);
		'h1: result_lo = u_s_extend (word128 [15: 8]);
		'h2: result_lo = u_s_extend (word128 [23:16]);
		'h3: result_lo = u_s_extend (word128 [31:24]);
		'h4: result_lo = u_s_extend (word128 [39:32]);
		'h5: result_lo = u_s_extend (word128 [47:40]);
		'h6: result_lo = u_s_extend (word128 [55:48]);
		'h7: result_lo = u_s_extend (word128 [63:56]);
		'h8: result_lo = u_s_extend (word128 [71:64]);
		'h9: result_lo = u_s_extend (word128 [79:72]);
		'ha: result_lo = u_s_extend (word128 [87:80]);
		'hb: result_lo = u_s_extend (word128 [95:88]);
		'hc: result_lo = u_s_extend (word128 [103:96]);
		'hd: result_lo = u_s_extend (word128 [111:104]);
		'he: result_lo = u_s_extend (word128 [119:112]);
		'hf: result_lo = u_s_extend (word128 [127:120]);
	     endcase

      1: case (addr_lsbs)
		'h0: result_lo = u_s_extend (word128 [15: 0]);
		'h2: result_lo = u_s_extend (word128 [31:16]);
		'h4: result_lo = u_s_extend (word128 [47:32]);
		'h6: result_lo = u_s_extend (word128 [63:48]);
		'h8: result_lo = u_s_extend (word128 [79:64]);
		'ha: result_lo = u_s_extend (word128 [95:80]);
		'hc: result_lo = u_s_extend (word128 [111:96]);
		'he: result_lo = u_s_extend (word128 [127:112]);
	     endcase

      2: case (addr_lsbs)
		'h0: result_lo = u_s_extend (word128 [31: 0]);
		'h4: result_lo = u_s_extend (word128 [63:32]);
		'h8: result_lo = u_s_extend (word128 [95:64]);
		'hc: result_lo = u_s_extend (word128 [127:96]);
	     endcase

      3: case (addr_lsbs)
		'h0: begin
           result_lo = u_s_extend (word128 [63:0]);
`ifdef ISA_CHERI
           if (valueOf(CLEN) == 64) tag = tpl_1(word128_tagged)[0] == 1'b1;
`endif
         end
		'h8: begin
           result_lo = u_s_extend (word128 [127:64]);
`ifdef ISA_CHERI
           if (valueOf(CLEN) == 64) tag = tpl_1(word128_tagged)[1] == 1'b1;
`endif
         end
	     endcase

      4: begin
            result_lo = word128[63:0];
            result_hi = word128[127:64];
`ifdef ISA_CHERI
            tag = tpl_1(word128_tagged)[0] == 1'b1;
`endif
         end
   endcase
   return tuple2(tag, {result_hi, result_lo});
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
// ALU for AMO ops.
// Returns the value to be stored back to mem.

`ifdef ISA_A
function Tuple2 #(Tuple2#(Bool, Bit #(128)),
		  Tuple2 #(Bool, Bit#(128))) fn_amo_op (
		                        Bit #(3)   funct3,    // encodes data size (.W or .D)
					Bit #(5)   funct5,    // encodes the AMO op
					WordXL     addr,      // lsbs indicate which 32b W in 64b D (.W)
					Cache_Entry ld_val,   // value loaded from mem
					Tuple2#(Bool, Bit #(128)) st_val);   // Value from CPU reg Rs2
   let extracted_q1 = fn_extract_and_extend_bytes(funct3, False, addr, ld_val);
   Bit #(128) q1    = tpl_2(extracted_q1);
   Bit #(128) q2    = tpl_2(st_val);
   Bit #(64) w1     = truncate(q1);
   Bit #(64) w2     = truncate(q2);
   Int #(64) i1     = unpack (w1);    // Signed, for signed ops
   Int #(64) i2     = unpack (w2);    // Signed, for signed ops
   if (funct3 == f3_AMO_W) begin
      w1 = zeroExtend (w1 [31:0]);
      w2 = zeroExtend (w2 [31:0]);
      i1 = unpack (signExtend (w1 [31:0]));
      i2 = unpack (signExtend (w2 [31:0]));
   end
   // new_st_val is new value to be stored back to mem (w1 op w2)
   Bit#(128) new_st_val_128;
   Bool new_st_tag = False;
   Bool old_ld_tag = False;
   if (funct3 == f3_AMO_CAP) begin
      new_st_val_128 = q2;
      new_st_tag = tpl_1(st_val);
      old_ld_tag = tpl_1 (extracted_q1);
   end else begin
     Bit #(64) new_st_val_64 = ?;
     case (funct5)
        f5_AMO_SWAP: new_st_val_64 = w2;
        f5_AMO_ADD:  new_st_val_64 = pack (i1 + i2);
        f5_AMO_XOR:  new_st_val_64 = w1 ^ w2;
        f5_AMO_AND:  new_st_val_64 = w1 & w2;
        f5_AMO_OR:   new_st_val_64 = w1 | w2;
        f5_AMO_MINU: new_st_val_64 = ((w1 < w2) ? w1 : w2);
        f5_AMO_MAXU: new_st_val_64 = ((w1 > w2) ? w1 : w2);
        f5_AMO_MIN:  new_st_val_64 = ((i1 < i2) ? w1 : w2);
        f5_AMO_MAX:  new_st_val_64 = ((i1 > i2) ? w1 : w2);
     endcase

     if (funct3 == f3_AMO_W)
       new_st_val_64 = zeroExtend (new_st_val_64 [31:0]);

     new_st_val_128 = zeroExtend(new_st_val_64);
   end

   return tuple2 (tuple2(old_ld_tag, q1),
                  tuple2(new_st_tag, zeroExtend(new_st_val_128)));
endfunction: fn_amo_op
`endif

// ================================================================

endpackage: Near_Mem_IFC
