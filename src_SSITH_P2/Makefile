###  -*-Makefile-*-

# ================================================================

.PHONY: help
help:
	@echo '    make  compile      Recompile Core (CPU, caches) into Verilog_RTL and copies into xilinx_ip/hdl'
	@echo '                           NOTE: needs Bluespec bsc compiler'
	@echo ''
	@echo '    make  clean        Remove intermediate build-files'
	@echo '    make  full_clean   Restore this directory to pristine state'

.PHONY: all
all: compile

# ================================================================

REPO ?= ..
ARCH ?= RV64ACDFIMSUxCHERI

# ================================================================
# RISC-V config macros passed into Bluespec 'bsc' compiler

BSC_COMPILATION_FLAGS += \
	-D RV64 \
	-D SV39 \
	-D RISCV \
	-D CapWidth=128 -D CheriBusBytes=8 \
	-D CheriMasterIDWidth=1 -D CheriTransactionIDWidth=5 \
	-D ISA_CHERI \
	-D ISA_PRIV_M  -D ISA_PRIV_S  -D ISA_PRIV_U  \
	-D ISA_I  -D ISA_M  -D ISA_A  -D ISA_C  \
	-D ISA_F -D ISA_D -D INCLUDE_FDIV  -D INCLUDE_FSQRT \
	-D SHIFT_BARREL    \
	-D MULT_SYNTH     \
	-D Near_Mem_Caches    \
	-D FABRIC64    \
	-D INCLUDE_GDB_CONTROL \
	-D BRVF_TRACE \
	-D XILINX_BSCAN  -D XILINX_XCVU9P  -D JTAG_TAP

# CHERI paramters
CAPSIZE = 128
TAGS_STRUCT = 0 64
TAGS_ALIGN = 32

# ================================================================
# Search path for bsc for .bsv files

# ================================================================
# Near-mem (Cache and optional MMU for VM)
# WT = Write-through; WB = write-back
# L1 = L1 only; L1_L2 = L1 + coherent L2

CACHES ?= WT_L1

ifeq ($(CACHES),WB_L1)
  NEAR_MEM_VM_DIR=Near_Mem_VM_WB_L1
else ifeq ($(CACHES),WB_L1_L2)
  NEAR_MEM_VM_DIR=Near_Mem_VM_WB_L1_L2
else
  NEAR_MEM_VM_DIR=Near_Mem_VM_WT_L1
endif

SRC_CORE ?= $(REPO)/src_Core/Core

CONTRIB_DIRS = %/Libraries/Bus

CORE_DIRS = $(REPO)/src_Core/CPU:$(REPO)/src_Core/ISA:$(REPO)/src_Core/RegFiles:$(SRC_CORE):$(REPO)/src_Core/Cache_Config:$(REPO)/src_Core/$(NEAR_MEM_VM_DIR):$(REPO)/src_Core/PLIC:$(REPO)/src_Core/Near_Mem_IO:$(REPO)/src_Core/Debug_Module:$(REPO)/src_Core/BSV_Additional_Libs:$(REPO)/src_SSITH_P2/src_BSV

CHERI_DIRS = $(REPO)/libs/cheri-cap-lib:$(REPO)/libs/TagController/TagController:$(REPO)/libs/TagController/TagController/CacheCore:$(REPO)/libs/BlueStuff/BlueUtils

AXI_DIRS = $(REPO)/libs/BlueStuff/AXI:$(REPO)/libs/BlueStuff/BlueBasics:$(REPO)/libs/BlueStuff

BSC_PATH = -p $(CONTRIB_DIRS):$(CUSTOM_DIRS):$(CORE_DIRS):$(TESTBENCH_DIRS):$(AXI_DIRS):$(RVFI_DII_DIRS):$(CHERI_DIRS):+

# ----------------
# Top-level file and module

TOPFILE   = src_BSV/P2_Core.bsv
TOPMODULE = mkP2_Core

# ================================================================
# bsc compilation flags

BSC_COMPILATION_FLAGS += \
	-keep-fires -aggressive-conditions -no-warn-action-shadowing -no-show-timestamps \
	-suppress-warnings G0020    \
	+RTS -K128M -RTS  -show-range-conflict \
        -unspecified-to X -opt-undetermined-vals

# ================================================================
# Generate Bluespec CHERI tag controller source file

.PHONY: tagsparams
tagsparams: $(REPO)/src_SSITH_P2/src_BSV/TagTableStructure.bsv
$(REPO)/src_SSITH_P2/src_BSV/TagTableStructure.bsv: $(REPO)/libs/TagController/tagsparams.py
	@echo "INFO: Re-generating CHERI tag controller parameters"
	$^ -v -c $(CAPSIZE) -s $(TAGS_STRUCT:"%"=%) -a $(TAGS_ALIGN) --covered-start-addr 0xc0000000 --covered-mem-size 0x3fffc000 --top-addr 0xfffff000 -b $@
	@echo "INFO: Re-generated CHERI tag controller parameters"


# ================================================================
# Generate Verilog RTL from BSV sources (needs Bluespec 'bsc' compiler)

RTL_GEN_DIRS = -vdir Verilog_RTL  -bdir build_dir  -info-dir build_dir

build_dir:
	mkdir -p $@

Verilog_RTL:
	mkdir -p $@

.PHONY: compile
compile:  build_dir tagsparams Verilog_RTL
	@echo  "INFO: Generating RTL into Verilog_RTL ..."
	bsc -u -elab -verilog  $(RTL_GEN_DIRS)  $(BSC_COMPILATION_FLAGS)  $(BSC_PATH)  $(TOPFILE)
	@echo  "INFO: Generated RTL into Verilog_RTL"
	cp  Verilog_RTL/*  xilinx_ip/hdl/
	@echo  "INFO: Copied RTL from  Verilog_RTL/  to  xilinx_ip/hdl/"
	cp  Verilog_RTL/*  altera_ip/hdl/
	@echo  "INFO: Copied RTL from  Verilog_RTL/  to  altera_ip/hdl/"

# ================================================================

.PHONY: clean
clean:
	rm -r -f  *~  Makefile_*  build_dir
	rm -f $(REPO)/src_SSITH_P2/src_BSV/TagTableStructure.bsv

.PHONY: full_clean
full_clean: clean
	rm -r -f  *.log  Verilog_RTL

# ================================================================
