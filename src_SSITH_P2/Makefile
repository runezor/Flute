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
ARCH ?= RV64ACDFIMSU

# ================================================================
# RISC-V config macros passed into Bluespec 'bsc' compiler

BSC_COMPILATION_FLAGS += \
	-D RV64 \
	-D SV39 \
	-D ISA_PRIV_M  -D ISA_PRIV_S  -D ISA_PRIV_U  \
	-D ISA_I  -D ISA_M  -D ISA_A  -D ISA_C  \
	-D ISA_F -D ISA_D -D ISA_FD_DIV  \
	-D ISA_FD -D ISA_F_OR_D \
	-D SHIFT_BARREL    \
	-D MULT_SYNTH     \
	-D Near_Mem_Caches    \
	-D FABRIC64    \
	-D INCLUDE_GDB_CONTROL \
	-D BRVF_TRACE \
	-D XILINX_BSCAN  -D XILINX_XCVU9P  -D JTAG_TAP

# ================================================================
# Search path for bsc for .bsv files

SRC_CORE ?= $(REPO)/src_Core/Core
CONTRIB_DIRS = %/Libraries/Bus
TESTBENCH_DIRS  = $(REPO)/src_Testbench/Fabrics/AXI4
CORE_DIRS = $(REPO)/src_Core/CPU:$(REPO)/src_Core/ISA:$(REPO)/src_Core/RegFiles:$(SRC_CORE):$(REPO)/src_Core/Near_Mem_VM:$(REPO)/src_Core/PLIC:$(REPO)/src_Core/Near_Mem_IO:$(REPO)/src_Core/Debug_Module:$(REPO)/src_Core/BSV_Additional_Libs
AXI_DIRS = %/Libraries/AMBA_TLM3/TLM3:%/Libraries/AMBA_TLM3/Axi:%/Libraries/AMBA_TLM3/Axi4

BSC_PATH = $(CONTRIB_DIRS):src_BSV:$(TESTBENCH_DIRS):$(CORE_DIRS):$(AXI_DIRS):+

# ----------------
# Top-level file and module

TOPFILE   = src_BSV/P2_Core.bsv
TOPMODULE = mkP2_Core

# ================================================================
# bsc compilation flags

BSC_COMPILATION_FLAGS += \
	-keep-fires -aggressive-conditions -no-warn-action-shadowing -no-show-timestamps \
	-suppress-warnings G0020    \
	+RTS -K128M -RTS  -show-range-conflict

# ================================================================
# Generate Verilog RTL from BSV sources (needs Bluespec 'bsc' compiler)

RTL_GEN_DIRS = -vdir Verilog_RTL  -bdir build_dir  -info-dir build_dir

build_dir:
	mkdir -p $@

Verilog_RTL:
	mkdir -p $@

.PHONY: compile
compile:  build_dir  Verilog_RTL
	@echo  "INFO: Generating RTL into Verilog_RTL ..."
	bsc -u -elab -verilog  $(RTL_GEN_DIRS)  $(BSC_COMPILATION_FLAGS) -p $(BSC_PATH)  $(TOPFILE)
	@echo  "INFO: Generated RTL into Verilog_RTL"
	cp  Verilog_RTL/*  xilinx_ip/hdl/
	@echo  "INFO: Copied RTL from  Verilog_RTL/  to  xilinx_ip/hdl/"

# ================================================================

.PHONY: clean
clean:
	rm -r -f  *~  Makefile_*  build_dir

.PHONY: full_clean
full_clean: clean
	rm -r -f  *.log  Verilog_RTL

# ================================================================
