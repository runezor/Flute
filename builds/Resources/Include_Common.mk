###  -*-Makefile-*-

# Copyright (c) 2018-2019 Bluespec, Inc. All Rights Reserved

# This file is not a standalone Makefile, but 'include'd by other Makefiles

# It contains common defs used by Makefiles generated for specific
# RISC-V implementations that differ in RISC-V architectural-feature
# choices, hardware implementation choices and simulator choices.

# ================================================================

.PHONY: help
help:
	@echo '    make  compile      Recompile Core (CPU, caches)'
	@echo '                           NOTE: needs Bluespec bsc compiler'
	@echo '                           For Bluesim: generates Bluesim intermediate files'
	@echo '                           For Verilog simulation: generates RTL'
	@echo '    make  simulator    Compiles and links intermediate files/RTL to create simulation executable'
	@echo '                           (Bluesim, verilator or iverilog)'
	@echo '    make  tagsparams   Generates the CHERI tag controller parameters source file'
	@echo '    make  all          = make  compile  simulator'
	@echo ''
	@echo '    make  run_example  Runs simulation executable on ELF given by EXAMPLE'
	@echo ''
	@echo '    make  test         Runs simulation executable on rv32ui-p-add or rv64ui-p-add'
	@echo '    make  isa_tests    Runs simulation executable on all relevant standard RISC-V ISA tests'
	@echo ''
	@echo '    make  clean        Remove intermediate build-files unnecessary for execution'
	@echo '    make  full_clean   Restore to pristine state (pre-building anything)'

.PHONY: all
all: simulator

# ================================================================
# Search path for bsc for .bsv files

CORE_DIRS = $(REPO)/src_Core/CPU:$(REPO)/src_Core/ISA:$(REPO)/src_Core/RegFiles:$(REPO)/src_Core/Core:$(REPO)/src_Core/Near_Mem_VM:$(REPO)/src_Core/PLIC:$(REPO)/src_Core/Near_Mem_IO:$(REPO)/src_Core/Debug_Module:$(REPO)/src_Core/BSV_Additional_Libs

TESTBENCH_DIRS  = $(REPO)/src_Testbench/Top:$(REPO)/src_Testbench/SoC

RVFI_DII_DIRS = $(REPO)/src_Verifier:$(REPO)/src_Verifier/BSV-RVFI-DII

CHERI_DIRS = $(REPO)/libs/cheri-cap-lib:$(REPO)/libs/TagController/TagController:$(REPO)/libs/TagController/TagController/CacheCore:$(REPO)/libs/BlueStuff/BlueUtils

AXI_DIRS = $(REPO)/libs/BlueStuff/AXI:$(REPO)/libs/BlueStuff/BlueBasics:$(REPO)/libs/BlueStuff

BSC_PATH = $(CUSTOM_DIRS):$(CORE_DIRS):$(TESTBENCH_DIRS):$(AXI_DIRS):$(RVFI_DII_DIRS):$(CHERI_DIRS):+

# ----------------
# Top-level file and module

TOPFILE   ?= $(REPO)/src_Testbench/Top/Top_HW_Side.bsv
TOPMODULE ?= mkTop_HW_Side

# ================================================================
# bsc compilation flags

# XXX
# Using '-no-show-timestamps' with
# Bluespec Compiler, version 2017.07.A (build 1da80f1, 2017-07-21)
# results in
# Error: Command line: (S0008)
#   Unrecognized flag: -no-show-timestamps
# XXX
BSC_COMPILATION_FLAGS += \
	-D MEM64 -D RISCV -D BLUESIM \
	-keep-fires -aggressive-conditions -no-warn-action-shadowing -check-assert \
	-suppress-warnings G0020    \
	+RTS -K128M -RTS  -show-range-conflict
	#-D NOTAG

# ================================================================
# Runs simulation executable on ELF given by EXAMPLE

EXAMPLE ?= PLEASE_DEFINE_EXAMPLE_PATH_TO_ELF

.PHONY: run_example
run_example:
	make -C  $(TESTS_DIR)/elf_to_hex
	$(TESTS_DIR)/elf_to_hex/elf_to_hex  $(EXAMPLE)  Mem.hex
	./exe_HW_sim  $(VERBOSITY)  +exit

# ================================================================
# Test: run the executable on the standard RISCV ISA test specified in TEST

TESTS_DIR ?= $(REPO)/Tests

VERBOSITY ?= +v1

.PHONY: test
test:
	make -C  $(TESTS_DIR)/elf_to_hex
	$(TESTS_DIR)/elf_to_hex/elf_to_hex  $(TESTS_DIR)/isa/$(TEST)  Mem.hex
	./exe_HW_sim  $(VERBOSITY)  +tohost

# ================================================================
# ISA Regression testing

.PHONY: isa_tests
isa_tests:
	make -C  $(TESTS_DIR)/elf_to_hex
	@echo "Running regressions on ISA tests; saving logs in Logs/"
	$(REPO)/Tests/Run_regression.py  ./exe_HW_sim  $(REPO)  ./Logs  $(ARCH)
	@echo "Finished running regressions; saved logs in Logs/"

# ================================================================
# Generate Bluespec CHERI tag controller source file

.PHONY: tagsparams
tagsparams: $(REPO)/libs/TagController/tagsparams.py
	@echo "INFO: Re-generating CHERI tag controller parameters"
	$^ -v -c $(CAPSIZE) -s $(TAGS_STRUCT:"%"=%) -a $(TAGS_ALIGN) --covered-start-addr 0x80000000 --covered-mem-size 0x3fffc000 --top-addr 0xbffff000 -b TagTableStructure.bsv

	@echo "INFO: Re-generated CHERI tag controller parameters"
compile: tagsparams

# ================================================================

.PHONY: clean
clean:
	rm -r -f  *~  Makefile_*  symbol_table.txt  build_dir  obj_dir
	rm -f $(REPO)/src_Testbench/SoC/TagTableStructure.bsv

.PHONY: full_clean
full_clean: clean
	rm -r -f  $(SIM_EXE_FILE)*  *.log  *.vcd  *.hex  Logs/

# ================================================================
