#!/usr/bin/python3

# Copyright (c) 2018-2020 Bluespec, Inc.
# See LICENSE for license details

#-
# RVFI_DII + CHERI modifications:
#     Copyright (c) 2018 Jack Deeley (RVFI_DII)
#     Copyright (c) 2018-19 Peter Rugg (RVFI_DII + CHERI)
#     All rights reserved.
#
#     This software was developed by SRI International and the University of
#     Cambridge Computer Laboratory (Department of Computer Science and
#     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
#     DARPA SSITH research programme.
#-

# ================================================================

usage_line = (
    "Usage:\n"
    "    $ CMD  <repo>  <arch>  <sim>  <opt debug>  <opt tandem verif>\n"
    "  where\n"
    "    <repo>            is a path to the CPU source repo (such as Piccolo/Flute)\n"
    "    <arch>            is a word like RV32IMU, RV64ACIMSU, etc.\n"
    "    <sim>             is bluesim, verilator or iverilog\n"
    "    <debug>           if present, is 'debug'\n"
    "    <tandem verif>    if present, is 'tv'\n"
)

# ================================================================

import sys
import os

# ================================================================

def main (argv = None):
    sys.stdout.write ("Use flag --help  or --h for a help message\n")
    if ((len (argv) < 4) or
        (len (argv) > 6) or
        (argv [1] == '-h') or (argv [1] == '--help')):

        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 0

    arg_repo  = argv [1]
    arg_arch  = argv [2]
    arg_sim   = argv [3]
    opt_args  = argv [4:]

    # ----------------
    # Collect <cpu_repo> and check if exists

    if (not os.path.exists (arg_repo)):
        sys.stdout.write ("Error: arg <repo> (='{0}') does not exist?\n".format (arg_repo))
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1

    repo     = os.path.join ("..", arg_repo)
    repobase = os.path.basename (os.path.abspath (os.path.normpath (arg_repo)))

    # ----------------
    # Collect <arch> and check if legal

    known_arch_features = "ACDFGIMSU"
    arch_split = arg_arch.split("x")
    arch_std = arch_split[0]
    arch = arch_std.upper ()

    # G is an abbreviation for IMAFD
    arch_std = arch_std.replace ("G", "IMAFD")

    # We always have "I"
    if ((not "I" in arch_std) and (not "G" in arch_std)): arch_std = arch_std + "I"

    # For Piccolo and Flute, we always have Priv U (along with Priv M)
    if (not "U" in arch_std): arch_std = arch_std + "U"

    if (not (arch_std.startswith ("RV32") or arch_std.startswith ("RV64"))):
        sys.stdout.write ("Error in command-line arg 1 (<arch>='{0}')\n".format (arch_std))
        sys.stdout.write ("    Should begin with 'RV32' or 'RV64'\n")
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1
    if (not all (map ((lambda x: x in known_arch_features), arch_std [4:]))):
        sys.stdout.write ("Error in command-line arg 1 (<arch>='{0}')\n".format (arch_std))
        sys.stdout.write ("    Should only contain alphabets from {0} after RV32/RV64\n".format (known_arch_features))
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1
    if (not ('I' in arch_std)):
        sys.stdout.write ("Error in command-line arg 1 (<arch>='{0}')\n".format (arch_std))
        sys.stdout.write ("    Should contain 'I'\n")
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1
    if (('S' in arch_std) and not ('U' in arch_std)):
        sys.stdout.write ("Error in command-line arg 1 (<arch>='{0}')\n".format (arch_std))
        sys.stdout.write ("    Should contain 'U' since it contains 'S'\n")
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1
    if (('D' in arch_std) and not ('F' in arch_std)):
        sys.stdout.write ("Error in command-line arg 1 (<arch>='{0}')\n".format (arch_std))
        sys.stdout.write ("    Should contain 'F' since it contains 'D'\n")
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1

    # ----------------
    # Collect optional <debug> and <tv> args

    debug = ""
    tv    = ""
    rvfi_dii = ""

    if ((len (opt_args) > 0) and (opt_args [0] == "debug")):
        debug = "_debug"
        opt_args = opt_args [1:]

    if ((len (opt_args) > 0) and (opt_args [0] == "tv")):
        tv = "_tv"
        opt_args = opt_args [1:]

    if ("RVFI_DII" in arch_std):
        arch_std = arch_std.replace("_RVFI_DII","")
        rvfi_dii = "_RVFI_DII"

    cheri = False

    for ext in arch_split:
        if ("RVFI_DII" in ext):
            rvfi_dii = "_RVFI_DII"
        if ("CHERI" in ext):
            cheri = True

    if (not(cheri)):
        sys.stdout.write ("Error in command-line arg 1 (<arch>='{0}')\n".format (arch_std))
        sys.stdout.write ("    Should contain 'xCHERI'\n")
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")

    arch_split = list(map ((lambda x : x.replace("_RVFI_DII", "")), arch_split))

    if (len (opt_args) > 0):
        sys.stdout.write ("Error in optional command-line args (='{0}')\n".format (opt_args [0]))
        sys.stdout.write ("    Should be  'debug', 'tv' or 'RVFI_DII'\n")
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1

    arch = canonical_arch_string ("x".join([arch_std] + arch_split[1:])) + rvfi_dii
    sys.stdout.write ("Canonical arch string is:  '{0}'\n".format (arch))

    # ----------------
    # Collect <sim> and check if legal

    sim = argv [3].lower ()
    if (not ((sim == 'bluesim') or
             (sim == 'verilator') or
             (sim == 'iverilog'))):
        sys.stdout.write ("Error in command-line arg for <sim> (='{0}')\n".format (sim))
        sys.stdout.write ("    Should be  'bluesim',  'verilator'  or  'iverilog'\n")
        sys.stdout.write (usage_line.replace ("CMD", argv [0]))
        sys.stdout.write ("\n")
        return 1

    # ----------------
    # All args collected; create the build directory and its Makefile

    make_build_dir (repo, repobase, arch, sim, debug, tv, rvfi_dii)

    return 0

# ================================================================
# Create canonical architecture string (alphabetical order, no duplicates)
# Can be invoked with or without the leading "RV32" or "RV64"

def canonical_arch_string (arch):
    arch_split = arch.split('x');
    arch_std = arch_split[0];
    prefix = ""
    letters_s = arch_std
    if arch_std.startswith ("RV32"):
        prefix = "RV32"
        letters_s = arch_std [4:]
    elif arch_std.startswith ("RV64"):
        prefix = "RV64"
        letters_s = arch_std [4:]

    # Convert  'letters_s'  string to list of single-char strings
    letters_l  = map  ((lambda j: letters_s [j]),  (range (len (letters_s))))
    # Remove duplicates by converting into a set
    letters_fs = frozenset (letters_l)
    # Convert into a sorted list
    letters_l  = sorted (letters_fs)
    # Join them back into a string
    letters_s  = "".join (letters_l)

    return ("x".join([prefix + letters_s] + arch_split[1:]))

# ================================================================
# Create the build directory and its Makefile

def make_build_dir (repo, repobase, arch, sim, debug, tv, rvfi_dii):

    # debugging only
    if False:
        sys.stdout.write ("repo     = '{0}'\n".format (repo))
        sys.stdout.write ("repobase = '{0}'\n".format (repobase))
        sys.stdout.write ("arch     = '{0}'\n".format (arch))
        sys.stdout.write ("sim      = '{0}'\n".format (sim))
        sys.stdout.write ("debug    = '{0}'\n".format (debug))
        sys.stdout.write ("tv       = '{0}'\n".format (tv))
        sys.stdout.write ("RVFI_DII = '{0}'\n".format (rvfi_dii))
        return

    # Create the directory
    dirname = arch + "_" + repobase + "_" + sim + debug + tv
    if (os.path.exists (dirname)):
        sys.stdout.write ("Directory  '{0}'  exists already\n".format (dirname))
    else:
        sys.stdout.write ("Creating directory    '{0}'\n".format (dirname));
        os.mkdir (dirname)

    arch = arch.replace("_RVFI_DII", "")

    # Create the Makefile (backing up existing copy, if any)
    Makefile_filename = os.path.join (dirname, "Makefile")
    if os.path.exists (Makefile_filename):
        # Back up exising copy by renaming it with a new numeric suffix
        j = 1
        while True:
            suffixed_name = "{0}_{1}".format (Makefile_filename, j)
            if (not os.path.exists (suffixed_name)): break
            j = j + 1
        sys.stdout.write ("    '{0}'  exists already\n".format (Makefile_filename))
        sys.stdout.write ("    Renaming it to {0}\n".format (suffixed_name))
        os.rename (Makefile_filename, suffixed_name)

    sys.stdout.write ("Creating Makefile  '{0}'\n".format (Makefile_filename))
    fo = open (Makefile_filename, "w")

    # Fill in the contents of the Makefile
    fo.write ("###  -*-Makefile-*-\n"
              "\n"
              "# *** DO NOT EDIT! ***\n"
              "# *** This file is program-generated, not hand-written. ***\n")

    fo.write ("# ================================================================\n")
    fo.write ("\n")
    fo.write ("REPO ?= {0}\n".format (repo))
    fo.write ("ARCH ?= {0}\n".format (arch))
    fo.write ("\n")

    arch_split = arch.split('x');
    arch_std = arch_split[0]

    # CHERI parameters
    fo.write ("\n")
    if (arch_std.startswith ("RV32")):
        fo.write ("CAPSIZE = 64\n")
    else:
        fo.write ("CAPSIZE = 128\n")
    fo.write ("TAGS_STRUCT = 0 64\n")
    fo.write ("TAGS_ALIGN = 32\n")
    fo.write ("\n")

    # RISC-V config macros passed into Bluespec 'bsc' compiler
    fo.write ("# ================================================================\n")
    fo.write ("# RISC-V config macros passed into Bluespec 'bsc' compiler\n")
    fo.write ("\n")
    fo.write ("BSC_COMPILATION_FLAGS += \\\n")
    fo.write ("\t-D " + arch_std [0:4] + " \\\n")

    # RISC-V privilege levels
    fo.write ("\t-D ISA_PRIV_M")
    if ("U" in arch_std): fo.write ("  -D ISA_PRIV_U")
    if ("S" in arch_std): fo.write ("  -D ISA_PRIV_S")
    fo.write ("  \\\n")

    # If 'S', specify Virtual Memory scheme
    if ("S" in arch_std):
        if (arch_std.startswith ("RV32")):
            fo.write ("\t-D SV32  \\\n")
        else:
            fo.write ("\t-D SV39  \\\n")

    fo.write("\t-D RISCV\\\n");
    if (arch_std.startswith ("RV32")):
        fo.write ("\t-D CapWidth=64\\\n")
    else:
        fo.write ("\t-D CapWidth=128\\\n")

    fo.write("\t-D PERFORMANCE_MONITORING\\\n")

    # RISC-V arch features
    arch_flags = ""
    if ("G" in arch_std):
        arch_flags = arch_flags + "  -D ISA_I"
        arch_flags = arch_flags + "  -D ISA_M"
        arch_flags = arch_flags + "  -D ISA_A"
        arch_flags = arch_flags + "  -D ISA_F"
        arch_flags = arch_flags + "  -D ISA_D"
        arch_flags = arch_flags + "  -D INCLUDE_FDIV"
        arch_flags = arch_flags + "  -D INCLUDE_FSQRT"
    else:
        if ("I" in arch_std): arch_flags = arch_flags + "  -D ISA_I"
        if ("M" in arch_std): arch_flags = arch_flags + "  -D ISA_M"
        if ("A" in arch_std): arch_flags = arch_flags + "  -D ISA_A"
        if ("F" in arch_std): arch_flags = arch_flags + "  -D ISA_F"
        if ("D" in arch_std): arch_flags = arch_flags + "  -D ISA_D"
        if (("F" in arch_std) or ("D" in arch_std)): arch_flags = arch_flags + "  -D INCLUDE_FDIV"
        if (("F" in arch_std) or ("D" in arch_std)): arch_flags = arch_flags + "  -D INCLUDE_FSQRT"
    if ("C" in arch_std): arch_flags = arch_flags + "  -D ISA_C"
    arch_flags += "".join(["  -D ISA_" + non_std_ext for non_std_ext in arch_split[1:]])
    fo.write ("\t{0}  \\\n".format (arch_flags.lstrip()))

    # Bluespec HW implementation choice for shifter
    # fo.write ("\t-D SHIFT_NONE    \\\n")
    fo.write ("\t-D SHIFT_BARREL    \\\n")
    # fo.write ("\t-D SHIFT_SERIAL    \\\n")
    # fo.write ("\t-D SHIFT_MULT    \\\n")

    # Bluespec HW implementation choice for integer multiply/divide
    fo.write ("\t-D MULT_SYNTH    \\\n")
    # fo.write ("\t-D MULT_SERIAL    \\\n")

    # Bluespec HW implementation choice for "near-mem"
    fo.write ("\t-D Near_Mem_Caches    \\\n")

    # Bluespec HW implementation choice for fabric data width
    fo.write ("\t-D FABRIC64    \\\n")

    # Bluespec testing: observe writes to <tohost> and terminate when non-zero
    fo.write ("\t-D WATCH_TOHOST    \\\n")

    # Support for RISC-V Debug Module
    if (debug != ""):
        fo.write ("\t-D INCLUDE_GDB_CONTROL  \\\n")

    # Support for Bluespec Tandem Verification traces
    if (tv != ""):
        fo.write ("\t-D INCLUDE_TANDEM_VERIF  \\\n")

    if (rvfi_dii != ""):
        fo.write ("\t-D RVFI_DII  \\\n")
        fo.write ("\t-D RVFI  \\\n")

    fo.write ("\n")

    # Default ISA test (RV32/RV64ui-p-add)
    fo.write ("\n"
              + "# Default ISA test\n"
              + "\n"
              + ("TEST ?= {0}".format (arch [0:4].lower()))
              + "ui-p-add\n")
    fo.write ("\n")

    # Include common boilerplate Makefile rules
    fo.write ("#================================================================\n")
    fo.write ("# Common boilerplate rules\n")
    fo.write ("\n")
    fo.write ("include $(REPO)/builds/Resources/Include_Common.mk\n")
    fo.write ("\n")

    # Include simulator-specific Makefile rules
    fo.write ("#================================================================\n")
    fo.write ("# Makefile rules for building for specific simulator: {0}\n".format (sim))
    fo.write ("\n")
    fo.write ("include $(REPO)/builds/Resources/Include_{0}.mk\n".format (sim))
    fo.write ("\n")

    fo.close ()

# ================================================================
# For non-interactive invocations, call main() and use its return value
# as the exit code.
if __name__ == '__main__':
  sys.exit (main (sys.argv))
