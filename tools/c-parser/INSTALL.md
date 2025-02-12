<!--
  Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

  SPDX-License-Identifier: BSD-2-Clause
-->

# Installation instructions for the C parser

NB: These instructions apply to the stand-alone release of the C parser.
If this is in an L4.verified checkout, see the top-level README.md instead.

This code requires Isabelle2021 and the MLton SML compiler.

The C parser supports multiple target architectures:

    - ARM
    - ARM_HYP
    - AARCH64
    - X64
    - RISCV64
    - Loongarch64

These platforms differ in integer sizes and various other details.
Choose your desired architecture using the L4V_ARCH environment variable:

    export L4V_ARCH=ARM

To build the main heap CParser, use the following command in this directory (src/c-parser).

    isabelle env make CParser

You can also build a regression test with the command

    isabelle env make cparser_test

The regression test may require a lot of memory to run. If your computer has
enough memory, configure your etc/settings file to use a 64-bit runtime:

    ML_PLATFORM=$ISABELLE_PLATFORM64
    ML_HOME=$(dirname "${ML_HOME}")/$ML_PLATFORM

## Loading the parser

The ROOTS file for the parser is in the src directory.
Run Isabelle with this directory as an argument, e.g.:

    isabelle jedit -d src -l CParser foo.thy

If that worked, then the C parser has been loaded successfully.
See the README.md file and PDF documentation for further instructions.

## Other tools

There are two executables that can be built in the standalone-parser directory:

    make standalone-cparser
    make standalone-tokenizer
