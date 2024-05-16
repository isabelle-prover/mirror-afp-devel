(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tracing AutoCorres internals.
 *
 *)

theory TraceDemo imports "AutoCorres2_Main.AutoCorres_Main" begin


install_C_file "trace_demo.c"

text \<open>Various tracing flags can be used to get insight into what goes on within the proofs,
e.g. to gain understanding, debug issues, search for performance bottlenecks etc.
In this file we illustrate some use cases.
To keep the traces meaningful and intelligible it is recommended to break the autocorres calls
single threaded and small, i.e. limit the functions and the phases to be translated.

There are a number of configuration options that influence tracing:

\<^item>@{attribute verbose}, the higher the number the more output. Start with 1 and
  increase successively.
\<^item>@{attribute verbose_timing}, the higher the number the more internal steps are measured and
 output. With @{attribute verbose_timing_threshold} a number of milliseconds can be specified
 that has to be reached in order for a tracing message to be printed. One approach to identify
 performance issues is to start with a low threshold and verbosity to identify a sensible
 threshold and then use that threshold with increased verbosity. Note that pretty printing
 inner syntax can have a decisive impact on performance! To get some culminated timing statistics
 also refer to the profiling options as demonstrated in \<^file>\<open>../proof-tests/profile_conversion.thy\<close>.
\<^item>@{attribute verbose_indent} can be used to indicate sub-proofs by indentation. This
affects the resolution proofs performed by the heap lifting and the word abstraction phase.
The default is \<open>-1\<close> which means no indentation. When set to a value greater or equal to \<open>0\<close> 
indentation is increased with the depth of the proof. When using indentation it might be
useful to copy-paste the output into a new jEdit buffer and enable the indentation based
folding mode: "Utilities -> Buffer Options -> folding mode" option to "indent".
\<^item>Autocorres option \<open>trace_opt\<close> enables some additional tracing for the optimisation steps in 
each phase. 
\<close>


declare [[verbose=2]]
autocorres [
  phase=L1,
  single_threaded,
  trace_opt
  ] "trace_demo.c"

declare [[verbose=0, verbose_timing=1, verbose_timing_threshold=0]]
autocorres [
  phase=L2,
  single_threaded,
  trace_opt
  ] "trace_demo.c"

declare [[verbose=0, verbose_timing=2, verbose_timing_threshold=0]]
autocorres [
  phase=HL,
  single_threaded,
  trace_opt
  ] "trace_demo.c"

declare [[verbose_indent=0, verbose_timing=2, 
verbose_timing_threshold=0, verbose=2]]
autocorres [
  phase=WA,
  single_threaded,
  trace_opt
  ] "trace_demo.c"


declare [[verbose_indent= -1, verbose_timing=2, 
verbose_timing_threshold=0, verbose=2]]
autocorres [
  phase=TS,
  single_threaded,
  trace_opt
  ] "trace_demo.c"




end
