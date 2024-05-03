(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory profile_conversion imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "profile_conversion.c"

text \<open>Some ML profiling for the various optimisation stages. See also the additional information
on tracing and timing in \<^file>\<open>../examples/TraceDemo.thy\<close>.\<close>


declare [[verbose=1]]
declare [[verbose_timing=2]]
declare [[autocorres_profile_conversion_enabled=true]]
declare [[autocorres_profile_conversion_verbosity=1]]
declare [[ML_print_depth=10000]]

text \<open>Option \<^verbatim>\<open>trace_opt\<close> has to be set in order for the profiling to step in.\<close>

autocorres [trace_opt]"profile_conversion.c"

ML \<open>
val res = (AutoCorresTrace.ProfileConv.get ( @{context}))
\<close>

text \<open>The table is index by a tuple: function name, phase, stage.
The output is a tuple: timing information, input term and the output term of the optimisation.
\<close>
ML \<open>
val t = AutoCorresTrace.ProfileConv.Table.lookup res ("in_loop", FunctionInfo.WA, FunctionInfo.PEEP)
\<close>

ML \<open>
val ps = AutoCorresTrace.ProfileConv.Table.dest res
\<close>


ML \<open>
open AutoCorresTrace.Statistics
\<close>

text \<open>Summary of all the information.\<close>
ML
\<open>
val _ = statistics ps
\<close>

text \<open>Examples of a retrieval of results by a predicate on the elements.\<close>
ML \<open>
val unchanged_glob_add = select ps (unchanged_eq andf (same_name "glob_add"))
val changed_glob_add = select ps (changed_eq andf (same_name "glob_add"))
\<close>

end