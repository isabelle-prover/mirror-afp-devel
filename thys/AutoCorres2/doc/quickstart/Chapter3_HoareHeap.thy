(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*<*)
theory Chapter3_HoareHeap
imports "AutoCorres2.AutoCorres"
begin

(*>*)

subsection \<open>\texttt{swap}\<close>

text \<open>

  Here, we use AutoCorres to verify a C program that reads and writes to the heap.
  Our C function, \texttt{swap}, swaps two words in memory:

\lstinputlisting[language=C, firstline=11]{swap.c}

  Again, we translate the program using the C parser and AutoCorres.
\<close>

install_C_file "sources/swap.c"
autocorres [heap_abs_syntax, ts_rules = nondet] "swap.c"
(*<*)
context swap_all_corres begin
(*>*)

text \<open>
  Most heap operations in C programs consist of accessing a pointer.
  AutoCorres abstracts the global C heap by creating one heap for
  each type. (In our simple \texttt{swap} example, it creates only
  a @{typ word32} heap.) This makes verification easier as long as
  the program does not access the same memory as two different types.

  There are other operations that are relevant to program verification,
  such as changing the type that occupies a given region of memory.
  AutoCorres will not abstract any functions that use these operations,
  so verifying them will be more complicated (but still possible).
\<close>

text \<open>
  The C parser expresses \texttt{swap} like this:
\<close>

thm swap_body_def
text \<open>@{thm [display] swap_body_def}\<close>

text \<open>
  AutoCorres abstracts the function to this:
\<close>

thm swap'_def
text \<open>@{thm [display] swap'_def }\<close>

text \<open>
  There are some things to note:

  The function contains guards (assertions) that the pointers
  \texttt{a} and \texttt{b} are valid. We need to prove that
  these guards never fail when verifying \texttt{swap}.
  Conversely, when verifying any function that calls
  \texttt{swap}, we need to show that the arguments are
  valid pointers.

  We saw a monadic program in the previous section, but here
  the monad is actually being used to carry the program heap.
\<close>


(*<*)
context 
  fixes s:: lifted_globals
  fixes a::"32 word ptr"
begin
(*>*)
text \<open>
  Now we prove that \texttt{swap} is correct. We use @{term x}
  and @{term y} to ``remember'' the initial values so that we can
  talk about them in the post-condition. The heap access syntax \<^term>\<open>s[a]\<close> is used
  to select the split heap \<^term>\<open>heap_w32\<close> from state \<^term>\<open>s\<close> at pointer \<^term>\<open>a::32 word ptr\<close>.
  \<^footnote>\<open>For more details on the split heap model in autocorres see \autoref{sec:open_struct}.\<close>
\<close>
(*<*)
end
(*>*)

lemma "\<lbrakk>IS_VALID(32 word) s a; s[a] = x; IS_VALID(32 word) s b; s[b] = y\<rbrakk> \<Longrightarrow>
         swap' a b \<bullet> s
       \<lbrace> \<lambda>_ s. s[a] = y \<and> s[b] = x \<rbrace>"
  apply (unfold swap'_def)
  apply runs_to_vcg
  apply clarsimp
  txt \<open>
    The C parser and AutoCorres both model the C heap using functions,
    which takes a pointer to some object in memory. Heap updates are
    modelled using the functional update @{term fun_upd}:

      @{thm [display] fun_upd_def}

    To reason about functional updates, we use the rule fun\_upd\_apply.
\<close>
  apply (simp add: fun_upd_apply)
  done

text \<open>
  Note that we have ``only'' proved that the function swaps its
  arguments. We have not proved that it does \emph{not} change
  any other state. This is a typical \emph{frame problem} with
  pointer reasoning. We can prove a more complete specification
  of \texttt{swap}:
\<close>
lemma "\<lbrakk>(\<And>x y s. P (s[a := x][b := y]) = P s);
       IS_VALID(32 word) s a; s[a] = x; IS_VALID(32 word) s b; s[b] = y ; P s \<rbrakk> \<Longrightarrow>
         (swap' a b) \<bullet> s
       \<lbrace> \<lambda>_ s. s[a] = y \<and> s[b] = x \<and> P s \<rbrace>"
  apply (unfold swap'_def)
  apply runs_to_vcg
  apply (clarsimp simp: fun_upd_apply)+
  done

text \<open>
  In other words, if predicate @{term P} does not depend on the
  inputs to \texttt{swap}, it will continue to hold.

  \emph{Separation logic} provides a more structured approach
  to this problem.
\<close>

(*<*)
end
(*>*)

section "Command Options and Invocation"

subsection "Session Structure"

text \<open>
The supplied session structure has some peculiarities to accomodate the AFP. The AFP presents
the documentation of the session that is named like the AFP-entry. This is @{session AutoCorres2}.
This session also includes this documentation and other example application of AutoCorres.
When you want to use AutoCorres for your own projects you do not have to import these examples.
Thats why we also supply the leaner @{session AutoCorres2_Main} as entry point, which we recommend
as parent session for your applications.
\<close>

subsection "C-Parser"

text \<open>Options for @{command install_C_file},

    syntax \<^verbatim>\<open>install_C_file <filename> [<option> = value, ...]\<close>:

\<^item> \<^verbatim>\<open>memsafe\<close> (default false): add additional guards to ensure that welltypedness of pointers
\<^item> \<^verbatim>\<open>c_types\<close> (default true): import types to UMM model
\<^item> \<^verbatim>\<open>c_defs\<close> (default true): import function to SIMPL
\<^item> \<^verbatim>\<open>roots\<close>: (default all functions): List of C functions that are the root functions to import
\<^item> \<^verbatim>\<open>prune_types\<close> (default true): only import those types that are actually used in the program
\<^item> \<^verbatim>\<open>machinety\<close>: HOL type for ghost state modelling the machine
\<^item> \<^verbatim>\<open>gostty\<close>: HOL type for some additional ghost state
\<^item> \<^verbatim>\<open>skip_asm\<close> (default false): Skip inline assembler
\<close>

text \<open> 
Moreover there are some Isabelle options for more feedback / tracing:
\<^item> \<^verbatim>\<open>c_parser_feedback_level\<close> (default 0), higher number means more tracing
\<^item> \<^verbatim>\<open>option c_parser_verbose\<close> (default false), enable for verbose messages
\<close>

subsubsection \<open>Multiple C Files\<close>

text \<open>Command @{command install_C_file} only has a single C file as argument. When your project
consists of several \<^verbatim>\<open>.c\<close> and \<^verbatim>\<open>.h\<close> you can register those dependencies first, with 
command @{command include_C_file}. The main C file, which is the argument to @{command install_C_file}, 
can then include all these files. If there is no such C file in your project you can create 
one to accomodate @{command install_C_file}.
\<close>

subsubsection \<open>Target Architecture Selection \<^verbatim>\<open>L4V_ARCH\<close>\<close>
text \<open>
The Environment variable \<^verbatim>\<open>L4V_ARCH\<close> can be used to determine the target architecture
which influences the sizes of C integral types and pointer types. Supported platforms are
\<^verbatim>\<open>ARM\<close> (default), \<^verbatim>\<open>ARM64\<close>, \<^verbatim>\<open>ARM_HYP\<close>,  \<^verbatim>\<open>RISCV64\<close> and \<^verbatim>\<open>X64\<close>.

For \<^verbatim>\<open>ARM\<close>, the sizes are:
\<^item> 128 bits: \<^verbatim>\<open>int128\<close>
\<^item> 64 bits: \<^verbatim>\<open>long long\<close>
\<^item> 32 bits: pointers, \<^verbatim>\<open>long\<close>, \<^verbatim>\<open>int\<close>
\<^item> 16 bits: \<^verbatim>\<open>short\<close>

For \<^verbatim>\<open>X64\<close>, \<^verbatim>\<open>ARM64\<close>, \<^verbatim>\<open>ARM_HYP\<close>:
\<^item> 128 bits: \<^verbatim>\<open>int128\<close>
\<^item> 64 bits: pointers, \<^verbatim>\<open>long long\<close>, \<^verbatim>\<open>long\<close>
\<^item> 32 bits: \<^verbatim>\<open>int\<close>
\<^item> 16 bits: \<^verbatim>\<open>short\<close>

For \<^verbatim>\<open>ARM64\<close> \<^verbatim>\<open>char\<close> is signed.

For example to build AutoCorres for ARM64:

    \<^verbatim>\<open>L4V_ARCH=ARM64 isabelle build -d . AutoCorres_Main\<close>
\<close>

subsection "AutoCorres"

text \<open>Options for @{command "init-autocorres"} / @{command "autocorres"}, 

    syntax \<^verbatim>\<open>autocorres [option = value, ...] <filename>\<close>:

\<^item> \<^verbatim>\<open>phase\<close>: perform autocorres up to specified phase only (L1, L2, HL, WA, IO, TS)
\<^item> \<^verbatim>\<open>scope\<close>: space separated list of functions to perform autocorres on. (Default all).
\<^item> \<^verbatim>\<open>scope_depth\<close>: depth of callees to also also include
\<^item> \<^verbatim>\<open>single_threaded\<close>: flag to disable parallel processing (e.g. to make more sense out of tracing messages)
\<^item> \<^verbatim>\<open>no_heap_abs\<close>: space separated list of functions that should be excluded from heap abstraction
\<^item> \<^verbatim>\<open>in_out_parameters\<close>: 'and' separated list of function specs e.g. \<^verbatim>\<open>inc(y:in_out)\<close>, 
  cf. \<^file>\<open>../In_Out_Parameters_Ex.thy\<close>
\<^item> \<^verbatim>\<open>in_out_globals\<close>: 'and' separated list of functions which modify global variables via pointers
\<^item> \<^verbatim>\<open>skip_io_abs\<close>: flag to disable IO abstraction
\<^item> \<^verbatim>\<open>addressable_fields\<close>: space separated list of paths to struct fields that should be addressable in
 the split heap,  cf. \<^file>\<open>../open_struct.thy\<close>
\<^item> \<^verbatim>\<open>ignore_addressable_fields_error\<close>: option to downgrade error to a warning
\<^item> \<^verbatim>\<open>skip_heap_abs\<close>: flag to disable heap abstraction (into split heap)
\<^item> \<^verbatim>\<open>unsigned_word_abs\<close>: space separated list of functions where unsigned words should be abstracted to \<^typ>\<open>nat\<close>.
\<^item> \<^verbatim>\<open>unsigned_word_abs_known_functions\<close>: assume unsigned word abstraction for function pointers
\<^item> \<^verbatim>\<open>no_signed_word_abs\<close>: space separated list of functions where abstraction of unsigned word 
  to \<^typ>\<open>int\<close> should be disabled.
\<^item> \<^verbatim>\<open>no_signed_word_abs_known_functions\<close>: don't assume unsigned word abstraction for function pointers
\<^item> \<^verbatim>\<open>skip_word_abs\<close>: flag to disable word abstraction
\<^item> \<^verbatim>\<open>ts_rules\<close>: space separated list of rules to consider during TS phase (pure, gets, option, nondet, exit).
\<^item> \<^verbatim>\<open>ts_force <rule-name>\<close>: space separated list of function names to put in the specified monad (pure, gets, option, nondet, exit).
\<^item> \<^verbatim>\<open>ts_force_known_functions\<close>: assume function pointers live in the specified monad (pure, gets, option, nondet, exit)
\<^item> \<^verbatim>\<open>heap_abs_syntax\<close>: enable some additional syntax for heap accesses
\<^item> \<^verbatim>\<open>do_polish\<close> (default true): flag for polish phase
\<^item> \<^verbatim>\<open>L1_opt\<close> (RAW | PEEP (default)): level for L1 optimisation
\<^item> \<^verbatim>\<open>L2_opt\<close> (RAW | PEEP (default)): level for L2 optimisation
\<^item> \<^verbatim>\<open>HL_opt\<close> (RAW | PEEP (default)): level for HL optimisation
\<^item> \<^verbatim>\<open>WA_opt\<close> (RAW | PEEP (default)): level for WA optimisation
\<^item> \<^verbatim>\<open>trace_opt\<close>: flag to enable some tracing
\<^item> \<^verbatim>\<open>gen_word_heaps\<close>: flag to generate word heaps even if the program does not use them 
\<^item> \<^verbatim>\<open>keep_going\<close>: continue despite some errors
\<^item> \<^verbatim>\<open>lifted_globals_field_prefix\<close>: custom prefix for split heap naming
\<^item> \<^verbatim>\<open>lifted_globals_field_suffix\<close>: custom suffix for split heap naming
\<^item> \<^verbatim>\<open>function_name_prefix\<close>: custom prefix for generated function names
\<^item> \<^verbatim>\<open>function_name_suffix\<close>: custom suffix for generated function names
\<^item> \<^verbatim>\<open>no_c_termination\<close>: flag to disable termination precondition for correspondence proofs
\<^item> \<^verbatim>\<open>unfold_constructor_bind\<close>: (Selectors (default) | Always | Never) to
  give some user level control to unfold certain "simple" binds.
   cf.: \<^file>\<open>../../tests/proof-tests/unfold_bind_options.thy\<close>
\<^item> \<^verbatim>\<open>base_locale\<close>: custom base locale for all autocorres locales
\<close>

text \<open>
Moreover there are some Isabelle options for more feedback / tracing:
\<^item> \<^verbatim>\<open>option verbose\<close> (default 0), higher value means more verbosity
\<^item> \<^verbatim>\<open>verbose_timing\<close> (default 0), higher value means more timing messages
\<^item> \<^verbatim>\<open>timing_threshold\<close> (default 3), threshold in milliseconds for timing messages
\<close>

(*<*)
end
(*>*)
