(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


chapter \<open>C-Translation Infrastructure \label{chap:CTranslationInfrastructure}\<close>

theory CTranslationInfrastructure
  imports
  CTranslation
begin

term guarded_spec_body
section \<open>Local Variables\<close>

text \<open>
Local variables in the SIMPL outcome of the C-Parser are represented in \<^typ>\<open>locals\<close>.
 The natural number in the domain encodes the canonical position
in the scope of the C-function: input arguments, then return variable, then local variables.
The byte list in the range of the function is the encoding of the value according to the
UMM (unified memory model) \<^class>\<open>c_type\<close>. The typing of variables is maintained as data in
@{ML_structure "CLocals"} and a typed view is achieved via \<^const>\<open>clookup\<close> and \<^const>\<open>cupdate\<close>.

In previous attempts local variables were represented first as a @{command record} and more 
recently as @{command statespace}. 
The representation as \<^typ>\<open>locals\<close> tries to combine the best of all previous approaches:
\<^item> Uniform (program independent) representation of local variables.
\<^item> Positional 'naming' enables a canonical parameter passing for function calls, 
  even if the names of parameters are unknown, as in the case of function-pointers.
\<^item> Lightweight "typing" via ML infrastructure instead of the 'fixes' of @{command statespace}. 
  Unfortunately, the more flexible @{command statespace} representation for local variables turned
  out to reveal some performance bottle neck in the locale infrastructure, which itself boils down to
  the resources consumed by the omnipresent instantiation of types and terms. 

\<close>

declare [[ML_print_depth = 1000]]

subsection \<open>Basic ML primitives\<close>

text \<open>
To define new variables the basic primitive is @{ML CLocals.define_locals} which takes a
scope (currently a two element list of qualifiers: program-name followed by function-name) and 
the list of local variable declarations (name, type and kind). 
Note that the order is relevant as it represents the canonical positional ordering.
\<close>

setup \<open>CLocals.define_locals ["prog", "myfun"] [
  ("x", @{typ \<open>32 word\<close>}, NameGeneration.Loc), 
  ("p", @{typ \<open>32 word ptr\<close>}, NameGeneration.Loc), 
  ("z", @{typ \<open>64 word\<close>}, NameGeneration.Loc)] \<close> 

ML \<open>CLocals.Data.get (Context.Proof @{context})\<close>

text \<open>
For each local variable a constant is defined with the position of the variable. The constant
name encodes the original name of the local variable. Whenever available we use this symbolic name
in favour of the plain literal number. However, at some places we use the plain numbers, in 
particular for parameter passing. There is some simplifier setup which we explain later that
allows to use either representation.

To enable syntax translations from short names to the symbolic constants together with their typing
one has to enter the correct scope, e.g.:
\<close>

local_setup \<open>
Local_Theory.declaration {pervasive=false, syntax=true, pos = \<^here>} (fn _ =>  
  CLocals.scope_map (K ["prog", "myfun"]))
\<close>

term prog.myfun.p_'
thm prog.myfun.p_'_def

text \<open>
Some remarks on the naming scheme for those symbolic constants. 
The qualifiers for both program-name and function-name are mandatory.
The name mangling with the suffix serves two purposes:
\<^item> Avoid name clashes with user input via variable names in the C sources (in particular 
  for the artificial return variable)
\<^item> Avoid name clashes for bound or free variables (or new constants) in HOL. Note that
  even a constant with mandatory qualifier e.g. \<open>foo.c\<close> would force the pretty printer to avoid
  a bound variable being named just as \<open>c\<close>. The pretty printer only takes 
  the @{ML Long_Name.base_name} into account.

The general suffix \<open>_'\<close> avoids clashes with C variable names as the prime is not
a legal character for C identifiers. Syntax translations will truncate this suffix.
The artificial return variable \<open>ret\<close> that the C-Parser introduces is internally \<open>ret'_'\<close> to
avoid a potential conflict with a local variable named \<open>ret\<close>.
\<close>

ML \<open>CLocals.Data.get (Context.Proof @{context})\<close>

subsection "Syntax"

text \<open>Plain lookup and update in locals.\<close>
term \<open>l \<cdot> p\<close>
ML_val \<open>\<^term>\<open>l \<cdot> p\<close>\<close>

term \<open>s\<langle>x := y\<rangle>\<close>
term \<open>s\<langle>x := y, p := k\<rangle>\<close>

ML_val \<open>\<^term>\<open>s\<langle>x := y\<rangle>\<close>\<close>
ML_val \<open>\<^term>\<open>s\<langle>x := y, p := k\<rangle>\<close>\<close>


text \<open>Lookup and update in a complete Simpl state, selecting the \<^const>\<open>locals\<close>\<close>

term \<open>s \<cdot>\<^sub>\<L> p\<close>
ML_val \<open>@{term \<open>s \<cdot>\<^sub>\<L> p\<close>}\<close>


term \<open>s\<langle>x :=\<^sub>\<L> y\<rangle>\<close>
term \<open>s\<langle>x :=\<^sub>\<L> y, p :=\<^sub>\<L> k\<rangle>\<close>


subsection "Simplifier setup"

text \<open>
The simplifier is setup to be able to deal with symbolic as well as literal numerals. Symbolic
ones are expanded on the fly employing the infrastructure form the code generator.
The trigger for this expansion is via a simplification procedure that. Conditional rules can be
configured via the attribute:
\<close>
ML \<open>@{attributes [code_simproc]}\<close>

text \<open>
The simplification procedure first checks wheter the precondition evaluates to true, via 
the code-generator. In case of success the simplifier is invoked to replay that proof and
trigger the rule. @{ML Code_Simproc.code_simp_prems}, @{ML Code_Simproc.code_prove}.

Note that the attribute also consumes an optional name to index the simprocs. This name is
taken from @{command named_theorems}.

The relevant setup of the rules can be found in \<^file>\<open>CLocals.thy\<close>.
\<close>

schematic_goal \<open>(clookup 2 (cupdate prog.myfun.z_' (\<lambda>_. 2::64 word) l)) = (?X::64 word)\<close>
  apply simp
  done

schematic_goal \<open>(clookup prog.myfun.z_' (cupdate prog.myfun.z_' (\<lambda>_. 2::64 word) l)) = (?X::64 word)\<close>
  apply simp
  done
schematic_goal "s\<langle>x := \<lambda>_. 2\<rangle> \<cdot> x = ?X"
  apply simp
  done

schematic_goal "s\<langle>x := \<lambda>_. 2\<rangle> \<cdot> p = ?X"
  apply simp
  done

install_C_file "ex.c"

thm size_td_simps
text \<open>The root locale storing the global content @{locale ex_global_addresses}. This is also
the locale ware the bodies of the imported functions are defined.\<close>

context ex_global_addresses
begin
text \<open>
The usage of global variables is analysed and three cases are distinguesed:
\<^item> static variables do not change there value. So they are defined as HOL constant with their
  initial value. In case no initialiser is given they are zero initialised.
\<^item> 'ordinary' global variables that are also updated somewhere in the code are stored in
  the record of global variables \<^typ>\<open>globals\<close>. They are accessed by the lookup and update function
  of the @{command record} package. 
\<^item> In case the address of a global variabe is taken somewhere in the code, we declare a
  global constant for a pointer to that variable. Lookup and update is then indirectly via the
  heap. Note that the pointer is only declared. There is no defining equation. Currently there
  are also no assumptions maintained about distinctness of global variable pointers. This is
  up to the user.
\<close>
thm global_const_defs
term g_static
term g_ordinary_' term g_ordinary_'_update
term g_addressed_'
thm main_body_def
thm globals.typing.get_upd
thm state.typing.get_upd
text \<open>
Functions also result in a declaration of a constant representing the global function pointer.
@{const ex.add}. They have the type @{typ "unit ptr"}.
\<close>
term ex.add

text \<open>When the code actually uses function pointers to perform indirect calls, some more
infrastructure is provided,  cf \<^file>\<open>../doc/fnptr.thy\<close>\<close>

text \<open>
When looking into the function bodies the symbolic names for the positional local variables
are displayed, fully qualified with program name as well as function name.
\<close>
thm add_body_def

text \<open>To have short names printed, one can either enter the scope of the function by activating
the corresponding \<open>variables\<close> bundle, or use the option to always display short names.\<close>
context includes add_variables
begin
thm add_body_def
end

declare [[clocals_short_names]]
thm  add_body_def
end

text \<open>The canonical locale to do verification of a procedure is the \<open>impl\<close> locale. This
activates the scope of the function and also stores the equation that the lookup of the
function pointer in the environment \<^const>\<open>\<Gamma>\<close> retrieves the expected body.\<close>

context add_impl
begin
thm add_body_def
thm add_impl

text \<open>
The symbolic names can be folded and unfolded by an attribute.
\<close>
thm add_body_def [unfold_locals]
thm add_body_def [unfold_locals, fold_locals]

text \<open>These attributes can also take qualifier in case an alternative scope should be added\<close>
thm call_add_body_def
thm call_add_body_def [unfold_locals] \<comment> \<open>nothing happens as we are in the wrong scope\<close>
thm call_add_body_def [unfold_locals call_add] \<comment> \<open>now they are expanded as we qualify the scope\<close>

end


context call_add_impl
begin
thm call_add_body_def
declare [[hoare_use_call_tr' = false]]
thm call_add_body_def
end

text \<open>All the implementations of the program are gathered in the \<open>simpl\<close> locale \<close>

context ex_simpl
begin
thm add_impl
thm call_add_impl
end

section "Infrastructure for states" 

type_synonym state = "(globals, locals, 32 signed word) CProof.state"

context add_impl
begin

text \<open>As a final part of the verification generator generator terms containing local and global
variables are generalised to a 'splitted' view, where each component becomes has a bound variable.\<close>


lemma "
  \<exists>s::state. s \<cdot>\<^sub>\<L> n = 3"
  apply (tactic \<open>HPInter.GENERALISE @{context} 1\<close>)
  by simp

lemma "
  \<exists>s::state. s \<cdot>\<^sub>\<L> n = 3"
  apply (tactic \<open>HPInter.GENERALISE @{context} 1\<close>)
  by simp

lemma "
  \<exists>s::state. s \<cdot>\<^sub>\<L> n = 3 \<and> s \<cdot>\<^sub>\<L> m = 3"
  apply (tactic \<open>HPInter.GENERALISE @{context} 1\<close>)
  by simp

lemma "
  \<exists>s::state. s \<cdot>\<^sub>\<L> n = 3 \<and> s \<cdot>\<^sub>\<L> m = 3 \<and> g_' (globals s) = 4 \<and> global_exn_var'_' s = Break"
  apply (tactic \<open>HPInter.GENERALISE @{context} 1\<close>)
  by simp



text \<open>Simpl syntax\<close>

ML \<open>
@{term \<open>\<lbrace>\<acute>n = x \<rbrace>\<close>}
\<close>
term \<open>\<lbrace>\<acute>n = x \<rbrace>\<close>
ML \<open>
@{term \<open>\<acute>n :== x \<close>}
\<close>
term \<open>\<acute>n :== x \<close>


term \<open>\<acute>n :== CALL add(x, y)\<close>
term \<open>\<acute>n :== CALL ex.add(x, y)\<close>
ML \<open>@{term \<open>\<acute>n :== CALL add(x, y)\<close>}\<close>


ML \<open>@{term \<open>\<acute>ret' :== PROC add(2, 3)\<close>}\<close> 

term \<open>\<acute>ret' :== PROC add(2, 3)\<close>

end

section \<open>Cached simproc examples\<close>

text \<open>Some more explanation on this is in \<^file>\<open>../doc/AutoCorresInfrastructure.thy\<close>\<close>


schematic_goal "TYPE(addr_bitsize word) \<le>\<^sub>\<tau> TYPE(unpacked_C[12]) "
  apply simp
  done


lemma "TYPE(8 word) \<le>\<^sub>\<tau> TYPE(array_C)"
  supply [[verbose=3]]
  apply simp
  done

lemma "TYPE(8 word) <\<^sub>\<tau> TYPE(array_C)"
  supply [[verbose=3]]
  apply simp
  done

lemma "TYPE(addr_bitsize word) \<le>\<^sub>\<tau> TYPE(matrix_C)"
  supply [[verbose=3]]
  apply simp
  done

lemma "TYPE(8 word) \<le>\<^sub>\<tau> TYPE(matrix_C)"
  apply simp
  done

ML \<open>
Cached_Theory_Simproc.trace_cache @{context}
\<close>

schematic_goal \<open>
field_names_no_padding (typ_info_t TYPE(outer_C)) (export_uinfo (typ_info_t TYPE(inner_C))) = ?XX\<close>
  supply [[simp_trace=true, verbose=5]]
  apply simp
  done
ML \<open>
Cached_Theory_Simproc.trace_cache @{context}
\<close>

schematic_goal \<open>
set (field_names_no_padding (typ_info_t TYPE(outer_C)) (export_uinfo (typ_info_t TYPE(inner_C)))) = ?XX\<close>
  supply [[simp_trace=true, verbose=5]]
  apply simp
  done
ML \<open>
Cached_Theory_Simproc.trace_cache @{context}
\<close>


lemma "export_uinfo (typ_info_t TYPE(unpacked_C)) = export_uinfo (typ_info_t (TYPE(32 word)))"
  supply [[simp_trace=true,verbose=3]]
  apply simp
  oops

lemma "typ_uinfo_t TYPE(unpacked_C) = export_uinfo (typ_info_t (TYPE(32 word)))"
  apply simp
  oops

lemma "typ_uinfo_t TYPE(32 signed word) = export_uinfo (typ_info_t (TYPE(32 word)))"
  supply [[simp_trace=true,verbose=3]]
  apply simp
  done


lemma "typ_uinfo_t TYPE(32 signed word[3]) = export_uinfo (typ_info_t (TYPE(32 word[3])))"
  supply [[simp_trace=true,verbose=3]]
  apply simp
  done

schematic_goal \<open>
set (field_names_no_padding (typ_info_t TYPE(unpacked_C)) (export_uinfo (typ_info_t TYPE(8 word)))) = ?XX\<close>
  supply [[simp_trace=true, verbose=3]]
  apply simp
  done

lemma "export_uinfo (typ_info_t TYPE(unpacked_C)) = export_uinfo (typ_info_t (TYPE(unpacked_C)))"
  supply [[simp_trace=true,verbose=3]]
  apply simp
  done

ML \<open>
Cached_Theory_Simproc.trace_cache @{context}
\<close>
lemma "TYPE (32 word) \<le>\<^sub>\<tau> TYPE(32 word[256])" 
  supply [[simp_trace=true,verbose=3]]
  apply simp
  done

lemma "TYPE (32 word) \<le>\<^sub>\<tau> TYPE(32 word[256])" 
  supply [[simp_trace=true,verbose=3]]
  apply simp
  done
ML \<open>
 Cached_Theory_Simproc.trace_cache @{context}
\<close>

schematic_goal "n < 12 \<Longrightarrow> field_lookup (typ_info_t TYPE(array_C)) [''elements_C'', replicate n CHR ''1'', ''chr_C''] 0 = ?X"
  supply [[simp_trace=true, simp_trace_depth_limit=1, verbose=5]]
  apply simp
  done

schematic_goal "n < 12 \<Longrightarrow> field_lookup (typ_uinfo_t TYPE(array_C)) [''elements_C'', replicate n CHR ''1'', ''chr_C''] 0 = ?X"
  supply [[simp_trace=true, simp_trace_depth_limit=1, verbose=5]]
  apply simp
  done

schematic_goal "n < 12 \<Longrightarrow> field_ti TYPE(array_C) [''elements_C'', replicate n CHR ''1'', ''chr_C''] = ?X"
  supply [[simp_trace=false, simp_trace_depth_limit=1, verbose=3]]
  apply simp
  done

schematic_goal "n < 12 \<Longrightarrow> field_ti TYPE(array_C) [''elements_C'', replicate n CHR ''1'', ''chr_C''] = ?X"
  supply [[simp_trace=false, simp_trace_depth_limit=1, verbose=3]]
  apply simp
  done

lemma "TYPE(unpacked_C[12]) \<le>\<^sub>\<tau> TYPE(array_C[2])"
  supply [[simp_trace=false, simp_trace_depth_limit=1, verbose=3]]
  apply simp
  done

lemma "\<not> TYPE(unpacked_C[12]) \<le>\<^sub>\<tau> TYPE(unpacked_C[24])"
  supply [[simp_trace=false, simp_trace_depth_limit=2, verbose=3]]
  apply simp
  done

lemma "TYPE(unpacked_C[12]) \<le>\<^sub>\<tau> TYPE(array_C)"
  apply simp
  done

lemma "typ_uinfo_t TYPE(unit ptr) \<noteq> typ_uinfo_t TYPE(32 word ptr)"
  apply simp
  done

text \<open>Matching of the interpreteted locale @{locale stack_heap_raw_state}\<close>

ML_val \<open>
  val cterm_match = With_Fresh_Stack_Ptr.cterm_match @{context}
  val {n=n1, init=init1, c=c1, instantiate=inst1, ...} = cterm_match @{cterm "state.With_Fresh_Stack_Ptr n i1 c1"}
  val {n=n2, init=init2, c=c2, instantiate=inst2, ...} = cterm_match @{cterm "state.With_Fresh_Stack_Ptr n i2 c2"}
  val t = inst1 {n=n2, init = init2, c= c2}
\<close>

ML_val \<open>
  val match = With_Fresh_Stack_Ptr.match @{context}
  val {n = n1, init=init1, c=c1, instantiate=inst1, ...} = match @{term "globals.With_Fresh_Stack_Ptr n i1 c1"}
  val {n = n2, init=init2, c=c2, instantiate=inst2, ...} = match @{term "globals.With_Fresh_Stack_Ptr n i2 c2"}
  val t = inst1 {n=n2, init = init2, c= c2}
\<close>


thm zero_simps
thm make_zero
thm size_simps
thm size_align_simps

thm h_val_fields
thm heap_update_fields
thm fg_cons_simps
thm fl_ti_simps
thm fl_Some_simps

end