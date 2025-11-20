(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Function Pointers"

theory fnptr
imports AutoCorres
begin

declare [[c_parser_feedback_level=0, ML_print_depth=1000]]
install_C_file "fnptr.c"


autocorres [no_body = g unop binop binop_u,
  ts_force nondet = voidcaller,  
  ts_force_known_functions = nondet] fnptr.c


text \<open>
Dealing with function pointers in AutoCorres has the following main challenges:
\<^item> Parameter passing
\<^item> Correspondence proofs
\<^item> Mutual recursion
\<close>

thm \<P>_defs
thm final_defs
context fnptr_global_addresses 
begin
thm l1_corres
thm ac_corres
thm fun_ptr_simps
thm fun_ptr_map_of_default_eqs
thm \<P>_defs
thm final_defs
thm monad_mono_intros
thm mono_bind [rotated]
end
subsubsection \<open>Parameter passing\<close> 

text \<open>
In C a function pointer type does not have to specify the names of the function parameters.
Hence when translating a call to a function pointer from C into SIMPL we need a
uniform way to pass the function parameters. Recall that in SIMPL local variables are represented
as part of the state, there is no lambda binding at that stage. For ordinary function calls
we know the names of the parameters and can refer to them, for function pointers we do not know
the names. Our approach is to generally switch to uniform names for the parameters, 
encoding the position and the type like: \<open>in1_int\<close>, \<open>in2_unsigned\<close>.

The mapping to the original names in the C file is implemented as syntactic sugar in the context.
As this mapping depends on the actual function we have to make sure to work in the correct 
context. The main interface to this mapping is defined in \<^file>\<open>../c-parser/HPInter.ML\<close> e.g.:

\<^item> @{ML "HPInter.all_locvars"}
\<^item> @{ML "HPInter.enter_scope"}

Note that the current implementation is a little bit fragile as it also depends on the
syntax translations for lookup and update in the underlying @{command statespace}.
\<close>

subsubsection \<open>Correspondence proofs\<close>

text \<open>
A function pointer call boils down to an indirection. Instead of calling the function directly by
its name we go via the function pointer and have to resolve the name from that pointer, e.g. by
an environment mapping pointers to functions.

When we come along a function pointer call in a correspondence proof we need a correspondence
proof for the function pointer. Were do we get it from? In full generality we do not know
much about were the function pointer might be pointing to.
One drastic way out could be to add a guard at the call point, which guarantees that
there is such a proof. This makes the proof trivial, but the code gets polluted with
correspondence guards which also show up at the user level. So whenever one wants to proof
a property about the resulting function one has to deal with this guard.


To keep the user level proofs clean, we first decided to use assumptions on the function
pointer environment (mapping function pointers to functions) and doing the correspondence proofs
under those assumptions. The assumptions were managed in locales. While this \<^emph>\<open>open world\<close> approach was appealing
because of its modular and abstract take on function pointers it showed various shortcomings
in practice:
\<^item> Performance of locales was bad due to a complex locale hierarchy with lots of assumptions
  and lemmas.
\<^item> Complexity of the code managing the various use cases we supported:
  \<^item> Constant function pointer as parameter to a function. Here constant means that the parameter is not
    modified within the function body.
  \<^item> Function pointer via constant global variable. Think of the global variable as a kind of dispatcher
    or class table, e.g. Array of structs representing "object descriptions" with
    function pointers as fields.
  \<^item> C-style object method calls: Instead of a pure function pointer, a pointer to a structure
    which containes function pointers is passed as a parameter.

After that experience we decided to go a for a \<^emph>\<open>closed world\<close> approach: The complete C-program
has to be known a priory. The C-Parser and autocorres make this assumption in other places as well.
For function pointers this means that at each function pointer call we can statically determine the
functions that might be called. So the function pointer call becomes a case distinction. This
reduces complexity and the number of locales and we do not have to distinguish the various 
use-cases of function pointers for the correspondence proofs. 
The C-Parser tries to infer the relevant functions at each function pointer call. When it does
 not succeed the user can manually add an attribute to the C code enumerating the potential callees.

\<close>
subsubsection \<open>Mutual recursion\<close>

text \<open>
The general approach to resolve a function pointer call is via a lookup in a program environment 
which maps the pointer to the definition of the function. In SIMPL the function is 
defined by a piece of syntax, and the program environment is an explicit context @{term \<Gamma>} which
appears in the semantic rules for SIMPL. Moreover, for each function that might be called via
a function pointer we introduce a pointer to that function. These pointers, and the assumption
that all of them are distinct are put to the locale of global variables.
 
In the final phase of Autocorres we introduce similar program environments @{term \<open>\<P>\<close>} 
that map the pointers to monadic HOL functions definitions. The main use of those environments
is put into equations of the form @{term "\<P> some_function_pointer = some_function"}. These
are collected in @{thm fun_ptr_simps}.

The function pointer environments themselves are defined by means of @{const map_of_default}.
More details on the construction of these environments comes below.

As from phase L2 on the parameters
of functions become lambda abstractions we introduce distinct program environment for each 
function type.

We also support mutual recursion via function pointers (case 2 above), e.g. a function
might call itself indirectly via a some function pointer variables. As all callees are statically
determined the global program analysis
takes this into account to determine the strongly connected components aka. (recursive) cliques.

\<close>

subsection \<open>Global locale: \<open>..._global_addresses\<close>\<close>

text \<open>The global locale fixes a function pointer for each function and assumes distincness of
those pointers. This locale is created during the initialisation phase of the C-Parser @{command install_C_file} 
before the individual functions are processed.

The fundamental locale is storing the addresses of global variables, including function
pointers and some basic properties about them.
\<close>


context fnptr_global_addresses
begin
text \<open>
For each function pointer a constant is declared 
e.g. @{const "fnptr.odd_disp"}, @{const "fnptr.add"}.
Note that these constants have to be qualified by the program name. 
In case there would be a conflict with Isabelle internal names, e.g. a function ending with \<open>__\<close> 
the name is suffixed with @{ML Hoare.proc_deco}, cf. @{ML NameGeneration.fun_ptr_name}.
\<close>
ML \<open>Hoare.proc_deco\<close>

text \<open>
Moreover the global variables and their defining equations, i.e. initialisation expressions
are collected in @{thm global_const_defs}.\<close>
thm global_const_defs
thm global_const_array_selectors \<comment> \<open>more efficient access to array components\<close>
thm global_const_non_array_selectors
thm global_const_selectors

text \<open>To express distinctness of function pointers we make use of the infrastructure
in \<^file>\<open>$ISABELLE_HOME/src/HOL/Statespace/DistinctTreeProver.thy\<close>, which is also the
foundation for @{command statespace}. A tree data structure is used to efficiently derive
distinctness and subset properties.
\<close>

thm fun_ptr_distinct
thm fun_ptr_subtree

text \<open>For every function pointer the locale assumes that they are not NULL,
i.e.  @{const c_fnptr_guard}. Based on the distinctness of the function pointers
we derive some simplification rules for @{const map_of_default}.\<close>
thm fun_ptr_guards
thm fun_ptr_simps
end

text \<open>Let us see the evolution of a function pointer call during the various autocorres phase. The
example is function \<open>call_binop\<close>, which calls function pointers via a global dispatcher 
array \<open>dispatcher\<close>.
The C-Parser has inferred that via this array the actual potential callees are \<open>add\<close>, \<open>mul\<close> or \<open>minus\<close>.
This set of potential function pointers is annotated in a SIMPL exception value: 
@{term "UndefinedFunction {fnptr.add, fnptr.mul, fnptr.minus}"} within the 'dynamic' function call:
@{const dynCall_exn}. From this annotation autocorres derives the function pointer environments.
\<close>
thm call_binop_body_def

text \<open>In phase L1 this results in: 
@{term "map_of_default (\<lambda>_. \<top>)
         [(fnptr.add, l1_add'), 
          (fnptr.mul, l1_mul'),
          (fnptr.minus, l1_minus')]"}.\<close>

thm l1_call_binop'_def

text \<open>In phases L1, L2, IO, and HL the @{const map_of_default} is unfolded to a nested 
@{const L2_condition}.\<close>
thm l2_call_binop'_def
thm hl_call_binop'_def

text \<open>In phase TS the nested conditions are folded into an @{const map_of_default} again.\<close>
thm ts.call_binop'_def

text \<open>Finally after all functions are processed by autocorres we pick the
@{const map_of_default}s from all the functions, define the environments @{const \<P>} and insert those
in the final definitions of the functions.\<close>
thm call_binop'_def
thm dispatcher.binop.\<P>_def

text \<open>All the environements definitions are collected in @{thm \<P>_defs} and all final functions in 
@{thm final_defs}\<close>
thm \<P>_defs
thm final_defs

text \<open>The environments are defined as qualified constants, with the base name @{const \<P>} and the
qualifier indicating some kind of canonical access path. For example in function @{const call_binop'} the
environment is @{const dispatcher.binop.\<P>}, where qualifier \<open>dispatcher\<close> comes from the global array 
and qualifier \<open>binop\<close> form the selected structure field. The general format of the qualifiers is:

  \<^verbatim>\<open>[function-name.]variable-name[.selector-name]*\<close>
 
The selectors are structure field selectors, intermediate array indices are omitted. The function-name
is introduced function pointers selected via local function parameters or variables, or in case
the access to a global variable has to be disambiguated.
\<close>

text \<open>Note that all definitions of the functions as well as the environments are on theory level.
We do not need any locale parameters or assumptions for the definitions.
However, do derive the equations for accessing the function pointer environments we have to take
disjointness of the function pointers into account. This disjointness assumption is in
@{locale fnptr_global_addresses}.
\<close>
context fnptr_global_addresses
begin

text \<open>Collection @{thm fun_ptr_simps} for positive equations for function pointers that are 
actually in the environment.\<close>
thm fun_ptr_simps

text \<open>Collection @{thm fun_ptr_undefined_simps} for negative equations for function pointers that are 
not in the environment.\<close>
thm fun_ptr_undefined_simps

text \<open>These lemmas are derived from the more basic collections on @{const map_of_default}\<close>
thm fun_ptr_map_of_default_eqs
thm fun_ptr_map_of_default_fallthrough_eqs

end


subsection \<open>Function / Recursive-clique specific locales\<close>

subsubsection \<open>L1\<close>


thm l1_def \<comment>\<open>all relevant l1 definitions\<close>
thm ac_def \<comment>\<open>definitions of all layers\<close>

text \<open>Note that there are two variants of the definition of @{const l1_add'}. First the
original definition and then an optimised version, already removing some 
exception handling. Here are the names of the theorems:\<close>
thm l1_add'_def
thm l1_opt_add'_def


context fnptr_global_addresses
begin
text \<open>\<^const>\<open>l1_call_binop'\<close> makes a function pointer call via the \<^const>\<open>dispatcher\<close> array selecting
field \<^const>\<open>binop_C\<close>. So it might call \<^const>\<open>l1_add'\<close>, \<^const>\<open>l1_minus'\<close> or \<^const>\<open>l1_mul'\<close>. 

Also note that the function pointer call is wrapped in a \<^const>\<open>L1_guarded\<close>. In 
particular the guard ensures that the index into the array is in range.
\<close>
thm l1_call_binop'_def
thm global_const_defs
thm l1_def


text \<open>The correspondence proofs are performed within the corres locale @{locale fnptr_global_addresses}. 
The results are
added to @{thm l1_corres}. Note that the correspondence proofs of the potential callees are
present. @{command autocorres} resolves call dependencies and 
first performs the correspondence proofs of the potential callees.\<close>
thm l1_call_binop'_corres
thm l1_corres
thm l1_def
end


text \<open>This function performs a function pointer call on a function parameter.
\<close>
thm l1_parameter_call'_def
thm l1_def


context fnptr_global_addresses
begin
thm l1_parameter_call'_corres
thm l1_corres
end

subsubsection \<open>L2\<close>



thm fun_ptr_simps
thm l2_call_binop'_def
thm l2_def


context fnptr_global_addresses
begin
thm l2_call_binop'_corres
thm l2_corres
thm l2_def
end

thm l2_parameter_call'_def
thm l2_def


context fnptr_global_addresses
begin

thm l2_parameter_call'_corres
thm l2_corres
thm l2_def
end

text \<open>When defining (mutual) recursion indirectly via function pointers this is handled
as any other (mutual) recursion.

Recall the general flow of how to arrive at a new level with definition and correspondence proof.
\<^item> First the induction step of the correspondence proof is performed, assuming that the recursive
  calls are in the correspondence relation. 
\<^item> If that proof is successful the function body or bodies are used to do the actual definition(s) of the
  function(s).
\<^item> After the definition is done the actual correspondence proof is performed using the induction step
  as major ingredient, replacing the body / bodies with the new definition(s).
\<close>

context fnptr_global_addresses
begin
thm fun_ptr_simps
thm l2_corres
thm l2_def
thm l2_odd_disp'_def \<comment>\<open>Foundational definition of @{command fixed_point}. FIXME: should we conceale this?\<close>
thm l2_odd_disp'.simps
end


context fnptr_global_addresses
begin
thm fun_ptr_simps
thm l2_corres
thm l2_def
thm l2_odd_disp'.simps
(* thm l2_impl_odd_disp'_def *) \<comment>\<open>canonical variant. FIXME: should we rename this (simps?)?\<close>
end

subsubsection \<open>HL\<close>


thm fun_ptr_simps
thm hl_call_binop'_def
thm hl_def


context fnptr_global_addresses
begin
thm hl_call_binop'_corres
thm hl_corres
thm hl_def
end

thm hl_parameter_call'_def
thm hl_def

context fnptr_global_addresses
begin
thm hl_parameter_call'_corres
thm hl_corres
thm hl_def
end

subsubsection \<open>WA\<close>


thm fun_ptr_simps
thm wa_call_binop'_def
thm wa_def


context fnptr_global_addresses
begin
thm wa_call_binop'_corres
thm wa_corres
thm wa_def
end


thm wa_parameter_call'_def
thm wa_def


context fnptr_global_addresses
begin
thm wa_parameter_call'_corres
thm wa_corres
thm wa_def
end

subsubsection \<open>TS\<close>


text \<open>\<^const>\<open>add'\<close> is defined within the option monad. Note that (lifted version) also end
up in the more expressive program environments (cf. @{thm fun_ptr_simps}). So function pointer
calls to this function can be performed in any of those monads.\<close>
thm add'_def
thm fun_ptr_simps
thm ts_def



thm fun_ptr_simps
thm call_binop'_def
thm ts_def



context fnptr_global_addresses
begin
thm call_binop'_corres
thm ts_corres
thm ts_def
end


thm fun_ptr_simps
thm fac'.simps
thm ts_def


context fnptr_global_addresses
begin
thm fac'_corres
thm ts_corres
thm ts_def
end


text \<open>Recall that in case of a function pointer call via a parameter we assume correspondence
of the parameter. So in which monad should we end up? Which monad should we assume for the
parameter? Currently we assume the same monad as for the function. We consecutively try the
correspondence from the most restrictive to the most expressive monad and we end up in the monad
with the first successful proof. If you want a different (more expressive) monad you can
configure this via the autocorres option \<open>ts_force\<close>.\<close>


thm parameter_call'_def
thm wa_def


context fnptr_global_addresses
begin
thm parameter_call'_corres
thm wa_corres
thm wa_def
end


thm ts_def



subsubsection \<open>Final AutoCorres\<close>

text \<open>Once all phases are passed and the correspondence proofs between the consecutive layers are
ready they are combined to the final correspondence layer, from SIMPL upto TS. The program 
environments @{const \<P>} are defined and inserted into the functions.\<close>
context fnptr_global_addresses
begin
thm parameter_call'_ac_corres
end

context fnptr_global_addresses
begin
thm call_binop'_ac_corres
end

context fnptr_global_addresses
begin
thm odd_disp'_ac_corres
thm even_disp'_ac_corres
end

text \<open>When all functions of a C file are translated the following summary locales are introduced.\<close>

context fnptr_global_addresses \<comment>\<open>All implementation locales of phase TS\<close>
begin
thm fun_ptr_simps
thm even_disp'.simps
(* thm impl_even_disp'_def *) (* fixme: naming? *)
thm ac_def
end

context fnptr_global_addresses \<comment>\<open>All corres locales of all phases\<close>
begin
thm l1_corres
thm l2_corres
thm hl_corres
thm wa_corres
thm ts_corres
thm ac_corres
thm final_defs
thm \<P>_defs

thm l1_def
thm l2_def
thm l2_even_disp'_def (* fixme: make this concealed? *)
thm l2_even_disp'.simps
thm hl_def
thm wa_def
thm ts_def
thm ac_def

thm global_const_defs
thm fun_ptr_simps
thm fun_ptr_distinct
thm fun_ptr_subtree
end


end

