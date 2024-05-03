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

(*
FIXME: what about a final-autocorres sanity check?
 We could take all the method_callers, determine which functions they might call
 (via type), And see if the choosen WA and TS abstraction actually match.
*)


install_C_file "fnptr.c"

autocorres [
  ts_force nondet = voidcaller,  
  ts_force_known_functions = option ] fnptr.c


text \<open>
Dealing with function pointers in AutoCorres has the following main challenges:
\<^item> Parameter passing
\<^item> Correspondence proofs
\<^item> Mutual recursion
\<close>

subsubsection \<open>Parameter passing\<close> 

text \<open>
In C a function pointer type does not have to specify the names of the function parameters.
Hence when translating a call to a function pointer from C into SIMPL we need a
uniform way to pass the function parameters. Recall that in SIMPL local variables are represented
as part of the state, there is no lambda binding at that stage. For ordinary function calls
we know the names of the parameters and can refer to them, for function pointers we do not know
the names. Our approach is to generally switch to uniform names for the parameters, 
encoding the position and the type like: \<open>in1_int\<close>, \<open>in2_unsigned\<close>.

The mapping to the original names in the C file is implemented as syntactic sugar in the locale.
As this mapping depends on the actual function we have to make sure to work in the correct 
context. The main interface to this mapping is defined in \<^file>\<open>../c-parser/HPInter.ML\<close> e.g.:

\<^item> @{ML "HPInter.all_locvars"}
\<^item> @{ML "HPInter.enter_scope"}

Note that the current implementation is a little bit fragile as it also depends on the
syntax translations for lookup and update in the underlying @{command statespace}.
\<close>

subsubsection \<open>Correspondence proofs\<close>

text \<open>
When we come along a function pointer call in a correspondence proof we need a correspondence
proof for the function pointer. Were to we get it from? In full generality we do not know
much about were the function pointer might be pointing to.
One drastic way out could be to add a guard at the call point, which guarantees that
there is such a proof. This makes the proof trivial, but the code gets polluted with
correspondence guards which also show up at the user level. So whenever one wants to proof
a property about the resulting function one has to deal with this guard.

To keep the user level proofs clean, we decided to take another approach, by restricting the programs we
can handle to some common use cases:
\<^item> Constant function pointer as parameter to a function. Here constant means that the parameter is not
  modified within the function body.
\<^item> Function pointer via constant global variable. Think of the global variable as a kind of dispatcher
  or class table, e.g. Array of structs representing "object descriptions" with
  function pointers as fields.
\<^item> C-style object method calls: Instead of a pure function pointer, a pointer to a structure
  which containes function pointers is passed as a parameter.

In the first case we can add the correspondence assumption to the locale of the function. In the
second case we can even resolve the correspondence proof as we can statically infer which functions might
be called via the global variable.
\<close>
subsubsection \<open>Mutual recursion\<close>

text \<open>
The general approach to resolve a function pointer call is via a lookup in a program environment 
which maps the pointer to the definition of the function. In SIMPL the function is 
defined by a piece of syntax, and the program environment is an explicit context @{term \<Gamma>} which
appears in the semantic rules for SIMPL. Moreover, for each function that might be called via
a function pointer we introduce a pointer to that function. These pointers, and the assumption
that all of them are distinct are put to the locale of global variables.
 
In each phase of Autocorres we introduce a similar program environment @{term \<open>\<P>\<close>} 
that maps the pointer to a monadic HOL function definition. As from phase L2 on the parameters 
of functions become lambda abstractions we introduce a distinct program environment for each 
function type. These program environments are introduced as locale parameters. 
Then we successively add the implementation equations of the 
form @{term "\<P> some_function_pointer = some_function"} as the functions are defined.

The correspondence theorems (or assumptions) for function pointer calls then relates the 
functions resolved via their respective environment, 
e.g. relate @{term \<open>the (\<Gamma> p)\<close>} with @{term \<open>\<P> p\<close>}.

We also support mutual recursion via global function pointers (case 2 above), e.g. a function
might call itself indirectly via a global function pointer variable. The global program analysis
takes this into account to determine the strongly connected components aka. (recursive) cliques.

This adds another twist to the approach with program environments just described. 
The assumption @{term "\<P> some_function_pointer = some_recursive_function_via_\<P>"} can only be added after the
function @{term some_recursive_function_via_\<P>} is defined, but the definition already depends on the
program environment. How do we cut the loop?

The core idea is to split the definition into two phases. 
First we define the @{command "fixed_point"}
by explicitly extending the program environment at each call. 
Instead of calling @{term "\<P> p"} directly we call
@{term "map_of_default \<P> [(some_function_pointer, some_recursive_function_via_\<P>)] p"}
where @{term some_recursive_function_via_\<P>} participates in the fixed point construction.
Once the function is defined, we create a new locale, extending the program environment
with the assumption @{term "\<P> some_function_pointer = some_recursive_function_via_\<P>"} and simplifying

@{term "map_of_default \<P> [(some_function_pointer, some_recursive_function_via_\<P>)] p = \<P> p"}

in the function body. After this extra step we again uniformly represent recursive and 
non-recursive function pointer calls with @{term \<open>\<P> p\<close>}.
\<close>

subsection \<open>Global locales\<close>

text \<open>The global locales fix the program environments (mapping function pointers to definitions) 
for a phase. These locales are created in the initialisation phase of @{command autocorres} before the
individual functions are processed.

The fundamental locale is storing the addresses of global variables, including function
pointers and some basic properties about them.
\<close>


context fnptr_global_addresses
begin
text \<open>
For each function pointer a constant is declared 
e.g. @{term "fnptr.odd_disp"}, @{term "fnptr.add"}.
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

thm fun_ptr_simps
end

text \<open>Note that the program environment @{term \<P>} for l1 programs is only declared as constant
 (without a definition).
This environment is 'populated' in derived locales as the definitions of function become available.
\<close>

text \<open>A program environment for each distinct function pointer type is introduced for each further
phase.
e.g. @{term \<P>_l2_unsigned___unsigned}, @{term \<P>_l2_int___int}\<close>


context fnptr_global_addresses
begin
text \<open>For example if the function pointer would index into the dispatcher array @{const dispatcher_u} and
select a @{const binop_u_C}, it would result into subgoals for each of the possible pointers, namely
and @{const fnptr.add_u} @{const fnptr.add_gu}.\<close>
term dispatcher_u


text \<open>In this bundle we define some introduction rules to support the correspondence proofs.
In phase L1 and L2 the correspondence proof is quite explicitly done in ML and the rules for
function pointer calls are explicitly instantiated in ML.
Here in layer HL the proof is done by applying intro rules and synthesising the abstract
version of the program. The following rules relate the abstract and concrete program
environments that are used for function pointer calls.
\<close>
context includes fnptr_hl_impl_corres
begin
 thm fun_ptr_intros
end

text \<open>
Note for example, that in the current goal state the concrete program would be of the 
shape \<^term>\<open>\<P>_l2____int p\<close> whereas the abstract program would be a plain schematic variable. 
This variable is then instantiated with \<^term>\<open>\<P>_hl____int p\<close>.
Once the rule is applied the identity marker \<^const>\<open>DYN_CALL\<close> triggers the
sidecondition splitter / solver: @{ML AutoCorresUtil.dyn_call_split_simp_sidecondition_tac}, which
splits the generic correspondence of some generic function pointer to its possible values.
\<close>


text \<open>For example if the function pointer would index into the dispatcher array @{const dispatcher_u} and
select a @{const binop_u_C}, it would result into subgoals for each of the possible pointers, namely
@{const fnptr.add_u} and @{const fnptr.add_gu}.
\<close>


context includes fnptr_wa_impl_corres
begin
text \<open>Like in phase HL we also have some custom intro rules to support the instantiation of
function pointer calls.\<close>
thm fun_ptr_intros
thm global_const_defs
thm fun_ptr_simps
end


text \<open>The TS phase adds another dimension to the program environments, the monad type.
E.g. \<^const>\<open>\<P>_pure_unsigned___unsigned\<close>, \<^const>\<open>\<P>_gets_unsigned___unsigned\<close>, 
 \<^const>\<open>\<P>_option_unsigned___unsigned\<close>, \<^const>\<open>\<P>_nondet_unsigned___unsigned\<close>, \<^const>\<open>\<P>_exit_unsigned___unsigned\<close>.
\<close>

context includes fnptr_ts_impl_corres
begin
text \<open>Again we have custom intro rules to support instantiation of the abstract program environment.\<close>
thm fun_ptr_intros
thm global_const_defs
thm fun_ptr_simps
end
end

subsection \<open>Function / Recursive-clique specific locales\<close>

subsubsection \<open>L1\<close>

context l1_definition_add \<comment>\<open>holds the definition of the function\<close>
begin
thm l1_def \<comment>\<open>all relevant l1 definitions\<close>
thm ac_def \<comment>\<open>definitions of all layers\<close>

text \<open>Note that there are two variants of the definition of @{const l1_add'}. First the
original definition and then an optimised version, already removing some 
exception handling. Here are the names of the theorems:\<close>
thm l1_add'_def
thm l1_opt_add'_def
end

context l1_impl_add 
begin

text \<open>As @{const l1_add'} might also be called indirectly via a function pointer, we populate
the program environment with the definition\<close>
thm l1_add'_impl \<comment>\<open>Mapping of the function-pointer to the definition in the corresponding environment.\<close>

text \<open>The equation is also added to @{thm fun_ptr_simps}.\<close>
thm fun_ptr_simps
thm l1_def
end

context l1_definition_call_binop
begin
text \<open>\<^const>\<open>l1_call_binop'\<close> makes a function pointer call via the \<^const>\<open>dispatcher\<close> array selecting
field \<^const>\<open>binop_C\<close>. So it might call \<^const>\<open>l1_add'\<close>, \<^const>\<open>l1_minus'\<close> or \<^const>\<open>l1_mul'\<close>. 
The definitions of these functions are also imported into the locale (cf. @{thm l1_def}), 
as well as the corresponding entries in the program environment (cf. @{thm fun_ptr_simps}).
Also note that the function pointer call is wrapped in a \<^const>\<open>L1_guarded\<close>. In 
particular the guard ensures that the index into the array is in range. It is essential
to have this information available in the correspondence proof to split the function pointer
call to its potential targets.
\<close>
thm l1_call_binop'_def
thm global_const_defs
thm l1_def
thm fun_ptr_simps
end

context l1_corres_call_binop
begin
text \<open>The correspondence proofs are performed within the corres locales. The results are
added to @{thm l1_corres}. Note that the correspondence proofs of the potential callees are
present. @{command autocorres} resolves call dependencies and 
first performs the correspondence proofs of the potential callees.\<close>
thm l1_call_binop'_corres
thm l1_corres
thm l1_def
end

context l1_definition_parameter_call
begin
text \<open>This function performs a function pointer call on a function parameter. Recall that
we only support the case were the function pointer parameter value stays the same within the function.
The phase L1 is special, as we postpone the correspondence proof of the function pointer call
to the L2 layer. The reason is that in the L2 layer we replace the parameters with lambda
abstraction and thus the fact that the value does not change becomes trivial. In L1 we would
have to propagate this information trough every state update, from the invocation of the function
to the function pointer call. This proof is anyway performed in the L2 phase.
Postponing the correspondence proof is achieved by just assuming the correspondence in \<^const>\<open>L1_guarded\<close>.
\<close>
thm l1_parameter_call'_def
thm l1_def
end

context l1_corres_parameter_call
begin
thm l1_parameter_call'_corres
thm l1_corres
end

subsubsection \<open>L2\<close>

context l2_definition_add
begin
thm fun_ptr_simps
end

context l2_impl_add
begin
thm fun_ptr_simps
end

context l2_definition_call_binop
begin
thm fun_ptr_simps
thm l2_call_binop'_def
thm l2_def
end

context l2_corres_call_binop
begin
thm l2_call_binop'_corres
thm l2_corres
thm l2_def
end

context l2_definition_parameter_call
begin
text \<open>Note that in contrast to L1 we do not have any correspondence assumption in \<^const>\<open>L2_guarded\<close>.
The function pointer parameter is just inserted in the function pointer call and thus is immediately
the same value.
\<close>
thm l2_parameter_call'_def
thm l2_def
end

context l2_corres_parameter_call
begin
text \<open>In contrast to the function pointer call via a global variable, where we statically
resolve which functions are potentially called, we add an explicit assumption on the 
parameter to the correspondence theorem. As in phase L2 we also have to proof the postponed
L1 correspondence we actually have both assumptions here.\<close>
thm l2_parameter_call'_corres
thm l2_corres
thm l2_def
end

text \<open>When defining (mutual) recursion indirectly via function pointers, there is a 
subtlety in the definition of the functions.
In order to have an admissible \<^const>\<open>L2corres\<close> property the program environment
for the current clique is temporarily explicitly 
exended via \<^const>\<open>map_of_default\<close> in the function bodies.
After definition of the function and extending the hypothetical program environment with
the new definitions this construction is hidden again.

Compare the variation of @{thm l2_def} in \<^locale>\<open>l2_corres_odd_disp_even_disp\<close> vs.
\<^locale>\<open>l2_impl_odd_disp_even_disp\<close> and the extended program 
environment in @{thm fun_ptr_simps}.

Also recall the general flow of how to arrive at a new level with definition and correspondence proof.
\<^item> First the induction step of the correspondence proof is performed, assuming that the recursive
  calls are in the correspondence relation. 
\<^item> If that proof is successful the function body or bodies are used to do the actual definition(s) of the
  function(s).
\<^item> After the definition is done the actual correspondence proof is performed using the induction step
  as major ingredient, replacing the body / bodies with the new definition(s).
\<^item> The program environments are extended with the assumptions that the pointers are mapped to the
  new definitions and the right hand sides of the definitions are simplified.
\<close>
context l2_corres_odd_disp_even_disp
begin
thm fun_ptr_simps
thm l2_corres
thm l2_def
thm l2_odd_disp'_def \<comment>\<open>Foundational definition of @{command fixed_point}. FIXME: should we conceale this?\<close>
thm l2_odd_disp'.simps
end

context l2_impl_odd_disp_even_disp
begin
thm fun_ptr_simps
thm l2_corres
thm l2_def
thm l2_odd_disp'.simps
thm l2_impl_odd_disp'_def \<comment>\<open>canonical variant. FIXME: should we rename this (simps?)?\<close>
end

subsubsection \<open>HL\<close>

context hl_definition_call_binop
begin
thm fun_ptr_simps
thm hl_call_binop'_def
thm hl_def
end

context hl_corres_call_binop
begin
thm hl_call_binop'_corres
thm hl_corres
thm hl_def
end

context hl_definition_parameter_call
begin
thm hl_parameter_call'_def
thm hl_def
end

context hl_corres_parameter_call
begin
thm hl_parameter_call'_corres
thm hl_corres
thm hl_def
end

subsubsection \<open>WA\<close>

context wa_definition_call_binop
begin
thm fun_ptr_simps
thm wa_call_binop'_def
thm wa_def
end

context wa_corres_call_binop
begin
thm wa_call_binop'_corres
thm wa_corres
thm wa_def
end

context wa_definition_parameter_call
begin
thm wa_parameter_call'_def
thm wa_def
end

context wa_corres_parameter_call
begin
thm wa_parameter_call'_corres
thm wa_corres
thm wa_def
end

subsubsection \<open>TS\<close>

context ts_impl_add
begin
text \<open>\<^const>\<open>add'\<close> is defined within the option monad. Note that (lifted version) also end
up in the more expressive program environments (cf. @{thm fun_ptr_simps}). So function pointer
calls to this function can be performed in any of those monads.\<close>
thm add'_def
thm fun_ptr_simps
thm ts_def
end

context ts_definition_call_binop
begin
thm fun_ptr_simps
thm call_binop'_def
thm ts_def
end

context ts_corres_call_binop
begin
thm call_binop'_corres
thm ts_corres
thm ts_def
end

context ts_definition_fac
begin
thm fun_ptr_simps
thm fac'.simps
thm ts_def
end

context ts_corres_fac
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

context ts_definition_parameter_call
begin
thm parameter_call'_def
thm wa_def
end

context ts_corres_parameter_call
begin
thm parameter_call'_corres
thm wa_corres
thm wa_def
end

context ts_impl_call_binop
begin
thm ts_def
end


subsubsection \<open>Final AutoCorres\<close>

text \<open>Once all phases are passed and the correspondence proofs between the consecutive layers are
ready they are combined to the final correspondence layer, from SIMPL upto TS.\<close>
context corres_parameter_call
begin
thm parameter_call'_ac_corres
end

context corres_call_binop
begin
thm call_binop'_ac_corres
end

context corres_odd_disp_even_disp
begin
thm odd_disp'_ac_corres
thm even_disp'_ac_corres
end

text \<open>When all functions of a C file are translated the following summary locales are introduced.\<close>


context fnptr_all_impl \<comment>\<open>All implementation locales of phase TS\<close>
begin
thm fun_ptr_simps
thm even_disp'.simps
thm impl_even_disp'_def (* fixme: naming? *)
thm ac_def
end

context fnptr_all_corres \<comment>\<open>All corres locales of all phases\<close>
begin
thm l1_corres
thm l2_corres
thm hl_corres
thm wa_corres
thm ts_corres
thm ac_corres

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
thm fun_ptr_intros
thm fun_ptr_distinct
thm fun_ptr_subtree
end

subsubsection \<open>Method calls of C-style objects\<close>

text \<open>
The goal is to also support function pointer invocations via C-style object methods: 
Instead of a plain function pointer a function gets a  pointer to a structure (object) that
contains function pointers as structure fields. This adds an important twist to the refinement
proofs of autocorres. When we invoke a method via \<^verbatim>\<open>p->method(...)\<close> we actually calculate the
function pointer from the heap object referenced by pointer \<^verbatim>\<open>p\<close>. As with the cases described before 
at that point we have to argue that the referenced function fulfills the 'corres' predicate. 
However, now we have the indirection via the heap. So somehow we have to keep track of the
function pointers stored in the heap. As other pointer objects might also be stored and manipulated 
in the heap this typically requires user-level reasoning about the heap layout and disjointness
of certain pointers. As autocorres is mainly used as a preprocessing tool for arbitrary C programs 
we want to avoid making too restrictive assumptions here. Instead we postpone the argument to
the user. The core idea is that we want to argue that the actually referenced function is a 
'known function' for which we know or can assume that the 'corres' predicate holds. We introduce
a predicate \<^const>\<open>known_function\<close> into our locale hierarchy, which takes a function pointer
\<^term>\<open>p::unit ptr\<close> and tells us if this is a known function for which we can assume 'corres'. 
On every invocation of a object method we introduce a guard \<^term>\<open>known_function (p\<rightarrow>method)\<close> into
the code. Autocorres can then utilise this guard together with the assumption that the
correspondence holds for all known functions. It is then left as an exercise for the user to
discharge the guards. This boils down to an invariant argument that every time you 
assign something to \<^term>\<open>p\<rightarrow>method\<close> it has to be a \<^const>\<open>known_function\<close>.
To support this, everytime a function is defined which might be such a function pointer, we
utilise the implementation locales to store the information that this is a \<^const>\<open>known_function\<close>.
\<close>

text \<open>Here are the locales about the \<^const>\<open>known_function\<close> which state correspondence. These
are imported as parents in all individual corres locales.\<close>

context fnptr_l1_corres
begin
thm known_function_corres
end

context fnptr_l2_corres
begin
thm known_function_corres
end

context fnptr_hl_corres
begin
thm known_function_corres
end

text \<open>The locales for phases WA and TS are special as they might change the signature of
the resulting function depending on the called functions. We make assumptions about
called methods to derive the definition of the calling function. E.g. for phase WA we
have to know whether a called method will do signed or unsigned word abstractions. For phase TS
we have to know in which monad the called methods are defined in order to select the right
monad for the caller.
We can use the autocorres options \<^verbatim>\<open>ts_force_known_functions\<close>, \<^verbatim>\<open>unsigned_word_abs_known_functions\<close> and
 \<^verbatim>\<open>no_signed_word_abs_known_functions\<close> analogous to the corresponding options 
for individual functions.

In our example program we have chosen the option monad as a result monad. Note that
autocorres does some sanity checks to ensure that e.g. the chosen monad is expressible enough, but
ultimately it is the responsibility of the user to ensure that the monad and the word abstraction
options match all potential instances of the methods.
\<close>

context fnptr_wa_corres
begin
thm known_function_corres
end

context fnptr_ts_corres
begin
thm known_function_corres
end

context ts_definition_call_object_binop_return
begin
thm ts_def
end

context ts_definition_call_object_binop_assign
begin
thm ts_def
end

context ts_definition_call_object_binop_emb
begin
thm ts_def
end

text \<open>Here you can see all known functions that autocorres has detected. Note that for this
analysis autocorres assumes that it has total knowledge of the complete program. It collects
all functions for which addresses are calculated in the program and considers them as
 \<^const>\<open>known_function\<close>.
\<close>
context fnptr_all_impl
begin
thm known_function
end



end

