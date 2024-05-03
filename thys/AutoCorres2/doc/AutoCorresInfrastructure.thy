(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter \<open>Overview of AutoCorres \label{chap:AutoCorresInfrastructure}\<close>

theory AutoCorresInfrastructure
imports AutoCorres
begin



text \<open>
This theory elaborates on some of the (internal) AutoCorres infrastructure and is also supposed to
act as a testbench for this infrastructure, e.g. simplifier setup.

Following the Isabelle tradition user relevant changes to AutoCorres are described in
the file \<^file>\<open>../NEWS\<close>.
\<close>

section \<open>Building Blocks\<close>

text \<open>'AutoCorres' has the following major building blocks and contributions.

\<^item> The 'C-parser' (by Michael Norrish) takes C-Input files and parses them to 'SIMPL' (by Norbert Schirmer) programs within Isabelle/HOL: 
    \<^item> C-parser: \autoref{chap:strictc}
    \<^item> SIMPL: @{url \<open>https://www-wjp.cs.uni-saarland.de/leute/private_homepages/nschirmer/pub/schirmer_phd.pdf\<close>}
\<^item> The unified memory model (UMM) (by Harvey Tuch) models C-types as HOL-types with conversions between
  the typed view and the raw-byte-level view. Moreover it provides a separation logic framework.
    \<^item> UMM: @{url \<open>https://trustworthy.systems/publications/papers/Tuch%3Aphd.pdf\<close>}
\<^item> AutoCorres (by David Greenaway): @{url \<open>https://trustworthy.systems/publications/nicta_full_text/8758.pdf\<close>}
\<close>
text\<open>
Some historic remarks, that might give some insight why things are as they are.
The motivation for AutoCorres was the C-verification tasks coming from the sel4 Projects 
@{url \<open>https://sel4.systems\<close>}, a verified microkernel, written in C.

The project started with high level HOL-specifications, refining them to monadic functions (within
HOL and Haskell) and then refining them to C-code. The nondetermistic state-monad 
goes back to Cook. et al \<^url>\<open>http://www.cse.unsw.edu.au/~kleing/papers/Cock_KS_08.pdf\<close>. 
To link the C-code with the monadic functions
within Isabelle / HOL the C-parser was written. The C-parser produces SIMPL programs, and 
SIMPL is equipped with various semantics (big and small-step) and a Hoare-logic framework including 
a verification condition generator.
The correspondence of the C-functions represented in SIMPL and the monadic functions was manually 
expressed within this framework.

AutoCorres was then built after (or in parallel) to this verification effort in order to speed
up the process for future projects.

While the main concepts described in the publications above are still valid, a lot
of things have evolved and were extended. Especially the implementation details have
changed. In this document we also give some notes on these differences. Also see
 \<^file>\<open>../NEWS\<close>.
\<close>

section \<open>C Parser\<close>

text \<open>
Some remarks on the C-Parser
\<^item> Lexical and syntactical analysis is implemented using ML-Lex / ML-Yacc coming from the MLton project
  \<^url>\<open>http://mlton.org/\<close>. Originally mlton was used to generate the ML files from the grammers. 
  Meanwhile this is all integrated into Isabelle/ML.
\<^item> The C parser first generates an ML-data structure representing the program. It then does some
  transformations on that data structure (e.g. storing results of nested function calls into temporary
  variables), before translating it to SIMPL. In roughly the following steps:
  \<^enum> Generating HOL-types for the C-types. 
     \<^item> The C parser performs a complete program analysis to determine the types used.
     \<^item> Defines the types and performs the UMM proofs, in particular conversions and properties to and 
       from raw byte lists.
  \<^enum> Defining the state-space type: global variables, local variables, heap variables. The C parser
    does a complete program analysis to determine how global and heap variables are used to decide whether
    to model them as part of the globals-record or the heap. When no 'address-of' a variable is
    calculated it is stored as part of the global variable record, otherwise it is stored within
    the heap. Global variables are more abstract to deal with compared to heap variables.
  \<^enum> Defining the SIMPL procedures
  \<^enum> Proving 'modifies' specifications for the procedures, i.e. frame conditions on global variables.
\<close>

section \<open>AutoCorres\<close>

text \<open>AutoCorres abstracts the SIMPL program to a monadic HOL function in various phases, producing
correspondence (a.k.a. simulation, a.k.a. refinement) theorems along the way. Note that the translation 
(and the correspondence theorems) might only be partial in the following sense: A phase might
introduce additional guards into the code. Simulation only holds for programs that do not fail 
on the abstract execution. Note that non-termination is currently also modelled as failure. So
simulation only holds for terminating abstract programs:
  \<^item> Correspondence relation: @{const ac_corres}

Each phase is processed in similar stages:
\<^item> Raw translation and refinement-proof
\<^item> Optimisation of the output program, sometimes distinguished between a more lightweight 
  "peephole" optimisation and a more heavyweight "flow" optimisation
\<^item> Define a constant for the output of the translation for that phase.

The phases are:
\<^item> From SIMPL (deep embedding of statements, shallow embedding of expressions) to L1 (shallow 
  embedding of statements and expressions). The transformation preserves the state-space representation,
  and merely focuses on translating SIMPL statements to monadic functions:
  \<^item> Definition of L1: \<^file>\<open>../L1Defs.thy\<close>
  \<^item> Correspondence relation: @{const L1corres} 
  \<^item> Peephole optimisation:  \<^file>\<open>../L1Peephole.thy\<close>
  \<^item> Flow optimisation: \<^file>\<open>../ExceptionRewrite.thy\<close>
  \<^item> Main ML file:  \<^file>\<open>../simpl_conv.ML\<close>
\<^item> Local variable abstraction, from L1 to L2. In L2, local variables are represented as lambda
  abstractions. So the underlying state-space type changes, getting rid of the local variable record.
  As local variables are now treated as lambda abstractions, and thus names become meaningless, 
  autocorres keeps the original names around as part of (logically redundant) name annotations within 
  the L2 constants, e.g. @{term "L2_gets (\<lambda>_. x) [c_source_name_hint]"}. Lists of names are
  used, as variables might pile up in tuples. These annotations are removed in the final
  polishing phase of autocorres, attempting to rename the bound variables accordingly on the fly.
  \<^item> Definition of L2: \<^file>\<open>../L2Defs.thy\<close>
  \<^item> Correspondence relation: @{const L2corres} 
  \<^item> Exception rewriting, introducing nested exceptions: \<^file>\<open>../L2ExceptionRewrite.thy\<close>
  \<^item> Peephole optimisation:  \<^file>\<open>../L2Peephole.thy\<close>
  \<^item> Main ML files:  \<^file>\<open>../local_var_extract.ML\<close>, \<^file>\<open>../l2_opt.ML\<close>
  From now on we stay in the language L2, and also the optimisation stages are reused.
\<^item> In/Out parameter abstraction (IO). Pointer parameters are replaced by passing value parameters.
  This step may eliminate pointers to local variables.
  \<^item> Theory: \<^file>\<open>../In_Out_Parameters.thy\<close>
  \<^item> Correspondence relation: @{const IOcorres}
  \<^item> Documentation: \<^file>\<open>In_Out_Parameters_Ex.thy\<close>
\<^item> Heap abstraction, referred to as heap-lifting (HL). 
  The monolithic-byte-oriented heap is abstracted to a typed-split-heap model. For
  that the new type \<open>lifted_globals\<close> is introduced. Note, that the separation logic of Tuch also
  attempts to give a typed view on top of the byte-level-heap. In case of nested structure types
  it even is capable to express the various levels of typed-heap views from bytes to individual structure fields
  to (nested) structures. AutoCorres takes a simpler, more pragmatic approach here and only
  provides a single split-heap abstraction on the level of complete types. This means there
  is a heap for every compound type and for every primitive type but not for nested 
  structures. However, autocorres allows to
  mix between the abstractions layers (split-heap vs. byte-heap) on the granularity of functions.
  So you can model low-level functions like memory-allocators on the untyped byte-heap and then still
  use these functions within other functions in the split-heap abstraction.
  Meanwhile, genuine support for a split-heap approach with addressable nested structures was added. It is
  described in \<^file>\<open>open_struct.thy\<close>. 
  \<^item> Main theory:  \<^file>\<open>../HeapLift.thy\<close>
  \<^item> Correspondence relation: @{const L2Tcorres}
  \<^item> Main ML files:  \<^file>\<open>../heap_lift_base.ML\<close>, \<^file>\<open>../heap_lift.ML\<close>
\<^item> Word abstraction (WA): (un)signed n-bit words are converted to @{typ int} or @{typ nat}. This
  conversion only affects local variable (lambda abstraction), so the underlying state-space type
  is maintained. When reading and storing to memory the values are converted accordingly. 
  \<^item> Main theory:  \<^file>\<open>../WordAbstract.thy\<close> 
  \<^item> Correspondence relation: @{const corresTA}
  \<^item> Main ML file:  \<^file>\<open>../word_abstract.ML\<close>
\<^item> Type strengthening (TS), sometimes also referred to as type lifting or type specialisation: 
  Best effort approach to simplify the structure of the monad as far as possible:
  \<^item> Pure functions
  \<^item> Reader monad, read-only state-dependant functions.
  \<^item> Option (reader) monad, in particular for potential non-terminating functions (recursion / while). 
    Nontermination is treated as failure in autocorres and failure of guards are 
    represented as a result of @{term None}
  \<^item> Nondeterministic state monad (exceptional control flow confined within function boundaries). 
    Failure (of guards) and nontermination are represented by @{const Failure} as outcome.
  \<^item> Nondeterministic state monad with exit (exceptional control flow crossing function boundaries).
  New monad types can be registered within Isabelle / ML.
  \<^item> Main theories:  \<^file>\<open>../TypeStrengthen.thy\<close>, \<^file>\<open>../Refines_Spec.thy\<close>
  \<^item> Correspondence relation: @{const refines}. Originally this was actually 
    based on equality. As we now implement (mutually) recursive functions by a CCPO
    @{command fixed_point} instead of introducing an explicit measure parameter we changed to
    simulation. Equality is not @{const ccpo.admissible}, whereas simulation is.
  \<^item> Main ML files:  \<^file>\<open>../type_strengthen.ML\<close>,  \<^file>\<open>../monad_types.ML\<close>,  \<^file>\<open>../monad_convert.ML\<close>
\<^item> Polish. Performed as a part of type strengthening. Here remaining special and limited L2 definitions are
  expanded to 'ordinary' monadic functions. Also annotations of original c variable names are removed
  and bound variables are named accordingly.
\<close>


section \<open>AutoCorres Flow\<close>

text \<open>
The original AutoCorres implementation of David Greenaway was refined in several ways. In particular
from a high level perspective the concepts of incremental build and parallel processing where
unified:
\<^item> Parallel processing is moved to the outermost invocation of autocorres. All tasks 
  are calculated respecting the dependencies of the call graph and the various autocorres phases, cf.
  @{ML AutoCorres.parallel_autocorres}.
\<^item> Every task then invokes a distinct call to @{ML AutoCorres.do_autocorres} exactly specifying 
  the scope (which function clique) and which phase via the options. 
\<^item> The results of an invocation are maintained in generic data, such that they are available to 
  subsequent dependent calls.

The common parts of each phase are implemented in @{ML_structure AutoCorresUtil}. 
The last phase, Type strengthening (TS), historically played a special role and still does not
make much use of @{ML_structure AutoCorresUtil}, but conceptually it follows the same idea:

Functions are processed in a sequence of cliques, from the bottom of the call graph to the top. 
Here a clique is either a single function or a group of strongly connected recursive calls. 
After processing of a phase the clique might get splitted due to dead code elimination. This
general idea is implemented in @{ML AutoCorresUtil.convert_and_define_cliques}.
\<close>

subsection \<open>General Remarks\<close>

text \<open>
\<^item> The main autocorres files, putting everything together:
  \<^file>\<open>../AutoCorres.thy\<close>, \<^file>\<open>../autocorres.ML\<close>
\<^item> There are two main approaches in a single phase to come up with an abstract program (output
  of the phase) and the correspondence proof to the concrete program (input of the phase):
  \<^item> Implicit synthesis of the abstract program from the concrete program by applying "intro" rules, 
  where the abstract program is initialised with a schematic variable. Prototypical examples are
  the heap abstraction, word abstraction and type strengthening.
  \<^item> First explicitly calculate the abstract program (fragment) within ML from the 
  concrete program (fragment), and then perform the correspondence proof. An prototypical
  example is the local variable abstraction.
\<^item> The common aspects of the various stages within a single phase is (partially) generalised into
  library functions: \<^file>\<open>../autocorres_util.ML\<close>

\<close>

subsection \<open>Links to more documentation / examples\<close>
text \<open>
\<^item> Pointers to local variables: \<^file>\<open>pointers_to_locals.thy\<close>
\<^item> In-Out parameters: \<^file>\<open>In_Out_Parameters_Ex.thy\<close>
\<^item> Addressable fields and open types: \<^file>\<open>open_struct.thy\<close>
\<^item> Function pointers:  \<^file>\<open>fnptr.thy\<close>
\<^item> Unions: \<^file>\<open>union_ac.thy\<close>
\<close>

section \<open>Overview on the Locales\<close>

text \<open>The representation of local variables in SIMPL and L1 where changed from records
to 'Statespaces' as implemented by @{command statespace} and finally to
positional variables as in \<^typ>\<open>locals\<close> in  \<^file>\<open>../c-parser/CLocals.thy\<close>.
 This allows for an uniform representation of local variables as a function from 
'nat to byte list', Typing is achieved by ML data organised in locales and bundles,
cf.  \<^file>\<open>../c-parser/CTranslationInfrastructure.thy\<close>. 
These are also used to do the L1 and the L2 correspondence proofs. Starting from
L2 on the local variables are represented as lambda bindings.

We describe the various locales (and bundles) later on with our running examples.

To support function pointers even more locales where introduced. See \<^file>\<open>fnptr.thy\<close>.
\<close>



section \<open>Example Program\<close>

install_C_file "autocorres_infrastructure_ex.c"
print_theorems
thm upd_lift_simps
thm fl_ti_simps

text \<open>The variables consist of parameters (input and output) and the local variables. Note that 
this is merely a ML-declaration of the scope which can be accesses via a bundle,
cf.  \<^file>\<open>../c-parser/CTranslationInfrastructure.thy\<close>.
\<close>
context includes add_variables
begin
term "\<acute>n :== 42"
end

text \<open>Adresses of global variables or function pointers are kept in the \<open>global_addresses\<close> locale.\<close>
print_locale autocorres_infrastructure_ex_global_addresses

text \<open>This is everything necessary to define the body of a function. All bodies 
are defined in that locale.\<close>
context autocorres_infrastructure_ex_global_addresses
  opening add_variables
begin
term add_body
thm add_body_def
end

text \<open>The implementation locale holds the defining equation of the function in SIMPL and is closed
under callees. \<close>

context call_add_impl
begin
thm add_impl
thm call_add_impl
end

text \<open>In case of a clique there is a clique locale and aliases for each function.\<close>
print_locale even_odd_impl
print_locale even_impl
print_locale odd_impl

text \<open>The locale importing all implementations is named like the file with suffix \<open>_simpl\<close>.\<close>

print_locale "autocorres_infrastructure_ex_simpl"

subsection \<open>Incremental Build\<close>

autocorres [phase=L1, scope=add] "autocorres_infrastructure_ex.c"
autocorres [phase=L2, scope=add] "autocorres_infrastructure_ex.c"
autocorres [phase=HL, scope=add] "autocorres_infrastructure_ex.c"
autocorres [phase=WA, scope=add] "autocorres_infrastructure_ex.c"
autocorres [phase=TS, scope=add] "autocorres_infrastructure_ex.c"

subsection \<open>All the rest\<close>

autocorres "autocorres_infrastructure_ex.c"

context unsigned_to_signed_impl
begin
thm unsigned_to_signed_body_def
end
context autocorres_infrastructure_ex_all_corres 
begin
thm unsigned_to_signed'_def
text \<open>The SIMPL versions produced by c-parser\<close>

declare [[clocals_short_names]]
thm max_body_def
thm add_body_def
term "add_body::((globals, locals, 32 signed word) CProof.state, unit ptr, strictc_errortype) com"
thm call_add_body_def
thm seq_assign_body_def
thm call_seq_assign_body_def
thm inc_g_body_def
thm deref_body_def
thm deref_g_body_def
thm factorial_body_def
thm call_factorial_body_def
thm odd_body_def
thm even_body_def
thm dead_f_body_def
thm dead_h_body_def
thm dead_g_body_def

text \<open>L1 versions. Monadic with same state. 
Note that recursive procedures are defined with the @{command fixed_point} package and hence
the \<open>.simps\<close> instead of \<open>_def\<close> makes more sense to look at.
In this layer a first exception elimination optimisation takes places. The optimized definition
has the extension "opt".
\<close>

declare [[show_types=false]]
thm l1_max'_def
thm l1_opt_max'_def

term "l1_add'::(unit, unit, (globals, locals, 32 signed word) CProof.state) exn_monad"
thm l1_add'_def
thm l1_opt_add'_def

thm l1_call_add'_def
thm l1_opt_call_add'_def

thm l1_seq_assign'_def
thm l1_opt_seq_assign'_def

thm l1_call_seq_assign'_def
thm l1_opt_call_seq_assign'_def

thm l1_inc_g'_def
thm l1_opt_inc_g'_def

thm l1_deref'_def
thm l1_opt_deref'_def

thm l1_deref_g'_def
thm l1_opt_deref_g'_def

thm l1_factorial'.simps
thm l1_opt_factorial'_def

thm l1_call_factorial'_def
thm l1_opt_call_factorial'_def

thm l1_odd'.simps
thm l1_opt_odd'_def

thm l1_even'.simps
thm l1_opt_even'_def

thm l1_dead_f'.simps
thm l1_opt_dead_f'_def

thm l1_dead_h'.simps
thm l1_opt_dead_h'_def

thm l1_dead_g'.simps
thm l1_opt_dead_g'_def


text \<open>L2 version: lambda bindings for local variables\<close>

thm l2_max'_def
term "l2_add'::32 signed word \<Rightarrow> 32 signed word
      \<Rightarrow> (32 signed word c_exntype, 32 signed word, globals) exn_monad"
thm l2_add'_def
thm l2_call_add'_def
thm l2_seq_assign'_def
thm l2_call_seq_assign'_def
thm l2_inc_g'_def
thm l2_deref'_def
thm l2_deref_g'_def
thm l2_factorial'.simps
thm l2_call_factorial'_def
thm l2_odd'.simps
thm l2_even'.simps
thm l2_dead_f'.simps
thm l2_dead_h'.simps
thm l2_dead_g'_def \<comment>\<open>Note that @{term l2_dead_g'} is no longer part of the clique, because of dead code elimination.\<close>


text \<open>Heap abstraction. Note that the change in the heap component of the global variables. The
type changes to @{typ lifted_globals} instead of @{typ globals}.\<close>

print_record globals \<comment> \<open>contains byte level tagged heap: @{term "t_hrs_'"}\<close>
print_record lifted_globals \<comment> \<open>contains split heap with single component @{term heap_w32}, 
                                as we only have a pointers to unsigend.\<close>

thm hl_max'_def
term "hl_add':: 32 signed word \<Rightarrow> 32 signed word 
      \<Rightarrow> (32 signed word c_exntype, 32 signed word, lifted_globals) exn_monad"
thm hl_add'_def
thm hl_call_add'_def
thm hl_seq_assign'_def
thm hl_call_seq_assign'_def
thm hl_inc_g'_def
thm hl_deref'_def
thm hl_deref_g'_def
thm hl_factorial'.simps
thm hl_call_factorial'_def
thm hl_odd'.simps
thm hl_even'.simps
thm hl_dead_f'.simps
thm hl_dead_h'.simps
thm hl_dead_g'_def 


text \<open>Word abstraction.\<close>
thm wa_max'_def
term "wa_add'::int \<Rightarrow> int \<Rightarrow> (32 signed word c_exntype, int, lifted_globals) exn_monad"
thm wa_add'_def
thm wa_call_add'_def
thm wa_seq_assign'_def
thm wa_call_seq_assign'_def
thm wa_inc_g'_def
thm wa_deref'_def
thm wa_deref_g'_def
thm wa_factorial'.simps
thm wa_call_factorial'_def
thm wa_odd'.simps
thm wa_even'.simps
thm wa_dead_f'.simps
thm wa_dead_h'.simps
thm wa_dead_g'_def 


text \<open>Final definition.\<close>
term "max'::int \<Rightarrow> int \<Rightarrow> int"
thm max'_def
term "add':: int \<Rightarrow> int \<Rightarrow> lifted_globals \<Rightarrow> int option"
thm add'_def
thm wa_call_add'_def
thm wa_seq_assign'_def
thm wa_call_seq_assign'_def
thm wa_inc_g'_def
thm wa_deref'_def
thm wa_deref_g'_def
thm wa_factorial'.simps
thm wa_call_factorial'_def
thm wa_odd'.simps
thm wa_even'.simps
thm wa_dead_f'.simps
thm wa_dead_h'.simps
thm wa_dead_g'_def 
text \<open>Correspondence theorem.\<close>
thm factorial'_ac_corres
thm call_factorial'_ac_corres

end

section \<open>Simplification strategy and dealing with tuples in L2-optimization phases\<close>

text \<open>Consider a congruence rule from AutoCorres\<close>

lemma
  assumes c_eq: "\<And>r s. c r s = c' r s" 
  assumes bdy_eq: "\<And>r s. c' r s \<Longrightarrow> run (A r) s = run (A' r) s" 
  shows "L2_while c A = L2_while c' A'"
  using c_eq bdy_eq
  by (rule L2_while_cong)

text \<open>
Note that \<^term>\<open>r\<close> could be a tuple and and we would like to "split" it. The condition \<^term>\<open>c\<close> will 
already be formulated with \<^const>\<open>case_prod\<close>, e.g. \<^term>\<open>\<lambda>(x,y,z) s. x < y\<close>. 

When the congruence rule above is applied, variable \<^pattern>\<open>?c'\<close> has to be instantiated at some point.
First the congruence rule is applied as is. Then we use @{thm [source] split_paired_all} to split up the 
\<^term>\<open>r\<close>. For the example we will end up with the subgoal:

 \<^pattern>\<open>\<And>a b c s. (a < b) = ?c' (a, b, c) s\<close>

Mere Unification will fail here as it does not work "modulo" \<^const>\<open>case_prod\<close>. To find the proper 
instantiation we developed @{ML Tuple_Tools.tuple_inst_tac} which can be added to the simplifier as
a looper. It will instantiate \<^pattern>\<open>?c'\<close> with the respective \<^const>\<open>case_prod\<close> instance 
introducing a new schematic variable: \<^pattern>\<open>?c' = (\<lambda>(a, b, c). ?f a b c)\<close>. Now the unification 
will kick in and do the rest of the work.

However, allthough an instantiation is now found, it does not have the expected effect 
on \<^verbatim>\<open>body_eq\<close>. The problem is, that the premise of the implication is not simplified as it is added
to the "prems" of the simplifier so it will be \<^term>\<open>(\<lambda>(a, b, c) s. a < b) (a, b, c) s \<equiv> True\<close> and not
just \<^term>\<open>a < b \<equiv> True\<close>". The former format is unfortunately ineffective in the simplification of
the while body.

Fortunately the simpset can be instructed to apply a function to the premise before it is added.
So adding @{ML Tuple_Tools.mksimps} with @{ML Simplifier.set_mksimps} helps with that respect. As 
the simplifier descends into the term it calls the function to do "beta-reduction" of 
tuple application before adding the premise.

\<close>

lemma "L2_while (\<lambda>(x,y,z) s. 0 < (y::nat)) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. 0 < y)) (\<lambda>_. X)) x ns 
       = 
       L2_while (\<lambda>(x,y,z) s. 0 < y) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. True)) (\<lambda>_. X)) x ns"
 apply (tactic \<open>
simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimps @{thms split_paired_all}
           |> Simplifier.add_cong @{thm L2_seq_guard_cong}
           |> Simplifier.add_cong @{thm L2_while_cong}
           |> Simplifier.set_mksimps (Tuple_Tools.mksimps)
) 1\<close>)
  done

text \<open>
Unfortunately there is still an issue. Linear arithmetic is applied as a simproc by the simplifier,
e.g.
@{lemma "0 < (n::nat) \<Longrightarrow> Suc 0 \<le> n" by simp}

Unfortunately this does not work as expected in the setup above:
\<close>

unbundle clocals_string_embedding

lemma "L2_while (\<lambda>(x,y,z) s. 0 < (y::nat)) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) (\<lambda>_. X)) x ns 
       = 
       L2_while (\<lambda>(x,y,z) s. 0 < y) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. z = a)) (\<lambda>_. X)) x ns"
apply (tactic \<open>
simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimps @{thms split_paired_all}
           |> Simplifier.add_cong @{thm L2_seq_guard_cong}
           |> Simplifier.add_cong @{thm L2_while_cong}
           |> Simplifier.set_mksimps (Tuple_Tools.mksimps)
) 1\<close>)
  oops

  text \<open>After some investigation in the interplay between the simplifier and the linear arithmetic 
simproc it seems that the linear arithmetic somehow ignores the transformed theorem that 
@{ML Tuple_Tools.mksimps} yields. Without understanding all the details I guess the reason is
the missmatch between the term in the hyps and the prop of the resulting theorem. As the simplifier
adds descends into an implication \<^prop>\<open>P \<Longrightarrow> Q\<close> it generates a theorem from \<^prop>\<open>P\<close>, by also adding 
P to the hyps, so we have \<open>P [P]\<close> as a theorem. When @{ML Tuple_Tools.mksimps} kicks in it only 
simplifies the prop not the hyps. So we end up with 
   \<open>a < b \<equiv> True [(\<lambda>(a, b, c) s. a < b) (a, b, c) s \<equiv> True]\<close> 
instead of 
   \<open>a < b \<equiv> True [a < b \<equiv> True]\<close>.
This seems to irritate the linear arithmetic.
One solution could be to also simplify the hyps. We did not explore this path, as I would expect
some issues when the hyps are eventually discharged. Nevertheless there could be a solution 
following that path.

We came up with a different solution. We get rid of the dependency of @{ML Tuple_Tools.mksimps} by
using \<^prop>\<open>P =simp=> Q\<close> to trigger simplification of P.
\<close>

text \<open>Note the various options to trace the simplification process.\<close>
declare [[linarith_trace=false]]
declare [[simp_trace=false, simp_trace_depth_limit=100]]
declare [[simp_debug=false]]
declare [[show_hyps=false]]

lemma  
  assumes c_eq: "\<And>r s. c r s = c' r s" 
  assumes bdy_eq: "\<And>r s. c' r s =simp=> run (A r) s = run (A' r) s"  
  shows "L2_while c A = L2_while c' A' "
  using c_eq bdy_eq by (rule L2_while_simp_cong)

lemma "L2_while (\<lambda>(x,y,z) s. 0 < (y::nat)) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) (\<lambda>_. X)) x ns 
       = 
       L2_while (\<lambda>(x,y,z) s. 0 < y) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. z = a)) (\<lambda>_. X)) x ns"
apply (tactic \<open>
simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimps @{thms split_paired_all}
           |> Simplifier.add_cong @{thm L2_seq_guard_cong}
           |> Simplifier.add_cong @{thm L2_while_simp_cong}
) 1\<close>)
  done

text \<open>The more standard congruence rule also works fine.\<close>
lemma  
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "\<And>r s. c' r s =simp=> run (A r) s = run (A' r) s"  
  shows "L2_while c A = L2_while c' A'"
  using c_eq bdy_eq by (rule L2_while_simp_cong')



lemma "L2_while (\<lambda>(x,y,z) s. 0 < (y::nat)) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) (\<lambda>_. X)) x ns 
       = 
       L2_while (\<lambda>(x,y,z) s. 0 < y) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. z = a)) (\<lambda>_. X)) x ns"
apply (tactic \<open>
simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimps @{thms split_paired_all}
           |> Simplifier.add_cong @{thm L2_seq_guard_cong}
           |> Simplifier.add_cong @{thm L2_while_simp_cong'}
) 1\<close>)
  done

text \<open>To avoid repeated splitting (and diving into the subterms) of tuples with 
@{thm split_paired_all} consider the follwing simproc setup.
\<close>

lemma "L2_while (\<lambda>(x,y,z) s. 0 < (y::nat)) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) (\<lambda>_. X)) x ns 
       = 
       L2_while (\<lambda>(x,y,z) s. 0 < y) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. z = a)) (\<lambda>_. X)) x ns"
apply (tactic \<open>
simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimprocs [Tuple_Tools.split_tupled_all_simproc, Tuple_Tools.tuple_case_simproc]
           delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}
           |> Simplifier.add_cong @{thm L2_seq_guard_cong}
           |> Simplifier.add_cong @{thm L2_while_simp_cong'}
) 1\<close>)
  done

text \<open>This is also the setup of @{ML L2Opt.cleanup_ss}\<close>
lemma "L2_while (\<lambda>(x,y,z) s. 0 < (y::nat)) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) (\<lambda>_. X)) x ns 
       = 
       L2_while (\<lambda>(x,y,z) s. 0 < y) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. z = a)) (\<lambda>_. X)) x ns"
apply (tactic \<open>
  asm_full_simp_tac (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) 1\<close>)
 done


lemma "L2_while (\<lambda>(x, y, z) s. y = 0)
     (\<lambda>(x, y, z).
         L2_seq (L2_gets (\<lambda>s. y) [\<S> ''ret'']) (\<lambda>r. XXX21 r x))
     names =
    L2_while (\<lambda>(x, y, z) s. y = 0) (\<lambda>(x, y, z). L2_seq (L2_gets (\<lambda>s. 0) [\<S> ''ret'']) (\<lambda>r. XXX21 r x)) names"
apply (tactic \<open>
  asm_full_simp_tac (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) 1\<close>)
  done


lemma "PROP SPLIT (\<And>r. ((\<lambda>(x,y,z). y < z \<and> z=s) r) \<Longrightarrow> P r)
 \<equiv> (\<And>x y z. y < z \<and> z = s \<Longrightarrow> P (x, y, s))"
  apply (tactic \<open>
asm_full_simp_tac (put_simpset HOL_basic_ss @{context} 
 addsimprocs [Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc] |> Simplifier.add_cong @{thm SPLIT_cong}) 1
\<close>)
  done
 
experiment
begin

schematic_goal foo:
"\<And>x1 x2 x3 s. (case (x1, x2, x3) of (x, y, z) \<Rightarrow> \<lambda>s. 0 < y) s \<Longrightarrow> 
 (case (x1, x2, x3) of (x, y, z) \<Rightarrow> L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) X) = ?A' (x1, x2, x3) s"
  apply (tactic \<open>
asm_full_simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimprocs [Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc]
           delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}

) 1\<close>)
  done
text \<open>\<^pattern>\<open>?A'\<close> should be properly instantiated.\<close>
thm foo

end

declare [[simp_trace=true, simp_trace_depth_limit=100]]
lemma "L2_while (\<lambda>(x,y,z) s. 0 < (y::nat)) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) X) x ns
       = 
       L2_while (\<lambda>(x,y,z) s. 0 < y) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. z = a)) X) x ns"
apply (tactic \<open>
asm_full_simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimprocs [Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc]
           delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}
           |> Simplifier.add_cong @{thm L2_seq_guard_cong}
           |> Simplifier.add_cong @{thm L2_while_cong_simp_split}
           |> Simplifier.add_cong @{thm SPLIT_cong}
) 1\<close>)
  done

text \<open>Finally the following setup implements a very controlled tuple esplitting on
the While body.\<close>

lemma 
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "PROP SPLIT (\<And>r s. c' r s \<Longrightarrow> run (A r) s = run (A' r) s)"  
  shows "L2_while c A = L2_while c' A'"
  using c_eq bdy_eq by (rule L2_while_cong_split)

text \<open>With @{const SPLIT} we mark a position in the term that will trigger 
@{ML Tuple_Tools.SPLIT_simproc}. By adding @{thm SPLIT_cong} as congruence rule we
prohibit the simplifier from diving into the loop body before we actually split the
result variable. Note that the simplifier usually works bottom up, only congruence rules
are applied top down.
\<close>

lemma "L2_while (\<lambda>(x,y,(z::nat)) s. 0 < (y::nat) \<and> y=x) (\<lambda>(x,y,z). L2_seq (L2_guard (\<lambda>_. Suc 0 \<le> y \<and> z = a)) X) x ns
       = 
  L2_while (\<lambda>(x, y, z) s. 0 < y \<and> y = x) (\<lambda>(x, x, z). L2_seq (L2_guard (\<lambda>_. z = a)) X) x ns"
apply (tactic \<open>
asm_full_simp_tac ( @{context} 
           addloop ("tuple_inst_tac", Tuple_Tools.tuple_inst_tac)
           addsimprocs [Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc]
           delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}
           |> Simplifier.add_cong @{thm L2_seq_guard_cong}
           |> Simplifier.add_cong @{thm L2_while_cong_simp_split}
           |> Simplifier.add_cong @{thm SPLIT_cong}
) 1\<close>)
  done


section \<open>Simplification of conditions (guards, loops, conditionals)\<close>

text \<open>
The basic peephole optimization for conditions tries to simplify "trivial" guards / conditions by
propagating the information of guards / conditions to subsequent guards / conditions. It is
called "peephole" optimisation (in contrast to "flow"-sensitive), because it only propagates the
state independent information of gaurds, i.e. constraints on constant expressions or local variables, 
not constraints on the state itself.

To facilitate this propagation with congruence rules and simprocs, 
we introduce two special constants \<^const>\<open>L2_seq_gets\<close> and \<^const>\<open>L2_seq_guard\<close> that are introduced
as intermediate step by a conversion. With this marking we can distinguish the cases by congruence
rules, without the marking both cases would be subject to a single congruence rule for \<^const>\<open>L2_seq\<close>. 
(Note that the simplifier only considers the head term of a congruence rules.)

We add the congruence rules @{thm L2_marked_seq_gets_cong} and @{thm L2_marked_seq_guard_cong}.
The congruence rules for the guard is a standard congruence rules that adds the gaurd as a precondition for
simplifying the second statement in the sequential composition. The congruence rule for 
@{thm L2_marked_seq_gets_cong} stops the simplifier from descending into the second term
of the sequential composition. Instead the simproc @{ML L2Opt.l2_marked_gets_bind_simproc} is 
triggered to analyse the situation.
It does the following:

\<^item> If the returned value in the first statement is simple, only occurs once in second statement, or
is a structure-constructor or update that is only appied to structure-selections then the value is
directly propagated to the second statement and the sequential composition is removed.
\<^item> It peeks into the prems of the simplifier to see if there are already "interesting" facts collected
from the congruence rules of guards / conditions. If not, it unfolds the marking and continues with
the ordinary sequential composition by simplifying the second statement. "Interesting" means there
is at least one premise that has impact on the new return value. E.g. if we have \<^term>\<open>x + y < 5\<close> in the
prems, and we now we return \<^term>\<open>x + y\<close>, than the simproc introduces a new variable \<^term>\<open>r\<close> for return value,
augments the context with the equation \<^term>\<open>r = x + y\<close> and derives the new premise \<^term>\<open>r < 5\<close> which
is put to the premises of the simplifier as well as the simpset. Then the simplifier is called recursively
on the second statement of the sequential composition with the augmented context. When it is finished
it uses the rule @{thm L2_marked_seq_gets_stop} to introduce the constant \<^const>\<open>STOP\<close>. The congruence 
rule @{thm STOP_cong} prohibits the simplifier to descend down into the just simplified 
second statement again. 

Note that this setup works around the limitation of the simplifier that does not allow us to modify
the context by something like a "congproc", similar to a "simproc". Keep in mind that a congruence
rule is applied top-down as the simplifier works its way down into a term, whereas a simpproc (or any
other simplification rule) is applied buttom up. So a simproc / simplification rule can build on 
the fact that the subterms are already normalised. The simplifier makes use of this by doing some
bookkeeping with "term-skeletons" to avoid resimplification of subterms. This mechanism fails
short in our setup of using a congruence rule to stop simplification of the second statement and
calling the simproc instead. That is why we explicitly introduce \<^const>\<open>STOP\<close>. It will be removed
after simplification by an additional traversal of the term.
\<close>


declare [[simp_trace=false, ML_print_depth=1000]]

text \<open>Propagation of simple constant by unfolding.\<close>

lemma "L2_seq_gets c [\<S> ''r'']  (\<lambda>r. (L2_guard (\<lambda>_. P r ))) =
       L2_guard (\<lambda>_. P c )"
  by (tactic \<open>simp_tac (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) 1\<close>)

text \<open>Propagation of term, as it only appears once in the second statement.\<close>

lemma "L2_seq_gets (c + d) [\<S> ''r'']  (\<lambda>r. (L2_guard (\<lambda>_. P r ))) =
       L2_guard (\<lambda>_. P (c + d) )"
  by (tactic \<open>simp_tac (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) 1\<close>)

text \<open>As nothing is in the prems yet, marking is just removed and second statement is thus simplified\<close>
lemma "L2_seq_gets (c + d) [\<S> ''r'']  (\<lambda>r. (L2_guard (\<lambda>_. P r \<and> (P r \<longrightarrow> Q r)))) =
       L2_seq (L2_gets (\<lambda>_. c + d) [\<S> ''r'']) (\<lambda>r. L2_guard (\<lambda>_. P r \<and> Q r))"
  by (tactic \<open>simp_tac (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) 1\<close>)

text \<open>The first guard condition is propagated to the second guard, via the intermediate
assignment @{term "r = a + b"}.\<close>
lemma "L2_seq_guard (\<lambda>_. a + b < 5) 
        (\<lambda>_. L2_seq_gets (a + b) [\<S> ''r''] 
          (\<lambda>r. L2_guard (\<lambda>_. r < 5 \<and> P))) =
       L2_seq_guard (\<lambda>_. a + b < 5)  
         (\<lambda>_. L2_guard (\<lambda>_. P))"
  by (tactic \<open>simp_tac (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) 1\<close>)


ML \<open>
fun assert_rhs thm =
 Tuple_Tools.assert_cterm' @{context} (Thm.term_of (Thm.rhs_of thm))

\<close>
ML_val \<open>
val ct = @{cterm "L2_seq_guard (\<lambda>_. (a::int) + b < 5) 
    (\<lambda>_. L2_seq_gets (a + b) [\<S> ''r'']  
      (\<lambda>r. (L2_guard (\<lambda>_. r < 5 \<and> P))))"}
val test = Simplifier.asm_full_rewrite (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) ct
val _ = assert_rhs test 
 @{cterm "STOP (L2_seq_guard (\<lambda>_. (a::int) + b < 5) (\<lambda>_. L2_guard (\<lambda>_. P)))"}
\<close>


lemma "L2_seq_guard (\<lambda>s. V1 + a - (r::int) \<le> 2)
        (\<lambda>_. L2_seq (L2_condition (\<lambda>s. CC) (L2_seq_guard (\<lambda>s. V1 + a - r \<le> 3) (\<lambda>_. X1)) X2) (\<lambda>_. X3)) =
       L2_seq_guard (\<lambda>s. V1 + a - r \<le> 2)
        (\<lambda>_. L2_seq (L2_condition (\<lambda>s. CC) (L2_seq_guard (\<lambda>s. True) (\<lambda>_. X1)) X2) (\<lambda>_. X3))"
  by (tactic \<open>asm_full_simp_tac (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) 1\<close>)

ML_val \<open>
val ct = @{cterm "L2_seq_guard (\<lambda>s. (V1 + a - (r::int) \<le> 2))
          (\<lambda>_. L2_seq (L2_condition (\<lambda>s. CC) (L2_seq_guard (\<lambda>s. V1 + a - r \<le> 3) (\<lambda>_. X1)) X2) (\<lambda>_. X3))"}

val test = Simplifier.asm_full_rewrite (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP) ct 
val _ = assert_rhs test
  @{cterm "STOP (L2_seq_guard (\<lambda>s. V1 + a - r \<le> 2)
     (\<lambda>_. L2_seq (L2_condition (\<lambda>s. CC) (STOP (L2_seq_guard (\<lambda>s. True) (\<lambda>_. X1))) X2) (\<lambda>_. X3)))"}
\<close>

ML \<open>
val ct = @{cterm "L2_seq_guard
         (\<lambda>_. ((g k)::int) + (a::int) - r \<le> n)
          (\<lambda>_. 
            (L2_seq_guard (\<lambda>s. (g k) + a - r \<le> n + 1) (\<lambda>_. X1)))"}

val test = Simplifier.asm_full_rewrite (Variable.set_body true (L2Opt.cleanup_ss @{context} [] FunctionInfo.PEEP)) ct
val _ = assert_rhs test @{cterm "STOP (L2_seq_guard (\<lambda>_. g k + a - r \<le> n) (\<lambda>_. STOP (L2_seq_guard (\<lambda>s. True) (\<lambda>_. X1))))"}
\<close>


declare [[simp_trace=false, linarith_trace=false]]

section \<open>Tricks to enforce first-order unification\<close>

ML_val \<open>
val fo = Utils.reify_comb_conv @{context} @{pattern "?a $ (?g $ ?x)"} @{cterm "(f z) (k y) "}
val orig = Utils.unreify_comb_conv @{context} @{pattern "?a $ (?g $ ?x)"} (Thm.rhs_of fo)
val t = Utils.dest_reified_comb @{cterm "a $ b"}
\<close>

text \<open>In heap lifting phase:\<close>
thm heap_abs_fo
text \<open>In word abstraction phase:\<close>
thm abstract_val_fun_app

lemma abstract_val_fun_app':
   "\<lbrakk>abstract_val Q x id x'; abstract_val P f id f' \<rbrakk> \<Longrightarrow>
           abstract_val (P \<and> Q) (g (f x)) g (f' x')"
  by (simp add: abstract_val_def)


schematic_goal "abstract_val ?Q ?f g (f' a')"
  apply (rule abstract_val_fun_app')
   (* back *) (* we need backtracking to get the 'obvious' unifier *) 
  oops

text \<open>@{ML\<open>Utils.fo_arg_resolve_tac\<close>} does the trick for us.  \<close>

schematic_goal "abstract_val ?Q ?f g (f' a')"
  apply (tactic \<open>Utils.fo_arg_resolve_tac @{context} @{thm abstract_val_fun_app} @{context} 1\<close>)
  oops


text \<open>It turned out that @{ML\<open>Utils.fo_arg_resolve_tac\<close>} and other tactics like simplification
can become quite slow when operating under a lot of bound variables. We introduced a
@{ML\<open>WordAbstract.thin_abs_var_tac\<close>} to remove unused premises and bound variables.
It is triggered by @{const THIN} in the rules, e.g. @{thm corresTA_L2_seq}.
\<close>
schematic_goal "
\<And>n' s r r' ra r'a sa.

               abs_var r id r' \<Longrightarrow>
               abs_var ra id r'a \<Longrightarrow> abstract_val (?Q57 r ra sa) (?b60 r ra sa) id (6 * r'a)"
 
  apply (tactic \<open>WordAbstract.thin_abs_var_tac @{context} 1\<close> )
  oops

schematic_goal "
\<And>n' s r r' ra r'a sa.
               abs_var n id n' \<Longrightarrow>
               abs_var r id r' \<Longrightarrow>
               abs_var ra id r'a \<Longrightarrow> abstract_val (?Q57 r ra sa) (?b60 r ra sa) id (6 * r'a)"
 
  apply (tactic \<open>WordAbstract.thin_abs_var_tac @{context} 1\<close> )
  oops

section "Exception Rewriting"

text \<open>
This section highlights some of the ideas to rewrite and optimise exceptions.

In SIMPL and L1 the cause for an exception is stored in the state record in field
@{const global_exn_var'_'}. 
The handler then inspects the state to decide whether it is responsible or not, and either
handles the exception or re-raises it.
In L2 this is refined in several steps. 
\<^item> The cause of the exception is moved out of the state and represented as an error result 
  in the L2 monad.
\<^item> The check for the cause in the handler of @{const L2_catch} is resolved to a static
  nesting of @{const L2_try} instead. The static nesting depth is directly reflected in the
  depth of the sum that reflects the error value \<open>Inl (Inl ...)\<close>. For local exceptions
  this sequence of @{const Inl} ends with an @{const Inr}, global exception (crossing
  function boundaries) end in an @{const Inl}.
\<^item> The tuple arity of intermediate bindings in statements like @{term L2_seq}, 
  @{term L2_while} is optimised to only propagate values that are actually used later on. 
  As a side effect of this step, unnecessary nondeterministic initialisation steps for 
  local variables (especially the technical return variable) are removed. 
  The initialisation becomes unnecessary if the variable is strictly assigned to before 
  used. This is always the case for the return variable, as  \<open>return x\<close> is translated
  to an assignment to the return variable followed by raising the @{const Return} exception.
 
Note that the field @{const global_exn_var'_'} has a special status, it is neither
part of @{const globals} nor @{const locals}. In function calls it is treated like a global
variable to ensure that the exception passes function boundaries. However, in the local variable
abstraction of phase L2 it is treated similar to local variable and abstracted to lambda bindings. 

\<close>
declare [[verbose=3]]
declare [[verbose_timing = 3]]

subsection \<open>Preliminary examples illustrating the usage of @{const rel_spec_monad}\<close>

schematic_goal "rel_spec_monad (=) (=)
(L2_catch
        (L2_seq
          (L2_catch
          
              (L2_while (\<lambda>r s. True)
                (\<lambda>r. L2_condition (\<lambda>s. 3 < a) (L2_throw (Return, (1::int)) [\<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_seq
                         (L2_condition (\<lambda>s. 1 < a)
                           ((L2_throw (Nonlocal (1::nat), r) [\<S> ''global_exn_var'', \<S> ''ret''])::(nat c_exntype \<times> int, int, 'a) exn_monad)
                           (L2_throw (Break, r) [\<S> ''global_exn_var'', \<S> ''ret'']))
                         (\<lambda>ra. L2_gets (\<lambda>s. r) [\<S> ''ret''])))
                r [\<S> ''ret''])
              
            (\<lambda>(a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>_. b) [\<S> ''ret''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, 2) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b).
            L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret'']) (L2_throw (the_Nonlocal a) [\<S> ''global_exn_var''])))

?A
"
  supply c_exntype.case_distrib [where h=from_xval, simp] prod.case_distrib [where h=from_xval, simp]
    from_xval_simps [simp] c_exntype.case_cong [cong]
  apply (simp add: cond_return2 if_c_exntype_cases)
  apply (rule rel_spec_monad_rel_xvalI)
  apply (rule rel_spec_monad_rel_xval_try_catch [split_tuple f arity: 2])
  apply (rule rel_spec_monad_L2_seq_rel_xval_same_split)
   apply (rule rel_spec_monad_rel_xval_try_catch [split_tuple f arity: 2])
   apply (rule rel_spec_monad_L2_while_rel_xval_same_split)
   apply (rule rel_spec_monad_eq_rel_xval_L2_condition)
    apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
     apply (rule rel_xval.Exn)
     apply simp
     apply (rule rel_sum_Inl)
     apply simp
     apply (rule rel_sum_Inr)
     apply (rule refl)
    apply (simp add: SANITIZE_NAMES_def)
   apply (rule rel_spec_monad_L2_seq_rel_xval_same_split)
    apply (rule rel_spec_monad_eq_rel_xval_L2_condition)
     apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
      apply (rule rel_xval.Exn)
      apply simp
      apply (rule rel_sum_Inl)
      apply simp
      apply (rule rel_sum_Inl)
      apply (rule refl)
     apply (simp add: SANITIZE_NAMES_def)
    apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
     apply (rule rel_xval.Exn)
     apply simp
     apply (rule rel_sum_Inr)
     apply (rule refl)
    apply (simp add: SANITIZE_NAMES_def)
   apply (rule rel_spec_monad_rel_xval_L2_gets)
  apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
   apply (rule rel_xval.Exn)
   apply simp
   apply (rule rel_sum_Inr)
   apply (rule refl)
  apply (simp add: SANITIZE_NAMES_def)
  done


schematic_goal "rel_spec_monad (=) (=)
(L2_seq (L2_unknown [\<S> ''ret__int''])
 (\<lambda>r. L2_catch
        (L2_seq
          (L2_catch
            (L2_seq
              (L2_while (\<lambda>r s. True)
                (\<lambda>r. L2_condition (\<lambda>s. 3 < a) (L2_throw (Return, 1) [\<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_seq
                         (L2_condition (\<lambda>s. 1 < a)
                           (L2_throw (Nonlocal 1, r) [\<S> ''global_exn_var'', \<S> ''ret''])
                           (L2_throw (Break, r) [\<S> ''global_exn_var'', \<S> ''ret'']))
                         (\<lambda>ra. L2_gets (\<lambda>s. r) [\<S> ''ret''])))
                r [\<S> ''ret''])
              (\<lambda>r. L2_gets (\<lambda>s. ()) [\<S> ''ret'']))
            (\<lambda>(a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>_. ()) [\<S> ''ret''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, 2) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b).
            L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret''])
             (L2_throw a [\<S> ''global_exn_var'']))))

?A
"
  supply c_exntype.case_distrib [where h=from_xval, simp] prod.case_distrib [where h=from_xval, simp]
         from_xval_simps [simp] c_exntype.case_cong [cong]
  apply (simp add: cond_return2 if_c_exntype_cases)
  apply (rule rel_spec_monad_rel_xvalI)
  apply (rule rel_spec_monad_L2_seq_rel_xval_same_split)
   apply (rule rel_spec_monad_rel_xval_L2_unknown)
  apply (rule rel_spec_monad_rel_xval_try_catch [split_tuple f arity: 2])
  apply (rule rel_spec_monad_L2_seq_rel_xval_same_split)  
   apply (rule rel_spec_monad_rel_xval_try_catch [split_tuple f arity: 2])
   apply (rule rel_spec_monad_L2_seq_rel_xval_same_split)  
   apply (rule rel_spec_monad_L2_while_rel_xval_same_split)
    apply (rule rel_spec_monad_eq_rel_xval_L2_condition)
     apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
      apply (rule rel_xval.Exn)
      apply simp
      apply (rule rel_sum_Inl)
      apply simp
      apply (rule rel_sum_Inr)
      apply (rule refl)
     apply (simp add: SANITIZE_NAMES_def)
    apply (rule rel_spec_monad_L2_seq_rel_xval_same_split)
     apply (rule rel_spec_monad_eq_rel_xval_L2_condition)
     apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
      apply (rule rel_xval.Exn)
      apply simp
      apply (rule rel_sum_Inl)
      apply simp
      apply (rule rel_sum_Inl)
      apply (rule refl)
      apply (simp add: SANITIZE_NAMES_def)
    apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
      apply (rule rel_xval.Exn)
      apply simp
      apply (rule rel_sum_Inr)
      apply (rule refl)
     apply (simp add: SANITIZE_NAMES_def)
    apply (rule rel_spec_monad_rel_xval_L2_gets)
   apply (rule rel_spec_monad_rel_xval_L2_gets)
    apply (rule rel_spec_monad_L2_throw_sanitize_names [where ns' = "[]"])
      apply (rule rel_xval.Exn)
      apply simp
      apply (rule rel_sum_Inr)
      apply (rule refl)
  apply (simp add: SANITIZE_NAMES_def)
  done


subsection \<open>From @{const L2_catch} and flat exceptions to @{const L2_try} and nested exceptions\<close>

schematic_goal "rel_spec_monad (=) (=)
(L2_seq (L2_unknown [\<S> ''ret__int''])
 (\<lambda>r. L2_catch
        (L2_seq
          (L2_catch
            (L2_seq
              (L2_while (\<lambda>r s. True)
                (\<lambda>r. L2_condition (\<lambda>s. 3 < a) (L2_throw (Return, 1) [\<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_seq
                         (L2_condition (\<lambda>s. 1 < a)
                           (L2_throw (Nonlocal 1, r) [\<S> ''global_exn_var'', \<S> ''ret''])
                           (L2_throw (Break, r) [\<S> ''global_exn_var'', \<S> ''ret'']))
                         (\<lambda>ra. L2_gets (\<lambda>s. r) [\<S> ''ret''])))
                r [\<S> ''ret''])
              (\<lambda>r. L2_gets (\<lambda>s. ()) [\<S> ''ret'']))
            (\<lambda>(a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>_. ()) [\<S> ''ret''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, 2) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b).
            L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret''])
             (L2_throw a [\<S> ''global_exn_var'']))))

?A
"
  apply (simp add: cond_return2 if_c_exntype_cases cong: c_exntype.case_cong)
  apply (rule rel_spec_monad_rel_xvalI)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done


schematic_goal "rel_spec_monad (=) (=)
(L2_seq (L2_unknown [\<S> ''ret__int''])
 (\<lambda>r. L2_catch
        (L2_seq
          (L2_catch
            (L2_seq
              (L2_while (\<lambda>r s. True)
                (\<lambda>r. L2_condition (\<lambda>s. 3 < a) (L2_throw (Return, 1) [\<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_seq
                         (L2_condition (\<lambda>s. 1 < a)
                           (L2_throw (Nonlocal 1, r) [\<S> ''global_exn_var'', \<S> ''ret''])
                           (L2_throw (Break, r) [\<S> ''global_exn_var'', \<S> ''ret'']))
                         (\<lambda>ra. L2_gets (\<lambda>s. r) [\<S> ''ret''])))
                r [\<S> ''ret''])
              (\<lambda>r. L2_gets (\<lambda>s. ()) [\<S> ''ret'']))
            (\<lambda>(a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>_. ()) [\<S> ''ret''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, 2) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b).
            L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret''])
             (L2_throw a [\<S> ''global_exn_var'']))))

?A
"
  apply (simp add: cond_return2 if_c_exntype_cases cong: c_exntype.case_cong)
  apply (rule rel_spec_monad_rel_xvalI)
  apply (rel_spec_monad_L2_rewrite)
  done

schematic_goal "rel_spec_monad (=) (=)
 (L2_seq (L2_unknown [\<S> ''ret__int''])
                                   (\<lambda>ret__int.
                                       L2_catch
                                        (L2_seq
                                          (L2_condition (\<lambda>s. p = 0x20 \<or> 2 <s p)
                                            (L2_condition (\<lambda>s. p \<noteq> 0x1E \<and> p \<noteq> 2) (L2_throw (Return, p) [\<S> ''global_exn_var'', \<S> ''ret''])
                                              (L2_gets (\<lambda>_. ret__int) [\<S> ''ret'']))
                                            (L2_gets (\<lambda>_. ret__int) [\<S> ''ret'']))
                                          (\<lambda>ret__int.
                                              L2_seq
                                               (L2_call (l2_add' undefined p p) (\<lambda>global_exn_var. (Nonlocal (the_Nonlocal global_exn_var), ret__int))
                                                 [\<S> ''global_exn_var'', \<S> ''ret''])
                                               (\<lambda>p___int. L2_throw (Return, p) [\<S> ''global_exn_var'', \<S> ''ret''])))
                                        (\<lambda>(global_exn_var, ret__int).
                                            L2_condition (\<lambda>s. is_local global_exn_var) (L2_gets (\<lambda>_. ret__int) [\<S> ''ret''])
                                             (L2_throw global_exn_var [\<S> ''global_exn_var'']))))
?A
"
  apply (simp add: cond_return2 if_c_exntype_cases cong: c_exntype.case_cong)
  apply (rule rel_spec_monad_rel_xvalI)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done

ML \<open>
val thm = L2_Exception_Rewrite.abstract_try_catch @{context} @{term "(L2_seq (L2_unknown [\<S> ''ret__int''])
 (\<lambda>r. L2_catch
        (L2_seq
          (L2_catch
            (L2_seq
              (L2_while (\<lambda>r s. True)
                (\<lambda>r. L2_condition (\<lambda>s. 3 < a) (L2_throw (Return, 1) [\<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_seq
                         (L2_condition (\<lambda>s. 1 < a)
                           (L2_throw (Nonlocal 1, r) [\<S> ''global_exn_var'', \<S> ''ret''])
                           (L2_throw (Break, r) [\<S> ''global_exn_var'', \<S> ''ret'']))
                         (\<lambda>ra. L2_gets (\<lambda>s. r) [\<S> ''ret''])))
                r [\<S> ''ret''])
              (\<lambda>r. L2_gets (\<lambda>s. ()) [\<S> ''ret'']))
            (\<lambda>(a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>_. ()) [\<S> ''ret''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, 2) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b).
            L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret''])
             (L2_throw a [\<S> ''global_exn_var'']))))"}
\<close>

schematic_goal "rel_spec_monad (=) (rel_xval (=) (=))
(L2_seq (L2_unknown [\<S> ''ret__int''])
 (\<lambda>r. L2_catch
        (L2_seq
          (L2_catch
            (L2_seq
              (L2_while (\<lambda>r s. True)
                (\<lambda>r. L2_condition (\<lambda>s. 3 < a) (L2_throw (Return, 1) [\<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_condition (\<lambda>s. 1 < a) (L2_gets (\<lambda>s. r) [\<S> ''ret''])
                         (L2_throw (Break, r) [\<S> ''global_exn_var'', \<S> ''ret''])))
                r [\<S> ''ret''])
              (\<lambda>r. L2_gets (\<lambda>s. ()) [\<S> ''ret'']))
            (\<lambda>(a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>_. ()) [\<S> ''ret''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, 2) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b). L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret'']) (L2_throw a [\<S> ''global_exn_var'']))))
?A"
  apply (simp add: cond_return2 if_c_exntype_cases cong: c_exntype.case_cong)
  apply (rel_spec_monad_L2_rewrite)
  done

schematic_goal 
"rel_spec_monad (=) (rel_xval (=) (=))
(L2_seq (L2_unknown [\<S> ''ret__int''])
 (\<lambda>r. L2_catch
        (L2_seq
          (L2_catch
            (L2_seq
              (L2_while (\<lambda>(a, b) a. True)
                (\<lambda>(a, b).
                    L2_seq
                     (L2_condition (\<lambda>s. 3 < a)
                       (L2_throw (a, Return, 1) [\<S> ''a'', \<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_seq
                         (L2_condition (\<lambda>s. 1 < a) (L2_gets (\<lambda>s. a + 1) [\<S> ''a''])
                           (L2_throw (a, Break, b) [\<S> ''a'', \<S> ''global_exn_var'', \<S> ''ret'']))
                         (\<lambda>r. L2_gets (\<lambda>s. (r, b)) [\<S> ''a'', \<S> ''ret''])))
                     (\<lambda>(a, b). L2_gets (\<lambda>s. (a, b)) [\<S> ''a'', \<S> ''ret'']))
                (a, r) [\<S> ''a'', \<S> ''ret''])
              (\<lambda>(a, b). L2_gets (\<lambda>s. a) [\<S> ''a'']))
            (\<lambda>(aa, a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>s. aa) [\<S> ''a''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, r) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b).
            L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret''])
             (L2_throw a [\<S> ''global_exn_var'']))))
?A"
  apply (simp add: cond_return2 if_c_exntype_cases cong: c_exntype.case_cong)
  apply (rel_spec_monad_L2_rewrite)
  done


declare [[show_main_goal=true]]
subsection \<open>Flatten the error type of calls, aka get rid of constructor @{term Nonlocal}\<close>


(* this should be the same as lift_exit_status *)
schematic_goal "rel_spec_monad (=) (rel_xval rel_Nonlocal (=))
(L2_seq (L2_unknown [\<S> ''ret__int''])
 (\<lambda>r. L2_catch
        (L2_seq
          (L2_catch
            (L2_seq
              (L2_while (\<lambda>r s. True)
                (\<lambda>r. L2_condition (\<lambda>s. 3 < a) (L2_throw (Return, 1) [\<S> ''global_exn_var'', \<S> ''ret''])
                       (L2_seq
                         (L2_condition (\<lambda>s. 1 < a)
                           (L2_throw (Nonlocal 1, r) [\<S> ''global_exn_var'', \<S> ''ret''])
                           (L2_throw (Break, r) [\<S> ''global_exn_var'', \<S> ''ret'']))
                         (\<lambda>ra. L2_gets (\<lambda>s. r) [\<S> ''ret''])))
                r [\<S> ''ret''])
              (\<lambda>r. L2_gets (\<lambda>s. ()) [\<S> ''ret'']))
            (\<lambda>(a, b).
                L2_condition (\<lambda>s. a = Break) (L2_gets (\<lambda>_. ()) [\<S> ''ret''])
                 (L2_throw (a, b) [\<S> ''global_exn_var'', \<S> ''ret''])))
          (\<lambda>r. L2_throw (Return, 2) [\<S> ''global_exn_var'', \<S> ''ret'']))
        (\<lambda>(a, b).
            L2_condition (\<lambda>s. is_local a) (L2_gets (\<lambda>s. b) [\<S> ''ret''])
             (L2_throw a [\<S> ''global_exn_var'']))))

?A
"
  apply (simp add: cond_return2 if_c_exntype_cases cong: c_exntype.case_cong)
  apply (rel_spec_monad_L2_rewrite)
  done

text \<open>Some statistics on the caches involved.\<close>
ML \<open>
val statistics = map (apsnd  Fun_Cache.get_info) (Fun_Cache.all_handlers ()) 
\<close>


section \<open>Tuple optimization by analysing variable use and removing unused variables.\<close>

text \<open>The cases for @{const L2_seq} are the points were the 
uses-analysis is invoked: @{ML \<open>Rel_Spec_Monad_Synthesize_Rules.analyse_uses\<close>}.
The analysis follows the usage of the bound variable within the term.
\<close>



schematic_goal "
 rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. ()))) 
(L2_seq (L2_gets (\<lambda>_. x) [\<S> ''x'']) 
      (\<lambda>x. L2_seq 
        (L2_gets (\<lambda>_. (x, y)) [\<S> ''x'',\<S> ''y'']) 
        (\<lambda>(x, y). L2_gets (\<lambda>_. y) [\<S> ''y''])))
?X
"
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step) 
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done


schematic_goal "
 rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
(L2_seq (L2_gets (\<lambda>_. x) [\<S> ''x'']) 
      (\<lambda>x. L2_seq 
        (L2_gets (\<lambda>_. (x, y)) [\<S> ''x'',\<S> ''y'']) 
        (\<lambda>(x, y). L2_gets (\<lambda>_. y) [\<S> ''y''])))
?X
"
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step) 
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done


schematic_goal "
 rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
   (L2_seq (L2_gets (\<lambda>_. (l,m)) [\<S> ''l'', \<S> ''m'']) 
      (\<lambda>(x, y). L2_seq 
        (L2_gets (\<lambda>_. (x, k)) [\<S> ''x'', \<S> ''y''])
        
        (\<lambda>(a, b).
         L2_seq 
          (L2_while (\<lambda>(x,y) _. x < 2) 
            (\<lambda>(x,y). (L2_gets (\<lambda>_. (y, k)) [\<S> ''x'', \<S> ''y'']) ) 
            (a, b)  [\<S> ''x'', \<S> ''y''])
          (\<lambda>(x, y). L2_gets (\<lambda>_. y) [\<S> ''y'']) )))
?X"
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step)  
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)  
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done



declare [[show_main_goal=true]]
schematic_goal "
 rel_spec_monad (=) (rel_xval(=) (rel_project (\<lambda>v. v))) 
   (L2_seq (L2_gets (\<lambda>_. (l,m)) [\<S> ''l'', \<S> ''m'']) 
      (\<lambda>(x, y). L2_seq 
        (L2_gets (\<lambda>_. (x, k)) [\<S> ''x'', \<S> ''y''])
        
        (\<lambda>(a, b).
         L2_seq 
          (L2_while (\<lambda>(x,y) _. y < 2) 
            (\<lambda>(x,y). (L2_gets (\<lambda>_. (y, k)) [\<S> ''x'', \<S> ''y'']) ) 
            (a, b)  [\<S> ''x'', \<S> ''y''])
          (\<lambda>(x, y). L2_gets (\<lambda>_. y) [\<S> ''y'']) )))
?X"
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) 
  apply (rel_spec_monad_L2_step) (* L2_seq *)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done



schematic_goal "
 rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
(L2_seq (L2_unknown [\<S> ''ret__unsigned''])
 (\<lambda>x. L2_try
        (L2_seq
          (L2_while (\<lambda>(n___int, ret__unsigned) s. True)
            (\<lambda>(x1, x2).
                L2_seq (L2_guard (\<lambda>s. 0 \<le> 2147483649 + sint x1 \<and> sint x1 \<le> 2147483646))
                 (\<lambda>xa. L2_seq (L2_gets (\<lambda>_. x1 + 1) [\<S> ''n''])
                         (\<lambda>xb. L2_seq
                                 (L2_condition (\<lambda>s. xb <s 2) (L2_throw (Inr 1) [\<S> ''ret''])
                                   (L2_throw (Inr 2) [\<S> ''ret'']))
                                 (\<lambda>xc. L2_gets (\<lambda>_. (xb, xc)) [\<S> ''n'', \<S> ''ret'']))))
            (n, x) [\<S> ''n'', \<S> ''ret''])
          (\<lambda>(x1, x2). L2_fail))))
?X"

  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done

schematic_goal "rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
 (L2_seq (L2_call (l2_plus' undefined 1 2) (\<lambda>e. e) [])
   (\<lambda>x. L2_seq (L2_call (l2_plus' undefined 2 3) (\<lambda>e. e) [])
          (\<lambda>xa. L2_gets (\<lambda>s. if xa = 0 then 1 else 0) [\<S> ''ret''])))
?XX" 
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done


schematic_goal "rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
(L2_seq (L2_unknown [\<S> ''ret__int''])
  (\<lambda>x. L2_seq (L2_gets (\<lambda>_. 2) [\<S> ''x''])
         (\<lambda>xa. L2_try
                 (L2_seq
                   (L2_try
                     (L2_seq
                       (L2_while (\<lambda>(a___int, ret__int, y___int) s. True)
                         (\<lambda>(x1, x2, x3).
                             L2_seq (L2_gets (\<lambda>_. 4) [\<S> ''y''])
                              (\<lambda>xb. L2_seq
                                      (L2_condition (\<lambda>s. 3 <s x1) (L2_throw (Inl (Inr 1)) [\<S> ''ret'', \<S> ''y''])
                                        (L2_seq
                                          (L2_condition (\<lambda>s. 1 <s x1)
                                            (L2_seq (L2_guard (\<lambda>s. 0 \<le> 2147483649 + sint x1 \<and> sint x1 \<le> 2147483646))
                                               (\<lambda>xc. L2_gets (\<lambda>s. x1 + 1) [\<S> ''a'']))
                                            (L2_try
                                              (L2_seq (L2_try (L2_while (\<lambda>_ s. True) (\<lambda>xc. L2_throw (Inr xc) []) () [])) (\<lambda>xc. L2_throw (Inl (Inr xb)) []))))
                                          (\<lambda>xc. L2_gets (\<lambda>_. (xc, x2)) [\<S> ''a'', \<S> ''ret''])))
                                      (\<lambda>(x1, x2). L2_gets (\<lambda>_. (x1, x2, xb)) [\<S> ''a'', \<S> ''ret'', \<S> ''y''])))
                         (a, x, 3) [\<S> ''a'', \<S> ''ret'', \<S> ''y''])
                       (\<lambda>(x1, x2, x3). L2_gets (\<lambda>_. x3) [\<S> ''y''])))
                   (\<lambda>xb. L2_seq (L2_guard (\<lambda>s. - 2147483648 \<le> sint xa + sint xb \<and> sint xa + sint xb \<le> 2147483647))
                           (\<lambda>xc. L2_throw (Inr (xa + xb)) [\<S> ''ret'']))))))
?X"
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) 
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) 
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step) 
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)  
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done


schematic_goal "rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
  (L2_condition (\<lambda>s. n = 0) (L2_gets (\<lambda>s. 0) [\<S> ''ret''])
    (L2_seq (L2_call (l2_even' (recguard_dec rec_measure') (n - 1)) (\<lambda>e. e) [])
      (\<lambda>x. L2_gets (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (if x = 0 then 1 else 0))
             [\<S> ''ret''])))
?X"
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done



schematic_goal "rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
 (L2_seq (L2_unknown [\<S> ''ret__unsigned''])
   (\<lambda>x. L2_condition (\<lambda>s. n = 0) (L2_gets (\<lambda>s. 0) [\<S> ''ret''])
          (L2_try
            (L2_seq
              (L2_call
                (l2_fac_exit' (recguard_dec rec_measure') (n - 1))
                 (\<lambda>e. Inl (Nonlocal (the_Nonlocal e))) [\<S> ''ret''])
              (\<lambda>xa. L2_throw (Inr xa) [\<S> ''ret''])))))
?X"                              
  apply (rel_spec_monad_L2_step)  
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done


schematic_goal "rel_spec_monad (=) (rel_xval (=) (rel_project (\<lambda>v. v))) 
(L2_try
 (L2_call (l2_just_exit' undefined)
  (\<lambda>e. Inl (Nonlocal (the_Nonlocal e))) [])
   ) 
?X" 
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  apply (rel_spec_monad_L2_step)
  done
   


declare [[show_main_goal=false]]
declare [[verbose=0]]
declare [[verbose_timing=0]]

section \<open>Locales, Local-Theories, Named-Targets, Morphisms and Declarations...\<close>

text \<open>
We explore some of the concepts of Locales, Local-Theories, Named-Targets, Declarations etc.
Besided the corresponding chapters in the Isabelle/Isar Reference Manual as well as the
Isabelle/Isar Implementation Manual, the following references give a solid theoretical background:
\<^item> Local Theories: \<^url>\<open>http://isabelle.in.tum.de/~haftmann/pdf/local_theory_specifications_haftmann_wenzel.pdf\<close>
\<^item> Locales: \<^url>\<open>http://www21.in.tum.de/~ballarin/publications/jar2013.pdf\<close>
\<^item> Morphisms and Declarations: \<^url>\<open>https://www21.in.tum.de/~wenzelm/papers/context-methods.pdf\<close>

Roughly speaking, locales provide the infrastructure to manage the dependency graph of locale declarations. 
When entering a locale this dependency graph is traversed and results in a blue-print to build a
local context by expanding and evaluating the locale expressions in a canonical order. 
The result is presented to the user as a local theory. A local theory consists of an axiomatic part 
(think of fixes and assumes) and a derived part, consisting of definitions
and theorems within the axiomatic part.
\<close>


locale Foo =
  fixes N::nat
  fixes M::nat
  assumes N_le_M: "N < M"

text \<open>Locale @{locale Foo} is blue-print to build a local context. We can enter this context
with @{command context}.\<close>

context Foo
begin

text \<open>Within the context we can explore it. As an example the locale assumption becomes a
theorem within the context\<close>

thm N_le_M

text \<open>Within the context the axiomatic part (fixes and assumes) are often accessed implicitly. For
example the fixes are presented as free Variables with the declared type fixed.\<close>

ML \<open>@{assert} (@{term N} = Free ("N", @{typ nat}))\<close>

text \<open>The locale assumptions are wrapped up in the locale predicate @{const Foo}, and internally
become part of the hypothesis of a (local theory) theorem. Theorems derived within the local
theory will all carry around this implicit hypothesis. \<close>

declare [[show_hyps]]
thm N_le_M
ML \<open>@{thm N_le_M}\<close>
thm Foo_def

text \<open>There is also an exported version of the theorem that holds on the theory level. Here
the implicit hypothesis becomes an explicit precondition.\<close>

thm Foo.N_le_M

text \<open>A definition in a local theory has multiple effects. A generalised definition, where the
locale fixes become explicit parameters is issued in the background theory. Moreover, an
abbreviation that hides these parameters in introduced.\<close>
definition G_def: "G = M + N"

lemma "G = Foo.G N M"..

ML \<open>@{assert} (@{term G} = @{term "Foo.G N M"})\<close>

text \<open>When working within ML we also deal with another view, the \<^emph>\<open>auxiliary context\<close> as 
referred to in the Isabelle documentation. On the Isar top-level we are usually only
exposed to the \<^emph>\<open>background theory\<close>, e.g. @{term "Foo.G"} and the \<^emph>\<open>target context\<close>, e.g. @{term G}.\<close>

local_setup \<open> fn lthy0 =>
 let

  val ((trm, (def_name, def_thm)), lthy1) = lthy0 |>
        Specification.definition (SOME (Binding.name "F", NONE, NoSyn))
            [] [] (Binding.empty_atts, @{prop "F = G + M"})
  \<comment> \<open>lthy1 is now the auxiliary context. Here @{term F} aka. \<open>trm\<close> is not an abbreviation but
  acutally a fixed variable in that auxiliary context. \<close>
  val _ = @{print} trm
  val _ = @{assert} (trm = Free ("F", @{typ nat}))
  \<comment>\<open>Theorems within this context will have an additional hypothesis reflecting the definition equation
  of the @{term F}, @{term "F \<equiv> Foo.F N M"}. This can be explored already in \<open>def_thm\<close>.\<close>
  
  val _ = writeln (Thm.string_of_thm lthy1 def_thm)

  \<comment>\<open>One can switch between the different views / versions of a theorem by \<^emph>\<open>exporting\<close> it,
  either by means of an explicit export-morphism or by an export function.
  Out of the auxiliary context into the target context (view of the locale):\<close>
  val [target_def_thm] = Proof_Context.export lthy1 lthy0 [def_thm]
  val _ = writeln ("target_def_thm: " ^ Thm.string_of_thm lthy1 target_def_thm)
  val phi_target = Proof_Context.export_morphism lthy1 lthy0
  val target_def_thm' = Morphism.thm phi_target def_thm
  val _ = writeln ("target_def_thm': "  ^ Thm.string_of_thm lthy1 target_def_thm')
  \<comment>\<open>Out on the theory level.\<close>
  val thy_lthy = Proof_Context.init_global (Proof_Context.theory_of lthy1)
  val [theory_def_thm] = Proof_Context.export lthy1 thy_lthy [def_thm]
  val _ = writeln ("theory_def_thm: " ^ Thm.string_of_thm lthy1 theory_def_thm)
  val phi_thy = Proof_Context.export_morphism lthy1 thy_lthy
  val theory_def_thm' = Morphism.thm phi_thy def_thm
  val _ = writeln ("theory_def_thm': " ^ Thm.string_of_thm lthy1 theory_def_thm')
 in
  lthy1
 end
\<close>

text \<open>Here we have the target view of the freshly defined @{term F}.\<close>
ML \<open>@{assert} (@{term F} = @{term "Foo.F N M"})\<close>

text \<open>One notable logical difference of the view on a definition within a auxiliary context
and the target context is polymorphism. Within the auxiliary context the definition is always 
monomorphic, maybe referring to implicitly fixed types 'variables', or better frees. Within
the target context it might be polymorphic (depending on the definition), 
as it is just an abbreviation for the global constant applied to the locale parameters.

The fixed view of the auxiliary context can be quite handy when continuing work with the
freshly defined function, do some proofs etc. in ML.

Working with nested contexts, like fixing and assuming new stuff opening and closing them and
exporting results is supported within ML by @{ML Local_Theory.begin_nested} and 
@{ML Local_Theory.end_nested}. The term might be a little bit misleading as you don't actually 
open an close a target but open and close a context block within the same target. 

The following example illustrates this first with toplevel commands and then with ML.
\<close>


context
  fixes K
  assumes M_le_K: "M < K"
begin
lemma N_le_K: "N < K"
  by (rule less_trans [OF N_le_M M_le_K])

text \<open>Here we have the local view on the theorem within the nested context.\<close>
thm N_le_K
end

text \<open>Now we have the exported view of the theorem within the target context.\<close>
thm N_le_K

local_setup \<open>fn lthy0 =>
let
  val (_, lthy) = lthy0 |> Local_Theory.begin_nested 
  val ([K], lthy) = Variable.add_fixes ["K"] lthy
  val _ = writeln ("is_fixed K: " ^ @{make_string} (Variable.is_fixed lthy "K"))
  val ([M_le_K], lthy_inner) = Assumption.add_assumes  [(Thm.cterm_of lthy (Syntax.read_prop lthy "M < K"))] lthy
  val thm = @{thm less_trans} OF [@{thm N_le_M}, M_le_K]
  val ([(th_name,[thm])],  lthy) = Local_Theory.notes [((Binding.name "N_le_K'",[]), [([thm], [])])] lthy_inner 
  val _ = writeln ("thm: " ^ Thm.string_of_thm lthy thm)
  val lthy = lthy |> Local_Theory.end_nested
  val _ = writeln ("is_fixed K: " ^ @{make_string} (Variable.is_fixed lthy "K"))
  val [target_thm] = Proof_Context.export lthy_inner lthy [thm]
  val _ = writeln ("target_thm: " ^ Thm.string_of_thm lthy target_thm)
in
  lthy
end

\<close>

text \<open>Here we have the exported view of the theorem within the target context.\<close>
thm N_le_K'

end

text \<open>After a definition in a local theory the context is extended with a fixed variable
for the lhs and an equation that relates it to the global definition. So everything what happens
thereafter happens within that extended context.
\<close>
ML_val \<open>
val lthy = Named_Target.theory_init @{theory}
val ((lhs,(name, thm)), lthy) = Local_Theory.define ((\<^binding>\<open>foo\<close>, Mixfix.NoSyn), ((Binding.empty, []), @{term "42::nat"})) lthy
val prems = Assumption.all_prems_of lthy
\<close>

text \<open>By surrounding the definition with a @{ML Local_Theory.begin_nested} and @{ML Local_Theory.end_nested}
you can step out of the extended context again. Don't forget to export the results as well. \<close>
ML_val \<open>
val lthy = Named_Target.theory_init @{theory} |> Local_Theory.begin_nested |> snd
val ((lhs,(name, thm)), lthy) = Local_Theory.define ((\<^binding>\<open>foo\<close>, Mixfix.NoSyn), ((Binding.empty, []), @{term "42::nat"})) lthy
val lthy' = Local_Theory.end_nested lthy
val prems = Assumption.all_prems_of lthy'
val [thm'] = Proof_Context.export lthy lthy' [thm]
\<close>


section \<open>Morphisms and Declarations\<close>
text \<open>
As we have seen before, when working with locales and local theories, we deal with different
views on the same results (like theorems). The locale infrastructure takes care to provide
the results in the 'expected' way by a careful naming policy for facts and (local) constants.

When maintaining results in custom (generic) context data, Isabelle provides mechanisms
around the notion of a \<^emph>\<open>declaration\<close>, which comes in various flavours. In particular
attached to (local) theorems / facts in the form of  attributes (rule and declaration attributes) 
or as local theory declarations. In the case of attributes the morphism is implicit, as 
the theorem / facts they are attached to are already in the expected localized version. So the
function can refer to these theorem / facts. In case of local theory declarations the morphism
is explicitly passed as an argument to the function.

In ML, attributes are functions from @{ML_type "thm * Proof.context -> thm * Proof.context"},
in practice presented as either a declaration attribute (modifying the context)
@{ML_type "thm -> Proof.context -> Proof.context"} or as a rule attribute (modifying the theorem)
@{ML_type "Proof.context -> thm -> thm"}. 
Local theory declarations are functions, taking a morphism and modifying the @{ML_type local_theory}: 
@{ML_type "Morphism.morphism -> local_theory -> local_theory"}.


All these declarations are part of the context-building-infrastructure of locales and local
theories. In that sense a local theory declaration can be thought of as declaration attribute attached
to a dummy fact. Whenever a context is entered and the fact is processed the declarations are 
reevaluated on the that context. As we have
seen, at each point there are three contexts simultaneously, representing the background theory,
the target context and the auxiliary context. So at each point there are also three views
on the data, 'viewed' via the application of the explicit or implicit morphisms.

Note that when implementing context data and tools, morphisms come in two variants. 
Import and export morphisms. Exporting results or data out of a context into a more general context 
can often be treated explicit by @{ML Proof_Context.export} or @{ML Proof_Context.export_morphism} or
variants of those functions. This is because going out of a context is unambigous and therefor a 
single morphism is enough.

Whereas when entering into a context (like entering a locale) the morphisms are internally generated
and provided by the locale infrastructure. As a locale might be imported several times in
different variants into the same local theory there is no unambigous morphism. Each import provides
a different morphism.

When issuing a local theory declaration via @{ML Local_Theory.declaration} there is also 
two flags to define, represented as a record @{ML_type "{syntax: bool, pervasive: bool}"}.

\<^item> A pervasive declaration is also applied to the background-theory (besides the target and auxiliary
 context)
\<^item> A syntax declaration is activated already in the syntax phase of the locale roundup. This means,
when your context data already has to be ready to enabling parsing of new assumptions declaring 
a new locale you have to set the syntax flag. 

Note that theorem attributes are treated like @{ML "{pervasive = false, syntax = false}"}. That
means that they are not evaluated on the background-theory version of the facts. 
This makes perfect sense for typical attributes like @{attribute "simp"}. 
The theorem is only added to the simpset within the locale. The background-theorem is not added to 
the simpset of the theory. Keep in mind that the background-theorem is typically an implication with
the locale predicate as precondition. 
However, when you interprete the locale on the theory level the interpreted 
version of the theorem is added to the simpset of the theory, here the locale-predicate precondition
is discharged.

In the following we have some examples illustrating the described behaviour.
\<close>

ML \<open>

structure MyData = Generic_Data (
  type T = int;
  val empty = 0;  
  val merge = fst;
)
\<close>

ML \<open>
val n_theory = MyData.get (Context.Theory @{theory})
val _ = @{assert} (n_theory = 0)
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 0)
\<close>

setup \<open>
Context.theory_map (MyData.put 1)
\<close>
ML \<open>
val n_theory = MyData.get (Context.Theory @{theory})
val _ = @{assert} (n_theory = 1)
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 1)
\<close>


context Foo
begin
ML \<open>
val n_theory = MyData.get (Context.Theory @{theory})
val _ = @{assert} (n_theory = 1)
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 1)
val n_target = MyData.get (Context.Proof (Local_Theory.target_of @{context}))
val _ = @{assert} (n_target = 1)
\<close>


text \<open>Manipulating data by functions like @{ML Context.proof_map} will only have very limited
and especially temporary effect. It is applied to the auxiliary context only. When exiting the
auxiliary context it will be away. Also it has no effect on the target context.\<close>
local_setup
\<open>fn lthy =>
 let
   val lthy = lthy |> Context.proof_map (MyData.put 2)
   val n_aux = MyData.get (Context.Proof lthy)
   val _ = @{assert} (n_aux = 2)
   val n_target = MyData.get (Context.Proof (Local_Theory.target_of lthy))
   val _ = @{assert} (n_target = 1)
   val n_theory = MyData.get (Context.Theory (Proof_Context.theory_of lthy))
   val _ = @{assert} (n_theory = 1)

 in
   lthy
 end
\<close>

text \<open>You might be surprised to see that the value is already reset here. 
The reason is that every toplevel command resets the context and is treated like a block.
Think of a @{ML "Local_Theory.begin_nested"} / @{ML "Local_Theory.end_nested"}.\<close>

ML \<open>
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 1)
\<close>


text \<open>A non pervasive declaration takes effect on the auxiliary and the target context but not
the theory context.\<close>

local_setup \<open>fn lthy =>
  let
    val lthy = lthy |> Local_Theory.declaration {pervasive=false, syntax=false, pos=\<^here>} (fn phi =>  MyData.put 3)
   val n_aux = MyData.get (Context.Proof lthy)
   val _ = @{assert} (n_aux = 3)
   val n_target = MyData.get (Context.Proof (Local_Theory.target_of lthy))
   val _ = @{assert} (n_target = 3)
   val n_theory = MyData.get (Context.Theory (Proof_Context.theory_of lthy))
   val _ = @{assert} (n_theory = 1)
  in lthy end
\<close>

text \<open>As expected the effect is still there at this point.\<close>
ML \<open>
val n_theory = MyData.get (Context.Theory (Proof_Context.theory_of @{context}))
val _ = @{assert} (n_theory = 1)
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 3)
val n_target = MyData.get (Context.Proof (Local_Theory.target_of @{context}))
val _ = @{assert} (n_target = 3)
\<close>
end

text \<open>Note that the declaration is persistent in the sense that when reentering the locale
it will be evaluated again. So when designing custom data and implementing declarations or
attributes one has to be clear about the order of things and that they might be applied in 
many different situations. Using @{ML MyData.map} instead of @{ML MyData.put} might be handy to 
design robust data management.
\<close>

context Foo
begin
ML \<open>
val n_theory = MyData.get (Context.Theory (Proof_Context.theory_of @{context}))
val _ = @{assert} (n_theory = 1)
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 3)
val n_target = MyData.get (Context.Proof (Local_Theory.target_of @{context}))
val _ = @{assert} (n_target = 3)
\<close>

text \<open>A pervasive declaration also effects the theory.\<close>
local_setup \<open>fn lthy =>
  let
    val lthy = lthy |> Local_Theory.declaration {pervasive=true, syntax=false, pos=\<^here>} (fn phi =>  MyData.put 4)
   val n_aux = MyData.get (Context.Proof lthy)
   val _ = @{assert} (n_aux = 4)
   val n_target = MyData.get (Context.Proof (Local_Theory.target_of lthy))
   val _ = @{assert} (n_target = 4)
   val n_theory = MyData.get (Context.Theory (Proof_Context.theory_of lthy))
   val _ = @{assert} (n_theory = 4)
  in lthy end
\<close>

ML \<open>
val n_theory = MyData.get (Context.Theory (Proof_Context.theory_of @{context}))
val _ = @{assert} (n_theory = 4)
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 4)
val n_target = MyData.get (Context.Proof (Local_Theory.target_of @{context}))
val _ = @{assert} (n_target = 4)
\<close>

end

ML \<open>
val n_theory = MyData.get (Context.Theory @{theory})
val _ = @{assert} (n_theory = 4)
val n_aux = MyData.get (Context.Proof @{context})
val _ = @{assert} (n_aux = 4)
\<close>


subsection \<open>Excurse on Proof Context vs. Local Theory.\<close>

text \<open>
A local theory is represented as a proof context. So a local theory is a semantic subtype of
a proof context. Every local theory is a proof context but not every proof context is a local
theory. In particular a local theory is a proof context that is ready to accept (local theory) 
definitions (@{ML Local_Theory.define}) and notes (@{ML Local_Theory.note}).

The Isabelle sources try to be consistent in the naming, i.e. 'ctxt' vs 'lthy' in
parameters and variables and @{ML_type "Proof.context"} vs. @{ML_type "local_theory"} in signatures. 
But as @{ML_type "local_theory"} is only a type synonym for @{ML_type "Proof.context"},
there is no type check for this convention. The nesting level that you get with 
@{ML "Local_Theory.level"} is an indicator. A Level of \<open>0\<close> is not a proper local theory. 
\<close>

text \<open>With @{ML Proof_Context.init_global} you get a proof context not a local theory.\<close>

ML_val \<open>
val ctxt = Proof_Context.init_global @{theory}
val level = Local_Theory.level ctxt
val is_theory = Named_Target.is_theory ctxt
val locale = Named_Target.locale_of ctxt
val bottom_locale = Named_Target.bottom_locale_of ctxt
\<close>

text \<open>With @{ML Named_Target.theory_init} you get a local theory.\<close>
ML_val \<open>
val lthy = Named_Target.theory_init @{theory}
val level = Local_Theory.level lthy
val is_theory = Named_Target.is_theory lthy
val locale_of = Named_Target.locale_of lthy
val bottom_locale = Named_Target.bottom_locale_of lthy
\<close>

text \<open>With @{ML Locale.init} you get a proof context not a local theory.\<close>
ML_val \<open>
val ctxt = Locale.init (Locale.intern @{theory} "Foo") @{theory}
val level = Local_Theory.level ctxt
val is_theory = Named_Target.is_theory ctxt
val locale_of = Named_Target.locale_of ctxt
val bottom_locale = Named_Target.bottom_locale_of ctxt
\<close>

text \<open>With @{ML Named_Target.init} you get a local theory.\<close>
ML_val \<open>
val lthy = Named_Target.init [] (Locale.intern @{theory} "Foo") @{theory}
val level = Local_Theory.level lthy
val is_theory = Named_Target.is_theory lthy
val locale_of = Named_Target.locale_of lthy
val bottom_locale = Named_Target.bottom_locale_of lthy
\<close>


subsection \<open>Attributes vs. Local Theory Declarations\<close>

text \<open>Attributes on local facts, are not applied on the underlying theory level foundation.
Only when you interpret a locale on the theory level the attributes get activated.
This corresponds to general @{ML Local_Theory.declaration} where you have the flag \<open>pervasive=false\<close>.

To demonstrate this we define an artificial tracing attribute.
\<close>

attribute_setup trace_attr =
\<open>
Attrib.thms >> (fn ths =>
  Thm.declaration_attribute 
    (fn thm => fn context =>
       let
         val (kind, level, is_theory, locale, bottom_locale) = case context of 
                 Context.Proof ctxt => 
                    let 
                      val level = Local_Theory.level ctxt 
                    in 
                     (if level = 0 then "context" else "local_theory", 
                      string_of_int level, 
                      @{make_string} (Named_Target.is_theory ctxt), 
                      @{make_string} (Named_Target.locale_of ctxt), 
                      @{make_string} (Named_Target.bottom_locale_of ctxt)) 
                    end
               | _ => ("theory", "0", "true", "NONE", "NONE")

         val _ = tracing ("trace_attr (" ^ kind ^ ", " ^ level ^ ", " ^ 
           is_theory ^ ", " ^ locale ^  ", " ^ bottom_locale ^ "): " ^ 
           Thm.string_of_thm (Context.proof_of context) thm)
       in context end))
\<close>



text \<open>First we try the attribute on a theory level theorem.
When you put the cursor on or after the \<open>simp\<close> you see the tracing output of our
attribute.\<close>
lemma foo[trace_attr]: "x = x"
  by simp

text \<open>Interestingly we see four tracing outputs. Here the outputs and my interpretation:
\<^item> \<open>trace_attr (local_theory, 1, true, NONE, NONE): ?x = ?x\<close> 
  This seems to be the immediate auxiliary context of the lemma.
\<^item> \<open>trace_attr (theory, 0, true, NONE, NONE): ?x = ?x\<close>
  This is the theory level.
\<^item> \<open>trace_attr (context, 0, false, NONE, NONE): ?x = ?x\<close> 
  This seems to be a theory-context that might be generated with @{ML Proof_Context.init_global}.
\<^item> \<open>trace_attr (local_theory, 1, true, NONE, NONE): ?x = ?x\<close>
  This seems to be from reentering the original lemma context.
 \<close>


text \<open>Now let us look at a nested context.\<close>
context Foo
begin
context
begin
lemma silly[trace_attr]: "M = M" by simp
end
end

text \<open>As you see there is no theory level trace:
\<^item> \<open>trace_attr (local_theory, 2, false, NONE, SOME "Scratch.Foo"): M = M  [Foo N M] \<close>
  This is the original context of the lemma.
\<^item> \<open>trace_attr (context, 0, false, NONE, SOME "Scratch.Foo"): M = M  [Foo N M]\<close> 
  This seems to be the target context but not as a local theory. 
\<^item> \<open>trace_attr (local_theory, 1, false, SOME "Scratch.Foo", SOME "Scratch.Foo"): M = M  [Foo N M]\<close>
  This seems to be the target context as a local theory. 
\<^item> \<open>trace_attr (local_theory, 2, false, NONE, SOME "Scratch.Foo"): M = M  [Foo N M]\<close>
  This seems to be from reentering the original lemma context.
\<close>

text \<open>Let us now try an interpretation of the locale on the theory level.\<close>
definition NN::nat where "NN = 2"
definition MM::nat where "MM = 3"


interpretation Foo NN MM
  by (unfold_locales) (simp add: NN_def MM_def)

text \<open>We can see the trace of the activation of the attribute:
\<open>trace_attr (theory, 0, true, NONE, NONE): MM = MM\<close>
\<close>

section \<open>ML Antiquotations\<close>
text \<open>
The notion of quote / antiquote is related to lisps quotation and quasi-quotation mechanisms
or the notion of 'interpolation' that is used in the context of macros in other programming 
languages. In lisp, "everything is a list", in particular the program itself and you can 
dynamically evaluate a list. With quotation you can express that a list is meant to be plain
data and should not be immediately evaluated. With quasi-quotation you can build data which
inside uses a lisp-expression that evaluates / expands to some data that is inserted at that point.

This is a first intuition to understand ML antiquotations in Isabele/ML. An ML antiquotation
is something embedded into the Isabelle/ML program text, that is not itself plain ML, but
something that evaluates to a piece of ML text that is inserted in that position. A prominent
example is the term antiquotation, which transforms a logical term (presented in the inner-syntax)
of the logic, to the ML representation of that term. @{ML_type term}
\<close>

ML_val \<open>
\<^term>\<open>x + y\<close>
\<close>
text \<open>
The expansion takes place during compile time of the piece of Isabelle/ML. To be more precise it is
expanded already during lexing of Isabelle/ML. This is important to keep in mind when writing
your own antiquotations. The context you can refer to during the expansion of the antiquotation
is the context you have during the lexing phase. This design decision facilitates robustness and
predictability of the resulting ML code. Note that the expanded ML-code itself might of course
be dynamically used later on in various contexts, but it is always the same code.

The main interface to write your own ML antiquotations is @{ML_structure ML_Antiquotation}. The
more low-level (and more flexible) interface it is based on is @{ML ML_Context.add_antiquotation}.
The interface in @{ML_structure ML_Antiquotation} distinguishes the 
antiquotations into the variants  \<open>inline\<close>, \<open>value\<close> and \<open>special-form\<close>. 

The \<open>inline\<close> variant is the closest to the intuition of macro expansion. The inline-antiquotaton
yields a piece of ML-text that is literally inserted at the position of the antiquotation. The
term antiquotation is an example of this. @{ML \<open>\<^term>\<open>x + y\<close>\<close>}. It is implemented with
@{ML ML_Antiquotation.inline_embedded}. 

\<^footnote>\<open>Note that there is also a variant without the 'embedded'.
suffix @{ML ML_Antiquotation.inline}. What is the difference? According to a mail thread
\<^url>\<open>https://lists.cam.ac.uk/mailman/htdig/cl-isabelle-users/2021-October/msg00023.html\<close> the 'embedded'
is a hint to Isabelle that antiquotation expects its argument as an 'embedded language' enclosed
by a cartouche. This can nowadays be considered as the canonical way. Historically, Isabelle
first distinguished between the outer-syntax (e.g. Isar or plain ML as Meta-Language) and the 
inner-syntax of the object logic like HOL or FOL. Meanwhile Isabelle embraces a lot of different 
languages that in some cases can even be nested, and the languages can be 
dynamically extended by declaring new commands or antiquotations.\<close>

For the \<open>value\<close> variant the intuition is that the expanded antiquotation is immediatly evaluated in the
compile time context and the resulting value is what is inserted at the position of 
the antiquotation. An example is the cterm antiquotation, e.g. @{ML \<open>@{cterm "a = b"}\<close>}.

Following the static nature of antiquotations this abstract value is produced statically during
compile time and is bound to some value as in \<open>val x = ...compile-time-context...\<close>, and then this
value \<open>x\<close> is what appears in the expanded ML text.
So to implement such an antiquotation means to provide two main ingredients: the code
for the value binding (referred to as environment) and the code to reference that value (referred
to as body). This is what the interface  @{ML ML_Antiquotation.declaration} offers. The 
argument @{ML_type "Proof.context -> string * string"} is the central point. The pair of
strings denotes the ML-text for the environment and the body respectively. See for
example the theorem antiquotation: @{ML \<open>@{thm refl}\<close>}. This can also be considered a \<open>value\<close> 
antiquotation, albeit being implemented by the more low-level interface.

Digging even deeper into @{ML ML_Context.add_antiquotation} the @{ML_type ML_Context.decl} also
refers to a pair of ML-code, denoting an environment and the body, but here presented as 
@{ML_type \<open>ML_Lex.token list\<close>} not as a string. This interface gives a lot of flexibility into
the design of antiquotations. A notable example is the 'instantiate'-antiquotation. e.g:
\<close>
ML_val \<open>
fun foo t =
 \<^instantiate>\<open>'a =\<^typ>\<open>nat\<close> and a =\<^term>\<open>s::nat\<close> and b = t in  
   prop \<open>a + b = b + a\<close> for a b::\<open>'a::plus\<close>\<close> 
\<close>
text \<open>
Note the nesting of antiquotations in that example. The 'environment-part' here consists of all the
right hand sides of the instantiations as well as the proposition. The 'body-part' is an ML-expression 
that instantiates the proposition with the terms. The body part cannot be immediately evaluated
during compile time as the value of parameter \<open>t\<close> of the function is not yet known. So the
result is an ML-expression that references \<open>t\<close> among the right and sides of the instantiations
that are evaluated at compile time.


The special-form antiquotation packs the text in a function thunk, e.g. @{ML \<open>\<^try>\<open>I\<close>\<close>}.
\<close>

section \<open>Markup and Reports\<close>

text \<open>
Isabelle provides a rich set of markup to display information in Isabelle/jEdit.
Markup can either be directly attached to a string, or an existing source text can be decorated
by sending \<^emph>\<open>reports\<close> to PIDE.
An example for direct markup is the printing of terms, e.g.:
\<close>
ML \<open>
val str = Syntax.string_of_term @{context} @{term "a + b"}
\<close>
text \<open>You can make the markup visible by sending it to an output function, e.g.\<close>
ML \<open>
tracing str
\<close>
text \<open>The markup is itself encoded in the string by the format @{ML_structure YXML}
The plain information (without markup) can be extracted:
\<close>
ML_val \<open>
YXML.content_of str
\<close>
text \<open>The markup can be expanded to the @{ML_type XML.tree} by @{ML YXML.parse}\<close>
ML_val \<open>
YXML.parse str
\<close>

text \<open>
To build up markup you can use @{ML_structure Markup}. The type for markup is a pair of
element name and a list of properties. A property @{ML_type Properties.T} is a key value pair which
are both strings. First you build up your markup by using the various functions supplied in
@{ML_structure Markup}, then you attach it to a string via @{ML Markup.markup}.
\<close>


ML_val \<open>
val m = Markup.url "http:\\www.isabelle.in.tum.de"
val decorated = Markup.markup m "attach url to this string"
val xml = YXML.parse decorated
\<close>

text \<open>With @{ML Position.report} you can add markup to a given position, e.g. here we
add the warning-twigglies and an url:\<close>

ML_val \<open>
val pos = Position.range_position (Position.range (\<^here>,    \<^here>))
val w = Markup.warning
val u = Markup.url "http:\\\\www.isabelle.in.tum.de"
val _ = Position.report pos w
val _ = Position.report pos u
\<close>


text \<open>The standard message channels @{ML error}, @{ML warning} and @{ML tracing} scan
the string for position information and automatically markup the position.
\<close>

ML_val \<open>
val this_spot = \<^here> (* wiggly line *)
val msg = "Look here: " ^ Position.here this_spot
val _ = warning msg
\<close>

text \<open>There are some fine points regarding the command region were the message is issued.
By default markup is only shown in the actual command region.\<close>
ML \<open>
val this_spot_is_not_marked = \<^here> (* no wiggly line *)
val msg1 = "Look here: " ^ Position.here this_spot_is_not_marked
\<close>

text \<open>We do not get the wiggly lines in the @{command ML} above, instead the @{command ML_val}\<close>
ML_val (* wiggly line *) \<open>
val _ = warning msg1
\<close>

text \<open>We can put markup to a previous command if we first safe the command position of the
first command, and temporary use this in the second command when issuing the message.\<close>

ML \<open>
val command_thread_position = Position.thread_data ();
val this_spot_is_marked = \<^here> (* wiggly line *)
val msg2 = "Look here: " ^ Position.here this_spot_is_marked
\<close>

ML_val (* no wiggly line *) \<open>
val _ = Position.setmp_thread_data command_thread_position warning msg2
\<close>

text \<open>To inspect the markup attached to the source you can use the panel
Sidekick and select the language "isabelle-markup"
When you hover over an entity in the upper half of the panel you see the attached markup
in the lower half of the panel.

Reports are also used in autocorres @{ML_structure Feedback} to provide warning and error 
markup for C programs.
\<close>


text \<open>
An illustrative example for custom markup and reports can be seen in the document
antiquotation for rail diagrams:
is \<^file>\<open>$ISABELLE_HOME/src/Pure/Tools/rail.ML\<close>. It is used extensively in the Isabelle 
documentation, watch out for \<^verbatim>\<open>\<^rail>\<open>\<close>\<close> e.g. in 
 \<^file>\<open>$ISABELLE_HOME/src/Doc/Datatypes/Datatypes.thy\<close>
\<close>


section \<open>Term Synthesize via Intro Rules\<close>

text \<open>A repeated task in the various AutoCorres phases is to synthesize a typically more abstract 
monadic function (output) from a given monadic function (input) together with a simulation theorem 
that connects both versions of the function. One strategy is to formulate introduction rules
for the correspondence relation for the different language constructs and then recursively
apply those rules guided by the constructs in the "input" function, and as a side effect of
the rule application to synthesize the "output" function. 
Examples are, heap abstraction, word abstraction, exception rewriting (as described above) and 
type strengthening. Currently there is not (yet) an uniform implementation of this strategy, but
the different instances are converging.
Currently the most recent incarnation is the setup for type strengthening to perform the
\<^const>\<open>refines\<close> proofs:
\<^item> A term net is used for efficient lookup of potentially matching rules. It is indexed by the
  input function as well as the desired result relation.
\<^item> Splitting of tuples in rules is automatically performed to match the current term.
\<^item> Priorities of rules are specified to guarantee that the most specific rules are tried first
\<^item> A cache is used both for positive and negative proof attempts. 
  As there might be multiple applicable rules when decomposing the input function, 
  partial results might already be proven or have failed.
  Using a cache helps to prune repeated subproof attempts.

The setup for this phase can be found in \<^file>\<open>../Refines_Spec.thy\<close>. It employs 
@{command synthesize_rules}, as defined in \<^file>\<open>../lib/ml-helpers/Synthesize.thy\<close>.
This command can be seen as generalisation of @{command named_theorems}, with support for
the kind of features just sketched.

For a set of @{command synthesize_rules} you can generate patterns to support indexing of rules
via subterms: @{command add_synthesize_pattern}.

With @{command print_synthesize_rules} you can inspect the set:
\<close>

print_synthesize_rules pure

text \<open>You can also supply an term to select the matching rules:\<close>

print_synthesize_rules pure \<open>Trueprop (refines_spec (L2_try f) _ (return ?f') _ (rel_prod rel_liftE (=)))\<close>

text \<open>Rules are added via attribute @{attribute synthesize_rule}, where you can also specify the rule sets
the priority and whether to split some variables. In order to preserve the theorem name
for debugging purposes you should apply that attribute in a separate @{command lemmas} and
not directly in the original @{command lemma}\<close>

text \<open>
The main tactic to drive application of those rules is @{ML "CT.cache_deepen_tac"}. This
tactic has type @{ML_type context_tactic} and supports implementing a cache within the 
@{ML_type Proof.context}. The user provides a cache and a single-step tactic that is
recursively tried on the emerging subgoals.

The interface of the cache is captured in record @{ML_type CT.ctxt_cache}:
\<^item> @{ML \<open>#lookup: CT.ctxt_cache -> Proof.context -> cterm -> int -> context_tactic\<close>}
  The lookup function gets the goal presented as a @{ML_type cterm} and returns a subgoal tactic.
  A cache miss is implemented by @{ML "K CT.no_tac"}.
\<^item> @{ML \<open>#insert: CT.ctxt_cache -> (Timing.timing * int * int) -> thm -> Proof.context -> Proof.context\<close>}
  The insert functions gets timing information tupled with the total number of alternatives and the current alternative
  as input together with the just proven subgoal. It can use that information to decide whether to
  really extend the cache or to ignore the result.
\<^item> @{ML \<open>#propagate: CT.ctxt_cache -> Proof.context -> Proof.context -> Proof.context\<close>}
  To propagate the cache throughout backtracking the propagate function is supplied. It gets
  the current context and the old context as argument and can propagate the cache from the
  current context to the old one (to which it backtracks).

The cache used for the type strengthening phase is implemented in @{ML Monad_Convert.sim_nondet}.
It is based on @{ML Synthesize_Rules.gen_cond_cache}. 
It uses a term net to index the cached results and only adds rules for compound statements
like \<^const>\<open>L2_seq\<close>, not for atomic ones. The idea here is that proving simulation for an
atomic statement is just a single rule application and is thus not worth to be cached.

Failed proof attempts are represented by @{thm ex_falso_quodlibet} instantiated with the failed
subgoal. This is how they are presented to the cache and can be stored. When a cache lookup is performed and
the cache results in such an instance of @{thm ex_falso_quodlibet} which matches the current
subgoal the proof attempt will be immediately aborted at that depth and 
potential alternative proof steps 'higher up' (smaller depth) may get explored. 
\<close>

text \<open>
Next we illustrate the approach with a small example.
\<close>

lemma refines_liftE_nondet: "refines (liftE f) f s s (rel_prod rel_liftE (=))"
  by (auto simp add: refines_def_old reaches_liftE)

lemma refines_L2_unknown:
  shows "refines (L2_unknown ns) (L2_VARS (select UNIV) ns) s s (rel_prod rel_liftE (=))"
  by (rule Refines_Spec.refines_L2_unknown_nondet)

lemmas refines_spec_monad_rules =
  refines_L2_seq_nondet [simplified THIN_def]
  refines_L2_gets_nondet
  refines_L2_unknown

lemmas refines_option_monad_rules =
  refines_L2_seq_option [simplified THIN_def]
  refines_L2_gets_option

schematic_goal \<open>refines ( L2_seq (L2_gets (\<lambda>_. n::nat) []) (\<lambda>n. L2_gets (\<lambda>_. n + m) [])) (?f'::(?'c , 'a) res_monad) ?s ?s ?R\<close>

  apply (rule refines_spec_monad_rules)
   prefer 2 
   \<comment>\<open>Note that @{ML "CT.cache_deepen_tac"} follows the convention of tactics to solve subgoals from the back.
     So the second subgoal is solved first. \<close>
   apply (rule refines_spec_monad_rules)
  apply (rule refines_spec_monad_rules)
  done

text \<open>First we define the single-step tactics, which just try some rules.\<close>
ML \<open>
fun get_nondet_tacs goal = @{thms refines_spec_monad_rules} 
  |> map (fn thm => (Utils.guess_binding_of_thm @{context} thm, thm))
  |> CT.binding_resolve_tac  

fun get_option_tacs goal =  @{thms refines_option_monad_rules}  
  |> map (fn thm => (Utils.guess_binding_of_thm @{context} thm, thm))
  |> CT.binding_resolve_tac  


fun get_all_tacs goal = get_option_tacs goal @ get_nondet_tacs goal
\<close>

text \<open>Now we define a simple cache which stores all emerging subgoals in a list and tries
to resolve with those subgoals on a lookup.\<close>
ML \<open>
structure List_Cache = Proof_Data (
  type T = thm list 
  val init = K [])

val list_cache:CT.ctxt_cache = {
  lookup = fn ctxt => fn goal =>  
    let 
       val _  = tracing ("lookup: " ^ Syntax.string_of_term ctxt (Thm.term_of goal))
    in
      CT.resolve_tac (List_Cache.get ctxt)
    end,
  insert = fn timing => fn thm => fn ctxt => 
    let
      val thm' = thm |> Thm.forall_elim_vars ((Thm.maxidx_of thm) + 1) |> zero_var_indexes
      val _ = tracing ("insert: " ^ Thm.string_of_thm ctxt thm') 
    in
      ctxt |> List_Cache.map (cons thm') 
    end,
  propagate = fn current => fn old => current
  }
\<close>


text \<open>We only try nondet-rules, so we end up in the nondet monad.\<close>
schematic_goal 
\<open>refines ( L2_seq (L2_gets (\<lambda>_. n::nat) []) (\<lambda>n. L2_gets (\<lambda>_. n + m) [])) 
  (?f'::(?'c, 'a) res_monad) ?s ?s ?R\<close>
  apply (tactic \<open>
    Context_Tactic.NO_CONTEXT_TACTIC @{context} (
    CT.cache_deepen_tac (K 1) list_cache get_nondet_tacs 1
   )\<close>)
  done

schematic_goal 
\<open>refines ( L2_seq (L2_gets (\<lambda>_. n::nat) []) (\<lambda>n. L2_gets (\<lambda>_. n + m) [])) (?f'::(?'c, 'a) res_monad) ?s ?s ?R\<close>
  thm refines_option_monad_rules
  apply (rule  refines_option_monad_rules)
   apply (rule  refines_option_monad_rules)
  apply (rule  refines_option_monad_rules)
  done


text \<open>We only try the option-rules, so we end up in the option monad.\<close>
schematic_goal 
\<open>refines ( L2_seq (L2_gets (\<lambda>_. n::nat) []) (\<lambda>n. L2_gets (\<lambda>_. n + m) [])) (?f'::(?'c, 'a) res_monad) ?s ?s ?R\<close>
  apply (tactic \<open>
    Context_Tactic.NO_CONTEXT_TACTIC @{context} (
    CT.cache_deepen_tac (K 1) list_cache get_option_tacs 1
   )\<close>)
  done

text \<open>No we try both the option-rules and the nondet-rules. As the option rules come first
we end up in the option monad\<close>
schematic_goal 
\<open>refines ( L2_seq (L2_gets (\<lambda>_. n::nat) []) (\<lambda>n. L2_gets (\<lambda>_. n + m) [])) (?f'::(?'c, 'a) res_monad) ?s ?s ?R\<close>
  apply (tactic \<open>
    Context_Tactic.NO_CONTEXT_TACTIC @{context} (
    CT.cache_deepen_tac (K 1) list_cache get_all_tacs 1
   )\<close>)
  done


text \<open>By including a \<^const>\<open>L2_unknown\<close> in the example we have to end up in the nondet monad, as
it cannot be handled in the option monad. Note the difference in the outcome of the fist and
second proof attempt. In the first one we only provide the nondet-rules in the second one we
also provide the option-rules. This results in a different "translation" of the first \<^const>\<open>L2_gets\<close>.\<close>

schematic_goal 
\<open>refines ( L2_seq (L2_gets (\<lambda>_. n::nat) []) (\<lambda>n. L2_unknown [])) (?f'::( ?'c, 'a) res_monad) ?s ?s ?R\<close>
  apply (tactic \<open>
    Context_Tactic.NO_CONTEXT_TACTIC @{context} (
    CT.cache_deepen_tac (K 1) list_cache get_all_tacs 1
   )\<close>)
  done


schematic_goal 
\<open>refines ( L2_seq (L2_gets (\<lambda>_. n::nat) []) (\<lambda>n. L2_unknown [])) (?f'::(?'c, 'a) res_monad) ?s ?s ?R\<close>
  apply (tactic \<open>
    Context_Tactic.NO_CONTEXT_TACTIC @{context} (
    CT.cache_deepen_tac (K 1) list_cache get_nondet_tacs 1
   )\<close>)
  done

end
