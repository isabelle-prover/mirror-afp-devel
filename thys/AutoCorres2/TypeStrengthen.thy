(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Strengthen functions into simpler monads.
 *
 * Each block of lifting lemmas converts functions in the "L2" monadic
 * framework (an exception framework) into its own framework.
 *)

theory TypeStrengthen
imports
  Refines_Spec
begin


(* Set up the database and ts_rule attribute. *)
ML_file "monad_types.ML"

lemma gets_the_ogets_return_conv [fun_ptr_simps]: "gets_the (ogets (\<lambda>_. f)) = return f"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff ogets_def)
  done

lemma gets_the_ogets_gets_conv [fun_ptr_simps]: "gets_the (ogets f) = gets f"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff ogets_def)
  done

lemma gets_the_ogets: "gets_the (ogets f) = gets f"
  apply (simp add: gets_the_def assert_opt_def[abs_def] ogets_def gets_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma gets_the_obind:
  "gets_the (f |>> g) = gets_the f >>= (\<lambda>x. gets_the (g x))"
  apply (simp add: obind_def)
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto split: option.splits)
  done

lemma gets_the_oguard: "gets_the (oguard P) = guard P"
  apply (simp add: oguard_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma gets_the_ocondition:
  "gets_the (ocondition P f g) = condition P (gets_the f) (gets_the g)"
  apply (simp add: ocondition_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


(* FIXME: move to AutoCorresInfrastructure? *)
(* FIXME: update description *)
text \<open>
A best-effort approach to determine the simplest possible 'monad' for the final definition 
is implemented. We first try to define a function 
into the most restrictive monad and if that fails successively try more expressive monads until
we finally hit the most expressive monad.
In the original autocorres version this phase was based on equations and not on  
on a simulation relation as all the other autocorres phases.
With the switch to model recursive functions with a CCPO @{command fixed_point} instead 
of @{command function} with an explicit measure parameter this did no longer work, as equations
are not @{const ccpo.admissible}. Fortunately simulation is admissible, so we
changed this phase to @{const refines}, cf: \<^file>\<open>Refines_Spec.thy\<close>.
So the main purpose of this theory is to set up the available target monads 
by applying some meta information: \<^file>\<open>monad_types.ML\<close>.



The correspondence equations have the format:

(*) @{term "p = L2_call_lift p'"}

where @{term "L2_call_lift"} depends on the (simpler) target monad and lifts the program @{term p'} 
from that simpler monad to the fully fledged monad we start with:
 
The program @{term p} is the definition we have from the last layer of autocorres (WA).
The final definition will refer to @{term p'}. 

For the code to work @{term "L2_call_lift"} has to be a distinct constant, as some matching is
performed on that assumption. That is why some new definitions are introduced below.

Note that the final (most expressive) monad is characterised by the 
lifting function is @{const lift_exit_status} which merely removes the exception handling artefact
from SIMPL by extracting the exception value @{typ 'a} from @{typ "'a c_exntype"}. So it should
be sufficiently expressive for any input C program.


When the proof for a certain monad fails it can either have a good reason (as the input
function is just not expressible in that particular monad) or it can fail because the 
implementation is missing some rules.

Note some peculiarities on the current state of affairs:
\<^item> When a guard remains (e.g. bounds for an integer) you end up at least in the option monad 
  (to model the possible failure).
\<^item> As recursive functions are currently implemented with @{command fixed_point} they are
  at least in the option monad.
\<close>



(*
 * Lifting into pure functional Isabelle.
 *)

setup \<open>
Monad_Types.new_monad_type
  "pure"
  "Pure function"
  "" (* unused ccpo_name for recursive definitions *)
  100
  #resT
  (fn _ => fn _ => error "monad_type pure: there is no previous monad to lift from")
  {rules_name = @{synthesize_rules_name pure}, 
   relator = @{term "rel_liftE::('a, 'b) xval \<Rightarrow> 'b val \<Rightarrow> bool"}, 
   relator_from_c_exntype = NONE, lift = @{term "return"}, 
      dest_lift = (fn @{term_pat "return ?x"} => SOME x | _ => NONE),
   lift_prev = []}
|> Context.theory_map
\<close>


(*
 * Lifting into pure functional Isabelle with state.
 *)

setup \<open>
Monad_Types.new_monad_type
  "gets" (* reader monad *)
  "Read-only function"
  "" (* unused ccpo_name for recursive definitions *)
  80
  (fn {stateT, resT, exT} => stateT --> resT)
  (fn _ => fn stateT => let fun lift t = Abs ("_", stateT, t) in Utils.lift_result_with_arity 0 lift end)
  {rules_name = @{synthesize_rules_name reader}, 
   relator = @{term "rel_liftE::('a, 'b) xval \<Rightarrow> 'b val \<Rightarrow> bool"},
   relator_from_c_exntype = NONE, lift = @{term gets}, 
   dest_lift = (fn @{term_pat "gets ?x"} => SOME x | _ => NONE),
   lift_prev = @{thms refines_lift_pure_reader}}
|> Context.theory_map
\<close>


(*
 * Lifting into option monad.
 *)

lemma monotone_L2_VARS [partial_function_mono]:  
  "monotone R X a \<Longrightarrow> monotone R X (\<lambda>f. L2_VARS (a f) ns)"
  by (simp add:  L2_VARS_def)


lemma monotone_ocondition [partial_function_mono]:
  assumes mono_X: "monotone R (fun_ord Q) X"
  assumes mono_Y: "monotone R (fun_ord Q) Y"
  shows "monotone R (fun_ord Q) 
    (\<lambda>f. (ocondition C (X f) (Y f)))"
  using mono_X mono_Y unfolding ocondition_def monotone_def fun_ord_def
  by auto

declare Complete_Partial_Order2.option.preorder [partial_function_mono]

(*
lemma monotone_ocondition_option_le_fun [partial_function_mono]:
  assumes mono_X: "monotone R option.le_fun X"
  assumes mono_Y: "monotone R option.le_fun Y"
  shows "monotone R option.le_fun 
    (\<lambda>f. (ocondition C (X f) (Y f)))"
  using mono_X mono_Y unfolding ocondition_def monotone_def 
  by (auto simp add: flat_ord_def fun_ord_def split: option.splits)
 *)

lemma monotone_obind[partial_function_mono]:
  "monotone R option.le_fun a \<Longrightarrow> (\<And>x. monotone R option.le_fun (\<lambda>f. b f x)) \<Longrightarrow>
    monotone R option.le_fun (\<lambda>f. obind (a f) (b f))"
  unfolding monotone_def obind_def
  apply (clarsimp simp add: flat_ord_def fun_ord_def split: option.splits)
  by (metis option.sel option.simps(3))

lemma monotone_option_fun_const [partial_function_mono]:
 "monotone R option.le_fun (\<lambda>f. c)"
  by (auto simp add: monotone_def flat_ord_def fun_ord_def)

lemma option_while_eq_Some:
  "option_while C B I = Some F \<longleftrightarrow> (Some I, Some F) \<in> option_while' C B"
  using option_while'_THE by (force simp: option_while_def)

lemma option_while'_monotone:
  assumes B: "\<And>r. flat_ord None (B r) (B' r)"
  assumes b: "(a, b) \<in> option_while' C B" "b \<noteq> None" shows "(a, b) \<in> option_while' C B'"
  using b
proof induction
  case (step r1 r2 s) then show ?case
    by (metis B flat_ord_def option.simps(2) option_while'.intros(3))
qed (auto intro: option_while'.intros)
lemma monotone_option_while[partial_function_mono]:
  assumes B: "\<And>a. monotone R (flat_ord None) (\<lambda>f. B f a)"
  shows "monotone R (flat_ord None) (\<lambda>f. option_while C (B f) I)"
proof
  fix x y assume "R x y"
  show "option_ord (option_while C (B x) I) (option_while C (B y) I)"
    unfolding flat_ord_def
  proof (intro disjCI2)
    assume "option_while C (B x) I \<noteq> None"
    then obtain F where "option_while C (B x) I = Some F" by auto
    then have x: "(Some I, Some F) \<in> option_while' C (B x)"
      by (auto simp: option_while_eq_Some)
    have "(Some I, Some F) \<in> option_while' C (B y)"
      using B \<open>R x y\<close> by (intro option_while'_monotone[OF _ x]) (auto simp: monotone_def)
    with x show "option_while C (B x) I = option_while C (B y) I"
      unfolding option_while_eq_Some[symmetric] by simp
  qed
qed

lemma monotone_owhile[partial_function_mono]:
  "(\<And>a. monotone R option.le_fun (\<lambda>f. B f a)) \<Longrightarrow>
    monotone R option.le_fun (\<lambda>f. owhile C (B f) I)"
  unfolding owhile_def monotone_fun_ord_apply
  by (intro allI monotone_option_while) simp


setup \<open>
let open Mutual_CCPO_Rec in
  add_ccpo "option_state_monad" (fn ctxt => fn T =>
    let
      val oT = range_type T
    in
      synth_fun ctxt (domain_type T) (synth_option ctxt oT)
    end)
  |> Context.theory_map
end
\<close>

lemma refines_lift_pure_option:
  assumes f: "refines f (return f') s s (rel_prod rel_liftE (=))"
  shows "refines f (gets_the (oreturn f')) s s (rel_prod rel_liftE (=))"
  using f
  apply (auto simp add: refines_def_old)
  done



setup \<open>
Monad_Types.new_monad_type
  "option"
  "Option monad"
  "option_state_monad"
  60
  (fn {stateT, resT, exT} =>
     stateT --> Term.map_atyps (fn T => if T = @{typ "'a"} then resT else T) @{typ "'a option"})
  (fn ctxt => fn _ => let fun lift t = \<^infer_instantiate>\<open>t = t in term \<open>ogets t\<close>\<close> ctxt
                      in Utils.lift_result_with_arity 1 lift end)
  {rules_name = @{synthesize_rules_name option}, 
   relator = @{term "rel_liftE::('a, 'b) xval \<Rightarrow> 'b val \<Rightarrow> bool"}, 
    relator_from_c_exntype = NONE, lift = @{term gets_the},
    dest_lift = (fn @{term_pat "gets_the ?x"} => SOME x | _ => NONE),
   lift_prev = @{thms refines_lift_pure_option refines_lift_reader_option}}
|> Context.theory_map
\<close>



(*
 * Lifting into the nondeterministic state monad.
 * All L2 terms can be lifted into it.
 *)

setup \<open>
Monad_Types.new_monad_type
  "nondet"
  "Nondeterministic state monad"
  "spec_monad_gfp"
  20
  (fn {stateT, resT, exT} =>
     Term.map_atyps (fn T => if T = @{typ "'a"} then resT
                               else if T = @{typ "'s"} then stateT else T)
       @{typ "('a, 's) res_monad"})
  (fn ctxt => fn _ => let fun lift t = \<^infer_instantiate>\<open>t = t in term \<open>gets_the t::('a, 's) res_monad\<close>\<close> ctxt in Utils.lift_result_with_arity 1 lift end)
  {rules_name = @{synthesize_rules_name nondet}, 
   relator = @{term "rel_liftE::('a, 'b) xval \<Rightarrow> 'b val \<Rightarrow> bool"},
   relator_from_c_exntype = NONE, lift = @{term \<open>\<lambda>x. x\<close>},
   dest_lift = (fn _ => NONE),
   lift_prev = []}
|> Context.theory_map
\<close>

setup \<open>
Monad_Types.new_monad_type
  "exit"
  "Nondeterministic state monad with exit (default)"
  "spec_monad_gfp"
  10
  (fn {stateT, resT, exT} =>
     Term.map_atyps (fn T => if T = @{typ "'a"} then resT
                             else if T = @{typ "'s"} then stateT 
                             else if T = @{typ "'e"} then HP_TermsTypes.strip_c_exntype exT
                             else T)
       @{typ "('e, 'a, 's) exn_monad"})
  (fn ctxt => fn _ => let fun lift t = \<^infer_instantiate>\<open>t = t in term \<open>liftE t:: (exit_status, 'a, 's) exn_monad\<close>\<close> ctxt in Utils.lift_result_with_arity 0 lift end)
  {rules_name = @{synthesize_rules_name exit}, 
    relator = @{term \<open>rel_xval (=) (=)\<close>}, 
    relator_from_c_exntype = SOME @{term \<open>rel_xval rel_Nonlocal (=)\<close>}, lift = @{term \<open>\<lambda>x. x\<close>},   
    dest_lift = (fn _ => NONE),
   lift_prev = []}
|> Context.theory_map
\<close>


lemma id_comps: 
  "id o f = f" 
  "((\<lambda>s. s) o f) = f"
  by (simp_all add: comp_def)

lemma gets_bind_ign: "gets f >>= (\<lambda>x. m) = m"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

end
