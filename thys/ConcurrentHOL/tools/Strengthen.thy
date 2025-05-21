(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

text\<open>

A tactic for applying monotonicity facts in term contexts.
 \<^item> think \<open>subst\<close> but for inequations
 \<^item> from \<^url>\<open>https://github.com/seL4/l4v/blob/master/lib/Monads/Strengthen.thy\<close> with minor changes:
  \<^item> discarded the \<open>strengthen_implementation\<close> locale
   \<^item> \<open>named_theorems\<close> is more pleasant
  \<^item> nuked fancy syntax
  \<^item> added rules for lattice operators (etc)

Limitations:
 \<^item> does not handle \<open>using\<close> facts well
 \<^item> does not handle eta-expanded/contracted things too well
 \<^item> loops if there are schematics in the goal
 \<^item> \<open>mk_strg\<close> doesn't work with lhs/rhs opts intended to handle less_eq

\<close>

theory Strengthen
imports Main
begin

lemma mono_image:
  shows "mono ((`) f)"
by (rule monoI) blast

lemma mono_vimage:
  shows "mono ((-`) f)"
by (rule monoI) blast

lemma antimono_uminus_boolean_algebra:
  shows "antimono (\<lambda>X::_::boolean_algebra. -X)"
by (rule antimonoI) simp

lemma mono_minus_boolean_algebra:
  fixes x :: "_::boolean_algebra"
  assumes "x \<le> x'"
  assumes "y' \<le> y"
  shows "x - y \<le> x' - y'"
by (metis assms compl_le_compl_iff diff_eq inf.mono)

lemma mono_lfp:
  shows "mono lfp"
by (rule monoI) (simp add: le_fun_def lfp_mono)

text \<open>Implementation of the @{text strengthen} tool and the @{text mk_strg}
attribute. See the theory @{text Strengthen_Demo} for a demonstration.\<close>

definition st :: "bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "st P rel x y = (x = y \<or> (P \<and> rel x y) \<or> (\<not> P \<and> rel y x))"

definition st_prop1 :: "prop \<Rightarrow> prop \<Rightarrow> prop" where
  "st_prop1 (PROP P) (PROP Q) \<equiv> (PROP Q \<Longrightarrow> PROP P)"

definition st_prop2 :: "prop \<Rightarrow> prop \<Rightarrow> prop" where
  "st_prop2 (PROP P) (PROP Q) \<equiv> (PROP P \<Longrightarrow> PROP Q)"

definition st_failed :: bool where
  "st_failed \<longleftrightarrow> True"

definition st_elim :: "prop \<Rightarrow> prop" where
 "st_elim (P :: prop) \<equiv> P"

definition st_oblig :: "prop \<Rightarrow> prop" where
  "st_oblig (P :: prop) \<equiv> P"

(*
notation st_elim ("{elim| _ |}")
notation st_oblig ("{oblig| _ |}")
notation st_failed ("<strg-failed>")

syntax (ASCII)
  "_ap_strg_bool" :: "['a, 'a] => 'a"  ("_ =strg<--|=> _")
  "_ap_wkn_bool" :: "['a, 'a] => 'a"  ("_ =strg-->|=> _")
  "_ap_ge_bool" :: "['a, 'a] => 'a"  ("_ =strg<=|=> _")
  "_ap_le_bool" :: "['a, 'a] => 'a"  ("_ =strg>=|=> _")

syntax
  "_ap_strg_bool" :: "['a, 'a] => 'a"  ("_ =strg\<longleftarrow>|=> _")
  "_ap_wkn_bool" :: "['a, 'a] => 'a"  ("_ =strg\<longrightarrow>|=> _")
  "_ap_ge_bool" :: "['a, 'a] => 'a"  ("_ =strg\<le>|=> _")
  "_ap_le_bool" :: "['a, 'a] => 'a"  ("_ =strg\<ge>|=> _")

translations
  "P =strg\<longleftarrow>|=> Q" == "CONST st (CONST False) (CONST HOL.implies) P Q"
  "P =strg\<longrightarrow>|=> Q" == "CONST st (CONST True) (CONST HOL.implies) P Q"
  "P =strg\<le>|=> Q" == "CONST st (CONST False) (CONST Orderings.less_eq) P Q"
  "P =strg\<ge>|=> Q" == "CONST st (CONST True) (CONST Orderings.less_eq) P Q"

lemma failedI:
  "<strg-failed>"
  by (simp add: st_failed_def)
*)

lemma failedI:
  "st_failed"
  by (simp add: st_failed_def)

lemma strengthen_refl:
  "st P rel x x"
  by (simp add: st_def)

lemma st_prop_refl:
  "PROP (st_prop1 (PROP P) (PROP P))"
  "PROP (st_prop2 (PROP P) (PROP P))"
  unfolding st_prop1_def st_prop2_def
  by safe

lemma strengthenI:
  "rel x y \<Longrightarrow> st True rel x y"
  "rel y x \<Longrightarrow> st False rel x y"
  by (simp_all add: st_def)

lemmas imp_to_strengthen = strengthenI(2)[where rel="(\<longrightarrow>)"]
lemmas rev_imp_to_strengthen = strengthenI(1)[where rel="(\<longrightarrow>)"]
lemmas ord_to_strengthen = strengthenI[where rel="(\<le>)"]

lemma use_strengthen_imp:
  "st False (\<longrightarrow>) Q P \<Longrightarrow> P \<Longrightarrow> Q"
  by (simp add: st_def)

lemma use_strengthen_prop_elim:
  "PROP P \<Longrightarrow> PROP (st_prop2 (PROP P) (PROP Q))
    \<Longrightarrow> (PROP Q \<Longrightarrow> PROP R) \<Longrightarrow> PROP R"
  unfolding st_prop2_def
  apply (drule(1) meta_mp)+
  apply assumption
  done

lemma strengthen_Not:
  "st False rel x y \<Longrightarrow> st (\<not> True) rel x y"
  "st True rel x y \<Longrightarrow> st (\<not> False) rel x y"
  by auto

lemmas gather =
    swap_prems_eq[where A="PROP (Trueprop P)" and B="PROP (st_elim Q)" for P Q]
    swap_prems_eq[where A="PROP (Trueprop P)" and B="PROP (st_oblig Q)" for P Q]

lemma mk_True_imp:
  "P \<equiv> True \<longrightarrow> P"
  by simp

lemma narrow_quant:
  "(\<And>x. PROP P \<Longrightarrow> PROP (Q x)) \<equiv> (PROP P \<Longrightarrow> (\<And>x. PROP (Q x)))"
  "(\<And>x. (R \<longrightarrow> S x)) \<equiv> PROP (Trueprop (R \<longrightarrow> (\<forall>x. S x)))"
  "(\<And>x. (S x \<longrightarrow> R)) \<equiv> PROP (Trueprop ((\<exists>x. S x) \<longrightarrow> R))"
  apply (simp_all add: atomize_all)
  apply (rule equal_intr_rule)
   apply assumption
  apply assumption
  done

ML \<open>
structure Make_Strengthen_Rule = struct

fun binop_conv' cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2;

val mk_elim = Conv.rewr_conv @{thm st_elim_def[symmetric]}
val mk_oblig = Conv.rewr_conv @{thm st_oblig_def[symmetric]}

fun count_vars t = Term.fold_aterms
    (fn (Var v) => Termtab.map_default (Var v, 0) (fn x => x + 1)
        | _ => I) t Termtab.empty

fun gather_to_imp ctxt drule pattern = let
    val pattern = (if drule then "D" :: pattern else pattern)
    fun inner pat ct = case (head_of (Thm.term_of ct), pat) of
        (@{term Pure.imp}, ("E" :: pat)) => binop_conv' mk_elim (inner pat) ct
      | (@{term Pure.imp}, ("A" :: pat)) => binop_conv' mk_elim (inner pat) ct
      | (@{term Pure.imp}, ("O" :: pat)) => binop_conv' mk_oblig (inner pat) ct
      | (@{term Pure.imp}, _) => binop_conv' (Object_Logic.atomize ctxt) (inner (drop 1 pat)) ct
      | (_, []) => Object_Logic.atomize ctxt ct
      | (_, pat) => raise THM ("gather_to_imp: leftover pattern: " ^ commas pat, 1, [])
    fun simp thms = Raw_Simplifier.rewrite_wrt ctxt false thms
    fun ensure_imp ct = case strip_comb (Thm.term_of ct) |> apsnd (map head_of)
     of
        (@{term Pure.imp}, _) => Conv.arg_conv ensure_imp ct
      | (@{term HOL.Trueprop}, [@{term HOL.implies}]) => Conv.all_conv ct
      | (@{term HOL.Trueprop}, _) => Conv.arg_conv (Conv.rewr_conv @{thm mk_True_imp}) ct
      | _ => raise CTERM ("gather_to_imp", [ct])
    val gather = simp @{thms gather}
        then_conv (if drule then Conv.all_conv else simp @{thms atomize_conjL})
        then_conv simp @{thms atomize_imp}
        then_conv ensure_imp
  in Conv.fconv_rule (inner pattern then_conv gather) end

fun imp_list t = let
    val (x, y) = Logic.dest_implies t
  in x :: imp_list y end handle TERM _ => [t]

fun mk_ex (xnm, T) t = HOLogic.exists_const T $ Term.lambda (Var (xnm, T)) t
fun mk_all (xnm, T) t = HOLogic.all_const T $ Term.lambda (Var (xnm, T)) t

fun quantify_vars ctxt drule thm = let
    val (lhs, rhs) = Thm.concl_of thm |> HOLogic.dest_Trueprop
      |> HOLogic.dest_imp
    val all_vars = count_vars (Thm.prop_of thm)
    val new_vars = count_vars (if drule then rhs else lhs)
    val quant = filter (fn v => Termtab.lookup new_vars v = Termtab.lookup all_vars v)
            (Termtab.keys new_vars)
        |> map (Thm.cterm_of ctxt)
  in fold Thm.forall_intr quant thm
    |> Conv.fconv_rule (Raw_Simplifier.rewrite_wrt ctxt false @{thms narrow_quant})
  end

fun mk_strg (typ, pat) ctxt thm = let
    val drule = typ = "D" orelse typ = "D'"
    val imp = gather_to_imp ctxt drule pat thm
      |> (if typ = "I'" orelse typ = "D'"
          then quantify_vars ctxt drule else I)
  in if typ = "I" orelse typ = "I'"
    then imp RS @{thm imp_to_strengthen}
    else if drule then imp RS @{thm rev_imp_to_strengthen}
    else if typ = "lhs" then imp RS @{thm ord_to_strengthen(1)}
    else if typ = "rhs" then imp RS @{thm ord_to_strengthen(2)}
    else raise THM ("mk_strg: unknown type: " ^ typ, 1, [thm])
 end

fun auto_mk ctxt thm = let
    val concl_C = try (fst o dest_Const o head_of
        o HOLogic.dest_Trueprop) (Thm.concl_of thm)
  in case (Thm.nprems_of thm, concl_C) of
    (_, SOME @{const_name st_failed}) => thm
  | (_, SOME @{const_name st}) => thm
  | (0, SOME @{const_name HOL.implies}) => (thm RS @{thm imp_to_strengthen}
      handle THM _ => @{thm failedI})
  | _ => mk_strg ("I'", []) ctxt thm
  end

fun mk_strg_args (SOME (typ, pat)) ctxt thm = mk_strg (typ, pat) ctxt thm
  | mk_strg_args NONE ctxt thm = auto_mk ctxt thm

val arg_pars = Scan.option (Scan.first (map Args.$$$ ["I", "I'", "D", "D'", "lhs", "rhs"])
  -- Scan.repeat (Args.$$$ "A" || Args.$$$ "E" || Args.$$$ "O" || Args.$$$ "_"))

val attr_pars : attribute context_parser
    = (Scan.lift arg_pars -- Args.context)
        >> (fn (args, ctxt) => Thm.rule_attribute [] (K (mk_strg_args args ctxt)))

end

\<close>

attribute_setup mk_strg = \<open>Make_Strengthen_Rule.attr_pars\<close>
          "put rule in 'strengthen' form (see theory Strengthen_Demo)"

lemma do_elim:
  "PROP P \<Longrightarrow> PROP st_elim (PROP P)"
  by (simp add: st_elim_def)

lemma intro_oblig:
  "PROP P \<Longrightarrow> PROP st_oblig (PROP P)"
  by (simp add: st_oblig_def)

named_theorems strg \<open>strengthening congruence rules\<close>

ML \<open>

structure Strengthen = struct

val tracing = Attrib.config_bool @{binding strengthen_trace} (K false)

fun map_context_total f (Context.Theory t) = (Context.Theory (f t))
  | map_context_total f (Context.Proof p)
    = (Context.Proof (Context.raw_transfer (f (Proof_Context.theory_of p)) p))

val setup = snd tracing;

fun goal_predicate t = let
    val gl = Logic.strip_assums_concl t
    val cn = head_of #> dest_Const #> fst
  in if cn gl = @{const_name st_oblig} then "oblig"
    else if cn gl = @{const_name st_elim} then "elim"
    else if cn gl = @{const_name st_prop1} then "st_prop1"
    else if cn gl = @{const_name st_prop2} then "st_prop2"
    else if cn (HOLogic.dest_Trueprop gl) = @{const_name st} then "st"
    else ""
  end handle TERM _ => ""

fun do_elim ctxt = SUBGOAL (fn (t, i) => if goal_predicate t = "elim"
    then eresolve_tac ctxt @{thms do_elim} i else all_tac)

fun final_oblig_strengthen ctxt = SUBGOAL (fn (t, i) => case goal_predicate t of
    "oblig" => resolve_tac ctxt @{thms intro_oblig} i
  | "st" => resolve_tac ctxt @{thms strengthen_refl} i
  | "st_prop1" => resolve_tac ctxt @{thms st_prop_refl} i
  | "st_prop2" => resolve_tac ctxt @{thms st_prop_refl} i
  | _ => all_tac)

infix 1 THEN_TRY_ALL_NEW;

(* Like THEN_ALL_NEW but allows failure, although at least one subsequent
   method must succeed. *)
fun (tac1 THEN_TRY_ALL_NEW tac2) i st = let
    fun inner b j st = if i > j then (if b then all_tac else no_tac) st
      else ((tac2 j THEN inner true (j - 1)) ORELSE inner b (j - 1)) st
  in st |> (tac1 i THEN (fn st' =>
    inner false (i + Thm.nprems_of st' - Thm.nprems_of st) st')) end

fun maybe_trace_tac false _ _ = K all_tac
  | maybe_trace_tac true ctxt msg = SUBGOAL (fn (t, _) => let
    val tr = Pretty.big_list msg [Syntax.pretty_term ctxt t]
  in
    Basic_Output.tracing (Pretty.string_of tr);
    all_tac
  end)

fun maybe_trace_rule false _ _ rl = rl
  | maybe_trace_rule true ctxt msg rl = let
    val tr = Pretty.big_list msg [Syntax.pretty_term ctxt (Thm.prop_of rl)]
  in
    Basic_Output.tracing (Pretty.string_of tr);
    rl
  end

type params = {trace : bool, once : bool}

fun params once ctxt = {trace = Config.get ctxt (fst tracing), once = once}

fun apply_tac_as_strg ctxt (params : params) (tac : tactic)
  = SUBGOAL (fn (t, i) => case Logic.strip_assums_concl t of
      @{term Trueprop} $ (@{term "st False (\<longrightarrow>)"} $ x $ _)
      => let
    val triv = Thm.trivial (Thm.cterm_of ctxt (HOLogic.mk_Trueprop x))
    val trace = #trace params
  in
    fn thm => tac triv
        |> Seq.map (maybe_trace_rule trace ctxt "apply_tac_as_strg: making strg")
        |> Seq.maps (Seq.try (Make_Strengthen_Rule.auto_mk ctxt))
        |> Seq.maps (fn str_rl => resolve_tac ctxt [str_rl] i thm)
  end | _ => no_tac)

fun opt_tac f (SOME v) = f v
  | opt_tac _ NONE = K no_tac

fun apply_strg ctxt (params : params) congs rules tac = EVERY' [
    maybe_trace_tac (#trace params) ctxt "apply_strg",
    DETERM o TRY o resolve_tac ctxt @{thms strengthen_Not},
    DETERM o ((resolve_tac ctxt rules THEN_ALL_NEW do_elim ctxt)
        ORELSE' (opt_tac (apply_tac_as_strg ctxt params) tac)
        ORELSE' (resolve_tac ctxt congs THEN_TRY_ALL_NEW
            (fn i => apply_strg ctxt params congs rules tac i)))
]

fun setup_strg ctxt params thms meths = let
    val congs = Named_Theorems.get ctxt \<^named_theorems>\<open>strg\<close>
    val rules = map (Make_Strengthen_Rule.auto_mk ctxt) thms
    val tac = case meths of [] => NONE
      | _ => SOME (FIRST (map (fn meth => NO_CONTEXT_TACTIC ctxt
        (Method.evaluate meth ctxt [])) meths))
  in apply_strg ctxt params congs rules tac
        THEN_ALL_NEW final_oblig_strengthen ctxt end

fun strengthen ctxt asm concl thms meths = let
    val strg = setup_strg ctxt (params false ctxt) thms meths
  in
    (if not concl then K no_tac
        else resolve_tac ctxt @{thms use_strengthen_imp} THEN' strg)
    ORELSE' (if not asm then K no_tac
        else eresolve_tac ctxt @{thms use_strengthen_prop_elim} THEN' strg)
  end

fun default_strengthen ctxt thms = strengthen ctxt false true thms []

val strengthen_args =
  Attrib.thms >> curry (fn (rules, ctxt) =>
    Method.CONTEXT_METHOD (fn _ =>
      Method.RUNTIME (CONTEXT_TACTIC
        (strengthen ctxt false true rules [] 1))
    )
  );

val strengthen_asm_args =
  Attrib.thms >> curry (fn (rules, ctxt) =>
    Method.CONTEXT_METHOD (fn _ =>
      Method.RUNTIME (CONTEXT_TACTIC
        (strengthen ctxt true false rules [] 1))
    )
  );

val strengthen_method_args =
  Method.text_closure >> curry (fn (meth, ctxt) =>
    Method.CONTEXT_METHOD (fn _ =>
      Method.RUNTIME (CONTEXT_TACTIC
        (strengthen ctxt true true [] [meth] 1))
    )
  );

end

\<close>

setup "Strengthen.setup"

method_setup strengthen = \<open>Strengthen.strengthen_args\<close>
  "strengthen the goal (see theory Strengthen_Demo)"

method_setup strengthen_asm = \<open>Strengthen.strengthen_asm_args\<close>
  "apply ''strengthen'' to weaken an assumption"

method_setup strengthen_method = \<open>Strengthen.strengthen_method_args\<close>
  "use an argument method in ''strengthen'' sites"

text \<open>Important strengthen congruence rules.\<close>

lemma strengthen_imp_imp[simp]:
  "st True (\<longrightarrow>) A B = (A \<longrightarrow> B)"
  "st False (\<longrightarrow>) A B = (B \<longrightarrow> A)"
  by (simp_all add: st_def)

lemma st_monotone:
  assumes "monotone orda ordb f"
  assumes "st F orda P P'"
  shows "st F ordb (f P) (f P')"
using monotoneD[OF assms(1)] assms(2) unfolding st_def by blast

abbreviation(input)
  "st_ord t \<equiv> st t ((\<le>) :: ('a :: preorder) \<Rightarrow> _)"

lemma st_ord_antimono:
  assumes "antimono f"
  assumes "st_ord (\<not>F) P P'"
  shows "st_ord F (f P) (f P')"
using antimonoD[OF assms(1)] assms(2) unfolding st_def by blast

lemma strengthen_imp_ord[simp]:
  shows "st_ord True A B = (A \<le> B)"
    and "st_ord False A B = (B \<le> A)"
unfolding st_def by auto

lemma strengthen_imp_conj[strg]:
  assumes "A' \<Longrightarrow> st F (\<longrightarrow>) B B'"
  assumes "B \<Longrightarrow> st F (\<longrightarrow>) A A'"
  shows "st F (\<longrightarrow>) (A \<and> B) (A' \<and> B')"
using assms by (cases F) auto

lemma strengthen_imp_disj[strg]:
  assumes "\<not> A' \<Longrightarrow> st F (\<longrightarrow>) B B'"
  assumes "\<not> B \<Longrightarrow> st F (\<longrightarrow>) A A'"
  shows "st F (\<longrightarrow>) (A \<or> B) (A' \<or> B')"
using assms by (cases F) auto

lemma strengthen_imp_implies[strg]:
  assumes "st (\<not> F) (\<longrightarrow>) X X'"
  assumes "X \<Longrightarrow> st F (\<longrightarrow>) Y Y'"
  shows "st F (\<longrightarrow>) (X \<longrightarrow> Y) (X' \<longrightarrow> Y')"
using assms by (cases F) auto

lemma strengthen_lam[strg]:
  fixes P :: "_ \<Rightarrow> _::preorder"
  assumes "\<And>x. st F (\<le>) (P x) (Q x)"
  shows "st F (\<le>) (\<lambda>x. P x) (\<lambda>x. Q x)"
using assms by (cases F) (auto intro: le_funI)

lemma strengthen_all[strg]:
  assumes "\<And>x. st F (\<longrightarrow>) (P x) (Q x)"
  shows "st F (\<longrightarrow>) (\<forall>x. P x) (\<forall>x. Q x)"
using assms by (cases F) auto

lemma strengthen_ex[strg]:
  assumes "\<And>x. st F (\<longrightarrow>) (P x) (Q x)"
  shows "st F (\<longrightarrow>) (\<exists>x. P x) (\<exists>x. Q x)"
using assms by (cases F) auto

lemma strengthen_Ball[strg]:
  assumes "st_ord (\<not>F) S S'"
  assumes "\<And>x. x \<in> S \<Longrightarrow> st F (\<longrightarrow>) (P x) (Q x)"
  shows "st F (\<longrightarrow>) (\<forall>x \<in> S. P x) (\<forall>x \<in> S'. Q x)"
using assms by (cases F) auto

lemma strengthen_Bex[strg]:
  assumes "st_ord F S S'"
  assumes "\<And>x. x \<in> S \<Longrightarrow> st F (\<longrightarrow>) (P x) (Q x)"
  shows "st F (\<longrightarrow>) (\<exists>x \<in> S. P x) (\<exists>x \<in> S'. Q x)"
using assms by (cases F) auto

lemma strengthen_Collect[strg]:
  assumes "\<And>x. st F (\<longrightarrow>) (P x) (P' x)"
  shows "st_ord F {x. P x} {x. P' x}"
using assms by (cases F) auto

lemma strengthen_mem[strg]:
  assumes "st_ord F S S'"
  shows "st F (\<longrightarrow>) (x \<in> S) (x \<in> S')"
using assms by (cases F) auto

lemma strengthen_ord[strg]:
  assumes "st_ord (\<not> F) x x'"
  assumes "st_ord F y y'"
  shows "st F (\<longrightarrow>) (x \<le> y) (x' \<le> y')"
using assms by (cases F; simp; metis order_trans)

lemma strengthen_strict_ord[strg]:
  assumes "st_ord (\<not> F) x x'"
  assumes "st_ord F y y'"
  shows "st F (\<longrightarrow>) (x < y) (x' < y')"
using assms by (cases F; simp; metis order_le_less_trans order_less_le_trans)

lemmas strengthen_image[strg] = st_monotone[OF mono_image]
lemmas strengthen_vimage[strg] = st_monotone[OF mono_vimage]

lemmas strengthen_uminus_boolean_algebra[strg] = st_ord_antimono[OF antimono_uminus_boolean_algebra]

lemmas strengthen_lfp[strg] = st_monotone[OF mono_lfp]

lemma strengthen_minus_boolean_algebra[strg]:
  fixes x :: "_::boolean_algebra"
  assumes "st_ord F x x'"
  assumes "st_ord (\<not> F) y y'"
  shows "st_ord F (x - y) (x' - y')"
using assms by (cases F; simp add: mono_minus_boolean_algebra)

lemma strengthen_insert[strg]:
  assumes "st_ord F A A'"
  shows "st_ord F (insert x A) (insert x A')"
using assms by (cases F) auto

lemma strengthen_Set_bind[strg]:
  assumes "st_ord F A A'"
  assumes "\<And>x. x \<in> A \<Longrightarrow> st_ord F (B x) (B' x)"
  shows "st_ord F (Set.bind A B) (Set.bind A' B')"
using assms by (cases F; fastforce)

lemma strengthen_Sigma[strg]:
  assumes "st_ord F A A'"
  assumes "\<And>x. x \<in> A \<Longrightarrow> st_ord F (B x) (B' x)"
  shows "st_ord F (Sigma A B) (Sigma A' B')"
using assms by (cases F) auto

lemma strengthen_imp_strengthen_prop[strg]:
  "st False (\<longrightarrow>) P Q \<Longrightarrow> PROP (st_prop1 (Trueprop P) (Trueprop Q))"
  "st True (\<longrightarrow>) P Q \<Longrightarrow> PROP (st_prop2 (Trueprop P) (Trueprop Q))"
  unfolding st_prop1_def st_prop2_def
  by auto

lemma st_prop_meta_imp[strg]:
  "PROP (st_prop2 (PROP X) (PROP X'))
    \<Longrightarrow> PROP (st_prop1 (PROP Y) (PROP Y'))
    \<Longrightarrow> PROP (st_prop1 (PROP X \<Longrightarrow> PROP Y) (PROP X' \<Longrightarrow> PROP Y'))"
  "PROP (st_prop1 (PROP X) (PROP X'))
    \<Longrightarrow> PROP (st_prop2 (PROP Y) (PROP Y'))
    \<Longrightarrow> PROP (st_prop2 (PROP X \<Longrightarrow> PROP Y) (PROP X' \<Longrightarrow> PROP Y'))"
  unfolding st_prop1_def st_prop2_def
  by (erule meta_mp | assumption)+

lemma st_prop_meta_all[strg]:
  "(\<And>x. PROP (st_prop1 (PROP (X x)) (PROP (X' x))))
    \<Longrightarrow> PROP (st_prop1 (\<And>x. PROP (X x)) (\<And>x. PROP (X' x)))"
  "(\<And>x. PROP (st_prop2 (PROP (X x)) (PROP (X' x))))
    \<Longrightarrow> PROP (st_prop2 (\<And>x. PROP (X x)) (\<And>x. PROP (X' x)))"
  unfolding st_prop1_def st_prop2_def
   apply (rule Pure.asm_rl)
   apply (erule meta_allE, erule meta_mp)
   apply assumption
  apply (rule Pure.asm_rl)
  apply (erule meta_allE, erule meta_mp)
  apply assumption
  done

lemma strengthen_inf[strg]:
  fixes A :: "_::semilattice_inf"
  assumes "st_ord F A A'"
  assumes "st_ord F B B'"
  shows "st_ord F (inf A B) (inf A' B')"
using assms inf_mono by (cases F) auto

lemma strengthen_sup[strg]:
  fixes A :: "_::semilattice_sup"
  assumes "st_ord F A A'"
  assumes "st_ord F B B'"
  shows "st_ord F (sup A B) (sup A' B')"
using assms sup_mono by (cases F) auto

lemma strengthen_INF[strg]:
  fixes B :: "_ \<Rightarrow> _::complete_lattice"
  assumes "st_ord (\<not> F) A A'"
  assumes "\<And>x. x \<in> A \<Longrightarrow> st_ord F (B x) (B' x)"
  shows "st_ord F (Inf (B ` A)) (Inf (B' ` A'))"
using assms by (cases F) (auto simp: INF_superset_mono subset_iff)

lemma strengthen_Inf[strg]:
  fixes A :: "_::complete_lattice set"
  assumes "st_ord (\<not>F) A A'"
  shows "st_ord F (Inf A) (Inf A')"
using assms by (cases F) (auto simp: Inf_superset_mono)

lemma strengthen_SUP[strg]:
  fixes B :: "_ \<Rightarrow> _::complete_lattice"
  assumes "st_ord F A A'"
  assumes "\<And>x. x \<in> A \<Longrightarrow> st_ord F (B x) (B' x)"
  shows "st_ord F (Sup (B ` A)) (Sup (B' ` A'))"
using assms by (cases F) (auto simp: SUP_subset_mono subset_eq)

lemma strengthen_Sup[strg]:
  fixes A :: "_::complete_lattice set"
  assumes "st_ord F A A'"
  shows "st_ord F (Sup A) (Sup A')"
using assms by (cases F) (auto simp: Sup_subset_mono)

lemma strengthen_Let[strg]:
  assumes "\<And>x. x = y \<Longrightarrow> st_ord F (f x) (f' x)"
  shows "st_ord F (let x = y in f x) (let x = y in f' x)"
using assms by (cases F) auto

lemma strengthen_case_unit[strg]:
  assumes "st_ord F x x'"
  shows "st_ord F (case_unit x) (case_unit x')"
using assms by (cases F) (auto simp: case_unit_Unity le_funI)

lemma strengthen_if[strg]:
  assumes "st_ord F t t'"
  assumes "st_ord F e e'"
  shows "st_ord F (if i then t else e) (if i then t' else e')"
using assms by (cases F) auto

lemma strengthen_case_option[strg]:
  assumes "st_ord F none none'"
  assumes "\<And>x. st_ord F (some x) (some' x)"
  shows "st_ord F (case_option none some opt) (case_option none' some' opt)"
using assms by (cases F) (auto split: option.splits)

lemma strengthen_case_sum[strg]:
  assumes "\<And>x. st_ord F (l x) (l' x)"
  assumes "\<And>x. st_ord F (r x) (r' x)"
  shows "st_ord F (case_sum l r x) (case_sum l' r' x)"
using assms by (cases F) (auto split: sum.splits)

end
