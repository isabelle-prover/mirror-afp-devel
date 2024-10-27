(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Tagging\<close>
theory Tagging
  imports Main Subgoals "HOL-Eisbach.Eisbach"
  keywords "preferT" "prefersT" :: prf_script % "proof"
       and "subgoalT" "subgoalsT" :: prf_script_goal % "proof"
begin

subsection \<open>Basic Definitions and Theorems\<close>

definition ASM_TAG (\<open>\<paragraph>\<close>) where
  "ASM_TAG t \<equiv> True"

definition TAG :: "'b \<Rightarrow> 'a :: {} \<Rightarrow> 'a"  (\<open>(\<open>open_block notation=\<open>infix TAG\<close>\<close>_ \<bar> _)\<close> [13, 13] 14)
  where \<open>TAG t x \<equiv> x\<close>

abbreviation tag_prop  (\<open>(\<open>open_block notation=\<open>infix TAG\<close>\<close>_ \<bar>\<bar> _)\<close> [0, 0] 0)
  where "tag_prop t x \<equiv> PROP TAG t x"

lemma TAG_cong[cong]: "x \<equiv> y \<Longrightarrow> (tag \<bar> x) \<equiv> tag \<bar> (y::'a::{})"
  by simp

lemma ASM_TAG_cong[cong]: "\<paragraph> tag \<longleftrightarrow> \<paragraph> tag"
  by simp

lemma ASM_TAG_I[intro!]: "\<paragraph> x" by (simp add: ASM_TAG_def)

lemma TAG_TrueI[intro!, simp]: "tag \<bar> True"
  by (simp add: TAG_def)

lemma TAG_False[simp]: "(tag \<bar> False) \<longleftrightarrow> False"
  by (simp add: TAG_def)

lemma TAG_false[elim!]: "(tag \<bar> False) \<Longrightarrow> P"
  by (simp add: TAG_def)

lemma ASM_TAG_aux1:
  "PROP P \<equiv> (True \<Longrightarrow> PROP P)"
  by auto

lemma ASM_TAG_CONV1:
  "PROP TAG t P \<equiv> (ASM_TAG t \<Longrightarrow> PROP P)"
  unfolding TAG_def ASM_TAG_def by auto

lemma disjE_tagged: 
  "(P \<or> Q) \<Longrightarrow> (\<paragraph> ''l'' \<Longrightarrow> P \<Longrightarrow> R) \<Longrightarrow> (\<paragraph> ''r'' \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma conjI_tagged: 
  "(\<paragraph> ''l'' \<Longrightarrow> P) \<Longrightarrow> (\<paragraph> ''r'' \<Longrightarrow> Q) \<Longrightarrow> P \<and> Q"
  by blast

\<comment> \<open>We will use the syntax \<open>\<paragraph> t \<bar> A\<close> for tags that should end up in assumptions and conclusions:\<close>
lemma assm_tagE[elim!]:
  assumes "\<paragraph> t \<bar> A"
  assumes "\<paragraph> t \<Longrightarrow> t \<bar> A \<Longrightarrow> P"
  shows P
  using assms unfolding TAG_def by auto
\<comment> \<open>Consider \<^term>\<open>(\<paragraph> ''l'' \<bar> P) \<or> (\<paragraph> ''r'' \<bar> Q)\<close>\<close>

ML \<open>
fun unfold_tags ctxt = Local_Defs.unfold ctxt @{thms TAG_def}
val untagged_attr = Thm.rule_attribute [] (fn context => unfold_tags (Context.proof_of context))

fun unfold_tac' ctxt rewrs =
  let
    val rewrs = map (Local_Defs.abs_def_rule ctxt) rewrs
  in
    rewrite_goal_tac ctxt rewrs
  end

fun thin_asm_tag_tac ctxt = REPEAT o eresolve_tac ctxt @{thms thin_rl[of "\<paragraph> t" for t]}

fun untag_tac ctxt = thin_asm_tag_tac ctxt THEN' unfold_tac' ctxt @{thms TAG_def}
\<close>

method_setup untag =
  \<open>Args.context >> (fn _ => fn ctxt => SIMPLE_METHOD' (untag_tac ctxt))\<close> "remove tags"

subsubsection \<open>Subgoals Test\<close>

lemma
  assumes False
  shows
  "\<And>a b. A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> ''foo'' \<bar> AA a b"
  "A \<Longrightarrow> B \<Longrightarrow> C2 \<Longrightarrow> ''bar'' \<bar> B"
  "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> ''bar'' \<bar> C"
  "A2 \<Longrightarrow> B \<Longrightarrow> C22 \<Longrightarrow> ''bar'' \<bar> C"  
  "\<And>b. A2 \<Longrightarrow> B \<Longrightarrow> C22 \<Longrightarrow> ''foo'' \<bar> CC b"
  "\<And>a b. A2 \<Longrightarrow> B \<Longrightarrow> C22 \<Longrightarrow> f a b"
  "\<And>c d. A2 \<Longrightarrow> \<paragraph> ''foobar'' \<Longrightarrow> B \<Longrightarrow> C22 \<Longrightarrow> D c d"
  subgoals (concl) "f _"
    using \<open>False\<close> by simp
  subgoals (concl) "''foo'' \<bar> _"
    using \<open>False\<close> by simp+
  subgoals "''bar'' \<bar> _"
    using \<open>False\<close> by simp+
  subgoals (prems) "\<paragraph> ''foobar''"
  oops

subsection \<open>Conversions\<close>

ML \<open>
fun extract_tag_trm trm =
  case trm of
    \<^Const>\<open>Trueprop for \<^Const>\<open>TAG _ _ for tag _\<close>\<close> => SOME tag
  | \<^Const>\<open>TAG _ _ for tag _\<close> => SOME tag
  | _ => NONE

val tag_of_goal = extract_tag_trm o Logic.strip_assums_concl o Thm.prop_of
\<close>

ML \<open>
fun prems_conv cv ct =
  let
    val n = Logic.count_prems (Thm.term_of ct)
  in
    Conv.prems_conv n cv ct
  end

fun goal_conv cv ct =
  let
    val n = Logic.count_prems (Thm.term_of ct)
  in
    Conv.concl_conv n cv ct
  end
\<close>

ML \<open>
fun rm_head_tag_conv ctx = Conv.top_rewrs_conv @{thms TAG_def} ctx |> goal_conv
\<close>

ML \<open>
fun get_add_tag_rewrs _ tag_ct =
  let
    val ctyp = Thm.ctyp_of_cterm tag_ct
  in [
   \<^instantiate>\<open>'t = \<open>ctyp\<close> and t1 = tag_ct in
      lemma (schematic) \<open>(PROP P) \<equiv> (ASM_TAG t1 \<Longrightarrow> PROP P)\<close> for t1 :: 't and P
        by (unfold ASM_TAG_def, rule ASM_TAG_aux1)\<close>
  ]
  end
val it = get_add_tag_rewrs @{context} @{cterm "1"}
\<close>

lemma norm_tag:
  "Trueprop (t \<bar> P) \<equiv> (t \<bar>\<bar> P)"
  unfolding TAG_def by auto

ML \<open>
fun push_concl_tag_to_assms ctxt thm =
let
  val tag_opt = tag_of_goal thm
  val tag = the_default @{term "''$''"} tag_opt
  val ctag = Thm.cterm_of ctxt tag
  val push_thms = get_add_tag_rewrs ctxt ctag
  val rewr_conv = Conv.rewrs_conv push_thms
  val push_conv = prems_conv rewr_conv
  val push = Conv.fconv_rule push_conv
  val norm_conv = Conv.rewrs_conv @{thms norm_tag} |> goal_conv
  val norm_conv = Conv.top_sweep_conv (fn _ => norm_conv) ctxt
  val assms_conv = Conv.rewrs_conv @{thms ASM_TAG_CONV1}
    |> goal_conv
  val assms_conv = Conv.top_sweep_conv (fn _ => assms_conv) ctxt
  val rm = Conv.fconv_rule (rm_head_tag_conv ctxt)
in
  thm
  |> Conv.fconv_rule (prems_conv (norm_conv \<^cancel>\<open>ctxt\<close>))
  |> Conv.fconv_rule assms_conv
  |> (case tag_opt of NONE => I | _ => push)
  |> rm
end
\<close>

ML \<open>
val push_tags_attr =
  Thm.rule_attribute []
    (fn context => push_concl_tag_to_assms (Context.proof_of context))
\<close>

attribute_setup push_tags =
  \<open>Scan.succeed () >> (fn _ => push_tags_attr)\<close>

ML \<open>
fun extract_asm_tag_trm trm =
  case trm of
    \<^Const>\<open>Trueprop for \<^Const>\<open>ASM_TAG _ for tag\<close>\<close> => SOME tag
  | _ => NONE

fun mk_add_tag_thms t = [
  \<^instantiate>\<open>'t = \<open>Thm.ctyp_of_cterm t\<close> and t = t in
    lemma (schematic) \<open>Trueprop y \<equiv> Trueprop (t \<bar> y)\<close> for t :: 't by (unfold TAG_def)\<close>,
  \<^instantiate>\<open>'t = \<open>Thm.ctyp_of_cterm t\<close> and t = t in
    lemma (schematic) \<open>Trueprop y \<equiv> (t \<bar> Trueprop y)\<close> for t :: 't by (unfold TAG_def)\<close>
]

fun get_list_tag t =
  let
    val tags = Logic.strip_assums_hyp t |> List.mapPartial extract_asm_tag_trm
    val tag = HOLogic.mk_list @{typ string} tags
  in
    if tags = [] then NONE else SOME tag
  end

fun add_tag_conv assm t ctxt = case get_list_tag t of
    NONE => Conv.all_conv
  | SOME tag =>
  let
    val ctag = Thm.cterm_of ctxt tag
    val push_thms =
      if assm then
        get_add_tag_rewrs ctxt ctag
      else
        mk_add_tag_thms ctag
    val rewr_conv = Conv.rewrs_conv push_thms |> goal_conv
  in
    rewr_conv
  end

fun tidy_tags_tac0 assm ctxt i thm =
  let
    val t = Thm.cprem_of thm i |> Thm.term_of
    val cconv = add_tag_conv assm t |> Conv.top_sweep_conv
    val conv = cconv ctxt |> Conv.try_conv
  in
    (CONVERSION conv THEN' thin_asm_tag_tac ctxt) i thm
  end
  handle THM _ => Seq.empty

fun tidy_tags_tac assm ctxt =
  REPEAT o eresolve_tac ctxt @{thms assm_tagE} THEN' tidy_tags_tac0 assm ctxt

val tidy_tags_meth =       fn _ => fn ctxt => SIMPLE_METHOD' (tidy_tags_tac false ctxt)
val tidy_tags_assm_meth =  fn _ => fn ctxt => SIMPLE_METHOD' (tidy_tags_tac true  ctxt)
\<close>

method_setup tidy_tags_tac =
  \<open>Args.context >> tidy_tags_meth\<close>
  "compress tags into list of tags and tag goals"

method_setup tidy_tags_assm_tac =
  \<open>Args.context >> tidy_tags_assm_meth\<close>
  "compress tags into list of tags and tag assumptions"

method tidy_tags = changed \<open>tidy_tags_tac\<close>

method tidy_tags_assm = changed \<open>tidy_tags_assm_tac\<close>

lemma
  "n > 0" if "n > 1 \<or> n > 2" for n :: nat
  using that
  apply (rule disjE_tagged;  tidy_tags)
  oops

lemma
  "n > 0" if "(\<paragraph> ''l'' \<bar> n > 1) \<or> (\<paragraph> ''r'' \<bar> n > 2)" for n :: nat
  using that
  apply standard
  apply (all tidy_tags)
  oops

subsection \<open>Globbing\<close>

ML \<open>
datatype 't glob = WILDCARD | ANY | TOKEN of 't

fun
  matches_glob [] [] = true
| matches_glob [] _  = false
| matches_glob (TOKEN t :: ps) (t' :: ts) = t' = t andalso matches_glob ps ts
| matches_glob (ANY :: ps) (_ :: ts) = matches_glob ps ts
| matches_glob (WILDCARD :: ps) (t :: ts) =
  matches_glob ps (t :: ts) orelse matches_glob (WILDCARD :: ps) ts
| matches_glob (WILDCARD :: ps) [] = matches_glob ps []
| matches_glob _ [] = false

fun assert b = (if b then () else error "assert")

val p1 = [WILDCARD, TOKEN "a", WILDCARD, TOKEN "c"]
val p2 = [ANY, TOKEN "a", WILDCARD, TOKEN "c"]
val it1 = assert ([
  matches_glob p1 ["b", "a", "c"],
  matches_glob p1 ["b", "a", "c", "d"],
  matches_glob p1 ["a", "c"],
  matches_glob p1 ["b", "a", "d"]
] = [true, false, true, false])
val it2 = assert ([
  matches_glob p2 ["b", "a", "c"],
  matches_glob p2 ["b", "a", "c", "d"],
  matches_glob p2 ["a", "c"],
  matches_glob p2 ["b", "a", "d"]
] = [true, false, false, false])
\<close>

ML \<open>
fun tag_list_of goal =
  case extract_tag_trm goal of
      NONE => []
    | SOME t => map HOLogic.dest_string (HOLogic.dest_list t)
      handle TERM ("dest_list", _) => [HOLogic.dest_string t]

fun matches_glob_term glob = matches_glob glob o tag_list_of
\<close>

ML \<open>
val parse_glob_token = (Parse.sym_ident || Parse.name)
  >> (fn
    "*" => WILDCARD
  | "_" => ANY
  | s   => TOKEN s
  )
val parse_glob = Scan.repeat1 parse_glob_token
\<close>

subsection \<open>Reordering Subgoals\<close>

ML \<open>
val empty = (Vartab.empty, Vartab.empty)

fun matches thy pat trm = (Pattern.match thy (pat, trm) empty; true)
  handle Pattern.MATCH => false

fun matches_tag thy tag goal =
  case extract_tag_trm goal of
      NONE => false
    | SOME t => matches thy tag t

fun filter_thms thy pat = List.filter (fn thm => matches thy pat (Thm.prop_of thm))

(* Find index of first subgoal in thm whose conclusion matches pred *)
fun find_subgoal pred thm =
  let
    val subgoals = Thm.prems_of thm
  in
    Library.find_index (fn goal => pred (Logic.strip_assums_concl goal)) subgoals
  end

fun prefer_by_pred_tac pred: tactic = fn thm =>
  let
    val i = find_subgoal pred thm + 1
  in
    if i > 0 then Tactic.prefer_tac i thm else no_tac thm
  end

fun prefer_by_tag_tac thy tag: tactic =
  prefer_by_pred_tac (matches_tag thy tag)

fun prefer_pred pred st =
  let
    val st = Proof.assert_no_chain st
    val thy = Proof.theory_of st
  in
    Proof.refine_singleton
      (Method.Basic (fn _ => METHOD (fn _ => prefer_by_pred_tac (pred thy)))) st
  end

fun prefer_glob glob = prefer_pred (fn _ => matches_glob_term glob)
\<close>

ML \<open>Outer_Syntax.command \<^command_keyword>\<open>preferT\<close> "select subgoal by tag"
  (parse_glob >> (Toplevel.proof o prefer_glob))
\<close>

lemma
  "TAG ''p'' P" "TAG ''q'' Q" "PROP TAG ''r'' R" "TAG ''p'' P2"
  preferT r
  oops

lemma
  "\<And>t. TAG ''p'' P \<and> TAG ''q'' Q"
  apply (rule conjI)
  preferT q
  oops

subsection \<open>\<open>subgoalT\<close> and \<open>subgoalsT\<close>, and \<open>prefersT\<close>\<close>

ML \<open>
fun orelseOpt f g x = case f x of NONE => g x | y => y
fun assm_name_of_tags trm =
  extract_tag_trm trm |>
    Option.mapPartial (
      orelseOpt
        (try (HOLogic.dest_string o hd o HOLogic.dest_list))
        (try HOLogic.dest_string)
      )
  |> the_default ""
\<close>

ML \<open>
fun chop_by _  [] = []
  | chop_by eq (x :: xs) =
  let
    val (g, rest) = chop_prefix (eq x) xs
  in
    (x :: g) :: chop_by eq rest
  end
fun group_by k = chop_by (fn a => fn b => k a = k b) o sort_by k
\<close>

ML \<open>
val tag_name_of_prop = assm_name_of_tags o Thm.prop_of
fun note_of_thms (name, thms) =
  let
    val binding = Binding.qualified_name name
  in
    (((binding, [])), [(thms, [untagged_attr])])
  end
fun note_thms thms ctx =
  let
    val thms_tags = map (fn thm => (tag_name_of_prop thm, thm)) thms
    val grouped = group_by fst thms_tags |> map (fn g => (fst (hd g), map snd g))
  in
    Proof_Context.note_thmss "" (map note_of_thms grouped) ctx |> snd
  end
fun note_thms_tac thms (ctx, thm) = (note_thms thms ctx, thm) |> Seq.succeed |> Seq.make_results
fun note_thms_meth x = (Scan.succeed () >>
  (fn () => fn _ => CONTEXT_METHOD (fn thms => note_thms_tac thms))) x
\<close>

method_setup note_thms = \<open>note_thms_meth\<close>

ML \<open>
local
val opt_fact_binding =
  Scan.optional (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty)
    Binding.empty_atts;

val for_params =
  Scan.optional
    (\<^keyword>\<open>for\<close> |--
      Parse.!!! ((Scan.option Parse.dots >> is_some) --
        (Scan.repeat1 (Parse.maybe_position Parse.name_position))))
    (false, []);

fun subgoal_cmd facts_name_opt param_specs st =
  let
    val (subgoal_focus, st) = Subgoal.subgoal_cmd (Binding.empty, []) facts_name_opt param_specs st
    val prems = #prems subgoal_focus
    val st = Proof.map_context (note_thms prems) st
  in
    st
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>subgoalT\<close>
    "subgoal for tags"
    ((Scan.option parse_glob)
      -- (Scan.option (\<^keyword>\<open>premises\<close> |-- Parse.!!! opt_fact_binding)) --
      for_params >> (fn ((glob_opt, b), c) =>
        Toplevel.proofs (
          Seq.make_results
        o Seq.single
        o Proof.refine_singleton (Method.Basic (fn ctxt => SIMPLE_METHOD' (untag_tac ctxt)))
        o subgoal_cmd b c
        o (case glob_opt of SOME x => prefer_glob x | _ => fn x => x)
        o Proof.refine_singleton (Method.Basic (tidy_tags_meth []))
    )));

val parse_keep =
  Scan.optional (Args.parens (Args.$$$ "keep" >> K true)) false;

fun tidy_then_protect_meth glob =
  let
    val pred = matches_glob_term glob o Logic.strip_assums_concl o Thm.term_of
    fun tidy_then_protect_tac ctxt =
      TRYALL (tidy_tags_tac false ctxt)
      THEN  prefer_and_protect_subgoals_tac pred ctxt
    val tidy_then_protect = Method.Basic
      (SIMPLE_METHOD o tidy_then_protect_tac)
  in tidy_then_protect end

fun get_unprotect_thms keep =
  @{thms protected_conjunction_def protected_prop_def} @
  (if keep then [] else @{thms TAG_def})

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>subgoalsT\<close>
    "focus on all subgoals that match a given pattern within backward refinement"
    (parse_keep -- parse_glob >> (fn (keep, glob) => 
      Toplevel.proofs (
        unprotect_and_finish (get_unprotect_thms keep) o
        #2 o
        Subgoal.subgoal Binding.empty_atts NONE (false, []) o
        Proof.refine_singleton (tidy_then_protect_meth glob)
      )))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>prefersT\<close>
    "focus on all subgoals that match a given pattern within backward refinement"
    (parse_keep -- parse_glob >> (fn (keep, glob) => 
      Toplevel.proofs (
          unprotect_and_finish (get_unprotect_thms keep) o
          Proof.refine_singleton (tidy_then_protect_meth glob)
      )))
in end
\<close>

lemma
  assumes "TAG ''p'' P" Q False
  shows "TAG [''x''] True" "TAG [''y''] False" "TAG [''x'', ''y''] False" "TAG [''a'', ''b''] True"
  using assms
  apply -
  subgoal premises prems
    using prems
    apply note_thms
    thm p
    oops

lemma
  assumes "TAG ''p'' P" Q False
  shows "TAG [''x''] True" "TAG [''y''] False" "TAG [''x'', ''y''] False" "TAG [''a'', ''b''] True"
  using assms
  apply -
  subgoal premises prems
    using prems
    apply note_thms
    thm p
    oops

lemma
  assumes "TAG ''p'' P" "TAG [''q'', ''r''] Q" "TAG [''q''] QQ" False
  shows "TAG [''x''] True" "TAG [''y''] False" "TAG [''x'', ''y''] False" "TAG [''a'', ''b''] True"
  using assms
  apply -

  subgoalsT (keep) x *

  subgoalT x premises prems
    thm p q
    using \<open>False\<close> by simp
  subgoalT x _ premises prems
    thm p q
    using \<open>False\<close> by simp
  done
  subgoalT y premises prems
    thm p q
    using \<open>False\<close> by simp
  subgoalsT *
    using \<open>False\<close> by simp+
  oops

lemma
  assumes "TAG ''p'' P" "TAG [''q'', ''r''] Q" False
  shows
    "TAG [''x''] True" "TAG [''y''] False" P "TAG [''x'', ''y''] False" "TAG [''a'', ''b''] True"
  using assms
  apply -
  subgoalT x premises prems
    using prems apply -
    using \<open>False\<close> by simp

  subgoalT y premises prems
    using prems apply -
    using \<open>False\<close> by simp

  subgoalT premises prems
    using prems apply -
    using \<open>False\<close> by simp
  
  subgoalT x y premises prems
    using prems apply -
    using \<open>False\<close> by simp
  
  subgoalT a b premises prems
    using prems apply -
    thm p q
    using \<open>False\<close> by simp
  done

lemma
  "n > 0" if "(\<paragraph> ''l'' \<bar> n > 1) \<or> (\<paragraph> ''r'' \<bar> n > 2)" for n :: nat
  using that
  apply standard
  subgoalT l premises
    using l by simp
  subgoalT r premises
    using r by simp
  done

lemma
  "n > 0" if "(\<paragraph> ''l'' \<bar> n > 9) \<or> (\<paragraph> ''s'' \<bar> n > 2) \<or> (\<paragraph> ''s'' \<bar> n > 0)" for n :: nat
  using that
  apply (elim disjE)
  prefersT s \<comment> \<open>tidies all goals before tags are matched\<close>
   apply simp+
  subgoalT l premises
    using l by simp
  done

end