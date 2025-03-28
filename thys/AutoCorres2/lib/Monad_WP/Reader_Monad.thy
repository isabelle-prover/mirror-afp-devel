(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Contributions by:
 *   2012 Lars Noschinski <noschinl@in.tum.de>
 *     Option monad while loop formalisation.
 *)

chapter "Option Monad (State Reader)"

theory Reader_Monad
  imports
    "More_Lib" (* FIXME: reduce dependencies *)
    "Less_Monad_Syntax"
begin

type_synonym ('s,'a) lookup = "'s \<Rightarrow> 'a option"

text \<open>Similar to \<^const>\<open>map_option\<close> but the second function returns option as well\<close>
definition
  opt_map :: "('s,'a) lookup \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> ('s,'b) lookup" (infixl \<open>|>\<close> 54)
where
  "f |> g \<equiv> \<lambda>s. case f s of None \<Rightarrow> None | Some x \<Rightarrow> g x"

abbreviation opt_map_Some :: "('s \<rightharpoonup> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 's \<rightharpoonup> 'b" (infixl \<open>||>\<close> 54) where
  "f ||> g \<equiv> f |> (Some \<circ> g)"
lemmas opt_map_Some_def = opt_map_def

lemma opt_map_cong [fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s. f s = Some v \<Longrightarrow> g v = g' v\<rbrakk> \<Longrightarrow> f |> g = f' |> g'"
  by (rule ext) (simp add: opt_map_def split: option.splits)

lemma in_opt_map_eq:
  "((f |> g) s = Some v) = (\<exists>v'. f s = Some v' \<and> g v' = Some v)"
  by (simp add: opt_map_def split: option.splits)

lemma opt_mapE:
  "\<lbrakk> (f |> g) s = Some v; \<And>v'. \<lbrakk>f s = Some v'; g v' = Some v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp: in_opt_map_eq)

lemma opt_map_upd_None:
  "f(x := None) |> g = (f |> g)(x := None)"
  by (auto simp: opt_map_def)

lemma opt_map_upd_Some:
  "f(x \<mapsto> v) |> g = (f |> g)(x := g v)"
  by (auto simp: opt_map_def)

lemmas opt_map_upd[simp] = opt_map_upd_None opt_map_upd_Some

declare None_upd_eq[simp]

(* None_upd_eq[simp] so that this pattern is by simp. Hopefully not too much slowdown. *)
lemma "\<lbrakk> (f |> g) x = None; g v = None \<rbrakk> \<Longrightarrow> f(x \<mapsto> v) |> g = f |> g"
  by simp

definition
  obind :: "('s,'a) lookup \<Rightarrow> ('a \<Rightarrow> ('s,'b) lookup) \<Rightarrow> ('s,'b) lookup" (infixl \<open>|>>\<close> 53)
where
  "f |>> g \<equiv> \<lambda>s. case f s of None \<Rightarrow> None | Some x \<Rightarrow> g x s"

(* Enable "do { .. }" syntax *)
adhoc_overloading
  Monad_Syntax.bind \<rightleftharpoons> obind

definition
  "ofail = K None"

definition
  "oreturn = K o Some"

definition
  "oassert P \<equiv> if P then oreturn () else ofail"

definition oapply :: "'a \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option"
  where
  "oapply x \<equiv> \<lambda>s. s x"

text \<open>
  If the result can be an exception.
  Corresponding bindE would be analogous to lifting in NonDetMonad.
\<close>

definition
  "oreturnOk x = K (Some (Inr x))"

definition
  "othrow e = K (Some (Inl e))"

definition
  "oguard G \<equiv> (\<lambda>s. if G s then Some () else None)"

definition
  "ocondition c L R \<equiv> (\<lambda>s. if c s then L s else R s)"

definition
  "oskip \<equiv> oreturn ()"

text \<open>Monad laws\<close>
lemma oreturn_bind [simp]: "(oreturn x |>> f) = f x"
  by (auto simp add: oreturn_def obind_def K_def)

lemma obind_return [simp]: "(m |>> oreturn) = m"
  by (auto simp add: oreturn_def obind_def K_def split: option.splits)

lemma obind_assoc:
  "(m |>> f) |>> g  =  m |>> (\<lambda>x. f x |>> g)"
  by (auto simp add: oreturn_def obind_def K_def split: option.splits)


text \<open>Binding fail\<close>

lemma obind_fail [simp]:
  "f |>> (\<lambda>_. ofail) = ofail"
  by (auto simp add: ofail_def obind_def K_def split: option.splits)

lemma ofail_bind [simp]:
  "ofail |>> m = ofail"
  by (auto simp add: ofail_def obind_def K_def split: option.splits)



text \<open>Function package setup\<close>
lemma opt_bind_cong [fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s. f' s = Some v \<Longrightarrow> g v s = g' v s \<rbrakk> \<Longrightarrow> f |>> g = f' |>> g'"
  by (rule ext) (simp add: obind_def split: option.splits)

lemma opt_bind_cong_apply [fundef_cong]:
  "\<lbrakk> f s = f' s; \<And>v. f' s = Some v \<Longrightarrow> g v s = g' v s \<rbrakk> \<Longrightarrow> (f |>> g) s = (f' |>> g') s"
  by (simp add: obind_def split: option.splits)

lemma oassert_bind_cong [fundef_cong]:
  "\<lbrakk> P = P'; P' \<Longrightarrow> m = m' \<rbrakk> \<Longrightarrow> oassert P |>> m = oassert P' |>> m'"
  by (auto simp: oassert_def)

lemma oassert_bind_cong_apply [fundef_cong]:
  "\<lbrakk> P = P'; P' \<Longrightarrow> m () s = m' () s \<rbrakk> \<Longrightarrow> (oassert P |>> m) s = (oassert P' |>> m') s"
  by (auto simp: oassert_def)

lemma oreturn_bind_cong [fundef_cong]:
  "\<lbrakk> x = x'; m x' = m' x' \<rbrakk> \<Longrightarrow> oreturn x |>> m = oreturn x' |>> m'"
  by simp

lemma oreturn_bind_cong_apply [fundef_cong]:
  "\<lbrakk> x = x'; m x' s = m' x' s \<rbrakk> \<Longrightarrow> (oreturn x |>> m) s = (oreturn x' |>> m') s"
  by simp

lemma oreturn_bind_cong2 [fundef_cong]:
  "\<lbrakk> x = x'; m x' = m' x' \<rbrakk> \<Longrightarrow> (oreturn $ x) |>> m = (oreturn $ x') |>> m'"
  by simp

lemma oreturn_bind_cong2_apply [fundef_cong]:
  "\<lbrakk> x = x'; m x' s = m' x' s \<rbrakk> \<Longrightarrow> ((oreturn $ x) |>> m) s = ((oreturn $ x') |>> m') s"
  by simp

lemma ocondition_cong [fundef_cong]:
"\<lbrakk>c = c'; \<And>s. c' s \<Longrightarrow> l s = l' s; \<And>s. \<not>c' s \<Longrightarrow> r s = r' s\<rbrakk>
  \<Longrightarrow> ocondition c l r = ocondition c' l' r'"
  by (auto simp: ocondition_def)


text \<open>Decomposition\<close>

lemma ocondition_K_true [simp]:
  "ocondition (\<lambda>_. True) T F = T"
  by (simp add: ocondition_def)

lemma ocondition_K_false [simp]:
  "ocondition (\<lambda>_. False) T F = F"
  by (simp add: ocondition_def)

lemma ocondition_False:
    "\<lbrakk> \<And>s. \<not> P s \<rbrakk> \<Longrightarrow> ocondition P L R = R"
  by (rule ext, clarsimp simp: ocondition_def)

lemma ocondition_True:
    "\<lbrakk> \<And>s. P s \<rbrakk> \<Longrightarrow> ocondition P L R = L"
  by (rule ext, clarsimp simp: ocondition_def)

lemma in_oreturn [simp]:
  "(oreturn x s = Some v) = (v = x)"
  by (auto simp: oreturn_def K_def)

lemma oreturnE:
  "\<lbrakk>oreturn x s = Some v; v = x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma in_ofail [simp]:
  "ofail s \<noteq> Some v"
  by (auto simp: ofail_def K_def)

lemma ofailE:
  "ofail s = Some v \<Longrightarrow> P"
  by simp

lemma in_oassert_eq [simp]:
  "(oassert P s = Some v) = P"
  by (simp add: oassert_def)

lemma oassert_True [simp]:
  "oassert True = oreturn ()"
  by (simp add: oassert_def)

lemma oassert_False [simp]:
  "oassert False = ofail"
  by (simp add: oassert_def)

lemma oassertE:
  "\<lbrakk> oassert P s = Some v; P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by simp

lemma in_obind_eq:
  "((f |>> g) s = Some v) = (\<exists>v'. f s = Some v' \<and> g v' s = Some v)"
  by (simp add: obind_def split: option.splits)

lemma obind_eqI:
  "\<lbrakk> f s = f s' ; \<And>x. f s = Some x \<Longrightarrow> g x s = g' x s' \<rbrakk> \<Longrightarrow> obind f g s = obind f g' s'"
  by (simp add: obind_def split: option.splits)

(* full form of obind_eqI; the second equality makes more sense flipped here, as we end up
   with "f s = Some x ; f s' = f s" preventing "Some x = ..." *)
lemma obind_eqI_full:
  "\<lbrakk> f s = f s' ; \<And>x. \<lbrakk> f s = Some x; f s' = f s \<rbrakk> \<Longrightarrow> g x s = g' x s' \<rbrakk>
   \<Longrightarrow> obind f g s = obind f g' s'"
  by (drule sym[where s="f s"]) (* prevent looping *)
     (clarsimp simp: obind_def split: option.splits)

lemma obindE:
  "\<lbrakk> (f |>> g) s = Some v;
     \<And>v'. \<lbrakk>f s = Some v'; g v' s = Some v\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: in_obind_eq)

lemma in_othrow_eq [simp]:
  "(othrow e s = Some v) = (v = Inl e)"
  by (auto simp: othrow_def K_def)

lemma othrowE:
  "\<lbrakk>othrow e s = Some v; v = Inl e \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma in_oreturnOk_eq [simp]:
  "(oreturnOk x s = Some v) = (v = Inr x)"
  by (auto simp: oreturnOk_def K_def)

lemma oreturnOkE:
  "\<lbrakk>oreturnOk x s = Some v; v = Inr x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemmas omonadE [elim!] =
  opt_mapE obindE oreturnE ofailE othrowE oreturnOkE oassertE

lemma in_opt_map_Some_eq:
  "((f ||> g) x = Some y) = (\<exists>v. f x = Some v \<and> g v = y)"
  by (simp add: in_opt_map_eq)

lemma in_opt_map_None_eq[simp]:
  "((f ||> g) x = None) = (f x = None)"
  by (simp add: opt_map_def split: option.splits)

lemma oreturn_comp[simp]:
  "oreturn x \<circ> f = oreturn x"
  by (simp add: oreturn_def K_def o_def)

lemma ofail_comp[simp]:
  "ofail \<circ> f = ofail"
  by (auto simp: ofail_def K_def)

lemma oassert_comp[simp]:
  "oassert P \<circ> f = oassert P"
  by (simp add: oassert_def)

lemma fail_apply[simp]:
  "ofail s = None"
  by (simp add: ofail_def K_def)

lemma oassert_apply[simp]:
  "oassert P s = (if P then Some () else None)"
  by (simp add: oassert_def)

lemma oreturn_apply[simp]:
  "oreturn x s = Some x"
  by simp

lemma oapply_apply[simp]:
  "oapply x s = s x"
  by (simp add: oapply_def)

lemma obind_comp_dist:
  "obind f g o h = obind (f o h) (\<lambda>x. g x o h)"
  by (auto simp: obind_def split: option.splits)

lemma if_comp_dist:
  "(if P then f else g) o h = (if P then f o h else g o h)"
  by auto


section \<open>"While" loops over option monad.\<close>

text \<open>
  This is an inductive definition of a while loop over the plain option monad
  (without passing through a state)
\<close>

inductive_set
  option_while' :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a option rel"
  for C B
where
    final: "\<not> C r \<Longrightarrow> (Some r, Some r) \<in> option_while' C B"
  | fail: "\<lbrakk> C r; B r = None \<rbrakk> \<Longrightarrow> (Some r, None) \<in> option_while' C B"
  | step: "\<lbrakk> C r;  B r = Some r'; (Some r', sr'') \<in> option_while' C B \<rbrakk>
           \<Longrightarrow> (Some r, sr'') \<in> option_while' C B"

definition
  "option_while C B r \<equiv>
    (if (\<exists>s. (Some r, s) \<in> option_while' C B) then
      (THE s. (Some r, s) \<in> option_while' C B) else None)"

lemma option_while'_inj:
  assumes "(s,s') \<in> option_while' C B" "(s, s'') \<in> option_while' C B"
  shows "s' = s''"
  using assms by (induct rule: option_while'.induct) (auto elim: option_while'.cases)

lemma option_while'_inj_step:
  "\<lbrakk> C s; B s = Some s'; (Some s, t) \<in> option_while' C B ; (Some s', t') \<in> option_while' C B \<rbrakk> \<Longrightarrow> t = t'"
  by (metis option_while'.step option_while'_inj)

lemma option_while'_THE:
  assumes "(Some r, sr') \<in> option_while' C B"
  shows "(THE s. (Some r, s) \<in> option_while' C B) = sr'"
  using assms by (blast dest: option_while'_inj)

lemma option_while_simps:
  "\<not> C s \<Longrightarrow> option_while C B s = Some s"
  "C s \<Longrightarrow> B s = None \<Longrightarrow> option_while C B s = None"
  "C s \<Longrightarrow> B s = Some s' \<Longrightarrow> option_while C B s = option_while C B s'"
  "(Some s, ss') \<in> option_while' C B \<Longrightarrow> option_while C B s = ss'"
  using option_while'_inj_step[of C s B s']
  by (auto simp: option_while_def option_while'_THE
      intro: option_while'.intros
      dest: option_while'_inj
      elim: option_while'.cases)

lemma option_while_rule:
  assumes "option_while C B s = Some s'"
  assumes "I s"
  assumes istep: "\<And>s s'. C s \<Longrightarrow> I s \<Longrightarrow> B s = Some s' \<Longrightarrow> I s'"
  shows "I s' \<and> \<not> C s'"
proof -
  { fix ss ss' assume "(ss, ss') \<in> option_while' C B" "ss = Some s" "ss' = Some s'"
    then have ?thesis using \<open>I s\<close>
      by (induct arbitrary: s) (auto intro: istep) }
  then show ?thesis using assms(1)
    by (auto simp: option_while_def option_while'_THE split: if_split_asm)
qed

lemma option_while'_term:
  assumes "I r"
  assumes "wf M"
  assumes step_less: "\<And>r r'. \<lbrakk>I r; C r; B r = Some r'\<rbrakk> \<Longrightarrow> (r',r) \<in> M"
  assumes step_I: "\<And>r r'. \<lbrakk>I r; C r; B r = Some r'\<rbrakk> \<Longrightarrow> I r'"
  obtains sr' where "(Some r, sr') \<in> option_while' C B"
  apply atomize_elim
  using assms(2,1)
proof induct
  case (less r)
  show ?case
  proof (cases "C r" "B r" rule: bool.exhaust[case_product option.exhaust])
    case (True_Some r')
    then have "(r',r) \<in> M" "I r'"
      by (auto intro: less step_less step_I)
    then obtain sr' where "(Some r', sr') \<in> option_while' C B"
      by atomize_elim (rule less)
    then have "(Some r, sr') \<in> option_while' C B"
      using True_Some by (auto intro: option_while'.intros)
    then show ?thesis ..
  qed (auto intro: option_while'.intros)
qed

lemma option_while_rule':
  assumes "option_while C B s = ss'"
  assumes "wf M"
  assumes "I (Some s)"
  assumes less: "\<And>s s'. C s \<Longrightarrow> I (Some s) \<Longrightarrow> B s = Some s' \<Longrightarrow> (s', s) \<in> M"
  assumes step: "\<And>s s'. C s \<Longrightarrow> I (Some s) \<Longrightarrow> B s = Some s' \<Longrightarrow> I (Some s')"
  assumes final: "\<And>s. C s \<Longrightarrow> I (Some s) \<Longrightarrow> B s = None \<Longrightarrow> I None"
  shows "I ss' \<and> (case ss' of Some s' \<Rightarrow> \<not> C s' | _ \<Rightarrow> True)"
proof -
  define ss where "ss \<equiv> Some s"
  obtain ss1' where "(Some s, ss1') \<in> option_while' C B"
    using assms(3,2,4,5) by (rule option_while'_term)
  then have *: "(ss, ss') \<in> option_while' C B" using \<open>option_while C B s = ss'\<close>
    by (auto simp: option_while_simps ss_def)
  show ?thesis
  proof (cases ss')
    case (Some s') with * ss_def show ?thesis using \<open>I _\<close>
      by (induct arbitrary:s) (auto intro: step)
  next
    case None with * ss_def show ?thesis using \<open>I _\<close>
      by (induct arbitrary:s) (auto intro: step final)
  qed
qed

section \<open>Lift @{term option_while} to the @{typ "('a,'s) lookup"} monad\<close>

definition
  owhile :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('s,'a) lookup) \<Rightarrow> 'a \<Rightarrow> ('s,'a) lookup"
where
 "owhile c b a \<equiv> \<lambda>s. option_while (\<lambda>a. c a s) (\<lambda>a. b a s) a"

lemma owhile_unroll:
  "owhile C B r = ocondition (C r) (B r |>> owhile C B) (oreturn r)"
  by (auto simp: ocondition_def obind_def oreturn_def owhile_def
           option_while_simps K_def split: option.split)

text \<open>rule for terminating loops\<close>

lemma owhile_rule:
  assumes "I r s"
  assumes "wf M"
  assumes less: "\<And>r r'. \<lbrakk>I r s; C r s; B r s = Some r'\<rbrakk> \<Longrightarrow> (r',r) \<in> M"
  assumes step: "\<And>r r'. \<lbrakk>I r s; C r s; B r s = Some r'\<rbrakk> \<Longrightarrow> I r' s"
  assumes fail: "\<And>r. \<lbrakk>I r s; C r s; B r s = None\<rbrakk> \<Longrightarrow> Q None"
  assumes final: "\<And>r. \<lbrakk>I r s; \<not>C r s\<rbrakk> \<Longrightarrow> Q (Some r)"
  shows "Q (owhile C B r s)"
proof -
  let ?rs' = "owhile C B r s"
  have "(case ?rs' of Some r \<Rightarrow> I r s | _ \<Rightarrow> Q None)
      \<and> (case ?rs' of Some r' \<Rightarrow> \<not> C r' s | _ \<Rightarrow> True)"
    by (rule option_while_rule'[where B="\<lambda>r. B r s" and s=r, OF _ \<open>wf _\<close>])
       (auto simp: owhile_def intro: assms)
  then show ?thesis by (auto intro: final split: option.split_asm)
qed

end
