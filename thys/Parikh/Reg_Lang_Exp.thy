(* Authors: Fabian Lehr *)

section \<open>Regular language expressions\<close>

theory Reg_Lang_Exp
  imports 
    "Regular-Sets.Regular_Exp"
begin


subsection \<open>Definition\<close>

text \<open>We introduce regular language expressions which will be the building blocks of the systems of
equations defined later. Regular language expressions can contain both constant languages and
variable languages where variables are natural numbers for simplicity. Given a valuation, i.e.\ an
instantiation of each variable with a language, the regular language expression can be evaluated,
yielding a language.\<close>
datatype 'a rlexp = Var nat                          (* Variable *)
                  | Const "'a lang"                  (* Constant *)
                  | Union "'a rlexp" "'a rlexp"
                  | Concat "'a rlexp" "'a rlexp"     (* Concatenation *)
                  | Star "'a rlexp"                  (* Kleene star*)

type_synonym 'a valuation = "nat \<Rightarrow> 'a lang"

primrec eval :: "'a rlexp \<Rightarrow> 'a valuation \<Rightarrow> 'a lang" where
  "eval (Var n) v = v n" |
  "eval (Const l) _ = l" |
  "eval (Union f g) v = eval f v \<union> eval g v" |
  "eval (Concat f g) v = eval f v @@ eval g v" |
  "eval (Star f) v = star (eval f v)"

primrec vars :: "'a rlexp \<Rightarrow> nat set" where
  "vars (Var n) = {n}" |
  "vars (Const _) = {}" |
  "vars (Union f g) = vars f \<union> vars g" |
  "vars (Concat f g) = vars f \<union> vars g" |
  "vars (Star f) = vars f"

text \<open>Given some regular language expression, substituting each occurrence of a variable \<open>i\<close> by
the regular language expression \<open>s i\<close> yields the following regular language expression:\<close>
primrec subst :: "(nat \<Rightarrow> 'a rlexp) \<Rightarrow> 'a rlexp \<Rightarrow> 'a rlexp" where
  "subst s (Var n) = s n" |
  "subst _ (Const l) = Const l" |
  "subst s (Union f g) = Union (subst s f) (subst s g)" |
  "subst s (Concat f g) = Concat (subst s f) (subst s g)" |
  "subst s (Star f) = Star (subst s f)"



subsection \<open>Basic lemmas\<close>

lemma substitution_lemma:
  assumes "\<forall>i. v' i = eval (upd i) v"
  shows "eval (subst upd f) v = eval f v'"
  by (induction f rule: rlexp.induct) (use assms in auto)

lemma substitution_lemma_upd:
  "eval (subst (Var(x := f')) f) v = eval f (v(x := eval f' v))"
  using substitution_lemma[of "v(x := eval f' v)"] by force

lemma subst_id: "eval (subst Var f) v = eval f v"
  using substitution_lemma[of v] by simp

lemma vars_subst: "vars (subst upd f) = (\<Union>x \<in> vars f. vars (upd x))"
  by (induction f) auto

lemma vars_subst_upd_upper: "vars (subst (Var(x := fx)) f) \<subseteq> vars f - {x} \<union> vars fx"
proof
  fix y
  let ?upd = "Var(x := fx)"
  assume "y \<in> vars (subst ?upd f)"
  then obtain y' where "y' \<in> vars f \<and> y \<in> vars (?upd y')" using vars_subst by blast
  then show "y \<in> vars f - {x} \<union> vars fx" by (cases "x = y'") auto
qed


lemma eval_vars:
  assumes "\<forall>i \<in> vars f. s i = s' i"
  shows "eval f s = eval f s'"
  using assms by (induction f) auto

lemma eval_vars_subst:
  assumes "\<forall>i \<in> vars f. v i = eval (upd i) v"
  shows "eval (subst upd f) v = eval f v"
proof -
  let ?v' = "\<lambda>i. if i \<in> vars f then v i else eval (upd i) v"
  let ?v'' = "\<lambda>i. eval (upd i) v"
  have v'_v'': "?v' i = ?v'' i" for i using assms by simp
  then have v_v'': "\<forall>i. ?v'' i = eval (upd i) v" by simp
  from assms have "eval f v = eval f ?v'" using eval_vars[of f] by simp
  also have "\<dots> = eval (subst upd f) v"
    using assms substitution_lemma[OF v_v'', of f] by (simp add: eval_vars)
  finally show ?thesis by simp
qed


text \<open>\<^term>\<open>eval f\<close> is monotone:\<close>
lemma rlexp_mono:
  assumes "\<forall>i \<in> vars f. v i \<subseteq> v' i"
  shows "eval f v \<subseteq> eval f v'"
using assms proof (induction f rule: rlexp.induct)
  case (Star x)
  then show ?case
    by (smt (verit, best) eval.simps(5) in_star_iff_concat order_trans subsetI vars.simps(5))
qed fastforce+



subsection \<open>Continuity\<close>

(* TODO: rm, is in devel *)
lemma lang_pow_mono:
  fixes A :: "'a lang"
  assumes "A \<subseteq> B"
  shows "A ^^ n \<subseteq> B ^^ n"
  by (induction n) (use assms conc_mono[of A B] in auto)

lemma rlexp_cont_aux1:
  assumes "\<forall>i. v i \<le> v (Suc i)"
      and "w \<in> (\<Union>i. eval f (v i))"
    shows "w \<in> eval f (\<lambda>x. \<Union>i. v i x)"
proof -
  from assms(2) obtain n where n_intro: "w \<in> eval f (v n)" by auto
  have "v n x \<subseteq> (\<Union>i. v i x)" for x by auto
  with n_intro show "?thesis"
    using rlexp_mono[where v="v n" and v'="\<lambda>x. \<Union>i. v i x"] by auto
qed

lemma langpow_Union_eval:
  assumes "\<forall>i. v i \<le> v (Suc i)"
      and "w \<in> (\<Union>i. eval f (v i)) ^^ n"
    shows "w \<in> (\<Union>i. eval f (v i) ^^ n)"
using assms(2) proof (induction n arbitrary: w)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain u u' where w_decomp: "w = u@u'" and
    "u \<in> (\<Union>i. eval f (v i)) \<and> u' \<in> (\<Union>i. eval f (v i)) ^^ n" by fastforce
  with Suc have "u \<in> (\<Union>i. eval f (v i)) \<and> u' \<in> (\<Union>i. eval f (v i) ^^ n)" by auto
  then obtain i j where i_intro: "u \<in> eval f (v i)" and j_intro: "u' \<in> eval f (v j) ^^ n" by blast
  let ?m = "max i j"
  from i_intro Suc.prems(1) assms(1) rlexp_mono have 1: "u \<in> eval f (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded1 subset_eq)
  from Suc.prems(1) assms (1) rlexp_mono have "eval f (v j) \<subseteq> eval f (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded2)
  with j_intro lang_pow_mono have 2: "u' \<in> eval f (v ?m) ^^ n" by auto
  from 1 2 show ?case using w_decomp by auto
qed

lemma rlexp_cont_aux2:
  assumes "\<forall>i. v i \<le> v (Suc i)"
      and "w \<in> eval f (\<lambda>x. \<Union>i. v i x)"
    shows "w \<in> (\<Union>i. eval f (v i))"
using assms(2) proof (induction f arbitrary: w rule: rlexp.induct)
  case (Concat f g)
  then obtain u u' where w_decomp: "w = u@u'"
    and "u \<in> eval f (\<lambda>x. \<Union>i. v i x) \<and> u' \<in> eval g (\<lambda>x. \<Union>i. v i x)" by auto
  with Concat have "u \<in> (\<Union>i. eval f (v i)) \<and> u' \<in> (\<Union>i. eval g (v i))" by auto
  then obtain i j where i_intro: "u \<in> eval f (v i)" and j_intro: "u' \<in> eval g (v j)" by blast
  let ?m = "max i j"
  from i_intro Concat.prems(1) assms(1) rlexp_mono have "u \<in> eval f (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded1 subset_eq)
  moreover from j_intro Concat.prems(1) assms(1) rlexp_mono have "u' \<in> eval g (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded2 subset_eq)
  ultimately show ?case using w_decomp by auto
next
  case (Star f)
  then obtain n where n_intro: "w \<in> (eval f (\<lambda>x. \<Union>i. v i x)) ^^ n"
    using eval.simps(5) star_pow by blast
  with Star have "w \<in> (\<Union>i. eval f (v i)) ^^ n" using lang_pow_mono by blast
  with Star.prems assms have "w \<in> (\<Union>i. eval f (v i) ^^ n)" using langpow_Union_eval by auto
  then show ?case by (auto simp add: star_def)
qed fastforce+

text \<open>Now we prove that \<^term>\<open>eval f\<close> is continuous. This result is not needed in the further
proof, but it is interesting anyway:\<close>
(* currently unused *)
lemma rlexp_cont:
  assumes "\<forall>i. v i \<le> v (Suc i)"
  shows "eval f (\<lambda>x. \<Union>i. v i x) = (\<Union>i. eval f (v i))"
proof
  from assms show "eval f (\<lambda>x. \<Union>i. v i x) \<subseteq> (\<Union>i. eval f (v i))" using rlexp_cont_aux2 by auto
  from assms show "(\<Union>i. eval f (v i)) \<subseteq> eval f (\<lambda>x. \<Union>i. v i x)" using rlexp_cont_aux1 by blast
qed



subsection \<open>Regular language expressions which evaluate to regular languages\<close>

text \<open>Evaluating regular language expressions can yield non-regular languages even if
the valuation maps each variable to a regular language. This is because \<^const>\<open>Const\<close> may introduce
non-regular languages.
We therefore define the following predicate which guarantees that a regular language expression
\<open>f\<close> yields a regular language if the valuation maps all variables occurring in \<open>f\<close> to some regular
language. This is achieved by only allowing regular languages as constants.
However, note that this predicate is just an under-approximation, i.e.\ there exist regular language
expressions which do not satisfy this predicate but evaluate to regular languages anyway.\<close>

fun reg_eval :: "'a rlexp \<Rightarrow> bool" where
  "reg_eval (Var _) \<longleftrightarrow> True" |
  "reg_eval (Const l) \<longleftrightarrow> regular_lang l" |
  "reg_eval (Union f g) \<longleftrightarrow> reg_eval f \<and> reg_eval g" |
  "reg_eval (Concat f g) \<longleftrightarrow> reg_eval f \<and> reg_eval g" |
  "reg_eval (Star f) \<longleftrightarrow> reg_eval f"


lemma emptyset_regular: "reg_eval (Const {})"
  using lang.simps(1) reg_eval.simps(2) by blast

lemma epsilon_regular: "reg_eval (Const {[]})"
  using lang.simps(2) reg_eval.simps(2) by blast


text \<open>If the valuation \<open>v\<close> maps all variables occurring in the regular language expression \<open>f\<close> to
a regular language, then evaluating \<open>f\<close> again yields a regular language:\<close>
lemma reg_eval_regular:
  assumes "reg_eval f"
      and "\<And>n. n \<in> vars f \<Longrightarrow> regular_lang (v n)"
    shows "regular_lang (eval f v)"
using assms proof (induction f rule: reg_eval.induct)
  case (3 f g)
  then obtain r1 r2 where "Regular_Exp.lang r1 = eval f v \<and> Regular_Exp.lang r2 = eval g v" by auto
  then have "Regular_Exp.lang (Plus r1 r2) = eval (Union f g) v" by simp
  then show ?case by blast
next
  case (4 f g)
  then obtain r1 r2 where "Regular_Exp.lang r1 = eval f v \<and> Regular_Exp.lang r2 = eval g v" by auto
  then have "Regular_Exp.lang (Times r1 r2) = eval (Concat f g) v" by simp
  then show ?case by blast
next
  case (5 f)
  then obtain r  where "Regular_Exp.lang r = eval f v" by auto
  then have "Regular_Exp.lang (Regular_Exp.Star r) = eval (Star f) v" by simp
  then show ?case by blast
qed simp_all


text \<open>A \<^const>\<open>reg_eval\<close> regular language expression stays \<^const>\<open>reg_eval\<close> if all variables are substituted
by \<^const>\<open>reg_eval\<close> regular language expressions:\<close>
lemma subst_reg_eval:
  assumes "reg_eval f"
      and "\<forall>x \<in> vars f. reg_eval (upd x)"
    shows "reg_eval (subst upd f)"
  using assms by (induction f rule: reg_eval.induct) simp_all

lemma subst_reg_eval_update:
  assumes "reg_eval f"
      and "reg_eval g"
    shows "reg_eval (subst (Var(x := g)) f)"
  using assms subst_reg_eval fun_upd_def by (metis reg_eval.simps(1))


text \<open>For any finite union of \<^const>\<open>reg_eval\<close> regular language expressions exists a \<^const>\<open>reg_eval\<close> regular
language expression:\<close>
lemma finite_Union_regular_aux:
  "\<forall>f \<in> set fs. reg_eval f \<Longrightarrow> \<exists>g. reg_eval g \<and> \<Union>(vars ` set fs) = vars g
                                      \<and> (\<forall>v. (\<Union>f \<in> set fs. eval f v) = eval g v)"
proof (induction fs)
  case Nil
  then show ?case using emptyset_regular by fastforce
next
  case (Cons f1 fs)
  then obtain g where *: "reg_eval g \<and> \<Union>(vars ` set fs) = vars g
                          \<and> (\<forall>v. (\<Union>f\<in>set fs. eval f v) = eval g v)" by auto
  let ?g' = "Union f1 g"
  from Cons.prems * have "reg_eval ?g' \<and> \<Union> (vars ` set (f1 # fs)) = vars ?g'
      \<and> (\<forall>v. (\<Union>f\<in>set (f1 # fs). eval f v) = eval ?g' v)" by simp
  then show ?case by blast
qed

lemma finite_Union_regular:
  assumes "finite F"
      and "\<forall>f \<in> F. reg_eval f"
    shows "\<exists>g. reg_eval g \<and> \<Union>(vars ` F) = vars g \<and> (\<forall>v. (\<Union>f\<in>F. eval f v) = eval g v)"
  using assms finite_Union_regular_aux finite_list by metis



subsection \<open>Constant regular language expressions\<close>

text \<open>We call a regular language expression constant if it contains no variables. A constant
regular language expression always evaluates to the same language, independent on the valuation.
Thus, if the constant regular language expression is \<^const>\<open>reg_eval\<close>, then it evaluates to some
regular language, independent on the valuation.\<close>

abbreviation const_rlexp :: "'a rlexp \<Rightarrow> bool" where
  "const_rlexp f \<equiv> vars f = {}"

lemma const_rlexp_lang: "const_rlexp f \<Longrightarrow> \<exists>l. \<forall>v. eval f v = l"
  by (induction f) auto

lemma const_rlexp_regular_lang:
  assumes "const_rlexp f"
      and "reg_eval f"
    shows "\<exists>l. regular_lang l \<and> (\<forall>v. eval f v = l)"
  using assms const_rlexp_lang reg_eval_regular by fastforce

end
