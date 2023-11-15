section \<open>Syntax\<close>

theory Syntax
  imports
    "HOL-Library.Sublist"
    Utilities
begin

subsection \<open>Type symbols\<close>

datatype type =
  TInd ("i")
| TBool ("o")
| TFun type type (infixr "\<rightarrow>" 101)

primrec type_size :: "type \<Rightarrow> nat" where
  "type_size i = 1"
| "type_size o = 1"
| "type_size (\<alpha> \<rightarrow> \<beta>) = Suc (type_size \<alpha> + type_size \<beta>)"

primrec subtypes :: "type \<Rightarrow> type set" where
  "subtypes i = {}"
| "subtypes o = {}"
| "subtypes (\<alpha> \<rightarrow> \<beta>) = {\<alpha>, \<beta>} \<union> subtypes \<alpha> \<union> subtypes \<beta>"

lemma subtype_size_decrease:
  assumes "\<alpha> \<in> subtypes \<beta>"
  shows "type_size \<alpha> < type_size \<beta>"
  using assms by (induction rule: type.induct) force+

lemma subtype_is_not_type:
  assumes "\<alpha> \<in> subtypes \<beta>"
  shows "\<alpha> \<noteq> \<beta>"
  using assms and subtype_size_decrease by blast

lemma fun_type_atoms_in_subtypes:
  assumes "k < length ts"
  shows "ts ! k \<in> subtypes (foldr (\<rightarrow>) ts \<gamma>)"
  using assms by (induction ts arbitrary: k) (cases k, use less_Suc_eq_0_disj in \<open>fastforce+\<close>)

lemma fun_type_atoms_neq_fun_type:
  assumes "k < length ts"
  shows "ts ! k \<noteq> foldr (\<rightarrow>) ts \<gamma>"
  by (fact fun_type_atoms_in_subtypes[OF assms, THEN subtype_is_not_type])

subsection \<open>Variables\<close>

text \<open>
  Unfortunately, the Nominal package does not support multi-sort atoms yet; therefore, we need to
  implement this support from scratch.
\<close>

type_synonym var = "nat \<times> type"

abbreviation var_name :: "var \<Rightarrow> nat" where
  "var_name \<equiv> fst"

abbreviation var_type :: "var \<Rightarrow> type" where
  "var_type \<equiv> snd"

lemma fresh_var_existence:
  assumes "finite (vs :: var set)"
  obtains x where "(x, \<alpha>) \<notin> vs"
  using ex_new_if_finite[OF infinite_UNIV_nat]
proof -
  from assms obtain x where "x \<notin> var_name ` vs"
    using ex_new_if_finite[OF infinite_UNIV_nat] by fastforce
  with that show ?thesis
    by force
qed

lemma fresh_var_name_list_existence:
  assumes "finite (ns :: nat set)"
  obtains ns' where "length ns' = n" and "distinct ns'" and "lset ns' \<inter> ns = {}"
using assms proof (induction n arbitrary: thesis)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from assms obtain ns' where "length ns' = n" and "distinct ns'" and "lset ns' \<inter> ns = {}"
    using Suc.IH by blast
  moreover from assms obtain n' where "n' \<notin> lset ns' \<union> ns"
    using ex_new_if_finite[OF infinite_UNIV_nat] by blast
  ultimately
    have "length (n' # ns') = Suc n" and "distinct (n' # ns')" and "lset (n' # ns') \<inter> ns = {}"
    by simp_all
  with Suc.prems(1) show ?case
    by blast
qed

lemma fresh_var_list_existence:
  fixes xs :: "var list"
  and ns :: "nat set"
  assumes "finite ns"
  obtains vs' :: "var list"
  where "length vs' = length xs"
  and "distinct vs'"
  and "var_name ` lset vs' \<inter> (ns \<union> var_name ` lset xs) = {}"
  and "map var_type vs' = map var_type xs"
proof -
  from assms(1) have "finite (ns \<union> var_name ` lset xs)"
    by blast
  then obtain ns'
    where "length ns' = length xs"
    and "distinct ns'"
    and "lset ns' \<inter> (ns \<union> var_name ` lset xs) = {}"
    by (rule fresh_var_name_list_existence)
  define vs'' where "vs'' = zip ns' (map var_type xs)"
  from vs''_def and \<open>length ns' = length xs\<close> have "length vs'' = length xs"
    by simp
  moreover from vs''_def and \<open>distinct ns'\<close> have "distinct vs''"
    by (simp add: distinct_zipI1)
  moreover have "var_name ` lset vs'' \<inter> (ns \<union> var_name ` lset xs) = {}"
    unfolding vs''_def
    using \<open>length ns' = length xs\<close> and \<open>lset ns' \<inter> (ns \<union> var_name ` lset xs) = {}\<close>
    by (metis length_map set_map map_fst_zip)
  moreover from vs''_def have "map var_type vs'' = map var_type xs"
    by (simp add: \<open>length ns' = length xs\<close>)
  ultimately show ?thesis
    by (fact that)
qed

subsection \<open>Constants\<close>

type_synonym con = "nat \<times> type"

subsection \<open>Formulas\<close>

datatype form =
  FVar var
| FCon con
| FApp form form (infixl "\<sqdot>" 200)
| FAbs var form

syntax
  "_FVar" :: "nat \<Rightarrow> type \<Rightarrow> form" ("_\<^bsub>_\<^esub>" [899, 0] 900)
  "_FCon" :: "nat \<Rightarrow> type \<Rightarrow> form" ("\<lbrace>_\<rbrace>\<^bsub>_\<^esub>" [899, 0] 900)
  "_FAbs" :: "nat \<Rightarrow> type \<Rightarrow> form \<Rightarrow> form" ("(4\<lambda>_\<^bsub>_\<^esub>./ _)" [0, 0, 104] 104)
translations
  "x\<^bsub>\<alpha>\<^esub>" \<rightleftharpoons> "CONST FVar (x, \<alpha>)"
  "\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>" \<rightleftharpoons> "CONST FCon (c, \<alpha>)"
  "\<lambda>x\<^bsub>\<alpha>\<^esub>. A" \<rightleftharpoons> "CONST FAbs (x, \<alpha>) A"

subsection \<open>Generalized operators\<close>

text \<open>Generalized application. We define \<open>\<sqdot>\<^sup>\<Q>\<^sub>\<star> A [B\<^sub>1, B\<^sub>2, \<dots>, B\<^sub>n]\<close> as \<open>A \<sqdot> B\<^sub>1 \<sqdot> B\<^sub>2 \<sqdot> \<cdots> \<sqdot> B\<^sub>n\<close>:\<close>

definition generalized_app :: "form \<Rightarrow> form list \<Rightarrow> form" ("\<sqdot>\<^sup>\<Q>\<^sub>\<star> _ _" [241, 241] 241) where
  [simp]: "\<sqdot>\<^sup>\<Q>\<^sub>\<star> A Bs = foldl (\<sqdot>) A Bs"

text \<open>Generalized abstraction. We define \<open>\<lambda>\<^sup>\<Q>\<^sub>\<star> [x\<^sub>1, \<dots>, x\<^sub>n] A\<close> as \<open>\<lambda>x\<^sub>1. \<cdots> \<lambda>x\<^sub>n. A\<close>:\<close>

definition generalized_abs :: "var list \<Rightarrow> form \<Rightarrow> form" ("\<lambda>\<^sup>\<Q>\<^sub>\<star> _ _" [141, 141] 141) where
  [simp]: "\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A = foldr (\<lambda>(x, \<alpha>) B. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) vs A"

fun form_size :: "form \<Rightarrow> nat" where
  "form_size (x\<^bsub>\<alpha>\<^esub>) = 1"
| "form_size (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = 1"
| "form_size (A \<sqdot> B) = Suc (form_size A + form_size B)"
| "form_size (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = Suc (form_size A)"

fun form_depth :: "form \<Rightarrow> nat" where
  "form_depth (x\<^bsub>\<alpha>\<^esub>) = 0"
| "form_depth (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = 0"
| "form_depth (A \<sqdot> B) = Suc (max (form_depth A) (form_depth B))"
| "form_depth (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = Suc (form_depth A)"

subsection \<open>Subformulas\<close>

fun subforms :: "form \<Rightarrow> form set" where
  "subforms (x\<^bsub>\<alpha>\<^esub>) = {}"
| "subforms (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = {}"
| "subforms (A \<sqdot> B) = {A, B}"
| "subforms (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = {A}"

datatype direction = Left ("\<guillemotleft>") | Right ("\<guillemotright>")
type_synonym position = "direction list"

fun positions :: "form \<Rightarrow> position set" where
  "positions (x\<^bsub>\<alpha>\<^esub>) = {[]}"
| "positions (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = {[]}"
| "positions (A \<sqdot> B) = {[]} \<union> {\<guillemotleft> # p | p. p \<in> positions A} \<union> {\<guillemotright> # p | p. p \<in> positions B}"
| "positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = {[]} \<union> {\<guillemotleft> # p | p. p \<in> positions A}"

lemma empty_is_position [simp]:
  shows "[] \<in> positions A"
  by (cases A rule: positions.cases) simp_all

fun subform_at :: "form \<Rightarrow> position \<rightharpoonup> form" where
  "subform_at A [] = Some A"
| "subform_at (A \<sqdot> B) (\<guillemotleft> # p) = subform_at A p"
| "subform_at (A \<sqdot> B) (\<guillemotright> # p) = subform_at B p"
| "subform_at (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) (\<guillemotleft> # p) = subform_at A p"
| "subform_at _ _ = None"

fun is_subform_at :: "form \<Rightarrow> position \<Rightarrow> form \<Rightarrow> bool" ("(_ \<preceq>\<^bsub>_\<^esub>/ _)" [51,0,51] 50) where
  "is_subform_at A [] A' = (A = A')"
| "is_subform_at C (\<guillemotleft> # p) (A \<sqdot> B) = is_subform_at C p A"
| "is_subform_at C (\<guillemotright> # p) (A \<sqdot> B) = is_subform_at C p B"
| "is_subform_at C (\<guillemotleft> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = is_subform_at C p A"
| "is_subform_at _ _ _ = False"

lemma is_subform_at_alt_def:
  shows "A' \<preceq>\<^bsub>p\<^esub> A = (case subform_at A p of Some B \<Rightarrow> B = A' | None \<Rightarrow> False)"
  by (induction A' p A rule: is_subform_at.induct) auto

lemma superform_existence:
  assumes "B \<preceq>\<^bsub>p @ [d]\<^esub> C"
  obtains A where "B \<preceq>\<^bsub>[d]\<^esub> A" and "A \<preceq>\<^bsub>p\<^esub> C"
  using assms by (induction B p C rule: is_subform_at.induct) auto

lemma subform_at_subforms_con:
  assumes "\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> \<preceq>\<^bsub>p\<^esub> C"
  shows "\<nexists>A. A \<preceq>\<^bsub>p @ [d]\<^esub> C"
  using assms by (induction "\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>" p C rule: is_subform_at.induct) auto

lemma subform_at_subforms_var:
  assumes "x\<^bsub>\<alpha>\<^esub> \<preceq>\<^bsub>p\<^esub> C"
  shows "\<nexists>A. A \<preceq>\<^bsub>p @ [d]\<^esub> C"
  using assms by (induction "x\<^bsub>\<alpha>\<^esub>" p C rule: is_subform_at.induct) auto

lemma subform_at_subforms_app:
  assumes "A \<sqdot> B \<preceq>\<^bsub>p\<^esub> C"
  shows "A \<preceq>\<^bsub>p @ [\<guillemotleft>]\<^esub> C" and "B \<preceq>\<^bsub>p @ [\<guillemotright>]\<^esub> C"
  using assms by (induction "A \<sqdot> B" p C rule: is_subform_at.induct) auto

lemma subform_at_subforms_abs:
  assumes "\<lambda>x\<^bsub>\<alpha>\<^esub>. A \<preceq>\<^bsub>p\<^esub> C"
  shows "A \<preceq>\<^bsub>p @ [\<guillemotleft>]\<^esub> C"
  using assms by (induction "\<lambda>x\<^bsub>\<alpha>\<^esub>. A" p C rule: is_subform_at.induct) auto

lemma is_subform_implies_in_positions:
  assumes "B \<preceq>\<^bsub>p\<^esub> A"
  shows "p \<in> positions A"
  using assms by (induction rule: is_subform_at.induct) simp_all

lemma subform_size_decrease:
  assumes "A \<preceq>\<^bsub>p\<^esub> B" and "p \<noteq> []"
  shows "form_size A < form_size B"
  using assms by (induction A p B rule: is_subform_at.induct) force+

lemma strict_subform_is_not_form:
  assumes "p \<noteq> []" and "A' \<preceq>\<^bsub>p\<^esub> A"
  shows "A' \<noteq> A"
  using assms and subform_size_decrease by blast

lemma no_right_subform_of_abs:
  shows "\<nexists>B. B \<preceq>\<^bsub>\<guillemotright> # p\<^esub> \<lambda>x\<^bsub>\<alpha>\<^esub>. A"
  by simp

lemma subforms_from_var:
  assumes "A \<preceq>\<^bsub>p\<^esub> x\<^bsub>\<alpha>\<^esub>"
  shows "A = x\<^bsub>\<alpha>\<^esub>" and "p = []"
  using assms by (auto elim: is_subform_at.elims)

lemma subforms_from_con:
  assumes "A \<preceq>\<^bsub>p\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>"
  shows "A = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>" and "p = []"
  using assms by (auto elim: is_subform_at.elims)

lemma subforms_from_app:
  assumes "A \<preceq>\<^bsub>p\<^esub> B \<sqdot> C"
  shows "
    (A = B \<sqdot> C \<and> p = []) \<or>
    (A \<noteq> B \<sqdot> C \<and>
      (\<exists>p' \<in> positions B. p = \<guillemotleft> # p' \<and> A \<preceq>\<^bsub>p'\<^esub> B) \<or> (\<exists>p' \<in> positions C. p = \<guillemotright> # p' \<and> A \<preceq>\<^bsub>p'\<^esub> C))"
  using assms and strict_subform_is_not_form
  by (auto simp add: is_subform_implies_in_positions elim: is_subform_at.elims)

lemma subforms_from_abs:
  assumes "A \<preceq>\<^bsub>p\<^esub> \<lambda>x\<^bsub>\<alpha>\<^esub>. B"
  shows "(A = \<lambda>x\<^bsub>\<alpha>\<^esub>. B \<and> p = []) \<or> (A \<noteq> \<lambda>x\<^bsub>\<alpha>\<^esub>. B \<and> (\<exists>p' \<in> positions B. p = \<guillemotleft> # p' \<and> A \<preceq>\<^bsub>p'\<^esub> B))"
  using assms and strict_subform_is_not_form
  by (auto simp add: is_subform_implies_in_positions elim: is_subform_at.elims)

lemma leftmost_subform_in_generalized_app:
  shows "B \<preceq>\<^bsub>replicate (length As) \<guillemotleft>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> B As"
  by (induction As arbitrary: B) (simp_all, metis replicate_append_same subform_at_subforms_app(1))

lemma self_subform_is_at_top:
  assumes "A \<preceq>\<^bsub>p\<^esub> A"
  shows "p = []"
  using assms and strict_subform_is_not_form by blast

lemma at_top_is_self_subform:
  assumes "A \<preceq>\<^bsub>[]\<^esub> B"
  shows "A = B"
  using assms by (auto elim: is_subform_at.elims)

lemma is_subform_at_uniqueness:
  assumes "B \<preceq>\<^bsub>p\<^esub> A" and "C \<preceq>\<^bsub>p\<^esub> A"
  shows "B = C"
  using assms by (induction A arbitrary: p B C) (auto elim: is_subform_at.elims)

lemma is_subform_at_existence:
  assumes "p \<in> positions A"
  obtains B where "B \<preceq>\<^bsub>p\<^esub> A"
  using assms by (induction A arbitrary: p) (auto elim: is_subform_at.elims, blast+)

lemma is_subform_at_transitivity:
  assumes "A \<preceq>\<^bsub>p\<^sub>1\<^esub> B" and "B \<preceq>\<^bsub>p\<^sub>2\<^esub> C"
  shows "A \<preceq>\<^bsub>p\<^sub>2 @ p\<^sub>1\<^esub> C"
  using assms by (induction B p\<^sub>2 C arbitrary: A p\<^sub>1 rule: is_subform_at.induct) simp_all

lemma subform_nesting:
  assumes "strict_prefix p' p"
  and "B \<preceq>\<^bsub>p'\<^esub> A"
  and "C \<preceq>\<^bsub>p\<^esub> A"
  shows "C \<preceq>\<^bsub>drop (length p') p\<^esub> B"
proof -
  from assms(1) have "p \<noteq> []"
    using strict_prefix_simps(1) by blast
  with assms(1,3) show ?thesis
  proof (induction p arbitrary: C rule: rev_induct)
    case Nil
    then show ?case
      by blast
  next
    case (snoc d p'')
    then show ?case
    proof (cases "p'' = p'")
      case True
      obtain A' where "C \<preceq>\<^bsub>[d]\<^esub> A'" and "A' \<preceq>\<^bsub>p'\<^esub> A"
        by (fact superform_existence[OF snoc.prems(2)[unfolded True]])
      from \<open>A' \<preceq>\<^bsub>p'\<^esub> A\<close> and assms(2) have "A' = B"
        by (rule is_subform_at_uniqueness)
      with \<open>C \<preceq>\<^bsub>[d]\<^esub> A'\<close> have "C \<preceq>\<^bsub>[d]\<^esub> B"
        by (simp only:)
      with True show ?thesis
        by auto
    next
      case False
      with snoc.prems(1) have "strict_prefix p' p''"
        using prefix_order.dual_order.strict_implies_order by fastforce
      then have "p'' \<noteq> []"
        by force
      moreover from snoc.prems(2) obtain A' where "C \<preceq>\<^bsub>[d]\<^esub> A'" and "A' \<preceq>\<^bsub>p''\<^esub> A"
        using superform_existence by blast
      ultimately have "A' \<preceq>\<^bsub>drop (length p') p''\<^esub> B"
        using snoc.IH and \<open>strict_prefix p' p''\<close> by blast
      with \<open>C \<preceq>\<^bsub>[d]\<^esub> A'\<close> and snoc.prems(1) show ?thesis
        using is_subform_at_transitivity and prefix_length_less by fastforce
    qed
  qed
qed

lemma loop_subform_impossibility:
  assumes "B \<preceq>\<^bsub>p\<^esub> A"
  and "strict_prefix p' p"
  shows "\<not> B \<preceq>\<^bsub>p'\<^esub> A"
  using assms and prefix_length_less and self_subform_is_at_top and subform_nesting by fastforce

lemma nested_subform_size_decreases:
  assumes "strict_prefix p' p"
  and "B \<preceq>\<^bsub>p'\<^esub> A"
  and "C \<preceq>\<^bsub>p\<^esub> A"
  shows "form_size C < form_size B"
proof -
  from assms(1) have "p \<noteq> []"
    by force
  have "C \<preceq>\<^bsub>drop (length p') p\<^esub> B"
    by (fact subform_nesting[OF assms])
  moreover have "drop (length p') p \<noteq> []"
    using prefix_length_less[OF assms(1)] by force
  ultimately show ?thesis
    using subform_size_decrease by simp
qed

definition is_subform :: "form \<Rightarrow> form \<Rightarrow> bool" (infix "\<preceq>" 50) where
  [simp]: "A \<preceq> B = (\<exists>p. A \<preceq>\<^bsub>p\<^esub> B)"

instantiation form :: ord
begin

definition
  "A \<le> B \<longleftrightarrow> A \<preceq> B"

definition
  "A < B \<longleftrightarrow> A \<preceq> B \<and> A \<noteq> B"

instance ..

end

instance form :: preorder
proof (standard, unfold less_eq_form_def less_form_def)
  fix A
  show "A \<preceq> A"
    unfolding is_subform_def using is_subform_at.simps(1) by blast
next
  fix A and B and C
  assume "A \<preceq> B" and "B \<preceq> C"
  then show "A \<preceq> C"
    unfolding is_subform_def using is_subform_at_transitivity by blast
next
  fix A and B
  show "A \<preceq> B \<and> A \<noteq> B \<longleftrightarrow> A \<preceq> B \<and> \<not> B \<preceq> A"
    unfolding is_subform_def
    by (metis is_subform_at.simps(1) not_less_iff_gr_or_eq subform_size_decrease)
qed

lemma position_subform_existence_equivalence:
  shows "p \<in> positions A \<longleftrightarrow> (\<exists>A'. A' \<preceq>\<^bsub>p\<^esub> A)"
  by (meson is_subform_at_existence is_subform_implies_in_positions)

lemma position_prefix_is_position:
  assumes "p \<in> positions A" and "prefix p' p"
  shows "p' \<in> positions A"
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc d p'')
  from snoc.prems(1) have "p'' \<in> positions A"
    by (meson position_subform_existence_equivalence superform_existence)
  with snoc.prems(1,2) show ?case
    using snoc.IH by fastforce
qed

subsection \<open>Free and bound variables\<close>

consts vars :: "'a \<Rightarrow> var set"

overloading
  "vars_form" \<equiv> "vars :: form \<Rightarrow> var set"
  "vars_form_set" \<equiv> "vars :: form set \<Rightarrow> var set" (* abuse of notation *)
begin

fun vars_form :: "form \<Rightarrow> var set" where
  "vars_form (x\<^bsub>\<alpha>\<^esub>) = {(x, \<alpha>)}"
| "vars_form (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = {}"
| "vars_form (A \<sqdot> B) = vars_form A \<union> vars_form B"
| "vars_form (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = vars_form A \<union> {(x, \<alpha>)}"

fun vars_form_set :: "form set \<Rightarrow> var set" where
  "vars_form_set S = (\<Union>A \<in> S. vars A)"

end

abbreviation var_names :: "'a \<Rightarrow> nat set" where
  "var_names \<X> \<equiv> var_name ` (vars \<X>)"

lemma vars_form_finiteness:
  fixes A :: form
  shows "finite (vars A)"
  by (induction rule: vars_form.induct) simp_all

lemma vars_form_set_finiteness:
  fixes S :: "form set"
  assumes "finite S"
  shows "finite (vars S)"
  using assms unfolding vars_form_set.simps using vars_form_finiteness by blast

lemma form_var_names_finiteness:
  fixes A :: form
  shows "finite (var_names A)"
  using vars_form_finiteness by blast

lemma form_set_var_names_finiteness:
  fixes S :: "form set"
  assumes "finite S"
  shows "finite (var_names S)"
  using assms and vars_form_set_finiteness by blast

consts free_vars :: "'a \<Rightarrow> var set"

overloading
  "free_vars_form" \<equiv> "free_vars :: form \<Rightarrow> var set"
  "free_vars_form_set" \<equiv> "free_vars :: form set \<Rightarrow> var set" (* abuse of notation *)
begin

fun free_vars_form :: "form \<Rightarrow> var set" where
  "free_vars_form (x\<^bsub>\<alpha>\<^esub>) = {(x, \<alpha>)}"
| "free_vars_form (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = {}"
| "free_vars_form (A \<sqdot> B) = free_vars_form A \<union> free_vars_form B"
| "free_vars_form (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = free_vars_form A - {(x, \<alpha>)}"

fun free_vars_form_set :: "form set \<Rightarrow> var set" where
  "free_vars_form_set S = (\<Union>A \<in> S. free_vars A)"

end

abbreviation free_var_names :: "'a \<Rightarrow> nat set" where
  "free_var_names \<X> \<equiv> var_name ` (free_vars \<X>)"

lemma free_vars_form_finiteness:
  fixes A :: form
  shows "finite (free_vars A)"
  by (induction rule: free_vars_form.induct) simp_all

lemma free_vars_of_generalized_app:
  shows "free_vars (\<sqdot>\<^sup>\<Q>\<^sub>\<star> A Bs) = free_vars A \<union> free_vars (lset Bs)"
  by (induction Bs arbitrary: A) auto

lemma free_vars_of_generalized_abs:
  shows "free_vars (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) = free_vars A - lset vs"
  by (induction vs arbitrary: A) auto

lemma free_vars_in_all_vars:
  fixes A :: form
  shows "free_vars A \<subseteq> vars A"
proof (induction A)
  case (FVar v)
  then show ?case
    using surj_pair[of v] by force
next
  case (FCon k)
  then show ?case
    using surj_pair[of k] by force
next
  case (FApp A B)
  have "free_vars (A \<sqdot> B) = free_vars A \<union> free_vars B"
    using free_vars_form.simps(3) .
  also from FApp.IH have "\<dots> \<subseteq> vars A \<union> vars B"
    by blast
  also have "\<dots> = vars (A \<sqdot> B)"
    using vars_form.simps(3)[symmetric] .
  finally show ?case
    by (simp only:)
next
  case (FAbs v A)
  then show ?case
    using surj_pair[of v] by force
qed

lemma free_vars_in_all_vars_set:
  fixes S :: "form set"
  shows "free_vars S \<subseteq> vars S"
  using free_vars_in_all_vars by fastforce

lemma singleton_form_set_vars:
  shows "vars {FVar y} = {y}"
  using surj_pair[of y] by force

fun bound_vars where
  "bound_vars (x\<^bsub>\<alpha>\<^esub>) = {}"
| "bound_vars (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = {}"
| "bound_vars (B \<sqdot> C) = bound_vars B \<union> bound_vars C"
| "bound_vars (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) = {(x, \<alpha>)} \<union> bound_vars B"

lemma vars_is_free_and_bound_vars:
  shows "vars A = free_vars A \<union> bound_vars A"
  by (induction A) auto

fun binders_at :: "form \<Rightarrow> position \<Rightarrow> var set" where
  "binders_at (A \<sqdot> B) (\<guillemotleft> # p) = binders_at A p"
| "binders_at (A \<sqdot> B) (\<guillemotright> # p) = binders_at B p"
| "binders_at (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) (\<guillemotleft> # p) = {(x, \<alpha>)} \<union> binders_at A p"
| "binders_at A [] = {}"
| "binders_at A p = {}"

lemma binders_at_concat:
  assumes "A' \<preceq>\<^bsub>p\<^esub> A"
  shows "binders_at A (p @ p') = binders_at A p \<union> binders_at A' p'"
  using assms by (induction p A rule: is_subform_at.induct) auto

subsection \<open>Free and bound occurrences\<close>

definition occurs_at :: "var \<Rightarrow> position \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "occurs_at v p B \<longleftrightarrow> (FVar v \<preceq>\<^bsub>p\<^esub> B)"

lemma occurs_at_alt_def:
  shows "occurs_at v [] (FVar v') \<longleftrightarrow> (v = v')"
  and "occurs_at v p (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) \<longleftrightarrow> False"
  and "occurs_at v (\<guillemotleft> # p) (A \<sqdot> B) \<longleftrightarrow> occurs_at v p A"
  and "occurs_at v (\<guillemotright> # p) (A \<sqdot> B) \<longleftrightarrow> occurs_at v p B"
  and "occurs_at v (\<guillemotleft> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) \<longleftrightarrow> occurs_at v p A"
  and "occurs_at v (d # p) (FVar v') \<longleftrightarrow> False"
  and "occurs_at v (\<guillemotright> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) \<longleftrightarrow> False"
  and "occurs_at v [] (A \<sqdot> B) \<longleftrightarrow> False"
  and "occurs_at v [] (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) \<longleftrightarrow> False"
  by (fastforce elim: is_subform_at.elims)+

definition occurs :: "var \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "occurs v B \<longleftrightarrow> (\<exists>p \<in> positions B. occurs_at v p B)"

lemma occurs_in_vars:
  assumes "occurs v A"
  shows "v \<in> vars A"
  using assms by (induction A) force+

abbreviation strict_prefixes where
  "strict_prefixes xs \<equiv> [ys \<leftarrow> prefixes xs. ys \<noteq> xs]"

definition in_scope_of_abs :: "var \<Rightarrow> position \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "in_scope_of_abs v p B \<longleftrightarrow> (
    p \<noteq> [] \<and>
    (
      \<exists>p' \<in> lset (strict_prefixes p).
        case (subform_at B p') of
          Some (FAbs v' _) \<Rightarrow> v = v'
        | _ \<Rightarrow> False
    )
  )"

lemma in_scope_of_abs_alt_def:
  shows "
    in_scope_of_abs v p B
    \<longleftrightarrow>
    p \<noteq> [] \<and> (\<exists>p' \<in> positions B. \<exists>C. strict_prefix p' p \<and> FAbs v C \<preceq>\<^bsub>p'\<^esub> B)"
proof
  assume "in_scope_of_abs v p B"
  then show "p \<noteq> [] \<and> (\<exists>p' \<in> positions B. \<exists>C. strict_prefix p' p \<and> FAbs v C \<preceq>\<^bsub>p'\<^esub> B)"
    by (induction rule: subform_at.induct) force+
next
  assume "p \<noteq> [] \<and> (\<exists>p' \<in> positions B. \<exists>C. strict_prefix p' p \<and> FAbs v C \<preceq>\<^bsub>p'\<^esub> B)"
  then show "in_scope_of_abs v p B"
    by (induction rule: subform_at.induct) fastforce+
qed

lemma in_scope_of_abs_in_left_app:
  shows "in_scope_of_abs v (\<guillemotleft> # p) (A \<sqdot> B) \<longleftrightarrow> in_scope_of_abs v p A"
  by force

lemma in_scope_of_abs_in_right_app:
  shows "in_scope_of_abs v (\<guillemotright> # p) (A \<sqdot> B) \<longleftrightarrow> in_scope_of_abs v p B"
  by force

lemma in_scope_of_abs_in_app:
  assumes "in_scope_of_abs v p (A \<sqdot> B)"
  obtains p' where "(p = \<guillemotleft> # p' \<and> in_scope_of_abs v p' A) \<or> (p = \<guillemotright> # p' \<and> in_scope_of_abs v p' B)"
proof -
  from assms obtain d and p' where "p = d # p'"
    unfolding in_scope_of_abs_def by (meson list.exhaust)
  then show ?thesis
  proof (cases d)
    case Left
    with assms and \<open>p = d # p'\<close> show ?thesis
      using that and in_scope_of_abs_in_left_app by simp
  next
    case Right
    with assms and \<open>p = d # p'\<close> show ?thesis
      using that and in_scope_of_abs_in_right_app by simp
  qed
qed

lemma not_in_scope_of_abs_in_app:
  assumes "
    \<forall>p'.
      (p = \<guillemotleft> # p' \<longrightarrow> \<not> in_scope_of_abs v' p' A)
      \<and>
      (p = \<guillemotright> # p' \<longrightarrow> \<not> in_scope_of_abs v' p' B)"
  shows "\<not> in_scope_of_abs v' p (A \<sqdot> B)"
  using assms and in_scope_of_abs_in_app by metis

lemma in_scope_of_abs_in_abs:
  shows "in_scope_of_abs v (\<guillemotleft> # p) (FAbs v' B) \<longleftrightarrow> v = v' \<or> in_scope_of_abs v p B"
proof
  assume "in_scope_of_abs v (\<guillemotleft> # p) (FAbs v' B)"
  then obtain p' and C
    where "p' \<in> positions (FAbs v' B)"
    and "strict_prefix p' (\<guillemotleft> # p)"
    and "FAbs v C \<preceq>\<^bsub>p'\<^esub> FAbs v' B"
    unfolding in_scope_of_abs_alt_def by blast
  then show "v = v' \<or> in_scope_of_abs v p B"
  proof (cases p')
    case Nil
    with \<open>FAbs v C \<preceq>\<^bsub>p'\<^esub> FAbs v' B\<close> have "v = v'"
      by auto
    then show ?thesis
      by simp
  next
    case (Cons d p'')
    with \<open>strict_prefix p' (\<guillemotleft> # p)\<close> have "d = \<guillemotleft>"
      by simp
    from \<open>FAbs v C \<preceq>\<^bsub>p'\<^esub> FAbs v' B\<close> and Cons have "p'' \<in> positions B"
      by
        (cases "(FAbs v C, p', FAbs v' B)" rule: is_subform_at.cases)
        (simp_all add: is_subform_implies_in_positions)
    moreover from \<open>FAbs v C \<preceq>\<^bsub>p'\<^esub> FAbs v' B\<close> and Cons and \<open>d = \<guillemotleft>\<close> have "FAbs v C \<preceq>\<^bsub>p''\<^esub> B"
      by (metis is_subform_at.simps(4) old.prod.exhaust)
    moreover from \<open>strict_prefix p' (\<guillemotleft> # p)\<close> and Cons have "strict_prefix p'' p"
      by auto
    ultimately have "in_scope_of_abs v p B"
      using in_scope_of_abs_alt_def by auto
    then show ?thesis
      by simp
  qed
next
  assume "v = v' \<or> in_scope_of_abs v p B"
  then show "in_scope_of_abs v (\<guillemotleft> # p) (FAbs v' B)"
    unfolding in_scope_of_abs_alt_def
    using position_subform_existence_equivalence and surj_pair[of v']
    by force
qed

lemma not_in_scope_of_abs_in_var:
  shows "\<not> in_scope_of_abs v p (FVar v')"
  unfolding in_scope_of_abs_def by (cases p) simp_all

lemma in_scope_of_abs_in_vars:
  assumes "in_scope_of_abs v p A"
  shows "v \<in> vars A"
using assms proof (induction A arbitrary: p)
  case (FVar v')
  then show ?case
    using not_in_scope_of_abs_in_var by blast
next
  case (FCon k)
  then show ?case
    using in_scope_of_abs_alt_def by (blast elim: is_subform_at.elims(2))
next
  case (FApp B C)
  from FApp.prems obtain d and p' where "p = d # p'"
    unfolding in_scope_of_abs_def by (meson neq_Nil_conv)
  then show ?case
  proof (cases d)
    case Left
    with FApp.prems and \<open>p = d # p'\<close> have "in_scope_of_abs v p' B"
      using in_scope_of_abs_in_left_app by blast
    then have "v \<in> vars B"
      by (fact FApp.IH(1))
    then show ?thesis
      by simp
  next
    case Right
    with FApp.prems and \<open>p = d # p'\<close> have "in_scope_of_abs v p' C"
      using in_scope_of_abs_in_right_app by blast
    then have "v \<in> vars C"
      by (fact FApp.IH(2))
    then show ?thesis
      by simp
  qed
next
  case (FAbs v' B)
  then show ?case
  proof (cases "v = v'")
    case True
    then show ?thesis
      using surj_pair[of v] by force
  next
    case False
    with FAbs.prems obtain p' and d where "p = d # p'"
      unfolding in_scope_of_abs_def by (meson neq_Nil_conv)
    then show ?thesis
    proof (cases d)
      case Left
      with FAbs.prems and False and \<open>p = d # p'\<close> have "in_scope_of_abs v p' B"
        using in_scope_of_abs_in_abs by blast
      then have "v \<in> vars B"
        by (fact FAbs.IH)
      then show ?thesis
        using surj_pair[of v'] by force
    next
      case Right
      with FAbs.prems and \<open>p = d # p'\<close> and False show ?thesis
        by (cases rule: is_subform_at.cases) auto
    qed
  qed
qed

lemma binders_at_alt_def:
  assumes "p \<in> positions A"
  shows "binders_at A p = {v | v. in_scope_of_abs v p A}"
  using assms and in_set_prefixes by (induction rule: binders_at.induct) auto

definition is_bound_at :: "var \<Rightarrow> position \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_bound_at v p B \<longleftrightarrow> occurs_at v p B \<and> in_scope_of_abs v p B"

lemma not_is_bound_at_in_var:
  shows "\<not> is_bound_at v p (FVar v')"
  by (fastforce elim: is_subform_at.elims(2))

lemma not_is_bound_at_in_con:
  shows "\<not> is_bound_at v p (FCon k)"
  by (fastforce elim: is_subform_at.elims(2))

lemma is_bound_at_in_left_app:
  shows "is_bound_at v (\<guillemotleft> # p) (B \<sqdot> C) \<longleftrightarrow> is_bound_at v p B"
  by auto

lemma is_bound_at_in_right_app:
  shows "is_bound_at v (\<guillemotright> # p) (B \<sqdot> C) \<longleftrightarrow> is_bound_at v p C"
  by auto

lemma is_bound_at_from_app:
  assumes "is_bound_at v p (B \<sqdot> C)"
  obtains p' where "(p = \<guillemotleft> # p' \<and> is_bound_at v p' B) \<or> (p = \<guillemotright> # p' \<and> is_bound_at v p' C)"
proof -
  from assms obtain d and p' where "p = d # p'"
    using subforms_from_app by blast
  then show ?thesis
  proof (cases d)
    case Left
    with assms and that and \<open>p = d # p'\<close> show ?thesis
      using is_bound_at_in_left_app by simp
  next
    case Right
    with assms and that and \<open>p = d # p'\<close> show ?thesis
      using is_bound_at_in_right_app by simp
  qed
qed

lemma is_bound_at_from_abs:
  assumes "is_bound_at v (\<guillemotleft> # p) (FAbs v' B)"
  shows "v = v' \<or> is_bound_at v p B"
  using assms by (fastforce elim: is_subform_at.elims)

lemma is_bound_at_from_absE:
  assumes "is_bound_at v p (FAbs v' B)"
  obtains p' where "p = \<guillemotleft> # p'" and "v = v' \<or> is_bound_at v p' B"
proof -
  obtain x and \<alpha> where "v' = (x, \<alpha>)"
    by fastforce
  with assms obtain p' where "p = \<guillemotleft> # p'"
    using subforms_from_abs by blast
  with assms and that show ?thesis
    using is_bound_at_from_abs by simp
qed

lemma is_bound_at_to_abs:
  assumes "(v = v' \<and> occurs_at v p B) \<or> is_bound_at v p B"
  shows "is_bound_at v (\<guillemotleft> # p) (FAbs v' B)"
unfolding is_bound_at_def proof
  from assms(1) show "occurs_at v (\<guillemotleft> # p) (FAbs v' B)"
    using surj_pair[of v'] by force
  from assms show "in_scope_of_abs v (\<guillemotleft> # p) (FAbs v' B)"
    using in_scope_of_abs_in_abs by auto
qed

lemma is_bound_at_in_bound_vars:
  assumes "p \<in> positions A"
  and "is_bound_at v p A \<or> v \<in> binders_at A p"
  shows "v \<in> bound_vars A"
using assms proof (induction A arbitrary: p)
  case (FApp B C)
  from FApp.prems(2) consider (a) "is_bound_at v p (B \<sqdot> C)" | (b) "v \<in> binders_at (B \<sqdot> C) p"
    by blast
  then show ?case
  proof cases
    case a
    then have "p \<noteq> []"
      using occurs_at_alt_def(8) by blast
    then obtain d and p' where "p = d # p'"
      by (meson list.exhaust)
    with \<open>p \<in> positions (B \<sqdot> C)\<close>
    consider (a\<^sub>1) "p = \<guillemotleft> # p'" and "p' \<in> positions B" | (a\<^sub>2) "p = \<guillemotright> # p'" and "p' \<in> positions C"
      by force
    then show ?thesis
    proof cases
      case a\<^sub>1
      from a\<^sub>1(1) and \<open>is_bound_at v p (B \<sqdot> C)\<close> have "is_bound_at v p' B"
        using is_bound_at_in_left_app by blast
      with a\<^sub>1(2) have "v \<in> bound_vars B"
        using FApp.IH(1) by blast
      then show ?thesis
        by simp
    next
      case a\<^sub>2
      from a\<^sub>2(1) and \<open>is_bound_at v p (B \<sqdot> C)\<close> have "is_bound_at v p' C"
        using is_bound_at_in_right_app by blast
      with a\<^sub>2(2) have "v \<in> bound_vars C"
        using FApp.IH(2) by blast
      then show ?thesis
        by simp
    qed
  next
    case b
    then have "p \<noteq> []"
      by force
    then obtain d and p' where "p = d # p'"
      by (meson list.exhaust)
    with \<open>p \<in> positions (B \<sqdot> C)\<close>
    consider (b\<^sub>1) "p = \<guillemotleft> # p'" and "p' \<in> positions B" | (b\<^sub>2) "p = \<guillemotright> # p'" and "p' \<in> positions C"
      by force
    then show ?thesis
    proof cases
      case b\<^sub>1
      from b\<^sub>1(1) and \<open>v \<in> binders_at (B \<sqdot> C) p\<close> have "v \<in> binders_at B p'"
        by force
      with b\<^sub>1(2) have "v \<in> bound_vars B"
        using FApp.IH(1) by blast
      then show ?thesis
        by simp
    next
      case b\<^sub>2
      from b\<^sub>2(1) and \<open>v \<in> binders_at (B \<sqdot> C) p\<close> have "v \<in> binders_at C p'"
        by force
      with b\<^sub>2(2) have "v \<in> bound_vars C"
        using FApp.IH(2) by blast
      then show ?thesis
        by simp
    qed
  qed
next
  case (FAbs v' B)
  from FAbs.prems(2) consider (a) "is_bound_at v p (FAbs v' B)" | (b) "v \<in> binders_at (FAbs v' B) p"
    by blast
  then show ?case
  proof cases
    case a
    then have "p \<noteq> []"
      using occurs_at_alt_def(9) by force
    with \<open>p \<in> positions (FAbs v' B)\<close> obtain p' where "p = \<guillemotleft> # p'" and "p' \<in> positions B"
      by (cases "FAbs v' B" rule: positions.cases) fastforce+
    from \<open>p = \<guillemotleft> # p'\<close> and \<open>is_bound_at v p (FAbs v' B)\<close> have "v = v' \<or> is_bound_at v p' B"
      using is_bound_at_from_abs by blast
    then consider (a\<^sub>1) "v = v'" | (a\<^sub>2) "is_bound_at v p' B"
      by blast
    then show ?thesis
    proof cases
      case a\<^sub>1
      then show ?thesis
        using surj_pair[of v'] by fastforce
    next
      case a\<^sub>2
      then have "v \<in> bound_vars B"
        using \<open>p' \<in> positions B\<close> and FAbs.IH by blast
      then show ?thesis
        using surj_pair[of v'] by fastforce
    qed
  next
    case b
    then have "p \<noteq> []"
      by force
    with FAbs.prems(1) obtain p' where "p = \<guillemotleft> # p'" and "p' \<in> positions B"
      by (cases "FAbs v' B" rule: positions.cases) fastforce+
    with b consider (b\<^sub>1) "v = v'" | (b\<^sub>2) "v \<in> binders_at B p'"
      by (cases "FAbs v' B" rule: positions.cases) fastforce+
    then show ?thesis
    proof cases
      case b\<^sub>1
      then show ?thesis
        using surj_pair[of v'] by fastforce
    next
      case b\<^sub>2
      then have "v \<in> bound_vars B"
        using \<open>p' \<in> positions B\<close> and FAbs.IH by blast
      then show ?thesis
        using surj_pair[of v'] by fastforce
    qed
  qed
qed fastforce+

lemma bound_vars_in_is_bound_at:
  assumes "v \<in> bound_vars A"
  obtains p where "p \<in> positions A" and "is_bound_at v p A \<or> v \<in> binders_at A p"
using assms proof (induction A arbitrary: thesis rule: bound_vars.induct)
  case (3 B C)
  from \<open>v \<in> bound_vars (B \<sqdot> C)\<close> consider (a) "v \<in> bound_vars B" | (b) "v \<in> bound_vars C"
    by fastforce
  then show ?case
  proof cases
    case a
    with "3.IH"(1) obtain p where "p \<in> positions B" and "is_bound_at v p B \<or> v \<in> binders_at B p"
      by blast
    from \<open>p \<in> positions B\<close> have "\<guillemotleft> # p \<in> positions (B \<sqdot> C)"
      by simp
    from \<open>is_bound_at v p B \<or> v \<in> binders_at B p\<close>
    consider (a\<^sub>1) "is_bound_at v p B" | (a\<^sub>2) "v \<in> binders_at B p"
      by blast
    then show ?thesis
    proof cases
      case a\<^sub>1
      then have "is_bound_at v (\<guillemotleft> # p) (B \<sqdot> C)"
        using is_bound_at_in_left_app by blast
      then show ?thesis
        using "3.prems"(1) and is_subform_implies_in_positions by blast
    next
      case a\<^sub>2
      then have "v \<in> binders_at (B \<sqdot> C) (\<guillemotleft> # p)"
        by simp
      then show ?thesis
        using "3.prems"(1) and \<open>\<guillemotleft> # p \<in> positions (B \<sqdot> C)\<close> by blast
    qed
  next
    case b
    with "3.IH"(2) obtain p where "p \<in> positions C" and "is_bound_at v p C \<or> v \<in> binders_at C p"
      by blast
    from \<open>p \<in> positions C\<close> have "\<guillemotright> # p \<in> positions (B \<sqdot> C)"
      by simp
    from \<open>is_bound_at v p C \<or> v \<in> binders_at C p\<close>
    consider (b\<^sub>1) "is_bound_at v p C" | (b\<^sub>2) "v \<in> binders_at C p"
      by blast
    then show ?thesis
    proof cases
      case b\<^sub>1
      then have "is_bound_at v (\<guillemotright> # p) (B \<sqdot> C)"
        using is_bound_at_in_right_app by blast
      then show ?thesis
        using "3.prems"(1) and is_subform_implies_in_positions by blast
    next
      case b\<^sub>2
      then have "v \<in> binders_at (B \<sqdot> C) (\<guillemotright> # p)"
        by simp
      then show ?thesis
        using "3.prems"(1) and \<open>\<guillemotright> # p \<in> positions (B \<sqdot> C)\<close> by blast
    qed
  qed
next
  case (4 x \<alpha> B)
  from \<open>v \<in> bound_vars (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)\<close> consider (a) "v = (x, \<alpha>)" | (b) "v \<in> bound_vars B"
    by force
  then show ?case
  proof cases
    case a
    then have "v \<in> binders_at (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) [\<guillemotleft>]"
      by simp
    then show ?thesis
      using "4.prems"(1) and is_subform_implies_in_positions by fastforce
  next
    case b
    with "4.IH"(1) obtain p where "p \<in> positions B" and "is_bound_at v p B \<or> v \<in> binders_at B p"
      by blast
    from \<open>p \<in> positions B\<close> have "\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
      by simp
    from \<open>is_bound_at v p B \<or> v \<in> binders_at B p\<close>
    consider (b\<^sub>1) "is_bound_at v p B" | (b\<^sub>2) "v \<in> binders_at B p"
      by blast
    then show ?thesis
    proof cases
      case b\<^sub>1
      then have "is_bound_at v (\<guillemotleft> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
        using is_bound_at_to_abs by blast
      then show ?thesis
        using "4.prems"(1) and \<open>\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)\<close> by blast
    next
      case b\<^sub>2
      then have "v \<in> binders_at (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) (\<guillemotleft> # p)"
        by simp
      then show ?thesis
        using "4.prems"(1) and \<open>\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)\<close> by blast
    qed
  qed
qed simp_all

lemma bound_vars_alt_def:
  shows "bound_vars A = {v | v p. p \<in> positions A \<and> (is_bound_at v p A \<or> v \<in> binders_at A p)}"
  using bound_vars_in_is_bound_at and is_bound_at_in_bound_vars
  by (intro subset_antisym subsetI CollectI, metis) blast

definition is_free_at :: "var \<Rightarrow> position \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_free_at v p B \<longleftrightarrow> occurs_at v p B \<and> \<not> in_scope_of_abs v p B"

lemma is_free_at_in_var:
  shows "is_free_at v [] (FVar v') \<longleftrightarrow> v = v'"
  by simp

lemma not_is_free_at_in_con:
  shows "\<not> is_free_at v [] (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>)"
  by simp

lemma is_free_at_in_left_app:
  shows "is_free_at v (\<guillemotleft> # p) (B \<sqdot> C) \<longleftrightarrow> is_free_at v p B"
  by auto

lemma is_free_at_in_right_app:
  shows "is_free_at v (\<guillemotright> # p) (B \<sqdot> C) \<longleftrightarrow> is_free_at v p C"
  by auto

lemma is_free_at_from_app:
  assumes "is_free_at v p (B \<sqdot> C)"
  obtains p' where "(p = \<guillemotleft> # p' \<and> is_free_at v p' B) \<or> (p = \<guillemotright> # p' \<and> is_free_at v p' C)"
proof -
  from assms obtain d and p' where "p = d # p'"
    using subforms_from_app by blast
  then show ?thesis
  proof (cases d)
    case Left
    with assms and that and \<open>p = d # p'\<close> show ?thesis
      using is_free_at_in_left_app by blast
  next
    case Right
    with assms and that and \<open>p = d # p'\<close> show ?thesis
      using is_free_at_in_right_app by blast
  qed
qed

lemma is_free_at_from_abs:
  assumes "is_free_at v (\<guillemotleft> # p) (FAbs v' B)"
  shows "is_free_at v p B"
  using assms by (fastforce elim: is_subform_at.elims)

lemma is_free_at_from_absE:
  assumes "is_free_at v p (FAbs v' B)"
  obtains p' where "p = \<guillemotleft> # p'" and "is_free_at v p' B"
proof -
  obtain x and \<alpha> where "v' = (x, \<alpha>)"
    by fastforce
  with assms obtain p' where "p = \<guillemotleft> # p'"
    using subforms_from_abs by blast
  with assms and that show ?thesis
    using is_free_at_from_abs by blast
qed

lemma is_free_at_to_abs:
  assumes "is_free_at v p B" and "v \<noteq> v'"
  shows "is_free_at v (\<guillemotleft> # p) (FAbs v' B)"
unfolding is_free_at_def proof
  from assms(1) show "occurs_at v (\<guillemotleft> # p) (FAbs v' B)"
    using surj_pair[of v'] by fastforce
  from assms show "\<not> in_scope_of_abs v (\<guillemotleft> # p) (FAbs v' B)"
    unfolding is_free_at_def using in_scope_of_abs_in_abs by presburger
qed

lemma is_free_at_in_free_vars:
  assumes "p \<in> positions A" and "is_free_at v p A"
  shows "v \<in> free_vars A"
using assms proof (induction A arbitrary: p)
  case (FApp B C)
  from \<open>is_free_at v p (B \<sqdot> C)\<close> have "p \<noteq> []"
    using occurs_at_alt_def(8) by blast
  then obtain d and p' where "p = d # p'"
    by (meson list.exhaust)
  with \<open>p \<in> positions (B \<sqdot> C)\<close>
  consider (a) "p = \<guillemotleft> # p'" and "p' \<in> positions B" | (b) "p = \<guillemotright> # p'" and "p' \<in> positions C"
    by force
  then show ?case
  proof cases
    case a
    from a(1) and \<open>is_free_at v p (B \<sqdot> C)\<close> have "is_free_at v p' B"
      using is_free_at_in_left_app by blast
    with a(2) have "v \<in> free_vars B"
      using FApp.IH(1) by blast
    then show ?thesis
      by simp
  next
    case b
    from b(1) and \<open>is_free_at v p (B \<sqdot> C)\<close> have "is_free_at v p' C"
      using is_free_at_in_right_app by blast
    with b(2) have "v \<in> free_vars C"
      using FApp.IH(2) by blast
    then show ?thesis
      by simp
  qed
next
  case (FAbs v' B)
  from \<open>is_free_at v p (FAbs v' B)\<close> have "p \<noteq> []"
    using occurs_at_alt_def(9) by force
  with \<open>p \<in> positions (FAbs v' B)\<close> obtain p' where "p = \<guillemotleft> # p'" and "p' \<in> positions B"
    by (cases "FAbs v' B" rule: positions.cases) fastforce+
  moreover from \<open>p = \<guillemotleft> # p'\<close> and \<open>is_free_at v p (FAbs v' B)\<close> have "is_free_at v p' B"
    using is_free_at_from_abs by blast
  ultimately have "v \<in> free_vars B"
    using FAbs.IH by simp
  moreover from \<open>p = \<guillemotleft> # p'\<close> and \<open>is_free_at v p (FAbs v' B)\<close> have "v \<noteq> v'"
    using in_scope_of_abs_in_abs by blast
  ultimately show ?case
    using surj_pair[of v'] by force
qed fastforce+

lemma free_vars_in_is_free_at:
  assumes "v \<in> free_vars A"
  obtains p where "p \<in> positions A" and "is_free_at v p A"
using assms proof (induction A arbitrary: thesis rule: free_vars_form.induct)
  case (3 A B)
  from \<open>v \<in> free_vars (A \<sqdot> B)\<close> consider (a) "v \<in> free_vars A" | (b) "v \<in> free_vars B"
    by fastforce
  then show ?case
  proof cases
    case a
    with "3.IH"(1) obtain p where "p \<in> positions A" and "is_free_at v p A"
      by blast
    from \<open>p \<in> positions A\<close> have "\<guillemotleft> # p \<in> positions (A \<sqdot> B)"
      by simp
    moreover from \<open>is_free_at v p A\<close> have "is_free_at v (\<guillemotleft> # p) (A \<sqdot> B)"
      using is_free_at_in_left_app by blast
    ultimately show ?thesis
      using "3.prems"(1) by presburger
  next
    case b
    with "3.IH"(2) obtain p where "p \<in> positions B" and "is_free_at v p B"
      by blast
    from \<open>p \<in> positions B\<close> have "\<guillemotright> # p \<in> positions (A \<sqdot> B)"
      by simp
    moreover from \<open>is_free_at v p B\<close> have "is_free_at v (\<guillemotright> # p) (A \<sqdot> B)"
      using is_free_at_in_right_app by blast
    ultimately show ?thesis
      using "3.prems"(1) by presburger
  qed
next
  case (4 x \<alpha> A)
  from \<open>v \<in> free_vars (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)\<close> have "v \<in> free_vars A - {(x, \<alpha>)}" and "v \<noteq> (x, \<alpha>)"
    by simp_all
  then have "v \<in> free_vars A"
    by blast
  with "4.IH" obtain p where "p \<in> positions A" and "is_free_at v p A"
    by blast
  from \<open>p \<in> positions A\<close> have "\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
    by simp
  moreover from \<open>is_free_at v p A\<close> and \<open>v \<noteq> (x, \<alpha>)\<close> have "is_free_at v (\<guillemotleft> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
    using is_free_at_to_abs by blast
  ultimately show ?case
    using "4.prems"(1) by presburger
qed simp_all

lemma free_vars_alt_def:
  shows "free_vars A = {v | v p. p \<in> positions A \<and> is_free_at v p A}"
  using free_vars_in_is_free_at and is_free_at_in_free_vars
  by (intro subset_antisym subsetI CollectI, metis) blast

text \<open>
  In the following definition, note that the variable immeditately preceded by \<open>\<lambda>\<close> counts as a bound
  variable:
\<close>

definition is_bound :: "var \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_bound v B \<longleftrightarrow> (\<exists>p \<in> positions B. is_bound_at v p B \<or> v \<in> binders_at B p)"

lemma is_bound_in_app_homomorphism:
  shows "is_bound v (A \<sqdot> B) \<longleftrightarrow> is_bound v A \<or> is_bound v B"
proof
  assume "is_bound v (A \<sqdot> B)"
  then obtain p where "p \<in> positions (A \<sqdot> B)" and "is_bound_at v p (A \<sqdot> B) \<or> v \<in> binders_at (A \<sqdot> B) p"
    by auto
  then have "p \<noteq> []"
    by fastforce
  with \<open>p \<in> positions (A \<sqdot> B)\<close> obtain p' and d where "p = d # p'"
    by auto
  from \<open>is_bound_at v p (A \<sqdot> B) \<or> v \<in> binders_at (A \<sqdot> B) p\<close>
  consider (a) "is_bound_at v p (A \<sqdot> B)" | (b) "v \<in> binders_at (A \<sqdot> B) p"
    by blast
  then show "is_bound v A \<or> is_bound v B"
  proof cases
    case a
    then show ?thesis
    proof (cases d)
      case Left
      then have "p' \<in> positions A"
        using \<open>p = d # p'\<close> and \<open>p \<in> positions (A \<sqdot> B)\<close> by fastforce
      moreover from \<open>is_bound_at v p (A \<sqdot> B)\<close> have "occurs_at v p' A"
        using Left and \<open>p = d # p'\<close> and is_subform_at.simps(2) by force
      moreover from \<open>is_bound_at v p (A \<sqdot> B)\<close> have "in_scope_of_abs v p' A"
        using Left and \<open>p = d # p'\<close> by fastforce
      ultimately show ?thesis
        by auto
    next
      case Right
      then have "p' \<in> positions B"
        using \<open>p = d # p'\<close> and \<open>p \<in> positions (A \<sqdot> B)\<close> by fastforce
      moreover from \<open>is_bound_at v p (A \<sqdot> B)\<close> have "occurs_at v p' B"
        using Right and \<open>p = d # p'\<close> and is_subform_at.simps(3) by force
      moreover from \<open>is_bound_at v p (A \<sqdot> B)\<close> have "in_scope_of_abs v p' B"
        using Right and \<open>p = d # p'\<close> by fastforce
      ultimately show ?thesis
        by auto
    qed
  next
    case b
    then show ?thesis
    proof (cases d)
      case Left
      then have "p' \<in> positions A"
        using \<open>p = d # p'\<close> and \<open>p \<in> positions (A \<sqdot> B)\<close> by fastforce
      moreover from \<open>v \<in> binders_at (A \<sqdot> B) p\<close> have "v \<in> binders_at A p'"
        using Left and \<open>p = d # p'\<close> by force
      ultimately show ?thesis
        by auto
    next
      case Right
      then have "p' \<in> positions B"
        using \<open>p = d # p'\<close> and \<open>p \<in> positions (A \<sqdot> B)\<close> by fastforce
      moreover from \<open>v \<in> binders_at (A \<sqdot> B) p\<close> have "v \<in> binders_at B p'"
        using Right and \<open>p = d # p'\<close> by force
      ultimately show ?thesis
        by auto
    qed
  qed
next
  assume "is_bound v A \<or> is_bound v B"
  then show "is_bound v (A \<sqdot> B)"
  proof (rule disjE)
    assume "is_bound v A"
    then obtain p where "p \<in> positions A" and "is_bound_at v p A \<or> v \<in> binders_at A p"
      by auto
    from \<open>p \<in> positions A\<close> have "\<guillemotleft> # p \<in> positions (A \<sqdot> B)"
      by auto
    from \<open>is_bound_at v p A \<or> v \<in> binders_at A p\<close>
    consider (a) "is_bound_at v p A" | (b) "v \<in> binders_at A p"
      by blast
    then show "is_bound v (A \<sqdot> B)"
    proof cases
      case a
      then have "occurs_at v (\<guillemotleft> # p) (A \<sqdot> B)"
        by auto
      moreover from a have "is_bound_at v (\<guillemotleft> # p) (A \<sqdot> B)"
        by force
      ultimately show "is_bound v (A \<sqdot> B)"
        using \<open>\<guillemotleft> # p \<in> positions (A \<sqdot> B)\<close> by blast
    next
      case b
      then have "v \<in> binders_at (A \<sqdot> B) (\<guillemotleft> # p)"
        by auto
      then show "is_bound v (A \<sqdot> B)"
        using \<open>\<guillemotleft> # p \<in> positions (A \<sqdot> B)\<close> by blast
    qed
  next
    assume "is_bound v B"
    then obtain p where "p \<in> positions B" and "is_bound_at v p B \<or> v \<in> binders_at B p"
      by auto
    from \<open>p \<in> positions B\<close> have "\<guillemotright> # p \<in> positions (A \<sqdot> B)"
      by auto
    from \<open>is_bound_at v p B \<or> v \<in> binders_at B p\<close>
    consider (a) "is_bound_at v p B" | (b) "v \<in> binders_at B p"
      by blast
    then show "is_bound v (A \<sqdot> B)"
    proof cases
      case a
      then have "occurs_at v (\<guillemotright> # p) (A \<sqdot> B)"
        by auto
      moreover from a have "is_bound_at v (\<guillemotright> # p) (A \<sqdot> B)"
        by force
      ultimately show "is_bound v (A \<sqdot> B)"
        using \<open>\<guillemotright> # p \<in> positions (A \<sqdot> B)\<close> by blast
    next
      case b
      then have "v \<in> binders_at (A \<sqdot> B) (\<guillemotright> # p)"
        by auto
      then show "is_bound v (A \<sqdot> B)"
        using \<open>\<guillemotright> # p \<in> positions (A \<sqdot> B)\<close> by blast
    qed
  qed
qed

lemma is_bound_in_abs_body:
  assumes "is_bound v A"
  shows "is_bound v (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
using assms unfolding is_bound_def proof
  fix p
  assume "p \<in> positions A" and "is_bound_at v p A \<or> v \<in> binders_at A p"
  moreover from \<open>p \<in> positions A\<close> have "\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
    by simp
  ultimately consider (a) "is_bound_at v p A" | (b) "v \<in> binders_at A p"
    by blast
  then show "\<exists>p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. A). is_bound_at v p (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) \<or> v \<in> binders_at (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) p"
  proof cases
    case a
    then have "is_bound_at v (\<guillemotleft> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
      by force
    with \<open>\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)\<close> show ?thesis
      by blast
  next
    case b
    then have "v \<in> binders_at (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) (\<guillemotleft> # p)"
      by simp
    with \<open>\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)\<close> show ?thesis
      by blast
  qed
qed

lemma absent_var_is_not_bound:
  assumes "v \<notin> vars A"
  shows "\<not> is_bound v A"
  using assms and binders_at_alt_def and in_scope_of_abs_in_vars by blast

lemma bound_vars_alt_def2:
  shows "bound_vars A = {v \<in> vars A. is_bound v A}"
  unfolding bound_vars_alt_def using absent_var_is_not_bound by fastforce

definition is_free :: "var \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_free v B \<longleftrightarrow> (\<exists>p \<in> positions B. is_free_at v p B)"

subsection \<open>Free variables for a formula in another formula\<close>

definition is_free_for :: "form \<Rightarrow> var \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_free_for A v B \<longleftrightarrow>
    (
      \<forall>v' \<in> free_vars A.
        \<forall>p \<in> positions B.
          is_free_at v p B \<longrightarrow> \<not> in_scope_of_abs v' p B
    )"

lemma is_free_for_absent_var [intro]:
  assumes "v \<notin> vars B"
  shows "is_free_for A v B"
  using assms and occurs_def and is_free_at_def and occurs_in_vars by blast

lemma is_free_for_in_var [intro]:
  shows "is_free_for A v (x\<^bsub>\<alpha>\<^esub>)"
  using subforms_from_var(2) by force

lemma is_free_for_in_con [intro]:
  shows "is_free_for A v (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>)"
  using subforms_from_con(2) by force

lemma is_free_for_from_app:
  assumes "is_free_for A v (B \<sqdot> C)"
  shows "is_free_for A v B" and "is_free_for A v C"
proof -
  {
    fix v'
    assume "v' \<in> free_vars A"
    then have "\<forall>p \<in> positions B. is_free_at v p B \<longrightarrow> \<not> in_scope_of_abs v' p B"
    proof (intro ballI impI)
      fix p
      assume "v' \<in> free_vars A" and "p \<in> positions B" and "is_free_at v p B"
      from \<open>p \<in> positions B\<close> have "\<guillemotleft> # p \<in> positions (B \<sqdot> C)"
        by simp
      moreover from \<open>is_free_at v p B\<close> have "is_free_at v (\<guillemotleft> # p) (B \<sqdot> C)"
        using is_free_at_in_left_app by blast
      ultimately have "\<not> in_scope_of_abs v' (\<guillemotleft> # p) (B \<sqdot> C)"
        using assms and \<open>v' \<in> free_vars A\<close> by blast
      then show "\<not> in_scope_of_abs v' p B"
        by simp
    qed
  }
  then show "is_free_for A v B"
    by force
next
  {
    fix v'
    assume "v' \<in> free_vars A"
    then have "\<forall>p \<in> positions C. is_free_at v p C \<longrightarrow> \<not> in_scope_of_abs v' p C"
    proof (intro ballI impI)
      fix p
      assume "v' \<in> free_vars A" and "p \<in> positions C" and "is_free_at v p C"
      from \<open>p \<in> positions C\<close> have "\<guillemotright> # p \<in> positions (B \<sqdot> C)"
        by simp
      moreover from \<open>is_free_at v p C\<close> have "is_free_at v (\<guillemotright> # p) (B \<sqdot> C)"
        using is_free_at_in_right_app by blast
      ultimately have "\<not> in_scope_of_abs v' (\<guillemotright> # p) (B \<sqdot> C)"
        using assms and \<open>v' \<in> free_vars A\<close> by blast
      then show "\<not> in_scope_of_abs v' p C"
        by simp
    qed
  }
  then show "is_free_for A v C"
    by force
qed

lemma is_free_for_to_app [intro]:
  assumes "is_free_for A v B" and "is_free_for A v C"
  shows "is_free_for A v (B \<sqdot> C)"
unfolding is_free_for_def proof (intro ballI impI)
  fix v' and p
  assume "v' \<in> free_vars A" and "p \<in> positions (B \<sqdot> C)" and "is_free_at v p (B \<sqdot> C)"
  from \<open>is_free_at v p (B \<sqdot> C)\<close> have "p \<noteq> []"
    using occurs_at_alt_def(8) by force
  then obtain d and p' where "p = d # p'"
    by (meson list.exhaust)
  with \<open>p \<in> positions (B \<sqdot> C)\<close>
  consider (b) "p = \<guillemotleft> # p'" and "p' \<in> positions B" | (c) "p = \<guillemotright> # p'" and "p' \<in> positions C"
    by force
  then show "\<not> in_scope_of_abs v' p (B \<sqdot> C)"
  proof cases
    case b
    from b(1) and \<open>is_free_at v p (B \<sqdot> C)\<close> have "is_free_at v p' B"
      using is_free_at_in_left_app by blast
    with assms(1) and \<open>v' \<in> free_vars A\<close> and \<open>p' \<in> positions B\<close> have "\<not> in_scope_of_abs v' p' B"
      by simp
    with b(1) show ?thesis
      using in_scope_of_abs_in_left_app by simp
  next
    case c
    from c(1) and \<open>is_free_at v p (B \<sqdot> C)\<close> have "is_free_at v p' C"
      using is_free_at_in_right_app by blast
    with assms(2) and \<open>v' \<in> free_vars A\<close> and \<open>p' \<in> positions C\<close> have "\<not> in_scope_of_abs v' p' C"
      by simp
    with c(1) show ?thesis
      using in_scope_of_abs_in_right_app by simp
  qed
qed

lemma is_free_for_in_app:
  shows "is_free_for A v (B \<sqdot> C) \<longleftrightarrow> is_free_for A v B \<and> is_free_for A v C"
  using is_free_for_from_app and is_free_for_to_app by iprover

lemma is_free_for_to_abs [intro]:
  assumes "is_free_for A v B" and "(x, \<alpha>) \<notin> free_vars A"
  shows "is_free_for A v (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
unfolding is_free_for_def proof (intro ballI impI)
  fix v' and p
  assume "v' \<in> free_vars A" and "p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)" and "is_free_at v p (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
  from \<open>is_free_at v p (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)\<close> have "p \<noteq> []"
    using occurs_at_alt_def(9) by force
  with \<open>p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)\<close> obtain p' where "p = \<guillemotleft> # p'" and "p' \<in> positions B"
    by force
  then show "\<not> in_scope_of_abs v' p (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
  proof -
    from \<open>p = \<guillemotleft> # p'\<close> and \<open>is_free_at v p (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)\<close> have "is_free_at v p' B"
      using is_free_at_from_abs by blast
    with assms(1) and \<open>v' \<in> free_vars A\<close> and \<open>p' \<in> positions B\<close> have "\<not> in_scope_of_abs v' p' B"
      by force
    moreover from \<open>v' \<in> free_vars A\<close> and assms(2) have "v' \<noteq> (x, \<alpha>)"
      by blast
    ultimately show ?thesis
      using \<open>p = \<guillemotleft> # p'\<close> and in_scope_of_abs_in_abs by auto
  qed
qed

lemma is_free_for_from_abs:
  assumes "is_free_for A v (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)" and "v \<noteq> (x, \<alpha>)"
  shows "is_free_for A v B"
unfolding is_free_for_def proof (intro ballI impI)
  fix v' and p
  assume "v' \<in> free_vars A" and "p \<in> positions B" and "is_free_at v p B"
  then show "\<not> in_scope_of_abs v' p B"
  proof -
    from \<open>is_free_at v p B\<close> and assms(2) have "is_free_at v (\<guillemotleft> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
      by (rule is_free_at_to_abs)
    moreover from \<open>p \<in> positions B\<close> have "\<guillemotleft> # p \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
      by simp
    ultimately have "\<not> in_scope_of_abs v' (\<guillemotleft> # p) (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
      using assms and \<open>v' \<in> free_vars A\<close> by blast
    then show ?thesis
      using in_scope_of_abs_in_abs by blast
  qed
qed

lemma closed_is_free_for [intro]:
  assumes "free_vars A = {}"
  shows "is_free_for A v B"
  using assms by force

lemma is_free_for_closed_form [intro]:
  assumes "free_vars B = {}"
  shows "is_free_for A v B"
  using assms and is_free_at_in_free_vars by blast

lemma is_free_for_alt_def:
  shows "
    is_free_for A v B
    \<longleftrightarrow>
    (
      \<nexists>p.
      (
        p \<in> positions B \<and> is_free_at v p B \<and> p \<noteq> [] \<and>
        (\<exists>v' \<in> free_vars A. \<exists>p' C. strict_prefix p' p \<and> FAbs v' C \<preceq>\<^bsub>p'\<^esub> B)
      )
    )"
  unfolding is_free_for_def
  using in_scope_of_abs_alt_def and is_subform_implies_in_positions
  by meson

lemma binding_var_not_free_for_in_abs:
  assumes "is_free x B" and "x \<noteq> w"
  shows "\<not> is_free_for (FVar w) x (FAbs w B)"
proof (rule ccontr)
  assume "\<not> \<not> is_free_for (FVar w) x (FAbs w B)"
  then have "
    \<forall>v' \<in> free_vars (FVar w). \<forall>p \<in> positions (FAbs w B). is_free_at x p (FAbs w B)
      \<longrightarrow> \<not> in_scope_of_abs v' p (FAbs w B)"
    by force
  moreover have "free_vars (FVar w) = {w}"
    using surj_pair[of w] by force
  ultimately have "
    \<forall>p \<in> positions (FAbs w B). is_free_at x p (FAbs w B) \<longrightarrow> \<not> in_scope_of_abs w p (FAbs w B)"
    by blast
  moreover from assms(1) obtain p where "is_free_at x p B"
    by fastforce
  from this and assms(2) have "is_free_at x (\<guillemotleft> # p) (FAbs w B)"
    by (rule is_free_at_to_abs)
  moreover from this have "\<guillemotleft> # p \<in> positions (FAbs w B)"
    using is_subform_implies_in_positions by force
  ultimately have "\<not> in_scope_of_abs w (\<guillemotleft> # p) (FAbs w B)"
    by blast
  moreover have "in_scope_of_abs w (\<guillemotleft> # p) (FAbs w B)"
    using in_scope_of_abs_in_abs by blast
  ultimately show False
    by contradiction
qed

lemma absent_var_is_free_for [intro]:
  assumes "x \<notin> vars A"
  shows "is_free_for (FVar x) y A"
  using in_scope_of_abs_in_vars and assms and surj_pair[of x] by fastforce

lemma form_is_free_for_absent_var [intro]:
  assumes "x \<notin> vars A"
  shows "is_free_for B x A"
  using assms and occurs_in_vars by fastforce

lemma form_with_free_binder_not_free_for:
  assumes "v \<noteq> v'" and "v' \<in> free_vars A" and "v \<in> free_vars B"
  shows "\<not> is_free_for A v (FAbs v' B)"
proof -
  from assms(3) obtain p where "p \<in> positions B" and "is_free_at v p B"
    using free_vars_in_is_free_at by blast
  then have "\<guillemotleft> # p \<in> positions (FAbs v' B)" and "is_free_at v (\<guillemotleft> # p) (FAbs v' B)"
    using surj_pair[of v'] and is_free_at_to_abs[OF \<open>is_free_at v p B\<close> assms(1)] by force+
  moreover have "in_scope_of_abs v' (\<guillemotleft> # p) (FAbs v' B)"
    using in_scope_of_abs_in_abs by blast
  ultimately show ?thesis
    using assms(2) by blast
qed

subsection \<open>Replacement of subformulas\<close>

inductive
  is_replacement_at :: "form \<Rightarrow> position \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool"
  ("(4_\<lblot>_ \<leftarrow> _\<rblot> \<rhd> _)" [1000, 0, 0, 0] 900)
where
  pos_found: "A\<lblot>p \<leftarrow> C\<rblot> \<rhd> C'" if "p = []" and "C = C'"
| replace_left_app: "(G \<sqdot> H)\<lblot>\<guillemotleft> # p \<leftarrow> C\<rblot> \<rhd> (G' \<sqdot> H)" if "p \<in> positions G" and "G\<lblot>p \<leftarrow> C\<rblot> \<rhd> G'"
| replace_right_app: "(G \<sqdot> H)\<lblot>\<guillemotright> # p \<leftarrow> C\<rblot> \<rhd> (G \<sqdot> H')" if "p \<in> positions H" and "H\<lblot>p \<leftarrow> C\<rblot> \<rhd> H'"
| replace_abs: "(\<lambda>x\<^bsub>\<gamma>\<^esub>. E)\<lblot>\<guillemotleft> # p \<leftarrow> C\<rblot> \<rhd> (\<lambda>x\<^bsub>\<gamma>\<^esub>. E')" if "p \<in> positions E" and "E\<lblot>p \<leftarrow> C\<rblot> \<rhd> E'"

lemma is_replacement_at_implies_in_positions:
  assumes "C\<lblot>p \<leftarrow> A\<rblot> \<rhd> D"
  shows "p \<in> positions C"
  using assms by (induction rule: is_replacement_at.induct) auto

declare is_replacement_at.intros [intro!]

lemma is_replacement_at_existence:
  assumes "p \<in> positions C"
  obtains D where "C\<lblot>p \<leftarrow> A\<rblot> \<rhd> D"
using assms proof (induction C arbitrary: p thesis)
  case (FApp C\<^sub>1 C\<^sub>2)
  from FApp.prems(2) consider
    (a) "p = []"
  | (b) "\<exists>p'. p = \<guillemotleft> # p' \<and> p' \<in> positions C\<^sub>1"
  | (c) "\<exists>p'. p = \<guillemotright> # p' \<and> p' \<in> positions C\<^sub>2"
    by fastforce
  then show ?case
  proof cases
    case a
    with FApp.prems(1) show ?thesis
      by blast
  next
    case b
    with FApp.prems(1) show ?thesis
      using FApp.IH(1) and replace_left_app by meson
  next
    case c
    with FApp.prems(1) show ?thesis
      using FApp.IH(2) and replace_right_app by meson
  qed
next
  case (FAbs v C')
  from FAbs.prems(2) consider (a) "p = []" | (b) "\<exists>p'. p = \<guillemotleft> # p' \<and> p' \<in> positions C'"
    using surj_pair[of v] by fastforce
  then show ?case
  proof cases
    case a
    with FAbs.prems(1) show ?thesis
      by blast
  next
    case b
    with FAbs.prems(1,2) show ?thesis
      using FAbs.IH and surj_pair[of v] by blast
  qed
qed force+

lemma is_replacement_at_minimal_change:
  assumes "C\<lblot>p \<leftarrow> A\<rblot> \<rhd> D"
  shows "A \<preceq>\<^bsub>p\<^esub> D"
  and "\<forall>p' \<in> positions D. \<not> prefix p' p \<and> \<not> prefix p p' \<longrightarrow> subform_at D p' = subform_at C p'"
  using assms by (induction rule: is_replacement_at.induct) auto

lemma is_replacement_at_binders:
  assumes "C\<lblot>p \<leftarrow> A\<rblot> \<rhd> D"
  shows "binders_at D p = binders_at C p"
  using assms by (induction rule: is_replacement_at.induct) simp_all

lemma is_replacement_at_occurs:
  assumes "C\<lblot>p \<leftarrow> A\<rblot> \<rhd> D"
  and "\<not> prefix p' p" and "\<not> prefix p p'"
  shows "occurs_at v p' C \<longleftrightarrow> occurs_at v p' D"
using assms proof (induction arbitrary: p' rule: is_replacement_at.induct)
  case pos_found
  then show ?case
    by simp
next
  case replace_left_app
  then show ?case
  proof (cases p')
    case (Cons d p'')
    with replace_left_app.prems(1,2) show ?thesis
      by (cases d) (use replace_left_app.IH in force)+
  qed force
next
  case replace_right_app
  then show ?case
  proof (cases p')
    case (Cons d p'')
    with replace_right_app.prems(1,2) show ?thesis
      by (cases d) (use replace_right_app.IH in force)+
  qed force
next
  case replace_abs
  then show ?case
  proof (cases p')
    case (Cons d p'')
    with replace_abs.prems(1,2) show ?thesis
      by (cases d) (use replace_abs.IH in force)+
  qed force
qed

lemma fresh_var_replacement_position_uniqueness:
  assumes "v \<notin> vars C"
  and "C\<lblot>p \<leftarrow> FVar v\<rblot> \<rhd> G"
  and "occurs_at v p' G"
  shows "p' = p"
proof (rule ccontr)
  assume "p' \<noteq> p"
  from assms(2) have "occurs_at v p G"
    by (simp add: is_replacement_at_minimal_change(1))
  moreover have *: "occurs_at v p' C \<longleftrightarrow> occurs_at v p' G" if "\<not> prefix p' p" and "\<not> prefix p p'"
    using assms(2) and that and is_replacement_at_occurs by blast
  ultimately show False
  proof (cases "\<not> prefix p' p \<and> \<not> prefix p p'")
    case True
    with assms(3) and * have "occurs_at v p' C"
      by simp
    then have "v \<in> vars C"
      using is_subform_implies_in_positions and occurs_in_vars by fastforce
    with assms(1) show ?thesis
      by contradiction
  next
    case False
    have "FVar v \<preceq>\<^bsub>p\<^esub> G"
      by (fact is_replacement_at_minimal_change(1)[OF assms(2)])
    moreover from assms(3) have "FVar v \<preceq>\<^bsub>p'\<^esub> G"
      by simp
    ultimately show ?thesis
      using \<open>p' \<noteq> p\<close> and False and loop_subform_impossibility
      by (blast dest: prefix_order.antisym_conv2)
  qed
qed

lemma is_replacement_at_new_positions:
  assumes "C\<lblot>p \<leftarrow> A\<rblot> \<rhd> D" and "prefix p p'" and "p' \<in> positions D"
  obtains p'' where "p' = p @ p''" and "p'' \<in> positions A"
  using assms by (induction arbitrary: thesis p' rule: is_replacement_at.induct, auto) blast+

lemma replacement_override:
  assumes "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D" and "C\<lblot>p \<leftarrow> A\<rblot> \<rhd> F"
  shows "D\<lblot>p \<leftarrow> A\<rblot> \<rhd> F"
using assms proof (induction arbitrary: F rule: is_replacement_at.induct)
  case pos_found
  from pos_found.hyps(1) and pos_found.prems have "A = F"
    using is_replacement_at.simps by blast
  with pos_found.hyps(1) show ?case
    by blast
next
  case (replace_left_app p G C G' H)
  have "p \<in> positions G'"
    by (
        fact is_subform_implies_in_positions
          [OF is_replacement_at_minimal_change(1)[OF replace_left_app.hyps(2)]]
       )
  from replace_left_app.prems obtain F' where "F = F' \<sqdot> H" and "G\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'"
    by (fastforce elim: is_replacement_at.cases)
  from \<open>G\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'\<close> have "G'\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'"
    by (fact replace_left_app.IH)
  with \<open>p \<in> positions G'\<close> show ?case
    unfolding \<open>F = F' \<sqdot> H\<close> by blast
next
  case (replace_right_app p H C H' G)
  have "p \<in> positions H'"
    by
      (
        fact is_subform_implies_in_positions
          [OF is_replacement_at_minimal_change(1)[OF replace_right_app.hyps(2)]]
      )
  from replace_right_app.prems obtain F' where "F = G \<sqdot> F'" and "H\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'"
    by (fastforce elim: is_replacement_at.cases)
  from \<open>H\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'\<close> have "H'\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'"
    by (fact replace_right_app.IH)
  with \<open>p \<in> positions H'\<close> show ?case
    unfolding \<open>F = G \<sqdot> F'\<close> by blast
next
  case (replace_abs p E C E' x \<gamma>)
  have "p \<in> positions E'"
    by
      (
        fact is_subform_implies_in_positions
          [OF is_replacement_at_minimal_change(1)[OF replace_abs.hyps(2)]]
      )
  from replace_abs.prems obtain F' where "F = \<lambda>x\<^bsub>\<gamma>\<^esub>. F'" and "E\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'"
    by (fastforce elim: is_replacement_at.cases)
  from \<open>E\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'\<close> have "E'\<lblot>p \<leftarrow> A\<rblot> \<rhd> F'"
    by (fact replace_abs.IH)
  with \<open>p \<in> positions E'\<close> show ?case
    unfolding \<open>F = \<lambda>x\<^bsub>\<gamma>\<^esub>. F'\<close> by blast
qed

lemma leftmost_subform_in_generalized_app_replacement:
  shows "(\<sqdot>\<^sup>\<Q>\<^sub>\<star> C As)\<lblot>replicate (length As) \<guillemotleft> \<leftarrow> D\<rblot> \<rhd> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> D As)"
  using is_replacement_at_implies_in_positions and replace_left_app
  by (induction As arbitrary: D rule: rev_induct) auto

subsection \<open>Logical constants\<close>

abbreviation (input) \<xx> where "\<xx> \<equiv> 0"
abbreviation (input) \<yy> where "\<yy> \<equiv> Suc \<xx>"
abbreviation (input) \<zz> where "\<zz> \<equiv> Suc \<yy>"
abbreviation (input) \<ff> where "\<ff> \<equiv> Suc \<zz>"
abbreviation (input) \<gg> where "\<gg> \<equiv> Suc \<ff>"
abbreviation (input) \<hh> where "\<hh> \<equiv> Suc \<gg>"
abbreviation (input) \<cc> where "\<cc> \<equiv> Suc \<hh>"
abbreviation (input) \<cc>\<^sub>Q where "\<cc>\<^sub>Q \<equiv> Suc \<cc>"
abbreviation (input) \<cc>\<^sub>\<iota> where "\<cc>\<^sub>\<iota> \<equiv> Suc \<cc>\<^sub>Q"

definition Q_constant_of_type :: "type \<Rightarrow> con" where
  [simp]: "Q_constant_of_type \<alpha> = (\<cc>\<^sub>Q, \<alpha>\<rightarrow>\<alpha>\<rightarrow>o)"

definition iota_constant :: con where
  [simp]: "iota_constant \<equiv> (\<cc>\<^sub>\<iota>, (i\<rightarrow>o)\<rightarrow>i)"

definition Q :: "type \<Rightarrow> form" ("Q\<^bsub>_\<^esub>") where
  [simp]: "Q\<^bsub>\<alpha>\<^esub> = FCon (Q_constant_of_type \<alpha>)"

definition iota :: form ("\<iota>") where
  [simp]: "\<iota> = FCon iota_constant"

definition is_Q_constant_of_type :: "con \<Rightarrow> type \<Rightarrow> bool" where
  [iff]: "is_Q_constant_of_type p \<alpha> \<longleftrightarrow> p = Q_constant_of_type \<alpha>"

definition is_iota_constant :: "con \<Rightarrow> bool" where
  [iff]: "is_iota_constant p \<longleftrightarrow> p = iota_constant"

definition is_logical_constant :: "con \<Rightarrow> bool" where
  [iff]: "is_logical_constant p \<longleftrightarrow> (\<exists>\<beta>. is_Q_constant_of_type p \<beta>) \<or> is_iota_constant p"

definition type_of_Q_constant :: "con \<Rightarrow> type" where
  [simp]: "type_of_Q_constant p = (THE \<alpha>. is_Q_constant_of_type p \<alpha>)"

lemma constant_cases[case_names non_logical Q_constant \<iota>_constant, cases type: con]:
  assumes "\<not> is_logical_constant p \<Longrightarrow> P"
  and "\<And>\<beta>. is_Q_constant_of_type p \<beta> \<Longrightarrow> P"
  and "is_iota_constant p \<Longrightarrow> P"
  shows "P"
  using assms by blast

subsection \<open>Definitions and abbreviations\<close>

definition equality_of_type :: "form \<Rightarrow> type \<Rightarrow> form \<Rightarrow> form" ("(_ =\<^bsub>_\<^esub>/ _)" [103, 0, 103] 102) where
  [simp]: "A =\<^bsub>\<alpha>\<^esub> B = Q\<^bsub>\<alpha>\<^esub> \<sqdot> A \<sqdot> B"

definition equivalence :: "form \<Rightarrow> form \<Rightarrow> form" (infixl "\<equiv>\<^sup>\<Q>" 102) where
  [simp]: "A \<equiv>\<^sup>\<Q> B = A =\<^bsub>o\<^esub> B" \<comment> \<open>more modular than the definition in @{cite "andrews:2002"}\<close>

definition true :: form ("T\<^bsub>o\<^esub>") where
  [simp]: "T\<^bsub>o\<^esub> = Q\<^bsub>o\<^esub> =\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> Q\<^bsub>o\<^esub>"

definition false :: form ("F\<^bsub>o\<^esub>") where
  [simp]: "F\<^bsub>o\<^esub> = \<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub> =\<^bsub>o\<rightarrow>o\<^esub> \<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>"

definition PI :: "type \<Rightarrow> form" ("\<Prod>\<^bsub>_\<^esub>") where
  [simp]: "\<Prod>\<^bsub>\<alpha>\<^esub> = Q\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>)"

definition forall :: "nat \<Rightarrow> type \<Rightarrow> form \<Rightarrow> form" ("(4\<forall>_\<^bsub>_\<^esub>./ _)" [0, 0, 141] 141) where
  [simp]: "\<forall>x\<^bsub>\<alpha>\<^esub>. A = \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"

text \<open>Generalized universal quantification. We define \<open>\<forall>\<^sup>\<Q>\<^sub>\<star> [x\<^sub>1, \<dots>, x\<^sub>n] A\<close> as \<open>\<forall>x\<^sub>1. \<cdots> \<forall>x\<^sub>n. A\<close>:\<close>

definition generalized_forall :: "var list \<Rightarrow> form \<Rightarrow> form" ("\<forall>\<^sup>\<Q>\<^sub>\<star> _ _" [141, 141] 141) where
  [simp]: "\<forall>\<^sup>\<Q>\<^sub>\<star> vs A = foldr (\<lambda>(x, \<alpha>) B. \<forall>x\<^bsub>\<alpha>\<^esub>. B) vs A"

lemma innermost_subform_in_generalized_forall:
  assumes "vs \<noteq> []"
  shows "A \<preceq>\<^bsub>foldr (\<lambda>_ p. [\<guillemotright>,\<guillemotleft>] @ p) vs []\<^esub> \<forall>\<^sup>\<Q>\<^sub>\<star> vs A"
  using assms by (induction vs) fastforce+

lemma innermost_replacement_in_generalized_forall:
  assumes "vs \<noteq> []"
  shows "(\<forall>\<^sup>\<Q>\<^sub>\<star> vs C)\<lblot>foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<leftarrow> B\<rblot> \<rhd> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
using assms proof (induction vs)
  case Nil
  then show ?case
    by blast
next
  case (Cons v vs)
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  then show ?case
  proof (cases "vs = []")
    case True
    with \<open>v = (x, \<alpha>)\<close> show ?thesis
      unfolding True by force
  next
    case False
    then have "foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<in> positions (\<forall>\<^sup>\<Q>\<^sub>\<star> vs C)"
      using innermost_subform_in_generalized_forall and is_subform_implies_in_positions by blast
    moreover from False have "(\<forall>\<^sup>\<Q>\<^sub>\<star> vs C)\<lblot>foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<leftarrow> B\<rblot> \<rhd> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
      by (fact Cons.IH)
    ultimately have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs C)\<lblot>\<guillemotleft> # foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<leftarrow> B\<rblot> \<rhd> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
      by (rule replace_abs)
    moreover have "\<guillemotleft> # foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<in> positions (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs C)"
      using \<open>foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<in> positions (\<forall>\<^sup>\<Q>\<^sub>\<star> vs C)\<close> by simp
    ultimately have "
      (\<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs C))\<lblot>\<guillemotright> # \<guillemotleft> # foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<leftarrow> B\<rblot> \<rhd> (\<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs B))"
      by blast
    then have "(\<forall>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs C)\<lblot>[\<guillemotright>,\<guillemotleft>] @ foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs [] \<leftarrow> B\<rblot> \<rhd> (\<forall>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
      by simp
    then show ?thesis
      unfolding \<open>v = (x, \<alpha>)\<close> and generalized_forall_def and foldr.simps(2) and o_apply
      and case_prod_conv .
  qed
qed

lemma false_is_forall:
  shows "F\<^bsub>o\<^esub> = \<forall>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>"
  unfolding false_def and forall_def and PI_def and equality_of_type_def ..

definition conj_fun :: form ("\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>") where
  [simp]: "\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> =
    \<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>.
    (
      (\<lambda>\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<sqdot> T\<^bsub>o\<^esub>) =\<^bsub>(o\<rightarrow>o\<rightarrow>o)\<rightarrow>o\<^esub> (\<lambda>\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<sqdot> \<yy>\<^bsub>o\<^esub>)
    )"

definition conj_op :: "form \<Rightarrow> form \<Rightarrow> form" (infixl "\<and>\<^sup>\<Q>" 131) where
  [simp]: "A \<and>\<^sup>\<Q> B = \<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B"

text \<open>Generalized conjunction. We define \<open>\<and>\<^sup>\<Q>\<^sub>\<star> [A\<^sub>1, \<dots>, A\<^sub>n]\<close> as \<open>A\<^sub>1 \<and>\<^sup>\<Q> (\<cdots> \<and>\<^sup>\<Q> (A\<^sub>n\<^sub>-\<^sub>1 \<and>\<^sup>\<Q> A\<^sub>n) \<cdots>)\<close>:\<close>

definition generalized_conj_op :: "form list \<Rightarrow> form" ("\<and>\<^sup>\<Q>\<^sub>\<star> _" [0] 131) where
  [simp]: "\<and>\<^sup>\<Q>\<^sub>\<star> As = foldr1 (\<and>\<^sup>\<Q>) As"

definition imp_fun :: form ("\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>") where \<comment> \<open>\<open>\<equiv>\<close> used instead of \<open>=\<close>, see @{cite "andrews:2002"}\<close>
  [simp]: "\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> = \<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"

definition imp_op :: "form \<Rightarrow> form \<Rightarrow> form" (infixl "\<supset>\<^sup>\<Q>" 111) where
  [simp]: "A \<supset>\<^sup>\<Q> B = \<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B"

text \<open>Generalized implication. We define \<open>[A\<^sub>1, \<dots>, A\<^sub>n] \<supset>\<^sup>\<Q>\<^sub>\<star> B\<close> as \<open>A\<^sub>1 \<supset>\<^sup>\<Q> (\<cdots> \<supset>\<^sup>\<Q> (A\<^sub>n \<supset>\<^sup>\<Q> B) \<cdots>)\<close>:\<close>

definition generalized_imp_op :: "form list \<Rightarrow> form \<Rightarrow> form" (infixl "\<supset>\<^sup>\<Q>\<^sub>\<star>" 111) where
  [simp]: "As \<supset>\<^sup>\<Q>\<^sub>\<star> B = foldr (\<supset>\<^sup>\<Q>) As B"

text \<open>
  Given the definition below, it is interesting to note that \<open>\<sim>\<^sup>\<Q> A\<close> and \<open>F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> A\<close> are exactly the
  same formula, namely \<open>Q\<^bsub>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> \<sqdot> A\<close>:
\<close>

definition neg :: "form \<Rightarrow> form" ("\<sim>\<^sup>\<Q> _" [141] 141) where
  [simp]: "\<sim>\<^sup>\<Q> A = Q\<^bsub>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> \<sqdot> A"

definition disj_fun :: form ("\<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>") where
  [simp]: "\<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> = \<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"

definition disj_op :: "form \<Rightarrow> form \<Rightarrow> form" (infixl "\<or>\<^sup>\<Q>" 126) where
  [simp]: "A \<or>\<^sup>\<Q> B = \<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B"

definition exists :: "nat \<Rightarrow> type \<Rightarrow> form \<Rightarrow> form" ("(4\<exists>_\<^bsub>_\<^esub>./ _)" [0, 0, 141] 141) where
  [simp]: "\<exists>x\<^bsub>\<alpha>\<^esub>. A = \<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> A)"

lemma exists_fv:
  shows "free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. A) = free_vars A - {(x, \<alpha>)}"
  by simp

definition inequality_of_type :: "form \<Rightarrow> type \<Rightarrow> form \<Rightarrow> form" ("(_ \<noteq>\<^bsub>_\<^esub>/ _)" [103, 0, 103] 102) where
  [simp]: "A \<noteq>\<^bsub>\<alpha>\<^esub> B = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> B)"

subsection \<open>Well-formed formulas\<close>

inductive is_wff_of_type :: "type \<Rightarrow> form \<Rightarrow> bool" where
  var_is_wff: "is_wff_of_type \<alpha> (x\<^bsub>\<alpha>\<^esub>)"
| con_is_wff: "is_wff_of_type \<alpha> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>)"
| app_is_wff: "is_wff_of_type \<beta> (A \<sqdot> B)" if "is_wff_of_type (\<alpha>\<rightarrow>\<beta>) A" and "is_wff_of_type \<alpha> B"
| abs_is_wff: "is_wff_of_type (\<alpha>\<rightarrow>\<beta>) (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)" if "is_wff_of_type \<beta> A"

definition wffs_of_type :: "type \<Rightarrow> form set" ("wffs\<^bsub>_\<^esub>" [0]) where
  "wffs\<^bsub>\<alpha>\<^esub> = {f :: form. is_wff_of_type \<alpha> f}"

abbreviation wffs :: "form set" where
  "wffs \<equiv> \<Union>\<alpha>. wffs\<^bsub>\<alpha>\<^esub>"

lemma is_wff_of_type_wffs_of_type_eq [pred_set_conv]:
  shows "is_wff_of_type \<alpha> = (\<lambda>f. f \<in> wffs\<^bsub>\<alpha>\<^esub>)"
  unfolding wffs_of_type_def by simp

lemmas wffs_of_type_intros [intro!] = is_wff_of_type.intros[to_set]
lemmas wffs_of_type_induct [consumes 1, induct set: wffs_of_type] = is_wff_of_type.induct[to_set]
lemmas wffs_of_type_cases [consumes 1, cases set: wffs_of_type] = is_wff_of_type.cases[to_set]
lemmas wffs_of_type_simps = is_wff_of_type.simps[to_set]

lemma generalized_app_wff [intro]:
  assumes "length As = length ts"
  and "\<forall>k < length As. As ! k \<in> wffs\<^bsub>ts ! k\<^esub>"
  and "B \<in> wffs\<^bsub>foldr (\<rightarrow>) ts \<beta>\<^esub>"
  shows "\<sqdot>\<^sup>\<Q>\<^sub>\<star> B As \<in> wffs\<^bsub>\<beta>\<^esub>"
using assms proof (induction As ts arbitrary: B rule: list_induct2)
  case Nil
  then show ?case
    by simp
next
  case (Cons A As t ts)
  from Cons.prems(1) have "A \<in> wffs\<^bsub>t\<^esub>"
    by fastforce
  moreover from Cons.prems(2) have "B \<in> wffs\<^bsub>t\<rightarrow>foldr (\<rightarrow>) ts \<beta>\<^esub>"
    by auto
  ultimately have "B \<sqdot> A \<in> wffs\<^bsub>foldr (\<rightarrow>) ts \<beta>\<^esub>"
    by blast
  moreover have "\<forall>k < length As. (A # As) ! (Suc k) = As ! k \<and> (t # ts) ! (Suc k) = ts ! k"
    by force
  with Cons.prems(1) have "\<forall>k < length As. As ! k \<in> wffs\<^bsub>ts ! k\<^esub>"
    by fastforce
  ultimately have "\<sqdot>\<^sup>\<Q>\<^sub>\<star> (B \<sqdot> A) As \<in> wffs\<^bsub>\<beta>\<^esub>"
    using Cons.IH by (simp only:)
  moreover have "\<sqdot>\<^sup>\<Q>\<^sub>\<star> B (A # As) = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (B \<sqdot> A) As"
    by simp
  ultimately show ?case
    by (simp only:)
qed

lemma generalized_abs_wff [intro]:
  assumes "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<in> wffs\<^bsub>foldr (\<rightarrow>) (map snd vs) \<beta>\<^esub>"
using assms proof (induction vs)
  case Nil
  then show ?case
    by simp
next
  case (Cons v vs)
  let ?\<delta> = "foldr (\<rightarrow>) (map snd vs) \<beta>"
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  then have "FVar v \<in> wffs\<^bsub>\<alpha>\<^esub>"
    by auto
  from Cons.prems have "\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<in> wffs\<^bsub>?\<delta>\<^esub>"
    by (fact Cons.IH)
  with \<open>v = (x, \<alpha>)\<close> have "FAbs v (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) \<in> wffs\<^bsub>\<alpha>\<rightarrow>?\<delta>\<^esub>"
    by blast
  moreover from \<open>v = (x, \<alpha>)\<close> have "foldr (\<rightarrow>) (map snd (v # vs)) \<beta> = \<alpha>\<rightarrow>?\<delta>"
    by simp
  moreover have "\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B = FAbs v (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B)"
    by simp
  ultimately show ?case by (simp only:)
qed

lemma Q_wff [intro]:
  shows "Q\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<alpha>\<rightarrow>o\<^esub>"
  by auto

lemma iota_wff [intro]:
  shows "\<iota> \<in> wffs\<^bsub>(i\<rightarrow>o)\<rightarrow>i\<^esub>"
  by auto

lemma equality_wff [intro]:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "A =\<^bsub>\<alpha>\<^esub> B \<in> wffs\<^bsub>o\<^esub>"
  using assms by auto

lemma equivalence_wff [intro]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<equiv>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding equivalence_def by blast

lemma true_wff [intro]:
  shows "T\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
  by force

lemma false_wff [intro]:
  shows "F\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
  by auto

lemma pi_wff [intro]:
  shows "\<Prod>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>(\<alpha>\<rightarrow>o)\<rightarrow>o\<^esub>"
  using PI_def by fastforce

lemma forall_wff [intro]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<forall>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>o\<^esub>"
  using assms and pi_wff unfolding forall_def by blast

lemma generalized_forall_wff [intro]:
  assumes "B \<in> wffs\<^bsub>o\<^esub>"
  shows "\<forall>\<^sup>\<Q>\<^sub>\<star> vs B \<in> wffs\<^bsub>o\<^esub>"
using assms proof (induction vs)
  case (Cons v vs)
  then show ?case
    using surj_pair[of v] by force
qed simp

lemma conj_fun_wff [intro]:
  shows "\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>"
  by auto

lemma conj_op_wff [intro]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<and>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding conj_op_def by blast

lemma imp_fun_wff [intro]:
  shows "\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>"
  by auto

lemma imp_op_wff [intro]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<supset>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding imp_op_def by blast

lemma neg_wff [intro]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows " \<sim>\<^sup>\<Q> A \<in> wffs\<^bsub>o\<^esub>"
  using assms by fastforce

lemma disj_fun_wff [intro]:
  shows "\<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>"
  by auto

lemma disj_op_wff [intro]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<or>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  using assms by auto

lemma exists_wff [intro]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<exists>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>o\<^esub>"
  using assms by fastforce

lemma inequality_wff [intro]:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "A \<noteq>\<^bsub>\<alpha>\<^esub> B \<in> wffs\<^bsub>o\<^esub>"
  using assms by fastforce

lemma wffs_from_app:
  assumes "A \<sqdot> B \<in> wffs\<^bsub>\<beta>\<^esub>"
  obtains \<alpha> where "A \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  using assms by (blast elim: wffs_of_type_cases)

lemma wffs_from_generalized_app:
  assumes "\<sqdot>\<^sup>\<Q>\<^sub>\<star> B As \<in> wffs\<^bsub>\<beta>\<^esub>"
  obtains ts
  where "length ts = length As"
  and "\<forall>k < length As. As ! k \<in> wffs\<^bsub>ts ! k\<^esub>"
  and "B \<in> wffs\<^bsub>foldr (\<rightarrow>) ts \<beta>\<^esub>"
using assms proof (induction As arbitrary: B thesis)
  case Nil
  then show ?case
    by simp
next
  case (Cons A As)
  from Cons.prems have "\<sqdot>\<^sup>\<Q>\<^sub>\<star> (B \<sqdot> A) As \<in> wffs\<^bsub>\<beta>\<^esub>"
    by auto
  then obtain ts
    where "length ts = length As"
    and "\<forall>k < length As. As ! k \<in> wffs\<^bsub>ts ! k\<^esub>"
    and "B \<sqdot> A \<in> wffs\<^bsub>foldr (\<rightarrow>) ts \<beta>\<^esub>"
    using Cons.IH by blast
  moreover
  from \<open>B \<sqdot> A \<in> wffs\<^bsub>foldr (\<rightarrow>) ts \<beta>\<^esub>\<close> obtain t where "B \<in> wffs\<^bsub>t\<rightarrow>foldr (\<rightarrow>) ts \<beta>\<^esub>" and "A \<in> wffs\<^bsub>t\<^esub>"
    by (elim wffs_from_app)
  moreover from \<open>length ts = length As\<close> have "length (t # ts) = length (A # As)"
    by simp
  moreover from \<open>A \<in> wffs\<^bsub>t\<^esub>\<close> and \<open>\<forall>k < length As. As ! k \<in> wffs\<^bsub>ts ! k\<^esub>\<close>
  have "\<forall>k < length (A # As). (A # As) ! k \<in> wffs\<^bsub>(t # ts) ! k\<^esub>"
    by (simp add: nth_Cons')
  moreover from \<open>B \<in> wffs\<^bsub>t\<rightarrow>foldr (\<rightarrow>) ts \<beta>\<^esub>\<close> have "B \<in> wffs\<^bsub>foldr (\<rightarrow>) (t # ts) \<beta>\<^esub>"
    by simp
  ultimately show ?case
    using Cons.prems(1) by blast
qed

lemma wffs_from_abs:
  assumes "\<lambda>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>\<gamma>\<^esub>"
  obtains \<beta> where "\<gamma> = \<alpha>\<rightarrow>\<beta>" and "A \<in> wffs\<^bsub>\<beta>\<^esub>"
  using assms by (blast elim: wffs_of_type_cases)

lemma wffs_from_equality:
  assumes "A =\<^bsub>\<alpha>\<^esub> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  using assms by (fastforce elim: wffs_of_type_cases)+

lemma wffs_from_equivalence:
  assumes "A \<equiv>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding equivalence_def by (fact wffs_from_equality)+

lemma wffs_from_forall:
  assumes "\<forall>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding forall_def and PI_def
  by (fold equality_of_type_def) (drule wffs_from_equality, blast elim: wffs_from_abs)

lemma wffs_from_conj_fun:
  assumes "\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  using assms by (auto elim: wffs_from_app wffs_from_abs)

lemma wffs_from_conj_op:
  assumes "A \<and>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding conj_op_def by (elim wffs_from_conj_fun)+

lemma wffs_from_imp_fun:
  assumes "\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  using assms by (auto elim: wffs_from_app wffs_from_abs)

lemma wffs_from_imp_op:
  assumes "A \<supset>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding imp_op_def by (elim wffs_from_imp_fun)+

lemma wffs_from_neg:
  assumes "\<sim>\<^sup>\<Q> A \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding neg_def by (fold equality_of_type_def) (drule wffs_from_equality, blast)

lemma wffs_from_disj_fun:
  assumes "\<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  using assms by (auto elim: wffs_from_app wffs_from_abs)

lemma wffs_from_disj_op:
  assumes "A \<or>\<^sup>\<Q> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  using assms and wffs_from_disj_fun unfolding disj_op_def by blast+

lemma wffs_from_exists:
  assumes "\<exists>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms unfolding exists_def using wffs_from_neg and wffs_from_forall by blast

lemma wffs_from_inequality:
  assumes "A \<noteq>\<^bsub>\<alpha>\<^esub> B \<in> wffs\<^bsub>o\<^esub>"
  shows "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  using assms unfolding inequality_of_type_def using wffs_from_equality and wffs_from_neg by meson+

lemma wff_has_unique_type:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "A \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<alpha> = \<beta>"
using assms proof (induction arbitrary: \<alpha> \<beta> rule: form.induct)
  case (FVar v)
  obtain x and \<gamma> where "v = (x, \<gamma>)"
    by fastforce
  with FVar.prems have "\<alpha> = \<gamma>" and "\<beta> = \<gamma>"
    by (blast elim: wffs_of_type_cases)+
  then show ?case ..
next
  case (FCon k)
  obtain x and \<gamma> where "k = (x, \<gamma>)"
    by fastforce
  with FCon.prems have "\<alpha> = \<gamma>" and "\<beta> = \<gamma>"
    by (blast elim: wffs_of_type_cases)+
  then show ?case ..
next
  case (FApp A B)
  from FApp.prems obtain \<alpha>' and \<beta>' where "A \<in> wffs\<^bsub>\<alpha>'\<rightarrow>\<alpha>\<^esub>" and "A \<in> wffs\<^bsub>\<beta>'\<rightarrow>\<beta>\<^esub>"
    by (blast elim: wffs_from_app)
  with FApp.IH(1) show ?case
    by blast
next
  case (FAbs v A)
  obtain x and \<gamma> where "v = (x, \<gamma>)"
    by fastforce
  with FAbs.prems obtain \<alpha>' and \<beta>'
    where "\<alpha> = \<gamma>\<rightarrow>\<alpha>'" and "\<beta> = \<gamma>\<rightarrow>\<beta>'" and "A \<in> wffs\<^bsub>\<alpha>'\<^esub>" and "A \<in> wffs\<^bsub>\<beta>'\<^esub>"
    by (blast elim: wffs_from_abs)
  with FAbs.IH show ?case
    by simp
qed

lemma wffs_of_type_o_induct [consumes 1, case_names Var Con App]:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  and "\<And>x. \<P> (x\<^bsub>o\<^esub>)"
  and "\<And>c. \<P> (\<lbrace>c\<rbrace>\<^bsub>o\<^esub>)"
  and "\<And>A B \<alpha>. A \<in> wffs\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> \<P> (A \<sqdot> B)"
  shows "\<P> A"
  using assms by (cases rule: wffs_of_type_cases) simp_all

lemma diff_types_implies_diff_wffs:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "\<alpha> \<noteq> \<beta>"
  shows "A \<noteq> B"
  using assms and wff_has_unique_type by blast

lemma is_free_for_in_generalized_app [intro]:
  assumes "is_free_for A v B" and "\<forall>C \<in> lset Cs. is_free_for A v C"
  shows "is_free_for A v (\<sqdot>\<^sup>\<Q>\<^sub>\<star> B Cs)"
using assms proof (induction Cs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc C Cs)
  from snoc.prems(2) have "is_free_for A v C" and "\<forall>C \<in> lset Cs. is_free_for A v C"
    by simp_all
  with snoc.prems(1) have "is_free_for A v (\<sqdot>\<^sup>\<Q>\<^sub>\<star> B Cs)"
    using snoc.IH by simp
  with \<open>is_free_for A v C\<close> show ?case
    using is_free_for_to_app by simp
qed

lemma is_free_for_in_equality [intro]:
  assumes "is_free_for A v B" and "is_free_for A v C"
  shows "is_free_for A v (B =\<^bsub>\<alpha>\<^esub> C)"
  using assms unfolding equality_of_type_def and Q_def and Q_constant_of_type_def
  by (intro is_free_for_to_app is_free_for_in_con)

lemma is_free_for_in_equivalence [intro]:
  assumes "is_free_for A v B" and "is_free_for A v C"
  shows "is_free_for A v (B \<equiv>\<^sup>\<Q> C)"
  using assms unfolding equivalence_def by (rule is_free_for_in_equality)

lemma is_free_for_in_true [intro]:
  shows "is_free_for A v (T\<^bsub>o\<^esub>)"
  by force

lemma is_free_for_in_false [intro]:
  shows "is_free_for A v (F\<^bsub>o\<^esub>)"
  unfolding false_def by (intro is_free_for_in_equality is_free_for_closed_form) simp_all

lemma is_free_for_in_forall [intro]:
  assumes "is_free_for A v B" and "(x, \<alpha>) \<notin> free_vars A"
  shows "is_free_for A v (\<forall>x\<^bsub>\<alpha>\<^esub>. B)"
unfolding forall_def and PI_def proof (fold equality_of_type_def)
  have "is_free_for A v (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>)"
    using is_free_for_to_abs[OF is_free_for_in_true assms(2)] by fastforce
  moreover have "is_free_for A v (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
    by (fact is_free_for_to_abs[OF assms])
  ultimately show "is_free_for A v (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> =\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
    by (iprover intro: assms(1) is_free_for_in_equality is_free_for_in_true is_free_for_to_abs)
qed

lemma is_free_for_in_generalized_forall [intro]:
  assumes "is_free_for A v B" and "lset vs \<inter> free_vars A = {}"
  shows "is_free_for A v (\<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
using assms proof (induction vs)
  case Nil
  then show ?case
    by simp
next
  case (Cons v' vs)
  obtain x and \<alpha> where "v' = (x, \<alpha>)"
    by fastforce
  from Cons.prems(2) have "v' \<notin> free_vars A" and "lset vs \<inter> free_vars A = {}"
    by simp_all
  from Cons.prems(1) and \<open>lset vs \<inter> free_vars A = {}\<close> have "is_free_for A v (\<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
    by (fact Cons.IH)
  from this and \<open>v' \<notin> free_vars A\<close>[unfolded \<open>v' = (x, \<alpha>)\<close>] have "is_free_for A v (\<forall>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
    by (intro is_free_for_in_forall)
  with \<open>v' = (x, \<alpha>)\<close> show ?case
    by simp
qed

lemma is_free_for_in_conj [intro]:
  assumes "is_free_for A v B" and "is_free_for A v C"
  shows "is_free_for A v (B \<and>\<^sup>\<Q> C)"
proof -
  have "free_vars \<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> = {}"
    by force
  then have "is_free_for A v (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>)"
    using is_free_for_closed_form by fast
  with assms have "is_free_for A v (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> B \<sqdot> C)"
    by (intro is_free_for_to_app)
  then show ?thesis
    by (fold conj_op_def)
qed

lemma is_free_for_in_imp [intro]:
  assumes "is_free_for A v B" and "is_free_for A v C"
  shows "is_free_for A v (B \<supset>\<^sup>\<Q> C)"
proof -
  have "free_vars \<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> = {}"
    by force
  then have "is_free_for A v (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>)"
    using is_free_for_closed_form by fast
  with assms have "is_free_for A v (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> B \<sqdot> C)"
    by (intro is_free_for_to_app)
  then show ?thesis
    by (fold imp_op_def)
qed

lemma is_free_for_in_neg [intro]:
  assumes "is_free_for A v B"
  shows "is_free_for A v (\<sim>\<^sup>\<Q> B)"
  using assms unfolding neg_def and Q_def and Q_constant_of_type_def
  by (intro is_free_for_to_app is_free_for_in_false is_free_for_in_con)

lemma is_free_for_in_disj [intro]:
  assumes "is_free_for A v B" and "is_free_for A v C"
  shows "is_free_for A v (B \<or>\<^sup>\<Q> C)"
proof -
  have "free_vars \<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> = {}"
    by force
  then have "is_free_for A v (\<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>)"
    using is_free_for_closed_form by fast
  with assms have "is_free_for A v (\<or>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> B \<sqdot> C)"
    by (intro is_free_for_to_app)
  then show ?thesis
    by (fold disj_op_def)
qed

lemma replacement_preserves_typing:
  assumes "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D"
  and "A \<preceq>\<^bsub>p\<^esub> C"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "C \<in> wffs\<^bsub>\<beta>\<^esub> \<longleftrightarrow> D \<in> wffs\<^bsub>\<beta>\<^esub>"
using assms proof (induction arbitrary: \<beta> rule: is_replacement_at.induct)
  case (pos_found p C C' A)
  then show ?case
    using diff_types_implies_diff_wffs by auto
qed (metis is_subform_at.simps(2,3,4) wffs_from_app wffs_from_abs wffs_of_type_simps)+

corollary replacement_preserves_typing':
  assumes "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D"
  and "A \<preceq>\<^bsub>p\<^esub> C"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "C \<in> wffs\<^bsub>\<beta>\<^esub>" and "D \<in> wffs\<^bsub>\<gamma>\<^esub>"
  shows "\<beta> = \<gamma>"
  using assms and replacement_preserves_typing and wff_has_unique_type by simp

text \<open>Closed formulas and sentences:\<close>

definition is_closed_wff_of_type :: "form \<Rightarrow> type \<Rightarrow> bool" where
  [iff]: "is_closed_wff_of_type A \<alpha> \<longleftrightarrow> A \<in> wffs\<^bsub>\<alpha>\<^esub> \<and> free_vars A = {}"

definition is_sentence :: "form \<Rightarrow> bool" where
  [iff]: "is_sentence A \<longleftrightarrow> is_closed_wff_of_type A o"

subsection \<open>Substitutions\<close>

type_synonym substitution = "(var, form) fmap"

definition is_substitution :: "substitution \<Rightarrow> bool" where
  [iff]: "is_substitution \<theta> \<longleftrightarrow> (\<forall>(x, \<alpha>) \<in> fmdom' \<theta>. \<theta> $$! (x, \<alpha>) \<in> wffs\<^bsub>\<alpha>\<^esub>)"

fun substitute :: "substitution \<Rightarrow> form \<Rightarrow> form" ("\<^bold>S _ _" [51, 51]) where
  "\<^bold>S \<theta> (x\<^bsub>\<alpha>\<^esub>) = (case \<theta> $$ (x, \<alpha>) of None \<Rightarrow> x\<^bsub>\<alpha>\<^esub> | Some A \<Rightarrow> A)"
| "\<^bold>S \<theta> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>"
| "\<^bold>S \<theta> (A \<sqdot> B) = (\<^bold>S \<theta> A) \<sqdot> (\<^bold>S \<theta> B)"
| "\<^bold>S \<theta> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = (if (x, \<alpha>) \<notin> fmdom' \<theta> then \<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S \<theta> A else \<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S (fmdrop (x, \<alpha>) \<theta>) A)"

lemma empty_substitution_neutrality:
  shows "\<^bold>S {$$} A = A"
  by (induction A) auto

lemma substitution_preserves_typing:
  assumes "is_substitution \<theta>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<^bold>S \<theta> A \<in> wffs\<^bsub>\<alpha>\<^esub>"
using assms(2) and assms(1)[unfolded is_substitution_def] proof (induction arbitrary: \<theta>)
  case (var_is_wff \<alpha> x)
  then show ?case
    by (cases "(x, \<alpha>) \<in> fmdom' \<theta>") (use fmdom'_notI in \<open>force+\<close>)
next
  case (abs_is_wff \<beta> A \<alpha> x)
  then show ?case
  proof (cases "(x, \<alpha>) \<in> fmdom' \<theta>")
    case True
    then have "\<^bold>S \<theta> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S (fmdrop (x, \<alpha>) \<theta>) A"
      by simp
    moreover from abs_is_wff.prems have "is_substitution (fmdrop (x, \<alpha>) \<theta>)"
      by fastforce
    with abs_is_wff.IH have "\<^bold>S (fmdrop (x, \<alpha>) \<theta>) A \<in> wffs\<^bsub>\<beta>\<^esub>"
      by simp
    ultimately show ?thesis
      by auto
  next
    case False
    then have "\<^bold>S \<theta> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S \<theta> A"
      by simp
    moreover from abs_is_wff.IH have "\<^bold>S \<theta> A \<in> wffs\<^bsub>\<beta>\<^esub>"
      using abs_is_wff.prems by blast
    ultimately show ?thesis
      by fastforce
  qed
qed force+

lemma derived_substitution_simps:
  shows "\<^bold>S \<theta> T\<^bsub>o\<^esub> = T\<^bsub>o\<^esub>"
  and "\<^bold>S \<theta> F\<^bsub>o\<^esub> = F\<^bsub>o\<^esub>"
  and "\<^bold>S \<theta> (\<Prod>\<^bsub>\<alpha>\<^esub>) = \<Prod>\<^bsub>\<alpha>\<^esub>"
  and "\<^bold>S \<theta> (\<sim>\<^sup>\<Q> B) = \<sim>\<^sup>\<Q> (\<^bold>S \<theta> B)"
  and "\<^bold>S \<theta> (B =\<^bsub>\<alpha>\<^esub> C) = (\<^bold>S \<theta> B) =\<^bsub>\<alpha>\<^esub> (\<^bold>S \<theta> C)"
  and "\<^bold>S \<theta> (B \<and>\<^sup>\<Q> C) = (\<^bold>S \<theta> B) \<and>\<^sup>\<Q> (\<^bold>S \<theta> C)"
  and "\<^bold>S \<theta> (B \<or>\<^sup>\<Q> C) = (\<^bold>S \<theta> B) \<or>\<^sup>\<Q> (\<^bold>S \<theta> C)"
  and "\<^bold>S \<theta> (B \<supset>\<^sup>\<Q> C) = (\<^bold>S \<theta> B) \<supset>\<^sup>\<Q> (\<^bold>S \<theta> C)"
  and "\<^bold>S \<theta> (B \<equiv>\<^sup>\<Q> C) = (\<^bold>S \<theta> B) \<equiv>\<^sup>\<Q> (\<^bold>S \<theta> C)"
  and "\<^bold>S \<theta> (B \<noteq>\<^bsub>\<alpha>\<^esub> C) = (\<^bold>S \<theta> B) \<noteq>\<^bsub>\<alpha>\<^esub> (\<^bold>S \<theta> C)"
  and "\<^bold>S \<theta> (\<forall>x\<^bsub>\<alpha>\<^esub>. B) = (if (x, \<alpha>) \<notin> fmdom' \<theta> then \<forall>x\<^bsub>\<alpha>\<^esub>. \<^bold>S \<theta> B else \<forall>x\<^bsub>\<alpha>\<^esub>. \<^bold>S (fmdrop (x, \<alpha>) \<theta>) B)"
  and "\<^bold>S \<theta> (\<exists>x\<^bsub>\<alpha>\<^esub>. B) = (if (x, \<alpha>) \<notin> fmdom' \<theta> then \<exists>x\<^bsub>\<alpha>\<^esub>. \<^bold>S \<theta> B else \<exists>x\<^bsub>\<alpha>\<^esub>. \<^bold>S (fmdrop (x, \<alpha>) \<theta>) B)"
  by auto

lemma generalized_app_substitution:
  shows "\<^bold>S \<theta> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> A Bs) = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<^bold>S \<theta> A) (map (\<lambda>B. \<^bold>S \<theta> B) Bs)"
  by (induction Bs arbitrary: A) simp_all

lemma generalized_abs_substitution:
  shows "\<^bold>S \<theta> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) = \<lambda>\<^sup>\<Q>\<^sub>\<star> vs (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset vs) \<theta>) A)"
proof (induction vs arbitrary: \<theta>)
  case Nil
  then show ?case
    by simp
next
  case (Cons v vs)
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  then show ?case
  proof (cases "v \<notin> fmdom' \<theta>")
    case True
    then have *: "fmdom' \<theta> \<inter> lset (v # vs) = fmdom' \<theta> \<inter> lset vs"
      by simp
    from True have "\<^bold>S \<theta> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S \<theta> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A)"
      using \<open>v = (x, \<alpha>)\<close> by auto
    also have "\<dots> = \<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>\<^sup>\<Q>\<^sub>\<star> vs (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset vs) \<theta>) A)"
      using Cons.IH by (simp only:)
    also have "\<dots> = \<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset (v # vs)) \<theta>) A)"
      using \<open>v = (x, \<alpha>)\<close> and * by auto
    finally show ?thesis .
  next
    case False
    let ?\<theta>' = "fmdrop v \<theta>"
    have *: "fmdrop_set (fmdom' \<theta> \<inter> lset (v # vs)) \<theta> = fmdrop_set (fmdom' ?\<theta>' \<inter> lset vs) ?\<theta>'"
      using False by clarsimp (metis Int_Diff Int_commute fmdrop_set_insert insert_Diff_single)
    from False have "\<^bold>S \<theta> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S ?\<theta>' (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A)"
      using \<open>v = (x, \<alpha>)\<close> by auto
    also have "\<dots> = \<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>\<^sup>\<Q>\<^sub>\<star> vs (\<^bold>S (fmdrop_set (fmdom' ?\<theta>' \<inter> lset vs) ?\<theta>') A)"
      using Cons.IH by (simp only:)
    also have "\<dots> = \<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset (v # vs)) \<theta>) A)"
      using \<open>v = (x, \<alpha>)\<close> and * by auto
    finally show ?thesis .
  qed
qed

lemma generalized_forall_substitution:
  shows "\<^bold>S \<theta> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs A) = \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset vs) \<theta>) A)"
proof (induction vs arbitrary: \<theta>)
  case Nil
  then show ?case
    by simp
next
  case (Cons v vs)
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  then show ?case
  proof (cases "v \<notin> fmdom' \<theta>")
    case True
    then have *: "fmdom' \<theta> \<inter> lset (v # vs) = fmdom' \<theta> \<inter> lset vs"
      by simp
    from True have "\<^bold>S \<theta> (\<forall>\<^sup>\<Q>\<^sub>\<star> (v # vs) A) = \<forall>x\<^bsub>\<alpha>\<^esub>. \<^bold>S \<theta> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs A)"
      using \<open>v = (x, \<alpha>)\<close> by auto
    also have "\<dots> = \<forall>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset vs) \<theta>) A)"
      using Cons.IH by (simp only:)
    also have "\<dots> = \<forall>\<^sup>\<Q>\<^sub>\<star> (v # vs) (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset (v # vs)) \<theta>) A)"
      using \<open>v = (x, \<alpha>)\<close> and * by auto
    finally show ?thesis .
  next
    case False
    let ?\<theta>' = "fmdrop v \<theta>"
    have *: "fmdrop_set (fmdom' \<theta> \<inter> lset (v # vs)) \<theta> = fmdrop_set (fmdom' ?\<theta>' \<inter> lset vs) ?\<theta>'"
      using False by clarsimp (metis Int_Diff Int_commute fmdrop_set_insert insert_Diff_single)
    from False have "\<^bold>S \<theta> (\<forall>\<^sup>\<Q>\<^sub>\<star> (v # vs) A) = \<forall>x\<^bsub>\<alpha>\<^esub>. \<^bold>S ?\<theta>' (\<forall>\<^sup>\<Q>\<^sub>\<star> vs A)"
      using \<open>v = (x, \<alpha>)\<close> by auto
    also have "\<dots> = \<forall>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<^bold>S (fmdrop_set (fmdom' ?\<theta>' \<inter> lset vs) ?\<theta>') A)"
      using Cons.IH by (simp only:)
    also have "\<dots> = \<forall>\<^sup>\<Q>\<^sub>\<star> (v # vs) (\<^bold>S (fmdrop_set (fmdom' \<theta> \<inter> lset (v # vs)) \<theta>) A)"
      using \<open>v = (x, \<alpha>)\<close> and * by auto
    finally show ?thesis .
  qed
qed

lemma singleton_substitution_simps:
  shows "\<^bold>S {(x, \<alpha>) \<Zinj> A} (y\<^bsub>\<beta>\<^esub>) = (if (x, \<alpha>) \<noteq> (y, \<beta>) then y\<^bsub>\<beta>\<^esub> else A)"
  and "\<^bold>S {(x, \<alpha>) \<Zinj> A} (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>"
  and "\<^bold>S {(x, \<alpha>) \<Zinj> A} (B \<sqdot> C) = (\<^bold>S {(x, \<alpha>) \<Zinj> A} B) \<sqdot> (\<^bold>S {(x, \<alpha>) \<Zinj> A} C)"
  and "\<^bold>S {(x, \<alpha>) \<Zinj> A} (\<lambda>y\<^bsub>\<beta>\<^esub>. B) = \<lambda>y\<^bsub>\<beta>\<^esub>. (if (x, \<alpha>) = (y, \<beta>) then B else \<^bold>S {(x, \<alpha>) \<Zinj> A} B)"
  by (simp_all add: empty_substitution_neutrality fmdrop_fmupd_same)

lemma substitution_preserves_freeness:
  assumes "y \<notin> free_vars A" and "y \<noteq> z"
  shows "y \<notin> free_vars \<^bold>S {x \<Zinj> FVar z} A"
using assms(1) proof (induction A rule: free_vars_form.induct)
  case (1 x' \<alpha>)
  with assms(2) show ?case
    using surj_pair[of z] by (cases "x = (x', \<alpha>)") force+
next
  case (4 x' \<alpha> A)
  then show ?case
    using surj_pair[of z]
    by (cases "x = (x', \<alpha>)") (use singleton_substitution_simps(4) in presburger, auto)
qed auto

lemma renaming_substitution_minimal_change:
  assumes "y \<notin> vars A" and "y \<noteq> z"
  shows "y \<notin> vars (\<^bold>S {x \<Zinj> FVar z} A)"
using assms(1) proof (induction A rule: vars_form.induct)
  case (1 x' \<alpha>)
  with assms(2) show ?case
    using surj_pair[of z] by (cases "x = (x', \<alpha>)") force+
next
  case (4 x' \<alpha> A)
  then show ?case
    using surj_pair[of z]
    by (cases "x = (x', \<alpha>)") (use singleton_substitution_simps(4) in presburger, auto)
qed auto

lemma free_var_singleton_substitution_neutrality:
  assumes "v \<notin> free_vars A"
  shows "\<^bold>S {v \<Zinj> B} A = A"
  using assms
  by
    (induction A rule: free_vars_form.induct)
    (simp_all, metis empty_substitution_neutrality fmdrop_empty fmdrop_fmupd_same)

lemma identity_singleton_substitution_neutrality:
  shows "\<^bold>S {v \<Zinj> FVar v} A = A"
  by
    (induction A rule: free_vars_form.induct)
    (simp_all add: empty_substitution_neutrality fmdrop_fmupd_same)

lemma free_var_in_renaming_substitution:
  assumes "x \<noteq> y"
  shows "(x, \<alpha>) \<notin> free_vars (\<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B)"
  using assms by (induction B rule: free_vars_form.induct) simp_all

lemma renaming_substitution_preserves_form_size:
  shows "form_size (\<^bold>S {v \<Zinj> FVar v'} A) = form_size A"
proof (induction A rule: form_size.induct)
  case (1 x \<alpha>)
  then show ?case
    using form_size.elims by auto
next
  case (4 x \<alpha> A)
  then show ?case
    by (cases "v = (x, \<alpha>)") (use singleton_substitution_simps(4) in presburger, auto)
qed simp_all

text \<open>The following lemma corresponds to X5100 in @{cite "andrews:2002"}:\<close>

lemma substitution_composability:
  assumes "v' \<notin> vars B"
  shows "\<^bold>S {v' \<Zinj> A} \<^bold>S {v \<Zinj> FVar v'} B = \<^bold>S {v \<Zinj> A} B"
using assms proof (induction B arbitrary: v')
  case (FAbs w C)
  then show ?case
  proof (cases "v = w")
    case True
    from \<open>v' \<notin> vars (FAbs w C)\<close> have "v' \<notin> free_vars (FAbs w C)"
      using free_vars_in_all_vars by blast
    then have "\<^bold>S {v' \<Zinj> A} (FAbs w C) = FAbs w C"
      by (rule free_var_singleton_substitution_neutrality)
    from \<open>v = w\<close> have "v \<notin> free_vars (FAbs w C)"
      using surj_pair[of w] by fastforce
    then have "\<^bold>S {v \<Zinj> A} (FAbs w C) = FAbs w C"
      by (fact free_var_singleton_substitution_neutrality)
    also from \<open>\<^bold>S {v' \<Zinj> A} (FAbs w C) = FAbs w C\<close> have "\<dots> = \<^bold>S {v' \<Zinj> A} (FAbs w C)"
      by (simp only:)
    also from \<open>v = w\<close> have "\<dots> = \<^bold>S {v' \<Zinj> A} \<^bold>S {v \<Zinj> FVar v'} (FAbs w C)"
      using free_var_singleton_substitution_neutrality[OF \<open>v \<notin> free_vars (FAbs w C)\<close>] by (simp only:)
    finally show ?thesis ..
  next
    case False
    from FAbs.prems have "v' \<notin> vars C"
      using surj_pair[of w] by fastforce
    then show ?thesis
    proof (cases "v' = w")
      case True
      with FAbs.prems show ?thesis
        using vars_form.elims by auto
    next
      case False
      from \<open>v \<noteq> w\<close> have "\<^bold>S {v \<Zinj> A} (FAbs w C) = FAbs w (\<^bold>S {v \<Zinj> A} C)"
        using surj_pair[of w] by fastforce
      also from FAbs.IH have "\<dots> = FAbs w (\<^bold>S {v' \<Zinj> A} \<^bold>S {v \<Zinj> FVar v'} C)"
        using \<open>v' \<notin> vars C\<close> by simp
      also from \<open>v' \<noteq> w\<close> have "\<dots> = \<^bold>S {v' \<Zinj> A} (FAbs w (\<^bold>S {v \<Zinj> FVar v'} C))"
        using surj_pair[of w] by fastforce
      also from \<open>v \<noteq> w\<close> have "\<dots> = \<^bold>S {v' \<Zinj> A} \<^bold>S {v \<Zinj> FVar v'} (FAbs w C)"
        using surj_pair[of w] by fastforce
      finally show ?thesis ..
    qed
  qed
qed auto

text \<open>The following lemma corresponds to X5101 in @{cite "andrews:2002"}:\<close>

lemma renaming_substitution_composability:
  assumes "z \<notin> free_vars A" and "is_free_for (FVar z) x A"
  shows "\<^bold>S {z \<Zinj> FVar y} \<^bold>S {x \<Zinj> FVar z} A = \<^bold>S {x \<Zinj> FVar y} A"
using assms proof (induction A arbitrary: z)
  case (FVar v)
  then show ?case
    using surj_pair[of v] and surj_pair[of z] by fastforce
next
  case (FCon k)
  then show ?case
    using surj_pair[of k] by fastforce
next
  case (FApp B C)
  let ?\<theta>\<^sub>z\<^sub>y = "{z \<Zinj> FVar y}" and ?\<theta>\<^sub>x\<^sub>z = "{x \<Zinj> FVar z}" and ?\<theta>\<^sub>x\<^sub>y = "{x \<Zinj> FVar y}"
  from \<open>is_free_for (FVar z) x (B \<sqdot> C)\<close> have "is_free_for (FVar z) x B" and "is_free_for (FVar z) x C"
    using is_free_for_from_app by iprover+
  moreover from \<open>z \<notin> free_vars (B \<sqdot> C)\<close> have "z \<notin> free_vars B" and "z \<notin> free_vars C"
    by simp_all
  ultimately have *: "\<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z B = \<^bold>S ?\<theta>\<^sub>x\<^sub>y B" and **: "\<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z C = \<^bold>S ?\<theta>\<^sub>x\<^sub>y C"
    using FApp.IH by simp_all
  have "\<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z (B \<sqdot> C) = (\<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z B) \<sqdot> (\<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z C)"
    by simp
  also from * and ** have "\<dots> = (\<^bold>S ?\<theta>\<^sub>x\<^sub>y B) \<sqdot> (\<^bold>S ?\<theta>\<^sub>x\<^sub>y C)"
    by (simp only:)
  also have "\<dots> = \<^bold>S ?\<theta>\<^sub>x\<^sub>y (B \<sqdot> C)"
    by simp
  finally show ?case .
next
  case (FAbs w B)
  let ?\<theta>\<^sub>z\<^sub>y = "{z \<Zinj> FVar y}" and ?\<theta>\<^sub>x\<^sub>z = "{x \<Zinj> FVar z}" and ?\<theta>\<^sub>x\<^sub>y = "{x \<Zinj> FVar y}"
  show ?case
  proof (cases "x = w")
    case True
    then show ?thesis
    proof (cases "z = w")
      case True
      with \<open>x = w\<close> have "x \<notin> free_vars (FAbs w B)" and "z \<notin> free_vars (FAbs w B)"
        using surj_pair[of w] by fastforce+
      from \<open>x \<notin> free_vars (FAbs w B)\<close> have "\<^bold>S ?\<theta>\<^sub>x\<^sub>y (FAbs w B) = FAbs w B"
        by (fact free_var_singleton_substitution_neutrality)
      also from \<open>z \<notin> free_vars (FAbs w B)\<close> have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y (FAbs w B)"
        by (fact free_var_singleton_substitution_neutrality[symmetric])
      also from \<open>x \<notin> free_vars (FAbs w B)\<close> have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z (FAbs w B)"
        using free_var_singleton_substitution_neutrality by simp
      finally show ?thesis ..
    next
      case False
      with \<open>x = w\<close> have "z \<notin> free_vars B" and "x \<notin> free_vars (FAbs w B)"
        using \<open>z \<notin> free_vars (FAbs w B)\<close> and surj_pair[of w] by fastforce+
      from \<open>z \<notin> free_vars B\<close> have "\<^bold>S ?\<theta>\<^sub>z\<^sub>y B = B"
        by (fact free_var_singleton_substitution_neutrality)
      from \<open>x \<notin> free_vars (FAbs w B)\<close> have "\<^bold>S ?\<theta>\<^sub>x\<^sub>y (FAbs w B) = FAbs w B"
        by (fact free_var_singleton_substitution_neutrality)
      also from \<open>\<^bold>S ?\<theta>\<^sub>z\<^sub>y B = B\<close> have "\<dots> = FAbs w (\<^bold>S ?\<theta>\<^sub>z\<^sub>y B)"
        by (simp only:)
      also from \<open>z \<notin> free_vars (FAbs w B)\<close> have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y (FAbs w B)"
        by (simp add: \<open>FAbs w B = FAbs w (\<^bold>S ?\<theta>\<^sub>z\<^sub>y B)\<close> free_var_singleton_substitution_neutrality)
      also from \<open>x \<notin> free_vars (FAbs w B)\<close> have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z (FAbs w B)"
        using free_var_singleton_substitution_neutrality by simp
      finally show ?thesis ..
    qed
  next
    case False
    then show ?thesis
    proof (cases "z = w")
      case True
      have "x \<notin> free_vars B"
      proof (rule ccontr)
        assume "\<not> x \<notin> free_vars B"
        with \<open>x \<noteq> w\<close> have "x \<in> free_vars (FAbs w B)"
          using surj_pair[of w] by fastforce
        then obtain p where "p \<in> positions (FAbs w B)" and "is_free_at x p (FAbs w B)"
          using free_vars_in_is_free_at by blast
        with \<open>is_free_for (FVar z) x (FAbs w B)\<close> have "\<not> in_scope_of_abs z p (FAbs w B)"
          by (meson empty_is_position is_free_at_in_free_vars is_free_at_in_var is_free_for_def)
        moreover obtain p' where "p = \<guillemotleft> # p'"
          using is_free_at_from_absE[OF \<open>is_free_at x p (FAbs w B)\<close>] by blast
        ultimately have "z \<noteq> w"
          using in_scope_of_abs_in_abs by blast
        with \<open>z = w\<close> show False
          by contradiction
      qed
      then have *: "\<^bold>S ?\<theta>\<^sub>x\<^sub>y B = \<^bold>S ?\<theta>\<^sub>x\<^sub>z B"
        using free_var_singleton_substitution_neutrality by auto
      from \<open>x \<noteq> w\<close> have "\<^bold>S ?\<theta>\<^sub>x\<^sub>y (FAbs w B) = FAbs w (\<^bold>S ?\<theta>\<^sub>x\<^sub>y B)"
        using surj_pair[of w] by fastforce
      also from * have "\<dots> = FAbs w (\<^bold>S ?\<theta>\<^sub>x\<^sub>z B)"
        by (simp only:)
      also from FAbs.prems(1) have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y (FAbs w (\<^bold>S ?\<theta>\<^sub>x\<^sub>z B))"
        using \<open>x \<notin> free_vars B\<close> and free_var_singleton_substitution_neutrality by auto
      also from \<open>x \<noteq> w\<close> have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z (FAbs w B)"
        using surj_pair[of w] by fastforce
      finally show ?thesis ..
    next
      case False
      obtain v\<^sub>w and \<alpha> where "w = (v\<^sub>w, \<alpha>)"
        by fastforce
      with \<open>is_free_for (FVar z) x (FAbs w B)\<close> and \<open>x \<noteq> w\<close> have "is_free_for (FVar z) x B"
        using is_free_for_from_abs by iprover
      moreover from \<open>z \<notin> free_vars (FAbs w B)\<close> and \<open>z \<noteq> w\<close> and \<open>w = (v\<^sub>w, \<alpha>)\<close> have "z \<notin> free_vars B"
        by simp
      ultimately have *: "\<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z B = \<^bold>S ?\<theta>\<^sub>x\<^sub>y B"
        using FAbs.IH by simp
      from \<open>x \<noteq> w\<close> have "\<^bold>S ?\<theta>\<^sub>x\<^sub>y (FAbs w B) = FAbs w (\<^bold>S ?\<theta>\<^sub>x\<^sub>y B)"
        using \<open>w = (v\<^sub>w, \<alpha>)\<close> and free_var_singleton_substitution_neutrality by simp
      also from * have "\<dots> = FAbs w (\<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z B)"
        by (simp only:)
      also from \<open>z \<noteq> w\<close> have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y (FAbs w (\<^bold>S ?\<theta>\<^sub>x\<^sub>z B))"
        using \<open>w = (v\<^sub>w, \<alpha>)\<close> and free_var_singleton_substitution_neutrality by simp
      also from \<open>x \<noteq> w\<close> have "\<dots> = \<^bold>S ?\<theta>\<^sub>z\<^sub>y \<^bold>S ?\<theta>\<^sub>x\<^sub>z (FAbs w B)"
        using \<open>w = (v\<^sub>w, \<alpha>)\<close> and free_var_singleton_substitution_neutrality by simp
      finally show ?thesis ..
    qed
  qed
qed

lemma absent_vars_substitution_preservation:
  assumes "v \<notin> vars A"
  and "\<forall>v' \<in> fmdom' \<theta>. v \<notin> vars (\<theta> $$! v')"
  shows "v \<notin> vars (\<^bold>S \<theta> A)"
using assms proof (induction A arbitrary: \<theta>)
  case (FVar v')
  then show ?case
    using surj_pair[of v'] by (cases "v' \<in> fmdom' \<theta>") (use fmlookup_dom'_iff in force)+
next
  case (FCon k)
  then show ?case
    using surj_pair[of k] by fastforce
next
  case FApp
  then show ?case
    by simp
next
  case (FAbs w B)
  from FAbs.prems(1) have "v \<notin> vars B"
    using vars_form.elims by auto
  then show ?case
  proof (cases "w \<in> fmdom' \<theta>")
    case True
    from FAbs.prems(2) have "\<forall>v' \<in> fmdom' (fmdrop w \<theta>). v \<notin> vars ((fmdrop w \<theta>) $$! v')"
      by auto
    with \<open>v \<notin> vars B\<close> have "v \<notin> vars (\<^bold>S (fmdrop w \<theta>) B)"
      by (fact FAbs.IH)
    with FAbs.prems(1) have "v \<notin> vars (FAbs w (\<^bold>S (fmdrop w \<theta>) B))"
      using surj_pair[of w] by fastforce
    moreover from True have "\<^bold>S \<theta> (FAbs w B) = FAbs w (\<^bold>S (fmdrop w \<theta>) B)"
      using surj_pair[of w] by fastforce
    ultimately show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using FAbs.IH and FAbs.prems and surj_pair[of w] by fastforce
  qed
qed

lemma substitution_free_absorption:
  assumes "\<theta> $$ v = None" and "v \<notin> free_vars B"
  shows "\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) B = \<^bold>S \<theta> B"
using assms proof (induction B arbitrary: \<theta>)
  case (FAbs w B)
  show ?case
  proof (cases "v \<noteq> w")
    case True
    with FAbs.prems(2) have "v \<notin> free_vars B"
      using surj_pair[of w] by fastforce
    then show ?thesis
    proof (cases "w \<in> fmdom' \<theta>")
      case True
      then have "\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S (fmdrop w ({v \<Zinj> A} ++\<^sub>f \<theta>)) B)"
        using surj_pair[of w] by fastforce
      also from \<open>v \<noteq> w\<close> and True have "\<dots> = FAbs w (\<^bold>S ({v \<Zinj> A} ++\<^sub>f fmdrop w \<theta>) B)"
        by (simp add: fmdrop_fmupd)
      also from FAbs.prems(1) and \<open>v \<notin> free_vars B\<close> have "\<dots> = FAbs w (\<^bold>S (fmdrop w \<theta>) B)"
        using FAbs.IH by simp
      also from True have "\<dots> = \<^bold>S \<theta> (FAbs w B)"
        using surj_pair[of w] by fastforce
      finally show ?thesis .
    next
      case False
      with FAbs.prems(1) have "\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) B)"
        using \<open>v \<noteq> w\<close> and surj_pair[of w] by fastforce
      also from FAbs.prems(1) and \<open>v \<notin> free_vars B\<close> have "\<dots> = FAbs w (\<^bold>S \<theta> B)"
        using FAbs.IH by simp
      also from False have "\<dots> = \<^bold>S \<theta> (FAbs w B)"
        using surj_pair[of w] by fastforce
      finally show ?thesis .
    qed
  next
    case False
    then have "fmdrop w ({v \<Zinj> A} ++\<^sub>f \<theta>) = fmdrop w \<theta>"
      by (simp add: fmdrop_fmupd_same)
    then show ?thesis
      using surj_pair[of w] by (metis (no_types, lifting) fmdrop_idle' substitute.simps(4))
  qed
qed fastforce+

lemma substitution_absorption:
  assumes "\<theta> $$ v = None" and "v \<notin> vars B"
  shows "\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) B = \<^bold>S \<theta> B"
  using assms by (meson free_vars_in_all_vars in_mono substitution_free_absorption)

lemma is_free_for_with_renaming_substitution:
  assumes "is_free_for A x B"
  and "y \<notin> vars B"
  and "x \<notin> fmdom' \<theta>"
  and "\<forall>v \<in> fmdom' \<theta>. y \<notin> vars (\<theta> $$! v)"
  and "\<forall>v \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v) v B"
  shows "is_free_for A y (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) B)"
using assms proof (induction B arbitrary: \<theta>)
  case (FVar w)
  then show ?case
  proof (cases "w = x")
    case True
    with FVar.prems(3) have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FVar w) = FVar y"
      using surj_pair[of w] by fastforce
    then show ?thesis
      using self_subform_is_at_top by fastforce
  next
    case False
    then show ?thesis
    proof (cases "w \<in> fmdom' \<theta>")
      case True
      from False have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FVar w) = \<^bold>S \<theta> (FVar w)"
        using substitution_absorption and surj_pair[of w] by force
      also from True have "\<dots> = \<theta> $$! w"
        using surj_pair[of w] by (metis fmdom'_notI option.case_eq_if substitute.simps(1))
      finally have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FVar w) = \<theta> $$! w" .
      moreover from True and FVar.prems(4) have "y \<notin> vars (\<theta> $$! w)"
        by blast
      ultimately show ?thesis
        using form_is_free_for_absent_var by presburger
    next
      case False
      with FVar.prems(3) and \<open>w \<noteq> x\<close> have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FVar w) = FVar w"
        using surj_pair[of w] by fastforce
      with FVar.prems(2) show ?thesis
        using form_is_free_for_absent_var by presburger
    qed
  qed
next
  case (FCon k)
  then show ?case
    using surj_pair[of k] by fastforce
next
  case (FApp C D)
  from FApp.prems(2) have "y \<notin> vars C" and "y \<notin> vars D"
    by simp_all
  from FApp.prems(1) have "is_free_for A x C" and "is_free_for A x D"
    using is_free_for_from_app by iprover+
  have "\<forall>v \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v) v C \<and> is_free_for (\<theta> $$! v) v D"
  proof (rule ballI)
    fix v
    assume "v \<in> fmdom' \<theta>"
    with FApp.prems(5) have "is_free_for (\<theta> $$! v) v (C \<sqdot> D)"
      by blast
    then show "is_free_for (\<theta> $$! v) v C \<and> is_free_for (\<theta> $$! v) v D"
      using is_free_for_from_app by iprover+
  qed
  then have
    *: "\<forall>v \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v) v C" and **: "\<forall>v \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v) v D"
    by auto
  have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (C \<sqdot> D) = (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) C) \<sqdot> (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) D)"
    by simp
  moreover have "is_free_for A y (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) C)"
    by (rule FApp.IH(1)[OF \<open>is_free_for A x C\<close> \<open>y \<notin> vars C\<close> FApp.prems(3,4) *])
  moreover have "is_free_for A y (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) D)"
    by (rule FApp.IH(2)[OF \<open>is_free_for A x D\<close> \<open>y \<notin> vars D\<close> FApp.prems(3,4) **])
  ultimately show ?case
    using is_free_for_in_app by simp
next
  case (FAbs w B)
  obtain x\<^sub>w and \<alpha>\<^sub>w where "w = (x\<^sub>w, \<alpha>\<^sub>w)"
    by fastforce
  from FAbs.prems(2) have "y \<notin> vars B"
    using vars_form.elims by auto
  then show ?case
  proof (cases "w = x")
    case True
    from True and \<open>x \<notin> fmdom' \<theta>\<close> have "w \<notin> fmdom' \<theta>" and "x \<notin> free_vars (FAbs w B)"
      using \<open>w = (x\<^sub>w, \<alpha>\<^sub>w)\<close> by fastforce+
    with True have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = \<^bold>S \<theta> (FAbs w B)"
      using substitution_free_absorption by blast
    also have "\<dots> = FAbs w (\<^bold>S \<theta> B)"
      using \<open>w = (x\<^sub>w, \<alpha>\<^sub>w)\<close> \<open>w \<notin> fmdom' \<theta>\<close> substitute.simps(4) by presburger
    finally have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S \<theta> B)" .
    moreover from \<open>\<^bold>S \<theta> (FAbs w B) = FAbs w (\<^bold>S \<theta> B)\<close> have "y \<notin> vars (FAbs w (\<^bold>S \<theta> B))"
      using absent_vars_substitution_preservation[OF FAbs.prems(2,4)] by simp
    ultimately show ?thesis
      using is_free_for_absent_var by (simp only:)
  next
    case False
    obtain v\<^sub>w and \<alpha>\<^sub>w where "w = (v\<^sub>w, \<alpha>\<^sub>w)"
      by fastforce
    from FAbs.prems(1) and \<open>w \<noteq> x\<close> and \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> have "is_free_for A x B"
      using is_free_for_from_abs by iprover
    then show ?thesis
    proof (cases "w \<in> fmdom' \<theta>")
      case True
      then have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S (fmdrop w ({x \<Zinj> FVar y} ++\<^sub>f \<theta>)) B)"
        using \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> by (simp add: fmdrop_idle')
      also from \<open>w \<noteq> x\<close> and True have "\<dots> = FAbs w (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f fmdrop w \<theta>) B)"
        by (simp add: fmdrop_fmupd)
      finally
      have *: "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f fmdrop w \<theta>) B)" .
      have "\<forall>v \<in> fmdom' (fmdrop w \<theta>). is_free_for (fmdrop w \<theta> $$! v) v B"
      proof
        fix v
        assume "v \<in> fmdom' (fmdrop w \<theta>)"
        with FAbs.prems(5) have "is_free_for (fmdrop w \<theta> $$! v) v (FAbs w B)"
          by auto
        moreover from \<open>v \<in> fmdom' (fmdrop w \<theta>)\<close> have "v \<noteq> w"
          by auto
        ultimately show "is_free_for (fmdrop w \<theta> $$! v) v B"
          unfolding \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> using is_free_for_from_abs by iprover
      qed
      moreover from FAbs.prems(3) have "x \<notin> fmdom' (fmdrop w \<theta>)"
        by simp
      moreover from FAbs.prems(4) have "\<forall>v \<in> fmdom' (fmdrop w \<theta>). y \<notin> vars (fmdrop w \<theta> $$! v)"
        by simp
      ultimately have "is_free_for A y (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f fmdrop w \<theta>) B)"
        using \<open>is_free_for A x B\<close> and \<open>y \<notin> vars B\<close> and FAbs.IH by iprover
      then show ?thesis
      proof (cases "x \<notin> free_vars B")
        case True
        have "y \<notin> vars (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B))"
        proof -
          have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f fmdrop w \<theta>) B)"
            using * .
          also from \<open>x \<notin> free_vars B\<close> and FAbs.prems(3) have "\<dots> = FAbs w (\<^bold>S (fmdrop w \<theta>) B)"
            using substitution_free_absorption by (simp add: fmdom'_notD)
          finally have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S (fmdrop w \<theta>) B)" .
          with FAbs.prems(2) and \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> and FAbs.prems(4) show ?thesis
            using absent_vars_substitution_preservation by auto
        qed
        then show ?thesis
          using is_free_for_absent_var by simp
      next
        case False
        have "w \<notin> free_vars A"
        proof (rule ccontr)
          assume "\<not> w \<notin> free_vars A"
          with False and \<open>w \<noteq> x\<close> have "\<not> is_free_for A x (FAbs w B)"
            using form_with_free_binder_not_free_for by simp
          with FAbs.prems(1) show False
            by contradiction
        qed
        with \<open>is_free_for A y (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f fmdrop w \<theta>) B)\<close>
        have "is_free_for A y (FAbs w (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f fmdrop w \<theta>) B))"
          unfolding \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> using is_free_for_to_abs by iprover
        with * show ?thesis
          by (simp only:)
      qed
    next
      case False
      have "\<forall>v \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v) v B"
      proof (rule ballI)
        fix v
        assume "v \<in> fmdom' \<theta>"
        with FAbs.prems(5) have "is_free_for (\<theta> $$! v) v (FAbs w B)"
          by blast
        moreover from \<open>v \<in> fmdom' \<theta>\<close> and \<open>w \<notin> fmdom' \<theta>\<close> have "v \<noteq> w"
          by blast
        ultimately show "is_free_for (\<theta> $$! v) v B"
          unfolding \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> using is_free_for_from_abs by iprover
      qed
      with \<open>is_free_for A x B\<close> and \<open>y \<notin> vars B\<close> and FAbs.prems(3,4)
      have "is_free_for A y (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) B)"
        using FAbs.IH by iprover
      then show ?thesis
      proof (cases "x \<notin> free_vars B")
        case True
        have "y \<notin> vars (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B))"
        proof -
          from False and \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> and \<open>w \<noteq> x\<close>
          have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) B)"
            by auto
          also from \<open>x \<notin> free_vars B\<close> and FAbs.prems(3) have "\<dots> = FAbs w (\<^bold>S \<theta> B)"
            using substitution_free_absorption by (simp add: fmdom'_notD)
          finally have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S \<theta> B)" .
          with FAbs.prems(2,4) and \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> show ?thesis
            using absent_vars_substitution_preservation by auto
        qed
        then show ?thesis
          using is_free_for_absent_var by simp
      next
        case False
        have "w \<notin> free_vars A"
        proof (rule ccontr)
          assume "\<not> w \<notin> free_vars A"
          with False and \<open>w \<noteq> x\<close> have "\<not> is_free_for A x (FAbs w B)"
            using form_with_free_binder_not_free_for by simp
          with FAbs.prems(1) show False
            by contradiction
        qed
        with \<open>is_free_for A y (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) B)\<close>
        have "is_free_for A y (FAbs w (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) B))"
          unfolding \<open>w = (v\<^sub>w, \<alpha>\<^sub>w)\<close> using is_free_for_to_abs by iprover
        moreover from \<open>w \<notin> fmdom' \<theta>\<close> and \<open>w \<noteq> x\<close> and FAbs.prems(3)
        have "\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) (FAbs w B) = FAbs w (\<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f \<theta>) B)"
          using surj_pair[of w] by fastforce
        ultimately show ?thesis
          by (simp only:)
      qed
    qed
  qed
qed

text \<open>
  The following lemma allows us to fuse a singleton substitution and a simultaneous substitution,
  as long as the variable of the former does not occur anywhere in the latter:
\<close>

lemma substitution_fusion:
  assumes "is_substitution \<theta>" and "is_substitution {v \<Zinj> A}"
  and "\<theta> $$ v = None" and "\<forall>v' \<in> fmdom' \<theta>. v \<notin> vars (\<theta> $$! v')"
  shows "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> B = \<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) B"
using assms(1,3,4) proof (induction B arbitrary: \<theta>)
  case (FVar v')
  then show ?case
  proof (cases "v' \<notin> fmdom' \<theta>")
    case True
    then show ?thesis
      using surj_pair[of v'] by fastforce
  next
    case False
    then obtain A' where "\<theta> $$ v' = Some A'"
      by (meson fmlookup_dom'_iff)
    with False and FVar.prems(3) have "v \<notin> vars A'"
      by fastforce
    then have "\<^bold>S {v \<Zinj> A} A' = A'"
      using free_var_singleton_substitution_neutrality and free_vars_in_all_vars by blast
    from \<open>\<theta> $$ v' = Some A'\<close> have "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (FVar v') = \<^bold>S {v \<Zinj> A} A'"
      using surj_pair[of v'] by fastforce
    also from \<open>\<^bold>S {v \<Zinj> A} A' = A'\<close> have "\<dots> = A'"
      by (simp only:)
    also from \<open>\<theta> $$ v' = Some A'\<close> and \<open>\<theta> $$ v = None\<close> have "\<dots> = \<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (FVar v')"
      using surj_pair[of v'] by fastforce
    finally show ?thesis .
  qed
next
  case (FCon k)
  then show ?case
    using surj_pair[of k] by fastforce
next
  case (FApp C D)
  have "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (C \<sqdot> D) = \<^bold>S {v \<Zinj> A} ((\<^bold>S \<theta> C) \<sqdot> (\<^bold>S \<theta> D))"
    by auto
  also have "\<dots> = (\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> C) \<sqdot> (\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> D)"
    by simp
  also from FApp.IH have "\<dots> = (\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) C) \<sqdot> (\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) D)"
    using FApp.prems(1,2,3) by presburger
  also have "\<dots> = \<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (C \<sqdot> D)"
    by simp
  finally show ?case .
next
  case (FAbs w C)
  obtain v\<^sub>w and \<alpha> where "w = (v\<^sub>w, \<alpha>)"
    by fastforce
  then show ?case
  proof (cases "v \<noteq> w")
    case True
    show ?thesis
    proof (cases "w \<notin> fmdom' \<theta>")
      case True
      then have "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (FAbs w C) = \<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S \<theta> C))"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      also from \<open>v \<noteq> w\<close> have "\<dots> = FAbs w (\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> C)"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      also from FAbs.IH have "\<dots> = FAbs w (\<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) C)"
        using FAbs.prems(1,2,3) by blast
      also from \<open>v \<noteq> w\<close> and True have "\<dots> = \<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (FAbs w C)"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      finally show ?thesis .
    next
      case False
      then have "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (FAbs w C) = \<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S (fmdrop w \<theta>) C))"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      also from \<open>v \<noteq> w\<close> have "\<dots> = FAbs w (\<^bold>S {v \<Zinj> A} \<^bold>S (fmdrop w \<theta>) C)"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      also have "\<dots> = FAbs w (\<^bold>S ({v \<Zinj> A} ++\<^sub>f fmdrop w \<theta>) C)"
      proof -
        from \<open>is_substitution \<theta>\<close> have "is_substitution (fmdrop w \<theta>)"
          by fastforce
        moreover from \<open>\<theta> $$ v = None\<close> have "(fmdrop w \<theta>) $$ v = None"
          by force
        moreover from FAbs.prems(3) have "\<forall>v' \<in> fmdom' (fmdrop w \<theta>). v \<notin> vars ((fmdrop w \<theta>) $$! v')"
          by force
        ultimately show ?thesis
          using FAbs.IH by blast
      qed
      also from \<open>v \<noteq> w\<close> have "\<dots> = \<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (FAbs w C)"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close> fmdrop_idle')
      finally show ?thesis .
    qed
  next
    case False
    then show ?thesis
    proof (cases "w \<notin> fmdom' \<theta>")
      case True
      then have "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (FAbs w C) = \<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S \<theta> C))"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      also from \<open>\<not> v \<noteq> w\<close> have "\<dots> = FAbs w (\<^bold>S \<theta> C)"
        using \<open>w = (v\<^sub>w, \<alpha>)\<close> and singleton_substitution_simps(4) by presburger
      also from \<open>\<not> v \<noteq> w\<close> and True have "\<dots> = FAbs w (\<^bold>S (fmdrop w ({v \<Zinj> A} ++\<^sub>f \<theta>)) C)"
        by (simp add: fmdrop_fmupd_same fmdrop_idle')
      also from \<open>\<not> v \<noteq> w\<close> have "\<dots> = \<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (FAbs w C)"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      finally show ?thesis .
    next
      case False
      then have "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (FAbs w C) = \<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S (fmdrop w \<theta>) C))"
        by (simp add: \<open>w = (v\<^sub>w, \<alpha>)\<close>)
      also from \<open>\<not> v \<noteq> w\<close> have "\<dots> = FAbs w (\<^bold>S (fmdrop w \<theta>) C)"
        using \<open>\<theta> $$ v = None\<close> and False by (simp add: fmdom'_notI)
      also from \<open>\<not> v \<noteq> w\<close> have "\<dots> = FAbs w (\<^bold>S (fmdrop w ({v \<Zinj> A} ++\<^sub>f \<theta>)) C)"
        by (simp add: fmdrop_fmupd_same)
      also from \<open>\<not> v \<noteq> w\<close> and False and \<open>\<theta> $$ v = None\<close> have "\<dots> = \<^bold>S ({v \<Zinj> A} ++\<^sub>f \<theta>) (FAbs w C)"
        by (simp add: fmdom'_notI)
      finally show ?thesis .
    qed
  qed
qed

lemma updated_substitution_is_substitution:
  assumes "v \<notin> fmdom' \<theta>" and "is_substitution (\<theta>(v \<Zinj> A))"
  shows "is_substitution \<theta>"
unfolding is_substitution_def proof (intro ballI)
  fix v' :: var
  obtain x and \<alpha> where "v' = (x, \<alpha>)"
    by fastforce
  assume "v' \<in> fmdom' \<theta>"
  with assms(2)[unfolded is_substitution_def] have "v' \<in> fmdom' (\<theta>(v \<Zinj> A))"
    by simp
  with assms(2)[unfolded is_substitution_def] have "\<theta>(v \<Zinj> A) $$! (x, \<alpha>) \<in> wffs\<^bsub>\<alpha>\<^esub>"
    using \<open>v' = (x, \<alpha>)\<close> by fastforce
  with assms(1) and \<open>v' \<in> fmdom' \<theta>\<close> and \<open>v' = (x, \<alpha>)\<close> have "\<theta> $$! (x, \<alpha>) \<in> wffs\<^bsub>\<alpha>\<^esub>"
     by (metis fmupd_lookup)
  then show "case v' of (x, \<alpha>) \<Rightarrow> \<theta> $$! (x, \<alpha>) \<in> wffs\<^bsub>\<alpha>\<^esub>"
    by (simp add: \<open>v' = (x, \<alpha>)\<close>)
qed

definition is_renaming_substitution where
  [iff]: "is_renaming_substitution \<theta> \<longleftrightarrow> is_substitution \<theta> \<and> fmpred (\<lambda>_ A. \<exists>v. A = FVar v) \<theta>"

text \<open>
  The following lemma proves that $
  \d{\textsf{S}}\;^{x^1_{\alpha_1}\;\dots\;x^n_{\alpha_n}}_{y^1_{\alpha_1}\;\dots\;y^n_{\alpha_n}} B
  =
  \d{\textsf{S}}\;^{x^1_{\alpha_1}}_{y^1_{\alpha_1}}\;\cdots\;
  \d{\textsf{S}}\;^{x^n_{\alpha_n}}_{y^n_{\alpha_n}} B$ provided that

    \<^item> $x^1_{\alpha_1}\;\dots\;x^n_{\alpha_n}$ are distinct variables

    \<^item> $y^1_{\alpha_1}\;\dots\;y^n_{\alpha_n}$ are distinct variables, distinct from
      $x^1_{\alpha_1}\;\dots\;x^n_{\alpha_n}$ and from all variables in \<open>B\<close> (i.e., they are fresh
      variables)

  In other words, simultaneously renaming distinct variables with fresh ones is equivalent to
  renaming each variable one at a time.
\<close>

lemma fresh_vars_substitution_unfolding:
  fixes ps :: "(var \<times> form) list"
  assumes "\<theta> = fmap_of_list ps" and "is_renaming_substitution \<theta>"
  and "distinct (map fst ps)" and "distinct (map snd ps)"
  and "vars (fmran' \<theta>) \<inter> (fmdom' \<theta> \<union> vars B) = {}"
  shows "\<^bold>S \<theta> B = foldr (\<lambda>(x, y) C. \<^bold>S {x \<Zinj> y} C) ps B"
using assms proof (induction ps arbitrary: \<theta>)
  case Nil
  then have "\<theta> = {$$}"
    by simp
  then have "\<^bold>S \<theta> B = B"
    using empty_substitution_neutrality by (simp only:)
  with Nil show ?case
    by simp
next
  case (Cons p ps)
  from Cons.prems(1,2) obtain x and y where "\<theta> $$ (fst p) = Some (FVar y)" and "p = (x, FVar y)"
    using surj_pair[of p] by fastforce
  let ?\<theta>' = "fmap_of_list ps"
  from Cons.prems(1) and \<open>p = (x, FVar y)\<close> have "\<theta> = fmupd x (FVar y) ?\<theta>'"
    by simp
  moreover from Cons.prems(3) and \<open>p = (x, FVar y)\<close> have "x \<notin> fmdom' ?\<theta>'"
    by simp
  ultimately have "\<theta> = {x \<Zinj> FVar y} ++\<^sub>f ?\<theta>'"
    using fmap_singleton_comm by fastforce
  with Cons.prems(2) and \<open>x \<notin> fmdom' ?\<theta>'\<close> have "is_renaming_substitution ?\<theta>'"
    unfolding is_renaming_substitution_def and \<open>\<theta> = fmupd x (FVar y) ?\<theta>'\<close>
    using updated_substitution_is_substitution by (metis fmdiff_fmupd fmdom'_notD fmpred_filter)
  from Cons.prems(2) and \<open>\<theta> = fmupd x (FVar y) ?\<theta>'\<close> have "is_renaming_substitution {x \<Zinj> FVar y}"
    by auto
  have "
    foldr (\<lambda>(x, y) C. \<^bold>S {x \<Zinj> y} C) (p # ps) B
    =
    \<^bold>S {x \<Zinj> FVar y} (foldr (\<lambda>(x, y) C. \<^bold>S {x \<Zinj> y} C) ps B)"
    by (simp add: \<open>p = (x, FVar y)\<close>)
  also have "\<dots> = \<^bold>S {x \<Zinj> FVar y} \<^bold>S ?\<theta>' B"
  proof -
    from Cons.prems(3,4) have "distinct (map fst ps)" and "distinct (map snd ps)"
      by fastforce+
    moreover have "vars (fmran' ?\<theta>') \<inter> (fmdom' ?\<theta>' \<union> vars B) = {}"
    proof -
      have "vars (fmran' \<theta>) = vars ({FVar y} \<union> fmran' ?\<theta>')"
        using \<open>\<theta> = fmupd x (FVar y) ?\<theta>'\<close> and \<open>x \<notin> fmdom' ?\<theta>'\<close> by (metis fmdom'_notD fmran'_fmupd)
      then have "vars (fmran' \<theta>) = {y} \<union> vars (fmran' ?\<theta>')"
        using singleton_form_set_vars by auto
      moreover have "fmdom' \<theta> = {x} \<union> fmdom' ?\<theta>'"
        by (simp add: \<open>\<theta> = {x \<Zinj> FVar y} ++\<^sub>f ?\<theta>'\<close>)
      ultimately show ?thesis
        using Cons.prems(5) by auto
    qed
    ultimately show ?thesis
      using Cons.IH and \<open>is_renaming_substitution ?\<theta>'\<close> by simp
  qed
  also have "\<dots> = \<^bold>S ({x \<Zinj> FVar y} ++\<^sub>f ?\<theta>') B"
  proof (rule substitution_fusion)
    show "is_substitution ?\<theta>'"
      using \<open>is_renaming_substitution ?\<theta>'\<close> by simp
    show "is_substitution {x \<Zinj> FVar y}"
      using \<open>is_renaming_substitution {x \<Zinj> FVar y}\<close> by simp
    show "?\<theta>' $$ x = None"
      using \<open>x \<notin> fmdom' ?\<theta>'\<close> by blast
    show "\<forall>v' \<in> fmdom' ?\<theta>'. x \<notin> vars (?\<theta>' $$! v')"
    proof -
      have "x \<in> fmdom' \<theta>"
        using \<open>\<theta> = {x \<Zinj> FVar y} ++\<^sub>f ?\<theta>'\<close> by simp
      then have "x \<notin> vars (fmran' \<theta>)"
        using Cons.prems(5) by blast
      moreover have "{?\<theta>' $$! v' | v'. v' \<in> fmdom' ?\<theta>'} \<subseteq> fmran' \<theta>"
        unfolding \<open>\<theta> = ?\<theta>'(x \<Zinj> FVar y)\<close> using \<open>?\<theta>' $$ x = None\<close>
        by (auto simp add: fmlookup_of_list fmlookup_dom'_iff fmran'I weak_map_of_SomeI)
      ultimately show ?thesis
        by force
    qed
  qed
  also from \<open>\<theta> = {x \<Zinj> FVar y} ++\<^sub>f ?\<theta>'\<close> have "\<dots> = \<^bold>S \<theta> B"
    by (simp only:)
  finally show ?case ..
qed

lemma free_vars_agreement_substitution_equality:
  assumes "fmdom' \<theta> = fmdom' \<theta>'"
  and "\<forall>v \<in> free_vars A \<inter> fmdom' \<theta>. \<theta> $$! v = \<theta>' $$! v"
  shows "\<^bold>S \<theta> A = \<^bold>S \<theta>' A"
using assms proof (induction A arbitrary: \<theta> \<theta>')
  case (FVar v)
  have "free_vars (FVar v) = {v}"
    using surj_pair[of v] by fastforce
  with FVar have "\<theta> $$! v = \<theta>' $$! v"
    by force
  with FVar.prems(1) show ?case
    using surj_pair[of v] by (metis fmdom'_notD fmdom'_notI option.collapse substitute.simps(1))
next
  case FCon
  then show ?case
    by (metis prod.exhaust_sel substitute.simps(2))
next
  case (FApp B C)
  have "\<^bold>S \<theta> (B \<sqdot> C) = (\<^bold>S \<theta> B) \<sqdot> (\<^bold>S \<theta> C)"
    by simp
  also have "\<dots> = (\<^bold>S \<theta>' B) \<sqdot> (\<^bold>S \<theta>' C)"
  proof -
    have "\<forall>v \<in> free_vars B \<inter> fmdom' \<theta>. \<theta> $$! v = \<theta>' $$! v"
    and "\<forall>v \<in> free_vars C \<inter> fmdom' \<theta>. \<theta> $$! v = \<theta>' $$! v"
      using FApp.prems(2) by auto
    with FApp.IH(1,2) and FApp.prems(1) show ?thesis
      by blast
  qed
  finally show ?case
    by simp
next
  case (FAbs w B)
  from FAbs.prems(1,2) have *: "\<forall>v \<in> free_vars B - {w} \<inter> fmdom' \<theta>. \<theta> $$! v = \<theta>' $$! v"
    using surj_pair[of w] by fastforce
  show ?case
  proof (cases "w \<in> fmdom' \<theta>")
    case True
    then have "\<^bold>S \<theta> (FAbs w B) = FAbs w (\<^bold>S (fmdrop w \<theta>) B)"
      using surj_pair[of w] by fastforce
    also have "\<dots> = FAbs w (\<^bold>S (fmdrop w \<theta>') B)"
    proof -
      from * have "\<forall>v \<in> free_vars B \<inter> fmdom' (fmdrop w \<theta>). (fmdrop w \<theta>) $$! v = (fmdrop w \<theta>') $$! v"
        by simp
      moreover have "fmdom' (fmdrop w \<theta>) = fmdom' (fmdrop w \<theta>')"
        by (simp add: FAbs.prems(1))
      ultimately show ?thesis
        using FAbs.IH by blast
    qed
    finally show ?thesis
      using FAbs.prems(1) and True and surj_pair[of w] by fastforce
  next
    case False
    then have "\<^bold>S \<theta> (FAbs w B) = FAbs w (\<^bold>S \<theta> B)"
      using surj_pair[of w] by fastforce
    also have "\<dots> = FAbs w (\<^bold>S \<theta>' B)"
    proof -
      from * have "\<forall>v \<in> free_vars B \<inter> fmdom' \<theta>. \<theta> $$! v = \<theta>' $$! v"
        using False by blast
      with FAbs.prems(1) show ?thesis
        using FAbs.IH by blast
    qed
    finally show ?thesis
      using FAbs.prems(1) and False and surj_pair[of w] by fastforce
  qed
qed

text \<open>
  The following lemma proves that $
  \d{\textsf{S}}\;^{x_\alpha}_{A_\alpha}\;
  \d{\textsf{S}}\;^{x^1_{\alpha_1}\;\dots\;x^n_{\alpha_n}}_{A^1_{\alpha_1}\;\dots\;A^n_{\alpha_n}} B
  =
  \d{\textsf{S}}\;{
  \begingroup \setlength\arraycolsep{2pt} \begin{matrix}
  \scriptstyle{x_\alpha} & \scriptstyle{x^1_{\alpha_1}} & \scriptstyle{\dots} & \scriptstyle{x^n_{\alpha_n}} \\
  \scriptstyle{A_\alpha} & \scriptstyle{\d{\small{\textsf{S}}}\;^{x_\alpha}_{A_\alpha} A^1_{\alpha_1}}
  & \scriptstyle{\dots} & \scriptstyle{\d{\small{\textsf{S}}}\;^{x_\alpha}_{A_\alpha} A^n_{\alpha_n}}
  \end{matrix} \endgroup} B$ provided that $x_\alpha$ is distinct from $x^1_{\alpha_1}, \dots, x^n_{\alpha_n}$
  and $A^i_{\alpha_i}$ is free for $x^i_{\alpha_i}$ in $B$:
\<close>

lemma substitution_consolidation:
  assumes "v \<notin> fmdom' \<theta>"
  and "\<forall>v' \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v') v' B"
  shows "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> B = \<^bold>S ({v \<Zinj> A} ++\<^sub>f fmmap (\<lambda>A'. \<^bold>S {v \<Zinj> A} A') \<theta>) B"
using assms proof (induction B arbitrary: \<theta>)
  case (FApp B C)
  have "\<forall>v' \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v') v' B \<and> is_free_for (\<theta> $$! v') v' C"
  proof
    fix v'
    assume "v' \<in> fmdom' \<theta>"
    with FApp.prems(2) have "is_free_for (\<theta> $$! v') v' (B \<sqdot> C)"
      by blast
    then show "is_free_for (\<theta> $$! v') v' B \<and> is_free_for (\<theta> $$! v') v' C"
      using is_free_for_from_app by iprover
  qed
  with FApp.IH and FApp.prems(1) show ?case
    by simp
next
  case (FAbs w B)
  let ?\<theta>' = "fmmap (\<lambda>A'. \<^bold>S {v \<Zinj> A} A') \<theta>"
  show ?case
  proof (cases "w \<in> fmdom' \<theta>")
    case True
    then have "w \<in> fmdom' ?\<theta>'"
      by simp
    with True and FAbs.prems have "v \<noteq> w"
      by blast
    from True have "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (FAbs w B) = \<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S (fmdrop w \<theta>) B))"
      using surj_pair[of w] by fastforce
    also from \<open>v \<noteq> w\<close> have "\<dots> = FAbs w (\<^bold>S {v \<Zinj> A} \<^bold>S (fmdrop w \<theta>) B)"
      using surj_pair[of w] by fastforce
    also have "\<dots> = FAbs w (\<^bold>S (fmdrop w ({v \<Zinj> A} ++\<^sub>f ?\<theta>')) B)"
    proof -
      obtain x\<^sub>w and \<alpha>\<^sub>w where "w = (x\<^sub>w, \<alpha>\<^sub>w)"
        by fastforce
      have "\<forall>v' \<in> fmdom' (fmdrop w \<theta>). is_free_for ((fmdrop w \<theta>) $$! v') v' B"
      proof
        fix v'
        assume "v' \<in> fmdom' (fmdrop w \<theta>)"
        with FAbs.prems(2) have "is_free_for (\<theta> $$! v') v' (FAbs w B)"
          by auto
        with \<open>w = (x\<^sub>w, \<alpha>\<^sub>w)\<close> and \<open>v' \<in> fmdom' (fmdrop w \<theta>)\<close>
        have "is_free_for (\<theta> $$! v') v' (\<lambda>x\<^sub>w\<^bsub>\<alpha>\<^sub>w\<^esub>. B)" and "v' \<noteq> (x\<^sub>w, \<alpha>\<^sub>w)"
          by auto
        then have "is_free_for (\<theta> $$! v') v' B"
          using is_free_for_from_abs by presburger
        with \<open>v' \<noteq> (x\<^sub>w, \<alpha>\<^sub>w)\<close> and \<open>w = (x\<^sub>w, \<alpha>\<^sub>w)\<close> show "is_free_for (fmdrop w \<theta> $$! v') v' B"
          by simp
      qed
      moreover have "v \<notin> fmdom' (fmdrop w \<theta>)"
        by (simp add: FAbs.prems(1))
      ultimately show ?thesis
        using FAbs.IH and \<open>v \<noteq> w\<close> by (simp add: fmdrop_fmupd)
    qed
    finally show ?thesis
      using \<open>w \<in> fmdom' ?\<theta>'\<close> and surj_pair[of w] by fastforce
  next
    case False
    then have "w \<notin> fmdom' ?\<theta>'"
      by simp
    from FAbs.prems have "v \<notin> fmdom' ?\<theta>'"
      by simp
    from False have *: "\<^bold>S {v \<Zinj> A} \<^bold>S \<theta> (FAbs w B) = \<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S \<theta> B))"
      using surj_pair[of w] by fastforce
    then show ?thesis
    proof (cases "v \<noteq> w")
      case True
      then have "\<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S \<theta> B)) = FAbs w (\<^bold>S {v \<Zinj> A} (\<^bold>S \<theta> B))"
        using surj_pair[of w] by fastforce
      also have "\<dots> = FAbs w (\<^bold>S ({v \<Zinj> A} ++\<^sub>f ?\<theta>') B)"
      proof -
        obtain x\<^sub>w and \<alpha>\<^sub>w where "w = (x\<^sub>w, \<alpha>\<^sub>w)"
          by fastforce
        have "\<forall>v' \<in> fmdom' \<theta>. is_free_for (\<theta> $$! v') v' B"
        proof
          fix v'
          assume "v' \<in> fmdom' \<theta>"
          with FAbs.prems(2) have "is_free_for (\<theta> $$! v') v' (FAbs w B)"
            by auto
          with \<open>w = (x\<^sub>w, \<alpha>\<^sub>w)\<close> and \<open>v' \<in> fmdom' \<theta>\<close> and False
          have "is_free_for (\<theta> $$! v') v' (\<lambda>x\<^sub>w\<^bsub>\<alpha>\<^sub>w\<^esub>. B)" and "v' \<noteq> (x\<^sub>w, \<alpha>\<^sub>w)"
            by fastforce+
          then have "is_free_for (\<theta> $$! v') v' B"
            using is_free_for_from_abs by presburger
          with \<open>v' \<noteq> (x\<^sub>w, \<alpha>\<^sub>w)\<close> and \<open>w = (x\<^sub>w, \<alpha>\<^sub>w)\<close> show "is_free_for (\<theta> $$! v') v' B"
            by simp
        qed
        with FAbs.IH show ?thesis
          using FAbs.prems(1) by blast
      qed
      finally show ?thesis
      proof -
        assume "
          \<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S \<theta> B)) = FAbs w (\<^bold>S ({v \<Zinj> A} ++\<^sub>f fmmap (substitute {v \<Zinj> A}) \<theta>) B)"
        moreover have "w \<notin> fmdom' ({v \<Zinj> A} ++\<^sub>f fmmap (substitute {v \<Zinj> A}) \<theta>)"
          using False and True by auto
        ultimately show ?thesis
          using * and surj_pair[of w] by fastforce
      qed
    next
      case False
      then have "v \<notin> free_vars (FAbs w (\<^bold>S \<theta> B))"
        using surj_pair[of w] by fastforce
      then have **: "\<^bold>S {v \<Zinj> A} (FAbs w (\<^bold>S \<theta> B)) = FAbs w (\<^bold>S \<theta> B)"
        using free_var_singleton_substitution_neutrality by blast
      also have "\<dots> = FAbs w (\<^bold>S ?\<theta>' B)"
      proof -
        {
          fix v'
          assume "v' \<in> fmdom' \<theta>"
          with FAbs.prems(1) have "v' \<noteq> v"
            by blast
          assume "v \<in> free_vars (\<theta> $$! v')" and "v' \<in> free_vars B"
          with \<open>v' \<noteq> v\<close> have "\<not> is_free_for (\<theta> $$! v') v' (FAbs v B)"
            using form_with_free_binder_not_free_for by blast
          with FAbs.prems(2) and \<open>v' \<in> fmdom' \<theta>\<close> and False have False
            by blast
        }
        then have "\<forall>v' \<in> fmdom' \<theta>. v \<notin> free_vars (\<theta> $$! v') \<or> v' \<notin> free_vars B"
          by blast
        then have "\<forall>v' \<in> fmdom' \<theta>. v' \<in> free_vars B \<longrightarrow> \<^bold>S {v \<Zinj> A} (\<theta> $$! v') = \<theta> $$! v'"
          using free_var_singleton_substitution_neutrality by blast
        then have "\<forall>v' \<in> free_vars B. \<theta> $$! v' = ?\<theta>' $$! v'"
          by (metis fmdom'_map fmdom'_notD fmdom'_notI fmlookup_map option.map_sel)
        then have "\<^bold>S \<theta> B = \<^bold>S ?\<theta>' B"
          using free_vars_agreement_substitution_equality by (metis IntD1 fmdom'_map)
        then show ?thesis
          by simp
      qed
      also from False and FAbs.prems(1) have "\<dots> = FAbs w (\<^bold>S (fmdrop w ({v \<Zinj> A} ++\<^sub>f ?\<theta>')) B)"
        by (simp add: fmdrop_fmupd_same fmdrop_idle')
      also from False have "\<dots> = \<^bold>S ({v \<Zinj> A} ++\<^sub>f ?\<theta>') (FAbs w B)"
        using surj_pair[of w] by fastforce
      finally show ?thesis
        using * and ** by (simp only:)
    qed
  qed
qed force+

lemma vars_range_substitution:
  assumes "is_substitution \<theta>"
  and "v \<notin> vars (fmran' \<theta>)"
  shows "v \<notin> vars (fmran' (fmdrop w \<theta>))"
using assms proof (induction \<theta>)
  case fmempty
  then show ?case
    by simp
next
  case (fmupd v' A \<theta>)
  from fmdom'_notI[OF fmupd.hyps] and fmupd.prems(1) have "is_substitution \<theta>"
    by (rule updated_substitution_is_substitution)
  moreover from fmupd.prems(2) and fmupd.hyps have "v \<notin> vars (fmran' \<theta>)"
    by simp
  ultimately have "v \<notin> vars (fmran' (fmdrop w \<theta>))"
    by (rule fmupd.IH)
  with fmupd.hyps and fmupd.prems(2) show ?case
    by (simp add: fmdrop_fmupd)
qed

lemma excluded_var_from_substitution:
  assumes "is_substitution \<theta>"
  and "v \<notin> fmdom' \<theta>"
  and "v \<notin> vars (fmran' \<theta>)"
  and "v \<notin> vars A"
  shows "v \<notin> vars (\<^bold>S \<theta> A)"
using assms proof (induction A arbitrary: \<theta>)
  case (FVar v')
  then show ?case
  proof (cases "v' \<in> fmdom' \<theta>")
    case True
    then have "\<theta> $$! v' \<in> fmran' \<theta>"
      by (simp add: fmlookup_dom'_iff fmran'I)
    with FVar(3) have "v \<notin> vars (\<theta> $$! v')"
      by simp
    with True show ?thesis
      using surj_pair[of v'] and fmdom'_notI by force
  next
    case False
    with FVar.prems(4) show ?thesis
      using surj_pair[of v'] by force
  qed
next
  case (FCon k)
  then show ?case
    using surj_pair[of k] by force
next
  case (FApp B C)
  then show ?case
    by auto
next
  case (FAbs w B)
  have "v \<notin> vars B" and "v \<noteq> w"
    using surj_pair[of w] and FAbs.prems(4) by fastforce+
  then show ?case
  proof (cases "w \<notin> fmdom' \<theta>")
    case True
    then have "\<^bold>S \<theta> (FAbs w B) = FAbs w (\<^bold>S \<theta> B)"
      using surj_pair[of w] by fastforce
    moreover from FAbs.IH have "v \<notin> vars (\<^bold>S \<theta> B)"
      using FAbs.prems(1-3) and \<open>v \<notin> vars B\<close> by blast
    ultimately show ?thesis
      using \<open>v \<noteq> w\<close> and surj_pair[of w] by fastforce
  next
    case False
    then have "\<^bold>S \<theta> (FAbs w B) = FAbs w (\<^bold>S (fmdrop w \<theta>) B)"
      using surj_pair[of w] by fastforce
    moreover have "v \<notin> vars (\<^bold>S (fmdrop w \<theta>) B)"
    proof -
      from FAbs.prems(1) have "is_substitution (fmdrop w \<theta>)"
        by fastforce
      moreover from FAbs.prems(2) have "v \<notin> fmdom' (fmdrop w \<theta>)"
        by simp
      moreover from FAbs.prems(1,3) have "v \<notin> vars (fmran' (fmdrop w \<theta>))"
        by (fact vars_range_substitution)
      ultimately show ?thesis
        using FAbs.IH and \<open>v \<notin> vars B\<close> by simp
    qed
    ultimately show ?thesis
      using \<open>v \<noteq> w\<close> and surj_pair[of w] by fastforce
  qed
qed

subsection \<open>Renaming of bound variables\<close>

fun rename_bound_var :: "var \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  "rename_bound_var v y (x\<^bsub>\<alpha>\<^esub>) = x\<^bsub>\<alpha>\<^esub>"
| "rename_bound_var v y (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>"
| "rename_bound_var v y (B \<sqdot> C) = rename_bound_var v y B \<sqdot> rename_bound_var v y C"
| "rename_bound_var v y (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) =
    (
      if (x, \<alpha>) = v then
        \<lambda>y\<^bsub>\<alpha>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} (rename_bound_var v y B)
      else
        \<lambda>x\<^bsub>\<alpha>\<^esub>. (rename_bound_var v y B)
    )"

lemma rename_bound_var_preserves_typing:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "rename_bound_var (y, \<gamma>) z A \<in> wffs\<^bsub>\<alpha>\<^esub>"
using assms proof (induction A)
  case (abs_is_wff \<beta> A \<delta> x)
  then show ?case
  proof (cases "(x, \<delta>) = (y, \<gamma>)")
    case True
    from abs_is_wff.IH have "\<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A) \<in> wffs\<^bsub>\<beta>\<^esub>"
      using substitution_preserves_typing by (simp add: wffs_of_type_intros(1))
    then have "\<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A) \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>"
      by blast
    with True show ?thesis
      by simp
  next
    case False
    from abs_is_wff.IH have "\<lambda>x\<^bsub>\<delta>\<^esub>. rename_bound_var (y, \<gamma>) z A \<in> wffs\<^bsub>\<delta>\<rightarrow>\<beta>\<^esub>"
      by blast
    with False show ?thesis
      by auto
  qed
qed auto

lemma old_bound_var_not_free_in_abs_after_renaming:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  and "(z, \<gamma>) \<notin> vars A"
  shows "(y, \<gamma>) \<notin> free_vars (rename_bound_var (y, \<gamma>) z (\<lambda>y\<^bsub>\<gamma>\<^esub>. A))"
  using assms and free_var_in_renaming_substitution by (induction A) auto

lemma rename_bound_var_free_vars:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  and "(z, \<gamma>) \<notin> vars A"
  shows "(z, \<gamma>) \<notin> free_vars (rename_bound_var (y, \<gamma>) z A)"
  using assms by (induction A) auto

lemma old_bound_var_not_free_after_renaming:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  and "(z, \<gamma>) \<notin> vars A"
  and "(y, \<gamma>) \<notin> free_vars A"
  shows "(y, \<gamma>) \<notin> free_vars (rename_bound_var (y, \<gamma>) z A)"
using assms proof induction
  case (abs_is_wff \<beta> A \<alpha> x)
  then show ?case
  proof (cases "(x, \<alpha>) = (y, \<gamma>)")
    case True
    with abs_is_wff.hyps and abs_is_wff.prems(2) show ?thesis
      using old_bound_var_not_free_in_abs_after_renaming by auto
  next
    case False
    with abs_is_wff.prems(2,3) and assms(2) show ?thesis
      using abs_is_wff.IH by force
  qed
qed fastforce+

lemma old_bound_var_not_ocurring_after_renaming:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  shows "\<not> occurs_at (y, \<gamma>) p (\<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A))"
using assms(1) proof (induction A arbitrary: p)
  case (var_is_wff \<alpha> x)
  from assms(2) show ?case
    using subform_size_decrease by (cases "(x, \<alpha>) = (y, \<gamma>)") fastforce+
next
  case (con_is_wff \<alpha> c)
  then show ?case
    using occurs_at_alt_def(2) by auto
next
  case (app_is_wff \<alpha> \<beta> A B)
  then show ?case
  proof (cases p)
    case (Cons d p')
    then show ?thesis
      by (cases d) (use app_is_wff.IH in auto)
  qed simp
next
  case (abs_is_wff \<beta> A \<alpha> x)
  then show ?case
  proof (cases p)
    case (Cons d p')
    then show ?thesis
    proof (cases d)
      case Left
      have *: "\<not> occurs_at (y, \<gamma>) p (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A))"
        for x and \<alpha>
        using Left and Cons and abs_is_wff.IH by simp
      then show ?thesis
      proof (cases "(x, \<alpha>) = (y, \<gamma>)")
        case True
        with assms(2) have "
          \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z (\<lambda>x\<^bsub>\<alpha>\<^esub>. A))
          =
          \<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A)"
          using free_var_in_renaming_substitution and free_var_singleton_substitution_neutrality
          by simp
        moreover have "\<not> occurs_at (y, \<gamma>) p (\<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A))"
          using Left and Cons and * by simp
        ultimately show ?thesis
          by simp
      next
        case False
        with assms(2) have "
          \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z (\<lambda>x\<^bsub>\<alpha>\<^esub>. A))
          =
          \<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A)"
          by simp
        moreover have "\<not> occurs_at (y, \<gamma>) p (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A))"
          using Left and Cons and * by simp
        ultimately show ?thesis
          by simp
      qed
    qed (simp add: Cons)
  qed simp
qed

text \<open>
  The following lemma states that the result of \<^term>\<open>rename_bound_var\<close> does not contain bound
  occurrences of the renamed variable:
\<close>

lemma rename_bound_var_not_bound_occurrences:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  and "(z, \<gamma>) \<notin> vars A"
  and "occurs_at (y, \<gamma>) p (rename_bound_var (y, \<gamma>) z A)"
  shows "\<not> in_scope_of_abs (z, \<gamma>) p (rename_bound_var (y, \<gamma>) z A)"
using assms(1,3,4) proof (induction arbitrary: p)
  case (var_is_wff \<alpha> x)
  then show ?case
    by (simp add: subforms_from_var(2))
next
  case (con_is_wff \<alpha> c)
  then show ?case
    using occurs_at_alt_def(2) by auto
next
  case (app_is_wff \<alpha> \<beta> B C)
  from app_is_wff.prems(1) have "(z, \<gamma>) \<notin> vars B" and "(z, \<gamma>) \<notin> vars C"
    by simp_all
  from app_is_wff.prems(2)
  have "occurs_at (y, \<gamma>) p (rename_bound_var (y, \<gamma>) z B \<sqdot> rename_bound_var (y, \<gamma>) z C)"
    by simp
  then consider
    (a) "\<exists>p'. p = \<guillemotleft> # p' \<and> occurs_at (y, \<gamma>) p' (rename_bound_var (y, \<gamma>) z B)"
  | (b) "\<exists>p'. p = \<guillemotright> # p' \<and> occurs_at (y, \<gamma>) p' (rename_bound_var (y, \<gamma>) z C)"
    using subforms_from_app by force
  then show ?case
  proof cases
    case a
    then obtain p' where "p = \<guillemotleft> # p'" and "occurs_at (y, \<gamma>) p' (rename_bound_var (y, \<gamma>) z B)"
      by blast
    then have "\<not> in_scope_of_abs (z, \<gamma>) p' (rename_bound_var (y, \<gamma>) z B)"
      using app_is_wff.IH(1)[OF \<open>(z, \<gamma>) \<notin> vars B\<close>] by blast
    then have "\<not> in_scope_of_abs (z, \<gamma>) p (rename_bound_var (y, \<gamma>) z (B \<sqdot> C))" for C
      using \<open>p = \<guillemotleft> # p'\<close> and in_scope_of_abs_in_left_app by simp
    then show ?thesis
      by blast
  next
    case b
    then obtain p' where "p = \<guillemotright> # p'" and "occurs_at (y, \<gamma>) p' (rename_bound_var (y, \<gamma>) z C)"
      by blast
    then have "\<not> in_scope_of_abs (z, \<gamma>) p' (rename_bound_var (y, \<gamma>) z C)"
      using app_is_wff.IH(2)[OF \<open>(z, \<gamma>) \<notin> vars C\<close>] by blast
    then have "\<not> in_scope_of_abs (z, \<gamma>) p (rename_bound_var (y, \<gamma>) z (B \<sqdot> C))" for B
      using \<open>p = \<guillemotright> # p'\<close> and in_scope_of_abs_in_right_app by simp
    then show ?thesis
      by blast
  qed
next
  case (abs_is_wff \<beta> A \<alpha> x)
  from abs_is_wff.prems(1) have "(z, \<gamma>) \<notin> vars A" and "(z, \<gamma>) \<noteq> (x, \<alpha>)"
    by fastforce+
  then show ?case
  proof (cases "(y, \<gamma>) = (x, \<alpha>)")
    case True
    then have "occurs_at (y, \<gamma>) p (\<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A))"
      using abs_is_wff.prems(2) by simp
    moreover have "\<not> occurs_at (y, \<gamma>) p (\<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A))"
      using old_bound_var_not_ocurring_after_renaming[OF abs_is_wff.hyps assms(2)] and subforms_from_abs
      by fastforce
    ultimately show ?thesis
      by contradiction
  next
    case False
    then have *: "rename_bound_var (y, \<gamma>) z (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. rename_bound_var (y, \<gamma>) z A"
      by auto
    with abs_is_wff.prems(2) have "occurs_at (y, \<gamma>) p (\<lambda>x\<^bsub>\<alpha>\<^esub>. rename_bound_var (y, \<gamma>) z A)"
      by auto
    then obtain p' where "p = \<guillemotleft> # p'" and "occurs_at (y, \<gamma>) p' (rename_bound_var (y, \<gamma>) z A)"
      using subforms_from_abs by fastforce
    then have "\<not> in_scope_of_abs (z, \<gamma>) p' (rename_bound_var (y, \<gamma>) z A)"
      using abs_is_wff.IH[OF \<open>(z, \<gamma>) \<notin> vars A\<close>] by blast
    then have "\<not> in_scope_of_abs (z, \<gamma>) (\<guillemotleft> # p') (\<lambda>x\<^bsub>\<alpha>\<^esub>. rename_bound_var (y, \<gamma>) z A)"
      using \<open>p = \<guillemotleft> # p'\<close> and in_scope_of_abs_in_abs and \<open>(z, \<gamma>) \<noteq> (x, \<alpha>)\<close> by auto
    then show ?thesis
      using * and \<open>p = \<guillemotleft> # p'\<close> by simp
  qed
qed

lemma is_free_for_in_rename_bound_var:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  and "(z, \<gamma>) \<notin> vars A"
  shows "is_free_for (z\<^bsub>\<gamma>\<^esub>) (y, \<gamma>) (rename_bound_var (y, \<gamma>) z A)"
proof (rule ccontr)
  assume "\<not> is_free_for (z\<^bsub>\<gamma>\<^esub>) (y, \<gamma>) (rename_bound_var (y, \<gamma>) z A)"
  then obtain p
    where "is_free_at (y, \<gamma>) p (rename_bound_var (y, \<gamma>) z A)"
    and "in_scope_of_abs (z, \<gamma>) p (rename_bound_var (y, \<gamma>) z A)"
    by force
  then show False
    using rename_bound_var_not_bound_occurrences[OF assms] by fastforce
qed

lemma renaming_substitution_preserves_bound_vars:
  shows "bound_vars (\<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} A) = bound_vars A"
proof (induction A)
  case (FAbs v A)
  then show ?case
    using singleton_substitution_simps(4) and surj_pair[of v]
    by (cases "v = (y, \<gamma>)") (presburger, force)
qed force+

lemma rename_bound_var_bound_vars:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  shows "(y, \<gamma>) \<notin> bound_vars (rename_bound_var (y, \<gamma>) z A)"
  using assms and renaming_substitution_preserves_bound_vars by (induction A) auto

lemma old_var_not_free_not_occurring_after_rename:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  and "(y, \<gamma>) \<notin> free_vars A"
  and "(z, \<gamma>) \<notin> vars A"
  shows "(y, \<gamma>) \<notin> vars (rename_bound_var (y, \<gamma>) z A)"
  using assms and rename_bound_var_bound_vars[OF assms(1,2)]
  and old_bound_var_not_free_after_renaming and vars_is_free_and_bound_vars by blast

end
