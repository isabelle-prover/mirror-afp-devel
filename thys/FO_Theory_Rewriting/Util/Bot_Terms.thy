theory Bot_Terms
  imports Utils
begin

subsection \<open>Bottom terms\<close>

datatype 'f bot_term = Bot | BFun 'f (args: "'f bot_term list")

fun term_to_bot_term :: "('f, 'v) term \<Rightarrow> 'f bot_term"  ("_\<^sup>\<bottom>" [80] 80) where
  "(Var _)\<^sup>\<bottom> = Bot"
| "(Fun f ts)\<^sup>\<bottom> = BFun f (map term_to_bot_term ts)"

fun root_bot where
  "root_bot Bot = None" |
  "root_bot (BFun f ts) = Some (f, length ts)"

fun funas_bot_term where
  "funas_bot_term Bot = {}"
| "funas_bot_term (BFun f ss) = {(f, length ss)} \<union> (\<Union> (funas_bot_term ` set ss))"

lemma finite_funas_bot_term:
  "finite (funas_bot_term t)"
  by (induct t) auto

lemma funas_bot_term_funas_term:
  "funas_bot_term (t\<^sup>\<bottom>) = funas_term t"
  by (induct t) auto

lemma term_to_bot_term_root_bot [simp]:
  "root_bot (t\<^sup>\<bottom>) = root t"
  by (induct t) auto

lemma term_to_bot_term_root_bot_comp [simp]:
  "root_bot \<circ> term_to_bot_term = root"
  using term_to_bot_term_root_bot by force

inductive_set mergeP where
  base_l [simp]: "(Bot, t) \<in> mergeP"
| base_r [simp]: "(t, Bot) \<in> mergeP"
| step [intro]: "length ss = length ts \<Longrightarrow> (\<forall> i < length ts. (ss ! i, ts ! i) \<in> mergeP) \<Longrightarrow>
    (BFun f ss, BFun f ts) \<in> mergeP"

lemma merge_refl:
  "(s, s) \<in> mergeP"
  by (induct s) auto

lemma merge_symmetric:
  assumes "(s, t) \<in> mergeP"
  shows "(t, s) \<in> mergeP"
  using assms by induct auto

fun merge_terms :: "'f bot_term \<Rightarrow> 'f bot_term \<Rightarrow> 'f bot_term"  (infixr "\<up>" 67) where
  "Bot \<up> s = s"
| "s \<up> Bot = s"
| "(BFun f ss) \<up> (BFun g ts) = (if f = g \<and> length ss = length ts
     then BFun f (map (case_prod (\<up>)) (zip ss ts))
     else undefined)"

lemma merge_terms_bot_rhs[simp]:
  "s \<up> Bot = s" by (cases s) auto

lemma merge_terms_idem: "s \<up> s = s"
  by (induct s) (auto simp add: map_nth_eq_conv)

lemma merge_terms_assoc [ac_simps]:
  assumes "(s, t) \<in> mergeP" and "(t, u) \<in> mergeP"
  shows "(s \<up> t) \<up> u = s \<up> t \<up> u"
  using assms by (induct s t arbitrary: u) (auto elim!: mergeP.cases intro!: nth_equalityI)

lemma merge_terms_commutative [ac_simps]:
  shows "s \<up> t = t \<up> s"
  by (induct s t rule: merge_terms.induct)
   (fastforce simp: in_set_conv_nth intro!: nth_equalityI)+

lemma merge_dist:
  assumes "(s, t \<up> u) \<in> mergeP" and "(t, u) \<in> mergeP"
  shows "(s, t) \<in> mergeP" using assms
  by (induct t arbitrary: s u) (auto elim!: mergeP.cases, metis mergeP.step nth_mem)

lemma megeP_ass:
  "(s, t \<up> u) \<in> mergeP \<Longrightarrow> (t, u) \<in> mergeP \<Longrightarrow> (s \<up> t, u) \<in> mergeP"
  by (induct t arbitrary: s u) (auto simp: mergeP.step elim!: mergeP.cases)

inductive_set bless_eq where
  base_l [simp]: "(Bot, t) \<in> bless_eq"
| step [intro]: "length ss = length ts \<Longrightarrow> (\<forall> i < length ts. (ss ! i, ts ! i) \<in> bless_eq) \<Longrightarrow>
  (BFun f ss, BFun f ts) \<in> bless_eq"

text \<open>Infix syntax.\<close>
abbreviation "bless_eq_pred s t \<equiv> (s, t) \<in> bless_eq"
notation
  bless_eq ("{\<le>\<^sub>b}") and
  bless_eq_pred ("(_/ \<le>\<^sub>b _)" [56, 56] 55)

lemma BFun_leq_Bot_False [simp]:
  "BFun f ts \<le>\<^sub>b Bot \<longleftrightarrow> False"
  using bless_eq.cases by auto

lemma BFun_lesseqE [elim]:
  assumes "BFun f ts \<le>\<^sub>b t"
  obtains us where "length ts = length us" "t = BFun f us"
  using assms bless_eq.cases by blast

lemma bless_eq_refl: "s \<le>\<^sub>b s"
  by (induct s) auto

lemma bless_eq_trans [trans]:
  assumes "s \<le>\<^sub>b t" and "t \<le>\<^sub>b u"
  shows "s \<le>\<^sub>b u" using assms
proof (induct arbitrary: u)
  case (step ss ts f)
  from step(3) obtain us where [simp]: "u = BFun f us" "length ts = length us" by auto
  from step(3, 1, 2) have "i < length ss \<Longrightarrow> ss ! i \<le>\<^sub>b us ! i" for i
    by (cases rule: bless_eq.cases) auto
  then show ?case using step(1) by auto
qed auto

lemma bless_eq_anti_sym:
  "s \<le>\<^sub>b t \<Longrightarrow> t \<le>\<^sub>b s \<Longrightarrow> s = t"
  by (induct rule: bless_eq.induct) (auto elim!: bless_eq.cases intro: nth_equalityI)

lemma bless_eq_mergeP:
  "s \<le>\<^sub>b t \<Longrightarrow> (s, t) \<in> mergeP"
  by (induct s arbitrary: t) (auto elim!: bless_eq.cases)

lemma merge_bot_args_bless_eq_merge:
  assumes "(s, t) \<in> mergeP"
  shows "s \<le>\<^sub>b s \<up> t" using assms
  by (induct s arbitrary: t) (auto simp: bless_eq_refl elim!: mergeP.cases intro!: step)

lemma bless_eq_closued_under_merge:
  assumes "(s, t) \<in> mergeP" "(u, v) \<in> mergeP" "s \<le>\<^sub>b u" "t \<le>\<^sub>b v"
  shows "s \<up> t \<le>\<^sub>b u \<up> v" using assms(3, 4, 1, 2)
proof (induct arbitrary: t v)
  case (base_l t)
  then show ?case using bless_eq_trans merge_bot_args_bless_eq_merge
    by (metis merge_symmetric merge_terms.simps(1) merge_terms_commutative) 
next
  case (step ss ts f)
  then show ?case apply (auto elim!: mergeP.cases intro!: bless_eq.step)
    using bless_eq_trans merge_bot_args_bless_eq_merge apply blast
    by (metis bless_eq.cases bot_term.distinct(1) bot_term.sel(2))
qed

lemma bless_eq_closued_under_supremum:
  assumes "s \<le>\<^sub>b u" "t \<le>\<^sub>b u"
  shows "s \<up> t \<le>\<^sub>b u" using assms
  by (induct arbitrary: t) (auto elim!: bless_eq.cases intro!: bless_eq.step)

lemma linear_term_comb_subst:
  assumes "linear_term (Fun f ss)"
    and "length ss = length ts"
    and "\<And> i. i < length ts \<Longrightarrow> ss ! i \<cdot> \<sigma> i = ts ! i"
  shows "\<exists> \<sigma>. Fun f ss \<cdot> \<sigma> = Fun f ts"
  using assms subst_merge[of ss "\<sigma>"]
  apply auto apply (rule_tac x = \<sigma>' in exI)
  apply (intro nth_equalityI) apply auto
  by (metis term_subst_eq)

lemma bless_eq_to_instance:
  assumes "s\<^sup>\<bottom> \<le>\<^sub>b t\<^sup>\<bottom>" and "linear_term s"
  shows "\<exists> \<sigma>. s \<cdot> \<sigma> = t" using assms
proof (induct s arbitrary: t)
  case (Fun f ts)
  from Fun(2) obtain us where [simp]: "t = Fun f us" "length ts = length us" by (cases t) auto 
  have "i < length ts \<Longrightarrow> \<exists>\<sigma>. ts ! i \<cdot> \<sigma> = us ! i" for i
    using Fun(2, 3) Fun(1)[OF nth_mem, of i "us ! i" for i]
    by (auto elim: bless_eq.cases)
  then show ?case using Ex_list_of_length_P[of "length ts" "\<lambda> \<sigma> i. ts ! i \<cdot> \<sigma> = us ! i"]
    using linear_term_comb_subst[OF Fun(3)] by auto
qed auto

lemma instance_to_bless_eq:
  assumes "s \<cdot> \<sigma> = t"
  shows "s\<^sup>\<bottom> \<le>\<^sub>b t\<^sup>\<bottom>" using assms
proof (induct s arbitrary: t)
  case (Fun f ts) then show ?case
    by (cases t) auto
qed auto

end