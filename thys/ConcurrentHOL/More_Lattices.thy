(*<*)
theory More_Lattices
imports
  HOL_Basis
begin

(*>*)
section\<open> More lattice\label{sec:more_lattices}  \<close>

lemma (in semilattice_sup) sup_iff_le:
  shows "x \<squnion> y = y \<longleftrightarrow> x \<le> y"
    and "y \<squnion> x = y \<longleftrightarrow> x \<le> y"
by (simp_all add: le_iff_sup ac_simps)

lemma (in semilattice_inf) inf_iff_le:
  shows "x \<sqinter> y = x \<longleftrightarrow> x \<le> y"
    and "y \<sqinter> x = x \<longleftrightarrow> x \<le> y"
by (simp_all add: le_iff_inf ac_simps)

lemma if_sup_distr:
  fixes t e :: "_::semilattice_sup"
  shows if_sup_distrL: "(if b then t\<^sub>1 \<squnion> t\<^sub>2 else e) = (if b then t\<^sub>1 else e) \<squnion> (if b then t\<^sub>2 else e)"
    and if_sup_distrR: "(if b then t else e\<^sub>1 \<squnion> e\<^sub>2) = (if b then t else e\<^sub>1) \<squnion> (if b then t else e\<^sub>2)"
by (simp_all split: if_splits)

lemma INF_bot:
  assumes "F i = (\<bottom>::_::complete_lattice)"
  assumes "i \<in> X"
  shows "(\<Sqinter>i\<in>X. F i) = \<bottom>"
using assms by (metis INF_lower bot.extremum_uniqueI)

lemma mcont_fun_app_const[cont_intro]:
  shows "mcont Sup (\<le>) Sup (\<le>) (\<lambda>f. f c)"
by (fastforce intro!: mcontI monotoneI contI simp: le_fun_def)

declare mcont_applyI[cont_intro]

lemma INF_rename_bij:
  assumes "bij_betw \<pi> X Y"
  shows "(\<Sqinter>y\<in>Y. F Y y) = (\<Sqinter>x\<in>X. F (\<pi> ` X) (\<pi> x))"
using assms by (metis bij_betw_imp_surj_on image_image)

lemma Inf_rename_surj:
  assumes "surj \<pi>"
  shows "(\<Sqinter>x. F x) = (\<Sqinter>x. F (\<pi> x))"
using assms by (metis image_image)

lemma INF_unwind_index:
  fixes A :: "_\<Rightarrow>_:: complete_lattice"
  assumes "i \<in> I"
  shows "(\<Sqinter>x\<in>I. A x) = A i \<sqinter> (\<Sqinter>x\<in>I - {i}. A x)"
by (metis INF_insert assms insert_Diff)

lemma Sup_fst:
  shows "(\<Squnion>x\<in>X. P (fst x)) = (\<Squnion>x\<in>fst ` X. P x)"
by (simp add: image_image)

setup \<open>Sign.mandatory_path "order"\<close>

lemma assms_cong: \<comment>\<open> simplify assumptions only \<close>
  assumes "x = x'"
  shows "x \<le> y \<longleftrightarrow> x' \<le> y"
using assms by simp

lemma concl_cong: \<comment>\<open> simplify conclusions only \<close>
  assumes "y = y'"
  shows "x \<le> y \<longleftrightarrow> x \<le> y'"
using assms by simp

lemma "subgoal": \<comment>\<open> cut for lattice logics \<close>
  fixes P :: "_::semilattice_inf"
  assumes "P \<le> Q"
  assumes "P \<sqinter> Q \<le> R"
  shows "P \<le> R"
using assms by (simp add: inf_absorb1)

setup \<open>Sign.parent_path\<close>

paragraph\<open> Logical rules ala HOL \<close>

lemmas SupI = Sup_upper
lemmas rev_SUPI = SUP_upper2[of x A b f for x A b f]
lemmas SUPI = rev_SUPI[rotated]

lemmas SUPE = SUP_least[where u=z for z]
lemmas SupE = Sup_least

lemmas INFI = INF_greatest
lemmas InfI = Inf_greatest
lemmas infI = semilattice_inf_class.le_infI

lemma InfE:
  fixes R::"_::complete_lattice"
  assumes "P x \<le> R"
  shows "(\<Sqinter>x. P x) \<le> R"
using assms by (meson Inf_lower2 rangeI)

lemma INFE:
  fixes R::"'a::complete_lattice"
  assumes "P x \<le> R"
  assumes "x \<in> A"
  shows "\<Sqinter>(P ` A) \<le> R"
using assms by (metis INF_lower2)

lemmas rev_INFE = INFE[rotated]

lemma Inf_inf_distrib:
  fixes P::"_::complete_lattice"
  shows "(\<Sqinter>x. P x \<sqinter> Q x) = (\<Sqinter>x. P x) \<sqinter> (\<Sqinter>x. Q x)"
by (simp add: INF_inf_distrib)

lemma Sup_sup_distrib:
  fixes P::"_::complete_lattice"
  shows "(\<Squnion>x. P x \<squnion> Q x) = (\<Squnion>x. P x) \<squnion> (\<Squnion>x. Q x)"
by (simp add: SUP_sup_distrib)

lemma Inf_inf:
  fixes Q :: "_::complete_lattice"
  shows "(\<Sqinter>x. P x \<sqinter> Q) = (\<Sqinter>x. P x) \<sqinter> Q"
by (simp add: INF_inf_const2)

lemma inf_Inf:
  fixes P :: "_::complete_lattice"
  shows "(\<Sqinter>x. P \<sqinter> Q x) = P \<sqinter> (\<Sqinter>x. Q x)"
by (simp add: INF_inf_const1)

lemma SUP_sup:
  fixes Q :: "_::complete_lattice"
  assumes "X \<noteq> {}"
  shows "(\<Squnion>x\<in>X. P x \<squnion> Q) = (\<Squnion>x\<in>X. P x) \<squnion> Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" by (simp add: SUP_le_iff SupI le_supI1)
  from assms show "?rhs \<le> ?lhs" by (auto simp add: SUP_le_iff intro: SUPI le_supI1)
qed

lemma sup_SUP:
  fixes P :: "_::complete_lattice"
  assumes "X \<noteq> {}"
  shows "(\<Squnion>x\<in>X. P \<squnion> Q x) = P \<squnion> (\<Squnion>x\<in>X. Q x)"
using SUP_sup[OF assms, where P=Q and Q=P] by (simp add: ac_simps)


subsection\<open> Boolean lattices and implication\label{sec:more_lattices-boolean_implication} \<close>

lemma
  shows minus_Not[simp]: "- Not = id"
    and minus_id[simp]: "- id = Not"
by fastforce+

definition boolean_implication :: "'a::boolean_algebra \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>\<^bold>\<longrightarrow>\<^sub>B\<close> 60) where
  "x \<^bold>\<longrightarrow>\<^sub>B y = -x \<squnion> y"

definition boolean_eq :: "'a::boolean_algebra \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>\<^bold>\<longleftrightarrow>\<^sub>B\<close> 60) where
  "x \<^bold>\<longleftrightarrow>\<^sub>B y = x \<^bold>\<longrightarrow>\<^sub>B y \<sqinter> y \<^bold>\<longrightarrow>\<^sub>B x"

setup \<open>Sign.mandatory_path "boolean_implication"\<close>

lemma bool_alt_def[simp]:
  shows "P \<^bold>\<longrightarrow>\<^sub>B Q = (P \<longrightarrow> Q)"
by (auto simp: boolean_implication_def)

lemma pred__alt_def[simp]:
  shows "(P \<^bold>\<longrightarrow>\<^sub>B Q) x = (P x \<^bold>\<longrightarrow>\<^sub>B Q x)"
by (auto simp: boolean_implication_def)

lemma set_alt_def:
  shows "P \<^bold>\<longrightarrow>\<^sub>B Q = {x. x \<in> P \<longrightarrow> x \<in> Q}"
by (auto simp: boolean_implication_def)

lemma member:
  shows "x \<in> P \<^bold>\<longrightarrow>\<^sub>B Q \<longleftrightarrow> x \<in> P \<longrightarrow> x \<in> Q"
by (simp add: boolean_implication.set_alt_def)

lemmas setI = iffD2[OF boolean_implication.member, rule_format]

lemma simps[simp]:
  shows
    "\<top> \<^bold>\<longrightarrow>\<^sub>B P = P"
    "\<bottom> \<^bold>\<longrightarrow>\<^sub>B P = \<top>"
    "P \<^bold>\<longrightarrow>\<^sub>B \<top> = \<top>"
    "P \<^bold>\<longrightarrow>\<^sub>B P = \<top>"
    "P \<^bold>\<longrightarrow>\<^sub>B \<bottom> = -P"
    "P \<^bold>\<longrightarrow>\<^sub>B -P = -P"
by (simp_all add: boolean_implication_def shunt1)

lemma Inf_simps[simp]: \<comment>\<open>Miniscoping: pushing in universal quantifiers.\<close>
  shows
    "\<And>P (Q::_::complete_boolean_algebra).    (\<Sqinter>x. P x \<^bold>\<longrightarrow>\<^sub>B Q) = ((\<Squnion>x. P x) \<^bold>\<longrightarrow>\<^sub>B Q)"
    "\<And>P (Q::_::complete_boolean_algebra).    (\<Sqinter>x\<in>X. P x \<^bold>\<longrightarrow>\<^sub>B Q) = ((\<Squnion>x\<in>X. P x) \<^bold>\<longrightarrow>\<^sub>B Q)"
    "\<And>P (Q::_\<Rightarrow>_::complete_boolean_algebra). (\<Sqinter>x. P \<^bold>\<longrightarrow>\<^sub>B Q x) = (P \<^bold>\<longrightarrow>\<^sub>B (\<Sqinter>x. Q x))"
    "\<And>P (Q::_\<Rightarrow>_::complete_boolean_algebra). (\<Sqinter>x\<in>X. P \<^bold>\<longrightarrow>\<^sub>B Q x) = (P \<^bold>\<longrightarrow>\<^sub>B (\<Sqinter>x\<in>X. Q x))"
by (simp_all add: boolean_implication_def INF_sup sup_INF uminus_SUP)

lemma mono:
  assumes "x' \<le> x"
  assumes "y \<le> y'"
  shows "x \<^bold>\<longrightarrow>\<^sub>B y \<le> x' \<^bold>\<longrightarrow>\<^sub>B y'"
using assms by (simp add: boolean_implication_def sup.coboundedI1 sup.coboundedI2)

lemma strengthen[strg]:
  assumes "st_ord (\<not> F) X X'"
  assumes "st_ord F Y Y'"
  shows "st_ord F (X \<^bold>\<longrightarrow>\<^sub>B Y) (X' \<^bold>\<longrightarrow>\<^sub>B Y')"
using assms by (cases F) (use boolean_implication.mono in auto)

lemma eq_conv:
  shows "(P = Q) \<longleftrightarrow> (P \<^bold>\<longrightarrow>\<^sub>B Q) \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>B P) = \<top>"
unfolding boolean_implication_def order.eq_iff by (simp add: sup_shunt top.extremum_unique)

lemma uminus_imp[simp]:
  shows "-(P \<^bold>\<longrightarrow>\<^sub>B Q) = P \<sqinter> -Q"
by (simp add: boolean_implication_def)

lemma cases_simp[simp]:
  shows "(P \<^bold>\<longrightarrow>\<^sub>B Q) \<sqinter> (-P \<^bold>\<longrightarrow>\<^sub>B Q) = Q"
by (simp add: boolean_implication_def order.eq_iff boolean_algebra.disj_conj_distrib2 shunt1)

lemma conv_sup:
  shows "(P \<^bold>\<longrightarrow>\<^sub>B Q) = -P \<squnion> Q"
by (rule boolean_implication_def)

lemma infL:
  shows "P \<sqinter> Q \<^bold>\<longrightarrow>\<^sub>B R = P \<^bold>\<longrightarrow>\<^sub>B Q \<^bold>\<longrightarrow>\<^sub>B R"
by (simp add: boolean_implication_def sup_assoc)

lemmas uncurry = boolean_implication.infL[symmetric]

lemma shunt1:
  shows "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> y \<^bold>\<longrightarrow>\<^sub>B z"
by (simp add: boolean_implication_def shunt1)

lemma shunt2:
  shows "x \<sqinter> y \<le> z \<longleftrightarrow> y \<le> x \<^bold>\<longrightarrow>\<^sub>B z"
by (subst inf.commute) (rule boolean_implication.shunt1)

lemma mp:
  assumes "x \<sqinter> y \<le> z"
  shows "x \<le> y \<^bold>\<longrightarrow>\<^sub>B z"
using assms by (simp add: boolean_implication.shunt1)

lemma imp_trivialI:
  assumes "P \<sqinter> -R \<le> -Q"
  shows "P \<le> Q \<^bold>\<longrightarrow>\<^sub>B R"
using assms by (simp add: boolean_implication_def shunt2 sup.commute)

lemma shunt_top:
  shows "P \<^bold>\<longrightarrow>\<^sub>B Q = \<top> \<longleftrightarrow> P \<le> Q"
by (simp add: boolean_implication_def sup_shunt)

lemma detachment:
  shows "x \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>B y) = x \<sqinter> y" (is ?thesis1)
    and "(x \<^bold>\<longrightarrow>\<^sub>B y) \<sqinter> x = x \<sqinter> y" (is ?thesis2)
proof -
  show ?thesis1 by (simp add: boolean_algebra.conj_disj_distrib boolean_implication_def)
  then show ?thesis2 by (simp add: ac_simps)
qed

lemma discharge:
  assumes "x' \<le> x"
  shows "x' \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>B y) = x' \<sqinter> y" (is ?thesis1)
    and "(x \<^bold>\<longrightarrow>\<^sub>B y) \<sqinter> x' = y \<sqinter> x'" (is ?thesis2)
proof -
  from assms show ?thesis1
    by (simp add: boolean_implication_def inf_sup_distrib sup.absorb2 le_supI1 flip: sup_neg_inf)
  then show ?thesis2
    by (simp add: ac_simps)
qed

lemma trans:
  shows "(x \<^bold>\<longrightarrow>\<^sub>B y) \<sqinter> (y \<^bold>\<longrightarrow>\<^sub>B z) \<le> (x \<^bold>\<longrightarrow>\<^sub>B z)"
by (simp add: boolean_implication_def inf_sup_distrib le_supI1 le_supI2)

setup \<open>Sign.parent_path\<close>


subsection\<open> Compactness and algebraicity\label{sec:more_lattices-concepts} \<close>

text\<open>

Fundamental lattice concepts drawn from \<^citet>\<open>"DaveyPriestley:2002"\<close>.

\<close>

context complete_lattice
begin

definition compact_points :: "'a set" where \<comment>\<open> \<^citet>\<open>\<open>Definition~7.15(ii)\<close> in "DaveyPriestley:2002"\<close> \<close>
  "compact_points = {x. \<forall>S. x \<le> \<Squnion>S \<longrightarrow> (\<exists>T\<subseteq>S. finite T \<and> x \<le> \<Squnion>T)}"

lemmas compact_pointsI = subsetD[OF equalityD2[OF compact_points_def], simplified, rule_format]
lemmas compact_pointsD = subsetD[OF equalityD1[OF compact_points_def], simplified, rule_format]

lemma compact_point_bot:
  shows "\<bottom> \<in> compact_points"
by (rule compact_pointsI) auto

lemma compact_points_sup: \<comment>\<open> \<^citet>\<open>\<open>Lemma~7.16\<close> in "DaveyPriestley:2002"\<close> \<close>
  assumes "x \<in> compact_points"
  assumes "y \<in> compact_points"
  shows "x \<squnion> y \<in> compact_points"
proof(rule compact_pointsI)
  fix S assume "x \<squnion> y \<le> \<Squnion>S"
  with compact_pointsD[OF assms(1), of S] compact_pointsD[OF assms(2), of S]
  obtain X Y
    where "X \<subseteq> S \<and> finite X \<and> x \<le> \<Squnion>X"
      and "Y \<subseteq> S \<and> finite Y \<and> y \<le> \<Squnion>Y"
    by auto
  then show "\<exists>T\<subseteq>S. finite T \<and> x \<squnion> y \<le> \<Squnion> T"
    by (simp add: exI[where x="X \<union> Y"] Sup_union_distrib le_supI1 le_supI2)
qed

lemma compact_points_Sup: \<comment>\<open> \<^citet>\<open>\<open>Lemma~7.16\<close> in "DaveyPriestley:2002"\<close> \<close>
  assumes "X \<subseteq> compact_points"
  assumes "finite X"
  shows "\<Squnion>X \<in> compact_points"
using assms(2,1) by induct (simp_all add: compact_point_bot compact_points_sup)

lemma compact_points_are_ccpo_compact: \<comment>\<open> converse should hold \<close>
  assumes "x \<in> compact_points"
  shows "ccpo.compact Sup (\<le>) x"
proof(rule ccpo.compactI[OF complete_lattice_ccpo], rule ccpo.admissibleI, rule notI)
  fix X
  assume "Complete_Partial_Order.chain (\<le>) X" and "x \<le> \<Squnion>X" and *: "X \<noteq> {}" "\<forall>y\<in>X. \<not>x \<le> y" 
  from compact_pointsD[OF assms \<open>x \<le> \<Squnion>X\<close>]
  obtain T where "T \<subseteq> X" and "finite T" and "x \<le> \<Squnion>T" by blast
  with * Complete_Partial_Order.chain_subset[OF \<open>Complete_Partial_Order.chain (\<le>) X\<close> \<open>T \<subseteq> X\<close>]
  show False
    by (auto simp: sup.absorb1 sup.absorb2 bot_unique dest: chainD dest!: finite_Sup_in)
qed

definition directed :: "'a set \<Rightarrow> bool" where \<comment>\<open> \<^citet>\<open>\<open>Definition~7.7\<close> in "DaveyPriestley:2002"\<close> \<close>
  "directed X \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>x\<in>X. \<forall>y\<in>X. \<exists>z\<in>X. x \<le> z \<and> y \<le> z)"

lemmas directedI = iffD2[OF directed_def, simplified conj_explode, rule_format]
lemmas directedD = iffD1[OF directed_def]

lemma directed_empty:
  assumes "directed X"
  shows "X \<noteq> {}"
using assms by (simp add: directed_def)

lemma chain_directed:
  assumes "Complete_Partial_Order.chain (\<le>) Y"
  assumes "Y \<noteq> {}"
  shows "directed Y"
using assms by (metis chainD directedI)

lemma directed_alt_def:
  shows "directed X \<longleftrightarrow> (\<forall>Y\<subseteq>X. finite Y \<longrightarrow> (\<exists>x\<in>X. \<forall>y\<in>Y. y \<le> x))" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  have "\<exists>x\<in>X. \<forall>y\<in>Y. y \<le> x" if "finite Y" and "directed X" and "Y \<subseteq> X" and "Y \<noteq> {}"for Y
    using that by induct (force dest: directedD)+
  then show "?lhs \<Longrightarrow> ?rhs" by (auto simp: directed_def)
next
  assume ?rhs show ?lhs
  proof(rule directedI)
    from \<open>?rhs\<close> show "X \<noteq> {}" by blast
    fix x y assume "x \<in> X" and "y \<in> X" with \<open>?rhs\<close> show "\<exists>z\<in>X. x \<le> z \<and> y \<le> z"
      by (clarsimp dest!: spec[where x="{x, y}"])
  qed
qed

lemma compact_points_alt_def: \<comment>\<open> \<^citet>\<open>\<open>Definition~7.15(i) (finite points)\<close> in "DaveyPriestley:2002"\<close> \<close>
  shows "compact_points = {x::'a. \<forall>D. directed D \<and> x \<le> \<Squnion>D \<longrightarrow> (\<exists>d\<in>D. x \<le> d)}" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<subseteq> ?rhs"
    by (clarsimp simp: compact_points_def directed_alt_def) (metis Sup_least order.trans)
next
  have *: "\<Squnion>S = \<Squnion>{\<Squnion>T |T. T \<noteq> {} \<and> T \<subseteq> S \<and> finite T}" for S :: "'a set" \<comment>\<open> \<^citet>\<open>\<open>Exercise~7.5\<close> in "DaveyPriestley:2002"\<close> \<close>
    by (fastforce intro: order.antisym Sup_subset_mono Sup_least exI[where x="{x}" for x])
  have **: "directed {\<Squnion>T |T. T \<noteq> {} \<and> T \<subseteq> S \<and> finite T}" (is "directed ?D") if "S \<noteq> {}" for S :: "'a set"
  proof(rule directedI)
    from \<open>S \<noteq> {}\<close> show "?D \<noteq> {}" by blast
    fix x y assume "x \<in> ?D" "y \<in> ?D"
    then obtain X Y
      where "x = \<Squnion>X \<and> X \<noteq> {} \<and> X \<subseteq> S \<and> finite X"
        and "y = \<Squnion>Y \<and> Y \<noteq> {} \<and> Y \<subseteq> S \<and> finite Y"
      by blast
    then show "\<exists>z\<in>?D. x \<le> z \<and> y \<le> z"
      by - (rule bexI[where x="\<Squnion>(X \<union> Y)"]; auto simp: Sup_subset_mono)
  qed
  have "\<exists>T\<subseteq>X. finite T \<and> x \<le> \<Squnion>T" if "\<forall>D. directed D \<and> x \<le> \<Squnion>D \<longrightarrow> (\<exists>d\<in>D. x \<le> d)" and "x \<le> \<Squnion>X" for x X
    using that *[of X] **[of X] by force
  then show "?rhs \<subseteq> ?lhs"
    by (fastforce intro: compact_pointsI)
qed

lemmas compact_points_directedD
  = subsetD[OF equalityD1[OF compact_points_alt_def], simplified, rule_format, simplified conj_explode, rotated -1]

end

class algebraic_lattice = complete_lattice + \<comment>\<open> \<^citet>\<open>\<open>Definition~7.18\<close> in "DaveyPriestley:2002"\<close> \<close>
  assumes algebraic: "(x :: 'a) = \<Squnion>({Y. Y \<le> x} \<inter> compact_points)"
begin

lemma le_compact:
  shows "x \<le> y \<longleftrightarrow> (\<forall>z\<in>compact_points. z \<le> x \<longrightarrow> z \<le> y)"
by (subst algebraic) (auto simp: Sup_le_iff)

end

lemma (in ccpo) compact_alt_def:
  shows "ccpo.compact Sup (\<le>) x \<longleftrightarrow> (\<forall>Y. Y \<noteq> {} \<and> Complete_Partial_Order.chain (\<le>) Y \<and> x \<le> Sup Y \<longrightarrow> (\<exists>y\<in>Y. x \<le> y))"
by (auto elim!: ccpo.compact.cases dest: ccpo.admissibleD intro!: compactI ccpo.admissibleI)

lemma compact_points_eq_finite_sets: \<comment>\<open> \<^citet>\<open>\<open>Examples~7.17\<close> in "DaveyPriestley:2002"\<close> \<close>
  shows "compact_points = Collect finite" (is "?lhs = ?rhs")
proof(rule antisym)
  have *: "X \<subseteq> \<Union>{{x} |x. x \<in> X}" for X :: "'a set" by blast
  show "?lhs \<subseteq> ?rhs" by (force dest: compact_pointsD[OF _ *] elim: finite_subset)
next
  show "?rhs \<subseteq> ?lhs" by (metis CollectD compact_pointsI finite_subset_Union subsetI)
qed

instance set :: (type) algebraic_lattice
by standard (fastforce simp: compact_points_eq_finite_sets)

context semilattice_sup
begin

definition sup_irreducible_on :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where \<comment>\<open> \<^citet>\<open>\<open>Definition~2.42\<close> in "DaveyPriestley:2002"\<close> \<close>
  "sup_irreducible_on A x \<longleftrightarrow> (\<forall>y\<in>A. \<forall>z\<in>A. x = y \<squnion> z \<longrightarrow> x = y \<or> x = z)"

abbreviation sup_irreducible :: "'a \<Rightarrow> bool" where
  "sup_irreducible \<equiv> sup_irreducible_on UNIV"

lemma sup_irreducible_onI:
  assumes "\<And>y z. \<lbrakk>y \<in> A; z \<in> A; x = y \<squnion> z\<rbrakk> \<Longrightarrow> x = y \<or> x = z"
  shows "sup_irreducible_on A x"
using assms by (simp add: sup_irreducible_on_def)

lemma sup_irreducible_onD:
  assumes "sup_irreducible_on A x"
  assumes "x = y \<squnion> z"
  assumes "y \<in> A"
  assumes "z \<in> A"
  shows "x = y \<or> x = z"
using assms by (auto simp: sup_irreducible_on_def)

lemma sup_irreducible_on_less: \<comment>\<open> \<^citet>\<open>\<open>Definition~2.42 (alt)\<close> in "DaveyPriestley:2002"\<close> \<close>
  shows "sup_irreducible_on A x \<longleftrightarrow> (\<forall>y\<in>A. \<forall>z\<in>A. y < x \<and> z < x \<longrightarrow> y \<squnion> z < x)"
by (simp add: sup_irreducible_on_def ac_simps sup.strict_order_iff)
   (metis local.sup.commute local.sup.left_idem)

end

lemma sup_irreducible_bot:
  assumes "\<bottom> \<in> A"
  shows "sup_irreducible_on A (\<bottom>::_::bounded_semilattice_sup_bot)"
using assms by (auto intro: sup_irreducible_onI)

lemma sup_irreducible_le_conv:
  fixes x::"_::distrib_lattice"
  assumes "sup_irreducible x"
  shows "x \<le> y \<squnion> z \<longleftrightarrow> x \<le> y \<or> x \<le> z"
by (auto simp: inf.absorb_iff2 inf_sup_distrib1 ac_simps
         dest: sup_irreducible_onD[OF assms sym, simplified])

lemma set_sup_irreducible:
  shows "sup_irreducible X \<longleftrightarrow> (X = {} \<or> (\<exists>y. X = {y}))" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (auto simp: sup_irreducible_on_def) (metis insert_is_Un mk_disjoint_insert)
  show "?rhs \<Longrightarrow> ?lhs" by (auto intro: sup_irreducible_onI)
qed

definition Sup_irreducible_on :: "'a::complete_lattice set \<Rightarrow> 'a \<Rightarrow> bool" where \<comment>\<open> \<^citet>\<open>\<open>Definition~10.26\<close> in "DaveyPriestley:2002"\<close> \<close>
  "Sup_irreducible_on A x \<longleftrightarrow> (\<forall>S\<subseteq>A. x = \<Squnion>S \<longrightarrow> x \<in> S)"

abbreviation Sup_irreducible :: "'a::complete_lattice \<Rightarrow> bool" where
  "Sup_irreducible \<equiv> Sup_irreducible_on UNIV"

definition Sup_prime_on :: "'a::complete_lattice set \<Rightarrow> 'a \<Rightarrow> bool" where \<comment>\<open> \<^citet>\<open>\<open>Definition~10.26\<close> in "DaveyPriestley:2002"\<close> \<close>
  "Sup_prime_on A x \<longleftrightarrow> (\<forall>S\<subseteq>A. x \<le> \<Squnion>S \<longrightarrow> (\<exists>s\<in>S. x \<le> s))"

abbreviation Sup_prime :: "'a::complete_lattice \<Rightarrow> bool" where
  "Sup_prime \<equiv> Sup_prime_on UNIV"

lemma Sup_irreducible_onI:
  assumes "\<And>S. \<lbrakk>S \<subseteq> A; x = \<Squnion>S\<rbrakk> \<Longrightarrow> x \<in> S"
  shows "Sup_irreducible_on A x"
using assms by (simp add: Sup_irreducible_on_def)

lemma Sup_irreducible_onD:
  assumes "x = \<Squnion>S"
  assumes "S \<subseteq> A"
  assumes "Sup_irreducible_on A x"
  shows "x \<in> S"
using assms by (simp add: Sup_irreducible_on_def)

lemma Sup_prime_onI:
  assumes "\<And>S. \<lbrakk>S \<subseteq> A; x \<le> \<Squnion>S\<rbrakk> \<Longrightarrow> \<exists>s\<in>S. x \<le> s"
  shows "Sup_prime_on A x"
using assms by (simp add: Sup_prime_on_def)

lemma Sup_prime_onE:
  assumes "Sup_prime_on A x"
  assumes "x \<le> \<Squnion>S"
  assumes "S \<subseteq> A"
  obtains s where "s \<in> S" and "x \<le> s"
using assms Sup_prime_on_def by blast

lemma Sup_prime_on_conv:
  assumes "Sup_prime_on A x"
  assumes "S \<subseteq> A"
  shows "x \<le> \<Squnion>S \<longleftrightarrow> (\<exists>s\<in>S. x \<le> s)"
using assms by (auto simp: Sup_prime_on_def intro: Sup_upper2)

lemma Sup_prime_not_bot:
  assumes "Sup_prime_on A x"
  shows "x \<noteq> \<bottom>"
using assms by (force simp: Sup_prime_on_def)

lemma Sup_prime_on_imp_Sup_irreducible_on: \<comment>\<open> the converse holds in Heyting algebras \<close>
  assumes "Sup_prime_on A x"
  shows "Sup_irreducible_on A x"
using Sup_upper
by (fastforce intro!: Sup_irreducible_onI intro: antisym elim!: Sup_prime_onE[OF assms, rotated])

lemma Sup_irreducible_on_imp_sup_irreducible_on:
  assumes "Sup_irreducible_on A x"
  assumes "x \<in> A"
  shows "sup_irreducible_on A x"
using assms by (fastforce simp: Sup_irreducible_on_def sup_irreducible_on_def
                          dest: spec[where x="{x, y}" for x y])

lemma Sup_prime_is_compact:
  assumes "Sup_prime x"
  shows "x \<in> compact_points"
using assms by (simp add: compact_points_alt_def Sup_prime_on_def)
(*<*)

end
(*>*)
