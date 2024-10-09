theory 
  NREST_Auxiliaries
imports
  "HOL-Library.Extended_Nat" "Automatic_Refinement.Automatic_Refinement"
begin

unbundle lattice_syntax

section "Auxiliaries"

subsection "Auxiliaries for option"

lemma less_eq_option_None_is_None': "x \<le> None \<longleftrightarrow> x = None"
  by(auto simp: less_eq_option_None_is_None)

lemma everywhereNone: "(\<forall>x\<in>X. x = None) \<longleftrightarrow> X = {} \<or> X = {None}"
  by auto

subsection "Auxiliaries for enat"

lemma enat_minus_mono: "a' \<ge> b \<Longrightarrow> a' \<ge> a \<Longrightarrow> a' - b \<ge> (a::enat) - b"
  by (cases a; cases b; cases a') auto

lemma enat_plus_minus_aux1: "a + b \<le> a' \<Longrightarrow> \<not> a' < a \<Longrightarrow> b \<le> a' - (a::enat)"
  by (cases a; cases b; cases a') auto

lemma enat_plus_minus_aux2: "\<not> a < a' \<Longrightarrow> b \<le> a - a' \<Longrightarrow> a' + b \<le> (a::enat)"
  by (cases a; cases b; cases a') auto

lemma enat_minus_inf_conv[simp]: "a - enat n = \<infinity> \<longleftrightarrow> a=\<infinity>" by (cases a) auto
lemma enat_minus_fin_conv[simp]: "a - enat n = enat m \<longleftrightarrow> (\<exists>k. a=enat k \<and> m = k - n)"
  by (cases a) auto

lemma helper: "x2 \<le> x2a \<Longrightarrow> \<not> x2 < a \<Longrightarrow> \<not> x2a < a \<Longrightarrow>  x2 - (a::enat) \<le> x2a - a"
  by (cases x2; cases x2a; cases a) auto

lemma helper2: "x2b \<le> x2 \<Longrightarrow> \<not> x2a < x2  \<Longrightarrow> \<not> x2a < x2b \<Longrightarrow> x2a - (x2::enat) \<le> x2a - x2b"
  by (cases x2; cases x2a; cases x2b) auto

lemma Sup_finite_enat: "Sup X = Some (enat a) \<Longrightarrow> Some (enat a) \<in> X"
  by (auto simp: Sup_option_def Sup_enat_def these_empty_eq Max_eq_iff in_these_eq split: if_splits)

lemma Sup_enat_less2: "Sup X = \<infinity> \<Longrightarrow> \<exists>x\<in>X. enat t < x"
  by (subst less_Sup_iff[symmetric]) simp

lemma enat_upper[simp]: "t \<le> Some (\<infinity>::enat)"
  by (cases t, auto)

subsection "Auxiliary (for Sup and Inf)"

lemma aux11: "f`X={y} \<longleftrightarrow> (X\<noteq>{} \<and> (\<forall>x\<in>X. f x = y))" by auto
 
lemma aux2: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {None} \<longleftrightarrow> (M x = None \<and> M\<noteq>Map.empty)"
  by (cases "M x"; force simp: aux11)

lemma aux3: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1}
  = {Some t1 | t1. M x = Some t1} \<union> ({None | y. y\<noteq>x \<and> M y \<noteq> None })"
  by (fastforce split: if_splits simp: image_iff) 

lemma Sup_pointwise_eq_fun: "(\<Squnion>f \<in> {[x \<mapsto> t1] |x t1. M x = Some t1}. f x) = M x"
proof(cases "M x")
  case None
  then show ?thesis 
    by (auto simp add: Sup_option_def aux2 split: if_splits)
next
  case (Some a)
  have s: "Option.these {u. u = None \<and> (\<exists>y. y \<noteq> x \<and> (\<exists>ya. M y = Some ya))} = {}"
    by (auto simp add: in_these_eq)
  from Some show ?thesis
    by (auto simp add: Sup_option_def s aux3 split: if_splits)
qed

lemma SUP_eq_None_iff: "(\<Squnion>f \<in> X. f x) = None \<longleftrightarrow> X={} \<or> (\<forall>f\<in>X. f x = None)"
  by (smt SUP_bot_conv(2) SUP_empty Sup_empty empty_Sup)

lemma SUP_eq_Some_iff:
  "(\<Squnion>f \<in> X. f x) = Some t \<longleftrightarrow> (\<exists>f\<in>X. f x \<noteq> None) \<and> (t=Sup {t' | f t'. f\<in>X \<and> f x = Some t' })"
proof safe 
  show "(\<Squnion>f\<in>X. f x) = Some t \<Longrightarrow> \<exists>f\<in>X. f x \<noteq> None"
    by (metis SUP_eq_None_iff option.distinct(1))
qed (fastforce intro!: arg_cong[where f=Sup] simp: image_iff Option.these_def Sup_option_def split: option.splits if_splits)+



lemma Sup_enat_less: "X \<noteq> {} \<Longrightarrow> enat t \<le> Sup X \<longleftrightarrow> (\<exists>x\<in>X. enat t \<le> x)"
  using finite_enat_bounded by (simp add: Max_ge_iff Sup_upper2 Sup_enat_def) (meson nle_le)

(* 
  This is how implication can be phrased with an Inf operation.
  Generalization from boolean to enat can be explained this way.
 *)

lemma fixes Q P  shows
    "Inf { P x \<le> Q x |x. True}  \<longleftrightarrow> P \<le> Q" 
  unfolding le_fun_def by simp

end