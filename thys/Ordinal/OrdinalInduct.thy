(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Ordinal Induction\<close>

theory OrdinalInduct
imports OrdinalDef
begin

subsection \<open>Zero and successor ordinals\<close>

definition
  oSuc :: "ordinal \<Rightarrow> ordinal" where
    "oSuc x = oStrictLimit (\<lambda>n. x)"

lemma less_oSuc[iff]: "x < oSuc x"
  by (metis oStrictLimit_ub oSuc_def)

lemma oSuc_leI: "x < y \<Longrightarrow> oSuc x \<le> y"
  by (simp add: oStrictLimit_lub oSuc_def)

instantiation ordinal :: "{zero, one}"
begin

definition
  ordinal_zero_def:       "(0::ordinal) = oZero"

definition
  ordinal_one_def [simp]: "(1::ordinal) = oSuc 0"

instance ..

end


subsubsection \<open>Derived properties of 0 and oSuc\<close>

lemma less_oSuc_eq_le: "(x < oSuc y) = (x \<le> y)"
  by (metis dual_order.strict_trans1 less_oSuc linorder_not_le oSuc_leI)

lemma ordinal_0_le [iff]: "0 \<le> (x::ordinal)"
  by (simp add: oZero_least ordinal_zero_def)

lemma ordinal_not_less_0 [iff]: "\<not> (x::ordinal) < 0"
  by (simp add: linorder_not_less)

lemma ordinal_le_0 [iff]: "(x \<le> 0) = (x = (0::ordinal))"
  by (simp add: order_le_less)

lemma ordinal_neq_0 [iff]: "(x \<noteq> 0) = (0 < (x::ordinal))"
  by (simp add: order_less_le)

lemma ordinal_not_0_less [iff]: "(\<not> 0 < x) = (x = (0::ordinal))"
  by (simp add: linorder_not_less)

lemma oSuc_le_eq_less: "(oSuc x \<le> y) = (x < y)"
  by (meson leD leI less_oSuc_eq_le)

lemma zero_less_oSuc [iff]: "0 < oSuc x"
  by (rule order_le_less_trans, rule ordinal_0_le, rule less_oSuc)

lemma oSuc_not_0 [iff]: "oSuc x \<noteq> 0"
  by simp

lemma less_oSuc0 [iff]: "(x < oSuc 0) = (x = 0)"
  by (simp add: less_oSuc_eq_le)

lemma oSuc_less_oSuc [iff]: "(oSuc x < oSuc y) = (x < y)"
  by (simp add: less_oSuc_eq_le oSuc_le_eq_less)

lemma oSuc_eq_oSuc [iff]: "(oSuc x = oSuc y) = (x = y)"
  by (metis less_oSuc less_oSuc_eq_le order_antisym)

lemma oSuc_le_oSuc [iff]: "(oSuc x \<le> oSuc y) = (x \<le> y)"
  by (simp add: order_le_less)

lemma le_oSucE: 
  "\<lbrakk>x \<le> oSuc y; x \<le> y \<Longrightarrow> R; x = oSuc y \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp add: order_le_less less_oSuc_eq_le)

lemma less_oSucE:
  "\<lbrakk>x < oSuc y; x < y \<Longrightarrow> P; x = y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: less_oSuc_eq_le order_le_less)


subsection \<open>Strict monotonicity\<close>

locale strict_mono =
  fixes f
  assumes strict_mono: "A < B \<Longrightarrow> f A < f B"

lemmas strict_monoI = strict_mono.intro
  and strict_monoD = strict_mono.strict_mono

lemma strict_mono_natI:
  fixes f :: "nat \<Rightarrow> 'a::order"
  shows "(\<And>n. f n < f (Suc n)) \<Longrightarrow> strict_mono f"
  using OrdinalInduct.strict_monoI lift_Suc_mono_less by blast

lemma mono_natI:
  fixes f :: "nat \<Rightarrow> 'a::order"
  shows "(\<And>n. f n \<le> f (Suc n)) \<Longrightarrow> mono f"
  by (simp add: mono_iff_le_Suc)

lemma strict_mono_mono:
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "strict_mono f \<Longrightarrow> mono f"
  by (auto intro!: monoI simp add: order_le_less strict_monoD)

lemma strict_mono_monoD:
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "\<lbrakk>strict_mono f; A \<le> B\<rbrakk> \<Longrightarrow> f A \<le> f B"
  by (rule monoD[OF strict_mono_mono])

lemma strict_mono_cancel_eq:
  fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
  shows "strict_mono f \<Longrightarrow> (f x = f y) = (x = y)"
  by (metis OrdinalInduct.strict_monoD not_less_iff_gr_or_eq)

lemma strict_mono_cancel_less: 
  fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
  shows "strict_mono f \<Longrightarrow> (f x < f y) = (x < y)"
  using OrdinalInduct.strict_monoD linorder_neq_iff by fastforce

lemma strict_mono_cancel_le:
  fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
  shows "strict_mono f \<Longrightarrow> (f x \<le> f y) = (x \<le> y)"
  by (meson linorder_not_less strict_mono_cancel_less)


subsection \<open>Limit ordinals\<close>

definition
  oLimit :: "(nat \<Rightarrow> ordinal) \<Rightarrow> ordinal" where
  "oLimit f = (LEAST k. \<forall>n. f n \<le> k)"

lemma oLimit_leI: "\<forall>n. f n \<le> x \<Longrightarrow> oLimit f \<le> x"
  by (simp add: oLimit_def wellorder_Least_lemma(2))

lemma le_oLimit [iff]: "f n \<le> oLimit f"
  by (smt (verit, best) LeastI_ex leD oLimit_def oStrictLimit_ub ordinal_linear)

lemma le_oLimitI: "x \<le> f n \<Longrightarrow> x \<le> oLimit f"
  by (erule order_trans, rule le_oLimit)

lemma less_oLimitI: "x < f n \<Longrightarrow> x < oLimit f"
  by (erule order_less_le_trans, rule le_oLimit)

lemma less_oLimitD: "x < oLimit f \<Longrightarrow> \<exists>n. x < f n"
  by (meson linorder_not_le oLimit_leI)

lemma less_oLimitE: "\<lbrakk>x < oLimit f; \<And>n. x < f n \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto dest: less_oLimitD)

lemma le_oLimitE:
  "\<lbrakk>x \<le> oLimit f; \<And>n. x \<le> f n \<Longrightarrow> R; x = oLimit f \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp add: order_le_less dest: less_oLimitD)

lemma oLimit_const [simp]: "oLimit (\<lambda>n. x) = x"
  by (meson dual_order.refl le_oLimit oLimit_leI order_antisym)

lemma strict_mono_less_oLimit: "strict_mono f \<Longrightarrow> f n < oLimit f"
  by (meson OrdinalInduct.strict_monoD lessI less_oLimitI)

lemma oLimit_eqI:
  "\<lbrakk>\<And>n. \<exists>m. f n \<le> g m; \<And>n. \<exists>m. g n \<le> f m\<rbrakk> \<Longrightarrow> oLimit f = oLimit g"
  by (meson le_oLimitI nle_le oLimit_leI)

lemma oLimit_Suc:
  "f 0 < oLimit f \<Longrightarrow> oLimit (\<lambda>n. f (Suc n)) = oLimit f"
  by (smt (verit, ccfv_SIG) linorder_not_le nle_le oLimit_eqI oLimit_leI old.nat.exhaust)

lemma oLimit_shift:
  "\<forall>n. f n < oLimit f \<Longrightarrow> oLimit (\<lambda>n. f (n + k)) = oLimit f"
  apply (induct_tac k, simp)
  by (metis (no_types, lifting) add_Suc_shift leD le_oLimit less_oLimitD not_less_iff_gr_or_eq oLimit_Suc)

lemma oLimit_shift_mono:
  "mono f \<Longrightarrow> oLimit (\<lambda>n. f (n + k)) = oLimit f"
  by (meson le_add1 monoD oLimit_eqI)


text "limit ordinal predicate"

definition
  limit_ordinal :: "ordinal \<Rightarrow> bool" where
  "limit_ordinal x \<longleftrightarrow> (x \<noteq> 0) \<and> (\<forall>y. x \<noteq> oSuc y)"

lemma limit_ordinal_not_0 [simp]: "\<not> limit_ordinal 0"
  by (simp add: limit_ordinal_def)

lemma zero_less_limit_ordinal [simp]: "limit_ordinal x \<Longrightarrow> 0 < x"
  by (simp add: limit_ordinal_def)

lemma limit_ordinal_not_oSuc [simp]: "\<not> limit_ordinal (oSuc p)"
  by (simp add: limit_ordinal_def)

lemma oSuc_less_limit_ordinal:
  "limit_ordinal x \<Longrightarrow> (oSuc w < x) = (w < x)"
  by (metis limit_ordinal_not_oSuc oSuc_le_eq_less order_le_less)

lemma limit_ordinal_oLimitI:
  "\<forall>n. f n < oLimit f \<Longrightarrow> limit_ordinal (oLimit f)"
  by (metis less_oLimitD less_oSuc less_oSucE limit_ordinal_def order_less_imp_triv ordinal_neq_0)

lemma strict_mono_limit_ordinal:
  "strict_mono f \<Longrightarrow> limit_ordinal (oLimit f)"
  by (simp add: limit_ordinal_oLimitI strict_mono_less_oLimit)

lemma limit_ordinalI:
  "\<lbrakk>0 < z; \<forall>x<z. oSuc x < z\<rbrakk> \<Longrightarrow> limit_ordinal z"
  using limit_ordinal_def by blast


subsubsection \<open>Making strict monotonic sequences\<close>

primrec make_mono :: "(nat \<Rightarrow> ordinal) \<Rightarrow> nat \<Rightarrow> nat"
  where
    "make_mono f 0       = 0"
  | "make_mono f (Suc n) = (LEAST x. f (make_mono f n) < f x)"

lemma f_make_mono_less:
  "\<forall>n. f n < oLimit f \<Longrightarrow> f (make_mono f n) < f (make_mono f (Suc n))"
  by (metis less_oLimitD make_mono.simps(2) wellorder_Least_lemma(1))

lemma strict_mono_f_make_mono:
  "\<forall>n. f n < oLimit f \<Longrightarrow> strict_mono (\<lambda>n. f (make_mono f n))"
  by (rule strict_mono_natI, erule f_make_mono_less)

lemma le_f_make_mono:
  "\<lbrakk>\<forall>n. f n < oLimit f; m \<le> make_mono f n\<rbrakk> \<Longrightarrow> f m \<le> f (make_mono f n)"
  apply (auto simp add: order_le_less)
  apply (case_tac n, simp_all)
  by (metis LeastI less_oLimitD linorder_le_less_linear not_less_Least order_le_less_trans)

lemma make_mono_less:
  "\<forall>n. f n < oLimit f \<Longrightarrow> make_mono f n < make_mono f (Suc n)"
  by (meson f_make_mono_less le_f_make_mono linorder_not_less)

declare make_mono.simps [simp del]

lemma oLimit_make_mono_eq:
  assumes "\<forall>n. f n < oLimit f" shows "oLimit (\<lambda>n. f (make_mono f n)) = oLimit f"
proof -
  have "k \<le> make_mono f k" for k
    by (induction k) (auto simp: Suc_leI assms make_mono_less order_le_less_trans)
  then show ?thesis
    by (meson assms le_f_make_mono oLimit_eqI)
qed

subsection \<open>Induction principle for ordinals\<close>

lemma oLimit_le_oStrictLimit: "oLimit f \<le> oStrictLimit f"
  by (simp add: oLimit_leI oStrictLimit_ub order_less_imp_le)

lemma oLimit_induct [case_names zero suc lim]:
assumes zero: "P 0"
    and suc:  "\<And>x. P x \<Longrightarrow> P (oSuc x)"
    and lim:  "\<And>f. \<lbrakk>strict_mono f; \<forall>n. P (f n)\<rbrakk> \<Longrightarrow> P (oLimit f)"
shows "P a"
 apply (rule oStrictLimit_induct)
  apply (rule zero[unfolded ordinal_zero_def])
 apply (cut_tac f=f in oLimit_le_oStrictLimit)
 apply (simp add: order_le_less, erule disjE)
  apply (metis dual_order.order_iff_strict leD le_oLimit less_oStrictLimitD oSuc_le_eq_less suc)
  by (metis lim oLimit_make_mono_eq oStrictLimit_ub strict_mono_f_make_mono)

lemma ordinal_cases [case_names zero suc lim]:
assumes zero: "a = 0 \<Longrightarrow> P"
    and suc:  "\<And>x. a = oSuc x \<Longrightarrow> P"
    and lim:  "\<And>f. \<lbrakk>strict_mono f; a = oLimit f\<rbrakk> \<Longrightarrow> P"
  shows "P"
 apply (subgoal_tac "\<forall>x. a = x \<longrightarrow> P", force)
 apply (rule allI)
 apply (rule_tac a=x in oLimit_induct)
   apply (rule impI, erule zero)
  apply (rule impI, erule suc)
 apply (rule impI, erule lim, assumption)
done

end
