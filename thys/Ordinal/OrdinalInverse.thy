(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Inverse Functions\<close>

theory OrdinalInverse
imports OrdinalArith
begin

lemma (in normal) oInv_ex: 
  assumes "F 0 \<le> a" shows "\<exists>q. F q \<le> a \<and> a < F (oSuc q)"
proof -
  have "a < F z \<Longrightarrow> (\<exists>q<z. F q \<le> a \<and> a < F (oSuc q))" for z
  proof (induction z rule: oLimit_induct)
    case zero
    then show ?case
      using assms by auto
  next
    case (suc x)
    then show ?case
      by (metis less_oSuc linorder_not_le order_less_trans)
  next
    case (lim f)
    then show ?case
      by (metis less_oLimitD less_oLimitI oLimit)
  qed
  then show ?thesis
    by (metis increasing oSuc_le_eq_less)
qed

lemma oInv_uniq:
  assumes "mono (F::ordinal \<Rightarrow> ordinal)" "F x \<le> a" "a < F (oSuc x)" "F y \<le> a" "a < F (oSuc y)"
  shows "x = y"
proof (cases "x<y")
  case True
  with assms show ?thesis 
    by (meson dual_order.trans leD monoD oSuc_leI)
next
  case False
  with assms show ?thesis
    by (meson dual_order.strict_trans2 less_oSucE mono_strict_invE)
qed

definition
  oInv :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oInv F a = (if F 0 \<le> a then (THE x. F x \<le> a \<and> a < F (oSuc x)) else 0)"

lemma (in normal) oInv_bounds: "F 0 \<le> a \<Longrightarrow> F (oInv F a) \<le> a \<and> a < F (oSuc (oInv F a))"
  by (simp add: oInv_def) (metis (no_types, lifting) theI' mono oInv_ex oInv_uniq)

lemma (in normal) oInv_bound1:
  "F 0 \<le> a \<Longrightarrow> F (oInv F a) \<le> a"
  by (rule oInv_bounds[THEN conjunct1])

lemma (in normal) oInv_bound2: "a < F (oSuc (oInv F a))"
  by (metis cancel_less linorder_not_le oInv_bounds order.strict_trans ordinal_not_0_less)

lemma (in normal) oInv_equality: "\<lbrakk>F x \<le> a; a < F (oSuc x)\<rbrakk> \<Longrightarrow> oInv F a = x"
  by (meson mono normal.cancel_le normal_axioms oInv_bound1 oInv_bound2 oInv_uniq ordinal_0_le order_trans)

lemma (in normal) oInv_inverse: "oInv F (F x) = x"
  by (rule oInv_equality, simp_all add: cancel_less)

lemma (in normal) oInv_equality': "a = F x \<Longrightarrow> oInv F a = x"
  by (simp add: oInv_inverse)

lemma (in normal) oInv_eq_0: "a \<le> F 0 \<Longrightarrow> oInv F a = 0"
  by (metis nle_le oInv_def oInv_equality')

lemma (in normal) oInv_less: "\<lbrakk>F 0 \<le> a; a < F z\<rbrakk> \<Longrightarrow> oInv F a < z"
  using cancel_less oInv_bound1 by fastforce

lemma (in normal) le_oInv: "F z \<le> a \<Longrightarrow> z \<le> oInv F a"
  by (metis cancel_le dual_order.trans le_oSucE linorder_not_less oInv_bound2 order_le_less)

lemma (in normal) less_oInvD: "x < oInv F a \<Longrightarrow> F (oSuc x) \<le> a"
  by (metis (no_types) linorder_not_le nle_le oInv_eq_0 oInv_less oSuc_leI ordinal_0_le)

lemma (in normal) oInv_le: "a < F (oSuc x) \<Longrightarrow> oInv F a \<le> x"
  by (metis leD less_oInvD nle_le order_le_less)

lemma (in normal) mono_oInv: "mono (oInv F)"
proof
  fix x y :: ordinal
  assume "x \<le> y"
  show "oInv F x \<le> oInv F y"
  proof (rule linorder_le_cases [of x "F 0"])
    assume "x \<le> F 0" then show ?thesis by (simp add: oInv_eq_0)
  next
    assume "F 0 \<le> x" show ?thesis
      by (rule le_oInv, simp only: \<open>x \<le> y\<close> \<open>F 0 \<le> x\<close> order_trans [OF oInv_bound1])
  qed
qed

lemma (in normal) oInv_decreasing: "F 0 \<le> x \<Longrightarrow> oInv F x \<le> x"
  by (meson dual_order.trans increasing oInv_bound1)


subsection \<open>Division\<close>

instantiation ordinal :: modulo
begin

definition
  div_ordinal_def:
   "x div y = (if 0 < y then oInv ((*) y) x else 0)"

definition
  mod_ordinal_def: 
   "x mod y = ((x::ordinal) - y * (x div y))"

instance ..

end

lemma ordinal_divI: "\<lbrakk>x = y * q + r; r < y\<rbrakk> \<Longrightarrow> x div y = (q::ordinal)"
  using div_ordinal_def normal.oInv_equality normal_times by auto

lemma ordinal_times_div_le: "y * (x div y) \<le> (x::ordinal)"
  by (simp add: div_ordinal_def normal.oInv_bound1 normal_times)

lemma ordinal_less_times_div_plus: "0 < y \<Longrightarrow> x < y * (x div y) + (y::ordinal)"
  by (metis div_ordinal_def normal.oInv_bound2 normal_times ordinal_times_oSuc)

lemma ordinal_modI: "\<lbrakk>x = y * q + r; r < y\<rbrakk> \<Longrightarrow> x mod y = (r::ordinal)"
  by (simp add: mod_ordinal_def ordinal_divI)

lemma ordinal_mod_less: "0 < y \<Longrightarrow> x mod y < (y::ordinal)"
  by (simp add: mod_ordinal_def ordinal_less_times_div_plus ordinal_times_div_le)

lemma ordinal_div_plus_mod: "y * (x div y) + (x mod y) = (x::ordinal)"
  by (simp add: mod_ordinal_def ordinal_times_div_le)

lemma ordinal_div_less: "x < y * z \<Longrightarrow> x div y < (z::ordinal)"
  using div_ordinal_def normal.oInv_less normal_times by auto

lemma ordinal_le_div: "\<lbrakk>0 < y; y * z \<le> x\<rbrakk> \<Longrightarrow> (z::ordinal) \<le> x div y"
  by (simp add: div_ordinal_def normal.le_oInv normal_times)

lemma ordinal_mono_div: "mono (\<lambda>x. x div y::ordinal)"
  by (smt (verit) Orderings.order_eq_iff div_ordinal_def monoD monoI normal.mono_oInv normal_times)

lemma ordinal_div_monoL: "x \<le> x' \<Longrightarrow> x div y \<le> x' div (y::ordinal)"
  by (erule monoD[OF ordinal_mono_div])

lemma ordinal_div_decreasing: "(x::ordinal) div y \<le> x"
  by (simp add: div_ordinal_def normal.oInv_decreasing normal_times)

lemma ordinal_div_0: "x div 0 = (0::ordinal)"
  by (simp add: div_ordinal_def)

lemma ordinal_mod_0: "x mod 0 = (x::ordinal)"
  by (simp add: mod_ordinal_def)


subsection \<open>Derived properties of division\<close>

lemma ordinal_div_1 [simp]: "x div oSuc 0 = x"
  using ordinal_divI by force

lemma ordinal_mod_1 [simp]: "x mod oSuc 0 = 0"
  by (simp add: mod_ordinal_def)

lemma ordinal_div_self [simp]: "0 < x \<Longrightarrow> x div x = (1::ordinal)"
  by (metis ordinal_divI ordinal_one_def ordinal_plus_0 ordinal_times_1)

lemma ordinal_mod_self [simp]: "x mod x = (0::ordinal)"
  by (metis ordinal_modI ordinal_mod_0 ordinal_neq_0 ordinal_plus_0 ordinal_times_1)

lemma ordinal_div_greater [simp]: "x < y \<Longrightarrow> x div y = (0::ordinal)"
  by (simp add: ordinal_divI)

lemma ordinal_mod_greater [simp]: "x < y \<Longrightarrow> x mod y = (x::ordinal)"
  by (simp add: mod_ordinal_def)

lemma ordinal_0_div [simp]: "0 div x = (0::ordinal)"
  by (metis div_ordinal_def ordinal_div_greater)

lemma ordinal_0_mod [simp]: "0 mod x = (0::ordinal)"
  by (simp add: mod_ordinal_def)

lemma ordinal_1_dvd [simp]: "oSuc 0 dvd x"
  by (simp add: dvdI)

lemma ordinal_dvd_mod: "y dvd x = (x mod y = (0::ordinal))"
  by (metis dvd_def ordinal_0_times ordinal_div_plus_mod ordinal_modI ordinal_mod_0 ordinal_neq_0 ordinal_plus_0)

lemma ordinal_dvd_times_div: "y dvd x \<Longrightarrow> y * (x div y) = (x::ordinal)"
  by (metis ordinal_div_plus_mod ordinal_dvd_mod ordinal_plus_0)

lemma ordinal_dvd_oLimit:
  assumes "\<forall>n. x dvd f n" shows "x dvd oLimit f"
proof 
  show "oLimit f = x * oLimit (\<lambda>n. f n div x)"
    using assms by (simp add: ordinal_dvd_times_div)
qed


subsection \<open>Logarithms\<close>

definition
  oLog :: "ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oLog b = (\<lambda>x. if 1 < b then oInv ((**) b) x else 0)"

lemma ordinal_oLogI: 
  assumes "b ** y \<le> x" "x < b ** y * b" shows "oLog b x = y"
proof (cases "1 < b")
  case True
  then show ?thesis
    by (simp add: assms normal.oInv_equality normal_exp oLog_def)
qed (use assms linorder_neq_iff in fastforce)

lemma ordinal_exp_oLog_le: "\<lbrakk>0 < x; oSuc 0 < b\<rbrakk> \<Longrightarrow> b ** (oLog b x) \<le> x"
  by (simp add: normal.oInv_bound1 normal_exp oLog_def oSuc_leI)

lemma ordinal_less_exp_oLog: "oSuc 0 < b \<Longrightarrow> x < b ** (oLog b x) * b"
  by (metis normal.oInv_bound2 normal_exp oLog_def ordinal_exp_oSuc ordinal_one_def)

lemma ordinal_oLog_less: "\<lbrakk>0 < x; oSuc 0 < b; x < b ** y\<rbrakk> \<Longrightarrow> oLog b x < y"
  by (simp add: normal.oInv_less normal_exp oLog_def oSuc_leI)

lemma ordinal_le_oLog:
  "\<lbrakk>oSuc 0 < b; b ** y \<le> x\<rbrakk> \<Longrightarrow> y \<le> oLog b x"
  by (simp add: oLog_def normal.le_oInv[OF normal_exp])

lemma ordinal_oLogI2:
  assumes "oSuc 0 < b" "x = b ** y * q + r" "0 < q" "q < b" "r < b ** y"
  shows "oLog b x = y"
proof (rule ordinal_oLogI)
  show "b ** y \<le> x"
    using assms by (metis dual_order.trans ordinal_le_plusR ordinal_le_timesR)
  show "x < b ** y * b"
    using assms
    by (metis leD leI order_less_trans ordinal_divI ordinal_exp_not_0 ordinal_le_div)
qed

lemma ordinal_div_exp_oLog_less: "oSuc 0 < b \<Longrightarrow> x div (b ** oLog b x) < b"
  by (simp add: ordinal_div_less ordinal_less_exp_oLog)

lemma ordinal_oLog_base_0: "oLog 0 x = 0"
  by (simp add: oLog_def)

lemma ordinal_oLog_base_1: "oLog (oSuc 0) x = 0"
  by (simp add: oLog_def)

lemma ordinal_oLog_0: "oLog b 0 = 0"
  by (simp add: oLog_def normal.oInv_eq_0[OF normal_exp])

lemma ordinal_oLog_exp: "oSuc 0 < b \<Longrightarrow> oLog b (b ** x) = x"
  by (simp add: oLog_def normal.oInv_inverse[OF normal_exp])

lemma ordinal_oLog_self: "oSuc 0 < b \<Longrightarrow> oLog b b = oSuc 0"
  by (metis ordinal_exp_1 ordinal_oLog_exp)

lemma ordinal_mono_oLog: "mono (oLog b)"
  by (simp add: monoD monoI normal.mono_oInv normal_exp oLog_def)

lemma ordinal_oLog_monoR: "x \<le> y \<Longrightarrow> oLog b x \<le> oLog b y"
  by (erule monoD[OF ordinal_mono_oLog])

lemma ordinal_oLog_decreasing: "oLog b x \<le> x"
  by (metis normal.increasing normal_exp oLog_def ordinal_0_le ordinal_oLog_exp ordinal_oLog_monoR ordinal_one_def)

end
