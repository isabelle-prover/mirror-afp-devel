theory Nat_Util
  imports Main
begin

section \<open>HOL\<close>

lemma duplicate_assms:
  "(\<lbrakk>P; P\<rbrakk> \<Longrightarrow> Q) \<equiv> (P \<Longrightarrow> Q)"
  by simp

section \<open>Natural Number Arithmetic\<close>

lemma div_2_eq_Suc:
  "\<lbrakk>x div 2 = y div 2; x \<noteq> y\<rbrakk> \<Longrightarrow> (y = Suc x) \<or> (x = Suc y)"
  by linarith

lemma Suc_m_sub_n_div_2:
  "Suc ((m - n) div 2) > (m - Suc n) div 2"
  by (simp add: div_le_mono le_Suc_eq)

lemma Suc_div_2_less_Suc:
  "Suc x div 2 < Suc x"
  by simp

lemma nat_x_less_y_le_Suc_x:
  "\<lbrakk>x < y; y \<le> Suc x\<rbrakk> \<Longrightarrow> y = Suc x"
  by simp

lemma nat_sub_eq_add:
  "\<lbrakk>(a :: nat) - b = c - d; b < a\<rbrakk> \<Longrightarrow> a + d = c + b"
  by simp

end