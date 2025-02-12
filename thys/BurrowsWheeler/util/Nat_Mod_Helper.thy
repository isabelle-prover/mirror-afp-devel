theory Nat_Mod_Helper
  imports Main
begin

section "Nat Modulo Helper"

lemma nat_mod_add_neq_self:
  "\<lbrakk>a < (n :: nat); b < n; b \<noteq> 0\<rbrakk> \<Longrightarrow> (a + b) mod n \<noteq> a"
  by (metis add_diff_cancel_left' mod_if mod_mult_div_eq mod_mult_self1_is_0)

lemma nat_mod_a_pl_b_eq1:
  "\<lbrakk>n + b \<le> a; a < (n :: nat)\<rbrakk> \<Longrightarrow> (a + b) mod n = b - (n - a)"
  using order_le_less_trans by blast

lemma  not_mod_a_pl_b_eq2:
  "\<lbrakk>n - a \<le> b; a < n; b < (n :: nat)\<rbrakk> \<Longrightarrow> (a + b) mod n = b - (n - a)"
  using Nat.diff_diff_right add.commute mod_if by auto

end