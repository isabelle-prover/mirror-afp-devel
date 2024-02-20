section "The @{text estimation} tactic"

theory Estimation_Method
  imports Main "HOL-Eisbach.Eisbach_Tools"
begin

text "A few useful lemmas for working with inequalities."

lemma if_prop_cong:
  assumes "C = C'"
  assumes "C \<Longrightarrow> P A A'"
  assumes "\<not> C \<Longrightarrow> P B B'"
  shows "P (if C then A else B) (if C' then A' else B')"
  using assms by simp

lemma if_leqI:
  assumes "C \<Longrightarrow> A \<le> t"
  assumes "\<not> C \<Longrightarrow> B \<le> t"
  shows "(if C then A else B) \<le> t"
  using assms by simp

lemma if_le_max:
  "(if C then (t1 :: 'a :: linorder) else t2) \<le> max t1 t2"
  by simp

text "Prove some inequality by showing a chain of inequalities via an intermediate term."

method itrans for step :: "'a :: order" =
  (match conclusion in "s \<le> t" for s t :: 'a \<Rightarrow> \<open>rule order.trans[of s step t]\<close>)

text "A collection of monotonicity intro rules that will be automatically used by @{text estimation}."

lemmas mono_intros =
  order.refl add_mono diff_mono mult_le_mono max.mono min.mono power_increasing power_mono
  iffD2[OF Suc_le_mono] if_prop_cong[where P = "(\<le>)"] Nat.le0 one_le_numeral

text "Try to apply a given estimation rule @{text estimate} in a forward-manner."

method estimation uses estimate =
  (match estimate in "\<And>a. f a \<le> h a" (multi) for f h \<Rightarrow> \<open>
    match conclusion in "g f \<le> t" for g and t :: nat \<Rightarrow>
    \<open>rule order.trans[of "g f" "g h" t], intro mono_intros refl estimate\<close>\<close>
    
  \<bar> "x \<le> y" for x y \<Rightarrow> \<open>
    match conclusion in "g x \<le> t" for g and t :: nat \<Rightarrow>
    \<open>rule order.trans[of "g x" "g y" t], intro mono_intros refl estimate\<close>\<close>)

end