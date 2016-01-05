(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Matrix Conversions\<close>

text \<open>Essentially, the idea is to use the JNF results to estimate the growth rates of 
  matrices. Since the results in JNF are only applicable for real normed fields,
  we cannot directly use them for matrices over the integers or the rational numbers.
  To this end, we define a homomorphism which allows us to first convert all numbers
  to real numbers, and then do the analysis.\<close>

theory Ring_Hom_Matrix
imports 
  Matrix
  Real
  Ring_Hom
begin

context semiring_hom
begin
lemma mat_hom_pow: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "mat\<^sub>h (A ^\<^sub>m k) = (mat\<^sub>h A) ^\<^sub>m k"
proof (induct k)
  case (Suc k)
  thus ?case using mat_hom_mult[OF mat_pow_closed[OF A, of k] A] by simp
qed (simp add: mat_hom_one)

lemma hom_mat_sum: "hom (mat_sum A) = mat_sum (mat\<^sub>h A)"
proof -
  obtain B where id: "?thesis = (hom (setsum (op $$ A) B) = setsum (op $$ (mat\<^sub>h A)) B)"
    and B: "B \<subseteq> {0..<dim\<^sub>r A} \<times> {0..<dim\<^sub>c A}"
  unfolding mat_sum_def by auto
  from B have "finite B" 
    using finite_subset by blast
  thus ?thesis unfolding id using B
  proof (induct B)
    case (insert x F)
    show ?case unfolding setsum.insert[OF insert(1-2)] hom_add 
      using insert(3-) by auto
  qed simp
qed
end

locale ord_ring_hom = semiring_hom hom for 
  hom :: "'a :: linordered_idom \<Rightarrow> 'b :: floor_ceiling" +
  assumes hom_le: "hom x \<le> z \<Longrightarrow> x \<le> of_int \<lceil>z\<rceil>"

text \<open>Now a class based variant especially for homomorphisms into the reals.\<close>
class real_embedding = linordered_idom + real_of +
  assumes
    real_add: "real ((x :: 'a) + y) = real x + real y" and
    real_mult: "real (x * y) = real x * real y" and
    real_zero: "real 0 = 0" and
    real_one: "real 1 = 1" and
    real_le: "real x \<le> z \<Longrightarrow> x \<le> of_int \<lceil>z\<rceil>"

interpretation real_embedding: ord_ring_hom "(real :: 'a :: real_embedding \<Rightarrow> real)"
  by (unfold_locales, rule real_add, rule real_mult, rule real_zero, rule real_one, rule real_le)

instantiation real :: real_embedding
begin
definition real_real :: "real \<Rightarrow> real" where
  "real_real x = x"

instance
  by (intro_classes, auto simp: real_real_def, linarith)
end

instance int :: real_embedding
  by (intro_classes, auto simp: real_eq_of_int, linarith)

lemma real_of_rat_ineq: assumes "real_of_rat x \<le> z"
  shows "x \<le> of_int \<lceil>z\<rceil>"
proof -
  have "z \<le> of_int \<lceil>z\<rceil>" by linarith
  from order_trans[OF assms this] 
  have "real_of_rat x \<le> real_of_rat (of_int \<lceil>z\<rceil>)" by auto
  thus "x \<le> of_int \<lceil>z\<rceil>" using of_rat_less_eq by blast
qed

instantiation rat :: real_embedding
begin
definition real_rat :: "rat \<Rightarrow> real" where
  "real_rat x = of_rat x"

instance
  by (intro_classes, auto simp: real_rat_def of_rat_add of_rat_mult real_of_rat_ineq)
end

abbreviation mat_real ("mat\<^sub>\<real>") where "mat\<^sub>\<real> \<equiv> map\<^sub>m (real :: 'a :: real_embedding \<Rightarrow> real)"


end