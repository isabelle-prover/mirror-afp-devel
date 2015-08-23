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

theory Matrix_Conversions
imports 
  Matrix
  Real
begin

locale ring_hom = 
  fixes hom :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"
  assumes 
    hom_add: "hom (x + y) = hom x + hom y" and
    hom_mult: "hom (x * y) = hom x * hom y" and
    hom_zero: "hom 0 = 0" and
    hom_one: "hom 1 = 1"
begin

abbreviation mat_hom :: "'a mat \<Rightarrow> 'b mat" ("mat\<^sub>h")
  where "mat\<^sub>h \<equiv> mat_map hom"

lemma mat_hom_one: "mat\<^sub>h (\<one>\<^sub>m n) = \<one>\<^sub>m n"
  by (rule mat_eqI, auto simp: hom_one hom_zero)

lemma mat_hom_mult: assumes A: "A \<in> carrier\<^sub>m nr n" and B: "B \<in> carrier\<^sub>m n nc"
  shows "mat\<^sub>h (A \<otimes>\<^sub>m B) = mat\<^sub>h A \<otimes>\<^sub>m mat\<^sub>h B"
proof -
  let ?L = "mat\<^sub>h (A \<otimes>\<^sub>m B)"
  let ?R = "mat\<^sub>h A \<otimes>\<^sub>m mat\<^sub>h B"
  let ?A = "mat\<^sub>h A" 
  let ?B = "mat\<^sub>h B" 
  from A B have id: 
    "dim\<^sub>r ?L = nr" "dim\<^sub>r ?R = nr" 
    "dim\<^sub>c ?L = nc" "dim\<^sub>c ?R = nc"  by auto
  show ?thesis
  proof (rule mat_eqI, unfold id)
    fix i j
    assume *: "i < nr" "j < nc"
    def I \<equiv> "{0 ..< n}"
    have id: "{0 ..< dim\<^sub>v (col ?B j)} = I" "{0 ..< dim\<^sub>v (col B j)} = I" 
      unfolding I_def using * B by auto
    have finite: "finite I" unfolding I_def by auto
    have I: "I \<subseteq> {0 ..< n}" unfolding I_def by auto
    have "?L $$ (i,j) = hom (row A i \<bullet> col B j)" using A B * by auto
    also have "\<dots> = row ?A i \<bullet> col ?B j" unfolding scalar_prod_def id using finite I
    proof (induct I)
      case empty
      show ?case by (simp add: hom_zero)
    next
      case (insert k I)
      show ?case unfolding setsum.insert[OF insert(1-2)] hom_add hom_mult
        using insert(3-) * A B by auto
    qed
    also have "\<dots> = ?R $$ (i,j)" using A B * by auto
    finally
    show "?L $$ (i, j) = ?R $$ (i, j)" .
  qed auto
qed

lemma mat_hom_pow: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "mat\<^sub>h (A ^\<^sub>m k) = (mat\<^sub>h A) ^\<^sub>m k"
proof (induct k)
  case 0 
  show ?case by (simp add: mat_hom_one)
next
  case (Suc k)
  thus ?case using mat_hom_mult[OF mat_pow_closed[OF A, of k] A] by simp
qed

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
  qed (simp add: hom_zero)
qed
end

locale ord_ring_hom = ring_hom hom for 
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

abbreviation mat_real ("mat\<^sub>\<real>") where "mat\<^sub>\<real> \<equiv> map\<^sub>m (real :: 'a :: real_embedding \<Rightarrow> real)"

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

end