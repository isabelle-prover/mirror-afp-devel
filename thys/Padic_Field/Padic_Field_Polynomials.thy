theory Padic_Field_Polynomials
  imports Padic_Fields

begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>$p$-adic Univariate Polynomials and Hensel's Lemma\<close>
(**************************************************************************************************)
(**************************************************************************************************)
type_synonym padic_field_poly = "nat \<Rightarrow> padic_number"

type_synonym padic_field_fun = "padic_number \<Rightarrow> padic_number"

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Gauss Norms of Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text \<open>
  The Gauss norm of a polynomial is defined to be the minimum valuation of a coefficient of that
  polynomial. This induces a valuation on the ring of polynomials, and in particular it satisfies
  the ultrametric inequality. In addition, the Gauss norm of a polynomial $f(x)$ gives a lower
  bound for the value $\text{val } (f(a))$ in terms of $\text{val }(a)$, for a point
  $a \in \mathbb{Q}_p$. We introduce Gauss norms here as a useful tool for stating and proving
  Hensel's Lemma for the field $\mathbb{Q}_p$. We are abusing terminology slightly in calling
  this the Gauss norm, rather than the Gauss valuation, but this is just to conform with our
  decision to work exclusively with the $p$-adic valuation and not discuss the equivalent
  real-valued $p$-adic norm. For a detailed treatment of Gauss norms one can see, for example
  \<^cite>\<open>"engler2005valued"\<close>.
\<close>
context padic_fields
begin

no_notation Zp.to_fun (infixl\<open>\<bullet>\<close> 70)

abbreviation(input) Q\<^sub>p_x where
"Q\<^sub>p_x \<equiv> UP Q\<^sub>p"

definition gauss_norm where
"gauss_norm g = Min (val ` g ` {..degree g}) "

lemma gauss_normE:
  assumes "g \<in> carrier Q\<^sub>p_x"
  shows "gauss_norm g \<le> val (g k)"
  apply(cases "k \<le> degree g")
  unfolding gauss_norm_def
  using assms apply auto[1]
proof-
  assume "\<not> k \<le> degree g"
  then have "g k = \<zero>\<^bsub>Q\<^sub>p\<^esub> "
    by (simp add: UPQ.deg_leE assms)
  then show "Min (val ` g ` {..deg Q\<^sub>p g}) \<le> val (g k)"
    by (simp add: local.val_zero)
qed

lemma gauss_norm_geqI:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>n. val (g n) \<ge> \<alpha>"
  shows "gauss_norm g \<ge> \<alpha>"
  unfolding gauss_norm_def using assms
  by simp

lemma gauss_norm_eqI:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>n. val (g n) \<ge> \<alpha>"
  assumes "val (g i) = \<alpha>"
  shows "gauss_norm g = \<alpha>"
proof-
  have 0: "gauss_norm g \<le> \<alpha>"
    using assms gauss_normE gauss_norm_def by fastforce
  have 1: "gauss_norm g \<ge> \<alpha>"
    using assms gauss_norm_geqI by auto
  show ?thesis using 0 1 by auto
qed

lemma nonzero_poly_nonzero_coeff:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "g \<noteq> \<zero>\<^bsub>Q\<^sub>p_x\<^esub>"
  shows "\<exists>k. k \<le>degree g \<and> g k \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
proof(rule ccontr)
  assume "\<not> (\<exists>k\<le>degree g. g k \<noteq> \<zero>\<^bsub>Q\<^sub>p\<^esub>)"
  then have 0: "\<And>k. g k = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
    by (meson UPQ.deg_leE assms(1) not_le_imp_less)
  then show False
    using assms  UPQ.cfs_zero by blast
qed

lemma gauss_norm_prop:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "g \<noteq> \<zero>\<^bsub>Q\<^sub>p_x\<^esub>"
  shows "gauss_norm g \<noteq> \<infinity>"
proof-
  obtain k where k_def: "k \<le>degree g \<and> g k \<noteq>\<zero>\<^bsub>Q\<^sub>p\<^esub>"
    using assms nonzero_poly_nonzero_coeff
    by blast
  then have 0: "gauss_norm g \<le> val (g k)"
    using assms(1) gauss_normE by blast
  have "g k \<in> carrier Q\<^sub>p"
    using UPQ.cfs_closed assms(1) by blast
  hence "val (g k) < \<infinity>"
    using k_def assms
    by (metis eint_ord_code(3) eint_ord_simps(4) val_ineq)
  then show ?thesis
    using 0 not_le by fastforce
qed

lemma gauss_norm_coeff_norm:
  "\<exists>n \<le> degree g. (gauss_norm g) = val (g n)"
proof-
  have "finite (val ` g ` {..deg Q\<^sub>p g})"
    by blast
  hence "\<exists>x \<in> (val ` g ` {..deg Q\<^sub>p g}). gauss_norm g = x"
  unfolding gauss_norm_def
  by auto
  thus ?thesis unfolding gauss_norm_def
    by blast
qed

lemma gauss_norm_smult_cfs:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "gauss_norm g = val (g k)"
  shows "gauss_norm (a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) = val a + val (g k)"
proof-
  obtain l where l_def: "gauss_norm (a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) =  val ((a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) l)"
    using gauss_norm_coeff_norm
    by blast
  then have "gauss_norm (a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) =  val (a \<otimes>\<^bsub>Q\<^sub>p\<^esub> (g l))"
    using assms
    by simp
  then have "gauss_norm (a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) =  val a + val (g l)"
    by (simp add: UPQ.cfs_closed assms(1) assms(2) val_mult)
  then have 0: "gauss_norm (a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) \<le> val a +val (g k)"
    using assms  gauss_normE[of g l]
    by (metis UPQ.UP_smult_closed UPQ.cfs_closed UPQ.cfs_smult gauss_normE val_mult)
  have "val a + val (g k) = val ((a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) k)"
    by (simp add: UPQ.cfs_closed assms(1) assms(2) val_mult)
  then have "gauss_norm (a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) \<ge> val a + val (g k)"
    by (metis \<open>gauss_norm (a \<odot>\<^bsub>UP Q\<^sub>p\<^esub> g) = val a + val (g l)\<close> add_left_mono assms(1) assms(3) gauss_normE)
  then show ?thesis
    using 0  by auto
qed

lemma gauss_norm_smult:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "a \<in> carrier Q\<^sub>p"
  shows "gauss_norm (a \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g) = val a + gauss_norm g"
  using gauss_norm_smult_cfs[of g a] gauss_norm_coeff_norm[of g] assms
  by metis

lemma gauss_norm_ultrametric:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "h \<in> carrier Q\<^sub>p_x"
  shows "gauss_norm (g \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> h) \<ge> min (gauss_norm g) (gauss_norm h)"
proof-
  obtain k where "gauss_norm (g \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> h) = val ((g \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> h) k)"
    using gauss_norm_coeff_norm
    by blast
  then have 0: "gauss_norm (g \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> h) = val (g k \<oplus>\<^bsub>Q\<^sub>p\<^esub> h k)"
    by (simp add: assms(1) assms(2))
  have "min (val (g k)) (val (h k))\<ge> min (gauss_norm g) (gauss_norm h)"
    using gauss_normE[of g k] gauss_normE[of h k]  assms(1) assms(2) min.mono
    by blast
  then show ?thesis
    using 0 val_ultrametric[of "g k" "h k"] assms(1) assms(2) dual_order.trans
    by (metis (no_types, lifting) UPQ.cfs_closed)
qed

lemma gauss_norm_a_inv:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  shows "gauss_norm (\<ominus>\<^bsub>UP Q\<^sub>p\<^esub>f) = gauss_norm f"
proof-
  have 0: "\<And>n. ((\<ominus>\<^bsub>UP Q\<^sub>p\<^esub>f) n) = \<ominus> (f n)"
    using assms by simp
  have 1: "\<And>n. val ((\<ominus>\<^bsub>UP Q\<^sub>p\<^esub>f) n) = val (f n)"
    using 0 assms UPQ.UP_car_memE(1) val_minus by presburger
  obtain i where i_def: "gauss_norm f = val (f i)"
    using assms gauss_norm_coeff_norm by blast
  have 2: "\<And>k. val ((\<ominus>\<^bsub>UP Q\<^sub>p\<^esub>f) k) \<ge> val (f i)"
    unfolding 1
    using i_def assms gauss_normE by fastforce
  show ?thesis
    apply(rule gauss_norm_eqI[of _ _ i])
      apply (simp add: assms; fail)
    unfolding 1 using assms gauss_normE apply blast
    unfolding i_def by blast
qed

lemma gauss_norm_ultrametric':
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  shows "gauss_norm (f \<ominus>\<^bsub>UP Q\<^sub>p\<^esub> g) \<ge> min (gauss_norm f) (gauss_norm g)"
  unfolding a_minus_def
  using assms gauss_norm_a_inv[of g] gauss_norm_ultrametric
  by (metis UPQ.UP_a_inv_closed)

lemma gauss_norm_finsum:
  assumes "f \<in> A \<rightarrow> carrier Q\<^sub>p_x"
  assumes "finite A"
  assumes "A \<noteq> {}"
  shows " gauss_norm (\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i) \<ge> Min (gauss_norm ` (f`A))"
proof-
  obtain k where k_def: "val ((\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i) k) = gauss_norm (\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i)"
    by (metis gauss_norm_coeff_norm)
  then have 0: "val (\<Oplus>\<^bsub>Q\<^sub>p\<^esub>i\<in>A. f i k) \<ge> Min (val ` (\<lambda> i. f i k) ` A)"
    using finsum_val_ultrametric[of "\<lambda> i. f i k" A] assms
    by (simp add: \<open>\<lbrakk>(\<lambda>i. f i k) \<in> A \<rightarrow> carrier Q\<^sub>p; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> Min (val ` (\<lambda>i. f i k) ` A) \<le> val (\<Oplus>i\<in>A. f i k)\<close> Pi_iff UPQ.cfs_closed)
  have "(\<And>a. a \<in> A \<Longrightarrow> (val \<circ> (\<lambda>i. f i k)) a \<ge> gauss_norm (f a))"
    using gauss_normE assms
    by (metis (no_types, lifting) Pi_split_insert_domain Set.set_insert comp_apply)
  then have "Min (val ` (\<lambda> i. f i k) ` A) \<ge> Min ((\<lambda> i. gauss_norm (f  i)) ` A)"
    using Min_mono'[of A]
    by (simp add: assms(2) image_comp)
  then have 1: "Min (val ` (\<lambda> i. f i k) ` A) \<ge> Min (gauss_norm ` f ` A)"
    by (metis image_image)
  have "f \<in> A \<rightarrow> carrier (UP Q\<^sub>p) \<longrightarrow> ((\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i) \<in> carrier Q\<^sub>p_x \<and> ((\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i) k) = (\<Oplus>\<^bsub>Q\<^sub>p\<^esub>i\<in>A. f i k)) "
    apply(rule finite.induct[of A])
      apply (simp add: assms(2); fail)
     apply (metis (no_types, lifting) Pi_I Qp.add.finprod_one_eqI UPQ.P.finsum_closed UPQ.P.finsum_empty UPQ.cfs_zero empty_iff)
  proof-
    fix a A assume A: "finite A" "f \<in> A \<rightarrow> carrier (UP Q\<^sub>p) \<longrightarrow> ( finsum (UP Q\<^sub>p) f A \<in> carrier (UP Q\<^sub>p) \<and> finsum (UP Q\<^sub>p) f A k = (\<Oplus>i\<in>A. f i k)) "
    show " f \<in> insert a A \<rightarrow> carrier (UP Q\<^sub>p) \<longrightarrow>  finsum (UP Q\<^sub>p) f (insert a A) \<in> carrier (UP Q\<^sub>p) \<and> finsum (UP Q\<^sub>p) f (insert a A) k = (\<Oplus>i\<in>insert a A. f i k)"
      apply(cases "a \<in> A")
      using A
      apply (simp add: insert_absorb; fail)
    proof assume B: "a \<notin> A" " f \<in> insert a A \<rightarrow> carrier (UP Q\<^sub>p)"
      then have f_a: "f a \<in> carrier (UP Q\<^sub>p)"
        by blast
      have f_A: "f \<in> A \<rightarrow> carrier (UP Q\<^sub>p)"
        using B by blast
      have "finsum (UP Q\<^sub>p) f (insert a A) = f a \<oplus>\<^bsub>UP Q\<^sub>p\<^esub>finsum (UP Q\<^sub>p) f A"
        using assms A B f_a f_A  finsum_insert by simp
      then have 0: "finsum (UP Q\<^sub>p) f (insert a A) k = f a k \<oplus>\<^bsub>Q\<^sub>p\<^esub> (finsum (UP Q\<^sub>p) f A) k"
        using f_a f_A A B
        by simp
      have " ( \<lambda> a. f a k) \<in> A \<rightarrow> carrier Q\<^sub>p"
      proof fix a assume "a \<in> A"
        then have "f a \<in> carrier (UP Q\<^sub>p)"
          using f_A by blast
        then show "f a k \<in> carrier Q\<^sub>p"
          using A cfs_closed by blast
      qed
      then have 0: "finsum (UP Q\<^sub>p) f (insert a A) k = (\<Oplus>i\<in>insert a A. f i k)"
        using A B Qp.finsum_insert[of A a "\<lambda> a. f a k"]
        by (simp add: UPQ.cfs_closed)
      thus " finsum (UP Q\<^sub>p) f (insert a A) \<in> carrier (UP Q\<^sub>p) \<and> finsum (UP Q\<^sub>p) f (insert a A) k = (\<Oplus>i\<in>insert a A. f i k)"
        using B(2) UPQ.P.finsum_closed by blast
    qed
  qed
  then have "(\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i) \<in> carrier Q\<^sub>p_x \<and> ((\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i) k) = (\<Oplus>\<^bsub>Q\<^sub>p\<^esub>i\<in>A. f i k)"
    using assms by blast
  hence 3: "gauss_norm (\<Oplus>\<^bsub>Q\<^sub>p_x\<^esub>i\<in>A. f i) \<ge> Min (val ` (\<lambda> i. f i k) ` A)"
    using 0  k_def by auto
  thus ?thesis
    using 1 le_trans by auto
qed

lemma gauss_norm_monom:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "gauss_norm (monom Q\<^sub>p_x a n) = val a"
proof-
  have "val ((monom Q\<^sub>p_x a n) n) \<ge> gauss_norm (monom Q\<^sub>p_x a n)"
    using assms gauss_normE[of "monom Q\<^sub>p_x a n" n] UPQ.monom_closed
    by blast
  then show ?thesis
    using gauss_norm_coeff_norm[of "monom Q\<^sub>p_x a n"] assms val_ineq UPQ.cfs_monom by fastforce
qed

lemma val_val_ring_prod:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "val (a \<otimes>\<^bsub>Q\<^sub>p\<^esub> b) \<ge> val b"
proof-
  have 0: "val (a \<otimes>\<^bsub>Q\<^sub>p\<^esub> b) = val a + val b"
    using assms val_ring_memE[of a] val_mult
    by blast
  have 1: " val a \<ge> 0"
    using assms
    by (simp add: val_ring_memE)
  then show ?thesis
    using assms 0
    by simp
qed

lemma val_val_ring_prod':
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "val (b \<otimes>\<^bsub>Q\<^sub>p\<^esub> a) \<ge> val b"
  using val_val_ring_prod[of a b]
  by (simp add: Qp.m_comm val_ring_memE assms(1) assms(2))

lemma val_ring_nat_pow_closed:
  assumes "a \<in> \<O>\<^sub>p"
  shows "(a[^](n::nat)) \<in> \<O>\<^sub>p"
  apply(induction n)
  apply auto[1]
  using Qp.inv_one Z\<^sub>p_mem apply blast
  by (metis Qp.nat_pow_Suc Qp.nat_pow_closed val_ring_memE assms image_eqI inc_of_prod to_Zp_closed to_Zp_inc to_Zp_mult)

lemma val_ringI:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<ge>0"
  shows " a \<in> \<O>\<^sub>p"
  apply(rule val_ring_val_criterion)
  using assms by auto

notation UPQ.to_fun (infixl\<open>\<bullet>\<close> 70)

lemma val_gauss_norm_eval:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "a \<in> \<O>\<^sub>p"
  shows "val (g \<bullet> a) \<ge> gauss_norm g"
proof-
  have 0: "g\<bullet>a = (\<Oplus>\<^bsub>Q\<^sub>p\<^esub>i\<in>{..degree g}. (g i)\<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i))"
    using val_ring_memE assms to_fun_formula[of g a] by auto

  have 1: "(\<lambda>i. g i \<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i)) \<in> {..degree g} \<rightarrow> carrier Q\<^sub>p"
     using assms
    by (meson Pi_I val_ring_memE cfs_closed monom_term_car)
  then have 2: "val (g\<bullet>a) \<ge> Min (val ` (\<lambda> i. ((g i)\<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i))) ` {..degree g})"
    using 0 finsum_val_ultrametric[of "\<lambda> i. ((g i)\<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i))" "{..degree g}" ]
    by (metis finite_atMost not_empty_eq_Iic_eq_empty)
  have 3: "\<And> i. val ((g i)\<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i)) = val (g i) + val (a[^]i)"
    using assms val_mult
    by (simp add: val_ring_memE UPQ.cfs_closed)
  have 4: "\<And> i. val ((g i)\<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i)) \<ge> val (g i)"
  proof-
    fix i
    show "val ((g i)\<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i)) \<ge> val (g i)"
      using val_val_ring_prod'[of "a[^]i" "g i" ]
        assms(1) assms(2) val_ring_nat_pow_closed cfs_closed
      by simp
  qed
  have "Min (val ` (\<lambda>i. g i \<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i)) ` {..degree g}) \<ge> Min ((\<lambda>i. val (g i)) ` {..degree g})"
    using Min_mono'[of "{..degree g}" "\<lambda>i. val (g i)" "\<lambda>i. val (g i \<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i))" ] 4 2
    by (metis finite_atMost image_image)
  then have "Min (val ` (\<lambda>i. g i \<otimes>\<^bsub>Q\<^sub>p\<^esub> (a[^]i)) ` {..degree g}) \<ge> Min (val ` g ` {..degree g})"
    by (metis  image_image)
  then have  "val (g\<bullet>a) \<ge> Min (val ` g ` {..degree g})"
    using 2
    by (meson atMost_iff atMost_subset_iff in_mono)
  then show ?thesis
    by (simp add: \<open>val (g\<bullet>a) \<ge> Min (val ` g ` {..degree g})\<close> gauss_norm_def)
qed

lemma positive_gauss_norm_eval:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "gauss_norm g \<ge> 0"
  assumes "a \<in> \<O>\<^sub>p"
  shows "(g\<bullet>a) \<in> \<O>\<^sub>p"
  apply(rule val_ring_val_criterion[of "g\<bullet>a"])
  using assms val_ring_memE
  using UPQ.to_fun_closed apply blast
  using assms val_gauss_norm_eval[of g a] by auto

lemma positive_gauss_norm_valuation_ring_coeffs:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "gauss_norm g \<ge> 0"
  shows "g n \<in> \<O>\<^sub>p"
  apply(rule val_ringI)
  using cfs_closed assms(1) apply blast
  using gauss_normE[of g n] assms by auto

lemma val_ring_cfs_imp_nonneg_gauss_norm:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>n. g n \<in> \<O>\<^sub>p"
  shows "gauss_norm g \<ge> 0"
  by(rule gauss_norm_geqI, rule assms, rule val_ring_memE, rule assms)

lemma val_of_add_pow:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "val ([(n::nat)]\<cdot>a) \<ge> val a"
proof-
  have 0: "[(n::nat)]\<cdot>a = ([n]\<cdot>\<one>)\<otimes>a"
    using assms Qp.add_pow_ldistr Qp.cring_simprules(12) Qp.one_closed by presburger
  have 1: "val ([(n::nat)]\<cdot>a) = val ([n]\<cdot>\<one>) + val a"
    unfolding 0 by(rule val_mult, simp, rule assms)
  show ?thesis unfolding 1 using assms
    by (simp add: val_of_nat_inc)
qed

lemma gauss_norm_pderiv:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  shows "gauss_norm g \<le> gauss_norm (pderiv g)"
  apply(rule gauss_norm_geqI)
  using UPQ.pderiv_closed assms apply blast
  using gauss_normE pderiv_cfs val_of_add_pow
  by (smt UPQ.cfs_closed assms dual_order.trans)

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Mapping Polynomials with Value Ring Coefficients to Polynomials over $\mathbb{Z}_p$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition to_Zp_poly where
"to_Zp_poly g = (\<lambda>n. to_Zp (g n))"

lemma to_Zp_poly_closed:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "gauss_norm g \<ge> 0"
  shows "to_Zp_poly g \<in> carrier (UP Z\<^sub>p)"
proof-
  have  "to_Zp_poly g \<in> up Z\<^sub>p"
    apply(rule mem_upI)
   unfolding to_Zp_poly_def
   using cfs_closed[of g ] assms(1) to_Zp_closed[of ]  apply blast
  proof-
    have "\<exists>n. bound \<zero>\<^bsub>Q\<^sub>p\<^esub> n g"
     using UPQ.deg_leE assms(1) by auto
    then obtain n where n_def: " bound \<zero>\<^bsub>Q\<^sub>p\<^esub> n g"
      by blast
    then have " bound \<zero>\<^bsub>Z\<^sub>p\<^esub> n (\<lambda>n. to_Zp (g n))"
      unfolding bound_def
      by (simp add: to_Zp_zero)
    then show "\<exists>n. bound \<zero>\<^bsub>Z\<^sub>p\<^esub> n (\<lambda>n. to_Zp (g n))"
      by blast
  qed
  then show ?thesis using UP_def[of Z\<^sub>p]
    by simp
qed

definition poly_inc where
"poly_inc g = (\<lambda>n::nat. \<iota> (g n))"

lemma poly_inc_closed:
  assumes "g \<in> carrier (UP Z\<^sub>p)"
  shows "poly_inc g \<in> carrier Q\<^sub>p_x"
proof-
  have "poly_inc g \<in> up Q\<^sub>p"
  proof(rule mem_upI)
    show "\<And>n. poly_inc g n \<in> carrier Q\<^sub>p"
    proof- fix n
      have "g n \<in> carrier Z\<^sub>p"
        using assms UP_def
        by (simp add: UP_def mem_upD)
      then show "poly_inc g n \<in> carrier Q\<^sub>p"
        using assms poly_inc_def[of g] inc_def[of "g n" ] inc_closed
        by force
    qed
    show "\<exists>n. bound \<zero>\<^bsub>Q\<^sub>p\<^esub> n (poly_inc g)"
    proof-
      obtain n where n_def: " bound \<zero>\<^bsub>Z\<^sub>p\<^esub> n g"
        using assms  bound_def[of "\<zero>\<^bsub>Z\<^sub>p\<^esub>" _ g]Zp.cring_axioms UP_cring.deg_leE[of Z\<^sub>p g]
        unfolding UP_cring_def
        by metis
      then have " bound \<zero>\<^bsub>Q\<^sub>p\<^esub> n (poly_inc g)"
        unfolding poly_inc_def bound_def
        by (metis Qp.nat_inc_zero Zp.nat_inc_zero inc_of_nat)
      then show ?thesis by blast
    qed
  qed
  then show ?thesis
    by (simp add: \<open>poly_inc g \<in> up Q\<^sub>p\<close> UP_def)
qed

lemma poly_inc_inverse_right:
  assumes "g \<in> carrier (UP Z\<^sub>p)"
  shows "to_Zp_poly (poly_inc g) = g"
proof-
  have 0: "\<And>n. g n \<in> carrier Z\<^sub>p"
    by (simp add: Zp.cfs_closed assms)
  show ?thesis
    unfolding to_Zp_poly_def poly_inc_def
  proof
    fix n
    show "to_Zp (\<iota> (g n)) = g n"
      using 0 inc_to_Zp
      by auto
  qed
qed

lemma poly_inc_inverse_left:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "gauss_norm g \<ge>0"
  shows "poly_inc (to_Zp_poly g) = g"
proof
  fix x
  show "poly_inc (to_Zp_poly g) x = g x"
    using assms unfolding poly_inc_def to_Zp_poly_def
    by (simp add: positive_gauss_norm_valuation_ring_coeffs to_Zp_inc)
qed

lemma poly_inc_plus:
  assumes "f \<in> carrier (UP Z\<^sub>p)"
  assumes "g \<in> carrier (UP Z\<^sub>p)"
  shows "poly_inc (f \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> g) = poly_inc f \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc g"
proof
  fix n
  have 0: "poly_inc (f \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> g) n = \<iota> (f n \<oplus>\<^bsub>Z\<^sub>p\<^esub> g n)"
    unfolding poly_inc_def using assms by auto
  have 1: "(poly_inc f \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc g) n = poly_inc f n \<oplus> poly_inc g n"
    by(rule cfs_add, rule poly_inc_closed, rule assms, rule poly_inc_closed, rule assms)
  show "poly_inc (f \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> g) n = (poly_inc f \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc g) n"
    unfolding 0 1 unfolding poly_inc_def
    apply(rule inc_of_sum)
    using assms apply (simp add: Zp.cfs_closed; fail)
        using assms by (simp add: Zp.cfs_closed)
qed

lemma poly_inc_monom:
  assumes "a \<in> carrier Z\<^sub>p"
  shows "poly_inc (monom (UP Z\<^sub>p) a m) = monom (UP Q\<^sub>p) (\<iota> a) m"
proof fix n
  show "poly_inc (monom (UP Z\<^sub>p) a m) n = monom (UP Q\<^sub>p) (\<iota> a) m n"
    apply(cases "m = n")
    using assms cfs_monom[of "\<iota> a"] Zp.cfs_monom[of a] unfolding poly_inc_def
     apply (simp add: inc_closed; fail)
    using assms cfs_monom[of "\<iota> a"] Zp.cfs_monom[of a] unfolding poly_inc_def
    by (metis Qp.nat_mult_zero Zp_nat_inc_zero inc_closed inc_of_nat)
qed

lemma poly_inc_times:
  assumes "f \<in> carrier (UP Z\<^sub>p)"
  assumes "g \<in> carrier (UP Z\<^sub>p)"
  shows "poly_inc (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> g) = poly_inc f \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc g"
  apply(rule UP_ring.poly_induct3[of Z\<^sub>p])
  apply (simp add: Zp.is_UP_ring; fail)
  using assms apply blast
proof-
  fix p q
  assume A: "q \<in> carrier (UP Z\<^sub>p)"  "p \<in> carrier (UP Z\<^sub>p)"
            "poly_inc (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> p) = poly_inc f \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc p"
            "poly_inc (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> q) = poly_inc f \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc q"
  have 0: "(f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> (p \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> q)) = (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> p) \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> q)"
    using assms(1) A
    by (simp add: Zp.P.r_distr)
  have 1: "poly_inc (p \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> q) = poly_inc p \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc q"
    by(rule poly_inc_plus, rule A, rule A)
  show "poly_inc (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> (p \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> q)) = poly_inc f \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc (p \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> q)"
    unfolding 0 1 using A poly_inc_closed poly_inc_plus
    by (simp add: UPQ.P.r_distr assms(1))
next
  fix a fix n::nat
  assume A: "a \<in> carrier Z\<^sub>p"
  show "poly_inc (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> monom (UP Z\<^sub>p) a n) =
           poly_inc f \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc (monom (UP Z\<^sub>p) a n)"
  proof
    fix m
    show "poly_inc (f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> monom (UP Z\<^sub>p) a n) m =
         (poly_inc f \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc (monom (UP Z\<^sub>p) a n)) m"
    proof(cases "m < n")
      case True
      have T0: "(f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> monom (UP Z\<^sub>p) a n) m = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
        using True Zp.cfs_monom_mult[of f a m n] A assms
        by blast
      have T1: "poly_inc (monom (UP Z\<^sub>p) a n) =  (monom (UP Q\<^sub>p) (\<iota> a) n)"
        by(rule poly_inc_monom , rule A)
      show ?thesis
        unfolding T0 T1 using True
        by (metis A Q\<^sub>p_def T0 UPQ.cfs_monom_mult Zp_def assms(1) inc_closed padic_fields.to_Zp_zero padic_fields_axioms poly_inc_closed poly_inc_def to_Zp_inc zero_in_val_ring)
    next
      case False
      then have F0: "m \<ge> n"
        using False by simp
      have F1: "(f \<otimes>\<^bsub>UP Z\<^sub>p\<^esub> monom (UP Z\<^sub>p) a n) m = a \<otimes>\<^bsub>Z\<^sub>p\<^esub> f (m - n)"
        using Zp.cfs_monom_mult_l' F0 A assms by simp
      have F2: "poly_inc (monom (UP Z\<^sub>p) a n)  = monom (UP Q\<^sub>p) (\<iota> a) n "
        by(rule poly_inc_monom, rule A)
      have F3: "(poly_inc f \<otimes>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc (monom (UP Z\<^sub>p) a n)) m
                = (\<iota> a) \<otimes> (poly_inc f (m -n))"
        using UPQ.cfs_monom_mult_l' F0 A assms poly_inc_closed
        by (simp add: F2 inc_closed)
      show ?thesis
        unfolding F3 unfolding poly_inc_def F1
        apply(rule inc_of_prod, rule A)
        using assms Zp.cfs_closed by blast
    qed
  qed
qed

lemma poly_inc_one:
"poly_inc (\<one>\<^bsub>UP Z\<^sub>p\<^esub>) = \<one>\<^bsub>UP Q\<^sub>p\<^esub>"
apply(rule ext)
  unfolding poly_inc_def
  using inc_of_one inc_of_zero
  by simp

lemma poly_inc_zero:
"poly_inc (\<zero>\<^bsub>UP Z\<^sub>p\<^esub>) = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
apply(rule ext)
  unfolding poly_inc_def
  using inc_of_one inc_of_zero
  by simp

lemma poly_inc_hom:
"poly_inc \<in> ring_hom (UP Z\<^sub>p) (UP Q\<^sub>p)"
  apply(rule ring_hom_memI)
     apply(rule poly_inc_closed, blast)
    apply(rule poly_inc_times, blast, blast)
   apply(rule poly_inc_plus, blast, blast)
  by(rule poly_inc_one)

lemma poly_inc_as_poly_lift_hom:
  assumes "f \<in> carrier (UP Z\<^sub>p)"
  shows "poly_inc f = poly_lift_hom Z\<^sub>p Q\<^sub>p \<iota> f"
  apply(rule ext)
  unfolding poly_inc_def
  using Zp.poly_lift_hom_cf[of Q\<^sub>p \<iota> f] assms UPQ.R_cring local.inc_is_hom
  by blast

lemma poly_inc_eval:
  assumes "g \<in> carrier (UP Z\<^sub>p)"
  assumes "a \<in> carrier Z\<^sub>p"
  shows "to_function Q\<^sub>p (poly_inc g) (\<iota> a) = \<iota> (to_function Z\<^sub>p g a)"
proof-
  have 0: "poly_inc g = poly_lift_hom Z\<^sub>p Q\<^sub>p \<iota> g"
    using assms poly_inc_as_poly_lift_hom[of g] by blast
  have 1: "to_function Q\<^sub>p (poly_lift_hom Z\<^sub>p Q\<^sub>p \<iota> g) (\<iota> a) = \<iota> (to_function Z\<^sub>p g a)"
    using Zp.poly_lift_hom_eval[of Q\<^sub>p \<iota> g a] assms inc_is_hom
    unfolding to_fun_def Zp.to_fun_def
    using UPQ.R_cring by blast
  show ?thesis unfolding 0 1
    by blast
qed

lemma val_ring_poly_eval:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And> i. f i \<in> \<O>\<^sub>p"
  shows "\<And>x. x \<in> \<O>\<^sub>p \<Longrightarrow> f \<bullet> x \<in> \<O>\<^sub>p"
  apply(rule positive_gauss_norm_eval, rule assms)
  apply(rule val_ring_cfs_imp_nonneg_gauss_norm)
  using assms by auto

lemma Zp_res_of_pow:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a n = b n"
  shows "(a[^]\<^bsub>Z\<^sub>p\<^esub>(k::nat)) n = (b[^]\<^bsub>Z\<^sub>p\<^esub>(k::nat)) n"
  apply(induction k)
  using assms Group.nat_pow_0 to_Zp_one apply metis
  using Zp.geometric_series_id[of a b] Zp_residue_mult_zero(1) assms(1) assms(2) assms(3)
    pow_closed res_diff_zero_fact'' res_diff_zero_fact(1) by metis

lemma to_Zp_nat_pow:
  assumes "a \<in> \<O>\<^sub>p"
  shows "to_Zp (a[^](n::nat)) = (to_Zp a)[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)"
  apply(induction n)
  using assms Group.nat_pow_0 to_Zp_one apply metis
  using assms to_Zp_mult[of a] Qp.m_comm Qp.nat_pow_Suc val_ring_memE pow_suc to_Zp_closed val_ring_nat_pow_closed
  by metis

lemma  to_Zp_res_of_pow:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "to_Zp a n = to_Zp b n"
  shows "to_Zp (a[^](k::nat)) n = to_Zp (b[^](k::nat)) n"
  using assms val_ring_memE Zp_res_of_pow to_Zp_closed to_Zp_nat_pow by presburger

lemma poly_eval_cong:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>i. g i \<in> \<O>\<^sub>p"
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "to_Zp a k = to_Zp b k"
  shows "to_Zp (g \<bullet> a) k = to_Zp (g \<bullet> b) k"
proof-
  have "(\<forall>i. g i \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (g \<bullet> a) k = to_Zp (g \<bullet> b) k"
  proof(rule UPQ.poly_induct[of g])
    show " g \<in> carrier (UP Q\<^sub>p)"
      using assms by blast
    show "\<And>p. p \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p p = 0 \<Longrightarrow> (\<forall>i. p i \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (p \<bullet> a) k = to_Zp (p \<bullet> b) k"
    proof fix p assume A: "p \<in> carrier (UP Q\<^sub>p)" "deg Q\<^sub>p p = 0" "\<forall>i. p i \<in> \<O>\<^sub>p"
      obtain c where c_def: "c \<in> carrier Q\<^sub>p \<and> p = up_ring.monom (UP Q\<^sub>p) c 0"
        using A
        by (metis UPQ.zcf_degree_zero UPQ.cfs_closed UPQ.trms_of_deg_leq_0 UPQ.trms_of_deg_leq_degree_f)
      have p_eq: "p = up_ring.monom (UP Q\<^sub>p) c 0"
        using c_def by blast
      have p_cfs: "p 0 = c"
        unfolding p_eq using c_def UP_ring.cfs_monom[of Q\<^sub>p c 0 0] UPQ.P_is_UP_ring by presburger
      have c_closed: "c \<in> \<O>\<^sub>p"
        using p_cfs A(3) by blast
      have 0: "(p \<bullet> a) = c"
        unfolding p_eq using c_def assms by (meson UPQ.to_fun_const val_ring_memE(2))
      have 1: "(p \<bullet> b) = c"
        unfolding p_eq using c_def assms UPQ.to_fun_const val_ring_memE(2) by presburger
      show " to_Zp (p \<bullet> a) k = to_Zp (p \<bullet> b) k"
        unfolding 0 1 by blast
    qed
    show "\<And>p. (\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow> (\<forall>i. q i \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (q \<bullet> a) k = to_Zp (q \<bullet> b) k) \<Longrightarrow>
         p \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> 0 < deg Q\<^sub>p p \<Longrightarrow> (\<forall>i. p i \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (p \<bullet> a) k = to_Zp (p \<bullet> b) k"
    proof
      fix p assume A: "(\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow> (\<forall>i. q i \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (q \<bullet> a) k = to_Zp (q \<bullet> b) k)"
                      "p \<in> carrier (UP Q\<^sub>p)" "0 < deg Q\<^sub>p p " " \<forall>i. p i \<in> \<O>\<^sub>p"
      obtain q where q_def: "q \<in> carrier (UP Q\<^sub>p) \<and> deg Q\<^sub>p q < deg Q\<^sub>p p \<and> p = UPQ.ltrm p \<oplus>\<^bsub>UP Q\<^sub>p\<^esub>q"
        by (metis A(2) A(3) UPQ.ltrm_closed UPQ.ltrm_decomp UPQ.UP_a_comm)
      have 0: "\<And>i.  p i = q i \<oplus> UPQ.ltrm p i"
        using q_def A
        by (metis Qp.a_ac(2) UPQ.ltrm_closed UPQ.UP_car_memE(1) UPQ.cfs_add)
      have 1: "\<forall>i. q i \<in> \<O>\<^sub>p"
      proof fix i
        show "q i \<in> \<O>\<^sub>p"
          apply(cases "i < deg Q\<^sub>p p")
          using 0[of i] A(4) A(2) q_def
          using UPQ.ltrm_closed UPQ.P.a_ac(2) UPQ.trunc_cfs UPQ.trunc_closed UPQ.trunc_simps(1)
           apply (metis Qp.r_zero UPQ.ltrm_cfs UPQ.cfs_closed UPQ.deg_leE)
          using q_def
          by (metis (no_types, opaque_lifting) A(2) A(4) UPQ.P.add.m_closed UPQ.coeff_of_sum_diff_degree0 UPQ.deg_leE UPQ.equal_deg_sum UPQ.equal_deg_sum' \<open>\<And>thesis. (\<And>q. q \<in> carrier (UP Q\<^sub>p) \<and> deg Q\<^sub>p q < deg Q\<^sub>p p \<and> p = up_ring.monom (UP Q\<^sub>p) (p (deg Q\<^sub>p p)) (deg Q\<^sub>p p) \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> q \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> lessI linorder_neqE_nat)
      qed
      have 2: "UPQ.lcf p \<in> \<O>\<^sub>p"
        using A(4) by blast
      have 3: "UPQ.ltrm p \<bullet> a = UPQ.lcf p \<otimes> a[^] deg Q\<^sub>p p"
        apply(rule UP_cring.to_fun_monom) unfolding UP_cring_def
          apply (simp add: UPQ.R_cring)
         apply (simp add: A(2) UPQ.cfs_closed)
        using assms(3) val_ring_memE(2) by blast
      have 4: "UPQ.ltrm p \<bullet> b = UPQ.lcf p \<otimes> b[^] deg Q\<^sub>p p"
        apply(rule UP_cring.to_fun_monom) unfolding UP_cring_def
          apply (simp add: UPQ.R_cring)
         apply (simp add: A(2) UPQ.cfs_closed)
        using assms val_ring_memE(2) by blast
      have p_eq: "p = q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> UPQ.ltrm p"
        using q_def by (metis A(2) UPQ.ltrm_closed UPQ.UP_a_comm)
      have 5: "p \<bullet> a = q \<bullet> a \<oplus>  UPQ.lcf p \<otimes> a[^] deg Q\<^sub>p p"
        using assms val_ring_memE(2) p_eq q_def UPQ.to_fun_plus[of q "UPQ.ltrm p" a]
        by (metis "3" A(2) UPQ.ltrm_closed UPQ.to_fun_plus)
      have 6: "p \<bullet> b = q \<bullet> b \<oplus>  UPQ.lcf p \<otimes> b[^] deg Q\<^sub>p p"
        using assms val_ring_memE(2) p_eq q_def UPQ.to_fun_plus[of q "UPQ.ltrm p" a]
        by (metis "4" A(2) UPQ.ltrm_closed UPQ.to_fun_plus)
      have 7: "UPQ.lcf p \<otimes> b[^] deg Q\<^sub>p p \<in> \<O>\<^sub>p"
        apply(rule val_ring_times_closed)
        using "2" apply linarith
        by(rule val_ring_nat_pow_closed, rule assms)
      have 8: "UPQ.lcf p \<otimes> a[^] deg Q\<^sub>p p \<in> \<O>\<^sub>p"
        apply(rule val_ring_times_closed)
        using "2" apply linarith
        by(rule val_ring_nat_pow_closed, rule assms)
      have 9: "q \<bullet> a \<in> \<O>\<^sub>p"
        using q_def 1 assms(3) val_ring_poly_eval by blast
      have 10: "q \<bullet> b \<in> \<O>\<^sub>p"
        using q_def 1 assms(4) val_ring_poly_eval by blast
      have 11: "to_Zp (p \<bullet> a) = to_Zp (q \<bullet> a) \<oplus>\<^bsub>Z\<^sub>p\<^esub> to_Zp (UPQ.ltrm p \<bullet> a)"
        using 5 8 9 to_Zp_add 3 by presburger
      have 12: "to_Zp (p \<bullet> b) = to_Zp (q \<bullet> b) \<oplus>\<^bsub>Z\<^sub>p\<^esub> to_Zp (UPQ.ltrm p \<bullet> b)"
        using 6 10 7 to_Zp_add 4  by presburger
      have 13: "to_Zp (p \<bullet> a) k = to_Zp (q \<bullet> a) k \<oplus>\<^bsub>Zp_res_ring k\<^esub> to_Zp (UPQ.ltrm p \<bullet> a) k"
        unfolding 11 using residue_of_sum by blast
      have 14: "to_Zp (p \<bullet> b) k = to_Zp (q \<bullet> b) k \<oplus>\<^bsub>Zp_res_ring k\<^esub> to_Zp (UPQ.ltrm p \<bullet> b) k"
        unfolding 12 using residue_of_sum by blast
      have 15: "to_Zp (UPQ.ltrm p \<bullet> a) k = to_Zp (UPQ.ltrm p \<bullet> b) k"
      proof(cases "k = 0")
        case True
        have T0: "to_Zp (UPQ.ltrm p \<bullet> a) \<in> carrier Z\<^sub>p"
          unfolding 3 using 8  to_Zp_closed val_ring_memE(2) by blast
        have T1: "to_Zp (UPQ.ltrm p \<bullet> b) \<in> carrier Z\<^sub>p"
          unfolding 4 using 7 to_Zp_closed val_ring_memE(2) by blast
        show ?thesis unfolding True using T0 T1 padic_integers.p_res_ring_0
          by (metis p_res_ring_0' residues_closed)
      next
        case False
        have k_pos: "k > 0"
          using False by presburger
        have 150: "to_Zp (p (deg Q\<^sub>p p) \<otimes> a [^] deg Q\<^sub>p p) = to_Zp (p (deg Q\<^sub>p p)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp( a [^] deg Q\<^sub>p p)"
         apply(rule to_Zp_mult)
          using "2" apply blast
         by(rule val_ring_nat_pow_closed, rule assms)
        have 151: "to_Zp (p (deg Q\<^sub>p p) \<otimes> b [^] deg Q\<^sub>p p) = to_Zp (p (deg Q\<^sub>p p)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp( b [^] deg Q\<^sub>p p)"
         apply(rule to_Zp_mult)
          using "2" apply blast
         by(rule val_ring_nat_pow_closed, rule assms)
       have 152: "to_Zp (p (deg Q\<^sub>p p) \<otimes> a [^] deg Q\<^sub>p p) k = to_Zp (p (deg Q\<^sub>p p)) k \<otimes>\<^bsub>Zp_res_ring k\<^esub> to_Zp( a [^] deg Q\<^sub>p p) k"
         unfolding 150 using residue_of_prod by blast
       have 153: "to_Zp (p (deg Q\<^sub>p p) \<otimes> b [^] deg Q\<^sub>p p) k = to_Zp (p (deg Q\<^sub>p p)) k \<otimes>\<^bsub>Zp_res_ring k\<^esub> to_Zp( b [^] deg Q\<^sub>p p) k"
         unfolding 151 using residue_of_prod by blast
       have 154: "to_Zp( a [^] deg Q\<^sub>p p) k = to_Zp a k [^]\<^bsub>Zp_res_ring k\<^esub> deg Q\<^sub>p p"
       proof-
       have 01: "\<And>m::nat. to_Zp (a[^]m) k = to_Zp a k [^]\<^bsub>Zp_res_ring k\<^esub> m"
       proof-
         fix m::nat show "to_Zp (a [^] m) k = to_Zp a k [^]\<^bsub>Zp_res_ring k\<^esub> m"
       proof-
         have 00: "to_Zp (a[^]m) = to_Zp a [^]\<^bsub>Z\<^sub>p\<^esub> m"
         using assms to_Zp_nat_pow[of a "m"] by blast
       have 01: "to_Zp a \<in> carrier Z\<^sub>p"
         using assms to_Zp_closed val_ring_memE(2) by blast
       have 02: "to_Zp a k \<in> carrier (Zp_res_ring k)"
         using 01 residues_closed by blast
       have 03: "cring (Zp_res_ring k)"
         using k_pos padic_integers.R_cring padic_integers_axioms by blast
       have 01: "(to_Zp a [^]\<^bsub>Z\<^sub>p\<^esub> m) k = (to_Zp a) k [^]\<^bsub>Zp_res_ring k\<^esub> m"
         apply(induction m)
         using 01 02 apply (metis Group.nat_pow_0 k_pos residue_of_one(1))
         using residue_of_prod[of "to_Zp a [^]\<^bsub>Z\<^sub>p\<^esub> m" "to_Zp a" k] 01 02 03
       proof -
         fix ma :: nat
         assume "(to_Zp a [^]\<^bsub>Z\<^sub>p\<^esub> ma) k = to_Zp a k [^]\<^bsub>Zp_res_ring k\<^esub> ma"
         then show "(to_Zp a [^]\<^bsub>Z\<^sub>p\<^esub> Suc ma) k = to_Zp a k [^]\<^bsub>Zp_res_ring k\<^esub> Suc ma"
           by (metis (no_types) Group.nat_pow_Suc residue_of_prod)
       qed
       show ?thesis unfolding 00 01 by blast
       qed
       qed
       thus ?thesis by blast
       qed
       have 155: "to_Zp( b [^] deg Q\<^sub>p p) k = to_Zp b k [^]\<^bsub>Zp_res_ring k\<^esub> deg Q\<^sub>p p"
         using assms by (metis "154" to_Zp_res_of_pow)
       show ?thesis
         unfolding 3 4 152 153 154 155 assms by blast
     qed
     show "to_Zp (p \<bullet> a) k = to_Zp (p \<bullet> b) k"
       unfolding 13 14 15 using A 1 q_def by presburger
   qed
  qed
  thus ?thesis using assms by blast
qed

lemma to_Zp_poly_eval:
  assumes "g \<in> carrier Q\<^sub>p_x"
  assumes "gauss_norm g \<ge> 0"
  assumes "a \<in> \<O>\<^sub>p"
  shows "to_Zp (to_function Q\<^sub>p g a) = to_function Z\<^sub>p (to_Zp_poly g) (to_Zp a)"
proof-
  obtain h where h_def: "h = to_Zp_poly g"
    by blast
  obtain b where b_def: "b = to_Zp a"
    by blast
  have h_poly_inc: "poly_inc h = g"
    unfolding h_def using assms
    by (simp add: poly_inc_inverse_left)
  have b_inc: "\<iota> b = a"
    unfolding b_def using assms
    by (simp add: to_Zp_inc)
  have h_closed: "h \<in> carrier (UP Z\<^sub>p)"
    unfolding h_def using assms
    by (simp add: to_Zp_poly_closed)
  have b_closed: "b \<in> carrier Z\<^sub>p"
    unfolding b_def using assms
    by (simp add: to_Zp_closed val_ring_memE)
  have 0: "to_function Q\<^sub>p (poly_inc h) (\<iota> b) = \<iota> (to_function Z\<^sub>p h b)"
    apply(rule poly_inc_eval)
    using h_def assms apply (simp add: to_Zp_poly_closed; fail)
    unfolding b_def using assms
    by (simp add: to_Zp_closed val_ring_memE)
  have 1: "to_Zp (to_function Q\<^sub>p (poly_inc h) (\<iota> b)) = to_function Z\<^sub>p h b"
    unfolding 0
    using h_closed b_closed Zp.to_fun_closed Zp.to_fun_def inc_to_Zp by auto
  show ?thesis
    using 1 unfolding h_poly_inc b_inc
    unfolding h_def b_def by blast
qed

lemma poly_eval_equal_val:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>x. g x \<in> \<O>\<^sub>p"
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "val (g \<bullet> a) < eint n"
  assumes "to_Zp a n = to_Zp b n"
  shows "val (g \<bullet> b) = val (g \<bullet> a)"
proof-
  have "(\<forall>x. g x \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (g \<bullet> b) n = to_Zp (g \<bullet> a) n"
  proof(rule poly_induct[of g])
    show "g \<in> carrier (UP Q\<^sub>p)"
      by (simp add: assms(1))
    show "\<And>p. p \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p p = 0 \<Longrightarrow> (\<forall>x. p x \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (p \<bullet> b) n = to_Zp (p \<bullet> a) n"
    proof fix p assume A: "p \<in> carrier (UP Q\<^sub>p)" " deg Q\<^sub>p p = 0 " "\<forall>x. p x \<in> \<O>\<^sub>p "
      show "to_Zp (p \<bullet> b) n = to_Zp (p \<bullet> a) n"
        using A  by (metis val_ring_memE UPQ.to_fun_ctrm UPQ.trms_of_deg_leq_0 UPQ.trms_of_deg_leq_degree_f assms(3) assms(4))
    qed
    show "\<And>p. (\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow> (\<forall>x. q x \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (q \<bullet> b) n = to_Zp (q \<bullet> a) n) \<Longrightarrow>
         p \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> 0 < deg Q\<^sub>p p \<Longrightarrow> (\<forall>x. p x \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (p \<bullet> b) n = to_Zp (p \<bullet> a) n"
    proof fix p assume IH: "(\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow> (\<forall>x. q x \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (q \<bullet> b) n = to_Zp (q \<bullet> a) n)"
      assume A: "p \<in> carrier (UP Q\<^sub>p)" "0 < deg Q\<^sub>p p" "\<forall>x. p x \<in> \<O>\<^sub>p"
      show "to_Zp (p \<bullet> b) n = to_Zp (p \<bullet> a) n"
      proof-
        obtain q where q_def: "q \<in> carrier (UP Q\<^sub>p) \<and> deg Q\<^sub>p q < deg Q\<^sub>p p \<and>
                      p = q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> ltrm p"
          using A  by (meson UPQ.ltrm_decomp)
        have p_eq: "p = q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> ltrm p"
          using q_def by blast
        have "\<forall>x. q x \<in> \<O>\<^sub>p" proof fix x
          have px: "p x = (q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> ltrm p) x"
            using p_eq by simp
          show "q x \<in> \<O>\<^sub>p"
          proof(cases "x \<le> deg Q\<^sub>p q")
            case True
            then have "p x = q x"
              unfolding px using q_def A
              by (smt UPQ.ltrm_closed UPQ.P.add.right_cancel UPQ.coeff_of_sum_diff_degree0 UPQ.deg_ltrm UPQ.trunc_cfs UPQ.trunc_closed UPQ.trunc_simps(1) less_eq_Suc_le nat_neq_iff not_less_eq_eq)
            then show ?thesis using A
              by blast
          next
            case False
            then show ?thesis
              using q_def UPQ.deg_eqI eq_imp_le nat_le_linear zero_in_val_ring
              by (metis (no_types, lifting) UPQ.coeff_simp UPQ.deg_belowI)
          qed
        qed
        then have 0: " to_Zp (q \<bullet> b) n = to_Zp (q \<bullet> a) n"
          using IH q_def by blast
        have 1: "to_Zp (ltrm p \<bullet> b) n = to_Zp (ltrm p \<bullet> a) n"
        proof-
          have 10: "(ltrm p \<bullet> b) = (p (deg Q\<^sub>p p)) \<otimes> b[^] (deg Q\<^sub>p p)"
            using assms A  by (meson val_ring_memE UPQ.to_fun_monom)
          have 11: "(ltrm p \<bullet> a) = (p (deg Q\<^sub>p p)) \<otimes> a[^] (deg Q\<^sub>p p)"
            using assms A by (meson val_ring_memE UPQ.to_fun_monom)
          have 12: "to_Zp (b[^] (deg Q\<^sub>p p)) n = to_Zp (a[^] (deg Q\<^sub>p p)) n"
            using to_Zp_res_of_pow assms by metis
          have 13: "p (deg Q\<^sub>p p) \<in> \<O>\<^sub>p"
            using A(3) by blast
          have 14: "b[^] (deg Q\<^sub>p p) \<in> \<O>\<^sub>p"
            using assms(4) val_ring_nat_pow_closed by blast
          have 15: "a[^] (deg Q\<^sub>p p) \<in> \<O>\<^sub>p"
            using assms(3) val_ring_nat_pow_closed by blast
          have 16: "(ltrm p \<bullet> b) \<in> \<O>\<^sub>p"
            by (simp add: "10" "13" "14" val_ring_times_closed)
          have 17: "to_Zp (ltrm p \<bullet> b) n = to_Zp (p (deg Q\<^sub>p p)) n \<otimes>\<^bsub>Zp_res_ring n\<^esub> to_Zp (b[^] (deg Q\<^sub>p p)) n"
            using 10 13 14 15 16 assms residue_of_prod to_Zp_mult by presburger
          have 18: "(ltrm p \<bullet> a) \<in> \<O>\<^sub>p"
            by (simp add: "11" "15" A(3) val_ring_times_closed)
          have 19: "to_Zp (ltrm p \<bullet> a) n = to_Zp (p (deg Q\<^sub>p p)) n \<otimes>\<^bsub>Zp_res_ring n\<^esub> to_Zp (a[^] (deg Q\<^sub>p p)) n"
            using 10 13 14 15 16 17 18 assms residue_of_prod to_Zp_mult 11  by presburger
          show ?thesis using 12 17 19 by presburger
        qed
        have 2: "p (deg Q\<^sub>p p) \<in> \<O>\<^sub>p"
          using A(3) by blast
        have 3: "(ltrm p \<bullet> b) \<in> \<O>\<^sub>p"
          using 2 assms
          by (metis A(1) Q\<^sub>p_def val_ring_memE val_ring_memE UPQ.ltrm_closed Zp_def \<iota>_def
              gauss_norm_monom padic_fields.positive_gauss_norm_eval padic_fields_axioms)
        have 4: "(ltrm p \<bullet> a) \<in> \<O>\<^sub>p"
          using 2 assms
          by (metis A(1) Q\<^sub>p_def val_ring_memE val_ring_memE UPQ.ltrm_closed Zp_def \<iota>_def
              gauss_norm_monom padic_fields.positive_gauss_norm_eval padic_fields_axioms)
        have 5: "(q \<bullet> b) \<in> \<O>\<^sub>p"
          using  \<open>\<forall>x. q x \<in> \<O>\<^sub>p\<close> assms(4) q_def
          by (metis gauss_norm_coeff_norm positive_gauss_norm_eval val_ring_memE(1))
        have 6: "(q \<bullet> a) \<in> \<O>\<^sub>p"
          using  \<open>\<forall>x. q x \<in> \<O>\<^sub>p\<close> assms(3) q_def
          by (metis gauss_norm_coeff_norm positive_gauss_norm_eval val_ring_memE(1))
        have 7: "to_Zp (p \<bullet> b) = to_Zp (ltrm p \<bullet> b)  \<oplus>\<^bsub>Z\<^sub>p\<^esub> to_Zp (q \<bullet> b)"
          using 5 3 q_def by (metis (no_types, lifting) A(1) val_ring_memE UPQ.ltrm_closed UPQ.to_fun_plus add_comm assms(4) to_Zp_add)
        have 8: "to_Zp (p \<bullet> a) = to_Zp (ltrm p \<bullet> a)  \<oplus>\<^bsub>Z\<^sub>p\<^esub> to_Zp (q \<bullet> a)"
          using 4 6 q_def by (metis (no_types, lifting) A(1) val_ring_memE UPQ.ltrm_closed UPQ.to_fun_plus add_comm assms(3) to_Zp_add)
        have 9: "to_Zp (p \<bullet> b) \<in> carrier Z\<^sub>p"
          using A assms by (meson val_ring_memE UPQ.to_fun_closed to_Zp_closed)
        have 10: "to_Zp (p \<bullet> a) \<in> carrier Z\<^sub>p"
          using A assms val_ring_memE UPQ.to_fun_closed to_Zp_closed by presburger
        have 11: "to_Zp (p \<bullet> b) n = to_Zp (ltrm p \<bullet> b) n  \<oplus>\<^bsub>Zp_res_ring n\<^esub> to_Zp (q \<bullet> b) n"
          using 7 9 5 3 residue_of_sum by presburger
        have 12: "to_Zp (p \<bullet> a) n = to_Zp (ltrm p \<bullet> a) n \<oplus>\<^bsub>Zp_res_ring n\<^esub> to_Zp (q \<bullet> a) n"
          using 8 6 4 residue_of_sum by presburger
        show ?thesis using 0 11 12 q_def assms
          using "1" by presburger
      qed
    qed
  qed
  have "(\<forall>x. g x \<in> \<O>\<^sub>p) "
    using assms by blast
  hence 0: "to_Zp (g \<bullet> b) n = to_Zp (g \<bullet> a) n"
    using \<open>(\<forall>x. g x \<in> \<O>\<^sub>p) \<longrightarrow> to_Zp (g \<bullet> b) n = to_Zp (g \<bullet> a) n\<close> by blast
  have 1: "g \<bullet> a \<in> \<O>\<^sub>p"
    using  assms(1) assms(2) assms(3)
    by (metis gauss_norm_coeff_norm positive_gauss_norm_eval val_ring_memE(1))
  have 2: "g \<bullet> b \<in> \<O>\<^sub>p"
    using  assms(1) assms(2) assms(4)
    by (metis gauss_norm_coeff_norm positive_gauss_norm_eval val_ring_memE(1))
  have 3: "val (g \<bullet> b) < eint n"
  proof-
    have P0: "to_Zp (g \<bullet> a) \<in> carrier Z\<^sub>p"
      using 1 val_ring_memE to_Zp_closed by blast
    have P1: "to_Zp (g \<bullet> b) \<in> carrier Z\<^sub>p"
      using 2 val_ring_memE to_Zp_closed by blast
    have P2: "val_Zp (to_Zp (g \<bullet> a)) < n"
      using 1 assms to_Zp_val by presburger
    have P3: "to_Zp (g \<bullet> a) \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
      using P2 P0 unfolding val_Zp_def     by (metis P2 infinity_ilessE val_Zp_def)
    have P4: "(to_Zp (g \<bullet> a)) n \<noteq> 0"
      using 1 P2 P3 above_ord_nonzero[of "to_Zp (g \<bullet> a)" n]
      by (metis P0 eint.inject less_eintE val_ord_Zp)
    then have "to_Zp (g \<bullet> b) n \<noteq> 0"
      using 0 by linarith
    then have "val_Zp (to_Zp (g \<bullet> b)) < n"
      using P1 P0
      by (smt below_val_Zp_zero eint_ile eint_ord_simps(1) eint_ord_simps(2) nonzero_imp_ex_nonzero_res residue_of_zero(2) zero_below_val_Zp)
    then show ?thesis using 2
      by (metis to_Zp_val)
  qed
  thus ?thesis using 0 1 2 assms val_ring_equal_res_imp_equal_val[of "g \<bullet> b" "g \<bullet> a" n] by blast
qed

lemma to_Zp_poly_monom:
  assumes "a \<in> \<O>\<^sub>p"
  shows "to_Zp_poly (monom (UP Q\<^sub>p) a n) = monom (UP Z\<^sub>p) (to_Zp a) n"
  unfolding to_Zp_poly_def
  apply(rule ext)
  using assms cfs_monom[of a n] Zp.cfs_monom[of "to_Zp a" n]
  by (simp add: to_Zp_closed to_Zp_zero val_ring_memE(2))

lemma to_Zp_poly_add:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "gauss_norm f \<ge> 0"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "gauss_norm g \<ge> 0"
  shows "to_Zp_poly (f \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> g) = to_Zp_poly f \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> to_Zp_poly g"
proof-
  obtain F where F_def: "F = to_Zp_poly f"
    by blast
  obtain G where G_def: "G = to_Zp_poly g"
    by blast
  have F_closed: "F \<in> carrier (UP Z\<^sub>p)"
    unfolding F_def using assms
    by (simp add: to_Zp_poly_closed)
  have G_closed: "G \<in> carrier (UP Z\<^sub>p)"
    unfolding G_def using assms
    by (simp add: to_Zp_poly_closed)
  have F_inc: "poly_inc F = f"
    using assms unfolding F_def
    using poly_inc_inverse_left by blast
  have G_inc: "poly_inc G = g"
    using assms unfolding G_def
    by (simp add: poly_inc_inverse_left)
  have 0: "poly_inc (F \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> G) = poly_inc F \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> poly_inc G"
    using F_closed G_closed
    by (simp add: poly_inc_plus)
  have 1: "to_Zp_poly (poly_inc (F \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> G)) = F \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> G"
    using G_closed F_closed
    by (simp add: poly_inc_inverse_right)
  show ?thesis
    using  1 unfolding F_inc G_inc 0 unfolding F_def G_def
    by blast
qed

lemma to_Zp_poly_zero:
"to_Zp_poly (\<zero>\<^bsub>UP Q\<^sub>p\<^esub>) = \<zero>\<^bsub>UP Z\<^sub>p\<^esub>"
  unfolding to_Zp_poly_def
  apply(rule ext)
  by (simp add: to_Zp_zero)

lemma to_Zp_poly_one:
"to_Zp_poly (\<one>\<^bsub>UP Q\<^sub>p\<^esub>) = \<one>\<^bsub>UP Z\<^sub>p\<^esub>"
  unfolding to_Zp_poly_def
  apply(rule ext)
  by (metis Zp.UP_one_closed poly_inc_inverse_right poly_inc_one to_Zp_poly_def)

lemma val_ring_add_pow:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<ge> 0"
  shows "val ([(n::nat)]\<cdot>a) \<ge> 0"
proof-
  have 0: "[(n::nat)]\<cdot>a = ([n]\<cdot>\<one>)\<otimes>a"
    using assms Qp.add_pow_ldistr Qp.cring_simprules(12) Qp.one_closed by presburger
  show ?thesis unfolding 0 using assms
    by (meson Qp.nat_inc_closed val_ring_memE val_of_nat_inc val_ringI val_ring_times_closed)
qed

lemma to_Zp_poly_pderiv:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "gauss_norm g \<ge> 0"
  shows "to_Zp_poly (pderiv g) = Zp.pderiv (to_Zp_poly g)"
proof-
  have 0: "gauss_norm g \<ge> 0 \<longrightarrow> to_Zp_poly (pderiv g) = Zp.pderiv (to_Zp_poly g)"
  proof(rule poly_induct, rule assms, rule)
    fix p
    assume A: " p \<in> carrier (UP Q\<^sub>p)"
         "deg Q\<^sub>p p = 0"
         "0 \<le> gauss_norm p"
    obtain a where a_def: "a \<in> \<O>\<^sub>p \<and> p = monom (UP Q\<^sub>p) a 0"
      using A
      by (metis UPQ.ltrm_deg_0 positive_gauss_norm_valuation_ring_coeffs)
    have p_eq: "p = monom (UP Q\<^sub>p) a 0"
      using a_def by blast
    have 0: "to_Zp_poly p = monom (UP Z\<^sub>p) (to_Zp a) 0"
      unfolding p_eq
      apply(rule to_Zp_poly_monom)
      using a_def by blast
    have 1: "UPQ.pderiv (monom (UP Q\<^sub>p) a 0) = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
      using A(1) A(2) UPQ.pderiv_deg_0 p_eq by blast
    have 2: "Zp.pderiv (monom (UP Z\<^sub>p) (to_Zp a) 0) = \<zero>\<^bsub>UP Z\<^sub>p\<^esub>"
      apply(rule Zp.pderiv_deg_0)
       apply(rule Zp.monom_closed, rule to_Zp_closed)
      using a_def
       apply (simp add: val_ring_memE(2); fail)
      apply(cases "to_Zp a = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
      apply (simp; fail)
      apply(rule Zp.deg_monom, blast)
      using a_def
      by (simp add: to_Zp_closed val_ring_memE(2))
    show "to_Zp_poly (UPQ.pderiv p) = Zp.pderiv (to_Zp_poly p)"
      unfolding 0 unfolding p_eq
      unfolding 1 2 to_Zp_poly_zero by blast
  next
    fix p
    assume A: "\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow>
              deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow>
              0 \<le> gauss_norm q \<longrightarrow>
              to_Zp_poly (UPQ.pderiv q) = Zp.pderiv (to_Zp_poly q)"
              "p \<in> carrier (UP Q\<^sub>p)"
              " 0 < deg Q\<^sub>p p"
    show "0 \<le> gauss_norm p \<longrightarrow> to_Zp_poly (UPQ.pderiv p) = Zp.pderiv (to_Zp_poly p)"
    proof
      assume B: "0 \<le> gauss_norm p"
      obtain q where q_def: "q = trunc p"
        by blast
      have p_eq: "p = q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> ltrm p"
        by (simp add: A(2) UPQ.trunc_simps(1) q_def)
      have q_gauss_norm:    "gauss_norm q \<ge> 0"
        unfolding q_def
        apply(rule gauss_norm_geqI)
        using A apply (simp add: UPQ.trunc_closed; fail)
        using trunc_cfs[of p] A gauss_normE
      proof -
        fix n :: nat
        have f1: "\<zero> = q (deg Q\<^sub>p p)"
          by (simp add: UPQ.deg_leE UPQ.trunc_closed UPQ.trunc_degree \<open>0 < deg Q\<^sub>p p\<close> \<open>p \<in> carrier (UP Q\<^sub>p)\<close> q_def)
        have "\<forall>n. 0 \<le> val (p n)"
          by (meson B \<open>p \<in> carrier (UP Q\<^sub>p)\<close> eint_ord_trans gauss_normE)
        then show "0 \<le> val (Cring_Poly.truncate Q\<^sub>p p n)"
          using f1 by (metis (no_types) Qp.nat_mult_zero UPQ.ltrm_closed UPQ.coeff_of_sum_diff_degree0 UPQ.deg_ltrm UPQ.trunc_closed \<open>\<And>n. \<lbrakk>p \<in> carrier (UP Q\<^sub>p); n < deg Q\<^sub>p p\<rbrakk> \<Longrightarrow> Cring_Poly.truncate Q\<^sub>p p n = p n\<close> \<open>p \<in> carrier (UP Q\<^sub>p)\<close> nat_neq_iff p_eq q_def val_of_nat_inc)
      qed
      have 0: "to_Zp_poly (UPQ.pderiv q) = Zp.pderiv (to_Zp_poly q)"
        using A q_def q_gauss_norm
        by (simp add: UPQ.trunc_closed UPQ.trunc_degree)
      have 1: "UPQ.pderiv (monom (UP Q\<^sub>p) (p (deg Q\<^sub>p p)) (deg Q\<^sub>p p)) =
               monom (UP Q\<^sub>p) ([deg Q\<^sub>p p] \<cdot> p (deg Q\<^sub>p p)) (deg Q\<^sub>p p - 1)"
        apply(rule pderiv_monom)
        using A by (simp add: UPQ.UP_car_memE(1))
      have 2: "Zp.pderiv (monom (UP Z\<^sub>p) (to_Zp (p (deg Q\<^sub>p p))) (deg Q\<^sub>p p)) =
    monom (UP Z\<^sub>p) ([deg Q\<^sub>p p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> to_Zp ( p (deg Q\<^sub>p p))) (deg Q\<^sub>p p - 1)"
        using A  Zp.pderiv_monom[of "to_Zp ( p (deg Q\<^sub>p p))" "deg Q\<^sub>p p"]
        by (simp add: UPQ.lcf_closed to_Zp_closed)
      have 3: "to_Zp_poly (UPQ.pderiv (monom (UP Q\<^sub>p) (p (deg Q\<^sub>p p)) (deg Q\<^sub>p p))) = monom (UP Z\<^sub>p) (to_Zp ([deg Q\<^sub>p p] \<cdot> p (deg Q\<^sub>p p))) (deg Q\<^sub>p p - 1)"
        unfolding 1 apply(rule to_Zp_poly_monom)
        apply(rule val_ring_memI)
         apply (simp add: A(2) UPQ.UP_car_memE(1); fail)
        apply(rule val_ring_add_pow)
        using A
        apply (simp add: UPQ.lcf_closed; fail)
        using B A
        by (simp add: positive_gauss_norm_valuation_ring_coeffs val_ring_memE(1))
      have 4: "to_Zp_poly (ltrm p) = monom (UP Z\<^sub>p) (to_Zp (p (deg Q\<^sub>p p))) (deg Q\<^sub>p p)"
        apply(rule to_Zp_poly_monom) using A
        by (simp add: B positive_gauss_norm_valuation_ring_coeffs)
      have 5: "to_Zp_poly (UPQ.pderiv (ltrm p)) = Zp.pderiv (to_Zp_poly (ltrm p))"
        unfolding 3 4 2
        by (simp add: A(2) B positive_gauss_norm_valuation_ring_coeffs to_Zp_nat_add_pow)
      have 6: "pderiv p = pderiv q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> pderiv (ltrm p)"
        using p_eq
        by (metis A(2) UPQ.ltrm_closed UPQ.pderiv_add UPQ.trunc_closed p_eq q_def)
      have 7: "to_Zp_poly p = to_Zp_poly q \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> to_Zp_poly (ltrm p)"
        using p_eq
        by (metis (no_types, lifting) A(2) B UPQ.ltrm_closed UPQ.cfs_closed UPQ.trunc_closed gauss_norm_monom positive_gauss_norm_valuation_ring_coeffs q_def q_gauss_norm to_Zp_poly_add val_ring_memE(1))
      have 8: "to_Zp_poly  (pderiv p) =
                to_Zp_poly (UPQ.pderiv q) \<oplus>\<^bsub>UP Z\<^sub>p\<^esub>
                 to_Zp_poly (UPQ.pderiv (monom (UP Q\<^sub>p) (p (deg Q\<^sub>p p)) (deg Q\<^sub>p p)))"
        unfolding 6 apply(rule to_Zp_poly_add)
           apply (simp add: A(2) UPQ.pderiv_closed UPQ.trunc_closed q_def; fail)
          apply (metis A(2) UPQ.cfs_closed UPQ.pderiv_cfs UPQ.trunc_closed gauss_norm_coeff_norm positive_gauss_norm_valuation_ring_coeffs q_def q_gauss_norm val_ring_add_pow val_ring_memE(1))
         apply (simp add: A(2) UPQ.UP_car_memE(1) UPQ.pderiv_closed; fail)
        apply(rule eint_ord_trans[of _ "gauss_norm (monom (UP Q\<^sub>p) (p (deg Q\<^sub>p p)) (deg Q\<^sub>p p))"])
        apply (simp add: A(2) B UPQ.cfs_closed gauss_norm_monom positive_gauss_norm_valuation_ring_coeffs val_ring_memE(1); fail)
        apply(rule gauss_norm_pderiv)
        using A(2) UPQ.ltrm_closed by blast
      have 9: "Zp.pderiv  (to_Zp_poly p) =  Zp.pderiv (to_Zp_poly q) \<oplus>\<^bsub>UP Z\<^sub>p\<^esub>
         Zp.pderiv (to_Zp_poly (monom (UP Q\<^sub>p) (p (deg Q\<^sub>p p)) (deg Q\<^sub>p p)))"
          unfolding 7 apply(rule Zp.pderiv_add)
           apply(rule to_Zp_poly_closed)
            apply (simp add: A(2) UPQ.trunc_closed q_def; fail)
           apply (simp add: q_gauss_norm; fail)
           apply(rule to_Zp_poly_closed)
           apply (simp add: A(2) UPQ.UP_car_memE(1); fail)
          by (simp add: A(2) B UPQ.cfs_closed gauss_norm_monom positive_gauss_norm_valuation_ring_coeffs val_ring_memE(1))
      show "to_Zp_poly (UPQ.pderiv p) = Zp.pderiv (to_Zp_poly p)"
          unfolding 9 8 5 0 by blast
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma val_p_int_pow:
"val (\<pp>[^]k) = eint (k)"
  by (simp add: ord_p_pow_int p_intpow_closed(2))

definition int_gauss_norm where
"int_gauss_norm g = (SOME n::int. eint n = gauss_norm g)"

lemma int_gauss_norm_eq:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "g \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  shows "eint (int_gauss_norm g) = gauss_norm g"
proof-
  have 0: "gauss_norm g < \<infinity>"
    using assms by (simp add: gauss_norm_prop)
  then show ?thesis unfolding int_gauss_norm_def
    using assms
    by fastforce
qed

lemma int_gauss_norm_smult:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "g \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "int_gauss_norm (a \<odot>\<^bsub>UP Q\<^sub>p\<^esub> g) = ord a + int_gauss_norm g"
  using gauss_norm_smult[of g a] int_gauss_norm_eq val_ord assms
  by (metis (no_types, opaque_lifting) Qp.nonzero_closed UPQ.UP_smult_closed UPQ.cfs_zero
      eint.distinct(2) eint.inject gauss_norm_coeff_norm local.val_zero plus_eint_simps(1))

definition normalize_poly where
"normalize_poly g = (if g = \<zero>\<^bsub>UP Q\<^sub>p\<^esub> then g else (\<pp>[^](- int_gauss_norm g)) \<odot>\<^bsub>Q\<^sub>p_x\<^esub> g)"

lemma normalize_poly_zero:
"normalize_poly \<zero>\<^bsub>UP Q\<^sub>p\<^esub> = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  unfolding normalize_poly_def by simp

lemma normalize_poly_nonzero_eq:
  assumes "g \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  shows "normalize_poly g = (\<pp>[^](- int_gauss_norm g)) \<odot>\<^bsub>UP Q\<^sub>p\<^esub> g"
  using assms unfolding normalize_poly_def by simp

lemma int_gauss_norm_normalize_poly:
  assumes "g \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  shows "int_gauss_norm (normalize_poly g) = 0"
  using normalize_poly_nonzero_eq int_gauss_norm_smult assms
  by (simp add: ord_p_pow_int p_intpow_closed(2))

lemma normalize_poly_closed:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  shows "normalize_poly g \<in> carrier (UP Q\<^sub>p)"
  using assms unfolding normalize_poly_def
  by (simp add: p_intpow_closed(1))

lemma normalize_poly_nonzero:
  assumes "g \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  shows "normalize_poly g \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  using assms normalize_poly_nonzero_eq
  by (metis (no_types, lifting) UPQ.UP_smult_one UPQ.module_axioms UPQ.smult_r_null module.smult_assoc1 p_intpow_closed(1) p_intpow_inv')

lemma gauss_norm_normalize_poly:
  assumes "g \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  shows "gauss_norm (normalize_poly g) = 0"
proof-
  have 0: "eint (int_gauss_norm (normalize_poly g)) = gauss_norm (normalize_poly g)"
    by(rule int_gauss_norm_eq, rule normalize_poly_closed, rule assms,
          rule normalize_poly_nonzero, rule assms, rule assms)
  show ?thesis
    using 0 int_gauss_norm_normalize_poly assms
    by (simp add: zero_eint_def)
qed

lemma taylor_term_eval_eq:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "\<And>j. i \<noteq> j \<Longrightarrow> val (UPQ.taylor_term x f i \<bullet> t) < val (UPQ.taylor_term x f j \<bullet> t) "
  shows "val (f \<bullet> t) = val (UPQ.taylor_term x f i \<bullet> t)"
proof-
  have 0: "f = finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) {..deg Q\<^sub>p f}"
    by(rule UPQ.taylor_term_sum[of f "deg Q\<^sub>p f" x], rule assms, blast, rule assms)
  show ?thesis
  proof(cases "i \<in> {..deg Q\<^sub>p f}")
    case True
    have T0: "finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) {..deg Q\<^sub>p f} = UPQ.taylor_term x f i \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) ({..deg Q\<^sub>p f} - {i})"
      apply(rule UPQ.P.finsum_remove[of "{..deg Q\<^sub>p f}" "UPQ.taylor_term x f" i])
      by(rule UPQ.taylor_term_closed, rule assms, rule assms, blast, rule True)
    have T1: "f = UPQ.taylor_term x f i \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) ({..deg Q\<^sub>p f} - {i})"
      using 0 T0 by metis
    have T2: "finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) ({..deg Q\<^sub>p f} - {i}) \<in> carrier (UP Q\<^sub>p)"
      apply(rule UPQ.P.finsum_closed)
      using UPQ.taylor_term_closed assms(1) assms(2) by blast
    have T3: "UPQ.taylor_term x f i \<in> carrier (UP Q\<^sub>p)"
      by(rule UPQ.taylor_term_closed, rule assms, rule assms )
    obtain g where g_def: "g = f"
      by blast
    have T4: "g = UPQ.taylor_term x f i \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) ({..deg Q\<^sub>p f} - {i})"
      unfolding g_def by(rule T1)
    have g_closed: "g \<in> carrier (UP Q\<^sub>p)"
      unfolding g_def by(rule assms)
    have T5: "g \<bullet> t = UPQ.taylor_term x f i \<bullet> t \<oplus> ( finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) ({..deg Q\<^sub>p f} - {i})) \<bullet> t"
      unfolding T4 by(rule UPQ.to_fun_plus, rule T2, rule T3, rule assms)
    have T6: "( finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) ({..deg Q\<^sub>p f} - {i})) \<bullet> t =
                ( finsum Q\<^sub>p (\<lambda>i. UPQ.taylor_term x f i \<bullet> t) ({..deg Q\<^sub>p f} - {i}))"
      apply(rule UPQ.to_fun_finsum, blast)
      using assms UPQ.taylor_term_closed apply blast
      using assms by blast
    have T7: "\<And>j. j \<in> {..deg Q\<^sub>p f} - {i} \<Longrightarrow> val (UPQ.taylor_term x f j \<bullet> t) > val (UPQ.taylor_term x f i \<bullet> t)"
      using assms  by (metis Diff_iff singletonI)
    have T8: "val (( finsum (UP Q\<^sub>p) (UPQ.taylor_term x f) ({..deg Q\<^sub>p f} - {i})) \<bullet> t) > val (UPQ.taylor_term x f i \<bullet> t)"
      unfolding T6
      apply(rule finsum_val_ultrametric'')
      using UPQ.taylor_term_closed assms
      apply (metis (no_types, lifting) Pi_I UPQ.to_fun_closed)
        apply blast
      using assms T7 apply blast
      using assms(4)[of "Suc i"] using eint_ord_simps(4)
        assms(4) eint_ord_code(6)  g_def gr_implies_not_zero less_one by smt
    have T9: "val (g \<bullet> t) =  val (UPQ.taylor_term x f i \<bullet> t)"
      unfolding T5 using T8 T2 T3
      by (metis (no_types, lifting) Qp.add.m_comm UPQ.to_fun_closed assms(3) val_ultrametric_noteq)
    show ?thesis using T9 unfolding g_def by blast
  next
    case False
    have "i > deg Q\<^sub>p f"
      using False by simp
    hence "i > deg Q\<^sub>p (UPQ.taylor x f)"
      using assms UPQ.taylor_deg by presburger
    hence F0: "UPQ.taylor x f i = \<zero>"
      using assms UPQ.taylor_closed UPQ.deg_leE by blast
    have F1: "(UPQ.taylor_term x f i \<bullet> t) = \<zero>"
      using UPQ.to_fun_taylor_term[of f t x i]
      unfolding F0
      using assms Qp.cring_simprules(2) Qp.cring_simprules(4) Qp.integral_iff Qp.nat_pow_closed by presburger
    show ?thesis
      using assms(4)[of "Suc i"] unfolding F1
      by (metis eint_ord_code(6) local.val_zero n_not_Suc_n)
  qed
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Hensel's Lemma for \<open>p\<close>-adic fields\<close>
(**************************************************************************************************)
(**************************************************************************************************)

theorem hensels_lemma:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "a \<in> \<O>\<^sub>p"
  assumes "gauss_norm f \<ge> 0"
  assumes "val (f\<bullet>a) > 2*val ((pderiv f)\<bullet>a)"
  shows "\<exists>!\<alpha> \<in> \<O>\<^sub>p. f\<bullet>\<alpha> = \<zero> \<and> val (a \<ominus> \<alpha>) > val ((pderiv f)\<bullet>a)"
proof-
  have a_closed: "a \<in> carrier Q\<^sub>p"
    using assms val_ring_memE by auto
  have f_nonzero: "f \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
  proof(rule ccontr)
    assume N: "\<not> f \<noteq> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
    then have 0: "pderiv f = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
      using UPQ.deg_zero UPQ.pderiv_deg_0 by blast
    have 1: "f = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
      using N by auto
    have 2: "eint 2 * val (UPQ.pderiv \<zero>\<^bsub>UP Q\<^sub>p\<^esub> \<bullet> a) = \<infinity>"
      by (simp add: UPQ.to_fun_zero local.a_closed local.val_zero)
    show False using assms a_closed
      unfolding 2 1
      using eint_ord_simps(6) by blast
  qed
  obtain h where h_def: "h = to_Zp_poly f"
    by blast
  have h_closed: "h \<in> carrier (UP Z\<^sub>p)"
    unfolding h_def using assms
    by (simp add: to_Zp_poly_closed)
  have h_deriv: "Zp.pderiv h = to_Zp_poly (pderiv f)"
    unfolding h_def
    using to_Zp_poly_pderiv[of f] assms by auto
  have 0: "to_Zp (f\<bullet>a) = to_function Z\<^sub>p h (to_Zp a)"
    unfolding h_def
    using assms a_closed
    by (simp add: UPQ.to_fun_def to_Zp_poly_eval)
  have 1: "to_Zp ((pderiv f)\<bullet>a) = to_function Z\<^sub>p (Zp.pderiv h) (to_Zp a)"
    unfolding h_deriv
    using assms a_closed  UPQ.pderiv_closed UPQ.to_fun_def eint_ord_trans gauss_norm_pderiv to_Zp_poly_eval
    by presburger
  have 2: "val (f\<bullet>a) = val_Zp (to_function Z\<^sub>p h (to_Zp a))"
  proof-
    have 20: "f\<bullet>a \<in> \<O>\<^sub>p"
      using assms positive_gauss_norm_eval by blast
    have 21: "val (f\<bullet>a) = val_Zp (to_Zp (f\<bullet>a))"
      using 20 by (simp add: to_Zp_val)
    show ?thesis unfolding 21 0 by blast
  qed
  have 3: "val ((pderiv f)\<bullet>a) = val_Zp ( to_function Z\<^sub>p (Zp.pderiv h) (to_Zp a))"
  proof-
    have 30: "(pderiv f)\<bullet>a \<in> \<O>\<^sub>p"
      using positive_gauss_norm_eval assms gauss_norm_pderiv
      by (meson UPQ.pderiv_closed eint_ord_trans)
    have 31: "val ((pderiv f)\<bullet>a) = val_Zp (to_Zp ((pderiv f)\<bullet>a))"
      using 30 by (simp add: to_Zp_val)
    show ?thesis unfolding 31 1 by blast
  qed
  have 4: "\<exists>!\<alpha>. \<alpha> \<in> carrier Z\<^sub>p \<and>
        Zp.to_fun (to_Zp_poly f) \<alpha> = \<zero>\<^bsub>Z\<^sub>p\<^esub> \<and>
        val_Zp (Zp.to_fun (Zp.pderiv (to_Zp_poly f)) (to_Zp a))
        < val_Zp (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha>)"
    apply(rule hensels_lemma')
    using h_closed h_def apply blast
    using assms local.a_closed to_Zp_closed apply blast
    using assms unfolding 2 3 h_def Zp.to_fun_def by blast
  obtain \<alpha> where \<alpha>_def: "\<alpha> \<in> carrier Z\<^sub>p \<and>
        Zp.to_fun (to_Zp_poly f) \<alpha> = \<zero>\<^bsub>Z\<^sub>p\<^esub> \<and>
        val_Zp (Zp.to_fun (Zp.pderiv (to_Zp_poly f)) (to_Zp a))
        < val_Zp (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha>)
        \<and> (\<forall>x.  x \<in> carrier Z\<^sub>p \<and>
        Zp.to_fun (to_Zp_poly f) x = \<zero>\<^bsub>Z\<^sub>p\<^esub> \<and>
        val_Zp (Zp.to_fun (Zp.pderiv (to_Zp_poly f)) (to_Zp a))
        < val_Zp (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> x) \<longrightarrow> x = \<alpha>)"
    using 4 by blast
  obtain \<beta> where \<beta>_def: "\<beta> = \<iota> \<alpha>"
    by blast
  have \<beta>_closed: "\<beta> \<in> \<O>\<^sub>p"
    using \<alpha>_def unfolding \<beta>_def by simp
  have 5: "(Zp.to_fun (to_Zp_poly f) \<alpha>) = to_Zp (f\<bullet>\<beta>)"
    using \<beta>_closed to_Zp_poly_eval[of f \<beta>] assms
    unfolding \<beta>_def UPQ.to_fun_def
    by (simp add: Zp.to_fun_def \<alpha>_def inc_to_Zp)
  have 6: "to_Zp (f\<bullet>\<beta>) = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
    using 5 \<alpha>_def by auto
  have \<beta>_closed: "\<beta> \<in> \<O>\<^sub>p"
    unfolding \<beta>_def using \<alpha>_def  by simp
  have 7: "(f\<bullet>\<beta>) = \<zero>"
    using 6 assms unfolding \<beta>_def
    by (metis \<beta>_closed \<beta>_def inc_of_zero positive_gauss_norm_eval to_Zp_inc)
  have 8: "\<alpha> = to_Zp \<beta>"
    unfolding \<beta>_def using \<alpha>_def
    by (simp add: inc_to_Zp)
  have 9: "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha> = to_Zp (a \<ominus> \<beta>)"
    unfolding 8 using assms(2) \<beta>_closed
    by (simp add: to_Zp_minus)
  have 10: "val (a \<ominus> \<beta>) = val_Zp (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha>)"
    unfolding 9 using \<beta>_closed assms(2)
    to_Zp_val val_ring_minus_closed by presburger
  have 11: "val (a \<ominus> \<beta>) > val ((pderiv f)\<bullet>a)"
    using \<alpha>_def unfolding 9 10 3 h_def
    by (simp add: Zp.to_fun_def)
  have 12: "\<beta> \<in> \<O>\<^sub>p \<and> f \<bullet> \<beta> = \<zero> \<and> val (UPQ.pderiv f \<bullet> a) < val (a \<ominus> \<beta>)"
    using "11" "7" \<beta>_closed by linarith
  have 13: "\<forall>x. x\<in> \<O>\<^sub>p \<and> f \<bullet> x = \<zero> \<and> val (UPQ.pderiv f \<bullet> a) < val (a \<ominus> x)
            \<longrightarrow> x = \<beta>"
  proof(rule, rule)
    fix x assume A: "x \<in> \<O>\<^sub>p \<and>  f \<bullet> x = \<zero> \<and> val (UPQ.pderiv f \<bullet> a) < val (a \<ominus> x)"
    obtain y where y_def: "y = to_Zp x"
      by blast
    have y_closed: "y \<in> carrier Z\<^sub>p"
      unfolding y_def using A
      by (simp add: to_Zp_closed val_ring_memE(2))
    have eval: "Zp.to_fun (to_Zp_poly f) y = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
      unfolding y_def using A assms
      by (metis UPQ.to_fun_def Zp.to_fun_def to_Zp_poly_eval to_Zp_zero)
    have 0: "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> y = to_Zp (a \<ominus> x)"
      unfolding y_def using A assms
      by (simp add: to_Zp_minus)
    have q: " val_Zp (Zp.to_fun (Zp.pderiv (to_Zp_poly f)) (to_Zp a)) = val (UPQ.pderiv f \<bullet> a)"
      by (simp add: "3" Zp.to_fun_def h_def)
    have 1: "y \<in> carrier Z\<^sub>p \<and>
        Zp.to_fun (to_Zp_poly f) y = \<zero>\<^bsub>Z\<^sub>p\<^esub> \<and>
        val_Zp (Zp.to_fun (Zp.pderiv (to_Zp_poly f)) (to_Zp a))
        < val_Zp (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> y)"
      unfolding 0 eval Zp.to_fun_def h_def
      apply(intro conjI y_closed)
      using eval Zp.to_fun_def apply (simp; fail)
      using A unfolding 0 eval Zp.to_fun_def h_def 3
      using assms(2) to_Zp_val val_ring_minus_closed by presburger
    have 2: "y = \<alpha>"
      using 1 \<alpha>_def by blast
    show "x = \<beta>"
      using y_def unfolding 2 8 using A \<beta>_closed
      by (metis to_Zp_inc)
  qed
  show "\<exists>!\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<and> f \<bullet> \<alpha> = \<zero> \<and> val (UPQ.pderiv f \<bullet> a) < val (a \<ominus> \<alpha>)"
    using 12 13 by metis
qed

lemma nth_root_poly_root_fixed:
  assumes "(n::nat) > 1"
  assumes "a \<in> \<O>\<^sub>p"
  assumes "val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> a) > 2* val ([n]\<cdot>\<one>)"
  shows "(\<exists>! b \<in> \<O>\<^sub>p. (b[^]n) = a \<and>  val (b \<ominus> \<one>) > val ([n]\<cdot>\<one>))"
proof-
  obtain f where f_def: "f = up_ring.monom (UP Q\<^sub>p) \<one> n \<ominus>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) a 0"
    by blast
  have f_closed: "f \<in> carrier (UP Q\<^sub>p)"
    unfolding f_def apply(rule UPQ.P.ring_simprules)
     apply (simp; fail)   using assms
    by (simp add: val_ring_memE(2))
  have 0: "UPQ.pderiv (up_ring.monom (UP Q\<^sub>p) a 0) = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
    using assms
    by (simp add: val_ring_memE(2))
  have 1: "UPQ.pderiv (up_ring.monom (UP Q\<^sub>p) (\<one>) n) = (up_ring.monom (UP Q\<^sub>p) ([n]\<cdot>\<one>) (n-1)) "
    using UPQ.pderiv_monom by blast
  have 2: "up_ring.monom (UP Q\<^sub>p) \<one> n \<in> carrier (UP Q\<^sub>p)"
    by simp
  have 3: "up_ring.monom (UP Q\<^sub>p) a 0 \<in> carrier (UP Q\<^sub>p)"
    using assms val_ring_memE by simp
  have 4: "UPQ.pderiv f  = up_ring.monom (UP Q\<^sub>p) ([n] \<cdot> \<one>) (n - 1)  \<ominus>\<^bsub>UP Q\<^sub>p\<^esub> \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
    using 2 3 assms val_ring_memE UPQ.pderiv_minus[of "up_ring.monom (UP Q\<^sub>p) \<one> n" "up_ring.monom (UP Q\<^sub>p) a 0"]
    unfolding f_def 0 1 by blast
  have 5: "UPQ.pderiv f = (up_ring.monom (UP Q\<^sub>p) ([n]\<cdot>\<one>) (n-1))"
    unfolding 4 a_minus_def by simp
  have a_closed: "a \<in> carrier Q\<^sub>p"
    using assms val_ring_memE by blast
  have 6: "UPQ.pderiv f \<bullet> \<one> = [n]\<cdot>\<one> \<otimes> \<one>[^](n-1)"
    unfolding 5 using a_closed
    by (simp add: UPQ.to_fun_monom)
  have 7: "val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> a) > val \<one>"
  proof-
    have "eint 2 * val ([n] \<cdot> \<one>) \<ge> 0"
      by (meson eint_ord_trans eint_pos_int_times_ge val_of_nat_inc zero_less_numeral)
    thus ?thesis
      using assms unfolding val_one
      by (simp add: Q\<^sub>p_def)
  qed
  hence 8: "val a = val \<one>"
    using a_closed
    by (metis Qp.cring_simprules(6) ultrametric_equal_eq')
  have 9:"val (a [^] (n - 1)) = 0"
    by (simp add: "8" local.a_closed val_zero_imp_val_pow_zero)
  have 10: "val ([n]\<cdot>\<one> \<otimes> \<one>[^](n-1)) = val ([n]\<cdot>\<one>)"
    unfolding val_one 9 by simp
  have 11: "0 \<le> gauss_norm f"
  proof-
    have p0: "gauss_norm (up_ring.monom (UP Q\<^sub>p) \<one> n) \<ge> 0"
      using gauss_norm_monom by simp
    have p1: "gauss_norm (up_ring.monom (UP Q\<^sub>p) a 0) \<ge> 0"
      using gauss_norm_monom assms val_ring_memE by simp
    have p2: "min (gauss_norm (up_ring.monom (UP Q\<^sub>p) \<one> n)) (gauss_norm (up_ring.monom (UP Q\<^sub>p) a 0)) \<ge> 0"
      using p0 p1 by simp
    have p3: "0 \<le> gauss_norm
      (up_ring.monom (UP Q\<^sub>p) \<one> n \<ominus>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) a 0)"
      using gauss_norm_ultrametric'[of "up_ring.monom (UP Q\<^sub>p) \<one> n" "up_ring.monom (UP Q\<^sub>p) a 0"]
            p2  "2" "3" eint_ord_trans  by blast
    show ?thesis using p3 unfolding f_def by simp
  qed
  have 12: "\<And>\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<Longrightarrow> f \<bullet> \<alpha> = \<alpha>[^]n \<ominus> a"
    unfolding f_def using a_closed
    by (simp add: UPQ.to_fun_const UPQ.to_fun_diff UPQ.to_fun_monic_monom val_ring_memE(2))
  have 13: "\<exists>!\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<and> f \<bullet> \<alpha> = \<zero> \<and> val (UPQ.pderiv f \<bullet> \<one>) < val (\<one> \<ominus> \<alpha>)"
    apply(rule hensels_lemma, rule f_closed, rule one_in_val_ring, rule 11)
    unfolding 6 10
    using a_closed assms 12[of \<one>] assms(3)
    by (simp add: one_in_val_ring)
  have 14: "\<And>\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<Longrightarrow> \<alpha>[^]n = a \<longleftrightarrow> f \<bullet> \<alpha> = \<zero>"
    unfolding f_def using a_closed 12 f_def val_ring_memE(2) by auto
  have 15: "val (UPQ.pderiv f \<bullet> \<one>) = val ([n]\<cdot>\<one>)"
    unfolding 6 10 by auto
  have 16: "\<And>\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<Longrightarrow> val (\<one> \<ominus> \<alpha>) = val (\<alpha> \<ominus> \<one>)"
  proof-
    have 17: "\<And>\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<Longrightarrow> (\<one> \<ominus> \<alpha>) = \<ominus> (\<alpha> \<ominus> \<one>)"
      using val_ring_memE
      by (meson Qp.minus_a_inv Qp.one_closed)
    show "\<And>\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<Longrightarrow> val (\<one> \<ominus> \<alpha>) = val (\<alpha> \<ominus> \<one>)"
      unfolding 17
      using Qp.minus_closed Qp.one_closed val_minus val_ring_memE(2) by presburger
  qed
  show ?thesis using 13 unfolding 15 using 14 16 Qp.one_closed val_ring_memE(2) by metis
qed

lemma mod_zeroE:
  assumes "(a::int) mod k  = 0"
  shows "\<exists>l. a = l*k"
  using assms
  using Groups.mult_ac(2) by blast

lemma to_Zp_poly_closed':
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>i. g i \<in> \<O>\<^sub>p"
  shows "to_Zp_poly g \<in> carrier (UP Z\<^sub>p)"
proof(rule to_Zp_poly_closed)
  show "g \<in> carrier (UP Q\<^sub>p)"
    using assms(1) by blast
  show "0 \<le> gauss_norm g"
  proof-
    have "\<And>i. val (g i) \<ge> 0"
      using assms val_ring_memE by blast
    thus ?thesis unfolding gauss_norm_def
      by (metis  gauss_norm_coeff_norm gauss_norm_def)
  qed
qed

lemma to_Zp_poly_eval_to_Zp:
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>i. g i \<in> \<O>\<^sub>p"
  assumes "a \<in> \<O>\<^sub>p"
  shows "to_function Z\<^sub>p (to_Zp_poly g) (to_Zp a) = to_Zp (g \<bullet> a)"
proof-
  have "(\<forall>i. g i \<in> \<O>\<^sub>p) \<longrightarrow> to_function Z\<^sub>p (to_Zp_poly g) (to_Zp a) = to_Zp (g \<bullet> a)"
    apply(rule UPQ.poly_induct[of g]) using assms apply blast
  proof
    fix p assume A: "p \<in> carrier (UP Q\<^sub>p)" "deg Q\<^sub>p p = 0" "\<forall>i. p i \<in> \<O>\<^sub>p"
    obtain c where c_def: "c \<in> carrier Q\<^sub>p \<and> p = up_ring.monom (UP Q\<^sub>p) c  0"
      using A  by (metis UPQ.ltrm_deg_0 val_ring_memE(2))
    have 0: "to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c  0) = up_ring.monom (UP Z\<^sub>p) (to_Zp c) 0"
      unfolding to_Zp_poly_def proof fix n show " to_Zp (up_ring.monom (UP Q\<^sub>p) c 0 n) = up_ring.monom (UP Z\<^sub>p) (to_Zp c) 0 n"
        using UP_ring.cfs_monom[of Z\<^sub>p "to_Zp c" 0 n] UP_ring.cfs_monom[of Q\<^sub>p c 0 n] to_Zp_closed[of c ]
        unfolding UP_ring_def
        apply(cases "0 = n")
        using UPQ.cfs_monom Zp.cfs_monom c_def apply presburger
         using UPQ.cfs_monom Zp.cfs_monom c_def
         using to_Zp_zero by presburger
    qed
    have p_eq: "p = up_ring.monom (UP Q\<^sub>p) c  0"
      using c_def by blast
    have 1: "(up_ring.monom (UP Q\<^sub>p) c 0 \<bullet> a) = c"
      using UPQ.to_fun_to_poly[of c a]  c_def assms val_ring_memE
      unfolding to_polynomial_def  by blast
    show "to_function Z\<^sub>p (to_Zp_poly p) (to_Zp a) = to_Zp (p \<bullet> a)"
      using c_def assms(3) val_ring_memE(2)[of a]
      UP_cring.to_fun_to_poly[of Z\<^sub>p "to_Zp c" "to_Zp a"]
      unfolding p_eq 0 1 Zp.to_fun_def to_polynomial_def
      using Zp.UP_cring_axioms to_Zp_closed by blast
  next
    show "\<And>p. (\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow>
              deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow> (\<forall>i. q i \<in> \<O>\<^sub>p) \<longrightarrow> to_function Z\<^sub>p (to_Zp_poly q) (to_Zp a) = to_Zp (q \<bullet> a)) \<Longrightarrow>
         p \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> 0 < deg Q\<^sub>p p \<Longrightarrow> (\<forall>i. p i \<in> \<O>\<^sub>p) \<longrightarrow> to_function Z\<^sub>p (to_Zp_poly p) (to_Zp a) = to_Zp (p \<bullet> a)"
    proof  fix p
      assume A: "(\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow>
              deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow> (\<forall>i. q i \<in> \<O>\<^sub>p) \<longrightarrow> to_function Z\<^sub>p (to_Zp_poly q) (to_Zp a) = to_Zp (q \<bullet> a))"
            "p \<in> carrier (UP Q\<^sub>p)" "0 < deg Q\<^sub>p p" "\<forall>i. p i \<in> \<O>\<^sub>p"
      show "to_function Z\<^sub>p (to_Zp_poly p) (to_Zp a) = to_Zp (p \<bullet> a)"
      proof-
        obtain q where q_def: "q = truncate Q\<^sub>p  p"
          by blast
        have  q_closed: "q \<in> carrier (UP Q\<^sub>p)"
          unfolding q_def by(rule UPQ.trunc_closed, rule A)
        obtain c where c_def: "c = UPQ.lcf p"
          by blast
        obtain n where n_def: "n = deg Q\<^sub>p p"
          by blast
        have 0: "p = q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) c n"
          unfolding c_def n_def q_def
          using A(2) UPQ.trunc_simps(1) by blast
        have 1: "up_ring.monom (UP Q\<^sub>p) c n \<in> carrier  (UP Q\<^sub>p)"
          using A(2) UPQ.ltrm_closed c_def n_def by blast
        have 2: "p \<bullet> a  = q  \<bullet> a \<oplus> (c \<otimes> a[^]n)"
          unfolding 0 using assms val_ring_memE
          by (metis "1" A(4) UPQ.to_fun_monom UPQ.to_fun_plus c_def q_closed)
        have 3: "\<And>i. i < n \<Longrightarrow> q i = p i"
          unfolding n_def q_def
          using A(2) UPQ.trunc_cfs by blast
        have 4: "deg Q\<^sub>p q < n"
          unfolding n_def q_def using A
          using UPQ.trunc_degree by presburger
        have 5: "\<And>i. i \<ge> n \<Longrightarrow> i >  deg Q\<^sub>p q"
          using A[of ] less_le_trans[of "deg Q\<^sub>p q" "deg Q\<^sub>p p"] unfolding q_def n_def
          using "4" n_def q_def by blast
        have 6: "\<And>i. i \<ge> n \<Longrightarrow> q i = \<zero>"
          using q_closed 5 UPQ.deg_leE by blast
        have 7: "(\<forall>i. q i \<in> \<O>\<^sub>p) \<longrightarrow> to_function Z\<^sub>p (to_Zp_poly q) (to_Zp a) = to_Zp (q \<bullet> a)"
          apply(rule   A) unfolding q_def
          using q_closed q_def apply blast
          using "4" n_def q_def by blast
        have 8: "(\<forall>i. q i \<in> \<O>\<^sub>p)"
        proof fix i show "q i \<in> \<O>\<^sub>p" apply(cases "i < n")
            using 3 A(4) apply blast using 6[of i]
            by (metis less_or_eq_imp_le linorder_neqE_nat zero_in_val_ring)
        qed
        have 9: "to_function Z\<^sub>p (to_Zp_poly q) (to_Zp a) = to_Zp (q \<bullet> a)"
          using 7 8 by blast
        have 10: "to_Zp_poly p = to_Zp_poly q \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n)"
        proof fix x
          have 100: "to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n) = (up_ring.monom (UP Z\<^sub>p) (to_Zp c) n)"
            using to_Zp_poly_monom[of c] A(4) c_def by blast
          have 101: "deg Z\<^sub>p (to_Zp_poly q) \<le> n-1"
              apply(rule  UP_cring.deg_leqI)
              unfolding UP_cring_def using Zp.R_cring apply auto[1]
              using to_Zp_poly_closed' 8 q_closed apply blast
              unfolding to_Zp_poly_def using 4 6
              by (simp add: to_Zp_zero)
          have 102: "(to_Zp_poly q) \<in> carrier (UP Z\<^sub>p)"
            apply(rule to_Zp_poly_closed', rule q_closed) using 8 by blast
          have 103: "deg Z\<^sub>p (to_Zp_poly q) < n"
            using 101 4 by linarith
            have T0: "(to_Zp_poly q \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n)) x =
                    (to_Zp_poly q x) \<oplus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n) x)"
              apply(rule  UP_ring.cfs_add)
                apply (simp add: Zp.is_UP_ring)
               apply (simp add: "102")
              using "100" A(2) UPQ.lcf_closed c_def to_Zp_closed by auto
            have c_closed: "c \<in> \<O>\<^sub>p"
              unfolding c_def  using A(4) by blast
            have to_Zp_c_closed: "to_Zp c \<in> carrier Z\<^sub>p"
              using c_closed to_Zp_closed val_ring_memE(2) by blast
          show "to_Zp_poly p x = (to_Zp_poly q \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n)) x"
          proof(cases "x < n")
            case True
            have T1: "(to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n) x) = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
              using True UP_ring.cfs_monom[of Z\<^sub>p] unfolding UP_ring_def
              by (simp add: A(2) UPQ.ltrm_cfs c_def n_def to_Zp_poly_def to_Zp_zero)
            have T2: "to_Zp (p x) = to_Zp (q x)" using 3[of x] True by smt
            have T3: "to_Zp (p x) \<in> carrier Z\<^sub>p"
              apply(rule to_Zp_closed) using A(2) UPQ.UP_car_memE(1) by blast
            show ?thesis using T3
              unfolding T0  unfolding T1 unfolding  to_Zp_poly_def  T2
              using Zp.cring_simprules(8) add_comm by presburger
          next
            case False
            have F: "q x = \<zero> "
              using False
              by (metis "6" less_or_eq_imp_le linorder_neqE_nat)
            have F': "(to_Zp_poly q) x = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
             unfolding to_Zp_poly_def F using to_Zp_zero by blast
            show "to_Zp_poly p x = (to_Zp_poly q \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n)) x"
            proof(cases "x = n")
              case True
              have T1: "to_Zp (p x) \<in> carrier Z\<^sub>p"
                apply(rule to_Zp_closed)
                using A(2) UPQ.UP_car_memE(1) by blast
              have T2: "(to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n) x) = to_Zp c"
                unfolding 100 using UP_ring.cfs_monom[of Z\<^sub>p "to_Zp c" n n] unfolding UP_ring_def True
                using Zp.ring_axioms to_Zp_c_closed by presburger
              show ?thesis using to_Zp_c_closed unfolding T0 F' T2 unfolding to_Zp_poly_def True c_def n_def
                using Zp.cring_simprules(8) by presburger
            next
              case FF: False
              have F0: "p x = \<zero>"
                using FF False unfolding n_def
                using A(2) UPQ.UP_car_memE(2) linorder_neqE_nat by blast
              have F1: "q x = \<zero>"
                using FF False F by linarith
              have F2: "(up_ring.monom (UP Q\<^sub>p) c n) x = \<zero>"
                using FF False A(2) UPQ.cfs_closed UPQ.cfs_monom c_def by presburger
              show ?thesis unfolding T0 unfolding to_Zp_poly_def F0 F1 F2
                using Zp.r_zero Zp.zero_closed to_Zp_zero by presburger
            qed
          qed
        qed
        have 11: "deg Z\<^sub>p (to_Zp_poly q) \<le> n-1"
          apply(rule  UP_cring.deg_leqI)
          unfolding UP_cring_def using Zp.R_cring apply auto[1]
          using to_Zp_poly_closed' 8 q_closed apply blast
          unfolding to_Zp_poly_def using 4 6
          by (smt diff_commute diff_diff_cancel less_one less_or_eq_imp_le linorder_neqE_nat to_Zp_zero zero_less_diff)
        have 12: "(to_Zp_poly q) \<in> carrier (UP Z\<^sub>p)"
          apply(rule to_Zp_poly_closed', rule q_closed) using 8 by blast
        have 13: "deg Z\<^sub>p (to_Zp_poly q) < n"
          using 11 4 by linarith
        have 14: "to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n) = (up_ring.monom (UP Z\<^sub>p) (to_Zp c) n)"
          using to_Zp_poly_monom[of c] A(4) c_def by blast
        have 15: "Zp.to_fun (to_Zp_poly q \<oplus>\<^bsub>UP Z\<^sub>p\<^esub> to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n)) (to_Zp a)=
            Zp.to_fun (to_Zp_poly q) (to_Zp a) \<oplus>\<^bsub>Z\<^sub>p\<^esub> Zp.to_fun (to_Zp_poly (up_ring.monom (UP Q\<^sub>p) c n)) (to_Zp a)"
          apply(rule Zp.to_fun_plus)
          unfolding 14  apply(rule UP_ring.monom_closed)
          unfolding UP_ring_def
             apply (simp add: Zp.ring_axioms)
            apply (simp add: A(2) UPQ.cfs_closed c_def to_Zp_closed)
           using "12" apply blast
          apply(rule to_Zp_closed) using assms val_ring_memE by blast
        have 16: "to_Zp (q \<bullet> a \<oplus> c \<otimes> a [^] n) = to_Zp (q \<bullet> a)  \<oplus>\<^bsub>Z\<^sub>p\<^esub> to_Zp (c \<otimes> a [^] n)"
          apply(rule to_Zp_add)
           apply(rule val_ring_poly_eval, rule q_closed)
            using "8" apply blast
             apply(rule assms)
            apply(rule val_ring_times_closed)
            unfolding c_def using A(4) apply blast
          by(rule val_ring_nat_pow_closed, rule assms)
        have  17: " to_function Z\<^sub>p (up_ring.monom (UP Z\<^sub>p) (to_Zp c) n) (to_Zp a) =  to_Zp (c \<otimes> a [^] n)"
          proof-
            have 170: "to_Zp (c \<otimes> a [^] n) = to_Zp c \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp (a [^] n)"
              apply(rule  to_Zp_mult[of c "a[^]n"])
              unfolding c_def using A(4) apply blast
              by(rule val_ring_nat_pow_closed, rule assms)
            have 171: "to_Zp (a [^] n) = (to_Zp a [^]\<^bsub>Z\<^sub>p\<^esub>n)"
              by(rule to_Zp_nat_pow, rule assms)
            have 172: "to_Zp c \<in> carrier Z\<^sub>p "
              apply(rule to_Zp_closed) unfolding c_def
              using A(2) UPQ.UP_car_memE(1) by blast
            have 173: "to_Zp a \<in> carrier Z\<^sub>p "
              apply(rule to_Zp_closed) using assms val_ring_memE by blast
            show ?thesis
              using 172 173 Zp.to_fun_monom[of "to_Zp c" "to_Zp a" n] unfolding Zp.to_fun_def 170 171
              by blast
        qed
        show ?thesis
          using 15 unfolding Zp.to_fun_def 10 2 16 9 unfolding 14 17
          by blast
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma inc_nat_pow:
  assumes "a \<in> carrier Z\<^sub>p"
  shows "\<iota> ([(n::nat)] \<cdot>\<^bsub>Z\<^sub>p\<^esub>a) = [n]\<cdot>(\<iota> a)"
  apply(induction n)
  apply (metis Q\<^sub>p_def Qp.int_inc_zero Qp.nat_mult_zero Zp.add.nat_pow_0 Zp_int_inc_zero' \<iota>_def frac_inc_of_int)
  unfolding Qp.add.nat_pow_Suc Zp.add.nat_pow_Suc
  using Zp_nat_mult_closed assms inc_of_sum by presburger

lemma poly_inc_pderiv:
  assumes "g \<in> carrier (UP Z\<^sub>p)"
  shows "poly_inc (Zp.pderiv g) = UPQ.pderiv (poly_inc g)"
proof fix x
  have 0: "UPQ.pderiv (poly_inc g) x = [Suc x] \<cdot> poly_inc g (Suc x)"
    apply(rule UPQ.pderiv_cfs[of "poly_inc g" x])
    by(rule poly_inc_closed, rule assms)
  have 1: "Zp.pderiv g x = [Suc x] \<cdot>\<^bsub>Z\<^sub>p\<^esub> g (Suc x)"
    by(rule Zp.pderiv_cfs[of g x], rule assms)
  show "poly_inc (Zp.pderiv g) x = UPQ.pderiv (poly_inc g) x"
    unfolding 0  unfolding poly_inc_def 1 apply(rule  inc_nat_pow)
    using Zp.UP_car_memE(1) assms by blast
qed

lemma Zp_hensels_lemma:
  assumes "f \<in> carrier Zp_x"
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "Zp.to_fun (Zp.pderiv f) a \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
  assumes "Zp.to_fun f a \<noteq> \<zero>\<^bsub>Z\<^sub>p \<^esub>"
  assumes "val_Zp (Zp.to_fun f a) > eint 2 * val_Zp (Zp.to_fun (Zp.pderiv f) a)"
  obtains \<alpha> where
       "Zp.to_fun f \<alpha> = \<zero>\<^bsub>Z\<^sub>p\<^esub>" and "\<alpha> \<in> carrier Z\<^sub>p"
       "val_Zp (a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha>) > val_Zp (Zp.to_fun (Zp.pderiv f) a)"
       "val_Zp (a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha>) = val_Zp (divide (Zp.to_fun f a) (Zp.to_fun (Zp.pderiv f) a))"
       "val_Zp (Zp.to_fun (Zp.pderiv f) \<alpha>) = val_Zp (Zp.to_fun (Zp.pderiv f) a)"
proof-
  have "hensel p f a"
    using assms
    by (simp add: Zp_def hensel.intro hensel_axioms.intro padic_integers_axioms)
  then show ?thesis
    using hensel.full_hensels_lemma[of p f a] that
    unfolding Zp_def
    by blast
qed

end
end
