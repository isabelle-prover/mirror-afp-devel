theory Cring_Multivariable_Poly
imports  "HOL-Algebra.Indexed_Polynomials" Padic_Ints.Cring_Poly
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Multivariable Polynomials Over a Commutative Ring\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  This theory extends the content of \texttt{HOL-Algebra.Indexed\_Polynomials}, mainly in the
  context of a commutative base ring. In particular, the ring of polynomials over an arbitrary
  variable set is explicitly witnessed as a ring itself, which is commutative if the base is
  commutative, and a domain if the base ring is a domain. A universal property for polynomial
  evaluation is proved, which allows us to embed polynomial rings in a ring of functions over the
  base ring, as well as construe multivariable polynomials as univariate polynomials over a small
  base polynomial ring.
\<close>

type_synonym 'a monomial = "'a multiset"
type_synonym ('b,'a) mvar_poly = "'a multiset \<Rightarrow> 'b"
type_synonym ('a,'b) ring_hom = "'a \<Rightarrow> 'b"
type_synonym 'a u_poly = "nat \<Rightarrow> 'a"
(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Lemmas about multisets\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  Since multisets function as monomials in this formalization, we'll need some simple lemmas
  about multisets in order to define degree functions and certain lemmas about factorizations.
  Those are provided in this section.
\<close>

lemma count_size:
  assumes "size m \<le> K"
  shows "count m i \<le> K"
  using assms
  by (metis count_le_replicate_mset_subset_eq dual_order.trans order_refl size_mset_mono size_replicate_mset)

text\<open>The following defines the set of monomials with nonzero coefficients for a given polynomial:\<close>

definition monomials_of :: "('a,'c) ring_scheme \<Rightarrow> ('a, 'b) mvar_poly \<Rightarrow> ('b monomial) set" where
"monomials_of R P = {m. P m \<noteq> \<zero>\<^bsub>R\<^esub>}"

context ring
begin

lemma monomials_of_index_free:
  assumes "index_free P i"
  assumes "m \<in> monomials_of R P"
  shows "count m i = 0"
  using assms
  unfolding monomials_of_def index_free_def
  by (meson count_inI mem_Collect_eq)

lemma index_freeI:
  assumes "\<And>m. m \<in> monomials_of R P \<Longrightarrow> count m i = 0"
  shows "index_free P i"
  unfolding index_free_def
proof safe
  fix m
  assume "i \<in># m"
  then have "count m i \<noteq> 0"
    by simp
  then have "m \<notin> monomials_of R P"
    using assms
    by meson
  then show "P m = \<zero>"
    unfolding monomials_of_def
    by blast
qed

text\<open>\texttt{monomials\_of} R is subadditive\<close>

lemma monomials_of_add:
"monomials_of R (P \<Oplus> Q) \<subseteq> (monomials_of R P) \<union> (monomials_of R Q)"
proof
  fix x
  assume "x \<in> monomials_of R (P \<Oplus> Q) "
  then have "P x \<oplus> Q x \<noteq>\<zero>"
    by (simp add: indexed_padd_def monomials_of_def)
  then have "P x \<noteq>\<zero> \<or> Q x \<noteq> \<zero>"
    by auto
  then show "x \<in> (monomials_of R P) \<union> (monomials_of R Q)"
    by (simp add: monomials_of_def)
qed

lemma monomials_of_add_finite:
  assumes "finite (monomials_of R P)"
  assumes "finite (monomials_of R Q)"
  shows "finite (monomials_of R (P \<Oplus> Q))"
  by (meson assms(1) assms(2) finite_Un finite_subset monomials_of_add)

lemma monomials_ofE:
  assumes "m \<in> monomials_of R p"
  shows "p m \<noteq> \<zero>"
  using assms
  unfolding monomials_of_def
  by simp

lemma complement_of_monomials_of:
  assumes "m \<notin> monomials_of R P"
  shows "P m = \<zero>"
  using assms
  unfolding monomials_of_def
  by blast

text\<open>Multiplication by an indexed variable corresponds to adding that index to each monomial:\<close>

lemma monomials_of_p_mult:
"monomials_of R (P \<Otimes> i) = {m. \<exists> n \<in> (monomials_of R P). m = add_mset i n}"
proof
  show "monomials_of R (P \<Otimes> i) \<subseteq> {m. \<exists>n\<in>monomials_of R P. m = add_mset i n}"
    proof
      fix m
      assume A: "m \<in> monomials_of R (P \<Otimes> i)"
      show "m \<in> {m. \<exists>n\<in>monomials_of R P. m = add_mset i n}"
      proof-
        have "(P \<Otimes> i) m \<noteq> \<zero>"
          by (simp add: A monomials_ofE)
        then have "P (m - {# i #}) \<noteq>\<zero>"
          unfolding indexed_pmult_def
          by presburger
        then have 0: "(m - {# i #}) \<in> monomials_of R P"
          by (meson complement_of_monomials_of)
        have 1: " m = add_mset i  (m - {# i #})"
          by (metis \<open>(P \<Otimes> i) m \<noteq> \<zero>\<close> add_mset_remove_trivial_If indexed_pmult_def)
        then show ?thesis using 0 1
          by blast
      qed
    qed
  show "{m. \<exists>n\<in>monomials_of R P. m = add_mset i n} \<subseteq> monomials_of R (P \<Otimes> i)"
    unfolding monomials_of_def indexed_pmult_def
    by auto
qed

lemma monomials_of_p_mult':
"monomials_of R (p \<Otimes> i) = add_mset i ` (monomials_of R p)"
  using  monomials_of_p_mult
  by (simp add: monomials_of_p_mult image_def)

lemma monomials_of_p_mult_finite:
  assumes "finite (monomials_of R P)"
  shows "finite (monomials_of R (P \<Otimes> i))"
  using assms monomials_of_p_mult'[of P i]
  by simp

text\<open>Monomials of a constant either consist of the empty multiset, or nothing:\<close>

lemma monomials_of_const:
"(monomials_of R (indexed_const k)) = (if (k = \<zero>) then {} else {{#}})"
  unfolding monomials_of_def indexed_const_def
  by simp

lemma monomials_of_const_finite:
"finite (monomials_of R (indexed_const k))"
  by (simp add: monomials_of_const)

text\<open>A polynomial always has finitely many monomials:\<close>
lemma monomials_finite:
  assumes "P \<in> indexed_pset K I"
  shows "finite (monomials_of R P)"
  using assms
  apply(induction P)
  using monomials_of_const_finite apply blast
    using monomials_of_add_finite apply blast
      by (simp add: monomials_of_p_mult_finite)
end

(**************************************************************************************************)
(**************************************************************************************************)
    subsection\<open>Turning monomials into polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Constructor for turning a monomial into a polynomial\<close>

definition mset_to_IP :: "('a, 'b) ring_scheme \<Rightarrow> 'c monomial \<Rightarrow> ('a,'c) mvar_poly" where
"mset_to_IP R m n= (if (n = m) then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>)"

definition var_to_IP :: "('a, 'b) ring_scheme \<Rightarrow> 'c \<Rightarrow> ('a,'c) mvar_poly" ("pvar") where
"var_to_IP R i = mset_to_IP R {#i#}"

context ring
begin

lemma mset_to_IP_simp[simp]:
"mset_to_IP R m m = \<one>"
  by (simp add: mset_to_IP_def)

lemma mset_to_IP_simp'[simp]:
  assumes "n \<noteq>m"
  shows "mset_to_IP R m n = \<zero>"
  by (simp add: assms mset_to_IP_def)

lemma(in cring) monomials_of_mset_to_IP:
  assumes "\<one> \<noteq>\<zero>"
  shows "monomials_of R (mset_to_IP R m) = {m}"
  unfolding monomials_of_def mset_to_IP_def
proof
  show "{ma. (if ma = m then \<one> else \<zero>) \<noteq> \<zero>} \<subseteq> {m}"
    by auto
  show "{m} \<subseteq> {ma. (if ma = m then \<one> else \<zero>) \<noteq> \<zero>}"
    using assms by auto
qed

end

text\<open>The set of monomials of a fixed \<open>P\<close> which include a given variable:\<close>

definition monomials_with :: "('a, 'b) ring_scheme \<Rightarrow> 'c \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow> ('c monomial) set" where
"monomials_with R i P = {m. m \<in> monomials_of R P \<and> i \<in># m}"

context ring
begin

lemma monomials_withE:
  assumes "m \<in> monomials_with R i P"
  shows "i \<in># m"
        "m \<in> monomials_of R P"
  using assms unfolding monomials_with_def
  apply blast
     using assms unfolding monomials_with_def
     by blast

lemma monomials_withI:
  assumes "i \<in># m"
  assumes "m \<in> monomials_of R P"
  shows "m \<in> monomials_with R i P"
  using assms
  unfolding monomials_with_def
  by blast

end

text\<open>Restricting a polynomial to be zero outside of a given monomial set:\<close>

definition restrict_poly_to_monom_set ::
  "('a, 'b) ring_scheme \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow> ('c monomial) set \<Rightarrow>('a,'c) mvar_poly"  where
"restrict_poly_to_monom_set R P m_set m = (if m \<in> m_set then P m else \<zero>\<^bsub>R\<^esub>)"

context ring
begin

lemma restrict_poly_to_monom_set_coeff:
  assumes "carrier_coeff P"
  shows "carrier_coeff (restrict_poly_to_monom_set R P Ms)"
  by (metis assms carrier_coeff_def restrict_poly_to_monom_set_def zero_closed)

lemma restrict_poly_to_monom_set_coeff':
  assumes "P \<in> indexed_pset K I"
  assumes "I \<noteq> {}"
  assumes "\<And>m. P m \<in> S"
  assumes "\<zero> \<in> S"
  shows "\<And>m.  (restrict_poly_to_monom_set R P m_set m) \<in> S"
  using assms
  unfolding restrict_poly_to_monom_set_def
  by simp

lemma restrict_poly_to_monom_set_monoms:
  assumes "P \<in> indexed_pset I K"
  assumes "m_set \<subseteq> monomials_of R P"
  shows "monomials_of R (restrict_poly_to_monom_set R P m_set) = m_set"
  using assms
  unfolding monomials_of_def restrict_poly_to_monom_set_def
  by (simp add: subset_iff)
end

(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Degree Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsubsection\<open>Total Degree Function\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)


lemma multi_set_size_count:
  fixes m :: "'c monomial"
  shows "size m \<ge> count m i"
  by (metis count_le_replicate_mset_subset_eq order_refl size_mset_mono size_replicate_mset)

text\<open>Total degree function\<close>

definition total_degree :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> nat" where
"total_degree R P = (if (monomials_of R P = {}) then 0 else Max (size ` (monomials_of R P)))"

context ring
begin

lemma total_degree_ineq:
  assumes "m \<in> monomials_of R P"
  assumes "finite (monomials_of R P)"
  shows "total_degree R P \<ge> size m"
  unfolding total_degree_def using assms
  by force

lemma total_degree_in_monomials_of:
  assumes "monomials_of R P \<noteq> {}"
  assumes "finite (monomials_of R P)"
  obtains m where "m \<in> monomials_of R P \<and> size m = total_degree R P"
    using assms Max_in[of "(size ` monomials_of R P)"] unfolding total_degree_def
    by (metis (mono_tags, lifting) empty_is_image finite_imageI image_iff)

lemma total_degreeI:
  assumes "finite (monomials_of R P)"
  assumes "\<exists>m. m \<in> monomials_of R P \<and> size m = n"
  assumes "\<And>m. m \<in> monomials_of R P \<Longrightarrow> size m \<le> n"
  shows "n = total_degree R P"
proof(cases "monomials_of R P = {}")
  case True
  then show ?thesis
    using assms by blast
next
  case False
  obtain m where m_def: "m \<in> monomials_of R P \<and> size m = n"
    using assms by blast
  have 0: "n \<in> (size ` (monomials_of R P))"
    using m_def
    by blast
  have "\<And>k. k \<in> (size ` (monomials_of R P)) \<Longrightarrow> k \<le> n"
    using assms
    by blast
  then have 1: "\<And>m.  m \<in> (monomials_of R P) \<Longrightarrow> size m\<le> n"
    by blast
  obtain m' where m'_def: "m' \<in> monomials_of R P \<and> size m' = total_degree R P"
    using assms total_degree_in_monomials_of
    by blast
  then have 2: "size m' \<le> n"
    using 1
    by blast
  have 3: "n \<le>size m'"
    using assms m'_def total_degree_ineq by auto
  show ?thesis using 2 3
    using dual_order.antisym m'_def by blast
qed
end

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsubsection\<open>Degree in One Variable\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

definition degree_in_var ::
  "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> 'c \<Rightarrow> nat" where
"degree_in_var R P i =  (if (monomials_of R P = {}) then 0 else Max ((\<lambda>m. count m i) ` (monomials_of R P)))"

context ring
begin

lemma degree_in_var_ineq:
  assumes "m \<in> monomials_of R P"
  assumes "finite (monomials_of R P)"
  shows "degree_in_var R P i \<ge> count m i"
  unfolding degree_in_var_def using assms
  by force

lemma degree_in_var_in_monomials_of:
  assumes "monomials_of R P \<noteq> {}"
  assumes "finite (monomials_of R P)"
  obtains m where "m \<in> monomials_of R P \<and> count m i = degree_in_var R P i"
  using assms Max_in[of "((\<lambda>m. count m i) ` (monomials_of R P))"] unfolding degree_in_var_def
  by (metis (no_types, lifting) empty_is_image finite_imageI image_iff)

lemma degree_in_varI:
  assumes "finite (monomials_of R P)"
  assumes "\<exists>m. m \<in> monomials_of R P \<and> count m i = n"
  assumes "\<And>c. c \<in> monomials_of R P \<Longrightarrow> count c i \<le> n"
  shows "n = degree_in_var R P i"
proof-
  obtain l where l_def: "l \<in> monomials_of R P \<and> count l i = degree_in_var R P i"
    by (metis assms(1) assms(2) degree_in_var_in_monomials_of equals0D)
  have "degree_in_var R P i \<le> n"
    using assms(3) l_def
    by force
  then show ?thesis
    using assms(1) assms(2) dual_order.antisym degree_in_var_ineq
    by fastforce
qed

text\<open>Total degree bounds degree in a single variable:\<close>

lemma total_degree_degree_in_var:
  assumes "finite (monomials_of R P)"
  shows "total_degree R P \<ge> degree_in_var R P i"
proof(cases " (monomials_of R P) = {}")
  case True
  then show ?thesis
    unfolding total_degree_def degree_in_var_def
    by simp
next
  case False
  then   obtain m1 where m1_def: "m1 \<in> monomials_of R P \<and> count m1 i = degree_in_var R P i"
    by (meson assms degree_in_var_in_monomials_of)
  have "size m1 \<ge>count m1 i"
    by (simp add: multi_set_size_count)
  then show ?thesis
    by (simp add: assms local.ring_axioms m1_def order.trans ring.total_degree_ineq)
qed
end

text\<open>The set of monomials of maximal degree in variable \<open>i\<close>:\<close>

definition max_degree_monoms_in_var ::
  "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> 'c \<Rightarrow> ('c monomial) set" where
"max_degree_monoms_in_var R P i = {m. m \<in> monomials_of R P \<and> count m i = degree_in_var R P i}"

context ring
begin

lemma max_degree_monoms_in_var_memI:
  assumes "m \<in> monomials_of R P"
  assumes "count m i = degree_in_var R P i"
  shows "m \<in> max_degree_monoms_in_var R P i"
  using assms unfolding max_degree_monoms_in_var_def
  by blast

lemma max_degree_monoms_in_var_memE:
  assumes "m \<in> max_degree_monoms_in_var R P i"
  shows   "m \<in> monomials_of R P"
          "count m i = degree_in_var R P i"
  using assms unfolding max_degree_monoms_in_var_def
  apply blast
    using assms unfolding max_degree_monoms_in_var_def
    by blast
end

text\<open>The set of monomials of \<open>P\<close> of fixed degree in variable \<open>i\<close>:\<close>

definition fixed_degree_in_var ::
  "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> ('c monomial) set" where
"fixed_degree_in_var R P i n = {m. m \<in> monomials_of R P \<and> count m i = n}"

context ring
begin

lemma fixed_degree_in_var_subset:
"fixed_degree_in_var R P i n \<subseteq> monomials_of R P"
  unfolding fixed_degree_in_var_def
  by blast

lemma fixed_degree_in_var_max_degree_monoms_in_var:
"max_degree_monoms_in_var R P i = fixed_degree_in_var R P i (degree_in_var R P i)"
  unfolding max_degree_monoms_in_var_def fixed_degree_in_var_def
  by auto

lemma fixed_degree_in_varI:
  assumes "m \<in> monomials_of R P"
  assumes "count m i = n"
  shows "m \<in> fixed_degree_in_var R P i n"
  unfolding fixed_degree_in_var_def
  using assms
  by blast

lemma fixed_degree_in_varE:
  assumes "m \<in> fixed_degree_in_var R P i n"
  shows "m \<in> monomials_of R P"
          "count m i = n"
  apply (meson assms fixed_degree_in_var_subset in_mono)
    using assms fixed_degree_in_var_def by force

definition restrict_to_var_deg ::
 "('a,'c) mvar_poly \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c monomial \<Rightarrow> 'a"  where
"restrict_to_var_deg P i n = restrict_poly_to_monom_set R P (fixed_degree_in_var R P i n)"

lemma restrict_to_var_deg_var_deg:
  assumes "finite (monomials_of R P)"
  assumes "Q = restrict_to_var_deg P i n"
  assumes "monomials_of R Q \<noteq> {}"
  shows "n = degree_in_var R Q i"
  apply(rule degree_in_varI)
    apply (metis assms(1) assms(2) fixed_degree_in_varE(1) monomials_ofE restrict_poly_to_monom_set_def
      restrict_to_var_deg_def rev_finite_subset subsetI)
      apply (metis (full_types) assms(2) assms(3) equals0I fixed_degree_in_varE(2)
      monomials_ofE restrict_poly_to_monom_set_def restrict_to_var_deg_def)
        by (metis assms(2) eq_iff fixed_degree_in_varE(2) monomials_ofE restrict_poly_to_monom_set_def restrict_to_var_deg_def)

lemma index_free_degree_in_var[simp]:
  assumes "index_free P i"
  shows "degree_in_var R P i = 0"
proof(cases "monomials_of R P = {}")
  case True
  then show ?thesis
    using assms
    unfolding degree_in_var_def
    by simp
next
  case False
  then have 0: "degree_in_var R P i =  Max ((\<lambda>m. count m i) ` (monomials_of R P))"
    unfolding degree_in_var_def
    by simp
  have"((\<lambda>m. count m i) ` (monomials_of R P)) = {0}"
  proof
    show "(\<lambda>m. count m i) ` monomials_of R P \<subseteq> {0}"
      using False assms monomials_of_index_free[of P i]
      by auto
    show "{0} \<subseteq> (\<lambda>m. count m i) ` monomials_of R P"
      using False  \<open>(\<lambda>m. count m i) ` monomials_of R P \<subseteq> {0}\<close>
      by auto
  qed
  then show ?thesis using 0
    by simp
qed

lemma degree_in_var_index_free:
  assumes "degree_in_var R P i = 0"
  assumes "finite (monomials_of R P)"
  shows "index_free P i"
  apply(rule index_freeI)
  by (metis assms(1) assms(2) degree_in_var_ineq le_zero_eq)

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Constructing the Multiplication Operation on the Ring of Indexed Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

  (**********************************************************************)
  (**********************************************************************)
  subsubsection\<open>The Set of Factors of a Fixed Monomial\<close>
  (**********************************************************************)
  (**********************************************************************)

  text\<open>The following function maps a monomial to the set of monomials which divide it:\<close>

definition mset_factors :: "'c monomial \<Rightarrow> ('c monomial) set" where
"mset_factors m = {n. n \<subseteq># m}"

context ring
begin

lemma monom_divides_factors:
"n \<in> (mset_factors m)\<longleftrightarrow> n \<subseteq># m"
  unfolding mset_factors_def by auto

lemma mset_factors_mono:
  assumes "n \<subseteq># m"
  shows "mset_factors n \<subseteq> mset_factors m"
  unfolding mset_factors_def
  by (simp add: Collect_mono_iff assms subset_mset.order_trans)

lemma mset_factors_size_bound:
  assumes "n \<in> mset_factors m"
  shows "size n \<le> size m"
  using assms
  unfolding mset_factors_def
  by (simp add: size_mset_mono)

lemma sets_to_inds_finite:
  assumes "finite I"
  shows "finite S \<Longrightarrow> finite (Pi\<^sub>E S (\<lambda>_. I))"
  using assms
  by (simp add: finite_PiE)

end

    (**********************************************************************************************)
    (**********************************************************************************************)
    subsubsection\<open>Finiteness of the Factor Set of a Monomial\<close>
    (**********************************************************************************************)
    (**********************************************************************************************)

text\<open>
  This section shows that any monomial m has only finitely many factors. This is done by mapping
  the set of factors injectively into a finite extensional function set. Explicitly, a monomial is
  just mapped to its count function, restricted to the set of indices where the count is nonzero.
\<close>

definition mset_factors_to_fun ::
  "('a,'b) ring_scheme \<Rightarrow> 'c monomial \<Rightarrow> 'c monomial \<Rightarrow> ('c \<Rightarrow> nat)" where
"mset_factors_to_fun R m n = (if (n \<in> mset_factors m) then
                                           (restrict  (count n) (set_mset m)) else undefined)"
context ring
begin

lemma mset_factors_to_fun_prop:
  assumes "size m = n"
  shows "mset_factors_to_fun R m \<in> (mset_factors m) \<rightarrow> (Pi\<^sub>E (set_mset m) (\<lambda>_. {0.. n}))"
proof
  fix x
  assume A: "x \<in> (mset_factors m)"
  show "mset_factors_to_fun R m x \<in> (set_mset m) \<rightarrow>\<^sub>E {0..n} "
  proof
    show "\<And>xa. xa \<in># m \<Longrightarrow> mset_factors_to_fun R m x xa \<in> {0..n}"
      proof-
        fix y
        assume Ay: "y \<in># m"
        show P0: "mset_factors_to_fun R m x y \<in> {0..n}"
        proof-
          have "mset_factors_to_fun R m x = restrict (count x) (set_mset m)"
            using A  unfolding mset_factors_to_fun_def
            by simp
          then have "mset_factors_to_fun R m x y  = count x y"
            using Ay
            by simp
          then show ?thesis
            using A INTEG.R.mset_factors_size_bound assms count_size by fastforce
        qed
      qed
    fix z
    assume Ay: "z \<notin>#m"
    show "mset_factors_to_fun R m x z = undefined"
      using A Ay unfolding mset_factors_to_fun_def
      by simp
  qed
qed

lemma mset_factors_to_fun_inj:
  shows "inj_on (mset_factors_to_fun R m) (mset_factors m) "
proof
  fix x y
  assume A: "x \<in> mset_factors m" "y \<in> mset_factors m"
  show "mset_factors_to_fun R m x = mset_factors_to_fun R m y \<Longrightarrow> x = y"
  proof-
    assume A0:  "mset_factors_to_fun R m x = mset_factors_to_fun R m y"
    show " x = y"
    proof-
      have "\<And>i. count x i = count y i"
      proof- fix i
        show "count x i = count y i"
        proof(cases "i \<in># m")
          case True
          then show ?thesis using A0 A unfolding mset_factors_to_fun_def
            by (metis restrict_def)
        next
          case False
          then show ?thesis
             using A0 A unfolding mset_factors_to_fun_def
             by (metis monom_divides_factors count_inI mset_subset_eqD)
        qed
      qed
      then show ?thesis
        using multiset_eqI by blast
    qed
  qed
qed

lemma finite_target:
"finite (Pi\<^sub>E (set_mset m) (\<lambda>_. {0..(n::nat)}))"
proof-
  have 0: "finite (set_mset m)"
    by simp
  have 1: "finite ({0..n})"
    by simp
  then show ?thesis using 0
    by (simp add: finite_PiE)
qed

text\<open>A multiset has only finitely many factors:\<close>

lemma mset_factors_finite[simp]:
"finite (mset_factors m)"
proof-
  have 0: "inj_on (mset_factors_to_fun R m) (mset_factors m) "
    by (simp add: mset_factors_to_fun_inj)
  have 1: "(mset_factors_to_fun R m) \<in> (mset_factors m) \<rightarrow> (Pi\<^sub>E (set_mset m) (\<lambda>_. {0 .. (size m)}))"
    by (metis mset_factors_to_fun_prop)
  have 2: "finite (Pi\<^sub>E (set_mset m) (\<lambda>_. {0 .. (size m)}))"
    by (simp add: finite_target)
  have 3: "((mset_factors_to_fun R m) ` (mset_factors m)) \<subseteq> (Pi\<^sub>E (set_mset m) (\<lambda>_. {0 .. (size m)}))"
    using 1 2
    by blast
  then have "finite ((mset_factors_to_fun R m) ` (mset_factors m))"
    using 2 finite_subset by auto
  then show ?thesis using 0 1 2
    finite_imageD[of "mset_factors_to_fun R m" "mset_factors m" ]
    by blast
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Definition of Indexed Polynomial Multiplication.\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context ring
begin

text\<open>Monomial division:\<close>

lemma monom_divide:
  assumes "n \<in> mset_factors m"
  shows "(THE k. n + k = m ) = m - n "
  apply(rule the_equality)
  using assms unfolding mset_factors_def
  apply simp
    using assms unfolding mset_factors_def
    by auto

text\<open>A monomial is a factor of itself:\<close>

lemma m_factor[simp]:
"m \<in> mset_factors m"
  using local.ring_axioms ring.monom_divides_factors by blast

end

text\<open>The definition of polynomial multiplication:\<close>

definition P_ring_mult :: "('a, 'b) ring_scheme \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow> 'c monomial \<Rightarrow> 'a"
  where
"P_ring_mult R P Q m = (finsum R (\<lambda>x. (P x) \<otimes>\<^bsub>R\<^esub> (Q (m - x))) (mset_factors m))"

abbreviation(in ring) P_ring_mult_in_ring (infixl "\<Otimes>\<^sub>p" 65)where
"P_ring_mult_in_ring \<equiv>  P_ring_mult R"

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Distributivity Laws for Polynomial Multiplication\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context ring
begin

lemma P_ring_rdistr:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  assumes "carrier_coeff c"
  shows "a \<Otimes>\<^sub>p (b \<Oplus> c) = (a \<Otimes>\<^sub>p b)\<Oplus> (a \<Otimes>\<^sub>p c)"
proof
  fix m
  show "(a \<Otimes>\<^sub>p (b \<Oplus> c)) m = (a \<Otimes>\<^sub>p b \<Oplus> (a \<Otimes>\<^sub>p c)) m"
  proof-
    have RHS: "(a \<Otimes>\<^sub>p b \<Oplus> (a \<Otimes>\<^sub>p c)) m =
                  (\<Oplus>x\<in>mset_factors m. a x \<otimes> b (m - x)) \<oplus> (\<Oplus>x\<in>mset_factors m. a x \<otimes> c (m - x))"
      unfolding indexed_padd_def P_ring_mult_def by auto
    have LHS: "(a \<Otimes>\<^sub>p (b \<Oplus> c)) m=
                  ( \<Oplus>x\<in>mset_factors m. a x \<otimes> b (m - x) \<oplus> a x \<otimes> c (m - x))"
      unfolding indexed_padd_def  P_ring_mult_def
      by (meson assms(1) assms(2) assms(3) local.ring_axioms r_distr ring.carrier_coeff_def)
    have RHS': "(a \<Otimes>\<^sub>p b \<Oplus> (a \<Otimes>\<^sub>p c)) m =
                  (\<Oplus>x\<in>mset_factors m. a x \<otimes> b (m - x) \<oplus> a x \<otimes> c (m - x))"
    proof-
      have 0: "(\<lambda>x. a x \<otimes> b (m - x)) \<in> mset_factors m \<rightarrow> carrier R"
      proof
        fix x assume "x \<in> mset_factors m"
        then show "a x \<otimes> b (m - x) \<in> carrier R"
          using assms carrier_coeffE
          by blast
      qed
      have 1: "(\<lambda>x. a x \<otimes> c (m - x)) \<in> mset_factors m \<rightarrow> carrier R"
      proof
        fix x assume "x \<in> mset_factors m"
        then show "a x \<otimes> c (m - x) \<in> carrier R"
          using assms carrier_coeffE
          by blast
      qed
      then show ?thesis
        using 0 1 RHS assms finsum_addf[of "\<lambda>x. a x \<otimes> b (m - x)" "mset_factors m"
                                                    "\<lambda>x. a x \<otimes> c (m - x)"]
        by metis
    qed
    show ?thesis using LHS RHS' by auto
  qed
qed

lemma P_ring_ldistr:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  assumes "carrier_coeff c"
  shows "  (b \<Oplus> c) \<Otimes>\<^sub>p  a = (b \<Otimes>\<^sub>p a)\<Oplus> (c \<Otimes>\<^sub>p a)"
proof
  fix m
  show "((b \<Oplus> c) \<Otimes>\<^sub>p  a) m = ((b \<Otimes>\<^sub>p a)\<Oplus> (c \<Otimes>\<^sub>p a)) m"
  proof-
    have RHS: "((b \<Otimes>\<^sub>p a)\<Oplus> (c \<Otimes>\<^sub>p a)) m =
                  (\<Oplus>x\<in>mset_factors m. b x \<otimes> a (m - x)) \<oplus> (\<Oplus>x\<in>mset_factors m. c x \<otimes> a (m - x))"
      unfolding indexed_padd_def P_ring_mult_def by auto
    have LHS: "((b \<Oplus> c) \<Otimes>\<^sub>p  a)  m=
                  ( \<Oplus>x\<in>mset_factors m. b x \<otimes> a (m - x) \<oplus> c x \<otimes> a (m - x))"
      unfolding indexed_padd_def  P_ring_mult_def
      by (meson assms(1) assms(2) assms(3) l_distr local.ring_axioms ring.carrier_coeff_def)
    have RHS': "((b \<Otimes>\<^sub>p a)\<Oplus> (c \<Otimes>\<^sub>p a)) m =
                  (\<Oplus>x\<in>mset_factors m. b x \<otimes> a (m - x) \<oplus> c x \<otimes> a (m - x))"
    proof-
      have 0: "(\<lambda>x. b x \<otimes> a (m - x)) \<in> mset_factors m \<rightarrow> carrier R"
      proof
        fix x assume "x \<in> mset_factors m"
        then show "b x \<otimes> a (m - x) \<in> carrier R"
          using assms carrier_coeffE
          by blast
      qed
      have 1: "(\<lambda>x. c x \<otimes> a (m - x)) \<in> mset_factors m \<rightarrow> carrier R"
      proof
        fix x assume "x \<in> mset_factors m"
        then show "c x \<otimes> a (m - x) \<in> carrier R"
          using assms carrier_coeffE
          by blast
      qed
      then show ?thesis
        using 0 1 RHS assms finsum_addf[of "\<lambda>x. b x \<otimes> a (m - x)" "mset_factors m"
                                                    "\<lambda>x. c x \<otimes> a (m - x)"]
        by metis
    qed
    show ?thesis using LHS RHS' by auto
  qed
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Multiplication Commutes with \texttt{indexed\_pmult}\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context ring
begin

text\<open>This lemma shows how we can write the factors of a monomial $m$ times a variable $i$ in terms
      of the factors of m:\<close>

lemma mset_factors_add_mset:
"mset_factors (add_mset i m) = mset_factors m \<union> add_mset i ` (mset_factors m)"
proof
  show "mset_factors (add_mset i m) \<subseteq> mset_factors m \<union> add_mset i ` mset_factors m"
  proof fix x
    assume A: "x \<in> mset_factors (add_mset i m)"
    show "x \<in> mset_factors m \<union> add_mset i ` mset_factors m"
    proof(cases "i \<in># x")
      case True
      then have "x - {#i#} \<subseteq># m"
        using A INTEG.R.monom_divides_factors subset_eq_diff_conv by force
      then show ?thesis
        by (metis INTEG.R.monom_divides_factors True UnI2 add_mset_remove_trivial image_iff multi_member_split)
    next
      case False
      have 0: "x \<subseteq># add_mset i m"
        using A INTEG.R.monom_divides_factors by blast
      hence "x \<subseteq>#  m"
        using mset_subset_eqI[of x m] 0 False
        by (metis count_add_mset count_greater_zero_iff count_inI less_Suc_eq_le
            subseteq_mset_def union_single_eq_member)
      thus ?thesis
        using INTEG.R.monom_divides_factors by blast
    qed
  qed
  show "mset_factors m \<union> add_mset i ` mset_factors m \<subseteq> mset_factors (add_mset i m)"
  proof fix x assume A: "x \<in> mset_factors m \<union> add_mset i ` mset_factors m"
    have "x \<subseteq># add_mset i m"
    proof(cases "x \<in> mset_factors m")
      case True
      then have "x \<subseteq># m"
        by (simp add: INTEG.R.monom_divides_factors)
      hence "(\<And>a. count x a \<le> count (add_mset i m) a)"
        using mset_subset_eq_count[of x m] count_add_mset[of i m]
              nat_le_linear not_less_eq_eq by fastforce
      thus ?thesis
        using mset_subset_eqI by blast
    next
      case False
      then obtain n where n_def: "n \<in> mset_factors m \<and> x = add_mset i n"
        using A by blast
      then have "x \<subseteq># add_mset i m"
        by (simp add: INTEG.R.monom_divides_factors)
      then show ?thesis
        by simp
    qed
    thus "x \<in> mset_factors (add_mset i m)"
      by (simp add: INTEG.R.monom_divides_factors)
  qed
qed

end
(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Associativity of Polynomial Multiplication.\<close>
(**************************************************************************************************)
(**************************************************************************************************)
context ring
begin

lemma finsum_eq:
  assumes "f \<in> S \<rightarrow> carrier R"
  assumes "g \<in> S \<rightarrow> carrier R"
  assumes "(\<lambda> x \<in> S. f x) = (\<lambda> x \<in> S. g x)"
  shows " finsum R f S = finsum R g S"
        by (metis assms(1) assms(3) finsum_cong' restrict_apply')

lemma finsum_eq_induct:
  assumes "f \<in> S \<rightarrow> carrier R"
  assumes "g \<in> T \<rightarrow> carrier R"
  assumes "finite S"
  assumes "finite T"
  assumes "bij_betw h S T"
  assumes "\<And>s. s \<in> S \<Longrightarrow> f s = g (h s)"
  shows "finite U \<Longrightarrow> U \<subseteq> S \<Longrightarrow> finsum R f U = finsum R g (h ` U)"
  apply(induct rule: finite_induct)
  apply (simp; fail)
proof-
  fix x
  fix F :: "'c set"
  assume F_fin: "finite F"
  assume x_not_in: "x \<notin> F"
  assume IH: "(F \<subseteq> S \<Longrightarrow> finsum R f F = finsum R g (h ` F)) "
  show "insert x F \<subseteq> S \<Longrightarrow> finsum R f (insert x F) = finsum R g (h ` insert x F)"
  proof-
    assume A: "insert x F \<subseteq> S"
    then have F_sub: "F \<subseteq>S"
      by simp
    have x_in: "x \<in> S"
      using A by blast
    have fx_in: "f x \<in>  carrier R"
      using x_in assms(1)
      by auto
    have ghx_fx_eq:
      "f x = g (h x)"
      using x_in assms
      by blast
    have I: "finsum R f F = finsum R g (h ` F)"
      using F_sub IH by blast
    have f_fact: "f \<in> F \<rightarrow> carrier R "
      using assms(1) F_sub
      by blast
    have "finsum R f (insert x F) = (f x) \<otimes>\<^bsub>add_monoid R\<^esub> (finsum R f F) "
      using F_fin  x_not_in comm_monoid.finprod_insert[of "(add_monoid R)" F x f ]
      unfolding finsum_def
      using f_fact fx_in local.add.comm_monoid_axioms
      by auto
    have "finsum R g (h ` insert x F) = finsum R g (insert (h x) (h ` F))"
      by simp
    then have "finsum R g (h ` insert x F) = (g (h x)) \<otimes>\<^bsub>add_monoid R\<^esub> finsum R g (h ` F)"
    proof-
       have 0: "finite (h ` F)"
         by (simp add: F_fin)
       have 1: "h x \<notin> h ` F"
       proof-
         have 10: "bij_betw h F (h` F)"
           using assms(5) F_sub bij_betw_subset
           by blast
         show ?thesis
         proof
           assume "h x \<in> h ` F "
           then  obtain s where s_def: "s \<in> F \<and> h s = h x"
             using 10
             by auto
           have "s \<in> S"
             using F_sub s_def by blast
           then have "s = x"
             using x_in assms(5)
               s_def
             unfolding bij_betw_def inj_on_def
             by blast
           then show False using x_not_in
             using s_def by blast
         qed
       qed
       have 2: "g \<in> h ` F \<rightarrow> carrier (add_monoid R)"
       proof
         fix y
         assume Ay: "y \<in> h ` F"
         then obtain s where s_def: "y = h s \<and> s \<in> F"
           by blast
         then have s_S: "s \<in> S"
           using F_sub by blast
         have "h ` F \<subseteq> T"
           using F_sub assms(5)
           unfolding bij_betw_def
           by blast
         then have "g y \<in> carrier R"
           using Ay assms(2)
           by blast
         then show "g y \<in> carrier (add_monoid R)"
           by simp
       qed
       have "g (h x) \<in> carrier (add_monoid R)"
         using fx_in ghx_fx_eq
         by auto
       then show ?thesis
         using 0 1 2 comm_monoid.finprod_insert[of "(add_monoid R)" "(h ` F)"  "h x" g ]
         unfolding finsum_def
         by (simp add: local.add.comm_monoid_axioms)
    qed
    then have "finsum R g (h ` insert x F) = f x  \<otimes>\<^bsub>add_monoid R\<^esub> (finsum R f F)"
      using I ghx_fx_eq by auto
    then show ?thesis
      by (simp add: \<open>finsum R f (insert x F) = f x \<otimes>\<^bsub>add_monoid R\<^esub> finsum R f F\<close>)
  qed
qed

lemma finsum_bij_eq:
  assumes "f \<in> S \<rightarrow> carrier R"
  assumes "g \<in> T \<rightarrow> carrier R"
  assumes "finite S"
  assumes "bij_betw h S T"
  assumes "\<And>s. s \<in> S \<Longrightarrow> f s = g (h s)"
  shows "finsum R f S = finsum R g T"
proof-
  have 0: "finite T"
    using assms bij_betw_finite
    by blast
  have 1: "(\<And>s. s \<in> S \<Longrightarrow> f s = g (h s)) "
    using assms
    by blast
  have "(\<And>s. s \<in> S \<Longrightarrow> f s = g (h s)) \<Longrightarrow> finite S \<Longrightarrow> S \<subseteq> S \<Longrightarrow> finsum R f S = finsum R g (h ` S)"
    using 0 assms finsum_eq_induct[of f S g T h S ]
  by blast
  then have "finsum R f S = finsum R g (h ` S)"
    using assms(5) assms(3)
    by blast
  then show ?thesis
    using assms(5) assms(4) bij_betw_imp_surj_on
    by blast
qed

lemma monom_comp:
  assumes "x \<subseteq># m"
  assumes "y \<subseteq># m - x"
  shows "x \<subseteq># m - y"
using assms
  by (metis add_diff_cancel_left' subset_eq_diff_conv
      subset_mset.le_diff_conv2 subset_mset.order_refl subset_mset.order_trans)

lemma monom_comp':
  assumes "x \<subseteq># m"
  assumes "y = m - x"
  shows "x = m - y"
  using assms
  by (metis add_diff_cancel_right' subset_mset.add_diff_inverse)

text \<open>
  This lemma turns iterated sums into sums over a product set. The first lemma is only a technical
  phrasing of \texttt{double\_finsum'} to facilitate an inductive proof, and likely can and should
  be simplified.
\<close>

lemma double_finsum_induct:
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> finite (F s)"
  assumes "P = (\<lambda>S. {(s, t). s \<in> S \<and>  t \<in> (F s)})"
  assumes "\<And>s y. s \<in> S \<Longrightarrow> y \<in> (F s) \<Longrightarrow> g s y \<in> carrier R"
  shows "finite T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> finsum R (\<lambda>s. finsum R (g s) (F s)) T =
         finsum R (\<lambda> c. g (fst c) (snd c)) (P  T)"
  apply(induct rule: finite_induct)
  apply (simp add: assms(3); fail)
proof-
  fix x
  fix T :: "'c set"
  assume AT: "finite T"
  assume x_notin: "x \<notin> T"
  assume IH: "(T \<subseteq> S \<Longrightarrow> (\<Oplus>s\<in>T. finsum R (g s) (F s)) = (\<Oplus>c\<in>P T. g (fst c) (snd c)))"
  assume A: "insert x T \<subseteq>S"
  show " (\<Oplus>s\<in>insert x T. finsum R (g s) (F s)) = (\<Oplus>c\<in>P (insert x T). g (fst c) (snd c))"
  proof-
    have 0: "(\<lambda>s. finsum R (g s) (F s)) \<in> T \<rightarrow> carrier R"
    proof
      fix v
      assume A0: "v \<in> T"
      then have A1: "v \<in> S"
        using A by blast
      then show "finsum R (g v) (F v) \<in> carrier R"
      proof-
        have 00: "finite (F v)"
          using assms A
          using \<open>v \<in> T\<close> by blast
        have "g v \<in> F v \<rightarrow> carrier R"
        proof
          fix l assume "l \<in> F v"
          then show "g v l \<in> carrier R"
            using A1 assms(4)[of v l]
            by blast
        qed
        then show ?thesis
          using finsum_closed by blast
      qed
    qed
    have 1: "finsum R (g x) (F x) \<in> carrier R"
    proof-
      have "x \<in> S"
        using A by blast
      then show ?thesis using assms(4) finsum_closed[of "(g x)" "F x"]
        by blast
    qed
    have 2: " (\<Oplus>s\<in>insert x T. finsum R (g s) (F s)) = finsum R (g x) (F x) \<oplus> (\<Oplus>s\<in> T. finsum R (g s) (F s))"
      using 0 1 finsum_insert[of T x "(\<lambda>s. finsum R (g s) (F s))"] AT x_notin
      by blast
    have 3: "P (insert x T) = P {x} \<union> P T"
    proof
      show "P (insert x T) \<subseteq> P {x} \<union> P T"
      proof
        fix y
        assume "y \<in> P (insert x T)"
        then show "y \<in> P {x} \<union> P T"
          using assms
          by blast
      qed
      show "P {x} \<union> P T \<subseteq> P (insert x T)"
      proof
        fix y
        assume Ay: "y \<in> P {x} \<union> P T"
        show "y  \<in> P (insert x T)"
        proof(cases "y \<in> P {x}")
          case True
          then have "y \<in> ({(s, t). s \<in> {x} \<and> t \<in> F s})"
            using assms(3) by auto
          then have "fst y = x \<and> snd y \<in> F x"
            using Product_Type.Collect_case_prodD by auto
          then show ?thesis using assms(3)
            using fst_def by auto
        next
          case False
          then have "y \<in> P T"
            using Ay
            by blast
          then have "y \<in> ({(s, t). s \<in> T \<and> t \<in> F s})"
            using assms(3) by blast
          then obtain s t where st_def: "y = (s, t) \<and>s \<in> T \<and> t \<in> F s"
            by blast
          then have "y = (s, t) \<and>s \<in> (insert x T) \<and> t \<in> F s"
            by blast
          then show ?thesis using assms(3)
            by simp
        qed
      qed
    qed
    have 4: "P {x} \<inter> P T = {}"
    proof
      show "P {x} \<inter> P T \<subseteq> {}"
      proof
        fix y
        assume B: "y \<in> P {x} \<inter> P T"
        then have "fst y = x"
        proof-
          have "y \<in> {(s, t). s \<in> {x} \<and> t \<in> F s}"
            using assms(3) B by auto
          then obtain s t where "y = (s, t) \<and> s \<in> {x} \<and> t \<in> F s"
            by blast
          then show ?thesis
            by auto
        qed
        have "fst y \<in> T"
        proof-
          have "y \<in> {(s, t). s \<in> T \<and> t \<in> F s}"
            using assms(3) B by auto
          then obtain s t where "y = (s, t) \<and> s \<in> T \<and> t \<in> F s"
            by blast
          then show ?thesis
            by simp
        qed
        then have False
          using x_notin
          by (simp add: \<open>fst y = x\<close>)
        then show "y \<in> {}"
          by simp
      qed
      show "{} \<subseteq> P {x} \<inter> P T"
        by simp
    qed
    have 5: "(\<lambda>c. g (fst c) (snd c)) \<in> P {x} \<rightarrow> carrier R"
    proof
      fix y
      assume X0: "y \<in> P {x}"
      obtain s t where st_def: "y = (s, t) \<and> (s, t) \<in> P {x}"
        by (metis X0 old.prod.exhaust)
      then have st: "s = x \<and> t \<in> F x"
        using assms(3) by blast
      then have "g (fst y) (snd y) = g x t \<and>t \<in> F x"
        by (simp add: st_def)
      then show "g (fst y) (snd y) \<in> carrier R"
        using assms(4)[of x t] A
        by simp
    qed
    have 6: "(\<lambda>c. g (fst c) (snd c)) \<in> P T \<rightarrow> carrier R"
    proof
      fix y
      assume X0: "y \<in> P T"
      obtain s t where st_def: "y = (s, t) \<and> (s, t) \<in> P T"
        by (metis X0 old.prod.exhaust)
      then have st: "s \<in> T \<and> t \<in> F s"
        using assms(3) by blast
      then have "g (fst y) (snd y) = g s t \<and>t \<in> F s"
        by (simp add: st_def)
      then show "g (fst y) (snd y) \<in> carrier R"
        using assms(4)[of s t] A st
        by auto
    qed
    have 07: "\<And>x. x \<in> S \<Longrightarrow>  finite (P {x})"
    proof-
      fix x
      assume "x \<in> S"
      have "bij_betw snd (P {x}) (F x)"
        unfolding bij_betw_def
      proof
        show "inj_on snd (P {x})"
        proof
          fix a b
          assume Aa: "a \<in> P {x}"
          assume Ab: "b \<in> P {x}"
          have 0: "fst a = x"
          proof-
            have" a \<in> {(s, t). s \<in> {x} \<and> t \<in> F s} "
              using Aa  assms(3)
              by blast
            then obtain s t where st_def: "a = (s, t) \<and> s \<in> {x} \<and> t \<in> F s"
              by blast
            then show ?thesis
              by auto
          qed
          have 1: "fst b = x"
          proof-
            have" b \<in> {(s, t). s \<in> {x} \<and> t \<in> F s} "
              using Ab  assms(3)
              by blast
            then obtain s t where st_def: "b = (s, t) \<and> s \<in> {x} \<and> t \<in> F s"
              by blast
            then show ?thesis
              by auto
          qed
          show "snd a = snd b \<Longrightarrow> a = b"
            using 0 1
            by (simp add: prod_eqI)
        qed
        show "snd ` P {x} = F x"
        proof
          show "snd ` P {x} \<subseteq> F x"
          proof
            fix y
            assume 0: "y \<in> snd ` P {x}"
            then obtain q where q_def: " q \<in> P {x} \<and> y = snd q"
              by blast
            then obtain s t where st: "q = (s, t) \<and> s \<in> {x} \<and> t \<in> F s"
              using assms(3) by blast
            then have  1: "s = x"
              by blast
            have 2: "snd q = t"
              by (simp add: st)
            then show "y \<in> F x"
              using q_def st by blast
          qed
          show "F x \<subseteq> snd ` P {x}"
          proof
            fix y
            assume "y \<in> F x"
            then have C: "(x, y) \<in> P {x}"
              using assms(3)
              by simp
            then have "y = snd (x, y)"
              by auto
            then show "y \<in> snd ` P {x}"
              using C
              by blast
          qed
        qed
      qed
      then show "finite (P {x})"
        using assms(2)[of x] bij_betw_finite
        \<open>x \<in> S\<close>
        by blast
    qed
    have 7: "finite (P {x})"
      using 07 A
      by blast
    have 8: "finite (P T)"
    proof-
      have "\<And>D. finite D \<Longrightarrow> D \<subseteq> S \<Longrightarrow> finite (P D)"
      proof-
        fix D
        show "finite D \<Longrightarrow> D \<subseteq> S  \<Longrightarrow> finite (P D)"
          apply(induct rule: finite_induct)
        proof-
          have "P {} = {}" using assms(3)
            by blast
          then show "finite (P {})"
            by auto
          show "\<And>x F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> (F \<subseteq> S \<Longrightarrow> finite (P F)) \<Longrightarrow> insert x F \<subseteq> S \<Longrightarrow> finite (P (insert x F))"
          proof-
            fix x
            fix Q :: "'c set "
            assume fin: "finite Q"
            assume notin: "x \<notin> Q"
            assume fin_pf: "(Q \<subseteq> S \<Longrightarrow> finite (P Q))"
            assume I: "insert x Q \<subseteq> S "
            show "finite (P (insert x Q))"
            proof-
              have x_in: "x \<in> S"
                using I by blast
              have 0: "(P (insert x Q)) \<subseteq> (P Q) \<union> P {x}"
              proof
                fix y
                assume "y \<in> P (insert x Q)"
                obtain s t where st: "y = (s, t) \<and> s \<in> (insert x Q) \<and> t \<in> F s"
                  using assms(3) x_in  \<open>y \<in> P (insert x Q)\<close>
                  by blast
                show "y \<in> (P Q) \<union> P {x}"
                proof(cases "s \<in> Q")
                  case True
                  then have "y \<in> P Q"
                    using st assms(3)
                    by simp
                  then show ?thesis using st assms(3)
                    by blast
                next
                  case False
                  then have "s = x"
                    using st by blast
                  then have  "s \<in>{x} \<and> t \<in> F s"
                    using st by blast
                  then have "y \<in> P {x}"
                    using st assms(3)
                    by auto
                  then show ?thesis by auto
                qed
              qed
              have 1: "finite  (P Q)"
                using I fin_pf by blast
              have "finite (P {x})"
                using "07" x_in by blast
              then show ?thesis using 0 1
                using finite_subset by auto
            qed
          qed
        qed
      qed
      then show ?thesis
        using A AT by blast
    qed
    have 9: "(\<Oplus>q\<in>P (insert x T). g (fst q) (snd q)) =
          (\<Oplus>q\<in>P T. g (fst q) (snd q)) \<oplus> (\<Oplus>q\<in>P {x}. g (fst q) (snd q))"
      using 8 7 6 5 4 3 finsum_Un_disjoint[of "P {x}" "P T" "\<lambda>q. g (fst q) (snd q)"]
      by (simp add: "7" \<open>\<lbrakk>finite (P {x}); finite (P T); P {x} \<inter> P T = {}; (\<lambda>p. g (fst p) (snd p))
           \<in> P {x} \<rightarrow> carrier R; (\<lambda>p. g (fst p) (snd p)) \<in> P T \<rightarrow> carrier R\<rbrakk> \<Longrightarrow>
           (\<Oplus>p\<in>P {x} \<union> P T. g (fst p) (snd p)) = (\<Oplus>p\<in>P {x}. g (fst p) (snd p)) \<oplus>
             (\<Oplus>p\<in>P T. g (fst p) (snd p))\<close> add.m_comm)
    have 10: "(\<Oplus>p\<in>P (insert x T). g (fst p) (snd p))
        =  (\<Oplus>s\<in>T. finsum R (g s) (F s))\<oplus> (\<Oplus>p\<in>P {x}. g (fst p) (snd p))"
      using IH 9 A
      by auto
    have 11: "(\<Oplus>p\<in>P {x}. g (fst p) (snd p)) = finsum R (g x) (F x)"
    proof-
      obtain h :: "('c \<times> 'd) \<Rightarrow> 'd" where h_def: "h = snd"
        by simp
      have 110: "bij_betw h (P {x}) (F x)"
        unfolding bij_betw_def
      proof
        show "inj_on h (P {x})"
          unfolding inj_on_def
        proof
          fix q
          assume Ap: "q \<in>  P {x}"
          show " \<forall>y\<in>P {x}. h q = h y \<longrightarrow> q = y"
          proof
            fix y
            assume q_def: "y \<in> P {x}"
            then have C0: "fst y = x"
               using assms(3)
               by (simp add: case_prod_beta)
            have C1: "fst q = x"
              using assms(3) Ap
               by (simp add: case_prod_beta)
             show  "h q = h y \<longrightarrow> q = y"
               using C0 C1 h_def
               by (simp add: prod_eq_iff)
          qed
        qed
        show "h ` P {x} = F x"
        proof
          show "h ` P {x} \<subseteq> F x"
          proof
            fix y
            assume "y \<in> h ` P {x}"
            then obtain d where d_def: "y = h d \<and> d \<in> P {x}"
              by blast
            then obtain s t where st_def: "d = (s, t)"
              by (meson surj_pair)
            then have "s = x \<and> t \<in> F x"
              using assms(3) d_def
              by blast
            then  show "y \<in> F x"
              using assms(3)
              by (simp add: d_def h_def st_def)
          qed
          show "F x \<subseteq> h ` P {x}"
          proof
            fix y
            assume E0:  "y \<in> F x"
            have E1: "y = h (x , y)"
              by (simp add: h_def)
            have "(x, y) \<in> P {x}"
              using E0 assms(3) by blast
            then show "y \<in> h ` P {x} "
              using E1 assms(3) by blast
          qed
        qed
      qed
      have 111: "g x \<in> F x \<rightarrow> carrier R "
      proof
        fix y
        assume "y \<in> F x"
        then show "g x y \<in> carrier R"
          using assms A
          by blast
      qed
      have 112: "(\<And>s. s \<in> P {x} \<Longrightarrow> g (fst s) (snd s) = g x (h s))"
      proof-
        fix s
        assume "s \<in> P{x}"
        then have "s \<in> {(s, t). s = x \<and> t \<in> F s}"
          using assms(3) by blast
        then obtain t where "s = (x, t) \<and> t \<in> F x"
          using assms(3)
          by blast
        then show "g (fst s) (snd s) = g x (h s)"
          by (simp add: h_def)
      qed



      show ?thesis using 5 7  110 111 112 finsum_bij_eq[of "\<lambda>p. g (fst p) (snd p)" "P {x}" "g x" "F x" h ]
        by auto
    qed
    have 12: "(\<Oplus>p\<in>P (insert x T). g (fst p) (snd p))
        =  (\<Oplus>s\<in>T. finsum R (g s) (F s))\<oplus> finsum R (g x) (F x)"
      using 10 11 by auto
    then show ?thesis using 2
      by (simp add: "2" "0" "1" add.m_comm)
  qed
qed

lemma double_finsum:
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> finite (F s)"
  assumes "P = {(s, t). s \<in> S \<and>  t \<in> (F s)}"
  assumes "\<And>s y. s \<in> S \<Longrightarrow> y \<in> (F s) \<Longrightarrow> g s y \<in> carrier R"
  shows "finsum R (\<lambda>s. finsum R (g s) (F s)) S =
         finsum R (\<lambda> p. g (fst p) (snd p)) P"
proof-
  obtain P' where P'_def: "P' =  (\<lambda>S. {(s, t). s \<in> S \<and>  t \<in> (F s)})"
    by simp
  have "finsum R (\<lambda>s. finsum R (g s) (F s)) S =
         finsum R (\<lambda> p. g (fst p) (snd p)) (P' S)"
    using double_finsum_induct[of S F P' g S]
          assms P'_def
    by blast
  then show ?thesis
    using P'_def assms
    by blast
qed

end

text\<open>
  The product index set for the double sums in the coefficients of the
  $((a \otimes_p b) \otimes_p c)$. It is the set of pairs $(x,y)$ of monomials, such that
  $x$ is a factor of monomial $m$, and $y$ is a factor of monomial $x$.
\<close>

definition right_cuts :: "'c monomial \<Rightarrow> ('c monomial \<times> 'c monomial) set" where
"right_cuts m = {(x, y). x \<subseteq># m \<and> y \<subseteq># x}"

context ring
begin

lemma right_cuts_alt_def:
"right_cuts m = {(x, y). x \<in> mset_factors m \<and> y \<in> mset_factors x}"
  unfolding mset_factors_def right_cuts_def
  by simp

lemma right_cuts_finite:
"finite (right_cuts m)"
proof-
  have "finite (mset_factors m \<times> mset_factors m)"
    using mset_factors_finite
    by blast
  have "right_cuts m \<subseteq> (mset_factors m \<times> mset_factors m)"
  proof
    fix p
    assume p_def: "p \<in> right_cuts m"
    obtain x y where xy: "p = (x , y) \<and> x \<subseteq># m \<and> y \<subseteq>#x"
      using p_def unfolding right_cuts_def
      by blast
    then have "x \<in> mset_factors m \<and> y \<in> mset_factors m"
      using monom_divides_factors
      by auto
    then show "p \<in> (mset_factors m \<times> mset_factors m)"
      by (simp add: xy)
  qed
  then show ?thesis
    using \<open>finite (mset_factors m \<times> mset_factors m)\<close> finite_subset
    by blast
qed

lemma assoc_aux0:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  assumes "carrier_coeff c"
  assumes "g = (\<lambda>x y.  a x \<otimes> (b y \<otimes> c (m - x - y)))"
  shows "\<And>s y. s \<in> mset_factors m \<Longrightarrow> y \<in> mset_factors (m - x)
            \<Longrightarrow> g s y \<in> carrier R"
  using assms carrier_coeffE by blast

lemma assoc_aux1:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  assumes "carrier_coeff c"
  assumes "g = (\<lambda>x y.  (a y  \<otimes> b (x - y)) \<otimes> c (m - x))"
  shows "\<And>s y. s \<in> mset_factors m \<Longrightarrow> y \<in> mset_factors x \<Longrightarrow> g s y \<in> carrier R"
  using assms carrier_coeffE by blast
end

text\<open>
  The product index set for the double sums in the coefficients of the
  $(a \otimes_p (b \otimes_p c))$. It is the set of pairs $(x,y)$ such that $x$ is a factor
  of $m$ and $y$ is a factor of $m/x$.
\<close>

definition left_cuts :: "'c monomial \<Rightarrow> ('c monomial \<times> 'c monomial) set" where
"left_cuts m = {(x, y). x \<subseteq>#m \<and> y \<subseteq># (m - x)}"

context ring
begin

lemma left_cuts_alt_def:
"left_cuts m = {(x, y). x \<in> mset_factors m \<and> y \<in> mset_factors (m - x)}"
  unfolding mset_factors_def left_cuts_def
  by simp

text\<open>This lemma witnesses the bijection between left and right cuts for the proof of associativity:\<close>

lemma left_right_cuts_bij:
"bij_betw (\<lambda> (x,y). (x + y, x))  (left_cuts m) (right_cuts m)"
  unfolding bij_betw_def right_cuts_def left_cuts_def
proof
  show "inj_on (\<lambda>(x, y). (x + y, x)) {(x, y). x \<subseteq># m \<and> y \<subseteq># m - x}"
    unfolding inj_on_def
    by auto
  show "(\<lambda>(x, y). (x + y, x)) ` {(x, y). x \<subseteq># m \<and> y \<subseteq># m - x} = {(x, y). x \<subseteq># m \<and> y \<subseteq># x}"
  proof
    show "(\<lambda>(x, y). (x + y, x)) ` {(x, y). x \<subseteq># m \<and> y \<subseteq># m - x} \<subseteq> {(x, y). x \<subseteq># m \<and> y \<subseteq># x}"
    proof
      fix p
      assume "p  \<in> (\<lambda>(x, y). (x + y, x)) ` {(x, y). x \<subseteq># m \<and> y \<subseteq># m - x}"
      then obtain a b where ab: "a \<subseteq># m \<and> b \<subseteq># m - a \<and> p = (\<lambda>(x, y). (x + y, x)) (a, b)"
        by blast
      then have "p = (a + b, a)"
        by simp
      then show "p \<in> {(x, y). x \<subseteq># m \<and> y \<subseteq># x}"
        using ab
        by (metis (no_types, lifting) case_prodI mem_Collect_eq mset_subset_eq_add_left
            subset_mset.le_diff_conv2 union_commute)
    qed
    show "{(x, y). x \<subseteq># m \<and> y \<subseteq># x} \<subseteq> (\<lambda>(x, y). (x + y, x)) ` {(x, y). x \<subseteq># m \<and> y \<subseteq># m - x}"
    proof
      fix p
      assume p_def: "p \<in> {(x, y). x \<subseteq># m \<and> y \<subseteq># x}"
      then obtain a b where ab: "p = (a, b) \<and> a \<subseteq># m \<and> b \<subseteq># a"
        by blast
      then have "p = (\<lambda>(x, y). (x + y, x)) (b, a - b)"
        using ab
        by simp
      then show " p \<in> (\<lambda>(x, y). (x + y, x)) ` {(x, y). x \<subseteq># m \<and> y \<subseteq># m - x}"
        by (metis (mono_tags, lifting) ab case_prodI image_eqI mem_Collect_eq
            subset_mset.diff_add subset_mset.dual_order.trans subset_mset.le_diff_conv2)
    qed
  qed
qed

lemma left_cuts_sum:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  assumes "carrier_coeff c"
  shows "(a \<Otimes>\<^sub>p (b \<Otimes>\<^sub>p c)) m = (\<Oplus>p \<in> left_cuts m. a (fst p) \<otimes> (b (snd p) \<otimes> c (m - (fst p) - (snd p))))"
proof-
  have U: "(a \<Otimes>\<^sub>p (b \<Otimes>\<^sub>p c)) m = (\<Oplus>x\<in>mset_factors m. (\<Oplus>xa\<in>mset_factors (m - x). a x \<otimes> (b xa \<otimes> c (m - x - xa))))"
    unfolding P_ring_mult_def
  proof-
    obtain f where f_def:
          "f = (\<lambda>x . a x \<otimes> (\<Oplus>xa\<in>mset_factors (m - x). b xa \<otimes> c (m - x - xa)))"
      by simp
    obtain g where g_def:
      "g =  (\<lambda>x . \<Oplus>xa\<in>mset_factors (m - x). a x \<otimes> (b xa \<otimes> c (m - x - xa)))"
      by simp
    have 0: "restrict f (mset_factors m) = restrict g (mset_factors m)"
    proof
      fix x
      show "restrict f (mset_factors m) x = restrict g (mset_factors m) x"
      proof(cases "x \<in> mset_factors m")
        case True
         have T0: "restrict f (mset_factors m) x = a x \<otimes> (\<Oplus>xa\<in>mset_factors (m - x). b xa \<otimes> c (m - x - xa))"
           using f_def True by auto
         have T1: "restrict g (mset_factors m) x = (\<Oplus>xa\<in>mset_factors (m - x). a x \<otimes> (b xa \<otimes> c (m - x - xa)))"
           using True g_def by auto
         show "restrict f (mset_factors m) x = restrict g (mset_factors m) x"
           using assms finsum_rdistr[of "mset_factors (m - x)" "a x" "\<lambda> xa. b xa \<otimes> c (m - x - xa)"]
           by (metis (mono_tags, lifting) mset_factors_finite Pi_I T0 T1 carrier_coeffE m_closed)
      next
        case False
        then have "restrict f (mset_factors m)  x = undefined" using f_def
          by (simp add: restrict_def)
        have  "restrict g (mset_factors m) x = undefined" using g_def False
          using restrict_def by auto
        then show ?thesis using f_def g_def
          using \<open>restrict f (mset_factors m) x = undefined\<close>
          by auto

      qed
    qed
    have 1: "f \<in> mset_factors m \<rightarrow> carrier R"
      using f_def assms
      by (simp add: carrier_coeffE)
    have 2: "g \<in> mset_factors m \<rightarrow> carrier R"
      using g_def assms
      by (simp add: carrier_coeffE)
    show "(\<Oplus>x\<in>mset_factors m. a x \<otimes> (\<Oplus>xa\<in>mset_factors (m - x). b xa \<otimes> c (m - x - xa))) =
    (\<Oplus>x\<in>mset_factors m. \<Oplus>xa\<in>mset_factors (m - x). a x \<otimes> (b xa \<otimes> c (m - x - xa)))"
      using f_def g_def finsum_eq[of "f"
                "mset_factors m" "g"] 0 1 2
      by blast
  qed
  have 0: "(\<And>s. s \<in> mset_factors m \<Longrightarrow> finite (mset_factors (m - s)))"
    by simp
  have 1: "finite (mset_factors m)"
    by simp
  have 2: "(\<And>s y. s \<in> mset_factors m \<Longrightarrow> y \<in> mset_factors (m - s) \<Longrightarrow> a s \<otimes> (b y \<otimes> c (m - s - y)) \<in> carrier R)"
    using assms assoc_aux0[of a b c ]
    by blast
    have "(\<Oplus>x\<in>mset_factors m. (\<Oplus>xa\<in>mset_factors (m - x). a x \<otimes> (b xa \<otimes> c (m - x - xa)))) =
          (\<Oplus>p \<in> left_cuts m. a (fst p) \<otimes> (b (snd p) \<otimes> c (m - (fst p) - (snd p)))) "
    using assms left_cuts_alt_def[of m] 0 1 2
          double_finsum[of "mset_factors m" "\<lambda>x. mset_factors (m - x)" "left_cuts m" "(\<lambda>x y.  a x \<otimes> (b y \<otimes> c (m - x - y)))"]
    by blast
  then show ?thesis using U
    by auto
qed

lemma right_cuts_sum:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  assumes "carrier_coeff c"
  shows "(a \<Otimes>\<^sub>p b \<Otimes>\<^sub>p c) m = (\<Oplus>p \<in> right_cuts m. a (snd  p) \<otimes> (b ((fst p) -(snd p)) \<otimes> c (m - (fst p))))"
proof-
  have 0: "finite (mset_factors m)"
    by simp
  have 1: "(\<And>s. s \<in> mset_factors m \<Longrightarrow> finite (mset_factors s))"
    by auto
  have 2: "right_cuts m = {(s, t). s \<in> mset_factors m \<and> t \<in> mset_factors s}"
    unfolding right_cuts_def
    by (simp add: monom_divides_factors)
  have 3: "(\<And>s y. s \<in> mset_factors m \<Longrightarrow> y \<in> mset_factors s \<Longrightarrow> a y \<otimes> b (s - y) \<otimes> c (m - s) \<in> carrier R)"
    using assoc_aux1 assms(1) assms(2) assms(3)
    by blast
  have 4: "(\<Oplus>s\<in>mset_factors m. (\<Oplus>y\<in>mset_factors s. a y \<otimes> b (s - y) \<otimes> c (m - s))) =
    (\<Oplus>p\<in>right_cuts m. a (snd p) \<otimes> b (fst p - snd p) \<otimes> c (m - fst p))"
    using 0 1 2 3
      double_finsum[of "mset_factors m" _ "right_cuts m"
        "(\<lambda>x y.  (a y  \<otimes> b (x - y)) \<otimes> c (m - x))"]
    by auto
  have 5: "(\<Oplus>x\<in>mset_factors m. (\<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa)) \<otimes> c (m - x)) =
           (\<Oplus>x\<in>mset_factors m. \<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa) \<otimes> c (m - x))"
  proof-
    obtain f where f_def: "f =( \<lambda>x. (\<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa)) \<otimes> c (m - x))"
      by simp
    obtain g where g_def: "g = (\<lambda>x.  \<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa) \<otimes> c (m - x))"
      by simp
    have 50: "\<And>s. s \<in> (mset_factors m) \<Longrightarrow> f s = g s"
    proof-
      fix x
      assume As:  "x \<in> mset_factors m"
      show "f x = g x"
      proof-
        have f_eq: "f x = (\<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa)) \<otimes> c (m - x)"
          using f_def
          by auto
        have g_eq: "g x =  (\<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa) \<otimes> c (m - x))"
          using g_def
          by auto
        have f_eq': "f x =  (\<Oplus>xa\<in>mset_factors x. (a xa \<otimes> b (x - xa)) \<otimes> c (m - x))"
          using f_eq finsum_ldistr[of "mset_factors x" "c (m - x)" "\<lambda>xa. (a xa \<otimes> b (x - xa))" ] assms
          by (simp add: \<open>\<lbrakk>finite (mset_factors x); c (m - x) \<in> carrier R; (\<lambda>xa. a xa \<otimes> b (x - xa)) \<in> mset_factors x \<rightarrow> carrier R\<rbrakk> \<Longrightarrow> (\<Oplus>i\<in>mset_factors x. a i \<otimes> b (x - i)) \<otimes> c (m - x) = (\<Oplus>i\<in>mset_factors x. a i \<otimes> b (x - i) \<otimes> c (m - x))\<close> Pi_I carrier_coeffE)
        then show "f x = g x"
          by (simp add: g_eq)
      qed
    qed
    have 51: "f \<in> mset_factors m \<rightarrow> carrier R"
    proof
      fix x
      assume "x \<in> mset_factors m"
      have "(\<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa)) \<otimes> c (m - x )\<in> carrier R"
        using assms carrier_coeffE finsum_closed[of "\<lambda>xa.  a xa \<otimes> b (x - xa)" "mset_factors x"]
        by blast
      then show "f x \<in> carrier R" using assms f_def by auto
    qed
    have 52: "g \<in> mset_factors m \<rightarrow> carrier R"
    proof
      fix x
      assume "x \<in> mset_factors m"
      show "g x \<in> carrier R"
        using assms finsum_closed[of "\<lambda>xa. a xa \<otimes> b (x - xa) \<otimes> c (m - x)" "mset_factors x"] g_def
        by (metis (no_types, lifting) "50" "51" Pi_iff \<open>x \<in> mset_factors m\<close>)
    qed

    show ?thesis
      using 50 51 52 finsum_eq[of f "(mset_factors m) " g]
      by (metis (mono_tags, lifting) f_def finsum_cong' g_def)
  qed
  then have  6: "(\<Oplus>x\<in>mset_factors m. (\<Oplus>xa\<in>mset_factors x. a xa \<otimes> b (x - xa)) \<otimes> c (m - x)) =
    (\<Oplus>p\<in>right_cuts m. a (snd p) \<otimes> b (fst p - snd p) \<otimes> c (m - fst p))"
    by (simp add: "4")
  have 7: "(\<Oplus>p\<in>right_cuts m. a (snd p) \<otimes> b (fst p - snd p) \<otimes> c (m - fst p))
      = (\<Oplus>p\<in>right_cuts m. a (snd p) \<otimes> (b (fst p - snd p) \<otimes> c (m - fst p)))"
    using assms
    by (meson local.ring_axioms m_assoc ring.carrier_coeff_def)
  then show ?thesis
    using assms 5 6
    unfolding P_ring_mult_def
    by simp
qed

text\<open>The Associativity of Polynomial Multiplication:\<close>

lemma P_ring_mult_assoc:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  assumes "carrier_coeff c"
  shows "a \<Otimes>\<^sub>p (b \<Otimes>\<^sub>p c) = (a \<Otimes>\<^sub>p b) \<Otimes>\<^sub>p c"
proof
  fix m
  show "(a \<Otimes>\<^sub>p (b \<Otimes>\<^sub>p c)) m = (a \<Otimes>\<^sub>p b \<Otimes>\<^sub>p c) m"
  proof-
    obtain f where f_def: "f = (\<lambda>p.  a (snd  p) \<otimes> (b ((fst p) -(snd p)) \<otimes> c (m - (fst p))))"
      by simp
    obtain g where g_def: "g = (\<lambda>p. a (fst p) \<otimes> (b (snd p) \<otimes> c (m - (fst p) - (snd p))))"
      by simp
    have f_dom: "f \<in> right_cuts m \<rightarrow> carrier R"
      using assms f_def unfolding right_cuts_def
      by (simp add: carrier_coeffE)
    have g_dom: "g \<in> left_cuts m \<rightarrow> carrier R"
      using assms g_def unfolding left_cuts_def
      by (simp add: carrier_coeffE)
    have 0: "finite (right_cuts m)"
      by (simp add: right_cuts_finite)
    have 1: "bij_betw (\<lambda> (x,y). (x + y, x))  (left_cuts m) (right_cuts m)"
      by (simp add: left_right_cuts_bij)
    have 2: "(\<And>s. s \<in> left_cuts m \<Longrightarrow> g s = f (case s of (x, y) \<Rightarrow> (x + y, x)))"
    proof-
      fix s
      assume "s \<in> left_cuts m"
      then obtain x y where xy: "s = (x, y) \<and> x \<subseteq># m \<and> y \<subseteq># m - x"
        using  left_cuts_def
        by blast
      then have g_eq: "g s = a x \<otimes> (b y \<otimes> c (m - x - y))"
        using g_def fst_conv
        by auto
      have f_eq: "f (case s of (x, y) \<Rightarrow> (x + y, x)) = f (x + y, x)"
        by (simp add: xy)
      then have f_eq': "f (case s of (x, y) \<Rightarrow> (x + y, x)) = a x \<otimes> (b ((x + y) - x) \<otimes> c (m - (x + y)))"
        using f_def
        by simp
      then show "g s = f (case s of (x, y) \<Rightarrow> (x + y, x))"
        by (simp add: g_eq)
    qed
    have 3: "finsum R g (left_cuts m) = finsum R f (right_cuts m)"
    using 0 1 2 finsum_bij_eq[of g "left_cuts m" f "right_cuts m" "\<lambda> (x,y). (x + y, x)" ]
      using bij_betw_finite f_dom g_dom by blast
    then show ?thesis using assms right_cuts_sum left_cuts_sum
      by (metis (mono_tags, lifting) f_def f_dom finsum_cong' g_def g_dom)
  qed
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Commutativity of Polynomial Multiplication\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context ring
begin

lemma mset_factors_bij:
"bij_betw (\<lambda>x. m - x) (mset_factors m) (mset_factors m)"
  apply(rule bij_betwI')
  apply (metis monom_comp' monom_divides_factors)
   apply (simp add: monom_divides_factors)
    by (meson monom_comp' monom_divides_factors diff_subset_eq_self)

lemma(in cring) P_ring_mult_comm:
  assumes "carrier_coeff a"
  assumes "carrier_coeff b"
  shows "a \<Otimes>\<^sub>p b  = b \<Otimes>\<^sub>p a"
proof
  fix m
  show "(a \<Otimes>\<^sub>p b) m = (b \<Otimes>\<^sub>p a) m"
  unfolding P_ring_mult_def
  apply (rule finsum_bij_eq[of "\<lambda> x. a x \<otimes> b (m - x)" "mset_factors m"
                          "\<lambda>x. b x \<otimes> a (m - x)" "mset_factors m" "\<lambda>x. m - x"])
  proof
    show "\<And>x. x \<in> mset_factors m \<Longrightarrow> a x \<otimes> b (m - x) \<in> carrier R"
    proof-
      fix x
      assume "x \<in> mset_factors m"
      show "a x \<otimes> b (m - x) \<in> carrier R"
        using assms carrier_coeffE
        by blast
    qed
    show "(\<lambda>x. b x \<otimes> a (m - x)) \<in> mset_factors m \<rightarrow> carrier R"
    proof
      fix x
      assume "x \<in> mset_factors m"
      show "b x \<otimes> a (m - x) \<in> carrier R"
        using assms  carrier_coeffE
        by blast
    qed
    show "finite (mset_factors m)"
      by simp
    show "bij_betw ((-) m) (mset_factors m) (mset_factors m)"
      by (simp add: mset_factors_bij)
    show "\<And>s. s \<in> mset_factors m \<Longrightarrow> a s \<otimes> b (m - s) = b (m - s) \<otimes> a (m - (m - s))"
    proof-
      fix s
      assume "s \<in> mset_factors m"
      then show "a s \<otimes> b (m - s) = b (m - s) \<otimes> a (m - (m - s))"
        using assms carrier_coeffE
        by (metis local.ring_axioms m_comm ring.monom_comp' ring.monom_divides_factors)
    qed
  qed
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Closure properties for multiplication\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Building monomials from polynomials:\<close>

lemma indexed_const_P_mult_eq:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "(indexed_const a) \<Otimes>\<^sub>p  (indexed_const b) = indexed_const (a \<otimes> b)"
proof-
  have 0: "monomials_of R (indexed_const a) = (if (a = \<zero>) then {} else {{#}})"
    unfolding monomials_of_def indexed_const_def
    by auto
  have 1: "monomials_of R (indexed_const b) = (if (b = \<zero>) then {} else {{#}})"
    unfolding monomials_of_def indexed_const_def
    by auto
  show ?thesis
    unfolding P_ring_mult_def
  proof
    fix m:: "'c monomial"
    show "(\<Oplus>x\<in>mset_factors m. indexed_const a x \<otimes> indexed_const b (m - x)) = indexed_const (a \<otimes> b) m "
    proof(cases "m = {#}")
      case True
      then have T0: "mset_factors m = {{#}}"
        unfolding mset_factors_def
        by simp
      have "(\<Oplus>x\<in>mset_factors m. indexed_const a x \<otimes> indexed_const b (m - x)) =
                   indexed_const a {#} \<otimes> indexed_const b ({#} - {#}) "
      proof-
        have 0: "(\<lambda>x. indexed_const a x \<otimes> indexed_const b (m - x)) \<in> {} \<rightarrow> carrier R"
          by blast
        have 1: "indexed_const a {#} \<otimes> indexed_const b (m - {#}) \<in> carrier R"
          by (simp add: assms(1) assms(2) indexed_const_def)
        have 2: "(\<Oplus>x\<in>{{#}}. indexed_const a x \<otimes> indexed_const b (m - x)) =
                 indexed_const a {#} \<otimes> indexed_const b (m - {#}) \<oplus> (\<Oplus>x\<in>{}. indexed_const a x \<otimes> indexed_const b (m - x))"
        using True T0 0 1  finsum_insert[of "{}" "{#}" "\<lambda>x. indexed_const a x \<otimes> indexed_const b (m - x)"  ]
            by (simp add: indexed_const_def)
        then show ?thesis
          using True T0 0 1  finsum_insert[of "{}" "{#}" "\<lambda>x. indexed_const a x \<otimes> indexed_const b (m - x)"  ]
              finsum_empty[of "\<lambda>x. indexed_const a x \<otimes> indexed_const b (m - x)"]
          by (simp add: \<open>\<lbrakk>finite {}; {#} \<notin> {}; (\<lambda>x. indexed_const a x \<otimes> indexed_const b (m - x)) \<in> {} \<rightarrow> carrier R; indexed_const a {#} \<otimes> indexed_const b (m - {#}) \<in> carrier R\<rbrakk> \<Longrightarrow> (\<Oplus>x\<in>{{#}}. indexed_const a x \<otimes> indexed_const b (m - x)) = indexed_const a {#} \<otimes> indexed_const b (m - {#}) \<oplus> (\<Oplus>x\<in>{}. indexed_const a x \<otimes> indexed_const b (m - x))\<close> indexed_const_def)
      qed
      then show ?thesis
        by (simp add: True indexed_const_def)
    next
      case False
      then show ?thesis using 0 1
        by (simp add: add.finprod_one_eqI assms(1) assms(2)
            indexed_const_def )
    qed
  qed
qed

lemma indexed_const_P_multE:
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "c \<in> carrier R"
  shows "(P \<Otimes>\<^sub>p (indexed_const c)) m =  (P m) \<otimes> c"
  unfolding P_ring_mult_def
proof-
  have 3: "m \<notin> mset_factors m - {m}"
    by simp
  have 4: "finite ((mset_factors m) - {m})"
    by simp
  have 5: "P m \<otimes> indexed_const c (m - m) \<in> carrier R "
  by (metis assms(1) assms(2) cancel_comm_monoid_add_class.diff_cancel
      carrier_coeffE indexed_const_def indexed_pset_in_carrier local.ring_axioms
      ring.ring_simprules(5) subsetI)
  have 0: "(\<lambda>x. P x \<otimes> indexed_const c (m - x)) \<in> mset_factors m - {m} \<rightarrow> carrier R"
  proof
    fix x
    assume "x \<in> mset_factors m - {m}"
    then show "P x \<otimes> indexed_const c (m - x) \<in> carrier R "
      using assms
      by (meson carrier_coeffE indexed_const_in_carrier indexed_pset_in_carrier m_closed subsetI)
  qed
  have 1: "P m \<otimes> indexed_const c ( m - m) =  (P m \<otimes> c)"
    by (simp add: indexed_const_def)
  have 2: "\<And>x. x \<in> mset_factors m \<Longrightarrow>  P x \<otimes> indexed_const c (m - x)  = (if x = m then (P m \<otimes> c) else \<zero>)"
  proof-
    fix x
    assume "x \<in> mset_factors m "
    then have "indexed_const c (m - x) = (if x = m then c else \<zero>)"
      unfolding indexed_const_def
      by (metis cancel_comm_monoid_add_class.diff_cancel
          diff_zero monom_comp' monom_divides_factors)
    then show  "P x \<otimes> indexed_const c (m - x)  = (if x = m then (P m \<otimes> c) else \<zero>)"
      by (metis assms(1) carrier_coeffE indexed_pset_in_carrier
            local.semiring_axioms semiring.r_null set_eq_subset)
  qed
  then have "(\<Oplus>x\<in>(mset_factors m) - {m}. P x \<otimes> indexed_const c (m - x)) = \<zero>"
    using assms
    by (metis (no_types, lifting) DiffD1 DiffD2 add.finprod_one_eqI singletonI)
  then show "(\<Oplus>x\<in>(mset_factors m). P x \<otimes> indexed_const c (m - x)) = P m \<otimes> c"
    using assms 0 1 3 4 5 finsum_insert[of "(mset_factors m) - {m}"
                                    m "\<lambda>x. P x \<otimes> indexed_const c (m - x) "]
    by (metis (no_types, lifting) m_factor add.l_cancel_one
              insert_Diff_single insert_absorb zero_closed)
qed

lemma indexed_const_var_mult:
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "c \<in> carrier R"
  assumes "i \<in> I"
  shows "P \<Otimes> i \<Otimes>\<^sub>p indexed_const c = (P \<Otimes>\<^sub>p (indexed_const c)) \<Otimes> i "
proof
  fix m
  show "(P \<Otimes> i \<Otimes>\<^sub>p indexed_const c) m = (P \<Otimes>\<^sub>p indexed_const c \<Otimes> i) m"
  proof(cases "i \<in># m")
    case True
    then have T0: "(P \<Otimes> i \<Otimes>\<^sub>p indexed_const c) m  = (P \<Otimes> i) m \<otimes> c"
      using assms indexed_const_P_multE[of "P \<Otimes> i" I c m]
      by (simp add: indexed_pset.indexed_pmult)
    then show ?thesis using assms indexed_const_P_multE[of P I c m]
      unfolding  indexed_pmult_def
      using True indexed_const_P_multE by fastforce
  next
    case False
        then have T0: "(P \<Otimes> i \<Otimes>\<^sub>p indexed_const c) m  = (P \<Otimes> i) m \<otimes> c"
      using assms indexed_const_P_multE[of "P \<Otimes> i" I c m]
      by (simp add: indexed_pset.indexed_pmult)
    then show ?thesis using assms indexed_const_P_multE[of P I c m]
      unfolding  indexed_pmult_def
      using False by auto
  qed
qed

lemma indexed_const_P_mult_closed:
  assumes "a \<in> indexed_pset I (carrier R)"
  assumes "c \<in> carrier R"
  shows "a \<Otimes>\<^sub>p (indexed_const c) \<in> indexed_pset I (carrier R)"
  apply(rule indexed_pset.induct[of a I "(carrier R)" ])
     apply (simp add: assms(1); fail)
proof-
  show "\<And>k. (k \<in> carrier R) \<Longrightarrow> ((indexed_const k) \<Otimes>\<^sub>p (indexed_const c)) \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>])"
    using assms
    by (metis indexed_const_P_mult_eq indexed_pset.simps m_closed)
  show "\<And>P Q. P \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow>
           P \<Otimes>\<^sub>p indexed_const c \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow>
           Q \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow> Q \<Otimes>\<^sub>p indexed_const c \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow> P \<Oplus> Q \<Otimes>\<^sub>p indexed_const c \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>])"
    using P_ring_ldistr
    by (metis assms(2) carrier_coeff_def indexed_const_in_carrier indexed_pset.indexed_padd indexed_pset_in_carrier subsetI)
  show "\<And>P i. P \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow> P \<Otimes>\<^sub>p indexed_const c \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow> i \<in> I \<Longrightarrow> P \<Otimes> i \<Otimes>\<^sub>p indexed_const c \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>])"
  proof-
    fix P i
    assume A0: "P \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>])"
    assume A1: " (P \<Otimes>\<^sub>p indexed_const c) \<in> ((carrier R) [\<X>\<^bsub>I\<^esub>])"
    assume A2: "i \<in> I"
    show "P \<Otimes> i \<Otimes>\<^sub>p indexed_const c \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
      using assms  A0 A1 A2 indexed_const_var_mult local.ring_axioms ring.indexed_pset.simps
      by (metis (no_types, opaque_lifting))
  qed
qed

lemma monom_add_mset:
"mset_to_IP R (add_mset i m) = mset_to_IP R m \<Otimes> i"
  unfolding indexed_pmult_def
  by (metis (no_types, opaque_lifting) add_mset_diff_bothsides diff_empty mset_to_IP_def multi_member_split union_single_eq_member)

text\<open>Monomials are closed under multiplication:\<close>

lemma monom_mult:
"mset_to_IP R m \<Otimes>\<^sub>p mset_to_IP R n = mset_to_IP R (m + n)"
proof-
  have "(\<lambda>ma. \<Oplus>x\<in>mset_factors ma. (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>))
       = (\<lambda>ma. (if ma = n + m then \<one> else \<zero>))"
  proof
    fix ma
    show "(\<Oplus>x\<in>mset_factors ma. (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>)) = (if ma = n + m then \<one> else \<zero>)"

    proof-
      have 0: "\<And>x. x \<in> mset_factors ma \<Longrightarrow>
            (\<lambda> x. (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>)) x =
                  (if (x = m) then (if ma - x = n then \<one> else \<zero>) else \<zero>) "
        by simp
      then have 1: "(\<Oplus>x\<in>((mset_factors ma) - {m}). (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>)) =
            \<zero>"
        by (metis (no_types, lifting) add.finprod_one_eqI mem_Collect_eq set_diff_eq singletonI)
      have 2: "finite (mset_factors ma - {m}) "
        by simp
      have 3: "m \<notin> mset_factors ma - {m}"
        by simp
      have 4: "(\<lambda>x. (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>)) \<in> mset_factors ma - {m} \<rightarrow> carrier R"
      proof
        fix x
        assume " x \<in> mset_factors ma - {m}"
        show "(if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>) \<in> carrier R "
          by auto
      qed
      show ?thesis
      proof(cases "m \<in> (mset_factors ma)")
        case True
        have T0: " (\<Oplus>x\<in>insert m (mset_factors ma - {m}). (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>)) =
      (if m = m then \<one> else \<zero>) \<otimes> (if ma - m = n then \<one> else \<zero>) \<oplus>
      (\<Oplus>x\<in>mset_factors ma - {m}. (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>))"
          using True 1 2 3 4 finsum_insert[of "((mset_factors ma) - {m})" m
                                   "\<lambda>x. (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>)"]
          using m_closed one_closed zero_closed by presburger
        have T1: "(mset_factors ma) = insert m (mset_factors ma - {m})"
          using True
          by blast
        then have  "(\<Oplus>x\<in>(mset_factors ma). (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>))
                      = (if m = m then \<one> else \<zero>) \<otimes> (if ma - m = n then \<one> else \<zero>)"
          using T0 T1 1 add.l_cancel_one insert_Diff_single insert_absorb2 l_one mk_disjoint_insert one_closed zero_closed
          by presburger
        then have "(\<Oplus>x\<in>(mset_factors ma). (if x = m then \<one> else \<zero>) \<otimes> (if ma - x = n then \<one> else \<zero>))
                      = (if ma - m = n then \<one> else \<zero>)"
          by simp
        then show ?thesis
          by (metis (no_types, lifting) monom_divides_factors True add.commute add_diff_cancel_right' subset_mset.add_diff_inverse)
      next
        case False
        then show ?thesis
          by (metis (no_types, lifting) "0" monom_divides_factors add.finprod_one_eqI mset_subset_eq_add_right)
      qed
    qed
  qed
  then show ?thesis
  unfolding mset_to_IP_def P_ring_mult_def
  by (simp add: union_commute)
qed

lemma poly_index_mult:
  assumes "a \<in> indexed_pset I (carrier R)"
  assumes "i \<in> I"
  shows "a \<Otimes> i = a \<Otimes>\<^sub>p mset_to_IP R {#i#}"
proof
  fix m
  show "(a \<Otimes> i) m = (a \<Otimes>\<^sub>p mset_to_IP R {#i#}) m"
  proof(cases "i \<in># m")
    case True
    have T0: "(a \<Otimes> i) m = a (m - {#i#})"
      by (simp add: True indexed_pmult_def)
    have T1: "(a \<Otimes>\<^sub>p mset_to_IP R {#i#}) m = a (m - {#i#})"
    proof-
      have T10: "(a \<Otimes>\<^sub>p mset_to_IP R {#i#}) m
                = (\<Oplus>x\<in>mset_factors m. a x \<otimes> mset_to_IP R {#i#} (m - x)) "
        unfolding P_ring_mult_def
        by auto
      have T11: "\<And>x. x \<in> mset_factors m \<Longrightarrow>
                  mset_to_IP R {#i#} (m - x) = (if x = (m - {#i#}) then \<one> else \<zero>)"
        unfolding mset_to_IP_def
        by (metis Multiset.diff_cancel Multiset.diff_right_commute True diff_single_eq_union
            diff_single_trivial diff_zero monom_comp' monom_divides_factors multi_drop_mem_not_eq)
      have T12: "\<And>x. x \<in> mset_factors m \<Longrightarrow>
              a x \<otimes> mset_to_IP R {#i#} (m - x) = (if  x = (m - {#i#}) then a (m - {#i#}) else \<zero>)"
      proof-
        fix x
        assume "x \<in> mset_factors m"
        then show " a x \<otimes> mset_to_IP R {#i#} (m - x) = (if x = m - {#i#} then a (m - {#i#}) else \<zero>)"
          apply(cases "x = m - {#i#}")
           apply (metis T0 T11 \<open>x \<in> mset_factors m\<close> assms(1) carrier_coeffE empty_subsetI
              ideal_is_subalgebra indexed_pset_in_carrier oneideal r_one subalgebra_in_carrier)
          by (metis T11 \<open>x \<in> mset_factors m\<close> assms(1) carrier_coeffE carrier_is_subalgebra
              empty_subsetI  indexed_pset_in_carrier  r_null  subalgebra_in_carrier)
      qed
      have  T13: "(\<Oplus>x\<in>(mset_factors m) - {m - {#i#}}. a x \<otimes> mset_to_IP R {#i#} (m - x)) = \<zero>"
        using T12
        by (metis (no_types, lifting) DiffE add.finprod_one_eqI singletonI)
      have T14: "finite (mset_factors m - {m - {#i#}})"
        using mset_factors_finite by blast
      have T15: "m - {#i#} \<notin> mset_factors m - {m - {#i#}}"
        by simp
      have T16: "  (\<lambda>x. a x \<otimes> mset_to_IP R {#i#} (m - x)) \<in> mset_factors m - {m - {#i#}} \<rightarrow> carrier R"
      proof
        fix x
        assume "x \<in> mset_factors m - {m - {#i#}}"
        then show " a x \<otimes> mset_to_IP R {#i#} (m - x) \<in> carrier R"
          using assms T12 by auto
      qed
      have "m - (m - {#i#}) = {#i#}"
        by (metis monom_comp' True single_subset_iff)
      then have T17: " a (m - {#i#}) \<otimes> mset_to_IP R {#i#} (m - (m - {#i#})) \<in> carrier R"
        unfolding mset_to_IP_def apply auto using assms
        by (meson carrier_coeffE carrier_is_subalgebra empty_subsetI indexed_pset_in_carrier m_closed one_closed subalgebra_in_carrier)
      have T18:"(\<Oplus>x\<in>insert (m - {#i#}) (mset_factors m - {m - {#i#}}). a x \<otimes> mset_to_IP R {#i#} (m - x)) =
      a (m - {#i#}) \<otimes> mset_to_IP R {#i#} (m - (m - {#i#})) \<oplus> (\<Oplus>x\<in>mset_factors m - {m - {#i#}}. a x \<otimes> mset_to_IP R {#i#} (m - x))"
        using T12 T13 T14 T15 T16 T17 unfolding P_ring_mult_def
        using finsum_insert[of "mset_factors m - {m - {#i#}}" "m - {#i#}"
            "\<lambda>x. a x \<otimes> mset_to_IP R {#i#} (m - x)"]
        by blast
      have T19: "a (m - {#i#}) \<otimes> mset_to_IP R {#i#} (m - (m - {#i#})) = a (m - {#i#}) "
      proof-
        have " (m - (m - {#i#})) = {#i#}"
          using True
          by (metis monom_comp' single_subset_iff)
        then have "mset_to_IP R {#i#} (m - (m - {#i#})) = \<one>"
          by (metis mset_to_IP_def)
        have "a (m - {#i#}) \<in> carrier R"
          using assms
          by (meson carrier_coeffE carrier_is_subalgebra exp_base_closed
              indexed_pset_in_carrier one_closed subalgebra_in_carrier)
        then show ?thesis using assms
          using \<open>mset_to_IP R {#i#} (m - (m - {#i#})) = \<one>\<close> by auto
      qed
      have T20: "(\<Oplus>x\<in>insert (m - {#i#}) ((mset_factors m) - {m - {#i#}}). a x \<otimes> mset_to_IP R {#i#} (m - x)) =
       a (m - {#i#}) \<oplus> (\<Oplus>x\<in>mset_factors m - {m - {#i#}}. a x \<otimes> mset_to_IP R {#i#} (m - x))"
        using T18 T19 by auto
      have T21: "insert (m - {#i#}) ((mset_factors m) - {m - {#i#}}) = mset_factors m"
      proof-
        have "(m - {#i#}) \<in> mset_factors m"
          by (simp add: monom_divides_factors)
        then show ?thesis
          by blast
      qed
      then show ?thesis using T13 T20 True unfolding P_ring_mult_def
        using T17 T19 by auto
    qed
    then show ?thesis
      by (simp add: T0)
  next
    case False
    have F0: "(a \<Otimes> i) m = \<zero> "
      by (simp add: False indexed_pmult_def)
    have F1: "  (a \<Otimes>\<^sub>p mset_to_IP R {#i#}) m = \<zero>"
      unfolding P_ring_mult_def
    proof-
      have "\<And>x. x \<in> mset_factors m \<Longrightarrow>  a x \<otimes> mset_to_IP R {#i#} (m - x) = \<zero>"
      proof-
        fix x
        assume A: "x \<in> mset_factors m"
        have B: "m - x \<noteq> {#i#}" using False A
          by (metis diff_subset_eq_self single_subset_iff)
        then show "a x \<otimes> mset_to_IP R {#i#} (m - x) = \<zero>"
          using assms False unfolding mset_to_IP_def
          using  carrier_coeffE indexed_pset_in_carrier by fastforce
      qed
      then show "(\<Oplus>x\<in>mset_factors m. a x \<otimes> mset_to_IP R {#i#} (m - x)) = \<zero>"
        by (simp add: add.finprod_one_eqI)
    qed
    then show ?thesis
      by (simp add: F0)
  qed
qed

lemma mset_to_IP_mult_closed:
  assumes "a \<in> indexed_pset I (carrier R)"
  shows "set_mset m \<subseteq> I \<Longrightarrow> a \<Otimes>\<^sub>p mset_to_IP R m \<in> indexed_pset I (carrier R)"
proof(induction m)
  case empty
  then have "mset_to_IP R {#} = indexed_const \<one>"
    unfolding mset_to_IP_def indexed_const_def by auto
  then show ?case
    by (simp add: \<open>mset_to_IP R {#} = indexed_const \<one>\<close> assms indexed_const_P_mult_closed)
next
  case (add x m)
  fix x
  fix m :: "'c monomial"
  assume A: "set_mset (add_mset x m) \<subseteq> I"
  assume B: "set_mset m \<subseteq> I \<Longrightarrow> a \<Otimes>\<^sub>p mset_to_IP R m \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
  show " a \<Otimes>\<^sub>p mset_to_IP R (add_mset x m) \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
  proof-
    have 0: "x \<in> I"
      using A by auto
    have 1: "set_mset m \<subseteq> I"
      using A by auto
    have 2: " a \<Otimes>\<^sub>p mset_to_IP R m \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
      using "1" B by blast
    have 3: " a \<Otimes>\<^sub>p mset_to_IP R (add_mset x m) = (a \<Otimes>\<^sub>p mset_to_IP R m) \<Otimes> x"
    proof-
      have 30: " a \<Otimes>\<^sub>p mset_to_IP R (add_mset x m) = a \<Otimes>\<^sub>p (mset_to_IP R m \<Otimes> x)"
        using monom_add_mset[of x m]
        by auto
      have 31: "(a \<Otimes>\<^sub>p mset_to_IP R m) \<Otimes> x = a \<Otimes>\<^sub>p (mset_to_IP R m \<Otimes> x)"
      proof
        fix y
        show "(a \<Otimes>\<^sub>p mset_to_IP R m \<Otimes> x) y = (a \<Otimes>\<^sub>p (mset_to_IP R m \<Otimes> x)) y "
        proof-
          have 310: "(a \<Otimes>\<^sub>p mset_to_IP R m \<Otimes> x) y = (a \<Otimes>\<^sub>p mset_to_IP R m \<Otimes>\<^sub>p mset_to_IP R {#x#}) y"
            using poly_index_mult "0" "2"
            by fastforce
          have 311: " (mset_to_IP R m \<Otimes> x) = mset_to_IP R m \<Otimes>\<^sub>p mset_to_IP R {#x#}"
            using  "0" "2"
            by (metis add_mset_add_single monom_add_mset monom_mult)
          have 312: "carrier_coeff a "
            using assms indexed_pset_in_carrier by blast
          have 313: "carrier_coeff (mset_to_IP R m)"
            by (simp add: carrier_coeff_def mset_to_IP_def)
          have 314: "carrier_coeff (mset_to_IP R {#x#})"
            by (metis carrier_coeff_def mset_to_IP_def one_closed zero_closed)
          show ?thesis
            using 310 311 312 313 314
                  P_ring_mult_assoc[of a "mset_to_IP R m" "mset_to_IP R {#x#}"]
            by simp
        qed
      qed
      then show ?thesis
        by (simp add: monom_add_mset)
    qed
    then show ?thesis
      by (simp add: "0" "1" B indexed_pset.indexed_pmult)
  qed
qed

text\<open>
  A predicate which identifies when the variables used in a given polynomial $P$ are only
   drawn from a fixed variable set $I$.
\<close>
abbreviation monoms_in where
"monoms_in I P \<equiv> (\<forall>m \<in> monomials_of R P. set_mset m \<subseteq> I)"

lemma monoms_of_const:
"monomials_of R (indexed_const k) = (if k = \<zero> then {} else {{#}})"
  unfolding indexed_const_def monomials_of_def
  by auto

lemma const_monoms_in:
"monoms_in I (indexed_const k)"
  unfolding indexed_const_def monomials_of_def
  using  count_empty count_eq_zero_iff monomials_ofE subsetI
  by simp

lemma mset_to_IP_indices:
  shows  "P \<in> indexed_pset I (carrier R) \<Longrightarrow> monoms_in I P"
  apply(erule indexed_pset.induct[of])
   apply (simp add: const_monoms_in; fail)
proof-
  show "\<And>P Q. P \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow>
           \<forall>m\<in>monomials_of R P. set_mset m \<subseteq> I \<Longrightarrow>
           Q \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow> \<forall>m\<in>monomials_of R Q. set_mset m \<subseteq> I \<Longrightarrow> \<forall>m\<in>monomials_of R (P \<Oplus> Q). set_mset m \<subseteq> I"
  proof
    fix P Q
    fix m
    assume A: "P \<in> (carrier R [\<X>\<^bsub>I\<^esub>])" "\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> I"
                "Q \<in> (carrier R [\<X>\<^bsub>I\<^esub>])" "\<forall>m\<in>monomials_of R Q. set_mset m \<subseteq> I"
                  " m \<in> monomials_of R (P \<Oplus> Q)"
    show "set_mset m \<subseteq> I"
    proof-
      have "m \<in> monomials_of R P \<or> m \<in> monomials_of R Q"
        using A using monomials_of_add[of P Q]
        by blast
      then show ?thesis using A
        by blast
    qed
  qed
  show "\<And>P i. P \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow> \<forall>m\<in>monomials_of R P. set_mset m \<subseteq> I \<Longrightarrow> i \<in> I \<Longrightarrow> \<forall>m\<in>monomials_of R (P \<Otimes> i). set_mset m \<subseteq> I"
  proof
    fix P
    fix i
    fix m
    assume A: "P \<in> (carrier R [\<X>\<^bsub>I\<^esub>])" "\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> I" "i \<in> I" "m \<in> monomials_of R (P \<Otimes> i)"
    obtain n where "n \<in> monomials_of R P \<and> m = add_mset i n"
      using A
      by (metis image_iff monomials_of_p_mult')
    then show "set_mset m \<subseteq> I"
      using A
      by auto
  qed
qed

lemma mset_to_IP_indices':
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "m \<in> monomials_of R P"
  shows "set_mset m \<subseteq> I"
  using assms(1) assms(2) mset_to_IP_indices by blast

lemma one_mset_to_IP:
 "mset_to_IP R {#} = indexed_const \<one>"
  unfolding mset_to_IP_def indexed_const_def
  by blast

lemma mset_to_IP_closed:
  shows "set_mset m \<subseteq> I \<Longrightarrow>mset_to_IP R m \<in> indexed_pset I (carrier R) "
  apply(induction m)
  apply (simp add: indexed_pset.indexed_const one_mset_to_IP)
  by (metis (no_types, lifting) add_mset_commute indexed_pset.simps
      monom_add_mset mset_add subset_iff union_single_eq_member)

lemma mset_to_IP_closed':
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "m \<in> monomials_of R P"
  shows "mset_to_IP R m \<in> indexed_pset I (carrier R)"
  by (meson assms(1) assms(2) mset_to_IP_closed mset_to_IP_indices')

text\<open>This lemma expresses closure under multiplcation for indexed polynomials.\<close>

lemma  P_ring_mult_closed:
  assumes "carrier_coeff P"
  assumes "carrier_coeff Q"
  shows  "carrier_coeff (P_ring_mult R P Q)"
  unfolding carrier_coeff_def
proof
  fix m
  have "(\<lambda>x. P x \<otimes> Q (m - x)) \<in> mset_factors m \<rightarrow> carrier R"
  proof
    fix x
    assume "x \<in> mset_factors m"
    then show "P x \<otimes> Q (m - x) \<in> carrier R"
      using assms  carrier_coeffE
      by blast
  qed
  then show "(P \<Otimes>\<^sub>p Q) m \<in> carrier R"
    using assms finsum_closed[of "(\<lambda>x. (P x) \<otimes> (Q (m - x)))" "mset_factors m"]
    unfolding carrier_coeff_def  P_ring_mult_def
    by blast
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Multivariable Polynomial Induction\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma mpoly_induct:
  assumes "\<And>Q. Q \<in> indexed_pset I (carrier R) \<and> card (monomials_of R Q) = 0 \<Longrightarrow> P Q"
  assumes "\<And>n. (\<And>Q. Q \<in> indexed_pset I (carrier R) \<and> card (monomials_of R Q) \<le>  n \<Longrightarrow> P Q)
             \<Longrightarrow> (\<And>Q. Q \<in> indexed_pset I (carrier R) \<and> card (monomials_of R Q) \<le> (Suc n) \<Longrightarrow> P Q)"
  assumes "Q \<in> indexed_pset I (carrier R)"
  shows "P Q"
proof-
  have "\<And>m. \<And>Q. Q \<in> indexed_pset I (carrier R) \<and> card(monomials_of R Q) \<le> m \<Longrightarrow> P Q"
  proof-
    fix m
    show "\<And>Q. Q \<in> indexed_pset I (carrier R) \<and> card(monomials_of R Q) \<le> m \<Longrightarrow> P Q"
      apply(induction m)
      using assms(1)
       apply blast
      using assms
      by blast
  qed
  then show ?thesis
    using assms(3) by blast
qed

lemma monomials_of_card_zero:
  assumes "Q \<in> indexed_pset I (carrier R) \<and> card (monomials_of R Q) = 0"
  shows "Q = indexed_const \<zero>"
proof-
  have 0: "carrier_coeff  Q"
    using assms  indexed_pset_in_carrier
    by blast
  have "\<And>m. Q m = \<zero>"
    unfolding monomials_of_def
    using assms monomials_finite
    by (metis card_0_eq complement_of_monomials_of empty_iff)
  then show  ?thesis
  using 0 assms unfolding indexed_const_def
  by auto
qed

text\<open>Polynomial induction on the number of monomials with nonzero coefficient:\<close>

lemma mpoly_induct':
  assumes "P (indexed_const \<zero>)"
  assumes "\<And>n. (\<And>Q. Q \<in> indexed_pset I (carrier R) \<and> card (monomials_of R Q) \<le>  n \<Longrightarrow> P Q)
             \<Longrightarrow> (\<And>Q. Q \<in> indexed_pset I (carrier R) \<and> card (monomials_of R Q) = (Suc n) \<Longrightarrow> P Q)"
  assumes "Q \<in> indexed_pset I (carrier R)"
  shows "P Q"
  apply(rule mpoly_induct)
  using assms(1) monomials_of_card_zero apply blast
proof-
  show "\<And>n Q. (\<And>Q. Q \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) \<le> n \<Longrightarrow> P Q) \<Longrightarrow> Q \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) \<le> Suc n \<Longrightarrow> P Q"
  proof-
    fix n
    fix Q
    assume A0: "(\<And>Q. Q \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) \<le> n \<Longrightarrow> P Q)"
    assume A1: "Q \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) \<le> Suc n"
    show "P Q"
      apply(cases  "card (monomials_of R Q) = Suc n")
      using assms A0 A1
       apply blast
      using assms A0 A1
      using le_SucE by blast
  qed
  show "Q \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
    using assms by auto
qed

lemma monomial_poly_split:
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "m \<in> monomials_of R P"
  shows "(restrict_poly_to_monom_set R P ((monomials_of R P) - {m})) \<Oplus> ((mset_to_IP R m) \<Otimes>\<^sub>p (indexed_const (P m))) = P"
proof fix x
  show "(restrict_poly_to_monom_set R P (monomials_of R P - {m}) \<Oplus> (mset_to_IP R m \<Otimes>\<^sub>p indexed_const (P m))) x = P x"
  proof(cases "x = m")
    case True
    have T0: "(restrict_poly_to_monom_set R P (monomials_of R P - {m})) x = \<zero>"
      unfolding restrict_poly_to_monom_set_def
      by (simp add: True)
    have T1: "(mset_to_IP R m \<Otimes>\<^sub>p indexed_const (P m)) x = P x"
      using assms True indexed_const_P_multE[of "mset_to_IP R m" I "P m" m]
              mset_to_IP_simp
      by (metis Idl_subset_ideal' carrier_coeffE genideal_one indexed_pset_in_carrier
          l_one mset_to_IP_closed' one_closed)
    then show ?thesis
      using T0 True
      unfolding indexed_padd_def
      using assms(1) carrier_coeffE indexed_pset_in_carrier l_zero
      by fastforce
  next
    case False
    then have F0: "(restrict_poly_to_monom_set R P (monomials_of R P - {m})) x = P x"
    proof(cases "x \<in> monomials_of R P")
      case True
      then show ?thesis
        by (simp add: False restrict_poly_to_monom_set_def)
    next
      case False
      then show ?thesis
        by (simp add: complement_of_monomials_of restrict_poly_to_monom_set_def)
    qed
    have F1: "mset_to_IP R m \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
      using assms(1) assms(2) mset_to_IP_closed' by blast
    have F2: "P m \<in> carrier R"
      using assms(1) carrier_coeffE indexed_pset_in_carrier by blast
    have F3: "(mset_to_IP R m \<Otimes>\<^sub>p indexed_const (P m)) x = \<zero>"
      using False F1 F2 assms indexed_const_P_multE[of "mset_to_IP R m" I "P m" x]
      by (simp add: F1 \<open>m \<in> monomials_of R P\<close>)
    then show ?thesis using F0 unfolding indexed_padd_def
      using assms(1) carrier_coeffE indexed_pset_in_carrier
      by fastforce
  qed
qed

lemma restrict_not_in_monoms:
  assumes "a \<notin> monomials_of R P"
  shows "restrict_poly_to_monom_set R P A = restrict_poly_to_monom_set R P (insert a A)"
proof
  fix x
  show " restrict_poly_to_monom_set R P A x = restrict_poly_to_monom_set R P (insert a A) x "
    unfolding restrict_poly_to_monom_set_def using assms unfolding monomials_of_def
  by simp
qed

lemma restriction_closed':
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "finite ms"
  shows "(restrict_poly_to_monom_set R P ms) \<in> indexed_pset I (carrier R)"
  apply(rule finite.induct[of ms])
  apply (simp add: assms(2); fail)
proof-
  show "restrict_poly_to_monom_set R P {} \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
  proof-
    have "restrict_poly_to_monom_set R P {} = indexed_const \<zero>"
      unfolding restrict_poly_to_monom_set_def indexed_const_def by auto
    then show ?thesis
      by (simp add: indexed_pset.indexed_const)
  qed
  show "\<And>A a. finite A \<Longrightarrow> restrict_poly_to_monom_set R P A \<in> (carrier R [\<X>\<^bsub>I\<^esub>]) \<Longrightarrow> restrict_poly_to_monom_set R P (insert a A) \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
  proof-
    fix A
    fix a
    assume A: "restrict_poly_to_monom_set R P A \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
    show "restrict_poly_to_monom_set R P (insert a A) \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
    proof(cases "a \<in> monomials_of R P")
      case True
      then have T0: "mset_to_IP R a \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
        using assms(1) mset_to_IP_closed' by blast
      then have T1: "(mset_to_IP R a \<Otimes>\<^sub>p indexed_const (P a)) \<in>  (carrier R [\<X>\<^bsub>I\<^esub>])"
        by (meson assms(1) carrier_coeffE indexed_pset_in_carrier
      local.ring_axioms ring.indexed_const_P_mult_closed subset_refl)

      show ?thesis
      proof(cases "a \<in> A")
        case True
        then show ?thesis
          by (simp add: A insert_absorb)
      next
        case False
        have "restrict_poly_to_monom_set R P (insert a A) = restrict_poly_to_monom_set R P A \<Oplus>  (mset_to_IP R a \<Otimes>\<^sub>p indexed_const (P a))"
        proof
          fix x
          show "restrict_poly_to_monom_set R P (insert a A) x = (restrict_poly_to_monom_set R P A \<Oplus> (mset_to_IP R a \<Otimes>\<^sub>p indexed_const (P a))) x"
          proof(cases "x = a")
            case True
            then have FT0: "(if x \<in> insert a A then P x else \<zero>) = P x"
              by simp
            have FT1: "(if x \<in> A then P x else \<zero>) = \<zero>"
              by (simp add: False True)
            have FT2: "P a \<in> carrier R"
              using assms(1) carrier_coeffE indexed_pset_in_carrier by blast
            have FT3: "(mset_to_IP R a \<Otimes>\<^sub>p indexed_const (P a)) x = P x"
              using T0 FT2 True indexed_const_P_multE[of "mset_to_IP R a" I "P a" x] mset_to_IP_simp[of a]
              by simp
            then show ?thesis
              using False
              unfolding restrict_poly_to_monom_set_def indexed_padd_def
              using FT0 FT1 FT3  assms
            by (simp add: FT2 True)
          next
            case F: False
            then have FT0: "(if x \<in> insert a A then P x else \<zero>) = (if x \<in> A then P x else \<zero>)"
              by simp
            have FT2: "P a \<in> carrier R"
              using assms(1) carrier_coeffE indexed_pset_in_carrier by blast
            have FT3: "(mset_to_IP R a \<Otimes>\<^sub>p indexed_const (P a)) x = \<zero>"
              using T0 FT2 True indexed_const_P_multE[of "mset_to_IP R a" I "P a" x] mset_to_IP_simp[of a]
              by (simp add: F mset_to_IP_def)
            show ?thesis
              unfolding restrict_poly_to_monom_set_def indexed_padd_def
            proof-

              show "(if x \<in> insert a A then P x else \<zero>) = (if x \<in> A then P x else \<zero>) \<oplus> (mset_to_IP R a \<Otimes>\<^sub>p indexed_const (P a)) x"
                apply(cases "x \<in> A")
                using FT0 FT2 FT3 F False assms  carrier_coeffE indexed_pset_in_carrier local.ring_axioms
                apply fastforce
                    using FT0 FT2 FT3 F False assms
                    by simp
                qed
          qed
        qed
        then show ?thesis
          using A T1 indexed_pset.simps by blast
      qed
    next
      case False
      then show ?thesis
        using A restrict_not_in_monoms by fastforce
    qed
  qed
qed

lemma restriction_restrict:
"restrict_poly_to_monom_set R P ms = restrict_poly_to_monom_set R P (ms \<inter> monomials_of R P)"
proof
  fix x
  show "restrict_poly_to_monom_set R P ms x = restrict_poly_to_monom_set R P (ms \<inter> monomials_of R P) x"
    unfolding restrict_poly_to_monom_set_def monomials_of_def
  by simp
qed

lemma restriction_closed:
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "Q = restrict_poly_to_monom_set R P ms"
  shows "Q \<in> indexed_pset I (carrier R)"
proof-
  have "Q = restrict_poly_to_monom_set R P (ms \<inter> monomials_of R P)"
    using assms restriction_restrict
    by blast
  then show ?thesis
    using assms restriction_closed'[of P I "(ms \<inter> monomials_of R P)"]
    using monomials_finite
    by blast
qed

lemma monomial_split_card:
  assumes "P \<in> indexed_pset I (carrier R)"
  assumes "m \<in> monomials_of R P"
  shows "card (monomials_of R (restrict_poly_to_monom_set R P ((monomials_of R P) - {m})))=
        card (monomials_of R P) -1"
proof-
  have 0: "(monomials_of R (restrict_poly_to_monom_set R P ((monomials_of R P) - {m}))) =
        (monomials_of R P) - {m}"
    using assms(1)
    by (meson Diff_subset restrict_poly_to_monom_set_monoms)
  then have 1:  "card (monomials_of R (restrict_poly_to_monom_set R P ((monomials_of R P) - {m}))) =
              card ((monomials_of R P) - {m})"
    by auto
  have " card ((monomials_of R P) - {m}) =  card (monomials_of R P) - 1"
    using assms(2)
  using assms(1) monomials_finite by fastforce
    then show ?thesis
    by (simp add: "1")
qed

lemma P_ring_mult_closed':
  assumes "a \<in> indexed_pset I (carrier R)"
  assumes "b \<in> indexed_pset I (carrier R)"
  shows "a \<Otimes>\<^sub>p b \<in> indexed_pset I (carrier R)"
  apply(rule mpoly_induct'[of "\<lambda>b. a \<Otimes>\<^sub>p b \<in> indexed_pset I (carrier R)" I b])
  using assms(1) indexed_const_P_mult_closed apply blast
proof-
  show "b \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
    using assms by auto
  show "\<And>n Q. (\<And>Q. Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) \<le> n \<Longrightarrow> a \<Otimes>\<^sub>p Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>])) \<Longrightarrow>
           Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) = Suc n \<Longrightarrow> a \<Otimes>\<^sub>p Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>])"
  proof-
    fix n
    fix Q
    assume A0: "(\<And>Q. Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) \<le> n \<Longrightarrow> a \<Otimes>\<^sub>p Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>]))"
    assume A1: "Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>]) \<and> card (monomials_of R Q) = Suc n"
    obtain m where m_def: "m \<in> monomials_of R Q"
      using A1
      by fastforce
    obtain P where P_def: "P = (restrict_poly_to_monom_set R Q ((monomials_of R Q) - {m}))"
      by simp
    have "P \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
      using P_def A1 restriction_closed
      by blast
    have 0: "a \<Otimes>\<^sub>p P \<in>  (carrier R [\<X>\<^bsub>I\<^esub>])"
      using A0 P_def
      by (metis A1 One_nat_def \<open>P \<in> (carrier R [\<X>\<^bsub>I\<^esub>])\<close> diff_Suc_Suc m_def
          minus_nat.diff_0 monomial_split_card nat_le_linear)
    have 1: "a \<Otimes>\<^sub>p (mset_to_IP R m) \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
      using assms mset_to_IP_mult_closed[of a I m] A1 m_def mset_to_IP_indices
      by blast
    have 2: "a \<Otimes>\<^sub>p (mset_to_IP R m \<Otimes>\<^sub>p indexed_const (Q m)) \<in> (carrier R [\<X>\<^bsub>I\<^esub>])"
      using P_ring_mult_assoc[of a "mset_to_IP R m" " indexed_const (Q m)"]
        1
      by (metis A1 assms(1) carrier_coeffE indexed_pset.indexed_const
          indexed_pset_in_carrier local.ring_axioms m_def mset_to_IP_closed'
          ring.indexed_const_P_mult_closed set_eq_subset)
    have 3: "(P \<Oplus> (mset_to_IP R m \<Otimes>\<^sub>p indexed_const (Q m))) = Q"
      using P_def monomial_poly_split[of Q I m]
      using A1 m_def by blast
    have 4: "(a \<Otimes>\<^sub>p P ) \<Oplus> (a \<Otimes>\<^sub>p (mset_to_IP R m \<Otimes>\<^sub>p indexed_const (Q m))) = a \<Otimes>\<^sub>p Q"
      using assms 2 3 P_ring_rdistr[of a P "(mset_to_IP R m \<Otimes>\<^sub>p indexed_const (Q m))"]
      by (metis A1 Idl_subset_ideal' P_ring_mult_closed \<open>P \<in> (carrier R [\<X>\<^bsub>I\<^esub>])\<close>
          carrier_coeffE indexed_pset.indexed_const indexed_pset_in_carrier m_def
          mset_to_IP_closed' onepideal principalideal.generate)
    then show " a \<Otimes>\<^sub>p Q \<in>  (carrier R [\<X>\<^bsub>I\<^esub>])"
      by (metis "0" "2" indexed_pset.indexed_padd)
  qed
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Subtraction of Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition P_ring_uminus :: "('a,'b) ring_scheme \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow> ('a,'c) mvar_poly" where
"P_ring_uminus R P = (\<lambda>m. \<ominus>\<^bsub>R\<^esub> (P m))"

context ring

begin


lemma P_ring_uminus_eq:
  assumes "a \<in> indexed_pset I (carrier R)"
  shows "P_ring_uminus R a  = a \<Otimes>\<^sub>p (indexed_const (\<ominus> \<one>))"
proof
    fix x
    have "(a \<Otimes>\<^sub>p indexed_const (\<ominus> \<one>)) x = a x \<otimes> \<ominus> \<one>"
      using indexed_const_P_multE[of a I "\<ominus> \<one>" x] assms
      by blast
    then show "P_ring_uminus R a x = (a \<Otimes>\<^sub>p indexed_const (\<ominus> \<one>)) x"
      unfolding P_ring_uminus_def
      using assms
      by (metis Idl_subset_ideal' carrier_coeffE indexed_pset_in_carrier
        one_closed onepideal principalideal.generate r_minus r_one)
qed

lemma P_ring_uminus_closed:
  assumes "a \<in> indexed_pset I (carrier R)"
  shows "P_ring_uminus R a \<in> indexed_pset I (carrier R)"
  using assms P_ring_uminus_eq
  by (metis add.l_inv_ex indexed_const_P_mult_closed minus_equality one_closed)

lemma P_ring_uminus_add:
  assumes "a \<in> indexed_pset I (carrier R)"
  shows "P_ring_uminus R a \<Oplus> a = indexed_const \<zero>"
proof
  fix x
  show "(P_ring_uminus R a \<Oplus> a) x = indexed_const \<zero> x"
    using assms
    unfolding P_ring_uminus_def indexed_const_def indexed_padd_def
    by (meson carrier_coeffE indexed_pset_in_carrier
        local.ring_axioms ring.ring_simprules(9) set_eq_subset)
qed

text\<open>multiplication by 1\<close>

lemma one_mult_left:
  assumes "a \<in> indexed_pset I (carrier R)"
  shows "(indexed_const \<one>) \<Otimes>\<^sub>p a = a"
proof
  fix m
  show "(indexed_const \<one> \<Otimes>\<^sub>p a) m = a m "
    unfolding indexed_const_def P_ring_mult_def
  proof-
    have 0: "(\<Oplus>x\<in>((mset_factors m) - {{#}}). (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x)) = \<zero>"
    proof-
      have "\<And>x. x\<in>((mset_factors m) - {{#}}) \<Longrightarrow>  (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x) = \<zero> \<otimes> a (m - x)"
        by simp
      then have "\<And>x. x\<in>((mset_factors m) - {{#}}) \<Longrightarrow>  (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x) = \<zero>"
        using assms
        by (metis carrier_coeffE  indexed_pset_in_carrier local.ring_axioms ring.ring_simprules(24) set_eq_subset)
      then show ?thesis
        by (meson add.finprod_one_eqI)
    qed
    have 1: "(\<lambda>x. (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x)) {#} = a m"
      by (metis (full_types) assms carrier_coeffE diff_zero
          indexed_pset_in_carrier local.ring_axioms ring.ring_simprules(12) set_eq_subset)
    have 2: "(\<Oplus>x\<in>insert {#} (mset_factors m - {{#}}). (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x)) =
              (\<lambda>x. (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x)) {#} \<oplus>
             (\<Oplus>x\<in>((mset_factors m) - {{#}}). (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x))"
    proof-
      have 20:"finite (mset_factors m - {{#}})"
        by simp
      have 21: " {#} \<notin> mset_factors m - {{#}}"
        by blast
      have 22: " (\<lambda>x. (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x)) \<in> mset_factors m - {{#}} \<rightarrow> carrier R"
      proof
        fix x
        assume A: "x \<in> mset_factors m - {{#}}"
        show "(if x = {#} then \<one> else \<zero>) \<otimes> a (m - x) \<in> carrier R"
          apply(cases "x = {#}")
          using A
          apply blast
              using assms carrier_coeffE indexed_pset_in_carrier  local.ring_axioms
              one_closed ring.ring_simprules(5) set_eq_subset zero_closed
              by (metis (mono_tags, opaque_lifting))
      qed
      have 23: "(if {#} = {#} then \<one> else \<zero>) \<otimes> a (m - {#}) \<in> carrier R"
        by (metis "1" assms carrier_coeffE indexed_pset_in_carrier set_eq_subset)
      show ?thesis
        using 20 21 22 23 finsum_insert[of  "((mset_factors m) - {{#}})" "{#}"
            " (\<lambda>x. (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x))"]
        by blast
    qed
    have 3: "insert {#} (mset_factors m - {{#}}) = mset_factors m"
    proof-
      have "{#} \<in> mset_factors m"
        using monom_divides_factors subset_mset.zero_le
        by blast
      then show ?thesis
        by blast
    qed
    show "(\<Oplus>x\<in>mset_factors m. (if x = {#} then \<one> else \<zero>) \<otimes> a (m - x)) = a m"
      using 0 1 2 3 assms
      by (metis (no_types, lifting) Idl_subset_ideal' carrier_coeffE
          genideal_one indexed_pset_in_carrier one_closed r_zero)
  qed
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
                     subsection\<open>The Carrier of the Ring of Indexed Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)


abbreviation(input) Pring_set where
"Pring_set R I \<equiv> ring.indexed_pset R I (carrier R) "

context ring

begin

lemma Pring_set_zero:
  assumes "f \<in> Pring_set R I"
  assumes "\<not> set_mset m \<subseteq>  I"
  shows " f m = \<zero>\<^bsub>R\<^esub>"
proof-
  have "\<not> set_mset m \<subseteq>  I \<Longrightarrow> f m = \<zero>\<^bsub>R\<^esub>"
  apply(induction m)
  apply simp
  by (meson assms complement_of_monomials_of mset_to_IP_indices')
  then show ?thesis
    using assms(2) by blast
qed

lemma(in ring) Pring_cfs_closed:
  assumes "P \<in> Pring_set R I"
  shows "P m \<in> carrier R"
  using assms carrier_coeffE indexed_pset_in_carrier
  by blast

lemma indexed_pset_mono_aux:
  assumes "P \<in> indexed_pset I S"
  shows "S \<subseteq> T \<Longrightarrow> P \<in> indexed_pset I T"
  using assms
  apply(induction P)
  using indexed_pset.indexed_const apply blast
  using indexed_pset.indexed_padd apply blast
  by (simp add: indexed_pset.indexed_pmult)

lemma indexed_pset_mono:
  assumes "S \<subseteq> T"
  shows "indexed_pset I S \<subseteq> indexed_pset I T"
  using assms indexed_pset_mono_aux
  by blast

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Scalar Multiplication\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition poly_scalar_mult :: "('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow> ('a,'c) mvar_poly" where
"poly_scalar_mult R c P = (\<lambda> m. c \<otimes>\<^bsub>R\<^esub> P m)"

lemma(in cring) poly_scalar_mult_eq:
  assumes "c \<in> carrier R"
  shows "P \<in> Pring_set R (I :: 'c set) \<Longrightarrow> poly_scalar_mult R c P = indexed_const c \<Otimes>\<^sub>p P"
proof(erule indexed_pset.induct)
  show "\<And>k. k \<in> carrier R \<Longrightarrow> poly_scalar_mult R c (indexed_const k) = indexed_const c \<Otimes>\<^sub>p indexed_const k"
  proof-
    fix k
    assume A0: "k \<in> carrier R"
    show "poly_scalar_mult R c (indexed_const k)  = (indexed_const c \<Otimes>\<^sub>p indexed_const k) "
      unfolding poly_scalar_mult_def
    proof
      show "\<And>m. c \<otimes> indexed_const k m = (indexed_const c \<Otimes>\<^sub>p indexed_const k) m"
          using indexed_const_P_mult_eq
          by (metis A0  assms indexed_const_P_mult_eq indexed_const_def local.semiring_axioms semiring.r_null)
    qed
  qed
  show "\<And>P Q. P \<in> Pring_set R I \<Longrightarrow>
           poly_scalar_mult R c P = indexed_const c \<Otimes>\<^sub>p P \<Longrightarrow>
           Q \<in> Pring_set R I \<Longrightarrow> poly_scalar_mult R c Q = indexed_const c \<Otimes>\<^sub>p Q \<Longrightarrow> poly_scalar_mult R c (P \<Oplus> Q) = indexed_const c \<Otimes>\<^sub>p (P \<Oplus> Q)"
  proof
    fix P Q :: "'c monomial \<Rightarrow> 'a"
    fix x :: "'c monomial"
    assume A0: "P \<in> Pring_set R I"
    assume A1: "poly_scalar_mult R c P = indexed_const c \<Otimes>\<^sub>p P"
    assume A2: "Q \<in> Pring_set R I"
    assume A3: "poly_scalar_mult R c Q = indexed_const c \<Otimes>\<^sub>p Q"
    show "poly_scalar_mult R c (P \<Oplus> Q) x = (indexed_const c \<Otimes>\<^sub>p (P \<Oplus> Q)) x"
    proof-
      have P0: "poly_scalar_mult R c (P \<Oplus> Q) = (poly_scalar_mult R c P) \<Oplus> (poly_scalar_mult R c Q)"
        unfolding poly_scalar_mult_def
      proof
        fix m
        show "c \<otimes> (P \<Oplus> Q) m = ((\<lambda>m. c \<otimes> P m) \<Oplus> (\<lambda>m. c \<otimes> Q m)) m"
        proof-
          have LHS: "c \<otimes> (P \<Oplus> Q) m = c \<otimes> ( P m \<oplus> Q m) "
            by (simp add: indexed_padd_def)
          then have LHS1: "c \<otimes> (P \<Oplus> Q) m = (c \<otimes>  P m) \<oplus> (c \<otimes>Q m) "
          proof-
            have 0: "carrier_coeff P"
              using A0 indexed_pset_in_carrier
              by blast
            have 1: "P m \<in> carrier R"
              using 0 carrier_coeffE by blast
            have 2: "carrier_coeff Q"
              using A2 indexed_pset_in_carrier
              by blast
            have 3: "Q m \<in> carrier R" using 2
              using carrier_coeff_def
              by blast
            show ?thesis using 1 3 assms
              by (simp add: LHS r_distr)
          qed
          then show ?thesis
            by (simp add: indexed_padd_def)
        qed
      qed
      have P1: "poly_scalar_mult R c (P \<Oplus> Q) = (indexed_const c \<Otimes>\<^sub>p P) \<Oplus> (indexed_const c \<Otimes>\<^sub>p Q)"
        using P0 A1 A3
        by simp
      have P2: "indexed_const c \<in> Pring_set R I"
        using assms indexed_pset.indexed_const by blast
      show ?thesis
        using P2 A0 A2 P1
        by (metis P_ring_rdistr indexed_pset_in_carrier set_eq_subset)
    qed
  qed
  show "\<And>P i. P \<in> Pring_set R I \<Longrightarrow>
           poly_scalar_mult R c P = indexed_const c \<Otimes>\<^sub>p P \<Longrightarrow> i \<in> I \<Longrightarrow> poly_scalar_mult R c (P \<Otimes> i) = indexed_const c \<Otimes>\<^sub>p (P \<Otimes> i)"
  proof-
    fix P
    fix i
    assume A0:  "P \<in> Pring_set R I"
    assume A1: "poly_scalar_mult R c P = indexed_const c \<Otimes>\<^sub>p P"
    assume A2: "i \<in> I"
    show "poly_scalar_mult R c (P \<Otimes> i) = indexed_const c \<Otimes>\<^sub>p (P \<Otimes> i)"
    proof
      fix x
      show "poly_scalar_mult R c (P \<Otimes> i) x = (indexed_const c \<Otimes>\<^sub>p (P \<Otimes> i)) x"
      proof-
        have RHS: "(indexed_const c \<Otimes>\<^sub>p (P \<Otimes> i)) = (indexed_const c \<Otimes>\<^sub>p P) \<Otimes> i"
        proof-
          have B0: "P \<Otimes> i = P \<Otimes>\<^sub>p (mset_to_IP R {#i#})"
            by (meson A0 A2 poly_index_mult)
          have B1: " (indexed_const c \<Otimes>\<^sub>p P) \<Otimes> i = (indexed_const c \<Otimes>\<^sub>p P) \<Otimes>\<^sub>p (mset_to_IP R {#i#})"
            by (meson A0 A2 P_ring_mult_closed' assms indexed_pset.simps poly_index_mult)
          have B2: "(indexed_const c \<Otimes>\<^sub>p (P \<Otimes> i)) = indexed_const c \<Otimes>\<^sub>p P \<Otimes>\<^sub>p (mset_to_IP R {#i#})"
            by (metis A0 A2 B1 assms cring.P_ring_mult_comm indexed_const_var_mult
                indexed_pmult_in_carrier indexed_pset.indexed_const indexed_pset_in_carrier
                is_cring set_eq_subset)
          show ?thesis using A0 A1 A2 B2 B1 assms
          by (simp add: A0)
        then have RHS': "(indexed_const c \<Otimes>\<^sub>p (P \<Otimes> i)) = (poly_scalar_mult R c P) \<Otimes> i"
          using A0 A1 A2 assms
          by simp
        qed
        show ?thesis apply(cases "i \<in># x")
          unfolding poly_scalar_mult_def
           apply (metis A1 RHS poly_scalar_mult_def indexed_pmult_def )
          by (metis RHS assms indexed_pmult_def r_null)
      qed
    qed
  qed
qed

lemma(in cring) poly_scalar_mult_const:
  assumes "c \<in> carrier R"
  assumes "k \<in> carrier R"
  shows "poly_scalar_mult R k (indexed_const c) = indexed_const (k \<otimes> c)"
  using assms poly_scalar_mult_eq
  by (simp add: poly_scalar_mult_eq indexed_const_P_mult_eq indexed_pset.indexed_const)

lemma(in cring) poly_scalar_mult_closed:
  assumes "c \<in> carrier R"
  assumes "P \<in> Pring_set R I"
  shows "poly_scalar_mult R c P \<in> Pring_set R I"
  using assms poly_scalar_mult_eq
  by (metis P_ring_mult_closed' indexed_pset.indexed_const)

lemma(in cring) poly_scalar_mult_zero:
  assumes "P \<in> Pring_set R I"
  shows "poly_scalar_mult R \<zero> P = indexed_const \<zero>"
proof
  fix x
  show "poly_scalar_mult R \<zero> P x = indexed_const \<zero> x"
    unfolding poly_scalar_mult_def
    using assms
    by (metis Pring_cfs_closed indexed_zero_def l_null)
qed

lemma(in cring) poly_scalar_mult_one:
  assumes "P \<in> Pring_set R I"
  shows "poly_scalar_mult R \<one> P = P"
proof
  fix x show "poly_scalar_mult R \<one> P x = P x"
    using assms
    by (metis one_closed one_mult_left poly_scalar_mult_eq)
qed

lemma(in cring) times_poly_scalar_mult:
  assumes "P \<in> Pring_set R I"
  assumes "Q \<in> Pring_set R I"
  assumes "k \<in> carrier R"
  shows "P \<Otimes>\<^sub>p (poly_scalar_mult R k Q) = poly_scalar_mult R k (P \<Otimes>\<^sub>p Q)"
proof-
  have "P \<Otimes>\<^sub>p (poly_scalar_mult R k Q) = P \<Otimes>\<^sub>p (indexed_const k) \<Otimes>\<^sub>p Q"
  by (metis assms(1) assms(2) assms(3)  indexed_pset_mono_aux
      local.ring_axioms poly_scalar_mult_eq ring.P_ring_mult_assoc ring.indexed_pset.intros(1)
      ring.indexed_pset_in_carrier subset_refl)
  then have  "P \<Otimes>\<^sub>p (poly_scalar_mult R k Q) =  (indexed_const k) \<Otimes>\<^sub>p P \<Otimes>\<^sub>p Q"
  by (metis P_ring_mult_comm assms(1) assms(3) local.ring_axioms ring.indexed_pset.indexed_const ring.indexed_pset_in_carrier subset_refl)
  then show ?thesis
    by (metis (no_types, opaque_lifting) P_ring_mult_closed' Pring_cfs_closed assms(1) assms(2) assms(3)
        carrier_coeff_def  indexed_pset.indexed_const  local.ring_axioms poly_scalar_mult_eq ring.P_ring_mult_assoc)
qed

lemma(in cring) poly_scalar_mult_times:
  assumes "P \<in> Pring_set R I"
  assumes "Q \<in> Pring_set R I"
  assumes "k \<in> carrier R"
  shows " poly_scalar_mult R k (Q \<Otimes>\<^sub>p P) = (poly_scalar_mult R k Q) \<Otimes>\<^sub>p P"
  using assms times_poly_scalar_mult
  by (metis (no_types, opaque_lifting) P_ring_mult_comm  cring.P_ring_mult_comm
      cring.poly_scalar_mult_closed is_cring local.ring_axioms ring.indexed_pset_in_carrier subset_refl)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Defining the Ring of Indexed Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)
definition Pring :: "('b, 'e) ring_scheme  \<Rightarrow> 'a set  \<Rightarrow> ('b, ('b,'a) mvar_poly) module" where

"Pring R I \<equiv> \<lparr>  carrier = Pring_set R I,
                Group.monoid.mult = P_ring_mult R ,
                one = ring.indexed_const R \<one>\<^bsub>R\<^esub>,
                zero = ring.indexed_const R  \<zero>\<^bsub>R\<^esub>,
                add = ring.indexed_padd R,
                smult = poly_scalar_mult R\<rparr>"

context ring

begin

lemma Pring_car:
"carrier (Pring R I) = Pring_set R I"
  unfolding Pring_def
  by auto

text\<open>Definitions of the operations and constants:\<close>

lemma Pring_mult:
"a \<otimes>\<^bsub>Pring R I\<^esub> b = a \<Otimes>\<^sub>p b"
  unfolding Pring_def
  by simp

lemma Pring_add:
"a \<oplus>\<^bsub>Pring R I\<^esub> b = a \<Oplus> b"
  unfolding Pring_def
  by simp

lemma Pring_zero:
"\<zero>\<^bsub>Pring R I\<^esub> = indexed_const \<zero>"
  unfolding Pring_def by simp

lemma Pring_one:
"\<one>\<^bsub>Pring R I\<^esub> = indexed_const \<one>"
  unfolding Pring_def by simp

lemma Pring_smult:
"(\<odot>\<^bsub>Pring R I\<^esub>) = (poly_scalar_mult R)"
  unfolding Pring_def by simp

lemma Pring_carrier_coeff:
  assumes "a \<in> carrier (Pring R I)"
  shows "carrier_coeff a"
  using assms indexed_pset_in_carrier[of "(carrier R)" a I] Pring_car
  by blast

lemma Pring_carrier_coeff'[simp]:
  assumes "a \<in> carrier (Pring R I)"
  shows "a m \<in> carrier R"
  using Pring_car[of I] assms carrier_coeffE indexed_pset_in_carrier
  by blast

lemma Pring_add_closed:
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  shows "a \<oplus>\<^bsub>Pring R I\<^esub> b \<in> carrier (Pring R I)"
  using assms  Pring_def[of R I]
  by (simp add: Pring_def[of R I] indexed_pset.indexed_padd)

lemma Pring_mult_closed:
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  shows "a \<otimes>\<^bsub>Pring R I\<^esub> b \<in> carrier (Pring R I)"
  using assms  P_ring_mult_closed'[of a I b] Pring_car[of I] Pring_mult[of I a b]
  by (simp add: \<open>a \<otimes>\<^bsub>Pring R I\<^esub> b = a \<Otimes>\<^sub>p b\<close> \<open>carrier (Pring R I) = Pring_set R I\<close>)

lemma Pring_one_closed:
"\<one>\<^bsub>Pring R I\<^esub> \<in> carrier (Pring R I)"
proof-
  have "indexed_const \<one> \<in> carrier (Pring R I)"
    using Pring_car indexed_pset.simps by blast
  then show ?thesis
    unfolding Pring_def by auto
qed

lemma Pring_zero_closed:
"\<zero>\<^bsub>Pring R I\<^esub> \<in> carrier (Pring R I)"
proof-
  have "indexed_const \<zero> \<in> carrier (Pring R I)"
    using Pring_car indexed_pset.simps by blast
  then show ?thesis
    unfolding Pring_def by auto
qed

lemma Pring_var_closed:
  assumes "i \<in> I"
  shows "var_to_IP R i \<in> carrier (Pring R I)"
unfolding var_to_IP_def
  by (metis Pring_car Pring_one_closed assms indexed_pset.indexed_pmult
      local.ring_axioms monom_add_mset one_mset_to_IP ring.Pring_one)

text\<open>Properties of addition:\<close>

lemma Pring_add_assoc:
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  assumes "c \<in> carrier (Pring R I)"
  shows "a \<oplus>\<^bsub>Pring R I\<^esub> (b \<oplus>\<^bsub>Pring R I\<^esub> c) = (a \<oplus>\<^bsub>Pring R I\<^esub> b) \<oplus>\<^bsub>Pring R I\<^esub> c"
proof-
  have "a \<Oplus> (b \<Oplus> c) = (a \<Oplus>  b) \<Oplus>  c"
  proof
    fix x
    have "carrier_coeff a" "carrier_coeff b" "carrier_coeff c"
      using assms Pring_car[of I] Pring_carrier_coeff   apply blast
        using assms Pring_car[of I] Pring_carrier_coeff   apply blast
          using assms Pring_car[of I] Pring_carrier_coeff   by blast
    then have "a x \<in> carrier R" "b x \<in> carrier R" "c x \<in> carrier R"
      using carrier_coeffE apply blast
        using \<open>carrier_coeff b\<close> carrier_coeffE apply blast
          using \<open>carrier_coeff c\<close> carrier_coeffE by blast
    show "(a \<Oplus> (b \<Oplus> c)) x = (a \<Oplus> b \<Oplus> c) x"
      unfolding indexed_padd_def
      using assms
      by (simp add: \<open>a x \<in> carrier R\<close> \<open>b x \<in> carrier R\<close> \<open>c x \<in> carrier R\<close> add.m_assoc)
  qed
  then show ?thesis
    using assms
  by (simp add: Pring_add)
qed

lemma Pring_add_comm:
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  shows "a \<oplus>\<^bsub>Pring R I\<^esub> b = b \<oplus>\<^bsub>Pring R I\<^esub> a"
proof-
  have "a \<Oplus> b = b \<Oplus> a"
  proof fix x
    show "(a \<Oplus> b) x = (b \<Oplus> a) x"
      using assms
      by (metis abelian_monoid.a_comm abelian_monoid_axioms
          indexed_padd_def local.ring_axioms ring.Pring_carrier_coeff')
  qed
  then show ?thesis
    by (simp add: Pring_add)
qed

lemma Pring_add_zero:
  assumes "a \<in> carrier (Pring R I)"
  shows "a \<oplus>\<^bsub>Pring R I\<^esub> \<zero>\<^bsub>Pring R I\<^esub> = a"
        "\<zero>\<^bsub>Pring R I\<^esub> \<oplus>\<^bsub>Pring R I\<^esub> a  = a"
  using assms Pring_zero Pring_add
   apply (metis Pring_carrier_coeff indexed_padd_zero(1))
  using assms Pring_zero Pring_add
   by (metis Pring_carrier_coeff indexed_padd_zero(2))

text\<open>Properties of multiplication\<close>

lemma Pring_mult_assoc:
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  assumes "c \<in> carrier (Pring R I)"
  shows "a \<otimes>\<^bsub>Pring R I\<^esub> (b \<otimes>\<^bsub>Pring R I\<^esub> c) = (a \<otimes>\<^bsub>Pring R I\<^esub> b) \<otimes>\<^bsub>Pring R I\<^esub> c"
  using assms P_ring_mult_assoc[of a b c]
  by (metis Pring_carrier_coeff Pring_mult)

lemma Pring_mult_comm:
  assumes "cring R"
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  shows "a \<otimes>\<^bsub>Pring R I\<^esub> b = b \<otimes>\<^bsub>Pring R I\<^esub> a"
  using assms Pring_carrier_coeff[of a I] Pring_carrier_coeff[of b I]
        Pring_mult[of I b a]  Pring_mult[of I a b] cring.P_ring_mult_comm[of R a b]
  by metis

lemma Pring_mult_one:
  assumes "a \<in> carrier (Pring R I)"
  shows "a \<otimes>\<^bsub>Pring R I\<^esub> \<one>\<^bsub>Pring R I\<^esub> = a"
proof
  fix x
  show "(a \<otimes>\<^bsub>Pring R I\<^esub> \<one>\<^bsub>Pring R I\<^esub>) x = a x "
  proof-
    have 0: "(a \<otimes>\<^bsub>Pring R I\<^esub> \<one>\<^bsub>Pring R I\<^esub>) x = (a \<Otimes>\<^sub>p indexed_const \<one>) x"
        using assms Pring_mult[of I a "\<one>\<^bsub>Pring R I\<^esub>" ] Pring_one[of I]
        by metis
    have 1: "\<one> \<in> carrier R"
      by simp
    have 2: "(a \<otimes>\<^bsub>Pring R I\<^esub> \<one>\<^bsub>Pring R I\<^esub>) x =  a x \<otimes> \<one>"
      using 0 1 indexed_const_P_multE[of a I \<one> x]
        assms Pring_car[of I]
      by metis
    then show ?thesis
      using assms by auto
  qed
qed

lemma Pring_mult_one':
  assumes "a \<in> carrier (Pring R I)"
  shows "\<one>\<^bsub>Pring R I\<^esub>  \<otimes>\<^bsub>Pring R I\<^esub> a = a"
  using one_mult_left[of a I]
        assms Pring_one Pring_mult
  by (simp add: Pring_mult Pring_one Pring_car)

text\<open>Distributive laws\<close>

lemma Pring_mult_rdistr:
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  assumes "c \<in> carrier (Pring R I)"
  shows "a \<otimes>\<^bsub>Pring R I\<^esub> (b \<oplus>\<^bsub>Pring R I\<^esub> c) = (a \<otimes>\<^bsub>Pring R I\<^esub> b) \<oplus>\<^bsub>Pring R I\<^esub> (a \<otimes>\<^bsub>Pring R I\<^esub> c)"
proof-
  have "a \<Otimes>\<^sub>p (b \<Oplus> c) = a \<Otimes>\<^sub>p b \<Oplus> (a \<Otimes>\<^sub>p c)"
  using P_ring_rdistr[of a b c]
        assms Pring_carrier_coeff
  by metis
  then have "a \<Otimes>\<^sub>p (b \<oplus>\<^bsub>Pring R I\<^esub> c) = a \<Otimes>\<^sub>p b \<oplus>\<^bsub>Pring R I\<^esub> (a \<Otimes>\<^sub>p c)"
    using       Pring_add[of I b c] Pring_add[of I "a \<Otimes>\<^sub>p b" "a \<Otimes>\<^sub>p c"]
    by auto
  then have "a \<otimes>\<^bsub>Pring R I\<^esub> (b \<oplus>\<^bsub>Pring R I\<^esub> c) = (a \<Otimes>\<^sub>p b) \<oplus>\<^bsub>Pring R I\<^esub> (a \<Otimes>\<^sub>p c)"
    using  Pring_mult[of I a "(b \<oplus>\<^bsub>Pring R I\<^esub> c)"]
    by auto
  then have "a \<otimes>\<^bsub>Pring R I\<^esub> (b \<oplus>\<^bsub>Pring R I\<^esub> c) = (a \<otimes>\<^bsub>Pring R I\<^esub> b) \<oplus>\<^bsub>Pring R I\<^esub> (a \<Otimes>\<^sub>p c)"
    using Pring_mult[of I a b] by metis
  then show ?thesis
    using Pring_mult[of I a c] by metis
qed

lemma Pring_mult_ldistr:
  assumes "a \<in> carrier (Pring R I)"
  assumes "b \<in> carrier (Pring R I)"
  assumes "c \<in> carrier (Pring R I)"
  shows "(b \<oplus>\<^bsub>Pring R I\<^esub> c) \<otimes>\<^bsub>Pring R I\<^esub> a  = (b \<otimes>\<^bsub>Pring R I\<^esub> a) \<oplus>\<^bsub>Pring R I\<^esub> (c \<otimes>\<^bsub>Pring R I\<^esub> a)"
proof-
  have "(b \<Oplus> c) \<Otimes>\<^sub>p a = b \<Otimes>\<^sub>p a \<Oplus> (c \<Otimes>\<^sub>p a)"
  using P_ring_ldistr[of a b c]
        assms Pring_carrier_coeff
  by metis
  then have " (b \<oplus>\<^bsub>Pring R I\<^esub> c)  \<Otimes>\<^sub>p a = b \<Otimes>\<^sub>p a \<oplus>\<^bsub>Pring R I\<^esub> (c \<Otimes>\<^sub>p a)"
    using       Pring_add[of I b c] Pring_add[of I "b \<Otimes>\<^sub>p a" "c \<Otimes>\<^sub>p a"]
    by auto
  then have " (b \<oplus>\<^bsub>Pring R I\<^esub> c) \<otimes>\<^bsub>Pring R I\<^esub> a = (b \<Otimes>\<^sub>p a) \<oplus>\<^bsub>Pring R I\<^esub> (c \<Otimes>\<^sub>p a)"
    using  Pring_mult[of I "(b \<oplus>\<^bsub>Pring R I\<^esub> c)" a]
    by auto
  then have "(b \<oplus>\<^bsub>Pring R I\<^esub> c) \<otimes>\<^bsub>Pring R I\<^esub> a = (b \<otimes>\<^bsub>Pring R I\<^esub> a) \<oplus>\<^bsub>Pring R I\<^esub> (c \<Otimes>\<^sub>p a)"
    using Pring_mult[of I b a] by metis
  then show ?thesis
    using Pring_mult[of I c a] by metis
qed

text\<open>Properties of subtraction:\<close>

lemma Pring_uminus:
  assumes "a \<in> carrier (Pring R I)"
  shows "P_ring_uminus R a \<in> carrier (Pring R I)"
  using P_ring_uminus_closed[of a I] Pring_car[of I] assms
  by metis

lemma Pring_subtract:
  assumes "a \<in> carrier (Pring R I)"
  shows "P_ring_uminus R a \<oplus>\<^bsub>Pring R I\<^esub> a = \<zero>\<^bsub>Pring R I\<^esub>"
        "a \<oplus>\<^bsub>Pring R I\<^esub> P_ring_uminus R a = \<zero>\<^bsub>Pring R I\<^esub>"
  using assms Pring_add[of I "P_ring_uminus R a " a] Pring_zero[of I]
  apply  (simp add: Pring_car local.ring_axioms ring.P_ring_uminus_add)
    using assms Pring_add[of I "P_ring_uminus R a " a] Pring_zero[of I]
    by (metis P_ring_uminus_add P_ring_uminus_closed Pring_add_comm Pring_car)

text\<open>Pring R I is a ring\<close>

lemma Pring_is_abelian_group:
  shows "abelian_group (Pring R I)"
  apply(rule abelian_groupI)
  apply (simp add: Pring_add_closed)
    apply (simp add: local.ring_axioms ring.Pring_zero_closed)
      apply (simp add: Pring_add_assoc)
        apply (simp add: Pring_add_comm)
          apply (simp add: local.ring_axioms ring.Pring_add_zero(2))
  using Pring_subtract(1) Pring_uminus
  by blast

lemma Pring_is_monoid:
"Group.monoid (Pring R I)"
  apply(rule monoidI)
  using Pring_mult_closed apply blast
    apply (simp add: Pring_one_closed)
      apply (metis Pring_mult_assoc)
        using Pring_mult_one'
        apply blast
  using Pring_mult_one by blast

lemma Pring_is_ring:
  shows "ring (Pring R I)"
  apply(rule ringI)
  apply (simp add: Pring_is_abelian_group)
    apply (simp add: Pring_is_monoid)
      apply (simp add: Pring_mult_ldistr)
  by (simp add: Pring_mult_rdistr)

lemma Pring_is_cring:
  assumes "cring R"
  shows "cring (Pring R I)"
  apply(rule cringI)
  apply (simp add: Pring_is_abelian_group)
   apply (simp add: Pring_is_monoid assms local.ring_axioms
          monoid.monoid_comm_monoidI ring.Pring_mult_comm)
     by (simp add: Pring_mult_ldistr)

lemma Pring_a_inv:
  assumes "P \<in> carrier (Pring R I)"
  shows "\<ominus>\<^bsub>Pring R I\<^esub> P = P_ring_uminus R P"
proof-
  have 0: "P_ring_uminus R P \<in> carrier (Pring R I)"
    using Pring_uminus assms
    by blast
  have 1: "P_ring_uminus R P \<oplus>\<^bsub>Pring R I\<^esub> P = \<zero>\<^bsub>Pring R I\<^esub>"
    using Pring_subtract(1) assms
    by blast
  show ?thesis using 0 1 assms Pring_is_ring
  by (simp add: Pring_car Pring_is_abelian_group abelian_group.minus_equality)
qed


end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Defining the R-Algebra of Indexed Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context cring
begin

lemma Pring_smult_cfs:
  assumes "a \<in> carrier R"
  assumes "P \<in> carrier (Pring R I)"
  shows "(a \<odot>\<^bsub>Pring R I\<^esub> P) m = a \<otimes> (P m)"
  using assms Pring_smult
  by (simp add: Pring_smult poly_scalar_mult_def)

lemma Pring_smult_closed:
      "\<And> a x. [| a \<in> carrier R; x \<in> carrier (Pring R I) |] ==> a \<odot>\<^bsub>(Pring R I)\<^esub> x \<in> carrier (Pring R I)"
  by (simp add: Pring_car Pring_smult poly_scalar_mult_closed)

lemma Pring_smult_l_distr:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier (Pring R I) |] ==>
      (a \<oplus> b) \<odot>\<^bsub>(Pring R I)\<^esub> x = (a \<odot>\<^bsub>(Pring R I)\<^esub> x) \<oplus>\<^bsub>(Pring R I)\<^esub> (b \<odot>\<^bsub>(Pring R I)\<^esub> x)"
proof- fix a b x assume A: "a \<in> carrier R" "b \<in> carrier R" "x \<in> carrier (Pring R I)"
  show "(a \<oplus> b) \<odot>\<^bsub>Pring R I\<^esub> x = a \<odot>\<^bsub>Pring R I\<^esub> x \<oplus>\<^bsub>Pring R I\<^esub> b \<odot>\<^bsub>Pring R I\<^esub> x"
  proof fix m
    have "(a \<oplus> b) \<otimes> x m = (a \<otimes> (x m)) \<oplus> (b \<otimes> (x m))"
      by (meson A(1) A(2) A(3) Pring_carrier_coeff' local.semiring_axioms semiring.l_distr)
    thus "((a \<oplus> b) \<odot>\<^bsub>Pring R I\<^esub> x) m = (a \<odot>\<^bsub>Pring R I\<^esub> x \<oplus>\<^bsub>Pring R I\<^esub> b \<odot>\<^bsub>Pring R I\<^esub> x) m"
      using Pring_smult_cfs[of "a \<oplus> b" x I m]
            Pring_smult_cfs[of "a" x I m]
            Pring_smult_cfs[of "b" x I m]
            Pring_smult_closed[of a x I]
            Pring_smult_closed[of b x I]
            Pring_add  A
      by (simp add: \<open>(a \<oplus> b) \<otimes> x m = a \<otimes> x m \<oplus> b \<otimes> x m\<close> Pring_def indexed_padd_def poly_scalar_mult_def)
  qed
qed

lemma Pring_smult_r_distr:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier (Pring R I); y \<in> carrier (Pring R I) |] ==>
      a \<odot>\<^bsub>(Pring R I)\<^esub> (x \<oplus>\<^bsub>(Pring R I)\<^esub> y) = (a \<odot>\<^bsub>(Pring R I)\<^esub> x) \<oplus>\<^bsub>(Pring R I)\<^esub> (a \<odot>\<^bsub>(Pring R I)\<^esub> y)"
proof fix a x y m assume A: "a \<in> carrier R" "x \<in> carrier (Pring R I)" "y \<in> carrier (Pring R I)"
  show "(a \<odot>\<^bsub>Pring R I\<^esub> (x \<oplus>\<^bsub>Pring R I\<^esub> y)) m =
       (a \<odot>\<^bsub>Pring R I\<^esub> x \<oplus>\<^bsub>Pring R I\<^esub> a \<odot>\<^bsub>Pring R I\<^esub> y) m"
    using Pring_smult_cfs[of a "x \<oplus>\<^bsub>Pring R I\<^esub> y" I m]
            Pring_smult_cfs[of a x I m]
            Pring_smult_cfs[of a y I m]
            Pring_smult_closed[of a x I]
            Pring_smult_closed[of a y I]
            Pring_add  A
  by (metis (no_types, lifting) Pring_add_closed Pring_carrier_coeff' indexed_padd_def l_distr m_comm)
qed

lemma Pring_smult_assoc1:
      "!!a b x. [| a \<in> carrier R; b \<in> carrier R; x \<in> carrier (Pring R I) |] ==>
      (a \<otimes> b) \<odot>\<^bsub>Pring R I\<^esub> x = a \<odot>\<^bsub>Pring R I\<^esub> (b \<odot>\<^bsub>Pring R I\<^esub> x)"
proof fix a b x m  assume A: "a \<in> carrier R" "b \<in> carrier R" "x \<in> carrier (Pring R I)"
  show " (a \<otimes> b \<odot>\<^bsub>Pring R I\<^esub> x) m = (a \<odot>\<^bsub>Pring R I\<^esub> (b \<odot>\<^bsub>Pring R I\<^esub> x)) m"
      using Pring_smult_cfs[of "a \<otimes> b" x I m]
            Pring_smult_cfs[of a "b \<odot>\<^bsub>Pring R I\<^esub> x" I m]
            Pring_smult_cfs[of "b" x I m]
            Pring_smult_closed[of a "b \<odot>\<^bsub>Pring R I\<^esub> x" I]
            Pring_smult_closed[of b x I]
            A(1) A(2) A(3) m_assoc m_closed by auto
qed

lemma Pring_smult_one:
      "!!x. x \<in> carrier (Pring R I) ==> (one R) \<odot>\<^bsub>Pring R I\<^esub> x = x"
  by (simp add: Pring_car Pring_smult poly_scalar_mult_one)


lemma Pring_smult_assoc2:
      "!!a x y. [| a \<in> carrier R; x \<in> carrier (Pring R I); y \<in> carrier (Pring R I) |] ==>
      (a \<odot>\<^bsub>Pring R I\<^esub> x) \<otimes>\<^bsub>Pring R I\<^esub> y = a \<odot>\<^bsub>Pring R I\<^esub> (x \<otimes>\<^bsub>Pring R I\<^esub> y)"
  by (simp add: Pring_def poly_scalar_mult_times)

lemma Pring_algebra:
"algebra R (Pring R I)"
  apply(rule algebraI)
         apply (simp add: is_cring)
        apply (simp add: Pring_is_cring is_cring)
       apply (simp add: Pring_smult_closed)
      apply (simp add: Pring_smult_l_distr)
     apply (simp add: Pring_smult_r_distr)
    apply (simp add: Pring_smult_assoc1)
   apply (simp add: Pring_smult_one)
  by (simp add: Pring_smult_assoc2)


end



(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Evaluation of Polynomials and Subring Structure\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  In this section the aim is to define the evaluation of a polynomial over its base ring. We define
  both total evaluation of a polynomial at all variables, and partial evaluation at only a subset
  of variables. The basic input for evaluation is a variable assignment function mapping variables
  to ring elements. Once we can evaluate a polynomial $P$ in variables $I$ over a ring $R$ at an
  assignment $f: I \to R$, this can be generalized to evaluation of $P$ in some other ring $S$,
  given a variable assignment $f: I \to S$ and a ring homomorphism $\phi: R \to S$. We chose to
  define this by simply applying $\phi$ to the coefficients of $P$, and then using the first
  evaluation function over $S$. This could also have been done the other way around: define
  general polynomial evaluation over any ring, given a ring hom $\phi$, and then defining
  evaluation over the base ring $R$ as the specialization of this function to the case there
  $\phi = \mathit{id}_R$.\<close>

definition remove_monom ::
"('a,'b) ring_scheme \<Rightarrow> 'c monomial \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> ('a, 'c) mvar_poly" where
"remove_monom R m P = ring.indexed_padd R P (poly_scalar_mult R (\<ominus>\<^bsub>R\<^esub> P m) (mset_to_IP R m))"

context cring
begin

lemma remove_monom_alt_def:
  assumes "P \<in> Pring_set R I"
  shows "remove_monom R m P n = (if n = m then \<zero> else P n)"
  unfolding remove_monom_def
  apply(cases "n = m")
  using assms
   apply (metis Pring_cfs_closed cring.cring_simprules(3) poly_scalar_mult_def
          indexed_padd_def is_cring mset_to_IP_simp r_neg r_one)
   using assms
   by (metis Pring_cfs_closed add.l_cancel_one cring.cring_simprules(3)
       poly_scalar_mult_def indexed_padd_def is_cring mset_to_IP_simp' r_null zero_closed)

lemma remove_monom_zero:
  assumes "m \<notin> monomials_of R P"
  assumes "P \<in> Pring_set R I"
  shows "remove_monom R m P = P"
proof
  fix x
  show "remove_monom R m P x = P x "
    apply(cases "x \<in> monomials_of R P")
    using assms unfolding monomials_of_def remove_monom_def
  apply (metis cring.remove_monom_alt_def is_cring remove_monom_def)
    using assms unfolding monomials_of_def remove_monom_def
    by (metis assms(1) cring.remove_monom_alt_def is_cring local.ring_axioms
        remove_monom_def ring.complement_of_monomials_of)
qed

lemma remove_monom_closed:
  assumes "P \<in> Pring_set R I"
  shows "remove_monom R m P \<in> Pring_set R I"

  apply(cases "m \<in> monomials_of R P")
  using assms poly_scalar_mult_closed[of "(\<ominus> P m)" "(mset_to_IP R m)" I] mset_to_IP_closed[of m I]
  unfolding remove_monom_def
  apply (meson Pring_cfs_closed add.inv_closed indexed_pset.indexed_padd mset_to_IP_closed')
  by (metis assms remove_monom_def remove_monom_zero)

lemma remove_monom_monomials:
  assumes "P \<in> Pring_set R I"
  shows "monomials_of R (remove_monom R m P) = monomials_of R P - {m}"
proof
  show "monomials_of R (remove_monom R m P) \<subseteq> monomials_of R P - {m}"
    using assms remove_monom_alt_def[of P I m]
    unfolding monomials_of_def
    by auto
  show "monomials_of R P - {m} \<subseteq> monomials_of R (remove_monom R m P)"
    using assms remove_monom_alt_def[of P I m]
    unfolding monomials_of_def
    by auto
qed

text\<open>The additive decomposition of a polynomial by a monomial\<close>

lemma remove_monom_eq:
  assumes "P \<in> Pring_set R I"
  shows "P = (remove_monom R a P) \<Oplus> poly_scalar_mult R  (P a) (mset_to_IP R a)"
  unfolding remove_monom_def poly_scalar_mult_def
proof
  fix x
  show "P x = (P \<Oplus> (\<lambda>m. \<ominus> P a \<otimes> mset_to_IP R a m) \<Oplus> (\<lambda>m. P a \<otimes> mset_to_IP R a m)) x"
  apply(cases "x = a")
     apply (metis Pring_cfs_closed assms l_minus l_zero local.ring_axioms mset_to_IP_simp one_closed r_neg r_one ring.indexed_padd_def)
  proof-
    assume A: "x \<noteq> a"
    show "P x = (P \<Oplus> (\<lambda>m. \<ominus> P a \<otimes> mset_to_IP R a m) \<Oplus> (\<lambda>m. P a \<otimes> mset_to_IP R a m)) x"
      using assms A
      unfolding mset_to_IP_def indexed_padd_def
      using Pring_cfs_closed by fastforce
  qed
qed

lemma remove_monom_restrict_poly_to_monom_set:
  assumes "P \<in> Pring_set R I"
  assumes "monomials_of R P = insert a M"
  assumes "a \<notin> M"
  shows "(remove_monom R a P) = restrict_poly_to_monom_set R P M"
proof
  fix m
  show "remove_monom R a P m= restrict_poly_to_monom_set R P M m"
    apply(cases "m = a")
    using assms apply (metis remove_monom_alt_def restrict_poly_to_monom_set_def)
    using assms
    by (metis complement_of_monomials_of insert_iff remove_monom_alt_def restrict_poly_to_monom_set_def)
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Nesting of Polynomial Rings According to Nesting of Index Sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma(in ring) Pring_carrier_subset:
  assumes "J \<subseteq> I"
  shows "(Pring_set R J) \<subseteq> (Pring_set R I)"
proof
  fix P
  show "P \<in> Pring_set R J \<Longrightarrow>P \<in> Pring_set R I"
    apply(erule indexed_pset.induct)
    using indexed_pset.indexed_const apply blast
      using indexed_pset.indexed_padd apply blast
        by (meson assms indexed_pset.indexed_pmult subsetD)
qed

lemma(in cring) Pring_set_restrict_induct:
  shows "finite S \<Longrightarrow> \<forall>P. monomials_of R P = S \<and>  P \<in> Pring_set R I \<and>  (\<forall> m \<in> monomials_of R P. set_mset m \<subseteq> J) \<longrightarrow>  P \<in> Pring_set R J"
proof(erule finite.induct)
  show "\<forall>P. monomials_of R P = {} \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J) \<longrightarrow> P \<in> Pring_set R J"
  proof
    fix P
    show "monomials_of R P = {} \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J) \<longrightarrow> P \<in> Pring_set R J"
    proof
      assume A0: "monomials_of R P = {} \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J)"
      show "P \<in> Pring_set R J "
        by (metis A0 card_eq_0_iff indexed_pset.indexed_const monomials_of_card_zero zero_closed)
    qed
  qed
  show "\<And>A a. finite A \<Longrightarrow>
           \<forall>P. monomials_of R P = A \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J) \<longrightarrow> P \<in> Pring_set R J \<Longrightarrow>
           \<forall>P. monomials_of R P = insert a A \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J) \<longrightarrow> P \<in> Pring_set R J"
  proof
    fix A :: "('c monomial) set" fix a fix P
    assume A1: "finite A"
    assume A2: "\<forall>P. monomials_of R P = A \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J) \<longrightarrow> P \<in> Pring_set R J"
    show "monomials_of R P = insert a A \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J) \<longrightarrow> P \<in> Pring_set R J "
    proof
      assume A3: "monomials_of R P = insert a A \<and> P \<in> Pring_set R I \<and> (\<forall>m\<in>monomials_of R P. set_mset m \<subseteq> J)"
      show "P \<in> Pring_set R  J"
        apply(cases "a \<in>   A")
         apply (metis A2 A3 insert_absorb)
      proof-
        assume N: "a \<notin> A"
        obtain Q where Q_def: "Q = remove_monom R a P"
          by simp
        have Q0: "monomials_of R Q = A"
        proof-
          have 0:  "monomials_of R P = insert a A"
            by (simp add: A3)
          have 1: "P \<in> Pring_set R I"
            using A3 by blast
          have 2: "monomials_of R (remove_monom R a P) = monomials_of R P - {a}"
            using A3 remove_monom_monomials by blast
          then show ?thesis
            using Q_def 0
            by (simp add: N)
        qed
        have Q1: "Q \<in> Pring_set R I"
          using A3 Q_def remove_monom_closed by blast
        have Q2: "(\<forall>m\<in>monomials_of R Q. set_mset m \<subseteq> J)"
          using Q0 A3
          by blast
        have "Q \<in> Pring_set R J"
          using A2 Q0 Q1 Q2 by blast
        then show "P \<in> Pring_set R J"
        proof-
          have "P = Q \<Oplus> poly_scalar_mult R  (P a) (mset_to_IP R a)"
            using Q_def remove_monom_eq
            using A3 by blast
          then show ?thesis
            by (metis A3 Pring_cfs_closed \<open>Q \<in> Pring_set R J\<close> indexed_pset.indexed_padd insertCI mset_to_IP_closed poly_scalar_mult_closed)
        qed
      qed
    qed
  qed
qed

lemma(in cring) Pring_set_restrict:
  assumes "P \<in> Pring_set R I"
  assumes "(\<And>m.  m \<in> monomials_of R P \<Longrightarrow>  set_mset m \<subseteq> J)"
  shows " P \<in> Pring_set R J"
  using assms Pring_set_restrict_induct[of "monomials_of R P"]
  by (metis monomials_finite)

lemma(in ring) Pring_mult_eq:
  fixes I:: "'c set"
  fixes J:: "'c set"
  shows "(\<otimes>\<^bsub>Pring R I\<^esub>) = (\<otimes>\<^bsub>Pring R J\<^esub>)"
  by (simp add: Pring_def)

lemma(in ring) Pring_add_eq:
  fixes I:: "'c set"
  fixes J:: "'c set"
  shows "(\<oplus>\<^bsub>Pring R I\<^esub>) = (\<oplus>\<^bsub>Pring R J\<^esub>)"
  using Pring_def
  by (simp add: Pring_def)

lemma(in ring) Pring_one_eq:
  fixes I:: "'c set"
  fixes J:: "'c set"
  shows "(\<one>\<^bsub>Pring R I\<^esub>) = (\<one>\<^bsub>Pring R J\<^esub>)"
  using Pring_def
  by (simp add: Pring_def)

lemma(in ring) Pring_zero_eq:
  fixes I:: "'c set"
  fixes J:: "'c set"
  shows "(\<zero>\<^bsub>Pring R I\<^esub>) = (\<zero>\<^bsub>Pring R J\<^esub>)"
  using Pring_def
  by (simp add: Pring_def)

lemma(in ring) index_subset_Pring_subring:
  assumes "J \<subseteq> I"
  shows "subring (carrier (Pring R J)) (Pring R I)"
  apply(rule ring.subringI)
  apply (simp add: Pring_is_ring; fail)
    using assms
   apply (simp add: Pring_car Pring_carrier_subset; fail)
   using Pring_def
         apply (simp add: Pring_def indexed_pset.indexed_const; fail)
    proof-
      show "\<And>h. h \<in> carrier (Pring R J) \<Longrightarrow> \<ominus>\<^bsub>Pring R I\<^esub> h \<in> carrier (Pring R J)"
      proof-
        fix h
        assume A: "h \<in> carrier (Pring R J)"
        then have A0: "\<ominus>\<^bsub>Pring R J\<^esub> h = P_ring_uminus R h"
          using Pring_a_inv[of h J]
          by auto
        have A1: "\<ominus>\<^bsub>Pring R I\<^esub> h = P_ring_uminus R h"
          using assms A Pring_carrier_subset[of J I] Pring_a_inv[of h I] Pring_car
          by blast
        show "\<ominus>\<^bsub>Pring R I\<^esub> h \<in> carrier (Pring R J)"
          using A0 A1 A
          by (simp add: Pring_uminus)
      qed
      show " \<And>h1 h2. h1 \<in> carrier (Pring R J) \<Longrightarrow> h2 \<in> carrier (Pring R J) \<Longrightarrow> h1 \<otimes>\<^bsub>Pring R I\<^esub> h2 \<in> carrier (Pring R J)"
        using assms Pring_mult_eq
        by (metis Pring_mult_closed)
      show " \<And>h1 h2. h1 \<in> carrier (Pring R J) \<Longrightarrow> h2 \<in> carrier (Pring R J) \<Longrightarrow> h1 \<oplus>\<^bsub>Pring R I\<^esub> h2 \<in> carrier (Pring R J)"
        using assms Pring_add_eq
        by (metis Pring_add_closed)
    qed


(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Inclusion Maps\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition Pring_inc :: "('a, 'c) mvar_poly \<Rightarrow> ('a, 'c) mvar_poly" where
"Pring_inc \<equiv> (\<lambda>P. P)"

lemma(in ring) Princ_inc_is_ring_hom:
  assumes "J \<subseteq> I"
  shows "ring_hom_ring (Pring R J) (Pring R I) Pring_inc"
  unfolding Pring_inc_def
  apply(rule ring_hom_ringI)
  apply (simp add: Pring_is_ring)
    using Pring_is_ring apply blast
       using index_subset_Pring_subring[of I J] assms index_subset_Pring_subring subringE(1)
       apply blast
          using Pring_mult_eq[of I J]
          apply (simp add: Pring_mult)
             using Pring_add_eq[of I J]
             apply (simp add: Pring_add)
             using Pring_one_eq
  by (simp add: Pring_one_eq)

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Restricting a Multiset to a Subset of Variables\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition restrict_to_indices :: "'c monomial \<Rightarrow> 'c set \<Rightarrow> 'c monomial" where
"restrict_to_indices m S = filter_mset (\<lambda>i. i \<in> S) m"

lemma restrict_to_indicesE:
  assumes "i \<in># restrict_to_indices m S"
  shows "i \<in> S"
  using assms
  unfolding restrict_to_indices_def
  by simp

lemma restrict_to_indicesI[simp]:
  assumes "i \<in># m"
  assumes "i \<in> S"
  shows "i \<in># restrict_to_indices m S"
  using assms
  unfolding restrict_to_indices_def
  by simp

lemma restrict_to_indices_not_in[simp]:
  assumes "i \<in># m"
  assumes "i \<notin> S"
  shows "i \<notin># restrict_to_indices m S"
  using assms
  unfolding restrict_to_indices_def
  by (meson count_eq_zero_iff count_filter_mset)

lemma restrict_to_indices_submultiset[simp]:
"restrict_to_indices m S \<subseteq># m"
  unfolding restrict_to_indices_def
  using multiset_filter_subset
  by blast

lemma restrict_to_indices_add_element:
"restrict_to_indices (add_mset x m) S = (if x \<in> S then (add_mset x (restrict_to_indices m S) )
                                            else (restrict_to_indices m S) )"
  unfolding restrict_to_indices_def
  by (metis filter_mset_add_mset)

lemma restrict_to_indices_count[simp]:
"count (restrict_to_indices m S) i = (if (i \<in> S) then (count m i) else 0)"
  unfolding restrict_to_indices_def
  by (metis count_filter_mset)

lemma restrict_to_indices_subset:
"restrict_to_indices m S = restrict_to_indices m (set_mset m \<inter> S)"
proof(induction m)
  case empty
  then show ?case unfolding restrict_to_indices_def
    by (metis filter_empty_mset)
next
  case (add x m)
  assume IH: "restrict_to_indices m S = restrict_to_indices m (set_mset m \<inter> S)"
  show "restrict_to_indices (add_mset x m) S = restrict_to_indices (add_mset x m) (set_mset (add_mset x m) \<inter> S)"
  proof-
    have "\<And>i. count (restrict_to_indices (add_mset x m) S) i  =
              count (restrict_to_indices (add_mset x m) (set_mset (add_mset x m) \<inter> S)) i  "
    proof-
      fix i
      show "count (restrict_to_indices (add_mset x m) S) i  = count (restrict_to_indices (add_mset x m) (set_mset (add_mset x m) \<inter> S)) i"
        apply(cases "i \<in> S")
        using restrict_to_indices_count
        apply (metis IntI count_inI)
        by (metis restrict_to_indices_count Int_iff)
    qed
    then show ?thesis
      using multiset_eq_iff by blast
  qed
qed

text\<open>\texttt{Restrict\_to\_indices} only depends on the intersection
     of the index set with the set of indices in m:\<close>

lemma restrict_to_indices_subset':
  assumes "(set_mset m) \<inter> S = (set_mset m) \<inter> S'"
  shows "restrict_to_indices m S = restrict_to_indices m S'"
  by (metis restrict_to_indices_subset assms)

lemma mset_add_plus:
  assumes "m = n + k"
  shows "add_mset x m = (add_mset x n) + k"
  using assms
  by simp

text\<open>Restricting to \<open>S\<close> and the complement of \<open>S\<close> partitions \<open>m\<close>:\<close>

lemma restrict_to_indices_decomp:
  "m = (restrict_to_indices m S) + (restrict_to_indices m ((set_mset m) - S))"
  apply(induction m)
  apply (metis add.right_neutral empty_Diff restrict_to_indices_submultiset set_mset_empty subset_mset.le_zero_eq)
proof-
  fix x
  fix m
  assume A: "m = restrict_to_indices m S + restrict_to_indices m (set_mset m - S)"
  show "add_mset x m = restrict_to_indices (add_mset x m) S + restrict_to_indices (add_mset x m) (set_mset (add_mset x m) - S)"
  proof(cases "x \<in> S")
    case True
    then have T0: "restrict_to_indices (add_mset x m) S = (add_mset x (restrict_to_indices m S) ) "
      by (simp add: True restrict_to_indices_add_element)
    have T1: "restrict_to_indices (add_mset x m) (set_mset (add_mset x m) - S) =
            restrict_to_indices m (set_mset (add_mset x m) - S)"
      using True by (metis DiffD2 restrict_to_indices_add_element)
    have T2: "restrict_to_indices (add_mset x m) S +  restrict_to_indices (add_mset x m) (set_mset (add_mset x m) - S)
            = (add_mset x (restrict_to_indices m S) )  + restrict_to_indices m (set_mset (add_mset x m) - S)"
      using T0 T1
      by presburger
    have T3: " add_mset x m = add_mset x (restrict_to_indices m S) + restrict_to_indices m (set_mset m - S)"
      using T2 A using mset_add_plus[of m "restrict_to_indices m S" " restrict_to_indices m (set_mset m - S)" x]
      by blast
    have T4: "set_mset m \<inter> (set_mset (add_mset x m) - S) = set_mset m \<inter> (set_mset m - S)"
    proof
      show "set_mset m \<inter> (set_mset (add_mset x m) - S) \<subseteq> set_mset m \<inter> (set_mset m - S)"
        by blast
      show "set_mset m \<inter> (set_mset m - S) \<subseteq> set_mset m \<inter> (set_mset (add_mset x m) - S)"
        by (simp add: True)
    qed
    have T5: "restrict_to_indices m (set_mset (add_mset x m) - S) = restrict_to_indices m (set_mset m - S)"
      using T4 restrict_to_indices_subset'[of m "(set_mset (add_mset x m) - S)" " (set_mset m - S)" ]
      by blast
    then show ?thesis using T4
      by (metis T0 T1 T3)
  next
    case False
    then have F0: "restrict_to_indices (add_mset x m) S = (restrict_to_indices m S) "
      by (simp add: False restrict_to_indices_add_element)
    have F1: "restrict_to_indices (add_mset x m) (set_mset (add_mset x m) - S) =
            (add_mset x (restrict_to_indices m (set_mset (add_mset x m) - S)))"
      using False
      by (meson DiffI restrict_to_indices_add_element union_single_eq_member)

    have F2: "restrict_to_indices (add_mset x m) S +  restrict_to_indices (add_mset x m) (set_mset (add_mset x m) - S)
            = (restrict_to_indices m S) + (add_mset x (restrict_to_indices m (set_mset (add_mset x m) - S)))"
      using F0 F1
      by presburger
    have F3: " add_mset x m =  (restrict_to_indices m S) +  (add_mset x (restrict_to_indices m (set_mset m - S)))"
      using F2 A  mset_add_plus[of m "restrict_to_indices m (set_mset m - S)" "restrict_to_indices m S" x]
      by (metis union_mset_add_mset_right)
    have F4: " add_mset x m =  restrict_to_indices (add_mset x m) S+  (add_mset x (restrict_to_indices m (set_mset m - S)))"
      using F0 F3 by auto
    have F5: "add_mset x (restrict_to_indices m (set_mset m - S)) = restrict_to_indices (add_mset x m) (set_mset (add_mset x m) - S) "
    proof(cases "x \<in> set_mset m")
      case True
      then show ?thesis
        by (metis F1 add_mset_remove_trivial more_than_one_mset_mset_diff)
    next
      case F: False
      have "set_mset m \<inter> (set_mset (add_mset x m) - S) = set_mset m \<inter>(set_mset m - S)"
      proof
        show "set_mset m \<inter> (set_mset (add_mset x m) - S) \<subseteq> set_mset m \<inter> (set_mset m - S)"
          using F False
          by blast
        show "set_mset m \<inter> (set_mset m - S) \<subseteq> set_mset m \<inter> (set_mset (add_mset x m) - S)"
          using F False
          by (metis Diff_mono mset_add_plus Int_mono add_cancel_right_left
              set_eq_subset subsetI subset_iff union_commute union_iff)
      qed
      then show ?thesis
        by (metis F1 restrict_to_indices_subset')
    qed
    then show ?thesis
      using False F4
      by presburger
  qed
qed

definition remove_indices :: "'c monomial \<Rightarrow> 'c set \<Rightarrow> 'c monomial" where
"remove_indices m S = (restrict_to_indices m (set_mset m - S))"

lemma remove_indices_decomp:
"m = (restrict_to_indices m S) + (remove_indices m S)"
  unfolding remove_indices_def
  using restrict_to_indices_decomp
  by blast

lemma remove_indices_indices[simp]:
  assumes "set_mset m \<subseteq> I"
  shows "set_mset (remove_indices m S) \<subseteq> I - S"
  unfolding remove_indices_def using assms
  by (meson Diff_iff restrict_to_indicesE subsetD subsetI)

subsubsection\<open>Total evaluation of a monomial\<close>

text\<open>
  We define total evaluation of a monomial first, and then define the partial evaluation of a
  monomial in terms of this.
\<close>

abbreviation(input) closed_fun where
"closed_fun R g \<equiv> g \<in> UNIV \<rightarrow> carrier R"

definition monom_eval :: "('a, 'b) ring_scheme \<Rightarrow> 'c monomial \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'a"  where
"monom_eval R (m:: 'c monomial) g = fold_mset (\<lambda> x . \<lambda> y. if y \<in> carrier R then (g x) \<otimes>\<^bsub>R\<^esub> y else \<zero>\<^bsub>R\<^esub>) \<one>\<^bsub>R\<^esub> m"

context cring
begin

lemma closed_fun_simp:
  assumes "closed_fun R g"
  shows "g n \<in> carrier R"
  using assms
  by blast

lemma closed_funI:
  assumes "\<And>x. g x \<in> carrier R"
  shows "closed_fun R g"
  by (meson Pi_I assms)


text\<open>The following are necessary technical lemmas to prove properties of about folds over multisets:\<close>

lemma monom_eval_comp_fun:
  fixes g:: "'c \<Rightarrow> 'a"
  assumes "closed_fun R g"
  shows "comp_fun_commute (\<lambda> x . \<lambda>y. if y \<in> carrier R then  (g x) \<otimes> y else \<zero>)"
  unfolding comp_fun_commute_def
proof-
  have "\<And> x y. (\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>) \<circ> (\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>) =
          (\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>) \<circ> (\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>)"
  proof
    fix x y a
    show "((\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>) \<circ> (\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>)) a =
       ((\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>) \<circ> (\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>)) a"
    proof(cases "a \<in> carrier R")
      case True
      then show ?thesis
      proof-
        have LHS: "((\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>) \<circ> (\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>)) a =
                    ((\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>)  (g x \<otimes> a))"
          using True assms(1)  m_closed m_lcomm
          unfolding o_def
          by presburger

      then have LHS': "((\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>) \<circ> (\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>)) a =   g y \<otimes> (g x \<otimes> a) "
        using True assms m_closed
        by (meson PiE UNIV_I)
      then show ?thesis
        unfolding o_def
        using True assms m_closed m_lcomm
        by (smt PiE UNIV_I)
      qed
    next
      case False
      then show ?thesis
        unfolding o_def
        using assms r_null closed_fun_simp
        by smt
    qed
  qed
  then show " \<forall>y x. (\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>) \<circ> (\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>) =
          (\<lambda>y. if y \<in> carrier R then g x \<otimes> y else \<zero>) \<circ> (\<lambda>ya. if ya \<in> carrier R then g y \<otimes> ya else \<zero>)"
    by blast
qed

lemma monom_eval_car:
  assumes "closed_fun R g"
  shows "monom_eval R (m:: 'c monomial) g \<in> carrier R"
proof(induction m)
case empty
  then show ?case
    unfolding monom_eval_def
    by (metis fold_mset_empty one_closed)
next
  case (add x m)
  fix x m
  assume A: "monom_eval R m g \<in> carrier R"
  obtain f where f_def: "f = (\<lambda> x . \<lambda>y. if y \<in> carrier R then (g x) \<otimes> y else \<zero>)"
    by blast
  have 0: "comp_fun_commute f"
    using assms monom_eval_comp_fun[of g] f_def
    by blast
  have 1: "\<And>m. monom_eval R m g = fold_mset f \<one> m"
    using f_def monom_eval_def
    by blast
  have 2: "monom_eval R (add_mset x m) g = fold_mset f \<one> (add_mset x m)"
    using 1 by blast
  have 3: "g x \<in> carrier R"
    using assms  by blast
  then show "monom_eval R (add_mset x m) g \<in> carrier R"
    using assms 0 1 2 3
    by (metis A comp_fun_commute.fold_mset_add_mset f_def m_closed)
qed

text\<open>Formula for recursive (total) evaluation of a monomial:\<close>
lemma monom_eval_add:
  assumes "closed_fun R g"
  shows "monom_eval R (add_mset x M) g = (g x) \<otimes> (monom_eval R M g)"
proof-
  obtain f where f_def: "f = (\<lambda> x . \<lambda>y. if y \<in> carrier R then (g x) \<otimes> y else \<zero>)"
    by blast
  have 0: "comp_fun_commute f"
    using assms monom_eval_comp_fun f_def
    by blast
  have 1: "\<And>m. monom_eval R m g = fold_mset f \<one> m"
    using f_def monom_eval_def
    by blast
  have 2: "monom_eval R (add_mset x M) g = fold_mset f \<one> (add_mset x M)"
    using 1 by blast
  have 3: "g x \<in> carrier R"
    using assms  by blast
  have 4: "(g x) \<otimes> (monom_eval R M g) = f x (monom_eval R M g)"
    using f_def 3
    by (meson assms monom_eval_car)
  then show ?thesis
    by (metis "0" "1" comp_fun_commute.fold_mset_add_mset)
qed

end

text\<open>
  This function maps a polynomial $P$ to the set of monomials in $P$ which, after evaluating all
  variables in the set $S$ to values in the ring $R$, reduce to the monomial $n$.
\<close>

definition monomials_reducing_to ::
"('a,'b) ring_scheme \<Rightarrow> 'c monomial \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow> 'c set \<Rightarrow> ('c monomial) set" where
"monomials_reducing_to R n P S = {m \<in> monomials_of R P. remove_indices m S = n}"

lemma monomials_reducing_to_subset[simp]:
 "monomials_reducing_to R n P s \<subseteq> monomials_of R P"
  unfolding monomials_reducing_to_def
  by blast

context cring
begin

lemma monomials_reducing_to_finite:
  assumes "P \<in> Pring_set R I"
  shows "finite (monomials_reducing_to R n P s)"
  by (meson assms monomials_finite monomials_reducing_to_subset rev_finite_subset)

lemma monomials_reducing_to_disjoint:
  assumes "n1 \<noteq> n2"
  shows "monomials_reducing_to R n1 P S \<inter> monomials_reducing_to R n2 P S = {}"
  unfolding monomials_reducing_to_def
  using assms
  by blast

lemma monomials_reducing_to_submset:
assumes "n \<subset># m"
shows "n \<notin> monomials_reducing_to R m P S"
proof(rule ccontr)
  assume C: "\<not> n \<notin> monomials_reducing_to R m P S "
  then have "n \<in>  monomials_reducing_to R m P S "
    by blast
  then have "remove_indices n S = m"
    unfolding monomials_reducing_to_def
    by blast
  then show False
    by (metis (full_types) remove_indices_def restrict_to_indices_submultiset assms subset_mset.less_asym' subset_mset.less_irrefl subset_mset_def)
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Partial Evaluation of a Polynomial\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  This function takes as input a set $S$ of variables, an evaluation function $g$, and a polynomial
  to evaluate $P$. The output is a polynomial which is the result of evaluating the variables from
  the set $S$ which occur in $P$, according to the evaluation function $g$.
\<close>

definition poly_eval ::
  "('a,'b) ring_scheme \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> ('a, 'c) mvar_poly"where
"poly_eval R S g P m = (finsum R (\<lambda>n. monom_eval R (restrict_to_indices n S) g  \<otimes>\<^bsub>R\<^esub> (P n)) (monomials_reducing_to R m P S))"

context cring
begin

lemma finsum_singleton:
  assumes "S = {s}"
  assumes "f s \<in> carrier R"
  shows "finsum R f S = f s"
proof-
  have "finsum R f S = finsum R f (insert s {})"
    using assms(1)
    by blast
  then show ?thesis using finsum_insert[of "{}" s f] assms
    by (metis Pi_I empty_iff finite.emptyI finsum_empty r_zero)
qed

lemma poly_eval_constant:
  assumes "k \<in> carrier R"
  shows "poly_eval R S g (indexed_const k) = (indexed_const k)"
proof
  have S: "monomials_of R (indexed_const k) \<subseteq> {{#}}"
    unfolding indexed_const_def monomials_of_def
    by (metis (mono_tags, lifting) mem_Collect_eq singletonI subset_iff)
  fix x
  show "poly_eval R S g (indexed_const k) x = indexed_const k x "
  proof(cases "x = {#}")
    case True
    have "(monomials_reducing_to R x (indexed_const k) S) \<subseteq> {{#}}"
      using S monomials_reducing_to_subset
      by blast
    then show ?thesis
    proof(cases "k = \<zero>")
      case True
      then have "(monomials_reducing_to R x (indexed_const k) S) = {}"
        by (metis S \<open>monomials_reducing_to R x (indexed_const k) S \<subseteq> {{#}}\<close>
            monomials_reducing_to_subset monoms_of_const subset_antisym subset_singletonD)
      then show ?thesis
        unfolding poly_eval_def
        by (metis True finsum_empty indexed_const_def)
    next
      case False
      then have "monomials_of R (indexed_const k) = {{#}}"
        by (meson monoms_of_const)
      have "remove_indices {#} S = {#}"
        using remove_indices_decomp by blast
      then have "{#} \<in> monomials_reducing_to R x (indexed_const k) S"
        using True False unfolding monomials_reducing_to_def
              \<open>monomials_of R (indexed_const k) = {{#}}\<close>
        by blast
      then have 0: "monomials_reducing_to R x (indexed_const k) S = {{#}}"
        using \<open>monomials_reducing_to R x (indexed_const k) S \<subseteq> {{#}}\<close>
        by blast
      have 1: "restrict_to_indices {#} S = {#}"
        using restrict_to_indices_submultiset remove_indices_decomp by blast
      have 2: "monom_eval R (restrict_to_indices {#} S) g = \<one>"
        unfolding monom_eval_def
        using 1
        by (metis fold_mset_empty)
      have 3: "poly_eval R S g (indexed_const k)  x =
                (\<Oplus>n\<in>{{#}}. monom_eval R (restrict_to_indices n S) g \<otimes> indexed_const k n)"
        unfolding poly_eval_def
        using 0
        by presburger
      have 4: "(\<Oplus>n\<in>{{#}}. monom_eval R (restrict_to_indices n S) g \<otimes> indexed_const k n) = monom_eval R (restrict_to_indices {#} S) g \<otimes> indexed_const k {#}"
        using finsum_singleton[of "{{#}}" "{#}" "\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> indexed_const k n" ]
        by (metis "2" assms indexed_const_def l_one)
      then show ?thesis unfolding poly_eval_def
        using 0 1 2
        by (metis True assms indexed_const_def l_one)
    qed
  next
    case False
    then have F0: "(indexed_const k) x = \<zero>"
      by (meson indexed_const_def)
    have "(monomials_reducing_to R x (indexed_const k) S) = {}"
      unfolding monomials_reducing_to_def
    proof(rule ccontr)
      assume A: "{m \<in> monomials_of R (indexed_const k). remove_indices m S = x} \<noteq> {}"
      then obtain m where m_def: "m \<in> monomials_of R (indexed_const k) \<and> remove_indices m S = x"
        by blast
        then show False using A F0
          by (metis False S empty_eq_union empty_iff
              remove_indices_decomp singletonD subset_singletonD)
    qed
    then show ?thesis
      unfolding poly_eval_def
      by (metis False finsum_empty indexed_const_def)
  qed
qed

lemma finsum_partition:
  assumes "finite S"
  assumes "f \<in> S \<rightarrow> carrier R"
  assumes "T \<subseteq> S"
  shows "finsum  R f S  = finsum R f T  \<oplus> finsum  R f (S - T) "
proof-
  have "\<And>U. finite U \<Longrightarrow> U \<subseteq> S \<longrightarrow> finsum  R f S  = finsum R f U  \<oplus> finsum  R f (S - U) "
  proof-
    fix U
    show "finite U \<Longrightarrow> U \<subseteq> S \<longrightarrow> finsum R f S = finsum R f U \<oplus> finsum R f (S - U) "
    apply(erule finite.induct)
       apply (metis Diff_empty assms(2) finsum_closed finsum_empty l_zero)
    proof
      fix A :: "'c set" fix a
      assume A0: "finite A"
      show "A \<subseteq> S \<longrightarrow> finsum R f S = finsum R f A \<oplus> finsum R f (S - A) \<Longrightarrow> insert a A \<subseteq> S \<Longrightarrow> finsum R f S = finsum R f (insert a A) \<oplus> finsum R f (S - insert a A)"

      proof-
        assume A1: "A \<subseteq> S \<longrightarrow> finsum R f S = finsum R f A \<oplus> finsum R f (S - A)"
        assume A2: "insert a A \<subseteq> S"
        show "finsum R f S = finsum R f (insert a A) \<oplus> finsum R f (S - insert a A)"
          apply(cases "a \<in> A")
           apply (metis A1 A2 insert_absorb)
        proof-
          assume A3: "a \<notin> A"
          have A4: "f a \<in> carrier R"
            by (metis A2 Pi_iff assms(2) insert_subset)
          have A5: " finsum R f (insert a A) = f a \<oplus> finsum R f A"

            using A0 A1 A2 finsum_insert[of A a f] assms  A3
            by blast
          have A6: "a \<in> S"
            using A2 by blast
          have A7: "finsum R f S \<in> carrier R"
            using assms(2) finsum_closed by blast
          have A8: " finsum R f (S - A)\<in> carrier R"
            using Diff_subset[of S A] Pi_iff assms(2) finsum_closed[of f] subsetD[of _ S ]
            by (meson Pi_anti_mono in_mono)
          have A9: "finsum R f A \<in> carrier R"
            by (meson A2 Pi_anti_mono assms(2) finsum_closed insert_subset subsetD)
          have A10: "finsum R f A =  finsum R f S \<ominus> finsum R f (S - A)"
            using A7 A8 A9
            by (metis A1 A2 add.inv_solve_right' insert_subset minus_eq)
          have A11: " finsum R f (insert a A) = f a \<oplus> (finsum R f S \<ominus> finsum R f (S - A))"
            using A5 A6 A1 A2 assms  A10
            by presburger
          then have A12: " finsum R f (insert a A) =finsum R f S \<oplus>( f a  \<ominus> finsum R f (S - A))"
            using A4 A7 A8 add.inv_closed add.m_lcomm minus_eq by presburger
          have A13: "finsum R f (insert a A) \<in> carrier R"
            using A4 A5 A9 add.m_closed
            by presburger
          have A14: " finsum R f (S - insert a A) \<in> carrier R"
            by (meson Diff_subset Pi_anti_mono assms(2) finsum_closed in_mono)
          have A15: "finsum R f S = finsum R f (insert a A) \<ominus> ( f a  \<ominus> finsum R f (S - A)) "
            by (metis A12 A13 A4 A7 A8 add.inv_solve_right' minus_closed minus_eq)
          have A16: "finsum R f S = finsum R f (insert a A) \<oplus> finsum R f (S - A) \<ominus> f a"
            using  A1 A2 A4 A5 A8 A9 add.inv_closed add.m_assoc add.m_comm insert_subset minus_closed minus_eq r_neg1
            unfolding a_minus_def
            by (metis add.m_closed)
          have A16: "finsum R f S = finsum R f (insert a A) \<oplus> (finsum R f (S - A) \<ominus> f a)"
            unfolding a_minus_def
            using A13 A16 A4 A8 add.inv_closed add.m_assoc minus_eq by presburger
          have A17: "(finsum R f (S - A) \<ominus> f a) = finsum R f (S - insert a A) "
          proof-
            have A170: "(S - A) = insert a (S - insert a A)"
              using A3 A6 by blast
            have A171: "a \<notin> S - insert a A"
              by blast
            then have "finsum R f (S - A)  =(f a) \<oplus> finsum R f (S - insert a A) "
              using A170 finsum_insert[of "(S - insert a A)" a f]
              by (metis A4 Diff_subset Pi_anti_mono assms(1) assms(2)
                  rev_finite_subset subsetD )
            then show ?thesis
              by (metis A1 A13 A14 A16 A2 A4 A5 A8 A9 add.l_cancel
                  add.m_assoc add.m_comm insert_subset minus_closed)
          qed
          then show "finsum R f S = finsum R f (insert a A) \<oplus> finsum R f (S - insert a A) "
            using A16
            by presburger
        qed
      qed
    qed
  qed
  then show ?thesis
    by (meson assms(1) assms(3) rev_finite_subset)
qed

lemma finsum_eq_parition:
  assumes "finite S"
  assumes "f \<in> S \<rightarrow> carrier R"
  assumes "T \<subseteq> S"
  assumes "\<And>x. x \<in> S - T \<Longrightarrow> f x = \<zero>"
  shows "finsum  R f S  = finsum R f T"
  using assms
  by (metis add.finprod_mono_neutral_cong_right)

lemma poly_eval_scalar_mult:
  assumes "k \<in> carrier R"
  assumes "closed_fun R g"
  assumes "P \<in> Pring_set R I"
  shows "poly_eval R  S g (poly_scalar_mult R k P)=
         (poly_scalar_mult R k (poly_eval R S g P))"
proof
  fix m
  show "poly_eval R S g (poly_scalar_mult R k P) m = poly_scalar_mult R k (poly_eval R S g  P) m"
    unfolding poly_eval_def poly_scalar_mult_def
  proof-
    have 0: "(\<Oplus>n\<in>monomials_reducing_to R m P S. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n)) =
              (\<Oplus>n\<in>monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n)) "
    proof-
      have 00: "monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S \<subseteq> monomials_reducing_to R m P S"
      proof
        fix x show " x \<in> monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S \<Longrightarrow> x \<in> monomials_reducing_to R m P S"
        unfolding monomials_reducing_to_def
        using assms  assms(1) monomials_ofE complement_of_monomials_of  r_null[of k]
        by (metis (no_types, lifting) mem_Collect_eq)
       have 01: "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n)) \<in> monomials_reducing_to R m P S \<rightarrow> carrier R"
        by (smt Pi_I Pring_cfs_closed assms(1) assms(2) assms(3) closed_fun_simp m_closed monom_eval_car)
       have 02: "finite (monomials_reducing_to R m P S)"
        using assms(3) monomials_reducing_to_finite
        by blast
       have 03: "  (\<And>x. x \<in> monomials_reducing_to R m P S - monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S \<Longrightarrow>
          monom_eval R (restrict_to_indices x S) g \<otimes> (k \<otimes> P x) = \<zero>)"
       proof-
        fix x
        assume A: "x \<in> monomials_reducing_to R m P S - monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S "
        have "x \<notin> monomials_of R ((\<lambda>m. k \<otimes> P m))"
        proof
          assume "x \<in> monomials_of R (\<lambda>m. k \<otimes> P m)"
          then have "x \<in>  monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S"
            using A
            unfolding monomials_reducing_to_def
            by blast
          then show False
            using A by blast
        qed
        then show "monom_eval R (restrict_to_indices x S) g \<otimes> (k \<otimes> P x) = \<zero>"
          by (metis assms(2) complement_of_monomials_of monom_eval_car r_null)
       qed
      qed
      have 01: " (\<And>x. x \<in> monomials_reducing_to R m P S - monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S \<Longrightarrow> monom_eval R (restrict_to_indices x S) g \<otimes> (k \<otimes> P x) = \<zero>)"
      proof- fix x assume A: "x \<in> monomials_reducing_to R m P S - monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S"
        hence "x \<notin> monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S"
        by blast
         hence "(k \<otimes> P x) = \<zero>" unfolding monomials_reducing_to_def
        by (metis (no_types, lifting) A DiffD1 complement_of_monomials_of mem_Collect_eq monomials_reducing_to_def)
        thus "monom_eval R (restrict_to_indices x S) g \<otimes> (k \<otimes> P x) = \<zero>"
        using monom_eval_car[of g]  assms(2) r_null by presburger
      qed
      have 02: "finite (monomials_reducing_to R m P S)"
        using assms(3) monomials_reducing_to_finite by blast
      have 04: "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n)) \<in> monomials_reducing_to R m P S \<rightarrow> carrier R"
        by (smt Pi_I assms(1) assms(2) assms(3) closed_fun_simp cring.axioms(1) is_cring m_closed monom_eval_car ring.Pring_cfs_closed)
      show ?thesis
        using 00 01 02 04
            finsum_eq_parition[of "monomials_reducing_to R m P S"
                                "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n))"
                                "monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S"]
        by blast
    qed
    then have 1: " (\<Oplus>n\<in>monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n))
       = (\<Oplus>n\<in>monomials_reducing_to R m P S. k \<otimes> (monom_eval R (restrict_to_indices n S) g \<otimes> (P n)))      "
    proof-
      have "\<And>n. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n) = k \<otimes> (monom_eval R (restrict_to_indices n S) g \<otimes> (P n))"
        by (metis Pring_cfs_closed assms(1) assms(2) assms(3) m_lcomm monom_eval_car)
      then show ?thesis
        using 0
        by presburger
    qed
    show " (\<Oplus>n\<in>monomials_reducing_to R m (\<lambda>m. k \<otimes> P m) S. monom_eval R (restrict_to_indices n S) g \<otimes> (k \<otimes> P n))
       = k \<otimes>(\<Oplus>n\<in>monomials_reducing_to R m P S.  monom_eval R (restrict_to_indices n S) g \<otimes> (P n))      "
    proof-
      have "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> (P n)) \<in> (monomials_reducing_to R m P S) \<rightarrow> carrier R"
        by (meson Pi_I Pring_cfs_closed assms(2) assms(3) m_closed monom_eval_car)
      then have "k \<otimes> (\<Oplus>i\<in>monomials_reducing_to R m P S. monom_eval R (restrict_to_indices i S) g \<otimes> P i) =
      (\<Oplus>i\<in>monomials_reducing_to R m P S. k \<otimes> (monom_eval R (restrict_to_indices i S) g \<otimes> P i))"
        using finsum_rdistr[of "monomials_reducing_to R m P S"
                                  k
                                  "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> (P n))"]
              assms  monomials_reducing_to_finite by blast
      then show ?thesis
        using 1
        by presburger
    qed
  qed
qed

lemma poly_eval_monomial:
  assumes "closed_fun R g"
  assumes "\<one> \<noteq>\<zero>"
  shows "poly_eval R  S g (mset_to_IP R m)
           = poly_scalar_mult R (monom_eval R (restrict_to_indices m S) g)
                              (mset_to_IP R (remove_indices m S))"
proof
  have 0: "monomials_of R (mset_to_IP R m) = {m}"
    using assms  monomials_of_mset_to_IP
    by blast

  fix x
  show "poly_eval R  S g (mset_to_IP R m) x =
         poly_scalar_mult R (monom_eval R (restrict_to_indices m S) g)
                           (mset_to_IP R (remove_indices m S)) x "
  proof(cases "x = (remove_indices m S)")
    case True
    have "monomials_reducing_to R x (mset_to_IP R m) S = {m}"
      unfolding monomials_reducing_to_def
      using True 0
      by auto
    then have "poly_eval R  S g (mset_to_IP R m) x = monom_eval R (restrict_to_indices m S) g \<otimes> (mset_to_IP R m m)"
      unfolding poly_eval_def
      by (metis (mono_tags, lifting) assms(1) finsum_singleton monom_eval_car mset_to_IP_simp r_one)
    then show ?thesis
      by (metis True mset_to_IP_simp poly_scalar_mult_def)
  next
    case False
    then have "monomials_reducing_to R x (mset_to_IP R m) S = {}"
      unfolding monomials_reducing_to_def
      using 0
      by auto
    then have "poly_eval R S g (mset_to_IP R m) x = \<zero>"
      unfolding poly_eval_def
      by (metis finsum_empty)
    then show ?thesis
      using False
      by (metis assms(1) monom_eval_car mset_to_IP_simp' poly_scalar_mult_def r_null)
  qed
qed


lemma(in cring) poly_eval_monomial_closed:
  assumes "closed_fun R g"
  assumes "\<one> \<noteq>\<zero>"
  assumes "set_mset m \<subseteq> I"
  shows "poly_eval R S g (mset_to_IP R m) \<in> Pring_set R (I - S)"
proof-
  have "(mset_to_IP R (remove_indices m S)) \<in> Pring_set R (I - S)"
    using assms  mset_to_IP_closed[of "(remove_indices m S)" "I - S"]
    by (metis remove_indices_indices)
  then show ?thesis
    using assms poly_eval_monomial[of g S m  ]
          poly_scalar_mult_closed[of "(monom_eval R (restrict_to_indices m S) g)"
                                        "(mset_to_IP R (remove_indices m S))"]
    by (metis monom_eval_car)
qed

lemma poly_scalar_mult_iter:
  assumes "\<one> \<noteq>\<zero>"
  assumes "P \<in> Pring_set R I"
  assumes "k \<in> carrier R"
  assumes "n \<in> carrier R"
  shows "poly_scalar_mult R k (poly_scalar_mult R n P) = poly_scalar_mult R (k \<otimes> n) P"
  using assms
  unfolding poly_scalar_mult_def
  by (metis Pring_cfs_closed m_assoc)

lemma poly_scalar_mult_comm:
  assumes "\<one> \<noteq>\<zero>"
  assumes "P \<in> Pring_set R I"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "poly_scalar_mult R a (poly_scalar_mult R b P) = poly_scalar_mult R b (poly_scalar_mult R a P)"
  using assms  poly_scalar_mult_iter m_comm[of a b]
  by metis

lemma poly_eval_monomial_term:
  assumes "closed_fun R g"
  assumes "\<one> \<noteq>\<zero>"
  assumes "set_mset m \<subseteq> I"
  assumes "k \<in> carrier R"
  shows "poly_eval R  S g (poly_scalar_mult R k (mset_to_IP R m)) = poly_scalar_mult R (k\<otimes>(monom_eval R (restrict_to_indices m S) g))
                              (mset_to_IP R (remove_indices m S))"
proof-
  have 0: "poly_eval R  S g (poly_scalar_mult R k (mset_to_IP R m)) =
          poly_scalar_mult R k (poly_eval R S g (mset_to_IP R m))"
    using assms poly_eval_scalar_mult[of k g "mset_to_IP R m" I S] mset_to_IP_closed
    by blast
  have 1: "poly_eval R  S g (poly_scalar_mult R k (mset_to_IP R m)) =
           poly_scalar_mult R k (poly_scalar_mult R (monom_eval R (restrict_to_indices m S) g)
                              (mset_to_IP R (remove_indices m S))) "
    using 0 assms
    by (metis poly_eval_monomial)
  have 2: "mset_to_IP R (remove_indices m S) \<in> Pring_set R I"
    using assms mset_to_IP_closed
    by (metis Diff_subset remove_indices_def restrict_to_indicesE subset_iff)
  have 3: "monom_eval R (restrict_to_indices m S) g \<in> carrier R"
    using assms monom_eval_car by blast
  show ?thesis
    using 1 2 3 assms   poly_scalar_mult_iter[of  "mset_to_IP R (remove_indices m S)" I k "(monom_eval R (restrict_to_indices m S) g)"]
  by presburger
qed

lemma poly_eval_monomial_term_closed:
  assumes "closed_fun R g"
  assumes "\<one> \<noteq>\<zero>"
  assumes "set_mset m \<subseteq> I"
  assumes "k \<in> carrier R"
  shows "poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m)) \<in> Pring_set R (I - S)"
proof-
  have "(mset_to_IP R (remove_indices m S)) \<in> Pring_set R (I - S)"
    using assms
    by (meson remove_indices_indices mset_to_IP_closed)
  then show ?thesis
    using assms poly_eval_monomial_term remove_indices_indices[of m I S]
    by (metis cring.cring_simprules(5) cring.monom_eval_car is_cring poly_scalar_mult_closed)
qed

lemma finsum_split:
  assumes "finite S"
  assumes "f \<in> S \<rightarrow> carrier R"
  assumes "g \<in> S \<rightarrow> carrier R"
  assumes "k \<in> carrier  R"
  assumes "c \<in> S"
  assumes "\<And>s. s \<in> S \<and> s \<noteq> c \<Longrightarrow> f s = g s"
  assumes "g c = f c \<oplus> k"
  shows "finsum R g S = k \<oplus> finsum R f S"
proof-
  have 0: "finsum R f S = f c \<oplus> finsum R f (S - {c})"
  proof-
    have "f \<in> S - {c} \<rightarrow> carrier R"
      by (metis Pi_split_insert_domain assms(2) assms(5) insert_Diff)
    then show ?thesis
    using assms finsum_insert[of "S - {c}" c f]
    by (metis DiffD2 Pi_iff finite_Diff insert_Diff singletonI)
  qed
  have 1: "finsum R g S = g c \<oplus> finsum R g (S - {c})"
  proof-
    have "g \<in> S - {c} \<rightarrow> carrier R"
      by (metis Pi_split_insert_domain  assms(3) assms(5) insert_Diff)
    then show ?thesis
    using assms finsum_insert[of "S - {c}" c g]
    by (metis DiffD2 Pi_iff finite_Diff insert_Diff singletonI)
  qed
  have "finsum R f (S - {c}) = finsum R g (S - {c})"
    using assms Diff_iff Pi_split_insert_domain finsum_cong'[of "S- {c}" "S - {c}" g f]
      insert_Diff singletonI
    by blast
  then have "finsum R g S = f c \<oplus> k \<oplus> finsum R g (S - {c})"
    using assms  \<open>finsum R g S = g c \<oplus> finsum R g (S - {c})\<close>
    by presburger
  then have 1: "finsum R g S = f c \<oplus> k \<oplus> finsum R f (S - {c})"
    using \<open>finsum R f (S - {c}) = finsum R g (S - {c})\<close> by presburger
  have "finsum R g S = k \<oplus> ( f c \<oplus> finsum R f (S - {c}))"
  proof-
    have "f c \<in> carrier R"
      by (metis PiE assms(2) assms(5))
    have "finsum R f (S - {c}) \<in> carrier R"
      by (metis Pi_split_insert_domain assms(2) assms(5) finsum_closed insert_Diff)
    then show ?thesis using assms(4) 1
      using \<open>f c \<in> carrier R\<close> add.m_assoc add.m_lcomm
      by presburger
  qed
  then show ?thesis
    using "0"
    by presburger
qed

lemma poly_monom_induction:
assumes "P (indexed_const \<zero>)"
assumes "\<And>m k. set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> P (poly_scalar_mult R k (mset_to_IP R m))"
assumes "\<And>Q m k. Q \<in> Pring_set R I \<and> (P Q) \<and> set_mset m \<subseteq> I \<and> k \<in> carrier R\<Longrightarrow> P (Q \<Oplus> (poly_scalar_mult R k (mset_to_IP R m)))"
shows "\<And>Q. Q \<in> Pring_set R I \<Longrightarrow> P Q"
proof-
  have 0: "\<And>Ms. finite Ms \<Longrightarrow> (\<forall> Q \<in> Pring_set R I. monomials_of R Q = Ms \<longrightarrow> P Q)"
  proof-
    fix Ms
    show " finite Ms \<Longrightarrow> (\<forall> Q \<in> Pring_set R I. monomials_of R Q = Ms \<longrightarrow> P Q)"
    proof(erule finite.induct)
      show "\<forall>Q\<in>Pring_set R I. monomials_of R Q = {} \<longrightarrow> P Q"
      proof
        fix Q
        assume "Q \<in> Pring_set R I"
        show "monomials_of R Q = {} \<longrightarrow> P Q "
          using assms
          by (metis \<open>Q \<in> Pring_set R I\<close> card_0_eq monomials_finite monomials_of_card_zero)
      qed
      show "\<And>A a. finite A \<Longrightarrow> \<forall>Q\<in>Pring_set R I. monomials_of R Q = A \<longrightarrow> P Q \<Longrightarrow>
                    \<forall>Q\<in>Pring_set R I. monomials_of R Q = insert a A \<longrightarrow> P Q"
      proof
        fix A :: "'c monomial set" fix  a fix  Q
        assume A0: "finite A"
        assume A1: "\<forall>Q\<in>Pring_set R I. monomials_of R Q = A \<longrightarrow> P Q"
        assume A2: " Q \<in> Pring_set R I "
        show "monomials_of R Q = insert a A \<longrightarrow> P Q"
        proof
          assume A3: "monomials_of R Q = insert a A"
          show "P Q"
            apply(cases "a \<in> A")
             apply (metis A1 A2 A3 insert_absorb)
          proof-
            assume A4: "a \<notin> A"
            show "P Q"
            proof-
              have A5: "set_mset a \<subseteq> I"
                by (metis A2 A3 insert_iff mset_to_IP_indices)
              have A6: "set_mset a \<subseteq> I \<and> Q a \<in> carrier R"
                using A2 A5 Pring_cfs_closed by blast
              obtain Q' where Q'_def: "Q' = remove_monom R a Q"
                by simp
              then have "Q = Q' \<Oplus> poly_scalar_mult R (Q a) (mset_to_IP R a)"
                using A2 cring.remove_monom_eq is_cring by blast
              then show ?thesis using A6 assms
                by (metis A1 A2 A3 A4 Diff_empty Diff_insert0 Q'_def insert_Diff1
                    remove_monom_closed remove_monom_monomials singletonI)
            qed
          qed
        qed
      qed
    qed
  qed
  show "\<And>Q. Q \<in> Pring_set R I \<Longrightarrow> P Q"
  proof-
    fix Q
    assume "Q \<in> Pring_set R I"
    show "P Q"
      using 0[of "monomials_of R Q"]  \<open>Q \<in> Pring_set R I\<close> monomials_finite
      by blast
  qed
qed

lemma Pring_car_induct:
  assumes "q \<in> carrier (Pring R I)"
  assumes "P \<zero>\<^bsub>Pring R I\<^esub>"
  assumes "\<And>m k. set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> P (k \<odot>\<^bsub>Pring R I\<^esub>(mset_to_IP R m))"
  assumes "\<And>Q m k. Q \<in> carrier (Pring R I) \<and> (P Q) \<and> set_mset m \<subseteq> I \<and> k \<in> carrier R\<Longrightarrow>
             P (Q \<Oplus> (k \<odot>\<^bsub>Pring R I\<^esub> (mset_to_IP R m)))"
  shows "P q"
  using poly_monom_induction[of P I q] assms Pring_smult[of I] Pring_car[of I] Pring_zero
  by metis

lemma poly_monom_induction2:
assumes "P (indexed_const \<zero>)"
assumes "\<And>m k. set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> P (poly_scalar_mult R k (mset_to_IP R m))"
assumes "\<And>Q m k. Q \<in> Pring_set R I \<and> (P Q) \<and> set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> P (Q \<Oplus> (poly_scalar_mult R k (mset_to_IP R m)))"
assumes "Q \<in>  Pring_set R I"
shows "P Q"
  using assms(1) assms(2) assms(3) assms(4) poly_monom_induction by blast

lemma poly_monom_induction3:
assumes "Q \<in>  Pring_set R I"
assumes "P (indexed_const \<zero>)"
assumes "\<And>m k. set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> P (poly_scalar_mult R k (mset_to_IP R m))"
assumes "\<And>p q. p \<in> Pring_set R I \<Longrightarrow> (P p) \<Longrightarrow> q \<in> Pring_set R I \<Longrightarrow> (P q) \<Longrightarrow>  P (p \<Oplus> q)"
shows "P Q"
  apply(rule poly_monom_induction2[of _  I])
  using assms(2) apply blast
  using assms(3) apply blast
  apply (meson assms(3) assms(4) mset_to_IP_closed poly_scalar_mult_closed)
  using assms(1) by blast

lemma Pring_car_induct':
assumes "Q \<in> carrier (Pring R I)"
assumes "P \<zero>\<^bsub>Pring R I\<^esub>"
assumes "\<And>m k. set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> P (k \<odot>\<^bsub>Pring R I\<^esub> mset_to_IP R m)"
assumes "\<And>p q. p \<in> carrier (Pring R I) \<Longrightarrow> (P p) \<Longrightarrow> q \<in> carrier (Pring R I) \<Longrightarrow> (P q) \<Longrightarrow>  P (p \<oplus>\<^bsub>Pring R I\<^esub> q)"
shows "P Q"
  using poly_monom_induction3[of Q I P] assms Pring_smult Pring_add Pring_zero Pring_car
  by metis

lemma poly_eval_mono:
  assumes "P \<in> Pring_set R I"
  assumes "closed_fun R g"
  assumes "finite F"
  assumes "monomials_reducing_to R m P S \<subseteq> F"
  assumes "\<And>n. n \<in> F \<Longrightarrow> remove_indices n S = m"
  shows "poly_eval R S g P m = (\<Oplus>n\<in> F. monom_eval R (restrict_to_indices n S) g \<otimes> P n)"
proof-
  have 0: "(\<Oplus>n\<in> F. monom_eval R (restrict_to_indices n S) g \<otimes> P n)=
          (\<Oplus>n\<in> F - (monomials_reducing_to R m P S). monom_eval R (restrict_to_indices n S) g \<otimes> P n) \<oplus> poly_eval R S g P m"
  proof-
    have 00: "  (\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> P n) \<in> F \<rightarrow> carrier R"
      by (meson Pi_I Pring_cfs_closed assms(1) assms(2) m_closed monom_eval_car)
    have 01: "monomials_reducing_to R m P S \<subseteq> F"
      by (simp add: assms(4))
    have 02: "(\<Oplus>n\<in>F. monom_eval R (restrict_to_indices n S) g \<otimes> P n) =
    (\<Oplus>n\<in>monomials_reducing_to R m P S. monom_eval R (restrict_to_indices n S) g \<otimes> P n) \<oplus>
    (\<Oplus>n\<in>F - monomials_reducing_to R m P S. monom_eval R (restrict_to_indices n S) g \<otimes> P n)"
      using "00" "01" assms(3) finsum_partition by blast
    have 03: " (\<Oplus>n\<in>F - monomials_reducing_to R m P S. monom_eval R (restrict_to_indices n S) g \<otimes> P n)\<in> carrier R"
      by (metis (mono_tags, lifting) "00" DiffD1 PiE Pi_I finsum_closed)
    have "    (\<Oplus>n\<in>monomials_reducing_to R m P S. monom_eval R (restrict_to_indices n S) g \<otimes> P n) \<in> carrier R"
    proof -
      have "(\<lambda>m. monom_eval R (restrict_to_indices m S) g \<otimes> P m) \<in> monomials_reducing_to R m P S \<rightarrow> carrier R"
        using "00" "01" by blast
      then show ?thesis
        using finsum_closed by blast
    qed
    then show ?thesis
      unfolding poly_eval_def
      using  00 01 02 03  add.m_comm
      by presburger
  qed
  have "(\<Oplus>n\<in> F - (monomials_reducing_to R m P S). monom_eval R (restrict_to_indices n S) g \<otimes> P n) = \<zero>"
  proof-
    have "\<And>n. n \<in> F - (monomials_reducing_to R m P S) \<Longrightarrow>  monom_eval R (restrict_to_indices n S) g \<otimes> P n = \<zero>"
    proof-
      fix n
      assume A: "n \<in>  F - (monomials_reducing_to R m P S)"
      have "n \<notin> monomials_of R P"
      proof
        assume "n \<in> monomials_of R P"
        then have "n \<in> (monomials_reducing_to R m P S)"
          unfolding monomials_reducing_to_def
          using assms(5) A
          by blast
        then show False using A by blast
      qed
      then show " monom_eval R (restrict_to_indices n S) g \<otimes> P n = \<zero>"
        by (metis assms(2) monom_eval_car complement_of_monomials_of r_null)
    qed
    then show ?thesis
      by (meson add.finprod_one_eqI)
  qed
  then have 1: "(\<Oplus>n\<in>F. monom_eval R (restrict_to_indices n S) g \<otimes> P n) =
    \<zero> \<oplus> poly_eval R S g P m"
    using 0  Pi_I Pring_cfs_closed add.r_cancel_one assms(1) assms(2)
    by presburger
  have " (\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> P n) \<in> monomials_reducing_to R m P S \<rightarrow> carrier R"
    by (meson Pi_I Pring_cfs_closed assms(1) assms(2) m_closed monom_eval_car)
  hence "poly_eval R S g P m \<in> carrier R"
    using assms
    unfolding poly_eval_def
    using finsum_closed[of "\<lambda> n. monom_eval R (restrict_to_indices n S) g \<otimes> P n"
                          "monomials_reducing_to R m P S"]
    by (meson Pi_I Pring_cfs_closed m_closed monom_eval_car)
  then have "(\<Oplus>n\<in>F. monom_eval R (restrict_to_indices n S) g \<otimes> P n) = poly_eval R S g P m"
    using "1" add.r_cancel_one zero_closed
    by presburger
  then show ?thesis
    by presburger
qed

lemma finsum_group:
  assumes "\<And>n. f n \<in> carrier R"
  assumes "\<And>n. g n \<in>  carrier R"
  shows "finite S \<Longrightarrow> finsum R f S \<oplus> finsum R g S = finsum R (\<lambda>n. f n \<oplus> g n) S "
  apply(erule finite.induct)
  apply (metis finsum_empty r_zero zero_closed)
proof-
  fix A :: "'c set "
  fix a
  assume A0: "finite A"
  assume A1: "finsum R f A \<oplus> finsum R g A = (\<Oplus>n\<in>A. f n \<oplus> g n)"
  show "finsum R f (insert a A) \<oplus> finsum R g (insert a A) = (\<Oplus>n\<in>insert a A. f n \<oplus> g n)"
  proof(cases "a \<in> A")
    case True
    then show ?thesis
      by (metis A1 insert_absorb)
  next
    case False
    have LHS: "finsum R f (insert a A) \<oplus> finsum R g (insert a A) =
                  (f a \<oplus> finsum R f A) \<oplus> (g a \<oplus> finsum R g A)"
      using assms  finsum_insert[of A a f] finsum_insert[of A a g]
      by (metis A0 False Pi_I)
    have F0: "(\<lambda>n. f n \<oplus> g n) \<in> A \<rightarrow> carrier R"
      using assms
      by blast
    have F1: "(f a \<oplus> g a) \<in> carrier  R"
      using assms
      by blast
    have RHS: " (\<Oplus>n\<in>insert a A. f n \<oplus> g n) = (f a \<oplus> g a) \<oplus> (\<Oplus>n\<in>A. f n \<oplus> g n)"
      using F0 F1 assms finsum_insert[of A a " (\<lambda>n. f n \<oplus> g n)"] False A0
      by blast
    have F2: " f a \<oplus> finsum R f A \<oplus> (g a \<oplus> finsum R g A) = (f a \<oplus> g a) \<oplus> (finsum R f A \<oplus>  finsum R g A)"
    proof-
      have F20: "f a \<in> carrier R"
        using assms(1) by blast
      have F21: "g a \<in> carrier R"
        using assms(2) by blast
      have F22: "finsum R f A \<in> carrier R"
        by (metis Pi_iff assms(1) finsum_closed)
      have F23: "finsum R g A \<in> carrier R"
        by (metis Pi_I assms(2) finsum_closed)
      show ?thesis using F21 F20 F22 F23
        using add.m_assoc add.m_closed add.m_lcomm
        by presburger
    qed
    show ?thesis
      using RHS LHS assms A1 F2
      by presburger
  qed
qed

lemma poly_eval_add:
  assumes "P \<in> Pring_set R I"
  assumes "Q \<in> Pring_set R I"
  assumes "closed_fun R g"
  shows "poly_eval R S g (P \<Oplus> Q)   = poly_eval R S g P  \<Oplus> poly_eval R S g Q "
proof
  fix m
  show "poly_eval R S g (P \<Oplus> Q)  m = (poly_eval R S g P \<Oplus> poly_eval R S g Q) m"
  proof-
    obtain F where F_def: "F = monomials_reducing_to R m (P \<Oplus> Q) S \<union> monomials_reducing_to R m P S \<union>
                              monomials_reducing_to R m Q S"
      by simp
    have 0: "finite F"
    proof-
      have 00: "finite (monomials_reducing_to R m (P \<Oplus> Q) S)"
        using assms
        by (meson finite_subset monomials_finite monomials_of_add_finite monomials_reducing_to_subset)
      have 01: "finite (monomials_reducing_to R m P S)"
        using assms(1) monomials_reducing_to_finite by blast
      have 02: "finite (monomials_reducing_to R m Q S)"
        using assms(2) monomials_reducing_to_finite by blast
      show ?thesis
        using F_def 00 01 02
        by blast
    qed
    have 1: "\<And>n. n \<in> F \<Longrightarrow> remove_indices n S = m"
    proof-
      fix n
      assume A: "n \<in> F"
      show "remove_indices n S = m"
        using F_def
        unfolding monomials_reducing_to_def
        using A
        by blast
    qed
    have 2: "poly_eval R S g (P \<Oplus> Q)  m  = (\<Oplus>n\<in> F. monom_eval R (restrict_to_indices n S) g \<otimes> (P \<Oplus> Q) n)"
      using assms 0 1 poly_eval_mono[of "P \<Oplus> Q" I g F m] F_def indexed_pset.indexed_padd
      by blast
    have 3: "poly_eval R S g P m  = (\<Oplus>n\<in> F. monom_eval R (restrict_to_indices n S) g \<otimes> P n)"
      using assms 0 1 poly_eval_mono[of "P" I g F m] F_def indexed_pset.indexed_padd
      by blast
    have 4: "poly_eval R S g Q m  = (\<Oplus>n\<in> F. monom_eval R (restrict_to_indices n S) g \<otimes> Q n)"
      using assms 0 1 poly_eval_mono[of "Q" I g F m] F_def indexed_pset.indexed_padd
      by blast
    have 5: "poly_eval R S g P m \<oplus> poly_eval R S g Q m = (\<Oplus>n\<in> F. monom_eval R (restrict_to_indices n S) g \<otimes> P n
                                                          \<oplus> monom_eval R (restrict_to_indices n S) g \<otimes> Q n)"
    proof-
      have 50: "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> P n) \<in> F \<rightarrow> carrier R"
        by (meson Pi_I Pring_cfs_closed assms(1) assms(3) m_closed monom_eval_car)
      have 51: "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> Q n) \<in> F \<rightarrow> carrier R"
        by (meson Pi_I Pring_cfs_closed assms(2) assms(3) m_closed monom_eval_car)
      then show ?thesis
        using 0 2 3 50 finsum_group[of "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> P n)"
                                       "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> Q n)" F]
        by (metis (mono_tags, lifting) "4" Pring_cfs_closed assms(1) assms(2) assms(3) m_closed monom_eval_car)
    qed
    have 6: "poly_eval R S g P m \<oplus> poly_eval R S g Q m
           = (\<Oplus>n\<in> F. monom_eval R (restrict_to_indices n S) g \<otimes>( P n \<oplus>  Q n))"
    proof-
      have 0 : "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> P n \<oplus> monom_eval R (restrict_to_indices n S) g \<otimes> Q n) \<in> F \<rightarrow> carrier R"
        apply(rule Pi_I)
        by (meson Pring_cfs_closed add.m_closed assms(1) assms(2) assms(3) m_closed monom_eval_car)
      have 1: "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> (P n \<oplus> Q n)) \<in> F \<rightarrow> carrier R"
        apply(rule Pi_I)
        by (meson Pring_cfs_closed add.m_closed assms(1) assms(2) assms(3) m_closed monom_eval_car)
      have "\<And>n. n \<in> F \<Longrightarrow>  monom_eval R (restrict_to_indices n S) g \<otimes>( P n \<oplus>  Q n) = monom_eval R (restrict_to_indices n S) g \<otimes> P n
                                                          \<oplus> monom_eval R (restrict_to_indices n S) g \<otimes> Q n"
        using assms Pring_cfs_closed cring.monom_eval_car is_cring r_distr
        by metis
      then have "(\<lambda>x\<in>F. monom_eval R (restrict_to_indices x S) g \<otimes> P x \<oplus> monom_eval R (restrict_to_indices x S) g \<otimes> Q x)
                = (\<lambda>x\<in>F. monom_eval R (restrict_to_indices x S) g \<otimes> (P x \<oplus> Q x))"
        by (metis (no_types, lifting) restrict_ext)
      then show ?thesis
        using 5 finsum_eq[of "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> P n  \<oplus> monom_eval R (restrict_to_indices n S) g \<otimes> Q n)"
                            F "(\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes>( P n \<oplus>  Q n))" ] 0 1
        by presburger
    qed
    have 7: "monomials_reducing_to R m (P \<Oplus> Q) S \<subseteq> F"
      using F_def
      by blast
    have 8: "poly_eval R S g (P \<Oplus> Q)  m  = (\<Oplus>n\<in>F. monom_eval R (restrict_to_indices n S) g \<otimes> (P \<Oplus> Q) n)"
      using 7 0 1 "2"
      by blast
    obtain f where f_def: "f = (\<lambda>n. monom_eval R (restrict_to_indices n S) g \<otimes> (P \<Oplus> Q) n)"
      by blast
    obtain h where h_def: "h = (\<lambda>n.  monom_eval R (restrict_to_indices n S) g \<otimes>( P n \<oplus>  Q n))"
      by blast
    have 9: "f \<in> F \<rightarrow> carrier R"
      using f_def
      by (metis (mono_tags, lifting) Pi_I Pring_cfs_closed add.m_closed
          assms(1) assms(2) assms(3) indexed_padd_def m_closed monom_eval_car)
    have 10: "h \<in> F \<rightarrow> carrier R"
      using h_def
      by (metis (mono_tags, lifting) "9" Pi_cong f_def indexed_padd_def)
    have 11: "restrict f F = restrict h F"
      using f_def h_def
      by (metis indexed_padd_def)
    have "finsum R f F = finsum R h F"
      using 9 10 11 finsum_eq[of f F h]
      by blast
    then show ?thesis
      using f_def h_def
      by (metis (no_types, lifting) "6" "8"  indexed_padd_def)
  qed
qed

lemma poly_eval_Pring_add:
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  assumes "closed_fun R g"
  shows "poly_eval R S g (P \<oplus>\<^bsub>Pring R I\<^esub> Q)   = poly_eval R S g P \<oplus>\<^bsub>Pring R I\<^esub> poly_eval R S g Q "
  using assms poly_eval_add[of P I Q g S]
  by (metis Pring_add Pring_car)

text\<open>Closure of partial evaluation maps:\<close>
lemma(in cring) poly_eval_closed:
  assumes "closed_fun R g"
  assumes "P \<in> Pring_set R I"
  shows "poly_eval R S g P \<in> Pring_set R (I - S)"
proof-
  obtain Pr where Pr_def[simp]: "Pr = (\<lambda>Q. poly_eval R S g Q \<in> Pring_set R (I - S))"
    by blast
  have "Pr P"
    apply(rule poly_monom_induction2[of _ I _ ])
     apply (metis Pr_def indexed_pset.indexed_const poly_eval_constant zero_closed)
       apply (metis Pr_def assms(1) indexed_pset.indexed_const mset_to_IP_closed
        poly_eval_constant poly_eval_monomial_term_closed poly_scalar_mult_zero r_null r_one)
  proof-
    show "P \<in> Pring_set R I" using assms by blast
    show "\<And>Q m k. Q \<in> Pring_set R I \<and> Pr Q \<and> set_mset m \<subseteq> I \<and> k \<in> carrier R\<Longrightarrow> Pr (Q \<Oplus> poly_scalar_mult R k (mset_to_IP R m))"
    proof-
      fix Q
      fix m
      fix k
      assume A: "Q \<in> Pring_set R I \<and> Pr Q \<and> set_mset m \<subseteq> I\<and> k \<in> carrier R"
      then have 0: "poly_eval R S g Q \<in> Pring_set R (I - S)"
        using Pr_def by blast
      have 1: "poly_scalar_mult R k (mset_to_IP R m) \<in> Pring_set R I"
        using  A mset_to_IP_closed poly_scalar_mult_closed
        by blast
      have  "poly_eval R  S g (Q \<Oplus> poly_scalar_mult R k (mset_to_IP R m)) =
     poly_eval R S g Q \<Oplus> poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m))   "
        using assms poly_eval_add[of Q I " (poly_scalar_mult R k (mset_to_IP R m))" g]  "1" A
        by blast
      then show "Pr (Q \<Oplus> poly_scalar_mult R k (mset_to_IP R m))"
        using Pr_def
        by (metis "1" A assms(1) indexed_pset.indexed_padd poly_eval_monomial_term_closed poly_scalar_mult_one poly_scalar_mult_zero)
    qed
  qed
  then show ?thesis
    using Pr_def
    by blast
qed

lemma poly_scalar_mult_indexed_pmult:
  assumes "P \<in> Pring_set R I"
  assumes "k \<in> carrier R"
  shows " poly_scalar_mult R k (P \<Otimes> i) = (poly_scalar_mult R k P) \<Otimes> i"
proof-
  have 0: "mset_to_IP R {#i#} \<in> Pring_set R (I \<union> {i})"
    by (metis Un_upper2 mset_to_IP_closed set_mset_add_mset_insert set_mset_empty)
  have 1: "P \<in> Pring_set R (I \<union> {i})"
    using Pring_carrier_subset Un_upper1 assms(1) by blast
  show ?thesis
    using 0 1  poly_scalar_mult_times[of "mset_to_IP R {#i#}" "I \<union> {i}" P  k]
        poly_index_mult[of P "I \<union> {i}" i] assms
    by (metis Un_upper2 insert_subset poly_index_mult poly_scalar_mult_closed)
qed

lemma remove_indices_add_mset:
  assumes "i \<notin> S"
  shows "remove_indices (add_mset i m) S = add_mset i (remove_indices m S)"
  apply(induction m)
  apply (smt assms empty_eq_union remove_indices_decomp restrict_to_indicesE single_is_union union_single_eq_member)
  by (metis assms multi_union_self_other_eq remove_indices_decomp restrict_to_indices_add_element union_mset_add_mset_right)

lemma poly_eval_monom_insert:
  assumes "closed_fun R g"
  assumes "\<one> \<noteq>\<zero>"
  assumes "i \<in> S"
  shows "poly_eval R  S g (mset_to_IP R (add_mset i m))
           = poly_scalar_mult R (g i)
                    (poly_eval R  S g (mset_to_IP R m))"
proof-
  have 0: "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                poly_scalar_mult R (monom_eval R (restrict_to_indices (add_mset i m) S) g)
                              (mset_to_IP R (remove_indices (add_mset i m) S))"
    using assms(1) assms(2) poly_eval_monomial by blast
  have 1: "(mset_to_IP R (remove_indices (add_mset i m) S)) =
                           (mset_to_IP R (remove_indices m S))"
    using assms
    by (metis (full_types) Diff_iff insert_Diff1 remove_indices_def restrict_to_indices_add_element set_mset_add_mset_insert)
  have 2: "(monom_eval R (restrict_to_indices (add_mset i m) S) g) =
            (g i) \<otimes> ((monom_eval R (restrict_to_indices m S) g))"
    using assms
    by (metis monom_eval_add restrict_to_indices_add_element)
  have 3: "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                poly_scalar_mult R ((g i) \<otimes> ((monom_eval R (restrict_to_indices m S) g)))
                              (mset_to_IP R (remove_indices m S))"
    using 0 1 2 assms
    by presburger
  hence "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                poly_scalar_mult R (g i)
                  (poly_scalar_mult R ((monom_eval R (restrict_to_indices m S) g))
                              (mset_to_IP R (remove_indices m S)))"
    using assms poly_scalar_mult_iter[of "(mset_to_IP R (remove_indices m S))"
                                          UNIV "g i" "monom_eval R (restrict_to_indices m S) g"]
          mset_to_IP_closed[of "remove_indices m S" UNIV]
    by (metis PiE UNIV_I monom_eval_car subsetI)
  thus ?thesis using assms
    by (metis poly_eval_monomial)
qed

lemma poly_eval_monom_insert':
  assumes "closed_fun R g"
  assumes "\<one> \<noteq>\<zero>"
  assumes "i \<notin> S"
  shows "poly_eval R  S g (mset_to_IP R (add_mset i m))
           =  (poly_eval R  S g (mset_to_IP R m)) \<Otimes> i"
proof-
  have 0: "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                poly_scalar_mult R (monom_eval R (restrict_to_indices (add_mset i m) S) g)
                              (mset_to_IP R (remove_indices (add_mset i m) S))"
    using assms(1) assms(2) poly_eval_monomial by blast
  hence "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                poly_scalar_mult R (monom_eval R (restrict_to_indices m S) g)
                              (mset_to_IP R (remove_indices (add_mset i m) S))"
    by (metis assms(3) restrict_to_indices_add_element)
  hence "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                poly_scalar_mult R (monom_eval R (restrict_to_indices m S) g)
                              (mset_to_IP R (add_mset i (remove_indices m S)))"
    by (metis assms(3) remove_indices_add_mset)
  hence "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                poly_scalar_mult R (monom_eval R (restrict_to_indices m S) g)
                              (mset_to_IP R (remove_indices m S) \<Otimes> i)"
    by (metis monom_add_mset)
  hence "poly_eval R  S g (mset_to_IP R (add_mset i m)) =
                (poly_scalar_mult R (monom_eval R (restrict_to_indices m S) g)
                              (mset_to_IP R (remove_indices m S))) \<Otimes> i"
    by (metis assms(1) cring.monom_eval_car is_cring local.ring_axioms
        poly_scalar_mult_indexed_pmult ring.mset_to_IP_closed set_eq_subset)
  thus ?thesis
    by (metis assms(1) assms(2) poly_eval_monomial)
qed

lemma poly_eval_indexed_pmult_monomial:
  assumes "closed_fun R g"
  assumes "k \<in> carrier R"
  assumes "i \<in> S"
  assumes "\<one> \<noteq> \<zero>"
  shows "poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m) \<Otimes> i) =
          poly_scalar_mult R (g i) (poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m)))"
proof-
  have 0: "poly_scalar_mult R k (mset_to_IP R m) \<Otimes> i =
              poly_scalar_mult R k (mset_to_IP R (add_mset i m ))"
    using monom_add_mset[of i m] poly_scalar_mult_indexed_pmult
    by (metis (no_types, opaque_lifting) assms(2) local.ring_axioms  ring.mset_to_IP_closed subsetD subset_refl)
  hence 1: "poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m) \<Otimes> i)  =
             poly_scalar_mult R k (poly_eval R S g (mset_to_IP R (add_mset i m )))"
    by (metis assms(1) assms(2) cring.poly_eval_scalar_mult is_cring local.ring_axioms ring.mset_to_IP_closed subsetI)
  have 2: "poly_scalar_mult R (g i) (poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m)))
            = poly_scalar_mult R (g i)
              (poly_scalar_mult R k  (poly_eval R S g (mset_to_IP R m))) "
    by (smt assms(1) assms(2) local.ring_axioms poly_eval_scalar_mult ring.mset_to_IP_closed subsetD subset_refl)
  hence 3: "poly_scalar_mult R (g i) (poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m)))
            = poly_scalar_mult R k
              (poly_scalar_mult R (g i) (poly_eval R S g (mset_to_IP R m))) "
    using assms poly_scalar_mult_comm[of "(poly_eval R S g (mset_to_IP R m))" UNIV]
          poly_eval_closed[of g "(mset_to_IP R m)" UNIV]
    by (metis UNIV_I closed_fun_simp cring.poly_scalar_mult_comm
        is_cring local.ring_axioms ring.mset_to_IP_closed subsetI)
  have 4: "(poly_eval R S g (mset_to_IP R (add_mset i m))) =  (poly_scalar_mult R (g i) (poly_eval R S g (mset_to_IP R m)))"
    using assms poly_eval_monom_insert[of g i S m]
    by blast
  thus ?thesis
    using 1 3 poly_scalar_mult_comm assms
    by presburger
qed

lemma poly_eval_indexed_pmult_monomial':
  assumes "closed_fun R g"
  assumes "k \<in> carrier R"
  assumes "i \<notin> S"
  assumes "\<one> \<noteq> \<zero>"
  shows "poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m) \<Otimes> i) =
         (poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m))) \<Otimes> i"
proof-
  have "poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m) \<Otimes> i) =
      poly_scalar_mult R k (poly_eval R S g ( (mset_to_IP R m) \<Otimes> i))"
    using poly_eval_scalar_mult[of k g]
    by (metis UNIV_I assms(1) assms(2) local.ring_axioms poly_scalar_mult_indexed_pmult ring.monom_add_mset ring.mset_to_IP_closed subsetI)
  hence "poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m) \<Otimes> i) =
      poly_scalar_mult R k (poly_eval R S g (mset_to_IP R (add_mset i m)))"
    by (simp add: monom_add_mset)
  hence "poly_eval R S g (poly_scalar_mult R k (mset_to_IP R m) \<Otimes> i) =
      (poly_scalar_mult R k (poly_eval R S g (mset_to_IP R m))) \<Otimes> i"
    using poly_eval_monom_insert'[of g i S m]
    by (smt assms(1) assms(2) assms(3) assms(4) poly_eval_monomial_closed poly_scalar_mult_indexed_pmult subsetD subset_refl)
  thus ?thesis using assms poly_eval_scalar_mult[of k g _ UNIV S]
    by (metis UNIV_I mset_to_IP_closed subsetI)
qed

lemma indexed_pmult_add:
  assumes "p \<in> Pring_set R I"
  assumes "q \<in> Pring_set R I"
  shows "p \<Oplus> q \<Otimes> i = (p \<Otimes> i) \<Oplus> (q \<Otimes> i)"
  using assms poly_index_mult[of _ "I \<union> {i}"]
  by (smt Pring_carrier_subset Set.basic_monos(1) Un_upper1 Un_upper2 cring.axioms(1)
      insert_subset is_cring mk_disjoint_insert mset_to_IP_closed ring.P_ring_ldistr
      ring.indexed_pset.intros(2) ring.indexed_pset_in_carrier set_mset_add_mset_insert
      set_mset_empty)

lemma poly_eval_indexed_pmult:
  assumes "P \<in> Pring_set R I"
  assumes "closed_fun R g"
  shows "poly_eval R S g (P \<Otimes> i)   = (if i \<in> S then poly_scalar_mult R (g i) (poly_eval R S g P) else (poly_eval R S g P)\<Otimes> i )"
proof(cases "i \<in> S")
  case True
  have "poly_eval R S g (P \<Otimes> i) = poly_scalar_mult R (g i) (poly_eval R S g P)"
  apply(rule poly_monom_induction3[of P I])
    using assms apply blast
      apply (metis PiE UNIV_I assms(2) indexed_pmult_zero poly_eval_constant poly_scalar_mult_const r_null zero_closed)
        apply (meson True assms(2) poly_eval_indexed_pmult_monomial)
          apply (smt PiE True UNIV_I assms(2) genideal_one genideal_zero indexed_pmult_zero mset_to_IP_closed poly_eval_constant poly_eval_indexed_pmult_monomial poly_scalar_mult_one poly_scalar_mult_zero singletonD)
  proof- fix p q assume A:
          "p \<in> Pring_set R I"
          "poly_eval R S g (p \<Otimes> i) = poly_scalar_mult R (g i) (poly_eval R S g p)"
          "q \<in> Pring_set R I"
          "poly_eval R S g (q \<Otimes> i) = poly_scalar_mult R (g i) (poly_eval R S g q)"
    have "poly_eval R S g (p \<Oplus> q \<Otimes> i) = poly_eval R S g (p \<Otimes> i) \<Oplus> poly_eval R S g (q \<Otimes> i)"
      using assms poly_eval_add[of "p \<Otimes> i" "I \<union> {i}" "q \<Otimes> i" g S]
            indexed_pmult_add[of p  I q i]
      by (smt A(1) A(3) Pring_carrier_subset Un_insert_right Un_upper1 indexed_pset.indexed_pmult insert_iff insert_subset mk_disjoint_insert)
    hence "poly_eval R S g (p \<Oplus> q \<Otimes> i) = poly_scalar_mult R (g i) (poly_eval R S g p) \<Oplus>
                                           poly_scalar_mult R (g i) (poly_eval R S g q)"
      using A
      by presburger
    hence "poly_eval R S g (p \<Oplus> q \<Otimes> i) = poly_scalar_mult R (g i)
                                            ((poly_eval R S g p) \<Oplus> (poly_eval R S g q))"
      using Pring_smult poly_eval_closed[of g] A Pring_add Pring_car  \<open>poly_eval R S g (p \<Oplus> q \<Otimes> i) = poly_eval R S g (p \<Otimes> i) \<Oplus> poly_eval R S g (q \<Otimes> i)\<close> assms(1) assms(2) closed_fun_simp
            Pring_smult_r_distr[of "g i" "poly_eval R S g p" _ "poly_eval R S g q"] Pring_add Pring_car
      by metis
    thus "poly_eval R S g (p \<Oplus> q \<Otimes> i) = poly_scalar_mult R (g i) (poly_eval R S g (p \<Oplus> q))"
      by (metis A(1) A(3) assms(2) poly_eval_add)
  qed
  then show ?thesis
    using True by presburger
next
  case False
  have "poly_eval R S g (P \<Otimes> i) = (poly_eval R S g P) \<Otimes> i"
  apply(rule poly_monom_induction3[of P I])
       apply (simp add: assms(1))
        apply (metis indexed_pmult_zero poly_eval_constant zero_closed)
          apply (metis False assms(2) indexed_pmult_zero inv_unique l_null  mset_to_IP_closed
           one_closed one_mset_to_IP poly_eval_constant  poly_eval_indexed_pmult_monomial'
           poly_scalar_mult_zero  zero_closed)
  proof-fix p q assume A:
          "p \<in> Pring_set R I"
          "poly_eval R S g (p \<Otimes> i) = poly_eval R S g p \<Otimes> i"
          "q \<in> Pring_set R I"
          "poly_eval R S g (q \<Otimes> i) = poly_eval R S g q \<Otimes> i"
    have "poly_eval R S g (p \<Oplus> q \<Otimes> i) = poly_eval R S g (p \<Otimes> i) \<Oplus> poly_eval R S g (q \<Otimes> i)"
      using assms poly_eval_add[of "p \<Otimes> i" "I \<union> {i}" "q \<Otimes> i" g S]
            indexed_pmult_add[of p  I q i]
      by (smt A(1) A(3) Pring_carrier_subset Un_insert_right Un_upper1 indexed_pset.indexed_pmult insert_iff insert_subset mk_disjoint_insert)
    thus "poly_eval R S g (p \<Oplus> q \<Otimes> i) = poly_eval R S g (p \<Oplus> q) \<Otimes> i"
      by (metis A(1) A(2) A(3) A(4) assms(2) indexed_pmult_add poly_eval_add poly_eval_closed)
  qed
  then show ?thesis
    by (simp add: False)
qed

lemma poly_eval_index:
  assumes "\<one> \<noteq>\<zero>"
  assumes "closed_fun R g"
  shows "poly_eval R S g (mset_to_IP R {#i#})= (if i \<in> S then (indexed_const (g i)) else mset_to_IP R {#i#})"
proof-
  have 0: "poly_eval R S g (mset_to_IP R {#i#})= poly_scalar_mult R (monom_eval R (restrict_to_indices {#i#} S) g)
                              (mset_to_IP R (remove_indices {#i#} S))"
    using poly_eval_monomial[of g S "{#i#}" ] assms(1) assms(2) by blast
  show ?thesis proof(cases "i \<in> S")
    case True
    then have T0: "(restrict_to_indices {#i#} S) =  {#i#}"
      by (metis restrict_to_indices_add_element restrict_to_indices_submultiset add_mset_subseteq_single_iff)
    then have T1: "(monom_eval R (restrict_to_indices {#i#} S) g) = (monom_eval R {#i#} g)"
      by presburger
    then have "(monom_eval R (restrict_to_indices {#i#} S) g)  = g i \<otimes>  monom_eval R {#} g"
      using assms monom_eval_add[of g i "{#}"]
      by presburger
    then have T2: "(monom_eval R (restrict_to_indices {#i#} S) g)  = g i"
      unfolding monom_eval_def
      using T0
      by (metis PiE UNIV_I assms(2) fold_mset_empty r_one)
    have T3: "(remove_indices {#i#} S) = {#}"
      by (metis Diff_iff remove_indices_indices restrict_to_indicesE
          T0 multiset_cases subset_iff union_single_eq_member)
    then have T4: " (mset_to_IP R (remove_indices {#i#} S)) = indexed_const \<one>"
      by (metis one_mset_to_IP)
    have T5: "poly_eval R S g (mset_to_IP R {#i#})= poly_scalar_mult R (g i) (indexed_const \<one>)"
      using "0" T2 T4
      by presburger
    then show ?thesis using True  poly_scalar_mult_const
      by (metis T2 assms(2) monom_eval_car one_closed r_one)
  next
    case False
    have F0: "(restrict_to_indices {#i#} S) = {#}"
      using False restrict_to_indices_def
      by (metis restrict_to_indices_add_element filter_empty_mset)
    have F1: "(monom_eval R (restrict_to_indices {#i#} S) g) = \<one>"
      using F0
      unfolding monom_eval_def
      by (metis fold_mset_empty)
    have F2: "(remove_indices {#i#} S) = {#i#}"
      using False
      by (metis Diff_iff remove_indices_def restrict_to_indices_add_element
          restrict_to_indices_def filter_empty_mset set_mset_single singletonI)
    have F3: "(mset_to_IP R (remove_indices {#i#} S)) = mset_to_IP R {#i#}"
      by (simp add: F2)
    have F4: " poly_eval R S g (mset_to_IP R {#i#})= poly_scalar_mult R \<one> (mset_to_IP R {#i#})"
      using "0" F1 F3
      by presburger
    show ?thesis using False
      by (metis F4 mset_to_IP_closed poly_scalar_mult_one subset_iff)
  qed
qed

lemma poly_eval_indexed_pmult':
  assumes "P \<in> Pring_set R I"
  assumes "closed_fun R g"
  assumes "i \<in> I"
  shows "poly_eval R  S g (P \<Otimes>\<^sub>p  (mset_to_IP R {#i#}))  =  poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (mset_to_IP R {#i#})"
proof(cases "i \<in> S")
  case True
  have "(P \<Otimes>\<^sub>p mset_to_IP R {#i#})=(P \<Otimes> i) "
    using assms poly_index_mult
    by metis
  then have 0: " poly_eval R  S g (P \<Otimes>\<^sub>p mset_to_IP R {#i#}) = poly_scalar_mult R (g i) (poly_eval R S g P)"
    using True assms poly_eval_indexed_pmult[of P I g S i]
    by presburger
  have 1: "poly_eval R S g (mset_to_IP R {#i#}) = indexed_const (g i)"
    using assms True
    by (smt PiE UNIV_I genideal_one genideal_zero indexed_pmult_zero monom_add_mset one_mset_to_IP poly_eval_constant poly_eval_index singletonD)
  then have "poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (mset_to_IP R {#i#})=  poly_eval R S g P\<Otimes>\<^sub>p indexed_const (g i) "
    by presburger
  then have "poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (mset_to_IP R {#i#})= indexed_const (g i) \<Otimes>\<^sub>p  poly_eval R S g P"
    using assms P_ring_mult_comm[of "indexed_const (g i)" "poly_eval R S g P"]
    unfolding carrier_coeff_def
    by (metis "1" Pring_cfs_closed cring.closed_fun_simp indexed_pset.indexed_const is_cring poly_eval_closed)
  then have "poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (mset_to_IP R {#i#})= poly_scalar_mult R (g i)  (poly_eval R S g P)"
    using assms
    by (metis "0" "1" \<open>P \<Otimes>\<^sub>p mset_to_IP R {#i#} = P \<Otimes> i\<close> cring.closed_fun_simp is_cring poly_eval_closed poly_scalar_mult_eq)
  then show ?thesis using 0
    by presburger
next
  case False
  then have 0: "poly_eval R  S g (P \<Otimes>\<^sub>p  (mset_to_IP R {#i#})) = (poly_eval R S g P)\<Otimes> i "
    using assms
    by (metis poly_eval_indexed_pmult poly_index_mult)
  have 1: "poly_eval R S g (mset_to_IP R {#i#})= mset_to_IP R {#i#}"
    using False
    by (metis assms(2) indexed_pmult_zero monom_add_mset one_closed one_mset_to_IP poly_eval_constant poly_eval_index)
  then show ?thesis
    using 0 False assms poly_eval_index[of g]
    by (metis UNIV_I cring.Pring_set_restrict is_cring local.ring_axioms poly_eval_closed ring.poly_index_mult subsetI)
qed

lemma poly_eval_monom_mult:
  assumes "P \<in> Pring_set R I"
  assumes "closed_fun R g"
  shows "poly_eval R  S g (P  \<Otimes>\<^sub>p  (mset_to_IP R m))  = poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (mset_to_IP R m) "
proof(induct m)
  case empty
  have 0:  "mset_to_IP R {#} = indexed_const \<one>"
    using one_mset_to_IP by blast
  then have 1: "(P \<Otimes>\<^sub>p mset_to_IP R {#}) = P"
    using assms
    by (metis P_ring_mult_comm Pring_cfs_closed carrier_coeff_def
        mset_to_IP_simp mset_to_IP_simp' one_closed one_mult_left zero_closed)
  have 2: "poly_eval R S g  (mset_to_IP R {#}) = indexed_const \<one>"
    by (metis "0" one_closed poly_eval_constant)
  show ?case using 0 1 2
    by (metis assms(1) assms(2) cring.P_ring_mult_comm indexed_pset.indexed_const
        is_cring local.ring_axioms one_closed one_mult_left poly_eval_closed
        ring.indexed_pset_in_carrier set_eq_subset)
next
  case (add x m)
  fix x
  fix m
  assume A: "poly_eval R  S g (P \<Otimes>\<^sub>p mset_to_IP R m) = poly_eval R S g P \<Otimes>\<^sub>p poly_eval R S g (mset_to_IP R m)"
  show "poly_eval R  S g (P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m))= poly_eval R S g P \<Otimes>\<^sub>p poly_eval R  S g (mset_to_IP R (add_mset x m))"
  proof-
    obtain J where J_def: "J = I \<union> set_mset m \<union>{x}"
      by blast
    have I0: "P \<in> Pring_set R J"
      using J_def assms
      by (meson Pring_carrier_subset Un_upper1 subsetD)
    have I1: "set_mset m \<subseteq> J"
      using J_def by blast
    have I2: "x \<in> J"
      using J_def by blast
    have "mset_to_IP R (add_mset x m)= (mset_to_IP R m) \<Otimes> x"
      by (simp add: monom_add_mset)
    then have "(P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m)) = P \<Otimes>\<^sub>p((mset_to_IP R m) \<Otimes> x)"
      by simp
    then have "(P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m)) = P \<Otimes>\<^sub>p((mset_to_IP R m) \<Otimes>\<^sub>p (mset_to_IP R {#x#}))"
      by (metis add_mset_add_single monom_mult)
    then have I3: "(P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m)) = (P \<Otimes>\<^sub>p(mset_to_IP R m)) \<Otimes>\<^sub>p (mset_to_IP R {#x#})"
      by (metis I0 P_ring_mult_assoc indexed_pset_in_carrier mset_to_IP_closed set_eq_subset)
    have "poly_eval R  S g (P \<Otimes>\<^sub>p mset_to_IP R m \<Otimes>\<^sub>p mset_to_IP R {#x#}) =
            poly_eval R  S g (P \<Otimes>\<^sub>p mset_to_IP R m) \<Otimes>\<^sub>p poly_eval R S g  (mset_to_IP R {#x#})"
      using poly_eval_indexed_pmult'[of "(P \<Otimes>\<^sub>p(mset_to_IP R m))" J g x]
            I0 I1 I2 assms(2) assms(1) mset_to_IP_mult_closed
      by blast
    then have "poly_eval R S g (P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m)) =
          poly_eval R  S g (P \<Otimes>\<^sub>p(mset_to_IP R m)) \<Otimes>\<^sub>p  poly_eval R  S g (mset_to_IP R {#x#}) "
      using I3
      by simp
    then have "poly_eval R  S g (P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m)) =
         poly_eval R S g P \<Otimes>\<^sub>p poly_eval R S g (mset_to_IP R m)  \<Otimes>\<^sub>p  poly_eval R S g (mset_to_IP R {#x#}) "
      by (simp add: A)
    then have "poly_eval R S g  (P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m)) =
         poly_eval R S g P \<Otimes>\<^sub>p (poly_eval R S g (mset_to_IP R m)  \<Otimes>\<^sub>p  poly_eval R  S g (mset_to_IP R {#x#}))"
      using P_ring_mult_assoc[of "poly_eval R S g P " "poly_eval R S g (mset_to_IP R m)"  " poly_eval R  S g (mset_to_IP R {#x#})"]
      by (metis assms(1) assms(2)  indexed_pset_in_carrier mset_to_IP_closed poly_eval_closed set_eq_subset)
    then have "poly_eval R  S g (P \<Otimes>\<^sub>p mset_to_IP R (add_mset x m)) =
         poly_eval R S g P \<Otimes>\<^sub>p (poly_eval R  S g ((mset_to_IP R m) \<Otimes>\<^sub>p (mset_to_IP R {#x#})))"
      by (metis I1 I2 assms(2)  mset_to_IP_closed poly_eval_indexed_pmult')
    then show ?thesis
      by (metis add_mset_add_single monom_mult)
  qed
qed

abbreviation mon_term ("Mt") where
"Mt k m \<equiv> poly_scalar_mult R k (mset_to_IP R m)"

lemma poly_eval_monom_term_mult:
  assumes "P \<in> Pring_set R I"
  assumes "closed_fun R g"
  assumes "k \<in> carrier R"
  shows "poly_eval R S g (P \<Otimes>\<^sub>p (Mt k m))   = poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (Mt k m) "
proof-
  obtain J where J_def: "J = I \<union> (set_mset m)"
    by blast
  have J0: "P \<in> Pring_set R J"
    using J_def Pring_carrier_subset Un_upper1 assms(1) by blast
  have J1: "mset_to_IP R m  \<in> Pring_set R J"
    by (metis J_def Un_upper2 mset_to_IP_closed)
  have 0: "(P  \<Otimes>\<^sub>p  (Mt k m)) = poly_scalar_mult R k (P  \<Otimes>\<^sub>p  mset_to_IP R m)"
    using times_poly_scalar_mult[of P J "mset_to_IP R m" k ] J0 J1 assms(3)
    by blast
  have 1: "poly_eval R S g (P \<Otimes>\<^sub>p (Mt k m)) = poly_scalar_mult R k (poly_eval R  S g (P  \<Otimes>\<^sub>p  mset_to_IP R m))"
    by (metis "0" J0 J1 P_ring_mult_closed' assms(2) assms(3) cring.poly_eval_scalar_mult is_cring)
  have 2: "poly_eval R S g (P \<Otimes>\<^sub>p (Mt k m)) = poly_scalar_mult R k ((poly_eval R S g P)  \<Otimes>\<^sub>p (poly_eval R S g (mset_to_IP R m)))"
    by (metis "1" assms(1) assms(2)  poly_eval_monom_mult)
  have 3: "poly_eval R S g (P \<Otimes>\<^sub>p (Mt k m)) = (poly_eval R S g P)  \<Otimes>\<^sub>p poly_scalar_mult R k  (poly_eval R S g (mset_to_IP R m))"
    by (metis "0" "2" J0 J1 assms(2) assms(3)  poly_eval_closed times_poly_scalar_mult)
  then show ?thesis
    by (metis J1 assms(3) assms(2) poly_eval_scalar_mult)
qed

lemma poly_eval_mult:
  assumes "P \<in> Pring_set R I"
  assumes "Q \<in> Pring_set R I"
  assumes "closed_fun R g"
  shows "poly_eval R S g (P \<Otimes>\<^sub>p Q)  = poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g Q "
proof-
  obtain Pr where Pr_def: "Pr = (\<lambda>Q. poly_eval R S g (P \<Otimes>\<^sub>p Q)   = poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g Q )"
    by blast
  have "Pr Q"
  proof(rule poly_monom_induction2[of _ I])
    show "Q \<in> Pring_set R I"
      by (simp add: assms(2))
    show "Pr (indexed_const \<zero>)"
    proof-
      have 0: "(P \<Otimes>\<^sub>p indexed_const \<zero>) = indexed_const \<zero>"
        by (metis assms(1) cring.P_ring_mult_comm indexed_pset.indexed_const
            indexed_pset_in_carrier is_cring poly_scalar_mult_eq poly_scalar_mult_zero
            set_eq_subset zero_closed)
      have 1: "poly_eval R  S g (indexed_const \<zero>) = indexed_const \<zero>"
        using poly_eval_constant by blast
      have 2: "poly_eval R S g P  \<Otimes>\<^sub>p poly_eval R  S g (indexed_const \<zero>) = indexed_const \<zero>"
        using 1
        by (metis "0" assms(1) assms(3) local.ring_axioms one_closed poly_eval_monom_term_mult
            poly_scalar_mult_const r_one ring.one_mset_to_IP zero_closed)
      have 3: "poly_eval R S g (P \<Otimes>\<^sub>p indexed_const \<zero>) = indexed_const \<zero>"
        using "0" "1" by presburger
      show ?thesis
        using 2 3 Pr_def
        by presburger
    qed
    show "\<And>m k. set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> Pr (poly_scalar_mult R k (mset_to_IP R m))"
      using Pr_def assms(1) assms(3)  poly_eval_monom_term_mult by blast
    show " \<And>Q m k. Q \<in> Pring_set R I \<and> Pr Q \<and> set_mset m \<subseteq> I \<and> k \<in> carrier R \<Longrightarrow> Pr (Q \<Oplus> Mt k m)"
    proof-
      fix Q
      fix m
      fix k
      assume A: "Q \<in> Pring_set R I \<and> Pr Q \<and> set_mset m \<subseteq> I \<and> k \<in> carrier R"
      show "Pr (Q \<Oplus> Mt k m)"
      proof-
        have 0: "poly_eval R S g (P \<Otimes>\<^sub>p Q)   = poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g Q "
          using A Pr_def by blast
        have 1: "poly_eval R S g (P \<Otimes>\<^sub>p  (Mt k m))   = poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (Mt k m)"
          using A assms(1) assms(3)  poly_eval_monom_term_mult
          by blast
        have 2: "P \<Otimes>\<^sub>p  (Q \<Oplus> Mt k m) =(P \<Otimes>\<^sub>p  Q)\<Oplus> (P \<Otimes>\<^sub>p  (Mt k m)) "
          by (meson A assms(1) local.ring_axioms mset_to_IP_closed poly_scalar_mult_closed
              ring.P_ring_rdistr ring.indexed_pset_in_carrier set_eq_subset)
        have 3: "poly_eval R S g (P \<Otimes>\<^sub>p  (Q \<Oplus> Mt k m))= poly_eval R S g (P \<Otimes>\<^sub>p Q)  \<Oplus> poly_eval R S g (P \<Otimes>\<^sub>p  (Mt k m))     "
          by (metis "2" A P_ring_mult_closed' assms(1) assms(3)
              mset_to_IP_closed  poly_eval_add poly_scalar_mult_closed)
        have 4: "poly_eval R S g (P \<Otimes>\<^sub>p  (Q \<Oplus> Mt k m))=
        (poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g Q) \<Oplus> ( poly_eval R S g P  \<Otimes>\<^sub>p  poly_eval R S g (Mt k m) )"
          by (simp add: "0" "1" "3")
        have 5: " poly_eval R S g P \<Otimes>\<^sub>p (poly_eval R S g Q \<Oplus> poly_eval R S g (Mt k m)) = poly_eval R S g P \<Otimes>\<^sub>p poly_eval R S g Q \<Oplus> (poly_eval R S g P \<Otimes>\<^sub>p poly_eval R S g (Mt k m))"
          using ring.P_ring_rdistr[of R "(poly_eval R S g P)" "(poly_eval R S g Q)" "( poly_eval R S g (Mt k m) )"]
          by (meson A assms(1) assms(3) indexed_pset_in_carrier local.ring_axioms
              poly_eval_closed poly_scalar_mult_closed ring.mset_to_IP_closed subset_refl)
        have 6: "poly_eval R S g (P \<Otimes>\<^sub>p  (Q \<Oplus> Mt k m))=
        (poly_eval R S g P)  \<Otimes>\<^sub>p  ((poly_eval R S g Q) \<Oplus> ( poly_eval R S g (Mt k m) ))"
          using 4 5
          by simp
        have 7: "poly_eval R S g (P \<Otimes>\<^sub>p  (Q \<Oplus> Mt k m))=
        (poly_eval R S g P)  \<Otimes>\<^sub>p  (poly_eval R  S g (Q\<Oplus>(Mt k m)))"
          using 6 poly_eval_add[of "(poly_eval R S g Q)" I "(Mt k m)" g ]
          by (metis A assms(3) mset_to_IP_closed poly_eval_add poly_scalar_mult_closed)
        show ?thesis using 7
          using Pr_def by blast
      qed
    qed
  qed
  then show ?thesis
    using Pr_def by blast
qed

lemma poly_eval_Pring_mult:
  assumes "P \<in> Pring_set R I"
  assumes "Q \<in> Pring_set R I"
  assumes "closed_fun R g"
  shows "poly_eval R S g (P \<otimes>\<^bsub>Pring R I\<^esub> Q)  = poly_eval R S g P \<otimes>\<^bsub>Pring R I\<^esub> poly_eval R S g Q "
  by (metis Pring_mult assms(1) assms(2) assms(3) poly_eval_mult)

lemma poly_eval_smult:
  assumes "P \<in> Pring_set R I"
  assumes "a \<in> carrier R"
  assumes "closed_fun R g"
  shows "poly_eval R S g (a \<odot>\<^bsub>Pring R I\<^esub> P)  =a \<odot>\<^bsub>Pring R I\<^esub> poly_eval R S g P"
  using poly_eval_scalar_mult assms
  by (metis Pring_smult)

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Partial Evaluation is a Homomorphism\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma poly_eval_ring_hom:
  assumes "I \<subseteq> J"
  assumes "closed_fun R g"
  assumes "J - S \<subseteq> I"
  shows "ring_hom_ring (Pring R J) (Pring R I) (poly_eval R S g)"
  apply(rule ring_hom_ringI)
  apply (simp add: Pring_is_ring)
  apply (simp add: Pring_is_ring)
  apply (metis (full_types) Pring_car Pring_carrier_subset assms(2) assms(3) poly_eval_closed subset_iff)
  apply (metis Pring_car assms(2) local.ring_axioms poly_eval_mult ring.Pring_mult)
  apply (metis Pring_add Pring_car assms(2) poly_eval_add)
  by (metis Pring_one one_closed poly_eval_constant)

text\<open>\texttt{poly\_eval} R at the zero function is an inverse to the inclusion of polynomial rings\<close>

lemma poly_eval_zero_function:
  assumes "g = (\<lambda>n. \<zero>)"
  assumes "J - S = I"
  shows "P \<in> Pring_set R I \<Longrightarrow> poly_eval R S g P = P"
  apply(erule indexed_pset.induct)
  using poly_eval_constant apply blast
  using  assms poly_eval_add[of _ I _ g S]  zero_closed
  apply (metis Pi_I)
  using Diff_iff assms(1) assms(2) Pi_I[of UNIV g ]
      poly_eval_indexed_pmult set_eq_subset subsetD zero_closed
  by smt

lemma poly_eval_eval_function_eq:
  assumes "closed_fun R g"
  assumes "closed_fun R g'"
  assumes "restrict g S = restrict g' S"
  assumes "P \<in> Pring_set R I"
  shows "poly_eval R S g P = poly_eval R S g' P"
  apply(rule indexed_pset.induct[of P I "carrier R"])
     apply (simp add: assms(4))
    apply (metis poly_eval_constant)
   apply (metis assms(1) assms(2) poly_eval_add)
proof- fix P i assume A: "P \<in> Pring_set R I" "poly_eval R S g P = poly_eval R S g' P" "i \<in> I "
  show "poly_eval R S g (P \<Otimes> i) = poly_eval R S g' (P \<Otimes> i)"
  proof(cases "i \<in> S")
    case True
    then have "g i = g' i"
      using assms
      unfolding  restrict_def
      by meson
    then show ?thesis
      using assms A poly_eval_indexed_pmult[of P I g S i] poly_eval_indexed_pmult[of P I g' S i]
      by presburger
  next
    case False
    then show ?thesis
      using assms A poly_eval_indexed_pmult[of P I g S i] poly_eval_indexed_pmult[of P I g' S i]
      by presburger
  qed
qed

lemma poly_eval_eval_set_eq:
  assumes "closed_fun R g"
  assumes "S \<inter> I = S' \<inter> I"
  assumes "P \<in> Pring_set R I"
  assumes "\<one> \<noteq>\<zero>"
  shows "poly_eval R S g P = poly_eval R S' g P"
  apply(rule indexed_pset.induct[of P I "carrier R"])
     apply (simp add: assms(3))
  apply (metis poly_eval_constant)
   apply (metis assms(1) poly_eval_add)
proof- fix P i
  assume A: " P \<in> Pring_set R I" "poly_eval R S g P = poly_eval R S' g P" "i \<in> I "
  show "poly_eval R S g (P \<Otimes> i) = poly_eval R S' g (P \<Otimes> i)"
  using assms poly_eval_index[of g _ i] A
  by (metis Diff_Diff_Int Diff_iff poly_eval_indexed_pmult)
qed

lemma poly_eval_trivial:
  assumes "closed_fun R g"
  assumes "P \<in> Pring_set R (I - S)"
  shows "poly_eval R S g P = P"
  apply(rule indexed_pset.induct[of P "I - S" "carrier R"])
  apply (simp add: assms(2))
  using poly_eval_constant apply blast
  apply (metis assms(1) poly_eval_add)
  by (metis Diff_iff assms(1) poly_eval_indexed_pmult)

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Total Evaluation of a Polynomial\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma zero_fun_closed:
"closed_fun R (\<lambda>n. \<zero>)"
  by blast

lemma deg_zero_cf_eval:
  shows "P \<in> Pring_set R I \<Longrightarrow> poly_eval R I (\<lambda>n. \<zero>) P = indexed_const (P {#})"
  apply(erule indexed_pset.induct)
  apply (metis indexed_const_def poly_eval_constant)
proof-
  show " \<And>P Q. P \<in> Pring_set R I \<Longrightarrow>
           poly_eval R I (\<lambda>n. \<zero>) P = indexed_const (P {#}) \<Longrightarrow>
           Q \<in> Pring_set R I \<Longrightarrow> poly_eval R I (\<lambda>n. \<zero>) Q = indexed_const (Q {#}) \<Longrightarrow> poly_eval R I (\<lambda>n. \<zero>) (P \<Oplus> Q) = indexed_const ((P \<Oplus> Q) {#})"
  proof-
    fix P
    fix Q
    assume A: "P \<in> Pring_set R I"
    assume B: " poly_eval R I (\<lambda>n. \<zero>) P = indexed_const (P {#})"
    assume C: "Q \<in> Pring_set R I "
    assume D: " poly_eval R I (\<lambda>n. \<zero>) Q = indexed_const (Q {#})"
    have "indexed_const ((P \<Oplus> Q) {#}) = indexed_const (P {#})  \<Oplus> indexed_const (Q {#})"
      by (metis indexed_padd_const indexed_padd_def)
    thus "poly_eval R I (\<lambda>n. \<zero>) (P \<Oplus> Q) = indexed_const ((P \<Oplus> Q) {#})"
      using A B C D poly_eval_add[of P I Q "\<lambda>n. \<zero>" I]
      by (smt zero_fun_closed)
  qed
  show "\<And>P i. P \<in> Pring_set R I \<Longrightarrow> poly_eval R I (\<lambda>n. \<zero>) P = indexed_const (P {#}) \<Longrightarrow> i \<in> I \<Longrightarrow> poly_eval R I (\<lambda>n. \<zero>) (P \<Otimes> i) = indexed_const ((P \<Otimes> i) {#})"
  proof-
    fix P
    fix i
    assume A: "P \<in> Pring_set R I" "poly_eval R I (\<lambda>n. \<zero>) P = indexed_const (P {#})" "i \<in> I"
    show "poly_eval R I (\<lambda>n. \<zero>) (P \<Otimes> i) = indexed_const ((P \<Otimes> i) {#})"
    proof-
      have "poly_eval R I (\<lambda>n. \<zero>) (P \<Otimes> i) = indexed_const \<zero>"
        using A(1) A(3) cring.poly_eval_constant is_cring poly_eval_indexed_pmult
              poly_eval_scalar_mult poly_scalar_mult_zero zero_closed
        by (metis Pi_I)
      have "(P \<Otimes> i) {#} = \<zero>"
        using indexed_pmult_def
        by (metis empty_iff set_mset_empty)
      then show ?thesis
        using \<open>poly_eval R I (\<lambda>n. \<zero>) (P \<Otimes> i) = indexed_const \<zero>\<close>
        by presburger
    qed
  qed
qed

lemma deg_zero_cf_mult:
  assumes "P \<in> Pring_set R I"
  assumes "Q \<in> Pring_set R I"
  shows " (P \<Otimes>\<^sub>p Q) {#} = P {#} \<otimes> Q {#}"
proof-
  have "poly_eval R I (\<lambda>n. \<zero>) (P \<Otimes>\<^sub>p Q) = poly_eval R I (\<lambda>n. \<zero>) P \<Otimes>\<^sub>p  poly_eval R I (\<lambda>n. \<zero>) Q"
    using zero_fun_closed assms
    by (metis poly_eval_mult)
  then have 0: "indexed_const ((P \<Otimes>\<^sub>p Q) {#}) = (indexed_const (P {#})) \<Otimes>\<^sub>p (indexed_const (Q {#}))"
    by (metis P_ring_mult_closed' Pring_cfs_closed assms(1) assms(2) deg_zero_cf_eval indexed_const_P_mult_eq indexed_const_def)
  have "indexed_const ((P \<Otimes>\<^sub>p Q) {#}) = (indexed_const ((P {#}) \<otimes>(Q {#})))"
    apply(rule ccontr)
    using 0
    by (metis Pring_cfs_closed assms(1) assms(2) indexed_const_P_mult_eq)
  then show ?thesis
  proof -
    show ?thesis
      by (metis (no_types) \<open>indexed_const ((P \<Otimes>\<^sub>p Q) {#}) = indexed_const (P {#} \<otimes> Q {#})\<close>
        local.ring_axioms ring.indexed_const_def)
  qed
qed

definition deg_zero_cf :: "('a, 'c) mvar_poly \<Rightarrow> 'a" where
"deg_zero_cf P = P {#}"

lemma deg_zero_cf_ring_hom:
  shows "ring_hom_ring (Pring R I) R (deg_zero_cf)"
  apply(rule ring_hom_ringI)
  using Pring_is_ring apply blast
  apply (simp add: local.ring_axioms)
  apply (metis deg_zero_cf_def Pring_car Pring_cfs_closed)
  apply (metis deg_zero_cf_def Pring_car Pring_mult deg_zero_cf_mult)
  apply (metis deg_zero_cf_def Pring_add indexed_padd_def)
  by (metis deg_zero_cf_def Pring_one indexed_const_def)

end

definition eval_in_ring ::
 "('a,'b) ring_scheme \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> 'a" where
"eval_in_ring R S g P = (poly_eval R S g P) {#}"

definition total_eval ::
"('a,'b) ring_scheme \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> 'a"  where
"total_eval R g P = eval_in_ring R UNIV g P"

context cring
begin

lemma eval_in_ring_ring_hom:
  assumes "closed_fun R g"
  shows "ring_hom_ring (Pring R I) R (eval_in_ring R S g)"
  unfolding eval_in_ring_def
  apply(rule ring_hom_ringI)
  apply (simp add: Pring_is_ring)
  apply (simp add: local.ring_axioms)
    using Pring_car Pring_carrier_coeff' assms poly_eval_closed
     apply (metis )
        using Pring_mult[of I] poly_eval_mult[of _ I _ g S] poly_eval_closed[of g _ I S] deg_zero_cf_mult[of _ I] assms
          Pring_car[of I]
        apply (metis deg_zero_cf_mult)

          using Pring_add[of I ] poly_eval_add[of _ I _ g S] Pring_car[of I] assms indexed_padd_def
          apply metis
            unfolding deg_zero_cf_def
            by (metis Pring_one indexed_const_def one_closed poly_eval_constant)

lemma eval_in_ring_smult:
  assumes "P \<in> carrier (Pring R I)"
  assumes "a \<in> carrier R"
  assumes "closed_fun R g"
  shows "eval_in_ring R S g (a \<odot>\<^bsub>Pring R I\<^esub> P) = a \<otimes> eval_in_ring R S g P "
  using assms unfolding eval_in_ring_def
  by (smt Pring_car Pring_smult poly_eval_scalar_mult poly_scalar_mult_def)


lemma total_eval_ring_hom:
  assumes "closed_fun R g"
  shows "ring_hom_ring (Pring R I) R (total_eval R g)"
  using assms unfolding total_eval_def
  using eval_in_ring_ring_hom by blast

lemma total_eval_smult:
  assumes "P \<in> carrier (Pring R I)"
  assumes "a \<in> carrier R"
  assumes "closed_fun R g"
  shows "total_eval R g (a \<odot>\<^bsub>Pring R I\<^esub> P) = a \<otimes> total_eval R g P"
  using assms unfolding total_eval_def
  using eval_in_ring_smult by blast

lemma total_eval_const:
  assumes "k \<in> carrier R"
  shows "total_eval R g (indexed_const k) = k"
  unfolding total_eval_def eval_in_ring_def
  using assms
  by (metis indexed_const_def poly_eval_constant)

lemma total_eval_var:
  assumes "closed_fun R g"
  shows "(total_eval R g (mset_to_IP R {#i#})) = g i"
  unfolding total_eval_def eval_in_ring_def
  using UNIV_I assms indexed_const_def indexed_pmult_zero monom_add_mset one_closed
      one_mset_to_IP one_zeroD poly_eval_constant poly_eval_index  singletonD
  by (smt PiE iso_tuple_UNIV_I monom_eval_add monom_eval_car mset_to_IP_simp poly_scalar_mult_const r_one)

lemma total_eval_indexed_pmult:
  assumes "P \<in> carrier (Pring R I)"
  assumes "i \<in> I"
  assumes "closed_fun R g"
  shows "total_eval R g (P \<Otimes> i) = total_eval R g P \<otimes>\<^bsub>R\<^esub> g i"
proof-
  have "P \<Otimes> i = P \<Otimes>\<^sub>p mset_to_IP R ((add_mset i) {#})"
    using assms poly_index_mult[of P I i] Pring_car
    by blast
  then have 0: "(P \<Otimes> i) =  P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R {#i#})"
    by (simp add: Pring_mult)
  then have "total_eval R g (P \<Otimes> i) = (total_eval R g P) \<otimes>\<^bsub>R\<^esub> (total_eval R g (mset_to_IP R {#i#}))"
  proof-
    have "(mset_to_IP R {#i#}) \<in> carrier (Pring R I)"
      by (metis Pring_car assms(2) mset_to_IP_closed set_mset_single singletonD subset_iff)
    then show ?thesis
      using assms total_eval_ring_hom[of g I] ring_hom_mult
      by (metis "0" ring_hom_ring.homh)
  qed
  then show ?thesis
    by (metis assms(3) cring.total_eval_var is_cring)
qed

lemma total_eval_mult:
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  assumes "closed_fun R g"
  shows "total_eval R g (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (total_eval R g P) \<otimes>\<^bsub>R\<^esub>(total_eval R g Q) "
  by (metis assms(1) assms(2) assms(3) ring_hom_mult ring_hom_ring.homh total_eval_ring_hom)

lemma total_eval_add:
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  assumes "closed_fun R g"
  shows "total_eval R g (P \<oplus>\<^bsub>Pring R I\<^esub> Q) = (total_eval R g P) \<oplus>\<^bsub>R\<^esub>(total_eval R g Q) "
  by (metis assms(1) assms(2) assms(3) ring_hom_add ring_hom_ring.homh total_eval_ring_hom)

lemma total_eval_one:
  assumes "closed_fun R g"
  shows "total_eval R g \<one>\<^bsub>Pring R I\<^esub> = \<one>"
  by (metis Pring_one one_closed total_eval_const)

lemma total_eval_zero:
  assumes "closed_fun R g"
  shows "total_eval R g \<zero>\<^bsub>Pring R I\<^esub> = \<zero>"
  by (metis Pring_zero total_eval_const zero_closed)

lemma total_eval_closed:
  assumes "P \<in> carrier (Pring R I)"
  assumes "closed_fun R g"
  shows "total_eval R g P \<in> carrier R"
  using assms total_eval_ring_hom[of g]
  by (metis ring_hom_closed ring_hom_ring.homh)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Constructing Homomorphisms from Indexed Polynomial Rings and a Universal Property\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>The inclusion of \<open>R\<close> into its polynomial ring\<close>

lemma indexed_const_ring_hom:
"ring_hom_ring R (Pring R I) (indexed_const)"
  apply(rule ring_hom_ringI)
  apply (simp add: local.ring_axioms)
  apply (simp add: Pring_is_ring)
  using Pring_car indexed_pset.indexed_const apply blast
  apply (metis Pring_mult indexed_const_P_mult_eq)
  apply (metis indexed_padd_const local.ring_axioms ring.Pring_add)
  by (metis Pring_one)

lemma indexed_const_inj_on:
"inj_on (indexed_const) (carrier R)"
  by (metis cring.total_eval_const inj_onI is_cring)

end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Mapping $R[x] \to S[x]$ along a homomorphism $R \to S$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition ring_hom_to_IP_ring_hom ::
"('a, 'e) ring_hom \<Rightarrow> ('a, 'c) mvar_poly \<Rightarrow> 'c monomial \<Rightarrow> 'e"  where
"ring_hom_to_IP_ring_hom \<phi> P m = \<phi> (P m)"

context cring
begin

lemma ring_hom_to_IP_ring_hom_one:
  assumes "cring S"
  assumes "ring_hom_ring R S \<phi>"
  shows "ring_hom_to_IP_ring_hom \<phi> \<one>\<^bsub>Pring R I\<^esub> = \<one>\<^bsub>Pring S I\<^esub>"
  unfolding ring_hom_to_IP_ring_hom_def
proof
  fix m
  show " \<phi> (\<one>\<^bsub>Pring R I\<^esub> m) = \<one>\<^bsub>Pring S I\<^esub> m"
  proof(cases "m = {#}")
    case True
    then have "(\<one>\<^bsub>Pring R I\<^esub> m) = \<one>\<^bsub>R\<^esub>"
      by (metis Pring_one indexed_const_def)
    then have "\<phi> (\<one>\<^bsub>Pring R I\<^esub> m) = \<one>\<^bsub>S\<^esub>"
      using assms
      unfolding ring_hom_ring_def
      by (metis assms(2) ring_hom_one ring_hom_ring.homh)
    then show ?thesis using assms True ring.indexed_const_def ring_hom_ring_def
      by (metis ring.Pring_one)
  next
    case False
      then have "(\<one>\<^bsub>Pring R I\<^esub> m) = \<zero>\<^bsub>R\<^esub>"
        by (metis indexed_const_def local.ring_axioms ring.Pring_one)

    then have "\<phi> (\<one>\<^bsub>Pring R I\<^esub> m) = \<zero>\<^bsub>S\<^esub>"
      using assms
      unfolding ring_hom_ring_def cring_def
      by (metis assms(2) ring_hom_zero ring_hom_ring.homh)
    then show ?thesis using assms False ring.indexed_const_def ring_hom_ring_def
      by (metis ring.Pring_one)
  qed
qed

lemma ring_hom_to_IP_ring_hom_constant:
  assumes "cring S"
  assumes "ring_hom_ring R S \<phi>"
  assumes "a \<in> carrier R"
  shows "ring_hom_to_IP_ring_hom \<phi> ((indexed_const a):: 'c monomial \<Rightarrow> 'a) = ring.indexed_const S (\<phi> a)"
  unfolding ring_hom_to_IP_ring_hom_def indexed_const_def
proof
  fix m:: "'c monomial"
  show "\<phi> (if m = {#} then a else \<zero>) = ring.indexed_const S (\<phi> a) m"
    apply(cases "m = {#}")
  apply (simp add: assms(1) cring.axioms(1) ring.indexed_const_def)
  proof-
    assume "m \<noteq> {#} "
    then have "\<phi> (if m = {#} then a else \<zero>) = \<zero>\<^bsub>S\<^esub>"
      by (metis (full_types) assms(1) assms(2) cring_def local.ring_axioms
          ring_hom_ring.homh ring_hom_zero)
    then show " \<phi> (if m = {#} then a else \<zero>) = ring.indexed_const S (\<phi> a) m"
      using assms
      by (metis \<open>m \<noteq> {#}\<close> cring.axioms(1) ring.indexed_const_def)
  qed
qed

lemma ring_hom_to_IP_ring_hom_add:
  assumes "cring S"
  assumes "ring_hom_ring R S \<phi>"
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  shows "ring_hom_to_IP_ring_hom \<phi> (P \<oplus>\<^bsub>Pring R I\<^esub> Q) =
       (ring_hom_to_IP_ring_hom \<phi> P) \<oplus>\<^bsub>Pring S I\<^esub> (ring_hom_to_IP_ring_hom \<phi> Q)"
  unfolding ring_hom_to_IP_ring_hom_def
proof
  fix m
  show " \<phi> ((P \<oplus>\<^bsub>Pring R I\<^esub> Q) m) = ((\<lambda>m. \<phi> (P m)) \<oplus>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (Q m))) m"
  proof-
    have RHS: "((\<lambda>m. \<phi> (P m)) \<oplus>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (Q m))) m = \<phi> (P m) \<oplus>\<^bsub>S\<^esub> \<phi> (Q m)"
      using ring.Pring_add[of  S I _ _ ] assms
      by (metis cring.axioms(1) ring.indexed_padd_def)
    have LHS: "\<phi> ((P \<oplus>\<^bsub>Pring R I\<^esub> Q) m) = \<phi> ((P m)\<oplus>\<^bsub>R\<^esub> (Q m))"
      by (metis Pring_add indexed_padd_def)
    then show ?thesis
      using assms unfolding ring_hom_ring_def
      using  ring_hom_add[of \<phi> R S "P m" "Q m"]
      by (metis Pring_carrier_coeff' RHS assms(2) ring_hom_ring.homh)
  qed
qed

lemma ring_hom_to_IP_ring_hom_closed:
  assumes "cring S"
  assumes "ring_hom_ring R S \<phi>"
  assumes "P \<in> carrier (Pring R I)"
  shows "ring_hom_to_IP_ring_hom \<phi> P \<in> carrier (Pring S I)"
  apply(rule indexed_pset.induct[of P I "carrier R"])
  using Pring_car assms(3) apply blast
proof-
  show "\<And>k. k \<in> carrier R \<Longrightarrow> ring_hom_to_IP_ring_hom \<phi> (indexed_const k) \<in> carrier (Pring S I)"
  proof-
    fix k
    show " k \<in> carrier R \<Longrightarrow> ring_hom_to_IP_ring_hom \<phi> (indexed_const k) \<in> carrier (Pring S I)"
    proof-
      assume A: "k \<in> carrier R"
      have "(\<phi> k) \<in> carrier S"
        by (meson A assms(2) ring_hom_closed ring_hom_ring.homh)
      then have 0: "ring.indexed_const S (\<phi> k) \<in> carrier (Pring S I)"
        by (metis assms(1) cring.axioms(1) ring.Pring_car ring.indexed_pset.indexed_const)
      then show ?thesis
        using  assms(2)
        by (simp add: "0" A ring_hom_to_IP_ring_hom_constant[of S \<phi> k] assms(1))
    qed
  qed
  show "\<And>P Q. P \<in> Pring_set R I \<Longrightarrow>
           ring_hom_to_IP_ring_hom \<phi> P \<in> carrier (Pring S I) \<Longrightarrow>
           Q \<in> Pring_set R I \<Longrightarrow>
           ring_hom_to_IP_ring_hom \<phi> Q \<in> carrier (Pring S I) \<Longrightarrow> ring_hom_to_IP_ring_hom \<phi> (P \<Oplus> Q) \<in> carrier (Pring S I)"
    using ring_hom_to_IP_ring_hom_add[of S \<phi> _ I] Pring_car[of I] ring.Pring_car[of S I]
    by (metis Pring_add assms(1) assms(2) cring.axioms(1) ring.Pring_add_closed )
  show "\<And>P i. P \<in> Pring_set R I \<Longrightarrow>
           ring_hom_to_IP_ring_hom \<phi> P \<in> carrier (Pring S I) \<Longrightarrow> i \<in> I \<Longrightarrow> ring_hom_to_IP_ring_hom \<phi> (P \<Otimes> i) \<in> carrier (Pring S I)"
  proof-
    fix P
    fix i
    assume A: "P \<in> Pring_set R I " "ring_hom_to_IP_ring_hom \<phi> P \<in> carrier (Pring S I) " "i \<in> I"
    have 0: "(\<lambda>m. \<phi> ((P \<Otimes> i) m)) = ring.indexed_pmult S (ring_hom_to_IP_ring_hom \<phi> P) i"
    proof
      fix m
      show "\<phi> ((P \<Otimes> i) m) = ring.indexed_pmult S (ring_hom_to_IP_ring_hom \<phi> P) i m"
      proof(cases "i \<in># m")
        case True
        then have LHS: "\<phi> ((P \<Otimes> i) m) = \<phi>  (P (m - {#i#}))"
          by (metis indexed_pmult_def)
        then show ?thesis
          using True
          by (metis assms(1) cring.axioms(1) ring.indexed_pmult_def ring_hom_to_IP_ring_hom_def)
      next
        case False
        then have "\<phi> ((P \<Otimes> i) m) = \<phi> \<zero>\<^bsub>R\<^esub>"
          by (metis indexed_pmult_def)
        then have LHS: "\<phi> ((P \<Otimes> i) m) = \<zero>\<^bsub>S\<^esub>"
          by (metis assms(1) assms(2) cring.axioms(1) local.ring_axioms
              ring_hom_ring.homh ring_hom_zero)
        then show ?thesis
          using False assms ring.indexed_pmult_def
          by (metis cring.axioms(1))
      qed
    qed
    then show "ring_hom_to_IP_ring_hom \<phi> (P \<Otimes> i) \<in> carrier (Pring S I)"
      using assms
      unfolding ring_hom_to_IP_ring_hom_def
      by (metis "0" A(2) A(3) cring.axioms(1) ring.Pring_car ring.indexed_pset.simps)
  qed
qed

lemma ring_hom_to_IP_ring_hom_monom:
  assumes "cring S"
  assumes "ring_hom_ring R S \<phi>"
  shows "ring_hom_to_IP_ring_hom \<phi> (mset_to_IP R m) = mset_to_IP S m"
proof
  fix x
  show "ring_hom_to_IP_ring_hom \<phi> (mset_to_IP R m) x = mset_to_IP S m x"
    unfolding ring_hom_to_IP_ring_hom_def mset_to_IP_def apply( cases "x = m" )
     apply (metis (mono_tags, lifting) assms(2) ring_hom_one ring_hom_ring.homh)
    by (metis (full_types) assms(1) assms(2) cring.axioms(1) local.ring_axioms
        ring_hom_ring.homh ring_hom_zero)
qed

lemma Pring_morphism:
  assumes "cring S"
  assumes "\<phi> \<in> (carrier (Pring R I)) \<rightarrow> (carrier S)"
  assumes "\<phi> \<one>\<^bsub>Pring R I\<^esub> = \<one>\<^bsub>S\<^esub>"
  assumes "\<phi> \<zero>\<^bsub>Pring R I\<^esub> = \<zero>\<^bsub>S\<^esub>"
  assumes "\<And>P Q. P \<in> carrier (Pring R I) \<Longrightarrow> Q \<in> carrier (Pring R I) \<Longrightarrow>
          \<phi> (P \<oplus>\<^bsub>Pring R I\<^esub> Q) = (\<phi> P) \<oplus>\<^bsub>S\<^esub> (\<phi> Q)"
  assumes "\<And> i . \<And> P. i \<in> I \<Longrightarrow> P \<in> carrier (Pring R I) \<Longrightarrow>  \<phi> (P \<Otimes> i) =  (\<phi> P) \<otimes>\<^bsub>S\<^esub> (\<phi> (mset_to_IP R {#i#}))"
  assumes "\<And>k Q. k \<in> carrier R \<Longrightarrow> Q \<in> carrier (Pring R I) \<Longrightarrow>  \<phi> (poly_scalar_mult R k Q) =
                                     (\<phi> (indexed_const k)) \<otimes>\<^bsub>S\<^esub> (\<phi> Q)"
  shows "ring_hom_ring (Pring R I) S \<phi>"
  apply(rule ring_hom_ringI)
  apply (simp add: Pring_is_ring; fail)
  apply (simp add: assms(1) cring.axioms(1); fail)
  using assms(2) apply blast
proof-

  show "\<And>x y. x \<in> carrier (Pring R I) \<Longrightarrow> y \<in> carrier (Pring R I) \<Longrightarrow> \<phi> (x \<otimes>\<^bsub>Pring R I\<^esub> y) = \<phi> x \<otimes>\<^bsub>S\<^esub> \<phi> y"
  proof-
    fix P Q
    assume A0: "P \<in> carrier (Pring R I)"
    assume A1: "Q \<in> carrier (Pring R I)"
    show "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> Q"
    proof(rule mpoly_induct'[of ])
      show "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> indexed_const \<zero>) = \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> (indexed_const \<zero>)"
      proof-
        have 0: "(P \<otimes>\<^bsub>Pring R I\<^esub> indexed_const \<zero>) = \<zero>\<^bsub>Pring R I\<^esub>"
          using assms
          by (metis A0 Pring_is_cring Pring_zero cring.cring_simprules(27) is_cring)
        have 1: " \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> (indexed_const \<zero>) = \<zero>\<^bsub>S\<^esub>"
        proof-
          have "\<phi> P \<in> carrier S"
            using assms(2) A0
            by blast
          then show ?thesis
            using assms(4) Pring_zero[of I]
            by (metis assms(1) cring.cring_simprules(27))
        qed
        then show ?thesis using 0 1
          using assms(4) by presburger
      qed
      show "\<And>n Q. (\<And>Q. Q \<in> Pring_set R I \<and> card (monomials_of R Q) \<le> n \<Longrightarrow> \<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> Q) \<Longrightarrow>
           Q \<in> Pring_set R I \<and> card (monomials_of R Q) = Suc n \<Longrightarrow> \<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> Q"
      proof- fix n fix Q
        assume IH: " (\<And>Q. Q \<in> Pring_set R I \<and> card (monomials_of R Q) \<le> n \<Longrightarrow> \<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> Q)"
        assume A: "Q \<in> Pring_set R I \<and> card (monomials_of R Q) = Suc n"
        show "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> Q"
        proof-
          obtain m M where m_M_def: "monomials_of R Q = insert m M \<and> m \<notin> M"
            using A
            by (metis card_0_eq ex_in_conv finite.emptyI mk_disjoint_insert nat.distinct(1))
          have "Q = (restrict_poly_to_monom_set R Q M) \<oplus>\<^bsub>Pring R I\<^esub> (poly_scalar_mult R (Q m) (mset_to_IP R m))"
            by (metis A Pring_add m_M_def remove_monom_eq remove_monom_restrict_poly_to_monom_set)
          obtain Q' where Q'_def: "Q' = (restrict_poly_to_monom_set R Q M)"
            by simp
          have Q'_fact: " Q' \<in> Pring_set R I \<and> card (monomials_of R Q') \<le> n"
            proof-
              have 0: "Q' \<in> Pring_set R I"
                using Q'_def  A restriction_closed
                by blast
              have "monomials_of R Q' = M"
                using A m_M_def Q'_def
                by (metis restrict_poly_to_monom_set_monoms subset_insertI)
              then have "card (monomials_of R Q') = n" using A m_M_def
                by (metis "0" card_insert_disjoint diff_Suc_1 monomials_finite)
              then show ?thesis
                by (simp add: "0")
            qed
          have 0:"(P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (P \<otimes>\<^bsub>Pring R I\<^esub> (Q' \<oplus>\<^bsub>Pring R I\<^esub> (poly_scalar_mult R (Q m) (mset_to_IP R m))))"
            using Q'_def \<open>Q = restrict_poly_to_monom_set R Q M \<oplus>\<^bsub>Pring R I\<^esub> Mt (Q m) m\<close> by presburger
          have 1: "(P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (P \<otimes>\<^bsub>Pring R I\<^esub> Q') \<oplus>\<^bsub>Pring R I\<^esub> (P \<otimes>\<^bsub>Pring R I\<^esub> (poly_scalar_mult R (Q m) (mset_to_IP R m)))"
          proof-
            have 10: "P \<in> carrier (Pring R I)"
              by (simp add: A0)
            have 11: "Q \<in> carrier (Pring R I)"
              by (simp add: A Pring_car)
            have 12: "Q' \<in> carrier (Pring R I)"
              using A Pring_car Q'_def restriction_closed by blast
            have 13: "(poly_scalar_mult R (Q m) (mset_to_IP R m)) \<in> carrier (Pring R I)"
              by (metis A Pring_car Pring_carrier_coeff' insert_iff m_M_def mset_to_IP_closed' poly_scalar_mult_closed)
            then show ?thesis
              using 0 10 11 12 13
              by (metis Pring_mult_rdistr)
          qed
          then have "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q')) \<oplus>\<^bsub>S\<^esub> \<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> (poly_scalar_mult R (Q m) (mset_to_IP R m)))"
            by (metis A A0 Pring_car Pring_mult_closed Pring_cfs_closed Q'_def assms(5) insert_iff
                local.ring_axioms m_M_def poly_scalar_mult_closed ring.mset_to_IP_closed'
                ring.restriction_closed)
          then have "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (\<phi> P) \<otimes>\<^bsub>S\<^esub> (\<phi> Q') \<oplus>\<^bsub>S\<^esub> \<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> (poly_scalar_mult R (Q m) (mset_to_IP R m)))"
            using IH[of Q'] Q'_fact
            by presburger
          then have 2: "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (\<phi> P) \<otimes>\<^bsub>S\<^esub> (\<phi> Q') \<oplus>\<^bsub>S\<^esub> \<phi> (poly_scalar_mult R (Q m) (P \<otimes>\<^bsub>Pring R I\<^esub>  (mset_to_IP R m)))"
            by (metis A A0 Pring_car Pring_mult Pring_cfs_closed insert_iff m_M_def mset_to_IP_closed' times_poly_scalar_mult)
          have 3: "\<And>k. k \<in> carrier R \<Longrightarrow> set_mset m \<subseteq> I \<Longrightarrow> \<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub>  (mset_to_IP R m))) =
                    \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> (\<phi> P) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m)"
          proof(induction m)
            case empty
            assume A: "set_mset {#} \<subseteq> I"
            then have E0: "(P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#}) = P"
              by (metis A0 Pring_mult_one Pring_one one_mset_to_IP)
            have E1: "k \<in> carrier R"
              using A Pring_cfs_closed empty.prems(1)
              by linarith
            have E2: "\<phi> (mset_to_IP R {#}) = \<one>\<^bsub>S\<^esub>"
              by (metis Pring_one assms(3) one_mset_to_IP)
            have E3: " \<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#})) =
                       \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#})"
              using E1 E2 E0 assms(7)[of "k" "P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#}"]  A0
              by (simp add: A0 E1)
            have E4: " \<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#}) =  (\<phi> P) "
              using E0
              by auto
            have E5: " \<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#})) =
                       \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P"
              using E0 E3 by presburger
            have E6: " \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P =  \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P \<otimes>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>"
            proof-
              have 0: "\<phi> P \<in> carrier S"
                using assms A0
                by blast
              have "indexed_const k \<in> carrier (Pring R I)"
                using assms(2) E1 Pring_car indexed_pset.indexed_const
                by blast
              then have 1: "\<phi> (indexed_const k) \<in> carrier S"
                using assms(2)
                by blast
              show ?thesis
                using assms(1) 0 1
                by (metis cring.cring_simprules(12) cring.cring_simprules(14)
                    cring.cring_simprules(5) cring.cring_simprules(6))
            qed
            then show ?case
              using E0 E2 E3 by presburger
          next
            case (add x m)
            assume AA: "\<And>k. k \<in> carrier R \<Longrightarrow> set_mset m \<subseteq> I \<Longrightarrow> \<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R m)) = \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m)"
            assume P0: "set_mset (add_mset x m) \<subseteq> I"
            then have IA: "set_mset m \<subseteq>I"
              by (metis insert_subset set_mset_add_mset_insert)
            have IH: "\<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R m)) =
                        \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m)"
              using AA IA add.prems(1)
              by blast
            then have x_mem: "x \<in> I"
              by (meson P0 subsetD union_single_eq_member)
            have 0: " mset_to_IP R (add_mset x m) =  mset_to_IP R m \<Otimes> x"
              by (simp add: monom_add_mset)
            then have 1: "P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m) = P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m \<Otimes> x)"
              by simp
            have 2: "P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m) =( P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m)) \<Otimes> x"
            proof-
              have "mset_to_IP R (add_mset x m) = (mset_to_IP R m) \<Otimes> x"
                using "0" by blast
              then have "P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m) = P \<otimes>\<^bsub>Pring R I\<^esub> ((mset_to_IP R m) \<Otimes> x)"
                by simp
              then have "P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m) = P \<otimes>\<^bsub>Pring R I\<^esub> ((mset_to_IP R m) \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#x#})"
                by (metis IA Pring_mult mset_to_IP_closed poly_index_mult x_mem)
              then have "P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m) = (P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m)) \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#x#}"
                by (metis A0 IA Pring_car Pring_mult_assoc Pring_one Pring_one_closed
                    indexed_pset.indexed_pmult monom_add_mset mset_to_IP_closed one_mset_to_IP x_mem)
              then show ?thesis
                by (metis A0 IA Pring_car Pring_mult Pring_mult_closed mset_to_IP_closed poly_index_mult x_mem)
            qed
            have 3: "poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m)) =
                      poly_scalar_mult R k ( P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m) \<Otimes> x)"
              using "2" by presburger
            have 4: "poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m)) =
                      poly_scalar_mult R k ( P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m)) \<Otimes> x"
            proof-
              have "poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m)) =
                      poly_scalar_mult R k ( P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m) \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#x#})"
                by (metis "2" A0 IA Pring_car Pring_mult Pring_mult_closed mset_to_IP_closed poly_index_mult x_mem)
              have "poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m)) =
                      (poly_scalar_mult R k ( P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R m)) \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#x#}"
                by (metis A0 IA Pring_car Pring_mult Pring_mult_closed Pring_one Pring_one_closed
                    \<open>poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m)) = poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R m \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R {#x#})\<close>
                    add.prems(1) indexed_pset.indexed_pmult monom_add_mset mset_to_IP_closed
                    one_mset_to_IP poly_scalar_mult_times x_mem)
              then show ?thesis
                by (metis A0 IA Pring_car Pring_mult Pring_mult_closed add.prems(1)
                    cring.poly_scalar_mult_closed is_cring mset_to_IP_closed
                    poly_index_mult x_mem)
            qed
            have 5: "\<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m))) =
                      \<phi> (poly_scalar_mult R k ( P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m)) \<Otimes> x)"
              using 4 by metis
            have 6: "\<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m))) =
                      \<phi> (poly_scalar_mult R k ( P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R m))) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP  R {#x#})"
              using assms
              by (metis "5" A0 IA Pring_car Pring_mult_closed add.prems(1)
                  cring.poly_scalar_mult_closed is_cring mset_to_IP_closed x_mem)
            have 7: "\<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m))) =
                       \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP  R {#x#})"
              using assms 6 IH
              by presburger
            have 8: " \<phi> (mset_to_IP R m) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP  R {#x#}) = \<phi> (mset_to_IP R (add_mset x m))"
            proof-
              have "\<phi> (mset_to_IP R m) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP  R {#x#}) =
                    \<phi> ((mset_to_IP R m) \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP  R {#x#}))"
                by (metis IA Pring_car Pring_mult assms(6) mset_to_IP_closed poly_index_mult x_mem)
              then show ?thesis
                by (metis "0" IA Pring_car assms(6) mset_to_IP_closed x_mem)
            qed
            have 9: "\<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m))) =
             \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P \<otimes>\<^bsub>S\<^esub> ( \<phi> (mset_to_IP R m) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP  R {#x#}))"
            proof-
              have 0: "\<phi> (indexed_const k) \<in> carrier S"
              proof-
                have "(indexed_const k) \<in> carrier (Pring R I)"
                  using A Pring_car Pring_cfs_closed indexed_pset.indexed_const add.prems(1)
                  by blast
                then show ?thesis
                  using assms(2)
                  by blast
              qed
              have 1: "\<phi> P \<in> carrier S"
                using A0 assms(2)
                by blast
              have 2: "\<phi> (mset_to_IP R m) \<in> carrier S"
              proof-
                have "(mset_to_IP R m) \<in> carrier (Pring R I)"
                  using IA Pring_car mset_to_IP_closed by blast
                then show ?thesis using assms(2)
                  by blast
              qed
              have 3: " \<phi> (mset_to_IP  R {#x#}) \<in> carrier S"
              proof-
                have "(mset_to_IP  R {#x#}) \<in> carrier (Pring R I)"
                  by (metis Pring_car Pring_one Pring_one_closed indexed_pset.indexed_pmult
                      monom_add_mset one_mset_to_IP x_mem)
                then show ?thesis
                  using assms(2)
                  by blast
              qed
              have "\<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m))) =
                  \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> (\<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP  R {#x#}))"
                using 1 2 3 7
                by (metis "0" \<open>\<phi> (mset_to_IP R m) \<in> carrier S\<close> assms(1)
                    cring.cring_simprules(11) cring.cring_simprules(5))
              then show ?thesis
                by (metis "0" "1" "2" "3" "8" Pring_mult assms(1) cring.cring_simprules(11)
                    cring.cring_simprules(5))
            qed
            have 10: "\<phi> (poly_scalar_mult R k (P \<otimes>\<^bsub>Pring R I\<^esub> mset_to_IP R (add_mset x m))) =
             \<phi> (indexed_const k) \<otimes>\<^bsub>S\<^esub> \<phi> P \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R (add_mset x m))"
              using 8 9
              by presburger
            then show ?case
              by blast
          qed
          have 4: "\<phi> (poly_scalar_mult R (Q m) (P \<otimes>\<^bsub>Pring R I\<^esub>  (mset_to_IP R m))) =
                    \<phi> (indexed_const (Q m)) \<otimes>\<^bsub>S\<^esub> (\<phi> P) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m)"
            using 3
            by (metis A Pring_mult insert_iff local.ring_axioms m_M_def mset_to_IP_indices
                ring.Pring_cfs_closed)
          have 5: "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (\<phi> P) \<otimes>\<^bsub>S\<^esub> (\<phi> Q') \<oplus>\<^bsub>S\<^esub> \<phi> (indexed_const (Q m)) \<otimes>\<^bsub>S\<^esub> (\<phi> P) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m)"
            using 2 4
            by presburger
          have " \<phi> (indexed_const (Q m)) \<otimes>\<^bsub>S\<^esub> (\<phi> P) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m) =
                    (\<phi> P) \<otimes>\<^bsub>S\<^esub> \<phi> (indexed_const (Q m)) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m)"
          proof-
            have 0: "(\<phi> P)  \<in> carrier S"
              using A0 assms(2)
              by blast
            have 1: "\<phi> (indexed_const (Q m)) \<in> carrier S"
            proof-
              have "indexed_const (Q m ) \<in> carrier (Pring R I)"
                using A Pring_car Pring_cfs_closed indexed_pset.indexed_const by blast
              then show ?thesis
                using assms(2)
                by blast
            qed
            have 2: "\<phi> (mset_to_IP R m) \<in> carrier S"
            proof-
              have "(mset_to_IP R m) \<in> carrier (Pring R I)"
                by (metis A Pring_car insert_iff m_M_def mset_to_IP_closed')
              then show ?thesis using assms(2)
                by blast
            qed
            show ?thesis using assms(1) 0 1 2
              by (metis cring.cring_simprules(14))
          qed
          then  have 6: "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (\<phi> P) \<otimes>\<^bsub>S\<^esub> (\<phi> Q') \<oplus>\<^bsub>S\<^esub>  (\<phi> P) \<otimes>\<^bsub>S\<^esub> \<phi> (indexed_const (Q m)) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m)"
            using 5
            by presburger
          then have 7: "\<phi> (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = (\<phi> P) \<otimes>\<^bsub>S\<^esub> ((\<phi> Q') \<oplus>\<^bsub>S\<^esub>  \<phi> (indexed_const (Q m)) \<otimes>\<^bsub>S\<^esub> \<phi> (mset_to_IP R m))"
          proof-
            have 0: "(\<phi> P)  \<in> carrier S"
              using A0 assms(2)
              by blast
            have 1: "\<phi> (indexed_const (Q m)) \<in> carrier S"
            proof-
              have "indexed_const (Q m ) \<in> carrier (Pring R I)"
                using A Pring_car Pring_cfs_closed indexed_pset.indexed_const by blast
              then show ?thesis
                using assms(2)
                by blast
            qed
            have 2: "\<phi> (mset_to_IP R m) \<in> carrier S"
            proof-
              have "(mset_to_IP R m) \<in> carrier (Pring R I)"
                by (metis A Pring_car insert_iff m_M_def mset_to_IP_closed')
              then show ?thesis using assms(2)
                by blast
            qed
            have 3: "\<phi> Q' \<in> carrier S"
            proof-
              have "Q' \<in> carrier (Pring R I)"
                using Q'_fact Pring_car
                by blast
              then show ?thesis
                using assms(2)
                by blast
            qed
            show ?thesis using 0 1 2 3 6
              by (metis assms(1) cring.cring_simprules(11) cring.cring_simprules(25) cring.cring_simprules(5))
          qed
          then show ?thesis
            by (metis A Pring_car Pring_cfs_closed Q'_def Q'_fact
                \<open>Q = restrict_poly_to_monom_set R Q M \<oplus>\<^bsub>Pring R I\<^esub> Mt (Q m) m\<close> assms(5) assms(7)
                cring.poly_scalar_mult_closed insert_iff is_cring m_M_def mset_to_IP_closed')
        qed
      qed
      show "Q \<in> Pring_set R I "
        using A1 Pring_car
        by blast
    qed
  qed
  show "\<And>x y. x \<in> carrier (Pring R I) \<Longrightarrow> y \<in> carrier (Pring R I) \<Longrightarrow> \<phi> (x \<oplus>\<^bsub>Pring R I\<^esub> y) = \<phi> x \<oplus>\<^bsub>S\<^esub> \<phi> y"
    using assms(5)
    by blast
  show "\<phi> \<one>\<^bsub>Pring R I\<^esub> = \<one>\<^bsub>S\<^esub>"
    by (simp add: assms(3))
qed

lemma(in cring) indexed_const_Pring_mult:
  assumes "k \<in> carrier R"
  assumes "P \<in> carrier (Pring R I)"
  shows "(indexed_const k \<otimes>\<^bsub>Pring R I\<^esub> P) m = k \<otimes>\<^bsub>R\<^esub> (P m)"
        "(P \<otimes>\<^bsub>Pring R I\<^esub> indexed_const k) m = k \<otimes>\<^bsub>R\<^esub> (P m)"
  apply (metis Pring_car Pring_mult assms(1) assms(2) poly_scalar_mult_def poly_scalar_mult_eq)
  by (metis Pring_car Pring_carrier_coeff' Pring_mult assms(1) assms(2) indexed_const_P_multE m_comm)

lemma(in cring) ring_hom_to_IP_ring_hom_is_hom:
  assumes "cring S"
  assumes "ring_hom_ring R S \<phi>"
  shows "ring_hom_ring (Pring R I) (Pring S I) (ring_hom_to_IP_ring_hom \<phi>)"
proof(rule Pring_morphism)
  show 0: "cring (Pring S I)"
    by (simp add: assms(1) cring.axioms(1) ring.Pring_is_cring)
  show 1: "ring_hom_to_IP_ring_hom \<phi> \<in> carrier (Pring R I) \<rightarrow> carrier (Pring S I)"
    by (meson Pi_I assms(1) assms(2) ring_hom_to_IP_ring_hom_closed)
  show 2: "ring_hom_to_IP_ring_hom \<phi> \<one>\<^bsub>Pring R I\<^esub> = \<one>\<^bsub>Pring S I\<^esub>"
    by (simp add: assms(1) assms(2) ring_hom_to_IP_ring_hom_one)
  show 3: "ring_hom_to_IP_ring_hom \<phi> \<zero>\<^bsub>Pring R I\<^esub> = \<zero>\<^bsub>Pring S I\<^esub>"
  proof-
    have "\<And>m. \<phi> (\<zero>\<^bsub>Pring R I\<^esub> m) = \<zero>\<^bsub>S\<^esub>"
      using assms
      by (metis Pring_carrier_coeff' Pring_zero Pring_zero_closed cring.axioms(1)
          cring.cring_simprules(26) indexed_const_Pring_mult(2) is_cring ring.Pring_is_cring
          ring_hom_ring.homh ring_hom_zero zero_closed)
    then have "\<And>m. \<phi> (\<zero>\<^bsub>Pring R I\<^esub> m) = \<zero>\<^bsub>Pring S I\<^esub> m"
      by (metis assms(1) cring.axioms(1) ring.Pring_zero ring.indexed_const_def)
    then show ?thesis unfolding ring_hom_to_IP_ring_hom_def
      by blast
  qed
  show 4: " \<And>P Q. P \<in> carrier (Pring R I) \<Longrightarrow>
           Q \<in> carrier (Pring R I) \<Longrightarrow> ring_hom_to_IP_ring_hom \<phi> (P \<oplus>\<^bsub>Pring R I\<^esub> Q) = ring_hom_to_IP_ring_hom \<phi> P \<oplus>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> Q"
    using assms(1) assms(2) ring_hom_to_IP_ring_hom_add by blast
  show 5: " \<And>i P. i \<in> I \<Longrightarrow>
           P \<in> carrier (Pring R I) \<Longrightarrow>
           ring_hom_to_IP_ring_hom \<phi> (P \<Otimes> i) = ring_hom_to_IP_ring_hom \<phi> P \<otimes>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> (mset_to_IP R {#i#})"
  proof-
    fix i P
    assume i0: "i \<in> I"
    assume P0: "P \<in> carrier (Pring R I)"
    show  "ring_hom_to_IP_ring_hom \<phi> (P \<Otimes> i) = ring_hom_to_IP_ring_hom \<phi> P \<otimes>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> (mset_to_IP R {#i#})"
      unfolding ring_hom_to_IP_ring_hom_def
    proof
      fix m
      show " \<phi> ((P \<Otimes> i) m) = ((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (mset_to_IP R {#i#} m))) m"
      proof(cases "i \<in># m")
        case True
        have "(\<lambda>m. \<phi> (mset_to_IP R {#i#} m)) = mset_to_IP S {#i#}"
        proof
          fix m
          show "\<phi> (mset_to_IP R {#i#} m) = mset_to_IP S {#i#} m"
            apply(cases "{#i#} = m")
             apply (metis (mono_tags, lifting) assms(1) assms(2) cring.axioms(1) local.ring_axioms
                mset_to_IP_def one_mset_to_IP ring.Pring_one ring.Pring_one ring.one_mset_to_IP
                ring_hom_to_IP_ring_hom_def ring_hom_to_IP_ring_hom_one)
          proof-
            assume "{#i#} \<noteq> m"
            then have LHS: "(mset_to_IP R {#i#} m) = \<zero>\<^bsub>R\<^esub>"
              by (metis mset_to_IP_simp')
            have  RHS :"mset_to_IP S {#i#} m = \<zero>\<^bsub>S\<^esub>"
              by (metis \<open>{#i#} \<noteq> m\<close> mset_to_IP_def)
            have "\<phi> \<zero>\<^bsub>R\<^esub> = \<zero>\<^bsub>S\<^esub>"
              using assms(1) assms(2) cring.axioms(1) local.ring_axioms
                ring_hom_ring.homh ring_hom_zero by blast
            then show ?thesis
              using  LHS RHS
              by presburger
          qed
        qed
        then have RHS: "((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (mset_to_IP R {#i#} m))) m =
              ((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> mset_to_IP S {#i#}) m"
          by presburger
        then have RHS': "((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (mset_to_IP R {#i#} m))) m =
              (ring.indexed_pmult S (\<lambda>m. \<phi> (P m)) i) m"
        proof-
          have 0: "(\<lambda>m. \<phi> (P m)) \<in> Pring_set S I"
            using ring_hom_to_IP_ring_hom_closed[of S \<phi> P I] ring.Pring_car[of S I] assms
            unfolding ring_hom_to_IP_ring_hom_def
            using P0 cring.axioms(1) by blast
          show ?thesis using ring.poly_index_mult[of S "(\<lambda>m. \<phi> (P m))" I i]
            by (metis "0" \<open>(\<lambda>m. \<phi> (mset_to_IP R {#i#} m)) = mset_to_IP S {#i#}\<close>
                assms(1) cring.axioms(1) i0 ring.Pring_mult)
        qed
        then have RHS'': "((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (mset_to_IP R {#i#} m))) m =
            (\<lambda>m. \<phi> (P m)) (m - {#i#})" using ring.indexed_pmult_def[of S "(\<lambda>m. \<phi> (P m))" i] True
          by (metis assms(1) cring.axioms(1))
        then show ?thesis
          by (metis True indexed_pmult_def)
      next
        case False
        have LHS: "((P \<Otimes> i) m) = \<zero>\<^bsub>R\<^esub>"
          using False
          by (meson indexed_pmult_def)
        have "(\<lambda>m. \<phi> (mset_to_IP R {#i#} m)) = mset_to_IP S {#i#}"
        proof
          fix m
          show "\<phi> (mset_to_IP R {#i#} m) = mset_to_IP S {#i#} m"
            apply(cases "{#i#} = m")
             apply (metis (mono_tags, lifting) assms(1) assms(2) cring.axioms(1) local.ring_axioms
                mset_to_IP_def one_mset_to_IP ring.Pring_one ring.Pring_one ring.one_mset_to_IP
                ring_hom_to_IP_ring_hom_def ring_hom_to_IP_ring_hom_one)
          proof-
            assume "{#i#} \<noteq> m"
            then have LHS: "(mset_to_IP R {#i#} m) = \<zero>\<^bsub>R\<^esub>"
              by (metis mset_to_IP_simp')
            have  RHS :"mset_to_IP S {#i#} m = \<zero>\<^bsub>S\<^esub>"
              by (metis \<open>{#i#} \<noteq> m\<close> mset_to_IP_def)
            have "\<phi> \<zero>\<^bsub>R\<^esub> = \<zero>\<^bsub>S\<^esub>"
              using assms(1) assms(2) cring.axioms(1) local.ring_axioms
                ring_hom_ring.homh ring_hom_zero by blast
            then show ?thesis
              using  LHS RHS
              by presburger
          qed
        qed
        then have RHS: "((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (mset_to_IP R {#i#} m))) m =
              ((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> mset_to_IP S {#i#}) m"
          by presburger
        then have RHS': "((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (mset_to_IP R {#i#} m))) m =
              (ring.indexed_pmult S (\<lambda>m. \<phi> (P m)) i) m"
        proof-
          have 0: "(\<lambda>m. \<phi> (P m)) \<in> Pring_set S I"
            using ring_hom_to_IP_ring_hom_closed[of S \<phi> P I] ring.Pring_car[of S I] assms
            unfolding ring_hom_to_IP_ring_hom_def
            using P0 cring.axioms(1) by blast
          show ?thesis using ring.poly_index_mult[of S "(\<lambda>m. \<phi> (P m))" I i]
            by (metis "0" \<open>(\<lambda>m. \<phi> (mset_to_IP R {#i#} m)) = mset_to_IP S {#i#}\<close>
                assms(1) cring.axioms(1) i0 ring.Pring_mult)
        qed
        then have RHS'': "((\<lambda>m. \<phi> (P m)) \<otimes>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (mset_to_IP R {#i#} m))) m =
              \<zero>\<^bsub>S\<^esub>"
          using False
          by (metis assms(1) cring.axioms(1) ring.indexed_pmult_def)
        then show ?thesis
          using LHS False assms ring_hom_zero[of \<phi> R S]
          by (metis cring.axioms(1) local.ring_axioms ring_hom_ring.homh)
      qed
    qed
  qed
  show "\<And>k Q. k \<in> carrier R \<Longrightarrow>
           Q \<in> carrier (Pring R I) \<Longrightarrow>
           ring_hom_to_IP_ring_hom \<phi> (poly_scalar_mult R k Q) = ring_hom_to_IP_ring_hom \<phi> (indexed_const k) \<otimes>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> Q"
  proof-
    fix k Q
    assume A0: "k \<in> carrier R"
    assume A1: " Q \<in> carrier (Pring R I)"
    show "ring_hom_to_IP_ring_hom \<phi> (poly_scalar_mult R k Q) =
          ring_hom_to_IP_ring_hom \<phi> (indexed_const k) \<otimes>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> Q"
    proof
      fix x
      show "ring_hom_to_IP_ring_hom \<phi> (poly_scalar_mult R k Q) x = (ring_hom_to_IP_ring_hom \<phi> (indexed_const k) \<otimes>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> Q) x"
      proof-
        have LHS: "ring_hom_to_IP_ring_hom \<phi> (poly_scalar_mult R k Q) x = \<phi> (k \<otimes>\<^bsub>R\<^esub> Q x)"
          by (metis poly_scalar_mult_def ring_hom_to_IP_ring_hom_def)
        then have LHS': "ring_hom_to_IP_ring_hom \<phi> (poly_scalar_mult R k Q) x = (\<phi> k) \<otimes>\<^bsub>S\<^esub> \<phi> (Q x)"
        proof-
          have "Q x \<in> carrier  R"
            using A1 Pring_car local.ring_axioms ring.Pring_cfs_closed by blast
          then show ?thesis
            using LHS assms ring_hom_mult[of \<phi> R S k "Q x"]
            by (metis A0 ring_hom_ring.homh)
        qed
        have RHS: "(ring_hom_to_IP_ring_hom \<phi> (indexed_const k) \<otimes>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> Q) x =
               (\<phi> k) \<otimes>\<^bsub>S\<^esub> (\<phi> (Q x))"
        proof-
          have 0: "ring_hom_to_IP_ring_hom \<phi> (indexed_const k)= ring.indexed_const S (\<phi> k)"
            by (simp add: A0 assms(1) assms(2) ring_hom_to_IP_ring_hom_constant)
          have 1: "(\<phi> k) \<in> carrier S"
            by (meson A0 assms(2) ring_hom_closed ring_hom_ring.homh)
          have 2: "ring_hom_to_IP_ring_hom \<phi> Q \<in> carrier (Pring S I)"
            using A1 assms ring_hom_to_IP_ring_hom_closed
            by blast
          have 3: "(ring.indexed_const S (\<phi> k) \<otimes>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> Q) x = (\<phi> k) \<otimes>\<^bsub>S\<^esub> (\<phi> (Q x))"
            using assms(1) 1 2
                 cring.indexed_const_Pring_mult(1)[of S "\<phi> k" "ring_hom_to_IP_ring_hom \<phi> Q" I x]
                 ring_hom_to_IP_ring_hom_def[of \<phi> Q x]
            by presburger
          then show ?thesis
            by (metis "0")
        qed
        then show ?thesis
          using LHS'
          by metis
      qed
    qed
  qed
qed

lemma ring_hom_to_IP_ring_hom_smult:
  assumes "cring S"
  assumes "ring_hom_ring R S \<phi>"
  assumes "P \<in> carrier (Pring R I)"
  assumes "a \<in> carrier R"
  shows "ring_hom_to_IP_ring_hom \<phi> (a \<odot>\<^bsub>Pring R I\<^esub>P) =
                 \<phi> a \<odot>\<^bsub>Pring S I\<^esub> (ring_hom_to_IP_ring_hom \<phi> P)"
proof fix m
  have 0: "\<phi> ((a \<odot>\<^bsub>Pring R I\<^esub> P) m) = \<phi> (a \<otimes> (P m))"
    using assms
    by (metis Pring_smult_cfs)
  hence 1: "\<phi> ((a \<odot>\<^bsub>Pring R I\<^esub> P) m) = \<phi> a \<otimes>\<^bsub>S\<^esub> \<phi> (P m)"
    using assms ring_hom_mult[of \<phi> R S]
    by (metis Pring_carrier_coeff' ring_hom_ring.homh)
  have 2: "(\<phi> a \<odot>\<^bsub>Pring S I\<^esub> (\<lambda>m. \<phi> (P m))) m = \<phi> a \<otimes>\<^bsub>S\<^esub> \<phi> (P m)"
    using assms ring.Pring_smult[of S I]
    unfolding poly_scalar_mult_def cring_def
    by presburger
  show "ring_hom_to_IP_ring_hom \<phi> (a \<odot>\<^bsub>Pring R I\<^esub> P) m =
         (\<phi> a \<odot>\<^bsub>Pring S I\<^esub> ring_hom_to_IP_ring_hom \<phi> P) m"
    unfolding ring_hom_to_IP_ring_hom_def using assms 1 2
    by presburger
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>A Universal Property for Indexed Polynomial Rings\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma Pring_universal_prop_0:
  assumes a_cring: "cring S"
  assumes index_map: "closed_fun S g"
  assumes ring_hom: "ring_hom_ring R S \<phi>"
  assumes "\<psi> = (total_eval S g) \<circ> (ring_hom_to_IP_ring_hom \<phi>)"
  shows "(ring_hom_ring (Pring R I) S \<psi>)"
        "(\<forall>i \<in> I. \<psi> (mset_to_IP R {#i#}) = g i)"
        "(\<forall>a \<in> carrier R. \<psi> (indexed_const a) = \<phi> a)"
        "\<forall> \<rho>. (ring_hom_ring (Pring R I) S \<rho>) \<and>
          (\<forall>i \<in> I. \<rho> (mset_to_IP R {#i#}) = g i) \<and>
          (\<forall>a \<in> carrier R. \<rho> (indexed_const a) = \<phi> a) \<longrightarrow>
          (\<forall>x \<in> carrier (Pring R I). \<rho> x = \<psi> x)"
proof-
  have 0: " (ring_hom_to_IP_ring_hom \<phi>) \<in> ring_hom (Pring R I) (Pring S I)"
    using a_cring ring_hom ring_hom_ring.homh ring_hom_to_IP_ring_hom_is_hom
    by blast
  have 1: "(total_eval S g) \<in> ring_hom (Pring S I) S "
    using a_cring cring.total_eval_ring_hom index_map ring_hom_ring.homh
    by blast
  show P0: "ring_hom_ring (Pring R I) S \<psi> "
    using ring_hom_trans 0 1 Pring_is_ring a_cring assms(4) cring.axioms(1) ring_hom_ringI2
    by blast
  show P1: "\<forall>i\<in>I. \<psi> (mset_to_IP R {#i#}) = g i"
  proof
    fix i assume Pi: "i \<in> I"
    show "\<psi> (mset_to_IP R {#i#}) = g i"
    proof-
      have 0: "\<psi> (mset_to_IP R {#i#}) = (total_eval S g) ( (ring_hom_to_IP_ring_hom \<phi>) (mset_to_IP R {#i#}))"
        by (simp add: assms(4))
      have "( (ring_hom_to_IP_ring_hom \<phi>) (mset_to_IP R {#i#})) = (mset_to_IP S {#i#})"
        by (simp add: a_cring ring_hom ring_hom_to_IP_ring_hom_monom)
      then have "\<psi> (mset_to_IP R {#i#}) = (total_eval S g) (mset_to_IP S {#i#})"
        by (simp add: 0)
      then show ?thesis
        by (simp add: a_cring cring.total_eval_var index_map)
    qed
  qed
  show P2: "\<forall>a\<in>carrier R. \<psi> (indexed_const a) = \<phi> a"
  proof
    fix a assume A: "a \<in> carrier R"
    show "\<psi> (indexed_const a) = \<phi> a"
    proof-
      have 0: "ring_hom_to_IP_ring_hom \<phi> (indexed_const a) = ring.indexed_const S (\<phi> a)"
        by (simp add: A a_cring ring_hom ring_hom_to_IP_ring_hom_constant)
      have 1: "total_eval S g (ring.indexed_const S (\<phi> a)) = \<phi> a"
        by (meson A a_cring cring.total_eval_const ring_hom ring_hom_closed ring_hom_ring.homh)
      show ?thesis
        using assms 0 1
        by (simp add: "0" index_map)
    qed
  qed
  show "\<forall> \<rho>. (ring_hom_ring (Pring R I) S \<rho>) \<and>
          (\<forall>i \<in> I. \<rho> (mset_to_IP R {#i#}) = g i) \<and>
          (\<forall>a \<in> carrier R. \<rho> (indexed_const a) = \<phi> a) \<longrightarrow>
          (\<forall>x \<in> carrier (Pring R I). \<rho> x = \<psi> x)"
  proof
    fix \<rho>
    show "ring_hom_ring (Pring R I) S \<rho> \<and> (\<forall>i\<in>I. \<rho> (mset_to_IP R {#i#}) = g i) \<and> (\<forall>a\<in>carrier R. \<rho> (indexed_const a) = \<phi> a) \<longrightarrow>
         (\<forall>x\<in>carrier (Pring R I). \<rho> x = \<psi> x)"
    proof
        assume A: "(ring_hom_ring (Pring R I) S \<rho>) \<and>
          (\<forall>i \<in> I. \<rho> (mset_to_IP R {#i#}) = g i) \<and>
          (\<forall>a \<in> carrier R. \<rho> (indexed_const a) = \<phi> a)"
        show "(\<forall>x \<in> carrier (Pring R I). \<rho> x = \<psi> x)"
        proof
          fix x assume B: "x \<in> carrier (Pring R I)"
          show "\<rho> x = \<psi> x"
            apply(rule indexed_pset.induct[of x I "carrier R"])
            using B Pring_car apply blast
              apply (metis A P2)
          proof-
            show "\<And>P Q. P \<in> Pring_set R I \<Longrightarrow> \<rho> P = \<psi> P \<Longrightarrow> Q \<in> Pring_set R I \<Longrightarrow> \<rho> Q = \<psi> Q \<Longrightarrow> \<rho> (P \<Oplus> Q) = \<psi> (P \<Oplus> Q)"
            proof-
              fix P Q
              assume A0: "P \<in> Pring_set R I " "\<rho> P = \<psi> P" " Q \<in> Pring_set R I" " \<rho> Q = \<psi> Q "
              show "\<rho> (P \<Oplus> Q) = \<psi> (P \<Oplus> Q)"
                using A A0 ring_hom_add[of \<psi> "Pring R I" S P Q] ring_hom_add[of \<rho> "Pring R I" S P Q] P0
                by (metis Pring_add Pring_car ring_hom_ring.homh)
            qed
            show "\<And>P i. P \<in> Pring_set R I \<Longrightarrow> \<rho> P = \<psi> P \<Longrightarrow> i \<in> I \<Longrightarrow> \<rho> (P \<Otimes> i) = \<psi> (P \<Otimes> i)"
            proof-
              fix P i
              assume A0: " P \<in> Pring_set R I" " \<rho> P = \<psi> P" "i \<in> I"
              show "\<rho> (P \<Otimes> i) = \<psi> (P \<Otimes> i)"
              proof-
                have "\<rho> (P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R {#i#})) = \<psi> (P \<otimes>\<^bsub>Pring R I\<^esub> (mset_to_IP R {#i#}))"
                  using A A0 ring_hom_mult[of \<psi> "Pring R I" S P "(mset_to_IP R {#i#})"]
                        ring_hom_mult[of \<rho> "Pring R I" S P "(mset_to_IP R {#i#})"] P0
                  by (metis P1 Pring_car Pring_one Pring_one_closed indexed_pset.indexed_pmult
                      monom_add_mset one_mset_to_IP ring_hom_ring.homh)
                then show ?thesis
                  by (metis A0(1) A0(3) Pring_mult poly_index_mult)
              qed
            qed
          qed
        qed
    qed
  qed
qed

end

definition close_fun :: "'c set \<Rightarrow> ('e, 'f) ring_scheme \<Rightarrow> ('c \<Rightarrow> 'e) \<Rightarrow> ('c \<Rightarrow> 'e)" where
"close_fun I S g = (\<lambda>i. (if i \<in> I then g i else  \<zero>\<^bsub>S\<^esub>))"

context cring
begin

lemma close_funE:
  assumes "cring S"
  assumes "g \<in> I \<rightarrow> carrier S"
  shows "closed_fun S (close_fun I S g)"
  apply(rule cring.closed_funI)
  apply (simp add: assms(1))
  by (metis close_fun_def PiE assms(1) assms(2) cring.cring_simprules(2))

end

definition indexed_poly_induced_morphism ::
 "'c set \<Rightarrow> ('e, 'f) ring_scheme \<Rightarrow> ('a, 'e) ring_hom \<Rightarrow> ('c \<Rightarrow> 'e) \<Rightarrow> (('a,'c) mvar_poly, 'e) ring_hom" where
"indexed_poly_induced_morphism I S \<phi> g = (total_eval S (close_fun I S g)) \<circ> (ring_hom_to_IP_ring_hom \<phi>)"

context cring
begin

lemma Pring_universal_prop:
  assumes a_cring: "cring S"
  assumes index_map: "g \<in> I \<rightarrow> carrier S"
  assumes ring_hom: "ring_hom_ring R S \<phi>"
  assumes "\<psi> = indexed_poly_induced_morphism I S \<phi> g"
  shows "(ring_hom_ring (Pring R I) S \<psi>)"
        "(\<forall>i \<in> I. \<psi> (mset_to_IP R {#i#}) = g i)"
        "(\<forall>a \<in> carrier R. \<psi> (indexed_const a) = \<phi> a)"
        "\<forall> \<rho>. (ring_hom_ring (Pring R I) S \<rho>) \<and>
          (\<forall>i \<in> I. \<rho> (mset_to_IP R {#i#}) = g i) \<and>
          (\<forall>a \<in> carrier R. \<rho> (indexed_const a) = \<phi> a) \<longrightarrow>
          (\<forall>x \<in> carrier (Pring R I). \<rho> x = \<psi> x)"
proof-
  obtain g' where g'_def: "g' =  (close_fun I S g)"
    by simp
  have 0: "closed_fun S g'"
    using close_funE a_cring g'_def index_map
    by blast
  show "(ring_hom_ring (Pring R I) S \<psi>)" using assms 0
    using cring.Pring_universal_prop_0(1) indexed_poly_induced_morphism_def g'_def is_cring
    by blast
  show "(\<forall>i \<in> I. \<psi> (mset_to_IP R {#i#}) = g i)"
  proof-
    have "(\<forall>i \<in> I. \<psi> (mset_to_IP R {#i#}) = g' i)"
      apply(intro Pring_universal_prop_0[of S _ \<phi>] assms)
      unfolding assms indexed_poly_induced_morphism_def g'_def
      using assms 0 g'_def apply fastforce
      by auto
    thus ?thesis unfolding g'_def using assms
      by (simp add: close_fun_def)
  qed
  show "\<forall>a\<in>carrier R. \<psi> (indexed_const a) = \<phi> a"
    using 0  indexed_poly_induced_morphism_def Pring_universal_prop_0(3) a_cring assms(4) g'_def ring_hom
    by blast
  show "\<forall>\<rho>. ring_hom_ring (Pring R I) S \<rho> \<and> (\<forall>i\<in>I. \<rho> (mset_to_IP R {#i#}) = g i) \<and> (\<forall>a\<in>carrier R. \<rho> (indexed_const a) = \<phi> a) \<longrightarrow>
        (\<forall>x\<in>carrier (Pring R I). \<rho> x = \<psi> x)"
  proof-
    have "\<forall>\<rho>. ring_hom_ring (Pring R I) S \<rho> \<and> (\<forall>i\<in>I. \<rho> (mset_to_IP R {#i#}) = g' i) \<and> (\<forall>a\<in>carrier R. \<rho> (indexed_const a) = \<phi> a) \<longrightarrow>
        (\<forall>x\<in>carrier (Pring R I). \<rho> x = \<psi> x)"
      using assms 0 Pring_universal_prop_0(4)  g'_def
      unfolding indexed_poly_induced_morphism_def
      by blast
    then show ?thesis
      using g'_def
      unfolding close_fun_def
      by meson
  qed
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Mapping Mulitvariate Polynomials over a Single Variable to Univariate Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Constructor for multisets which have one distinct element\<close>

definition nat_to_mset :: "'c \<Rightarrow> nat \<Rightarrow> 'c monomial" where
"nat_to_mset i n = Abs_multiset (\<lambda>j. if (j = i) then n else 0)"

lemma nat_to_msetE: "count (nat_to_mset i n) i = n"
  unfolding nat_to_mset_def by simp

lemma nat_to_msetE':
  assumes "j \<noteq> i"
  shows "count (nat_to_mset i n) j = 0"
  unfolding nat_to_mset_def using assms by simp

lemma nat_to_mset_add: "nat_to_mset i (n + m) = (nat_to_mset i n) + (nat_to_mset i m)"
  apply(rule multiset_eqI)
  by (metis add.right_neutral nat_to_msetE nat_to_msetE' count_union)

lemma nat_to_mset_inj:
  assumes "n \<noteq> m"
  shows "(nat_to_mset i n) \<noteq> (nat_to_mset i m)"
  using assms
  by (metis nat_to_msetE)

lemma nat_to_mset_zero: "nat_to_mset i 0 = {#}"
  by (metis add.right_neutral add_cancel_right_right nat_to_mset_add)

lemma nat_to_mset_Suc: "nat_to_mset i (Suc n) = add_mset i (nat_to_mset i n)"
  using nat_to_mset_add[of i n 1]
  by (simp add: multiset_eqI nat_to_msetE nat_to_msetE')

lemma nat_to_mset_Pring_singleton:
  assumes "cring R"
  assumes "P \<in> carrier (Pring R {i})"
  assumes "m \<in> monomials_of R P"
  shows "m = nat_to_mset i (count m i)"
proof-
  have "\<And> j. count m j = count (nat_to_mset i (count m i)) j"
  proof-
    fix j
    show "count m j = count (nat_to_mset i (count m i)) j"
      apply(cases "j = i")
       apply (simp add: nat_to_msetE; fail)
    proof-
      assume A: "j \<noteq>i"
      have P0: "set_mset m \<subseteq> {i}"
        using assms
        by (metis cring.axioms(1) ring.Pring_car ring.mset_to_IP_indices)
      then have "count m j = 0"
        using A assms
        by (metis count_inI empty_iff singletonD subset_singletonD)
      then show " count m j = count (nat_to_mset i (count m i)) j"
        by (simp add: A nat_to_msetE')
    qed
  qed
  then show ?thesis
    using multiset_eqI by blast
qed

definition IP_to_UP :: "'d \<Rightarrow> ('e, 'd) mvar_poly \<Rightarrow> 'e u_poly" where
"IP_to_UP i P  = (\<lambda> (n::nat). P (nat_to_mset i n))"

lemma IP_to_UP_closed:
  assumes "cring R"
  assumes "P \<in> carrier (Pring R {i::'c})"
  shows "IP_to_UP i P \<in> carrier (UP R)"
proof-
  have "IP_to_UP i P \<in> up R"
    apply(rule mem_upI)
    using assms
     apply (metis cring_def IP_to_UP_def ring.Pring_carrier_coeff')
       unfolding bound_def IP_to_UP_def
       apply(rule ccontr)
     proof-
       assume A: "\<nexists>n. \<forall>m>n. P (nat_to_mset i m) = \<zero>\<^bsub>R\<^esub>"
       then have 0: "\<forall>n. \<exists>m> n. (nat_to_mset i m) \<in> monomials_of R P"
         by (meson assms(1) cring_def ring.complement_of_monomials_of)
       have "\<not> finite {m. (nat_to_mset i m) \<in> monomials_of R P }"
       proof
         assume "finite {m. nat_to_mset i m \<in> monomials_of R P}"
         then have "\<exists>n. \<forall>m>n.  m \<notin> {m. nat_to_mset i m \<in> monomials_of R P}"
           by (meson finite_nat_set_iff_bounded nat_less_le order.strict_trans)
         then have "\<exists>n. \<forall>m>n.  nat_to_mset i m \<notin> monomials_of R P"
           by (simp add: monomials_of_def)
         then show False using 0
           by blast
       qed
       then obtain S where S_def: "infinite (S::nat set) \<and> (\<forall>m \<in> S. (nat_to_mset i m) \<in> monomials_of R P)"
         by blast
       have "inj_on (nat_to_mset i) S"
         using inj_onI[of S "nat_to_mset i"]
         by (meson nat_to_mset_inj)
       then have 1: "infinite (nat_to_mset i ` S)"
         using S_def finite_imageD
         by blast
       have 2: "(nat_to_mset i ` S) \<subseteq> (monomials_of R P)"
         using S_def
         by blast
       then have "infinite (monomials_of R P)"
         using S_def "1" finite_subset
         by blast
       then show False using assms
         by (metis Pring_def cring_def partial_object.select_convs(1) ring.monomials_finite)
     qed
     then show ?thesis
       by (metis (no_types, lifting) UP_def partial_object.select_convs(1))
qed

lemma IP_to_UP_var:
  shows "IP_to_UP i (mset_to_IP R {#i#}) = X_poly R"
proof
  have UP: "UP_cring R"
    by (simp add: UP_cring_def cring_axioms)
  fix x
  show "IP_to_UP i (mset_to_IP R {#i#}) x = X_poly R x"
  proof(cases "x = 1")
    case True
    then have RHS: "X_poly R x = \<one>\<^bsub>R\<^esub>"
      unfolding X_poly_def using UP UP_ring.cfs_monom[of R]
      unfolding UP_ring_def
      using local.ring_axioms one_closed by presburger
    have LHS: "IP_to_UP i (mset_to_IP R ((add_mset i) {#})) x
        = mset_to_IP R ((add_mset i) {#}) (nat_to_mset i x)"
      unfolding IP_to_UP_def
      by blast
    have "(nat_to_mset i x) = {#i#}"
    proof-
      have "\<And>n. count (nat_to_mset i x) n = count {#i#} n"
        by (simp add: True nat_to_msetE nat_to_msetE')
      then show ?thesis
        using multi_count_eq
        by blast
    qed
    then have LHS: "IP_to_UP i (mset_to_IP R ((add_mset i) {#})) x
       =  mset_to_IP R ((add_mset i) {#}) {#i#}"
      using LHS by presburger
    then show ?thesis
      unfolding deg_zero_cf_def
      by (metis RHS mset_to_IP_simp)
  next
    case False
    then have RHS: "X_poly R x = \<zero>\<^bsub>R\<^esub>"
      unfolding X_poly_def
      using UP UP_ring.cfs_monom[of R]
      unfolding UP_ring_def
      using local.ring_axioms one_closed by presburger
    have LHS: "IP_to_UP i (mset_to_IP R ((add_mset i) {#})) x
        = mset_to_IP R ((add_mset i) {#}) (nat_to_mset i x)"
      unfolding IP_to_UP_def
      by blast
    then show ?thesis
      unfolding deg_zero_cf_def
      by (metis False RHS count_single mset_to_IP_def nat_to_msetE)
  qed
qed

end

context UP_cring
begin

lemma IP_to_UP_monom:
  shows "IP_to_UP i (mset_to_IP R (nat_to_mset i n)) = ((X_poly R)[^]\<^bsub>UP R\<^esub>n) "
proof
  fix x
  show "IP_to_UP i (mset_to_IP R (nat_to_mset i n)) x = (X_poly R [^]\<^bsub>UP R\<^esub> n) x"
  proof(cases "x = n")
    case True
    have RHS: "(X_poly R [^]\<^bsub>UP R\<^esub> n) x = \<one>\<^bsub>R\<^esub>"
      unfolding X_poly_def
      by (metis P.nat_pow_closed P.nat_pow_eone P_def R.one_closed True UP_cring.X_closed
          UP_cring.monom_coeff UP_one_closed UP_r_one deg_one is_UP_cring monom_one monom_rep_X_pow
          to_poly_inverse to_poly_mult_simp(2))
    have LHS:  "IP_to_UP i (mset_to_IP R (nat_to_mset i n)) x = \<one>\<^bsub>R\<^esub>"
      by (metis R.mset_to_IP_simp True IP_to_UP_def)
    then show ?thesis
      using RHS by presburger
  next
    case False
    have 0: "\<And>x y::nat. nat_to_mset x = nat_to_mset y \<Longrightarrow> x = y"
    proof-
      fix a b::nat assume A:  "nat_to_mset a = nat_to_mset b"
      then show "a = b" unfolding nat_to_mset_def
        by (metis A nat_to_msetE nat_to_msetE' zero_neq_one)
    qed
    have 1: "IP_to_UP i (mset_to_IP R (nat_to_mset i n)) x  = (if nat_to_mset i x = nat_to_mset i n then \<one> else \<zero>) "
      unfolding IP_to_UP_def mset_to_IP_def
      by blast
    hence 2: "IP_to_UP i (mset_to_IP R (nat_to_mset i n)) x  = (if x = n then \<one> else \<zero>) "
      using 0
      by (meson False nat_to_mset_inj)
    have 3: "(X_poly R [^]\<^bsub>UP R\<^esub> n) x = \<zero>"
      unfolding X_poly_def using False
      by (smt ctrm_degree P.nat_pow_closed P.nat_pow_eone P.r_null P_def R.one_closed
          UP_cring.ltrm_of_X UP_cring.ltrm_rep_X_pow UP_cring.X_closed UP_cring.monom_coeff
          UP_r_one UP_zero_closed X_mult_cf cfs_closed cfs_monom deg_nzero_nzero is_UP_cring
          monom_closed monom_one to_poly_inverse to_poly_mult_simp(2))
    thus ?thesis using 2 1
      using False by presburger
  qed
qed

lemma IP_to_UP_one:
 "IP_to_UP i \<one>\<^bsub>Pring R {i}\<^esub> = \<one>\<^bsub>UP R\<^esub>"
proof
  fix x
  show "IP_to_UP i \<one>\<^bsub>Pring R {i}\<^esub> x = \<one>\<^bsub>UP R\<^esub> x"
  proof(cases "x = 0")
    case True
    have RHS: "\<one>\<^bsub>UP R\<^esub> x = \<one>\<^bsub>R\<^esub>"
      using P_def True cfs_one by presburger
    have "\<one>\<^bsub>Pring R {i}\<^esub> = (\<lambda> m. if m = {#} then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>)"
      by (metis R.Pring_one R.indexed_const_def)
    then have "IP_to_UP i \<one>\<^bsub>Pring R {i}\<^esub> = IP_to_UP i (\<lambda> m. if m = {#} then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>)"
      by presburger
    then have LHS: "IP_to_UP i \<one>\<^bsub>Pring R {i}\<^esub> x = \<one>\<^bsub>R\<^esub>"
      by (smt True count_empty IP_to_UP_def multi_count_eq nat_to_msetE nat_to_msetE')
    then show ?thesis
      using RHS by presburger
  next
    case False
    have RHS: "\<one>\<^bsub>UP R\<^esub> x = \<zero>\<^bsub>R\<^esub>"
      by (smt False UP_def monoid.simps(2))
    show ?thesis
      using False count_empty
            nat_to_msetE
            ring.indexed_const_def
      unfolding IP_to_UP_def
      by (metis R.Pring_one R.ring_axioms RHS)
  qed
qed

lemma IP_to_UP_zero:
 "IP_to_UP i \<zero>\<^bsub>Pring R {i}\<^esub> = \<zero>\<^bsub>UP R\<^esub>"
proof
  fix x
  show "IP_to_UP i \<zero>\<^bsub>Pring R {i}\<^esub> x = \<zero>\<^bsub>UP R\<^esub> x"
    unfolding IP_to_UP_def using R.Pring_zero
    by (metis P_def R.indexed_zero_def cfs_zero)
qed

lemma IP_to_UP_add:
  assumes " x \<in> carrier (Pring R {i})"
  assumes " y \<in> carrier (Pring R {i})"
  shows " IP_to_UP i (x \<oplus>\<^bsub>Pring R {i}\<^esub> y) =
          IP_to_UP i x \<oplus>\<^bsub>UP R\<^esub> IP_to_UP i y"
proof
  fix n
  have LHS: "IP_to_UP i (x \<oplus>\<^bsub>Pring R {i}\<^esub> y) n = (x \<oplus>\<^bsub>Pring R {i}\<^esub> y) (nat_to_mset i n)"
    by (meson IP_to_UP_def)
  then have LHS: "IP_to_UP i (x \<oplus>\<^bsub>Pring R {i}\<^esub> y) n = x (nat_to_mset i n) \<oplus>\<^bsub>R\<^esub> y (nat_to_mset i n)"
    using assms  unfolding IP_to_UP_def
    by (metis R.Pring_add R.indexed_padd_def)
  have RHS: "(IP_to_UP i x \<oplus>\<^bsub>UP R\<^esub> IP_to_UP i y) n =
   (IP_to_UP i x) n \<oplus>\<^bsub>R\<^esub> (IP_to_UP i y) n"
    using assms UP_ring.cfs_add IP_to_UP_closed
    by (simp add: UP_ring.cfs_add R_cring cring.IP_to_UP_closed is_UP_ring)
  then   show "IP_to_UP i (x \<oplus>\<^bsub>Pring R {i}\<^esub> y) n = (IP_to_UP i x \<oplus>\<^bsub>UP R\<^esub> IP_to_UP i y) n"
    using assms
    by (metis LHS IP_to_UP_def)
qed

lemma IP_to_UP_indexed_const:
  assumes "k \<in> carrier R"
  shows "IP_to_UP i (ring.indexed_const R k) = to_polynomial R k"
proof
  fix x
  show "IP_to_UP i (ring.indexed_const R k) x = to_polynomial R k x"
  proof(cases "x = 0")
    case True
    have LHS: "IP_to_UP i (ring.indexed_const R k) x = k"
      using True unfolding IP_to_UP_def
      by (metis R.indexed_const_def nat_to_mset_zero)
    then show ?thesis
      using assms
      unfolding to_polynomial_def
      using True to_polynomial_def
      by (metis UP_ring.cfs_monom is_UP_ring)
  next
    case False
    have LHS: "IP_to_UP i (ring.indexed_const R k) x = \<zero>\<^bsub>R\<^esub>"
      using False unfolding IP_to_UP_def
      by (metis R.indexed_const_def nat_to_mset_inj nat_to_mset_zero)
    then show ?thesis
      using assms
      unfolding to_polynomial_def
      using False UP_cring.intro UP_cring.monom_coeff UP_cring.monom_rep_X_pow
      using P_def cfs_monom by presburger
  qed
qed

lemma IP_to_UP_indexed_pmult:
  assumes "p \<in> carrier (Pring R {i})"
  shows "IP_to_UP i (ring.indexed_pmult R p i) = (IP_to_UP i p) \<otimes>\<^bsub>UP R\<^esub> (X_poly R)"
proof
  fix n
  have 0: "IP_to_UP i p \<in> carrier (UP R)"
    by (simp add: R_cring assms cring.IP_to_UP_closed)
  show "IP_to_UP i (ring.indexed_pmult R p i) n = (IP_to_UP i p \<otimes>\<^bsub>UP R\<^esub> X_poly R) n"
  proof(cases "n = 0")
    case True
    then have RHS: "(IP_to_UP i p \<otimes>\<^bsub>UP R\<^esub> X_poly R) n = \<zero>\<^bsub>R\<^esub>"
      by (metis (no_types, lifting) "0" lcf_closed One_nat_def P.r_null P_def R.r_null
          UP_cring.ltrm_of_X UP_cring.cfs_monom_mult UP_cring.cfs_monom_mult_l UP_zero_closed
          X_closed cfs_times_X deg_leE deg_nzero_nzero is_UP_cring lessI neq0_conv plus_1_eq_Suc to_poly_inverse)
    have LHS: "IP_to_UP i (ring.indexed_pmult R p i) n = ring.indexed_pmult R p i (nat_to_mset i n)"
      unfolding IP_to_UP_def
      by blast
    then have LHS': "IP_to_UP i (ring.indexed_pmult R p i) n =
                  (p \<otimes>\<^bsub>Pring R {i}\<^esub> (mset_to_IP R {#i#})) (nat_to_mset i n)"
      using  assms(1) ring.Pring_car ring.Pring_mult
                ring.poly_index_mult singletonI
      by (metis R.ring_axioms)
  then have LHS': "IP_to_UP i (ring.indexed_pmult R p i) n =
                  (p \<otimes>\<^bsub>Pring R {i}\<^esub> (mset_to_IP R {#i#})) {#}"
    using True
    by (metis nat_to_mset_zero)
  then show ?thesis using RHS  LHS True assms(1) nat_to_mset_zero ring.indexed_pmult_def
    by (metis R.ring_axioms empty_iff set_mset_empty)
  next
    case False
    then have RHS: "(IP_to_UP i p \<otimes>\<^bsub>UP R\<^esub> X_poly R) n = (IP_to_UP i p ) (n -1)"
      using "0" Suc_diff_1 Suc_eq_plus1
           assms(1) bot_nat_def IP_to_UP_def nat_neq_iff not_less0
      by (metis (no_types, lifting) P_def UP_cring X_closed cfs_times_X cring.cring_simprules(14))
    have LHS: "IP_to_UP i (ring.indexed_pmult R p i) n = ring.indexed_pmult R p i (nat_to_mset i n)"
      unfolding IP_to_UP_def
      by blast
    then have LHS': "IP_to_UP i (ring.indexed_pmult R p i) n =
                  (p \<otimes>\<^bsub>Pring R {i}\<^esub> (mset_to_IP R {#i#})) (nat_to_mset i n)"
      using assms(1) ring.Pring_car ring.Pring_mult
      ring.poly_index_mult singletonI
      by (metis R.ring_axioms)
    then have LHS'': "IP_to_UP i (ring.indexed_pmult R p i) n =
                  (p \<otimes>\<^bsub>Pring R {i}\<^esub> (mset_to_IP R {#i#})) (add_mset i (nat_to_mset i (n-1))) "
      by (metis False Suc_diff_1 nat_to_mset_Suc neq0_conv)
    then show ?thesis using RHS unfolding IP_to_UP_def
      by (metis (no_types, lifting) False R.indexed_pmult_def Suc_diff_1 add_mset_remove_trivial add_mset_remove_trivial_If multi_self_add_other_not_self nat_to_mset_Suc neq0_conv)
  qed
qed

lemma IP_to_UP_ring_hom:
  shows "ring_hom_ring (Pring R {i}) (UP R) (IP_to_UP i)"
  apply(rule cring.Pring_morphism)
      apply (simp add: R_cring; fail)
  using P_def UP_cring apply blast
      apply (simp add: R.IP_to_UP_closed R_cring; fail)
      apply (meson IP_to_UP_one)
            apply (meson IP_to_UP_zero)
    apply (meson IP_to_UP_add)
  apply (metis R.IP_to_UP_var IP_to_UP_indexed_pmult singletonD)
proof-
  fix k Q
  assume A0: "k \<in> carrier R"
  assume A1: "Q \<in> carrier (Pring R {i})"
  show "IP_to_UP i (poly_scalar_mult R k Q) =
           IP_to_UP i (ring.indexed_const R k) \<otimes>\<^bsub>UP R\<^esub> IP_to_UP i Q"
    unfolding poly_scalar_mult_def
  proof
    fix x
    show "IP_to_UP i (\<lambda>m. k \<otimes>\<^bsub>R\<^esub> Q m) x =
         (IP_to_UP i (ring.indexed_const R k) \<otimes>\<^bsub>UP R\<^esub> IP_to_UP i Q) x"
    proof-
      have LHS: "IP_to_UP i (\<lambda>m. k \<otimes>\<^bsub>R\<^esub> Q m) x = k \<otimes>\<^bsub>R\<^esub> Q (nat_to_mset i x)"
        unfolding IP_to_UP_def
        by blast
      have RHS: "(IP_to_UP i (ring.indexed_const R k) \<otimes>\<^bsub>UP R\<^esub> IP_to_UP i Q) x =
                (to_polynomial R k \<otimes>\<^bsub>UP R\<^esub> IP_to_UP i Q) x"
        by (metis A0 IP_to_UP_indexed_const)
      have RHS': "(IP_to_UP i (ring.indexed_const R k) \<otimes>\<^bsub>UP R\<^esub> IP_to_UP i Q) x =
                k \<otimes>\<^bsub>R\<^esub> ((IP_to_UP i Q) x)"
      proof-
        have 0: "deg R (to_polynomial R k) = 0"
          using A0 degree_to_poly by blast
        have 1: "(IP_to_UP i Q) \<in> carrier (UP R)"
          using IP_to_UP_closed  unfolding P_def
          by (simp add: A1 R.IP_to_UP_closed R_cring)
        then show ?thesis
        proof -
          have "UP_cring R \<and> IP_to_UP i Q \<in> carrier (UP R)"
            using "1" is_UP_cring by blast
          then show ?thesis
            by (metis A0 UP_cring.to_poly_mult_simp(1) UP_ring.UP_mult_closed UP_ring.coeff_simp UP_ring.coeff_smult UP_ring.monom_closed IP_to_UP_indexed_const is_UP_ring to_polynomial_def)
        qed
      qed
      then show ?thesis
        by (metis IP_to_UP_def)
    qed
  qed
qed

lemma IP_to_UP_ring_hom_inj:
  shows "inj_on  (IP_to_UP i) (carrier (Pring R {i}))"
proof
  fix x y
  assume A: "x \<in> carrier (Pring R {i})" "y \<in> carrier (Pring R {i}) "
  assume B: "IP_to_UP i x = IP_to_UP i y"
  show "x = y"
  proof
    fix a
    show "x a = y a"
    proof(cases "set_mset a \<subseteq> {i}")
      case True
      then obtain n where "a = (nat_to_mset i n)"
        by (metis count_eq_zero_iff insert_subset multiset_eqI nat_to_msetE nat_to_msetE'
            set_eq_subset singletonD singleton_insert_inj_eq' subset_insertI subset_refl)
      then have LHS: "x a = IP_to_UP i x n"
        by (metis IP_to_UP_def)
      then show ?thesis
        by (metis B \<open>a = nat_to_mset i n\<close> IP_to_UP_def)
    next
      case False
      then show ?thesis
        using ring.Pring_set_zero[of R y "{i}" a] ring.Pring_set_zero[of R x "{i}" a] A
        by (metis R.Pring_car R.ring_axioms)
    qed
  qed
qed

lemma IP_to_UP_scalar_mult:
  assumes "a \<in> carrier R"
  assumes "p \<in> carrier (Pring R {i})"
  shows "(IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> p)) = a\<odot>\<^bsub>UP R\<^esub> (IP_to_UP i p)"
  apply(rule ring.indexed_pset.induct[of R p "{i}" "carrier R"])
  apply (simp add: R.ring_axioms; fail)
  using R.Pring_car assms(2) apply blast
  apply (metis IP_to_UP_indexed_const P_def R.m_closed R.poly_scalar_mult_const R.ring_axioms assms(1) ring.Pring_smult to_poly_closed to_poly_mult to_poly_mult_simp(1))
proof-
  show "\<And>P Q. P \<in> Pring_set R {i} \<Longrightarrow>
           IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> P) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i P \<Longrightarrow>
           Q \<in> Pring_set R {i} \<Longrightarrow> IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> Q) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i Q \<Longrightarrow> IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> (P \<Oplus> Q)) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i (P \<Oplus> Q)"
  proof-
    fix p Q
    assume A0: "p \<in> Pring_set R {i}"
              "IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> p) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i p"
              " Q \<in> Pring_set R {i}"
              "IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> Q) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i Q"
    show "IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> (p \<Oplus> Q)) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i (p \<Oplus> Q)"
    proof-
      have "(a \<odot>\<^bsub>Pring R {i}\<^esub> (p \<Oplus> Q)) = a \<odot>\<^bsub>Pring R {i}\<^esub>  p \<oplus>\<^bsub>Pring R {i}\<^esub> a \<odot>\<^bsub>Pring R {i}\<^esub>  Q"
        by (metis A0(1) A0(3) R.Pring_add R.Pring_car R.Pring_smult_r_distr assms(1))
      then show ?thesis using A0
        by (metis IP_to_UP_add P_def R.IP_to_UP_closed R.Pring_add R.Pring_car R.Pring_smult_closed R_cring UP_smult_r_distr assms(1))
      qed
  qed
  show " \<And>P ia. P \<in> Pring_set R {i} \<Longrightarrow> IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> P) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i P \<Longrightarrow> ia \<in> {i} \<Longrightarrow> IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> (P \<Otimes> ia)) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i (P \<Otimes> ia)"
  proof
    fix P j x
    assume A0: "P \<in> Pring_set R {i}"
    assume A1: "IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> P) = a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i P"
    assume A2: "j \<in> {i}"
    then have A3: "j = i"
      by blast
    have "IP_to_UP i (ring.indexed_pmult R P j) \<in> carrier (UP R)"
      by (simp add: A0 A3 R.Pring_car R.indexed_pset.indexed_pmult R_cring cring.IP_to_UP_closed)
    then have "(a \<odot>\<^bsub>UP R\<^esub> (\<lambda>n. ring.indexed_pmult R P j (nat_to_mset i n))) x = a \<otimes>\<^bsub>R\<^esub>((\<lambda>n. ring.indexed_pmult R P j (nat_to_mset i n))) x"
      using A0 A1 A3 assms unfolding IP_to_UP_def
      using P_def cfs_smult by blast
    then show " IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> (P \<Otimes> j)) x = (a \<odot>\<^bsub>UP R\<^esub> IP_to_UP i (P \<Otimes> j)) x"
      by (metis A0 A2 IP_to_UP_def P_def R.Pring_car R.Pring_smult_cfs R.indexed_pset.indexed_pmult \<open>IP_to_UP i (P \<Otimes> j) \<in> carrier (UP R)\<close> assms(1) cfs_smult)
  qed
qed

end

text\<open>Evaluation of indexed polynomials commutes with evaluation of univariate polynomials:\<close>

lemma pvar_closed:
  assumes "cring R"
  assumes "i \<in> I"
  shows "(pvar R i) \<in> carrier (Pring R I)"
  by (meson assms(1) assms(2) cring.axioms(1) ring.Pring_var_closed)

context UP_cring
begin

lemma pvar_mult:
  assumes "i \<in> I"
  assumes "j \<in>  I"
  shows "(pvar R i) \<otimes>\<^bsub>Pring R I\<^esub> (pvar R j) = mset_to_IP R {#i, j#}"
proof-
  have "{#i#} + {#j#}  = {# i, j#}"
    by auto
  then show ?thesis
    unfolding var_to_IP_def
    by (metis R.Pring_mult R.monom_mult)
qed

lemma pvar_pow:

  assumes "i \<in> I"
  shows "(pvar R i)[^]\<^bsub>Pring R I\<^esub>(n::nat) = mset_to_IP R (nat_to_mset i n)"
  apply(induction n)
  apply (metis Group.nat_pow_0 R.one_mset_to_IP R.ring_axioms nat_to_mset_zero ring.Pring_one)
proof-
  fix n
  assume IH: "pvar R i [^]\<^bsub>Pring R I\<^esub> n = mset_to_IP R (nat_to_mset i n)"
  show "pvar R i [^]\<^bsub>Pring R I\<^esub> Suc n = mset_to_IP R (nat_to_mset i (Suc n)) "
  proof-
    have "mset_to_IP R (nat_to_mset i (Suc n)) = mset_to_IP R (nat_to_mset i n) \<otimes>\<^bsub>Pring R I\<^esub> pvar R i"
      using R.monom_mult[of "nat_to_mset i n" "nat_to_mset i 1"]
      by (metis One_nat_def R.Pring_mult Suc_eq_plus1 nat_to_mset_Suc nat_to_mset_add nat_to_mset_zero var_to_IP_def)
    then show ?thesis
      using IH
      by simp
  qed
qed

lemma IP_to_UP_poly_eval:
  assumes "p \<in> Pring_set R {i}"
  assumes "closed_fun R g"
  shows "total_eval R g p = to_function R (IP_to_UP i p) (g i)"
  apply(rule R.indexed_pset.induct[of p "{i}" "carrier R" ])
  apply (simp add: assms(1); fail)
proof-
  show "\<And>k. k \<in> carrier R \<Longrightarrow> total_eval R g (R.indexed_const k) = to_function R (IP_to_UP i (R.indexed_const k)) (g i)"
  proof-
    fix k
    assume A: "k \<in> carrier R"
    have P0: "total_eval R g (ring.indexed_const R k) = k"
      unfolding total_eval_def eval_in_ring_def
      using cring.poly_eval_constant[of R k UNIV g]
      by (metis A R.indexed_const_def R_cring)
    have P1: "(IP_to_UP i (ring.indexed_const R k)) = to_polynomial R k"
      by (meson A IP_to_UP_indexed_const)
    have P2: "to_function R (IP_to_UP i (ring.indexed_const R k)) (g i) =
              to_function R (to_polynomial R k) (g i)"
      using P1 by presburger
    have P3: "to_function R (to_polynomial R k) (g i) = k"
      using A assms(2) to_fun_to_poly[of k "g i"] unfolding to_fun_def by blast
    then show "total_eval R g (R.indexed_const k) = to_function R (IP_to_UP i (R.indexed_const k)) (g i)"
      using P0 P2 by presburger
  qed
  show "\<And>P Q. P \<in> Pring_set R {i} \<Longrightarrow>
           total_eval R g P = to_function R  (IP_to_UP i P) (g i) \<Longrightarrow>
           Q \<in> Pring_set R {i} \<Longrightarrow>
           total_eval R g Q = to_function R  (IP_to_UP i Q) (g i) \<Longrightarrow> total_eval R g (P \<Oplus> Q) = to_function R (IP_to_UP i (P \<Oplus> Q)) (g i)"
  proof-
    fix p Q
    assume A0: "p \<in> Pring_set R {i}"
    assume A1: " total_eval R g p = to_function R (IP_to_UP i p) (g i)"
    assume A2: " Q \<in> Pring_set R {i}"
    assume A3: "total_eval R g Q = to_function R (IP_to_UP i Q) (g i)"
    have "total_eval R g (R.indexed_padd p Q) = (total_eval R g p) \<oplus>\<^bsub>R\<^esub> (total_eval R g Q)"
      using R.total_eval_add[of p "{i}" Q g] A0 A1
      by (metis A2 R.Pring_add R.Pring_car assms(2))
    then
    have 0: "total_eval R g (p \<Oplus> Q) = total_eval R g p \<oplus> total_eval R g Q "
      by blast
    have 1: "IP_to_UP i (p \<Oplus> Q) = IP_to_UP i p \<oplus>\<^bsub>UP R\<^esub> IP_to_UP i Q"
      using A0 A1 A3 assms A2 R.ring_axioms R_cring IP_to_UP_add
      by (metis R.Pring_add R.Pring_car)
    have "g i \<in> carrier R"
      using assms by blast
    hence 2: "to_function R (IP_to_UP i (p \<Oplus> Q)) (g i) = to_function R (IP_to_UP i p) (g i) \<oplus> to_function R (IP_to_UP i Q) (g i)"
      using A0 A1 A3 assms A2 R.ring_axioms R_cring to_fun_plus[of "IP_to_UP i p" "IP_to_UP i Q" "g i"]
            IP_to_UP_closed is_UP_cring UP_cring.to_fun_def
            to_fun_def 0 1
      unfolding to_fun_def P_def
      by (smt (z3) P_def R.IP_to_UP_closed R.Pring_car to_fun_plus)
    show "total_eval R g (R.indexed_padd p Q) = to_function R (IP_to_UP i (ring.indexed_padd R p Q)) (g i) "
      using A0 A1 A3 assms A2 R.ring_axioms R_cring is_UP_cring to_fun_def 0 1 2
      unfolding to_fun_def   by metis
  qed
  show "\<And>P ia.
       P \<in> Pring_set R {i} \<Longrightarrow>
       total_eval R g P = to_function R (IP_to_UP i P) (g i) \<Longrightarrow> ia \<in> {i} \<Longrightarrow> total_eval R g (P \<Otimes> ia) = to_function R (IP_to_UP i (P \<Otimes> ia)) (g i)"
  proof-
    fix P
    fix j
    assume A0: "P \<in> Pring_set R {i}"
    assume A1: "total_eval R g P = to_function R (IP_to_UP i P) (g i)"
    assume A2: "j \<in> {i}"
    then have A3: "j = i"
      by blast
    show "total_eval R g (P \<Otimes> j) = to_function R (IP_to_UP i (P \<Otimes> j)) (g i)"
    proof-
      have LHS: "total_eval R g (P \<Otimes> j) = (total_eval R g P) \<otimes>\<^bsub>R\<^esub> (g i)"
        using assms A0 A3
        by (metis R.Pring_car R_cring cring.total_eval_indexed_pmult insertI1)
      have RHS: "IP_to_UP i (P \<Otimes> j)=  IP_to_UP i P  \<otimes>\<^bsub> UP R\<^esub> X_poly R"
        by (metis A0 A3 IP_to_UP_indexed_pmult R.Pring_car)
      have "g i \<in> carrier R"
        using assms by blast
      then show ?thesis
          using A0 A1 A3 X_closed to_fun_X[of "g i"] to_fun_mult[of "IP_to_UP i P" "X_poly R" "g i"] LHS RHS
              assms  cring.axioms(1) domain.axioms(1)
              IP_to_UP_indexed_pmult IP_to_UP_closed
              Pring_car unfolding to_fun_def P_def
          by (smt (z3) P.m_comm P_def R.m_comm R_cring cring.IP_to_UP_closed ring.Pring_car to_fun_closed to_fun_def)
      qed
   qed
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Mapping Univariate Polynomials to Multivariate Polynomials over a Singleton Variable Set\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition UP_to_IP :: "('a,'b) ring_scheme \<Rightarrow> 'c \<Rightarrow> 'a u_poly \<Rightarrow> ('a, 'c) mvar_poly" where
"UP_to_IP R i P = (\<lambda> m. if (set_mset m) \<subseteq>  {i} then P (count m i) else \<zero>\<^bsub>R\<^esub>)"

context UP_cring
begin

lemma UP_to_IP_inv:
  assumes "p \<in> Pring_set R {i}"
  shows "UP_to_IP R i (IP_to_UP i p) = p"
proof
  fix x
  show "UP_to_IP R i (IP_to_UP i p) x = p x"
  proof(cases "(set_mset x) = {i}")
    case True
    have "{a. 0 < (\<lambda>j. if j = i then count x i else 0) a} = {i}"
      by (smt Collect_cong True count_eq_zero_iff neq0_conv singletonI singleton_conv)
  then have "finite {j. (if j = i then count x i else 0) \<noteq> 0}"
      by auto
    have "(\<lambda>j. if j = i then count x i else 0) = count x"
    proof
      fix j
      show "(if j = i then count x i else 0) = count x j "
        apply(cases "j = i")
        using True
        apply (simp; fail)
        using True
        by (metis count_inI singletonD)
    qed
    then have "(Abs_multiset (\<lambda>j. if j = i then count x i else 0)) = x"
      using count_inverse
      by simp
    then show ?thesis
      unfolding UP_to_IP_def IP_to_UP_def nat_to_mset_def
      by (metis True set_eq_subset)
  next
    case False
    then show ?thesis
      apply(cases "x = {#}")
       apply (metis count_empty empty_subsetI IP_to_UP_def nat_to_mset_zero set_mset_empty UP_to_IP_def)
     unfolding UP_to_IP_def IP_to_UP_def nat_to_mset_def
     using False  assms
     by (metis R.Pring_set_zero set_mset_eq_empty_iff subset_singletonD)
  qed
qed

lemma UP_to_IP_const:
  assumes "a \<in> carrier R"
  shows "UP_to_IP R i (to_polynomial R a) = ring.indexed_const R a"
proof
  fix x
  show "UP_to_IP R i (to_polynomial R a) x = ring.indexed_const R a x"
    apply(cases "x = {#}")
    unfolding UP_to_IP_def
    apply (metis R.indexed_const_def UP_ring.cfs_monom assms count_eq_zero_iff insert_absorb insert_not_empty is_UP_ring set_mset_empty subset_insert subset_refl to_polynomial_def)
  by (metis R.indexed_const_def UP_ring.cfs_monom assms count_eq_zero_iff is_UP_ring set_mset_eq_empty_iff subset_empty subset_insert to_polynomial_def)
qed

lemma UP_to_IP_add:
  assumes "p \<in> carrier (UP R)"
  assumes "Q \<in> carrier (UP R)"
  shows "UP_to_IP R i (p \<oplus>\<^bsub>UP R\<^esub> Q) =
         UP_to_IP R i p \<oplus>\<^bsub>Pring R {i}\<^esub> UP_to_IP R i Q"
proof
  fix x
  show "UP_to_IP R i (p \<oplus>\<^bsub>UP R\<^esub> Q) x = (UP_to_IP R i p \<oplus>\<^bsub>Pring R {i}\<^esub> UP_to_IP R i Q) x"
  proof(cases "set_mset x \<subseteq> {i}")
    case True
    have "(UP_to_IP R i p \<oplus>\<^bsub>Pring R {i}\<^esub> UP_to_IP R i Q) x =
          (UP_to_IP R i p) x \<oplus>\<^bsub>R\<^esub> (UP_to_IP R i Q) x"
      using True assms
      by (metis R.Pring_add R.indexed_padd_def)
    then show ?thesis     using assms True
      unfolding UP_to_IP_def UP_def
      by (smt partial_object.select_convs(1) restrict_def ring_record_simps(12))
  next
    case False
    have "(UP_to_IP R i p \<oplus>\<^bsub>Pring R {i}\<^esub> UP_to_IP R i Q) x =
          (UP_to_IP R i p) x \<oplus>\<^bsub>R\<^esub> (UP_to_IP R i Q) x"
            using False assms
            by (metis R.Pring_add R.indexed_padd_def)
    then show ?thesis using False assms
    unfolding UP_to_IP_def UP_def
    using R.l_zero R.zero_closed by presburger
  qed
qed

lemma UP_to_IP_var:
  shows "UP_to_IP R i (X_poly R) = pvar R i"
proof
  have 0: "(count {#i#} i) = 1"
    by simp
  have 1: "set_mset {#i#} \<subseteq> {i}"
    by simp
  have 2: "pvar R i {#i#} = \<one>"
    by (metis R.mset_to_IP_simp var_to_IP_def)
  fix x
  show "UP_to_IP R i (X_poly R) x = pvar R i x"
    apply(cases "x = {#i#}")
    using X_poly_def[of R] cfs_monom[of \<one> 1 "count x i"] 0 1 2
    unfolding UP_to_IP_def P_def
    using R.one_closed apply presburger
  proof-
    assume A: "x \<noteq>{#i#}"
    then show "(if set_mset x \<subseteq> {i} then X_poly R (count x i) else \<zero>\<^bsub>R\<^esub>) = pvar R i x"
    proof(cases "set_mset x \<subseteq> {i}")
      case True
      have "count x i \<noteq> 1" using True A
        by (metis One_nat_def count_empty count_inI count_single empty_iff multiset_eqI
            set_mset_add_mset_insert set_mset_empty set_mset_eq_empty_iff singletonD singletonI subset_singletonD)
      then have 0: "X_poly R (count x i) = \<zero>\<^bsub>R\<^esub>"
        using A UP_cring.X_closed UP_cring.degree_X UP_cring.intro True
        unfolding X_poly_def
        using P_def R.one_closed \<open>\<one> \<in> carrier R \<Longrightarrow> up_ring.monom P \<one> 1 (count x i) = (if 1 = count x i then \<one> else \<zero>)\<close> by presburger
      have "pvar R i x = \<zero>\<^bsub>R\<^esub>"
        using A var_to_IP_def
        by (metis R.mset_to_IP_simp')
      then show ?thesis
        using A "0" by presburger
    next
      case False
      have "pvar R i x = \<zero>\<^bsub>R\<^esub>" using A var_to_IP_def False
        by (metis "1" R.Pring_set_zero R.mset_to_IP_closed)
      then show ?thesis
        unfolding UP_to_IP_def
        using False by presburger
    qed
  qed
qed

lemma UP_to_IP_var_pow:
  shows "UP_to_IP R i ((X_poly R)[^]\<^bsub>UP R\<^esub> (n::nat)) = (pvar R i)[^]\<^bsub>Pring R {i}\<^esub>n"
proof
  fix x
  show "UP_to_IP R i (X_poly R [^]\<^bsub>UP R\<^esub> n) x = (pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) x "
  proof(cases "set_mset x \<subseteq> {i}")
    case True
    show ?thesis
    proof(cases "count x i = n")
      case T: True
      then have 0: "x = nat_to_mset i n"
        using True
        by (metis count_inI emptyE insert_iff multiset_eqI nat_to_msetE
            nat_to_msetE' subsetD)
      have 1: "x = nat_to_mset i (count x i)"
        using "0" T by auto
      then have LHS: "(pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) x = \<one>\<^bsub>R\<^esub>"
        using T True  0 1
        by (metis R.mset_to_IP_simp insertI1 pvar_pow)
      have 2: "UP_to_IP R i (X_poly R [^]\<^bsub>UP R\<^esub> n) x = (up_ring.monom (UP R) \<one> n) (count x i)"
        unfolding UP_to_IP_def X_poly_def using True
        by (metis ctrm_degree P.nat_pow_closed P.nat_pow_eone P_def R.one_closed UP_cring.monom_coeff
            UP_one_closed UP_r_one X_closed is_UP_cring monom_one monom_rep_X_pow to_poly_inverse
            to_poly_mult_simp(2))
      then show ?thesis
        using True T LHS P_def R.one_closed cfs_monom
        by presburger
    next
      case False
      have "(pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) = mset_to_IP R (nat_to_mset i n)"
        by (simp add: pvar_pow)
      hence 0: "(pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) x = \<zero>"
        by (metis False R.mset_to_IP_simp' nat_to_msetE)
      have 1: "UP_to_IP R i (X_poly R [^]\<^bsub>UP R\<^esub> n) x = (up_ring.monom (UP R) \<one> n) (count x i)"
        unfolding UP_to_IP_def X_poly_def  using False  True
        by (metis ctrm_degree P.nat_pow_closed P.nat_pow_eone P_def R.one_closed UP_one_closed
            UP_r_one X_closed cfs_monom monom_one monom_rep_X_pow to_poly_inverse to_poly_mult_simp(2))
      thus ?thesis using True False
        unfolding UP_to_IP_def X_poly_def 0
        by (metis P_def R.one_closed cfs_monom)
    qed
  next
    case False
    then have 0: "UP_to_IP R i (X_poly R [^]\<^bsub>UP R\<^esub> n) x = \<zero>"
      unfolding UP_to_IP_def
      by meson
    have "(pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) = mset_to_IP R (nat_to_mset i n)"
      by (simp add: pvar_pow)
    hence "(pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) x = \<zero>"
      by (metis False R.mset_to_IP_simp' count_eq_zero_iff nat_to_msetE' singleton_iff subsetI)
    then show ?thesis using 0
      by presburger
  qed
qed

lemma one_var_indexed_poly_monom_simp:
  assumes "a \<in> carrier R"
  shows "(a \<odot>\<^bsub>Pring R {i}\<^esub> ((pvar R i) [^]\<^bsub>Pring R {i}\<^esub> n)) x = (if x = (nat_to_mset i n) then a else \<zero>)"
proof-
  have 0: "(a \<odot>\<^bsub>Pring R {i}\<^esub> ((pvar R i) [^]\<^bsub>Pring R {i}\<^esub> n)) x =
                a \<otimes> (((pvar R i) [^]\<^bsub>Pring R {i}\<^esub> n) x)"
    using  Pring_smult_cfs Pring_var_closed assms cring_def is_cring monoid.nat_pow_closed ring.Pring_is_monoid singletonI
    by (simp add: monoid.nat_pow_closed ring.Pring_is_monoid R.Pring_smult_cfs R.Pring_var_closed R.ring_axioms)
  have 1: "(pvar R i) [^]\<^bsub>Pring R {i}\<^esub> n = mset_to_IP R (nat_to_mset i n)"
   using insertI1
   by (simp add: pvar_pow)
  then have 1: "(a \<odot>\<^bsub>Pring R {i}\<^esub> ((pvar R i) [^]\<^bsub>Pring R {i}\<^esub> n)) x=
              a \<otimes> (mset_to_IP R (nat_to_mset i n) x)"
    using "0" by presburger
  show ?thesis
    using assms 1 unfolding mset_to_IP_def
    using r_null r_one by simp
qed


lemma UP_to_IP_monom:
  assumes "a \<in> carrier R"
  shows "UP_to_IP R i (up_ring.monom (UP R) a n) = a \<odot>\<^bsub>Pring R {i}\<^esub> ((pvar R i)[^]\<^bsub>Pring R {i}\<^esub>n)"
proof
  fix x
  show "UP_to_IP R i (up_ring.monom (UP R) a n) x = (a \<odot>\<^bsub>Pring R {i}\<^esub> ((pvar R i) [^]\<^bsub>Pring R {i}\<^esub> n)) x"
  proof(cases "set_mset x \<subseteq> {i}")
    case True
    then show ?thesis
    proof(cases "count x i = n")
      case T: True
      then have "x = nat_to_mset i n"
        using True
        by (metis count_inI emptyE insert_iff multiset_eqI nat_to_msetE
            nat_to_msetE' subsetD)
      then have LHS: " (a \<odot>\<^bsub>Pring R {i}\<^esub> ((pvar R i) [^]\<^bsub>Pring R {i}\<^esub> n)) x = a"
        using assms
        by (simp add: one_var_indexed_poly_monom_simp)
      then show ?thesis
        unfolding UP_to_IP_def
        using T True  assms(1)
        by (metis UP_ring.cfs_monom is_UP_ring)
    next
      case False
      then show ?thesis using True
        unfolding UP_to_IP_def
        by (metis INTEG.R.nat_to_msetE P_def assms cfs_monom one_var_indexed_poly_monom_simp)
    qed
  next
    case False
    then show ?thesis
      unfolding UP_to_IP_def
      by (metis (no_types, opaque_lifting) one_var_indexed_poly_monom_simp assms
          count_eq_zero_iff  equalityD2 insert_subset nat_to_msetE' subsetI subset_eq)
  qed
qed

lemma UP_to_IP_monom':
  assumes "a \<in> carrier R"
  shows "UP_to_IP R i (up_ring.monom (UP R) a n) = a \<odot>\<^bsub>Pring R {i}\<^esub> ((pvar R i)[^]\<^bsub>Pring R {i}\<^esub>n)"
  by (metis R.Pring_smult UP_to_IP_monom assms)

lemma UP_to_IP_closed:
  assumes "p \<in> carrier P"
  shows "(UP_to_IP R i p) \<in> carrier (Pring R {i})"
  apply(rule poly_induct3[of ])
  using assms apply blast
  apply (metis P_def R.Pring_add_closed UP_to_IP_add)
proof-
  fix a fix n::nat
  assume A0: "a \<in> carrier R"
  have "(pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) \<in> carrier (Pring R {i})"
    using pvar_closed[of R ] monoid.nat_pow_closed[of "Pring R {i}"]
  proof -
    show ?thesis
      by (meson R.Pring_is_monoid R.Pring_var_closed monoid.nat_pow_closed singleton_iff)
  qed
  then show "a \<in> carrier R \<Longrightarrow>
           UP_to_IP R i (up_ring.monom P a n) \<in> carrier (Pring R {i})"
    using A0 assms(1) UP_to_IP_monom[of a i n] cring.poly_scalar_mult_closed [of R a _ "{i}"]
    by (metis P_def R.Pring_smult_closed)
qed

lemma IP_to_UP_inv:
  assumes "p \<in> carrier P"
  shows "IP_to_UP i (UP_to_IP R i p) = p"
  apply(rule poly_induct3[of ])
  using assms apply linarith
proof-
  show "\<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           IP_to_UP i (UP_to_IP R i p) = p \<Longrightarrow>
           IP_to_UP i (UP_to_IP R i q) = q \<Longrightarrow>
           IP_to_UP i (UP_to_IP R i (p \<oplus>\<^bsub>P\<^esub> q)) = p \<oplus>\<^bsub>P\<^esub> q"
  proof-
    fix p q assume A:
           "q \<in> carrier P"
           "p \<in> carrier P"
           "IP_to_UP i (UP_to_IP R i p) = p"
           "IP_to_UP i (UP_to_IP R i q) = q"
    show "IP_to_UP i (UP_to_IP R i (p \<oplus>\<^bsub>P\<^esub> q)) = p \<oplus>\<^bsub>P\<^esub> q"
      using A UP_to_IP_add[of p q i]
                  UP_to_IP_closed
                  IP_to_UP_add
      unfolding P_def
      by metis
  qed
  show "\<And>a n. a \<in> carrier R \<Longrightarrow>
           IP_to_UP i (UP_to_IP R i (up_ring.monom P a n)) =
           up_ring.monom P a n"
  proof-
    fix a fix n::nat
    assume A0: "a \<in> carrier R"
    have A1: "pvar R i [^]\<^bsub>Pring R {i}\<^esub> n \<in> carrier (Pring R {i})"
      using pvar_closed monoid.nat_pow_closed
      by (metis R.Pring_is_monoid R_cring singletonI)
    have "UP_to_IP R i (up_ring.monom (UP R) a n) = a \<odot>\<^bsub>Pring R {i}\<^esub>  (pvar R i [^]\<^bsub>Pring R {i}\<^esub> n)"
      by (meson A0 UP_to_IP_monom')
    then have A2: "IP_to_UP i (UP_to_IP R i (up_ring.monom (UP R) a n)) =
            IP_to_UP i (a \<odot>\<^bsub>Pring R {i}\<^esub> (pvar R i [^]\<^bsub>Pring R {i}\<^esub> n))"
      by presburger
    have A3: "IP_to_UP i (pvar R i [^]\<^bsub>Pring R {i}\<^esub> n) =  (up_ring.monom P \<one> n)"
    proof(induction n)
      case 0
      then show ?case
        by (metis Group.nat_pow_0 IP_to_UP_one P_def monom_one)
    next
      case (Suc n)

      then show ?case
      using IP_to_UP_ring_hom[of i]
              ring_hom_mult[of "IP_to_UP i" "Pring R {i}" "UP R" "pvar R i" "pvar R i [^]\<^bsub>Pring R {i}\<^esub> n"]
                ring_hom_ring.homh[of "Pring R {i}" "UP R"  "IP_to_UP i"]
      by (metis IP_to_UP_monom P.l_one P.nat_pow_closed P_def R.one_closed UP_cring.ctrm_degree UP_cring.monom_rep_X_pow  UP_one_closed X_closed cfs_monom is_UP_cring monom_one pvar_pow singletonI to_poly_inverse to_poly_mult_simp(1))
    qed
    then show "IP_to_UP i (UP_to_IP R i (up_ring.monom P a n)) =
           up_ring.monom P a n"
      using A2 IP_to_UP_scalar_mult[of a "pvar R i [^]\<^bsub>Pring R {i}\<^esub> n" i]
            A0 A1 P_def monic_monom_smult by presburger
  qed
qed

lemma UP_to_IP_mult:
  assumes "p \<in> carrier (UP R)"
  assumes "Q \<in> carrier (UP R)"
  shows "UP_to_IP R i (p \<otimes>\<^bsub>UP R\<^esub> Q) =
         UP_to_IP R i p \<otimes>\<^bsub>Pring R {i}\<^esub> UP_to_IP R i Q"
proof-
  have 0: "IP_to_UP i (UP_to_IP R i (p \<otimes>\<^bsub>UP R\<^esub> Q)) = (p \<otimes>\<^bsub>UP R\<^esub> Q)"
    by (meson UP_cring.IP_to_UP_inv UP_ring.UP_mult_closed assms(1) assms(2) is_UP_cring is_UP_ring)
  have 1: "IP_to_UP i (UP_to_IP R i p \<otimes>\<^bsub>Pring R {i}\<^esub> UP_to_IP R i Q) =
        IP_to_UP i (UP_to_IP R i p) \<otimes>\<^bsub>UP R\<^esub> IP_to_UP i ( UP_to_IP R i Q)"
    using IP_to_UP_ring_hom[of  i]
          ring_hom_mult[of "IP_to_UP i"]
          UP_to_IP_closed assms
    by (smt P_def ring_hom_ring.homh)
  have 2: "IP_to_UP i (UP_to_IP R i (p \<otimes>\<^bsub>UP R\<^esub> Q)) =
        IP_to_UP i (UP_to_IP R i p \<otimes>\<^bsub>Pring R {i}\<^esub> UP_to_IP R i Q)"
    using 0 1 assms
    by (metis UP_cring.IP_to_UP_inv is_UP_cring)
  then show ?thesis
    by (metis "0" P_def R.Pring_mult_closed R.ring_axioms assms(1) assms(2) ring.Pring_car UP_to_IP_closed UP_to_IP_inv)
qed

lemma UP_to_IP_ring_hom:
shows "ring_hom_ring (UP R) (Pring R {i}) (UP_to_IP R i)"
  apply(rule ring_hom_ringI)
  using P_def UP_ring apply force
  apply (simp add: R.Pring_is_ring; fail)
  apply (metis P_def UP_to_IP_closed)
  apply (meson UP_to_IP_mult)
  apply (meson UP_to_IP_add)
  by (metis IP_to_UP_one R.Pring_car R.Pring_one_closed UP_to_IP_inv)

end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>The isomorphism $R[I\cup J] \sim R[I][J]$, where $I$ and $J$ are disjoint variable sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  Given a ring $R$ and variable sets $I$ and $J$, we'd like to construct the canonical
  (iso)morphism $R[I\cup J] \to R[I][J]$. This can be done with the univeral property of the
  previous section. Let $\phi: R \to R[J]$ be the inclusion of constants, and $f: J \to R[I]$ be
  the map which sends the variable $i$ to the polynomial variable $i$ over the ring $R[I][J]$.
  Then these are the two basic pieces of input required to give us a canonical homomoprhism
  $R[I \cup J] \to R[I][J]$ with the universal property. The first map $\phi$ will be
  "\texttt{dist\_varset\_morpshim}" below, and the second map will be
  "\texttt{dist\_varset\_var\_ass}". The desired induced isomorphism will be
  called "\texttt{var\_factor}".   \<close>

definition(in ring) dist_varset_morphism
  :: "'d set \<Rightarrow> 'd set \<Rightarrow>
              ('a, (('a, 'd) mvar_poly, 'd) mvar_poly) ring_hom" where
  "dist_varset_morphism (I:: 'd set) (J:: 'd set) =
        (ring.indexed_const (Pring R J) :: ('d multiset \<Rightarrow> 'a) \<Rightarrow> 'd multiset \<Rightarrow> ('d multiset \<Rightarrow> 'a))\<circ> (ring.indexed_const R ::'a \<Rightarrow> 'd multiset \<Rightarrow> 'a)"

definition(in ring) dist_varset_var_ass
    :: "'d set \<Rightarrow> 'd set \<Rightarrow> 'd \<Rightarrow> (('a, 'd) mvar_poly, 'd) mvar_poly"
    where
"dist_varset_var_ass (I:: 'd set) (J:: 'd set)  = (\<lambda>i. if i \<in> J then ring.indexed_const (Pring R J) (pvar R i) else
                                                pvar (Pring R J) i )"

context cring
begin

lemma dist_varset_morphism_is_morphism:
  assumes "(I:: 'd set) \<subseteq> J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "\<phi> = dist_varset_morphism I J0"
  shows "ring_hom_ring R (Pring (Pring R J0) J1) \<phi>"
proof-
  have 0:"ring_hom_ring R (Pring R J0) indexed_const"
    by (simp add: indexed_const_ring_hom)
  have 1:"ring_hom_ring (Pring R J0) (Pring (Pring R J0) J1) (ring.indexed_const (Pring R J0))"
    by (simp add: cring.indexed_const_ring_hom is_cring local.ring_axioms ring.Pring_is_cring)
  show ?thesis using 0 1 assms ring_hom_trans[of "indexed_const" R "Pring R J0" "ring.indexed_const (Pring R J0)"
              "(Pring (Pring R J0) J1) "]
    unfolding dist_varset_morphism_def
  by (meson ring_hom_ring.axioms(1) ring_hom_ring.axioms(2) ring_hom_ring.homh ring_hom_ringI2)
qed

definition var_factor ::
  "'d set \<Rightarrow> 'd set \<Rightarrow> 'd set \<Rightarrow>
         (('a, 'd) mvar_poly, (('a, 'd) mvar_poly, 'd) mvar_poly) ring_hom "where
"var_factor (I:: 'd set) (J0:: 'd set) (J1:: 'd set) = indexed_poly_induced_morphism  I (Pring (Pring R J0) J1)
                                                        (dist_varset_morphism I J0) (dist_varset_var_ass I J0)"

lemma indexed_const_closed:
  assumes "x \<in> carrier R"
  shows "indexed_const x \<in> carrier (Pring R I)"
  using Pring_car assms indexed_pset.indexed_const by blast

lemma var_factor_morphism:
  assumes "(I:: 'd set) \<subseteq> J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "g = dist_varset_var_ass I J0"
  assumes "\<phi> = dist_varset_morphism I J0"
  assumes "\<psi> = (var_factor I J0 J1)"
  shows "ring_hom_ring (Pring R I) (Pring (Pring R J0) J1) \<psi> "
        "\<And>i. i \<in> J0 \<inter> I \<Longrightarrow> \<psi> (pvar R i) = ring.indexed_const (Pring R J0) (pvar R i)"
        "\<And>i. i \<in> J1 \<Longrightarrow> \<psi> (pvar R i) = pvar (Pring R J0) i"
        "\<And>a. a \<in> carrier (Pring R (J0 \<inter> I)) \<Longrightarrow> \<psi> a = ring.indexed_const (Pring R J0) a"
proof-
  have 0: "g \<in> I \<rightarrow> carrier (Pring (Pring R J0) J1)"
  proof
    fix x
    assume A0: "x \<in> I"
    then have A1: "x \<in> J0 \<or> x \<in> J1"
      by (meson UnE assms(1) subsetD)
    have A2: "x \<notin> J0 \<Longrightarrow> x \<in> J1"
      using A1 by blast
    show "g x \<in> carrier (Pring (Pring R J0) J1)"
      apply(cases "x \<in> J0")
      using assms A0 A1 A2 pvar_closed[of R x J0]
        pvar_closed[of "Pring R J0" x J1]
        cring.indexed_const_closed[of "Pring R J0" ]
      unfolding dist_varset_var_ass_def
       apply (smt Pring_is_cring is_cring)
      using assms A0 A1 A2 pvar_closed[of R x J0]
        pvar_closed[of "Pring R J0" x J1]
        cring.indexed_const_closed[of "Pring R J0" ]
      unfolding dist_varset_var_ass_def
      by (smt Pring_is_cring is_cring)
  qed
  have 1: " cring (Pring R J0)"
    by (simp add: Pring_is_cring is_cring)
  have 2: " cring (Pring (Pring R J0) J1)"
    by (simp add: "1" Pring_is_ring ring.Pring_is_cring)
  show C0: "ring_hom_ring (Pring R I) (Pring (Pring R J0) J1) \<psi> "
    using 0 assms Pring_universal_prop[of "Pring (Pring R J0) J1" g I \<phi> \<psi>]
        dist_varset_morphism_is_morphism[of I J0 J1]
    unfolding var_factor_def
    by (meson Pring_is_cring Pring_is_ring is_cring ring.Pring_is_cring)
  show C1: "\<And>i. i \<in> J0 \<inter> I \<Longrightarrow> \<psi> (pvar R i) = ring.indexed_const (Pring R J0) (pvar R i)"
    using  0 1 2 assms Pring_universal_prop(2)[of "Pring (Pring R J0) J1" g I \<phi> \<psi>]
        dist_varset_morphism_is_morphism[of I J0 J1 \<phi>] dist_varset_var_ass_def
        dist_varset_morphism_def unfolding var_factor_def  var_to_IP_def
    by (smt IntE dist_varset_var_ass_def inf_commute inf_le2 ring.Pring_is_cring subsetD var_to_IP_def)
  have 3: "\<And>i. i \<in> J1 \<Longrightarrow> g i = mset_to_IP (Pring R J0) {#i#} "
    using assms unfolding dist_varset_var_ass_def var_to_IP_def
    by (meson disjoint_iff_not_equal)
  show C2: "\<And>i. i \<in> J1 \<Longrightarrow> \<psi> (pvar R i) = pvar (Pring R J0) i"
      using  0 1 2 3 assms Pring_universal_prop(2)[of "Pring (Pring R J0) J1" g I \<phi> \<psi>]
        dist_varset_morphism_is_morphism[of I J0 J1 \<phi>]
         unfolding   var_factor_def  var_to_IP_def
         by (metis subsetD)
  have 4: "\<And>k. k \<in> carrier R \<Longrightarrow> \<psi> (indexed_const k) = ring.indexed_const (Pring R J0) (indexed_const k)"
      using  0 1 2 3 assms Pring_universal_prop(3)[of "Pring (Pring R J0) J1" g I \<phi> \<psi>]
        dist_varset_morphism_is_morphism[of I J0 J1 \<phi>] comp_apply
      unfolding   var_factor_def  var_to_IP_def dist_varset_morphism_def
      by metis
  show C3:  "\<And>a. a \<in> carrier (Pring R (J0 \<inter> I)) \<Longrightarrow> \<psi> a = ring.indexed_const (Pring R J0) a"
  proof- fix a assume A: "a \<in> carrier (Pring R (J0 \<inter> I))"
    show " \<psi> a = ring.indexed_const (Pring R J0) a"
      apply(rule indexed_pset.induct[of a "J0 \<inter> I" "carrier R"])
      using A Pring_car apply blast
      using 4
      apply blast
    proof-
      show "\<And>P Q. P \<in> Pring_set R (J0 \<inter> I) \<Longrightarrow>
           \<psi> P = ring.indexed_const (Pring R J0) P \<Longrightarrow>
           Q \<in> Pring_set R (J0 \<inter> I) \<Longrightarrow> \<psi> Q = ring.indexed_const (Pring R J0) Q \<Longrightarrow> \<psi> (P \<Oplus> Q) = ring.indexed_const (Pring R J0) (P \<Oplus> Q)"
      proof- fix P Q
        assume A0: "P \<in> Pring_set R (J0 \<inter> I)"
        assume A1: "\<psi> P = ring.indexed_const (Pring R J0) P"
        assume A2: "Q \<in> Pring_set R (J0 \<inter> I)"
        assume A3: "\<psi> Q = ring.indexed_const (Pring R J0) Q"
        have A0': "P \<in> Pring_set R I"
          using A0
          by (meson Int_lower2 Pring_carrier_subset subsetD)
        have A1': "Q \<in> Pring_set R I"
          by (meson A2 Int_lower2 Pring_carrier_subset subsetD)
        have B: "\<psi> (P \<Oplus> Q) = \<psi> P \<oplus>\<^bsub>Pring (Pring R J0) J1\<^esub> \<psi> Q"
          using A0' A1' A2 A3 C0 assms ring_hom_add
          by (metis (no_types, lifting) Pring_add local.ring_axioms ring.Pring_car ring_hom_ring.homh)
        have " ring.indexed_const (Pring R J0) (P \<Oplus> Q) =  ring.indexed_const (Pring R J0) P
                                 \<oplus>\<^bsub>Pring (Pring R J0) J1\<^esub>ring.indexed_const (Pring R J0) Q"
          by (simp add: Pring_add Pring_is_ring ring.Pring_add ring.indexed_padd_const)
        then show " \<psi> (P \<Oplus> Q) = ring.indexed_const (Pring R J0) (P \<Oplus> Q)"
          using B
          by (simp add: A1 A3)
      qed
      show "\<And>P i. P \<in> Pring_set R (J0 \<inter> I) \<Longrightarrow> \<psi> P = ring.indexed_const (Pring R J0) P \<Longrightarrow>
                    i \<in> J0 \<inter> I \<Longrightarrow> \<psi> (P \<Otimes> i) = ring.indexed_const (Pring R J0) (P \<Otimes> i)"
      proof- fix P i assume A0: "P \<in> Pring_set R (J0 \<inter> I)"
        assume A1: "\<psi> P = ring.indexed_const (Pring R J0) P"
        assume A2: "i \<in> J0 \<inter> I"
        have A0': "P \<in> carrier (Pring R I)"
          using A0  Pring_carrier_subset
          by (metis (no_types, opaque_lifting) Pring_car in_mono inf_commute le_inf_iff subset_refl)
        have A0'': "P \<in> carrier (Pring R J0)"
          using A0  Pring_carrier_subset
          by (metis (no_types, opaque_lifting) Pring_car in_mono inf_commute le_inf_iff subset_refl)
        have " \<psi> (P \<Otimes> i) = \<psi> P \<otimes>\<^bsub>Pring (Pring R J0) J1\<^esub>  ring.indexed_const (Pring R J0) (pvar R i)"
        proof-
          have "(P \<Otimes> i) = P \<otimes>\<^bsub>Pring R I\<^esub> pvar R i"
            using A0' A2 unfolding var_to_IP_def
            by (metis A0 Pring_mult poly_index_mult)
          then show ?thesis
            using A0' C0 A2 C1[of i] ring_hom_ring.homh
                  ring_hom_mult[of \<psi> "Pring R I" "Pring (Pring R J0) J1" P "pvar R i"]
          by (metis IntE Pring_var_closed)
        qed
        then have" \<psi> (P \<Otimes> i) = ring.indexed_const (Pring R J0) P \<otimes>\<^bsub>Pring (Pring R J0) J1\<^esub>
                           ring.indexed_const (Pring R J0) (pvar R i)"
          by (simp add: A1)
        then have " \<psi> (P \<Otimes> i) = ring.indexed_const (Pring R J0) (P \<otimes>\<^bsub>Pring R J0\<^esub> (pvar R i))"
          using A0'' A2  cring.indexed_const_ring_hom[of "Pring R J0" J1] ring_hom_ring.homh
                ring_hom_mult[of "ring.indexed_const (Pring R J0)" "Pring R J0" _  P "pvar R i"]
          by (smt "1" IntE Pring_var_closed)
        then show "\<psi> (P \<Otimes> i) = ring.indexed_const (Pring R J0) (P \<Otimes> i)"
          using poly_index_mult[of P J0 i] unfolding var_to_IP_def
          by (metis A0'' A2 IntE Pring_car Pring_mult)
      qed
    qed
  qed
qed

lemma var_factor_morphism':
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "\<psi> = (var_factor I J0 J1)"
  shows "ring_hom_ring (Pring R I) (Pring (Pring R J0) J1) \<psi> "
        "\<And>i. i \<in> J1 \<Longrightarrow> \<psi> (pvar R i) = pvar (Pring R J0) i"
        "\<And>a. a \<in> carrier (Pring R (J0 \<inter> I)) \<Longrightarrow> \<psi> a = ring.indexed_const (Pring R J0) a"
  using assms var_factor_morphism
  apply blast
   using assms var_factor_morphism(3)
  apply (metis subset_refl)
     using assms var_factor_morphism(4)
  by (metis Un_subset_iff Un_upper1)

text\<open>Constructing the inverse morphism for \texttt{var\_factor\_morphism} \<close>


lemma pvar_ass_closed:
  assumes "J1 \<subseteq> I"
  shows "pvar R \<in> J1 \<rightarrow> carrier (Pring R I)"
  by (meson Pi_I Pring_var_closed assms subsetD)

text\<open>The following function gives us the inverse morphism $R[I][J] \to R[I \cup J]$:\<close>
definition var_factor_inv :: "'d set \<Rightarrow> 'd set \<Rightarrow> 'd set \<Rightarrow>
  ((('a, 'd) mvar_poly, 'd) mvar_poly, ('a, 'd) mvar_poly) ring_hom" where
"var_factor_inv (I:: 'd set) (J0:: 'd set) (J1:: 'd set) = indexed_poly_induced_morphism J1 (Pring R I)
                                                        (id:: ('d multiset \<Rightarrow> 'a) \<Rightarrow> 'd multiset \<Rightarrow> 'a)
                                                       (pvar R)"

lemma var_factor_inv_morphism:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "\<psi> = (var_factor_inv I J0 J1)"
  shows "ring_hom_ring (Pring (Pring R J0) J1) (Pring R I)  \<psi> "
        "\<And>i. i \<in> J1 \<Longrightarrow> \<psi> (pvar (Pring R J0) i) = pvar R i"
        "\<And>a. a \<in> carrier (Pring R J0) \<Longrightarrow> \<psi> (ring.indexed_const (Pring R J0) a) = a"
proof-
  have 0:  "ring_hom_ring (Pring R J0) (Pring R I) id"
    apply(rule ring_hom_ringI)
      apply (simp add: Pring_is_ring; fail)
        apply (simp add: Pring_is_ring;fail )
       apply (metis Pring_car Pring_carrier_subset Un_upper1 assms(1) id_apply subsetD)
    apply (metis Pring_mult_eq id_apply)
     apply (metis Pring_add_eq id_apply)
  by (simp add: Pring_one_eq)
  then show "ring_hom_ring (Pring (Pring R J0) J1) (Pring R I)  \<psi> "
    using cring.Pring_universal_prop(1)[of "Pring R J0" "Pring R I" "pvar R" J1 id \<psi>]
        pvar_ass_closed[of J0 I]
    by (metis Pring_is_cring assms(2) assms(4) is_cring pvar_ass_closed var_factor_inv_def)
  show "\<And>i. i \<in> J1 \<Longrightarrow> \<psi> (pvar (Pring R J0) i) = pvar R i"
    using 0 assms pvar_ass_closed[of J0 I]
        cring.Pring_universal_prop(2)[of "Pring R J0" "Pring R I" "pvar R" J1 id \<psi>]
    by (metis Pring_is_cring is_cring pvar_ass_closed var_factor_inv_def var_to_IP_def)
  show "\<And>a. a \<in> carrier (Pring R J0) \<Longrightarrow> \<psi> (ring.indexed_const (Pring R J0) a) = a"
    using 0 assms pvar_ass_closed[of J0 I]
        cring.Pring_universal_prop(3)[of "Pring R J0" "Pring R I" "pvar R" J1 id \<psi>]
    by (smt Pi_I Pring_is_cring Pring_var_closed id_def is_cring subsetD var_factor_inv_def)
qed

lemma var_factor_inv_inverse:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "\<psi>1 = (var_factor_inv I J0 J1)"
  assumes "\<psi>0 = (var_factor I J0 J1)"
  assumes "P \<in> carrier (Pring R I)"
  shows "\<psi>1 (\<psi>0 P) = P"
  apply(rule indexed_pset.induct[of P I "carrier R"])
  using Pring_car assms(6) apply blast
    using var_factor_inv_morphism(3)[of I J0 J1 "\<psi>1"] var_factor_morphism'(3)[of I J0 J1 \<psi>0] assms
    apply (metis indexed_const_closed inf_sup_absorb)
proof-
  have 0: "ring_hom_ring (Pring (Pring R J0) J1) (Pring R I) \<psi>1"
    by (simp add: assms(1) assms(3) assms(4) var_factor_inv_morphism(1))
  have 1: "ring_hom_ring (Pring R I) (Pring (Pring R J0) J1) \<psi>0"
    by (simp add: assms(1) assms(3) assms(5) var_factor_morphism'(1))
  have 2: "\<psi>1 \<circ> \<psi>0 \<in> ring_hom (Pring R I) (Pring R I)"
    using 0 1 ring_hom_trans[of \<psi>0 "Pring R I" "Pring (Pring R J0) J1" \<psi>1 "Pring R I"]
          ring_hom_ring.homh[of "Pring R I" "Pring (Pring R J0) J1" \<psi>0]
          ring_hom_ring.homh[of "Pring (Pring R J0) J1" "Pring R I" \<psi>1]
    by blast
  show "\<And>P Q. P \<in> Pring_set R I \<Longrightarrow>
           \<psi>1 (\<psi>0 P) = P \<Longrightarrow> Q \<in> Pring_set R I \<Longrightarrow> \<psi>1 (\<psi>0 Q) = Q \<Longrightarrow> \<psi>1 (\<psi>0 (P \<Oplus> Q)) = P \<Oplus> Q"
  proof- fix P Q assume A0: "P \<in> Pring_set R I" "\<psi>1 (\<psi>0 P) = P"
    assume A1: "Q \<in> Pring_set R I" "\<psi>1 (\<psi>0 Q) = Q"
    show "\<psi>1 (\<psi>0 (P \<Oplus> Q)) = P \<Oplus> Q"
      using  A0 A1 2 ring_hom_add[of "\<psi>1 \<circ> \<psi>0" "Pring R I" "Pring R I" P Q] comp_apply[of \<psi>1 \<psi>0]
      by (simp add: "2" \<open>P \<in> Pring_set R I\<close> \<open>Q \<in> Pring_set R I\<close> Pring_add Pring_car)
  qed
  show "\<And>P i. P \<in> Pring_set R I \<Longrightarrow> \<psi>1 (\<psi>0 P) = P \<Longrightarrow> i \<in> I \<Longrightarrow> \<psi>1 (\<psi>0 (P \<Otimes> i)) = P \<Otimes> i"
  proof-
    fix P i assume A: "P \<in> Pring_set R I" "\<psi>1 (\<psi>0 P) = P" "i \<in> I"
    show "\<psi>1 (\<psi>0 (P \<Otimes> i)) = P \<Otimes> i"
    proof-
      have A0: "P \<Otimes> i = P \<otimes>\<^bsub>Pring R I\<^esub> pvar R i"
        by (metis A(1) A(3) Pring_mult local.ring_axioms ring.poly_index_mult var_to_IP_def)
      have A1: "\<psi>1 (\<psi>0 (pvar R i)) = pvar R i"
       by (metis A(3) Int_iff Pring_var_closed UnE Un_subset_iff Un_upper1 assms(1) assms(2)
           assms(3) assms(4) assms(5) cring.var_factor_morphism(2) is_cring
           var_factor_inv_morphism(2) var_factor_inv_morphism(3) var_factor_morphism'(2))
     then show ?thesis
       using 2 A0 A ring_hom_mult[of "\<psi>1 \<circ> \<psi>0" "Pring R I" _  P "pvar R i" ]
            Pring_car Pring_var_closed comp_apply[of \<psi>1 \<psi>0]
       by smt
   qed
 qed
qed

lemma var_factor_total_eval:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "\<psi> = (var_factor I J0 J1)"
  assumes "closed_fun R g"
  assumes "P \<in> carrier (Pring R I)"
  shows "total_eval R g P = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P))"
  apply(rule indexed_pset.induct[of P I "carrier R"])
  using Pring_car assms apply blast
    apply (metis Pring_is_cring assms(1) assms(2) assms(3) assms(4) cring.total_eval_const
      indexed_const_closed is_cring var_factor_morphism'(3))
proof-
  show "\<And>P Q. P \<in> Pring_set R I \<Longrightarrow>
           total_eval R g P = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P)) \<Longrightarrow>
           Q \<in> Pring_set R I \<Longrightarrow>
           total_eval R g Q = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> Q)) \<Longrightarrow>
           total_eval R g (P \<Oplus> Q) = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Oplus> Q)))"
  proof- fix P Q
    assume A: " P \<in> Pring_set R I"
           "total_eval R g P = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P))"
    assume B: " Q \<in> Pring_set R I"
           "total_eval R g Q = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> Q))"
    have 0: "\<psi> (P \<Oplus> Q) = \<psi> P \<oplus>\<^bsub>Pring (Pring R J0) J1\<^esub> \<psi> Q"
      using A B assms var_factor_morphism'(1)[of I J0 J1 \<psi>]
            Pring_add[of I P Q] Pring_car[of I]
            ring_hom_ring.homh[of "Pring R I" "Pring (Pring R J0) J1" \<psi>]
            ring_hom_add[of \<psi> "Pring R I" "Pring (Pring R J0) J1" P Q]
      by metis
    have 1: "closed_fun (Pring R J0) (indexed_const \<circ> g)"
      using assms comp_apply
      by (smt Pi_I closed_fun_simp indexed_const_closed)
    have 2: "\<psi> P \<in> carrier (Pring (Pring R J0) J1)"
      using assms A var_factor_morphism'(1)[of I J0 J1 \<psi>]
            ring_hom_ring.homh ring_hom_closed Pring_car
      by metis
    have 3: "\<psi> Q \<in> carrier (Pring (Pring R J0) J1)"
      using assms B var_factor_morphism'(1)[of I J0 J1 \<psi>]
          ring_hom_ring.homh ring_hom_closed Pring_car
      by metis
    have 4: "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Oplus> Q))) =
            (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P)) \<oplus>\<^bsub>Pring R J0\<^esub>
            (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> Q))"
      using 0 1 2 3 A B assms cring.total_eval_add[of "Pring R J0" "\<psi> P" J1 "\<psi> Q" "indexed_const \<circ> g"]
      by (metis Pring_car Pring_is_cring is_cring)
    have 5: "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P)) \<in> carrier (Pring R J0)"
      using 3 assms cring.total_eval_closed "1" "2" Pring_is_cring is_cring
      by blast
    have 6: "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> Q)) \<in> carrier (Pring R J0)"
      using 4 assms  "1" "3" Pring_is_cring cring.total_eval_closed is_cring
      by blast
    show "total_eval R g (P \<Oplus> Q) = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Oplus> Q)))"
      using 5 6 4 assms
            total_eval_add[of  "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> p))" J0
                              "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> Q))" ]
      by (smt A(1) A(2) B(1) B(2) Pring_add Pring_car in_mono indexed_pset_mono order_refl
          subsetD subset_iff total_eval_add)
  qed
  show "\<And>P i. P \<in> Pring_set R I \<Longrightarrow>
           total_eval R g P = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P)) \<Longrightarrow>
           i \<in> I \<Longrightarrow> total_eval R g (P \<Otimes> i) = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Otimes> i)))"
  proof- fix P i
    assume A: "P \<in> Pring_set R I"
           "total_eval R g P = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P))"
           "i \<in> I"
    have 0: "(P \<Otimes> i) = P \<otimes>\<^bsub>Pring R I\<^esub> (pvar R i)"
      using A poly_index_mult
      by (metis Pring_mult var_to_IP_def)
    have 1: "\<psi> (P \<Otimes> i) = \<psi> P \<otimes>\<^bsub>Pring (Pring R J0) J1\<^esub> \<psi> (pvar R i)"
      using 0 A assms var_factor_morphism'(1)[of I J0 J1 \<psi>]
            pvar_closed[of R i] ring_hom_mult ring_hom_ring.homh
      by (smt Pring_car Pring_var_closed)
    have 2: "\<psi> P \<in> carrier (Pring (Pring R J0) J1)"
      using assms A var_factor_morphism'(1)[of I J0 J1 \<psi>]
            ring_hom_ring.homh ring_hom_closed Pring_car
      by metis
    have 3: "\<psi> (pvar R i) \<in> carrier (Pring (Pring R J0) J1)"
      using assms A var_factor_morphism'(1)[of I J0 J1 \<psi>]
            ring_hom_ring.homh ring_hom_closed Pring_car pvar_closed[of R i I]
      by (metis is_cring)
    have 4: "closed_fun (Pring R J0) (indexed_const \<circ> g)"
      apply(rule cring.closed_funI)
      using Pring_is_cring is_cring apply blast
            using assms indexed_const_closed closed_fun_simp[of g] comp_apply[of indexed_const g]
          proof -
            fix x :: 'c
            show "(indexed_const \<circ> g) x \<in> carrier (Pring R J0)"
              by (metis (no_types) \<open>\<And>n. closed_fun R g \<Longrightarrow> g n \<in> carrier R\<close> \<open>\<And>x. (indexed_const \<circ> g) x = indexed_const (g x)\<close> \<open>closed_fun R g\<close> indexed_const_closed)
          qed
    have 5: "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Otimes> i))) =
              (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P)) \<otimes>\<^bsub>Pring R J0\<^esub>
              (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (pvar R i)))"
      using 2 3 4 cring.total_eval_ring_hom[of "Pring R J0" "indexed_const \<circ> g" J1]
      by (metis "1" Pring_is_cring cring.total_eval_mult is_cring)
    have 6: "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P)) \<in> carrier (Pring R J0)"
      using total_eval_closed "2" "4" Pring_is_cring cring.total_eval_closed is_cring
      by blast
    have 7: " (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (pvar R i))) \<in> carrier (Pring R J0)"
      using "3" "4" Pring_is_cring cring.total_eval_closed is_cring
      by blast
    have 8: " total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Otimes> i))) =
              total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> P)) \<otimes>\<^bsub>R\<^esub>
              total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (pvar R i)))"
      using 6 7
      by (metis "5" assms(5) cring.total_eval_mult is_cring)
    have 9: " total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Otimes> i))) =
              total_eval R g P \<otimes>\<^bsub>R\<^esub>
              total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (pvar R i)))"
      using "8" A(2)
      by presburger
    have 10: "total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (pvar R i))) =
              g i"
    proof(cases "i \<in> J0")
      case True
      then have "\<psi> (pvar R i) = ring.indexed_const (Pring R J0) (pvar R i)"
        using assms
        by (metis Pring_var_closed inf_sup_absorb var_factor_morphism'(3))
      then have "(total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (pvar R i))) =  (pvar R i)"
        by (metis Pring_is_cring Pring_var_closed True cring.total_eval_const is_cring)
      then show ?thesis
        using total_eval_var[of g i] assms var_to_IP_def
        by metis
    next
      case False
      then have "\<psi> (pvar R i) = (pvar  (Pring R J0)  i)"
        by (metis A(3) UnE assms(1) assms(2) assms(3) assms(4) cring.var_factor_morphism'(2) is_cring)
      then have "total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (pvar R i)) =
                  indexed_const (g i)"
        using cring.total_eval_var[of "Pring R J0" "indexed_const \<circ> g" i] comp_apply
        by (metis "4" Pring_is_cring is_cring var_to_IP_def)
      then show ?thesis
        using total_eval_const[of "g i" g] assms closed_fun_simp[of g i]
        by metis
    qed
    show "total_eval R g (P \<Otimes> i) = total_eval R g (total_eval (Pring R J0) (indexed_const \<circ> g) (\<psi> (P \<Otimes> i)))"
      using 9 10
      by (metis A(1) A(3) Pring_car assms(5) total_eval_indexed_pmult)
  qed
qed

lemma var_factor_closed:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "P \<in> carrier (Pring R I)"
  shows "var_factor I J0 J1 P \<in> carrier (Pring (Pring R J0 ) J1)"
  using assms var_factor_morphism'[of I J0 J1] ring_hom_ring.homh
  by (metis ring_hom_closed)

lemma var_factor_add:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  shows "var_factor I J0 J1 (P \<oplus>\<^bsub>Pring R I\<^esub> Q) = var_factor I J0 J1 P \<oplus>\<^bsub>Pring (Pring R J0) J1\<^esub>
                                                 var_factor I J0 J1 Q"
  using assms var_factor_morphism'[of I J0 J1] ring_hom_ring.homh
  by (metis (no_types, lifting) ring_hom_add)

lemma var_factor_mult:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  shows "var_factor I J0 J1 (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = var_factor I J0 J1 P \<otimes>\<^bsub>Pring (Pring R J0) J1\<^esub>
                                                 var_factor I J0 J1 Q"
  using assms var_factor_morphism'[of I J0 J1] ring_hom_ring.homh
  by (metis (no_types, lifting) ring_hom_mult)

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Viewing a Mulitvariable Polynomial as a Univariate Polynomial over a Multivariate Polynomial Base Ring\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition multivar_poly_to_univ_poly ::
 "'c set \<Rightarrow> 'c \<Rightarrow> ('a,'c) mvar_poly \<Rightarrow>
       (('a,'c) mvar_poly) u_poly  " where
"multivar_poly_to_univ_poly I i P = ((IP_to_UP i) \<circ> (var_factor I (I - {i}) {i})) P"

definition univ_poly_to_multivar_poly ::
  "'c set \<Rightarrow> 'c \<Rightarrow> (('a,'c) mvar_poly) u_poly \<Rightarrow>
        ('a,'c) mvar_poly"  where
"univ_poly_to_multivar_poly I i P =((var_factor_inv I (I - {i}) {i}) \<circ> (UP_to_IP (Pring R (I - {i})) i)) P"

lemma multivar_poly_to_univ_poly_is_hom:
  assumes "i \<in> I"
  shows "multivar_poly_to_univ_poly I i \<in> ring_hom (Pring R I) (UP (Pring R (I - {i})))"
  unfolding multivar_poly_to_univ_poly_def comp_apply
  apply(rule ring_hom_compose[of _ "Pring (Pring R (I - {i})) {i}" _ "var_factor I (I - {i}) {i}" "IP_to_UP i"])
       apply (simp add: Pring_is_ring; fail)
      apply (simp add: local.ring_axioms ring.Pring_is_ring; fail)
     apply(rule UP_ring.UP_ring) unfolding UP_ring_def
     apply (simp add: Pring_is_ring; fail)
    using assms var_factor_morphism'[of I "I - {i}" "{i}"] unfolding ring_hom_ring_def ring_hom_ring_axioms_def
    apply blast
    using UP_cring.IP_to_UP_ring_hom[of "Pring R (I - {i})" i]
    unfolding ring_hom_ring_def ring_hom_ring_axioms_def UP_cring_def
    using Pring_is_cring is_cring apply blast
    by blast

lemma multivar_poly_to_univ_poly_inverse:
  assumes "i \<in> I"
  assumes "\<psi>0 = multivar_poly_to_univ_poly I i"
  assumes "\<psi>1 = univ_poly_to_multivar_poly I i"
  assumes "P \<in> carrier (Pring R I)"
  shows "\<psi>1 (\<psi>0 P) = P"
proof-
  have closed: "var_factor I (I - {i}) {i} P \<in> carrier (Pring (Pring R (I - {i})) {i})"
    using assms var_factor_closed[of I "I - {i}" "{i}" P]
    by blast
  have cancel_1: "UP_to_IP (Pring R (I - {i})) i
                  (IP_to_UP i (var_factor I (I - {i}) {i} P)) =
                        var_factor I (I - {i}) {i} P"
    using closed assms  ring.Pring_car
          UP_cring.UP_to_IP_inv[of "Pring R (I - {i})" "var_factor I (I - {i}) {i} P" i]
          Pring_is_ring unfolding UP_cring_def
    using is_cring local.ring_axioms ring.Pring_is_cring
    by blast
  have "univ_poly_to_multivar_poly I i (multivar_poly_to_univ_poly I i P) =
        univ_poly_to_multivar_poly I i ((IP_to_UP i) (var_factor I (I - {i}) {i} P))"
    by (metis comp_apply multivar_poly_to_univ_poly_def)
  then have "univ_poly_to_multivar_poly I i (multivar_poly_to_univ_poly I i P) =
        ((var_factor_inv I (I - {i}) {i})  ((UP_to_IP (Pring R (I - {i})) i)
                 ((IP_to_UP i) (var_factor I (I - {i}) {i} P))))"
    using comp_apply univ_poly_to_multivar_poly_def
    by metis
  then have "univ_poly_to_multivar_poly I i (multivar_poly_to_univ_poly I i P) =
        ((var_factor_inv I (I - {i}) {i})  (var_factor I (I - {i}) {i} P))"
    using cancel_1
    by presburger
  then show ?thesis using assms var_factor_inv_inverse[of I "I - {i}" "{i}" _ _ P]
    by (metis Diff_cancel Diff_disjoint Diff_eq_empty_iff Diff_partition Un_Diff_cancel
        Un_Diff_cancel2 Un_insert_right empty_Diff empty_subsetI insert_Diff_if insert_absorb )
qed

lemma multivar_poly_to_univ_poly_total_eval:
  assumes "i \<in> I"
  assumes "\<psi> = multivar_poly_to_univ_poly I i"
  assumes "P \<in> carrier (Pring R I)"
  assumes "closed_fun R g"
  shows "total_eval R g P = total_eval R g (to_function (Pring R (I - {i})) (\<psi> P) (indexed_const (g i)))"
proof-
  have 0: "var_factor I (I - {i}) {i} P \<in> Pring_set (Pring R (I - {i})) {i}"
  proof-
    have 00: " ring (Pring R (I - {i}))"
      using Pring_is_ring
      by blast
    then show ?thesis
      using assms(1) assms(3) var_factor_closed[of I "I - {i}" "{i}" P] ring.Pring_car[of "Pring R (I - {i})" "{i}"]
      by blast
  qed
  have 1: "closed_fun (Pring R (I - {i})) (indexed_const \<circ> g)"
    using assms comp_apply  indexed_const_closed cring.closed_funI[of "Pring R (I - {i})"]
    by (metis Pring_is_cring closed_fun_simp is_cring)
  have 2: "cring (Pring R (I - {i}))"
    using Pring_is_cring is_cring by blast
  have "(to_function (Pring R (I - {i})) (\<psi> P) (indexed_const (g i)))
        =  total_eval (Pring R (I - {i})) (indexed_const \<circ> g) ((var_factor I (I - {i}) {i}) P) "
    using assms 0 1 2 comp_apply UP_cring.IP_to_UP_poly_eval[of "Pring R (I - {i})"
                                             "(var_factor I (I - {i}) {i}) P" i "indexed_const \<circ> g"]
    unfolding UP_cring_def multivar_poly_to_univ_poly_def
    by metis
  then have 3: "total_eval R g ((to_function (Pring R (I - {i})) (\<psi> P) (indexed_const (g i))) )
        = total_eval R g ( total_eval (Pring R (I - {i})) (indexed_const \<circ> g) ((var_factor I (I - {i}) {i}) P)) "
    by presburger
  then have "total_eval R g P = total_eval R g (total_eval (Pring R (I - {i})) (indexed_const \<circ> g) ((var_factor I (I - {i}) {i}) P)) "
    using assms var_factor_total_eval[of I "I - {i}" "{i}" "var_factor I (I - {i}) {i}" g P]
    by blast
  then show ?thesis
    using 3
    by presburger
qed

text\<open>
  Induction for polynomial rings. Basically just \texttt{indexed\_pset.induct} with some
  boilerplate translations removed
\<close>

lemma(in ring) Pring_car_induct'':
  assumes "Q \<in> carrier (Pring R I)"
  assumes "\<And>c. c \<in> carrier R \<Longrightarrow> P (indexed_const c)"
  assumes "\<And>p q. p \<in> carrier (Pring R I) \<Longrightarrow> q \<in> carrier (Pring R I) \<Longrightarrow> P p \<Longrightarrow> P q \<Longrightarrow> P (p \<oplus>\<^bsub>Pring R I\<^esub> q)"
  assumes "\<And>p i. p \<in> carrier (Pring R I) \<Longrightarrow> i \<in> I \<Longrightarrow> P p \<Longrightarrow> P (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i)"
  shows "P Q"
  apply(rule indexed_pset.induct[of Q I "carrier R"])
  using Pring_car assms(1) apply blast
  using assms(2) apply blast
  apply (metis (full_types) Pring_add Pring_car assms(3))
proof-
  fix Pa i assume A: "Pa \<in> Pring_set R I" "P Pa" "i \<in> I"
  then have 0: "Pa \<in> carrier (Pring R I)"
    using  assms A Pring_car
    by blast
  have "Pa \<Otimes> i = Pa \<otimes>\<^bsub>Pring R I\<^esub> pvar R i"
    using 0 poly_index_mult assms A
    by (metis Pring_mult var_to_IP_def)
  then show "P (Pa \<Otimes> i)"
    by (simp add: "0" A(2) A(3) assms)
qed

subsubsection\<open>Application: A Polynomial Ring over a Domain is a Domain\<close>

text \<open>
  In this section, we use the fact the UP \<open>R\<close> is a domain when \<open>R\<close> is a domain to show the analogous
  result for indexed polynomial rings. We first prove it inductively for rings with a finite
  variable set, and then generalize to infinite variable sets using the fact that any two
  multivariable polynomials over an indexed polynomial ring must also lie in a finitely indexed
  polynomial subring.
\<close>

lemma indexed_const_mult:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "indexed_const a \<otimes>\<^bsub> Pring R I\<^esub> indexed_const b  = indexed_const (a \<otimes>  b)"
  by (metis Pring_mult assms(1) assms(2) indexed_const_P_mult_eq)

lemma(in domain) Pring_fin_vars_is_domain:
  assumes "finite (I ::'c set)"
  shows "domain (Pring R I)"
proof(rule finite_induct, rule assms)
  show "domain (Pring R ({}::'c set))"
  proof(rule domainI)
    show " cring (Pring R {})"
      by (simp add: Pring_is_cring is_cring)
    show "\<one>\<^bsub>Pring R {}\<^esub> \<noteq> \<zero>\<^bsub>Pring R {}\<^esub>"
    proof-
      have "\<one>\<^bsub>Pring R {}\<^esub> {#} \<noteq> \<zero>\<^bsub>Pring R {}\<^esub> {#}"
        by (metis Pring_one Pring_zero local.ring_axioms ring.indexed_const_def zero_not_one)
      thus ?thesis
        by metis
    qed
    show "\<And>a b. a \<otimes>\<^bsub>Pring R ({}::'c set)\<^esub> b = \<zero>\<^bsub>Pring R {}\<^esub> \<Longrightarrow>
           a \<in> carrier (Pring R {}) \<Longrightarrow> b \<in> carrier (Pring R {}) \<Longrightarrow> a = \<zero>\<^bsub>Pring R {}\<^esub> \<or> b = \<zero>\<^bsub>Pring R {}\<^esub>"
    proof-
      fix a b assume A: "a \<otimes>\<^bsub>Pring R ({}::'c set)\<^esub> b = \<zero>\<^bsub>Pring R {}\<^esub>"
           "a \<in> carrier (Pring R {})" " b \<in> carrier (Pring R {})"
      have 0: "monomials_of R a \<subseteq> {{#}}"
        using A Pring_set_zero unfolding monomials_of_def Pring_car
        by blast
      have 1: "monomials_of R b \<subseteq> {{#}}"
        using A Pring_set_zero unfolding monomials_of_def Pring_car
        by blast
      obtain A where A_def: "A = a {#}"
        by blast
      obtain B where B_def: "B = b {#}"
        by blast
      have 2: "a = indexed_const A"
        unfolding A_def
        apply(rule ext)
        by (metis 0 complement_of_monomials_of empty_iff in_mono indexed_const_def insert_iff)
      have 3: "b = indexed_const B"
        unfolding B_def
        apply(rule ext)
        by (metis 1 complement_of_monomials_of empty_iff in_mono indexed_const_def insert_iff)
      have 4: "a \<otimes>\<^bsub>Pring R {}\<^esub> b = indexed_const (A \<otimes> B)"
        using A unfolding 2 3
        by (metis "2" "3" A_def B_def Pring_carrier_coeff' indexed_const_mult)
      have 5: "A \<otimes> B = \<zero>"
        using A unfolding 4 by (metis Pring_zero indexed_const_def)
      have 6: "A = \<zero> \<or> B = \<zero>"
        using 5 A_def B_def A
        by (simp add: domain.integral_iff domain_axioms)
      show "a = \<zero>\<^bsub>Pring R {}\<^esub> \<or> b = \<zero>\<^bsub>Pring R {}\<^esub>"
        unfolding 2 3 using 6
        by (metis Pring_zero)
    qed
  qed
  show "\<And>x F. finite (F:: 'c set) \<Longrightarrow> x \<notin> F \<Longrightarrow> domain (Pring R F) \<Longrightarrow> domain (Pring R (insert x F))"
  proof- fix S:: "'c set"  fix s assume A: "finite S" "s \<notin> S" "domain (Pring R S)"
    show "domain (Pring R (insert s S))"
    proof-
      have ring_hom: "multivar_poly_to_univ_poly (insert s S) s \<in> ring_hom (Pring R (insert s S)) (UP (Pring R S))"
        using multivar_poly_to_univ_poly_is_hom
        by (metis A(2) Diff_insert_absorb insertI1)
      have domain: "domain (UP (Pring R S))"
        apply(rule UP_domain.UP_domain)
        unfolding UP_domain_def by(rule A)
      show "domain (Pring R (insert s S))"
        apply(rule ring_hom_ring.inj_on_domain[of _ "UP (Pring R S)" "multivar_poly_to_univ_poly (insert s S) s"])
          apply(rule ring_hom_ring.intro)
            apply (simp add: Pring_is_ring; fail)
           apply(rule UP_ring.UP_ring)
        unfolding UP_ring_def
        apply (simp add: Pring_is_ring; fail)
        unfolding ring_hom_ring_axioms_def apply(rule ring_hom)
      proof(rule inj_onI)
        fix x y assume A: "x \<in> carrier (Pring R (insert s S))"
           "y \<in> carrier (Pring R (insert s S))"
           "multivar_poly_to_univ_poly (insert s S) s x = multivar_poly_to_univ_poly (insert s S) s y"
        then have 0: "univ_poly_to_multivar_poly (insert s S) s (multivar_poly_to_univ_poly (insert s S) s x)
       = univ_poly_to_multivar_poly (insert s S) s (multivar_poly_to_univ_poly (insert s S) s y)"
          by auto
        have 1: "univ_poly_to_multivar_poly (insert s S) s (multivar_poly_to_univ_poly (insert s S) s x) = x"
          using A by (meson cring.multivar_poly_to_univ_poly_inverse insertI1 is_cring)
        have 2: "univ_poly_to_multivar_poly (insert s S) s (multivar_poly_to_univ_poly (insert s S) s y) = y"
          using A  by (meson insertI1 multivar_poly_to_univ_poly_inverse)
        show "x = y"
          using 0 unfolding 1 2 by auto
      next
        show "domain (UP (Pring R S))"
          apply(rule UP_domain.UP_domain)
          unfolding UP_domain_def by(rule A)
      qed
    qed
  qed
qed

lemma locally_finite:
  assumes "a \<in> carrier (Pring R I)"
  shows "\<exists>J. J \<subseteq> I \<and> finite J \<and> a \<in> carrier (Pring R J)"
proof(rule Pring_car_induct[of _ I], rule assms)
  have 0: "\<zero>\<^bsub>Pring R I\<^esub> = \<zero>\<^bsub>Pring R {}\<^esub>"
    by (simp add: Pring_zero_eq)
  show "\<exists>J\<subseteq>I. finite J \<and> \<zero>\<^bsub>Pring R I\<^esub> \<in> carrier (Pring R J)"
    unfolding 0
    by (meson Pring_zero_closed empty_subsetI finite.emptyI)
next
  fix m k assume A: "set_mset m \<subseteq> I \<and> k \<in> carrier R"
  obtain J where J_def: "J = set_mset m"
    by blast
  have 0: "k \<odot>\<^bsub>Pring R I\<^esub> mset_to_IP R m = k \<odot>\<^bsub>Pring R J\<^esub> mset_to_IP R m"
    unfolding J_def by (simp add: Pring_smult)
  have 1: "k \<odot>\<^bsub>Pring R I\<^esub> mset_to_IP R m \<in> carrier (Pring R J)"
    unfolding 0 J_def using A
    by (simp add: Pring_car Pring_smult mset_to_IP_closed poly_scalar_mult_closed)
  show "\<exists>J\<subseteq>I. finite J \<and> k \<odot>\<^bsub>Pring R I\<^esub> mset_to_IP R m \<in> carrier (Pring R J)"
    using J_def 1 A by blast
next
  fix Q m k
  assume A: "Q \<in> carrier (Pring R I)\<and>(\<exists>J\<subseteq>I. finite J \<and> Q \<in> carrier (Pring R J)) \<and> set_mset m \<subseteq> I \<and> k \<in> carrier R"
  then obtain J where J_def: "J\<subseteq>I \<and> finite J \<and> Q \<in> carrier (Pring R J)"
    by blast
  obtain J' where J'_def: "J' = J \<union> set_mset m"
    by blast
  have 0: "finite J'"
    unfolding J'_def using J_def by blast
  have 1: "k \<odot>\<^bsub>Pring R I\<^esub> mset_to_IP R m = k \<odot>\<^bsub>Pring R J'\<^esub> mset_to_IP R m"
    unfolding J'_def using A by (simp add: Pring_smult)
  have 2: "Q \<in> carrier (Pring R J')"
    using J_def unfolding J'_def
    by (metis Pring_car Pring_carrier_subset Un_upper1 subsetD)
  have 3: "Q \<Oplus> k \<odot>\<^bsub>Pring R I\<^esub> mset_to_IP R m \<in> carrier (Pring R J')"
    using 0 1 2 J'_def A
    by (metis Pring_car Pring_smult_closed indexed_pset.indexed_padd mset_to_IP_closed sup.cobounded2)
  show "\<exists>J'\<subseteq>I. finite J' \<and> Q \<Oplus> k \<odot>\<^bsub>Pring R I\<^esub> mset_to_IP R m \<in> carrier (Pring R J')"
    using 3 0
    by (metis A J'_def J_def Un_subset_iff)
qed

lemma(in domain) Pring_is_domain:
  "domain (Pring R I)"
proof(rule domainI, simp add: Pring_is_cring is_cring)
  have 0: "\<one>\<^bsub>Pring R I\<^esub> {#} = \<one>"
    by (simp add: Pring_one indexed_const_def)
  have 1: "\<zero>\<^bsub>Pring R I\<^esub> {#} = \<zero>"
    by (simp add: Pring_zero indexed_const_def)
  have 2: "\<one> \<noteq> \<zero>"
    by simp
  show "\<one>\<^bsub>Pring R I\<^esub> \<noteq> \<zero>\<^bsub>Pring R I\<^esub>"
    using 0 1 2 by auto
next
  fix a b assume A: "a \<otimes>\<^bsub>Pring R I\<^esub> b = \<zero>\<^bsub>Pring R I\<^esub>"
                    "a \<in> carrier (Pring R I)"
                    "b \<in> carrier (Pring R I)"
  obtain J0 where J0_def: "J0 \<subseteq> I \<and> finite J0 \<and> a \<in> carrier (Pring R J0)"
    using A locally_finite by blast
  obtain J1 where J1_def: "J1 \<subseteq> I \<and> finite J1 \<and> b \<in> carrier (Pring R J1)"
    using A locally_finite by blast
  obtain J where J_def: "J = J0 \<union> J1"
    by blast
  have J_finite: "finite J"
    using J_def J0_def J1_def by blast
  have 0: "a \<in> carrier (Pring R J)"
    using J0_def unfolding J_def
    by (metis (no_types, lifting) Pring_car Pring_carrier_subset Un_upper1 subset_eq)
  have 1: "b \<in> carrier (Pring R J)"
    using J1_def unfolding J_def
    by (metis Pring_car Pring_carrier_subset in_mono sup.cobounded2)
  have 2: "a \<otimes>\<^bsub>Pring R J\<^esub> b = \<zero>\<^bsub>Pring R J\<^esub>"
    using A J_def 0 1 by (metis Pring_mult_eq Pring_zero_eq)
  have 3: "domain (Pring R J)"
    using J_finite Pring_fin_vars_is_domain[of J] by blast
  have 4: "a = \<zero>\<^bsub>Pring R J\<^esub> \<or> b = \<zero>\<^bsub>Pring R J\<^esub>"
    using 3 2 0 1  by (simp add: domain.integral)
  thus "a = \<zero>\<^bsub>Pring R I\<^esub> \<or> b = \<zero>\<^bsub>Pring R I\<^esub>"
    using Pring_zero_eq by blast
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Relabelling of Variables for Indexed Polynomial Rings\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition relabel_vars :: "'d set \<Rightarrow> 'e set \<Rightarrow> ('d \<Rightarrow> 'e) \<Rightarrow>
         ('a, 'd) mvar_poly \<Rightarrow> ('a, 'e) mvar_poly" where
"relabel_vars I J g = indexed_poly_induced_morphism I (Pring R J) indexed_const (\<lambda>i. pvar R (g i))"

lemma relabel_vars_is_morphism:
  assumes "g \<in> I \<rightarrow> J"
  shows "ring_hom_ring (Pring R I) (Pring R J) (relabel_vars I J g)"
        "\<And>i. i \<in> I \<Longrightarrow> relabel_vars I J g (pvar R i) = pvar R (g i)"
        "\<And>c. c \<in> carrier R \<Longrightarrow> relabel_vars I J g (indexed_const c) = indexed_const c"
  using Pring_universal_prop(1)[of "Pring R J" "\<lambda>i. pvar R (g i)" I indexed_const]
    assms unfolding relabel_vars_def
    apply (meson Pi_iff Pring_is_cring Pring_var_closed indexed_const_ring_hom is_cring)
proof-
  have 0: "cring (Pring R J)" " (\<lambda>i. mset_to_IP R {#g i#}) \<in> I \<rightarrow> carrier (Pring R J)"
    "ring_hom_ring R (Pring R J) indexed_const"
    using assms Pring_is_cring is_cring apply blast
    apply (smt Pi_iff Pring_var_closed assms var_to_IP_def)
    by (simp add: indexed_const_ring_hom)
  show "\<And>i. i \<in> I \<Longrightarrow> indexed_poly_induced_morphism I (Pring R J)
                        indexed_const (\<lambda>i. pvar R (g i)) (pvar R i) = pvar R (g i)"
    using 0 assms Pring_universal_prop(2)[of "Pring R J" "\<lambda>i. pvar R (g i)" I indexed_const]
    unfolding relabel_vars_def var_to_IP_def
    by blast
  show "\<And>c. c \<in> carrier R \<Longrightarrow> indexed_poly_induced_morphism I (Pring R J)
                          indexed_const (\<lambda>i. pvar R (g i)) (indexed_const c) = indexed_const c"
    using 0 assms Pring_universal_prop(3)[of "Pring R J" "\<lambda>i. pvar R (g i)" I indexed_const]
    unfolding  var_to_IP_def
    by blast
qed

lemma relabel_vars_add:
  assumes "g \<in> I \<rightarrow> J"
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  shows "relabel_vars I J g (P \<oplus>\<^bsub>Pring R I\<^esub> Q) = relabel_vars I J g P \<oplus>\<^bsub>Pring R J\<^esub> relabel_vars I J g Q"
  using assms relabel_vars_is_morphism(1)[of g I J] ring_hom_ring.homh ring_hom_add
  by (metis (no_types, lifting))

lemma relabel_vars_mult:
  assumes "g \<in> I \<rightarrow> J"
  assumes "P \<in> carrier (Pring R I)"
  assumes "Q \<in> carrier (Pring R I)"
  shows "relabel_vars I J g (P \<otimes>\<^bsub>Pring R I\<^esub> Q) = relabel_vars I J g P \<otimes>\<^bsub>Pring R J\<^esub> relabel_vars I J g Q"
  using assms relabel_vars_is_morphism(1)[of g I J] ring_hom_ring.homh ring_hom_mult
  by (metis (no_types, lifting))

lemma relabel_vars_closed:
  assumes "g \<in> I \<rightarrow> J"
  assumes "P \<in> carrier (Pring R I)"
  shows "relabel_vars I J g P \<in> carrier (Pring R J)"
  using assms relabel_vars_is_morphism(1)[of g I J] ring_hom_ring.homh
  by (metis ring_hom_closed)

lemma relabel_vars_smult:
  assumes "g \<in> I \<rightarrow> J"
  assumes "P \<in> carrier (Pring R I)"
  assumes "a \<in> carrier R"
  shows "relabel_vars I J g (a \<odot>\<^bsub>Pring R I\<^esub>P) = a \<odot>\<^bsub>Pring R J\<^esub>relabel_vars I J g P"
proof-
  have 0: "a \<odot>\<^bsub>Pring R I\<^esub>P = indexed_const a \<otimes>\<^bsub>Pring R I\<^esub> P"
    by (metis Pring_car Pring_mult Pring_smult assms(2) assms(3) poly_scalar_mult_eq)
  have 1: "a \<odot>\<^bsub>Pring R J\<^esub>relabel_vars I J g P = indexed_const a \<otimes>\<^bsub>Pring R J\<^esub> relabel_vars I J g P"
    by (metis Pring_car Pring_mult Pring_smult assms(1) assms(2) assms(3) poly_scalar_mult_eq relabel_vars_closed)
  show ?thesis using 0 1 assms relabel_vars_mult relabel_vars_is_morphism(3)[of g I J a]
    by (metis indexed_const_closed)
qed

lemma relabel_vars_inverse:
  assumes "g \<in> I \<rightarrow> J"
  assumes "h \<in> J \<rightarrow> I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> h (g i) = i"
  assumes "P \<in> carrier (Pring R I)"
  shows  "relabel_vars J I h (relabel_vars I J g P) = P"
  apply(rule Pring_car_induct''[of _ I])
  using assms(4) apply blast
  using assms
  apply (metis relabel_vars_is_morphism(3))
proof-
  show "\<And>p q. p \<in> carrier (Pring R I) \<Longrightarrow>
           q \<in> carrier (Pring R I) \<Longrightarrow>
           relabel_vars J I h (relabel_vars I J g p) = p \<Longrightarrow>
           relabel_vars J I h (relabel_vars I J g q) = q \<Longrightarrow>
           relabel_vars J I h (relabel_vars I J g (p \<oplus>\<^bsub>Pring R I\<^esub> q)) = p \<oplus>\<^bsub>Pring R I\<^esub> q"
  proof- fix p q assume A: " p \<in> carrier (Pring R I)" "q \<in> carrier (Pring R I)"
                "relabel_vars J I h (relabel_vars I J g p) = p"
           "relabel_vars J I h (relabel_vars I J g q) = q"
    show "relabel_vars J I h (relabel_vars I J g (p \<oplus>\<^bsub>Pring R I\<^esub> q)) = p \<oplus>\<^bsub>Pring R I\<^esub> q"
    proof-
      have 0: "relabel_vars I J g (p \<oplus>\<^bsub>Pring R I\<^esub> q) = relabel_vars I J g p \<oplus>\<^bsub>Pring R J\<^esub> relabel_vars I J g q"
        using A(1) A(2) assms(1) relabel_vars_add by blast
      then show ?thesis
        using assms A relabel_vars_is_morphism(3)[of g I J] relabel_vars_is_morphism(3)[of h J I]
              relabel_vars_closed[of g I J p] relabel_vars_closed[of g I J q]
              relabel_vars_add[of h J I "relabel_vars I J g p" "relabel_vars I J g q"]
        by presburger
    qed
  qed
  show "\<And>p i. p \<in> carrier (Pring R I) \<Longrightarrow>
           i \<in> I \<Longrightarrow>
           relabel_vars J I h (relabel_vars I J g p) = p \<Longrightarrow>
        relabel_vars J I h (relabel_vars I J g (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i)) = p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i"
  proof- fix p i assume A: " p \<in> carrier (Pring R I)"
                         "relabel_vars J I h (relabel_vars I J g p) = p"
                         "i \<in> I"
    show " relabel_vars J I h (relabel_vars I J g (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i)) = p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i"
    proof-
      have "relabel_vars J I h (relabel_vars I J g (pvar R i)) = pvar R i"
        using assms relabel_vars_is_morphism[of g I J] relabel_vars_is_morphism[of h J I]
        by (metis A(3) funcset_mem )
      then show ?thesis
        using assms  relabel_vars_is_morphism[of g I J] relabel_vars_is_morphism[of h J I]
              relabel_vars_closed[of g I J p] relabel_vars_closed[of g I J "pvar R i"]
              relabel_vars_mult[of g I J "p" "pvar R i"]
              relabel_vars_mult[of h J I "relabel_vars I J g p" "relabel_vars I J g (pvar R i)"]
        by (metis A(1) A(2) A(3) Pring_var_closed)
    qed
  qed
qed

lemma relabel_vars_total_eval:
  assumes "g \<in> I \<rightarrow> J"
  assumes "P \<in> carrier (Pring R I)"
  assumes "closed_fun R f"
  shows "total_eval R (f \<circ> g) P = total_eval R f (relabel_vars I J g P)"
proof(rule Pring_car_induct''[of P I])
  show "P \<in> carrier (Pring R I)"
    using assms(2) by blast
  show "\<And>c. c \<in> carrier R \<Longrightarrow> total_eval R (f \<circ> g) (indexed_const c) = total_eval R f (relabel_vars I J g (indexed_const c))"
    by (metis assms(1) relabel_vars_is_morphism(3) total_eval_const)
  show " \<And>p q. p \<in> carrier (Pring R I) \<Longrightarrow>
           q \<in> carrier (Pring R I) \<Longrightarrow>
           total_eval R (f \<circ> g) p = total_eval R f (relabel_vars I J g p) \<Longrightarrow>
           total_eval R (f \<circ> g) q = total_eval R f (relabel_vars I J g q) \<Longrightarrow>
           total_eval R (f \<circ> g) (p \<oplus>\<^bsub>Pring R I\<^esub> q) = total_eval R f (relabel_vars I J g (p \<oplus>\<^bsub>Pring R I\<^esub> q))"

  proof- fix p q assume A: "p \<in> carrier (Pring R I)" "q \<in> carrier (Pring R I)"
                           "total_eval R (f \<circ> g) p = total_eval R f (relabel_vars I J g p)"
                           "total_eval R (f \<circ> g) q = total_eval R f (relabel_vars I J g q)"
    have 0: "closed_fun R (f \<circ> g)"
      apply(rule closed_funI)
      using comp_apply[of f g] closed_fun_simp[of f] assms(3) by presburger
    have 1: " (relabel_vars I J g (p \<oplus>\<^bsub>Pring R I\<^esub> q)) =
               (relabel_vars I J g p) \<oplus>\<^bsub>Pring R J\<^esub> (relabel_vars I J g q)"
      using A(1) A(2) assms(1) relabel_vars_add by blast
    have 2: "total_eval R f (relabel_vars I J g (p \<oplus>\<^bsub>Pring R I\<^esub> q)) =
      (total_eval R f (relabel_vars I J g p)) \<oplus>\<^bsub>R\<^esub> (total_eval R f (relabel_vars I J g q))"
      using total_eval_add[of _ J _ f]
      by (metis "1" A(1) A(2) A(3) A(4) assms(1) assms(3) relabel_vars_closed)
    show "total_eval R (f \<circ> g) (p \<oplus>\<^bsub>Pring R I\<^esub> q) = total_eval R f (relabel_vars I J g (p \<oplus>\<^bsub>Pring R I\<^esub> q))"
      using A 0 1 2
      by (metis total_eval_add)
  qed
  show "\<And>p i. p \<in> carrier (Pring R I) \<Longrightarrow>
           i \<in> I \<Longrightarrow>
           total_eval R (f \<circ> g) p = total_eval R f (relabel_vars I J g p) \<Longrightarrow>
           total_eval R (f \<circ> g) (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i) = total_eval R f (relabel_vars I J g (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i))"
  proof- fix p i assume A: "p \<in> carrier (Pring R I)" " i \<in> I "
           "total_eval R (f \<circ> g) p = total_eval R f (relabel_vars I J g p)"
    have 0: "closed_fun R (f \<circ> g)"
            apply(rule closed_funI)
      using comp_apply[of f g] closed_fun_simp[of f] assms(3) by presburger
    have 1: " (relabel_vars I J g (p \<otimes>\<^bsub>Pring R I\<^esub>  (pvar R i))) =
               (relabel_vars I J g p) \<otimes>\<^bsub>Pring R J\<^esub> (relabel_vars I J g (pvar R i))"
      by (meson A(1) A(2) assms(1) local.ring_axioms relabel_vars_mult ring.Pring_var_closed)
    have 2: "total_eval R f (relabel_vars I J g (p \<otimes>\<^bsub>Pring R I\<^esub>  (pvar R i))) =
      (total_eval R f (relabel_vars I J g p)) \<otimes>\<^bsub>R\<^esub> (total_eval R f (relabel_vars I J g (pvar R i)))"
      using total_eval_mult[of "relabel_vars I J g p" J "relabel_vars I J g (pvar R i)"]
      by (metis "1" A(1) A(2) A(3) assms(1) assms(3) is_cring pvar_closed relabel_vars_closed)
    have 3: " total_eval R (f \<circ> g) (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i) =
                total_eval R (f \<circ> g) p \<otimes>\<^bsub>R\<^esub> total_eval R (f \<circ> g)( pvar R i)"
      by (meson "0" A(1) A(2) Pring_var_closed total_eval_mult)
    have 4: "total_eval R (f \<circ> g)( pvar R i) = (total_eval R f (relabel_vars I J g (pvar R i)))"
    proof-
      have 40: "total_eval R (f \<circ> g)( pvar R i) = (f \<circ> g) i"
        using total_eval_var[of "f \<circ>g" i]
        by (metis "0" var_to_IP_def)
      have 41: "relabel_vars I J g (pvar R i) = pvar R (g i)"
        by (simp add: A(2) assms(1) relabel_vars_is_morphism(2))
      have 42: "total_eval R f (relabel_vars I J g (pvar R i)) = f (g i)"
        using total_eval_var
        by (metis "41" assms(3) var_to_IP_def)
      show ?thesis
        by (metis "40" "42" comp_apply)
    qed
    show " total_eval R (f \<circ> g) (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i) =
            total_eval R f (relabel_vars I J g (p \<otimes>\<^bsub>Pring R I\<^esub> pvar R i))"
      using A 0 1 2 3 4
      by presburger
  qed
qed

end


end

