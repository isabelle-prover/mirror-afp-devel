subsection \<open>Implementation of Division on Multivariate Polynomials\<close>

theory MPoly_Divide_Code
  imports 
    MPoly_Divide 
    Polynomials.MPoly_Type_Class_FMap
    Polynomials.MPoly_Type_Univariate
begin

text \<open>
  We now set up code equations for some of the operations that we will need, such as division,
  \<^const>\<open>mpoly_to_poly\<close>, and \<^const>\<open>mpoly_to_mpoly_poly\<close>.
\<close>

lemma mapping_of_MPoly[code]: "mapping_of (MPoly p) = p"
  by (simp add: MPoly_inverse)

lift_definition filter_pm :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b :: zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" is
  "\<lambda>P f x. if P x then f x else 0"
  by (erule finite_subset[rotated]) auto

lemma lookup_filter_pm: "lookup (filter_pm P f) x = (if P x then lookup f x else 0)"
  by transfer auto


lemma filter_pm_code [code]: "filter_pm P (Pm_fmap m) = Pm_fmap (fmfilter P m)"
  by (auto intro!: poly_mapping_eqI simp: fmlookup_default_def lookup_filter_pm)

lemma remove_key_conv_filter_pm [code]: "remove_key x m = filter_pm (\<lambda>y. y \<noteq> x) m"
  by transfer auto

lemma finite_poly_coeff_nonzero: "finite {n. poly.coeff p n \<noteq> 0}"
  by (metis MOST_coeff_eq_0 eventually_cofinite)

lemma poly_degree_conv_Max:
  assumes "p \<noteq> 0"
  shows   "Polynomial.degree p = Max {n. poly.coeff p n \<noteq> 0}"
  using assms
proof (intro antisym degree_le Max.boundedI)
  fix n assume "n \<in> {n. poly.coeff p n \<noteq> 0}"
  thus "n \<le> Polynomial.degree p"
    by (simp add: le_degree)
qed (auto simp: poly_eq_iff finite_poly_coeff_nonzero)

lemma mpoly_to_poly_code_aux:
  fixes p :: "'a :: comm_monoid_add mpoly" and x :: nat
  defines "I \<equiv> (\<lambda>m. lookup m x) ` Set.filter (\<lambda>m. \<forall>y\<in>keys m. y = x) (keys (mapping_of p))"
  shows   "I = {n. poly.coeff (mpoly_to_poly x p) n \<noteq> 0}"
    and   "mpoly_to_poly x p = 0 \<longleftrightarrow> I = {}"
    and   "I \<noteq> {} \<Longrightarrow> Polynomial.degree (mpoly_to_poly x p) = Max I"
proof -
  have "n \<in> I \<longleftrightarrow> poly.coeff (mpoly_to_poly x p) n \<noteq> 0" for n
  proof -
    have "I = (\<lambda>m. lookup m x) ` (keys (mapping_of p) \<inter> {m. \<forall>y\<in>keys m. y = x})"
      by (auto simp: I_def Set.filter_def)
    also have "{m. \<forall>y\<in>keys m. y = x} = range (\<lambda>n. monomial n x)" (is "?lhs = ?rhs")
    proof (intro equalityI subsetI)
      fix m assume "m \<in> ?lhs"
      hence "m = monomial (lookup m x) x"
        by transfer (auto simp: fun_eq_iff when_def)
      thus "m \<in> ?rhs" by auto
    qed (auto split: if_splits)
    also have "n \<in> (\<lambda>m. lookup m x) ` (keys (mapping_of p) \<inter> \<dots>) \<longleftrightarrow>
               monomial n x \<in> keys (mapping_of p)" by force
    also have "\<dots> \<longleftrightarrow> poly.coeff (mpoly_to_poly x p) n \<noteq> 0"
      by (simp add: coeff_def in_keys_iff)
    finally show ?thesis .
  qed
  thus I: "I = {n. poly.coeff (mpoly_to_poly x p) n \<noteq> 0}"
    by blast
  show eq_0_iff: "mpoly_to_poly x p = 0 \<longleftrightarrow> I = {}"
    unfolding I by (auto simp: poly_eq_iff)
  show "I \<noteq> {} \<Longrightarrow> Polynomial.degree (mpoly_to_poly x p) = Max I"
    by (subst poly_degree_conv_Max) (use eq_0_iff I in auto)
qed


lemma mpoly_to_poly_code [code]:
  "Polynomial.coeffs (mpoly_to_poly x p) =
     (let I = (\<lambda>m. lookup m x) ` Set.filter (\<lambda>m. \<forall>y\<in>keys m. y = x) (keys (mapping_of p))
      in  if I = {} then [] else map (\<lambda>n. MPoly_Type.coeff p (Poly_Mapping.single x n)) [0..<Max I + 1])"
  (is "?lhs = ?rhs")
proof -
  define I where "I = (\<lambda>m. lookup m x) ` Set.filter (\<lambda>m. \<forall>y\<in>keys m. y = x) (keys (mapping_of p))"
  show ?thesis
  proof (cases "I = {}")
    case True
    thus ?thesis using mpoly_to_poly_code_aux(2)[of x p]
      by (simp add: I_def)
  next
    case False
    have [simp]: "mpoly_to_poly x p \<noteq> 0"
      using mpoly_to_poly_code_aux(2)[of x p] False by (simp add: I_def)
    from False have "?rhs = map (\<lambda>n. MPoly_Type.coeff p (Poly_Mapping.single x n)) [0..<Max I + 1]"
      (is "_ = ?rhs'")
      by (simp add: I_def Let_def)
    also have "\<dots> = ?lhs"
    proof (rule nth_equalityI)
      show "length ?rhs' = length ?lhs"
        using mpoly_to_poly_code_aux(3)[of x p] False
        by (simp add: I_def length_coeffs_degree)
      thus "?rhs' ! n = ?lhs ! n" if "n < length ?rhs'" for n using that
        by (auto simp del: upt_Suc simp: nth_coeffs_coeff)
    qed
    finally show ?thesis ..
  qed
qed


fun mpoly_to_mpoly_poly_impl_aux1 :: "nat \<Rightarrow> ((nat \<Rightarrow>\<^sub>0 nat) \<times> 'a) list \<Rightarrow> nat \<Rightarrow> ((nat \<Rightarrow>\<^sub>0 nat) \<times> 'a) list" where
  "mpoly_to_mpoly_poly_impl_aux1 i [] j = []"
| "mpoly_to_mpoly_poly_impl_aux1 i ((mon', c) # xs) j =
     (if lookup mon' i = j then [(remove_key i mon', c)] else []) @ mpoly_to_mpoly_poly_impl_aux1 i xs j"

lemma mpoly_to_mpoly_poly_impl_aux1_altdef:
  "mpoly_to_mpoly_poly_impl_aux1 i xs j =
     map (\<lambda>(mon, c). (remove_key i mon, c)) (filter (\<lambda>(mon, c). lookup mon i = j) xs)"
  by (induction xs) auto

lemma map_of_mpoly_to_mpoly_poly_impl_aux1:
  "map_of (mpoly_to_mpoly_poly_impl_aux1 i xs j) = (\<lambda>mon.
     (if lookup mon i > 0 then None
      else map_of xs (mon + Poly_Mapping.single i j)))"
  apply (rule ext)
  apply (induction i xs j rule: mpoly_to_mpoly_poly_impl_aux1.induct)
   apply (auto simp: remove_key_lookup)
    apply (meson remove_key_sum)
   apply (metis add_left_cancel lookup_single_eq remove_key_sum)
  apply (metis remove_key_add remove_key_single remove_key_sum single_zero)
  done

lemma lookup0_fmap_of_list_mpoly_to_mpoly_poly_impl_aux1:
  "lookup0 (fmap_of_list (mpoly_to_mpoly_poly_impl_aux1 i xs j)) = (\<lambda>mon.
     lookup0 (fmap_of_list xs) (mon + Poly_Mapping.single i j) when lookup mon i = 0)"
  by (auto simp add: fmlookup_default_def fmlookup_of_list map_of_mpoly_to_mpoly_poly_impl_aux1)

definition mpoly_to_mpoly_poly_impl_aux2 where
  "mpoly_to_mpoly_poly_impl_aux2 i p j = poly.coeff (mpoly_to_mpoly_poly i p) j"

lemma coeff_MPoly: "MPoly_Type.coeff (MPoly f) m = lookup f m"
  by (simp add: coeff_def mpoly.MPoly_inverse)

lemma mpoly_to_mpoly_poly_impl_aux2_code [code]:
  "mpoly_to_mpoly_poly_impl_aux2 i (MPoly (Pm_fmap (fmap_of_list xs))) j =
     MPoly (Pm_fmap (fmap_of_list (mpoly_to_mpoly_poly_impl_aux1 i xs j)))"
  unfolding mpoly_to_mpoly_poly_impl_aux2_def
  by (rule mpoly_eqI)
     (simp add: coeff_coeff_mpoly_to_mpoly_poly coeff_MPoly
                lookup0_fmap_of_list_mpoly_to_mpoly_poly_impl_aux1)

definition mpoly_to_mpoly_poly_impl :: "nat \<Rightarrow> 'a :: comm_ring_1 mpoly \<Rightarrow> 'a mpoly list" where
  "mpoly_to_mpoly_poly_impl x p = (if p = 0 then [] else
     map (mpoly_to_mpoly_poly_impl_aux2 x p) [0..<Suc (MPoly_Type.degree p x)])"

lemma mpoly_to_mpoly_poly_eq_0_iff [simp]: "mpoly_to_mpoly_poly x p = 0 \<longleftrightarrow> p = 0"
proof -
  interpret transfer_mpoly_to_mpoly_poly x .
  define p' where "p' = mpoly_to_mpoly_poly x p"
  have [transfer_rule]: "R p' p"
    by (auto simp: R_def p'_def)
  show ?thesis
    unfolding p'_def [symmetric] by transfer_prover
qed

lemma mpoly_to_mpoly_poly_code [code]:
  "Polynomial.coeffs (mpoly_to_mpoly_poly x p) = mpoly_to_mpoly_poly_impl x p"
  by (intro nth_equalityI)
     (auto simp: mpoly_to_mpoly_poly_impl_def length_coeffs_degree
                 mpoly_to_mpoly_poly_impl_aux2_def coeffs_nth simp del: upt_Suc)

value "mpoly_to_mpoly_poly 0 (Var 0 ^ 2 + Var 0 * Var 1 + Var 1 ^ 2 :: int mpoly)"

value "Rings.divide (Var 0 ^ 2 * Var 1 + Var 0 * Var 1 ^ 2 :: int mpoly) (Var 1)"

end