section \<open>Root Filter via Interval Arithmetic\<close>

subsection \<open>Generic Framework\<close>

text \<open>We provide algorithms for finding all real or complex roots of a polynomial
  from a superset of the roots via interval arithmetic. 
  These algorithms are much faster than just
  evaluating the polynomial via algebraic number computations.\<close>

theory Roots_via_IA
  imports 
    Algebraic_Numbers.Interval_Arithmetic
begin

definition interval_of_real :: "nat \<Rightarrow> real \<Rightarrow> real interval" where
  "interval_of_real prec x =
      (if is_rat x then Interval x x
       else let n = 2 ^ prec; x' = x * of_int n
            in  Interval (of_rat (Rat.Fract \<lfloor>x'\<rfloor> n)) (of_rat (Rat.Fract \<lceil>x'\<rceil> n)))"

definition interval_of_complex :: "nat \<Rightarrow> complex \<Rightarrow> complex_interval" where
  "interval_of_complex prec z =
     Complex_Interval (interval_of_real prec (Re z)) (interval_of_real prec (Im z))"

fun poly_interval :: "'a :: {plus,times,zero} list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "poly_interval [] _ = 0"
| "poly_interval [c] _ = c"
| "poly_interval (c # cs) x = c + x * poly_interval cs x"

definition filter_fun_complex :: "complex poly \<Rightarrow> nat \<Rightarrow> complex \<Rightarrow> bool" where
  "filter_fun_complex p = (let c = coeffs p in
      (\<lambda> prec. let cs = map (interval_of_complex prec) c
      in (\<lambda> x. 0 \<in>\<^sub>c poly_interval cs (interval_of_complex prec x))))" 

definition filter_fun_real :: "real poly \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool" where
  "filter_fun_real p = (let c = coeffs p in
      (\<lambda> prec. let cs = map (interval_of_real prec) c
      in (\<lambda> x. 0 \<in>\<^sub>i poly_interval cs (interval_of_real prec x))))" 

definition genuine_roots :: "_ poly \<Rightarrow> _ list \<Rightarrow> _ list" where
  "genuine_roots p xs = filter (\<lambda>x. poly p x = 0) xs"

lemma zero_in_interval_0 [simp, intro]: "0 \<in>\<^sub>i 0"
  unfolding zero_interval_def by auto

lemma zero_in_complex_interval_0 [simp, intro]: "0 \<in>\<^sub>c 0"
  unfolding zero_complex_interval_def by (auto simp: in_complex_interval_def)

lemma length_coeffs_degree':
  "length (coeffs p) = (if p = 0 then 0 else Suc (degree p))"
  by (cases "p = 0") (auto simp: length_coeffs_degree)

lemma poly_in_poly_interval_complex:
  assumes "list_all2 (\<lambda>c ivl. c \<in>\<^sub>c ivl) (coeffs p) cs" "x \<in>\<^sub>c ivl"
  shows   "poly p x \<in>\<^sub>c poly_interval cs ivl"
proof -
  have len_eq: "length (coeffs p) = length cs"
    using assms(1) list_all2_lengthD by blast
  have "coeffs p = map (\<lambda>i. coeffs p ! i) [0..<length cs]"
    by (subst len_eq [symmetric], rule map_nth [symmetric])
  also have "\<dots> = map (poly.coeff p) [0..<length cs]"
    by (intro map_cong) (auto simp: nth_coeffs_coeff len_eq)
  finally have "list_all2 (\<lambda>c ivl. c \<in>\<^sub>c ivl) (map (poly.coeff p) [0..<length cs]) cs"
    using assms by simp
  moreover have "length cs \<ge> length (coeffs p)"
    using len_eq by simp
  ultimately show ?thesis using assms(2)
  proof (induction cs ivl arbitrary: p x rule: poly_interval.induct)
    case (1 ivl p x)
    thus ?case by auto
  next
    case (2 c ivl p x)
    have "degree p = 0"
      using 2 by (auto simp: degree_eq_length_coeffs)
    then obtain c' where [simp]: "p = [:c':]"
      by (meson degree_eq_zeroE)
    show ?case using 2 by auto
  next
    case (3 c1 c2 cs ivl p x)
    obtain q c where [simp]: "p = pCons c q"
      by (cases p rule: pCons_cases)
    have "list_all2 in_complex_interval (map (poly.coeff p) [0..<length (c1 # c2 # cs)])
                  (c1 # c2 # cs)"
      using "3.prems"(1) by simp
    also have "[0..<length (c1 # c2 # cs)] = 0 # map Suc [0..<length (c2 # cs)]"
      by (metis length_Cons map_Suc_upt upt_conv_Cons zero_less_Suc)
    also have "map (poly.coeff p) \<dots> = c # map (poly.coeff q) [0..<length (c2 # cs)]"
      by auto
    finally have "c \<in>\<^sub>c c1" and
        "list_all2 in_complex_interval (map (poly.coeff q) [0..<length (c2 # cs)]) (c2 # cs)"
      using "3.prems" by (simp_all del: upt_Suc)

    have IH: "poly q x \<in>\<^sub>c poly_interval (c2 # cs) ivl"
    proof (rule "3.IH")
      show "length (coeffs q) \<le> length (c2 # cs)"
        using "3.prems"(2) unfolding length_coeffs_degree' by auto
    qed fact+

    show ?case
      using IH "3.prems" \<open>c \<in>\<^sub>c c1\<close>
      by (auto intro!: plus_complex_interval times_complex_interval)
  qed
qed

lemma poly_in_poly_interval_real: fixes x :: real 
  assumes "list_all2 (\<lambda>c ivl. c \<in>\<^sub>i ivl) (coeffs p) cs" "x \<in>\<^sub>i ivl"
  shows   "poly p x \<in>\<^sub>i poly_interval cs ivl"
proof -
  have len_eq: "length (coeffs p) = length cs"
    using assms(1) list_all2_lengthD by blast
  have "coeffs p = map (\<lambda>i. coeffs p ! i) [0..<length cs]"
    by (subst len_eq [symmetric], rule map_nth [symmetric])
  also have "\<dots> = map (poly.coeff p) [0..<length cs]"
    by (intro map_cong) (auto simp: nth_coeffs_coeff len_eq)
  finally have "list_all2 (\<lambda>c ivl. c \<in>\<^sub>i ivl) (map (poly.coeff p) [0..<length cs]) cs"
    using assms by simp
  moreover have "length cs \<ge> length (coeffs p)"
    using len_eq by simp
  ultimately show ?thesis using assms(2)
  proof (induction cs ivl arbitrary: p x rule: poly_interval.induct)
    case (1 ivl p x)
    thus ?case by auto
  next
    case (2 c ivl p x)
    have "degree p = 0"
      using 2 by (auto simp: degree_eq_length_coeffs)
    then obtain c' where [simp]: "p = [:c':]"
      by (meson degree_eq_zeroE)
    show ?case using 2 by auto
  next
    case (3 c1 c2 cs ivl p x)
    obtain q c where [simp]: "p = pCons c q"
      by (cases p rule: pCons_cases)
    have "list_all2 in_interval (map (poly.coeff p) [0..<length (c1 # c2 # cs)])
                  (c1 # c2 # cs)"
      using "3.prems"(1) by simp
    also have "[0..<length (c1 # c2 # cs)] = 0 # map Suc [0..<length (c2 # cs)]"
      by (metis length_Cons map_Suc_upt upt_conv_Cons zero_less_Suc)
    also have "map (poly.coeff p) \<dots> = c # map (poly.coeff q) [0..<length (c2 # cs)]"
      by auto
    finally have "c \<in>\<^sub>i c1" and
        "list_all2 in_interval (map (poly.coeff q) [0..<length (c2 # cs)]) (c2 # cs)"
      using "3.prems" by (simp_all del: upt_Suc)

    have IH: "poly q x \<in>\<^sub>i poly_interval (c2 # cs) ivl"
    proof (rule "3.IH")
      show "length (coeffs q) \<le> length (c2 # cs)"
        using "3.prems"(2) unfolding length_coeffs_degree' by auto
    qed fact+

    show ?case
      using IH "3.prems" \<open>c \<in>\<^sub>i c1\<close>
      by (auto intro!: plus_in_interval times_in_interval)
  qed
qed


lemma in_interval_of_real [simp, intro]: "x \<in>\<^sub>i interval_of_real prec x"
  unfolding interval_of_real_def by (auto simp: Let_def of_rat_rat field_simps)

lemma in_interval_of_complex [simp, intro]: "z \<in>\<^sub>c interval_of_complex prec z"
  unfolding interval_of_complex_def in_complex_interval_def by auto

lemma distinct_genuine_roots [simp, intro]: 
  "distinct xs \<Longrightarrow> distinct (genuine_roots p xs)"
  by (simp add: genuine_roots_def)

definition filter_fun :: "'a poly \<Rightarrow> (nat \<Rightarrow> 'a :: comm_ring \<Rightarrow> bool) \<Rightarrow> bool" where
  "filter_fun p f = (\<forall> n x. poly p x = 0 \<longrightarrow> f n x)" 

lemma filter_fun_complex: "filter_fun p (filter_fun_complex p)"
  unfolding filter_fun_def
proof (intro impI allI)
  fix prec x
  assume root: "poly p x = 0" 
  define cs where "cs = map (interval_of_complex prec) (coeffs p)"
  have cs: "list_all2 in_complex_interval (coeffs p) cs"
    unfolding cs_def list_all2_map2 by (intro list_all2_refl in_interval_of_complex)
  define P where "P = (\<lambda>x. 0 \<in>\<^sub>c poly_interval cs (interval_of_complex prec x))"
  have "P x" 
  proof -
    have "poly p x \<in>\<^sub>c poly_interval cs (interval_of_complex prec x)"
      by (intro poly_in_poly_interval_complex in_interval_of_complex cs)
    with root show ?thesis
      by (simp add: P_def)
  qed
  thus "filter_fun_complex p prec x" unfolding filter_fun_complex_def Let_def P_def
    using cs_def by blast
qed

lemma filter_fun_real: "filter_fun p (filter_fun_real p)"
  unfolding filter_fun_def
proof (intro impI allI)
  fix prec x
  assume root: "poly p x = 0" 
  define cs where "cs = map (interval_of_real prec) (coeffs p)"
  have cs: "list_all2 in_interval (coeffs p) cs"
    unfolding cs_def list_all2_map2 by (intro list_all2_refl in_interval_of_real)
  define P where "P = (\<lambda>x. 0 \<in>\<^sub>i poly_interval cs (interval_of_real prec x))"
  have "P x" 
  proof -
    have "poly p x \<in>\<^sub>i poly_interval cs (interval_of_real prec x)"
      by (intro poly_in_poly_interval_real in_interval_of_real cs)
    with root show ?thesis
      by (simp add: P_def)
  qed
  thus "filter_fun_real p prec x" unfolding filter_fun_real_def Let_def P_def
    using cs_def by blast
qed

context
  fixes p :: "'a :: comm_ring poly" and f
  assumes ff: "filter_fun p f" 
begin

lemma genuine_roots_step:
  "genuine_roots p xs = genuine_roots p (filter (f prec) xs)"
  unfolding genuine_roots_def filter_filter 
  using ff[unfolded filter_fun_def, rule_format, of _ prec] by metis 

lemma genuine_roots_step_preserve_invar:
  assumes "{z. poly p z = 0} \<subseteq> set xs"
  shows   "{z. poly p z = 0} \<subseteq> set (filter (f prec) xs)"
proof -
  have "{z. poly p z = 0} = set (genuine_roots p xs)"
    using assms by (auto simp: genuine_roots_def)
  also have "\<dots> = set (genuine_roots p (filter (f prec) xs))"
    using genuine_roots_step[of _ prec] by simp
  also have "\<dots> \<subseteq> set (filter (f prec) xs)"
    by (auto simp: genuine_roots_def)
  finally show ?thesis .
qed
end

lemma genuine_roots_finish:
  fixes p :: "'a :: field_char_0 poly" 
  assumes "{z. poly p z = 0} \<subseteq> set xs" "distinct xs"
  assumes "length xs = card {z. poly p z = 0}"
  shows   "genuine_roots p xs = xs"
proof -
  have [simp]: "p \<noteq> 0"
    using finite_subset[OF assms(1) finite_set] infinite_UNIV_char_0 by auto
  have "length (genuine_roots p xs) = length xs"
    unfolding genuine_roots_def using assms 
    by (simp add: Int_absorb2 distinct_length_filter)
  thus ?thesis
    unfolding genuine_roots_def
    by (metis filter_True length_filter_less linorder_not_less order_eq_iff)
qed

text \<open>This is type of the initial search problem. It consists of a polynomial $p$, 
  a list $xs$ of candidate roots, the cardinality of the set of roots of $p$ and a filter function to
  drop non-roots that is parametric in a precision parameter.\<close>
typedef (overloaded) 'a genuine_roots_aux =
  "{(p :: 'a :: field_char_0 poly, xs, n, ff). 
    distinct xs \<and> 
    {z. poly p z = 0} \<subseteq> set xs \<and> 
    card {z. poly p z = 0} = n \<and>
    filter_fun p ff}"
  by (rule exI[of _ "(1, [], 0, \<lambda> _ _. False)"], auto simp: filter_fun_def)

setup_lifting type_definition_genuine_roots_aux

lift_definition genuine_roots' :: "nat \<Rightarrow> 'a :: field_char_0 genuine_roots_aux \<Rightarrow> 'a list" is
  "\<lambda>prec (p, xs, n, ff). genuine_roots p xs" .

lift_definition genuine_roots_impl_step' :: "nat \<Rightarrow> 'a :: field_char_0 genuine_roots_aux \<Rightarrow> 'a genuine_roots_aux" is
  "\<lambda>prec (p, xs, n, ff). (p, filter (ff prec) xs, n, ff)"
  by (safe, intro distinct_filter, auto simp: filter_fun_def)

lift_definition gr_poly :: "'a :: field_char_0 genuine_roots_aux \<Rightarrow> 'a poly" is
  "\<lambda>(p :: 'a poly, _, _, _). p" .

lift_definition gr_list :: "'a :: field_char_0 genuine_roots_aux \<Rightarrow> 'a list" is
  "\<lambda>(_, xs :: 'a list, _, _). xs" .

lift_definition gr_numroots :: "'a :: field_char_0 genuine_roots_aux \<Rightarrow> nat" is
  "\<lambda>(_, _, n, _). n" .

lemma genuine_roots'_code [code]:
  "genuine_roots' prec gr =
     (if length (gr_list gr) = gr_numroots gr then gr_list gr
      else genuine_roots' (2 * prec) (genuine_roots_impl_step' prec gr))"
proof (transfer, clarify)
  fix prec :: nat and p :: "'a poly" and xs :: "'a list" and ff
  assume *: "{z. poly p z = 0} \<subseteq> set xs" "distinct xs" "filter_fun p ff" 
  show "genuine_roots p xs =
          (if length xs = card {z. poly p z = 0} then xs
           else genuine_roots p (filter (ff prec) xs))"
    using genuine_roots_finish[of p xs] genuine_roots_step[of p] * by auto
qed

definition initial_precision :: nat where "initial_precision = 10" 

definition genuine_roots_impl :: "'a genuine_roots_aux \<Rightarrow> 'a :: field_char_0 list" where
  "genuine_roots_impl = genuine_roots' initial_precision" 

lemma genuine_roots_impl: "set (genuine_roots_impl p) = {z. poly (gr_poly p) z = 0}" 
  "distinct (genuine_roots_impl p)" 
  unfolding genuine_roots_impl_def
  by (transfer, auto simp: genuine_roots_def, transfer, auto)

end