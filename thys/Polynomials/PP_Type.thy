(* Author: Alexander Maletzky *)

theory PP_Type
  imports Power_Products OAlist
begin

text \<open>For code generation, we must introduce a copy of type @{typ "'a \<Rightarrow>\<^sub>0 'b"} for power-products.\<close>

typedef (overloaded) ('a, 'b) pp = "UNIV::('a \<Rightarrow>\<^sub>0 'b) set"
  morphisms mapping_of PP ..

setup_lifting type_definition_pp

lift_definition pp_of_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b::zero) pp"
  is Abs_poly_mapping .

subsection \<open>\<open>lookup_pp\<close>, \<open>keys_pp\<close> and \<open>single_pp\<close>\<close>

lift_definition lookup_pp :: "('a, 'b::zero) pp \<Rightarrow> 'a \<Rightarrow> 'b" is lookup .

lift_definition keys_pp :: "('a, 'b::zero) pp \<Rightarrow> 'a set" is keys .

lift_definition single_pp :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b::zero) pp" is Poly_Mapping.single .

lemma lookup_pp_of_fun: "finite {x. f x \<noteq> 0} \<Longrightarrow> lookup_pp (pp_of_fun f) = f"
  by (transfer, rule Abs_poly_mapping_inverse, simp)

lemma pp_of_lookup: "pp_of_fun (lookup_pp t) = t"
  by (transfer, fact lookup_inverse)

lemma pp_eqI: "(\<And>u. lookup_pp s u = lookup_pp t u) \<Longrightarrow> s = t"
  by (transfer, rule poly_mapping_eqI)

lemma pp_eq_iff: "(s = t) \<longleftrightarrow> (lookup_pp s = lookup_pp t)"
  by (auto intro: pp_eqI)

lemma keys_pp_iff: "x \<in> keys_pp t \<longleftrightarrow> (lookup_pp t x \<noteq> 0)"
  by (simp add: in_keys_iff keys_pp.rep_eq lookup_pp.rep_eq)

lemma pp_eqI':
  assumes "\<And>u. u \<in> keys_pp s \<union> keys_pp t \<Longrightarrow> lookup_pp s u = lookup_pp t u"
  shows "s = t"
proof (rule pp_eqI)
  fix u
  show "lookup_pp s u = lookup_pp t u"
  proof (cases "u \<in> keys_pp s \<union> keys_pp t")
    case True
    thus ?thesis by (rule assms)
  next
    case False
    thus ?thesis by (simp add: keys_pp_iff)
  qed
qed

lemma lookup_single_pp: "lookup_pp (single_pp x e) y = (e when x = y)"
  by (transfer, simp only: lookup_single)

subsection \<open>Additive Structure\<close>

instantiation pp :: (type, zero) zero
begin

lift_definition zero_pp :: "('a, 'b) pp" is "0::'a \<Rightarrow>\<^sub>0 'b" .

lemma lookup_zero_pp [simp]: "lookup_pp 0 = 0"
  by (transfer, simp add: lookup_zero_fun)

instance ..

end

lemma single_pp_zero [simp]: "single_pp x 0 = 0"
  by (rule pp_eqI, simp add: lookup_single_pp)

instantiation pp :: (type, monoid_add) monoid_add
begin

lift_definition plus_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> ('a, 'b) pp" is "(+)::('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> _" .

lemma lookup_plus_pp: "lookup_pp (s + t) = lookup_pp s + lookup_pp t"
  by (transfer, simp add: lookup_plus_fun)

instance by intro_classes (transfer, simp add: fun_eq_iff add.assoc)+

end

lemma single_pp_plus: "single_pp x a + single_pp x b = single_pp x (a + b)"
  by (rule pp_eqI, simp add: lookup_single_pp lookup_plus_pp when_def)

instance pp :: (type, comm_monoid_add) comm_monoid_add
  by intro_classes (transfer, simp add: fun_eq_iff ac_simps)+

instantiation pp :: (type, cancel_comm_monoid_add) cancel_comm_monoid_add
begin

lift_definition minus_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> ('a, 'b) pp" is "(-)::('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> _" .

lemma lookup_minus_pp: "lookup_pp (s - t) = lookup_pp s - lookup_pp t"
  by (transfer, simp only: lookup_minus_fun)

instance by intro_classes (transfer, simp add: fun_eq_iff diff_diff_add)+

end

subsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class comm_powerprod}\<close>

instance poly_mapping :: (type, cancel_comm_monoid_add) comm_powerprod
  by standard

subsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class ninv_comm_monoid_add}\<close>

instance poly_mapping :: (type, ninv_comm_monoid_add) ninv_comm_monoid_add
proof (standard, transfer)
  fix s t::"'a \<Rightarrow> 'b"
  assume "(\<lambda>k. s k + t k) = (\<lambda>_. 0)"
  hence "s + t = 0" by (simp only: plus_fun_def zero_fun_def)
  hence "s = 0" by (rule plus_eq_zero)
  thus "s = (\<lambda>_. 0)" by (simp only: zero_fun_def)
qed

subsection \<open>@{typ "('a, 'b) pp"} belongs to class @{class lcs_powerprod}\<close>

lemma adds_pp_iff: "(s adds t) \<longleftrightarrow> (mapping_of s adds mapping_of t)"
  unfolding adds_def by (transfer, fact refl)

instantiation pp :: (type, add_linorder) lcs_powerprod
begin

lift_definition lcs_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> ('a, 'b) pp" is "lcs_powerprod_class.lcs" .

lemma lookup_lcs_pp: "lookup_pp (lcs s t) x = max (lookup_pp s x) (lookup_pp t x)"
  by (transfer, simp add: lookup_lcs_fun lcs_fun_def)

instance
  apply (intro_classes, simp_all only: adds_pp_iff)
  subgoal by (transfer, rule adds_lcs)
  subgoal by (transfer, elim lcs_adds)
  subgoal by (transfer, rule lcs_comm)
  done

end

subsection \<open>@{typ "('a, 'b) pp"} belongs to class @{class ulcs_powerprod}\<close>

instance pp :: (type, add_linorder_min) ulcs_powerprod by intro_classes (transfer, elim plus_eq_zero)

subsection \<open>Dickson's lemma for power-products in finitely many indeterminates\<close>

lemma almost_full_on_pp_iff:
  "almost_full_on (adds) A \<longleftrightarrow> almost_full_on (adds) (mapping_of ` A)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  with _ show ?r
  proof (rule almost_full_on_hom)
    fix x y :: "('a, 'b) pp"
    assume "x adds y"
    thus "mapping_of x adds mapping_of y" by (simp only: adds_pp_iff)
  qed
next
  assume ?r
  hence "almost_full_on (\<lambda>x y. mapping_of x adds mapping_of y) A"
    using subset_refl by (rule almost_full_on_map)
  thus ?l by (simp only: adds_pp_iff[symmetric])
qed

lift_definition varnum_pp :: "('a::countable, 'b::zero) pp \<Rightarrow> nat" is "varnum {}" .

lemma dickson_grading_varnum_pp:
  "dickson_grading (varnum_pp::('a::countable, 'b::add_wellorder) pp \<Rightarrow> nat)"
proof (rule dickson_gradingI)
  fix s t :: "('a, 'b) pp"
  show "varnum_pp (s + t) = max (varnum_pp s) (varnum_pp t)" by (transfer, rule varnum_plus)
next
  fix m::nat
  show "almost_full_on (adds) {x::('a, 'b) pp. varnum_pp x \<le> m}" unfolding almost_full_on_pp_iff
  proof (transfer, simp)
    fix m::nat
    from dickson_grading_varnum_empty show "almost_full_on (adds) {x::'a \<Rightarrow>\<^sub>0 'b. varnum {} x \<le> m}"
      by (rule dickson_gradingD2)
  qed
qed

instance pp :: (countable, add_wellorder) graded_dickson_powerprod
  by (standard, rule, fact dickson_grading_varnum_pp)

instance pp :: (finite, add_wellorder) dickson_powerprod
proof
  have eq: "range mapping_of = UNIV" by (rule surjI, rule PP_inverse, rule UNIV_I)
  show "almost_full_on (adds) (UNIV::('a, 'b) pp set)" by (simp add: almost_full_on_pp_iff eq dickson)
qed

subsection \<open>Lexicographic Term Order\<close>

lift_definition lex_pp :: "('a, 'b) pp \<Rightarrow> ('a::linorder, 'b::{zero,linorder}) pp \<Rightarrow> bool" is lex_pm .

lift_definition lex_pp_strict :: "('a, 'b) pp \<Rightarrow> ('a::linorder, 'b::{zero,linorder}) pp \<Rightarrow> bool" is lex_pm_strict .

lemma lex_pp_alt: "lex_pp s t = (s = t \<or> (\<exists>x. lookup_pp s x < lookup_pp t x \<and> (\<forall>y<x. lookup_pp s y = lookup_pp t y)))"
  by (transfer, fact lex_pm_alt)

lemma lex_pp_refl: "lex_pp s s"
  by (transfer, fact lex_pm_refl)

lemma lex_pp_antisym: "lex_pp s t \<Longrightarrow> lex_pp t s \<Longrightarrow> s = t"
  by (transfer, intro lex_pm_antisym)

lemma lex_pp_trans: "lex_pp s t \<Longrightarrow> lex_pp t u \<Longrightarrow> lex_pp s u"
  by (transfer, rule lex_pm_trans)

lemma lex_pp_lin: "lex_pp s t \<or> lex_pp t s"
  by (transfer, fact lex_pm_lin)

lemma lex_pp_lin': "\<not> lex_pp t s \<Longrightarrow> lex_pp s t"
  using lex_pp_lin by blast \<comment>\<open>Better suited for \<open>auto\<close>.\<close>

corollary lex_pp_strict_alt [code]:
  "lex_pp_strict s t = (\<not> lex_pp t s)" for s t::"(_, _::ordered_comm_monoid_add) pp"
  by (transfer, fact lex_pm_strict_alt)

lemma lex_pp_zero_min: "lex_pp 0 s" for s::"(_, _::add_linorder_min) pp"
  by (transfer, fact lex_pm_zero_min)

lemma lex_pp_plus_monotone: "lex_pp s t \<Longrightarrow> lex_pp (s + u) (t + u)"
  for s t::"(_, _::{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) pp"
  by (transfer, intro lex_pm_plus_monotone)

lemma lex_pp_plus_monotone': "lex_pp s t \<Longrightarrow> lex_pp (u + s) (u + t)"
  for s t::"(_, _::{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) pp"
  unfolding add.commute[of u] by (rule lex_pp_plus_monotone)

instantiation pp :: (linorder, "{ordered_comm_monoid_add, linorder}") linorder
begin

definition less_eq_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool"
  where "less_eq_pp = lex_pp"

definition less_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool"
  where "less_pp = lex_pp_strict"

instance by intro_classes (auto simp: less_eq_pp_def less_pp_def lex_pp_refl lex_pp_strict_alt intro: lex_pp_antisym lex_pp_lin' elim: lex_pp_trans)

end

subsection \<open>Degree\<close>

lift_definition deg_pp :: "('a, 'b::comm_monoid_add) pp \<Rightarrow> 'b" is deg_pm .

lemma deg_pp_alt: "deg_pp s = sum (lookup_pp s) (keys_pp s)"
  by (transfer, transfer, simp add: deg_fun_def supp_fun_def)

lemma deg_pp_zero [simp]: "deg_pp 0 = 0"
  by (transfer, fact deg_pm_zero)

lemma deg_pp_eq_0_iff [simp]: "deg_pp s = 0 \<longleftrightarrow> s = 0" for s::"('a, 'b::add_linorder_min) pp"
  by (transfer, fact deg_pm_eq_0_iff)

lemma deg_pp_plus: "deg_pp (s + t) = deg_pp s + deg_pp (t::('a, 'b::comm_monoid_add) pp)"
  by (transfer, fact deg_pm_plus)

lemma deg_pp_single: "deg_pp (single_pp x k) = k"
  by (transfer, fact deg_pm_single)

subsection \<open>Degree-Lexicographic Term Order\<close>

lift_definition dlex_pp :: "('a::linorder, 'b::{ordered_comm_monoid_add,linorder}) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool"
  is dlex_pm .

lift_definition dlex_pp_strict :: "('a::linorder, 'b::{ordered_comm_monoid_add,linorder}) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool"
  is dlex_pm_strict .

lemma dlex_pp_alt: "dlex_pp s t \<longleftrightarrow> (deg_pp s < deg_pp t \<or> (deg_pp s = deg_pp t \<and> lex_pp s t))"
  by transfer (simp only: dlex_pm_def dord_pm_alt)

lemma dlex_pp_refl: "dlex_pp s s"
  by (transfer) (fact dlex_pm_refl)

lemma dlex_pp_antisym: "dlex_pp s t \<Longrightarrow> dlex_pp t s \<Longrightarrow> s = t"
  by (transfer, elim dlex_pm_antisym)

lemma dlex_pp_trans: "dlex_pp s t \<Longrightarrow> dlex_pp t u \<Longrightarrow> dlex_pp s u"
  by (transfer, rule dlex_pm_trans)

lemma dlex_pp_lin: "dlex_pp s t \<or> dlex_pp t s"
  by (transfer, fact dlex_pm_lin)

corollary dlex_pp_strict_alt [code]: "dlex_pp_strict s t = (\<not> dlex_pp t s)"
  by (transfer, fact dlex_pm_strict_alt)

lemma dlex_pp_zero_min: "dlex_pp 0 s"
  for s t::"(_, _::add_linorder_min) pp"
  by (transfer, fact dlex_pm_zero_min)

lemma dlex_pp_plus_monotone: "dlex_pp s t \<Longrightarrow> dlex_pp (s + u) (t + u)"
  for s t::"(_, _::{ordered_ab_semigroup_add_imp_le, ordered_cancel_comm_monoid_add}) pp"
  by (transfer, rule dlex_pm_plus_monotone)

subsection \<open>Degree-Reverse-Lexicographic Term Order\<close>

lift_definition drlex_pp :: "('a::linorder, 'b::{ordered_comm_monoid_add,linorder}) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool"
  is drlex_pm .

lift_definition drlex_pp_strict :: "('a::linorder, 'b::{ordered_comm_monoid_add,linorder}) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool"
  is drlex_pm_strict .

lemma drlex_pp_alt: "drlex_pp s t \<longleftrightarrow> (deg_pp s < deg_pp t \<or> (deg_pp s = deg_pp t \<and> lex_pp t s))"
  by transfer (simp only: drlex_pm_def dord_pm_alt)

lemma drlex_pp_refl: "drlex_pp s s"
  by (transfer, fact drlex_pm_refl)

lemma drlex_pp_antisym: "drlex_pp s t \<Longrightarrow> drlex_pp t s \<Longrightarrow> s = t"
  by (transfer, rule drlex_pm_antisym)

lemma drlex_pp_trans: "drlex_pp s t \<Longrightarrow> drlex_pp t u \<Longrightarrow> drlex_pp s u"
  by (transfer, rule drlex_pm_trans)

lemma drlex_pp_lin: "drlex_pp s t \<or> drlex_pp t s"
  by (transfer, fact drlex_pm_lin)

corollary drlex_pp_strict_alt [code]: "drlex_pp_strict s t = (\<not> drlex_pp t s)"
  by (transfer, fact drlex_pm_strict_alt)

lemma drlex_pp_zero_min: "drlex_pp 0 s"
  for s t::"(_, _::add_linorder_min) pp"
  by (transfer, fact drlex_pm_zero_min)

lemma drlex_pp_plus_monotone: "drlex_pp s t \<Longrightarrow> drlex_pp (s + u) (t + u)"
  for s t::"(_, _::{ordered_ab_semigroup_add_imp_le, ordered_cancel_comm_monoid_add}) pp"
  by (transfer, rule drlex_pm_plus_monotone)


subsection \<open>Power-Products Represented by @{type oalist_tc}\<close>

instantiation pp :: (type, "{equal, zero}") equal
begin

definition equal_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> bool" where
  "equal_pp p q \<equiv> (\<forall>t. lookup_pp p t = lookup_pp q t)"

instance by standard (auto simp: equal_pp_def intro: pp_eqI)

end

definition PP_oalist :: "('a::linorder, 'b::zero) oalist_tc \<Rightarrow> ('a, 'b) pp"
  where "PP_oalist xs = pp_of_fun (OAlist_tc_lookup xs)"

code_datatype PP_oalist

lemma lookup_PP_oalist [simp, code]: "lookup_pp (PP_oalist xs) = OAlist_tc_lookup xs"
  unfolding PP_oalist_def
proof (rule lookup_pp_of_fun)
  have "{x. OAlist_tc_lookup xs x \<noteq> 0} \<subseteq> fst ` set (list_of_oalist_tc xs)"
  proof (rule, simp)
    fix x
    assume "OAlist_tc_lookup xs x \<noteq> 0"
    thus "x \<in> fst ` set (list_of_oalist_tc xs)"
      using in_OAlist_tc_sorted_domain_iff_lookup set_OAlist_tc_sorted_domain by blast
  qed
  also have "finite ..." by simp
  finally (finite_subset) show "finite {x. OAlist_tc_lookup xs x \<noteq> 0}" .
qed

lemma keys_PP_oalist [code]: "keys_pp (PP_oalist xs) = set (OAlist_tc_sorted_domain xs)"
  by (rule set_eqI, simp add: keys_pp_iff in_OAlist_tc_sorted_domain_iff_lookup)

lemma zero_PP_oalist [code]: "(0::('a::linorder, 'b::zero) pp) = PP_oalist OAlist_tc_empty"
  by (rule pp_eqI, simp add: lookup_OAlist_tc_empty)

lemma plus_PP_oalist [code]:
  "PP_oalist xs + PP_oalist ys = PP_oalist (OAlist_tc_map2_val_neutr (\<lambda>_. (+)) xs ys)"
  by (rule pp_eqI, simp add: lookup_plus_pp, rule lookup_OAlist_tc_map2_val_neutr[symmetric], simp_all)

lemma minus_PP_oalist [code]:
  "PP_oalist xs - PP_oalist ys = PP_oalist (OAlist_tc_map2_val_rneutr (\<lambda>_. (-)) xs ys)"
  by (rule pp_eqI, simp add: lookup_minus_pp, rule lookup_OAlist_tc_map2_val_rneutr[symmetric], simp)

lemma equal_PP_oalist [code]: "equal_class.equal (PP_oalist xs) (PP_oalist ys) = (xs = ys)"
  by (simp add: equal_eq pp_eq_iff, auto elim: OAlist_tc_lookup_inj)

lemma lcs_PP_oalist [code]:
  "lcs (PP_oalist xs) (PP_oalist ys) = PP_oalist (OAlist_tc_map2_val_neutr (\<lambda>_. max) xs ys)"
  for xs ys :: "('a::linorder, 'b::add_linorder_min) oalist_tc"
  by (rule pp_eqI, simp add: lookup_lcs_pp, rule lookup_OAlist_tc_map2_val_neutr[symmetric], simp_all add: max_def)

lemma deg_pp_PP_oalist [code]: "deg_pp (PP_oalist xs) = sum_list (map snd (list_of_oalist_tc xs))"
proof -
  have "irreflp ((<)::_::linorder \<Rightarrow> _)" by (rule irreflpI, simp)
  have "deg_pp (PP_oalist xs) = sum (OAlist_tc_lookup xs) (set (OAlist_tc_sorted_domain xs))"
    by (simp add: deg_pp_alt keys_PP_oalist)
  also have "... = sum_list (map (OAlist_tc_lookup xs) (OAlist_tc_sorted_domain xs))"
    by (rule sum.distinct_set_conv_list, rule distinct_sorted_wrt_irrefl,
        fact, fact transp_on_less, fact sorted_OAlist_tc_sorted_domain)
  also have "... = sum_list (map snd (list_of_oalist_tc xs))"
    by (rule arg_cong[where f=sum_list], simp add: OAlist_tc_sorted_domain_def OAlist_tc_lookup_eq_valueI)
  finally show ?thesis .
qed

lemma single_PP_oalist [code]: "single_pp x e = PP_oalist (oalist_tc_of_list [(x, e)])"
  by (rule pp_eqI, simp add: lookup_single_pp OAlist_tc_lookup_single)

definition adds_pp_add_linorder :: "('b, 'a::add_linorder) pp \<Rightarrow> _ \<Rightarrow> bool"
  where [code_abbrev]: "adds_pp_add_linorder = (adds)"

lemma adds_pp_PP_oalist [code]:
  "adds_pp_add_linorder (PP_oalist xs) (PP_oalist ys) = OAlist_tc_prod_ord (\<lambda>_. less_eq) xs ys"
  for xs ys::"('a::linorder, 'b::add_linorder_min) oalist_tc"
proof (simp add: adds_pp_add_linorder_def adds_pp_iff adds_poly_mapping lookup_pp.rep_eq[symmetric] OAlist_tc_prod_ord_alt le_fun_def,
      intro iffI allI ballI)
  fix k
  assume "\<forall>x. OAlist_tc_lookup xs x \<le> OAlist_tc_lookup ys x"
  thus "OAlist_tc_lookup xs k \<le> OAlist_tc_lookup ys k" by blast
next
  fix x
  assume *: "\<forall>k\<in>fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys).
              OAlist_tc_lookup xs k \<le> OAlist_tc_lookup ys k"
  show "OAlist_tc_lookup xs x \<le> OAlist_tc_lookup ys x"
  proof (cases "x \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys)")
    case True
    with * show ?thesis ..
  next
    case False
    hence "x \<notin> set (OAlist_tc_sorted_domain xs)" and "x \<notin> set (OAlist_tc_sorted_domain ys)"
      by (simp_all add: set_OAlist_tc_sorted_domain)
    thus ?thesis by (simp add: in_OAlist_tc_sorted_domain_iff_lookup)
  qed
qed

subsubsection \<open>Constructor\<close>

definition "sparse\<^sub>0 xs = PP_oalist (oalist_tc_of_list xs)" \<comment>\<open>sparse representation\<close>

subsubsection \<open>Computations\<close>

experiment begin

abbreviation "X \<equiv> 0::nat"
abbreviation "Y \<equiv> 1::nat"
abbreviation "Z \<equiv> 2::nat"

value [code] "sparse\<^sub>0 [(X, 2::nat), (Z, 7)]"

lemma
  "sparse\<^sub>0 [(X, 2::nat), (Z, 7)] - sparse\<^sub>0 [(X, 2), (Z, 2)] = sparse\<^sub>0 [(Z, 5)]"
  by eval

lemma
  "lcs (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 7)]) (sparse\<^sub>0 [(Y, 3), (Z, 2)]) = sparse\<^sub>0 [(X, 2), (Y, 3), (Z, 7)]"
  by eval

lemma
  "(sparse\<^sub>0 [(X, 2::nat), (Z, 1)]) adds (sparse\<^sub>0 [(X, 3), (Y, 2), (Z, 1)])"
  by eval

lemma
  "lookup_pp (sparse\<^sub>0 [(X, 2::nat), (Z, 3)]) X = 2"
  by eval

lemma
  "deg_pp (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3), (X, 1)]) = 6"
  by eval

end

end (* theory *)
