(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section "Misc results for polynomials and sign variations"

theory BF_Misc imports
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  Sturm_Tarski.Sturm_Tarski
begin

subsection \<open>Misc\<close>

lemma lead_coeff_pderiv:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  shows "lead_coeff (pderiv p) = of_nat (degree p) * lead_coeff p"
  apply (auto simp:degree_pderiv coeff_pderiv)
  apply (cases "degree p")
  by (auto simp add: coeff_eq_0)

lemma gcd_degree_le_min:
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "degree (gcd p q) \<le> min (degree p) (degree q)"
  by (simp add: assms(1) assms(2) dvd_imp_degree_le)

lemma lead_coeff_normalize_field:
  fixes p::"'a::{field,semidom_divide_unit_factor} poly"
  assumes "p\<noteq>0"
  shows "lead_coeff (normalize p) = 1"
  by (metis (no_types, lifting) assms coeff_normalize divide_self_if dvd_field_iff 
      is_unit_unit_factor leading_coeff_0_iff normalize_eq_0_iff normalize_idem)

lemma smult_normalize_field_eq:
  fixes p::"'a::{field,semidom_divide_unit_factor} poly"
  shows "p = smult (lead_coeff p) (normalize p)"
proof (rule poly_eqI)
  fix n
  have "unit_factor (lead_coeff p) = lead_coeff p"
    by (metis dvd_field_iff is_unit_unit_factor unit_factor_0)
  then show "coeff p n = coeff (smult (lead_coeff p) (normalize p)) n"
    by simp
qed

lemma lead_coeff_gcd_field:
  fixes p q::"'a::{field,semidom_divide_unit_factor,factorial_ring_gcd} poly"
  assumes "p\<noteq>0 \<or> q\<noteq>0"
  shows "lead_coeff (gcd p q) = 1"
  using assms by (metis gcd.normalize_idem gcd_eq_0_iff lead_coeff_normalize_field)

lemma poly_gcd_0_iff:
  "poly (gcd p q) x = 0 \<longleftrightarrow> poly p x=0 \<and> poly q x=0"
  by (simp add:poly_eq_0_iff_dvd)

lemma order_multiplicity_eq:
  assumes "p\<noteq>0"
  shows "order a p = multiplicity [:-a,1:] p"
  by (metis assms multiplicity_eqI order_1 order_2)

lemma order_gcd:
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "order x (gcd p q) = min (order x p) (order x q)"
proof -
  have "prime [:- x, 1:]" 
    apply (auto simp add: prime_elem_linear_poly normalize_poly_def  intro!:primeI)
    by (simp add: pCons_one)
  then show ?thesis  
    using assms
    by (auto simp add:order_multiplicity_eq intro:multiplicity_gcd)
qed


subsection \<open>More results about sign variations (i.e. @{term changes}\<close>

lemma changes_0[simp]:"changes (0#xs) = changes xs"
  by (cases xs) auto

lemma changes_Cons:"changes (x#xs) = (if filter (\<lambda>x. x\<noteq>0) xs = [] then 
                            0 
                          else if x* hd (filter (\<lambda>x. x\<noteq>0) xs) < 0 then 
                            1 + changes xs 
                          else changes xs)"
  apply (induct xs)
  by auto

lemma changes_filter_eq:
  "changes (filter (\<lambda>x. x\<noteq>0) xs) = changes xs"
  apply (induct xs)
  by (auto simp add:changes_Cons)

lemma changes_filter_empty:
  assumes "filter (\<lambda>x. x\<noteq>0) xs = []"
  shows "changes xs = 0" "changes (a#xs) = 0" using assms
  apply (induct xs)
  apply auto
  by (metis changes_0 neq_Nil_conv)

lemma changes_append:
  assumes "xs\<noteq> [] \<and> ys\<noteq> [] \<longrightarrow> (last xs = hd ys \<and> last xs\<noteq>0)"
  shows "changes (xs@ys) = changes xs + changes ys"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have ?case when "xs=[]"
    using that Cons 
    apply (cases ys)
    by auto
  moreover have ?case when "ys=[]"
    using that Cons by auto
  moreover have ?case when "xs\<noteq>[]" "ys\<noteq>[]"
  proof -
    have "filter (\<lambda>x. x \<noteq> 0) xs \<noteq>[]"
      using that Cons 
      apply auto 
      by (metis (mono_tags, lifting) filter.simps(1) filter.simps(2) filter_append snoc_eq_iff_butlast)
    then have "changes (a # xs @ ys) = changes (a # xs) + changes ys"
      apply (subst (1 2) changes_Cons)
      using that Cons by auto
    then show ?thesis by auto
  qed
  ultimately show ?case by blast
qed

lemma changes_drop_dup:
  assumes "xs\<noteq> []" "ys\<noteq> [] \<longrightarrow> last xs=hd ys"
  shows "changes (xs@ys) = changes (xs@ tl ys)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have ?case when "ys=[]"
    using that by simp
  moreover have ?case when "ys\<noteq>[]" "xs=[]"
    using that Cons
    apply auto
    by (metis changes.simps(3) list.exhaust_sel not_square_less_zero)
  moreover have ?case when "ys\<noteq>[]" "xs\<noteq>[]"
  proof -
    define ts ts' where "ts = filter (\<lambda>x. x \<noteq> 0) (xs @ ys)"
      and "ts' = filter (\<lambda>x. x \<noteq> 0) (xs @ tl ys)"
    have "(ts = [] \<longleftrightarrow> ts' = []) \<and> hd ts = hd ts'"
    proof (cases "filter (\<lambda>x. x \<noteq> 0) xs = []")
      case True
      then have "last xs = 0" using \<open>xs\<noteq>[]\<close> 
        by (metis (mono_tags, lifting) append_butlast_last_id append_is_Nil_conv 
            filter.simps(2) filter_append list.simps(3))
      then have "hd ys=0" using Cons(3)[rule_format, OF \<open>ys\<noteq>[]\<close>] \<open>xs\<noteq>[]\<close> by auto
      then have "filter (\<lambda>x. x \<noteq> 0) ys = filter (\<lambda>x. x \<noteq> 0) (tl ys)"
        by (metis (mono_tags, lifting) filter.simps(2) list.exhaust_sel that(1))
      then show ?thesis unfolding ts_def ts'_def by auto
    next
      case False
      then show ?thesis unfolding ts_def ts'_def by auto
    qed
    moreover have "changes (xs @ ys) = changes (xs @ tl ys)"
      apply (rule Cons(1))
      using that Cons(3) by auto
    moreover have "changes (a # xs @ ys) = (if ts = [] then 0 else if a * hd ts < 0 
            then 1 + changes (xs @ ys) else changes (xs @ ys))"
      using changes_Cons[of a "xs @ ys",folded ts_def] .
    moreover have "changes (a # xs @ tl ys) = (if ts' = [] then 0 else if a * hd ts' < 0 
            then 1 + changes (xs @ tl ys) else changes (xs @ tl ys))"
      using changes_Cons[of a "xs @ tl ys",folded ts'_def] .
    ultimately show ?thesis by auto
  qed
  ultimately show ?case by blast
qed

(*
  TODO: the following lemmas contain duplicates of some lemmas in 
          Winding_Number_Eval/Missing_Algebraic.thy
  Will resolve later.  
*)

subsection \<open>Induction on polynomial roots\<close>

lemma poly_root_induct_alt [case_names 0 no_proots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
  assumes "\<And>p. (\<And>a. poly p a \<noteq> 0) \<Longrightarrow> Q p"
  assumes "\<And>a p. Q p \<Longrightarrow> Q ([:-a, 1:] * p)"
  shows   "Q p"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  have ?case when "p=0" using \<open>Q 0\<close> that by auto
  moreover have ?case when "\<nexists>a. poly p a = 0"
    using assms(2) that by blast
  moreover have ?case when "\<exists>a. poly p a = 0" "p\<noteq>0"
  proof -
    obtain a where "poly p a =0" using \<open>\<exists>a. poly p a = 0\<close> by auto
    then obtain q where pq:"p= [:-a,1:] * q" by (meson dvdE poly_eq_0_iff_dvd)
    then have "q\<noteq>0" using \<open>p\<noteq>0\<close> by auto
    then have "degree q<degree p" unfolding pq by (subst degree_mult_eq,auto)
    then have "Q q" using less by auto
    then show ?case using assms(3) unfolding pq by auto
  qed
  ultimately show ?case by auto
qed

subsection \<open>Polynomial roots / zeros\<close>

definition proots_within::"'a::comm_semiring_0 poly \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "proots_within p s = {x\<in>s. poly p x=0}"

abbreviation proots::"'a::comm_semiring_0 poly \<Rightarrow> 'a set" where
  "proots p \<equiv> proots_within p UNIV"

lemma proots_def: "proots p = {x. poly p x=0}" 
  unfolding proots_within_def by auto 

lemma proots_within_empty[simp]:
  "proots_within p {} = {}" unfolding proots_within_def by auto

lemma proots_within_0[simp]:
  "proots_within 0 s = s" unfolding proots_within_def by auto

lemma proots_withinI[intro,simp]:
  "poly p x=0 \<Longrightarrow> x\<in>s \<Longrightarrow> x\<in>proots_within p s"
  unfolding proots_within_def by auto

lemma proots_within_iff[simp]:
  "x\<in>proots_within p s \<longleftrightarrow> poly p x=0 \<and> x\<in>s"
  unfolding proots_within_def by auto

lemma proots_within_union:
  "proots_within p A \<union> proots_within p B = proots_within p (A \<union> B)"
  unfolding proots_within_def by auto

lemma proots_within_times:
  fixes s::"'a::{semiring_no_zero_divisors,comm_semiring_0} set"
  shows "proots_within (p*q) s = proots_within p s \<union> proots_within q s"
  unfolding proots_within_def by auto

lemma proots_within_gcd:
  fixes s::"'a::factorial_ring_gcd set"
  shows "proots_within (gcd p q) s= proots_within p s \<inter> proots_within q s"
  unfolding proots_within_def 
  by (auto simp add: poly_eq_0_iff_dvd) 

lemma proots_within_inter:
  "NO_MATCH UNIV s \<Longrightarrow> proots_within p s = proots p \<inter> s" 
  unfolding proots_within_def by auto

lemma proots_within_proots[simp]:
  "proots_within p s \<subseteq> proots p"
  unfolding proots_within_def by auto

lemma finite_proots[simp]: 
  fixes p :: "'a::idom poly"
  shows "p\<noteq>0 \<Longrightarrow> finite (proots_within p s)"
  unfolding proots_within_def using poly_roots_finite by fast

lemma proots_within_pCons_1_iff:
  fixes a::"'a::idom"
  shows "proots_within [:-a,1:] s = (if a\<in>s then {a} else {})"
    "proots_within [:a,-1:] s = (if a\<in>s then {a} else {})"
  by (cases "a\<in>s",auto)

lemma proots_within_uminus[simp]:
  fixes p :: "'a::comm_ring poly"
  shows "proots_within (- p) s = proots_within p s"
  by auto

lemma proots_within_smult:
  fixes a::"'a::{semiring_no_zero_divisors,comm_semiring_0}"
  assumes "a\<noteq>0"
  shows "proots_within (smult a p) s = proots_within p s"
  unfolding proots_within_def using assms by auto 

subsection \<open>Polynomial roots counting multiplicities.\<close>

(*counting the number of proots WITH MULTIPLICITIES within a set*)
definition proots_count::"'a::idom poly \<Rightarrow> 'a set \<Rightarrow> nat" where
  "proots_count p s = (\<Sum>r\<in>proots_within p s. order r p)"  

lemma proots_count_emtpy[simp]:"proots_count p {} = 0"
  unfolding proots_count_def by auto

lemma proots_count_times:
  fixes s :: "'a::idom set"
  assumes "p*q\<noteq>0"
  shows "proots_count (p*q) s = proots_count p s + proots_count q s"
proof -
  define pts where "pts=proots_within p s" 
  define qts where "qts=proots_within q s"
  have [simp]: "finite pts" "finite qts" 
    using `p*q\<noteq>0` unfolding pts_def qts_def by auto
  have "(\<Sum>r\<in>pts \<union> qts. order r p) =  (\<Sum>r\<in>pts. order r p)" 
  proof (rule comm_monoid_add_class.sum.mono_neutral_cong_right,simp_all)
    show "\<forall>i\<in>pts \<union> qts - pts. order i p = 0" 
      unfolding pts_def qts_def proots_within_def using order_root by fastforce
  qed
  moreover have "(\<Sum>r\<in>pts \<union> qts. order r q) = (\<Sum>r\<in>qts. order r q)" 
  proof (rule comm_monoid_add_class.sum.mono_neutral_cong_right,simp_all)
    show "\<forall>i\<in>pts \<union> qts - qts. order i q = 0" 
      unfolding pts_def qts_def proots_within_def using order_root by fastforce
  qed
  ultimately show ?thesis unfolding proots_count_def
    apply (simp add:proots_within_times order_mult[OF `p*q\<noteq>0`] sum.distrib)
    apply (fold pts_def qts_def)
    by auto
qed

lemma proots_count_power_n_n:
  shows "proots_count ([:- a, 1:]^n) s = (if a\<in>s \<and> n>0 then n else 0)"
proof -
  have "proots_within ([:- a, 1:] ^ n) s= (if a\<in>s \<and> n>0 then {a} else {})"
    unfolding proots_within_def by auto
  thus ?thesis unfolding proots_count_def using order_power_n_n by auto
qed

lemma degree_proots_count:
  fixes p::"complex poly"
  shows "degree p = proots_count p UNIV"
proof (induct "degree p" arbitrary:p )
  case 0
  then obtain c where c_def:"p=[:c:]" using degree_eq_zeroE by auto
  then show ?case unfolding proots_count_def 
    apply (cases "c=0")
    by (auto intro!:sum.infinite simp add:infinite_UNIV_char_0 order_0I)
next
  case (Suc n)
  then have "degree p\<noteq>0" and "p\<noteq>0" by auto
  obtain z where "poly p z = 0" 
    using Fundamental_Theorem_Algebra.fundamental_theorem_of_algebra `degree p\<noteq>0` constant_degree[of p]
    by auto
  define onez where "onez=[:-z,1:]" 
  have [simp]: "onez\<noteq>0" "degree onez = 1" unfolding onez_def by auto
  obtain q where q_def:"p= onez * q" 
    using poly_eq_0_iff_dvd `poly p z = 0` dvdE unfolding onez_def by blast
  hence "q\<noteq>0" using `p\<noteq>0` by auto
  hence "n=degree q" using degree_mult_eq[of onez q] `Suc n = degree p` 
    apply (fold q_def)
    by auto
  hence "degree q = proots_count q UNIV" using Suc.hyps(1) by simp
  moreover have " Suc 0 = proots_count onez UNIV" 
    unfolding onez_def using proots_count_power_n_n[of z 1 UNIV]
    by auto
  ultimately show ?case 
    unfolding q_def using degree_mult_eq[of onez q] proots_count_times[of onez q UNIV] `q\<noteq>0`
    by auto
qed

lemma proots_count_smult:
  fixes a::"'a::{semiring_no_zero_divisors,idom}"
  assumes "a\<noteq>0"
  shows "proots_count (smult a p) s= proots_count p s"
proof (cases "p=0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding proots_count_def
    using order_smult[OF assms] proots_within_smult[OF assms] by auto
qed


lemma proots_count_pCons_1_iff:
  fixes a::"'a::idom"
  shows "proots_count [:-a,1:] s = (if a\<in>s then 1 else 0)"
  unfolding proots_count_def 
  by (cases "a\<in>s",auto simp add:proots_within_pCons_1_iff order_power_n_n[of _ 1,simplified])

lemma proots_count_uminus[simp]:
  "proots_count (- p) s = proots_count p s"
  unfolding proots_count_def by simp

lemma card_proots_within_leq:
  assumes "p\<noteq>0"
  shows "proots_count p s \<ge> card (proots_within p s)" using assms
proof (induct rule:poly_root_induct[of _ "\<lambda>x. x\<in>s"])
  case 0
  then show ?case unfolding proots_within_def proots_count_def by auto
next
  case (no_roots p)
  then have "proots_within p s = {}" by auto
  then show ?case unfolding proots_count_def by auto
next
  case (root a p)
  have "card (proots_within ([:- a, 1:] * p) s) 
      \<le> card (proots_within [:- a, 1:] s)+card (proots_within p s)" 
    unfolding proots_within_times by (auto simp add:card_Un_le)
  also have "... \<le> 1+ proots_count p s"
  proof -
    have "card (proots_within [:- a, 1:] s) \<le> 1"
    proof (cases "a\<in>s")
      case True
      then have "proots_within [:- a, 1:] s = {a}" by auto
      then show ?thesis by auto
    next
      case False
      then have "proots_within [:- a, 1:] s = {}" by auto
      then show ?thesis by auto
    qed
    moreover have "card (proots_within p s) \<le> proots_count p s"
      apply (rule root.hyps)
      using root by auto
    ultimately show ?thesis by auto
  qed
  also have "... =  proots_count ([:- a,1:] * p) s"
    apply (subst proots_count_times)
    subgoal by (metis mult_eq_0_iff pCons_eq_0_iff root.prems zero_neq_one)  
    using root by (auto simp add:proots_count_pCons_1_iff)
  finally have "card (proots_within ([:- a, 1:] * p) s) \<le> proots_count ([:- a, 1:] * p) s" .
  then show ?case 
    by (metis (no_types, hide_lams) add.inverse_inverse add.inverse_neutral minus_pCons 
        mult_minus_left proots_count_uminus proots_within_uminus)
qed

lemma proots_count_leq_degree:
  assumes "p\<noteq>0"
  shows "proots_count p s\<le> degree p" using assms
proof (induct rule:poly_root_induct[of _ "\<lambda>x. x\<in>s"])
  case 0
  then show ?case by auto
next
  case (no_roots p)
  then have "proots_within p s = {}" by auto
  then show ?case unfolding proots_count_def by auto
next
  case (root a p)
  have "proots_count ([:a, - 1:] * p) s = proots_count [:a, - 1:] s + proots_count p s"
    apply (subst proots_count_times)
    using root by auto
  also have "... = 1 + proots_count p s"
  proof -
    have "proots_count [:a, - 1:] s  =1"
      by (metis (no_types, lifting) add.inverse_inverse add.inverse_neutral minus_pCons 
          proots_count_pCons_1_iff proots_count_uminus root.hyps(1))
    then show ?thesis by auto
  qed
  also have "... \<le>  degree ([:a,-1:] * p)" 
    apply (subst degree_mult_eq)
    subgoal by auto
    subgoal using root by auto
    subgoal using root by (simp add: \<open>p \<noteq> 0\<close>)
    done
  finally show ?case .
qed

(*TODO: not a duplicate*)
lemma proots_count_union_disjoint:
  assumes "A \<inter> B = {}" "p\<noteq>0"
  shows "proots_count p (A \<union> B) = proots_count p A + proots_count p B"
  unfolding proots_count_def 
  apply (subst proots_within_union[symmetric])
  apply (subst sum.union_disjoint)
  using assms by auto

end