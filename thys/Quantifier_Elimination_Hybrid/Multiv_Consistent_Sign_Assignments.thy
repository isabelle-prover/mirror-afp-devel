(* This file includes a variety of useful definitions and helper lemmas,
including a definition of consistent sign assignments for multivariate
polynomials (of type real mpoly).
 *)

theory Multiv_Consistent_Sign_Assignments
  imports
    Multiv_Poly_Props
    "Datatype_Order_Generator.Order_Generator"

begin

derive linorder "rat list"

section "Define satisfies evaluation and proofs"
definition satisfies_evaluation_alternate:: "real list \<Rightarrow> real mpoly \<Rightarrow> rat \<Rightarrow> bool" where 
  "satisfies_evaluation_alternate val f n = 
  (sgn (eval_mpoly val f) = real_of_rat (sgn n))"

definition satisfies_evaluation:: "real list \<Rightarrow> real mpoly \<Rightarrow> rat \<Rightarrow> bool" where 
  "satisfies_evaluation val f n = 
  ((Sturm_Tarski.sign (eval_mpoly val f)::real) = (Sturm_Tarski.sign n::real))"

lemma satisfies_evaluation_alternate:
  shows "satisfies_evaluation_alternate val f n = satisfies_evaluation val f n"
proof - 
  have h1: "sgn (eval_mpoly val f) = real_of_rat (sgn n) \<Longrightarrow> of_int (Sturm_Tarski.sign (eval_mpoly val f)) = of_int (Sturm_Tarski.sign n)"
    by (metis (no_types, lifting) Sturm_Tarski.sign_def of_rat_1 of_rat_eq_0_iff of_rat_eq_iff rel_simps(91) sgn_eq_0_iff sgn_if sign_simps(2))
  have h2: "(of_int( Sturm_Tarski.sign (eval_mpoly val f))::real) = (of_int(Sturm_Tarski.sign n)::real) \<Longrightarrow> sgn (eval_mpoly val f) = real_of_rat (sgn n)"
    by (smt (verit) Sturm_Tarski.sign_def of_int_hom.injectivity of_rat_eq_0_iff of_rat_hom.hom_1_iff of_rat_neg_one sgn_if sign_simps(2))
  then show ?thesis unfolding satisfies_evaluation_alternate_def satisfies_evaluation_def using h1 h2
    by blast
qed

lemma eval_mpoly_poly_one_less_degree:
  assumes "satisfies_evaluation val (Polynomial.lead_coeff q) 0"
  shows "eval_mpoly_poly val (one_less_degree q) =
         eval_mpoly_poly val q"
  using assms
  unfolding one_less_degree_def satisfies_evaluation_def
  by (metis assms diff_zero eval_mpoly_map_poly_comm_ring_hom.base.map_poly_hom_monom eval_mpoly_poly_comm_ring_hom.hom_minus eval_mpoly_poly_def monom_eq_0 of_rat_0 satisfies_evaluation_alternate satisfies_evaluation_alternate_def sgn_0_0)

lemma degree_valuation_le:
  shows "Polynomial.degree (eval_mpoly_poly val p) \<le> Polynomial.degree p"
  unfolding eval_mpoly_poly_def
  by (simp add: degree_map_poly_le) 

lemma satisfies_evaluation_nonzero:
  assumes "satisfies_evaluation val p n"
  assumes "n \<noteq> 0"
  shows "eval_mpoly val p \<noteq> 0"
  using assms unfolding satisfies_evaluation_def
  by (smt (verit, ccfv_threshold) Sturm_Tarski.sign_def of_int_eq_iff)

lemma degree_valuation:
  assumes "satisfies_evaluation val (Polynomial.lead_coeff p) n"
  assumes "n \<noteq> 0"
  shows "Polynomial.degree p = Polynomial.degree (eval_mpoly_poly val p)"
  using satisfies_evaluation_nonzero[OF assms]
  unfolding eval_mpoly_poly_def satisfies_evaluation_def
  by (metis Ring_Hom_Poly.degree_map_poly degree_0 eval_mpoly_map_poly_comm_ring_hom.hom_zero)

lemma lead_coeff_valuation:
  assumes "satisfies_evaluation val (Polynomial.lead_coeff p) n"
  assumes "n \<noteq> 0"
  shows "eval_mpoly val (Polynomial.lead_coeff p) =
        Polynomial.lead_coeff (eval_mpoly_poly val p)"
  using satisfies_evaluation_nonzero[OF assms]
  unfolding eval_mpoly_poly_def satisfies_evaluation_def
  using assms(1) assms(2) degree_valuation eval_mpoly_poly_def by force

(* a restatement of lead_coeff_valuation *)
lemma eval_commutes:
  fixes p:: "real mpoly Polynomial.poly"
  assumes "eval_mpoly val (Polynomial.lead_coeff p) \<noteq> 0"
  shows "eval_mpoly val (Polynomial.lead_coeff p) = Polynomial.lead_coeff (eval_mpoly_poly val p)"
proof - 
  have "(Polynomial.degree p) = (Polynomial.degree (eval_mpoly_poly val p))" 
    using assms
    using degree_valuation satisfies_evaluation_def
    by (metis degree_valuation_le eval_mpoly_map_poly_comm_ring_hom.base.coeff_map_poly_hom eval_mpoly_poly_def le_antisym le_degree) 
  then have "eval_mpoly val (Polynomial.coeff p (Polynomial.degree p)) = Polynomial.coeff (eval_mpoly_poly val p) (Polynomial.degree (eval_mpoly_poly val p))"
    using assms lead_coeff_valuation satisfies_evaluation_def
    using eval_mpoly_poly_coeff1 le_refl by presburger 
  then show ?thesis
    by auto
qed

lemma eval_mpoly_poly_pseudo_divmod:
  assumes "satisfies_evaluation val (Polynomial.lead_coeff p) n"
  assumes "n \<noteq> 0" 
  assumes "satisfies_evaluation val (Polynomial.lead_coeff q) m"
  assumes "m \<noteq> 0" 
  shows "pseudo_divmod (eval_mpoly_poly val p) (eval_mpoly_poly val q) =
   (map_prod (eval_mpoly_poly val) (eval_mpoly_poly val) (pseudo_divmod p q))"
proof -
  from satisfies_evaluation_nonzero[OF assms(3-4)]
  have 1: "eval_mpoly_poly val q \<noteq> 0" using assms unfolding satisfies_evaluation_def
    by (metis assms(3-4) lead_coeff_valuation leading_coeff_0_iff)
  then have 2: "q \<noteq> 0"
    using eval_mpoly_poly_def by fastforce
  show ?thesis unfolding pseudo_divmod_def
    using 1 2 apply auto
    unfolding eval_mpoly_poly_def
    by (smt (verit) assms degree_valuation eval_mpoly_map_poly_comm_ring_hom.base.pseudo_divmod_main_hom eval_mpoly_poly_def lead_coeff_valuation leading_coeff_0_iff length_coeffs_degree map_poly_0 satisfies_evaluation_nonzero)
qed

lemma eval_mpoly_poly_pseudo_mod:
  assumes "satisfies_evaluation val (Polynomial.lead_coeff p) n"
  assumes "n \<noteq> 0" 
  assumes "satisfies_evaluation val (Polynomial.lead_coeff q) m"
  assumes "m \<noteq> 0" 
  shows "pseudo_mod (eval_mpoly_poly val p)
     (eval_mpoly_poly val q) =
    eval_mpoly_poly val (pseudo_mod p q)"
  unfolding pseudo_mod_def 
  using assms eval_mpoly_poly_pseudo_divmod by auto

lemma eval_mpoly_poly_smult:
  shows "Polynomial.smult (eval_mpoly val m) (eval_mpoly_poly val r) =
         eval_mpoly_poly val (Polynomial.smult m r)"
  apply (intro poly_eqI)
  apply (simp_all add:eval_mpoly_poly_def coeff_map_poly eval_mpoly_def)
  by (simp add: insertion_mult)

section "Consistent Sign Assignments for mpoly type"

(* Plugs in 0's by default when length val < length vars in accord with the definition of eval_mpoly *)
definition mpoly_sign:: "real list \<Rightarrow> real mpoly \<Rightarrow> rat" where 
  "mpoly_sign val f = of_int (Sturm_Tarski.sign (eval_mpoly val f))"

lemma mpoly_sign_lemma_valuation_length:
  "{x. \<exists>(val::real list). mpoly_sign val q = x} = 
  {x. \<exists>(val::real list). ((\<forall>v \<in> vars q. length val > v) \<and> mpoly_sign val q = x)}" 
proof -
  have subset1: "{x. \<exists>(val::real list). mpoly_sign val q = x} 
  \<subseteq> {x. \<exists>(val::real list). ((\<forall>v \<in> vars q. length val > v) \<and> mpoly_sign val q = x)}" 
  proof clarsimp 
    fix val::"real list"
    {
      assume *: "(\<forall>v\<in>vars q. v < length val)"
      then have "(\<forall>v\<in>vars q. v < length val) \<and> mpoly_sign val q = mpoly_sign val q"
        by auto
      then have "\<exists>vala. (\<forall>v\<in>vars q. v < length vala) \<and> mpoly_sign vala q = mpoly_sign val q"
        by auto
    }
    moreover {
      assume *: "(\<exists>v\<in>vars q. v \<ge> length val)"
      have "finite {vars q}"
        by simp
      then have "\<exists>k. \<forall>v\<in>vars q. k > v"
        by (meson finite_nat_set_iff_bounded vars_finite) 
      then obtain k where k_prop: "\<forall>v\<in>vars q. k > v" 
        by auto
      then have gtz: "k - length val > 0"
        using * by auto
      let ?app_len = "k - length val "
      have "\<exists>(l::real list). length l = ?app_len \<and> (\<forall>i < ?app_len. l ! i = 0)"
        using gtz Polynomial.coeff_monom length_map length_upt nth_map
      proof -
        { fix nn :: "real list \<Rightarrow> nat"
          { assume "\<exists>r n na nb. nn (map (poly.coeff (Polynomial.monom r n)) [na..<nb]) < nb - na \<and> nb - na = k - length val \<and> r = 0"
            then have "\<exists>r n ns. nn (map (poly.coeff (Polynomial.monom r n)) ns) < length ns \<and> length ns = k - length val \<and> r = 0"
              by (metis length_upt)
            then have "\<exists>rs. \<not> nn rs < k - length val \<or> length rs = k - length val \<and> rs ! nn rs = 0"
              by (metis (no_types) Polynomial.coeff_monom length_map nth_map) }
          then have "\<exists>rs. \<not> nn rs < k - length val \<or> length rs = k - length val \<and> rs ! nn rs = 0"
            by blast }
        then have "\<exists>rs. \<forall>n. \<not> n < k - length val \<or> length rs = k - length val \<and> rs ! n = (0::real)"
          by meson
        then show ?thesis
          using gtz by blast 
      qed
      then obtain l::"real list" where l_prop: "length l = ?app_len \<and> (\<forall>i < ?app_len. l ! i = 0)"
        by auto
      let ?new_list = "append val l"
      have "length ?new_list = k" using l_prop
        by (metis add_diff_cancel_left' gtz length_append less_imp_add_positive zero_less_diff)
      then have p1: "\<forall>v\<in>vars q. v < length ?new_list" 
        using k_prop
        by meson 
      have p2: "mpoly_sign ?new_list q = mpoly_sign val q"
        using l_prop  unfolding mpoly_sign_def eval_mpoly_def
        by (smt (verit, best) insertion_irrelevant_vars nth_default_append nth_default_def) 
      then have "\<exists>vala. (\<forall>v\<in>vars q. v < length vala) \<and> mpoly_sign vala q = mpoly_sign val q"
        using p1 p2
        by blast 
    }
    ultimately have "\<exists>vala. (\<forall>v\<in>vars q. v < length vala) \<and> mpoly_sign vala q = mpoly_sign val q"
      using not_le_imp_less by blast
    then show "\<exists>vala. (\<forall>v\<in>vars q. v < length vala) \<and> mpoly_sign vala q = mpoly_sign val q"
      by blast
  qed
  have subset2: "{x. \<exists>(val::real list). ((\<forall>v \<in> vars q. length val > v) \<and> mpoly_sign val q = x)} 
    \<subseteq> {x. \<exists>(val::real list). mpoly_sign val q = x}"
    by blast 
  show ?thesis using subset1 subset2 by auto
qed

definition map_mpoly_sign::"real mpoly list \<Rightarrow> real list \<Rightarrow> rat list"
  where "map_mpoly_sign qs val \<equiv>
    map ((rat_of_int \<circ> Sturm_Tarski.sign) \<circ> (eval_mpoly val)) qs"

definition all_lists:: "nat \<Rightarrow> real list set" where
  "all_lists n = {(ls::real list). length ls = n}"

(* The set of all rational sign vectors for qs wrt the set S
  When S = all_lists n for the appropriate length n, then this quantifies 
  over all real lists of length n *)
definition mpoly_consistent_sign_vectors::"real mpoly list \<Rightarrow> real list set \<Rightarrow> rat list set"
  where "mpoly_consistent_sign_vectors qs S = (map_mpoly_sign qs) ` S"

definition mpoly_csv::"real mpoly list \<Rightarrow> rat list set"
  where "mpoly_csv qs = {sign_vec. (\<exists> val. map_mpoly_sign qs val = sign_vec)}"

section "Data structure definitions"

definition mpoly_sign_data:: "real list \<Rightarrow> real mpoly \<Rightarrow> (real mpoly \<times> rat)" where 
  "mpoly_sign_data val f = (f, mpoly_sign val f)"

definition map_mpoly_sign_data:: "real list \<Rightarrow> real mpoly list \<Rightarrow> (real mpoly \<times> rat) list" where 
  "map_mpoly_sign_data val qs =  map (\<lambda>x. mpoly_sign_data val x) qs"

definition mpoly_csv_data::"real mpoly list \<Rightarrow> (real mpoly \<times> rat) list set"
  where "mpoly_csv_data qs = {sign_vec. (\<exists> val. map_mpoly_sign_data val qs = sign_vec)}"

definition all_coeffs:: "real mpoly Polynomial.poly list \<Rightarrow> real mpoly list"
  where "all_coeffs qs = concat (map Polynomial.coeffs qs)"

primrec all_coeffs_alt:: "real mpoly Polynomial.poly list \<Rightarrow> real mpoly list"
  where "all_coeffs_alt [] = []"
  | "all_coeffs_alt (h#T) = append (Polynomial.coeffs h) (all_coeffs T)"

lemma all_coeffs_alt: "all_coeffs qs = all_coeffs_alt qs"
  by (metis (no_types, opaque_lifting) all_coeffs_alt.simps(1) all_coeffs_alt.simps(2) all_coeffs_def concat.simps(1) concat.simps(2) list.exhaust list.simps(8) list.simps(9))  

definition all_coeffs_csv_data::"real mpoly Polynomial.poly list \<Rightarrow> (real mpoly \<times> rat) list set"
  where "all_coeffs_csv_data qs = mpoly_csv_data (all_coeffs qs)"

primrec 


lookup_assump_aux:: "'k \<Rightarrow> ('k \<times> 'a) list \<Rightarrow> 'a option"
where "lookup_assump_aux p [] = None"
| "lookup_assump_aux p (h # T) = 
        (if (fst h = p) then Some (snd h) else lookup_assump_aux p T)"

fun lookup_assump:: "real mpoly \<Rightarrow>  (real mpoly \<times> rat) list \<Rightarrow> rat"
  where "lookup_assump p q = (case (lookup_assump_aux p q) of
    None \<Rightarrow> 1000
    | Some i \<Rightarrow> i)"

section "Lemmas about first nonzero coefficient helper"

(* Under a valuation satisfying assumps, the lead coefficient has this sign *)
primrec first_nonzero_coefficient_helper:: "(real mpoly \<times> rat) list \<Rightarrow> real mpoly list \<Rightarrow>  rat"
  where "first_nonzero_coefficient_helper assumps [] = 0"
  | "first_nonzero_coefficient_helper assumps (h # T) = 
    (case lookup_assump_aux h assumps of
         (Some i) \<Rightarrow> (if i \<noteq> 0 then i else first_nonzero_coefficient_helper assumps T)
          | None \<Rightarrow> first_nonzero_coefficient_helper assumps T)"

(* Have to reverse the list because coefficients go from lowest to highest *)
definition sign_of_first_nonzero_coefficient:: "(real mpoly \<times> rat) list \<Rightarrow> real mpoly Polynomial.poly \<Rightarrow> rat"
  where "sign_of_first_nonzero_coefficient assumps q = first_nonzero_coefficient_helper assumps (rev (Polynomial.coeffs q))"

definition sign_of_first_nonzero_coefficient_aux:: "(real mpoly \<times> rat) list \<Rightarrow> real mpoly list \<Rightarrow> rat"
  where "sign_of_first_nonzero_coefficient_aux assumps coeffl = first_nonzero_coefficient_helper assumps coeffl"

lemma sign_of_first_nonzero_coefficient_aux:"sign_of_first_nonzero_coefficient_aux assumps (rev (Polynomial.coeffs q)) = sign_of_first_nonzero_coefficient assumps q"
  by (simp add: sign_of_first_nonzero_coefficient_aux_def sign_of_first_nonzero_coefficient_def)

definition sign_of_first_nonzero_coefficient_list:: "real mpoly Polynomial.poly list \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> rat list"
  where "sign_of_first_nonzero_coefficient_list qs assumps = map (\<lambda>q. sign_of_first_nonzero_coefficient assumps q) qs"

lemma all_coeffs_member:
  fixes qs:: "real mpoly Polynomial.poly list"
  fixes q:: "real mpoly Polynomial.poly"
  fixes coeff:: "real mpoly"
  assumes "q \<in> set qs"
  assumes inset: "coeff \<in> set (Polynomial.coeffs q) "
  shows "coeff \<in> set (all_coeffs qs)"
proof -
  have "coeff \<in> set (all_coeffs qs)"
    using assms
  proof (induction qs)
    case Nil
    then show ?case by auto
  next
    case (Cons a qs)
    then show ?case
      by (metis Un_iff all_coeffs_alt all_coeffs_alt.simps(2) set_ConsD set_append) 
  qed
  then show ?thesis using all_coeffs_alt by auto
qed

lemma map_mpoly_sign_data_duplicates:
  fixes qs:: "real mpoly list"
  fixes val:: "real list"
  fixes coeff:: "real mpoly"
  shows "((coeff, i) \<in> set (map_mpoly_sign_data val qs) \<and> (coeff, k) \<in> set (map_mpoly_sign_data val qs)
    \<Longrightarrow> i = k)"
proof clarsimp 
  assume m1: "(coeff, i) \<in> set (map_mpoly_sign_data val qs)"
  assume m2: "(coeff, k) \<in> set (map_mpoly_sign_data val qs)"
  show "i = k"
    using m1 m2 unfolding  map_mpoly_sign_data_def mpoly_sign_data_def
    by (smt (verit, del_insts) fst_conv imageE list.set_map snd_conv) 
qed

lemma lookup_assump_aux_property:
  fixes i:: "rat"
  fixes l:: "(real mpoly \<times> rat) list"
  assumes "(c, i) \<in> set l"
  assumes no_duplicates: "\<forall> j k. 
    ((c, j) \<in> set l \<and> (c, k) \<in> set l \<longrightarrow> j = k)"
  shows "lookup_assump_aux c l = Some i"
  using assms
proof (induct l)
  case Nil
  then show ?case
    by (simp add: member_rec(2)) 
next
  case (Cons a l)
  then show ?case
    by force 
qed

value "Polynomial.coeffs ([:1, 2, 3:]::real Polynomial.poly)"

lemma lookup_assump_aux_eo:
  shows "lookup_assump_aux p assumps = None \<or> (\<exists>k. lookup_assump_aux p assumps = Some k)"
  using option.exhaust_sel by blast

lemma lookup_assump_means_inset:
  assumes "lookup_assump_aux p assumps = Some k"
  shows "(p, k) \<in> set assumps"
  using assms proof (induct assumps)
  case Nil
  then show ?case by auto
next
  case (Cons a assumps)
  then show ?case
    by (metis list.set_intros(1) list.set_intros(2) lookup_assump_aux.simps(2) option.inject prod.collapse)
qed

lemma inset_means_lookup_assump_some:
  assumes  "(p, k) \<in> set assumps "
  shows "\<exists>j. lookup_assump_aux p assumps = Some j"
  using assms
proof (induct assumps)
  case Nil
  then show ?case
    by (simp add: member_rec(2))
next
  case (Cons a assumps)
  then show ?case
    by force
qed

value "List.drop 2 [(0::int), 0, 3, 2, 1]"

lemma sign_of_first_nonzero_coefficient_drop:
  assumes "list_len = length ell"
  assumes "k < list_len"
  assumes "\<And>i. ((i \<ge> k \<and> i < list_len) \<Longrightarrow> (lookup_assump_aux (ell ! i) assumps = None \<or> lookup_assump_aux (ell ! i) assumps = Some 0))"
  shows "first_nonzero_coefficient_helper assumps (rev ell) = first_nonzero_coefficient_helper assumps (drop (list_len - k) (rev ell))"
  using assms 
proof (induct "length ell" arbitrary: ell list_len k)
  case 0
  then show ?case
    by auto 
next
  case (Suc x)  
  then have "\<exists>sub_ell. ell = sub_ell @[nth ell (length ell - 1)]"
    by (metis cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 diff_is_0_eq lessI take_Suc_conv_app_nth take_all)
  then obtain sub_ell where sub_ell: "ell = sub_ell @ [nth ell (length ell - 1)]" by auto
  then have len_sub_ell: "length sub_ell = x"
    by (metis Suc.hyps(2) diff_Suc_1 length_append_singleton) 
  have rev_prop: "rev ell = (nth ell (length ell - 1))#(rev sub_ell)"
    using sub_ell
    by simp 
  then have drop_prop: "(drop (x - (k-1)) (rev sub_ell)) = (drop (x - k + 2) (rev ell))"
    by (smt (verit, best) Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_1 Suc_diff_Suc Suc_eq_plus1 add_diff_cancel_right add_diff_inverse_nat diff_Suc_1 diff_diff_left diff_is_0_eq drop_Suc_Cons drop_rev less_imp_le_nat less_one) 
  then have drop_prop2: "(drop (x - (k-1)) (rev sub_ell)) = (drop (x - k + 1) (drop 1 (rev ell)))"
    by simp
  have "\<exists>i. (i \<ge> k \<and> i < list_len) \<longrightarrow>
    lookup_assump_aux (ell ! i) assumps = None \<or> lookup_assump_aux (ell ! i) assumps = Some 0"
    using Suc.prems(3) by presburger
  let ?i = "(length ell - 1)"
  have "lookup_assump_aux (ell ! ?i) assumps = None \<or> lookup_assump_aux (ell ! ?i) assumps = Some 0"
    using assms(3) assms(2)
    by (metis Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc.prems(3) diff_Suc_1 lessI linorder_not_le not_less_eq)
  then have "lookup_assump_aux ((rev ell) ! 0) assumps = None \<or> lookup_assump_aux ((rev ell) ! 0) assumps = Some 0"
    using rev_prop
    by (metis nth_Cons_0) 
  then have key_prop: "first_nonzero_coefficient_helper assumps (rev ell) =
       first_nonzero_coefficient_helper assumps (drop 1 (rev ell))"
    unfolding first_nonzero_coefficient_helper_def
    by (smt (verit, ccfv_SIG) One_nat_def drop0 drop_Suc_Cons list.simps(7) nth_Cons_0 option.simps(4) option.simps(5) rev_prop) 
  then have key_prop2: "first_nonzero_coefficient_helper assumps (rev ell) =
       first_nonzero_coefficient_helper assumps (rev sub_ell)"
    using rev_prop
    by (metis One_nat_def drop0 drop_Suc_Cons) 
  have eo: "k = length ell - 1 \<or> k < length sub_ell"
    using len_sub_ell
    using Suc.hyps(2) Suc.prems(1) Suc.prems(2) by linarith 
  moreover {
    assume *: "k = length ell - 1"
    then have len: "list_len - k = 1" 
      using len_sub_ell Suc.prems(1) Suc.hyps(2)
      by simp
    then have "first_nonzero_coefficient_helper assumps (rev ell) =
       first_nonzero_coefficient_helper assumps (drop (list_len - k) (rev ell))"
      using key_prop by auto
  }
  moreover {
    assume *: "k < length sub_ell"
    have impl: "x = length sub_ell \<Longrightarrow>
    k < length sub_ell \<Longrightarrow>
    (\<And>i. k \<le> i \<and> i < length sub_ell \<Longrightarrow>
          lookup_assump_aux (sub_ell ! i) assumps = None \<or>
          lookup_assump_aux (sub_ell ! i) assumps = Some 0) \<Longrightarrow>
    first_nonzero_coefficient_helper assumps (rev sub_ell) =
    first_nonzero_coefficient_helper assumps (drop ((length sub_ell) - k) (rev sub_ell))"
      using Suc.prems Suc.hyps sub_ell
      by blast 
    have "\<And>i. (i \<ge> k \<and> i < list_len) \<Longrightarrow>
    lookup_assump_aux (ell ! i) assumps = None \<or> lookup_assump_aux (ell ! i) assumps = Some 0"
      using Suc.prems(3) by auto 
    then have sub_ell_prop: "(\<And>i. (i \<ge> k \<and> i < (length sub_ell)) \<Longrightarrow>
          lookup_assump_aux (sub_ell ! i) assumps = None \<or>
          lookup_assump_aux (sub_ell ! i) assumps = Some 0)"
      using sub_ell
      by (metis Suc.hyps(2) Suc.prems(1) len_sub_ell less_SucI nth_append) 
    then have "first_nonzero_coefficient_helper assumps (rev sub_ell) =
    first_nonzero_coefficient_helper assumps (drop ((length sub_ell) - k) (rev sub_ell))"
      using "*" len_sub_ell sub_ell_prop impl
      by blast 
    then have "first_nonzero_coefficient_helper assumps (rev ell) =
       first_nonzero_coefficient_helper assumps (drop (list_len - k) (rev ell))"
      using key_prop2 drop_prop2
      by (metis (full_types) Suc.hyps(2) Suc.prems(1) diff_Suc_1 diff_commute drop_Cons' len_sub_ell rev_prop) 
    }
  ultimately have "first_nonzero_coefficient_helper assumps (rev ell) =
       first_nonzero_coefficient_helper assumps (drop (list_len - k) (rev ell))"
    using eo
    by fastforce 
  then show ?case by auto
qed

value "Polynomial.coeffs ([:0, 1, 2, 3:]::real Polynomial.poly)"
value "Polynomial.degree ([:0, 1, 2, 3:]::real Polynomial.poly)"

lemma helper_two:
  assumes deg_gt: "Polynomial.degree q > 0"
  assumes sat_eval: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes lc_zero: "lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some 0"
  shows "sign_of_first_nonzero_coefficient assumps q = sign_of_first_nonzero_coefficient assumps (one_less_degree q)" 
proof - 
  let ?coeffs_q = "Polynomial.coeffs q"
  let ?coeffs_less = "Polynomial.coeffs (one_less_degree q)"
  obtain r where r:"Polynomial.degree q = Suc r"
    using deg_gt not0_implies_Suc 
    by blast
  from poly_as_sum_of_monoms[of q]
  have lc_is: "(Polynomial.lead_coeff q) = (Polynomial.coeffs q) ! (r + 1)"
    using r
    by (metis Suc_eq_plus1 coeffs_nth deg_gt degree_0 le_refl less_numeral_extra(3)) 
  have qis: "q = (\<Sum>i\<le>r. Polynomial.monom (poly.coeff q i) i) + Polynomial.monom (Polynomial.lead_coeff q) (Polynomial.degree q)"
    using \<open>(\<Sum>i\<le>Polynomial.degree q. Polynomial.monom (poly.coeff q i) i) = q\<close> r by auto
  then have oldis: "q - Polynomial.monom (Polynomial.lead_coeff q) (Polynomial.degree q) = (\<Sum>i\<le>r. Polynomial.monom (poly.coeff q i) i)"
    using diff_eq_eq by blast
  have same_coeffs: "\<forall>i \<le> r. Polynomial.coeff q i = Polynomial.coeff (one_less_degree q) i"
    using qis oldis
    by (metis (no_types, lifting) Multiv_Poly_Props.one_less_degree_def Orderings.order_eq_iff Polynomial.coeff_diff Polynomial.coeff_monom diff_zero not_less_eq_eq r)   
  then have coeff_zer: "\<forall>i \<le> r . (i > (length (Polynomial.coeffs (one_less_degree q)) -1 ) \<longrightarrow> (Polynomial.coeffs q) ! i = 0)"
    by (metis coeffs_between_one_less_degree coeffs_nth deg_gt degree_0 degree_eq_length_coeffs le_imp_less_Suc nat_less_le r)
  then have "\<And>i. (i < r + 1 \<and> i \<ge> (length (Polynomial.coeffs (one_less_degree q)))) \<Longrightarrow> (lookup_assump_aux ((Polynomial.coeffs q) ! i) assumps = None \<or> lookup_assump_aux ((Polynomial.coeffs q) ! i) assumps = Some 0)"
  proof -
    fix i
    let ?coeff = "(Polynomial.coeffs q) ! i"
    assume "i < r + 1 \<and> i \<ge> (length (Polynomial.coeffs (one_less_degree q)))"
    then have " (Polynomial.coeffs q) ! i = 0" using coeff_zer
      by (metis (no_types, lifting) Multiv_Poly_Props.one_less_degree_def Polynomial.coeff_monom Suc_eq_plus1 add_diff_cancel_left' coeffs_eq_Nil coeffs_nth degree_0 diff_less diff_zero length_0_conv length_greater_0_conv less_Suc_eq_le less_imp_diff_less oldis order_le_less qis r)
    then have "\<And>k. Polynomial.coeffs q ! i = 0 \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> (0, k) \<in> set assumps \<Longrightarrow> False"
      using sat_eval unfolding satisfies_evaluation_def
      using eval_mpoly_map_poly_comm_ring_hom.base.hom_zero sat_eval satisfies_evaluation_nonzero by blast 
    then have "\<not>(\<exists>k. k \<noteq> 0 \<and> (?coeff, k) \<in> set assumps)"
      by (metis \<open>Polynomial.coeffs q ! i = 0\<close>) 
    then have "\<not>(\<exists>k. k \<noteq> 0 \<and> lookup_assump_aux ((Polynomial.coeffs q) ! i) assumps = Some k)"
      using lookup_assump_means_inset
      by metis
    then show "(lookup_assump_aux ((Polynomial.coeffs q) ! i) assumps = None \<or> lookup_assump_aux ((Polynomial.coeffs q) ! i) assumps = Some 0)"
      using lookup_assump_aux_eo
      by metis 
  qed
  then have lookup_inbtw: "\<And>i. (i < r + 2 \<and> i \<ge> (length (Polynomial.coeffs (one_less_degree q)))) \<Longrightarrow> (lookup_assump_aux ((Polynomial.coeffs q) ! i) assumps = None \<or> lookup_assump_aux ((Polynomial.coeffs q) ! i) assumps = Some 0)"
    using lc_is lc_zero nat_less_le
    by (metis Suc_1 add_Suc_right less_antisym) 
  let ?ell = "(Polynomial.coeffs q)"
  let ?list_len = "length ?ell"
  let ?k = "(length (Polynomial.coeffs (one_less_degree q)))"
  have sublist: "Sublist.strict_prefix (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)) (Polynomial.coeffs q)"
    using deg_gt one_less_degree_is_strict_prefix assms by auto 
  then have drop_is: "(drop (?list_len - ?k) (rev ?ell)) = (rev (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)))"
    using same_coeffs one_less_degree_is_strict_prefix
    by (metis append_eq_conv_conj deg_gt one_less_degree_is_prefix prefix_def rev_take) 
  let ?full_list = "(rev (Polynomial.coeffs q))"
  let ?sub_list = "(rev (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)))"
  have "length (Polynomial.coeffs q) = r + 2"
    using r unfolding Polynomial.coeffs_def 
    by auto 
  have fnz: "first_nonzero_coefficient_helper assumps (?full_list) = 
    first_nonzero_coefficient_helper assumps (drop (length ?full_list - length ?sub_list) (?full_list))"
    using lookup_inbtw sign_of_first_nonzero_coefficient_drop[of "r + 2" "Polynomial.coeffs q" "length ?sub_list" assumps]
    by (metis \<open>length (Polynomial.coeffs q) = r + 2\<close> diff_is_0_eq drop0 length_rev linorder_not_le) 
  have "?full_list = append (take (length ?full_list - length ?sub_list) ?full_list) ?sub_list "
    using sublist drop_is
    by (metis append_take_drop_id length_rev) 
  then have "first_nonzero_coefficient_helper assumps (rev (Polynomial.coeffs q)) =
    first_nonzero_coefficient_helper assumps
    (rev (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)))"
    using fnz
    by (simp add: drop_is) 
  then show ?thesis 
    unfolding sign_of_first_nonzero_coefficient_def by auto
qed 

lemma sign_fnz_aux_helper:
  assumes "\<forall>elem. elem \<in> set coeffl \<longrightarrow> lookup_assump_aux elem ell  = Some 0"
  shows "sign_of_first_nonzero_coefficient_aux ell coeffl = 0" using assms
proof (induct coeffl)
  case Nil
  then show ?case 
    by (simp add: sign_of_first_nonzero_coefficient_aux_def) 
next
  case (Cons a x)
  have firsth: "lookup_assump_aux a ell = Some 0"
    using Cons.prems
    by (simp add: member_rec(1)) 
  have "\<forall>elem. elem \<in> set x \<longrightarrow> lookup_assump_aux elem ell = Some 0 "
    using Cons.prems
    by (simp add: member_rec(1)) 
  then have bigh: "sign_of_first_nonzero_coefficient_aux ell x = 0"
    using Cons.hyps by auto
  then have "first_nonzero_coefficient_helper ell x = 0"
    unfolding sign_of_first_nonzero_coefficient_aux_def 
    by auto
  then show ?case using firsth unfolding sign_of_first_nonzero_coefficient_aux_def
    by auto
qed

lemma sign_fnz_helper: 
  assumes "\<forall>coeff. coeff \<in> set (Polynomial.coeffs q) \<longrightarrow> lookup_assump_aux coeff (map_mpoly_sign_data val (all_coeffs qs)) 
    = Some 0"
  shows "sign_of_first_nonzero_coefficient (map_mpoly_sign_data val (all_coeffs qs)) q = 0" using assms
proof - 
  have "sign_of_first_nonzero_coefficient_aux (map_mpoly_sign_data val (all_coeffs qs)) (rev (Polynomial.coeffs q)) = 0"
    using sign_fnz_aux_helper[of "(Polynomial.coeffs q)" "(map_mpoly_sign_data val (all_coeffs qs))"] assms
    by (metis in_set_member set_rev sign_fnz_aux_helper) 
  then show ?thesis using
      sign_of_first_nonzero_coefficient_aux by auto
qed

lemma sign_of_first_nonzero_coefficient_zer:
  assumes qin: "q \<in> set qs"
  assumes "(eval_mpoly_poly val q) = 0"
  shows "sign_of_first_nonzero_coefficient (map_mpoly_sign_data val (all_coeffs qs)) q =
       Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))"
proof - 
  have st_zero: "Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q)) = 0"
    using assms
    by simp
  have h1: "\<And>coeff.
       q \<in> set qs \<Longrightarrow>
       Poly (map (eval_mpoly val) (Polynomial.coeffs q)) = 0 \<Longrightarrow>
       coeff \<in> set (Polynomial.coeffs q) \<Longrightarrow> 0 < eval_mpoly val coeff \<Longrightarrow> False"
    by (metis (no_types, opaque_lifting) Poly_eq_0 image_eqI image_set in_set_replicate less_numeral_extra(3))
  have h2: "\<And>coeff.
       q \<in> set qs \<Longrightarrow>
       Poly (map (eval_mpoly val) (Polynomial.coeffs q)) = 0 \<Longrightarrow>
       coeff \<in> set (Polynomial.coeffs q) \<Longrightarrow>
       \<not> 0 < eval_mpoly val coeff \<Longrightarrow> eval_mpoly val coeff = 0"
    by (metis (no_types, opaque_lifting) Poly_eq_0 image_eqI image_set in_set_replicate)
  have coeff_zero: "\<forall>coeff \<in> set (Polynomial.coeffs q). mpoly_sign val coeff = 0"
    using assms unfolding eval_mpoly_poly_def map_poly_def mpoly_sign_def
    using h1 h2 using sign_simps(2) by blast 
  have "\<forall>coeff \<in> set (Polynomial.coeffs q). lookup_assump_aux coeff (map_mpoly_sign_data val (all_coeffs qs))
    = Some 0"
  proof clarsimp
    fix  coeff
    assume inset: "coeff \<in> set (Polynomial.coeffs q) "
    then have h1: "mpoly_sign val coeff = 0" 
      using coeff_zero by auto
    have h2: "coeff \<in> set (all_coeffs qs)"
      using qin inset all_coeffs_member all_coeffs_alt
      by blast 
    have "(coeff, 0) \<in> set (map_mpoly_sign_data val (all_coeffs qs))"
      unfolding map_mpoly_sign_data_def mpoly_sign_data_def 
      using h1 h2
      by (simp add: list.set_map member_def) 
    then show "lookup_assump_aux coeff (map_mpoly_sign_data val (all_coeffs qs)) = Some 0"
      using lookup_assump_aux_property map_mpoly_sign_data_duplicates by presburger
  qed     
  then have "\<forall>coeff. coeff \<in> set (Polynomial.coeffs q)  \<longrightarrow> lookup_assump_aux coeff (map_mpoly_sign_data val (all_coeffs qs)) 
    = Some 0"
    by simp
  then show ?thesis using st_zero sign_fnz_helper
    by simp
qed

lemma sign_of_first_nonzero_coefficient_nonzer:
  assumes inset: "q \<in> set qs"
  assumes nonz: "(eval_mpoly_poly val q) \<noteq> 0"                   
  assumes sat_eval: "\<And>p n. (p,n) \<in> set (map_mpoly_sign_data val (all_coeffs qs)) \<Longrightarrow> satisfies_evaluation val p n"
  shows "sign_of_first_nonzero_coefficient (map_mpoly_sign_data val (all_coeffs qs)) q =
       Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))"
proof - 
  let ?assumps = "(map_mpoly_sign_data val (all_coeffs qs))"
  have qnonz: "q \<noteq> 0" using nonz by auto 
  let ?eval_q = "(eval_mpoly_poly val q)"
  have "\<forall>x > (Polynomial.degree ?eval_q). Polynomial.coeff ?eval_q x = 0"
    using coeff_eq_0 by blast
  have deg_leq: "(Polynomial.degree ?eval_q) \<le> Polynomial.degree q"
    by (simp add: degree_map_poly_le eval_mpoly_poly_def)
  let ?deg_eq = "Polynomial.degree ?eval_q"
  let ?deg_q = "Polynomial.degree q"
  have st_nonzero: "Sturm_Tarski.sign (Polynomial.lead_coeff ?eval_q) \<noteq> 0"
    using nonz
    by (simp add: Sturm_Tarski.sign_def)
  then have coi_sign: "mpoly_sign val (Polynomial.coeff q ?deg_eq) = Sturm_Tarski.sign (Polynomial.lead_coeff ?eval_q)"
    unfolding mpoly_sign_def eval_mpoly_poly_def
    by auto
  let ?coi = "Polynomial.coeff q ?deg_eq"
  have mem: "((mpoly_sign_data val ?coi)::real mpoly \<times> rat) \<in> set ?assumps"
    unfolding map_mpoly_sign_data_def using all_coeffs_member[of q qs ?coi]
    by (metis \<open>Polynomial.degree (eval_mpoly_poly val q) \<le> Polynomial.degree q\<close> coeff_in_coeffs eval_mpoly_poly_comm_ring_hom.hom_zero image_eqI image_set inset nonz)
  then obtain elem1 elem2 where elems_prop: "(elem1, elem2) = mpoly_sign_data val ?coi"
    using mpoly_sign_data_def by force
  then have elem2_prop: "elem2 = Sturm_Tarski.sign (Polynomial.lead_coeff ?eval_q)"
    using coi_sign 
    by (simp add: mpoly_sign_data_def) 
  have key1: "lookup_assump_aux ?coi ?assumps = Some (rat_of_int (Sturm_Tarski.sign (Polynomial.lead_coeff ?eval_q)))"
    using sat_eval elems_prop mem elem2_prop st_nonzero
    by (simp add: eval_mpoly_poly_coeff1 lookup_assump_aux_property map_mpoly_sign_data_duplicates mpoly_sign_data_def mpoly_sign_def)
  have len_coeffs_q: "length (Polynomial.coeffs q) = ?deg_q + 1"
    unfolding Polynomial.coeffs_def using qnonz
    by simp 
  have len_coeffs_eq: "length (Polynomial.coeffs ?eval_q) = ?deg_eq + 1"
    using length_coeffs nonz by blast
  moreover {
    assume *: "(Polynomial.degree ?eval_q) = Polynomial.degree q"
    then have coi_is: "?coi = Polynomial.lead_coeff q"
      by simp
    have "\<exists> h T. (rev (Polynomial.coeffs q)) = (h#T)"
      by (meson neq_Nil_conv not_0_coeffs_not_Nil qnonz rev_is_Nil_conv)
    then obtain h T where ht_prop: "(rev (Polynomial.coeffs q)) = (h#T)" 
      by auto
    have "(rev (Polynomial.coeffs q)) ! 0 = (Polynomial.coeffs q) ! (Polynomial.degree q)"
      by (simp add: degree_eq_length_coeffs qnonz rev_nth)
    then have revis: "(rev (Polynomial.coeffs q)) ! 0 = ?coi" 
      using coi_is
      by (simp add: coeffs_nth qnonz) 
    then have "lookup_assump_aux ((rev (Polynomial.coeffs q)) ! 0) ?assumps = Some (rat_of_int (Sturm_Tarski.sign (Polynomial.lead_coeff ?eval_q)))"
      using key1 st_nonzero coi_sign revis
      unfolding sign_of_first_nonzero_coefficient_def first_nonzero_coefficient_helper_def
      by auto
    then have ?thesis
      using ht_prop st_nonzero unfolding sign_of_first_nonzero_coefficient_def 
      by auto
  }
  moreover {
    assume *: "(Polynomial.degree ?eval_q) < Polynomial.degree q"
    then have lt: "Polynomial.degree (eval_mpoly_poly val q) + 1 < Polynomial.degree q + 1" 
      using len_coeffs_q len_coeffs_eq add_less_cancel_right by blast
    have key2: "\<And>x. ((x \<ge> ?deg_eq + 1 \<and> x < ?deg_q + 1) \<Longrightarrow> 
      lookup_assump_aux ((Polynomial.coeffs q) ! x) ?assumps = Some 0)"  
    proof - 
      fix x
      assume xgeq: "(x \<ge> ?deg_eq + 1 \<and> x < ?deg_q + 1)"
      let ?coi2 = "((Polynomial.coeffs q) ! x)"
      have mem: "((mpoly_sign_data val ?coi2)::real mpoly \<times> rat) \<in> set ?assumps"
        unfolding map_mpoly_sign_data_def using all_coeffs_member[of q qs ?coi2]
        by (metis image_eqI image_set inset len_coeffs_q nth_mem xgeq)
      then obtain newelem2 where newelems_prop: "(?coi2, newelem2) = mpoly_sign_data val ?coi2"
        using mpoly_sign_data_def by force
      have xzer: "eval_mpoly val ?coi2 = 0"
        using xgeq
        by (metis Suc_eq_plus1 coeff_eq_0 coeffs_nth eval_mpoly_map_poly_comm_ring_hom.base.coeff_map_poly_hom eval_mpoly_poly_def linorder_not_le not_less_eq_eq qnonz) 
      have elem2_prop: "(sgn (eval_mpoly val ?coi2) = real_of_rat (sgn newelem2))"
        using sat_eval[of ?coi2 "newelem2"] mem newelems_prop
        using satisfies_evaluation_alternate unfolding satisfies_evaluation_alternate_def satisfies_evaluation_def
        by metis
      then  have key11: "lookup_assump_aux ?coi2 ?assumps = Some 0"
        using xzer
        by (metis lookup_assump_aux_property map_mpoly_sign_data_duplicates mem newelems_prop of_rat_0 of_rat_hom.injectivity sgn_0_0)
      then show "lookup_assump_aux ((Polynomial.coeffs q) ! x) ?assumps = Some 0" by auto
    qed
    then have "(\<And>i. Polynomial.degree (eval_mpoly_poly val q) + 1 \<le> i \<and> i < Polynomial.degree q + 1 \<Longrightarrow>
          lookup_assump_aux (Polynomial.coeffs q ! i) ?assumps = None \<or>
          lookup_assump_aux (Polynomial.coeffs q ! i) ?assumps = Some 0)"
      by blast
    then have fnz: "first_nonzero_coefficient_helper ?assumps (rev (Polynomial.coeffs q))
     = first_nonzero_coefficient_helper ?assumps (drop ((?deg_q + 1) - (?deg_eq + 1)) (rev (Polynomial.coeffs q)))"
      using sign_of_first_nonzero_coefficient_drop[of "?deg_q + 1" "Polynomial.coeffs q" "?deg_eq + 1" ?assumps]
      using len_coeffs_q lt by auto 
    have coeff_deg_eq: "(Polynomial.coeffs q) ! ?deg_eq = ?coi"
      unfolding Polynomial.coeffs_def
      by (smt (verit, ccfv_threshold) Polynomial.coeffs_def coeffs_nth deg_leq qnonz)
    have "(Polynomial.coeffs q) ! ?deg_eq = (Polynomial.coeff q ?deg_eq)"
      unfolding Polynomial.coeffs_def
      by (smt (verit, ccfv_SIG) Polynomial.coeffs_def coeff_deg_eq) 
    then have drop_zer_is: "(drop (?deg_q - ?deg_eq) (rev (Polynomial.coeffs q))) ! 0 = (Polynomial.coeff q ?deg_eq)"
      using len_coeffs_q
      by (metis (no_types, lifting) add.right_neutral add_Suc_right deg_leq degree_eq_length_coeffs diff_diff_cancel diff_diff_left diff_le_self diff_less_Suc length_rev nth_drop plus_1_eq_Suc rev_nth) 
    let ?loi = "(drop (?deg_q - ?deg_eq) (rev (Polynomial.coeffs q))) "
    have "\<exists>h T. ?loi = h#T"
      by (metis Suc_eq_plus1 append.right_neutral append_take_drop_id diff_is_0_eq diff_less_Suc diff_less_mono le_refl len_coeffs_q length_rev length_take less_nat_zero_code min.cobounded2 variables.cases)
    then have "first_nonzero_coefficient_helper ?assumps (drop ((?deg_q + 1) - (?deg_eq + 1)) (rev (Polynomial.coeffs q))) =
     (Sturm_Tarski.sign (Polynomial.lead_coeff ?eval_q))"
      using key1 st_nonzero drop_zer_is unfolding first_nonzero_coefficient_helper_def 
      by auto
    then have ?thesis  unfolding sign_of_first_nonzero_coefficient_def
      using fnz
      by auto
  }
  ultimately have ?thesis 
    using deg_leq nat_less_le by blast 
  then show ?thesis by auto 
qed

lemma sign_of_first_nonzero_coefficient:
  assumes inset: "q \<in> set qs"                 
  assumes sat_eval: "\<And>p n. (p,n) \<in> set (map_mpoly_sign_data val (all_coeffs qs)) \<Longrightarrow> satisfies_evaluation val p n"
  shows "sign_of_first_nonzero_coefficient (map_mpoly_sign_data val (all_coeffs qs)) q =
       Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))"
  using assms sign_of_first_nonzero_coefficient_zer sign_of_first_nonzero_coefficient_nonzer
  by blast

section "Relating multiple definitions"

lemma csv_as_expected_left:
  fixes qs:: "real mpoly list"
  assumes n_is: "n = length (variables_list qs)"      
  assumes biggest_var_is: "biggest_var = nth (variables_list qs) (n-1) + 1"
    (* Need this to have a finite set for characterize_consistent_signs_at_roots *)
  assumes qs_signs: "qs_signs = mpoly_consistent_sign_vectors qs (all_lists biggest_var)"
  shows "(sign_val \<in> qs_signs) \<Longrightarrow> (\<exists> val. (map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> (\<lambda>p. eval_mpoly val p)) qs = sign_val))" 
proof - 
  assume inset: "sign_val \<in> qs_signs"
  have "\<exists>(l::real list). (List.length l = biggest_var \<and> sign_val = map_mpoly_sign qs l)"
    using inset qs_signs unfolding mpoly_consistent_sign_vectors_def all_lists_def
    by blast 
  then show "(\<exists> val. (map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> (\<lambda>p. eval_mpoly val p)) qs = sign_val))"
    using map_mpoly_sign_def by auto
qed

lemma in_list_lemma:
  assumes "n = length l"
  shows inlist: "(v \<in> set l \<Longrightarrow> (\<exists>k\<le>n-1. v = nth l k)) "
  using assms
proof (induct l arbitrary: n v)
  case Nil
  then show ?case
    by (simp add: member_rec(2)) 
next
  case (Cons a l)
  then have "n - 1 = length l"
    by simp
  then have ex_l: "v \<in> set l \<longrightarrow> (\<exists>k\<le>n-2. v = l ! k)"
    using Cons.hyps
    by (metis diff_diff_left one_add_one) 
  have eo: "v \<in> set (a#l) \<Longrightarrow> v = a \<or> v \<in> set l"
    by (simp add: member_rec(1))
  show ?case
  proof -
    have h1: "v = a \<Longrightarrow> \<exists>k\<le>n - Suc 0. v = (a # l) ! k"
      by auto
    have h2: "v \<in> set l \<Longrightarrow> \<exists>k\<le>n - Suc 0. v = (a # l) ! k"
    proof - 
      assume *: "v \<in> set l"
      then have "(\<exists>k\<le>n-2. v = l ! k)"
        using ex_l
        by (metis nat_1_add_1 plus_1_eq_Suc) 
      then obtain k where "k \<le> n - 2 \<and> v = l ! k"
        by auto
      then have "l ! k = (a # l) ! (k+1)"
        by force 
      then show "\<exists>k\<le>n - Suc 0. v = (a # l) ! k"
        by (metis "*" One_nat_def Suc_leI \<open>n - 1 = length l\<close> in_set_conv_nth nth_Cons_Suc)
    qed
    show ?thesis
      using h1 h2 Cons
      by (metis One_nat_def eo) 
  qed 
qed

lemma eval_list_longer_than_degree:
  assumes gt_than: "\<forall>i \<in> vars q. length val > i"
  assumes "length ell \<ge> length val"
  assumes "\<forall>i < length val. ell ! i = val ! i"
  shows "eval_mpoly ell q = eval_mpoly val q"
proof - 
  have "\<And>m. lookup (mapping_of q) m  \<noteq> 0 \<Longrightarrow> (\<Prod>v. nth_default 0 ell v ^ lookup m v) = (\<Prod>v. nth_default 0 val v ^ lookup m v)"
  proof - 
    fix m
    assume *: "lookup (mapping_of q) m  \<noteq> 0"
    then have "\<forall>v. (lookup m v \<noteq> 0 \<longrightarrow> v \<in> vars q)"
      by (metis coeff_def coeff_isolate_variable_sparse isovarsparNotIn)
    then have zer_lookup: "\<forall> v \<ge> length val. lookup m v = 0"
      using * assms
      using linorder_not_less by blast 
    have h1: "\<forall> v \<ge> length val. nth_default 0 ell v ^ lookup m v = 1"
      using zer_lookup by auto
    have h2: "\<forall> v \<ge> length val. nth_default 0 val v ^ lookup m v = 1"
      using zer_lookup by auto
    have h3: "\<forall> v < length val. nth_default 0 ell v ^ lookup m v = nth_default 0 val v ^ lookup m v "
      using assms
      by (metis nth_default_def order_less_le_trans)
    then show "(\<Prod>v. nth_default 0 ell v ^ lookup m v) = (\<Prod>v. nth_default 0 val v ^ lookup m v)" 
      using h1 h2 h3
      by (metis linorder_not_le) 
  qed
  then show ?thesis 
    using assms unfolding eval_mpoly_def unfolding insertion_def insertion_aux_def
    unfolding insertion_fun_def
    by (smt (verit, best) Prod_any.cong Sum_any.cong id_apply map_fun_apply mult_cancel_left) 
qed

lemma same_eval_list_tailing_zeros:
  assumes "length ell > length val"
  assumes "\<forall>i < length val. ell ! i = val ! i"
  assumes ell_zeros: "\<forall> i < length ell. (i \<ge> length val \<longrightarrow> ell ! i = 0)"
  shows "eval_mpoly ell q = eval_mpoly val q"
proof - 
  have "\<And>m. lookup (mapping_of q) m  \<noteq> 0 \<Longrightarrow> (\<Prod>v. nth_default 0 ell v ^ lookup m v) = (\<Prod>v. nth_default 0 val v ^ lookup m v)"
  proof - 
    fix m
    assume "lookup (mapping_of q) m  \<noteq> 0"
    have h1_val: "\<forall> v \<ge> length val. nth_default 0 val v = 0"
      by (simp add: nth_default_beyond)
    have h1_ell: "\<And> v . v \<ge> length val \<Longrightarrow> nth_default 0 ell v = 0"
      by (simp add: ell_zeros nth_default_eq_dflt_iff)
    have h1: "\<forall> v \<ge> length val. nth_default 0 ell v ^ lookup m v = nth_default 0 val v ^ lookup m v "
      using h1_val h1_ell
      by presburger 
    have h2: "\<forall> v < length val. nth_default 0 ell v ^ lookup m v = nth_default 0 val v ^ lookup m v "
      using assms
      by (metis nth_default_nth order_less_trans) 
    then show "(\<Prod>v. nth_default 0 ell v ^ lookup m v) = (\<Prod>v. nth_default 0 val v ^ lookup m v)" 
      using h1 h2
      by (metis linorder_not_le) 
  qed
  then show ?thesis 
    using assms unfolding eval_mpoly_def unfolding insertion_def insertion_aux_def
    unfolding insertion_fun_def
    by (smt (verit, best) Prod_any.cong Sum_any.cong id_apply map_fun_apply mult_cancel_left) 
qed

lemma biggest_variable_in_sorted_list:
  assumes length_nonz: "variables_list qs \<noteq> []"
  assumes n_is: "n = length (variables_list qs)"
  shows "(m \<in> set (variables_list qs) \<Longrightarrow> (nth (variables_list qs) (n-1)) \<ge> m)"
proof -
  have allk: "\<forall>k < n-1. (nth (variables_list qs) k) \<le> (nth (variables_list qs) (k+1))"
    using n_is
    by (simp add: sorted_wrt_nth_less) 
  then have "\<And>v. \<forall>k<n - Suc 0. sorted_list_of_set (variables qs) ! k \<le> sorted_list_of_set (variables qs) ! Suc k \<Longrightarrow>
         (\<And>n l v. n = length l \<Longrightarrow> v \<in> set l \<Longrightarrow> \<exists>k\<le>n - Suc 0. v = l ! k) \<Longrightarrow>
         v \<in> set (sorted_list_of_set (variables qs)) \<Longrightarrow>
         v \<le> sorted_list_of_set (variables qs) ! (n - Suc 0)"
    by (metis One_nat_def Suc_less_eq Suc_pred diff_less in_list_lemma length_greater_0_conv length_nonz less_numeral_extra(1) n_is sorted_iff_nth_Suc sorted_nth_mono variables_list.simps) 
  then have allin: "\<forall>v. (v \<in> set (variables_list qs) \<longrightarrow> v \<le> nth (variables_list qs) (n-1))"
    using inlist allk
    by (auto)
  then show "\<And> m. (m \<in> set (variables_list qs) \<Longrightarrow> (nth (variables_list qs) (n-1)) \<ge> m)"
  proof -
    fix m
    assume mem: "m \<in> set (variables_list qs)"
    let ?len = "length (variables_list qs)"
    have "\<exists>w < ?len. m = (variables_list qs) ! w"
      using mem
      by (metis in_set_conv_nth) 
    then obtain w where w_prop: "w < ?len \<and>m = (variables_list qs) ! w"
      by auto
    then have leq: "w \<le> n-1" using n_is 
      by auto 
    have "sorted (variables_list qs)"
      using sorted_sorted_list_of_set 
      by simp
    then show "nth (variables_list qs) (n-1) \<ge> m"
      using leq w_prop allin mem 
      by blast 
  qed
qed

lemma csv_as_expected_right:
  fixes qs:: "real mpoly list"
  assumes length_nonz: "length (variables_list qs) > 0"
  assumes n_is: "n = length (variables_list qs)"      
  assumes biggest_var_is: "biggest_var = nth (variables_list qs) (n-1) + 1"
    (* Need this to have a finite set for characterize_consistent_signs_at_roots *)
  assumes qs_signs: "qs_signs = mpoly_consistent_sign_vectors qs (all_lists biggest_var)"
  shows "(\<exists> val. (map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> (\<lambda>p. eval_mpoly val p)) qs = sign_val)) \<Longrightarrow> (sign_val \<in> qs_signs)" 
proof - 
  assume "(\<exists> val. (map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> (\<lambda>p. eval_mpoly val p)) qs = sign_val))"
  then obtain val where val_prop: "(map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> (\<lambda>p. eval_mpoly val p)) qs = sign_val)"
    by auto
  then have "length sign_val = length qs"
    using  List.length_map by auto 
  have inlist: "\<forall>v. (v \<in> set (variables_list qs) \<longrightarrow> (\<exists>k\<le>n-1. v = nth (variables_list qs) k)) "
    using in_list_lemma n_is
    by metis 
  have allin: "\<forall>v. (v \<in> set (variables_list qs) \<longrightarrow> v \<le> nth (variables_list qs) (n-1))"
    using inlist
    by (metis biggest_variable_in_sorted_list length_nonz less_numeral_extra(3) list.size(3) n_is) 
  have "sorted_list_of_set (variables qs) = remdups (sorted_list_of_set (variables qs))"
    by (metis remdups_id_iff_distinct sorted_list_of_set(3)) 
  then have remdups: "variables_list qs = remdups (variables_list qs)"
    by simp
  have "(nth (variables_list qs) (n-1)) \<in> set (variables_list qs)" 
    using n_is length_nonz
    by (metis Suc_pred' in_set_conv_nth lessI) 
      (* then show it's the biggest element in the list *)
  then have biggest: "\<And> m. (m \<in> set (variables_list qs) \<Longrightarrow> (nth (variables_list qs) (n-1)) \<ge> m)" 
    using assms biggest_variable_in_sorted_list
    using allin by presburger 
  have gtthan_to_zero: "\<forall>m \<ge> biggest_var. \<forall>(q::real mpoly) \<in> set(qs). MPoly_Type.degree (q::real mpoly) m = 0" 
  proof clarsimp 
    fix m q
    assume m: "biggest_var \<le> m"
    assume qin: "q \<in> set qs" 
    have "\<forall> v. (v \<in> set (variables_list qs) \<longrightarrow> m > v)"
      using biggest m
      using biggest_var_is by fastforce  
    then have "\<forall>v \<in> vars q. m > v"
      using qin variables_list_prop 
      by blast 
    then show "MPoly_Type.degree q m = 0"
      using biggest_var_is n_is degree_eq_0_iff 
      by blast
  qed
    (* then truncate val or expand val *)
  moreover {
    assume *: "length val \<ge> biggest_var"
    let ?ell = "take biggest_var val"
    have ell_prop: "length ?ell = biggest_var"
      by (simp add: "*")
    have "\<And>(q::real mpoly). q\<in> set qs \<Longrightarrow>  eval_mpoly ?ell q = eval_mpoly val q"
    proof - fix q
      assume "q \<in> set (qs)"
      have h1: "\<forall>i\<in>vars q. i < length (take biggest_var val)"
        by (metis \<open>q \<in> set qs\<close> degree_eq_0_iff ell_prop gtthan_to_zero linorder_le_less_linear)
      have h2: "length (take biggest_var val) \<le> length val" 
        using * ell_prop by auto
      have h3: "\<forall>i<length (take biggest_var val). val ! i = take biggest_var val ! i"
        by simp
      show "eval_mpoly ?ell q = eval_mpoly val q"
        using h1 h2 h3 eval_list_longer_than_degree[of q ?ell val]
        by auto
    qed
    then have "map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> eval_mpoly ?ell) qs = map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> eval_mpoly val) qs "
      by auto
    then have "\<exists>ell. length ell = biggest_var \<and> map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> eval_mpoly ell) qs = sign_val"
      using ell_prop val_prop
      by blast 
  } 
  moreover {
    assume *: "length val < biggest_var"
    let ?ell = "val @ (zero_list (biggest_var - length val))"
    have len: "length ?ell = biggest_var"
      using * zero_list_len
      by (metis add_diff_cancel_left' eq_diff_iff length_append less_or_eq_imp_le zero_less_diff) 
    then have p1: "(\<forall> n < length val. ?ell ! n = val ! n)"
      using *
      by (meson nth_append) 
    have p2: "(\<forall>n \<ge> length val. n < biggest_var \<longrightarrow> ?ell ! n = 0)"
      using * zero_list_member
      by (metis diff_less_mono leD nth_append)
    have "\<And>q. (q::real mpoly) \<in> set(qs) \<Longrightarrow> eval_mpoly ?ell q = eval_mpoly val q"
    proof -
      fix q
      assume "q \<in> set qs"
      show "eval_mpoly ?ell q = eval_mpoly val q"
        using p1 p2  same_eval_list_tailing_zeros[of val ?ell q] * len
        by presburger
    qed
    then have "\<exists>ell. length ell = biggest_var \<and> map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> eval_mpoly ell) qs = sign_val"
      using val_prop len
      by (smt (verit) comp_apply map_eq_conv) 
  }
  ultimately  have "\<exists>ell. length ell = biggest_var \<and> map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> eval_mpoly ell) qs = sign_val"
    by (meson linorder_le_less_linear)
  then show ?thesis using qs_signs unfolding mpoly_consistent_sign_vectors_def map_mpoly_sign_def
    using all_lists_def by auto
qed

lemma csv_as_expected:
  assumes length_nonz: "length (variables_list qs) > 0"
  assumes n_is: "n = length (variables_list qs)"
  assumes biggest_var_is: "biggest_var = nth (variables_list qs) (n-1) + 1"
    (* Need this to have a finite set for characterize_consistent_signs_at_roots *)
  assumes qs_signs: "qs_signs = mpoly_consistent_sign_vectors qs (all_lists biggest_var)"
  shows "(sign_val \<in> qs_signs) \<longleftrightarrow> (\<exists> val. (map (rat_of_int \<circ> Sturm_Tarski.sign \<circ> (eval_mpoly val)) qs = sign_val))" 
  using assms csv_as_expected_left[of n qs biggest_var qs_signs sign_val] csv_as_expected_right
  by blast

definition dim_poly:: "real mpoly \<Rightarrow> nat"
  where "dim_poly q = Max (vars q)"

definition dim_poly_list:: "real mpoly list \<Rightarrow> nat"
  where "dim_poly_list qs = Max (variables qs)"

lemma dim_poly_list_prop:
  assumes length_nonz: "variables_list qs \<noteq> []"
  assumes n_is: "n = length (variables_list qs)"
  shows "dim_poly_list qs = nth (variables_list qs) (n-1)"
proof -
  let ?biggest_var = "nth (variables_list qs) (n-1)"
  have "?biggest_var \<in> set (variables_list qs)"
    using assms
    by (meson diff_less length_greater_0_conv member_def nth_mem zero_less_one)
  then have h1: "nth (variables_list qs) (n-1) \<in> variables qs"
    using variables_prop assms
    using variables_list_prop by blast 
  have h2: "\<forall>x \<in> variables qs. x \<le> nth (variables_list qs) (n-1)"
    using assms biggest_variable_in_sorted_list variables_list_prop variables_prop 
    by presburger
  show ?thesis using h1 h2 variables_finite unfolding dim_poly_list_def
    by (meson Max_eqI) 
qed

lemma lookup_assump_aux_subset_consistency:
  assumes val: "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  assumes subset: "set new_assumps \<subseteq> set branch_assms"
  assumes i_assm: "(\<exists>i. lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i \<and> i \<noteq> 0)"
  shows "(\<exists>i. lookup_assump_aux (Polynomial.lead_coeff r) branch_assms = Some i \<and> i \<noteq> 0)"
proof - 
  obtain i where i_prop: "lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i"
    "i \<noteq> 0"
    using i_assm
    by auto
  then have "(Polynomial.lead_coeff r, i) \<in> set new_assumps"
    by (meson lookup_assump_means_inset)
  then have in_set: "(Polynomial.lead_coeff r, i) \<in> set branch_assms"
    using subset by auto
  then have "satisfies_evaluation val (Polynomial.lead_coeff r) i"
    using val by auto
  then have "\<not> (satisfies_evaluation val (Polynomial.lead_coeff r) 0)"
    using i_prop(2) unfolding satisfies_evaluation_def
    by (metis linorder_neqE_linordered_idom of_int_hom.hom_0_iff one_neq_zero sign_simps(1) sign_simps(2) sign_simps(3) zero_neq_neg_one)  
  then have not_in_set: "(Polynomial.lead_coeff r, 0) \<notin> set branch_assms"
    using val
    by blast 
  show ?thesis using in_set not_in_set i_prop(2)
    by (metis inset_means_lookup_assump_some lookup_assump_means_inset) 
qed

lemma lookup_assump_aux_subset_consistent_sign:
  assumes val: "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  assumes subset: "set new_assumps \<subseteq> set branch_assms"
  assumes i1: "lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i1"
  assumes i2: "lookup_assump_aux (Polynomial.lead_coeff r) branch_assms = Some i2"
  shows "Sturm_Tarski.sign i1 = Sturm_Tarski.sign i2"
proof - 
  have "(Polynomial.lead_coeff r, i1) \<in> set new_assumps"
    using i1
    by (simp add: lookup_assump_means_inset)
  then have in_set: "(Polynomial.lead_coeff r, i1) \<in> set branch_assms"
    using subset by auto
  then have sat_eval: "satisfies_evaluation val (Polynomial.lead_coeff r) i1"
    using val by auto
  have "Sturm_Tarski.sign i1 \<noteq> Sturm_Tarski.sign i2 \<Longrightarrow> False"
  proof - 
    assume "Sturm_Tarski.sign i1 \<noteq> Sturm_Tarski.sign i2 "
    then have "\<not> (satisfies_evaluation val (Polynomial.lead_coeff r) i2)"
      using sat_eval unfolding satisfies_evaluation_def
      by presburger
    then have not_in_set: "(Polynomial.lead_coeff r, i2) \<notin> set branch_assms"
      using val
      by blast 
    then show "False" using i2
      by (meson lookup_assump_means_inset member_def) 
  qed
  then show ?thesis
    by blast 
qed


lemma lookup_assump_aux_subset_not_none:
  assumes val: "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  assumes subset: "set new_assumps \<subseteq> set branch_assms"
  assumes i1: "lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i1"
  shows "\<exists>i2. lookup_assump_aux (Polynomial.lead_coeff r) branch_assms = Some i2"
proof - 
  have "(Polynomial.lead_coeff r, i1) \<in> set new_assumps"
    using i1
    by (simp add: lookup_assump_means_inset)
  then have in_set: "(Polynomial.lead_coeff r, i1) \<in> set branch_assms"
    using subset by auto
  then show ?thesis
    by (simp add: inset_means_lookup_assump_some member_def) 
qed

end