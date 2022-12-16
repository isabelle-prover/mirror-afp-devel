(* This file generalizes the notion of Tarski queries 
  to multivariate polynomials.
*)

theory Multiv_Tarski_Query
  imports
    Multiv_Pseudo_Remainder_Sequence
    Hybrid_Multiv_Matrix

begin

definition sign_rat::"'a::{zero,linorder} \<Rightarrow> rat" where
  "sign_rat n = rat_of_int (Sturm_Tarski.sign n)"

section "Connect multivariate Tarski queries to univariate"

lemma cast_sgn_same_map:
  shows "map of_rat (map sgn ell) = map sgn ell"
  by simp 

lemma changes_cast_sgn_same_map:
  shows "changes ((map of_rat ell)::real list) = changes (ell::rat list)"
proof (induct "length ell" arbitrary: ell rule: less_induct)
  case less
  then have indhyp: "\<forall>ell1. length ell1 < length ell \<longrightarrow> changes (map real_of_rat ell1) = changes ell1"
    by blast
  {
    assume *: "length ell = 0"
    then have "changes (map real_of_rat ell) = changes ell"
      by auto
  }
  moreover {
    assume *: "length ell = 1"
    then have "\<exists>h. ell = [h]"
      by (simp add: length_Suc_conv)
    then have "changes (map real_of_rat ell) = changes ell"
      by auto
  }
  moreover {
    assume *: "length ell > 1"
    then have "\<exists>elem1 elem2 ell1. ell = elem1 # (elem2 # ell1)"
      by (metis One_nat_def Suc_le_length_iff le_simps(1) length_Cons less_Suc_eq_le)
    then obtain elem1 elem2 ell1 where ell_prop: "ell = elem1 # (elem2 # ell1)" 
      by auto
    have len_lt: "length (elem1 # ell1) < length ell"
      by (simp add: ell_prop)
    then have h1: "changes (map real_of_rat (elem1 # ell1)) = changes (elem1 # ell1)"
      using indhyp
      by blast
    have h2: "changes (map real_of_rat (elem2 # ell1)) = changes (elem2 # ell1)"
      using indhyp
      by (metis len_lt list.size(4)) 
    have h3: "real_of_rat elem1 * real_of_rat elem2 < 0 \<Longrightarrow> elem2 \<noteq> 0 \<Longrightarrow> elem1 * elem2 < 0"
      by (metis of_rat_less_0_iff of_rat_mult)
    have h4: "\<not> real_of_rat elem1 * real_of_rat elem2 < 0 \<Longrightarrow> elem2 \<noteq> 0 \<Longrightarrow> elem1 * elem2 < 0 \<Longrightarrow> False"
      by (metis of_rat_less_0_iff of_rat_mult)
    have "changes (map real_of_rat (elem1 # (elem2 # ell1))) = changes (elem1 # (elem2 # ell1))"
      using h1 h2 h3 h4 by auto
    then have "changes (map real_of_rat ell) = changes ell"
      using ell_prop by auto
  }
  ultimately show ?case
    by (meson less_one linorder_neqE_nat) 
qed

lemma spmods_multiv_lc_auxNone:
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes pnonz: "p \<noteq> 0"
  assumes lookup_none: "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = None"
  shows "(assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # acc)) 
    \<or> (\<exists>k \<noteq> 0. (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, k) # acc)))"
proof - 
  have "(assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # acc)) 
\<or> ((assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (1::rat)) # acc))) \<or>
(assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (-1::rat)) # acc))"
    using lookup_none inset pnonz spmods_multiv.simps[of p q acc] 
    by auto
  then show ?thesis
    using class_field.zero_not_one class_field.neg_1_not_0
    by metis 
qed

lemma spmods_multiv_lc_auxSome1:
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes pnonz: "p \<noteq> 0"
  assumes lookup_some: "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = Some 0"
  shows "(((Polynomial.lead_coeff p), 0) \<in> set acc  \<and> (assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q acc))"
  using assms spmods_multiv.simps[of p q acc]
  using in_set_member lookup_assum_aux_mem option.simps(5) by fastforce 

lemma spmods_multiv_lc_auxSome2:
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes pnonz: "p \<noteq> 0"
  assumes lookup_some: "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = Some i \<and> i \<noteq> 0"
  shows "(\<exists>k \<noteq> 0. (((Polynomial.lead_coeff p), k) \<in> set acc  \<and> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q acc)))"
  using assms spmods_multiv.simps[of p q acc] lookup_assum_aux_mem
  by (smt (verit, best) in_set_member option.simps(5)) (* may take a couple of seconds to load *) 

lemma spmods_multiv_lc_aux:
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes pnonz: "p \<noteq> 0"
  shows "(\<exists>accum. (((Polynomial.lead_coeff p), 0) \<in> set accum  \<and> (assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q accum)))
\<or> (\<exists>accum. (\<exists>k \<noteq> 0. ((((Polynomial.lead_coeff p), k) \<in> set accum) \<and> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q accum))))" 
proof - 
  have "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = None \<or> (\<exists>k. (lookup_assump_aux (Polynomial.lead_coeff p) acc) = Some k)"
    by auto
  {assume *: "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = None"
    then have "(\<exists>accum. (((Polynomial.lead_coeff p), 0) \<in> set accum  \<and> (assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q accum)))
      \<or> (\<exists>accum. (\<exists>k \<noteq> 0. ((((Polynomial.lead_coeff p), k) \<in> set accum) \<and> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q accum))))"
      using spmods_multiv_lc_auxNone
      by (meson inset list.set_intros(1) pnonz)
  } moreover {assume *: "(\<exists>k. (lookup_assump_aux (Polynomial.lead_coeff p) acc) = Some k)"
    then have "(\<exists>accum. (((Polynomial.lead_coeff p), 0) \<in> set accum  \<and> (assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q accum)))
      \<or> (\<exists>accum. (\<exists>k \<noteq> 0. ((((Polynomial.lead_coeff p), k) \<in> set accum) \<and> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q accum))))"
      using spmods_multiv_lc_auxSome2
      by (metis inset pnonz spmods_multiv_lc_auxSome1) 
  } moreover {assume *: "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = Some 0"
    then have "(\<exists>accum. (((Polynomial.lead_coeff p), 0) \<in> set accum  \<and> (assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q accum)))
      \<or> (\<exists>accum. (\<exists>k \<noteq> 0. ((((Polynomial.lead_coeff p), k) \<in> set accum) \<and> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q accum))))"
      by (metis inset pnonz spmods_multiv_lc_auxSome1) 
  }
  ultimately show ?thesis
    by blast 
qed

(* Uses spmods_multiv_aux_sturm_lc as a helper lemma *)
lemma spmods_multiv_lc:
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes lc_inset: "lc \<in> set (lead_coeffs sturm_seq)"
  shows"\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0"
  using assms  
proof (induct p q acc arbitrary:assumps sturm_seq lc rule: spmods_multiv.induct)
  case ih: (1 p q acc)
  have "p = 0 \<or> p \<noteq> 0" by auto
  moreover {
    assume *: "p = 0"
    then have "sturm_seq = []"
      using ih.prems(1) spmods_multiv.simps by fastforce
    then have "set (lead_coeffs sturm_seq) = {}" by auto
    then have "False"
      using ih.prems(2) by force 
  }
  moreover {
    assume *: "p \<noteq> 0"
    moreover {
      assume **: "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = None"
      then have "(assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # acc)) 
    \<or> (\<exists>k \<noteq> 0. (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, k) # acc)))"
        using  * spmods_multiv_lc_auxNone[of assumps sturm_seq p q acc]
          ih(3) by auto
      moreover {
        assume eo: "(assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # acc))"
        then have "\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0" 
          using ih * ** by blast 
      }
      moreover {
        assume eo: "(\<exists>k \<noteq> 0. (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, k) # acc)))"
        then obtain k where k_prop: "k \<noteq> 0 \<and> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, k) # acc))"
          by auto
        then have "\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0"
          using * spmods_multiv_aux_sturm_lc[of p k "((Polynomial.lead_coeff p, k) # acc)" assumps sturm_seq q] lc_inset
          using ih.prems(2) by auto
      }
      ultimately have "\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0" 
        by blast
    }
    moreover {
      assume **: "\<exists>i. (lookup_assump_aux (Polynomial.lead_coeff p) acc) = Some i"
      then obtain i where i_prop: "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = Some i"
        by auto
      moreover {
        assume i: "i = 0"
        then have "(((Polynomial.lead_coeff p), 0) \<in> set acc   \<and> (assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q acc))"
          using * i_prop spmods_multiv_lc_auxSome1[of assumps sturm_seq p q acc] ih(3)
          by auto
        then have "\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0" using * ih(4) i_prop i
            ih(2)[of i assumps sturm_seq lc] by auto
      }
      moreover {
        assume i: "i \<noteq> 0"
        then have h1: "(\<exists>accum. (\<exists>k \<noteq> 0. ((((Polynomial.lead_coeff p), k)) \<in> set accum \<and> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q accum))))"
          using * i_prop spmods_multiv_lc_auxSome2[of assumps sturm_seq p q acc] ih(3)
          by auto
        then have "\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0" 
          using  spmods_multiv_aux_sturm_lc[of p i acc assumps sturm_seq]
        proof -
          have f1: "\<forall>p r ps psa psb pa pb. ((Polynomial.lead_coeff p, r) \<notin> set ps \<or> r = 0 \<or> (psa, psb) \<notin> set (spmods_multiv_aux p pa ps) \<or> pb \<notin> set psb) \<or> (\<exists>r. (Polynomial.lead_coeff pb, r) \<in> set psa \<and> r \<noteq> 0)"
            using spmods_multiv_aux_sturm_lc by blast
          obtain rr :: "real mpoly Polynomial.poly \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> rat" where
            "\<forall>x0 x3. (\<exists>v7. (Polynomial.lead_coeff x0, v7) \<in> set x3 \<and> v7 \<noteq> 0) = ((Polynomial.lead_coeff x0, rr x0 x3) \<in> set x3 \<and> rr x0 x3 \<noteq> 0)"
            by moura
          then have f2: "\<forall>p r ps psa psb pa pb. ((Polynomial.lead_coeff p, r) \<notin> set ps \<or> r = 0 \<or> (psa, psb) \<notin> set (spmods_multiv_aux p pa ps) \<or> pb \<notin> set psb) \<or> (Polynomial.lead_coeff pb, rr pb psa) \<in> set psa \<and> rr pb psa \<noteq> 0"
            using f1 by presburger
          obtain pp :: "real mpoly Polynomial.poly set \<Rightarrow> (real mpoly Polynomial.poly \<Rightarrow> real mpoly) \<Rightarrow> real mpoly \<Rightarrow> real mpoly Polynomial.poly" where
            f3: "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (pp x0 x1 x2) \<and> pp x0 x1 x2 \<in> x0)"
            by moura
          have "lc \<in> Polynomial.lead_coeff ` set sturm_seq"
            by (smt (z3) ih.prems(2) list.set_map)
          then have f4: "lc = Polynomial.lead_coeff (pp (set sturm_seq) Polynomial.lead_coeff lc) \<and> pp (set sturm_seq) Polynomial.lead_coeff lc \<in> set sturm_seq"
            using f3 by (meson imageE)
          then have "(Polynomial.lead_coeff (pp (set sturm_seq) Polynomial.lead_coeff lc), rr (pp (set sturm_seq) Polynomial.lead_coeff lc) assumps) \<in> set assumps \<and> rr (pp (set sturm_seq) Polynomial.lead_coeff lc) assumps \<noteq> 0"
            using f2 by (meson h1)
          then show ?thesis
            using f4 by auto
        qed
      }
      ultimately have "\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0"
        by blast
    }
    ultimately have "\<exists>r. (lc,r) \<in> set assumps \<and> r \<noteq> 0"
      by blast
  }
  ultimately show ?case by blast 
qed

lemma map_eq_2:
  assumes "\<forall>i < n.  f i = g i"
  shows "map (\<lambda>i. f i) [0..<n] =  map (\<lambda>i. g i) [0..<n]"
  by (simp add: assms)

lemma changes_eq:
  shows "changes q = changes (map real_of_int q)"
proof (induct "length q" arbitrary: q)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then have ind: "\<forall>q. x = length q \<longrightarrow> changes q = changes (map real_of_int q)" 
    by auto
  have  "Suc x = length q"
    using Suc.hyps(2) by blast 
  have x_zer: "x = 0 \<Longrightarrow>  changes q = changes (map real_of_int q)" 
  proof - 
    assume "x = 0"
    then have "\<exists>a. q = [a]"
      using Suc.hyps(2)
      by (metis length_Suc_conv nat.distinct(1) remdups_adj.cases) 
    then obtain a where a_prop: "q = [a]" by auto
    have "changes [a] = changes (map real_of_int [a])" by auto
    then show "changes q = changes (map real_of_int q)" 
      using a_prop by auto
  qed
  have x_nonz: "x \<noteq> 0 \<Longrightarrow>  changes q = changes (map real_of_int q)" 
  proof - 
    assume "x \<noteq> 0"
    then have "\<exists>a b c. q = a#b#c"
      using Suc.hyps(2)
      by (metis Suc_length_conv list_decode.cases) 
    then obtain a b c where abc_prop: "q = a#b#c" by auto
    have "changes (a#b#c) = changes (map real_of_int (a#b#c))"
      apply (auto)
      using Suc.hyps(1) Suc.hyps(2) abc_prop apply force
         apply (simp add: mult_less_0_iff)
        apply (simp add: Suc.hyps(1) Suc.hyps(2) Suc_inject abc_prop)
       apply (metis of_int_less_0_iff of_int_mult)
      by (simp add: Suc.hyps(1) Suc.hyps(2) Suc_inject abc_prop)
    then show "changes q = changes (map real_of_int q)" 
      using abc_prop by auto
  qed
  then show ?case using x_zer x_nonz by auto
qed

lemma eval_mpoly_commutes_helper:
  assumes val_sat: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  shows "i < length sturm_seq \<Longrightarrow> eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i)) = Polynomial.lead_coeff (eval_mpoly_poly val (sturm_seq ! i))"
proof -
  fix i
  assume i_lt: "i < length sturm_seq"
  have s1: "eval_mpoly val (map Polynomial.lead_coeff sturm_seq ! i) = eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i))"
    by (simp add: i_lt)
  have s2: "Polynomial.lead_coeff (map (eval_mpoly_poly val) sturm_seq ! i) = Polynomial.lead_coeff (eval_mpoly_poly val (sturm_seq ! i))"
    using i_lt by force 
  let ?ssi = "(sturm_seq ! i)"
  have " Polynomial.lead_coeff (sturm_seq ! i) \<in> set (lead_coeffs sturm_seq)"
    using i_lt by force 
  then have ex_s: "\<exists>s \<noteq> 0. (Polynomial.lead_coeff ?ssi, s) \<in> set assumps"
    using spmods_multiv_aux_sturm_lc
    by (metis (no_types, lifting) inset spmods_multiv_lc) 
  then have "eval_mpoly val (Polynomial.lead_coeff ?ssi) \<noteq> 0"
    using val_sat[of "Polynomial.lead_coeff (sturm_seq ! i)" "0"] 
    unfolding satisfies_evaluation_def
    using satisfies_evaluation_nonzero val_sat by blast
  then show "eval_mpoly val (Polynomial.lead_coeff ?ssi) = Polynomial.lead_coeff (eval_mpoly_poly val ?ssi)"
    by (metis ex_s degree_valuation eval_mpoly_map_poly_comm_ring_hom.base.coeff_map_poly_hom eval_mpoly_poly_def val_sat)
qed

(* Now show that they match up when called correctly *)
lemma changes_R_smods_multiv_connect_aux:
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes degree_list: "degree_list = degrees sturm_seq"
    (* Take the leading coefficients from each of the entries in the Sturm sequence,
    because what matters are the signs of the leading coefficients *)
  assumes signs_list: "signs_list \<in> mpoly_consistent_sign_vectors (lead_coeffs sturm_seq) (all_lists (length val))"
    (* Say there's a good valuation val *)
  assumes val_sat: "\<forall> p n. ((p,n) \<in> set assumps \<longrightarrow> satisfies_evaluation val p n)"
    (* val needs to satisfy the additional constraints of signs_list *)
  assumes key: "signs_list = map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq)" 
  shows "changes_R_smods_multiv signs_list degree_list = changes_R_smods_multiv_val sturm_seq val"
proof - 
  let ?eval_ss = "eval_mpoly_poly_list val sturm_seq"
  have "signs_list \<in> (map_mpoly_sign (lead_coeffs sturm_seq)) ` {(ls::real list). length ls = length val}"
    using signs_list unfolding mpoly_consistent_sign_vectors_def all_lists_def 
    by auto
  then have "\<exists>l \<in>{(ls::real list). length ls = length val}. signs_list  = map_mpoly_sign (lead_coeffs sturm_seq) l"
    by auto
  then obtain l::"real list" where l_prop: "length l = length val \<and> signs_list  = map_mpoly_sign (lead_coeffs sturm_seq) l"
    by auto
  then have l1: "length signs_list = length sturm_seq"
    unfolding map_mpoly_sign_def by auto
  have l2: "length degree_list = length sturm_seq" 
    using degree_list by auto
  have len_eq: "length degree_list = length signs_list \<and> length sturm_seq = length signs_list"
    using l1 l2 by auto
  have same_len: "length degree_list = length signs_list"
    using l1 l2 by auto
  have sminus: "sminus degree_list signs_list = changes_poly_neg_inf ?eval_ss"
  proof -
    have len_eq2: "length (eval_mpoly_poly_list val sturm_seq) = length degree_list"
      using l2 unfolding eval_mpoly_poly_list_def 
      by auto
    have dhelp:"\<And>i. i < length degree_list \<Longrightarrow> (sgn (signs_list ! i)) = sgn ((Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))::real)"
    proof - 
      fix i
      assume i_lt: "i < length degree_list "
      have "(signs_list ! i) = sign_rat (eval_mpoly val ((lead_coeffs sturm_seq) ! i)) "
        using signs_list
        using i_lt len_eq
        by (metis (no_types, lifting) key length_map nth_map)
      then have h1: "(sgn (signs_list ! i)) = sign_rat (eval_mpoly val ((lead_coeffs sturm_seq) ! i))"
        by (simp add: Sturm_Tarski.sign_def sign_rat_def)
      have helper1: "sign_rat (eval_mpoly val ((lead_coeffs sturm_seq) ! i)) = 
            sign_rat (eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i)))"
        using i_lt len_eq by auto
      have helper2: "sign_rat (Polynomial.lead_coeff (map (map_poly (eval_mpoly val)) sturm_seq ! i)) =
              sign_rat (Polynomial.lead_coeff (eval_mpoly_poly val (sturm_seq ! i)))"
        using i_lt eval_mpoly_poly_def eval_mpoly_poly_list_def len_eq2 by force
      have helper3: "sign_rat (eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i))) =  sign_rat (Polynomial.lead_coeff (eval_mpoly_poly val (sturm_seq ! i)))"
        using val_sat inset eval_mpoly_commutes_helper
        by (metis i_lt len_eq) 
      then have "sign_rat (eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i))) = sign_rat ((Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))::real)"
        unfolding eval_mpoly_poly_list_def eval_mpoly_poly_def
        by (simp add: helper2 helper3)
      then have "(of_rat \<circ> sign_rat) (eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i))) = sgn ((Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))::real)"
        using sgn_sign_eq
        by (simp add: Sturm_Tarski.sign_def sgn_real_def sign_rat_def) 
      then have "(of_rat \<circ> sign_rat) (eval_mpoly val ((lead_coeffs sturm_seq) ! i)) = sgn ((Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))::real)"
        by (simp add: helper1)       
      then show " (sgn (signs_list ! i)) = sgn ((Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))::real)"
        using h1 of_int_hom.hom_one of_int_minus sign_rat_def
        by (smt (z3) comp_eq_dest_lhs of_rat_0 of_rat_1 of_rat_neg_one of_real_0 of_real_1 of_real_minus sgn_if)
    qed
    have dhelp2: "\<And>i. i < length degree_list \<Longrightarrow> Polynomial.degree (eval_mpoly_poly_list val sturm_seq ! i) = Polynomial.degree (sturm_seq ! i)"
    proof - 
      fix i
      assume "i < length degree_list "
      then have i_lt: "i < length sturm_seq" using len_eq by auto
      then have s1: "eval_mpoly val (map Polynomial.lead_coeff sturm_seq ! i) = eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i))"
        by simp 
      have s2: "Polynomial.lead_coeff (map (eval_mpoly_poly val) sturm_seq ! i) = Polynomial.lead_coeff (eval_mpoly_poly val (sturm_seq ! i))"
        using i_lt by force 
      let ?ssi = "(sturm_seq ! i)"
      have " Polynomial.lead_coeff (sturm_seq ! i) \<in> set (lead_coeffs sturm_seq)"
        using i_lt by force 
      then have "\<exists>k\<noteq>0. (Polynomial.lead_coeff ?ssi, k) \<in> set assumps"
        using spmods_multiv_lc[of assumps sturm_seq p q acc "Polynomial.lead_coeff (sturm_seq ! i)"] inset
        by blast
      then  have "eval_mpoly val (Polynomial.lead_coeff ?ssi) \<noteq> 0"
        using val_sat unfolding satisfies_evaluation_def
        using satisfies_evaluation_nonzero val_sat by blast
      then show "Polynomial.degree (eval_mpoly_poly_list val sturm_seq ! i) = Polynomial.degree (sturm_seq ! i)"   
        unfolding eval_mpoly_poly_list_def eval_mpoly_poly_def
        by (metis (no_types, lifting) Ring_Hom_Poly.degree_map_poly i_lt degree_0 map_poly_0 nth_map)     
    qed
    have d1: "\<And>i. even (Polynomial.degree (eval_mpoly_poly_list val sturm_seq ! i)) \<Longrightarrow>
         i < length degree_list \<Longrightarrow>
          (sgn ((- 1) ^ degree_list ! i * signs_list ! i)) = sgn (Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))"
    proof - 
      fix i
      assume even: "even (Polynomial.degree (eval_mpoly_poly_list val sturm_seq ! i))"
      assume i_lt_deg: "i < length degree_list"
      have ev: "even (degree_list ! i)"
        using dhelp2 even degree_list
        using i_lt_deg by auto 
      then show "(sgn ((- 1) ^ degree_list ! i * signs_list ! i)) = sgn (Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))"
        using dhelp ev i_lt_deg
        by simp 
    qed
    have d2: "\<And>i. odd (Polynomial.degree (eval_mpoly_poly_list val sturm_seq ! i)) \<Longrightarrow>
         i < length degree_list \<Longrightarrow>
          of_rat (sgn ((- 1) ^ degree_list ! i * signs_list ! i)) = - sgn (Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))"
    proof - 
      fix i
      assume odd: "odd (Polynomial.degree (eval_mpoly_poly_list val sturm_seq ! i))"
      assume i_lt_deg: "i < length degree_list"
      have odd1: "odd (degree_list ! i)"
        using dhelp2 odd degree_list
        using i_lt_deg by auto 
      then have " (sgn ((- 1) ^ degree_list ! i * signs_list ! i)) = - sgn (Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))"
        using dhelp odd
        by (simp add: i_lt_deg of_rat_hom.hom_uminus) 
      then show "real_of_rat (sgn ((- 1) ^ degree_list ! i * signs_list ! i)) =
         - sgn (Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i))"
        by (smt (verit, ccfv_SIG) of_rat_0 of_rat_1 of_rat_neg_one of_real_0 of_real_1 of_real_eq_iff of_real_minus sgn_rat_def)
    qed
    have "\<forall>i < length degree_list. (of_rat ((sgn ( (- 1) ^ degree_list ! i * signs_list ! i))) =
     sgn (if even (Polynomial.degree ((eval_mpoly_poly_list val sturm_seq)!i)) then sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)) else - sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i))))"
      using d1 d2
      by (smt (verit) minus_of_real_eq_of_real_iff of_rat_0 of_rat_1 of_rat_hom.eq_iff of_real_0 of_real_1 real_of_rat_sgn sgn_real_def)
    then have "map of_rat (map (\<lambda>i. (sgn ( (- 1) ^ degree_list ! i * signs_list ! i))) [0..<length degree_list]) =
     map 
      (\<lambda>i. sgn (if even (Polynomial.degree ((eval_mpoly_poly_list val sturm_seq)!i)) then sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)) else - sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i))))
       [0..< length degree_list]"
      using map_eq_2 add.left_neutral length_map map_upt nth_map nth_upt of_int_minus
      by auto
    then have "map of_rat (map sgn ((map (\<lambda>i. ((- 1) ^ degree_list ! i * signs_list ! i)) [0..<length degree_list]))) =
     (map sgn 
    (map (\<lambda>i. if even (Polynomial.degree ((eval_mpoly_poly_list val sturm_seq)!i)) 
        then sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)) else 
            - sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)))
       [0..< length degree_list])::real list)"
      by auto
    then have h1:"map of_rat (map sgn ((map (\<lambda>i. ((- 1) ^ degree_list ! i * signs_list ! i)) [0..<length degree_list]))) =
     map sgn 
    (map (\<lambda>i. if even (Polynomial.degree ((eval_mpoly_poly_list val sturm_seq)!i)) 
        then sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)) else 
            - sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)))
       [0..< length (eval_mpoly_poly_list val sturm_seq)])"
      using len_eq2
      by presburger      
    have h2: "(map (\<lambda>i. if even (Polynomial.degree ((eval_mpoly_poly_list val sturm_seq)!i)) 
        then sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)) else 
            - sgn (Polynomial.lead_coeff ((eval_mpoly_poly_list val sturm_seq)!i)))
       [0..< length (eval_mpoly_poly_list val sturm_seq)]) = 
      (map (\<lambda>p. if even (Polynomial.degree p) 
        then sgn (Polynomial.lead_coeff p) else 
            - sgn (Polynomial.lead_coeff p))
       (eval_mpoly_poly_list val sturm_seq))"
      using map_upt by fastforce
    let ?m1 = " ((map (\<lambda>i. ((- 1) ^ degree_list ! i * signs_list ! i)) [0..<length degree_list]))"
    let ?m2 = "((map (\<lambda>p. if even (Polynomial.degree p) then sgn (Polynomial.lead_coeff p) else - sgn (Polynomial.lead_coeff p))
       (eval_mpoly_poly_list val sturm_seq)))::real list"
    have "map of_rat ((map sgn ?m1)::rat list) = ((map sgn ?m2)::real list)"
      unfolding changes_poly_neg_inf_def sgn_neg_inf_def
      using h1 h2
      by presburger 
    then have c1: "changes ((map of_rat(map sgn ?m1))::real list) = changes ((map sgn ?m2)::real list)"
      using arg_cong  
      by auto
        (* using arg_cong[of "(map sgn ?m1)" "(map sgn ?m2)" "changes"] by auto*)
    have c2: "changes (map sgn ?m1) = changes ?m1"
      using changes_map_sgn_eq[of ?m1] changes_eq 
      by auto
    have c3: "changes (map sgn ?m2::real list) = changes ?m2"
      using changes_map_sgn_eq[of ?m2] changes_eq 
      by auto
    have c0: "changes (map (real_of_rat \<circ> sgn) ?m1) = changes (map sgn ?m1)"
      using changes_cast_sgn_same_map
      by (metis list.map_comp)  
    then have "changes ?m1  = changes ?m2"
      using c1 c2 c3 cast_sgn_same_map list.map_comp
      by metis
    then have "changes (map (\<lambda>i. (-1)^(nth degree_list i)*(nth signs_list i)) [0..< length degree_list]) = 
             changes_poly_neg_inf (eval_mpoly_poly_list val sturm_seq)"
      unfolding changes_poly_neg_inf_def sgn_neg_inf_def 
      using changes_map_sgn_eq
      by force 
    then show "sminus degree_list signs_list = changes_poly_neg_inf (eval_mpoly_poly_list val sturm_seq)"
      by auto
  qed
  have splus: "changes signs_list = changes_poly_pos_inf ?eval_ss"
  proof - 
    (* Linking l and val *)
    (* Know val is a consistent valuation with all of the assumptions, and know that 
    sturm_seq was generated with those assumptions, know signs_list is a consistent 
    sign_rat assignment for the LC's of the sturm sequence
    *)
    have eq1: " map_mpoly_sign (lead_coeffs sturm_seq) l = 
      map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq)"
      using l_prop key 
      by auto
    have "\<forall>i < length sturm_seq. ((sign_rat (eval_mpoly val (nth (lead_coeffs sturm_seq) i))) =
     sign_rat (sgn_pos_inf (nth (eval_mpoly_poly_list val sturm_seq) i)))"
    proof clarsimp 
      fix i
      assume "i < length sturm_seq"
      have s1: "eval_mpoly val (map Polynomial.lead_coeff sturm_seq ! i) = eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i))"
        by (simp add: \<open>i < length sturm_seq\<close>)
      have s2: "Polynomial.lead_coeff (map (eval_mpoly_poly val) sturm_seq ! i) = Polynomial.lead_coeff (eval_mpoly_poly val (sturm_seq ! i))"
        using \<open>i < length sturm_seq\<close> by force 
      let ?ssi = "(sturm_seq ! i)"
      have s3: "eval_mpoly val (Polynomial.lead_coeff ?ssi) = Polynomial.lead_coeff (eval_mpoly_poly val ?ssi)"
        using eval_mpoly_commutes_helper[of assumps val sturm_seq] inset val_sat
        using \<open>i < length sturm_seq\<close> by blast 
      have " sign_rat (eval_mpoly val (map Polynomial.lead_coeff sturm_seq ! i)) = sign_rat (sgn (Polynomial.lead_coeff (eval_mpoly_poly_list val sturm_seq ! i)))"
        using s1 s2 s3 
        using eval_mpoly_poly_list_def
        by (simp add: sign_rat_def)
      then show "sign_rat (eval_mpoly val (Polynomial.lead_coeff (sturm_seq ! i))) = sign_rat (sgn_pos_inf (eval_mpoly_poly_list val sturm_seq ! i))"
        unfolding sgn_pos_inf_def
        by (simp add: s1)
    qed
    then have eq2: " map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq) = 
    (map (sign_rat \<circ> sgn_pos_inf) (eval_mpoly_poly_list val sturm_seq))"
      by (smt (verit, ccfv_threshold) comp_eq_dest_lhs eval_mpoly_poly_def eval_mpoly_poly_list_def key l2 length_map list.map_comp nth_map nth_map_conv same_len)
    have "map_mpoly_sign (lead_coeffs sturm_seq) l =
     (map (sign_rat \<circ> sgn_pos_inf) (eval_mpoly_poly_list val sturm_seq))" 
      using eq1 eq2 by auto
    then have "changes
     (map (Sturm_Tarski.sign \<circ>
           eval_mpoly l)
       (lead_coeffs sturm_seq)) =
    changes
     (map (\<lambda>p. sgn (Polynomial.lead_coeff p))
       (eval_mpoly_poly_list val sturm_seq))"
      unfolding changes_poly_pos_inf_def sign_rat_def map_mpoly_sign_def  
        sgn_pos_inf_def
      using changes_map_sign_of_int_eq list.map_comp
      by (metis (no_types, lifting) changes_map_sign_eq comp_apply nth_map_conv)
    then have "changes (map_mpoly_sign (lead_coeffs sturm_seq) l) = 
  changes_poly_pos_inf (eval_mpoly_poly_list val sturm_seq)"
      by (metis (no_types, lifting) changes_map_sign_eq changes_map_sign_of_int_eq changes_poly_pos_inf_def list.map_comp map_eq_conv map_mpoly_sign_def sgn_pos_inf_def)
    then  show ?thesis  using l_prop unfolding map_mpoly_sign_def by auto
  qed
  show ?thesis using sminus splus unfolding changes_R_smods_multiv_def changes_R_smods_multiv_val_def
    by (metis)
qed

(* This is changes_R_smods_multiv_connect_aux, but with the signs_list assumption removed *)
lemma changes_R_smods_multiv_connect:
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes degree_list: "degree_list = degrees sturm_seq"
    (* say there's a good valuation val *)
  assumes val_sat: "\<forall> p n. ((p,n) \<in> set assumps \<longrightarrow> satisfies_evaluation val p n)"
    (* val needs to satisfy the additional constraints of signs_list. *)
  assumes key: "signs_list = map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq)" 
  shows "changes_R_smods_multiv signs_list degree_list = changes_R_smods_multiv_val sturm_seq val"
proof - 
  have l1: "length signs_list = length sturm_seq"
    using key by auto
  then have "((map ((\<lambda>x. sign_rat (eval_mpoly val x)) \<circ> Polynomial.lead_coeff) sturm_seq)::rat list)
    \<in> (((\<lambda>x. map (sign_rat \<circ> eval_mpoly x \<circ> Polynomial.lead_coeff) sturm_seq) `
       {ls. length ls = length val})::rat list set)"
    by auto 
  then have "signs_list \<in> mpoly_consistent_sign_vectors (lead_coeffs sturm_seq) (all_lists (length val))"
    using key
    unfolding mpoly_consistent_sign_vectors_def map_mpoly_sign_def
    by (smt (verit) all_lists_def comp_apply image_eqI map_eq_conv mem_Collect_eq sign_rat_def)
  then show ?thesis using assms changes_R_smods_multiv_connect_aux
    by auto 
qed 

(* Later stated with changes_R_smods_multiv instead of changes_R_smods_multiv_val *)
lemma changes_R_smods_multiv_val_univariate:
  assumes "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "changes_R_smods_multiv_val sturm_seq val = changes_R_smods (eval_mpoly_poly val p) (eval_mpoly_poly val q)"
  using matches_ss unfolding changes_R_smods_def changes_R_smods_multiv_val_def
  using assms changes_poly_neg_inf_def changes_poly_pos_inf_def eval_mpoly_poly_list_def spmods_smods_sgn_map_eq(2) spmods_smods_sgn_map_eq(3)
    spmods_multiv_sound
  by metis

lemma changes_R_smods_multiv_signs_list_connect:
  assumes len_same: "length signs_list = length degree_list"
  assumes key: "((map sign_rat signs_list)::rat list) = (signs_list_var::rat list)"
  shows "changes_R_smods_multiv signs_list degree_list = changes_R_smods_multiv signs_list_var degree_list" 
proof - 
  have changes_same: "changes signs_list = changes signs_list_var"
    using key
    using changes_map_sign_of_int_eq  map_eq_conv 
    unfolding sign_rat_def
    by (metis (mono_tags, lifting) comp_apply)
  let ?ell1 = "(map (\<lambda>i. (-1)^(nth degree_list i)*(nth signs_list i)) [0..< length degree_list])"
  let ?ell2 = "(map (\<lambda>i. (-1)^(nth degree_list i)*(nth signs_list_var i)) [0..< length degree_list])"
  have "\<And>x. x < length degree_list \<Longrightarrow>
         sgn ((- 1) ^ degree_list ! x * signs_list ! x) = sgn ((- 1) ^ degree_list ! x * map sign_rat signs_list ! x)"
  proof -
    fix x
    assume "x < length degree_list"
    have h1: " sgn ((- 1) ^ degree_list ! x * signs_list ! x) =  sgn ((- 1) ^ degree_list ! x) * sgn (signs_list ! x)"
      using sgn_mult by blast
    have h2: "sgn ((- 1) ^ degree_list ! x * map sign_rat signs_list ! x) = sgn ((- 1) ^ degree_list ! x) * sgn (map sign_rat signs_list ! x)"
      using sgn_mult 
      by blast
    have h3: "sgn (map sign_rat signs_list ! x) =  sgn (signs_list ! x)"
      using key unfolding sign_rat_def
      using \<open>x < length degree_list\<close> len_same sgn_rat_def by fastforce
    show "sgn ((- 1) ^ degree_list ! x * signs_list ! x) = sgn ((- 1) ^ degree_list ! x * map sign_rat signs_list ! x)"
      using h1 h2 h3 
      by metis 
  qed
  then have "map sgn ?ell1 = map sgn ?ell2"
    using key
    by auto
  then have "changes ?ell1 = changes ?ell2"
    using changes_map_sgn_eq
    by (metis (no_types, lifting))
  then show ?thesis
    using changes_R_smods_multiv_def changes_same sminus.simps by presburger 
qed

lemma changes_R_smods_multiv_univariate:
  assumes "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes degree_list: "degree_list = degrees sturm_seq"
    (* say there's a good valuation val *)
  assumes val_sat: "\<forall> p n. ((p,n) \<in> set assumps \<longrightarrow> satisfies_evaluation val p n)"
    (* val needs to satisfy the additional constraints of signs_list. *)
  assumes key: "map (sign_rat::rat\<Rightarrow>rat) signs_list = map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq)" 
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "changes_R_smods_multiv signs_list degree_list = changes_R_smods (eval_mpoly_poly val p) (eval_mpoly_poly val q)"
proof -
  have same_len: "length signs_list = length degree_list"
    using degree_list key
    by (metis length_map) 
  from changes_R_smods_multiv_signs_list_connect[OF same_len key]
  have h2: "
    changes_R_smods_multiv signs_list degree_list =
    changes_R_smods_multiv ((map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq))) degree_list"
    by auto
  have h1: "changes_R_smods_multiv (map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq)) degree_list = changes_R_smods (eval_mpoly_poly val p) (eval_mpoly_poly val q)"
    using changes_R_smods_multiv_connect changes_R_smods_multiv_val_univariate assms by auto
  then show ?thesis using h1 h2 by auto 
qed

theorem pderiv_commutes:
  fixes p:: "real mpoly Polynomial.poly"
  fixes val:: "real list"
  shows "pderiv (eval_mpoly_poly val p) = (eval_mpoly_poly val (pderiv p))"
  by (simp add: eval_mpoly_map_poly_idom_hom.base.map_poly_pderiv eval_mpoly_poly_def)

theorem sturm_R_multiv_comm:
  shows "card {x. Polynomial.poly (eval_mpoly_poly val p) x=0} = changes_R_smods (eval_mpoly_poly val p) ((eval_mpoly_poly val (pderiv p)))" 
  using pderiv_commutes  Sturm_Tarski.sturm_R
  by auto

theorem sturm_R_multiv2:
  assumes "q = pderiv p"
  assumes "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "card {x. Polynomial.poly (eval_mpoly_poly val p) x=0} = changes_R_smods_multiv_val sturm_seq val" 
  using changes_R_smods_multiv_val_univariate Sturm_Tarski.sturm_R sturm_R_multiv_comm
  using assms(1) assms(2) assms(3)
  by force

(* proof shares overlap with univariate restate_tarski2 proof*)
theorem restate_tarski_multiv:
  fixes p:: "real mpoly Polynomial.poly"
  fixes q:: "real mpoly Polynomial.poly"
  assumes "(eval_mpoly_poly val p) \<noteq> 0"
  assumes "(assumps, sturm_seq) \<in> set (spmods_multiv p ((pderiv p)*q) acc)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "changes_R_smods_multiv_val sturm_seq val = 
    int (card {x. Polynomial.poly (eval_mpoly_poly val p) x=0 \<and> Polynomial.poly (eval_mpoly_poly val q) x>0})
    - int(card {x. Polynomial.poly (eval_mpoly_poly val p) x=0 \<and> Polynomial.poly (eval_mpoly_poly val q) x<0})" 
proof - 
  have 0: "changes_R_smods_multiv_val sturm_seq val = changes_R_smods (eval_mpoly_poly val p) (eval_mpoly_poly val ((pderiv p)*q))"
    using changes_R_smods_multiv_val_univariate assms
    by blast 
  let ?p = "(eval_mpoly_poly val p)::real Polynomial.poly"
  let ?q = "(eval_mpoly_poly val q)::real Polynomial.poly"
  have h1: "taq {x. poly ?p x=0} ?q = changes_R_smods ?p (pderiv ?p * ?q)"
    using sturm_tarski_R[symmetric] by auto
  have pd_comm: "pderiv (eval_mpoly_poly val p) * eval_mpoly_poly val q = eval_mpoly_poly val (pderiv p * q)"
    using eval_mpoly_poly_comm_ring_hom.hom_mult pderiv_commutes by auto
  let ?all = "{x. Polynomial.poly ?p x=0}"
  let ?lt = "{x. Polynomial.poly ?p x=0 \<and> Polynomial.poly ?q x < 0}"
  let ?gt = "{x. Polynomial.poly ?p x=0 \<and> Polynomial.poly ?q x > 0}"
  let ?eq = "{x. Polynomial.poly ?p x=0 \<and> Polynomial.poly ?q x = 0}"
  have cardlt: "(\<Sum>x | poly (eval_mpoly_poly val p) x = 0 \<and>
           poly (eval_mpoly_poly val q) x < 0.
       if 0 < poly (eval_mpoly_poly val q) x then 1
       else if poly (eval_mpoly_poly val q) x = 0 then 0
            else - 1) = -int (card ?lt)"
    by auto
  have cardgt: "(\<Sum>x | poly (eval_mpoly_poly val p) x = 0 \<and>
           0 < poly (eval_mpoly_poly val q) x.
       if 0 < poly (eval_mpoly_poly val q) x then 1
       else if poly (eval_mpoly_poly val q) x = 0 then 0
            else - 1) = int (card ?gt)"
    by auto
  have empty: "{x. poly (eval_mpoly_poly val p) x = 0 \<and>
              poly (eval_mpoly_poly val q) x < 0} \<inter>
          {x. poly (eval_mpoly_poly val p) x = 0 \<and>
              0 < poly (eval_mpoly_poly val q) x} = {}"
    by auto
  then have cardzer: "(\<Sum>x\<in>{x. poly (eval_mpoly_poly val p) x = 0 \<and>
              poly (eval_mpoly_poly val q) x < 0} \<inter>
          {x. poly (eval_mpoly_poly val p) x = 0 \<and>
              0 < poly (eval_mpoly_poly val q) x}.
       if 0 < poly (eval_mpoly_poly val q) x then 1
       else if poly (eval_mpoly_poly val q) x = 0 then 0
            else - 1) = 0" by auto
  have eq: "?all = ?lt \<union> ?gt \<union> ?eq" by force
  from poly_roots_finite[OF assms(1)] have fin: "finite ?all" .
  have  "(\<Sum>x | poly ?p x = 0. Sturm_Tarski.sign (poly ?q x)) = int (card ?gt) - int (card ?lt)"
    unfolding eq Sturm_Tarski.sign_def 
    apply (subst sum_Un)
    apply (auto simp add:fin) 
    apply (subst sum_Un) 
    apply (simp add: fin)
    apply (simp add: fin)  
    using cardzer cardlt cardgt empty 
    by auto
  then have "changes_R_smods (eval_mpoly_poly val p) (eval_mpoly_poly val ((pderiv p)*q)) = int (card ?gt) - int (card ?lt)"
    using h1 taq_def pd_comm
    by metis
  then have "changes_R_smods_multiv_val sturm_seq val = int (card ?gt) - int (card ?lt)"
    using 0 by auto 
  then show ?thesis
    by presburger 
qed

lemma sminus_map_sign:
  assumes same_len: "length signs_list = length degree_list"
  shows "sminus degree_list signs_list =
    sminus degree_list (map sign_rat signs_list) "
proof - 
  let ?xs = "(map (\<lambda>i. (- 1) ^ degree_list ! i * signs_list ! i) [0..<length degree_list])"
  have changes_same: "changes ?xs = changes (map sign_rat ?xs)"
    using changes_map_sign_eq[of ?xs]
    unfolding sign_rat_def
    by (smt (verit, best) Sturm_Tarski.sign_def changes_map_sign_of_int_eq map_eq_conv o_apply) 
  have "(map (\<lambda>i. (-1)^(nth degree_list i)*(nth (map sign_rat signs_list) i)) [0..< length degree_list])
 = (map sign_rat ?xs)"
  proof clarsimp 
    fix x
    assume "x < length degree_list" 
    then have "x < length signs_list" 
      using same_len  
      by auto
    then have p2: "map sign_rat signs_list ! x  = 
        sign_rat (signs_list ! x)"
      using nth_map by blast
    have p1: "(- 1) ^ degree_list ! x = (1::int) \<or> (- 1) ^ degree_list ! x = (-1::int)"
      using neg_one_even_power neg_one_odd_power by blast
    show "(- 1) ^ degree_list ! x * map sign_rat signs_list ! x =
      (sign_rat ((- 1) ^ degree_list ! x * signs_list ! x))"
      using p1 p2
      by (metis (no_types, opaque_lifting) mult_1 mult_minus_left neg_one_even_power neg_one_odd_power of_int_minus sign_rat_def sign_uminus)
  qed
  then have " changes (map sign_rat ?xs)
= changes (map (\<lambda>i. (-1)^(nth degree_list i)*(nth (map sign_rat signs_list) i)) [0..< length degree_list])"
    unfolding sign_rat_def
    by presburger 
  then have "changes (map (\<lambda>i. (-1)^(nth degree_list i)*(nth signs_list i)) [0..< length degree_list])
    = changes (map (\<lambda>i. (-1)^(nth degree_list i)*(nth (map sign_rat signs_list) i)) [0..< length degree_list])"
    using changes_same
    by (metis (no_types, lifting)) 
  then show ?thesis by auto 
qed

lemma changes_R_smods_multiv_map_sign:
  assumes "length signs_list = length degree_list"
  shows "changes_R_smods_multiv signs_list degree_list =
  changes_R_smods_multiv (map sign_rat signs_list) degree_list "
  using assms sminus_map_sign
  unfolding changes_R_smods_multiv_def
  using changes_R_smods_multiv_def changes_R_smods_multiv_signs_list_connect by presburger 

lemma construct_NofI_single_M_univariate_superset:
  assumes new_p: "new_p = sum_list (map (\<lambda>x. x^2) (p # I1))"
  assumes new_q: "new_q = ((pderiv new_p)*(prod_list I2))"
  assumes seq_in: "(assumps, sturm_seq) \<in> set (spmods_multiv new_p new_q acc)"
  assumes superset: "set assumps \<subseteq> set assumps_superset"
  assumes good_val: "\<And>p n. (p,n) \<in> set assumps_superset \<Longrightarrow> satisfies_evaluation val p n"
  shows "construct_NofI_single_M (assumps_superset, sturm_seq) = 
    (assumps_superset, construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val I1) (eval_mpoly_poly_list val I2))"
proof - 
  let ?other_p = "sum_list (map power2 (eval_mpoly_poly val p # eval_mpoly_poly_list val I1))"
  have "eval_mpoly_poly val (sum_list (map power2 I1)) = sum_list (map power2 (eval_mpoly_poly_list val I1)) "
  proof (induct I1)
    case Nil
    then show ?case
      by (simp add: eval_mpoly_poly_list_def) 
  next
    case (Cons a I1)
    then show ?case
      by (simp add: eval_mpoly_poly_comm_ring_hom.hom_add eval_mpoly_poly_comm_ring_hom.hom_power eval_mpoly_poly_list_def) 
  qed
  then have eval1: "?other_p = eval_mpoly_poly val new_p"
    using new_p eval_mpoly_poly_comm_ring_hom.hom_add eval_mpoly_poly_comm_ring_hom.hom_power
    by auto
  then have eval2: "(pderiv ?other_p * prod_list (eval_mpoly_poly_list val I2)) = eval_mpoly_poly val new_q"
    using new_q eval_mpoly_poly_comm_ring_hom.hom_mult
    by (simp add: eval_mpoly_poly_list_def pderiv_commutes) 
  let ?new_signs = "(map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff) sturm_seq)"
    (* Intuitively, works because the leading coeffs of the sturm_sequence will be in assumps,
     and because val is good *)
  have lookup_some: "\<And>ss_poly.
       ss_poly \<in> set sturm_seq \<Longrightarrow> \<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
  proof -
    fix ss_poly
    assume "ss_poly \<in> set sturm_seq"
    then show "\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      using seq_in spmods_multiv_sturm_lc[of assumps sturm_seq new_p new_q acc ss_poly]
        inset_means_lookup_assump_some
      by metis
  qed
  have "\<And>ss_poly. ss_poly \<in> set sturm_seq \<Longrightarrow> 
      (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i \<and> 
         sign_rat i = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly)))"
  proof - 
    fix ss_poly
    assume "ss_poly \<in> set sturm_seq "
    then have " \<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      using lookup_some by auto
    then obtain i where i_prop: "lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      by auto
    then have "((Polynomial.lead_coeff ss_poly), i) \<in> set assumps"
      using lookup_assump_means_inset[of "(Polynomial.lead_coeff ss_poly)" assumps]
      by (simp add: lookup_assum_aux_mem)  
    then have "(sign_rat (i)) = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly))"
      using good_val[of "(Polynomial.lead_coeff ss_poly)" i] unfolding satisfies_evaluation_def
      by (metis of_int_hom.injectivity sign_rat_def subsetD superset)
    then show "(\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i \<and> 
         sign_rat i = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly)))"
      using i_prop by auto
  qed
  then have help1: "\<And>ss_poly. ss_poly \<in> set sturm_seq \<Longrightarrow> 
      (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset = Some i)"
    using superset sign_rat_def good_val in_set_member inset_means_lookup_assump_some lookup_assum_aux_mem satisfies_evaluation_def subset_code(1)
    by (smt (verit, ccfv_SIG))
  then have help2: "\<And>ss_poly. \<And> i. (ss_poly \<in> set sturm_seq \<and> lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset = Some i) \<Longrightarrow> sign_rat i = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly))"
  proof - 
    fix ss_poly
    fix i
    assume "(ss_poly \<in> set sturm_seq \<and> lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset = Some i)"
    then show "sign_rat i = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly))"
      using superset sign_rat_def good_val lookup_assum_aux_mem satisfies_evaluation_def
      by (metis of_int_hom.eq_iff)
  qed
  then have all_ex_i: "\<And>ss_poly. ss_poly \<in> set sturm_seq \<Longrightarrow> 
      (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset = Some i \<and> 
        sign_rat i = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly)))"
    using help1 help2
    by blast 
  then have helper: "(map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) = map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq)"
    by force
  then have rel1: "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) = changes_R_smods_multiv_val sturm_seq val"
    using helper changes_R_smods_multiv_connect[of assumps sturm_seq new_p new_q acc "degrees sturm_seq" val ?new_signs]
    using assms
    by (simp add: changes_R_smods_multiv_connect subset_code(1)) 
  have rel2: "changes_R_smods_multiv_val sturm_seq val =
    changes_R_smods (eval_mpoly_poly val new_p) (eval_mpoly_poly val new_q)"
    using assms changes_R_smods_multiv_val_univariate[of assumps sturm_seq new_p new_q acc val]
      eval1 eval2
    by blast
  have c1: "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) =
    (changes_R_smods ?other_p (pderiv ?other_p * prod_list (eval_mpoly_poly_list val I2)))"
    using rel1 rel2
    using eval1 eval2
    by presburger
  have "\<And>ss_poly. ss_poly \<in> set sturm_seq \<Longrightarrow> 
  (case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) =
    sign_rat (case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> i)"
  proof -
    fix ss_poly
    assume "ss_poly \<in> set sturm_seq"
    then have " \<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset = Some i"
      using lookup_some superset
      using all_ex_i by blast
    then obtain i where i_prop: "lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset = Some i"
      by auto
    then have eq1: "(case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i)  = sign_rat i"
      by auto 
    have eq2: "sign_rat (case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) = sign_rat i"
      using i_prop by auto 
    then show "(case lookup_assump_aux (Polynomial.lead_coeff ss_poly)
              assumps_superset of
        None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) =
       sign_rat
        (case lookup_assump_aux (Polynomial.lead_coeff ss_poly)
               assumps_superset of
         None \<Rightarrow> 1000 | Some i \<Rightarrow> i)"
      using eq1 eq2
      by fastforce 
  qed
  then have "(map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) 
    =  (map sign_rat (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) )"
    by auto
  then have "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq))
    = (changes_R_smods_multiv
       (map sign_rat (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) )
       (degrees sturm_seq))"
    by (smt (verit, ccfv_threshold))
  then have "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) =
    (changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq))"
    using  changes_R_smods_multiv_map_sign
    by (metis (no_types, lifting) length_map)
  then have c2: "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps_superset of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) =
    (changes_R_smods ?other_p (pderiv ?other_p * prod_list (eval_mpoly_poly_list val I2)))"
    using c1
    by presburger
  show ?thesis using c2 
    unfolding construct_NofI_R_def  
    apply (simp) unfolding construct_NofI_R_def
    by (metis)
qed

(* This requires showing that construct_NofI_M is unique given these input assumptions
Intuitively works because assumps contains all lookup info for lead coefficients of sturm_seq
*)
lemma construct_NofI_single_M_univariate:
  assumes new_p: "new_p = sum_list (map (\<lambda>x. x^2) (p # I1))"
  assumes new_q: "new_q = ((pderiv new_p)*(prod_list I2))"
  assumes seq_in: "(assumps, sturm_seq) \<in> set (spmods_multiv new_p new_q acc)"
  assumes good_val: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "construct_NofI_single_M (assumps, sturm_seq) = 
    (assumps, construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val I1) (eval_mpoly_poly_list val I2))"
proof - 
  let ?other_p = "sum_list (map power2 (eval_mpoly_poly val p # eval_mpoly_poly_list val I1))"
  have "eval_mpoly_poly val (sum_list (map power2 I1)) = sum_list (map power2 (eval_mpoly_poly_list val I1)) "
  proof (induct I1)
    case Nil
    then show ?case
      by (simp add: eval_mpoly_poly_list_def) 
  next
    case (Cons a I1)
    then show ?case
      by (simp add: eval_mpoly_poly_comm_ring_hom.hom_add eval_mpoly_poly_comm_ring_hom.hom_power eval_mpoly_poly_list_def) 
  qed
  then have eval1: "?other_p = eval_mpoly_poly val new_p"
    using new_p eval_mpoly_poly_comm_ring_hom.hom_add eval_mpoly_poly_comm_ring_hom.hom_power
    by auto
  then have eval2: "(pderiv ?other_p * prod_list (eval_mpoly_poly_list val I2)) = eval_mpoly_poly val new_q"
    using new_q eval_mpoly_poly_comm_ring_hom.hom_mult
    by (simp add: eval_mpoly_poly_list_def pderiv_commutes) 
  let ?new_signs = "(map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff) sturm_seq)"
    (* Intuitively works as the leading coeffs of the sturm_sequence will be in assumps,
     and because val is good *)
  have lookup_some: "\<And>ss_poly.
       ss_poly \<in> set sturm_seq \<Longrightarrow> \<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
  proof -
    fix ss_poly
    assume "ss_poly \<in> set sturm_seq"
    then show "\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      using seq_in spmods_multiv_sturm_lc[of assumps sturm_seq new_p new_q acc ss_poly]
        inset_means_lookup_assump_some
      by metis
  qed
  have "\<And>ss_poly. ss_poly \<in> set sturm_seq \<Longrightarrow> 
      (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i \<and> 
         sign_rat i = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly)))"
  proof - 
    fix ss_poly
    assume "ss_poly \<in> set sturm_seq "
    then have " \<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      using lookup_some by auto
    then obtain i where i_prop: "lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      by auto
    then have "((Polynomial.lead_coeff ss_poly), i) \<in> set assumps"
      using lookup_assump_means_inset[of "(Polynomial.lead_coeff ss_poly)" assumps]
      by (simp add: lookup_assum_aux_mem)  
    then have "(sign_rat (i)) = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly))"
      using good_val[of "(Polynomial.lead_coeff ss_poly)" i] unfolding satisfies_evaluation_def
      by (metis of_int_hom.injectivity sign_rat_def)
    then show "(\<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i \<and> 
         sign_rat i = sign_rat (eval_mpoly val (Polynomial.lead_coeff ss_poly)))"
      using i_prop by auto
  qed
  then have "(map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) = map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs sturm_seq)"
    by force
  then have rel1: "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) = changes_R_smods_multiv_val sturm_seq val"
    using changes_R_smods_multiv_connect[of assumps sturm_seq new_p new_q acc "degrees sturm_seq" val ?new_signs]
    using assms(3) assms(4)
    using changes_R_smods_multiv_connect by blast 
  have rel2: "changes_R_smods_multiv_val sturm_seq val =
    changes_R_smods (eval_mpoly_poly val new_p) (eval_mpoly_poly val new_q)"
    using assms changes_R_smods_multiv_val_univariate[of assumps sturm_seq new_p new_q acc val]
      eval1 eval2
    by blast
  have c1: "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) =
    (changes_R_smods ?other_p (pderiv ?other_p * prod_list (eval_mpoly_poly_list val I2)))"
    using rel1 rel2
    using eval1 eval2
    by presburger
  have "\<And>ss_poly. ss_poly \<in> set sturm_seq \<Longrightarrow> 
  (case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) =
    sign_rat (case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i)"
  proof -
    fix ss_poly
    assume "ss_poly \<in> set sturm_seq"
    then have " \<exists>i. lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      using lookup_some by auto
    then obtain i where i_prop: "lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps = Some i"
      by auto
    then have eq1: "(case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i)  = sign_rat i"
      by auto 
    have eq2: "sign_rat (case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) = sign_rat i"
      using i_prop by auto 
    then show "(case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) =
    sign_rat (case lookup_assump_aux (Polynomial.lead_coeff ss_poly) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i)"
      using eq1 eq2
      by metis 
  qed
  then have "(map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) 
=  (map sign_rat (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) )"
    by auto
  then have changes_1: "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq))
= (changes_R_smods_multiv
       (map sign_rat (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq) )
       (degrees sturm_seq))"
    by (smt (verit, ccfv_threshold))
  then have changes2: "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> sign_rat i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) =
(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq))"
    using  changes_R_smods_multiv_map_sign
    by (metis (no_types, lifting) length_map)
  then have "(changes_R_smods_multiv
       (map ((\<lambda>lc. case lookup_assump_aux lc assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) \<circ>
             Polynomial.lead_coeff)
         sturm_seq)
       (degrees sturm_seq)) =
    (changes_R_smods ?other_p (pderiv ?other_p * prod_list (eval_mpoly_poly_list val I2)))"
    using c1
    by presburger
  then show ?thesis
    unfolding construct_NofI_R_def using c1 changes2
    by (smt (verit, ccfv_SIG) construct_NofI_R_def construct_NofI_single_M_univariate_superset dual_order.refl good_val new_p new_q seq_in)
    (* apply (simp) unfolding construct_NofI_R_def
    using c1 changes2 by presburger *)
qed

lemma construct_NofI_M_univariate_tarski_query:
  assumes inset: "(assumps, tarski_query) \<in> set (construct_NofI_M p acc I1 I2)"
  assumes val: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "tarski_query = construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val I1) (eval_mpoly_poly_list val I2)"
proof - 
  let ?ell_map = "map construct_NofI_single_M (construct_NofI_R_spmods p acc I1 I2)"
  let ?ell = "construct_NofI_R_spmods p acc I1 I2"
  have same_len: "length ?ell = length ?ell_map"
    by auto
  have "(assumps, tarski_query) \<in> set (map construct_NofI_single_M (construct_NofI_R_spmods p acc I1 I2))"
    using inset
    by (metis construct_NofI_M.simps)
  then have "\<exists> n < length ?ell_map. ?ell_map ! n = (assumps, tarski_query)"
    by (metis construct_NofI_M.simps in_set_conv_nth inset length_map) 
  then obtain n where n_prop: "n <  length ?ell_map \<and> ?ell_map ! n = (assumps, tarski_query)"
    by auto
  then have "?ell_map ! n = construct_NofI_single_M (?ell ! n)"
    by force
  then have assumps_tq: "construct_NofI_single_M (?ell ! n) = (assumps, tarski_query)"
    using n_prop by auto
  obtain input_assumps ss where tuple_prop: "(input_assumps, ss) = ?ell ! n"
    using n_prop same_len
    by (metis old.prod.exhaust) 
  then have atq_is: "(assumps, tarski_query) = 
    (let lcs = lead_coeffs ss;
         sa_list = map (\<lambda>lc. lookup_assump lc input_assumps) lcs;
         degrees_list = degrees ss in
      (input_assumps, rat_of_int (changes_R_smods_multiv sa_list degrees_list)))"
    by (metis assumps_tq construct_NofI_single_M.simps)
  then have as_is: "assumps = input_assumps"
    by auto
  have in_spmods_multiv: "(assumps, ss) \<in> set ((let new_p = sum_list (map (\<lambda>x. x^2) (p # I1)) in
    spmods_multiv new_p ((pderiv new_p)*(prod_list I2))) acc)"
    using tuple_prop in_set_member
    using as_is construct_NofI_R_spmods_def n_prop by auto
  let ?multiv_p = "sum_list (map power2 (p # I1))"
  let ?multiv_q = "(pderiv ?multiv_p * prod_list I2)"
  let ?univ_p = "sum_list (map power2 (eval_mpoly_poly val p # eval_mpoly_poly_list val I1))"
  let ?univ_q = "(pderiv ?univ_p * prod_list (eval_mpoly_poly_list val I2))"
  let ?signs_list = "map (\<lambda>lc. lookup_assump lc assumps) (lead_coeffs ss)"
  have " map_poly (eval_mpoly val) (p\<^sup>2 + sum_list (map power2 I1)) =
    (map_poly (eval_mpoly val) p)\<^sup>2 + sum_list (map (power2 \<circ> map_poly (eval_mpoly val)) I1)"
    using eval_mpoly_map_poly_comm_ring_hom.hom_mult  eval_mpoly_map_poly_comm_ring_hom.hom_sum
  proof - 
    have h1: "map_poly (eval_mpoly val) (p\<^sup>2 + sum_list (map power2 I1)) = (map_poly (eval_mpoly val) p)\<^sup>2 + map_poly (eval_mpoly val) (sum_list (map power2 I1))"
      using eval_mpoly_map_poly_comm_ring_hom.hom_add eval_mpoly_map_poly_comm_ring_hom.hom_power by presburger 
    have "map_poly (eval_mpoly val) (sum_list (map power2 I1)) =
       (sum_list (map (map_poly (eval_mpoly val)\<circ>power2) I1))"
      using eval_mpoly_map_poly_comm_ring_hom.hom_add
      by (simp add: eval_mpoly_map_poly_comm_ring_hom.hom_sum_list) 
    then have h2: "map_poly (eval_mpoly val) (sum_list (map power2 I1)) = sum_list (map (power2 \<circ> map_poly (eval_mpoly val)) I1) "
      using  eval_mpoly_map_poly_comm_ring_hom.hom_add eval_mpoly_map_poly_comm_ring_hom.hom_power
      by (metis (mono_tags, lifting) comp_apply map_eq_conv)
    then show ?thesis
      using h1 h2 by auto 
  qed
  then have p_connect: "eval_mpoly_poly val ?multiv_p = ?univ_p"
    unfolding eval_mpoly_poly_def eval_mpoly_poly_list_def
    by auto
  then have "eval_mpoly_poly val (pderiv ?multiv_p) = pderiv ?univ_p"
    by (metis pderiv_commutes)
  then have q_connect: "eval_mpoly_poly val ?multiv_q = ?univ_q"
    using  eval_mpoly_map_poly_comm_ring_hom.hom_mult
    unfolding eval_mpoly_poly_list_def
    using eval_mpoly_poly_comm_ring_hom.hom_mult eval_mpoly_poly_comm_ring_hom.prod_list_map_hom by presburger 
  have tq_is: "tarski_query = 
    (let lcs = lead_coeffs ss;
         sa_list = map (\<lambda>lc. lookup_assump lc assumps) lcs;
         degrees_list = degrees ss in
     rat_of_int (changes_R_smods_multiv sa_list degrees_list))"
    using as_is atq_is by auto
  have "\<And>x. x \<in> set ss \<Longrightarrow>
         sign_rat
          (case lookup_assump_aux (Polynomial.lead_coeff x) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) =
         sign_rat (eval_mpoly val (Polynomial.lead_coeff x))"
  proof - 
    fix x
    assume "x \<in> set ss"
    then have "\<exists>i. (Polynomial.lead_coeff x, i) \<in> set assumps"
      using in_spmods_multiv spmods_multiv_sturm_lc[of assumps ss _ _ acc x]
      by meson
    then obtain i where i_prop: "(Polynomial.lead_coeff x, i) \<in> set assumps"
      by auto 
    then have "satisfies_evaluation val (Polynomial.lead_coeff x) i"
      using val
      by auto
    then have "\<And>j. (Polynomial.lead_coeff x, j) \<in> set assumps \<Longrightarrow> sign_rat i = sign_rat j"
      using val unfolding satisfies_evaluation_def
      by (metis of_int_hom.injectivity sign_rat_def)
    then have "\<exists>j. (case lookup_assump_aux (Polynomial.lead_coeff x) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) = j \<and> sign_rat i = sign_rat j"
      by (smt (verit, del_insts) i_prop in_set_member inset_means_lookup_assump_some lookup_assum_aux_mem option.case(2))
    then show "sign_rat
          (case lookup_assump_aux (Polynomial.lead_coeff x) assumps of None \<Rightarrow> 1000 | Some i \<Rightarrow> i) =
         sign_rat (eval_mpoly val (Polynomial.lead_coeff x))"
      using i_prop val
      by (metis of_int_hom.injectivity satisfies_evaluation_def sign_rat_def) 
  qed
  then have "map sign_rat (map (\<lambda>lc. lookup_assump lc assumps) (lead_coeffs ss)) =
    map (\<lambda>x. sign_rat (eval_mpoly val x)) (lead_coeffs ss)"
    using val by auto
  then have "changes_R_smods_multiv (map (\<lambda>lc. lookup_assump lc assumps) (lead_coeffs ss)) (degrees ss) =
    changes_R_smods (eval_mpoly_poly val (sum_list (map power2 (p # I1))))
     (eval_mpoly_poly val (pderiv (sum_list (map power2 (p # I1))) * prod_list I2))"
    using changes_R_smods_multiv_univariate[of assumps ss ?multiv_p ?multiv_q acc "degrees ss" val ?signs_list] in_spmods_multiv val
    by (smt (verit, ccfv_SIG)) (* Takes a couple of seconds to load *)
  then show ?thesis 
    unfolding construct_NofI_R_def  
    using p_connect q_connect tq_is
    by metis 
qed

end