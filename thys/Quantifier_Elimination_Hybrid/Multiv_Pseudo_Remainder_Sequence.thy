(* This uses insights from Wenda Li's Pseudo_Remainder_Sequence.thy,
but it specializes pseudo-remainder sequences to our type of polynomials.
*)

theory Multiv_Pseudo_Remainder_Sequence
  imports
    Multiv_Consistent_Sign_Assignments

begin

section "Functions"

definition mul_pseudo_mod:: "'a::{comm_ring_1,semiring_1_no_zero_divisors} Polynomial.poly \<Rightarrow> 'a Polynomial.poly \<Rightarrow> 'a Polynomial.poly" where
  "mul_pseudo_mod p q = (
  let m =
    (if even(Polynomial.degree p+1-Polynomial.degree q)
    then -1                
    else -Polynomial.lead_coeff q) in
    Polynomial.smult m (pseudo_mod p q))"

(* This is only ever called when LC p != 0 *)
(* Key helper function for spmods_multiv *)
function spmods_multiv_aux::
  "real mpoly Polynomial.poly \<Rightarrow>
   real mpoly Polynomial.poly \<Rightarrow>
   (real mpoly \<times> rat) list \<Rightarrow> 
   ((real mpoly \<times> rat) list \<times> real mpoly Polynomial.poly list) list" where
  "spmods_multiv_aux p q assumps = (
  if q = 0 then [(assumps, [p])] else
    (case (lookup_assump_aux (Polynomial.lead_coeff q) assumps) of
      None \<Rightarrow>
        let left = spmods_multiv_aux p (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # assumps) in
        let res_one  = spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (1::rat)) # assumps) in
        let res_minus_one  = spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (-1::rat)) # assumps) in
        let right_one = map (\<lambda>x. (fst x, Cons p (snd x))) res_one in
        let right_minus_one = map (\<lambda>x. (fst x, Cons p (snd x))) res_minus_one in
          append left (append right_one right_minus_one)
      | (Some i) \<Rightarrow>
        (if i = 0 then  spmods_multiv_aux p (one_less_degree q) assumps
        else 
          let res = spmods_multiv_aux q (mul_pseudo_mod p q) assumps in
          map (\<lambda>x. (fst x, Cons p (snd x))) res
        )
  ))" using prod_cases3
   apply blast
  by fastforce
termination
  apply (relation "measure (\<lambda>(p,q,r). if q = [:0:] then 1 else 2 + Polynomial.degree q)")
       apply blast
      apply (auto)
  using one_less_degree_degree
      apply (metis one_less_degree_def cancel_comm_monoid_add_class.diff_cancel degree_0_id gr0I monom_0)
  unfolding mul_pseudo_mod_def
  using pseudo_mod(2)
     apply auto[1]
    apply (simp add: degree_pseudo_mod_less)
   apply (metis Multiv_Poly_Props.one_less_degree_def cancel_comm_monoid_add_class.diff_cancel degree_0_id monom_0 not_gr_zero one_less_degree_degree)
  by (metis degree_pseudo_mod_less degree_smult_eq smult_eq_0_iff)

(* The top-level function to generate multivariate pseudo-remainder sequences 
  specialized to real mpoly Polynomial.poly *)
function spmods_multiv::
  "real mpoly Polynomial.poly \<Rightarrow>
   real mpoly Polynomial.poly \<Rightarrow>
   (real mpoly \<times> rat) list \<Rightarrow> 
   ((real mpoly \<times> rat) list \<times> (real mpoly Polynomial.poly list)) list" 
  where "spmods_multiv p q assumps = (
  if p = 0 then [(assumps,[])] else
  (case (lookup_assump_aux (Polynomial.lead_coeff p) assumps) of
      None \<Rightarrow>
        let left = spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # assumps) in
        let right_one  = spmods_multiv_aux p q ((Polynomial.lead_coeff p, (1::rat)) # assumps) in
        let right_minus_one  = spmods_multiv_aux p q ((Polynomial.lead_coeff p, (-1::rat)) # assumps) in
        left @ (right_one @ right_minus_one)
      | (Some i) \<Rightarrow>
        (if i = 0 then  spmods_multiv (one_less_degree p) q assumps
        else 
          spmods_multiv_aux p q assumps
        )
  ))"
  using spmods_multiv_aux.cases apply blast
  by force
termination
  apply (relation "measure (\<lambda>(p,q). if p = [:0:] then 1 else 2 + Polynomial.degree p)")
    apply blast
   apply (auto)
  using one_less_degree_degree
   apply (metis Multiv_Poly_Props.one_less_degree_def cancel_comm_monoid_add_class.diff_cancel degree_0_id monom_0 not_gr_zero)
  by (metis Multiv_Poly_Props.one_less_degree_def cancel_comm_monoid_add_class.diff_cancel degree_0_id monom_0 not_gr_zero one_less_degree_degree)

declare spmods_multiv_aux.simps[simp del]
declare spmods_multiv.simps[simp del]

section "Proofs"

lemma mul_pseudo_mod_valuation:
  assumes "satisfies_evaluation val (Polynomial.lead_coeff p) n"
  assumes "n \<noteq> 0" 
  assumes "satisfies_evaluation val (Polynomial.lead_coeff q) m"
  assumes "m \<noteq> 0" 
  shows "mul_pseudo_mod (eval_mpoly_poly val p) (eval_mpoly_poly val q) =
    eval_mpoly_poly val (mul_pseudo_mod p q)"
proof -
  from degree_valuation[OF assms(1-2)] have
    1: "Polynomial.degree p = Polynomial.degree (eval_mpoly_poly val p)" .
  from degree_valuation[OF assms(3-4)] have
    2: "Polynomial.degree q = Polynomial.degree (eval_mpoly_poly val q)" .
  from lead_coeff_valuation[OF assms(1-2)] have
    3: "eval_mpoly val (Polynomial.lead_coeff p) = Polynomial.lead_coeff (eval_mpoly_poly val p)" .
  from lead_coeff_valuation[OF assms(3-4)] have
    4: "eval_mpoly val (Polynomial.lead_coeff q) = Polynomial.lead_coeff (eval_mpoly_poly val q)" .
  show ?thesis 
    using assms
    by (smt (verit, ccfv_SIG) "1" "2" "4" eval_mpoly_map_poly_comm_ring_hom.base.hom_one eval_mpoly_map_poly_comm_ring_hom.base.hom_uminus eval_mpoly_poly_pseudo_mod eval_mpoly_poly_smult mul_pseudo_mod_def of_int_hom.hom_one of_int_hom.hom_uminus)
  (* apply (auto simp add: mul_pseudo_mod_def 1 2 3 4 eval_mpoly_poly_comm_ring_hom.hom_uminus eval_mpoly_poly_pseudo_mod eval_mpoly_poly_smult)
     apply (metis "2" "4" eval_mpoly_poly_smult)
    by (metis 2 4 eval_mpoly_poly_smult) *)
qed

lemma spmods_multiv_aux_induct[case_names Base Rec Lookup0 LookupN0]:
  fixes p q :: "real mpoly Polynomial.poly"
  fixes assumps ::"(real mpoly \<times> rat) list"
  assumes base: "\<And>p q assumps. q = 0 \<Longrightarrow> P p q assumps"
    and rec: "\<And>p q assumps.
        \<lbrakk>q \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff q) assumps = None;
        P p (one_less_degree q) ((Polynomial.lead_coeff q, 0) # assumps);
        P q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, 1) # assumps);
        P q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, -1) # assumps)\<rbrakk> \<Longrightarrow>
        P p q assumps"
    and lookup0: "\<And>p q assumps.
        \<lbrakk>q \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some 0;
        P p (one_less_degree q) assumps\<rbrakk> \<Longrightarrow> P p q assumps"
    and lookupN0: "\<And>p q assumps r. 
        \<lbrakk>q \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some r;
        r \<noteq> 0;
        P q (mul_pseudo_mod p q) assumps\<rbrakk> \<Longrightarrow> P p q assumps"
  shows "P p q assumps"
  apply(induct p q assumps rule: spmods_multiv_aux.induct)
  by (metis base rec lookup0 lookupN0 not_None_eq)


lemma spmods_multiv_induct[case_names Base Rec Lookup0 LookupN0]:
  fixes p q :: "real mpoly Polynomial.poly"
  fixes assumps ::"(real mpoly \<times> rat) list"
  assumes base: "\<And>p q assumps. p = 0 \<Longrightarrow> P p q assumps"
    and rec: "\<And>p q assumps.
        \<lbrakk>p \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff p) assumps = None;
        P (one_less_degree p) q ((Polynomial.lead_coeff p, 0) # assumps)\<rbrakk> \<Longrightarrow>
        P p q assumps"
    and lookup0: "\<And>p q assumps.
        \<lbrakk>p \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff p) assumps = Some 0;
        P (one_less_degree p) q assumps\<rbrakk> \<Longrightarrow> P p q assumps"
    and lookupN0: "\<And>p q assumps r. 
        \<lbrakk>p \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff p) assumps = Some r;
        r \<noteq> 0\<rbrakk> \<Longrightarrow> P p q assumps"
  shows "P p q assumps"
  apply(induct p q assumps rule: spmods_multiv.induct)
  by (metis base rec lookup0 lookupN0 not_None_eq)


lemma spmods_multiv_aux_assum_acc:
  assumes "(acc',seq') \<in> set (spmods_multiv_aux p q acc)"
  shows "set acc \<subseteq> set acc'"
  using assms  
proof (induct p q acc arbitrary:acc' seq' rule: spmods_multiv_aux_induct)
  case (Base p q assumps)
  then show ?case by (auto simp add: spmods_multiv_aux.simps)
next
  case (Rec p q assumps)
  then show ?case using spmods_multiv_aux.simps[of p q assumps]
    by (smt (z3) Un_iff imageE insert_subset list.set(2) list.set_map old.prod.inject option.simps(4) prod.collapse set_append)
    (* apply (auto simp add: spmods_multiv_aux.simps[of p q assumps])
     apply blast
    by blast *)
next
  case (Lookup0 p q assumps)
  then show ?case
    by (auto simp add: spmods_multiv_aux.simps[of p q assumps])
next
  case (LookupN0 p q assumps r)
  then show ?case using spmods_multiv_aux.simps[of p q assumps]
    using option.simps(5) prod.collapse by fastforce
qed

lemma spmods_multiv_assum_acc:
  assumes "(acc',seq') \<in> set (spmods_multiv p q acc)"
  shows "set acc \<subseteq> set acc'"
  using assms  
proof (induct p q acc arbitrary:acc' seq' rule: spmods_multiv_induct)
  case (Base p q assumps)
  then show ?case by (auto simp add: spmods_multiv.simps)
next
  case (Rec p q assumps)
  then show ?case
    using spmods_multiv_aux_assum_acc spmods_multiv.simps[of p q assumps]
    by (metis Un_iff insert_subset list.set(2) option.simps(4) set_append)
next
  case (Lookup0 p q assumps)
  then show ?case
    by (auto simp add: spmods_multiv.simps[of p q assumps])
next
  case (LookupN0 p q assumps r)
  then show ?case
    using spmods_multiv_aux_assum_acc
    by (auto simp add: spmods_multiv.simps[of p q assumps])
qed


lemma lookup_assum_aux_mem:
  assumes "lookup_assump_aux x ls = Some i"
  shows "(x,i) \<in> set ls"
  using assms
  apply (induction ls)
   apply force
  by (metis fst_conv list.set_intros(1) list.set_intros(2) lookup_assump_aux.simps(2) old.prod.exhaust option.inject prod.sel(2))

lemma matches_ss:
  assumes "(Polynomial.lead_coeff p,m) \<in> set assumps" "m \<noteq> 0"
  assumes "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p q acc)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "map (eval_mpoly_poly val) sturm_seq =
    spmods (eval_mpoly_poly val p) (eval_mpoly_poly val q)"
  using assms
proof (induct p q acc arbitrary:assumps sturm_seq m rule: spmods_multiv_aux_induct)
  case (Base p q assumps)
  then show ?case
    using lead_coeff_valuation satisfies_evaluation_nonzero spmods_multiv_aux.simps by fastforce
next
  case ih: (Rec p q acc)
  let ?left = "spmods_multiv_aux p (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # acc)"
  let ?res_one = "spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (1::rat)) # acc)"
  let ?res_minus_one = "spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (-1::rat)) # acc)"
  have rec: "(assumps, sturm_seq) \<in> set ?left \<or>
    (assumps, sturm_seq) \<in> set (map (\<lambda>x. (fst x, Cons p (snd x))) ?res_one) \<or>
    (assumps, sturm_seq) \<in> set (map (\<lambda>x. (fst x, Cons p (snd x))) ?res_minus_one)"
    using ih by (auto simp add:  spmods_multiv_aux.simps[of p q acc])
  moreover {
    assume "(assumps, sturm_seq) \<in> set ?left"
    then have "map (eval_mpoly_poly val) sturm_seq = spmods (eval_mpoly_poly val p) (eval_mpoly_poly val q)"
      by (metis eval_mpoly_poly_one_less_degree ih.hyps(3) ih.prems(1) ih.prems(2) ih.prems(4) insert_subset list.set(2) spmods_multiv_aux_assum_acc)
  }
  moreover {
    assume **:"
      (assumps, sturm_seq) \<in> set (map (\<lambda>x. (fst x, Cons p (snd x))) ?res_one) \<or>
      (assumps, sturm_seq) \<in> set (map (\<lambda>x. (fst x, Cons p (snd x))) ?res_minus_one)"
    then obtain s ss where ss:"sturm_seq = s#ss"
      and rec:"(assumps,ss) \<in> set ?res_one \<or> (assumps,ss) \<in> set ?res_minus_one"
      by auto
    have lead_coeff_inset: "(Polynomial.lead_coeff q,1) \<in> set assumps \<or> (Polynomial.lead_coeff q,-1) \<in> set assumps"
      using ** spmods_multiv_aux_assum_acc by fastforce
    then have A:"map (eval_mpoly_poly val) ss =
      spmods (eval_mpoly_poly val q) (eval_mpoly_poly val (mul_pseudo_mod p q))"
      by (metis ih.hyps(4) ih.hyps(5) ih.prems(4) local.rec zero_neq_neg_one zero_neq_one)
    have B:"spmods (eval_mpoly_poly val p) (eval_mpoly_poly val q) =
      ((eval_mpoly_poly val p) # (spmods (eval_mpoly_poly val q) (mul_pseudo_mod  (eval_mpoly_poly val p) (eval_mpoly_poly val q))))"
      by (metis ih.prems(1) ih.prems(2) ih.prems(4) lead_coeff_valuation leading_coeff_0_iff mul_pseudo_mod_def satisfies_evaluation_nonzero spmods.simps)
    have C: "mul_pseudo_mod (eval_mpoly_poly val p) (eval_mpoly_poly val q) = eval_mpoly_poly val (mul_pseudo_mod p q)"
      by (metis lead_coeff_inset ih.prems(1) ih.prems(2) ih.prems(4) mul_pseudo_mod_valuation zero_neq_neg_one zero_neq_one)
    have "map (eval_mpoly_poly val) sturm_seq = spmods (eval_mpoly_poly val p) (eval_mpoly_poly val q)"
      using A B C rec ss ** by auto 
  }
  ultimately show ?case 
    using local.rec by blast
next
  case (Lookup0 p q acc)
  then have rec: "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p (one_less_degree q) acc)"
    by (auto simp add:  spmods_multiv_aux.simps[of p q acc])
  have "(Polynomial.lead_coeff q,0) \<in> set acc"
    by (simp add: Lookup0.hyps(2) lookup_assum_aux_mem)
  then have "satisfies_evaluation val (Polynomial.lead_coeff q) 0"
    using Lookup0.prems(3) Lookup0.prems(4) spmods_multiv_aux_assum_acc by blast
  then have "eval_mpoly_poly val (one_less_degree q) = (eval_mpoly_poly val q)"
    by (auto simp add: eval_mpoly_poly_one_less_degree)
  then show ?case
    using Lookup0.hyps(3) Lookup0.prems(1) Lookup0.prems(2) Lookup0.prems(4) local.rec by presburger
next
  case ih:(LookupN0 p q acc r)
  then have asm:"(assumps, sturm_seq) \<in> set (
       map (\<lambda>x. (fst x, Cons p (snd x)))
        (spmods_multiv_aux q (mul_pseudo_mod p q) acc))"
    by (auto simp add:  spmods_multiv_aux.simps[of p q acc])
  then obtain s ss where ss:"sturm_seq = s#ss"
    and rec:"(assumps,ss) \<in> set (spmods_multiv_aux q (mul_pseudo_mod p q) acc)"
    by auto
  have A:"map (eval_mpoly_poly val) ss = spmods (eval_mpoly_poly val q) (eval_mpoly_poly val (mul_pseudo_mod p q))"
    using ih(4)[OF _ _ rec]
    by (meson ih.hyps(2) ih.hyps(3) ih.prems(4) in_mono local.rec lookup_assump_means_inset spmods_multiv_aux_assum_acc) 
  have B:"spmods (eval_mpoly_poly val p) (eval_mpoly_poly val q) =
    ((eval_mpoly_poly val p) # (spmods (eval_mpoly_poly val q) (mul_pseudo_mod  (eval_mpoly_poly val p) (eval_mpoly_poly val q))))"
    by (metis ih(5) ih(6) ih.prems(4) lead_coeff_valuation leading_coeff_0_iff mul_pseudo_mod_def satisfies_evaluation_nonzero spmods.simps)
  have C: "mul_pseudo_mod (eval_mpoly_poly val p)  (eval_mpoly_poly val q) = eval_mpoly_poly val (mul_pseudo_mod p q)"
    by (meson ih.hyps(2) ih.hyps(3) ih.prems(1) ih.prems(2) ih.prems(4) local.rec lookup_assum_aux_mem mul_pseudo_mod_valuation spmods_multiv_aux_assum_acc subsetD)
  show ?case
    using A B C rec ss asm by force
qed

lemma spmods_multiv_aux_sturm_lc:
  assumes "(Polynomial.lead_coeff p,m) \<in> set acc" "m \<noteq> 0"
  assumes "(acc',seq') \<in> set (spmods_multiv_aux p q acc)"
  assumes "el \<in> set seq'"
  shows "\<exists>r. (Polynomial.lead_coeff el,r) \<in> set acc' \<and> r \<noteq> 0"
  using assms
proof (induct p q acc arbitrary:acc' seq' el m rule: spmods_multiv_aux_induct)
  case (Base p q acc)
  then show ?case
    using empty_iff fst_conv list.set(1) prod.sel(2) set_ConsD spmods_multiv_aux.simps by auto
next
  case (Rec p q acc)
  then show ?case
    apply (auto simp add: spmods_multiv_aux.simps[of p q acc])
       apply (meson Rec.prems(3) spmods_multiv_aux_assum_acc subset_eq)
      apply (metis zero_neq_one)
     apply (meson Rec.prems(3) spmods_multiv_aux_assum_acc subset_iff)
    by (metis zero_neq_neg_one)

next
  case (Lookup0 p q acc)
  then show ?case
    by (auto simp add: spmods_multiv_aux.simps[of p q acc])
next
  case (LookupN0 p q acc r)
  then show ?case
    apply (auto simp add: spmods_multiv_aux.simps[of p q acc])
    using spmods_multiv_aux_assum_acc apply blast
    by (meson lookup_assum_aux_mem)
qed

lemma spmods_multiv_sturm_lc:
  assumes "(acc',seq') \<in> set (spmods_multiv p q acc)"
  assumes "el \<in> set seq'"
  shows "\<exists>r. (Polynomial.lead_coeff el,r) \<in> set acc' \<and> r \<noteq> 0"
  using assms
proof (induct p q acc arbitrary:acc' seq' rule: spmods_multiv_induct)
  case (Base p q assumps)
  then show ?case 
    using spmods_multiv.simps
    by simp
next
  case (Rec p q assumps)
  then show ?case 
    apply (auto simp add: spmods_multiv.simps[of p q assumps]) 
    using spmods_multiv_aux_sturm_lc
     apply (metis list.set_intros(1) zero_neq_one)
    by (metis list.set_intros(1) spmods_multiv_aux_sturm_lc zero_neq_neg_one)  
next
  case (Lookup0 p q assumps)
  then show ?case 
    by (auto simp add: spmods_multiv.simps[of p q assumps]) 
next
  case (LookupN0 p q assumps r)
  then show ?case using spmods_multiv.simps[of p q assumps] 
    spmods_multiv_aux_sturm_lc lookup_assum_aux_mem
    by (smt (verit, ccfv_threshold) option.simps(5))    
    (* apply (auto simp add: spmods_multiv.simps[of p q assumps]) 
    using spmods_multiv_aux_sturm_lc
    by (meson lookup_assum_aux_mem) *)
qed


lemma matches_len_complete:
  assumes "\<And>p n. (p,n) \<in> set acc \<Longrightarrow> satisfies_evaluation val p n"
  obtains assumps sturm_seq where
    "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p q acc)"
    "\<And> p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  using assms
proof (induct p q acc arbitrary: thesis rule: spmods_multiv_aux_induct)
  case (Base p q acc)
  then show ?case
    by (simp add: spmods_multiv_aux.simps)
next
  case ih: (Rec p q acc)
  let ?left = "spmods_multiv_aux p (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # acc)"
  let ?res_one = "spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (1::rat)) # acc)"
  let ?res_minus_one = "spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (-1::rat)) # acc)"
  have "satisfies_evaluation val (Polynomial.lead_coeff q) 0 \<or>
    satisfies_evaluation val (Polynomial.lead_coeff q) 1 \<or>
    satisfies_evaluation val (Polynomial.lead_coeff q) (-1)"
    unfolding satisfies_evaluation_def
    apply auto
    using Sturm_Tarski.sign_cases
    by (metis of_int_hom.hom_one of_int_minus) 
  then have q:"
  (\<forall>p n. (p,n) \<in> set ((Polynomial.lead_coeff q, 0) # acc) \<longrightarrow> satisfies_evaluation val p n) \<or>
  (\<forall>p n. (p,n) \<in> set ((Polynomial.lead_coeff q, 1) # acc) \<longrightarrow> satisfies_evaluation val p n) \<or>
  (\<forall>p n. (p,n) \<in> set ((Polynomial.lead_coeff q, -1) # acc) \<longrightarrow> satisfies_evaluation val p n)"
    by (simp add: ih.prems(2))
  moreover {
    assume *:"(\<forall>p n. (p,n) \<in> set ((Polynomial.lead_coeff q, 0) # acc) \<longrightarrow> satisfies_evaluation val p n)"
    then have ?case using * ih(3)
      by (metis (no_types, lifting) Un_iff ih.hyps(1) ih.hyps(2) ih.prems(1) option.case(1) set_append spmods_multiv_aux.simps)
  }
  moreover {
    assume *:"(\<forall>p n. (p,n) \<in> set ((Polynomial.lead_coeff q, 1) # acc) \<longrightarrow> satisfies_evaluation val p n)"
    then have ?case using * ih(4)
      by (smt (z3) Un_iff fst_conv ih.hyps(1) ih.hyps(2) ih.prems(1) in_set_conv_decomp list.simps(9) map_append option.case(1) set_append spmods_multiv_aux.simps)
  }
  moreover {
    assume *:"(\<forall>p n. (p,n) \<in> set ((Polynomial.lead_coeff q, -1) # acc) \<longrightarrow> satisfies_evaluation val p n)"
    then have ?case using * ih(5)
      by (smt (z3) Un_iff fst_conv ih.hyps(1) ih.hyps(2) ih.prems(1) in_set_conv_decomp list.simps(9) map_append option.case(1) set_append spmods_multiv_aux.simps)
  }
  ultimately show ?case
    by fastforce
next
  case (Lookup0 p q acc)
  then show ?case
    by (auto simp add: spmods_multiv_aux.simps[of p q acc])
next
  case ih: (LookupN0 p q assumps r)
  then obtain assumps' sturm_seq' where
    "(assumps', sturm_seq') \<in> set (spmods_multiv_aux q (mul_pseudo_mod p q) assumps)"
    "(\<And>p n. (p, n) \<in> set assumps' \<Longrightarrow> satisfies_evaluation val p n)"
    by blast
  then show ?case using ih spmods_multiv_aux.simps[of p q assumps] fst_conv image_eqI
    by (smt (verit) list.set_map option.simps(5))
    (* apply (auto simp add: spmods_multiv_aux.simps[of p q assumps])
    by (metis (mono_tags, lifting) fst_conv image_eqI) *)
qed

lemma spmods_multiv_nonz_some:
  fixes p:: "real mpoly Polynomial.poly"
  fixes q:: "real mpoly Polynomial.poly"
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  shows "p \<noteq> 0 \<Longrightarrow> \<exists>i. lookup_assump_aux (Polynomial.lead_coeff p) assumps = Some i"
  using assms 
proof (induct p q acc rule: spmods_multiv_induct)
  case (Base p q acc)
  then show ?case by auto
next
  case (Rec p q acc)
  then have "(lookup_assump_aux (Polynomial.lead_coeff p) acc) = None"
    by meson
  then have "set (spmods_multiv p q acc) =
      set (spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # acc)) 
      \<union> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (1::rat)) # acc))
      \<union> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (-1::rat)) # acc))"
    by (simp add: Rec.prems(1) spmods_multiv.simps sup_assoc)
  then have "(assumps, sturm_seq) \<in> set (spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # acc))
      \<or> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (1::rat)) # acc))
      \<or> (assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (-1::rat)) # acc))"
    using Rec.prems(2) by blast  
  then show ?case 
    using spmods_multiv_assum_acc spmods_multiv_aux_assum_acc
    by (metis insert_subset inset_means_lookup_assump_some list.set(2))
next
  case (Lookup0 p q acc)
  then show ?case
    by (meson inset_means_lookup_assump_some lookup_assum_aux_mem spmods_multiv_assum_acc subset_eq)
next
  case (LookupN0 p q acc r)
  then show ?case
    by (meson in_set_member inset_means_lookup_assump_some lookup_assump_means_inset spmods_multiv_assum_acc subsetD)
qed

lemma spmods_multiv_aux_nonz_some:
  fixes p:: "real mpoly Polynomial.poly"
  fixes q:: "real mpoly Polynomial.poly"
  assumes inset: "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p q acc)"
  shows "q \<noteq> 0 \<Longrightarrow> \<exists>i. lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some i"
  using assms 
proof (induct p q acc rule: spmods_multiv_aux_induct)
  case (Base p q acc)
  then show ?case by auto
next
  case (Rec p q acc)
  then have "(lookup_assump_aux (Polynomial.lead_coeff q) acc) = None"
    by meson
  then have "set (spmods_multiv_aux p q acc) =
      set (spmods_multiv_aux p (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # acc)) 
      \<union> set ( map (\<lambda>x. (fst x, Cons p (snd x))) (spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (1::rat)) # acc)))
      \<union> set ( map (\<lambda>x. (fst x, Cons p (snd x)))  (spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (-1::rat)) # acc)))"
    using Rec.prems(1) spmods_multiv_aux.simps 
    by (simp add: Rec.prems(1) spmods_multiv_aux.simps sup_assoc)
  then have bigh: "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # acc))
      \<or> (assumps, sturm_seq) \<in> set ( map (\<lambda>x. (fst x, Cons p (snd x))) (spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (1::rat)) # acc)))
      \<or> (assumps, sturm_seq) \<in> set ( map (\<lambda>x. (fst x, Cons p (snd x)))  (spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, (-1::rat)) # acc)))"
    using Rec.prems(2) 
    by blast  
  have h1: "(\<And>acc' seq' p q acc. (acc', seq') \<in> set (spmods_multiv_aux p q acc) \<Longrightarrow> set acc \<subseteq> set acc') \<Longrightarrow>
    (assumps, sturm_seq)
    \<in> set (spmods_multiv_aux p (Multiv_Poly_Props.one_less_degree q)
             ((Polynomial.lead_coeff q, 0) # acc)) \<Longrightarrow>
    \<exists>i. lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some i"
    by (meson in_set_member inset_means_lookup_assump_some list.set_intros(1) subsetD)
  have h2: "\<And>b. (\<And>acc' seq' p q acc. (acc', seq') \<in> set (spmods_multiv_aux p q acc) \<Longrightarrow> set acc \<subseteq> set acc') \<Longrightarrow>
         (assumps, b)
         \<in> set (spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, 1) # acc)) \<Longrightarrow>
         sturm_seq = p # b \<Longrightarrow> \<exists>i. lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some i"
    by (meson in_set_member inset_means_lookup_assump_some list.set_intros(1) subsetD)
  have h3: "\<And>b. (\<And>acc' seq' p q acc. (acc', seq') \<in> set (spmods_multiv_aux p q acc) \<Longrightarrow> set acc \<subseteq> set acc') \<Longrightarrow>
         (assumps, b)
         \<in> set (spmods_multiv_aux q (mul_pseudo_mod p q) ((Polynomial.lead_coeff q, - 1) # acc)) \<Longrightarrow>
         sturm_seq = p # b \<Longrightarrow> \<exists>i. lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some i"
    by (meson in_set_member inset_means_lookup_assump_some list.set_intros(1) subsetD)
  show ?case 
    using bigh spmods_multiv_aux_assum_acc h1 h2 h3
    by auto
next
  case (Lookup0 p q acc)
  then show ?case
    by (meson inset_means_lookup_assump_some lookup_assum_aux_mem spmods_multiv_aux_assum_acc subsetD) 
next
  case (LookupN0 p q acc r)
  then show ?case
    by (meson in_set_member inset_means_lookup_assump_some lookup_assump_means_inset spmods_multiv_aux_assum_acc subsetD)
qed

lemma spmods_multiv_sound:
  assumes "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "map (eval_mpoly_poly val) sturm_seq =
    spmods (eval_mpoly_poly val p) (eval_mpoly_poly val q)"
  using assms
proof (induct p q acc arbitrary:assumps sturm_seq rule: spmods_multiv_induct)
  case (Base p q assumps)
  then show ?case
    by (simp add: spmods_multiv.simps)
next
  case (Rec p q assumps)
  then show ?case
    by (smt (verit, best) UnE eval_mpoly_poly_one_less_degree list.set_intros(1) matches_ss option.simps(4) set_append spmods_multiv.simps spmods_multiv_assum_acc spmods_multiv_aux_assum_acc subsetD zero_neq_neg_one zero_neq_one) 
next
  case (Lookup0 p q assumps)
  define pval where pval:"pval = eval_mpoly_poly val p"
  define qval where qval:"qval = eval_mpoly_poly val q"
  have "(Polynomial.lead_coeff p,0) \<in> set assumps"
    using Lookup0.hyps Lookup0.prems
    by (meson lookup_assum_aux_mem spmods_multiv_assum_acc subset_code(1))
  then have "satisfies_evaluation val (Polynomial.lead_coeff p) 0"
    using Lookup0.hyps Lookup0.prems by blast
  from eval_mpoly_poly_one_less_degree[OF this] have
    eval_prop: "eval_mpoly_poly val (one_less_degree p) = pval" using pval qval 
    by auto
  have "map (eval_mpoly_poly val) sturm_seq = spmods pval qval"
    using Lookup0.hyps Lookup0.prems pval qval
    by (simp add: eval_prop spmods_multiv.simps) 
  then show ?case
    using pval qval by blast 
next
  case (LookupN0 p q assumps r)
  define pval where pval:"pval = eval_mpoly_poly val p"
  define qval where qval:"qval = eval_mpoly_poly val q"
  {
    assume right: "\<exists>k. lookup_assump_aux (Polynomial.lead_coeff p) assumps = Some k \<and>k \<noteq> 0"
    then obtain k where k_prop: "lookup_assump_aux (Polynomial.lead_coeff p) assumps = Some k \<and>k \<noteq> 0"
      by auto 
    then have "(Polynomial.lead_coeff p,k) \<in> set assumps"
      using spmods_multiv_aux_assum_acc
      by (simp add: lookup_assum_aux_mem) 
    have "k \<noteq> 0"
      using k_prop by auto
    then have
      "map (eval_mpoly_poly val) sturm_seq = spmods pval qval"
      using matches_ss[of p k assumps sturm_seq q _ val] right LookupN0.prems(2)  LookupN0.prems LookupN0.hyps
      using \<open>(Polynomial.lead_coeff p, k) \<in> set assumps\<close> pval qval
      by (simp add: spmods_multiv.simps) 
  }
  then have "map (eval_mpoly_poly val) sturm_seq = spmods pval qval"
    using LookupN0.hyps LookupN0.prems
      lookup_assump_aux_subset_consistency option.case(2) spmods_multiv.simps spmods_multiv_aux_assum_acc
    by (smt (verit) Sturm_Tarski.sign_def in_mono lookup_assum_aux_mem of_int_hom.injectivity satisfies_evaluation_def sign_simps(2) spmods_multiv_nonz_some)
  then show ?case
    using pval qval by blast
qed

end