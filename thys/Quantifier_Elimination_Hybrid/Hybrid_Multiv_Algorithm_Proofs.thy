(* This file includes proofs (soundness and completeness) for our 
  top-level hybrid QE algorithm defined in Hybrid_Multiv_Algorithm.thy.
*)


theory Hybrid_Multiv_Algorithm_Proofs

imports Hybrid_Multiv_Algorithm
  Hybrid_Multiv_Matrix_Proofs
  Virtual_Substitution.ExportProofs

begin

subsection "Lemmas about branching (lc assump generation)"

lemma lc_assump_generation_induct[case_names Base Rec Lookup0 LookupN0]:
  fixes q :: "real mpoly Polynomial.poly"
  fixes assumps ::"(real mpoly \<times> rat) list"
  assumes base: "\<And>q assumps. q = 0 \<Longrightarrow> P q assumps"
    and rec: "\<And>q assumps.
        \<lbrakk>q \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff q) assumps = None;
        P (one_less_degree q) ((Polynomial.lead_coeff q, 0) # assumps)\<rbrakk> \<Longrightarrow>
        P q assumps"
    and lookup0: "\<And>q assumps.
        \<lbrakk>q \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some 0;
        P (one_less_degree q) assumps\<rbrakk> \<Longrightarrow> P q assumps"
    and lookupN0: "\<And>q assumps r. 
        \<lbrakk>q \<noteq> 0;
        lookup_assump_aux (Polynomial.lead_coeff q) assumps = Some r;
        r \<noteq> 0\<rbrakk> \<Longrightarrow> P q assumps"
  shows "P q assumps"
  apply(induct q assumps rule: lc_assump_generation.induct)
  by (metis base rec lookup0 lookupN0 not_None_eq)


lemma lc_assump_generation_subset:
  assumes "(branch_assms, branch_poly_list) \<in> set(lc_assump_generation q assumps)"
  shows "set assumps \<subseteq> set branch_assms"
  using assms 
proof (induct q assumps rule: lc_assump_generation_induct)
  case (Base q assumps)
  then show ?case 
    by (auto simp add: lc_assump_generation.simps)
next
  case (Rec q assumps)
  let ?zero = "lc_assump_generation (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # assumps)"
  let ?one  = "((Polynomial.lead_coeff q, (1::rat)) # assumps, q)"
  let ?minus_one  = "((Polynomial.lead_coeff q, (-1::rat)) # assumps, q)"
  have "(branch_assms, branch_poly_list) \<in> set (?one#?minus_one#?zero)"
    using Rec.hyps Rec(4) lc_assump_generation.simps by auto 
  then show ?case
    using Rec(3) by force  
next
  case (Lookup0 q assumps)
  then show ?case 
    using lc_assump_generation.simps
    by simp 
next
  case (LookupN0 q assumps r)
  then show ?case 
    by (auto simp add: lc_assump_generation.simps)
qed

lemma branch_init_assms_subset:
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  shows "set init_assumps \<subseteq> set branch_assms"
  using assms
proof (induct qs arbitrary: branch_assms branch_poly_list init_assumps)
  case Nil
  then show ?case
    by (simp add: lc_assump_generation_list.simps(1))
next
  case (Cons a bpl)
  then show ?case
    using lc_assump_generation_subset 
    apply (auto simp add: lc_assump_generation_list.simps)
    by blast
qed

lemma prod_list_var_gen_nonzero:
  shows "prod_list_var_gen qs \<noteq> 0"
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then show ?case by auto 
qed

(* Invariant: For all (a, q) in the output, either
  q is 0 or the leading coefficient of q is assumed nonzero in a *)
lemma lc_assump_generation_inv:
  assumes "(a, q) \<in> set (lc_assump_generation init_q assumps)"
  shows "q = (0::rmpoly) \<or> (\<exists>i. (lookup_assump_aux (Polynomial.lead_coeff q) a = Some i \<and> i \<noteq> 0))"
  using assms
proof (induct init_q assumps arbitrary: q a rule: lc_assump_generation_induct )
  case (Base init_q assumps)
  then show ?case 
    using lc_assump_generation.simps by auto 
next
  case (Rec init_q assumps)
  let ?zero = "lc_assump_generation (one_less_degree init_q) ((Polynomial.lead_coeff init_q, (0::rat)) # assumps)"
  let ?one  = "((Polynomial.lead_coeff init_q, (1::rat)) # assumps, init_q)"
  let ?minus_one = "((Polynomial.lead_coeff init_q, (-1::rat)) # assumps, init_q)"
  have "(a, q) \<in> set (?one # ?minus_one # ?zero)"
    using Rec.prems Rec.hyps(1) Rec.hyps(2) lc_assump_generation.simps
    by auto
  then have eo: "(a, q) = ?one \<or> (a, q) = ?minus_one \<or> (a, q) \<in> set(?zero)"
    by auto
  {assume *: "(a, q) = ?one"
    then have "q = (0::rmpoly) \<or> (\<exists>i. (lookup_assump_aux (Polynomial.lead_coeff q) a = Some i \<and> i \<noteq> 0))"
      by auto
  }
  moreover {assume *: "(a, q) = ?minus_one"
    then have "q = (0::rmpoly) \<or> (\<exists>i. (lookup_assump_aux (Polynomial.lead_coeff q) a = Some i \<and> i \<noteq> 0))"
      by auto
  }
  moreover   {assume *: "(a, q)  \<in> set(?zero)"
    then have "q = (0::rmpoly) \<or> (\<exists>i. (lookup_assump_aux (Polynomial.lead_coeff q) a = Some i \<and> i \<noteq> 0))"
      using Rec.hyps Rec.prems by auto
  }
  ultimately show ?case 
    using lc_assump_generation.simps
    using eo by fastforce
next
  case (Lookup0 init_q assumps)
  then show ?case using lc_assump_generation.simps by auto 
next
  case (LookupN0 init_q assumps r)
  then show ?case using lc_assump_generation.simps by auto 
qed

lemma lc_assump_generation_list_inv:
  assumes val: "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  shows "q \<in> set branch_poly_list \<Longrightarrow> q = 0 \<or> (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff q) branch_assms = Some i \<and> i \<noteq> 0)"
  using assms
proof (induct qs arbitrary: q init_assumps branch_poly_list branch_assms)
  case Nil
  then have "(branch_assms, branch_poly_list) \<in> set [(init_assumps, [])]"
    using lc_assump_generation_list.simps by auto
  then have "branch_poly_list = []"
    using in_set_member
    by simp 
  then show ?case 
    using Nil.prems(1)
    by simp  
next
  case (Cons a qs)
  let ?rec = "lc_assump_generation a init_assumps"
  have inset: "(branch_assms,branch_poly_list) \<in> set (
    concat (map (
      \<lambda>(new_assumps, r). (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec) ) ?rec ))"
    using Cons.prems lc_assump_generation_list.simps
    by auto 
  then obtain new_assumps r where deconstruct_prop:
    "(new_assumps, r) \<in> set ?rec"
    "(branch_assms,branch_poly_list) \<in> set (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec)"
    using inset
    by (metis (no_types, lifting) concat_map_in_set nth_mem prod.collapse split_def)
  then obtain elem list_rec where list_rec_prop:
    "list_rec = lc_assump_generation_list qs new_assumps"
    "elem \<in> set list_rec"
    "(branch_assms,branch_poly_list) = (fst elem, r#(snd elem))" 
    by auto
  then have pair_in_set: "(branch_assms, snd elem) \<in> set (lc_assump_generation_list qs new_assumps)"
    using deconstruct_prop by auto
  then have snd_elem_is: "\<And>q. q \<in> set (snd elem) \<Longrightarrow>
    q = 0 \<or> (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff q) branch_assms = Some i \<and> i \<noteq> 0)"
    using Cons.hyps
    by (simp add: local.Cons(3)) 
  have ris_var: "r = 0 \<or> (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff r)new_assumps = Some i \<and> i \<noteq> 0) "
    using lc_assump_generation_inv[of new_assumps r a init_assumps] deconstruct_prop(1) 
    by auto
  have "set new_assumps \<subseteq> set branch_assms"
    using deconstruct_prop list_rec_prop
    using pair_in_set branch_init_assms_subset by presburger
  then have "(\<exists>i. lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i \<and> i \<noteq> 0) \<Longrightarrow>
(\<exists>i. lookup_assump_aux (Polynomial.lead_coeff r) branch_assms = Some i \<and> i \<noteq> 0)"
    using val lookup_assump_aux_subset_consistency
    using local.Cons(3) by blast
  then have ris: "r = 0 \<or> (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff r) branch_assms = Some i \<and> i \<noteq> 0) "
    using ris_var by auto
  then show ?case
    using ris snd_elem_is list_rec_prop(3)
    using Cons.prems(1) by auto
qed

subsection "Correctness of sign determination inner"

lemma q_dvd_prod_list_var_prop:
  assumes "q \<in> set qs"
  assumes "q \<noteq> 0"
  shows "q dvd prod_list_var_gen qs" using assms
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then have eo: "q = a \<or>q \<in> set qs" by auto
  have c1: "q = a \<Longrightarrow> q dvd prod_list_var_gen (a#qs)"
  proof - 
    assume "q = a"
    then have "prod_list_var_gen (a#qs) = q*(prod_list_var_gen qs)" using Cons.prems
      unfolding prod_list_var_gen_def by auto
    then show ?thesis using prod_list_var_gen_nonzero[of qs] by auto
  qed
  have c2: "q \<in> set qs \<longrightarrow> q dvd prod_list_var_gen qs"
    using Cons.prems Cons.hyps unfolding prod_list_var_gen_def by auto
  show ?case using eo c1 c2 by auto
qed

lemma poly_p_nonzero_on_branch:
  assumes assms: "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  assumes "p = poly_p_in_branch (branch_assms, branch_poly_list)"
  shows "eval_mpoly_poly val p \<noteq> 0"
proof - 
  (* Some intuition: the assumps on the qs are contained in branch_assms,
    then because branch_assms contains the proper assumps,
    the poly_p_in_branch definition correctly handles things *)
  {assume *: "(check_all_const_deg_gen branch_poly_list = True)"
    then have p_is: "p = [:0, 1:]"
      using assms
      using poly_p_in_branch.simps by presburger 
    then have "eval_mpoly_poly val p \<noteq> 0"
      by (metis Polynomial.lead_coeff_monom degree_0 dvd_refl eval_commutes eval_mpoly_map_poly_comm_ring_hom.base.hom_one not_is_unit_0 poly_dvd_1 x_as_monom)
  }
  moreover {assume *: "(check_all_const_deg_gen branch_poly_list = False)"
    then have p_is: "p = (pderiv (prod_list_var_gen branch_poly_list)) * (prod_list_var_gen branch_poly_list)"
      using assms
      using poly_p_in_branch.simps by presburger 
    then have assms_inv: "\<And>q. q \<in> set branch_poly_list \<Longrightarrow> q = 0 \<or> (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff q) branch_assms = Some i \<and> i \<noteq> 0)"
      using lc_assump_generation_list_inv assms
      by (meson assms(2)) 
    have q_inv: "\<And>q. q \<in> set branch_poly_list \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> eval_mpoly_poly val q \<noteq> 0"
      using assms_inv assms 
      by (metis eval_commutes leading_coeff_0_iff lookup_assum_aux_mem satisfies_evaluation_nonzero)
    then have "\<And>q. q \<in> set branch_poly_list \<Longrightarrow> (q \<noteq> 0 \<longleftrightarrow> eval_mpoly_poly val q \<noteq> 0)"
      by auto
    then have prod_list_eval: "(eval_mpoly_poly val (prod_list_var_gen branch_poly_list)) = (prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list))"
    proof (induct branch_poly_list)
      case Nil
      then show ?case by auto
    next
      case (Cons a branch_poly_list)
      { assume *: "a = 0"
        then have h1: "eval_mpoly_poly val (prod_list_var_gen (a # branch_poly_list)) = 
          eval_mpoly_poly val (prod_list_var_gen branch_poly_list)"
          by simp
        have "eval_mpoly_poly val a = 0"
          using * by auto 
        then have h2: "prod_list_var_gen (map (eval_mpoly_poly val) (a # branch_poly_list))
      = prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list)"
          by auto
        then have "eval_mpoly_poly val (prod_list_var_gen (a # branch_poly_list)) =
       prod_list_var_gen (map (eval_mpoly_poly val) (a # branch_poly_list))"
          using Cons.hyps Cons.prems h1 h2
          by (simp add: member_rec(1)) 
      }
      moreover { assume *: "a \<noteq> 0"
        then have h1: "eval_mpoly_poly val (prod_list_var_gen (a # branch_poly_list)) = 
          (eval_mpoly_poly val a)*(eval_mpoly_poly val (prod_list_var_gen branch_poly_list))"
          by (simp add: eval_mpoly_poly_comm_ring_hom.hom_mult)
        have "eval_mpoly_poly val a \<noteq> 0"
          using * assms Cons.prems
          by (meson list.set_intros(1))
        then have h2: "prod_list_var_gen (map (eval_mpoly_poly val) (a # branch_poly_list))
          = (eval_mpoly_poly val a)* prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list)"
          by auto
        have "eval_mpoly_poly val (prod_list_var_gen (a # branch_poly_list)) =
          prod_list_var_gen (map (eval_mpoly_poly val) (a # branch_poly_list))"
          using Cons.hyps Cons.prems h1 h2
          by (simp add: member_rec(1)) 
      }
      ultimately show ?case 
        by auto 
    qed
    have degree_q_inv: "\<And>q. q \<in> set branch_poly_list \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> Polynomial.degree (eval_mpoly_poly val q) = Polynomial.degree q"
      using assms_inv assms q_inv
      by (metis degree_valuation lookup_assum_aux_mem) 
    have prod_nonz: "eval_mpoly_poly val (prod_list_var_gen branch_poly_list) \<noteq> 0"
      using q_inv prod_list_eval
      by (simp add: prod_list_var_gen_nonzero)
    have ex_q: "\<exists>q \<in> set branch_poly_list. (q \<noteq> 0 \<and> Polynomial.degree q > 0)"
      using * proof (induct branch_poly_list)
      case Nil
      then show ?case by auto
    next
      case (Cons a branch_poly_list)
      then show ?case
        by (metis bot_nat_0.not_eq_extremum check_all_const_deg_gen.simps(2) degree_0 list.set_intros(1) list.set_intros(2))
    qed
    obtain pos_deg_poly where pos_deg_poly: "pos_deg_poly\<in>set branch_poly_list \<and> pos_deg_poly \<noteq> 0 \<and> 0 < Polynomial.degree pos_deg_poly"
      using ex_q by blast 
    have "pos_deg_poly dvd (prod_list_var_gen branch_poly_list)"
      by (simp add: Hybrid_Multiv_Algorithm_Proofs.q_dvd_prod_list_var_prop pos_deg_poly)
    then have nonc_dvd: "(eval_mpoly_poly val pos_deg_poly) dvd (eval_mpoly_poly val (prod_list_var_gen branch_poly_list))"
      by blast
    have "Polynomial.degree (eval_mpoly_poly val pos_deg_poly) > 0"
      using pos_deg_poly degree_q_inv
      by metis 
    then have prod_nonc:"Polynomial.degree (eval_mpoly_poly val (prod_list_var_gen branch_poly_list)) \<noteq> 0"
      using  nonc_dvd prod_nonz
      by (metis bot_nat_0.extremum_strict dvd_const) 
    then have "eval_mpoly_poly val p \<noteq> 0"
      using prod_nonz prod_nonc
      by (metis eval_mpoly_poly_comm_ring_hom.hom_mult no_zero_divisors p_is pderiv_commutes pderiv_eq_0_iff) 
  }
  ultimately show ?thesis by auto
qed

lemma calc_data_to_signs_and_extract_signs:
  shows "(calculate_data_to_signs ell) = extract_signs ell"
  by auto

lemma branch_poly_eval:
  assumes "(a, q) \<in> set (lc_assump_generation init_q init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set a \<Longrightarrow> satisfies_evaluation val p n"
  shows "(eval_mpoly_poly val) q = (eval_mpoly_poly val) init_q"
  using assms 
proof (induct init_q init_assumps arbitrary: q a rule: lc_assump_generation_induct )
  case (Base init_q init_assumps)
  then show ?case
    by (simp add: lc_assump_generation.simps) 
next
  case (Rec init_q init_assumps)
  then show ?case using lc_assump_generation.simps
      basic_trans_rules(31) eval_mpoly_poly_one_less_degree in_set_member lc_assump_generation_subset member_rec(1) option.case(1) prod.inject
    by (smt (verit, best))
next
  case (Lookup0 init_q init_assumps)
  then show ?case 
    using lc_assump_generation.simps
    by (smt (z3) eval_mpoly_poly_one_less_degree lc_assump_generation_subset lookup_assum_aux_mem option.simps(5) subset_eq) 
      (* Takes a second to load *)
next
  case (LookupN0 init_q init_assumps r)
  then show ?case
    by (simp add: lc_assump_generation.simps) 
qed

lemma eval_prod_list_var_gen_match:
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  shows "eval_mpoly_poly val (prod_list_var_gen branch_poly_list) =
    prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list)"
  using assms 
proof (induct qs arbitrary: branch_assms branch_poly_list init_assumps val)
  case Nil
  then have "(branch_assms, branch_poly_list) \<in> set [(init_assumps, [])]"
    using lc_assump_generation_list.simps by auto
  then have "branch_poly_list = []"
    using in_set_member
    by simp
  then show ?case
    by simp
next
  case (Cons a qs)
  let ?rec = "lc_assump_generation a init_assumps"
  have inset: "(branch_assms,branch_poly_list) \<in> set (
    concat (map (
      \<lambda>(new_assumps, r). (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec) ) ?rec ))"
    using Cons.prems lc_assump_generation_list.simps
    by auto 
  then obtain new_assumps r where deconstruct_prop:
    "(new_assumps, r) \<in> set ?rec"
    "(branch_assms,branch_poly_list) \<in> set (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec)"
    using inset
    by (metis (no_types, lifting) concat_map_in_set nth_mem prod.collapse split_def)
  then obtain elem list_rec where list_rec_prop:
    "list_rec = lc_assump_generation_list qs new_assumps"
    "elem \<in> set list_rec"
    "(branch_assms,branch_poly_list) = (fst elem, r#(snd elem))" 
    by auto
  then have branch_assms_inset: "(branch_assms, snd elem) \<in> set (lc_assump_generation_list qs new_assumps)"
    using deconstruct_prop by auto
  then have "set new_assumps \<subseteq> set branch_assms"
    using deconstruct_prop list_rec_prop branch_init_assms_subset
    by presburger
  have ris_var: "r = 0 \<or> (\<exists>i. lookup_assump_aux (Polynomial.lead_coeff r)new_assumps = Some i \<and> i \<noteq> 0) "
    using lc_assump_generation_inv[of new_assumps r a init_assumps] deconstruct_prop(1) 
    by auto
  then have r_prop: "r = 0 \<longleftrightarrow> eval_mpoly_poly val r = 0"
    by (metis \<open>set new_assumps \<subseteq> set branch_assms\<close> basic_trans_rules(31) eval_commutes eval_mpoly_poly_comm_ring_hom.hom_zero leading_coeff_0_iff local.Cons(3) lookup_assum_aux_mem satisfies_evaluation_nonzero)
  have "eval_mpoly_poly val (prod_list_var_gen (snd elem)) =
    prod_list_var_gen (map (eval_mpoly_poly val) (snd elem))"
    using Cons.hyps list_rec_prop
    using branch_assms_inset local.Cons(3) by blast 
  then show ?case using r_prop list_rec_prop(3)
    by (simp add: eval_mpoly_poly_comm_ring_hom.hom_mult) 
qed

lemma map_branch_poly_list:
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  shows "(map (eval_mpoly_poly val) qs) = (map (eval_mpoly_poly val) branch_poly_list)"
  using assms 
proof (induct qs arbitrary: branch_assms branch_poly_list init_assumps)
  case Nil
  then have "(branch_assms, branch_poly_list) \<in> set [(init_assumps, [])]"
    using lc_assump_generation_list.simps by auto
  then have "branch_poly_list = []"
    using in_set_member
    by simp 
  then show ?case 
    using Nil.prems(1)
    by meson 
next
  case (Cons a qs)
  let ?rec = "lc_assump_generation a init_assumps"
  have inset: "(branch_assms,branch_poly_list) \<in> set (
    concat (map (
      \<lambda>(new_assumps, r). (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec) ) ?rec ))"
    using Cons.prems lc_assump_generation_list.simps
    by auto 
  then obtain new_assumps r where deconstruct_prop:
    "(new_assumps, r) \<in> set ?rec"
    "(branch_assms,branch_poly_list) \<in> set (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec)"
    using inset
    by (metis (no_types, lifting) concat_map_in_set nth_mem prod.collapse split_def)
  then obtain elem list_rec where list_rec_prop:
    "list_rec = lc_assump_generation_list qs new_assumps"
    "elem \<in> set list_rec"
    "(branch_assms,branch_poly_list) = (fst elem, r#(snd elem))" 
    by auto
  then have branch_assms_inset: "(branch_assms, snd elem) \<in> set (lc_assump_generation_list qs new_assumps)"
    using deconstruct_prop by auto
  then have map_prop: "map (eval_mpoly_poly val) (qs) =
    map (eval_mpoly_poly val) (snd elem)" using Cons.hyps Cons.prems
    by blast
  have "set new_assumps \<subseteq> set branch_assms"
    using deconstruct_prop list_rec_prop branch_assms_inset branch_init_assms_subset 
    by presburger
  then have "eval_mpoly_poly val r = eval_mpoly_poly val a"
    using branch_poly_eval
    by (meson basic_trans_rules(31) deconstruct_prop(1) local.Cons(3)) 
  then show ?case 
    using map_prop list_rec_prop(3)
    by simp 
qed

lemma check_constant_degree_match:
  assumes "(a, q) \<in> set (lc_assump_generation init_q init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set a \<Longrightarrow> satisfies_evaluation val p n"
  shows "Polynomial.degree q = Polynomial.degree (eval_mpoly_poly val init_q)"
  using assms 
proof (induct init_q init_assumps arbitrary: q a rule: lc_assump_generation_induct )
  case (Base init_q init_assumps)
  then show ?case 
    using lc_assump_generation.simps
    by simp 
next
  case (Rec init_q init_assumps)
  then show ?case using lc_assump_generation.simps
    by (metis branch_poly_eval degree_0 degree_valuation eval_mpoly_poly_comm_ring_hom.hom_zero lc_assump_generation_inv lookup_assum_aux_mem) 
next
  case (Lookup0 init_q init_assumps)
  then show ?case  using lc_assump_generation.simps
    by (metis branch_poly_eval degree_0 degree_valuation eval_mpoly_poly_comm_ring_hom.hom_zero lc_assump_generation_inv lookup_assum_aux_mem) 
next
  case (LookupN0 init_q init_assumps r)
  then show ?case
    using lc_assump_generation.simps
    by (metis branch_poly_eval degree_0 degree_valuation eval_mpoly_poly_comm_ring_hom.hom_zero lc_assump_generation_inv lookup_assum_aux_mem) 
qed

lemma check_constant_degree_match_list:
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  shows "(check_all_const_deg_gen branch_poly_list) = (check_all_const_deg_gen (map (eval_mpoly_poly val) qs))"
  using assms
proof (induct qs arbitrary: branch_assms branch_poly_list init_assumps)
  case Nil
  then have "(branch_assms, branch_poly_list) \<in> set [(init_assumps, [])]"
    using lc_assump_generation_list.simps
    by auto
  then have "branch_poly_list = []"
    using in_set_member
    by simp 
  then show ?case
    by simp 
next
  case (Cons a qs)
  let ?rec = "lc_assump_generation a init_assumps"
  have inset: "(branch_assms,branch_poly_list) \<in> set (
    concat (map (
      \<lambda>(new_assumps, r). (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec) ) ?rec ))"
    using Cons.prems lc_assump_generation_list.simps
    by auto 
  then obtain new_assumps r where deconstruct_prop:
    "(new_assumps, r) \<in> set ?rec"
    "(branch_assms,branch_poly_list) \<in> set (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec)"
    using inset
    by (metis (no_types, lifting) concat_map_in_set nth_mem prod.collapse split_def)
  then obtain elem list_rec where list_rec_prop:
    "list_rec = lc_assump_generation_list qs new_assumps"
    "elem \<in> set list_rec"
    "(branch_assms,branch_poly_list) = (fst elem, r#(snd elem))" 
    by auto
  then have branch_assms_inset: "(branch_assms, snd elem) \<in> set (lc_assump_generation_list qs new_assumps)"
    using deconstruct_prop by auto
  then have ind_prop: "(check_all_const_deg_gen (snd elem)) = (check_all_const_deg_gen (map (eval_mpoly_poly val) qs))" using Cons.hyps Cons.prems
    by blast
  have "set new_assumps \<subseteq> set branch_assms"
    using deconstruct_prop list_rec_prop branch_assms_inset branch_init_assms_subset 
    by presburger
  then have "Polynomial.degree r = Polynomial.degree (eval_mpoly_poly val a)"
    using check_constant_degree_match
    by (meson basic_trans_rules(31) deconstruct_prop(1) local.Cons(3)) 
  then show ?case 
    using ind_prop list_rec_prop(3)
    by simp 
qed

lemma check_all_const_deg_match:
  shows "check_all_const_deg qs = check_all_const_deg_gen qs"
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then show ?case by auto
qed

lemma prod_list_var_match:
  shows "prod_list_var_gen qs = prod_list_var qs"
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then show ?case by auto
qed

lemma sign_lead_coeff_on_branch:
  assumes "(a, q) \<in> set (lc_assump_generation init_q init_assumps)"
  assumes "q \<noteq> 0"
  assumes "\<And>p n. (p,n) \<in> set a \<Longrightarrow> satisfies_evaluation val p n"
  shows "((Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a))) = 
   Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))"
  using assms 
proof (induct init_q init_assumps arbitrary: q a rule: lc_assump_generation_induct )
  case (Base init_q init_assumps)
  then show ?case using lc_assump_generation.simps
    by simp 
next
  case (Rec init_q init_assumps)
  let ?zero = "lc_assump_generation (one_less_degree init_q) ((Polynomial.lead_coeff init_q, (0::rat)) # init_assumps)"
  let ?one  = "((Polynomial.lead_coeff init_q, (1::rat)) # init_assumps, init_q)"
  let ?minus_one  = "((Polynomial.lead_coeff init_q, (-1::rat)) # init_assumps, init_q)"
  have inset: "(a, q) \<in> set (?one#?minus_one#?zero)"
    using Rec.hyps lc_assump_generation.simps Rec(4)
    by auto 
  { assume * : "(a, q) = ?one"
    then have h1: "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a) = (1::rat)"
      by auto
    have h2: "satisfies_evaluation val (Polynomial.lead_coeff q) (1)"
      using Rec.hyps
      by (metis "*" Pair_inject Rec.prems(3) list.set_intros(1)) 
    then have h3: "Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q)) = (1::int)"
      unfolding satisfies_evaluation_def eval_mpoly_def
      by (metis Sturm_Tarski.sign_def h2 lead_coeff_valuation of_int_hom.injectivity one_neq_zero satisfies_evaluation_def verit_comp_simplify(28))
        (* may take a second to load *)
    have "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a) = 
      ((Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))))"
      using h1 h3 
      by auto
  } moreover { 
    assume * : "(a, q) = ?minus_one"
    then have h1: "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a) = (-1::rat)"
      by auto
    have h2: "satisfies_evaluation val (Polynomial.lead_coeff q) (-1)"
      using Rec.hyps
      by (metis "*" Pair_inject Rec.prems(3) list.set_intros(1)) 
    then have h3: "rat_of_int (Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))) = (-1::rat)"
      unfolding satisfies_evaluation_def eval_mpoly_def
      by (metis Sturm_Tarski.sign_def degree_valuation eval_mpoly_def eval_mpoly_map_poly_comm_ring_hom.base.coeff_map_poly_hom eval_mpoly_poly_def h2 of_int_hom.hom_one of_int_hom.injectivity of_int_minus rel_simps(88) sign_uminus verit_comp_simplify(28))
        (* May take a second to load *)
    have "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a) = 
      ((Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))))"
      using h1 h3
      by (metis of_int_eq_iff of_rat_of_int_eq) 
  }
  moreover { 
    assume * : "(a, q) \<in> set ?zero"
    then have "(a, q)
    \<in> set (lc_assump_generation (Multiv_Poly_Props.one_less_degree init_q)
             ((Polynomial.lead_coeff init_q, 0) # init_assumps))"
      by auto 
    then have "set ((Polynomial.lead_coeff init_q, 0) # init_assumps) \<subseteq> set a "
      using lc_assump_generation_subset by presburger 
    then have "\<And>p n. (p, n) \<in> set ((Polynomial.lead_coeff init_q, 0) # init_assumps) \<Longrightarrow> satisfies_evaluation val p n"
      using Rec.prems by auto 
    then have "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a) = 
      Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q))"
      using Rec.hyps Rec.prems
      by (smt (verit, ccfv_SIG) "*" Sturm_Tarski.sign_cases more_arith_simps(10) neg_one_neq_one sign_uminus) 
      (* Takes a couple seconds to load *)
  }
  ultimately show ?case using lc_assump_generation.simps
      inset 
    by (smt (verit, del_insts) set_ConsD) (* Takes a second *)
next
  case (Lookup0 init_q init_assumps)
  then show ?case using lc_assump_generation.simps
    by auto

next
  case (LookupN0 init_q init_assumps r)
  then have match: "(a, q) = (init_assumps, init_q)"
    using lc_assump_generation.simps in_set_member by auto 
  then obtain i where i_prop: "i \<noteq> 0"
    "lookup_assump_aux (Polynomial.lead_coeff init_q) init_assumps = Some i"
    "(Polynomial.lead_coeff init_q, i) \<in> set init_assumps"
    using LookupN0.prems LookupN0.hyps
    by (meson lookup_assum_aux_mem)  
  then have "(Polynomial.lead_coeff init_q, i) \<in> set a"
    using match by auto
  then have sat_eval: "satisfies_evaluation val (Polynomial.lead_coeff init_q) i"
    using LookupN0(6) by blast
  have "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a)
   = Sturm_Tarski.sign i"
    using i_prop match lookup_assump_aux_subset_consistent_sign
    by simp
  then show ?case
    by (smt (verit, del_insts) LookupN0(6) LookupN0.prems(1) sat_eval branch_poly_eval i_prop(1) lead_coeff_valuation of_int_hom.injectivity satisfies_evaluation_def) 
qed

lemma sign_lead_coeff_on_branch_init:
  assumes "(a, q) \<in> set (lc_assump_generation init_q init_assumps)"
  assumes "q \<noteq> 0"
  assumes "\<And>p n. (p,n) \<in> set a \<Longrightarrow> satisfies_evaluation val p n"
  shows "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a) = 
   Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val init_q))"
  using sign_lead_coeff_on_branch branch_poly_eval
  by (metis assms(1) assms(2) assms(3)) 

lemma pos_limit_point_on_branch:
  assumes "(a, q) \<in> set (lc_assump_generation init_q init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set a \<Longrightarrow> satisfies_evaluation val p n"
  shows "rat_of_int (Sturm_Tarski.sign (sgn_pos_inf (eval_mpoly_poly val q))) = 
     (if q = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a))"
  using assms 
proof - 
  have "rat_of_int (Sturm_Tarski.sign (sgn_pos_inf (eval_mpoly_poly val q))) = 
    Sturm_Tarski.sign (Polynomial.lead_coeff (eval_mpoly_poly val q)) "
    unfolding sgn_pos_inf_def
    by auto
  then show ?thesis using sign_lead_coeff_on_branch assms
    by (smt (verit, del_insts) eval_mpoly_poly_comm_ring_hom.hom_zero leading_coeff_0_iff sign_simps(2))
      (* May take a few seconds to load *)
qed

lemma pos_limit_point_on_branch_init:
  assumes "(a, q) \<in> set (lc_assump_generation init_q init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set a \<Longrightarrow> satisfies_evaluation val p n"
  shows "rat_of_int (Sturm_Tarski.sign (sgn_pos_inf (eval_mpoly_poly val init_q))) = 
     (if q = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a))"
  using assms pos_limit_point_on_branch  sign_lead_coeff_on_branch_init
  using branch_poly_eval by force

lemma pos_limit_point_on_branch_list:
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  assumes "(pos_limit_branch, neg_limit_branch) = limit_points_on_branch (branch_assms, branch_poly_list)"
  shows "map rat_of_int (sgn_pos_inf_rat_list (map (eval_mpoly_poly val) qs)) = pos_limit_branch"
  using assms 
proof (induct qs arbitrary: pos_limit_branch neg_limit_branch branch_assms branch_poly_list init_assumps)
  case Nil
  then have "(branch_assms, branch_poly_list) \<in> set [(init_assumps, [])]"
    using lc_assump_generation_list.simps
    by auto
  then have "branch_poly_list = []"
    using in_set_member
    by simp 
  then show ?case using Nil.prems 
    unfolding eval_mpoly_poly_def sgn_pos_inf_rat_list_def
    by auto
next
  case (Cons a qs) 
  let ?rec = "lc_assump_generation a init_assumps"
  have inset: "(branch_assms,branch_poly_list) \<in> set (
    concat (map (
      \<lambda>(new_assumps, r). (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec) ) ?rec ))"
    using Cons.prems lc_assump_generation_list.simps
    by auto 
  then obtain new_assumps r where deconstruct_prop:
    "(new_assumps, r) \<in> set ?rec"
    "(branch_assms,branch_poly_list) \<in> set (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec)"
    using inset
    by (metis (no_types, lifting) concat_map_in_set nth_mem prod.collapse split_def)
  then obtain elem list_rec where list_rec_prop:
    "list_rec = lc_assump_generation_list qs new_assumps"
    "elem \<in> set list_rec"
    "(branch_assms,branch_poly_list) = (fst elem, r#(snd elem))" 
    by auto
  then have snd_elem_inset: "(branch_assms, snd elem) \<in> set (lc_assump_generation_list qs new_assumps)"
    using deconstruct_prop by auto
  obtain pos_limit_sublist neg_limit_sublist where sublist_prop:
    "(pos_limit_sublist, neg_limit_sublist) = limit_points_on_branch (branch_assms, snd elem)"
    by auto 
  then have ind_prop: "pos_limit_sublist = map rat_of_int (sgn_pos_inf_rat_list (map (eval_mpoly_poly val) qs))"
    using snd_elem_inset Cons.hyps Cons.prems
    by blast
  have sublist_connection: "pos_limit_branch = (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))#pos_limit_sublist"
    using Cons.prems(3) sublist_prop list_rec_prop(3)
    by simp 
  have list_prop: "map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_pos_inf x)))
     (map (eval_mpoly_poly val) (a#qs)) = 
  (rat_of_int (Sturm_Tarski.sign (sgn_pos_inf (eval_mpoly_poly val a)))) # map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_pos_inf x)))
     (map (eval_mpoly_poly val) qs)"
    by simp
  have tail_prop: "pos_limit_branch =
    (if r = 0 then 0
     else Sturm_Tarski.sign
           (lookup_assump (Polynomial.lead_coeff r) branch_assms)) #
      map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_pos_inf x)))
     (map (eval_mpoly_poly val) qs)"
    using sublist_connection ind_prop  unfolding sgn_pos_inf_rat_list_def
    by auto 
  have subs: "set new_assumps \<subseteq> set branch_assms"
    using deconstruct_prop list_rec_prop snd_elem_inset branch_init_assms_subset 
    by presburger
  then have r_sign: "rat_of_int (Sturm_Tarski.sign (sgn_pos_inf (eval_mpoly_poly val a))) = 
     (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps))"
    using pos_limit_point_on_branch_init deconstruct_prop(1) local.Cons(3) subsetD
    by (smt (verit, ccfv_threshold))
  have r_inv: "r = (0::rmpoly) \<or> (\<exists>i. (lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i \<and> i \<noteq> 0))"
    using lc_assump_generation_inv
    by (meson deconstruct_prop(1)) 
  have r_match: " (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps))
=  (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))"
  proof - 
    {assume *: "r = 0"
      then have "(if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps))
=  (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))"
        by auto 
    } moreover {assume *: "r \<noteq> 0"
      then obtain i1 where i1_prop: "lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i1 \<and> i1 \<noteq> 0"
        using r_inv by auto 
      then obtain i2 where i2_prop: "lookup_assump_aux (Polynomial.lead_coeff r) branch_assms = Some i2 \<and> i2 \<noteq> 0"
        using lookup_assump_aux_subset_consistency subs
        using Cons.prems(2) by blast 
      then have " Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps) = 
      Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms)"
        using lookup_assump_aux_subset_consistent_sign subs
          i1_prop i2_prop Cons.prems(2)  
      proof -
        obtain mm :: "real list \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> real mpoly" and rr :: "real list \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> rat" where
          "\<forall>x4 x5. (\<exists>v6 v7. (v6, v7) \<in> set x5 \<and> \<not> satisfies_evaluation x4 v6 v7) = ((mm x4 x5, rr x4 x5) \<in> set x5 \<and> \<not> satisfies_evaluation x4 (mm x4 x5) (rr x4 x5))"
          by moura
        then have "\<forall>ps rs psa p r ra. ((mm rs ps, rr rs ps) \<in> set ps \<and> \<not> satisfies_evaluation rs (mm rs ps) (rr rs ps) \<or> \<not> set psa \<subseteq> set ps \<or> lookup_assump_aux (Polynomial.lead_coeff p) psa \<noteq> Some r \<or> lookup_assump_aux (Polynomial.lead_coeff p) ps \<noteq> Some ra) \<or> (Sturm_Tarski.sign r) = Sturm_Tarski.sign ra"
          by (meson lookup_assump_aux_subset_consistent_sign)
        then have "(Sturm_Tarski.sign i1) = Sturm_Tarski.sign i2"
          using i1_prop i2_prop local.Cons(3) subs by blast
        then show ?thesis
          by (simp add: i1_prop i2_prop)
      qed
        (*  by (smt (verit, del_insts) lookup_assump.simps option.case(2)) *)
      then have "(if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps))
=  (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))"
        by auto
    }
    ultimately show ?thesis
      by auto
  qed
  then have "rat_of_int (Sturm_Tarski.sign (sgn_pos_inf (eval_mpoly_poly val a))) = 
     (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))"
    using r_sign r_match
    by fastforce 
  then have "pos_limit_branch = (rat_of_int (Sturm_Tarski.sign (sgn_pos_inf (eval_mpoly_poly val a)))) #
    (map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_pos_inf x)))
     (map (eval_mpoly_poly val) qs)) " 
    using tail_prop
    by (smt (verit, ccfv_threshold) list.inj_map_strong list.map(2) of_rat_hom.eq_iff) 
  then show ?case using  list_prop
    using sgn_pos_inf_rat_list_def 
    by (auto)
qed

lemma neg_limit_point_on_branch_init:
  assumes "(a, q) \<in> set (lc_assump_generation init_q init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set a \<Longrightarrow> satisfies_evaluation val p n"
  shows "rat_of_int (Sturm_Tarski.sign (sgn_neg_inf (eval_mpoly_poly val init_q))) = 
     (if q = 0 then 0 else (Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a))*(-1)^(Polynomial.degree q))"
proof - 
  have at_inf: "rat_of_int
     (Sturm_Tarski.sign  (sgn_class.sgn (Polynomial.lead_coeff (eval_mpoly_poly val init_q)))) =
    (if q = 0 then 0
     else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff q) a))"
    using assms  pos_limit_point_on_branch_init 
    unfolding sgn_pos_inf_def 
    by auto
  have "Polynomial.degree q = Polynomial.degree (eval_mpoly_poly val init_q)"
    using check_constant_degree_match assms by auto  
  then show ?thesis using at_inf
    unfolding sgn_neg_inf_def
    using Sturm_Tarski_casting degree_0 even_zero more_arith_simps(6) more_arith_simps(8) ring_1_class.minus_one_power_iff by auto
      (* Takes a couple seconds to load *)
qed

lemma neg_limit_point_on_branch_list:
  assumes "(branch_assms, branch_poly_list) \<in> set (lc_assump_generation_list qs init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set branch_assms \<Longrightarrow> satisfies_evaluation val p n"
  assumes "(pos_limit_branch, neg_limit_branch) = limit_points_on_branch (branch_assms, branch_poly_list)"
  shows "map rat_of_int (sgn_neg_inf_rat_list (map (eval_mpoly_poly val) qs)) = neg_limit_branch"
  using assms
proof (induct qs arbitrary: pos_limit_branch neg_limit_branch branch_assms branch_poly_list init_assumps)
  case Nil
  then have "(branch_assms, branch_poly_list) \<in> set [(init_assumps, [])]"
    using lc_assump_generation_list.simps
    by auto
  then have "branch_poly_list = []"
    using in_set_member
    by simp 
  then show ?case using Nil.prems 
    unfolding eval_mpoly_poly_def sgn_neg_inf_rat_list_def
    by auto
next
  case (Cons a qs) 
  let ?rec = "lc_assump_generation a init_assumps"
  have inset: "(branch_assms,branch_poly_list) \<in> set (
    concat (map (
      \<lambda>(new_assumps, r). (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec) ) ?rec ))"
    using Cons.prems lc_assump_generation_list.simps
    by auto 
  then obtain new_assumps r where deconstruct_prop:
    "(new_assumps, r) \<in> set ?rec"
    "(branch_assms,branch_poly_list) \<in> set (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec)"
    using inset
    by (metis (no_types, lifting) concat_map_in_set nth_mem prod.collapse split_def)
  then obtain elem list_rec where list_rec_prop:
    "list_rec = lc_assump_generation_list qs new_assumps"
    "elem \<in> set list_rec"
    "(branch_assms,branch_poly_list) = (fst elem, r#(snd elem))" 
    by auto
  then have snd_elem_inset: "(branch_assms, snd elem) \<in> set (lc_assump_generation_list qs new_assumps)"
    using deconstruct_prop by auto
  obtain pos_limit_sublist neg_limit_sublist where sublist_prop:
    "(pos_limit_sublist, neg_limit_sublist) = limit_points_on_branch (branch_assms, snd elem)"
    by auto 
  then have ind_prop_var: "neg_limit_sublist = map rat_of_int (sgn_neg_inf_rat_list (map (eval_mpoly_poly val) qs))"
    using snd_elem_inset Cons.hyps Cons.prems by blast
  then have ind_prop: "neg_limit_sublist = sgn_neg_inf_rat_list (map (eval_mpoly_poly val) qs)"
    by auto
  have sublist_connection: "pos_limit_branch = (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))#pos_limit_sublist"
    using Cons.prems(3) sublist_prop list_rec_prop(3)
    by simp 
  then have sublist_connection_var: "pos_limit_branch = (if r = 0 then 0 else (rat_of_int \<circ> Sturm_Tarski.sign) (lookup_assump (Polynomial.lead_coeff r) branch_assms))#pos_limit_sublist"
    using Cons.prems(3) sublist_prop list_rec_prop(3)
    by simp 
  have list_prop: "map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_neg_inf x)))
     (map (eval_mpoly_poly val) (a#qs)) = 
  (rat_of_int (Sturm_Tarski.sign (sgn_neg_inf (eval_mpoly_poly val a)))) # map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_neg_inf x)))
     (map (eval_mpoly_poly val) qs)"
    by simp
  have ind_prop_var2: "neg_limit_sublist =
     (map (\<lambda>x. (rat_of_int \<circ> Sturm_Tarski.sign) (sgn_neg_inf x))
       (map (eval_mpoly_poly val) qs))"
    using ind_prop_var unfolding sgn_neg_inf_rat_list_def 
    by auto
  have "neg_limit_branch =
    (if r = 0 then (0::rat)
     else ((rat_of_int \<circ> Sturm_Tarski.sign)
           (lookup_assump (Polynomial.lead_coeff r) branch_assms)*(-1)^(Polynomial.degree r))) #
   map (\<lambda>x. ((rat_of_int \<circ> Sturm_Tarski.sign) (sgn_neg_inf x)))
     (map (eval_mpoly_poly val) qs)"
    using  sublist_connection_var ind_prop_var2 local.Cons(4)  unfolding sgn_neg_inf_rat_list_def 
    unfolding limit_points_on_branch.simps
    by (metis (no_types, lifting) limit_points_on_branch.simps list.simps(9) list_rec_prop(3) prod.simps(1) sublist_prop)
  then have tail_prop_helper: "neg_limit_branch =
    (if r = 0 then 0
     else rat_of_int (Sturm_Tarski.sign
           (lookup_assump (Polynomial.lead_coeff r) branch_assms)*(-1)^(Polynomial.degree r))) #
   map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_neg_inf x)))
     (map (eval_mpoly_poly val) qs)"
    by auto
  then have tail_prop: "neg_limit_branch =
    (if r = 0 then 0
     else Sturm_Tarski.sign
           (lookup_assump (Polynomial.lead_coeff r) branch_assms)*(-1)^(Polynomial.degree r)) #
      map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_neg_inf x)))
     (map (eval_mpoly_poly val) qs)"
    by (smt (verit, ccfv_threshold) list.map(2) of_int_hom.hom_zero of_rat_of_int_eq)
  have subs: "set new_assumps \<subseteq> set branch_assms"
    using deconstruct_prop list_rec_prop snd_elem_inset branch_init_assms_subset 
    by presburger
  then have r_sign: "rat_of_int (Sturm_Tarski.sign (sgn_neg_inf (eval_mpoly_poly val a))) = 
     (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps)*(-1)^(Polynomial.degree r))"
    using neg_limit_point_on_branch_init deconstruct_prop(1) local.Cons(3) subsetD
    by (smt (verit, ccfv_threshold))
  have r_inv: "r = (0::rmpoly) \<or> (\<exists>i. (lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i \<and> i \<noteq> 0))"
    using lc_assump_generation_inv
    by (meson deconstruct_prop(1)) 
  have r_match_pre: " (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps))
    =  (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))"
  proof - 
    {assume *: "r = 0"
      then have "(if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps))
        =  (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))"
        by auto 
    } moreover {assume *: "r \<noteq> 0"
      then obtain i1 where i1_prop: "lookup_assump_aux (Polynomial.lead_coeff r) new_assumps = Some i1 \<and> i1 \<noteq> 0"
        using r_inv by auto 
      then obtain i2 where i2_prop: "lookup_assump_aux (Polynomial.lead_coeff r) branch_assms = Some i2 \<and> i2 \<noteq> 0"
        using lookup_assump_aux_subset_consistency subs
        using Cons.prems(2) by blast 
      then have "Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps) = 
      Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms)"
        using lookup_assump_aux_subset_consistent_sign subs
          i1_prop i2_prop Cons.prems(2)
      proof -
        obtain mm :: "real list \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> real mpoly" and rr :: "real list \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> rat" where
          "\<forall>x4 x5. (\<exists>v6 v7. (v6, v7) \<in> set x5 \<and> \<not> satisfies_evaluation x4 v6 v7) = ((mm x4 x5, rr x4 x5) \<in> set x5 \<and> \<not> satisfies_evaluation x4 (mm x4 x5) (rr x4 x5))"
          by moura
        then have "\<forall>ps rs psa p r ra. ((mm rs ps, rr rs ps) \<in> set ps \<and> \<not> satisfies_evaluation rs (mm rs ps) (rr rs ps) \<or> \<not> set psa \<subseteq> set ps \<or> lookup_assump_aux (Polynomial.lead_coeff p) psa \<noteq> Some r \<or> lookup_assump_aux (Polynomial.lead_coeff p) ps \<noteq> Some ra) \<or> (Sturm_Tarski.sign r) = Sturm_Tarski.sign ra"
          by (meson lookup_assump_aux_subset_consistent_sign)
        then have "(Sturm_Tarski.sign i1) = Sturm_Tarski.sign i2"
          using i1_prop i2_prop local.Cons(3) subs by blast
        then show ?thesis
          by (simp add: i1_prop i2_prop)
      qed
        (*  by (smt (verit, del_insts) lookup_assump.simps option.case(2)) *)
      then have "(if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps))
        =  (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms))"
        by auto
    }
    ultimately show ?thesis
      by auto
  qed
  then have r_match: "(if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) new_assumps)*(-1)^(Polynomial.degree r))
=  (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms)*(-1)^(Polynomial.degree r))"
    by metis
  then have "rat_of_int (Sturm_Tarski.sign (sgn_neg_inf (eval_mpoly_poly val a))) = 
     (if r = 0 then 0 else Sturm_Tarski.sign (lookup_assump (Polynomial.lead_coeff r) branch_assms)*(-1)^(Polynomial.degree r))"
    using r_sign r_match
    by fastforce 
  then have "neg_limit_branch = (rat_of_int (Sturm_Tarski.sign (sgn_neg_inf (eval_mpoly_poly val a)))) #
    (map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_neg_inf x)))
     (map (eval_mpoly_poly val) qs)) " 
    using tail_prop tail_prop_helper
    by (simp add: of_rat_hom.injectivity)
  then show ?case using  list_prop
    using sgn_neg_inf_rat_list_def
    by auto
qed

lemma complex_rat_casting_lemma:
  fixes a:: "int list"
  fixes b:: "rat list"
  shows "map complex_of_int a = map of_rat b \<Longrightarrow> map rat_of_int a = b"
  by (metis (no_types, lifting) list.inj_map_strong list.map_comp of_rat_hom.injectivity of_rat_of_int)

lemma complex_rat_casting_lemma_sets:
  fixes a:: "rat list list"
  fixes b1:: "int list"
  fixes b2:: "int list"
  fixes c:: "rat list list"
  assumes "set (map (map of_rat) a) \<union> {map complex_of_int b1, map complex_of_int b2} 
    = set (map (map of_rat) c)"
  shows "set a \<union> {map rat_of_int b1, map rat_of_int b2} = set c"
proof - 
  have "map complex_of_int b1 \<in> set (map (map of_rat) c)"
    using assms by auto 
  then have h1: "map rat_of_int b1 \<in> set c"
    using complex_rat_casting_lemma by auto
  have "map complex_of_int b2 \<in> set (map (map of_rat) c)"
    using assms by auto 
  then have h2: "map rat_of_int b2 \<in> set c"
    using complex_rat_casting_lemma by auto
  have set_lem: "\<And> a b c . a \<union> b = c \<Longrightarrow> a \<subseteq> c"
    by blast
  have "set (map (map of_rat) a) \<subseteq> set (map (map of_rat) c)"
    using assms set_lem[of "set (map (map of_rat) a)" "{map complex_of_int b1, map complex_of_int b2}" "set (map (map of_rat) c)"]
    by auto
  then have "\<And>x. x \<in> set (map (map of_rat) a) \<Longrightarrow> x \<in> set (map (map of_rat) c)"
    by auto 
  then have h3: "\<And>x. x \<in> set a \<Longrightarrow> x \<in> set c"
    using complex_rat_casting_lemma
    by fastforce 
  have h4_a: "\<And>x. x \<in> set (map (map of_rat) c) \<Longrightarrow>
         x \<noteq> map complex_of_int b1 \<Longrightarrow> x \<notin> set (map (map of_rat) a) \<Longrightarrow> x = map complex_of_int b2"
    using assms
    by blast 
  have h4: "\<And>x. x \<in> set c \<Longrightarrow>
         x \<noteq> map rat_of_int b1 \<Longrightarrow> x \<notin> set a \<Longrightarrow> x = map rat_of_int b2"
  proof - 
    fix x
    assume a1: "x \<in> set c"
    assume a2: "x \<noteq> map rat_of_int b1" 
    assume a3: "x \<notin> set a"
    have "((map of_rat x)::complex list) \<in> set (map (map of_rat) c)"
      using a1 by auto 
    then have impl: "((map of_rat x)::complex list) \<noteq> map complex_of_int b1 \<Longrightarrow> (map of_rat x) \<notin> set (map (map of_rat) a) \<Longrightarrow> (map of_rat x) = map complex_of_int b2"
      using h4_a[of "((map of_rat x)::complex list)"]
      using a3 imageE inj_map_eq_map list.set_map of_rat_hom.inj_f by fastforce 
    have impl_h1: "((map of_rat x)::complex list) \<noteq> map complex_of_int b1"
      using a2 complex_rat_casting_lemma
      by metis
    have impl_h2: "(map of_rat x) \<notin> set (map (map of_rat) a)"
      using a3 complex_rat_casting_lemma by (auto) 
    then have "(map of_rat x) = map complex_of_int b2"
      using impl impl_h1 impl_h2 by auto 
    then show "x = map rat_of_int b2"
      using complex_rat_casting_lemma by metis 
  qed
  show ?thesis using h1 h2 h3 h4 by auto
qed

lemma complex_rat_casting_lemma_sets2:
  shows "{map rat_of_int
    (map (\<lambda>x. Sturm_Tarski.sign (sgn_neg_inf x))
      (map (eval_mpoly_poly val) qs)),
   map rat_of_int
    (map (\<lambda>x. Sturm_Tarski.sign (sgn_pos_inf x))
      (map (eval_mpoly_poly val) qs))} = {map (\<lambda>x. (rat_of_int \<circ> Sturm_Tarski.sign) (sgn_neg_inf x))
      (map (eval_mpoly_poly val) qs),
     map (\<lambda>x. (rat_of_int \<circ> Sturm_Tarski.sign) (sgn_pos_inf x))
      (map (eval_mpoly_poly val) qs)}"
proof - 
  have h1: "map rat_of_int
    (map (\<lambda>x. Sturm_Tarski.sign (sgn_neg_inf x))
      (map (eval_mpoly_poly val) qs)) = map (\<lambda>x. (rat_of_int \<circ> Sturm_Tarski.sign) (sgn_neg_inf x))
      (map (eval_mpoly_poly val) qs)"
    by auto
  have h2: "map rat_of_int
    (map (\<lambda>x. Sturm_Tarski.sign (sgn_pos_inf x))
      (map (eval_mpoly_poly val) qs)) = map (\<lambda>x. (rat_of_int \<circ> Sturm_Tarski.sign) (sgn_pos_inf x))
      (map (eval_mpoly_poly val) qs)"
    by auto
  show ?thesis using h1 h2
    by auto 
qed

lemma sign_determination_inner_gives_noncomp_signs_at_roots:
  assumes "(assumps, signs) \<in> set (sign_determination_inner qs init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "set signs = (consistent_sign_vectors_R (map (eval_mpoly_poly val) qs) UNIV)"
proof - 
  have elem_in_set: "(assumps, signs) \<in> set (let branches = lc_assump_generation_list qs init_assumps  in
    concat (map (\<lambda>branch. 
    let poly_p_branch = poly_p_in_branch branch;
        (pos_limit_branch, neg_limit_branch) = limit_points_on_branch branch;
        calculate_data_branch = extract_signs (calculate_data_assumps_M poly_p_branch (snd branch) (fst branch))
     in map (\<lambda>(a, signs). (a, pos_limit_branch#neg_limit_branch#signs)) calculate_data_branch
    ) branches))"
    using assms 
    by auto
  obtain branch where branch_prop: "branch \<in> set (lc_assump_generation_list qs init_assumps)"
    "(assumps, signs) \<in> set (
    let poly_p_branch = poly_p_in_branch branch;
        (pos_limit_branch, neg_limit_branch) = limit_points_on_branch branch;
        calculate_data_branch = extract_signs (calculate_data_assumps_M poly_p_branch (snd branch) (fst branch))
    in map (\<lambda>(a, signs). (a, pos_limit_branch#neg_limit_branch#signs)) calculate_data_branch)"
    using elem_in_set
    by auto
  then obtain branch_assms branch_poly_list where branch_is: 
    "branch = (branch_assms, branch_poly_list)"
    using poly_p_in_branch.cases by blast
  then obtain calculate_data_branch poly_p_branch pos_limit_branch neg_limit_branch
    where branch_prop_expanded:
      "poly_p_branch = poly_p_in_branch branch"
      "(pos_limit_branch, neg_limit_branch) = limit_points_on_branch branch"
      "calculate_data_branch = extract_signs (calculate_data_assumps_M poly_p_branch branch_poly_list branch_assms)"
      "branch \<in> set (lc_assump_generation_list qs init_assumps)"
      "(assumps, signs) \<in> set (
       map (\<lambda>(a, signs). (a, pos_limit_branch#neg_limit_branch#signs)) calculate_data_branch)"
    using branch_prop
    by (metis (no_types, lifting) case_prod_beta fst_conv prod.exhaust_sel snd_conv)
  obtain calc_a calc_signs where calc_prop:
    "(calc_a, calc_signs) \<in> set calculate_data_branch"
    "(assumps, signs) = (calc_a, pos_limit_branch#neg_limit_branch#calc_signs)"
    using in_set_member branch_prop_expanded(5)
    by auto
  then have branch_assms_subset: "set branch_assms \<subseteq> set assumps" 
    using branch_prop_expanded(3) extract_signs_M_subset
    by blast
  have "set init_assumps \<subseteq> set branch_assms"
    using branch_is branch_prop(1) branch_init_assms_subset
    by blast
  have assumps_calc_a: "assumps = calc_a"
    using calc_prop by auto 
  let ?poly_p_branch = "poly_p_in_branch (branch_assms, branch_poly_list)"
  have nonz_poly_p: "eval_mpoly_poly val ?poly_p_branch \<noteq> 0"
    using poly_p_nonzero_on_branch
    using \<open>set branch_assms \<subseteq> set assumps\<close> assms(2) branch_is branch_prop(1) by blast 
  have map_branch_poly_list: "(map (eval_mpoly_poly val) qs) = (map (eval_mpoly_poly val) branch_poly_list)"
    using map_branch_poly_list
    using assms(2) branch_assms_subset branch_is branch_prop(1) by blast 
  have "(calc_a, calc_signs)
    \<in> set (calculate_data_to_signs (calculate_data_assumps_M poly_p_branch branch_poly_list branch_assms))"
    using calc_prop branch_prop_expanded calc_data_to_signs_and_extract_signs
    by metis
  then have "(assumps, calc_signs)
    \<in> set (calculate_data_to_signs (calculate_data_assumps_M poly_p_branch branch_poly_list branch_assms))"
    using assumps_calc_a by auto  
  then have "set calc_signs = set(characterize_consistent_signs_at_roots (eval_mpoly_poly val ?poly_p_branch) (map (eval_mpoly_poly val) branch_poly_list))"
    using nonz_poly_p calculate_data_assumps_gives_noncomp_signs_at_roots[of assumps signs poly_p_branch branch_poly_list branch_assms val ]
    using assms(2) branch_is branch_prop_expanded(1) calculate_data_assumps_gives_noncomp_signs_at_roots by blast
  then have calc_signs_is: "set calc_signs = set(characterize_consistent_signs_at_roots (eval_mpoly_poly val ?poly_p_branch) (map (eval_mpoly_poly val) qs))"
    using map_branch_poly_list by auto
  have poly_p_is: "poly_p_in_branch (branch_assms, branch_poly_list) = (if (check_all_const_deg_gen branch_poly_list = True) then  [:0, 1:] else 
  (pderiv (prod_list_var_gen branch_poly_list)) * (prod_list_var_gen branch_poly_list))"
    by auto 
  have const_match: "(check_all_const_deg_gen branch_poly_list) = (check_all_const_deg_gen (map (eval_mpoly_poly val) qs))"
    using check_constant_degree_match_list
    using assms(2) branch_assms_subset branch_is branch_prop(1) by blast 
  have "eval_mpoly_poly val (prod_list_var_gen branch_poly_list) =
    prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list)"
    using eval_prod_list_var_gen_match
    using assms(2) branch_assms_subset branch_is branch_prop(1) by blast
  then have same_prod:  "eval_mpoly_poly val ((pderiv (prod_list_var_gen branch_poly_list)) * (prod_list_var_gen branch_poly_list))
= pderiv (prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list)) * (prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list))"
    by (metis eval_mpoly_poly_comm_ring_hom.hom_mult pderiv_commutes)
  {assume *: "check_all_const_deg_gen branch_poly_list = True"
    then have "?poly_p_branch = [: 0, 1 :]"
      using poly_p_is by presburger
    then have "(eval_mpoly_poly val ?poly_p_branch) = [:0, 1:]"
      unfolding eval_mpoly_poly_def
      by auto
    then have "(eval_mpoly_poly val ?poly_p_branch) =  (poly_f_nocrb (map (eval_mpoly_poly val) qs))"
      unfolding poly_f_nocrb_def using const_match check_all_const_deg_match "*" 
      by presburger
  } 
  moreover {assume *: "check_all_const_deg_gen branch_poly_list = False"
    then have "(eval_mpoly_poly val ?poly_p_branch)  = pderiv (prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list)) * (prod_list_var_gen (map (eval_mpoly_poly val) branch_poly_list))"
      using poly_p_is same_prod by auto 
    then have h1: "(eval_mpoly_poly val ?poly_p_branch)  = pderiv (prod_list_var_gen (map (eval_mpoly_poly val) qs)) * (prod_list_var_gen (map (eval_mpoly_poly val) qs))"
      using map_branch_poly_list
      by presburger 
    have "(check_all_const_deg (map (eval_mpoly_poly val) qs) = False) "
      using * const_match check_all_const_deg_match by auto
    then have "(eval_mpoly_poly val ?poly_p_branch) =  (poly_f_nocrb (map (eval_mpoly_poly val) qs))"
      using h1 prod_list_var_match
      unfolding poly_f_nocrb_def
      by metis 
  }
  ultimately have poly_branch_no_crb_connect: "(eval_mpoly_poly val ?poly_p_branch) =  (poly_f_nocrb (map (eval_mpoly_poly val) qs))"
    by auto 
  let ?eval_qs = "(map (eval_mpoly_poly val) qs)"
  have "set calc_signs =
    set (characterize_consistent_signs_at_roots (poly_f_nocrb ?eval_qs) ?eval_qs)"
    using poly_branch_no_crb_connect calc_signs_is
    by presburger 
      (* Use Renegar_Modified *)
  then have calc_signs_relation: "(set calc_signs) \<union> {sgn_neg_inf_rat_list ?eval_qs, sgn_pos_inf_rat_list ?eval_qs} =
    set (characterize_consistent_signs_at_roots (poly_f ?eval_qs) ?eval_qs)"
    using poly_f_ncrb_connection[of ?eval_qs] 
    by auto
      (* Some minor casting details *)
  then have "set calc_signs \<union>
    {map rat_of_int
      (sgn_neg_inf_rat_list (map (eval_mpoly_poly val) qs)),
     map rat_of_int
      (sgn_pos_inf_rat_list (map (eval_mpoly_poly val) qs))} =
    set (characterize_consistent_signs_at_roots
          (poly_f (map (eval_mpoly_poly val) qs))
          (map (eval_mpoly_poly val) qs))"
    unfolding sgn_neg_inf_rat_list2_def sgn_pos_inf_rat_list2_def 
    using complex_rat_casting_lemma_sets[of calc_signs "(sgn_neg_inf_rat_list (map (eval_mpoly_poly val) qs))" "(sgn_pos_inf_rat_list (map (eval_mpoly_poly val) qs))" 
        "(characterize_consistent_signs_at_roots (poly_f (map (eval_mpoly_poly val) qs)) (map (eval_mpoly_poly val) qs))"]  
    by (auto) 
  then have calc_signs_relation_var: "(set calc_signs) \<union> ({sgn_neg_inf_rat_list2 ?eval_qs, sgn_pos_inf_rat_list2 ?eval_qs}::rat list set) =
    set (characterize_consistent_signs_at_roots (poly_f ?eval_qs) ?eval_qs)"
    unfolding sgn_neg_inf_rat_list2_def sgn_pos_inf_rat_list2_def sgn_neg_inf_rat_list_def sgn_pos_inf_rat_list_def
    using complex_rat_casting_lemma_sets2
    by auto
  have pos_inf: "sgn_pos_inf_rat_list ?eval_qs = pos_limit_branch"
    using branch_prop_expanded(2) pos_limit_point_on_branch_list
    using assms(2) branch_assms_subset branch_is branch_prop(1)
    by (smt (verit, ccfv_threshold) basic_trans_rules(31) list.map_comp of_rat_of_int)
  then have pos_inf_var: "sgn_pos_inf_rat_list2 ?eval_qs = pos_limit_branch"
    unfolding sgn_pos_inf_rat_list2_def 
    using complex_rat_casting_lemma[of "(sgn_pos_inf_rat_list (map (eval_mpoly_poly val) qs))" pos_limit_branch]
    unfolding sgn_pos_inf_rat_list_def by auto
  have neg_inf: "sgn_neg_inf_rat_list ?eval_qs = neg_limit_branch"
    using branch_prop_expanded(2) neg_limit_point_on_branch_init
    using assms(2) branch_assms_subset branch_is branch_prop(1)
    by (smt (verit, ccfv_SIG) basic_trans_rules(31) list.map_comp neg_limit_point_on_branch_list of_rat_of_int)
  then have neg_inf_var: "sgn_neg_inf_rat_list2 ?eval_qs = neg_limit_branch"
    unfolding sgn_neg_inf_rat_list2_def 
    using complex_rat_casting_lemma[of "(sgn_neg_inf_rat_list (map (eval_mpoly_poly val) qs))" neg_limit_branch]
    unfolding sgn_neg_inf_rat_list_def 
    by auto 
  have "set signs = set (characterize_consistent_signs_at_roots (poly_f ?eval_qs) ?eval_qs)"
    using calc_signs_relation_var pos_inf_var neg_inf_var calc_prop(2)
    unfolding sgn_neg_inf_rat_list2_def sgn_pos_inf_rat_list2_def
    by auto
  then show "set signs = (consistent_sign_vectors_R (map (eval_mpoly_poly val) qs) UNIV)"
    using find_consistent_signs_at_roots_R poly_f_ncrb_connection calc_signs_is 
      main_step_R
    by (metis find_consistent_signs_R_def poly_f_nonzero) 
qed

subsection "Completeness"

(* This is the branch where all of the leading coefficients satisfy
the given sign conditions.  *)
lemma lc_assump_generation_valuation:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "\<exists>branch \<in> set (lc_assump_generation q init_assumps).
      set (fst branch) \<subseteq> set (init_assumps) \<union> set
      (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
  using assms
proof (induct q init_assumps rule: lc_assump_generation_induct )
  case (Base q assumps)
  then show ?case 
    using lc_assump_generation.simps by auto
next
  case (Rec q assumps)
  let ?zero = "lc_assump_generation (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # assumps)"
  let ?one  = "((Polynomial.lead_coeff q, (1::rat)) # assumps, q)"
  let ?minus_one  = "((Polynomial.lead_coeff q, (-1::rat)) # assumps, q)"
  have set_is: "set (lc_assump_generation q assumps) = set (?one#?minus_one#?zero)"
    using Rec.hyps Rec(4) lc_assump_generation.simps by auto 
  let ?lc = "(Polynomial.lead_coeff q)"
  have eo: "satisfies_evaluation val ?lc (0::rat) \<or> satisfies_evaluation val ?lc (1::rat) \<or> satisfies_evaluation val ?lc (-1::rat)"
    unfolding satisfies_evaluation_def eval_mpoly_def Sturm_Tarski.sign_def by auto
  {assume *: "satisfies_evaluation val ?lc (1::rat) "
    then have "1 = mpoly_sign val (Polynomial.lead_coeff q)"
      unfolding satisfies_evaluation_def eval_mpoly_def mpoly_sign_def Sturm_Tarski.sign_def
      by simp
    then have "(Polynomial.lead_coeff q, 1)  \<in> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      by (simp add: Rec(1) coeff_in_coeffs)
    then have "set (fst ?one) \<subseteq> set assumps \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      by auto
    then have " \<exists>branch\<in>set (lc_assump_generation q assumps).
          set (fst branch) \<subseteq> set assumps \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      using set_is by auto
  } moreover
  {assume *: "satisfies_evaluation val ?lc (-1::rat) "
    then have "-1 = mpoly_sign val (Polynomial.lead_coeff q)"
      unfolding satisfies_evaluation_def eval_mpoly_def mpoly_sign_def Sturm_Tarski.sign_def
      by (smt (z3) of_int_1 of_int_minus rel_simps(66) zero_neq_neg_one)
    then have "(Polynomial.lead_coeff q, -1)  \<in> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      by (simp add: Rec(1) coeff_in_coeffs)
    then have "set (fst ?minus_one) \<subseteq> set assumps \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      by auto
    then have " \<exists>branch\<in>set (lc_assump_generation q assumps).
          set (fst branch) \<subseteq> set assumps \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      using set_is by auto
  } moreover {assume *: "satisfies_evaluation val ?lc (0::rat) "
    then have "\<exists>branch\<in>set (lc_assump_generation (Multiv_Poly_Props.one_less_degree q) ((Polynomial.lead_coeff q, 0) # assumps)).
       set (fst branch)
       \<subseteq> set ((Polynomial.lead_coeff q, 0) # assumps) \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)))"
      using lc_assump_generation.simps
      using Rec(3) Rec(4) by fastforce 
    then obtain branch where branch_prop: "branch\<in>set (lc_assump_generation (Multiv_Poly_Props.one_less_degree q) ((Polynomial.lead_coeff q, 0) # assumps))"
      "set (fst branch)
       \<subseteq> set ((Polynomial.lead_coeff q, 0) # assumps) \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)))"
      by auto
    then have branch_prop_2: "branch\<in>set ?zero"
      by auto
    have "0 = mpoly_sign val (Polynomial.lead_coeff q)" using *
      unfolding satisfies_evaluation_def eval_mpoly_def mpoly_sign_def Sturm_Tarski.sign_def
      by simp
    then have lc_sign: "(Polynomial.lead_coeff q, 0) \<in> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      by (simp add: Rec(1) coeff_in_coeffs)
    {assume **: "Multiv_Poly_Props.one_less_degree q \<noteq> 0"
      then have "set (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)) \<subseteq> set (Polynomial.coeffs q)"
        using coeff_one_less_degree_subset unfolding Polynomial.coeffs_def
        by blast
      then have "set (fst branch) \<subseteq> set assumps \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
        using branch_prop
        by (smt (verit, del_insts) UnCI UnE lc_sign imageE image_eqI list.set_map set_ConsD subset_code(1)) 
      then have "\<exists>branch\<in>set (lc_assump_generation q assumps).
       set (fst branch)          
       \<subseteq> set assumps \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
        using  branch_prop_2
        using set_is by force 
    }
    moreover {assume **: "Multiv_Poly_Props.one_less_degree q = 0"
      then have "\<exists>branch\<in>set (lc_assump_generation q assumps).
         set (fst branch) \<subseteq> set assumps \<union>
            set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
        using Rec.hyps(2) UnCI lc_sign insert_subset lc_assump_generation.elims list.set(2) option.case(1) prod.sel(1) subsetI
        by (metis (no_types, lifting))
    }
    ultimately have " \<exists>branch\<in>set (lc_assump_generation q assumps).
          set (fst branch) \<subseteq> set assumps \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      by auto
  }
  ultimately show ?case using eo by auto 
next
  case (Lookup0 q assumps)
  then obtain branch where branch_prop:"branch\<in>set (lc_assump_generation (Multiv_Poly_Props.one_less_degree q) assumps)"
    "set (fst branch)
       \<subseteq> set assumps \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)))"
    by auto
  have same_gen: "lc_assump_generation (one_less_degree q) assumps = lc_assump_generation q assumps"
    using Lookup0.hyps lc_assump_generation.simps by auto
  then have branch_prop_2 :"branch\<in>set (lc_assump_generation q assumps)"
    using branch_prop(1) by auto
  {assume *: "Multiv_Poly_Props.one_less_degree q \<noteq> 0"
    then have "set (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)) \<subseteq> set (Polynomial.coeffs q)"
      using coeff_one_less_degree_subset unfolding Polynomial.coeffs_def
      by blast
    then have "set (fst branch)          
       \<subseteq> set assumps \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      using branch_prop_2 branch_prop(2) by auto
    then have "\<exists>branch\<in>set (lc_assump_generation q assumps).
       set (fst branch)          
       \<subseteq> set assumps \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      using branch_prop_2
      by auto
  }
  moreover {assume *: "Multiv_Poly_Props.one_less_degree q = 0"
    then have "\<exists>branch\<in>set (lc_assump_generation q assumps).
       set (fst branch)
       \<subseteq> set assumps \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs q))"
      by (simp add: Lookup0(2) lc_assump_generation.simps)
  }
  ultimately show ?case 
    by force 
next
  case (LookupN0 q assumps r)
  then show ?case using lc_assump_generation.simps
    by simp 
qed

lemma lc_assump_generation_valuation_satisfies_eval:
  fixes q:: "rmpoly"
  assumes "(p,n) \<in> set (map (\<lambda>x. (x, mpoly_sign val x)) ell)"
  shows "satisfies_evaluation val p n"
proof - 
  obtain c where c_prop: "c \<in> set ell"
    "(p, n) = (c, mpoly_sign val c)"
    using assms by auto
  have "satisfies_evaluation val c (mpoly_sign val c)"
    unfolding satisfies_evaluation_def mpoly_sign_def eval_mpoly_def
      Sturm_Tarski.sign_def by auto
  then show ?thesis
    using c_prop by auto
qed

(* relate lc_assump_generation_list to lc_assump_generation *)
lemma lc_assump_generation_list_valuation:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "\<exists>branch \<in> set (lc_assump_generation_list qs init_assumps).
      set (fst branch) \<subseteq> set (init_assumps) \<union> set
      (map (\<lambda>x. (x, mpoly_sign val x)) (coeffs_list qs))"
  using assms
proof (induct qs arbitrary: init_assumps)
  case Nil
  then show ?case 
    using lc_assump_generation_list.simps
    by simp 
next
  case (Cons a qs)
  then obtain branch_a where branch_a_prop: "branch_a \<in> set (lc_assump_generation a init_assumps)"
    "set (fst branch_a) \<subseteq> set (init_assumps) \<union> set
      (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs a))"
    using lc_assump_generation_valuation
    by blast 
  then obtain branch_a_assms branch_a_poly where branch_a_is: "branch_a = (branch_a_assms, branch_a_poly)"
    "set (branch_a_assms) \<subseteq> set (init_assumps) \<union> set
      (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs a))"
    by (meson prod.exhaust_sel)
  have inset: "set (map (\<lambda>elem. (fst elem, branch_a_poly#(snd elem))) (lc_assump_generation_list qs branch_a_assms)) 
    \<subseteq> set (lc_assump_generation_list (a#qs) init_assumps)"
    using lc_assump_generation_list.simps branch_a_is(1) branch_a_prop(1)
    by auto
  have "\<And>p n. (p,n) \<in> set branch_a_assms \<Longrightarrow> satisfies_evaluation val p n"
    using lc_assump_generation_valuation_satisfies_eval branch_a_is(1) fst_conv local.Cons(2) Set.basic_monos(7) UnE
  proof -
    fix p :: "real mpoly" and n :: rat
    assume "(p, n) \<in> set branch_a_assms"
    then show "satisfies_evaluation val p n"
      by (meson UnE lc_assump_generation_valuation_satisfies_eval Set.basic_monos(7) branch_a_is(2) local.Cons(2))
  qed
  then obtain branch where branch_props:
    "branch\<in>set (lc_assump_generation_list qs branch_a_assms)"
    "set (fst branch)
       \<subseteq> set branch_a_assms \<union>
          set (map (\<lambda>x. (x, mpoly_sign val x)) (coeffs_list qs))"
    using Cons.hyps[of branch_a_assms] by auto
  then have branch_inset:
    "(fst branch, branch_a_poly#(snd branch))
    \<in> set (lc_assump_generation_list (a#qs) init_assumps)"
    using inset
    by auto
  then have subset_h: "set (fst branch) \<subseteq> set (init_assumps) \<union> (set
      (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs a))
    \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (coeffs_list qs)))"
    using branch_props(2) branch_a_is(2) by auto
  have "coeffs_list (a # qs) = (Polynomial.coeffs a) @ (coeffs_list qs)"
    unfolding coeffs_list_def by auto
  then have same_set:
    "set (map (\<lambda>x. (x, mpoly_sign val x)) (coeffs_list (a#qs))) = (set
      (map (\<lambda>x. (x, mpoly_sign val x)) (Polynomial.coeffs a))
    \<union> set (map (\<lambda>x. (x, mpoly_sign val x)) (coeffs_list qs)))"
    by auto
  then have "set (fst branch) \<subseteq> set (init_assumps) \<union> set
      (map (\<lambda>x. (x, mpoly_sign val x)) (coeffs_list (a#qs)))"
    using subset_h by auto
  then show ?case
    using branch_inset
    by (metis (no_types, lifting) prod.sel(1))
qed

lemma base_case_info_M_assumps_complete:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, mat_eq) \<in> set (base_case_info_M_assumps init_assumps).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
  using assms unfolding base_case_info_M_assumps_def by auto

lemma matches_len_complete_spmods_ex:
  assumes "\<And>p' n'. (p',n') \<in> set acc \<Longrightarrow> satisfies_evaluation val p' n'"
  shows  "\<exists>(assumps, sturm_seq) \<in> set (spmods_multiv p q acc).
    (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
  using assms
proof (induct p q acc rule: spmods_multiv_induct)
  case (Base p q acc)
  then show ?case 
    by (auto simp add: spmods_multiv.simps)
next
  case (Rec p q acc)
  let ?left = "spmods_multiv (one_less_degree p) q ((Polynomial.lead_coeff p, (0::rat)) # acc)"
  let ?res_one = "spmods_multiv_aux p q ((Polynomial.lead_coeff p, (1::rat)) # acc)"
  let ?res_minus_one = "spmods_multiv_aux p q ((Polynomial.lead_coeff p, (-1::rat)) # acc)"
  have spmods_is: "spmods_multiv p q acc = ?left @ (?res_one @ ?res_minus_one)"
    using spmods_multiv.simps Rec(1-2) by auto
  have "satisfies_evaluation val (Polynomial.lead_coeff p) 0 \<or>
    satisfies_evaluation val (Polynomial.lead_coeff p) 1 \<or>
    satisfies_evaluation val (Polynomial.lead_coeff p) (-1)"
    unfolding satisfies_evaluation_def
    apply auto
    using Sturm_Tarski.sign_cases
    by (metis of_int_1 of_int_minus) 
  then have q:"
  (\<forall>p' n'. (p',n') \<in> set ((Polynomial.lead_coeff p, 0) # acc) \<longrightarrow> satisfies_evaluation val p' n') \<or>
  (\<forall>p' n'. (p',n') \<in> set ((Polynomial.lead_coeff p, 1) # acc) \<longrightarrow> satisfies_evaluation val p' n') \<or>
  (\<forall>p' n'. (p',n') \<in> set ((Polynomial.lead_coeff p, -1) # acc) \<longrightarrow> satisfies_evaluation val p' n')"
    using Rec 
    by simp 
  moreover {
    assume *:"(\<forall>p' n'. (p',n') \<in> set ((Polynomial.lead_coeff p, 0) # acc) \<longrightarrow> satisfies_evaluation val p' n')"
    then have "\<exists>a\<in>set (spmods_multiv (Multiv_Poly_Props.one_less_degree p) q
              ((Polynomial.lead_coeff p, 0) # acc)).
       case a of
       (a, ss) \<Rightarrow>
         \<forall>a\<in>set a. case a of (a, b) \<Rightarrow> satisfies_evaluation val a b"
      using Rec by auto
    then have ?case using spmods_is by auto
  }
  moreover {
    assume *:"(\<forall>p' n'. (p',n') \<in> set ((Polynomial.lead_coeff p, 1) # acc) \<longrightarrow> satisfies_evaluation val p' n')"
    then obtain assumps sturm_seq where
      "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (1::rat)) # acc))"
      "\<And> p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
      using matches_len_complete[of "((Polynomial.lead_coeff p, (1::rat)) # acc)" val p q]
      by blast 
    then have ?case using spmods_is by auto
  }
  moreover {
    assume *:"(\<forall>p' n'. (p',n') \<in> set ((Polynomial.lead_coeff p, -1) # acc) \<longrightarrow> satisfies_evaluation val p' n')"
    then obtain assumps sturm_seq where
      "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p q ((Polynomial.lead_coeff p, (-1::rat)) # acc))"
      "\<And> p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
      using matches_len_complete[of "((Polynomial.lead_coeff p, (-1::rat)) # acc)" val p q]
      by blast 
    then have ?case using spmods_is by auto
  }
  ultimately show ?case
    by fastforce
next
  case (Lookup0 p q acc)
  then show ?case  by (auto simp add: spmods_multiv.simps)
next
  case (LookupN0 p q acc r)
  then have spmods_is: "spmods_multiv p q acc = spmods_multiv_aux p q acc"
    using spmods_multiv.simps by auto
  obtain assumps sturm_seq where
    "(assumps, sturm_seq) \<in> set (spmods_multiv_aux p q acc)"
    "\<And> p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
    using LookupN0(4) matches_len_complete[of acc val p q]
    by blast 
  then show ?case
    using spmods_is by auto
qed

lemma matches_len_complete_spmods:
  assumes "\<And>p n. (p,n) \<in> set acc \<Longrightarrow> satisfies_evaluation val p n"
  obtains assumps sturm_seq where
    "(assumps, sturm_seq) \<in> set (spmods_multiv p q acc)"
    "(f,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val f n"
  using assms matches_len_complete_spmods_ex
  by (smt (verit, ccfv_threshold) case_prodD case_prodE) 

lemma tarski_queries_complete_aux:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, tq) \<in> set (construct_NofI_R_spmods p init_assumps I1 I2).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
  unfolding construct_NofI_R_spmods_def
  using assms matches_len_complete_spmods_ex[of init_assumps val "monoid_add_class.sum_list (map power2 (p # I1))"]
  by meson 

lemma tarski_queries_complete:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, tq) \<in> set (construct_NofI_M p init_assumps I1 I2).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
proof - 
  have cnoi_is: "construct_NofI_M p init_assumps I1 I2 =
  (let ss_list = construct_NofI_R_spmods p init_assumps I1 I2 in
  map construct_NofI_single_M ss_list)" 
    by auto
  obtain assumps tq where assumps_tq: "(assumps, tq) \<in> set (construct_NofI_R_spmods p init_assumps I1 I2)"
    "(\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    using tarski_queries_complete_aux assms
    by (smt (verit, ccfv_threshold) case_prodE) (* Takes a second to load *) 
  then have inset: "construct_NofI_single_M (assumps, tq) \<in> set (construct_NofI_M p init_assumps I1 I2)"
    by (metis (no_types, lifting) \<open>construct_NofI_M p init_assumps I1 I2 = Let (construct_NofI_R_spmods p init_assumps I1 I2) (map construct_NofI_single_M)\<close> in_set_conv_nth length_map nth_map)
      (* Takes a second to load *)
  obtain r where "(assumps, r) = construct_NofI_single_M (assumps, tq)"
    using construct_NofI_single_M.simps by auto
  then show ?thesis
    using inset assumps_tq(2)
    by (smt (verit) case_prodI) 
qed

lemma solve_for_rhs_rec_M_complete:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, rhs_vec) \<in> set (construct_rhs_vector_rec_M p init_assumps ell).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
  using assms proof (induct ell arbitrary: init_assumps )
  case Nil
  then show ?case by auto
next
  case (Cons a ell)
  then obtain qs1 qs2 where qs_prop: "a = (qs1, qs2)"
    by (meson prod.exhaust)
  have "\<exists> (assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    using tarski_queries_complete assms
    using local.Cons(2) by presburger
  then obtain assumps tq where assumps_tq: "(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)"
    "(\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    by blast 
  then have ind_h: "\<exists>a\<in>set (construct_rhs_vector_rec_M p assumps ell).
       case a of
       (assumps1, rhs_vec1) \<Rightarrow>
         \<forall>a\<in>set assumps1. case a of (a, b) \<Rightarrow> satisfies_evaluation val a b"
    using Cons.hyps
    by (metis (no_types, lifting) case_prodD) 
  {assume *: "ell = []"
    then have "construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#[])
      = construct_rhs_vector_rec_M p init_assumps (a#ell)"
      using qs_prop
      by blast 
    have rhs_is: "construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#[]) = 
    (let TQ_list = construct_NofI_M p init_assumps qs1 qs2 in
    map (\<lambda>(new_assumps, tq). (new_assumps, [tq])) TQ_list)"
      using * construct_rhs_vector_rec_M.simps(2) by blast 
    have "(assumps, [tq]) \<in> set (construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#[]))"
      using assumps_tq rhs_is
      by (smt (verit, best) image_eqI list.set_map old.prod.case) 
    then have ?case using assumps_tq(1)
      using "*" assumps_tq(2) qs_prop by blast
  } moreover {assume *: "length ell > 0"
    then obtain v va where "ell = v#va"
      by (meson Suc_le_length_iff Suc_less_eq le_simps(2))
    then have "construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#ell) = 
    concat (let TQ_list = construct_NofI_M p init_assumps qs1 qs2 in
    (map (\<lambda>(new_assumps, tq). (let rec = construct_rhs_vector_rec_M p new_assumps ell in
     map (\<lambda>r. (fst r,  tq#snd r)) rec)) TQ_list))"
      using * construct_rhs_vector_rec_M.simps(3) by auto
    then have subset_prop: "set (let rec = construct_rhs_vector_rec_M p assumps ell in
     map (\<lambda>r. (fst r,  tq#snd r)) rec) \<subseteq> set (construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#ell))"
      using assumps_tq
      by auto
    then obtain assumps1 rhs_vec1 where assumps1_rhs1: 
      "(assumps1, rhs_vec1) \<in> set (construct_rhs_vector_rec_M p assumps ell)"
      "(\<forall> (p,n) \<in> set assumps1. satisfies_evaluation val p n)"
      using ind_h
      by blast 
    then have "(assumps1, tq#rhs_vec1) \<in> set (let rec = construct_rhs_vector_rec_M p assumps ell in
     map (\<lambda>r. (fst r,  tq#snd r)) rec)" (* Takes a couple seconds to load *)
      by (metis (no_types, lifting) fst_eqD in_set_conv_nth length_map nth_map snd_conv)
    then have "(assumps1, tq#rhs_vec1) \<in> set (construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#ell))"
      using subset_prop by auto
    then have ?case
      using assumps1_rhs1(2) qs_prop 
      by auto
  }
  ultimately show ?case by auto
qed


lemma solve_for_rhs_M_complete:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, rhs_vec) \<in> set (construct_rhs_vector_M p init_assumps qs Is).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
proof - 
  obtain assumps rhs_rec_vec where assumps_rec:
    "(assumps, rhs_rec_vec) \<in> set (construct_rhs_vector_rec_M p init_assumps (pull_out_pairs qs Is))"
    " (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    using assms solve_for_rhs_rec_M_complete
    by (smt (verit, ccfv_threshold) case_prodE) 
  then have "(assumps, rhs_rec_vec)
    \<in> set (construct_rhs_vector_rec_M p init_assumps
      (map (\<lambda>(I1, I2). (retrieve_polys qs I1, retrieve_polys qs I2)) Is)) \<Longrightarrow>
    (\<And>z f A. (z \<in> f ` A) = (\<exists>x\<in>A. z = f x)) \<Longrightarrow>
    \<forall>x\<in>set assumps. case x of (x, xa) \<Rightarrow> satisfies_evaluation val x xa \<Longrightarrow>
    \<exists>x\<in>set (construct_rhs_vector_rec_M p init_assumps
              (map (\<lambda>(I1, I2). (retrieve_polys qs I1, retrieve_polys qs I2))
                Is)).
       \<forall>x\<in>set (fst x). case x of (x, xa) \<Rightarrow> satisfies_evaluation val x xa"
    by fastforce
  then show ?thesis
    using image_iff assumps_rec unfolding construct_rhs_vector_M_def by auto
qed

lemma solve_for_lhs_M_complete: 
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, lhs_vec) \<in> set (solve_for_lhs_M p init_assumps qs subsets matr).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
proof - 
  obtain assumps rhs_vec where assumps_prop:
    "(assumps, rhs_vec) \<in> set (construct_rhs_vector_M p init_assumps qs subsets)"
    "(\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    using solve_for_rhs_M_complete assms
    by (metis (mono_tags, lifting) prod.simps(2) surj_pair) 
  let ?rhs = "(assumps, rhs_vec)"
  have "(assumps, rhs_vec)
    \<in> set (construct_rhs_vector_M p init_assumps qs subsets) \<Longrightarrow>
    (assumps, solve_for_lhs_single_M p qs subsets matr rhs_vec)
    \<in> (\<lambda>rhs. (fst rhs, solve_for_lhs_single_M p qs subsets matr (snd rhs))) `
       set (construct_rhs_vector_M p init_assumps qs subsets)"
    using image_iff by fastforce 
  then have "(fst ?rhs, solve_for_lhs_single_M p qs subsets matr (snd ?rhs))
    \<in> set (solve_for_lhs_M p init_assumps qs subsets matr)"
    using assumps_prop(1) unfolding  solve_for_lhs_M_def 
    by auto
  then show ?thesis using assumps_prop(2)  
    by auto
qed

lemma reduce_system_single_M_complete:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, mat_eq) \<in> set (reduce_system_single_M p qs (init_assumps, (m,subs,signs))).
    (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
proof - 
  obtain assumps lhs_vec where assumps_lhs:
    "(assumps, lhs_vec) \<in> set (solve_for_lhs_M p init_assumps qs subs m)"
    " (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    using assms solve_for_lhs_M_complete
    by (metis (mono_tags, lifting) split_conv surj_pair) 
  then have "(assumps, lhs_vec) \<in> set (solve_for_lhs_M p init_assumps qs subs m) \<Longrightarrow>
    \<forall>x\<in>set assumps. case x of (p, n) \<Rightarrow> satisfies_evaluation val p n \<Longrightarrow>
    (\<And>z f A. (z \<in> f ` A) = (\<exists>x\<in>A. z = f x)) \<Longrightarrow>
    \<exists>x\<in>set (solve_for_lhs_M p init_assumps qs subs m).
       \<forall>x\<in>set (fst x). case x of (x, xa) \<Rightarrow> satisfies_evaluation val x xa"
    by (metis fst_conv) 
  then show ?thesis
    using assumps_lhs image_iff reduce_system_single_M.simps by auto
qed

lemma reduce_system_M_concat_map_helper:
  fixes a:: "'a list"
  fixes b:: "'a list list"
  assumes "a \<in> set b"
  shows "set a \<subseteq>  set (concat b)"
  using assms by auto


lemma reduce_system_M_complete:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes "(init_assumps, mat_eq) \<in> set input_list"
  shows "\<exists> (assumps, mat_eq) \<in> set (reduce_system_M p qs input_list).
    (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
proof - 
  obtain m subs signs where mat_eq: "(init_assumps, (m,subs,signs)) \<in> set input_list"
    using assms(2)
    by (metis prod_cases3) 
  have reduce: "reduce_system_M p qs input_list = concat (map (reduce_system_single_M p qs) input_list)"
    using reduce_system_M.simps by auto
  have elem: "(reduce_system_single_M p qs (init_assumps, (m,subs,signs))) \<in> set (map (reduce_system_single_M p qs) input_list)"
    using mat_eq
    by (metis (no_types, opaque_lifting) image_eqI image_set) 
  then have "set (reduce_system_single_M p qs (init_assumps, (m,subs,signs))) \<subseteq>  set (concat (map (reduce_system_single_M p qs) input_list))"
    using reduce_system_M_concat_map_helper[of "(reduce_system_single_M p qs (init_assumps, (m,subs,signs)))" "(map (reduce_system_single_M p qs) input_list)"]
    by auto
  then have subset: "set (reduce_system_single_M p qs (init_assumps, (m,subs,signs))) \<subseteq> set 
        (reduce_system_M p qs input_list)"
    using mat_eq reduce by auto
  have "\<exists> (assumps, mat_eq )\<in> set (reduce_system_single_M p qs (init_assumps, (m,subs,signs))).
    (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    using reduce_system_single_M_complete assms(1)
    by presburger 
  then show ?thesis using subset
    using basic_trans_rules(31) by blast 
qed

lemma combine_systems_M_complete:
  assumes "(assumps1, mat_eq1) \<in> set list1"
  assumes "(\<forall> (p,n) \<in> set assumps1. satisfies_evaluation val p n)"
  assumes "(assumps2, mat_eq2) \<in> set list2"
  assumes "(\<forall> (p,n) \<in> set assumps2. satisfies_evaluation val p n)"
  shows "\<exists> (assumps, mat_eq) \<in> set (snd (combine_systems_M p q1 list1 q2 list2)).
    (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
proof - 
  have snd_is: "snd (combine_systems_M p q1 list1 q2 list2) = concat (map (\<lambda>l1. (map (\<lambda>l2. combine_systems_single_M p q1 l1 q2 l2) list2)) list1)"
    by auto 
  have "(assumps1, mat_eq1) \<in> set list1 \<Longrightarrow>
    (assumps2, mat_eq2) \<in> set list2 \<Longrightarrow>
    \<exists>x\<in>set list1.
       (assumps1 @ assumps2,
        snd (combine_systems_R p (q1, mat_eq1) (q2, mat_eq2)))
       \<in> combine_systems_single_M p q1 x q2 ` set list2"
    by (metis combine_systems_single_M.simps rev_image_eqI) 
  then have inset: "combine_systems_single_M p q1 (assumps1, mat_eq1) q2 (assumps2, mat_eq2)
  \<in> set (concat (map (\<lambda>l1. (map (\<lambda>l2. combine_systems_single_M p q1 l1 q2 l2) list2)) list1))"
    using snd_is assms(1) assms(3) by auto
  obtain mat_eq where mat_eq: "(append assumps1 assumps2, mat_eq) = combine_systems_single_M p q1 (assumps1, mat_eq1) q2 (assumps2, mat_eq2)"
    using combine_systems_single_M.simps by auto
  then have "(append assumps1 assumps2, mat_eq) \<in>
  set (concat (map (\<lambda>l1. (map (\<lambda>l2. combine_systems_single_M p q1 l1 q2 l2) list2)) list1))"
    using inset by auto 
  then have inset2: "(append assumps1 assumps2, mat_eq) \<in> set (snd (combine_systems_M p q1 list1 q2 list2))"
    using snd_is by auto
  have "\<And>p n. (p,n) \<in> set (append assumps1 assumps2) \<Longrightarrow> satisfies_evaluation val p n"
    using assms(2) assms(4) by auto
  then show ?thesis
    using inset2
    by blast
qed

lemma get_all_valuations_calculate_data_M:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows  "\<exists> (assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
  using assms
proof (induct "length qs" arbitrary: val p init_assumps qs rule: less_induct)
  case (less qs val p init_assumps) 
  have "length qs = 0 \<or> length qs = 1 \<or> length qs > 1"
    by (meson less_one nat_neq_iff)
  {assume *: "length qs = 0"
    then have calc_data_is: "calculate_data_assumps_M p [] init_assumps
    =  map (\<lambda>(assumps,(a,(b,c))). (assumps, (a,b,map (drop 1) c))) (reduce_system_M p [1] (base_case_info_M_assumps init_assumps))"
      using calculate_data_assumps_M.simps
      by simp
    obtain assumps_inbtw mat_eq_inbtw where inbtw_props: "(assumps_inbtw, mat_eq_inbtw) \<in> set (base_case_info_M_assumps init_assumps)"
      "(\<forall> (p,n) \<in> set assumps_inbtw. satisfies_evaluation val p n)"
      using base_case_info_M_assumps_complete less(2)
      by (metis (no_types, lifting) case_prodE)
    then have "(\<And>p n. (p, n) \<in> set assumps_inbtw \<Longrightarrow> satisfies_evaluation val p n)"
      by auto
    then have "\<exists> (assumps, mat_eq) \<in> set (reduce_system_M p [1] (base_case_info_M_assumps init_assumps)).
      (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using reduce_system_M_complete[of assumps_inbtw val mat_eq_inbtw "(base_case_info_M_assumps init_assumps)" p "[1]"] inbtw_props(1) 
      by fastforce 
    then obtain assumps mat_eq where assumps_mat: "(assumps, mat_eq) \<in> set (reduce_system_M p [1] (base_case_info_M_assumps init_assumps))"
      "(\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      by blast
    then obtain a b c where "mat_eq = (a, (b, c))"
      by (metis prod.exhaust_sel)
    then have "(assumps, (a, (b, c))) \<in> set (reduce_system_M p [1] (base_case_info_M_assumps init_assumps))"
      using assumps_mat(1) by auto
    then have "(assumps, (a,b,map (drop 1) c)) \<in> set (calculate_data_assumps_M p [] init_assumps)"
      using calc_data_is image_iff
      by (smt (z3) image_set split_conv) 
    then have "\<exists> (assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using assumps_mat(2) * by blast  
  } moreover
  {assume *: "length qs = 1"
    then have calc_data_is: "calculate_data_assumps_M p qs init_assumps = reduce_system_M p qs (base_case_info_M_assumps init_assumps)"
      by auto
    obtain assumps_inbtw mat_eq_inbtw where inbtw_props: "(assumps_inbtw, mat_eq_inbtw) \<in> set (base_case_info_M_assumps init_assumps)"
      "(\<forall> (p,n) \<in> set assumps_inbtw. satisfies_evaluation val p n)"
      using base_case_info_M_assumps_complete less(2)
      by (metis (no_types, lifting) case_prodE)
    then have "(\<And>p n. (p, n) \<in> set assumps_inbtw \<Longrightarrow> satisfies_evaluation val p n)"
      by auto
    then have "\<exists> (assumps, mat_eq) \<in> set (reduce_system_M p qs (base_case_info_M_assumps init_assumps)).
      (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using reduce_system_M_complete[of assumps_inbtw val mat_eq_inbtw "(base_case_info_M_assumps init_assumps)" p qs] inbtw_props(1) 
      by fastforce 
    then have "\<exists> (assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using calc_data_is by auto
  } moreover
  {assume *: "length qs > 1"
    let ?len = "length qs"
    have calc_data_is: "calculate_data_assumps_M p qs init_assumps
    = (let q1 = take (?len div 2) qs; left = calculate_data_assumps_M p q1 init_assumps;
             q2 = drop (?len div 2) qs; right = calculate_data_assumps_M p q2 init_assumps;
             comb = combine_systems_M p q1 left q2 right in
             reduce_system_M p (fst comb) (snd comb)
        )" using * calculate_data_assumps_M.simps
      by (smt (z3) div_eq_0_iff bot_nat_0.not_eq_extremum div_greater_zero_iff rel_simps(69))
        (* Takes a second to load *)
    let ?q1 = "take (?len div 2) qs"
    let ?left = "calculate_data_assumps_M p ?q1 init_assumps"
    let ?q2 = "drop (?len div 2) qs"
    let ?right = "calculate_data_assumps_M p ?q2 init_assumps"
    let ?comb = "combine_systems_M p ?q1 ?left ?q2 ?right"
    have calc_data_is2: "calculate_data_assumps_M p qs init_assumps
       =  reduce_system_M p (fst ?comb) (snd ?comb)" using calc_data_is
      unfolding Let_def
      by auto
    have "length ?q1 < ?len" using * 
      by auto
    then have "\<exists> (assumps, mat_eq) \<in> set ?left.
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using less.hyps[of ?q1 init_assumps val p]
        less.prems by auto
    then obtain assumps1 mat_eq1 where assumps1:
      "(assumps1, mat_eq1) \<in> set ?left"
      "(\<forall> (p,n) \<in> set assumps1. satisfies_evaluation val p n)"
      by blast       
    have "length ?q2 < ?len" using *
      by auto
    then have "\<exists> (assumps, mat_eq) \<in> set ?right.
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using less.hyps[of ?q2 init_assumps val p]
        less.prems by auto
    then obtain assumps2 mat_eq2 where assumps2:
      "(assumps2, mat_eq2) \<in> set ?right"
      "(\<forall> (p,n) \<in> set assumps2. satisfies_evaluation val p n)"
      by blast
    have "\<exists> (assumps, mat_eq) \<in> set (snd ?comb).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using combine_systems_M_complete assumps1 assumps2
      by auto 
    then obtain assumps_inbtw mat_eq_inbtw where
      "(assumps_inbtw, mat_eq_inbtw) \<in> set (snd ?comb)"
      "(\<forall> (p,n) \<in> set assumps_inbtw. satisfies_evaluation val p n)"
      by blast
    then have "\<exists> (assumps, mat_eq) \<in> set (reduce_system_M p (fst ?comb) (snd ?comb)).
    (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using reduce_system_M_complete[of assumps_inbtw val mat_eq_inbtw "snd ?comb" p "fst ?comb"]
      by fastforce
    then have "\<exists> (assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps).
   (\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
      using calc_data_is2
      by presburger
  }
  ultimately show ?case
    using \<open>length qs = 0 \<or> length qs = 1 \<or> 1 < length qs\<close> by fastforce
qed

fun extract_signs_single:: "assumps \<times> matrix_equation \<Rightarrow> (assumps \<times> rat list list)"
  where "extract_signs_single (assumps, mat_eq) = (assumps, snd (snd mat_eq))"

lemma extract_signs_alt_char:
  shows "extract_signs qs = map extract_signs_single qs"
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then show ?case
    using extract_signs.simps extract_signs_single.simps
    by (smt (verit, ccfv_threshold) list.map(2) snd_conv split_conv surj_pair) 
qed

lemma get_all_valuations_helper:
  assumes  "(assumps, mat_eq) \<in> set ell"
  assumes "extract_signs_single (assumps, mat_eq) = (assumps, signs)"
  shows "(assumps, signs) \<in> set (extract_signs ell)"
proof - 
  have " extract_signs ell = map extract_signs_single ell "
    using extract_signs_alt_char 
    by metis
  then show ?thesis using assms image_eqI
    by (metis list.set_map)
qed

lemma get_all_valuations_alt:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "\<exists>(assumps, signs) \<in> set (sign_determination_inner qs init_assumps).
   (\<forall>p n. (p,n) \<in> set assumps \<longrightarrow> satisfies_evaluation val p n)"
proof -   obtain branch_gen where branch_gen_prop:
    "branch_gen \<in> set (lc_assump_generation_list qs init_assumps)"
    "set (fst branch_gen) \<subseteq> set (init_assumps) \<union> set
      (map (\<lambda>x. (x, mpoly_sign val x)) (coeffs_list qs))"
    using assms lc_assump_generation_list_valuation
    by blast 
  then have branch_gen: "\<And>p n. (p,n) \<in> set (fst branch_gen) \<Longrightarrow> satisfies_evaluation val p n "
    using lc_assump_generation_valuation_satisfies_eval
    by (meson UnE assms in_mono) 
  let ?poly_p_branch = "poly_p_in_branch branch_gen"
  let ?pos_limit_branch = "fst (limit_points_on_branch branch_gen) "
  let ?neg_limit_branch = "snd (limit_points_on_branch branch_gen) "
  let ?calculate_data_branch = "extract_signs (calculate_data_assumps_M ?poly_p_branch (snd branch_gen) (fst branch_gen))"
  have lim_points: "limit_points_on_branch branch_gen = (?pos_limit_branch, ?neg_limit_branch)"
    by auto
  have "set (let poly_p_branch = poly_p_in_branch branch_gen;
        (pos_limit_branch, neg_limit_branch) = limit_points_on_branch branch_gen;
        calculate_data_branch = extract_signs (calculate_data_assumps_M poly_p_branch (snd branch_gen) (fst branch_gen))
     in map (\<lambda>(a, signs). (a, pos_limit_branch#neg_limit_branch#signs)) calculate_data_branch)
     \<subseteq>  set (sign_determination_inner qs init_assumps)"
    using branch_gen_prop(1) sign_determination_inner.simps by auto
  then have in_signdet: "set (map (\<lambda>(a, signs). (a, ?pos_limit_branch#?neg_limit_branch#signs)) ?calculate_data_branch)
  \<subseteq> set (sign_determination_inner qs init_assumps)"
    using lim_points unfolding Let_def
  proof -
    assume "set (case limit_points_on_branch branch_gen of (pos_limit_branch, neg_limit_branch) \<Rightarrow> map (\<lambda>(a, signs). (a, pos_limit_branch # neg_limit_branch # signs)) (extract_signs (calculate_data_assumps_M (poly_p_in_branch branch_gen) (snd branch_gen) (fst branch_gen)))) \<subseteq> set (sign_determination_inner qs init_assumps)"
    then show ?thesis
      by (simp add: split_def)
  qed 
  obtain  assumps mat_eq where assumps_mat_prop:
    "(assumps, mat_eq) \<in> set (calculate_data_assumps_M ?poly_p_branch (snd branch_gen) (fst branch_gen))"
    "(\<forall> (p,n) \<in> set assumps. satisfies_evaluation val p n)"
    using get_all_valuations_calculate_data_M branch_gen
    by (smt (verit, del_insts) prod.exhaust_sel split_def)
  then obtain m subsets signs where mat_eq_is: "mat_eq = (m, (subsets, signs))"
    using prod_cases3 by blast
  then have pull_out: "extract_signs_single (assumps, mat_eq) = (assumps, signs)"
    using extract_signs_single.simps by auto
  have "?calculate_data_branch =  (map extract_signs_single
             (calculate_data_assumps_M (poly_p_in_branch branch_gen)
               (snd branch_gen) (fst branch_gen)))"
    using extract_signs_alt_char by auto
  then have "(assumps, signs) \<in> set ?calculate_data_branch"
    using assumps_mat_prop(1) pull_out  get_all_valuations_helper
    by blast 
  then have "(assumps, ?pos_limit_branch#?neg_limit_branch#signs) \<in>
    set (sign_determination_inner qs init_assumps)"
    using in_signdet by auto
  then show ?thesis 
    using assumps_mat_prop(2)
    by blast 
qed

lemma get_all_valuations:
  assumes "\<And>p n. (p,n) \<in> set init_assumps \<Longrightarrow> satisfies_evaluation val p n"
  obtains assumps signs where "(assumps, signs) \<in> set (sign_determination_inner qs init_assumps)"
    "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  using assms get_all_valuations_alt
  by (metis (no_types, lifting) case_prodE)

subsection "Correctness of elim forall and elim exist"

lemma subset_zip_is_subset:
  assumes "set qs1 \<subseteq> set qs"
  assumes "signs = map (mpoly_sign val) qs"
  assumes "signs1 = map (mpoly_sign val) qs1"
  shows subset: "set (zip qs1 signs1) \<subseteq> set (zip qs signs)"
proof clarsimp 
  fix a b 
  assume *: "(a, b) \<in> set (zip qs1 signs1)"
  then have "a \<in> set qs1"
    by (meson set_zip_leftD)
  then have a_in_qs: "a \<in> set qs"
    using assms by auto
  have "\<And>ba. set qs1 \<subseteq> set qs \<Longrightarrow>
          signs = map (mpoly_sign val) qs \<Longrightarrow>
          signs1 = map (mpoly_sign val) qs1 \<Longrightarrow>
          zip qs1 (map (mpoly_sign val) qs1) =
          map2 (\<lambda>x y. (x, mpoly_sign val y)) qs1 qs1 \<Longrightarrow>
          (a, ba) \<in> set (zip qs1 qs1) \<Longrightarrow>
          b = mpoly_sign val ba \<Longrightarrow> mpoly_sign val ba = mpoly_sign val a"
     by (simp add: zip_same)
  then have b_is: "b = mpoly_sign val a"
    using * assms zip_map2[of qs1 "mpoly_sign val" qs1]  
    by (auto) 
  have "(a, mpoly_sign val a) \<in> set (map (\<lambda>(x,y).(x, mpoly_sign val y)) (zip qs qs))"
    using a_in_qs zip_same[of a a qs] by auto
  then have "(a, mpoly_sign val a) \<in> set (map2 (\<lambda>x y. (x, mpoly_sign val y)) qs qs)"
    by auto
  then show "(a, b) \<in> set (zip qs signs)"
    using b_is a_in_qs assms zip_map2[of qs "mpoly_sign val" qs]
    using assms(1) by presburger
qed

lemma extract_polys_subset:
  assumes "signs = map (mpoly_sign val) qs"
  assumes "signs1 = map (mpoly_sign val) qs1"
  assumes "set qs1 \<subseteq> set qs"
  assumes "Some w = lookup_sem_M F (zip qs1 signs1)"
  shows "lookup_sem_M F (zip qs signs) = lookup_sem_M F (zip qs1 signs1)"
  using assms
proof (induct F arbitrary: w)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  have subset: "set (zip qs1 signs1) \<subseteq> set (zip qs signs)"
    using subset_zip_is_subset Atom.prems by auto
  show ?case 
  proof (cases x)
    case (Less x1)
    then obtain i where i_prop: "lookup_assump_aux x1 (zip qs1 signs1) = Some i"
      using Atom.prems lookup_sem_M.simps
      by (metis lookup_assump_aux_eo option.simps(3) option.simps(4))
    have i_is: "(x1, i) \<in> set (zip qs1 signs1) "
      using i_prop lookup_assump_means_inset[of x1 "(zip qs1 signs1)" i]
        in_set_member[of "(x1, i)" "(zip qs1 signs1)" ] by auto
    then have "(x1, i) \<in> set (zip qs signs)"
      using subset by auto
    then obtain i1 where "lookup_assump_aux x1 (zip qs signs) = Some i1"
      using inset_means_lookup_assump_some[of x1 i "(zip qs signs)"]
      by meson 
    then have i1_is: "(x1, i1) \<in> set (zip qs signs)"
      using lookup_assump_means_inset[of x1 "(zip qs signs)" i1]
        in_set_member[of "(x1, i1)" "(zip qs signs)"] by auto
    have "\<And>b. signs1 = map (mpoly_sign val) qs1 \<Longrightarrow>
         zip qs1 (map (mpoly_sign val) qs1) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs1 qs1 \<Longrightarrow>
         (x1, b) \<in> set (zip qs1 qs1) \<Longrightarrow>
         i = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i_sign :"i = mpoly_sign val x1"
      using i_is  Atom.prems(2) zip_map2[of qs1 "mpoly_sign val" qs1]      
      by (auto) 
    have "\<And>b. signs = map (mpoly_sign val) qs \<Longrightarrow>
         zip qs (map (mpoly_sign val) qs) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs qs \<Longrightarrow>
         (x1, b) \<in> set (zip qs qs) \<Longrightarrow>
         i1 = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i1_sign: "i1 = mpoly_sign val x1"
      using i1_is  Atom.prems(1) zip_map2[of qs "mpoly_sign val" qs]
      by (auto) 
    have "Sturm_Tarski.sign i1 = Sturm_Tarski.sign i"
      using i_sign i1_sign
      by blast 
    then show ?thesis using Atom.prems i_prop lookup_sem_M.simps
      using Less \<open>lookup_assump_aux x1 (zip qs signs) = Some i1\<close> i1_sign i_sign by presburger
  next
    case (Eq x1)
    then obtain i where i_prop: "lookup_assump_aux x1 (zip qs1 signs1) = Some i"
      using Atom.prems lookup_sem_M.simps
      by (metis lookup_assump_aux_eo option.simps(3) option.simps(4))
    have i_is: "(x1, i) \<in> set (zip qs1 signs1) "
      using i_prop lookup_assump_means_inset[of x1 "(zip qs1 signs1)" i]
        in_set_member[of "(x1, i)" "(zip qs1 signs1)" ] by auto
    then have "(x1, i) \<in> set (zip qs signs)"
      using subset by auto
    then obtain i1 where "lookup_assump_aux x1 (zip qs signs) = Some i1"
      by (meson inset_means_lookup_assump_some) 
    then have i1_is: "(x1, i1) \<in> set (zip qs signs)"
      using lookup_assump_means_inset[of x1 "(zip qs signs)" i1]
        in_set_member[of "(x1, i1)" "(zip qs signs)"] by auto
    have "\<And>b. signs1 = map (mpoly_sign val) qs1 \<Longrightarrow>
         zip qs1 (map (mpoly_sign val) qs1) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs1 qs1 \<Longrightarrow>
         (x1, b) \<in> set (zip qs1 qs1) \<Longrightarrow>
         i = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i_sign :"i = mpoly_sign val x1"
      using i_is  Atom.prems(2) zip_map2[of qs1 "mpoly_sign val" qs1]
      by (auto)  
    have "\<And>b. signs = map (mpoly_sign val) qs \<Longrightarrow>
         zip qs (map (mpoly_sign val) qs) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs qs \<Longrightarrow>
         (x1, b) \<in> set (zip qs qs) \<Longrightarrow>
         i1 = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i1_sign: "i1 = mpoly_sign val x1"
      using i1_is  Atom.prems(1) zip_map2[of qs "mpoly_sign val" qs]
      by (auto)  
    have "Sturm_Tarski.sign i1 = Sturm_Tarski.sign i"
      using i_sign i1_sign
      by blast 
    then show ?thesis using Atom.prems i_prop lookup_sem_M.simps
      using Eq \<open>lookup_assump_aux x1 (zip qs signs) = Some i1\<close> i1_sign i_sign by presburger
  next
    case (Leq x1)
    then obtain i where i_prop: "lookup_assump_aux x1 (zip qs1 signs1) = Some i"
      using Atom.prems lookup_sem_M.simps
      by (metis lookup_assump_aux_eo option.simps(3) option.simps(4))
    have i_is: "(x1, i) \<in> set (zip qs1 signs1) "
      using i_prop lookup_assump_means_inset[of x1 "(zip qs1 signs1)" i]
        in_set_member[of "(x1, i)" "(zip qs1 signs1)" ] by auto
    then have "(x1, i) \<in> set (zip qs signs)"
      using subset by auto
    then obtain i1 where "lookup_assump_aux x1 (zip qs signs) = Some i1"
      by (meson inset_means_lookup_assump_some)
    then have i1_is: "(x1, i1) \<in> set (zip qs signs)"
      using lookup_assump_means_inset[of x1 "(zip qs signs)" i1]
        in_set_member[of "(x1, i1)" "(zip qs signs)"] by auto
    have "\<And>b. signs1 = map (mpoly_sign val) qs1 \<Longrightarrow>
         zip qs1 (map (mpoly_sign val) qs1) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs1 qs1 \<Longrightarrow>
         (x1, b) \<in> set (zip qs1 qs1) \<Longrightarrow>
         i = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i_sign :"i = mpoly_sign val x1"
      using i_is  Atom.prems(2) zip_map2[of qs1 "mpoly_sign val" qs1]
      by (auto) 
    have "\<And>b. signs = map (mpoly_sign val) qs \<Longrightarrow>
         zip qs (map (mpoly_sign val) qs) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs qs \<Longrightarrow>
         (x1, b) \<in> set (zip qs qs) \<Longrightarrow>
         i1 = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i1_sign: "i1 = mpoly_sign val x1"
      using i1_is  Atom.prems(1) zip_map2[of qs "mpoly_sign val" qs]
      by (auto) 
    have "Sturm_Tarski.sign i1 = Sturm_Tarski.sign i"
      using i_sign i1_sign
      by blast 
    then show ?thesis using Atom.prems i_prop lookup_sem_M.simps
      using Leq \<open>lookup_assump_aux x1 (zip qs signs) = Some i1\<close> i1_sign i_sign by presburger
  next
    case (Neq x1)
    then obtain i where i_prop: "lookup_assump_aux x1 (zip qs1 signs1) = Some i"
      using Atom.prems lookup_sem_M.simps
      by (metis lookup_assump_aux_eo option.simps(3) option.simps(4))
    have i_is: "(x1, i) \<in> set (zip qs1 signs1) "
      using i_prop lookup_assump_means_inset[of x1 "(zip qs1 signs1)" i]
        in_set_member[of "(x1, i)" "(zip qs1 signs1)" ] by auto
    then have "(x1, i) \<in> set (zip qs signs)"
      using subset by auto
    then obtain i1 where "lookup_assump_aux x1 (zip qs signs) = Some i1"
      by (meson inset_means_lookup_assump_some) 
    then have i1_is: "(x1, i1) \<in> set (zip qs signs)"
      using lookup_assump_means_inset[of x1 "(zip qs signs)" i1]
        in_set_member[of "(x1, i1)" "(zip qs signs)"] by auto
    have "\<And>b. signs1 = map (mpoly_sign val) qs1 \<Longrightarrow>
         zip qs1 (map (mpoly_sign val) qs1) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs1 qs1 \<Longrightarrow>
         (x1, b) \<in> set (zip qs1 qs1) \<Longrightarrow>
         i = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i_sign :"i = mpoly_sign val x1"
      using i_is  Atom.prems(2) zip_map2[of qs1 "mpoly_sign val" qs1]
      by (auto)
    have " \<And>b. signs = map (mpoly_sign val) qs \<Longrightarrow>
         zip qs (map (mpoly_sign val) qs) =
         map2 (\<lambda>x y. (x, mpoly_sign val y)) qs qs \<Longrightarrow>
         (x1, b) \<in> set (zip qs qs) \<Longrightarrow>
         i1 = mpoly_sign val b \<Longrightarrow> mpoly_sign val b = mpoly_sign val x1"
      by (simp add: zip_same)
    then have i1_sign: "i1 = mpoly_sign val x1"
      using i1_is  Atom.prems(1) zip_map2[of qs "mpoly_sign val" qs]
      by (auto)
    have "Sturm_Tarski.sign i1 = Sturm_Tarski.sign i"
      using i_sign i1_sign
      by blast 
    then show ?thesis using Atom.prems i_prop lookup_sem_M.simps
      using Neq \<open>lookup_assump_aux x1 (zip qs signs) = Some i1\<close> i1_sign i_sign by presburger
  qed
next
  case (And F1 F2)
  let ?sub_ell = "(zip qs1 signs1)"
  have case_some: "lookup_sem_M (fm.And F1 F2) ?sub_ell = (case (lookup_sem_M F1 ?sub_ell, lookup_sem_M F2 ?sub_ell) 
      of (Some i, Some j) \<Rightarrow> Some (i \<and> j)
      | _ \<Rightarrow> None)"
    using lookup_sem_M.simps by simp
  have e1: "\<exists>w1. lookup_sem_M F1 ?sub_ell = Some w1"
    using case_some And.prems(4)
    using proper_interval_bool.elims(1) by fastforce 
  have e2: "\<exists>w2. lookup_sem_M F2 ?sub_ell = Some w2"
    using case_some And.prems(4)
    using proper_interval_bool.elims(1)
    by (smt (z3) option.case(1) option.simps(5) split_conv) 
  then obtain w1 w2 where "lookup_sem_M F1 ?sub_ell = Some w1"
    "lookup_sem_M F2 ?sub_ell = Some w2"
    using e1 e2 by auto
  have ind1: " lookup_sem_M F1 (zip qs signs) = lookup_sem_M F1 (zip qs1 signs1)"
    using e1 And.hyps(1) And.prems(1-3) by auto
  have ind2: " lookup_sem_M F2 (zip qs signs) = lookup_sem_M F2 (zip qs1 signs1)"
    using e2 And.hyps(2) And.prems(1-3) by auto
  then show ?case  using lookup_sem_M.simps
      ind1 ind2
    by presburger 
next
  case (Or F1 F2)
  let ?sub_ell = "(zip qs1 signs1)"
  have case_some: "lookup_sem_M (fm.Or F1 F2) ?sub_ell = (case (lookup_sem_M F1 ?sub_ell, lookup_sem_M F2 ?sub_ell) 
      of (Some i, Some j) \<Rightarrow> Some (i \<or> j)
      | _ \<Rightarrow> None)"
    using lookup_sem_M.simps by simp
  have e1: "\<exists>w1. lookup_sem_M F1 ?sub_ell = Some w1"
    using case_some Or.prems(4)
    using proper_interval_bool.elims(1) by fastforce 
  have e2: "\<exists>w2. lookup_sem_M F2 ?sub_ell = Some w2"
    using case_some Or.prems(4)
    using proper_interval_bool.elims(1) 
    by (smt (z3) option.case(1) option.simps(5) split_conv) 
  then obtain w1 w2 where "lookup_sem_M F1 ?sub_ell = Some w1"
    "lookup_sem_M F2 ?sub_ell = Some w2"
    using e1 e2 by auto
  have ind1: " lookup_sem_M F1 (zip qs signs) = lookup_sem_M F1 (zip qs1 signs1)"
    using e1 Or.hyps(1) Or.prems(1-3) by auto
  have ind2: " lookup_sem_M F2 (zip qs signs) = lookup_sem_M F2 (zip qs1 signs1)"
    using e2 Or.hyps(2) Or.prems(1-3) by auto
  then show ?case  using lookup_sem_M.simps
      ind1 ind2
    by presburger 
next
  case (Neg F)
  then show ?case
    by (metis lookup_sem_M.simps(5) not_Some_eq option.case(1))
next
  case (ExQ F)
  then show ?case by auto
next
  case (AllQ F)
  then show ?case by auto
next
  case (ExN x1 F)
  then show ?case
    by (metis add_Suc_right le_Suc_eq' le_add_same_cancel1 lookup_sem_M.simps(10) lookup_sem_M.simps(14)) 
next
  case (AllN x1 F)
  then show ?case
    by (metis lookup_sem_M.simps(11) lookup_sem_M.simps(15) zero_list.cases) 
qed

lemma extract_polys_semantics:
  assumes "qs = extract_polys F"
  assumes "signs = map (mpoly_sign val) qs"
  assumes "countQuantifiers F = 0"
  shows "Some (eval F val) = lookup_sem_M F (zip qs signs)"
  using assms
proof (induct F arbitrary: qs signs)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case 
    by auto
next
  case (Atom x)
  then show ?case 
  proof (cases x)
    case (Less x1)
    then have "extract_polys (fm.Atom x) = [x1]"
      using extract_polys.simps by auto 
    then have qs_is: "qs = [x1]" using Atom.prems
      by auto
    then have signs_is: "signs = [mpoly_sign val x1]"
      using Atom.prems by auto
    then have zip_is: "zip qs signs = [(x1, mpoly_sign val x1)]"
      using qs_is by auto
    then have lookup_sem_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = 
      (case (lookup_assump_aux x1 (zip qs signs)) of
     Some i \<Rightarrow> Some (i < 0)
    | _ \<Rightarrow> None)"using Less
      by auto 
    have "lookup_assump_aux x1 (zip qs signs) = Some (mpoly_sign val x1)"
      using zip_is by auto
    then have lookup_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = Some ((mpoly_sign val x1) < 0)"
      using lookup_sem_is by auto
    have eval_is: "eval (fm.Atom x) val = (insertion (nth_default 0 val) x1 < 0)"
      using Less by auto
    have "(mpoly_sign val x1) < 0 =  (insertion (nth_default 0 val) x1 < 0)"
      unfolding mpoly_sign_def eval_mpoly_def Sturm_Tarski.sign_def
      by auto
    then show ?thesis using eval_is lookup_is 
      by auto
  next
    case (Eq x1)  
    then have "extract_polys (fm.Atom x) = [x1]"
      using extract_polys.simps by auto 
    then have qs_is: "qs = [x1]" using Atom.prems
      by auto
    then have signs_is: "signs = [mpoly_sign val x1]"
      using Atom.prems by auto
    then have zip_is: "zip qs signs = [(x1, mpoly_sign val x1)]"
      using qs_is by auto
    then have lookup_sem_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = 
      (case (lookup_assump_aux x1 (zip qs signs)) of
     Some i \<Rightarrow> Some (i = 0)
    | _ \<Rightarrow> None)"using Eq
      by auto 
    have "lookup_assump_aux x1 (zip qs signs) = Some (mpoly_sign val x1)"
      using zip_is by auto
    then have lookup_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = Some ((mpoly_sign val x1) = 0)"
      using lookup_sem_is by auto
    have eval_is: "eval (fm.Atom x) val = (insertion (nth_default 0 val) x1 = 0)"
      using Eq by auto
    have "(mpoly_sign val x1) = 0 =  (insertion (nth_default 0 val) x1 = 0)"
      unfolding mpoly_sign_def eval_mpoly_def Sturm_Tarski.sign_def
      by auto
    then show ?thesis using eval_is lookup_is 
      by auto
  next
    case (Leq x1)
    then have "extract_polys (fm.Atom x) = [x1]"
      using extract_polys.simps by auto 
    then have qs_is: "qs = [x1]" using Atom.prems
      by auto
    then have signs_is: "signs = [mpoly_sign val x1]"
      using Atom.prems by auto
    then have zip_is: "zip qs signs = [(x1, mpoly_sign val x1)]"
      using qs_is by auto
    then have lookup_sem_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = 
      (case (lookup_assump_aux x1 (zip qs signs)) of
     Some i \<Rightarrow> Some (i \<le> 0)
    | _ \<Rightarrow> None)"using Leq
      by auto 
    have "lookup_assump_aux x1 (zip qs signs) = Some (mpoly_sign val x1)"
      using zip_is by auto
    then have lookup_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = Some ((mpoly_sign val x1) \<le> 0)"
      using lookup_sem_is by auto
    have eval_is: "eval (fm.Atom x) val = (insertion (nth_default 0 val) x1 \<le> 0)"
      using Leq by auto
    have "(mpoly_sign val x1) \<le> 0 =  (insertion (nth_default 0 val) x1 \<le> 0)"
      unfolding mpoly_sign_def eval_mpoly_def Sturm_Tarski.sign_def
      by auto
    then show ?thesis using eval_is lookup_is 
      by auto
  next
    case (Neq x1)
    then have "extract_polys (fm.Atom x) = [x1]"
      using extract_polys.simps by auto 
    then have qs_is: "qs = [x1]" using Atom.prems
      by auto
    then have signs_is: "signs = [mpoly_sign val x1]"
      using Atom.prems by auto
    then have zip_is: "zip qs signs = [(x1, mpoly_sign val x1)]"
      using qs_is by auto
    then have lookup_sem_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = 
      (case (lookup_assump_aux x1 (zip qs signs)) of
     Some i \<Rightarrow> Some (i \<noteq> 0)
    | _ \<Rightarrow> None)"using Neq
      by auto 
    have "lookup_assump_aux x1 (zip qs signs) = Some (mpoly_sign val x1)"
      using zip_is by auto
    then have lookup_is: "lookup_sem_M (fm.Atom x) (zip qs signs) = Some ((mpoly_sign val x1) \<noteq> 0)"
      using lookup_sem_is by auto
    have eval_is: "eval (fm.Atom x) val = (insertion (nth_default 0 val) x1 \<noteq> 0)"
      using Neq by auto
    have "(mpoly_sign val x1) \<noteq> 0 =  (insertion (nth_default 0 val) x1 \<noteq> 0)"
      unfolding mpoly_sign_def eval_mpoly_def Sturm_Tarski.sign_def
      by auto
    then show ?thesis using eval_is lookup_is 
      by auto
  qed
next
  case (And F1 F2)
  have qs_is: "qs = (extract_polys F1)@(extract_polys F2)"
    using And.prems(1) extract_polys.simps
    by force
  then obtain signs1 signs2 where signs_prop:
    "signs1 = map (mpoly_sign val) (extract_polys F1) "
    "signs2 = map (mpoly_sign val) (extract_polys F2) "
    "signs = signs1 @ signs2"
    using And.prems(2) by auto
  have subset_f1: "set (extract_polys F1) \<subseteq> set qs"
    using qs_is by auto
  have subset_f2: "set (extract_polys F2) \<subseteq> set qs"
    using qs_is by auto
  have f1_free: "countQuantifiers F1 = 0"
    using And.prems(3)
    by auto
  have f2_free: "countQuantifiers F2 = 0"
    using And.prems(3)
    by auto
  have zip_is: "(zip qs signs) = (zip (extract_polys F1) signs1)@(zip (extract_polys F2) signs2)"
    using qs_is signs_prop(3)
    by (simp add: signs_prop(1)) 
  have ind1: "Some (eval F1 val) = lookup_sem_M F1 (zip (extract_polys F1) signs1)"
    using And.hyps(1) signs_prop(1) f1_free by auto
  have subset: "set (zip (extract_polys F1) signs1) \<subseteq> set (zip qs signs)"
    using subset_zip_is_subset And.prems signs_prop(1) by auto
  then have lookup1: "lookup_sem_M F1 (zip (extract_polys F1) signs1) = lookup_sem_M F1 (zip qs signs)"
    using extract_polys_subset[of signs val qs signs1 "extract_polys F1"] ind1 subset_f1 signs_prop(1) qs_is And.prems(2)
    by auto
  then have restate_ind1: "lookup_sem_M F1 (zip qs signs) = Some (eval F1 val)"
    using ind1 lookup1
    by auto
  have ind2: "Some (eval F2 val) = lookup_sem_M F2 (zip (extract_polys F2) signs2)"
    using And.hyps(2) signs_prop(2) f2_free by auto
  then have lookup2: "lookup_sem_M F2 (zip (extract_polys F2) signs2) = lookup_sem_M F2 (zip qs signs)"
    using extract_polys_subset[of signs val qs signs2 "extract_polys F2"] ind2 subset_f2 signs_prop(2) And.prems(2)
    by auto
  then have restate_ind2: "lookup_sem_M F2 (zip qs signs) = Some (eval F2 val)"
    using ind2 lookup2
    by auto
  show ?case using signs_prop(3) 
      restate_ind1 restate_ind2 
      qs_is zip_is lookup_sem_M.simps
    by simp
next
  case (Or F1 F2)
  have qs_is: "qs = (extract_polys F1)@(extract_polys F2)"
    using Or.prems(1) extract_polys.simps
    by force
  then obtain signs1 signs2 where signs_prop:
    "signs1 = map (mpoly_sign val) (extract_polys F1) "
    "signs2 = map (mpoly_sign val) (extract_polys F2) "
    "signs = signs1 @ signs2"
    using Or.prems(2) by auto
  have subset_f1: "set (extract_polys F1) \<subseteq> set qs"
    using qs_is by auto
  have subset_f2: "set (extract_polys F2) \<subseteq> set qs"
    using qs_is by auto
  have f1_free: "countQuantifiers F1 = 0"
    using Or.prems(3)
    by auto
  have f2_free: "countQuantifiers F2 = 0"
    using Or.prems(3) 
    by auto
  have zip_is: "(zip qs signs) = (zip (extract_polys F1) signs1)@(zip (extract_polys F2) signs2)"
    using qs_is signs_prop(3)
    by (simp add: signs_prop(1)) 
  have ind1: "Some (eval F1 val) = lookup_sem_M F1 (zip (extract_polys F1) signs1)"
    using Or.hyps(1) signs_prop(1) f1_free by auto
  have subset: "set (zip (extract_polys F1) signs1) \<subseteq> set (zip qs signs)"
    using subset_zip_is_subset Or.prems signs_prop(1) by auto
  then have lookup1: "lookup_sem_M F1 (zip (extract_polys F1) signs1) = lookup_sem_M F1 (zip qs signs)"
    using extract_polys_subset[of signs val qs signs1 "extract_polys F1"] ind1 subset_f1 signs_prop(1) qs_is Or.prems(2)
    by auto
  then have restate_ind1: "lookup_sem_M F1 (zip qs signs) = Some (eval F1 val)"
    using ind1 lookup1
    by auto
  have ind2: "Some (eval F2 val) = lookup_sem_M F2 (zip (extract_polys F2) signs2)"
    using Or.hyps(2) signs_prop(2) f2_free by auto
  then have lookup2: "lookup_sem_M F2 (zip (extract_polys F2) signs2) = lookup_sem_M F2 (zip qs signs)"
    using extract_polys_subset[of signs val qs signs2 "extract_polys F2"] ind2 subset_f2 signs_prop(2) Or.prems(2)
    by auto
  then have restate_ind2: "lookup_sem_M F2 (zip qs signs) = Some (eval F2 val)"
    using ind2 lookup2
    by auto
  show ?case using signs_prop(3) 
      restate_ind1 restate_ind2 
      qs_is zip_is lookup_sem_M.simps
    by simp
next
  case (Neg F)
  have qs_is: "qs = (extract_polys F)"
    using Neg.prems(1) extract_polys.simps
    by force
  have cq_zer: "countQuantifiers F = 0"
    using Neg.prems(3) by auto
  have "Some (eval F val) = lookup_sem_M F (zip qs signs)"
    using qs_is cq_zer Neg.hyps[of qs signs] Neg.prems(2) 
    by auto
  then show ?case using lookup_sem_M.simps
    by (smt (verit, best) eval.simps(6) option.simps(5))  
next
  case (ExQ F)
  have "countQuantifiers (ExQ F) > 0"
    by auto 
  then show ?case using ExQ.prems(3) by auto
next
  case (AllQ F)
  have "countQuantifiers (AllQ F) > 0"
    by auto 
  then show ?case using AllQ.prems(3) by auto
next
  case (ExN x1 F)
  {assume *: "x1 = 0"
    then have h1: "eval (ExN x1 F) val = eval F val"
      by auto
    have h2: "lookup_sem_M (ExN x1 F) (zip qs signs)
        = lookup_sem_M F (zip qs signs)"
      using * by auto
    have qs_is: "qs = extract_polys F" using * ExN.prems(1)
        extract_polys.simps by auto
    have "countQuantifiers F = 0"
      using ExN.prems(3) by auto
    then have "Some (eval (ExN x1 F) val) =
       lookup_sem_M (ExN x1 F) (zip qs signs)"
      using qs_is h1 h2 ExN.hyps[of qs signs] ExN.prems(2) by auto
  }
  moreover {assume *: "x1 > 0"
    then have "countQuantifiers (ExN x1 F) > 0"
      by auto 
    then have "Some (eval (ExN x1 F) val) =
       lookup_sem_M (ExN x1 F) (zip qs signs)"
      using ExN.prems(3) by auto 
  }
  ultimately show ?case
    by fastforce 
next
  case (AllN x1 F)
  {assume *: "x1 = 0"
    then have h1: "eval (AllN x1 F) val = eval F val"
      by auto
    have h2: "lookup_sem_M (AllN x1 F) (zip qs signs)
        = lookup_sem_M F (zip qs signs)"
      using * by auto
    have qs_is: "qs = extract_polys F" using * AllN.prems(1)
        extract_polys.simps by auto
    have "countQuantifiers F = 0"
      using AllN.prems(3) by auto
    then have "Some (eval (AllN x1 F) val) =
       lookup_sem_M (AllN x1 F) (zip qs signs)"
      using qs_is h1 h2 AllN.hyps[of qs signs] AllN.prems(2) by auto
  }
  moreover {assume *: "x1 > 0"
    then have "countQuantifiers (AllN x1 F) > 0"
      by auto 
    then have "Some (eval (AllN x1 F) val) =
       lookup_sem_M (AllN x1 F) (zip qs signs)"
      using AllN.prems(3) by auto 
  }
  ultimately show ?case
    by fastforce 
qed

lemma create_disjunction_eval:
  assumes "eval (create_disjunction data) xs"
  shows "\<exists> a \<in> set data. (eval (assump_to_atom_fm (fst a)) xs)"
  using assms
proof (induct data)
  case Nil
  then show ?case by auto
next
  case (Cons a data)
  then show ?case
    by (metis create_disjunction.elims eval_Or fst_conv list.set_intros(1) list.set_intros(2) list.simps(1) list.simps(3)) 
qed

lemma assump_to_atom_fm_conjunction:
  assumes "eval (assump_to_atom_fm assumps) xs"
  shows "(p, n) \<in> set assumps \<Longrightarrow> satisfies_evaluation xs p n"
  using assms
proof (induct assumps)
  case Nil
  then show ?case by auto
next
  case (Cons a assumps)
  then have eval_prop: "eval (assump_to_atom_fm assumps) xs"
    "eval (Atom (assump_to_atom ((fst a), (snd a)))) xs"
     apply (metis assump_to_atom_fm.simps(2) eval.simps(4) old.prod.exhaust)
    by (metis Cons.prems(2) assump_to_atom_fm.simps(2) eval.simps(4) prod.exhaust_sel)
  {assume * : "(p, n) = a"
    have "aEval (if n = 0 then atom.Eq p else if n < 0 then Less p else Less (- p))
     xs \<Longrightarrow> Sturm_Tarski.sign (eval_mpoly xs p) = Sturm_Tarski.sign n"
    proof - 
      assume eval_h: "aEval (if n = 0 then atom.Eq p else if n < 0 then Less p else Less (- p))
     xs"
      {assume **: "n = 0"
        then have "Sturm_Tarski.sign (eval_mpoly xs p) = Sturm_Tarski.sign n"
          using eval_h unfolding eval_mpoly_def by auto
      } moreover
      {assume **: "n > 0"
        then have "Sturm_Tarski.sign (eval_mpoly xs p) = Sturm_Tarski.sign n"
          using eval_h unfolding eval_mpoly_def by auto
      } moreover
      {assume **: "n < 0"
        then have "Sturm_Tarski.sign (eval_mpoly xs p) = Sturm_Tarski.sign n"
          using eval_h unfolding eval_mpoly_def by auto
      }
      ultimately show "Sturm_Tarski.sign (eval_mpoly xs p) = Sturm_Tarski.sign n"
        using linorder_cases by blast
    qed
    then have "satisfies_evaluation xs p n"
      using eval_prop(2) * unfolding satisfies_evaluation_def
      by auto
  }
  moreover {assume *: "(p, n) \<in> set assumps"
    then have "satisfies_evaluation xs p n"
      using eval_prop(1) Cons.hyps by auto 
  }
  ultimately show ?case using Cons.prems(1) by auto
qed

lemma eval_elim_forall_correct1:
  fixes F:: "atom fm"
  assumes *: "countQuantifiers F = 0"
  assumes "eval (elim_forall F) xs"
  shows "(eval F (x#xs))"
proof - 
  let ?qs = "extract_polys F"
  let ?univ_qs = "univariate_in ?qs 0"
  let ?reindexed_univ_qs = "map (map_poly (lowerPoly 0 1)) ?univ_qs"
  let ?data = "sign_determination_inner ?reindexed_univ_qs []"
  let ?new_data = "filter (\<lambda>(assumps, signs_list). 
      list_all (\<lambda> signs.
      let paired_signs = zip ?qs signs in
        lookup_sem_M F paired_signs = (Some True)) 
      signs_list
      ) ?data"
  have "elim_forall F = create_disjunction ?new_data"
    unfolding elim_forall.simps  Let_def 
    by fastforce
  then have "eval (create_disjunction ?new_data) xs"
    using assms
    by presburger
  then obtain a where a_prop1: "a \<in> set ?new_data"
    "(eval (assump_to_atom_fm (fst a)) xs)"
    using create_disjunction_eval
    by blast 
  then have a_prop2: "a \<in> set ?data"
    "(list_all (\<lambda> signs.
      let paired_signs = zip ?qs signs in
        lookup_sem_M F paired_signs = (Some True)) 
      (snd a))"
     apply (smt (verit, best) mem_Collect_eq set_filter)
    by (smt (verit, del_insts) a_prop1(1) mem_Collect_eq set_filter split_def)
  have a_in: "(fst a, snd a) \<in> set (sign_determination_inner ?reindexed_univ_qs [])"
    using a_prop2(1) by auto 
  have "\<And>p n. (p,n) \<in> set (fst a) \<Longrightarrow> satisfies_evaluation xs p n"
    using a_prop1(2) assump_to_atom_fm_conjunction
    by blast 
  from sign_determination_inner_gives_noncomp_signs_at_roots[OF a_in this]
  have "set (snd a) =
    consistent_sign_vectors_R (map (eval_mpoly_poly xs) ?reindexed_univ_qs) UNIV"
    by auto
  then have csv: "(consistent_sign_vec (map (eval_mpoly_poly xs) ?reindexed_univ_qs)) x \<in> set (snd a)"
    unfolding consistent_sign_vectors_R_def by auto
      (* Some rewriting with map sign and using reindexed_univ_qs_eval*)
  have map_rel1: "map (Sturm_Tarski.sign) (map (\<lambda>p. poly p x) (map (eval_mpoly_poly xs) (map (map_poly (lowerPoly 0 1)) (univariate_in (extract_polys F) 0))))
= (consistent_sign_vec (map (eval_mpoly_poly xs) ?reindexed_univ_qs)) x"
    unfolding consistent_sign_vec_def Sturm_Tarski.sign_def 
    by auto
  then have  map_rel2: "map (eval_mpoly (x # xs)) (extract_polys F) =
    map (\<lambda>p. poly p x) (map (eval_mpoly_poly xs) (map (map_poly (lowerPoly 0 1)) (univariate_in (extract_polys F) 0)))"
    using reindexed_univ_qs_eval[of _ "(extract_polys F)"] by auto
  then have map_rel3: "map Sturm_Tarski.sign (map (eval_mpoly (x # xs)) (extract_polys F)) =
    map (Sturm_Tarski.sign) (map (\<lambda>p. poly p x) (map (eval_mpoly_poly xs) (map (map_poly (lowerPoly 0 1)) (univariate_in (extract_polys F) 0))))"
    by auto
  have map_rel4: "map Sturm_Tarski.sign (map (eval_mpoly (x # xs)) (extract_polys F)) =  map (mpoly_sign (x#xs)) ?qs"
    unfolding mpoly_sign_def by auto
  have "map (mpoly_sign (x#xs)) ?qs =(consistent_sign_vec (map (eval_mpoly_poly xs) ?reindexed_univ_qs)) x "
    using map_rel1 map_rel2 map_rel3 map_rel4
    by (metis list.inj_map_strong of_rat_hom.injectivity)
      (* May take a couple of seconds to load *)
  then obtain signs where signs_prop: "signs \<in> set (snd a)"
    "signs = map (mpoly_sign (x#xs)) ?qs"
    using csv by auto
  then have lookup_sem_match: "Some (eval F (x#xs)) = lookup_sem_M F (zip ?qs signs)"
    using * extract_polys_semantics by auto
  have "lookup_sem_M F (zip ?qs signs) = Some (True)"
    using a_prop2(2) signs_prop(1) unfolding Let_def
    by (smt (verit, ccfv_SIG) lookup_sem_match a_prop2(2) list.pred_mono_strong mem_Collect_eq option.simps(1) set_filter subset_code(1) subset_set_code) 
  then show ?thesis
    using lookup_sem_match by auto
qed

lemma assump_to_atom_fm_eval:
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation xs p n"
  shows "(eval (assump_to_atom_fm assumps) xs)"
  using assms
proof (induct assumps)
  case Nil
  then show ?case by auto
next
  case (Cons a assumps)
  then have h1: "eval (assump_to_atom_fm assumps) xs"
    by simp
  have sat_eval: "satisfies_evaluation xs (fst a) (snd a)"
    using Cons.prems by auto
  have h2: "eval (Atom (assump_to_atom ((fst a), (snd a)))) xs"
  proof - 
    {assume *: "snd a = 0"
      then have "eval (Atom (assump_to_atom ((fst a), (snd a)))) xs"
        using sat_eval unfolding satisfies_evaluation_def eval_mpoly_def
          Sturm_Tarski.sign_def 
        by (smt (verit, del_insts) aEval.simps(1) assump_to_atom.simps eval.simps(1) less_numeral_extra(3) of_int_hom.eq_iff)
          (* May take a couple seconds to load *)
    } moreover
    {assume *: "0 < snd a"
      then have "(eval_mpoly xs (fst a)) > 0"
        using sat_eval unfolding satisfies_evaluation_def Sturm_Tarski.sign_def
        by (smt (verit, del_insts) of_int_hom.eq_iff)
          (* May take a second to load *)
      then have "aEval (Less (-(fst a))) xs"
        using * unfolding eval_mpoly_def by auto
      then have " aEval (assump_to_atom a) xs"
        using * assump_to_atom.simps[of "fst a" "snd a"] by auto
      then have "eval (Atom (assump_to_atom ((fst a), (snd a)))) xs"
        by auto
    } moreover
    {assume *: "0 > snd a"
      then have "(eval_mpoly xs (fst a)) < 0"
        using sat_eval unfolding satisfies_evaluation_def Sturm_Tarski.sign_def
        by (smt (z3) of_int_hom.eq_iff sign_simps(1) sign_simps(3))
          (* May take a second to load *)
      then have "aEval (Less ((fst a))) xs"
        using * unfolding eval_mpoly_def by auto
      then have " aEval (assump_to_atom a) xs"
        using * assump_to_atom.simps[of "fst a" "snd a"] by auto
      then have "eval (Atom (assump_to_atom ((fst a), (snd a)))) xs"
        by auto
    }
    ultimately show ?thesis
      by linarith 
  qed
  then show ?case 
    using h1 h2
    by (metis assump_to_atom_fm.simps(2) eval.simps(4) prod.exhaust_sel) 
qed

lemma create_disjunction_true:
  assumes "(assumps, signs) \<in> set data"
  assumes  "(eval (assump_to_atom_fm assumps) xs)"
  shows "eval (create_disjunction data) xs"
  using assms 
proof (induct data)
  case Nil
  then show ?case by auto
next
  case (Cons a data)
  then show ?case
    by (metis create_disjunction.simps(2) eval.simps(5) prod.exhaust_sel set_ConsD) 
qed

lemma eval_elim_forall_correct2:
  fixes F:: "atom fm"
  assumes "countQuantifiers F = 0"
  assumes "(\<forall>x. (eval F (x#xs)))"
  shows "eval (elim_forall F) xs"
proof - 
  let ?qs = "extract_polys F"
  let ?univ_qs = "univariate_in ?qs 0"
  let ?reindexed_univ_qs = "map (map_poly (lowerPoly 0 1)) ?univ_qs"
  let ?data = "sign_determination_inner ?reindexed_univ_qs []"
  let ?new_data = "filter (\<lambda>(assumps, signs_list). 
      list_all (\<lambda> signs.
      let paired_signs = zip ?qs signs in
        lookup_sem_M F paired_signs = (Some True)) 
      signs_list
      ) ?data"
  have h1: "elim_forall F = create_disjunction ?new_data"
    unfolding elim_forall.simps Let_def 
    by fastforce
  have "\<And>p n. (p,n) \<in> set [] \<Longrightarrow> satisfies_evaluation xs p n"
    by auto
      (*Uses that we have all the branches *)
  then obtain assumps signs where assumps_signs: "(assumps, signs) \<in> set ?data"
    "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation xs p n"
    using get_all_valuations[of "[]" xs]
    by blast 
  then have assump_to_atom_eval: "(eval (assump_to_atom_fm assumps) xs)"
    using assump_to_atom_fm_eval
    by blast 
  then have a_in: "(assumps, signs) \<in> set (sign_determination_inner ?reindexed_univ_qs [])"
    using assumps_signs(1)
    by auto
  from sign_determination_inner_gives_noncomp_signs_at_roots[OF a_in assumps_signs(2)]
  have signs_is_csvs: "set signs =
    consistent_sign_vectors_R (map (eval_mpoly_poly xs) ?reindexed_univ_qs) UNIV"
    by auto
      (* uses "(\<forall>x. (eval F (x#xs)))" and lookup_sem *)
  have "\<And> sign. sign \<in> set signs \<Longrightarrow>
          lookup_sem_M F (zip ?qs sign) = (Some True)"
  proof - 
    fix sign 
    assume "sign \<in> set signs"
    have "\<exists>(x::real). sign = consistent_sign_vec (map (eval_mpoly_poly xs) ?reindexed_univ_qs) x"
      using signs_is_csvs unfolding consistent_sign_vectors_R_def
      using \<open>sign \<in> set signs\<close> by auto
    then obtain x where x_prop: "sign = consistent_sign_vec (map (eval_mpoly_poly xs) ?reindexed_univ_qs) x"
      by auto
    have map_rel1: "map (Sturm_Tarski.sign) (map (\<lambda>p. poly p x) (map (eval_mpoly_poly xs) (map (map_poly (lowerPoly 0 1)) (univariate_in (extract_polys F) 0))))
    = (consistent_sign_vec (map (eval_mpoly_poly xs) ?reindexed_univ_qs)) x"
      unfolding consistent_sign_vec_def Sturm_Tarski.sign_def 
      by auto
    then have  map_rel2: "map (eval_mpoly (x # xs)) (extract_polys F) =
    map (\<lambda>p. poly p x) (map (eval_mpoly_poly xs) (map (map_poly (lowerPoly 0 1)) (univariate_in (extract_polys F) 0)))"
      using reindexed_univ_qs_eval[of _ "(extract_polys F)"] by auto
    then have map_rel3: "map Sturm_Tarski.sign (map (eval_mpoly (x # xs)) (extract_polys F)) =
    map (Sturm_Tarski.sign) (map (\<lambda>p. poly p x) (map (eval_mpoly_poly xs) (map (map_poly (lowerPoly 0 1)) (univariate_in (extract_polys F) 0))))"
      by auto
    have map_rel4: "map Sturm_Tarski.sign (map (eval_mpoly (x # xs)) (extract_polys F)) =  map (mpoly_sign (x#xs)) ?qs"
      unfolding mpoly_sign_def by auto
    have "map (mpoly_sign (x#xs)) ?qs =(consistent_sign_vec (map (eval_mpoly_poly xs) ?reindexed_univ_qs)) x "
      using map_rel1 map_rel2 map_rel3 map_rel4
      by (metis (no_types, lifting) list.inj_map_strong of_rat_hom.injectivity)
        (* May take a second to load *)
    then have "sign = map (mpoly_sign (x#xs)) ?qs"
      using x_prop by auto 
    then have "Some (eval F (x#xs)) = lookup_sem_M F (zip ?qs sign)"
      using assms(1) extract_polys_semantics by auto
    then show "lookup_sem_M F (zip ?qs sign) = (Some True)"
      using assms(2) by auto 
  qed
  then have "list_all (\<lambda> sign.
        let paired_signs = zip ?qs sign in
          lookup_sem_M F paired_signs = (Some True)) 
        signs"
    by (meson Ball_set_list_all) 
  then have h2: "(assumps, signs) \<in> set ?new_data" 
    using assumps_signs(1)
    by (smt (verit, del_insts) case_prod_conv mem_Collect_eq set_filter) 
      (* using create_disjunction lemma *)
  show ?thesis 
    using h1 h2 assump_to_atom_eval create_disjunction_true
    by presburger
qed

lemma eval_elim_forall_correct:
  fixes F:: "atom fm"
  assumes "countQuantifiers F = 0"
  shows "(\<forall>x. (eval F (x#xs))) = eval (elim_forall F) xs"
  using eval_elim_forall_correct2 eval_elim_forall_correct1
  using assms by blast

(* This theorem relies extensively on many helper lemmas*)
theorem elim_forall_correct:
  fixes F:: "atom fm"
  assumes "countQuantifiers F = 0"
  shows "eval (AllQ F) xs = eval (elim_forall F) xs"
  using eval_elim_forall_correct
  using assms eval.simps(8) by blast 

lemma elim_exists_correct:
  fixes F:: "atom fm"
  assumes "countQuantifiers F = 0"
  shows "eval (ExQ F) xs = eval (elim_exist F) xs"
  using elim_forall_correct
  by (metis (no_types, opaque_lifting) assms countQuantifiers.simps(6) elim_exist_def eval.simps(6) eval.simps(7) eval.simps(8))


subsection "Correctness of QE"
lemma assump_to_atom_no_quantifiers:
  shows "countQuantifiers (assump_to_atom_fm a) = 0"
proof (induct a)
  case Nil
  then show ?case by auto
next
  case (Cons a1 a2)
  then show ?case 
    using countQuantifiers.simps
    by (smt (verit, best) add.right_neutral assump_to_atom_fm.elims list.simps(1))
qed

lemma create_disjunction_no_quantifiers:
  shows "countQuantifiers (create_disjunction ell) = 0"
proof (induct ell)
  case Nil
  then show ?case by auto 
next
  case (Cons a ell)
  then show ?case
    using assump_to_atom_no_quantifiers
    by (metis add.right_neutral countQuantifiers.simps(5) create_disjunction.elims list.simps(1) list.simps(3)) 
qed

lemma elim_forall_no_quantifiers:
  fixes F:: "atom fm"
  shows "countQuantifiers (elim_forall F) = 0"
  using create_disjunction_no_quantifiers
  by (metis elim_forall.simps)

lemma elim_exists_no_quantifiers:
  fixes F:: "atom fm"
  shows "countQuantifiers (elim_exist F) = 0"
  using elim_forall_no_quantifiers
  using countQuantifiers.simps(6) elim_exist_def by presburger 

lemma qe_removes_quantifiers:
  shows "countQuantifiers (qe F) = 0"
proof (induct F)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  then show ?case by auto
next
  case (And F1 F2)
  then show ?case by auto
next
  case (Or F1 F2)
  then show ?case by auto
next
  case (Neg F)
  then show ?case by auto
next
  case (ExQ F)
  then show ?case 
    using elim_exists_no_quantifiers qe.simps(7) by presburger
next
  case (AllQ F)
  then show ?case 
    using elim_forall_no_quantifiers
    using qe.simps(8) by presburger
next
  case (ExN n F)
  then show ?case
  proof (induct n)
    case 0
    then show ?case 
      by auto 
  next
    case (Suc n)
    then show ?case 
      using elim_exists_no_quantifiers
      by simp
  qed
next
  case (AllN n F)
  then show ?case
  proof (induct n)
    case 0
    then show ?case 
      by auto 
  next
    case (Suc n)
    then show ?case 
      using elim_forall_no_quantifiers
      by (metis funpow.simps(2) o_apply qe.simps(9))
  qed
qed

lemma elim_exist_N_correct:
  assumes "countQuantifiers F = 0"
  shows "eval (ExN n F) xs = eval ((elim_exist ^^ n) F) xs"
  using assms
proof (induct n arbitrary: xs F)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  have "eval (ExN (Suc n) F) xs = eval (ExN n (ExQ F)) xs"
    using  unwrapExist' by auto
  moreover have "... =  eval (ExN n (elim_exist F)) xs"
    using elim_exists_correct Suc.prems
    by auto 
  moreover have "... =  eval ((elim_exist ^^ n) (elim_exist F)) xs"
    using Suc.hyps[of " elim_exist F"] elim_exists_no_quantifiers 
    by auto 
  moreover have "... =  eval ((elim_exist ^^ (n+1)) F) xs"
    using funpow_Suc_right unfolding o_def
    by (smt (verit, best) o_apply semiring_norm(174))
  ultimately show ?case
    by (metis semiring_norm(174))
qed

lemma elim_all_N_correct:
  assumes "countQuantifiers F = 0"
  shows "eval (AllN n F) xs = eval ((elim_forall ^^ n) F) xs"
  using assms 
proof (induct n arbitrary: xs F)
  case 0
  then show ?case
    by (metis clearQuantifiers.simps(11) funpow_0 opt') 
next
  case (Suc n)
  have "eval (AllN (Suc n) F) xs = eval (AllN n (AllQ F)) xs"
    using  unwrapForall' by auto
  moreover have "... =  eval (AllN n (elim_forall F)) xs"
    using elim_forall_correct Suc.prems
    using eval.simps(9) by presburger 
  moreover have "... =  eval ((elim_forall ^^ n) (elim_forall F)) xs"
    using Suc.hyps[of " elim_forall F"] elim_forall_no_quantifiers
    by presburger 
  moreover have "... =  eval ((elim_forall ^^ (n+1)) F) xs"
    using funpow_Suc_right unfolding o_def
    by (smt (verit, best) o_apply semiring_norm(174))
  ultimately show ?case
    by (metis semiring_norm(174))
qed

theorem qe_correct:
  fixes F:: "atom fm"
  shows "eval F xs = eval (qe F) xs"
proof (induct F arbitrary: xs)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  then show ?case by auto
next
  case (And F1 F2)
  then show ?case
    using eval.simps 
    by auto
next
  case (Or F1 F2)
  then show ?case
    using eval.simps 
    by auto
next
  case (Neg F)
  then show ?case 
    using eval.simps 
    by auto
next
  case (ExQ F)
  have "countQuantifiers (qe F) = 0"
    using qe_removes_quantifiers by auto
  from elim_exists_correct[OF this]
  have h: "eval (ExQ (qe F)) xs = eval (elim_exist (qe F)) xs"
    .
  have "eval (ExQ F) xs = eval ( ExQ (qe F)) xs"
    using ExQ.hyps
    by simp 
  then show ?case 
    using h
    by auto 
next
  case (AllQ F)
  have "countQuantifiers (qe F) = 0"
    using qe_removes_quantifiers by auto
  from elim_forall_correct[OF this]
  have h: "eval (AllQ (qe F)) xs = eval (elim_forall (qe F)) xs"
    .
  have "eval (AllQ F) xs = eval (AllQ (qe F)) xs"
    using AllQ.hyps
    by simp 
  then show ?case 
    using h
    using qe.simps(8) by presburger 
next
  case (ExN n F)
  have cq: "countQuantifiers (qe F) = 0"
    using qe_removes_quantifiers by auto
  have h: "eval (ExN n F) xs = eval (ExN n (qe F)) xs"
    using ExN.hyps
    by simp 
  have "eval (ExN n (qe F)) xs = eval ((elim_exist ^^ n) (qe F)) xs"
    using elim_exist_N_correct[OF cq] .
  then show ?case
    using h by auto
next
  case (AllN n F)
  have cq: "countQuantifiers (qe F) = 0"
    using qe_removes_quantifiers by auto
  have h: "eval (AllN n F) xs = eval (AllN n (qe F)) xs"
    using AllN.hyps
    by simp 
  have "eval (AllN n (qe F)) xs = eval ((elim_forall ^^ n) (qe F)) xs"
    using elim_all_N_correct[OF cq] .
  then show ?case
    using h by auto
qed

theorem qe_extended_correct:
  fixes F:: "atom fm"
  shows "eval F xs = eval (qe_with_VS F) xs"
  using qe_correct VSLEG
  by (simp add: qe_with_VS_def)

end