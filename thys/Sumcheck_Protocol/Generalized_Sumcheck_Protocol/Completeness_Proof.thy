(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Completeness Proof for the Sumcheck Protocol\<close>

theory Completeness_Proof
  imports
    Sumcheck_Protocol
begin

context multi_variate_polynomial begin

text \<open>Completeness proof\<close>

theorem completeness_inductive:  
  assumes 
    \<open>v = (\<Sum>\<sigma> \<in> substs (set (map fst rm)) H. eval p \<sigma>)\<close>
    \<open>vars p \<subseteq> set (map fst rm)\<close>
    \<open>distinct (map fst rm)\<close>
    \<open>H \<noteq> {}\<close>
  shows 
    "sumcheck honest_prover u (H, p, v) r_prev rm"
  using assms
proof(induction honest_prover u "(H, p, v)" r_prev rm arbitrary: H p v rule: sumcheck.induct)
  case (1 s H p v r_prev)
  then show ?case by(simp)
next
  case (2 s H p v r_prev x r rm)

  note IH = 2(1)    \<comment> \<open>induction hypothesis\<close>

  let ?V = "set (map fst rm)"
  let ?q = "(\<Sum>\<sigma> \<in> substs ?V H. inst p \<sigma>)"

  have \<open>vars p \<subseteq> insert x ?V\<close> \<open>x \<notin> ?V\<close> \<open>distinct (map fst rm)\<close>
    using 2(3-4) by(auto)

  \<comment> \<open>evaluation check\<close>
  have \<open>(\<Sum>\<sigma> \<in> substs (insert x ?V) H. eval p \<sigma>) = (\<Sum>h\<in>H. eval ?q [x \<mapsto> h])\<close>
  proof - 
    have "(\<Sum>\<sigma>\<in>substs (insert x ?V) H. eval p \<sigma>) = 
          (\<Sum>h\<in>H. (\<Sum>\<sigma> \<in> substs ?V H. eval p ([x \<mapsto> h] ++ \<sigma>)))" 
      using \<open>x \<notin> ?V\<close> 
      by(auto simp add: sum_merge)
    also have "\<dots> = (\<Sum>h\<in>H. eval ?q [x \<mapsto> h])"
      using \<open>vars p \<subseteq> insert x ?V\<close>
      by(auto simp add: eval_sum_inst)
    finally show ?thesis .
  qed
  moreover 
  \<comment> \<open>recursive check\<close>
  have \<open>sumcheck honest_prover () (H, inst p [x \<mapsto> r], eval ?q [x \<mapsto> r]) r rm\<close>
  proof -
    have \<open>vars (inst p [x \<mapsto> r]) \<subseteq> ?V\<close> 
      using \<open>vars p \<subseteq> insert x ?V\<close> vars_inst by fastforce
    moreover
    have "eval ?q [x \<mapsto> r] = (\<Sum>\<sigma> \<in> substs ?V H. eval (inst p [x \<mapsto> r]) \<sigma>)" 
      using \<open>vars p \<subseteq> insert x ?V\<close> \<open>x \<notin> set (map fst rm)\<close>
      by (auto simp add: eval_sum_inst_commute)
    ultimately
    show ?thesis using IH \<open>distinct (map fst rm)\<close> \<open>H \<noteq> {}\<close> 
      by (simp add: honest_prover_def)
  qed
  ultimately show ?case using 2(2-3,5)
    by (simp add: honest_prover_def honest_prover_vars honest_prover_deg)
qed


corollary completeness:  
  assumes 
    \<open>(H, p, v) \<in> Sumcheck\<close>
    \<open>vars p = set (map fst rm)\<close>   
    \<open>distinct (map fst rm)\<close>
    \<open>H \<noteq> {}\<close>
  shows 
    "sumcheck honest_prover u (H, p, v) r rm"
  using assms
  by (auto simp add: Sumcheck_def intro: completeness_inductive)

end

end