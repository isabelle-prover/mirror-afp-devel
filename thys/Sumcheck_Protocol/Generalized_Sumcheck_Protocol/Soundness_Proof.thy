(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Soundness Proof for the Sumcheck Protocol\<close>

theory Soundness_Proof
  imports
    Probability_Tools
    Sumcheck_Protocol
begin

context multi_variate_polynomial begin

\<comment> \<open>Helper lemma: 
   Proves that the probability of two different polynomials evaluating to the same value is small.\<close>
lemma prob_roots:
  assumes "deg q2 \<le> deg p" and "vars q2 \<subseteq> {x}" 
  shows "measure_pmf.prob (pmf_of_set UNIV) 
        {r. deg q1 \<le> deg p \<and> vars q1 \<subseteq> {x} \<and> q1 \<noteq> q2 \<and> eval q1 [x \<mapsto> r] = eval q2 [x \<mapsto> r]} 
        \<le> real (deg p) / real CARD('a)"
proof -
  have "card {r. deg q1 \<le> deg p \<and> vars q1 \<subseteq> {x} \<and> 
                 q1 \<noteq> q2 \<and> eval q1 [x \<mapsto> r] = eval q2 [x \<mapsto> r]} = 
         card {r. deg q1 \<le> deg p \<and> vars q1 \<subseteq> {x} \<and> 
                  deg q2 \<le> deg p \<and> vars q2 \<subseteq> {x} \<and>
                  q1 \<noteq> q2 \<and> eval q1 [x \<mapsto> r] = eval q2 [x \<mapsto> r]}" using assms by(auto)
   also have "\<dots> \<le> deg p"  by(auto simp add: roots)
   finally show ?thesis by(auto simp add: measure_pmf_of_set divide_right_mono) 
qed   


text \<open>Soundness proof\<close>

theorem soundness_inductive:
  assumes 
    "vars p \<subseteq> set vs" and
    "deg p \<le> d" and 
    "distinct vs" and 
    "H \<noteq> {}"
  shows 
    "measure_pmf.prob 
       (pmf_of_set (tuples UNIV (length vs)))
       {rs. 
          sumcheck pr s (H, p, v) r (zip vs rs) \<and> 
          v \<noteq> (\<Sum>\<sigma> \<in> substs (set vs) H. eval p \<sigma>)} 
     \<le> real (length vs) * real d / real (CARD('a))"
  using assms
proof(induction vs arbitrary: s p v r)
  case Nil
  show ?case
    by(simp)
next
  case (Cons x vs)

  \<comment> \<open>abbreviations\<close>
  let ?prob = "measure_pmf.prob (pmf_of_set (tuples UNIV (Suc (length vs))))"
  let ?reduced_prob = "measure_pmf.prob (pmf_of_set (tuples UNIV (length vs)))"

  let ?q = "\<Sum>\<sigma> \<in> substs (set vs) H. inst p \<sigma>"      \<comment> \<open>honest polynomial q\<close>

  let ?pr_q = "fst (pr (H, p, v) x vs r s)"      \<comment> \<open>polynomial q from prover\<close>
  let ?pr_s' = "snd (pr (H, p, v) x vs r s)"     \<comment> \<open>prover's next state\<close>

  \<comment> \<open>some useful derived facts\<close> 
  have \<open>vars (p) \<subseteq> insert x (set vs)\<close> \<open>x \<notin> set vs\<close> \<open>distinct vs\<close> 
    using \<open>vars (p) \<le> set (x # vs)\<close> \<open>distinct (x # vs)\<close> by auto

  have P0: 
    \<open>?prob {r1#rs | r1 rs.                
               deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>      
               v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
               sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and> 
               v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval (p) \<sigma>) \<and> ?pr_q = ?q} = 0\<close>
  proof -
    have "(\<Sum>a\<in>H. eval (?q) [x \<mapsto> a]) = 
          (\<Sum>a\<in>H. \<Sum>\<sigma> \<in> substs (set vs) H. eval (p) ([x \<mapsto> a] ++ \<sigma>))"
      using \<open>vars (p) \<subseteq> insert x (set vs)\<close> \<open>x \<notin> set vs\<close>  
      by(auto simp add: eval_sum_inst)
    moreover 
    have "(\<Sum>a\<in>H. \<Sum>\<sigma> \<in> substs (set vs) H. eval (p) ([x \<mapsto> a] ++ \<sigma>)) =
          (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval (p) \<sigma>)" using \<open>x \<notin> set vs\<close>
      by(auto simp add: sum_merge) 
    ultimately
    have "{r1#rs | r1 rs.                      
                 v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                 v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval (p) \<sigma>) \<and> ?pr_q = ?q} = {}" 
      by(auto)    
    then show "?thesis" 
      by (intro prob_empty) (auto 4 4)
  qed

  { \<comment> \<open>left-hand-side case where we use the roots assumption\<close>
    have \<open>?prob {r1#rs | r1 rs. 
                       deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                       v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                       ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] = eval (?q) [x \<mapsto> r1]} \<le>
          ?prob {r1#rs | r1 rs. 
                       deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                       ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] = eval (?q) [x \<mapsto> r1]}\<close>
      by (intro prob_mono) (auto 4 4) 

    also have \<open>... =
          measure_pmf.prob (pmf_of_set UNIV) {r1. 
              deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
              ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] = eval (?q) [x \<mapsto> r1]}\<close>
      by (auto simp add: prob_tuples_hd_tl_indep[where Q = "\<lambda>rs. True", simplified]) 

    also have \<open>... \<le> real (deg (p)) / real CARD('a)\<close> 
      using \<open>vars (p) \<subseteq> insert x (set vs)\<close> \<open>H \<noteq> {}\<close> 
      by(auto simp add: prob_roots honest_prover_deg honest_prover_vars)

    also have \<open>... \<le> real d / real CARD('a)\<close> using \<open>deg (p) \<le> d\<close>
      by (simp add: divide_right_mono) 

    finally
    have \<open>?prob {r1#rs | r1 rs. 
                       deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                       v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                       ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] = eval (?q) [x \<mapsto> r1]}
           \<le> real d / real CARD('a)\<close> .
  }
  note RP_left = this

  {
    have *: \<open>\<And>\<alpha>. eval (?q) [x \<mapsto> \<alpha>] = (\<Sum>\<sigma> \<in> substs (set vs) H. eval (inst (p) [x \<mapsto> \<alpha>]) \<sigma>)\<close>
      using \<open>vars (p) \<subseteq> insert x (set vs)\<close> \<open>x \<notin> set vs\<close>
      by(auto simp add: eval_sum_inst_commute)

    have \<open>\<And>\<alpha>. vars (inst (p) [x \<mapsto> \<alpha>]) \<subseteq> set vs\<close> using vars_inst \<open>vars (p) \<subseteq> insert x (set vs)\<close> 
      by fastforce
    have \<open>\<And>\<alpha>. deg (inst (p) [x \<mapsto> \<alpha>]) \<le> d\<close> using deg_inst \<open>deg (p) \<le> d\<close>
      using le_trans by blast

    \<comment> \<open>right-hand-side case where we apply the induction hypothesis\<close>
    have \<open>?prob {r1#rs | r1 rs.
                       deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                       v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                       ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] \<noteq> eval (?q) [x \<mapsto> r1]}
         \<le> ?prob {r1#rs | r1 rs. 
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                       eval (?pr_q) [x \<mapsto> r1] \<noteq> (\<Sum>\<sigma> \<in> substs (set vs) H. eval (inst (p) [x \<mapsto> r1]) \<sigma>)}\<close>
      by(intro prob_mono) (auto simp add: *)

    \<comment> \<open>fix @{text "r1"}\<close>
    also have \<open>\<dots> = (\<Sum>\<alpha> \<in> UNIV.
                     ?reduced_prob {rs. 
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> \<alpha>], eval (?pr_q) [x \<mapsto> \<alpha>]) \<alpha> (zip vs rs) \<and>
                       eval (?pr_q) [x \<mapsto> \<alpha>] \<noteq> (\<Sum>\<sigma> \<in> substs (set vs) H. eval (inst (p) [x \<mapsto> \<alpha>]) \<sigma>)})
                  / real(CARD('a))\<close>
      by(auto simp add: prob_tuples_fixed_hd)

    \<comment> \<open>apply the induction hypothesis\<close>
    also have \<open>\<dots> \<le> (\<Sum>\<alpha> \<in> (UNIV::'a set). real (length vs) * real d / real CARD('a)) 
                    / real(CARD('a))\<close>
      using \<open>\<And>\<alpha>. vars (inst (p) [x \<mapsto> \<alpha>]) \<subseteq> set vs\<close> 
            \<open>\<And>\<alpha>. deg (inst (p) [x \<mapsto> \<alpha>]) \<le> d\<close> 
            \<open>distinct vs\<close> \<open>H \<noteq> {}\<close>
      by (intro divide_right_mono sum_mono Cons.IH) (auto)

    also have \<open>\<dots> = real (length vs) * real d / real CARD('a)\<close>
      by fastforce  

    finally
    have \<open>?prob {r1#rs | r1 rs. 
                       deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                       v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                       ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] \<noteq> eval (?q) [x \<mapsto> r1]}
         \<le> real (length vs) * real d / real CARD('a)\<close> .
  }
  note RP_right = this 
  
  \<comment> \<open>main equational reasoning proof\<close>
  have \<open>?prob {rs. 
          sumcheck pr s (H, p, v) r (zip (x # vs) rs) \<and> 
          v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval p \<sigma>)} 
      = ?prob {r1#rs | r1 rs. sumcheck pr s (H, p, v) r (zip (x # vs) (r1#rs))
                               \<and> v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval p \<sigma>)}\<close>
   by(intro prob_cong) (auto simp add: tuples_Suc) 

  \<comment> \<open>unfold sumcheck\<close>
  also have \<open>\<dots> = ?prob {r1#rs | r1 rs. 
                  (let (q, s') = pr (H, p, v) x vs r s in
                  deg q \<le> deg p \<and> vars q \<subseteq> {x} \<and>
                  v = (\<Sum>a \<in> H. eval q [x \<mapsto> a])  \<and> 
                  sumcheck pr s' (H, inst p [x \<mapsto> r1], eval q [x \<mapsto> r1]) r1 (zip vs rs)) \<and> 
                  v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval p \<sigma>)}\<close>
    by(intro prob_cong) (auto del: subsetI)

  also have \<open>\<dots> = ?prob {r1#rs | r1 rs . 
                  deg ?pr_q \<le> deg p \<and> vars ?pr_q \<subseteq> {x} \<and>
                  v = (\<Sum>a\<in>H. eval ?pr_q [x \<mapsto> a]) \<and>
                  sumcheck pr ?pr_s' (H, inst p [x \<mapsto> r1], eval ?pr_q [x \<mapsto> r1]) r1 (zip vs rs) \<and> 
                  v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval p \<sigma>)}\<close>
    by (intro prob_cong) (auto del: subsetI)

  \<comment> \<open>case split on whether prover's polynomial q equals honest one\<close>
   also have \<open>\<dots> = ?prob {r1#rs | r1 rs.                
                     deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>      
                     v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                     sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and> 
                     v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval (p) \<sigma>) \<and> ?pr_q = ?q} 
                + ?prob {r1#rs | r1 rs. 
                     deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                     v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                     sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                     v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval (p) \<sigma>) \<and> ?pr_q \<noteq> ?q}\<close>
     by(intro prob_disjoint_cases) auto
 
  \<comment> \<open>first probability is 0\<close>
  also have \<open>\<dots> = ?prob {r1#rs | r1 rs. 
                     deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                     v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                     sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                     v \<noteq> (\<Sum>\<sigma> \<in> substs (insert x (set vs)) H. eval (p) \<sigma>) \<and> ?pr_q \<noteq> ?q}\<close> 
    by (simp add: P0)

  \<comment> \<open>dropped condition\<close>
  also have \<open>\<dots> \<le> ?prob {r1#rs | r1 rs. 
                     deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                     v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                     sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                     ?pr_q \<noteq> ?q}\<close>
    by(intro prob_mono) (auto)

  also have \<open>\<dots> =
          ?prob {r1#rs | r1 rs.  
                       deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                       v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a]) \<and>
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                       ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] = eval (?q) [x \<mapsto> r1]} + 
          ?prob {r1#rs | r1 rs.  
                       deg (?pr_q) \<le> deg (p) \<and> vars (?pr_q) \<subseteq> {x} \<and>
                       v = (\<Sum>a\<in>H. eval (?pr_q) [x \<mapsto> a])  \<and>
                       sumcheck pr (?pr_s') (H, inst (p) [x \<mapsto> r1], eval (?pr_q) [x \<mapsto> r1]) r1 (zip vs rs) \<and>
                       ?pr_q \<noteq> ?q \<and> eval (?pr_q) [x \<mapsto> r1] \<noteq> eval (?q) [x \<mapsto> r1]}\<close>
    by(intro prob_disjoint_cases) (auto)

  also have \<open>\<dots> \<le> real d / real CARD('a) + 
                  (real (length vs) * real d) / real CARD('a)\<close>
    by (intro add_mono RP_left RP_right)

  also have \<open>\<dots> = (1 + real (length vs)) * real d / real CARD('a)\<close>
    by (metis add_divide_distrib mult_Suc of_nat_Suc of_nat_add of_nat_mult)

  finally show ?case by simp
qed


corollary soundness:
  assumes 
    "(H, p, v) \<notin> Sumcheck"
    "vars p = set vs" and  
    "distinct vs" and 
    "H \<noteq> {}"
  shows 
    "measure_pmf.prob 
       (pmf_of_set (tuples UNIV (arity p)))
       {rs. sumcheck pr s (H, p, v) r (zip vs rs)} 
     \<le> real (arity p) * real (deg p) / real (CARD('a))"
  using assms
proof - 
  have *: \<open>arity p = length vs\<close> using \<open>vars p = set vs\<close> \<open>distinct vs\<close> 
    by (simp add: arity_def distinct_card)

  have "measure_pmf.prob (pmf_of_set (tuples UNIV (arity p)))
          {rs. sumcheck pr s (H, p, v) r (zip vs rs)} =
        measure_pmf.prob (pmf_of_set (tuples UNIV (arity p)))
          {rs. sumcheck pr s (H, p, v) r (zip vs rs) \<and> (H, p, v) \<notin> Sumcheck}"
  using \<open>(H, p, v) \<notin> Sumcheck\<close>
    by (intro prob_cong) (auto)
  also have "\<dots> \<le> real (arity p) * real (deg p) / real (CARD('a))" using assms(2-) *
    by (auto simp add: Sumcheck_def intro!: soundness_inductive)
  finally show ?thesis by simp
qed


end 

end