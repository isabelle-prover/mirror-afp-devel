theory Sum_Distribution
imports Probability
begin


typ "nat + nat"


term "case a of Inl e \<Rightarrow> e"
term "(case_sum (\<lambda>a. undefined) (\<lambda>e. e)) a"

definition "Sum_pmf p Da Db = (bernoulli_pmf p) \<bind> (%b. if b then map_pmf Inl Da else map_pmf Inr Db )"

lemma b0: "bernoulli_pmf 0 = return_pmf False" 
apply(rule pmf_eqI) apply(case_tac i)
  by(simp_all)  
lemma b1: "bernoulli_pmf 1 = return_pmf True" 
apply(rule pmf_eqI) apply(case_tac i)
  by(simp_all)  


lemma Sum_pmf_0: "Sum_pmf 0 Da Db = map_pmf Inr Db"
unfolding Sum_pmf_def
apply(rule pmf_eqI) 
  by(simp add: b0 bind_return_pmf)

lemma Sum_pmf_1: "Sum_pmf 1 Da Db = map_pmf Inl Da"
unfolding Sum_pmf_def
apply(rule pmf_eqI) 
  by(simp add: b1 bind_return_pmf)


definition "Proj1_pmf D = map_pmf (%a. case a of Inl e \<Rightarrow> e) (cond_pmf D {f. (\<exists>e. Inl e = f)})"


lemma A: "(case_sum (\<lambda>e. e) (\<lambda>a. undefined)) (Inl e) = e"
  by(simp)

lemma B: "inj (case_sum (\<lambda>e. e) (\<lambda>a. undefined))"
  oops

lemma none: "(set_pmf (bernoulli_pmf (5 / 10) \<bind>
          (\<lambda>b. if b then map_pmf Inl Da else map_pmf Inr Db))
          \<inter> {f. (\<exists>e. Inl e = f)}) \<noteq> {}"
    apply(simp add: UNIV_bool)
      using set_pmf_not_empty by fast

lemma C: "set_pmf (Proj1_pmf (Sum_pmf 0.5 Da Db)) = set_pmf Da"
proof -

    
  show ?thesis
    unfolding Sum_pmf_def Proj1_pmf_def
    apply(simp add: )
    using none[of Da Db] apply(simp add: set_cond_pmf UNIV_bool)
      by force
qed

thm integral_measure_pmf

thm pmf_cond pmf_cond[OF none]
(*
lemma "Proj1_pmf (Sum_pmf 0.5 Da Db) =  Da" 
proof -

  have kl: "\<And>e. pmf (map_pmf Inr Db) (Inl e) = 0"
    apply(simp only: pmf_eq_0_set_pmf)
    apply(simp) by blast

  term "(\<integral>x. pmf M x \<partial>count_space X)"
  term measure_pmf.prob
  term "measure M"

  have "(LINT x|count_space {f. \<exists>e. Inl e = f}.
        measure_pmf.prob Da (Inl -` {x})) = 1"
        sorry

  have "\<And>x. Inr -` {x} = e"
    unfolding vimage_def sorry

  have "\<And>x. x\<in>{f. \<exists>e. Inl e = f} \<Longrightarrow> Inr -` {x} = {}"
    sorry

  have "(LINT x|count_space {f. \<exists>e. Inl e = f}.
        measure_pmf.prob Db (Inr -` {x})) = 0"
        unfolding vimage_def
        apply(simp add: integral_pmf[symmetric]) sorry
 

  have ll: "measure_pmf.prob
           (bernoulli_pmf (1 / 2) \<bind>
            (\<lambda>b. if b then map_pmf Inl Da else map_pmf Inr Db))
           {f. \<exists>e. Inl e = f} = 1/2" 
     apply(simp add: integral_pmf[symmetric] pmf_bind)
     apply(subst integral_add)
      using integrable_pmf apply fast
      using integrable_pmf apply fast 
        apply(simp)
     using kl 
     

     unfolding bind_pmf_def bernoulli_pmf_def
     apply(simp)   sorry
     

  have E: "(cond_pmf
       (bernoulli_pmf (5 / 10) \<bind>
        (\<lambda>b. if b then map_pmf Inl Da else map_pmf Inr Db))
       {f. \<exists>e. Inl e = f}) =
    map_pmf Inl Da"
    apply(rule pmf_eqI)
      apply(subst pmf_cond)
      using none[of Da Db] apply (simp)
        apply(auto)
          apply(subst pmf_bind)
          apply(simp add: kl ll)
        defer 
          apply(simp only: pmf_eq_0_set_pmf) by auto

  have ID: "case_sum (\<lambda>e. e) (\<lambda>a. undefined) \<circ> Inl = id"
    by fastforce
  show ?thesis 
    unfolding Sum_pmf_def Proj1_pmf_def
    apply(simp only: E)
    apply(simp add: pmf.map_comp ID)
  done

qed

lemma proj1_pmf: "p>0 \<Longrightarrow> Proj1_pmf (Sum_pmf p Da Db) =  Da" sorry

definition "Proj2_pmf D = map_pmf (%a. case a of Inr e \<Rightarrow> e) (cond_pmf D {f. (\<exists>e. Inl e = f)})"

lemma proj2_pmf: "p<1 \<Longrightarrow> Proj2_pmf (Sum_pmf p Da Db) =  Db" sorry



definition "invSum invA invB D x i == invA (Proj1_pmf D) x i \<and> invB (Proj2_pmf D) x i"


lemma invSum_split: "p>0 \<Longrightarrow> p<1 \<Longrightarrow> invA Da x i \<Longrightarrow> invB Db x i \<Longrightarrow> invSum invA invB (Sum_pmf p Da Db) x i"
by(simp add: invSum_def proj1_pmf proj2_pmf)

term "(%a. case a of Inl e \<Rightarrow> Inl (fa e) | Inr e \<Rightarrow> Inr (fb e))"
definition "f_on2 fa fb = (%a. case a of Inl e \<Rightarrow> map_pmf Inl (fa e) | Inr e \<Rightarrow> map_pmf Inr (fb e))"
 
term "bind_pmf"


lemma Sum_bind_pmf: assumes a: "bind_pmf Da fa = Da'" and b: "bind_pmf Db fb = Db'"
  shows "bind_pmf (Sum_pmf p Da Db) (f_on2 fa fb)
              = Sum_pmf p Da' Db'"
proof -
  { fix x
  have "(if x then map_pmf Inl Da else map_pmf Inr Db) \<bind>
                 case_sum (\<lambda>e. map_pmf Inl (fa e))
                  (\<lambda>e. map_pmf Inr (fb e))
            =
        (if x then map_pmf Inl Da \<bind> case_sum (\<lambda>e. map_pmf Inl (fa e))
                  (\<lambda>e. map_pmf Inr (fb e))
              else map_pmf Inr Db \<bind> case_sum (\<lambda>e. map_pmf Inl (fa e))
                  (\<lambda>e. map_pmf Inr (fb e)))"
                  apply(simp) done
  also
    have "\<dots> = (if x then map_pmf Inl (bind_pmf Da fa) else map_pmf Inr (bind_pmf Db fb))"
      by(auto simp add: map_pmf_def bind_assoc_pmf bind_return_pmf)
  also
    have "\<dots> = (if x then map_pmf Inl Da' else map_pmf Inr Db')"
      using a b by simp
  finally
    have "(if x then map_pmf Inl Da else map_pmf Inr Db) \<bind>
                 case_sum (\<lambda>e. map_pmf Inl (fa e))
                  (\<lambda>e. map_pmf Inr (fb e)) = (if x then map_pmf Inl Da' else map_pmf Inr Db')" .  
  } note gr=this



  show ?thesis
    unfolding Sum_pmf_def f_on2_def
    apply(rule pmf_eqI) 
    apply(case_tac i)
    by(simp_all add: bind_return_pmf bind_assoc_pmf gr)
qed

definition "sum_map_pmf fa fb = (%a. case a of Inl e \<Rightarrow> Inl (fa e) | Inr e \<Rightarrow> Inr (fb e))"
 
lemma Sum_map_pmf: assumes a: "map_pmf fa Da = Da'" and b: "map_pmf fb Db = Db'"
  shows "map_pmf (sum_map_pmf fa fb) (Sum_pmf p Da Db) 
              = Sum_pmf p Da' Db'"
proof -
  have "map_pmf (sum_map_pmf fa fb) (Sum_pmf p Da Db)
        = bind_pmf (Sum_pmf p Da Db) (f_on2 (\<lambda>x. return_pmf (fa x)) (\<lambda>x. return_pmf (fb x)))"
        using a b
  unfolding map_pmf_def sum_map_pmf_def f_on2_def
    by(auto simp add: bind_return_pmf sum.case_distrib) 
also
  have "\<dots> = Sum_pmf p Da' Db'"
 using assms[unfolded map_pmf_def]  
 by(rule Sum_bind_pmf )
finally
  show ?thesis .
qed

*)


end