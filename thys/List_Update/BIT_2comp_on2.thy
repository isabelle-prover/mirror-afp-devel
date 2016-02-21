theory BIT_2comp_on2
imports BIT Phase_Partitioning
begin

lemma E_bernoulli3: assumes "0<p"
    and "p<1"
    and "finite (set_pmf (bind_pmf (bernoulli_pmf p) f))"
    shows "E (bind_pmf (bernoulli_pmf p) f) = E(f True)*p + E(f False)*(1-p)" (is "?L = ?R")
proof -

  have T: "(\<Sum>a\<in>(\<Union>x. set_pmf (f x)). (a * pmf (f True) a))
            = E(f True)"
    unfolding E_def
    apply(subst integral_measure_pmf[of "bind_pmf (bernoulli_pmf p) f"])
      using assms apply(simp)
      using assms apply(simp add: set_pmf_bernoulli) apply blast
      using assms by(simp add: set_pmf_bernoulli) 
  have F: "(\<Sum>a\<in>(\<Union>x. set_pmf (f x)). (a * pmf (f False) a))
            = E(f False)"
    unfolding E_def
    apply(subst integral_measure_pmf[of "bind_pmf (bernoulli_pmf p) f"])
      using assms apply(simp)
      using assms apply(simp add: set_pmf_bernoulli) apply blast
      using assms by(simp add: set_pmf_bernoulli) 

  have "?L = (\<Sum>a\<in>(\<Union>x. set_pmf (f x)).
       a *
       (pmf (f True) a * p +
        pmf (f False) a * (1 - p)))"  
  unfolding E_def 
  apply(subst integral_measure_pmf[of "bind_pmf (bernoulli_pmf p) f"])
    using assms apply(simp)
    apply(simp)
    using assms apply(simp add: set_pmf_bernoulli )
    by(simp add: pmf_bind)
  also have "\<dots> = (\<Sum>a\<in>(\<Union>x. set_pmf (f x)). (a * pmf (f True) a * p)
                                    + (a * pmf (f False) a * (1 - p)))"
    apply(rule setsum.cong) apply(simp) by algebra
  also have "\<dots> = (\<Sum>a\<in>(\<Union>x. set_pmf (f x)). (a * pmf (f True) a * p))
                  + (\<Sum>a\<in>(\<Union>x. set_pmf (f x)). (a * pmf (f False) a * (1 - p)))"
    by (simp add: setsum.distrib)
  also have "\<dots> = (\<Sum>a\<in>(\<Union>x. set_pmf (f x)). (a * pmf (f True) a)) * p
                  + (\<Sum>a\<in>(\<Union>x. set_pmf (f x)). (a * pmf (f False) a )) * (1 - p)"
    by (simp add: setsum_left_distrib)    
  also have "\<dots> = ?R" unfolding T F by simp
  finally show ?thesis .
qed 


term "Partial_Cost_Model.config'_rand"
          
definition config2 where
  "config2 A rs init n == config'_rand A init (take n rs)"

lemma config2_config: "config2 (I,S) qs (bind_pmf (I init) (\<lambda>is. return_pmf (init, is))) i 
          = config'' (I,S) qs init i"
by(simp add: config2_def) 
                

lemma config2_append: "x\<le>length xs \<Longrightarrow> config2 (I, S) (xs @ ys) init x
          =  config2 (I, S) xs init x"
apply(induct x) by(simp_all add: nth_append config2_def)

lemma config2_append_le: "x<length xs \<Longrightarrow> config2 (I, S) (xs @ ys) init x
          =  config2 (I, S) xs init x"
using config2_append less_imp_le by metis


lemma config2_append_ge: "config2 (I, S) (xs @ ys) init (length xs+x)
          =  config2 (I, S) ys (config2 (I,S) xs init (length xs)) x"
apply(induct x)
  apply(simp add: config2_append config2_def)
  apply(simp add: bind_assoc_pmf bind_return_pmf)
    by(simp add: config'_rand_append config2_def)

lemma config2_append_ge2: "x\<ge>length xs \<Longrightarrow> config2 (I, S) (xs @ ys) init x
          =  config2 (I, S) ys (config2 (I,S) xs init (length xs)) (x-length xs)"
using config2_append_ge by (metis le_add_diff_inverse) 

definition T_on_n2 where "T_on_n2 A qs init n == T_on_rand'_n A init qs n"

lemma T_on_n2_append: "i < length \<sigma> \<Longrightarrow> T_on_n2 (I,S) (\<sigma> @ qs) init i = T_on_n2 (I,S) \<sigma> init i"
 by(simp add: nth_append config2_append T_on_n2_def) 


lemma T_on_n2_nn: "i\<le>length qs \<Longrightarrow> (T_on_n2 (I,S) qs init i)\<ge>0"
apply(cases i) apply(simp_all add: T_on_n2_def)
  apply(rule E_nonneg)
    apply(simp add: split_def) 
  apply(rule E_nonneg)
    by(simp add: split_def)


definition T\<^sub>p_on2  where
  "T\<^sub>p_on2 A qs init == \<Sum>i<(length qs). T_on_n2 A qs init i"

lemma aha: "T\<^sub>p_on2 A qs init = Partial_Cost_Model.T_on_rand' A init qs"
apply(subst T_on_rand'_as_sum) unfolding T\<^sub>p_on2_def T_on_n2_def by simp
  

lemma splitquerylist2: " 
       T\<^sub>p_on2 (I,S) (xs@ys) init
     = T\<^sub>p_on2 (I,S) xs init + T\<^sub>p_on2 (I,S) ys (config2 (I,S) xs init (length xs))"
unfolding aha config2_def 
  apply(subst take_all) 
    apply(simp)
    by(rule T_on_rand'_append)
 

lemma config_append: "i < length \<sigma>  \<Longrightarrow> config'' (I, S) (\<sigma>@xs) [x, y] i = config'' (I, S) \<sigma> [x, y] i"
apply(induct i) apply(simp_all add: nth_append) done
 
subsubsection "go through the four phase types"


definition "type0 init x y = do {
                  (a::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  (b::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  return_pmf  ([x,y], ([a,b],init))
                }"

lemma T\<^sub>p_on2_from_type0: "T\<^sub>p_on2 BIT qs (type0 [x,y] x y) = T\<^sub>p_on_rand BIT [x,y] qs"
unfolding T\<^sub>p_on2_def T_on_rand_as_sum
proof(rule setsum.cong, goal_cases)
  case (2 e)
  show ?case unfolding T_on_n2_def
  apply(simp only: config2_config[symmetric])
    apply(simp add: config2_def BIT_init_def bind_assoc_pmf map_pmf_def type0_def bind_return_pmf)
     by(simp add: bind_commute_pmf[where C= "(\<lambda>a b.  return_pmf ([x, y], ([a,b],[x,y])))"])     
qed simp

definition "type1 init x y = do {
                  (a::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  (b::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  return_pmf ( if ~[a,b]!(index init x)\<and>[a,b]!(index init y) then ([y,x], ([a,b],init))
                         else ([x,y], ([a,b],init)))
                }"



definition "inv_BIT init qs x y = (config2 BIT qs (type0 init x y) (length qs) = (type0 init (last qs) (other (last qs) x y)))"



lemma bit_yx: assumes "x \<noteq> y" "qs \<in> lang (Star(Times (Atom y) (Atom x))) "
       "init \<in> {[x,y],[y,x]}"
   shows "T\<^sub>p_on2 BIT (qs@r) (type1 init x y) = 0.75 * length qs + T\<^sub>p_on2 BIT r (type1 init x y)
    \<and> config2 BIT qs (type1 init x y) (length qs) = (type1 init x y)"
proof -
  from assms have "qs \<in> star ({[y]} @@ {[x]})" by (simp)
  from this assms show ?thesis
  proof (induct qs rule: star_induct)
    case (append u v)
    then have uyx: "u = [y,x]" by auto 
     
    have yy: "T\<^sub>p_on2 BIT (v @ r) (type1 init x y) = 0.75*length v + T\<^sub>p_on2 BIT r (type1 init x y) 
            \<and> config2 BIT v (type1 init x y) (length v) = (type1 init x y)"
        apply(rule append(3)) 
          apply(fact)+
          using append(2,6) by(simp_all)
    note A=append(4)
 
    have s2: "config2 BIT [y,x] (type1 init x y) (Suc (Suc 0)) = (type1 init x y)"
      unfolding type1_def  
      apply(simp add: A bind_return_pmf BIT_step_def config2_def bind_assoc_pmf split_def)
      proof (goal_cases)
        case 1                                                 
        show ?case (is "bernoulli_pmf (1 / 2) \<bind> (\<lambda>xa. bernoulli_pmf (1 / 2) \<bind>
                          (\<lambda>xb. return_pmf (?A xa xb))) = bernoulli_pmf (1 / 2) \<bind> (\<lambda>xa. bernoulli_pmf (1 / 2) \<bind>
                          (\<lambda>xb. return_pmf (?B xa xb)))")
        proof -
            {fix a b
                 have "?A a b = (if  [a,b]!(index init x)\<and>~[a,b]!(index init y) then ([y,x], ([~a,~b],init)) 
                         else ([x,y], ([~a,~b],init)))"  
                    (* these two steps need some time, because they calculate the behaviour of
                        BIT for 2^3=8 cases each *)
                    using append(4,6)
                    apply(cases "init=[x,y]")
                      apply(simp add: step_def swap_def mtf2_def) 
                      apply(simp add: step_def swap_def mtf2_def) 
                    done
            } note man=this
 
            show ?case unfolding man
            apply(rule pmf_eqI)
              apply(simp only: pmf_bind) 
              using append(4,6)
                    apply(cases "init=[x,y]") 
                  apply(simp) apply smt   
                  apply(simp) apply smt done
        qed
    qed

                             
      
    have ta: "T\<^sub>p_on2 BIT u (type1 init x y) = 1.5"
      unfolding T\<^sub>p_on2_def type1_def uyx T_on_n2_def
      apply(simp add: bind_return_pmf bind_assoc_pmf   BIT_step_def split_def)

      apply(subst E_bernoulli3) 
        apply(simp) apply(simp) apply(simp)
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp)   
        using A 
          using assms(3)
            apply(cases "init=[x,y]")
            by(simp_all add: t\<^sub>p_def step_def swap_def mtf2_def) 
  

    have "BIT_2comp_on2.config2 BIT (u @ v) (type1 init x y) (length (u @ v)) =
           config2 BIT v (config2 BIT u (type1 init x y) (length u)) (length v)"
            by (simp add:  config2_append_ge)
    also have "\<dots> = type1 init x y" by (simp add: s2 uyx yy)
    finally have config: "BIT_2comp_on2.config2 BIT (u @ v) (type1 init x y) (length (u @ v)) = type1 init x y" .


    have "T\<^sub>p_on2 BIT (u @ (v @ r)) (type1 init x y) 
        = T\<^sub>p_on2 BIT u (type1 init x y) + T\<^sub>p_on2 BIT (v@r) ( config2 BIT u (type1 init x y) (length u))"
          by (simp only: splitquerylist2)
    also have "\<dots> =  T\<^sub>p_on2 BIT u (type1 init x y) + T\<^sub>p_on2 BIT (v@r) (type1 init x y)"
      unfolding uyx apply(simp)

      by(simp only: s2) 
    also have "\<dots> = T\<^sub>p_on2 BIT u (type1 init x y) + 0.75*length v + T\<^sub>p_on2 BIT r (type1 init x y)"
        by(simp only: yy) 
    also have "\<dots> = 2*0.75 + 0.75*length v + T\<^sub>p_on2 BIT r (type1 init x y)" by(simp add: ta) 
    also have "\<dots> = 0.75 * (2+length v) + T\<^sub>p_on2 BIT r (type1 init x y)"
      by (simp add: ring_distribs del: add_2_eq_Suc' add_2_eq_Suc)
    also have "\<dots> = 0.75 * length (u @ v) + T\<^sub>p_on2 BIT r (type1 init x y)"
      using uyx by simp
    finally show ?case using config by simp 
  qed (simp add: config2_def)
qed

lemma bit_yxyx: assumes "x \<noteq> y" "init \<in> {[x,y],[y,x]}"
      "qs \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
 shows "T\<^sub>p_on2 BIT (qs@r) (type0 init x y) = 0.75* length qs + T\<^sub>p_on2 BIT r (type1 init x y)
       \<and> config2 BIT qs (type0 init x y) (length qs) = (type1 init x y)"
proof -
  obtain u v where uu: "u \<in> lang (Times (Atom y) (Atom x))"
                      and vv: "v \<in> lang (seq[ Star(Times (Atom y) (Atom x))])"
                      and qsuv: "qs = u @ v" 
                      using assms(3)
                      by (auto simp: conc_def)  
  from uu have uyx: "u = [y,x]" by(auto)

  from qsuv uyx have vqs: "length v = length qs - 2" by auto
  from qsuv uyx  have vqs2: "length v + 2 = length qs" by auto



    have A: "x\<noteq>y" "init \<in> {[x,y],[y,x]}" using assms by auto

   have s2: "config2 BIT [y,x] (type0 init x y) (Suc (Suc 0)) = (type1 init x y)"
      unfolding type0_def type1_def  config2_def
      apply(simp add: A bind_return_pmf  BIT_step_def bind_assoc_pmf split_def)
      proof (goal_cases)
        case 1                                                 
        show ?case (is "bernoulli_pmf (1 / 2) \<bind> (\<lambda>xa. bernoulli_pmf (1 / 2) \<bind>
                          (\<lambda>xb. return_pmf (?A xa xb))) = bernoulli_pmf (1 / 2) \<bind> (\<lambda>xa. bernoulli_pmf (1 / 2) \<bind>
                          (\<lambda>xb. return_pmf (?B xa xb)))")
        proof -
            {fix a b
                 have "?A a b = (if  [a,b]!(index init x)\<and>~[a,b]!(index init y) then ([y,x], ([~a,~b],init)) 
                         else ([x,y], ([~a,~b],init)))"
                  using A 
                    apply(cases "init=[x,y]")
                    by(simp_all add: step_def swap_def mtf2_def) 
            } note man=this
 
            show ?case unfolding man
            apply(rule pmf_eqI)
              apply(simp only: pmf_bind) 
              using A 
                  apply(cases "init=[x,y]")
                  apply(simp_all) by smt+  
        qed
    qed
     
                             
      
    have ta: "T\<^sub>p_on2 BIT u (type0 init x y) = 1.5"
      unfolding  T\<^sub>p_on2_def type0_def uyx T_on_n2_def 
      apply(simp add: bind_return_pmf bind_assoc_pmf BIT_step_def split_def)
apply(subst E_bernoulli3) 
        apply(simp) apply(simp) apply(simp)
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp)  
        using A  
        apply(cases "init=[x,y]")
          by(simp_all add: t\<^sub>p_def step_def swap_def mtf2_def) 
 
    have tat: "T\<^sub>p_on2 BIT (v@r) (type1 init x y) =   0.75*length v +T\<^sub>p_on2 BIT r (type1 init x y)
            \<and> config2 BIT v (type1 init x y) (length v) = (type1 init x y)"
        apply(rule bit_yx)
      apply(fact)+
      using vv A by(simp_all)



    have "config2 BIT (u @ v) (type0 init x y) (length (u @ v)) =
           config2 BIT v (config2 BIT u (type0 init x y) (length u)) (length v)"
            by (simp add:  config2_append_ge)
    also have "\<dots> = type1 init x y" by (auto simp add: s2 uyx tat)
    finally have config: "config2 BIT (u @ v) (type0 init x y) (length (u @ v)) = type1 init x y" .

    have "T\<^sub>p_on2 BIT (u @ (v @ r)) (type0 init x y) 
        = T\<^sub>p_on2 BIT u (type0 init x y) + T\<^sub>p_on2 BIT (v@r) ( config2 BIT u (type0 init x y) (length u))"
          by (simp only: splitquerylist2)
    also have "\<dots> =  T\<^sub>p_on2 BIT u (type0 init x y) + T\<^sub>p_on2 BIT (v@r) (type1 init x y)"
      unfolding uyx apply(simp)

      by(simp only: s2) 
    also have "\<dots> = T\<^sub>p_on2 BIT u (type0 init x y) + 0.75*length v + T\<^sub>p_on2 BIT r (type1 init x y)"
        by(simp only: tat) 
    also have "\<dots> = 2*0.75 + 0.75*length v + T\<^sub>p_on2 BIT r (type1 init x y)" by(simp add: ta) 
    also have "\<dots> = 0.75 * (2+length v) + T\<^sub>p_on2 BIT r (type1 init x y)"
      by (simp add: ring_distribs del: add_2_eq_Suc' add_2_eq_Suc) 
    also have "\<dots> = 0.75 * length (u @ v) + T\<^sub>p_on2 BIT r (type1 init x y)"
      using uyx by simp
    finally show ?thesis using qsuv config by simp
qed
 

lemma BIT_a_config: assumes "qs \<in> Lxx x y" "x \<noteq> y"
    " init \<in> {[x,y],[y,x]}"
   "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
  shows  "config2 BIT qs (type0 init x y) (length qs) = (type0 init y x)"
proof - 
  from assms(4) have alt: "qs = [x,y,y] \<or> qs = [y,y]" apply(simp) by fastforce
  with assms(2) show ?thesis 
    unfolding  type0_def config2_def
    apply(cases "qs=[y,y]")
      apply(simp add: mtf2_def step_def split_def swap_def bind_assoc_pmf bind_return_pmf BIT_step_def )
      apply(rule pmf_eqI)
        apply(simp only: pmf_bind)  
          using assms(3)
            apply(cases "init=[x,y]")
            apply(simp_all add: swap_def) 

      apply(simp add: mtf2_def step_def split_def swap_def bind_assoc_pmf bind_return_pmf BIT_step_def )
      apply(rule pmf_eqI)
        apply(simp only: pmf_bind)  
          using assms(3)
            apply(cases "init=[x,y]")
            apply(simp_all add: swap_def) apply smt+
    done
qed


lemma BIT_a: "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y 
       \<Longrightarrow> init \<in> {[x,y],[y,x]} \<Longrightarrow>
  qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y]) \<Longrightarrow>
   T\<^sub>p_on2 BIT qs (type0 init x y) = 1.5"
  apply (auto simp add: conc_def  T_on_n2_def  mtf_def T\<^sub>p_on2_def type0_def)
    apply(simp_all add: bind_return_pmf map_pmf_def bind_assoc_pmf split_def BIT_step_def t\<^sub>p_def step_def mtf2_def swap_def)
    apply(simp_all add: E_bernoulli3)
    apply(simp_all add: swap_def) 
    done


lemma bit_a: assumes "qs \<in> Lxx x y" "x \<noteq> y"
 "init \<in> {[x,y],[y,x]}"
 "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
 shows "T\<^sub>p_on2 BIT qs (type0 init x y)  \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y]) 
    \<and> inv_BIT init qs x y"
proof -
  from assms have lqs: "last qs = y" by fastforce
  from assms BIT_a have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y) = 1.5" by auto
  with OPT2_A[OF assms(2,4)] have "T\<^sub>p_on2 BIT qs (type0 init x y) \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" by auto
  moreover from BIT_a_config assms lqs have "inv_BIT init qs x y" unfolding inv_BIT_def by(auto simp: other_def)
  ultimately show ?thesis by simp
qed

lemma BIT_x: assumes "x\<noteq>y"
       "init \<in> {[x,y],[y,x]}" "qs \<in> lang (Plus (Atom x) One)"
 shows "T\<^sub>p_on2 BIT (qs@r) (type0 init x y) = T\<^sub>p_on2 BIT r (type0 init x y)
    \<and> config2 BIT qs (type0 init x y) (length qs) = (type0 init x y)"
proof - 
  have A: "x\<noteq>y"  using assms by auto

  have s: "config2 BIT qs (type0 init x y) (length qs) = type0 init x y"
    unfolding  type0_def config2_def using assms(2,3)
    apply(cases "init=[x,y]")
    apply(auto simp: mtf2_def step_def split_def swap_def bind_assoc_pmf bind_return_pmf BIT_step_def)
    apply(rule pmf_eqI)  
      apply(simp_all only: pmf_bind) 
          apply(simp_all)
    apply(rule pmf_eqI)  
      apply(simp_all only: pmf_bind) 
          apply(simp_all) apply(smt) done

  have t: "T\<^sub>p_on2 BIT qs (type0 init x y) = 0"
    using assms(2,3)
    apply(cases "init=[x,y]")
      unfolding  T\<^sub>p_on2_def type0_def T_on_n2_def
      apply(auto simp add: bind_return_pmf bind_assoc_pmf BIT_step_def split_def)
      apply(subst E_bernoulli3) 
        apply(simp) apply(simp) apply(simp)
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        apply(subst E_bernoulli3) 
          apply(simp) apply(simp) apply(simp) 
        using A 
          by(simp_all add: t\<^sub>p_def step_def swap_def mtf2_def) 

  have "T\<^sub>p_on2 BIT (qs@r) (type0 init x y) = T\<^sub>p_on2 BIT qs (type0 init x y) + T\<^sub>p_on2 BIT r (config2 BIT qs (type0 init x y) (length qs))"
          by (simp only: splitquerylist2)  
  also have "\<dots> = T\<^sub>p_on2 BIT r (type0 init x y)" by(simp only: t s)
  finally show ?thesis using s by simp
qed
        

lemma BIT_b: assumes "x \<noteq> y"
       "init \<in> {[x,y],[y,x]}"
    "v \<in> lang (seq [Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
    shows "T\<^sub>p_on2 BIT v (type0 init x y) = 0.75 * length v - 0.5
    \<and> config2 BIT v (type0 init x y) (length v) = (type0 init y x)"
proof -
  have lenvmod: "length v mod 2 = 0"
  proof -
    from assms(3) have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}" by(simp add: conc_assoc)
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[y]} @@ {[y]}" by (metis concE)
    then have "p = [y,x]" "r=[y,y]" by auto
    with pqr have a: "length v = 4+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show "length v mod 2 = 0" by auto
  qed
        
  have A: "x\<noteq>y"  using assms by auto
 
  from assms(3) have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom y, Atom y])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom y, Atom y])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[y,y]" by auto
  from aa have lena: "length a > 0" by auto
  from vab bb have lenv: "length v = length a + 2" by auto
 
  from bit_yxyx assms(1,2) aa have stars: "T\<^sub>p_on2 BIT (a @ b) (type0 init x y) = 0.75 * length a + T\<^sub>p_on2 BIT b (type1 init x y)"
                             and s2: "config2 BIT a (type0 init x y) (length a) = type1 init x y"  by fast+

  have t: "T\<^sub>p_on2 BIT b (type1 init x y) = 1"
    unfolding bb  using assms(2) 
    apply(cases "init=[x,y]")
      unfolding  T\<^sub>p_on2_def type1_def T_on_n2_def
      apply(simp_all add: bind_return_pmf bind_assoc_pmf BIT_step_def split_def) 
        apply(simp_all add: E_bernoulli3)             
        using A  
          by(simp_all add: t\<^sub>p_def step_def swap_def mtf2_def) 
 
    have s: "config2 BIT [y, y] (type1 init x y) (Suc (Suc 0)) = type0 init y x"
      unfolding type0_def type1_def config2_def
        using assms(1,2)
       apply(cases "init=[x,y]")
      apply(auto simp: step_def map_pmf_def split_def bind_assoc_pmf bind_return_pmf BIT_step_def)
      apply(rule pmf_eqI)
        apply(simp only: pmf_bind)   
            apply(simp add: mtf2_def swap_def) 
      apply(rule pmf_eqI)
        apply(simp only: pmf_bind)   
            apply(simp add: mtf2_def swap_def)  
      done 


    have "config2 BIT (a @ b) (type0 init x y) (length (a @ b)) =
           config2 BIT b (config2 BIT a (type0 init x y) (length a)) (length b)"
            by (simp add:  config2_append_ge)
    also have "\<dots> = type0 init y x" by (auto simp add: s2 vab bb s)
    finally have config: "config2 BIT (a @ b) (type0 init x y) (length (a @ b)) = type0 init y x" .

  have calc: "3 * Suc (Suc (length a)) / 4 - 1 / 2 = 3 * (2+length a) / 4 - 1 / 2" by simp

  from t stars have "T\<^sub>p_on2 BIT (a @ b) (type0 init x y) = 0.75 * length a + 1" by auto
  then have whatineed: "T\<^sub>p_on2 BIT v (type0 init x y) = 0.75 * length v - 0.5" unfolding lenv 
    unfolding vab
    by(simp add: ring_distribs del: add_2_eq_Suc')
  with config vab show ?thesis by simp
qed


lemma bit_b: assumes "qs \<in> Lxx x y" "x \<noteq> y"
      "init \<in> {[x,y],[y,x]}"
   "qs \<in> lang (seq[Plus (Atom x) One, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom y, Atom y])"
 shows  "T\<^sub>p_on2 BIT qs (type0 init x y)  \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y])
    \<and> inv_BIT init qs x y"
proof -
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
        and qsuv: "qs = u @ v" 
        using assms
        by (auto simp: conc_def) 
  have lenv: "length v mod 2 = 0 \<and> last v = y \<and> v\<noteq>[]"
  proof -
    from vv have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}" by simp
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[y]} @@ {[y]}" by (metis concE)
    then have rr: "p = [y,x]" "r=[y,y]" by auto
    with pqr have a: "length v = 4+length q" by auto

    have "last v = last r" using pqr rr by auto
    then have c: "last v = y" using rr by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b c show ?thesis by auto
  qed
        
  from vv have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom y, Atom y])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom y, Atom y])"
                      and vab: "v = a @ b" 
                      by(erule concE)  

  from BIT_x[OF assms(2,3) uu] have u_t: "T\<^sub>p_on2 BIT (u @ v) (type0 init x y) = T\<^sub>p_on2 BIT v (type0 init x y)"
      and u_c: "config2 BIT u (type0 init x y) (length u) = type0 init x y" by auto
  from BIT_b[OF assms(2,3) vv] have b_t: "T\<^sub>p_on2 BIT v (type0 init x y) = 0.75 * length v - 0.5"
      and  b_c: "config2 BIT v (type0 init x y) (length v) = (type0 init y x)" by auto

  have "T\<^sub>p_on2 BIT qs (type0 init x y) = T\<^sub>p_on2 BIT (u@v) (type0 init x y)"
    by(simp add: T\<^sub>p_on2_from_type0 qsuv)
  also have "\<dots> = T\<^sub>p_on2 BIT v (type0 init x y)" by(rule u_t)
  also have "\<dots> = 0.75 * length v - 0.5" by(rule b_t)
  finally have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y) = 0.75 * length v - 0.5" .


  (* config *)

    have "config2 BIT (u @ v) (type0 init x y) (length (u @ v)) =
           config2 BIT v (config2 BIT u (type0 init x y) (length u)) (length v)"
            by (simp add:  config2_append_ge)
    also have "\<dots> = type0 init y x" by (auto simp add: u_c b_c)
    finally have config: "config2 BIT qs (type0 init x y) (length qs) = type0 init y x" using qsuv by auto

    from lenv have "v \<noteq> []"  "last v = y" by auto
    then have 1:  "last qs = y" using last_appendR qsuv by simp 
    then have 2: "other (last qs) x y = x" unfolding other_def by simp

  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom y, Atom y])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_B) by(fact)+

  show ?thesis using BIT OPT lenv config 1 2  by (auto simp: inv_BIT_def)
qed



lemma BIT_c: assumes "x \<noteq> y" "init \<in> {[x,y],[y,x]}"
    "v \<in> lang (seq [Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
 shows  "T\<^sub>p_on2 BIT v (type0 init x y) = 0.75 * length v - 0.5
        \<and> config2 BIT v (type0 init x y) (length v) = type0 init x y"
proof -
  have lenvmod: "length v mod 2 = 1"
  proof -
    from assms(3) have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}" by(simp add: conc_assoc)
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[x]}" by (metis concE)
    then have "p = [y,x]" "r=[x]" by auto
    with pqr have a: "length v = 3+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show "length v mod 2 = 1" by auto
  qed
        
  have A: "x\<noteq>y"  using assms by auto
 
  from assms(3) have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom x])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom x])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[x]" by auto
  from aa have lena: "length a > 0" by auto
  from vab bb have lenv: "length v = length a + 1" by auto
 
  from bit_yxyx assms(1,2) aa have stars: "T\<^sub>p_on2 BIT (a @ b) (type0 init x y) = 0.75 * length a + T\<^sub>p_on2 BIT b (type1 init x y)"
                             and s2: "config2 BIT a (type0 init x y) (length a) = type1 init x y"  apply(auto) by fast+

  have t:"T\<^sub>p_on2 BIT b (type1 init x y) = 0.25"
    unfolding bb  using assms(2) 
      apply(cases "init=[x,y]")
      unfolding  T\<^sub>p_on2_def type1_def T_on_n2_def
      apply(simp_all add: bind_return_pmf bind_assoc_pmf BIT_step_def split_def)
      apply(simp_all add: E_bernoulli3) 
        using A  
          apply(simp_all add: t\<^sub>p_def step_def swap_def mtf2_def) done
 
 
    have s: "config2 BIT [x] (type1 init  x y) (Suc 0) = type0 init  x y" 
    unfolding type0_def type1_def config2_def
      using assms(1,2)
      apply(cases "init=[x,y]")
      apply(auto simp add: step_def split_def swap_def bind_assoc_pmf bind_return_pmf BIT_step_def)
      apply(rule pmf_eqI)
        apply(simp only: pmf_bind)  
            apply(simp add: mtf2_def swap_def)  
      apply(rule pmf_eqI)
        apply(simp only: pmf_bind)  
            apply(simp add: mtf2_def swap_def)  apply(smt)
      done 


    have "config2 BIT (a @ b) (type0 init x y) (length (a @ b)) =
           config2 BIT b (config2 BIT a (type0 init x y) (length a)) (length b)"
            by (simp add:  config2_append_ge)
    also have "\<dots> = type0 init x y" by (auto simp add: s2 vab bb s)
    finally have config: "config2 BIT (a @ b) (type0 init x y) (length (a @ b)) = type0 init x y" .

 
  from t stars have "T\<^sub>p_on2 BIT (a @ b) (type0 init x y) = 3/4 * length a + 1/4" by auto 
  then have whatineed: "T\<^sub>p_on2 BIT v (type0 init x y) = 0.75 * length v - 0.5" unfolding lenv 
    unfolding vab
      by (simp add: ring_distribs del: One_nat_def) 
  with config vab show ?thesis by simp
qed
 

lemma bit_c: assumes "qs \<in> Lxx x y" "x \<noteq> y" "init \<in> {[x,y],[y,x]}"
  " qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x])"
 shows "T\<^sub>p_on2 BIT qs (type0 init x y) \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])
        \<and> inv_BIT init qs x y"
proof -
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
        and qsuv: "qs = u @ v" 
        using assms
        by (auto simp: conc_def) 
  have lenv: "length v mod 2 = 1 \<and> length v \<ge> 3 \<and> last v = x"
  proof -
    from vv have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}" by auto
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in> {[x]}" by (metis concE)
    then have rr: "p = [y,x]"  "r=[x]" by auto
    with pqr have a: "length v = 3+length q" by auto

    have "last v = last r" using pqr rr by auto
    then have c: "last v = x" using rr by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b c show "length v mod 2 = 1 \<and> length v \<ge> 3 \<and> last v = x" by auto
  qed


  from BIT_x[OF assms(2,3) uu] have u_t: "T\<^sub>p_on2 BIT (u @ v) (type0 init x y) = T\<^sub>p_on2 BIT v (type0 init x y)"
      and u_c: "config2 BIT u (type0 init x y) (length u) = type0 init x y" by auto
  from BIT_c[OF assms(2,3) vv] have c_t: "T\<^sub>p_on2 BIT v (type0 init x y) = 0.75 * length v - 0.5"
      and  c_c: "config2 BIT v (type0 init x y) (length v) = (type0 init x y)" by auto

  have "T\<^sub>p_on2 BIT qs (type0 init x y) = T\<^sub>p_on2 BIT (u@v) (type0 init x y)"
    by(simp add: T\<^sub>p_on2_from_type0 qsuv)
  also have "\<dots> = T\<^sub>p_on2 BIT v (type0 init x y)" by(rule u_t)
  also have "\<dots> = 0.75 * length v - 0.5" by(rule c_t)
  finally have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y) = 0.75 * length v - 0.5" .


  (* config *)

    have "config2 BIT (u @ v) (type0 init x y) (length (u @ v)) =
           config2 BIT v (config2 BIT u (type0 init x y) (length u)) (length v)"
            by (simp add:  config2_append_ge)
    also have "\<dots> = type0 init x y" by (auto simp add: u_c c_c)
    finally have config: "config2 BIT qs (type0 init x y) (length qs) = type0 init x y" using qsuv by auto
 
    from lenv have "v \<noteq> []"  "last v = x" by auto
    then have 1:  "last qs = x" using last_appendR qsuv by simp 
    then have 2: "other (last qs) x y = y" unfolding other_def by simp
    
  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom x])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_C) by(fact)+

  have vgt3: "length v \<ge> 3" using lenv by simp
  have "T\<^sub>p_on2 BIT qs (type0 init x y)  = 0.75 * length v - 0.5" using BIT by simp
  also have "\<dots> \<le> 1.75 * (length v - 1)/2"
  proof -
    have "10 + 6 * length v \<le> 7 * Suc (length v) 
        \<longleftrightarrow> 10 + 6 * length v \<le> 7 * length v + 7" by auto
    also have "\<dots> \<longleftrightarrow> 3 \<le> length v" by auto
    also have "\<dots> \<longleftrightarrow> True" using vgt3 by auto
    finally have A: " 6 * length v - 4 \<le> 7 * (length v - 1)" by simp
    show ?thesis apply(simp) using A by linarith 
  qed    
  also have "\<dots> = 1.75 * (length v div 2)"
  proof -
    from mod_div_equality have "length v = length v div 2 * 2 + length v mod 2" by auto
    with lenv have "length v = length v div 2 * 2 + 1" by auto 
    then have "(length v - 1) / 2 = length v div 2" by simp
    then show ?thesis by simp
  qed
  also have "\<dots> = 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" using OPT by auto
  finally show ?thesis using config 1 2  by (simp add: inv_BIT_def)
qed

lemma BIT_d_config: assumes "qs \<in> Lxx x y" "x \<noteq> y" "init \<in> {[x,y],[y,x]}"
    "qs \<in> lang (seq [Atom x, Atom x])"
 shows "config2 BIT qs (type0 init x y) (length qs) = (type0 init (last qs) (other (last qs) x y))"
proof -
  from assms have "qs = [x,x]" by auto
  then show ?thesis unfolding config2_def
     using assms(3)
     apply(cases "init=[x,y]")
     apply(simp_all add: other_def type0_def  BIT_step_def bind_return_pmf bind_assoc_pmf)
      by(simp_all add: mtf2_def step_def split_def swap_def bind_assoc_pmf bind_return_pmf BIT_step_def)
qed


lemma BIT_d : assumes "qs \<in> Lxx x y" "x \<noteq> y" "init \<in> {[x,y],[y,x]}"
    "qs \<in> lang (seq [Atom x, Atom x])"
  shows "T\<^sub>p_on2 BIT qs (type0 init x y) = 0"
proof -
  from assms have qs: "qs = [x,x]" by auto 
  
  have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y) = 0"
    unfolding T\<^sub>p_on2_def  qs type0_def T_on_n2_def
    using assms(2,3) 
    apply(cases "init=[x,y]")
    apply(simp_all add: bind_return_pmf bind_assoc_pmf split_def BIT_step_def t\<^sub>p_def step_def mtf2_def)
    done
  show ?thesis using  BIT by simp
qed

lemma bit_d: assumes "qs \<in> Lxx x y" "x \<noteq> y" "init \<in> {[x,y],[y,x]}"
    "qs \<in> lang (seq [Atom x, Atom x])"
  shows "T\<^sub>p_on2 BIT qs (type0 init x y) \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])
    \<and> inv_BIT init qs x y"
proof -
  from assms have qs: "qs = [x,x]" by auto
  then have OPT: "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = 0" by (simp add: t\<^sub>p_def step_def)
  
  show ?thesis using OPT BIT_d BIT_d_config assms  by (simp add: inv_BIT_def)
qed


lemma D': "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y \<Longrightarrow>
    init \<in> {[x,y],[y,x]} \<Longrightarrow>
      T\<^sub>p_on2 BIT qs (type0 init x y) \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])
       \<and> inv_BIT init qs x y"
apply(rule LxxI[where P="(\<lambda>x y qs.  T\<^sub>p_on2 BIT qs (type0 init x y) \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<and>
                                    inv_BIT init qs x y)"])
  apply(fact bit_d)
  apply(fact bit_b)
  apply(fact bit_c)
  apply(fact bit_a)
  by (simp)   

(* we need to restrict to nat here, because we rely on checking for equivalence of regular
expressions (the phases) which is uptodate only available for nat *)
theorem BIT_OPT2: "x \<noteq> y \<Longrightarrow> set \<sigma> \<subseteq> {x,y}
    \<Longrightarrow> init \<in> {[x,y], [y,x]}
     \<Longrightarrow> T\<^sub>p_on2 BIT \<sigma> (type0 init (x::nat) y) \<le> 1.75 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 1.75"
 proof (induction "length \<sigma>" arbitrary: \<sigma> x y rule: less_induct)
  case (less \<sigma>)
  show ?case
  proof (cases "\<exists>xs ys. \<sigma>=xs@ys \<and> xs \<in> Lxx x y")
    case True
    then obtain xs ys where qs: "\<sigma>=xs@ys" and xsLxx: "xs \<in> Lxx x y" by auto

    with Lxx1 have len: "length ys < length \<sigma>" by fastforce
    from qs(1) less(3) have ysxy: "set ys \<subseteq> {x,y}" by auto

    have xsset: "set xs \<subseteq> {x, y}" using less(3) qs by auto
    from xsLxx Lxx1 have lxsgt1: "length xs \<ge> 2" by auto
    then have xs_not_Nil: "xs \<noteq> []" by auto

    from D'[OF xsLxx less(2,4) ] 
      have D1: "T\<^sub>p_on2 BIT xs (type0 init x y) \<le> 1.75 * T\<^sub>p [x, y] xs (OPT2 xs [x, y])" 
        and s: "config2 BIT xs (type0 init x y) (length xs) = (type0 init (last xs) (other (last xs) x y))" by (auto simp: inv_BIT_def)

    term "config"

    from xsLxx Lxx_ends_in_two_equal obtain pref e where "xs = pref @ [e,e]" by metis
    then have endswithsame: "xs = pref @ [last xs, last xs]" by auto 

    let ?c' = "[last xs, other (last xs) x y]" 

    have setys: "set ys \<subseteq> {x,y}" using qs less by auto 
    have setxs: "set xs \<subseteq> {x,y}" using qs less by auto 
    have lxs: "last xs \<in> set xs" using xs_not_Nil by auto
    from lxs setxs have lxsxy: "last xs \<in> {x,y}" by auto  
    from lxs setxs have otherxy: "other (last xs) x y \<in> {x,y}" by (simp add: other_def)
    from less(2) have other_diff: "last xs \<noteq> other (last xs) x y" by(simp add: other_def)
    from lxsxy otherxy other_diff have setxy: "{last xs, other (last xs) x y} = {x,y}" by force

    have "T\<^sub>p_on2 BIT ys (config2 BIT xs (type0 init x y) (length xs)) = T\<^sub>p_on2 BIT ys (type0 init (last xs) (other (last xs) x y))"
      using s by auto
    also from len have "\<dots> \<le> 1.75 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 1.75"       
            apply(subst less(1))
              apply(simp_all add: other_diff setxy setys)
              using otherxy other_diff lxsxy less(4) apply(cases "last xs=x") by (auto)
    finally have c: "T\<^sub>p_on2 BIT ys (config2 BIT xs (type0 init x y) (length xs))  \<le> 1.75 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 1.75" .
    

    have well: "T\<^sub>p [x, y] xs (OPT2 xs [x, y]) + T\<^sub>p ?c' ys (OPT2 ys ?c')
        = T\<^sub>p [x, y] (xs @ ys) (OPT2 (xs @ ys) [x, y])"
          apply(rule OPTauseinander[where pref=pref])
            apply(fact)+
            using lxsxy other_diff otherxy apply(fastforce)
            apply(simp)
            using endswithsame by simp  

    have E0: "T\<^sub>p_on2 BIT \<sigma> (type0 init x y)
          =  T\<^sub>p_on2 BIT (xs@ys)  (type0 init x y)" using qs by auto 
    also have E1: "\<dots> = T\<^sub>p_on2 BIT xs (type0 init x y) + T\<^sub>p_on2 BIT ys (config2 BIT xs (type0 init x y) (length xs))"
            by (rule splitquerylist2)

    also have E2: "\<dots> \<le> T\<^sub>p_on2 BIT xs (type0 init x y) + 1.75 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 1.75"
        using c by simp
    also have E3: "\<dots> \<le> 1.75 * T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + 1.75 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 1.75"
        using D1  T\<^sub>p_on2_from_type0  by simp        
    also have "\<dots> \<le> 1.75 * (T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + T\<^sub>p ?c' ys (OPT2 ys ?c')) + 1.75"
        by(auto)
    also have  "\<dots> = 1.75 * (T\<^sub>p [x,y] (xs@ys) (OPT2 (xs@ys) [x,y])) + 1.75"
      using well by auto 
    also have E4: "\<dots> = 1.75 * (T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y])) + 1.75"
        using qs by auto
    finally show ?thesis .
 
  next
    case False
    note f1=this
    from Lxx_othercase[OF less(3) this, unfolded hideit_def] have
        nodouble: "\<sigma> = [] \<or> \<sigma> \<in> lang (nodouble x y)" by  auto
    show ?thesis
    proof (cases "\<sigma> = []")
      case True
      then show ?thesis unfolding T\<^sub>p_on2_def  by(simp)
    next                           
      case False
      (* with padding *)
      from False nodouble have qsnodouble: "\<sigma> \<in> lang (nodouble x y)" by auto
      let ?padded = "pad \<sigma> x y"
      from False pad_adds2[of \<sigma> x y] less(3) obtain addum where ui: "pad \<sigma> x y = \<sigma> @ [last \<sigma>]" by auto
      from nodouble_padded[OF False qsnodouble] have pLxx: "?padded \<in> Lxx x y" .

      have E0: "T\<^sub>p_on2 BIT \<sigma> (type0 init x y) \<le> T\<^sub>p_on2 BIT ?padded (type0 init x y)"
      proof -
        have "T\<^sub>p_on2 BIT \<sigma> (type0 init x y) = setsum (T_on_n2 BIT \<sigma> (type0 init x y)) {..<length \<sigma>}"
          unfolding T\<^sub>p_on2_def by simp
        also have "\<dots>
             = setsum (T_on_n2 BIT (\<sigma> @ [last \<sigma>]) (type0 init x y)) {..<length \<sigma>}"
          proof(rule setsum.cong, goal_cases)
            case (2 t)
            then have "t < length \<sigma>" by auto 
            then show ?case by(simp only:  T_on_n2_append[unfolded ])
          qed simp
        also have "... \<le> T\<^sub>p_on2 BIT ?padded (type0 init x y)"
          unfolding ui T\<^sub>p_on2_def apply(simp)
             by(simp add: T_on_n2_nn ) 
        finally show ?thesis by auto
      qed  
 
      also from pLxx have E1: "\<dots> \<le> 1.75 * T\<^sub>p [x,y] ?padded (OPT2 ?padded [x,y])"
        using D'[OF pLxx less(2,4) ] by simp
      also have E2: "\<dots> \<le> 1.75 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 1.75"
      proof -
        from False less(2) obtain \<sigma>' x' y' where qs': "\<sigma> = \<sigma>' @ [x']" and x': "x' = last \<sigma>" "y'\<noteq>x'" "y' \<in>{x,y}" 
            by (metis append_butlast_last_id insert_iff)
        have tla: "last \<sigma> \<in> {x,y}" using less(3) False last_in_set by blast
        with x' have grgr: "{x,y} = {x',y'}" by auto
        then have "(x = x' \<and> y = y') \<or> (x = y' \<and> y = x')" using less(2) by auto
        then have tts: "[x, y] \<in> {[x', y'], [y', x']}" by blast
        
        from qs' ui have pd: "?padded = \<sigma>' @ [x', x']" by auto 

        have "T\<^sub>p [x,y] (?padded) (OPT2 (?padded) [x,y])
              = T\<^sub>p [x,y] (\<sigma>' @ [x', x']) (OPT2 (\<sigma>' @ [x', x']) [x,y])"
                unfolding pd by simp
        also have gr: "\<dots>
            \<le> T\<^sub>p [x,y] (\<sigma>' @ [x']) (OPT2 (\<sigma>' @ [x']) [x,y]) + 1"
              apply(rule OPT2_padded[where x="x'" and y="y'"])
                apply(fact)
                using grgr qs' less(3) by auto
        also have "\<dots> \<le> T\<^sub>p [x,y] (\<sigma>) (OPT2 (\<sigma>) [x,y]) + 1" 
              unfolding qs' by simp
        finally show ?thesis by auto
      qed
      finally show ?thesis .  
    qed
  qed 
qed

theorem BIT_175comp_on_2: assumes "x \<noteq> y" "set \<sigma> \<subseteq> {x,y}"
   shows "T\<^sub>p_on_rand BIT [x::nat,y] \<sigma>  \<le> 1.75 * (T\<^sub>p_opt [x,y] \<sigma>) + 1.75" 
proof -
  have "T\<^sub>p_on_rand BIT [x,y]  \<sigma>
          = T\<^sub>p_on2 BIT \<sigma> (type0 [x,y] x y)" by(simp add: T\<^sub>p_on2_from_type0)
  also have "\<dots> \<le> 1.75 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 1.75"
    apply(rule BIT_OPT2)
      by(simp_all add: assms)
  also have "\<dots> = 1.75 *  T\<^sub>p_opt [x,y] \<sigma> + 1.75"
    by(simp add: OPT2_is_opt assms)
  finally show ?thesis .
qed



end