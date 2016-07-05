theory BIT_2comp_on2
imports BIT Phase_Partitioning
begin

section "auxliary lemmas"

subsection "E_bernoulli3"

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


subsection "types of configurations"


definition "type0 init x y = do {
                  (a::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  (b::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  return_pmf  ([x,y], ([a,b],init))
                }"

definition "type1 init x y = do {
                  (a::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  (b::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  return_pmf ( if ~[a,b]!(index init x)\<and>[a,b]!(index init y) then ([y,x], ([a,b],init))
                         else ([x,y], ([a,b],init)))
                }"

definition "type3 init x y = do {
                  (a::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  (b::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  return_pmf ( if [a,b]!(index init x)\<and>~[a,b]!(index init y) then ([x,y], ([a,b],init))
                         else ([y,x], ([a,b],init)))
                }"

definition "type4 init x y = do {
                  (a::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  (b::bool) \<leftarrow> (bernoulli_pmf 0.5);
                  return_pmf ( if ~[a,b]!(index init y) then ([x,y], ([a,b],init))
                         else ([y,x], ([a,b],init)))
                }"


definition "BIT_inv s x i == (s = (type0 i x (hd (filter (\<lambda>y. y\<noteq>x) i) )))"

lemma BIT_inv2: "x\<noteq>y \<Longrightarrow> z\<in>{x,y} \<Longrightarrow> BIT_inv s z [x,y] = (s= type0 [x,y] z (other z x y))"
  unfolding BIT_inv_def by(auto simp add: other_def)


subsection "effect of BIT"

lemma oneBIT_step3x: 
    assumes "x\<noteq>y" "x:{x0,y0}" "y:{x0,y0}"
    shows "(type3 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is'))))
                = type1 [x0, y0] x y"
proof -
    from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto
    have "(type3 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is')))) 
            = (type3 [x0, y0] x y) \<bind> (%s. Step_rand BIT x s )"
            by (simp add: bind_assoc_pmf bind_return_pmf split_def)
  also               
    from  assms(1) kas2
    have "...
            = type1 [x0, y0] x y"
      apply(simp add: type3_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
      apply(safe) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type1_def)
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type1_def)   
          apply smt done
  finally 
    show ?thesis  .
qed 
lemma costBIT_0y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type0 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s y \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) y a))))) = 1"
using assms apply(auto)
  apply(simp_all add: type0_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done

lemma costBIT_0x: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type0 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s x \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) x a))))) = 0"
using assms apply(auto)
  apply(simp_all add: type0_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done
lemma costBIT_1x: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type1 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s x \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) x a))))) = 1/4"
using assms apply(auto)
  apply(simp_all add: type1_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done

lemma costBIT_1y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type1 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s y \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) y a))))) = 3/4"
using assms apply(auto)
  apply(simp_all add: type1_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done
  


lemma costBIT_3y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type3 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s y \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) y a))))) = 1/4"
using assms apply(auto)
  apply(simp_all add: type3_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done
  
lemma costBIT_3x: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type3 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s x \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) x a))))) = 3/4"
using assms apply(auto)
  apply(simp_all add: type3_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done

lemma costBIT_4x: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type4 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s x \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) x a))))) = 0.5"
using assms apply(auto)
  apply(simp_all add: type4_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done
lemma costBIT_4y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows
  "E (type4 [x0, y0] x y \<bind>
       (\<lambda>s. BIT_step s y \<bind>
            (\<lambda>(a, is'). return_pmf (real (t\<^sub>p (fst s) y a))))) = 0.5"
using assms apply(auto)
  apply(simp_all add: type4_def BIT_step_def bind_assoc_pmf bind_return_pmf )
  apply(simp_all add: E_bernoulli3 t\<^sub>p_def)
  done

lemma oneBIT_step4y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows "(type4 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s y \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) y a, is'))))
                = type0 [x0, y0] y x"
proof -
    from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto
    have "(type4 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s y \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) y a, is')))) 
            = (type4 [x0, y0] x y) \<bind> (%s. Step_rand BIT y s )"
            by (simp add: bind_assoc_pmf bind_return_pmf split_def)
  also               
    from  assms(1) kas2
    have "...
            = type0 [x0, y0] y x"
      apply(simp add: type4_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
      apply(safe) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type0_def)
          apply smt
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type0_def)   
          done
  finally 
    show ?thesis  .
qed 

lemma oneBIT_step0y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows "(type0 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s y \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) y a, is'))))
                = type4 [x0, y0] x y"
proof -
    from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto
    have "(type0 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s y \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) y a, is')))) 
            = (type0 [x0, y0] x y) \<bind> (%s. Step_rand BIT y s )"
            by (simp add: bind_assoc_pmf bind_return_pmf split_def)
  also               
    from  assms(1) kas2
    have "...
            = type4 [x0, y0] x y"
      apply(simp add: type0_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
      apply(safe) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type4_def)
          apply smt
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type4_def)   
          done
  finally 
    show ?thesis  .
qed 

lemma oneBIT_step3y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows "(type3 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s y \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) y a, is'))))
                = type0 [x0, y0] y x"
proof -
  from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto       
  from assms(1) kas2
  show ?thesis 
    apply(simp add: type3_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
    apply(safe) 
      apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type0_def)
        apply smt
      apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type0_def)   
        done 
qed 


lemma oneBIT_step1y: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows "(type1 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s y \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) y a, is'))))
                = type3 [x0, y0] x y"
proof -
    from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto
    have "(type1 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s y \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) y a, is')))) 
            = (type1 [x0, y0] x y) \<bind> (%s. Step_rand BIT y s )"
            by (simp add: bind_assoc_pmf bind_return_pmf split_def)
  also               
    from  assms(1) kas2
    have "...
            = type3 [x0, y0] x y"
      apply(simp add: type1_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
      apply(safe) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type3_def)
          apply smt
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type3_def)   
          done
  finally 
    show ?thesis  .
qed 

lemma oneBIT_step4x: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows "(type4 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is'))))
                = type1 [x0, y0] x y"
proof -
    from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto
    have "(type4 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is')))) 
            = (type4 [x0, y0] x y) \<bind> (%s. Step_rand BIT x s )"
            by(simp add: bind_assoc_pmf bind_return_pmf split_def)
  also               
    from  assms(1) kas2
    have "...
            = type1 [x0, y0] x y"
      apply(simp add: type4_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
      apply(safe) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type1_def) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type1_def)   
          by smt  
  finally 
    show ?thesis  .
qed 

lemma oneBIT_step1x: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows "(type1 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is'))))
                = type0 [x0, y0] x y"
proof -
    from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto
    have "(type1 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is')))) 
            = (type1 [x0, y0] x y) \<bind> (%s. Step_rand BIT x s )"
            by(simp add: bind_assoc_pmf bind_return_pmf split_def)
  also               
    from  assms(1) kas2
    have "...
            = type0 [x0, y0] x y"
      apply(simp add: type1_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
      apply(safe) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type0_def) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind swap_def type0_def)   
          by smt  
  finally 
    show ?thesis  .
qed 

lemma oneBIT_step0x: 
    assumes "x\<noteq>y" "x : {x0,y0}" "y\<in>{x0,y0}"
    shows "(type0 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is'))))
                = type0 [x0, y0] x y"
proof -
    from assms have kas2: " [x0,y0] = [x,y] \<or>  [x0,y0] = [y,x]" by auto
    have "(type0 [x0, y0] x y \<bind>
        (\<lambda>s. BIT_step s x \<bind>
             (\<lambda>(a, is'). return_pmf (step (fst s) x a, is')))) 
            = (type0 [x0, y0] x y) \<bind> (%s. Step_rand BIT x s )"
            by(simp add: bind_assoc_pmf bind_return_pmf split_def)
  also               
    from  assms(1) kas2
    have "...
            = type0 [x0, y0] x y "
      apply(simp add: type0_def BIT_step_def bind_assoc_pmf bind_return_pmf step_def mtf2_def)
      apply(safe)
        apply(rule pmf_eqI) apply(simp add: pmf_bind) 
        apply(rule pmf_eqI) apply(simp add: pmf_bind)   
          by smt (* sledgehammer
proof -
  fix i :: 'b
  have f1: "pmf (f ([x, y], [False, True], [y, x])) i / 2 + pmf (f ([x, y], [False, False], [y, x])) i / 2 = pmf (f ([x, y], [False, False], [y, x])) i / 2 + pmf (f ([x, y], [False, True], [y, x])) i / 2"
    by simp
  have "pmf (f ([x, y], [True, True], [y, x])) i / 2 + pmf (f ([x, y], [True, False], [y, x])) i / 2 = pmf (f ([x, y], [True, False], [y, x])) i / 2 + pmf (f ([x, y], [True, True], [y, x])) i / 2"
    by algebra
  then show "(pmf (f ([x, y], [True, False], [y, x])) i / 2 + pmf (f ([x, y], [True, True], [y, x])) i / 2) / 2 + (pmf (f ([x, y], [False, False], [y, x])) i / 2 + pmf (f ([x, y], [False, True], [y, x])) i / 2) / 2 = (pmf (f ([x, y], [True, True], [y, x])) i / 2 + pmf (f ([x, y], [True, False], [y, x])) i / 2) / 2 + (pmf (f ([x, y], [False, True], [y, x])) i / 2 + pmf (f ([x, y], [False, False], [y, x])) i / 2) / 2"
    using f1 by presburger
qed *)
  finally 
    show ?thesis  .
qed 
 
            
        
section "go through the four phase types"

 
 

subsection "yx"
 
lemma bit_yx': assumes "x \<noteq> y" 
      and kas: "init \<in> {[x,y],[y,x]}"
      and "qs \<in> lang (Star(Times (Atom y) (Atom x))) "
   shows "T\<^sub>p_on_rand' BIT (type1 init x y) (qs@r) = 0.75 * length qs + T\<^sub>p_on_rand' BIT (type1 init x y) r 
    \<and> config'_rand BIT (type1 init x y) qs  = (type1 init x y)"
proof -
  from assms have "qs \<in> star ({[y]} @@ {[x]})" by (simp)
  from this assms show ?thesis
  proof (induct qs rule: star_induct)
    case (append u v)
    then have uyx: "u = [y,x]" by auto 
     
    have yy: "T\<^sub>p_on_rand' BIT (type1 init x y)  (v @ r)  = 0.75*length v + T\<^sub>p_on_rand' BIT (type1 init x y) r  
            \<and> config'_rand BIT  (type1 init x y) v = (type1 init x y)"
        apply(rule append(3)) 
          apply(fact)+
          using append(2,6) by(simp_all)
    note A=append(4)
 
    have s2: "config'_rand BIT  (type1 init x y) [y,x] = (type1 init x y)"
      using kas
      apply(auto)
        using assms(1) apply(simp add: oneBIT_step1y oneBIT_step3x)
        using assms(1) apply(simp add: oneBIT_step1y oneBIT_step3x)
            done
                             
    have ta: "T\<^sub>p_on_rand' BIT (type1 init x y) u = 1.5"
      unfolding uyx using kas
        apply(auto)
          using assms(1) apply(simp_all add: oneBIT_step1y)
          by(simp_all add: costBIT_1y costBIT_3x)                             
       

    have "config'_rand BIT  (type1 init x y) (u @ v) =
           config'_rand BIT (config'_rand BIT (type1 init x y) u) v "
            by (simp add: config'_rand_append)
    also have "\<dots> = type1 init x y" by (simp only: s2 uyx yy)
    finally have config: "config'_rand BIT  (type1 init x y) (u @ v) = type1 init x y" .


    have "T\<^sub>p_on_rand' BIT (type1 init x y) (u @ (v @ r))  
        = T\<^sub>p_on_rand' BIT (type1 init x y) u  + T\<^sub>p_on_rand' BIT ( config'_rand BIT (type1 init x y)  u) (v@r) "
          by (simp only: T_on_rand'_append)
    also have "\<dots> =  T\<^sub>p_on_rand' BIT  (type1 init x y) u + T\<^sub>p_on_rand' BIT (type1 init x y) (v@r) "
      unfolding uyx by(simp only: s2) 
    also have "\<dots> = T\<^sub>p_on_rand' BIT (type1 init x y) u  + 0.75*length v + T\<^sub>p_on_rand' BIT (type1 init x y) r "
        by(simp only: yy) 
    also have "\<dots> = 2*0.75 + 0.75*length v + T\<^sub>p_on_rand' BIT (type1 init x y) r " by(simp add: ta) 
    also have "\<dots> = 0.75 * (2+length v) + T\<^sub>p_on_rand' BIT (type1 init x y) r"
      by (simp add: ring_distribs del: add_2_eq_Suc' add_2_eq_Suc)
    also have "\<dots> = 0.75 * length (u @ v) + T\<^sub>p_on_rand' BIT (type1 init x y) r"
      using uyx by simp
    finally show ?case using config by simp 
  qed simp
qed


subsection "(yx)*yx"

lemma bit_yxyx': assumes "x \<noteq> y" and kas: "init \<in> {[x,y],[y,x]}" and
      "qs \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
   shows "T\<^sub>p_on_rand' BIT (type0 init x y) (qs@r) = 0.75 * length qs + T\<^sub>p_on_rand' BIT (type1 init x y) r 
    \<and> config'_rand BIT (type0 init x y) qs  = (type1 init x y)"
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



   have s2: "config'_rand BIT  (type0 init x y) [y,x] = (type1 init x y)"
      using kas
      apply(auto)
        using assms(1) apply(simp add: oneBIT_step0y oneBIT_step4x)
        using assms(1) apply(simp add: oneBIT_step0y oneBIT_step4x)
      done
              
                             
    have ta: "T\<^sub>p_on_rand' BIT (type0 init x y) u = 1.5"
      unfolding uyx using kas
        apply(auto)
          using assms(1) apply(simp_all add: oneBIT_step0y)
          apply (simp_all add: costBIT_0y costBIT_4x)  done
 
                  
    have tat: "T\<^sub>p_on_rand' BIT (type1 init x y) (v @ r) =   0.75*length v + T\<^sub>p_on_rand' BIT (type1 init x y) r
            \<and> config'_rand BIT (type1 init x y) v = (type1 init x y)"
        apply(rule bit_yx')
      apply(fact)+
      using vv A by(simp_all)


    have config: "config'_rand BIT (type0 init x y) (u @ v) =
            type1 init x y" by(simp only: config'_rand_append s2 uyx tat)
     
    have "T\<^sub>p_on_rand' BIT (type0 init x y) (u @ (v @ r)) 
        = T\<^sub>p_on_rand' BIT (type0 init x y) u + T\<^sub>p_on_rand' BIT (config'_rand BIT (type0 init x y) u) (v@r)"
          by (simp only: T_on_rand'_append)
  also
    have "\<dots> =  T\<^sub>p_on_rand' BIT (type0 init x y) u + T\<^sub>p_on_rand' BIT (type1 init x y) (v@r)"
      by(simp only: uyx s2) 
    also have "\<dots> = T\<^sub>p_on_rand' BIT (type0 init x y) u + 0.75*length v + T\<^sub>p_on_rand' BIT (type1 init x y) r"
        by(simp only: tat) 
    also have "\<dots> = 2*0.75 + 0.75*length v + T\<^sub>p_on_rand' BIT (type1 init x y) r" by(simp add: ta) 
    also have "\<dots> = 0.75 * (2+length v) + T\<^sub>p_on_rand' BIT (type1 init x y) r"
      by (simp add: ring_distribs del: add_2_eq_Suc' add_2_eq_Suc) 
    also have "\<dots> = 0.75 * length (u @ v) + T\<^sub>p_on_rand' BIT (type1 init x y) r"
      using uyx by simp
    finally show ?thesis using qsuv config by simp
qed
  
subsection "Phase Type A"

lemma BIT_a_config': assumes "x \<noteq> y"
    " init \<in> {[x,y],[y,x]}"
   "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
  shows  "config'_rand BIT (type0 init x y) qs = (type0 init y x)"
proof - 
  from assms(3) have alt: "qs = [x,y,y] \<or> qs = [y,y]" apply(simp) by fastforce
  show ?thesis
    using assms(1,2) alt
    apply(auto)
      apply(simp add: oneBIT_step0x oneBIT_step0y oneBIT_step4y)
      apply(simp add: oneBIT_step0y oneBIT_step4y) 
      apply(simp add: oneBIT_step0x oneBIT_step0y oneBIT_step4y)
      apply(simp add: oneBIT_step0y oneBIT_step4y) done
qed

lemma BIT_a': assumes "x \<noteq> y" "init \<in> {[x,y],[y,x]}"
    "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
    shows
   "T\<^sub>p_on_rand' BIT (type0 init x y) qs = 1.5"
proof - 
  from assms(3) have alt: "qs = [x,y,y] \<or> qs = [y,y]" apply(simp) by fastforce
  show ?thesis
    using assms(1,2) alt 
    apply(auto)
      apply(simp add: oneBIT_step0x oneBIT_step0y costBIT_0x costBIT_0y costBIT_4y)
      apply(simp add: oneBIT_step0x oneBIT_step0y costBIT_0x costBIT_0y costBIT_4y)
      apply(simp add: oneBIT_step0x oneBIT_step0y costBIT_0x costBIT_0y costBIT_4y)
      apply(simp add: oneBIT_step0x oneBIT_step0y costBIT_0x costBIT_0y costBIT_4y)
      done
qed
 
lemma bit_a': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "BIT_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}" "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
 shows  
    "T\<^sub>p_on_rand' BIT s qs  \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y]) 
      \<and>  BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]"
proof -

  from assms have f: "x0\<noteq>y0" by auto
  from assms(1,3) assms(2)[symmetric] have s: "s = type0 [x0,y0] x y"
    apply(simp add: BIT_inv2[OF f] other_def) by fast

  from assms(1,2) have kas: "[x,y] = [x0,y0] \<or> [x,y] = [y0,x0]" by auto

  from assms have lqs: "last qs = y" by fastforce
  from assms(1,2) kas have "T\<^sub>p_on_rand' BIT s qs = 1.5"
    unfolding s 
    apply(safe)
      apply(rule BIT_a')
        apply(simp) apply(simp) using assms(5) apply(simp)
      apply(rule BIT_a')
        apply(simp) apply(simp) using assms(5) apply(simp)
  done
  with OPT2_A[OF assms(1,5)] have BIT: "T\<^sub>p_on_rand' BIT s qs \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" by auto


  from assms(1,2) kas have "config'_rand BIT s qs = type0 [x0, y0] y x"
    unfolding s 
    apply(safe)
      apply(rule BIT_a_config')
        apply(simp) apply(simp) using assms(5) apply(simp)
      apply(rule BIT_a_config')
        apply(simp) apply(simp) using assms(5) apply(simp)
  done 
   
   then have "BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]"
    apply(simp)
    using assms(1) kas f lqs by(auto simp add: BIT_inv2 other_def) 

  then show ?thesis using BIT s by simp
qed  

subsection "x^+.."


lemma BIT_x': assumes "x\<noteq>y"
       "init \<in> {[x,y],[y,x]}" "qs \<in> lang (Plus (Atom x) One)"
 shows "T\<^sub>p_on_rand' BIT (type0 init x y) (qs@r) = T\<^sub>p_on_rand' BIT (type0 init x y) r 
    \<and> config'_rand BIT  (type0 init x y) qs = (type0 init x y)"
proof - 
  have A: "x\<noteq>y"  using assms by auto

  have s: "config'_rand BIT (type0 init x y) qs = type0 init x y"
    using assms  
      apply(auto simp add: oneBIT_step0x) done

  have t: "T\<^sub>p_on_rand' BIT (type0 init x y) qs = 0"
    using assms
    apply(auto simp add: costBIT_0x) done

  show ?thesis
    using s t by(simp add: T_on_rand'_append)
qed
        

subsection "Phase Type B"

lemma BIT_b': assumes "x \<noteq> y"
       "init \<in> {[x,y],[y,x]}"
    "v \<in> lang (seq [Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
    shows "T\<^sub>p_on_rand' BIT (type0 init x y) v = 0.75 * length v - 0.5
    \<and> config'_rand BIT  (type0 init x y) v = (type0 init y x)"
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
 
  from bit_yxyx' assms(1,2) aa have stars: "T\<^sub>p_on_rand' BIT (type0 init x y) (a @ b)  = 0.75 * length a + T\<^sub>p_on_rand' BIT (type1 init x y) b"
                             and s2: "config'_rand BIT (type0 init x y) a = type1 init x y"  by fast+

  have t: "T\<^sub>p_on_rand' BIT (type1 init x y) b = 1"
    unfolding bb  using assms(1,2)
      apply(auto)
       apply(simp add: oneBIT_step1y oneBIT_step3y costBIT_1y costBIT_3y)  
       apply(simp add: oneBIT_step1y oneBIT_step3y costBIT_1y costBIT_3y)  
  done

  have s: "config'_rand BIT  (type1 init x y) [y, y] = type0 init y x" 
      using assms(1,2)
      apply(auto) 
       apply(simp add: oneBIT_step1y oneBIT_step3y )  
       apply(simp add: oneBIT_step1y oneBIT_step3y )  
  done


    have config: "config'_rand BIT  (type0 init x y) (a @ b) =
             type0 init y x" by (simp only: config'_rand_append s2 vab bb s)
 
  have calc: "3 * Suc (Suc (length a)) / 4 - 1 / 2 = 3 * (2+length a) / 4 - 1 / 2" by simp

  from t stars have "T\<^sub>p_on_rand' BIT (type0 init x y) (a @ b) = 0.75 * length a + 1" by auto
  then have whatineed: "T\<^sub>p_on_rand' BIT  (type0 init x y) v = 0.75 * length v - 0.5" unfolding lenv 
    unfolding vab
    by(simp add: ring_distribs del: add_2_eq_Suc')
  with config vab show ?thesis by simp
qed

lemma bit_b': assumes "x \<noteq> y"
      "init \<in> {[x,y],[y,x]}"
   "qs \<in> lang (seq[Plus (Atom x) One, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom y, Atom y])"
 shows  "T\<^sub>p_on_rand' BIT (type0 init x y) qs \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y])"
  and "config'_rand BIT (type0 init x y) qs = type0 init y x"
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

  from BIT_x'[OF assms(1,2) uu] have u_t: "T\<^sub>p_on_rand' BIT (type0 init x y)  (u @ v)  = T\<^sub>p_on_rand' BIT (type0 init x y) v"
      and u_c: "config'_rand BIT (type0 init x y) u = type0 init x y" by auto
  from BIT_b'[OF assms(1,2) vv] have b_t: "T\<^sub>p_on_rand' BIT (type0 init x y) v  = 0.75 * length v - 0.5"
      and  b_c: "config'_rand BIT (type0 init x y) v = (type0 init y x)" by auto
 
  have BIT: "T\<^sub>p_on_rand' BIT (type0 init x y) qs  = 0.75 * length v - 0.5"
    by(simp add: qsuv u_t b_t)
          
  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom y, Atom y])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_B) by(fact)+


  from lenv have "v \<noteq> []"  "last v = y" by auto
  then have 1:  "last qs = y" using last_appendR qsuv by simp 
  then have 2: "other (last qs) x y = x" unfolding other_def by simp


  show "T\<^sub>p_on_rand' BIT (type0 init x y) qs \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y])" using BIT OPT lenv   1 2  by auto

  (* config *)

    show "config'_rand BIT  (type0 init x y) qs  =
        type0 init y x" by (auto simp add: config'_rand_append qsuv u_c b_c)
qed

lemma bit_b'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "BIT_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}" 
    "qs \<in> lang (seq[Plus (Atom x) One, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom y, Atom y])"
 shows  
    "T\<^sub>p_on_rand' BIT s qs  \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y]) 
      \<and>  BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]" 
proof -
  
  from assms have f: "x0\<noteq>y0" by auto
  from assms(1,3) assms(2)[symmetric] have s: "s = type0 [x0,y0] x y"
    apply(simp add: BIT_inv2[OF f] other_def) by fast

  from assms(1,2) have kas: "[x,y] = [x0,y0] \<or> [x,y] = [y0,x0]" by auto

  from assms have lqs: "last qs = y" by fastforce
  from assms(1,2) kas have BIT: "T\<^sub>p_on_rand' BIT s qs \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
    unfolding s 
    apply(safe)
      apply(rule bit_b'(1))
        apply(simp) apply(simp) using assms(5) apply(simp)
      apply(rule bit_b'(1))
        apply(simp) apply(simp) using assms(5) apply(simp)
  done 

  from assms(1,2) kas have "config'_rand BIT s qs = type0 [x0, y0] y x"
    unfolding s 
    apply(safe)
      apply(rule bit_b'(2))
        apply(simp) apply(simp) using assms(5) apply(simp)
      apply(rule bit_b'(2))
        apply(simp) apply(simp) using assms(5) apply(simp)
  done 
   
   then have "BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]"
    apply(simp)
    using assms(1) kas f lqs by(auto simp add: BIT_inv2 other_def) 

  then show ?thesis using BIT s by simp
qed


subsection "Phase Type C"


lemma BIT_c': assumes "x \<noteq> y"
       "init \<in> {[x,y],[y,x]}"
    "v \<in> lang (seq [Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
    shows "T\<^sub>p_on_rand' BIT (type0 init x y) v = 0.75 * length v - 0.5
    \<and> config'_rand BIT  (type0 init x y) v = (type0 init x y)"
proof -        
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
 
  from bit_yxyx' assms(1,2) aa have stars: "T\<^sub>p_on_rand' BIT (type0 init x y) (a @ b)  = 0.75 * length a + T\<^sub>p_on_rand' BIT (type1 init x y) b"
                             and s2: "config'_rand BIT (type0 init x y) a = type1 init x y"  by fast+

  have t: "T\<^sub>p_on_rand' BIT (type1 init x y) b = 1/4"
    unfolding bb  using assms(1,2)
      apply(auto)
       apply(simp add: costBIT_1x)  
       apply(simp add: costBIT_1x)  
  done

  have s: "config'_rand BIT  (type1 init x y) b = type0 init x y" 
      using assms(1,2) bb
      apply(auto) 
       apply(simp add: oneBIT_step1x )  
       apply(simp add: oneBIT_step1x )  
  done


    have config: "config'_rand BIT  (type0 init x y) (a @ b) =
             type0 init x y" by (simp only: config'_rand_append s2 vab s)
 
  have calc: "3 * Suc (Suc (length a)) / 4 - 1 / 2 = 3 * (2+length a) / 4 - 1 / 2" by simp

  from t stars have "T\<^sub>p_on_rand' BIT (type0 init x y) (a @ b) = 0.75 * length a + 1/4" by auto
  then have whatineed: "T\<^sub>p_on_rand' BIT  (type0 init x y) v = 0.75 * length v - 0.5" unfolding lenv 
    unfolding vab
    by(simp add: ring_distribs del: add_2_eq_Suc')
  with config vab show ?thesis by simp
qed

           
lemma bit_c': assumes "x \<noteq> y"
      "init \<in> {[x,y],[y,x]}"
   "qs \<in> lang (seq[Plus (Atom x) One, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])"
 shows  "T\<^sub>p_on_rand' BIT (type0 init x y) qs \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y])"
  and "config'_rand BIT (type0 init x y) qs = type0 init x y"
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
        
  from vv have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom x])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom x])"
                      and vab: "v = a @ b" 
                      by(erule concE)  

  from BIT_x'[OF assms(1,2) uu] have u_t: "T\<^sub>p_on_rand' BIT (type0 init x y)  (u @ v)  = T\<^sub>p_on_rand' BIT (type0 init x y) v"
      and u_c: "config'_rand BIT (type0 init x y) u = type0 init x y" by auto
  from BIT_c'[OF assms(1,2) vv] have b_t: "T\<^sub>p_on_rand' BIT (type0 init x y) v  = 0.75 * length v - 0.5"
      and  b_c: "config'_rand BIT (type0 init x y) v = (type0 init x y)" by auto
 
  have BIT: "T\<^sub>p_on_rand' BIT (type0 init x y) qs  = 0.75 * length v - 0.5"
    by(simp add: qsuv u_t b_t)
          
  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom x])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_C) by(fact)+


  from lenv have "v \<noteq> []"  "last v = x" by auto
  then have 1:  "last qs = x" using last_appendR qsuv by simp 
  then have 2: "other (last qs) x y = y" unfolding other_def by simp



  have vgt3: "length v \<ge> 3" using lenv by simp
  have "T\<^sub>p_on_rand' BIT (type0 init x y) qs  = 0.75 * length v - 0.5" using BIT by simp
also
  have "\<dots> \<le> 1.75 * (length v - 1)/2"
  proof -
    have "10 + 6 * length v \<le> 7 * Suc (length v) 
        \<longleftrightarrow> 10 + 6 * length v \<le> 7 * length v + 7" by auto
    also have "\<dots> \<longleftrightarrow> 3 \<le> length v" by auto
    also have "\<dots> \<longleftrightarrow> True" using vgt3 by auto
    finally have A: " 6 * length v - 4 \<le> 7 * (length v - 1)" by simp
    show ?thesis apply(simp) using A by linarith 
  qed    
also
  have "\<dots> = 1.75 * (length v div 2)"
  proof -
    from mod_div_equality have "length v = length v div 2 * 2 + length v mod 2" by auto
    with lenv have "length v = length v div 2 * 2 + 1" by auto 
    then have "(length v - 1) / 2 = length v div 2" by simp
    then show ?thesis by simp
  qed
also
  have "\<dots> = 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" using OPT by auto
finally
  show "T\<^sub>p_on_rand' BIT (type0 init x y) qs \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y])"
    using BIT OPT lenv   1 2  by auto

  (* config *)

    show "config'_rand BIT  (type0 init x y) qs  =
        type0 init x y" by (auto simp add: config'_rand_append qsuv u_c b_c)
qed

lemma bit_c'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "BIT_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}" 
    "qs \<in> lang (seq[Plus (Atom x) One, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])"
 shows  
    "T\<^sub>p_on_rand' BIT s qs  \<le> 1.75 * T\<^sub>p [x,y] qs (OPT2 qs [x,y]) 
      \<and>  BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]" 
proof -
  
  from assms have f: "x0\<noteq>y0" by auto
  from assms(1,3) assms(2)[symmetric] have s: "s = type0 [x0,y0] x y"
    apply(simp add: BIT_inv2[OF f] other_def) by fast

  from assms(1,2) have kas: "[x,y] = [x0,y0] \<or> [x,y] = [y0,x0]" by auto

  from assms have lqs: "last qs = x" by fastforce
  from assms(1,2) kas have BIT: "T\<^sub>p_on_rand' BIT s qs \<le> 1.75 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
    unfolding s 
    apply(safe)
      apply(rule bit_c'(1))
        apply(simp) apply(simp) using assms(5) apply(simp)
      apply(rule bit_c'(1))
        apply(simp) apply(simp) using assms(5) apply(simp)
  done 

  from assms(1,2) kas have "config'_rand BIT s qs = type0 [x0, y0] x y"
    unfolding s 
    apply(safe)
      apply(rule bit_c'(2))
        apply(simp) apply(simp) using assms(5) apply(simp)
      apply(rule bit_c'(2))
        apply(simp) apply(simp) using assms(5) apply(simp)
  done 
   
   then have "BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]"
    apply(simp)
    using assms(1) kas f lqs by(auto simp add: BIT_inv2 other_def) 

  then show ?thesis using BIT s by simp
qed  
 
subsection "Phase Type D"
 
lemma bit_d': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "BIT_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}"
  shows "qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow>
    T\<^sub>p_on_rand' BIT s qs \<le> 175 / 10\<^sup>2 * real (T\<^sub>p [x, y] qs (OPT2 qs [x, y])) \<and>
    BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]"
proof -
  assume "qs \<in> lang (seq [Atom x, Atom x])"
  then have qs: "qs = [x,x]" by auto
  then have OPT: "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = 0" by (simp add: t\<^sub>p_def step_def)
   
  from assms have f: "x0\<noteq>y0" by auto
  from assms(1,3) assms(2)[symmetric] have s: "s = type0 [x0,y0] x y"
    apply(simp add: BIT_inv2[OF f] other_def) by fast
    
  from assms(1,2) have kas: "[x,y] = [x0,y0] \<or> [x,y] = [y0,x0]" by auto
 
  have BIT: "T\<^sub>p_on_rand' BIT (type0 [x0,y0] x y) qs = 0"
    unfolding qs    
    using kas
    apply(auto)
    using assms(1,2) apply(simp_all add: oneBIT_step0x)
    apply(simp_all add: type0_def bind_return_pmf bind_assoc_pmf split_def BIT_step_def t\<^sub>p_def step_def mtf2_def)
    done


   have lqs: "last qs = x" "last qs \<in> {x0,y0}" using assms(2,4) qs by auto 

   have inv: "config'_rand BIT s qs = type0 [x0, y0] x y"
    unfolding qs s apply(simp )  
    using kas
    apply(auto)
    using assms(1,2) apply(simp_all add: oneBIT_step0x)
    done
   
   then have "BIT_inv (config'_rand BIT s qs) (last qs) [x0, y0]"
    apply(simp)
    using assms(1) kas f lqs by(auto simp add: BIT_inv2 other_def) 
    
  then show ?thesis using BIT s by(auto)
qed

section "Phase Partitioning"

lemma D'': assumes "qs \<in> Lxx a b"
    "a \<noteq> b" "{a, b} = {x, y}" "BIT_inv s a [x, y]"
    "set qs \<subseteq> {a, b}"
 shows "T\<^sub>p_on_rand' BIT s qs \<le> 175 / 10\<^sup>2 * real (T\<^sub>p [a, b] qs (OPT2 qs [a, b])) \<and>
    BIT_inv (Partial_Cost_Model.config'_rand BIT s qs) (last qs) [x, y]"
 apply(rule LxxE[OF assms(1)])
  apply(rule bit_d'[OF assms(2-5)]) apply(simp)
  apply(rule bit_b''[OF assms(2-5)]) apply(simp)
  apply(rule bit_c''[OF assms(2-5)]) apply(simp) 
  apply(rule bit_a'[OF assms(2-5)]) apply(simp)
  done

 

theorem BIT_175comp_on_2:
    assumes "(x::nat) \<noteq> y" "set \<sigma> \<subseteq> {x,y}"     
     shows "T\<^sub>p_on_rand BIT [x,y] \<sigma>  \<le> 1.75 * real (T\<^sub>p_opt [x,y] \<sigma>) + 1.75" 
proof (rule Phase_partitioning_general[where P=BIT_inv], goal_cases)
  case 4
  show "BIT_inv (map_pmf (Pair [x, y]) (fst BIT [x, y])) x [x, y]"
    using assms(1) apply(simp add: BIT_inv2 BIT_init_def type0_def)
      apply(simp add: map_pmf_def other_def bind_return_pmf bind_assoc_pmf)
      using bind_commute_pmf by fast
next
  case (5 a b qs s)
  then show ?case by(rule D'')
qed (simp_all add: assms)  
 
end