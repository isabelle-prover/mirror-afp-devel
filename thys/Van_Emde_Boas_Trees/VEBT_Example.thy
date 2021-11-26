(*by Lammich and Ammer*)
section \<open>Interface Usage Example\<close>
theory VEBT_Example
imports VEBT_Intf_Imperative VEBT_Example_Setup
begin



  subsection \<open>Test Program\<close>

  definition "test n xs ys \<equiv> do {
    t \<leftarrow> vebt_buildupi n;
    t \<leftarrow> mfold (\<lambda>x s. vebt_inserti s x) (0#xs) t;
    
    let f = (\<lambda>x. if\<^sub>m vebt_memberi t x then return x else the $\<^sub>m (vebt_predi t x));
   
    mmap f ys
  }"

  subsection \<open>Correctness without Time\<close>
  text \<open>The non-time part of our datastructure is fully integrated into sep-auto\<close>
  
  lemma fold_list_rl[sep_heap_rules]: "\<forall>x\<in>set xs. x<2^n \<Longrightarrow> hoare_triple 
    (vebt_assn n s t) 
    (mfold (\<lambda>x s. vebt_inserti s x) xs t)
    (\<lambda>t'. vebt_assn n (s \<union> set xs) t')"
  proof (induction xs arbitrary: s t)
    case Nil
    then show ?case by sep_auto
  next
    case (Cons a xs)
    
    note Cons.IH[sep_heap_rules]
    
    show ?case using Cons.prems
      by sep_auto
      
  qed    

    
  lemma test_hoare: "\<lbrakk>\<forall>x\<in>set xs. x<2^n; n>0\<rbrakk> \<Longrightarrow>  
      <emp> (test n xs ys) <\<lambda>r. \<up>(r = map (\<lambda>y. (GREATEST y'. y'\<in>insert 0 (set xs) \<and> y'\<le>y)) ys) >\<^sub>t "  
    unfolding test_def
      supply R = mmap_pure_aux[where f="(\<lambda>y. (GREATEST y'. y'\<in>insert 0 (set xs) \<and> y'\<le>y))"]
      apply (sep_auto decon: R)
      subgoal 
        by (metis (mono_tags, lifting) GreatestI_ex_nat zero_le_numeral)
      subgoal 
        by (metis (no_types, lifting) Greatest_equality le_eq_less_or_eq)
      apply sep_auto
      subgoal 
        apply (auto simp: is_pred_in_set_def)
        subgoal
          by (smt (z3) GreatestI_nat le_neq_implies_less less_eq_nat.simps(1))
        subgoal
          by (smt (z3) GreatestI_nat mult.right_neutral nat_less_le power_eq_0_iff power_mono_iff)
        subgoal
          by (metis (no_types, lifting) Greatest_le_nat less_imp_le)
      done
      apply sep_auto
    done

subsection \<open>Time Bound Reasoning\<close>
text \<open>
  We use some ad-hoc reasoning to also show the time-bound of our test program. 
  A generalization of such methods, or the integration of this entry into existing
  reasoning frameworks with time is left to future work.
\<close>
  
lemma insert_time_pure[cond_TBOUND]:"a < 2^n \<Longrightarrow>
  \<section>vebt_assn n S ti\<section> TBOUND (vebt_inserti ti a) (13 + 13 * nat \<lceil>log 2 (real n)\<rceil>)"
  by(rule htt_elim, rule vebt_inserti_rule, simp)
 
lemma member_time_pure[cond_TBOUND]:"\<section>vebt_assn n S ti\<section> TBOUND (vebt_memberi ti a) (5 + 5 * nat \<lceil>log 2 (real n)\<rceil>)"
  by(rule htt_elim, rule  vebt_memberi_rule)

lemma pred_time_pure[cond_TBOUND]:"\<section>vebt_assn n S ti\<section> TBOUND (vebt_predi ti a) (7 + 7 * nat \<lceil>log 2 (real n)\<rceil>)"
   by(rule htt_elim, rule  vebt_predi_rule)

lemma TBOUND_mfold[cond_TBOUND]:"
  (\<And> x. x \<in> set xs \<Longrightarrow> x < 2^n) \<Longrightarrow>
         \<section> vebt_assn n S ti \<section> TBOUND (mfold (\<lambda>x s. vebt_inserti s x) xs ti)  (length xs  * (13 + 13 * nat \<lceil>log 2 n \<rceil>) + 1)"
  apply(induction xs arbitrary: ti S)
   apply(subst mfold.simps)
   apply(cond_TBOUND, simp)
  apply sep_auto
  subgoal for a xs ti S
    apply(rule cond_TBOUND_mono[where b = "(13 + 13 * nat \<lceil>log 2 (real n)\<rceil>) + (length xs * (13 + 13 * nat \<lceil>log 2 (real n)\<rceil>) + 1)"])
    apply(rule cond_TBOUND, auto|(rule vebt_heap_rules(3), auto))+
    done
  done

lemma TBOUND_mmap[cond_TBOUND]: 
  defines b_def: "b ys n \<equiv> 1 + length ys * ( 5 + 5 * nat \<lceil>log 2 (real n)\<rceil> + 9 + 7 * nat \<lceil>log 2 (real n)\<rceil>)"
  shows "\<section> vebt_assn n S ti \<section> TBOUND
        (mmap (\<lambda>x. if\<^sub>m vebt_memberi ti x then return x
                   else vebt_predi ti x \<bind> (\<lambda>x. return (the x))) ys) (b ys n)"
  apply(induction ys arbitrary:)
   apply(subst mmap.simps)
  subgoal
    unfolding b_def
    apply(rule cond_TBOUND_mono[where b = 1], rule cond_TBOUND_return, simp)
    done
  apply sep_auto
  subgoal for a ys
   apply(rule cond_TBOUND_mono[
       where b = "((5 + 5 * nat \<lceil>log 2 (real n)\<rceil>) + max  1 ((7 + 7 * nat \<lceil>log 2 (real n)\<rceil>) + 1)) 
        +(b ys n + 1)"])
     apply(rule cond_TBOUND_bind[where Q = "\<lambda> r. vebt_assn n S ti"])
    apply(rule cond_TBOUND | rule mmap_pres | sep_auto | rule cond_TBOUND_cons)+
    unfolding b_def
    apply simp
    done
  done 

lemma TBOUND_test[cond_TBOUND]: "\<lbrakk>\<forall>x\<in>set xs. x<2^n; n>0 \<rbrakk> \<Longrightarrow>  
       \<section> \<up> (n> 0) \<section> TBOUND (test n xs ys) (10 * 2^n  + (
                              ( length (0#xs)  * (13 + 13 * nat \<lceil>log 2 n \<rceil>) + 1) +
                              (1 + length ys * ( 5 + 5 * nat \<lceil>log 2 (real n)\<rceil> +  9 + 7 * nat \<lceil>log 2 (real n)\<rceil>))))"
  unfolding test_def
  apply(cond_TBOUND| rule htt_elim[OF vebt_buildupi_rule] | sep_auto)+
  done

lemma test_hoare_with_time: "\<lbrakk>\<forall>x\<in>set xs. x<2^n; n>0\<rbrakk> \<Longrightarrow>  
    <emp> (test n xs ys) <\<lambda>r. \<up>(r = map (\<lambda>y. (GREATEST y'. y'\<in>insert 0 (set xs) \<and> y'\<le>y)) ys) * true > 
    T[10 * 2 ^ n +
       (length (0 # xs) * (13 + 13 * nat \<lceil>log 2 (real n)\<rceil>) + 1 +
        (1 + length ys * (5 + 5 * nat \<lceil>log 2 (real n)\<rceil> + 9 + 7 * nat \<lceil>log 2 (real n)\<rceil>)))]"
  apply(rule htt_intro, rule test_hoare, simp+)
  apply(rule cond_TBOUND_mono, rule cond_TBOUND_cons)
  defer
  apply(rule TBOUND_test, simp+)
  done 

end
