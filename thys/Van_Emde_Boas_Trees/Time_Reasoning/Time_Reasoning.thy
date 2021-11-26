(*by Lammich*)
theory Time_Reasoning
imports "../Separation_Logic_Imperative_HOL/Sep_Main"
begin

  text \<open>Separating correctness and time reasoning for imperative HOL.
    In this theory, we provide a method to add time-reasoning to 
    an already proved-correct program. 
    
    The time-reasoning can exploit knowledge from the correctness proof via assertions.
  \<close>

  
subsection \<open>Selectors\<close>
  text \<open>We define selectors into the result of a state-time-monad computation\<close> 
  
  definition "fails m h \<equiv> execute m h = None"
  definition "the_res m h \<equiv> case execute m h of Some (r,_,_) \<Rightarrow> r"
  definition "the_heap m h \<equiv> case execute m h of Some (_,h',_) \<Rightarrow> h'"

  text \<open>We define the time to be zero for a failing computation, 
    such that failing computations trivially satisfy time bounds.
    
    Note that the computation is already proved non-failing by the correctness proof,
    this allows us to assume computations do not fail for the time-bound proof.
  \<close>
  definition "time c h \<equiv> case execute c h of None \<Rightarrow> 0 | Some (_,_,t) \<Rightarrow> t"
    
  lemma time_refines: "refines c c' \<Longrightarrow> \<not>fails c' h \<Longrightarrow> time c h \<le> time c' h"
    unfolding time_def refines_def fails_def
    apply (auto split: option.splits)
    done
    
  lemma fails_refines: "refines c c' \<Longrightarrow> fails c h \<Longrightarrow> fails c' h"  
    unfolding time_def refines_def fails_def
    apply (auto split: option.splits) 
    by (metis option.exhaust prod_cases3)

subsubsection \<open>Simplification Lemmas\<close>      
      
    
  named_theorems fails_simp
  named_theorems time_simp

  
  
  lemma fails_return[fails_simp]: "\<not>fails (return x) h"
    unfolding fails_def by (auto simp add: execute_simps split: option.split)

  lemma fails_wait[fails_simp]: "\<not>fails (wait x) h"
    unfolding fails_def by (auto simp add: execute_simps split: option.split)

  lemma fails_assert'[fails_simp]: "fails (assert' P) h \<longleftrightarrow> \<not>P"
    unfolding fails_def by (auto simp add: execute_simps split: option.split)
          
  lemma fails_bind[fails_simp]: "fails (bind m f) h \<longleftrightarrow> (\<not>fails m h \<longrightarrow> fails (f (the_res m h)) (the_heap m h))"  
    unfolding fails_def the_res_def the_heap_def 
    apply (auto simp add: execute_simps split: option.split)
    using timeFrame.elims by auto
    
  lemma fails_array_nth[fails_simp]: "fails (Array_Time.nth p i) h \<longleftrightarrow> \<not>(i < Array_Time.length h p)"  
    unfolding fails_def by (auto simp add: execute_simps split: option.split)

  lemma fails_array_upd[fails_simp]: "fails (Array_Time.upd i x p) h \<longleftrightarrow> \<not>(i < Array_Time.length h p)"  
    unfolding fails_def by (auto simp add: execute_simps split: option.split)
    
  lemma fails_array_len[fails_simp]: "\<not>fails (Array_Time.len p) h"  
    unfolding fails_def by (auto simp add: execute_simps split: option.split)

  lemma fails_array_new[fails_simp]: "\<not>fails (Array_Time.new n x) h"  
    unfolding fails_def by (auto simp add: execute_simps split: option.split)
    
  lemma fails_array_of_list[fails_simp]: "\<not>fails (Array_Time.of_list xs) h"  
    unfolding fails_def by (auto simp add: execute_simps split: option.split)

  lemma fails_array_make[fails_simp]: "\<not>fails (Array_Time.make n f) h"  
    unfolding fails_def by (auto simp add: execute_simps split: option.split)
            
  lemma fails_array_map_entry[fails_simp]: "fails (Array_Time.map_entry i x p) h \<longleftrightarrow> \<not>(i < Array_Time.length h p)"  
    unfolding fails_def by (auto simp add: execute_simps split: option.split)

  lemma fails_array_swap[fails_simp]: "fails (Array_Time.swap i x p) h \<longleftrightarrow> \<not>(i < Array_Time.length h p)"
    unfolding fails_def by (auto simp add: execute_simps split: option.split)
  
  
    

  lemma time_return[time_simp]: "time (return x) h = 1"
    unfolding time_def by (simp add: execute_simps)

  lemma time_bind[time_simp]: "time (bind m f) h = (
    if \<not>fails m h \<and> \<not>fails (f (the_res m h)) (the_heap m h) then time m h + time (f (the_res m h)) (the_heap m h)
    else 0
  )"  
    unfolding time_def the_res_def fails_def the_heap_def
    by (auto simp add: execute_simps split: option.split)
    
  lemma time_wait[time_simp]: "time (wait n) h = n"
    unfolding time_def by (simp add: execute_simps)

  lemma time_raise[time_simp]: "time (raise msg) h = 0"  
    by (auto simp: time_def execute_simps)
    
  lemma time_assert'[time_simp]: "time (assert' P) h = 0"
    unfolding time_def 
    by (auto simp add: execute_simps split: option.split)
    
            
  lemma time_array_nth[time_simp]: "time (Array_Time.nth p i) h = (if fails (Array_Time.nth p i) h then 0 else 1)"
    unfolding time_def by (auto simp add: execute_simps fails_simp split: option.split)
    
  lemma time_array_upd[time_simp]: "time (Array_Time.upd i x p) h = (if fails (Array_Time.upd i x p) h then 0 else 1)"
    unfolding time_def by (auto simp add: execute_simps fails_simp split: option.split)
    
  lemma time_array_len[time_simp]: "time (Array_Time.len p) h = 1"
    unfolding time_def by (auto simp add: execute_simps fails_simp split: option.split)

  lemma time_array_new[time_simp]: "time (Array_Time.new n x) h = n+1"
    unfolding time_def 
    by (auto simp add: execute_simps fails_simp split: option.split prod.splits)
            
  lemma time_array_of_list[time_simp]: "time (Array_Time.of_list xs) h = length xs+1"
    unfolding time_def 
    by (auto simp add: execute_simps fails_simp split: option.split prod.splits)

  lemma time_array_make[time_simp]: "time (Array_Time.make n f) h = n+1"
    unfolding time_def 
    by (auto simp add: execute_simps fails_simp split: option.split prod.splits)

  lemma time_array_map_entry[time_simp]: "time (Array_Time.map_entry i f p) h = (if fails (Array_Time.map_entry i f p) h then 0 else 2)"
    unfolding time_def by (auto simp add: execute_simps fails_simp split: option.split)
        
  lemma time_array_swap[time_simp]: "time (Array_Time.swap i x p) h = (if fails (Array_Time.map_entry i f p) h then 0 else 2)"
    unfolding time_def by (auto simp add: execute_simps fails_simp split: option.split)

  lemma time_array_freeze[time_simp]: "time (Array_Time.freeze p) h = Array_Time.length h p+1"
    unfolding time_def 
    by (auto simp add: execute_simps fails_simp split: option.split prod.splits)
        
    
subsection \<open>Hoare Triple with Time\<close>  
    
  definition htt::"assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> nat\<Rightarrow> bool"("<_>/ _/ <_> T/[_]") where
  "htt P c Q t \<equiv> <P> c <Q> \<and> (\<forall>h as. (h,as) \<Turnstile> P \<longrightarrow> time c h \<le> t)" 
    
  lemma httI[intro?]: 
    assumes "<P> c <Q>"
    assumes "\<And>h as. (h,as) \<Turnstile> P \<Longrightarrow> time c h \<le> t"
    shows "< P> c <Q>T[t]"
    using assms unfolding htt_def by auto
  
  lemma htt_refine:  
    assumes "< P> c <Q>T[ t]"
    assumes "refines c' c"
    shows " <P> c' <Q>T[ t]"
    by (smt (verit, best) assms(1) assms(2) dual_order.trans fails_def 
      hoare_tripleE hoare_triple_refines htt_def option.simps(3) time_refines)

      
  lemma htt_cons_rule: 
    assumes  "<P'> c <Q'>T[t']"
      " P \<Longrightarrow>\<^sub>A P'"
      "\<And> x. Q' x \<Longrightarrow>\<^sub>A Q x" "t' \<le> t"
    shows "<P>c <\<lambda> x. Q x >T[t]"
    using assms cons_rule[OF assms(2,3)] unfolding htt_def
    using entails_def by fastforce
  
  lemma norm_pre_ex_rule_htt:
  " (\<And>x. <P x> f <Q>T[t]) \<Longrightarrow> <\<exists>\<^sub>Ax. P x> f <Q>T[t]"
    by (metis htt_def mod_ex_dist norm_pre_ex_rule)
  
  lemma norm_post_ex_rule_htt:
  " ( <P> f <(Q x)>T[t]) \<Longrightarrow> <P> f <\<lambda> r. (\<exists>\<^sub>A x. Q x r)>T[t]"
   by (meson ent_refl eq_iff htt_cons_rule triv_exI)
  
  lemma norm_pre_pure_iff_htt: 
  "<P * \<up> b> f <Q>T[t] = (b \<longrightarrow> <P> f <Q>T[t])"
    using htt_def by fastforce
  
  lemma norm_pre_pure_iff_htt': 
  "< \<up> b*P > f <Q>T[t] = (b \<longrightarrow> <P> f <Q>T[t])"
  using htt_def by fastforce
        
        
      
      
subsection \<open>Proving time Bounds\<close>      

  definition "TBOUND m t \<equiv> \<forall>h. time m h \<le> t"

  lemma TBOUNDI[intro?]: "\<lbrakk>\<And>h. time m h \<le> t\<rbrakk> \<Longrightarrow> TBOUND m t"
    by (auto simp: TBOUND_def)
    
  lemma TBOUNDD: "TBOUND m t \<Longrightarrow> time m h \<le> t"  
    by (auto simp: TBOUND_def)
    
  lemma TBOUND_eqI:
    assumes "\<And>h. time m h = t"
    shows "TBOUND m t"  
    apply rule
    using assms by simp
    
  lemma TBOUND_empty: "TBOUND (Heap.Heap Map.empty) t"
    unfolding TBOUND_def time_def by (simp)
        
  lemma TBOUND_mono: "TBOUND c t \<Longrightarrow> t\<le>t' \<Longrightarrow> TBOUND c t'"  
    apply (auto simp: TBOUND_def)
    by (meson order.trans)

lemma TBOUND_refines: "TBOUND c t \<Longrightarrow> refines c d \<Longrightarrow> TBOUND d t"  
  apply (auto simp: TBOUND_def refines_def time_def) 
  apply(auto split: option.split)  
  subgoal for h a aa b 
  proof-
    assume 1: "\<forall>h. (case execute c h of None \<Rightarrow> 0 | Some (x, xa, t) \<Rightarrow> t) \<le> t"
    show "\<forall>h. case execute d h of None \<Rightarrow> True | Some (r, h', t) \<Rightarrow> execute c h = Some (r, h', t) \<Longrightarrow>
    execute d h = Some (a, aa, b) \<Longrightarrow> b \<le> t "
    proof-
      assume 2:"\<forall>h. case execute d h of None \<Rightarrow> True | Some (r, h', t) \<Rightarrow> execute c h = Some (r, h', t)"
      show "execute d h = Some (a, aa, b) \<Longrightarrow> b \<le> t "
      proof-
        assume "execute d h = Some (a, aa, b)"
        hence  "execute c h = Some (a, aa, b)" using 2
          by (smt (z3) old.prod.case option.simps(5))
        thus "b \<le> t" using 1
          by (metis old.prod.case option.simps(5))
      qed
    qed
  qed
  done

  
        
  text \<open>This rule splits a Hoare-triple with time into 
    a Hoare-triple without time and a time-bound proof, 
    thus separating the proof of correctness and time.
  \<close>
  lemma httI_TBOUND: 
    assumes "<P> c <Q>"
    assumes "TBOUND c t"
    shows "< P> c <Q>T[t]"
    by (simp add: TBOUNDD assms(1) assms(2) httI)

  lemma htt_htD:  
    assumes "<P> c <Q>T[t]"
    shows "<P> c <Q>"
    using assms htt_def by auto
    
  subsubsection \<open>Admissibility\<close>  
  context begin
  private lemma TBOUND_adm_aux:
    "(\<lambda>f. \<forall>xx y. f xx = Some y \<longrightarrow> (case y of (_,_,tt) \<Rightarrow> tt \<le> t x))
     = (\<lambda>xa. \<forall>h. time (Heap.Heap xa) h \<le> t x)"
    apply (auto simp: fun_eq_iff time_def split: option.splits) 
    done
  
  lemma TBOUND_adm: "heap.admissible (\<lambda>f. \<forall>x. TBOUND (f x) (t x))"
    unfolding TBOUND_def
    apply (rule admissible_fun[OF heap_interpretation])
  
    unfolding Heap_lub_def Heap_ord_def
    apply (rule admissible_image)
    subgoal
      by (simp add: flat_interpretation partial_function_lift)
  
    subgoal
      apply (simp add: comp_def)
      apply (fold TBOUND_adm_aux)
      using option_admissible .
  
     apply (metis Heap_execute)  
    by simp
  end
  
  text \<open>Ad-hoc instances of admissible rule\<close>  
  lemma TBOUND_fi_adm: "heap.admissible (\<lambda> fi'. \<forall>x xa. TBOUND (curry fi' x xa) (foo x xa))"  
    apply (rule ccpo.admissibleI)
    apply clarsimp  
    apply (rule ccpo.admissibleD[OF TBOUND_adm, rule_format, where t="\<lambda>(x,xa). foo x xa" and x="(x,xa)" for x xa, simplified])
    by auto
  
  lemma TBOUND_fi'_adm: "heap.admissible (\<lambda> fi'. \<forall>x xa xb. TBOUND (curry (curry fi') x xa xb) (foo x xa xb))"  
    apply (rule ccpo.admissibleI)
    apply clarsimp
    apply (rule ccpo.admissibleD[OF TBOUND_adm, rule_format, where t="\<lambda>((x,xa),xb). foo x xa xb" and x="((x,xa),xb)" for x xa xb, simplified])
    by auto
  
  
  subsubsection \<open>Syntactic Rules for \<^const>\<open>TBOUND\<close>\<close>    
      
  text \<open>Technical workaround: 
    Tag to protect a schematic variable from the simplifier's solver.
    Used to simplify a term and then unify with schematic variable.
    
    A goal of the form \<open>EQ t ?t'\<close> can be simplified, and then resolved with rule \<open>EQ_refl\<close>.
    If one would run the simplifier on \<open>t = ?t'\<close>, the solver would apply @{thm refl} immediately, 
    not simplifying \<open>t\<close>.
  \<close>
  definition "EQ a b \<equiv> a=b"  
  lemma EQI: "a=b \<Longrightarrow> EQ a b" by (simp add: EQ_def)
  lemma EQD: "EQ a b \<Longrightarrow> a=b" by (simp add: EQ_def)
  lemma EQ_refl: "EQ a a" by (simp add: EQ_def)  
    

  named_theorems TBOUND \<open>Syntactic rules for time-bounds\<close>
    
  lemma TBOUND_bind: 
    assumes "TBOUND m t\<^sub>1"
    assumes "\<And>x h. \<lbrakk>x = the_res m h; \<not>fails m h\<rbrakk> \<Longrightarrow> TBOUND (f x) t\<^sub>2"
    shows "TBOUND (do {x\<leftarrow>m; f x}) (t\<^sub>1 + t\<^sub>2)"
    apply (rule)
    using assms[THEN TBOUNDD]
    apply (auto simp add: time_simp add_mono)
    done

  lemma TBOUND_assert'_bind: 
    assumes "EQ P P'"
    assumes "P \<Longrightarrow> TBOUND m t"
    shows "TBOUND (do {assert' P; m}) (if P' then t else 0)"
    apply (rule)
    using assms(2)[THEN TBOUNDD] using assms(1)[THEN EQD]
    apply (auto simp add: time_simp add_mono fails_simp)
    done

  lemma TBOUND_assert'_weak[TBOUND]: 
    assumes "P \<Longrightarrow> TBOUND m t"
    shows "TBOUND (do {assert' P; m}) t"
    apply (rule)
    using assms[THEN TBOUNDD]
    apply (auto simp add: time_simp add_mono fails_simp)
    done

  lemma TBOUND_bind_weak[TBOUND]: 
    assumes "TBOUND m t\<^sub>1"
    assumes "\<And>x h. \<lbrakk>\<not>fails m h\<rbrakk> \<Longrightarrow> TBOUND (f x) t\<^sub>2"
    shows "TBOUND (do {x\<leftarrow>m; f x}) (t\<^sub>1 + t\<^sub>2)"
    apply (rule)
    using assms[THEN TBOUNDD]
    apply (auto simp add: time_simp add_mono)
    done
    

  lemma TBOUND_return[TBOUND]: "TBOUND (return x) 1"
    apply(rule TBOUND_eqI)
    apply(simp add: time_simp)
    done
  
  lemma TBOUND_of_list[TBOUND]: "TBOUND (Array_Time.of_list xs) (Suc (length xs))"
     apply(rule TBOUND_eqI)
    apply(simp add: time_simp)
    done
  
  lemma TBOUND_len[TBOUND]: "TBOUND (Array_Time.len xs) 1"
     apply(rule TBOUND_eqI)
    apply(simp add: time_simp)
    done
  
  lemma TBOUND_nth[TBOUND]: "TBOUND (Array_Time.nth xs i) 1"
    apply(rule TBOUNDI)
    apply(simp add: time_simp)
    done
  
  lemma TBOUND_upd[TBOUND]: "TBOUND (Array_Time.upd xs i x) 1"
    apply(rule TBOUNDI)
    apply(simp add: time_simp)
    done
  
  lemma TBOUND_new[TBOUND]: "TBOUND (Array_Time.new n x) (n+1)"
    apply(rule TBOUNDI)
    apply(simp add: time_simp)
    done
  
  lemma TBOUND_make[TBOUND]: "TBOUND (Array_Time.make n f) (n+1)"
    apply(rule TBOUNDI)
    apply(simp add: time_simp)
    done
  
  lemma TBOUND_swap[TBOUND]: "TBOUND (Array_Time.swap i x a) 2"
    apply(rule TBOUNDI)
    apply(subst time_simp)
    apply(simp)
    done
  
  lemma TBOUND_map_entry[TBOUND]: "TBOUND (Array_Time.map_entry i x a) 2"
    apply(rule TBOUNDI)
    apply(subst time_simp)
    apply(simp)
    done
  
  lemma TBOUND_cons: " TBOUND m t\<Longrightarrow> EQ t  t' \<Longrightarrow> TBOUND m t'"
    unfolding EQ_def
    by simp
  
  
  lemma TBOUND_if_max[TBOUND]:
    assumes "P \<Longrightarrow> TBOUND m bm"
    assumes "\<not> P \<Longrightarrow> TBOUND n bn"
    shows "TBOUND (if P then m else n) (max bm bn)"
    using assms 
    apply( auto simp add: TBOUND_def max_def)
     apply (meson TBOUNDD TBOUND_mono assms)
    apply (meson dual_order.trans nat_le_linear)
    done
  
  lemma TBOUND_if_strong:
    assumes "EQ b b'" 
      assumes "b \<Longrightarrow> TBOUND m\<^sub>1 t\<^sub>1"  
      assumes "\<not>b \<Longrightarrow> TBOUND m\<^sub>2 t\<^sub>2"  
      shows "TBOUND (if b then m\<^sub>1 else m\<^sub>2) (if b' then t\<^sub>1  else t\<^sub>2)"
    using assms unfolding EQ_def by auto
  
    
  lemma TBOUND_if: 
    assumes "b \<Longrightarrow> TBOUND m\<^sub>1 t\<^sub>1"  
    assumes "\<not>b \<Longrightarrow> TBOUND m\<^sub>2 t\<^sub>2"  
    shows "TBOUND (if b then m\<^sub>1 else m\<^sub>2) (if b then t\<^sub>1 else t\<^sub>2)"
    using assms by auto
    
  lemma TBOUND_Let: 
    assumes "\<And>x. x = v \<Longrightarrow> TBOUND (f x) (t x)"  
    shows "TBOUND (let x=v in f x) (let x=v in t x)"
    using assms by auto
      
  lemma TBOUND_Let_strong: 
    assumes "EQ v v'"
    assumes "\<And> x. x = v \<Longrightarrow> TBOUND (f x) (bnd x)"
    shows " TBOUND (let x = v in f x) (let x = v' in bnd x)"
    using assms unfolding EQ_def by simp
  
  lemma TBOUND_Let_weak[TBOUND]: 
    assumes "\<And> x. x = v \<Longrightarrow> TBOUND (f x) (bnd )"
    shows " TBOUND (let x = v in f x) bnd "
    using assms by simp

  lemma TBOUND_option_case[TBOUND]: 
    assumes "t = None \<Longrightarrow> TBOUND f bnd"
     "\<And> x. t = Some x \<Longrightarrow> TBOUND (f' x) (bnd' x)"
    shows "TBOUND (case t of None \<Rightarrow> f | Some x \<Rightarrow> f' x) 
                (case t of None \<Rightarrow> bnd | Some x \<Rightarrow> bnd' x)"
    using assms
    apply(cases t)
     apply auto
    done

  lemma TBOUND_prod_case[TBOUND]:
    assumes "\<And> a b. t = (a, b) \<Longrightarrow> TBOUND (f a b) (bnd a b)"
    shows "TBOUND (case t of (a, b) \<Rightarrow> f a b) (case t of (a, b) \<Rightarrow> bnd a b) "
    using assms apply(cases t)
    by auto

 lemma TBOUND_assert'_bind_strong: 
    assumes "P \<Longrightarrow> TBOUND m t"
    shows "TBOUND (do {assert' P; m}) (if P then t else 0)"
    apply (rule)
    using assms[THEN TBOUNDD]
    apply (auto simp add: time_simp add_mono fails_simp)
    done

subsubsection \<open>Automation\<close>    
    
  named_theorems TBOUND_simps
  
  lemmas [TBOUND_simps] = if_cancel Let_const
  
  method TBOUND_simp_EQ = ( rule EQI; (elim conjE )? ;simp only: TBOUND_simps ; fail)
  
  method TBOUND_step_strong = (rule  TBOUND_assert'_bind TBOUND_Let_strong TBOUND_if_strong, TBOUND_simp_EQ) 
  
 method TBOUND_gen_step methods fallback =  
    (TBOUND_step_strong |
     rule TBOUND |
     assumption|
     rule TBOUND_cons, (rule TBOUND| assumption) |
     TBOUND_simp_EQ | 
     fallback)

  method TBOUND_step' = TBOUND_gen_step \<open>simp; fail\<close>
  method TBOUND_step = TBOUND_gen_step \<open>fail\<close>

 method defer_le = (rule asm_rl[of "_ \<le> _"], tactic \<open>defer_tac 1\<close>)

method TBOUND= (rule TBOUND_mono, ( TBOUND_step'+ ; fail), defer_le)

end
