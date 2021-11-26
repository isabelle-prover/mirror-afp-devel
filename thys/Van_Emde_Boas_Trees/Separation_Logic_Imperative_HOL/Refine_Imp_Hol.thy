section \<open>Refinement for Imperative-HOL Programs\<close>
theory Refine_Imp_Hol
  imports "Hoare_Triple"
            "HOL-Eisbach.Eisbach"
begin

  subsection \<open>Assertions\<close>
    
  text \<open>We add assertions that consume no time to Imperative HOL Time.
  
    Note that the original \<^const>\<open>assert\<close> consumes one time unit, i.e., is designed for 
    actually being checked at runtime. On the other hand, our assertions are not executable, 
    and must be refined before code generation.
  \<close>
  definition [code del]: "assert' P \<equiv> if P then ureturn () else raise ''assert''"

  lemma execute_assert'[execute_simps]: "execute (assert' P) h = (if P then Some ((),h,0) else None)"
    by (auto simp: assert'_def execute_simps)

  
  lemma assert'_rule: "\<lbrakk>\<And>h. h\<Turnstile>P \<Longrightarrow> \<phi>\<rbrakk> \<Longrightarrow> <P> assert' \<phi> <\<lambda>_. P>"  
    apply rule
    apply (auto simp: execute_simps in_range.simps relH_refl)
    done
    
  lemma assert'_bind_rule: 
    assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> \<phi>"
    assumes "\<phi> \<Longrightarrow> <P> c <Q>"
    shows "<P> do {assert' \<phi>; c} <Q>"  
    apply rule
    using assms
    apply (auto simp: execute_simps in_range.simps relH_refl elim!: hoare_tripleE)
    done    
    
  subsection \<open>Refinement Predicate\<close>  
  text \<open>An imperative-HOL program \<open>p\<close> refines a program \<open>q\<close>, if either \<open>q\<close> fails, or \<open>p\<close> returns the
    same result as \<open>q\<close>. In case \<open>q\<close> is already proved correct (in particular does not fail), this
    implies correctness of \<open>p\<close>. Moreover, for the refinement proof, we can assume that \<open>q\<close> does not fail,
    in particular, that all assertions in \<open>q\<close> hold. This can be used to transfer knowledge from the 
    correctness proof (proving the assertions) to the refinement proof (assuming the assertions).
  \<close>
  definition "refines p q \<equiv> \<forall>h. case execute q h of None \<Rightarrow> True | Some (r,h',t) \<Rightarrow> execute p h = Some (r,h',t)"

  lemma hoare_triple_refines:
    assumes "<P> c <Q>"
    assumes "refines c' c"
    shows "<P> c' <Q>"
    apply rule
    using assms
    by (auto simp: refines_def elim!: hoare_tripleE split: option.splits)
  
    
  subsubsection \<open>Admissibility\<close>
  context begin
  
  private lemma refines_adm_aux: "option.admissible (\<lambda>xa. \<forall>h a aa b. xa h = Some (a, aa, b) \<longrightarrow> execute (t x) h = Some (a, aa, b))"
  proof-
    have "option.admissible (\<lambda>xa. \<forall>h y. xa h = Some y \<longrightarrow> execute (t x) h = Some y)" 
      using option_admissible by metis
    thus ?thesis by auto
  qed
  
  lemma refines_adm: "heap.admissible (\<lambda>f. \<forall>x. refines (t x) (f x) )"
    unfolding refines_def
    apply (rule admissible_fun[OF heap_interpretation])
  
    unfolding Heap_lub_def Heap_ord_def
    apply (rule admissible_image)
    using option.partial_function_definitions_axioms partial_function_lift apply auto[1]
      apply(simp split: option.splits)
      apply auto[3]
    subgoal for x
      apply (simp add: comp_def)
      apply(rule refines_adm_aux)
      done
    subgoal for xa y 
      apply (metis Heap_execute)  
      done
    done
  
  end  

  subsection \<open>Syntactic rules for \<^const>\<open>refines\<close>\<close>  

  named_theorems refines_rule
  
  lemma refines_assert'[refines_rule]: "refines (ureturn ()) (assert' \<phi>)"
    unfolding refines_def
    by (simp add: execute_simps)
  
  lemma refines_assert'_bind[refines_rule]: "refines p q \<Longrightarrow> refines p (do {assert' \<phi>; q})"  
    unfolding refines_def
    apply (cases \<phi>)
    apply (auto simp add: execute_simps split: option.splits)
    done
    
  lemma refines_bind[refines_rule]: "refines m m' \<Longrightarrow> (\<And>x. refines (f x) (f' x)) \<Longrightarrow> refines (do {x\<leftarrow>m; f x}) (do {x\<leftarrow>m'; f' x})"
    unfolding refines_def
    apply clarsimp
    subgoal for h
      apply (cases "execute m' h"; cases "execute m h")
      apply (auto simp add: execute_simps split: option.splits)
      by (smt (verit, best) option.case(2) prod.simps(2) timeFrame.elims)
    done
    
  lemma refines_If[refines_rule]: "\<lbrakk>b\<Longrightarrow>refines t t'\<rbrakk> \<Longrightarrow> \<lbrakk>\<not>b\<Longrightarrow>refines e e'\<rbrakk> \<Longrightarrow> refines (If b t e) (If b t' e')" by auto
  lemma refines_Let[refines_rule]: "\<lbrakk> \<And>x. \<lbrakk>x=v\<rbrakk> \<Longrightarrow> refines (f x) (f' x) \<rbrakk> \<Longrightarrow> refines (let x=v in f x) (let x=v in f' x)" by auto
    
  
  lemma refines_refl: "refines p p"  
    unfolding refines_def
    by (auto split: option.splits)
 
  lemma refines_empty[simp]: "refines m  (Heap.Heap Map.empty)" 
    apply(simp add: refines_def)
    done
 
  lemma refines_let_right: assumes "refines m (m' a)"
    shows "refines m (let x = a in m' x)"
    using assms by simp
  
  lemma refines_case_prod_right: assumes "\<And> a b. refines m (m' a b)"
    shows "refines m (case t of (a,b) \<Rightarrow> m' a b)"
    using assms apply(cases t)
    by simp
  
  lemma refines_option[refines_rule]: assumes "a=a'" "refines m1 m1'" "\<And> x. refines (m2 x) (m2' x)"
    shows "refines (case a of None \<Rightarrow> m1 | Some x \<Rightarrow> m2 x)  (case a' of None \<Rightarrow> m1' | Some x \<Rightarrow> m2' x)"
    using assms apply(cases a')
     apply simp_all
    done
  
  lemma prod_case_refines[refines_rule]: assumes "p= p'" " \<And> a b. refines (f a b) (f' a b)"
    shows " refines (case p of (a, b) \<Rightarrow> f a b) (case p' of (a, b) \<Rightarrow> f' a b )" 
    using assms apply(cases p') by simp

subsection \<open>Automation\<close>    
    
  method refines_step= determ\<open>rule refines_rule refl refines_refl refines_let_right refines_case_prod_right 
                               | assumption | simp only:\<close>
  
  method refines = refines_step+    
    
end
