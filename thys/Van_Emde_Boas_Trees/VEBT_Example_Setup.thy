(*by Lammich and Ammer*)
section \<open>Setup for Usage Example\<close>
theory VEBT_Example_Setup
imports "Time_Reasoning/Simple_TBOUND_Cond"
begin
  text \<open>We provide a few monadic combinators and associated reasoning rules, 
    that are required for our usage example.
    
    Warning: ad-hoc and highly incomplete!
  \<close>

  fun mfold where
    "mfold f [] s = return s"
  | "mfold f (x#xs) s = do { s \<leftarrow> f x s; mfold f xs s }"  

  fun mmap where
    "mmap f [] = return []"
  | "mmap f (x#xs) = do { y\<leftarrow>f x; ys \<leftarrow> mmap f xs; return (y#ys) }"
  
  definition mIf :: "bool Heap \<Rightarrow> 'a Heap \<Rightarrow> 'a Heap \<Rightarrow> 'a Heap"
    ("(if\<^sub>m (_)/ then (_)/ else (_))" [0, 0, 10] 10)
    where "mIf b t e \<equiv> do { bb \<leftarrow> b; if bb then t else e }"
  
  lemma mIf_rule[sep_decon_rules]: 
    "<P> do { bb \<leftarrow> b; if bb then t else e } <Q> \<Longrightarrow> <P> mIf b t e <Q>"  
    unfolding mIf_def by simp

  abbreviation (input) pure_app (infix "$\<^sub>m" 10) where "f $\<^sub>m m \<equiv> do { x\<leftarrow>m; return (f x) }" 
  
    
  lemma mmap_pure_aux:
    assumes "\<And>x. x\<in>set xs \<Longrightarrow> <P> fi x <\<lambda>r. P * \<up>(r = f x)>"
    shows "<P> mmap fi xs <\<lambda>ys. P * \<up>(ys = map f xs )>"
    using assms
  proof (induction xs)
    case Nil
    then show ?case by sep_auto
  next
    case (Cons a xs)
    
    note [sep_heap_rules] = Cons
    
    show ?case 
      by sep_auto
    
  qed

lemma mmap_pres:
    assumes "\<And>x. x\<in>set xs \<Longrightarrow> <P> fi x <\<lambda>r. P>"
    shows "<P> mmap fi xs <\<lambda>ys. P >"
  using assms
  apply(induction xs)
   apply sep_auto+
  done

  
 lemma cond_TBOUND_mIf[cond_TBOUND]:
   assumes "\<section> P \<section> TBOUND cond b1"
    and    "\<And> h. \<section> Q (the_res cond h)\<section> TBOUND t b2"
    and    "\<And> h.\<section> Q (the_res cond h) \<section> TBOUND e b3"
    and    "<P> cond <Q>"
  shows    "\<section> P \<section> TBOUND (if\<^sub>m cond then t else e) (b1 + max b2 b3)"
   unfolding mIf_def
   apply(rule cond_TBOUND_bind)
   apply (rule assms)+
   subgoal for x h
    apply(auto split: if_split)
    apply(rule cond_TBOUND_mono[where b = b2])
     using assms apply (metis (full_types))
      apply simp
    apply(rule cond_TBOUND_mono[where b = b3])
     using assms apply (metis (full_types))
     apply simp
    done
   done

end
