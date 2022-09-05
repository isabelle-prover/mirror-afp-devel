(*  Title:      HOL/MicroJava/BV/Kildall.thy
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM

Kildall's algorithm.
*)

section \<open>Kildall's Algorithm \label{sec:Kildall}\<close>

theory Kildall_1
imports SemilatAlg
begin

primrec merges :: "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> 's list"
where
  "merges f []      \<tau>s = \<tau>s"
| "merges f (p'#ps) \<tau>s = (let (p,\<tau>) = p' in merges f ps (\<tau>s[p := \<tau> \<squnion>\<^bsub>f\<^esub> \<tau>s!p]))"


lemmas [simp] = Let_def Semilat.le_iff_plus_unchanged [OF Semilat.intro, symmetric]


lemma (in Semilat) nth_merges:
 "\<And>ss. \<lbrakk>p < length ss; ss \<in> nlists n A; \<forall>(p,t)\<in>set ps. p<n \<and> t\<in>A \<rbrakk> \<Longrightarrow>
  (merges f ps ss)!p = map snd [(p',t') \<leftarrow> ps. p'=p] \<Squnion>\<^bsub>f\<^esub> ss!p"
  (is "\<And>ss. \<lbrakk>_; _; ?steptype ps\<rbrakk> \<Longrightarrow> ?P ss ps")
(*<*)
proof (induct ps)
  show "\<And>ss. ?P ss []" by simp

  fix ss p' ps'
  assume ss: "ss \<in> nlists n A"
  assume l:  "p < length ss"
  assume "?steptype (p'#ps')"
  then obtain a b where
    p': "p'=(a,b)" and ab: "a<n" "b\<in>A" and ps': "?steptype ps'"
    by (cases p') auto
  assume "\<And>ss. p< length ss \<Longrightarrow> ss \<in> nlists n A \<Longrightarrow> ?steptype ps' \<Longrightarrow> ?P ss ps'"
  hence IH: "\<And>ss. ss \<in> nlists n A \<Longrightarrow> p < length ss \<Longrightarrow> ?P ss ps'" using ps' by iprover

  from ss ab
  have "ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a] \<in> nlists n A" by (simp add: closedD)
  moreover
  with l have "p < length (ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a])" by simp
  ultimately
  have "?P (ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a]) ps'" by (rule IH)
  with p' l
  show "?P ss (p'#ps')" by simp
qed
(*>*)


(** merges **)

lemma length_merges [simp]:
  "\<And>ss. size(merges f ps ss) = size ss"
(*<*) by (induct ps, auto) (*>*)

lemma (in Semilat) merges_preserves_type_lemma:
shows "\<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A)
         \<longrightarrow> merges f ps xs \<in> nlists n A"
(*<*)
apply (insert closedI)
apply (unfold closed_def)
apply (induct ps)
 apply simp
apply clarsimp
done
(*>*)

lemma (in Semilat) merges_preserves_type [simp]:
 "\<lbrakk> xs \<in> nlists n A; \<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A \<rbrakk>
  \<Longrightarrow> merges f ps xs \<in> nlists n A"
by (simp add: merges_preserves_type_lemma)

lemma (in Semilat) list_update_le_listI [rule_format]:
  "set xs \<subseteq> A \<longrightarrow> set ys \<subseteq> A \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<longrightarrow> p < size xs \<longrightarrow>  
   x \<sqsubseteq>\<^bsub>r\<^esub> ys!p \<longrightarrow> x\<in>A \<longrightarrow> xs[p := x \<squnion>\<^bsub>f\<^esub> xs!p] [\<sqsubseteq>\<^bsub>r\<^esub>] ys"
(*<*)
  apply (insert semilat)
  apply (simp only: Listn.le_def lesub_def semilat_def)
  apply (simp add: list_all2_conv_all_nth nth_list_update)
  done
(*>*)

lemma (in Semilat) merges_pres_le_ub:
  assumes "set ts \<subseteq> A"  "set ss \<subseteq> A"
    "\<forall>(p,t)\<in>set ps. t \<sqsubseteq>\<^bsub>r\<^esub> ts!p \<and> t \<in> A \<and> p < size ts"  "ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts"
  shows "merges f ps ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts"
(*<*)
proof -
  { fix t ts ps
    have
    "\<And>qs. \<lbrakk>set ts \<subseteq> A; \<forall>(p,t)\<in>set ps. t \<sqsubseteq>\<^bsub>r\<^esub> ts!p \<and> t \<in> A \<and> p< size ts \<rbrakk> \<Longrightarrow>
    set qs \<subseteq> set ps  \<longrightarrow> 
    (\<forall>ss. set ss \<subseteq> A \<longrightarrow> ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts \<longrightarrow> merges f qs ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts)"
    apply (induct_tac qs)
     apply simp
    apply (simp (no_asm_simp))
    apply clarify
    apply simp
    apply (erule allE, erule impE, erule_tac [2] mp)
     apply (drule bspec, assumption)
     apply (simp add: closedD)
    apply (drule bspec, assumption)
    apply (simp add: list_update_le_listI)
    done 
  } note this [dest]  
  from assms show ?thesis by blast
qed
(*>*)




end
