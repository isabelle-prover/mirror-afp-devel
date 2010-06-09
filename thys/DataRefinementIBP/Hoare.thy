header {* Hoare Triples  *}

theory Hoare

imports Statements WellFoundedTransitive

begin

text {*
A hoare triple for $p,q\in \mathit{State}\ \mathit{set}$, and 
$S : \mathit{State}\ \mathit{set} \to \mathit{State}\ \mathit{set}$ is valid,
denoted $\models p \{|S|\} q$, if every execution of $S$ starting from state $s\in p$
always terminates, and if it terminates in state $s'$, then $s'\in q$. When $S$ is
modeled as a predicate transformer, this definition is equivalent to requiring that
$p$ is a subset of the initial states from which the execution of $S$ is guaranteed
to terminate in $q$, that is $p \subseteq S\ q$.

The formal definition of a valid hoare triple only assumes that $p$ (and also $S\ q$) ranges
over a complete lattice.
*}

definition
  Hoare :: "'a::complete_lattice \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool" ("\<Turnstile> (_){| _ |}(_)" [0,0,900] 900) where
  "\<Turnstile> p {|S|} q = (p \<le> (S q))"

theorem hoare_sequential:
  "mono S \<Longrightarrow> (\<Turnstile> p {| S o T |} r) = ( (\<exists> q. \<Turnstile> p {| S |} q \<and> \<Turnstile> q {| T |} r))" 
  apply safe
  apply (simp_all add: Hoare_def mono_def)
  apply (rule_tac x = "T r" in exI)
  apply simp
  apply (rule_tac y = "S q" in order_trans)
  by auto

theorem hoare_choice:
  "\<Turnstile> p {| S \<sqinter> T |} q = (\<Turnstile> p {| S |} q \<and> \<Turnstile> p {| T |} q)"
  by (simp_all add: Hoare_def inf_fun_eq)

theorem hoare_assume:
  "(\<Turnstile> P {| assume R |} Q) = (P \<sqinter> R \<le> Q)"
  apply (simp add: Hoare_def assume_def)
  apply safe
  apply (case_tac "(inf P R) \<le> (inf (sup (- R) Q) R)")
  apply (simp add: inf_sup_distrib2 compl_inf_bot)
  apply (simp add: le_infI1)
  apply (case_tac "(sup (-R) (inf P R)) \<le> sup (- R) Q")
  apply (simp add: sup_inf_distrib1 compl_sup_top)
  by (simp add: le_supI2)

theorem hoare_mono:
  "mono S \<Longrightarrow> Q \<le> R \<Longrightarrow> \<Turnstile> P {| S |} Q \<Longrightarrow> \<Turnstile> P {| S |} R"
  apply (simp add: mono_def Hoare_def)
  apply (rule_tac y = "S Q" in order_trans)
  by auto

theorem hoare_pre:
  "R \<le> P \<Longrightarrow> \<Turnstile> P {| S |} Q \<Longrightarrow> \<Turnstile> R {| S |} Q"
  by (simp add: Hoare_def)

theorem hoare_Sup:
  "(\<forall> p \<in> P . \<Turnstile> p {| S |} q) \<Longrightarrow> \<Turnstile> Sup P {| S |} q"
  by (simp add: Hoare_def Sup_least)
  
lemma hoare_magic [simp]: "\<Turnstile> P {| top |} Q" 
  by (simp add: Hoare_def top_fun_eq)

lemma hoare_demonic: "\<Turnstile> P {| demonic R |} Q = (\<forall> s . s \<in> P \<longrightarrow>  R s \<subseteq> Q)"
  apply (unfold Hoare_def demonic_def)
  by auto

lemma hoare_not_guard:
  "mono S \<Longrightarrow> \<Turnstile> p {| S |} q \<Longrightarrow> \<Turnstile> (p \<squnion> (- grd S)) {| S |} q"
  apply (simp add: Hoare_def grd_def)
  apply (drule monoD)
  by auto

subsection {* Hoare rule for recursive statements *}

theorem fp_wf_induction:
  "mono f \<Longrightarrow> (\<forall> w . (p w) \<le> f (SUP_L p w)) \<Longrightarrow> f x = x \<Longrightarrow> SUP p \<le> x"
  apply (rule SUP_least)
  apply (rule less_induct1, simp_all)
  apply (rule_tac y = "f (SUP_L p xa)" in order_trans, simp)
  apply (drule_tac x = "SUP_L p xa" and y = "x" in monoD)
  by (simp_all add: SUP_L_least)

text {*
A statement $S$ is refined by another statement $S'$ if $\models p \{| S' |\} q$ 
is true for all $p$ and $q$ such that  $\models p \{| S |\} q$ is true. This
is equivalent to $S \le S'$. 

Next theorem can be used to prove refinement of a recursive program. A recursive
program is modeled as the least fixpoint of a monotonic mapping from predicate
transformers to predicate transformers.
*}

theorem lfp_wf_induction:
  "mono f \<Longrightarrow> (\<forall> w . (p w) \<le> f (SUP_L p w)) \<Longrightarrow> SUP p \<le> lfp f"
 apply (frule fp_wf_induction)
 apply simp_all
 apply (drule lfp_unfold)
 by simp

definition alpha_def:
  "\<alpha> x y z = (if y \<le> z then x else bot)"

lemma alpha_mono [simp]: "mono (\<alpha> x y)"
  apply (simp add: mono_def alpha_def)
  apply auto
  apply (drule_tac x = "y" and y = "xa" and z = "ya" in order_trans)
  by simp_all

lemma alpha_continous: 
  "\<alpha> (Sup X) y = Sup ((\<lambda> x . \<alpha> x y) ` X)"
  apply (rule antisym)
  apply (simp_all add: le_fun_def)
  apply auto
  apply (simp_all add: alpha_def)
  apply auto
  apply (simp_all add: Sup_fun_def)
  apply (simp_all add: alpha_def)
  apply (rule Sup_least)
  by auto

lemma alpha_continous1: 
  "\<alpha> (SUP X) y = SUP ((\<lambda> x . \<alpha> x y) o X)"
  by (simp add: expand_fun_eq alpha_def SUP_fun_eq, simp)

text {*
Next theorem shows the equivalence between the validity of Hoare
triples and refinement statements. This theorem together with the
theorem for refinement of recursive programs will be used to prove
a Hoare rule for recursive programs.
*}

theorem hoare_refinement_alpha:
  "mono f \<Longrightarrow>  (\<Turnstile> x {| f |} y) = (\<alpha> x y \<le> f)"
  apply safe
  apply (simp_all add: Hoare_def)
  apply (simp_all add: le_fun_def)
  apply (simp add: alpha_def)
  apply auto
  apply (drule_tac x = "y" and y = "xa" in monoD)
  apply auto
  apply (case_tac "\<alpha> x y y \<le> f y")
  apply (simp add: alpha_def)
  apply (erule notE)
  by auto

lemma alpha_continous2:
 "SUP_L ((\<lambda>x. \<alpha> x y) \<circ> p) w =  \<alpha> (SUP_L p w) y"
  apply (simp add: SUP_L_def SUPR_def alpha_continous)
  apply (case_tac "((\<lambda> x. \<alpha> x y) \<circ> p) ` {v . v < w} = ((\<lambda>x . \<alpha> x y) ` p ` {v. v < w})")
  by auto

text {*
Next theorem gives a Hoare rule for recursive programs. If we can prove correct the unfolding 
of the recursive definition applid to a program $f$, $\models p\ w\ \{| F\  f |\}\  y$, assumming
that $f$ is correct when starting from $p\  v$, $v<w$, $\models SUP-L\  p\  w\  \{| f |\}\  y$, then
the recursive program is correct $\models SUP\ p\ \{| lfp\  F |\}\  y$
*}

theorem hoare_fixpoint:
  "mono_mono F \<Longrightarrow>
   (!! w f . mono f \<and> \<Turnstile> SUP_L p w {| f |} y \<Longrightarrow> \<Turnstile> p w {| F f |} y) \<Longrightarrow> \<Turnstile> SUP p {| lfp F |} y"
  apply (simp add: mono_mono_def hoare_refinement_alpha)
  apply (simp add: alpha_continous1)
  apply (rule lfp_wf_induction)
  apply auto
  apply (simp add: alpha_continous2)
  apply (drule_tac x = "\<alpha> (SUP_L p w) y" in spec)
  by (simp add: hoare_refinement_alpha)

end