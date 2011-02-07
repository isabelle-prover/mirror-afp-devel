(*  Author:     Tobias Nipkow, 2007  *)

theory QElin_opt
imports QElin
begin

subsubsection{*An optimization*}

text{* Atoms are simplified asap. *}

definition
"asimp a = (case a of
 Less r cs \<Rightarrow> (if \<forall>c\<in> set cs. c = 0
               then if r<0 then TrueF else FalseF
               else Atom a) |
 Eq r cs \<Rightarrow> (if \<forall>c\<in> set cs. c = 0
             then if r=0 then TrueF else FalseF else Atom a))"

lemma asimp_pretty:
"asimp (Less r cs) =
 (if \<forall>c\<in> set cs. c = 0
  then if r<0 then TrueF else FalseF
  else Atom(Less r cs))"
"asimp (Eq r cs) =
 (if \<forall>c\<in> set cs. c = 0
  then if r=0 then TrueF else FalseF
  else Atom(Eq r cs))"
by(auto simp:asimp_def)

definition qe_FMo\<^isub>1 :: "atom list \<Rightarrow> atom fm" where
"qe_FMo\<^isub>1 as = list_conj [asimp(combine p q). p\<leftarrow>lbounds as, q\<leftarrow>ubounds as]"

lemma I_asimp: "R.I (asimp a) xs = I\<^isub>R a xs"
by(simp add:asimp_def iprod0_if_coeffs0 split:atom.split)

lemma I_qe_FMo\<^isub>1: "R.I (qe_FMo\<^isub>1 as) xs = R.I (qe_FM\<^isub>1 as) xs"
by(simp add:qe_FM\<^isub>1_def qe_FMo\<^isub>1_def I_asimp)

definition "qe_FMo = R\<^isub>e.lift_dnfeq_qe qe_FMo\<^isub>1"

lemma qfree_qe_FMo\<^isub>1: "qfree (qe_FMo\<^isub>1 as)"
by(auto simp:qe_FM\<^isub>1_def qe_FMo\<^isub>1_def asimp_def intro!:qfree_list_conj
        split:atom.split)

corollary I_qe_FMo: "R.I (qe_FMo \<phi>) xs = R.I \<phi> xs"
unfolding qe_FMo_def
apply(rule R\<^isub>e.I_lift_dnfeq_qe)
 apply(rule qfree_qe_FMo\<^isub>1)
apply(rule allI)
apply(subst I_qe_FMo\<^isub>1)
apply(rule I_qe_FM\<^isub>1)
 prefer 2 apply blast
apply(clarify)
apply(drule_tac x=a in bspec) apply simp
apply(simp add: depends\<^isub>R_def split:atom.splits list.splits)
done

theorem qfree_qe_FMo: "qfree (qe_FMo f)"
by(simp add:qe_FMo_def R\<^isub>e.qfree_lift_dnfeq_qe qfree_qe_FMo\<^isub>1)

end
