(*  ID:         $Id: QElin_opt.thy,v 1.2 2008-01-11 15:22:28 lsf37 Exp $
    Author:     Tobias Nipkow, 2007
*)

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

definition qe_less' :: "atom list \<Rightarrow> atom fm" where
"qe_less' as = list_conj [asimp(combine p q). p\<leftarrow>lbounds as, q\<leftarrow>ubounds as]"

lemma I_asimp: "R.I (asimp a) xs = I\<^isub>R a xs"
by(simp add:asimp_def iprod0_if_coeffs0 split:atom.split)

lemma I_qe_less': "R.I (qe_less' as) xs = R.I (qe_less as) xs"
by(simp add:qe_less_def qe_less'_def I_asimp)

definition "lin_qe' = R\<^isub>e.lift_dnfeq_qe qe_less'"

lemma qfree_qe_less': "qfree (qe_less' as)"
by(auto simp:qe_less_def qe_less'_def asimp_def intro!:qfree_list_conj
        split:atom.split)

corollary I_lin_qe': "R.I (lin_qe' \<phi>) xs = R.I \<phi> xs"
unfolding lin_qe'_def
apply(rule R\<^isub>e.I_lift_dnfeq_qe)
 apply(rule qfree_qe_less')
apply(rule allI)
apply(subst I_qe_less')
apply(rule I_qe_less)
 prefer 2 apply blast
apply(clarify)
apply(drule_tac x=a in bspec) apply simp
apply(simp add: depends\<^isub>R_def split:atom.splits list.splits)
done

theorem qfree_lin_qe': "qfree (lin_qe' f)"
by(simp add:lin_qe'_def R\<^isub>e.qfree_lift_dnfeq_qe qfree_qe_less')

end
