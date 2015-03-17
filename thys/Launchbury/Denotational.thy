theory Denotational
  imports "Abstract-Denotational-Props" "Value-Nominal"
begin

text {*
This is the actual denotational semantics as found in \cite{launchbury}.
*}

interpretation semantic_domain Fn Fn_project B B_project "\<Lambda> x. x".

abbreviation ESem_syn'' ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
abbreviation EvalHeapSem_syn''  ("\<^bold>\<lbrakk> _ \<^bold>\<rbrakk>\<^bsub>_\<^esub>"  [0,0] 110)  where "\<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> evalHeap \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)"
abbreviation HSem_syn' ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"
abbreviation HSem_bot  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>\<bottom>"

lemma ESem_simps_as_defined:
  "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> =  Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>(\<rho> f|` (fv (Lam [x].e)))(x := v)\<^esub>)"
  "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>    =  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<rho> x"
  "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>      =  \<rho>  x"
  "\<lbrakk> Bool b \<rbrakk>\<^bsub>\<rho>\<^esub>     =  B\<cdot>(Discr b)"
  "\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>\<^esub> = B_project\<cdot>(\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>\<^esub>)"
  "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>(\<rho> f|` fv (Let as body))\<^esub>"
  by (simp_all del: ESem_Lam ESem_Let add: ESem.simps(1,4) )

lemma ESem_simps:
  "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> =  Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>)"
  "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>    =  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<rho> x"
  "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>      =  \<rho>  x"
  "\<lbrakk> Bool b \<rbrakk>\<^bsub>\<rho>\<^esub>     =  B\<cdot>(Discr b)"
  "\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>\<^esub> = B_project\<cdot>(\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>\<^esub>)"
  "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub>"
  by simp_all
(*<*)

text {*
Excluded from the document, as these are unused in the current development.
*}

subsubsection {* Replacing subexpressions by variables *}

lemma HSem_subst_var_app:
  assumes fresh: "atom n \<sharp> x"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr)
  from fresh have [simp]: "n \<noteq> x" by (simp add: fresh_at_base)
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes fresh: "atom n \<sharp> x"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr)
  from fresh have [simp]: "n \<noteq> x" by (simp add: fresh_at_base)
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed
(*>*)


end
