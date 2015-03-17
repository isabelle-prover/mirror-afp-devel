theory ResourcedDenotational
imports "Abstract-Denotational-Props" "CValue-Nominal" "C-restr"
begin

type_synonym CEnv = "var \<Rightarrow> CValue"

interpretation semantic_domain
  "\<Lambda> f . \<Lambda> r. CFn\<cdot>(\<Lambda> v. (f\<cdot>(v|\<^bsub>r\<^esub>))|\<^bsub>r\<^esub>)"
  "\<Lambda> x y. (\<Lambda> r. (x\<cdot>r \<down>CFn y|\<^bsub>r\<^esub>)\<cdot>r)"
  "\<Lambda> b r. CB\<cdot>b"
  "\<Lambda> scrut v1 v2 r. CB_project\<cdot>(scrut\<cdot>r)\<cdot>(v1\<cdot>r)\<cdot>(v2\<cdot>r)"
  "C_case".

abbreviation ESem_syn'' ("\<N>\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
abbreviation EvalHeapSem_syn''  ("\<^bold>\<N>\<lbrakk> _ \<^bold>\<rbrakk>\<^bsub>_\<^esub>"  [0,0] 110)  where "\<^bold>\<N>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> evalHeap \<Gamma> (\<lambda> e. \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)"
abbreviation HSem_syn' ("\<N>\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"
abbreviation HSem_bot ("\<N>\<lbrace>_\<rbrace>"  [60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace> \<equiv> \<N>\<lbrace>\<Gamma>\<rbrace>\<bottom>"

text {*
Here we re-state the simplification rules, cleaned up by beta-reducing the locale parameters.
*}

lemma CESem_simps:
  "\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>  = (\<Lambda> (C\<cdot>r). CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v|\<^bsub>r\<^esub>)\<^esub>)|\<^bsub>r\<^esub>))"
  "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>     = (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn \<rho> x|\<^bsub>r\<^esub>)\<cdot>r)"
  "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>       = (\<Lambda> (C\<cdot>r). (\<rho>  x) \<cdot> r)"
  "\<N>\<lbrakk> Bool b \<rbrakk>\<^bsub>\<rho>\<^esub>      = (\<Lambda> (C\<cdot>r). CB\<cdot>(Discr b))"
  "\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>\<^esub>  = (\<Lambda> (C\<cdot>r). CB_project\<cdot>((\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r))"
  "\<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C \<cdot> r). (\<N>\<lbrakk>body\<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<rho>\<^esub>) \<cdot> r)"
  by (auto simp add: eta_cfun)

lemma CESem_bot[simp]:"(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>\<bottom> = \<bottom>"
  by (nominal_induct e arbitrary: \<sigma> rule: exp_strong_induct) auto

lemma CHSem_bot[simp]:"((\<N>\<lbrace> \<Gamma> \<rbrace>) x)\<cdot>\<bottom> = \<bottom>"
  by (cases "x \<in> domA \<Gamma>") (auto simp add: lookup_HSem_heap lookup_HSem_other)

text {*
Sometimes we do not care much about the resource usage and just want a simpler formula.
*}

lemma CESem_simps_no_tick:
  "(\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v|\<^bsub>r\<^esub>)\<^esub>)|\<^bsub>r\<^esub>)"
  "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r    \<sqsubseteq> ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn \<rho> x|\<^bsub>r\<^esub>)\<cdot>r"
  "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>         \<sqsubseteq> \<rho> x"
  "(\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> CB_project\<cdot>((\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r)"
  "\<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub>   \<sqsubseteq>  \<N>\<lbrakk>body\<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<rho>\<^esub>"
  apply -
  apply (rule below_trans[OF monofun_cfun_arg[OF below_C]], simp)
  apply (rule below_trans[OF monofun_cfun_arg[OF below_C]], simp)
  apply (rule cfun_belowI, rule below_trans[OF monofun_cfun_arg[OF below_C]], simp)
  apply (rule below_trans[OF monofun_cfun_arg[OF below_C]], simp)
  apply (rule cfun_belowI, rule below_trans[OF monofun_cfun_arg[OF below_C]], simp)
  done

lemma CELam_no_restr: "(\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>))"
proof-
  have "(\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v|\<^bsub>r\<^esub>)\<^esub>)|\<^bsub>r\<^esub>)" by (rule CESem_simps_no_tick)
  also have "\<dots> \<sqsubseteq> CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>))"
    by (intro cont2cont monofun_LAM below_trans[OF C_restr_below] monofun_cfun_arg below_refl fun_upd_mono)
  finally show ?thesis by this (intro cont2cont)
qed

lemma CEApp_no_restr: "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r    \<sqsubseteq> ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn \<rho> x)\<cdot>r"
proof-
  have "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r  \<sqsubseteq> ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn \<rho> x|\<^bsub>r\<^esub>)\<cdot>r" by (rule CESem_simps_no_tick)
  also have "\<rho> x|\<^bsub>r\<^esub> \<sqsubseteq> \<rho> x" by (rule C_restr_below)
  finally show ?thesis by this (intro cont2cont)
qed

end

