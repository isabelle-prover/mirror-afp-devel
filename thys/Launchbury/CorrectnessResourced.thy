theory CorrectnessResourced
  imports "ResourcedDenotational" Launchbury
begin

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) - domA \<Gamma> \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (domA \<Gamma>)"
  using assms
proof(nominal_induct arbitrary: \<rho> rule:reds.strong_induct)
case Lambda
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  hence "y \<noteq> x" by (simp_all add: fresh_at_base)

  have Gamma_subset: "domA \<Gamma> \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF Application.hyps(8)])

  case 1
  hence prem1: "fv (\<Gamma>, e) - domA \<Gamma> \<subseteq> set (x#L)" by auto

  from 1 Gamma_subset have *: "x \<in> set L \<or> x \<in> domA \<Delta>" by auto

  have "fv (\<Delta>, e'[y::=x]) - domA \<Delta> \<subseteq> (fv (\<Delta>, Lam [y]. e') - domA \<Delta>) \<union> {x}"
    by (auto dest!: set_mp[OF fv_subst_subset])
  also have "\<dots> \<subseteq> (fv (\<Gamma>, e) - domA \<Gamma>) \<union> {x}"
    using new_free_vars_on_heap[OF Application.hyps(8)] by auto
  also have "\<dots> \<subseteq> set L \<union> {x}" using prem1 by auto
  finally have "fv (\<Delta>, e'[y::=x]) - domA \<Delta> \<subseteq> set L \<union> {x}". 
  with *
  have prem2: "fv (\<Delta>, e'[y::=x]) - domA \<Delta> \<subseteq> set L" by auto
  
  have *: "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x"
  proof(cases "x \<in> domA \<Gamma>")
    case True
    thus ?thesis
      using fun_belowD[OF Application.hyps(10)[OF prem1], where \<rho>1 = \<rho> and x = x]
      by simp
  next
    case False 
    from False reds_avoids_live[OF Application.hyps(8)]
    show ?thesis by (simp add: lookup_HSem_other)
  qed

  {
  fix r
  have "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x)\<cdot>r"
    by (rule CEApp_no_restr)
  also have "((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)) \<sqsubseteq> ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>))"
    using Application.hyps(9)[OF prem1].
  also note `((\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x`
  also have "(\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> (CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := v)\<^esub>)))"
    by (rule CELam_no_restr)
  also have "CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := v)\<^esub>)) \<down>CFn ((\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x) = (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x)\<^esub>)"
    by simp
  also have "\<dots> = (\<N>\<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>)"
    unfolding ESem_subst[OF `y \<noteq> x`]..
  also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    using Application.hyps(12)[OF prem2].
  finally
  have "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> (\<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>)\<cdot>r" by this (intro cont2cont)+
  }
  thus ?case by (rule cfun_belowI)
  
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Theta>\<rbrace>\<rho>)  f|` (domA \<Gamma>)"
    using Application.hyps(10)[OF prem1]
          env_restr_below_subset[OF Gamma_subset Application.hyps(13)[OF prem2]]
    by (rule below_trans)
next
case (Variable \<Gamma> x e L \<Delta> z)
  hence [simp]:"x \<in> domA \<Gamma>"
    by (metis domA_from_set map_of_is_SomeD)

  case 2

  have "x \<notin> domA \<Delta>"
    by (rule reds_avoids_live[OF Variable.hyps(2)], simp_all)

  have subset: "domA (delete x \<Gamma>) \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF Variable.hyps(2)])

  have "fv (delete x \<Gamma>, e) \<union> {x} \<subseteq> fv (\<Gamma>, Var x)"
    by (rule fv_delete_heap[OF `map_of \<Gamma> x = Some e`])
  hence prem: "fv (delete x \<Gamma>, e) - domA (delete x \<Gamma>) \<subseteq> set (x # L)" using 2 by auto

  have fv_subset: "fv (delete x \<Gamma>, e) - domA (delete x \<Gamma>) \<subseteq> - (domA \<Delta> - domA \<Gamma>)"
    apply (rule subset_trans[OF prem])
    apply (rule subset_trans[OF reds_avoids_live'[OF Variable.hyps(2)]])
    by auto

  let "?new" = "domA \<Delta> - domA \<Gamma>"
  have "domA \<Gamma> \<subseteq> (-?new)" by auto

  have "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> = \<N>\<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_reorder[OF map_of_delete_insert[symmetric, OF Variable(1)]])
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  finally
  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)f|` (- ?new) \<sqsubseteq> (...) f|` (- ?new)" by (rule ssubst) (rule below_refl)
  also have "\<dots> \<sqsubseteq> (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>)) f|` (- ?new)"
  proof (induction rule: parallel_fix_ind[where P ="\<lambda> x y. x f|` (- ?new) \<sqsubseteq> y f|` (- ?new)"])
    case 1 show ?case by simp
  next
    case 2 show ?case ..
  next
    case (3 \<sigma> \<sigma>')
    hence "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>'\<^esub>"
      and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` domA (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>') f|` domA (delete x \<Gamma>)"
      using fv_subset by (auto intro: ESem_fresh_cong_below HSem_fresh_cong_below  env_restr_below_subset[OF _ 3])
    from below_trans[OF this(1) Variable(3)[OF prem]] below_trans[OF this(2) Variable(4)[OF prem]]
    have  "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>'\<^esub>"
       and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` domA (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>') f|` domA (delete x \<Gamma>)".
    thus ?case
      using subset
      by (auto intro!: fun_belowI simp add: lookup_override_on_eq  lookup_env_restr_eq elim: env_restr_belowD)
  qed
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>)) f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem'[symmetric], OF `x \<notin> domA \<Delta>`])
  also have "\<dots> = (\<N>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>)  f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem[symmetric], OF `x \<notin> domA \<Delta>`])
  finally
  show le: ?case by (rule env_restr_below_subset[OF `domA \<Gamma> \<subseteq> (-?new)`]) (intro cont2cont)+

  have "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x" by (rule CESem_simps_no_tick)
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>) x"
    using fun_belowD[OF le, where x = x] by simp
  also have "\<dots> = \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    by (simp add: lookup_HSem_heap)
  finally
  show "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"  by this (intro cont2cont)+
next
case (Let as \<Gamma> L body \<Delta> z)
  case 1
  have *: "domA as \<inter> domA \<Gamma> = {}" by (metis Let.hyps(1) fresh_distinct)
  
  have "fv (as @ \<Gamma>, body) - domA (as @ \<Gamma>) \<subseteq> fv (\<Gamma>, Let as body) - domA \<Gamma>"
    by auto
  with 1 have prem: "fv (as @ \<Gamma>, body) - domA (as @ \<Gamma>) \<subseteq> set L" by auto
  
  have f1: "atom ` domA as \<sharp>* \<Gamma>"
    using Let(1) by (simp add: set_bn_to_atom_domA)

  have "\<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
     by (rule CESem_simps_no_tick)
  also have "\<dots> =  \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> \<sqsubseteq>  \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule Let.hyps(4)[OF prem])
  finally
  show ?case  by this (intro cont2cont)+

  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) = (\<N>\<lbrace>as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)) f|` (domA \<Gamma>)"
    unfolding env_restr_HSem[OF *]..
  also have "\<N>\<lbrace>as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) = (\<N>\<lbrace>as @ \<Gamma>\<rbrace>\<rho>)"
    by (rule HSem_merge[OF f1])
  also have "\<dots> f|` domA \<Gamma> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>"
    by (rule env_restr_below_subset[OF _ Let.hyps(5)[OF prem]]) simp
  finally
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>".
qed


corollary correctness_empty_env:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>"
proof-
  from assms(2) have "fv (\<Gamma>, e) - domA \<Gamma> \<subseteq> set L" by auto
  note corr = correctness[OF assms(1) this, where \<rho> = "\<bottom>"]

  show "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" using corr(1).

  have "\<N>\<lbrace>\<Gamma>\<rbrace> = (\<N>\<lbrace>\<Gamma>\<rbrace>) f|` domA \<Gamma> "
    using env_restr_useless[OF HSem_edom_subset, where \<rho>1 = "\<bottom>"] by simp
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>) f|` domA \<Gamma>" using corr(2).
  also have "\<dots> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by (rule env_restr_below_itself)
  finally show "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by this (intro cont2cont)+
qed

end
