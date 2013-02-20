theory CorrectnessUpd
imports "Denotational-PropsUpd" "Launchbury"
begin

text {*
This is the main correctness theorem, Theorem 2 from \cite{launchbury}.
*}

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "distinctVars \<Gamma>"
  and     "fdom \<rho> - heapVars \<Gamma> \<subseteq> set L"
  shows   "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  using assms
proof(nominal_induct avoiding: \<rho> rule:reds_distinct_strong_ind)
case (Lambda \<Gamma> x e L \<rho>)
  case 1 show ?case by rule
  case 2 show ?case by rule
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' \<rho>)
  hence [simp]:"atom y \<sharp> \<lbrace>\<Delta>\<rbrace>\<rho>" and "y \<noteq> x"
    by (simp_all add: fresh_at_base)

  case 1
  hence hyp1: "fdom \<rho> - heapVars \<Gamma> \<subseteq> set (x # L)" by auto
  have hyp2: "fdom \<rho> - heapVars \<Delta> \<subseteq> set L"
    using 1 reds_doesnt_forget[OF distinct_redsD1[OF Application.hyps(9)]]
    by auto

  have [simp]: "\<lbrace>\<Gamma>\<rbrace>\<rho> f! x = \<lbrace>\<Delta>\<rbrace>\<rho> f! x"
  proof(cases "x \<in> heapVars \<Gamma>")
  case True
    thus ?thesis
      by (simp add: fmap_less_eqD[OF Application.hyps(11)[OF hyp1]])
  next
  case False
    have "x \<notin> heapVars \<Delta>"
      by (rule reds_avoids_live[OF distinct_redsD1[OF Application.hyps(9)] _ False], simp)
    with False
    show ?thesis
      by (simp add: the_lookup_HSem_other)
  qed

  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
  also have "\<dots> = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF Application.hyps(10)[OF hyp1]])
  also have "\<dots> = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by simp
  also have "... = \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<^esub>"
    by simp
  also have "... = \<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule ESem_subst[OF `y \<noteq> x` `atom y \<sharp> \<lbrace>\<Delta>\<rbrace>\<rho>`])
  also have "\<dots> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    by (rule Application.hyps(13)[OF hyp2])
  finally
  show ?case.
  
  case 2
  show ?case using Application hyp1 hyp2
    by (metis order_trans)
next
case (Variable x e \<Gamma> L \<Delta> z \<rho>)
  hence [simp]:"x \<in> heapVars \<Gamma>"
    by (metis heapVars_from_set)

  case 2

  have "x \<notin> heapVars \<Delta>"
    by (rule reds_avoids_live[OF distinct_redsD1[OF Variable.hyps(2)]], simp_all)

  have subset: "heapVars (delete x \<Gamma>) \<subseteq> heapVars \<Delta>"
    by (rule reds_doesnt_forget[OF distinct_redsD1[OF Variable.hyps(2)]])

  have new_fresh[simp]: "(heapVars \<Delta> - (heapVars \<Gamma> - {x})) \<inter> fdom \<rho> = {}"
    using reds_avoids_live[OF distinct_redsD1[OF Variable.hyps(2)]] 2
    by auto

  have [simp]: "insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) - heapVars \<Delta> = insert x (fdom \<rho> - heapVars \<Gamma>)"
    using new_fresh subset `x \<notin> _` by (auto simp del:new_fresh)

  have [simp]: "insert x (fdom \<rho> \<union> heapVars \<Delta>) - heapVars \<Delta> = insert x (fdom \<rho> - heapVars \<Gamma>)"
    using new_fresh subset `x \<notin> _` by (auto simp del:new_fresh)

  have [simp]: "(insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) \<inter> heapVars \<Delta>) = heapVars \<Gamma> - {x}"
    using new_fresh subset `x \<notin> _` by (auto simp del:new_fresh)

  have [simp]:"\<And> x y . x \<union> y \<union> y = x \<union> y" "\<And> x y. (x \<union> y) \<inter> y = y"
    by auto

  have [simp]: "insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) - (heapVars  \<Gamma> - {x}) = insert x (fdom \<rho> - heapVars \<Gamma>)"
    by auto

  have [simp]: "(heapVars \<Gamma> - {x}) \<inter> (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) = (heapVars \<Gamma> - {x})"
    by auto

  have [simp]: "(fdom \<rho> - heapVars \<Gamma>) \<inter> (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) = (fdom \<rho> - heapVars \<Gamma>)"
    by auto

  have condGamma: "fix_on_cond {\<rho>' . f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub> \<sqsubseteq> \<rho>'}
                               (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
                               (\<lambda>\<rho>'a. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'a))(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'a\<^esub>))"
    apply (rule fix_on_cond_cong[OF iterative_HSem'_cond])
      apply simp
      apply (rule arg_cong[OF Variable.hyps(3)])
    using 2 by auto

  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    apply (rule HSem_reorder)
    apply (simp_all add: Variable(5) distinctVars_Cons distinctVars_delete)[2]
    apply (rule distinctVars_set_delete_insert[symmetric, OF Variable(5) Variable(1)])
    done
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>))"
    apply (rule fix_on_cong[OF _ arg_cong[OF  Variable.hyps(3)]])
    apply (rule iterative_HSem'_cond)
    using 2 by auto
  also have "\<dots> \<le> fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Delta>) (\<lbrace>\<Delta>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>))"
    apply (subst fmap_less_restrict)
    apply (rule parallel_fix_on_ind[OF condGamma iterative_HSem'_cond[OF `x \<notin> heapVars \<Delta>`]])
    apply (intro adm_is_adm_on adm_lemmas cont2cont)
    (* bottom *)
    using subset apply auto[1]
    (* step *)
    apply simp
      apply (drule sym)
      apply (drule sym)
    apply (simp add: fmap_restr_fmap_upd fmap_restr_add)
    apply (rule arg_cong2[where f = "\<lambda> \<rho>. fmap_upd \<rho> x", OF arg_cong2[where f = "op f++"]])

    (* \<rho> *)
    apply (subst fmap_restr_useless[symmetric], auto)[1]

    (* \<Gamma> *)
    apply (subst Variable.hyps(4)[unfolded fmap_less_restrict])
      using 2 apply (auto)[1]
    apply simp
    apply (subst (1 2) HSem_restr[symmetric])
    apply simp
    
    (* x *)
    apply (subst (1 2) HSem_restr[symmetric])
    apply simp
    done
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Delta>) (\<lbrace>\<Delta>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem'[symmetric, OF reds_avoids_live[OF distinct_redsD1[OF Variable(2)]]], simp_all)
  also have "\<dots> = \<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>"
    by (rule iterative_HSem[symmetric, OF reds_avoids_live[OF distinct_redsD1[OF Variable(2)]]], simp_all)
  finally
  show le: ?case.

  case 1
  have "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    by (simp add: fmap_less_eqD[OF le])
  also have "\<dots> =  \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    by (simp add: the_lookup_HSem_heap)
  finally
  show ?case.
next
case (Let as \<Gamma> L body \<Delta> z \<rho>)
  case 1
  { fix a
    assume a: "a \<in> heapVars (asToHeap as)"
    have "atom a \<sharp> L" 
      by (rule Let(2)[unfolded fresh_star_def set_bn_to_atom_heapVars, rule_format, OF imageI[OF a]])
    hence "a \<notin> set L"
      by (metis fresh_list_elem not_self_fresh)
    moreover
    have "atom a \<sharp> \<Gamma>" 
      by (rule Let(1)[unfolded fresh_star_def set_bn_to_atom_heapVars, rule_format, OF imageI[OF a]])
    hence "a \<notin> heapVars \<Gamma>"
      by (metis heapVars_not_fresh)
    ultimately
    have "a \<notin> fdom \<rho>" and "a \<notin> heapVars \<Gamma>"
      using 1 by auto
  }
  hence "set (bn as) \<sharp>* \<rho>"
    apply (subst fresh_star_def)
    apply (subst set_bn_to_atom_heapVars)
    apply (auto simp add: sharp_Env)
    done
  hence  [simp]: "set (bn as) \<sharp>* (\<lbrace>\<Gamma>\<rbrace>\<rho>)"
    using Let(1) by simp
  
  have hyp: "fdom \<rho> - heapVars (asToHeap as @ \<Gamma>) \<subseteq> set L"
    using 1 by auto

  have d1: "distinctVars (\<Gamma> @ asToHeap as)"
    using Let(1) Let(3) Let(7)
    apply (simp add: distinctVars_append)
    by (metis fresh_assn_distinct inf_commute)
  
  have f1: "atom ` heapVars (asToHeap as) \<sharp>* (\<Gamma>, \<rho>)"
    using Let(1) `_ \<sharp>* \<rho>`
    by (simp add: set_bn_to_atom_heapVars fresh_star_Pair)

  have "\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
  also have "\<dots> =  \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_merge[OF d1 f1]])
  also have "\<dots> =  \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule Let.hyps(5)[OF hyp])
  finally
  show ?case.

  case 2
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_less[OF d1 f1])
  also have "\<dots> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
    by (rule Let.hyps(6)[OF hyp])
  finally
  show ?case.
qed
end
