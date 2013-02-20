theory "Denotational-PropsUpd"
  imports "DenotationalUpd"
begin

subsubsection {* Continuity of the semantics *}

lemma ESem_cont':"Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and
  "\<And>e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> cont (ESem e)"
proof(nominal_induct e and as avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
case (Lam x e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. atom x \<sharp> Y i" and [simp]:"atom x \<sharp> Lub Y"  using Lam.hyps(1) Lam.prems(1)
    unfolding sharp_Env by auto
  have "cont (ESem e)" using Lam.hyps(2) by (rule contI, auto)
  have  "cont (\<lambda> \<rho>. Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
    by (intro cont2cont cont_compose[OF `cont (ESem e)`])
  from contE[OF this, OF Lam.prems(2)]
  show ?case
    by simp
next
case (App e v Y0 Y)
  have "cont (ESem e)" using App.hyps(1) by (rule contI, auto)
  thus ?case
    by (auto intro:contE[OF _ App.prems(2)])
next
case (Var v Y0 Y)
  have "cont (\<lambda> \<rho>. ESem (Var v) \<rho>)" by auto
  thus ?case
    by (rule contE[OF _ Var.prems(2)])    
next
case (Let as e Y0 Y)
  have fdoms[simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. set (bn as) \<sharp>* Y i" and [simp]: "set (bn as) \<sharp>* Lub Y"  using Let.hyps(1) Let.prems(1)
    unfolding sharp_star_Env by auto
  have unset: "\<And>i. fdom (Y i) \<inter> (heapVars (asToHeap as)) = {}"
    using Let by (metis fdoms disjoint_iff_not_equal sharp_star_Env)
  have conts: "\<forall>e\<in>snd ` set (asToHeap as). cont (ESem e)" using Let.hyps(2) by metis
  have "cont (ESem e)" using Let.hyps(3) by (rule contI, auto)

  have chain: "chain (\<lambda>i. HSem (asToHeap as) (Y i))"
    apply (rule chainI)
    apply (rule HSem_monofun''[OF Let.hyps(2)  chainE[OF `chain Y`]])
    by assumption

  have "(\<Squnion> i. HSem (asToHeap as) (Y i)) = HSem (asToHeap as) (Lub Y)"
    apply (rule HSem_cont''[OF Let.hyps(2) `chain Y`, symmetric])
    by assumption
  thus ?case
    apply simp
    by (metis Let(3) chain)
next
case ANil thus ?case by auto
next
case (ACons v e as Y0 Y)
  have "cont (ESem e)" using ACons.hyps(1) by (rule contI, auto)
  with ACons
  show ?case by auto
qed

interpretation has_cont_ESem ESem
  apply default
  using ESem_cont'[OF refl]
  by (rule contI)

lemmas ESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]

abbreviation HSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<rho>"

abbreviation HSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>fempty"

subsubsection {* Denotation of Substitution *}

lemma ESem_subst: "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow>  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow>  heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<rho> f! y)\<^esub>)
                    = heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) "
proof (nominal_induct e and as  avoiding: \<rho> x y rule:exp_assn.strong_induct)
case (Var var \<rho> x y) thus ?case by auto
next
case (App exp var \<rho> x y) thus ?case by auto
next
case (Let as exp \<rho> x y)
  from `set (bn as) \<sharp>* x` `set (bn as) \<sharp>* y` 
  have "x \<notin> heapVars (asToHeap as) " "y \<notin> heapVars (asToHeap as)"
    by (induct as rule: exp_assn.bn_inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)
  hence [simp]:"heapVars (asToHeap (as[x::a=y])) = heapVars (asToHeap as)" 
     by (induct as rule: exp_assn.bn_inducts, auto)

  have lookup_other: "\<And> \<rho> . (\<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>) f! y = \<rho> f! y"
    using `y \<notin> heapVars (asToHeap as)`
    by (auto simp add: the_lookup_HSem_other)

  have [simp]:"fdom \<rho> \<union> heapVars (asToHeap as) - {x} = fdom \<rho> \<union> heapVars (asToHeap as)"
    using `x \<notin> heapVars (asToHeap as)` `atom x \<sharp> \<rho>` by (auto simp add: sharp_Env)

  have *: "\<rho>(x f\<mapsto> \<rho> f! y)\<^bsub>[fdom (\<rho>(x f\<mapsto> \<rho> f! y)) \<union> heapVars (asToHeap as)]\<^esub>
        = (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (asToHeap as)]\<^esub>)(x f\<mapsto> \<rho> f! y)" (is "_ = ?\<rho>1'(x f\<mapsto> _)")
    apply (subst fmap_upd_expand)
    apply auto[3]
    done

  let ?b1 = "f\<emptyset>\<^bsub>[fdom (\<rho>(x f\<mapsto> \<rho> f! y)) \<union> heapVars (asToHeap as)]\<^esub>"
  let ?b2 = "f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars (asToHeap as[x::a=y])]\<^esub>"
  let ?\<rho>1 = "\<rho>(x f\<mapsto> \<rho> f! y)"
  let ?\<rho>2 = \<rho>
  let ?F1 = "\<lambda>\<rho>' . heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)"
  let ?F2 = "\<lambda>\<rho>' . heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)"
  let ?L = "fix_on' ?b1 (\<lambda> \<rho>'. ?\<rho>1 f++ ?F1 \<rho>')"
  let ?R = "fix_on' ?b2 (\<lambda> \<rho>'. ?\<rho>2 f++ ?F2 \<rho>')"

  have "\<lbrace>asToHeap as\<rbrace>(\<rho>(x f\<mapsto> \<rho> f! y)) \<sqsubseteq> (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>)(x f\<mapsto> \<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho> f! y)"
    (is "?L \<sqsubseteq> ?R( x f\<mapsto> ?R f! y)")
  proof (rule HSem_ind) back back back
  case goal1 show ?case by simp
  case goal2 show ?case by simp
  case (goal3 \<rho>')
    have "?\<rho>1 f++ ?F1 \<rho>' = (\<rho> f++ ?F1 \<rho>')(x f\<mapsto> \<rho> f! y)"
      apply (rule fmap_add_upd_swap)
      using `x \<notin> heapVars (asToHeap as)` by simp
    also
    have  "... \<sqsubseteq> (\<rho> f++ ?F2 ?R)( x f\<mapsto> \<rho> f! y)"
    proof (rule cont2monofunE[OF fmap_upd_cont[OF fmap_add_cont2 cont_const]])
      have "?F1 \<rho>' \<sqsubseteq> ?F1 (?R( x f\<mapsto> ?R f! y))"
        by (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      also
      have "... = ?F2 ?R"
        apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
        using `x \<notin> heapVars (asToHeap as)`  `atom x \<sharp> \<rho>` apply (simp add: sharp_Env)
        by rule
      finally
      show "?F1 \<rho>' \<sqsubseteq> ?F2 ?R".
    qed
    also have "... = ?R( x f\<mapsto> \<rho> f! y)"
      by (rule arg_cong[OF HSem_eq[symmetric]])
    also have "... = ?R( x f\<mapsto> ?R f! y)"
      using `y \<notin> heapVars (asToHeap as)` by (simp add: the_lookup_HSem_other)
    finally
    show "?\<rho>1 f++ ?F1 \<rho>' \<sqsubseteq> ?R( x f\<mapsto> ?R f! y)".
  qed
  also
  have "?R (x f\<mapsto> ?R f! y) \<sqsubseteq> ?L"
  proof (rule HSem_ind) back 
  case goal1 show ?case by auto
  case goal2 show ?case
    using `y \<notin> heapVars (asToHeap as)` `x \<notin> heapVars (asToHeap as)`
    apply (auto intro!: fmap_upd_belowI simp  add: the_lookup_HSem_other)
    apply (cases "y \<in> fdom \<rho>")
    apply simp
    apply (simp add: lookup_not_fdom)
    done
  case (goal3 \<rho>')
    have "(?\<rho>2 f++ ?F2 \<rho>') (x f\<mapsto> (?\<rho>2 f++ ?F2 \<rho>') f! y) = (?\<rho>2 f++ ?F2 \<rho>')(x f\<mapsto> \<rho> f! y)"
      using `y \<notin> heapVars (asToHeap as)` by simp
    also
    have "... = (?\<rho>1 f++ ?F2 \<rho>')"
      apply (rule fmap_add_upd_swap[symmetric])
      using `x \<notin> heapVars (asToHeap as)` by simp
    also
    have "... = ?\<rho>1 f++ ?F1 (\<rho>'(x f\<mapsto> \<rho>' f! y))"
      apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
      using `atom x \<sharp> \<rho>` `x \<notin> heapVars (asToHeap as)` goal3(1) apply (simp add: sharp_Env)
      by rule
    also
    have  "... \<sqsubseteq> ?\<rho>1 f++ ?F1 ?L"
      by (rule cont2monofunE[OF fmap_add_cont2cont[OF cont_const cont2cont_heapToEnv[OF ESem_cont]]  `\<rho>'(x f\<mapsto> \<rho>' f! y) \<sqsubseteq> ?L`])
    also
    have  "... = ?L"
      by (rule HSem_eq[symmetric])
    finally
    show "(?\<rho>2 f++ ?F2 \<rho>') (x f\<mapsto> (?\<rho>2 f++ ?F2 \<rho>') f! y) \<sqsubseteq> ?L".
  qed
  finally
  show ?case
    using Let
    by (auto simp add: fresh_star_Pair fresh_at_base)[1]
next
case (Lam var exp \<rho> x' y) thus ?case
  apply (auto simp add: fresh_star_Pair pure_fresh)
  apply (subst fmap_upd_twist)
  apply (auto)[1]
  apply (rule cfun_eqI) 
  apply (erule_tac x = "x'" in meta_allE)
  apply (erule_tac x = "y" in meta_allE)
  apply (erule_tac x = "\<rho>(var f\<mapsto> x)" in meta_allE)
  apply (auto simp add: pure_fresh fresh_at_base)[1]
  done
next
case (ANil \<rho> x y) thus ?case by auto
next
case(ACons var exp as \<rho> x y)  thus ?case by auto
qed

subsubsection {* The semantics ignores fresh variables *}

lemma ESem_ignores_fresh:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<rho>2\<^esub>"
  and
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* as \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>) = heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>)"
proof (nominal_induct e and as avoiding: \<rho>1 \<rho>2 rule:exp_assn.strong_induct)
case (Var x \<rho>1 \<rho>2)
  show ?case
  proof(cases "x \<in> fdom \<rho>1")
  case True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    with Var(2)
    have "x \<notin> fdom \<rho>2" by (metis Diff_iff exp_assn.fresh(1) fresh_star_def imageI not_self_fresh)
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
next
case (App e x \<rho>1 \<rho>2)
  from App(3)
  have "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e"
    by (auto simp add: fresh_star_def)
  note hyps = App.hyps[OF App.prems(1) this]
  moreover
  have "\<rho>1 f! x = \<rho>2 f! x"
  proof(cases "x \<in> fdom \<rho>1")
  case True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    with App(3)
    have "x \<notin> fdom \<rho>2"
      by (metis Diff_iff exp_assn.fresh(2) fresh_star_def imageI not_self_fresh)
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
  ultimately
  show ?case
    by simp
next
case (Let as e \<rho>1 \<rho>2)
  have "fdom \<rho>1 \<subseteq> fdom \<rho>2" by (metis Let(5) fmap_less_fdom)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<lbrace>asToHeap as\<rbrace>\<rho>2"
  proof (rule parallel_HSem_ind)
  case goal1 show ?case by simp
  case goal2
    show ?case
      apply (rule fmap_bottom_less)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` by auto
  case (goal3 \<rho>1' \<rho>2')[simp]
    have prem: "atom ` (fdom \<rho>2' - fdom \<rho>1') \<sharp>* as"
      using Let(6) Let(1) Let(2)
      apply (auto simp add: sharp_star_Env fresh_star_def)
      by (metis Diff_iff sharp_Env)

    show "\<rho>1 f++ heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1'\<^esub>) \<le> \<rho>2 f++ heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2'\<^esub>) "
    proof(rule fmap_less_eqI)
    case goal1
      show ?case using `fdom \<rho>1 \<subseteq> fdom \<rho>2` by auto
    next
    case (goal2 x)
      thus ?case
      apply (cases "x \<in> heapVars (asToHeap as)")
      apply (simp add: Let(3)[OF goal3(3) prem])
      apply (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2`])
      done
    qed
  qed
  moreover
  have "atom ` (fdom (\<lbrace>asToHeap as\<rbrace>\<rho>2) - fdom (\<lbrace>asToHeap as\<rbrace>\<rho>1)) \<sharp>* e "
    using Let(6) Let(1) Let(2)
    apply (auto simp add: sharp_star_Env fresh_star_def)
    by (metis Diff_iff sharp_Env)
  ultimately
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>1\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>2\<^esub>"
    apply (rule Let.hyps(4))
    done
  thus "\<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
    using Let.hyps(1,2) by simp
next
case (Lam x e \<rho>1 \<rho>2)
  { fix v
    have "\<rho>1(x f\<mapsto> v) \<le> \<rho>2(x f\<mapsto> v)"
      apply (rule fmap_less_eqI)
      using fmap_less_fdom[OF Lam(4)] apply auto[1]
      apply (case_tac "xa = x")
      by (auto simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2`])
    moreover
    have "atom ` (fdom (\<rho>2(x f\<mapsto> v)) - fdom (\<rho>1(x f\<mapsto> v))) \<sharp>* e"
      using Lam(5)
      by (auto simp add: fresh_star_def)
    ultimately
    have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1(x f\<mapsto> v)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2(x f\<mapsto> v)\<^esub>"
      by (rule Lam(3))
  }
  thus "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
    using Lam(1,2)
    by simp
next
case ANil
  thus ?case by simp
next
case (ACons x e as \<rho>1 \<rho>2)
  from ACons(4)
  have prem1: "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e" and  prem2: "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* as"
    by (auto simp add: fresh_star_def)
  from ACons.hyps(1)[OF `\<rho>1 \<le> \<rho>2` prem1] ACons.hyps(2)[OF `\<rho>1 \<le> \<rho>2` prem2]
  show ?case by simp
qed

subsubsection {* Binding more variables increases knowledge *}

lemma HSem_subset_below:
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)" 
  shows "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
proof (rule HSem_ind) back
case goal1 show ?case by (auto intro!: adm_is_adm_on adm_subst[OF fmap_expand_cont])
next
case goal2 show ?case by (auto simp add: to_bot_fmap_def)
next
case (goal3 x)
  from fresh
  have "heapVars \<Gamma> \<inter> (fdom \<rho> \<union> heapVars \<Delta>) = {}"
    by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  hence fdoms: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
    by auto
  {
    fix v e
    assume "e \<in> snd` set \<Delta>"
    from fresh_star_heap_expr'[OF _ this]
    have fresh_e: "atom ` heapVars \<Gamma> \<sharp>* e"
      by (metis fresh fresh_star_Pair)
    have "\<lbrakk> e \<rbrakk>\<^bsub>x\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>x\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub>\<^esub>"
      apply (rule ESem_ignores_fresh)
      apply (rule less_fmap_expand)
        using `fdom x = _` apply auto[2]
      apply (simp add: `fdom x = _` fdoms)
      apply (rule fresh_e)
      done
    with goal3(2)
    have "\<lbrakk> e \<rbrakk>\<^bsub>x\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (metis cont2monofunE[OF ESem_cont])
  } note e_less = this

  show ?case
  proof (rule fmap_expand_belowI)
  case goal1 show ?case by auto
  case (goal2 y)
    show ?case
    proof (cases "y \<in> heapVars \<Delta>")
    case True
      thus ?thesis
        by (subst HSem_eq, auto intro: e_less[OF the_map_of_snd] simp add: lookupHeapToEnv map_add_dom_app_simps)
    next
    case False
      moreover
      with goal2(1) `_ = {}`
      have "y \<notin> heapVars \<Gamma>" by auto
      ultimately
      show ?thesis
        by (subst HSem_eq, simp)
    qed
  qed
qed

subsubsection {* Additional, fresh bindings in one or two steps *}

lemma HSem_merge:
  assumes distinct1: "distinctVars (\<Delta> @ \<Gamma>)"
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
  shows "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
proof(rule below_antisym)
  from distinct1
  have distinct2: "distinctVars (\<Gamma> @ \<Delta>)"
    by (auto simp add: distinctVars_append)

  from fresh
  have Gamma_fresh: "heapVars \<Gamma> \<inter> (fdom \<rho> \<union> heapVars \<Delta>) = {}"
    by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  hence fdoms: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
    by auto

  show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof (rule HSem_ind) back
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case goal2 show ?case by (auto simp add: to_bot_fmap_def)
  next
  case (goal3 \<rho>')
    show ?case
    proof (rule fmap_add_belowI)
    case goal1 show ?case by auto
    case (goal2 x)
      moreover
      have "\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>'\<^esub> \<sqsubseteq> \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>\<^esub>"
        by (rule cont2monofunE[OF ESem_cont `\<rho>' \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>`])
      ultimately
      show ?case
        by (subst HSem_eq, simp add: lookupHeapToEnv map_add_dom_app_simps dom_map_of_conv_image_fst)
      next
    case (goal3 x)
      moreover
      have "\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
        by (rule HSem_reorder[OF distinct1 distinct2], auto)
      ultimately
      show ?case
        using fmap_belowE[OF HSem_subset_below[OF fresh], of x]
        by simp
    qed
  qed
  
  show "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
  proof (rule HSem_ind[where h = "\<Gamma>@\<Delta>"])
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case goal2 show ?case by (auto simp add: to_bot_fmap_def)
  next
  case (goal3 \<rho>')
    note `\<rho>' \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>`
    show ?case
    proof (rule fmap_add_belowI)
    case goal1 show ?case by auto
    case (goal2 x)
      hence "x \<in> heapVars \<Gamma> \<or> (x \<notin> heapVars \<Gamma> \<and> x \<in> heapVars \<Delta>)" by auto      
      thus ?case
      proof
        assume "x \<in> heapVars \<Gamma> "
        moreover
        have "\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>'\<^esub> \<sqsubseteq> \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
          by (rule cont2monofunE[OF ESem_cont `\<rho>' \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>`])
        ultimately
        show ?thesis
          by (subst HSem_eq, simp add: lookupHeapToEnv map_add_dom_app_simps dom_map_of_conv_image_fst)
      next
        assume "x \<notin> heapVars \<Gamma> \<and> x \<in> heapVars \<Delta>"
        moreover
        have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<rho>'\<^esub> \<sqsubseteq> \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
          by (rule cont2monofunE[OF ESem_cont `\<rho>' \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>`])
        moreover
        have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
          apply (rule ESem_ignores_fresh[symmetric])
          apply (rule HSem_disjoint_less)
            using Gamma_fresh apply auto[1]
          apply (simp add: fdoms)
          by (metis calculation(1) fresh fresh_star_Pair fresh_star_heap_expr' the_map_of_snd)
        ultimately
        show ?thesis
          apply (subst HSem_eq[where h = \<Gamma>])
          apply (subst HSem_eq[where h = \<Delta>])
          apply (simp add: lookupHeapToEnv map_add_dom_app_simps dom_map_of_conv_image_fst)
          done
      qed  
    next
    case (goal3 y)
      moreover
        hence [simp]: "y \<notin> heapVars \<Gamma>" "y \<notin> heapVars \<Delta>" by auto
      ultimately
      show ?case
        apply (subst HSem_eq[where h = \<Gamma>])
        apply (subst HSem_eq[where h = \<Delta>])
        by simp
    qed
  qed
qed

subsubsection {* The semantics of let only adds new bindings *}

lemma HSem_less:
  assumes distinct1: "distinctVars (\<Delta> @ \<Gamma>)"
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
  shows "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
proof-
  have "heapVars \<Gamma> \<inter> fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) = {}"
    using fresh
    by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  hence "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    by (rule HSem_disjoint_less)
  also have "\<dots> =  \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
    by (rule HSem_merge[OF assms])
  finally
  show ?thesis.
qed
end
