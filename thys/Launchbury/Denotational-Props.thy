theory "Denotational-Props"
  imports "Denotational"
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
  have cont: "cont (ESem e)" using Let.hyps(3) by (rule contI, auto)
  have cond: "HSem_cond'' (asToHeap as) (\<Squnion> i. Y i)" by (rule disjoint_is_HSem_cond'[OF unset[unfolded fdoms] conts])
  have conds: "\<And>i. HSem_cond'' (asToHeap as) (Y i)" by (rule disjoint_is_HSem_cond'[OF unset conts])

  have chain: "chain (\<lambda>i. HSem (asToHeap as) (Y i))"
    apply (rule chainI)
    apply (rule HSem_monofun''[OF Let.hyps(2) conds conds chainE[OF `chain Y`]])
    by assumption

  have "(\<Squnion> i. HSem (asToHeap as) (Y i)) = HSem (asToHeap as) (Lub Y)"
    apply (rule HSem_cont''[OF Let.hyps(2) cond conds `chain Y`, symmetric])
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

(* TODO: Where to put this *)
  
lemma fresh_fmap_upd_lookup[simp]: "S \<sharp>* (\<rho>::Env) \<Longrightarrow> S \<sharp>* x \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> \<rho> f! y)"
  by (auto simp add: fresh_append fresh_star_fmap_upd_eq intro: eqvt_fresh_star_cong2[where f = fmap_delete, OF fmap_delete_eqvt])

lemma compatible_insert:
  assumes [simp]: "S = insert x (fdom \<rho>1)"
  and "x \<notin> fdom \<rho>1"
  and "x \<notin> fdom \<rho>2"
  and compat: "compatible \<rho>1 (\<rho>2\<^bsub>[fdom \<rho>1]\<^esub>)"  
  shows "compatible (\<rho>1(x f\<mapsto> y)) (\<rho>2\<^bsub>[S]\<^esub>)"
proof(rule compatible_fmapI)
case (goal1 z)
  show ?case
  apply(cases "z = x")
  using `x \<notin> fdom \<rho>2` apply simp
  using goal1(1) the_lookup_compatible[OF compat, of z]
  apply (cases "z \<in> fdom \<rho>2")
  by auto
next
case goal2 with assms(1) show ?case by simp
qed
    
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
  have "x \<notin> heapVars (asToHeap as)" "y \<notin> heapVars (asToHeap as) "
    by (induct as rule: exp_assn.bn_inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)
  hence [simp]:"heapVars (asToHeap (as[x::a=y])) = heapVars (asToHeap as)" 
     by (induct as rule: exp_assn.bn_inducts, auto)

  have cond1: "HSem_cond' (asToHeap as) (\<rho>(x f\<mapsto> \<rho> f! y))"
      (is "fix_join_cond ?\<rho>1 ?F1")
    apply (rule disjoint_is_HSem_cond)
    apply (auto simp add:  `x \<notin> heapVars (asToHeap as)`)
    by (metis Let(1) sharp_star_Env)
  have cond2: "HSem_cond' (asToHeap as[x::a=y]) \<rho>"
      (is "fix_join_cond ?\<rho>2 ?F2")
    apply (rule disjoint_is_HSem_cond)
    apply (auto simp add:  `x \<notin> heapVars (asToHeap as)`)
    by (metis Let(1) sharp_star_Env)

  have lookup_other: "\<And> \<rho> . \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho> f! y = \<rho> f! y"
    using `y \<notin> heapVars (asToHeap as)`
    by (auto simp add: the_lookup_HSem_other)

  have [simp]:"fdom \<rho> \<union> heapVars (asToHeap as) - {x} = fdom \<rho> \<union> heapVars (asToHeap as)"
    using `x \<notin> heapVars (asToHeap as)` `atom x \<sharp> \<rho>` by (auto simp add: sharp_Env)

  have *: "\<rho>(x f\<mapsto> \<rho> f! y)\<^bsub>[fdom (\<rho>(x f\<mapsto> \<rho> f! y)) \<union> heapVars (asToHeap as)]\<^esub>
        = (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (asToHeap as)]\<^esub>)(x f\<mapsto> \<rho> f! y)" (is "_ = ?\<rho>1'(x f\<mapsto> _)")
    apply (subst fmap_upd_expand)
    apply auto[3]
    done

  have "fix_on (fix_join_compat ?\<rho>1 ?F1) (\<lambda> \<rho>'. ?\<rho>1 \<squnion> ?F1 \<rho>') \<sqsubseteq>
       (fix_on (fix_join_compat ?\<rho>2 ?F2) (\<lambda> \<rho>'. ?\<rho>2 \<squnion> ?F2 \<rho>')) ( x f\<mapsto> (fix_on (fix_join_compat ?\<rho>2 ?F2) (\<lambda> \<rho>'. ?\<rho>2 \<squnion> ?F2 \<rho>') f! y))"
    (is "?L \<sqsubseteq> ?R( x f\<mapsto> ?R f! y)")
  proof (rule fix_on_ind[OF fix_on_cond_fjc[OF cond1]])
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2
    show ?case
      apply (subst bottom_of_fjc)
      apply (subst to_bot_fmap_def)
      apply (rule fmap_bottom_below)
      apply (subst (2) fmap_upd_fdom)
      apply (subst fdom_fix_on[OF fix_on_cond_fjc[OF cond2]])
      apply (simp add: bottom_of_fjc to_bot_fmap_def)
      done
  case (goal3 \<rho>')
    let "?F1' \<rho>'" = "heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars (asToHeap as)]\<^esub>"

    have "?\<rho>1 \<squnion> ?F1 \<rho>' = ?\<rho>1'(x f\<mapsto> \<rho> f! y) \<squnion> ?F1 \<rho>'"
      by (subst *, rule)
    also
    have "\<dots> = (?\<rho>1' \<squnion> ?F1' \<rho>')(x f\<mapsto> \<rho> f! y)"
      apply (subst fmap_upd_join)
      using `atom x \<sharp> \<rho>` `x \<notin> heapVars (asToHeap as)` apply (auto simp add: sharp_Env)[3]
      using rho_F_compat_fjc[OF cond1 goal3(1)] apply (metis *)
      by auto
    also
    { have "?F1' \<rho>' \<sqsubseteq> ?F1' (?R( x f\<mapsto> ?R f! y))"
        by (rule cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] goal3(2)])
      also
      have "... = ?F2 ?R"
        apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
          using `atom x \<sharp> \<rho>` `x \<notin> heapVars (asToHeap as)` fdom_fix_on[OF fix_on_cond_fjc[OF cond2]]
          apply (simp add: sharp_Env bottom_of_fjc)
        by simp
      also note calculation     
    } 
    hence "... \<sqsubseteq> (?\<rho>2 \<squnion> ?F2 ?R)( x f\<mapsto> \<rho> f! y)"
      apply (rule cont2monofunE[OF
              fmap_upd_cont[OF cont_id cont_const]
              join_mono'[OF rho_F_compat_fjc[OF cond2 fix_on_there[OF fix_on_cond_fjc[OF cond2]]]]
              , rotated])
      apply simp
    done
    also have "... = ?R( x f\<mapsto> \<rho> f! y)"
      by (rule arg_cong[OF fix_on_eq[OF fix_on_cond_fjc[OF cond2], symmetric]])
    also have "... = ?R( x f\<mapsto> ?R f! y)"
      by (subst lookup_other[of \<rho>, unfolded HSem_def'[OF cond2]], rule)
    finally show "?\<rho>1 \<squnion> ?F1 \<rho>' \<sqsubseteq> ?R( x f\<mapsto> ?R f! y)".
  qed
  also
  have "?R (x f\<mapsto> ?R f! y) \<sqsubseteq> ?L"
  proof (rule fix_on_ind[OF fix_on_cond_fjc[OF cond2]])
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2
    show ?case
      apply (subst fix_on_eq[OF fix_on_cond_fjc[OF cond1]])
      apply (subst bottom_of_fjc)
      apply (subst to_bot_fmap_def)
      apply (subst fdom_fmap_expand)
        apply simp
      
      apply (rule fmap_upd_belowI)
        apply (subst fdom_join[OF rho_F_compat_fjc[OF cond1 fix_on_there[OF fix_on_cond_fjc[OF cond1]]]])
        apply simp

      apply simp
      apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond1 fix_on_there[OF fix_on_cond_fjc[OF cond1]]]])
      apply (rule rev_below_trans[OF join_above1[OF the_lookup_compatible[OF rho_F_compat_fjc[OF cond1 fix_on_there[OF fix_on_cond_fjc[OF cond1]]]]]])
      apply (cases "y \<in> fdom \<rho>")
      using  `y \<notin> heapVars (asToHeap as)` apply (auto simp add: bottom_of_fjc to_bot_fmap_def lookup_not_fdom)
      done
  case (goal3 \<rho>')
    let "?F1' \<rho>'" = "heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars (asToHeap as)]\<^esub>"
    let "?F2' \<rho>'" = "heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)\<^bsub>[insert x (fdom \<rho> \<union> heapVars (asToHeap as))]\<^esub>"
    have "fdom \<rho>' = fdom \<rho> \<union> heapVars (asToHeap as)"
      using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond2] goal3(1)] by simp

    have "(?\<rho>2 \<squnion> ?F2 \<rho>') (x f\<mapsto> (?\<rho>2 \<squnion> ?F2 \<rho>') f! y) = (?\<rho>2 \<squnion> ?F2 \<rho>')(x f\<mapsto> \<rho> f! y)"
      apply (rule arg_cong) back
      apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond2 goal3(1)]])
      apply (case_tac "y \<in> fdom \<rho>")
      using `y \<notin> heapVars (asToHeap as)`
      by (auto simp add: sharp_Env lookup_not_fdom)
    also
    have "... = (?\<rho>1'(x f\<mapsto> \<rho> f! y) \<squnion> ?F2' \<rho>')"
      apply (subst fmap_upd_join)
      using `atom x \<sharp> \<rho>` `x \<notin> heapVars (asToHeap as)` apply (auto simp add: sharp_Env)[3]
      apply (rule compatible_insert)
        using `atom x \<sharp> \<rho>` `x \<notin> heapVars (asToHeap as)` apply (auto simp add: sharp_Env)[3]
      apply simp
      apply (rule rho_F_compat_fjc[OF cond2 goal3(1), simplified])
      apply simp
      done
    also
    have "... = ?\<rho>1 \<squnion> ?F2' \<rho>'"
      by (subst *, rule)
    also
    have "... = ?\<rho>1 \<squnion> ?F1 (\<rho>'(x f\<mapsto> \<rho>' f! y))"
      apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
        using `atom x \<sharp> \<rho>` `fdom \<rho>' = _` `x \<notin> heapVars (asToHeap as)` fdom_fix_on[OF fix_on_cond_fjc[OF cond2]]
        apply (simp add: sharp_Env bottom_of_fjc)
      by simp
    also
    from `\<rho>'(x f\<mapsto> \<rho>' f! y) \<sqsubseteq> ?L`
    have  "... \<sqsubseteq> ?L"
      unfolding bottom_of_fjc
      by (rule join_fjc[OF rho_fjc[OF cond1] F_pres_compat''[OF cond1], unfolded fjc_iff])
    finally
    show "(?\<rho>2 \<squnion> ?F2 \<rho>') (x f\<mapsto> (?\<rho>2 \<squnion> ?F2 \<rho>') f! y) \<sqsubseteq> ?L".
  qed
  finally
  have "\<lbrace>asToHeap as\<rbrace>(\<rho>(x f\<mapsto> \<rho> f! y)) = (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>)(x f\<mapsto> \<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho> f! y)"
    unfolding  HSem_def'[OF cond1] subst HSem_def'[OF cond2] .
  with Let
  show ?case 
  by (auto simp add: fresh_star_Pair fresh_at_base)
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

(* TODO move where? *)

lemma fmap_expand_compatible:
  assumes [simp]: "finite S"
  assumes compat:"compatible \<rho>1 \<rho>2"
  shows "compatible (\<rho>1\<^bsub>[S]\<^esub>) (\<rho>2\<^bsub>[S]\<^esub>)"
  apply (rule compatible_fmapI)
  apply (case_tac "x \<in> fdom \<rho>1")
  apply (auto simp add: fdom_compatible[OF compat] intro: the_lookup_compatible[OF compat])
  done


lemma fmap_expand_join:
  assumes [simp]: "finite S"
  assumes compat:"compatible \<rho>1 \<rho>2"
  shows "(\<rho>1 \<squnion> \<rho>2)\<^bsub>[S]\<^esub> = \<rho>1\<^bsub>[S]\<^esub> \<squnion> \<rho>2\<^bsub>[S]\<^esub>"
proof-
  have [simp]: "fdom \<rho>2 = fdom \<rho>1" by (metis fdom_compatible[OF compat])
  have [simp]: "fdom (\<rho>1 \<squnion> \<rho>2) = fdom \<rho>1" by (rule fdom_join[OF compat])
  have compat2: "compatible (\<rho>1\<^bsub>[S]\<^esub>) (\<rho>2\<^bsub>[S]\<^esub>)"
    by (rule fmap_expand_compatible[OF assms])
  show ?thesis
    apply (rule fmap_eqI)
    apply (simp add: fdom_join[OF compat2])
    apply (case_tac "x \<in> fdom \<rho>1")
    by (auto simp add: the_lookup_join[OF compat2] the_lookup_join[OF compat])
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
    have "x \<notin> fdom \<rho>2"
    proof
      assume "x \<in> fdom \<rho>2"
      hence "x \<in> fdom \<rho>2 - fdom \<rho>1" using False by simp
      thus False
        using Var(2)
        apply (simp add: fresh_star_def)
        apply (erule ballE[where x = "x"])
        by auto
    qed
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
    have "x \<notin> fdom \<rho>2"
    proof
      assume "x \<in> fdom \<rho>2"
      hence "x \<in> fdom \<rho>2 - fdom \<rho>1" using False by simp
      thus False
        using App(3)
        apply (simp add: fresh_star_def)
        apply (erule ballE[where x = "x"])
        by auto
    qed
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
  ultimately
  show ?case
    by simp
next
case (Let as e \<rho>1 \<rho>2)
  have cond1: "HSem_cond' (asToHeap as) \<rho>1"
      (is "fix_join_cond ?\<rho>1 ?F1")
    apply (rule disjoint_is_HSem_cond)
    using Let(1)
    by (auto simp add: sharp_star_Env)
  have cond2: "HSem_cond' (asToHeap as) \<rho>2"
      (is "fix_join_cond ?\<rho>2 ?F2")
    apply (rule disjoint_is_HSem_cond)
    using Let(2)
    by (auto simp add: sharp_star_Env)

  have "fdom \<rho>1 \<subseteq> fdom \<rho>2" by (metis Let(5) fmap_less_fdom)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<lbrace>asToHeap as\<rbrace>\<rho>2"
  proof (rule parallel_HSem_ind[OF cond1 cond2])
  case goal1 show ?case by (rule adm_is_adm_on, simp)
  case goal2
    show ?case
      apply (rule fmap_bottom_less)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` apply auto[2]
      done
  case (goal3 \<rho>1' \<rho>2')
    have [simp]:"fdom \<rho>1' = fdom \<rho>1 \<union> heapVars (asToHeap as)" and [simp]:"fdom \<rho>2' = fdom \<rho>2 \<union> heapVars (asToHeap as)"
      using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond1] goal3(1)]
      using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond2] goal3(2)]
      by simp+  
    note compat1 = rho_F_compat_fjc[OF cond1 goal3(1)]
    note compat2 = rho_F_compat_fjc[OF cond2 goal3(2)]

    have prem: "atom ` (fdom \<rho>2' - fdom \<rho>1') \<sharp>* as"
      using Let(6) Let(1) Let(2)
      apply (auto simp add: sharp_star_Env fresh_star_def)
      by (metis Diff_iff sharp_Env)

    show "?\<rho>1 \<squnion> ?F1 \<rho>1' \<le> ?\<rho>2 \<squnion> ?F2 \<rho>2'"
    proof(rule fmap_less_eqI)
    case goal1
      show ?case
        apply (subst fdom_join[OF compat1])
        apply (subst fdom_join[OF compat2])
        using `fdom \<rho>1 \<subseteq> fdom \<rho>2`
        by auto
    next
    case (goal2 x)
      hence dom: "x \<in> fdom \<rho>1 \<union> heapVars (asToHeap as)"      
        apply (subst (asm) fdom_join[OF compat1])
        by simp
      hence dom2: "x \<in> fdom \<rho>2 \<union> heapVars (asToHeap as)"
        by (auto intro: set_mp[OF `fdom \<rho>1 \<subseteq> fdom \<rho>2`])

      have "lookup ?\<rho>1 x = lookup ?\<rho>2 x"
      proof (cases "x \<in> fdom \<rho>1")
      case True
        hence "x \<in> fdom \<rho>2" by (rule set_mp[OF `fdom \<rho>1 \<subseteq> fdom \<rho>2`])
        with True show ?thesis
          by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
      next
      case False
        hence "x \<notin> fdom \<rho>2"
          using Let(2) dom 
          by (auto simp add: sharp_star_Env)
        with False dom show ?thesis by (simp add: lookup_not_fdom)
      qed
      moreover
      have "lookup (?F1 \<rho>1') x = lookup (?F2 \<rho>2') x"
      proof (cases "x \<in> heapVars (asToHeap as)")
      case True
        thus ?thesis
          by (simp add: Let(3)[OF goal3(3) prem])
      next
      case False
        thus ?thesis
          using dom dom2 by simp
      qed
      ultimately
      show ?case
        apply (subst the_lookup_join[OF compat1])
        apply (subst the_lookup_join[OF compat2])
        by simp
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

lemma HSem_add_fresh:
  assumes cond1: "HSem_cond' \<Gamma> \<rho>"
  assumes cond2: "HSem_cond' ((x,e) # \<Gamma>) \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>)"
  shows  "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
proof(rule HSem_add_fresh[OF assms])
case (goal1 e \<rho>')
  assume "e \<in> snd ` set \<Gamma>"
  hence "atom x \<sharp> e"
    apply auto
    by (metis fresh fresh_PairD(2) fresh_list_elem)

  assume "fdom \<rho>' = fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)"
  hence [simp]:"fdom \<rho>' - fdom \<rho>' \<inter> (fdom \<rho>' - {x}) = {x}" by auto

  show ?case
    apply (rule ESem_ignores_fresh[symmetric, OF fmap_restr_less])
    apply (simp add: fresh_star_def)
    using `atom x \<sharp> e`.
qed

lemma ESem_add_fresh:
  assumes cond1: "HSem_cond' \<Gamma> \<rho>"
  assumes cond2: "HSem_cond' ((x,e') # \<Gamma>) \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>, e)"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
proof(rule ESem_ignores_fresh[symmetric])
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) "
    apply (rule HSem_add_fresh[OF assms(1,2), symmetric])
    using fresh by (simp add: fresh_Pair)
  thus "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>"
    by (auto simp add: fmap_less_restrict)

  have "(insert x (fdom \<rho> \<union> heapVars \<Gamma>) - (fdom \<rho> \<union> heapVars \<Gamma>)) = {x}"
    using fresh
    apply (auto simp add: fresh_Pair sharp_Env)
    by (metis heapVars_not_fresh)
  thus "atom ` (fdom (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) - fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>)) \<sharp>* e"
    using fresh
    by (simp add: fresh_star_def fresh_Pair)
qed

subsubsection {* Replacing subexpressions by variables *}

lemma HSem_subst_var_app:
  assumes cond1: "HSem_cond' ((x, App (Var n) y) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, App e y) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes cond1: "HSem_cond' ((x, Var n) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, e) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
  finally
  show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

subsubsection {* Binding more variables increases knowledge *}

lemma HSem_subset_below:
  assumes cond2: "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)" 
  shows "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
proof (rule HSem_ind) back
case goal1 show ?case by (auto intro!: adm_is_adm_on adm_subst[OF fmap_expand_cont])
next
case goal2 show ?case by (auto simp add: to_bot_fmap_def)
next
show rho: "(\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> "
  apply (subst fmap_expand_idem)
  apply auto[3]
  using HSem_refines[OF cond2]
  by (auto simp add: sup.assoc)

  from fresh
  have "heapVars \<Gamma> \<inter> (fdom \<rho> \<union> heapVars \<Delta>) = {}"
    by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  hence fdoms: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
    by auto

case (goal3 x)
  note cond1 = goal3(1)
  have  "fdom x = fdom \<rho> \<union> heapVars \<Delta>"
    using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond1] goal3(2)]
    by simp
  {
    fix v e
    assume "e \<in> snd` set \<Delta>"
    thm fresh_star_heap_expr'
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
    with goal3(3)
    have "\<lbrakk> e \<rbrakk>\<^bsub>x\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (metis cont2monofunE[OF ESem_cont])
  } note e_less = this

  note compat = rho_F_compat_fjc[OF cond1 goal3(2)]
  note compat2 = rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]
  show ?case
    apply (subst fmap_expand_join[OF _ compat], simp)
    apply (rule join_below[OF fmap_expand_compatible[OF _ compat] rho], simp)
    apply (subst fmap_expand_idem)
      apply auto[3]
    apply (rule fmap_expand_belowI)
      apply auto[1]
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF compat2])
    apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat2]]])
    apply (subst lookup_fmap_expand1)
      apply auto[3]
    apply simp
    apply (subst lookupHeapToEnv, assumption)
    apply (subst lookupHeapToEnv)
      apply auto[1]
    apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
    apply (rule e_less)
    by (metis the_map_of_snd)
qed

subsubsection {* Additional, fresh bindings in one or two steps *}

lemma HSem_merge:
  assumes distinct1: "distinctVars (\<Delta> @ \<Gamma>)"
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
  assumes rho_fresh: "fdom \<rho> \<inter> heapVars (\<Gamma> @ \<Delta>) = {}"
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

  have cond1: "HSem_cond' \<Gamma> (\<lbrace>\<Delta>\<rbrace>\<rho>)"
    apply (rule disjoint_is_HSem_cond)
    using Gamma_fresh by auto
  have cond2: "HSem_cond' (\<Gamma>@\<Delta>) \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto
  have cond2': "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto
  have cond3: "HSem_cond' \<Delta> \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto

  show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof (rule HSem_ind) back
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case goal2 show ?case by (auto simp add: to_bot_fmap_def)
  next
  have "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_subset_below[OF cond2' fresh])
  also have "\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
    by (rule HSem_reorder[OF distinct1 distinct2], auto)
  finally
  show Delta_rho: "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
    by simp

  case (goal3 \<rho>')
    note compat = rho_F_compat_fjc[OF cond1 goal3(2)]
    note compat2 = rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]

    have "heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>\<^esub>)\<^bsub>[fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho> "
    proof (rule fmap_expand_belowI)
    case goal1 thus ?case by auto
    case (goal2 x)
      hence x:"x \<in> heapVars \<Gamma>" by auto
      thus ?case
        apply (subst lookupHeapToEnv, assumption)
        apply (subst (2) HSem_eq[OF cond2])
        apply (subst the_lookup_join[OF compat2])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat2]]])
        apply (subst lookup_fmap_expand1)
          using x apply auto[3]
        apply (subst lookupHeapToEnv)
          apply auto[1]
        apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
        done
    qed       
    thus ?case
      by (rule join_below[OF compat Delta_rho 
          below_trans[OF cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] goal3(3)]]])
  qed

  show "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
  proof (rule HSem_ind) back back
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case goal2 show ?case by (auto simp add: to_bot_fmap_def)
  next
  have "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub> = (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub>"
    by (rule fmap_expand_idem[symmetric], auto)
  also have "... \<sqsubseteq> (\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub>"
    by (rule cont2monofunE[OF fmap_expand_cont HSem_refines[OF cond3]])
  also have "... = (\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> heapVars (\<Gamma>)]\<^esub>"
    apply (rule arg_cong) back
    by auto
  also have "... \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    by (rule HSem_refines[OF cond1])
  finally
  show rho: "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> ".

  case (goal3 \<rho>')
    note compat = rho_F_compat_fjc[OF cond2 goal3(2)]
    note compat2 = rho_F_compat_fjc[OF cond1 HSem_there[OF cond1]]
    note compat3 = rho_F_compat_fjc[OF cond3 HSem_there[OF cond3]]

    have "heapToEnv (\<Gamma> @ \<Delta>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    proof (rule fmap_expand_belowI)
    case goal1 thus ?case by auto
    case (goal2 x)
      hence "x \<in> heapVars \<Gamma> \<or> (x \<notin> heapVars \<Gamma> \<and> x \<in> heapVars \<Delta>)" by auto      
      thus ?case
      proof
        assume x: "x \<in> heapVars \<Gamma>"
        thus ?thesis
        apply (subst lookupHeapToEnv)
          apply auto[1]
        apply (subst (2) HSem_eq[OF cond1])
        apply (subst the_lookup_join[OF compat2])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat2]]])
        apply (subst lookup_fmap_expand1)
          using x apply auto[3]
        apply (subst lookupHeapToEnv, assumption)
        apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
        done
      next
        assume x: "x \<notin> heapVars \<Gamma> \<and> x \<in> heapVars \<Delta>"
        hence [simp]:"x \<notin> heapVars \<Gamma>" and  "x \<in> heapVars \<Delta>" by auto
        from this(2)
        show ?thesis
        apply (subst lookupHeapToEnv)
          apply auto[1]
        apply (subst the_lookup_HSem_other)
          apply simp
        apply (subst (2) HSem_eq[OF cond3])
        apply (subst the_lookup_join[OF compat3])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat3]]])
        apply (subst lookup_fmap_expand1)
          using x apply auto[3]
        apply (subst lookupHeapToEnv, assumption)
        apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
        apply (rule eq_imp_below)
        apply (rule ESem_ignores_fresh[symmetric])
        apply (rule HSem_disjoint_less)
          using Gamma_fresh apply auto[1]
        apply (simp add: fdoms)
        apply (erule fresh_star_heap_expr'[OF _ the_map_of_snd, rotated])
        by (metis fresh fresh_star_Pair)
      qed  
    qed
    thus ?case
      by (rule join_below[OF compat rho 
          below_trans[OF cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] goal3(3)]]])
  qed
qed

subsubsection {* The semantics of let only adds new bindings *}

text {*
The following lemma is not as general as possible and specialized to @{text "\<rho> = fempty"}, as that is
the only case required later on, and easier to prove.
*}

lemma HSem_unfold_let:
  assumes cond1: "HSem_cond' ((x, Let as body) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, body) # asToHeap as @ \<Gamma>) \<rho>"
  assumes cond3: "HSem_cond' (asToHeap as @ ((x, body) # \<Gamma>)) \<rho>"
  assumes distinct1: "distinctVars (asToHeap as)"
  assumes distinct2: "distinctVars ((x, body) # \<Gamma>)"
  assumes fresh: "set (bn as) \<sharp>* (x, Let as body, \<Gamma>, \<rho>)"
  assumes too_lazy_to_do_it_for_more_than_fempty: "\<rho> = fempty"
  shows "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho> \<le> \<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>"
proof (rule iffD2[OF fmap_less_restrict])
  from fresh
  have fresh_Gamma: "atom ` heapVars (asToHeap as) \<sharp>* \<Gamma>"
    by (metis fresh_star_Pair set_bn_to_atom_heapVars)

  from fresh
  have "set (bn as) \<sharp>* ((x, Let as body) # \<Gamma>)"
    by (auto simp add: fresh_star_def fresh_Pair fresh_Cons)
  note notInAs = fresh_assn_distinct[OF this]

  from fresh
  have notInRho: "heapVars (asToHeap as) \<inter> fdom \<rho> = {}"
    by (auto simp add: fresh_star_Pair sharp_star_Env)

  have disjoint: "heapVars (asToHeap as) \<inter> insert x (fdom \<rho> \<union> heapVars \<Gamma>) = {}"
    using notInAs notInRho
    by auto
  hence x_not_as: "x \<notin> heapVars (asToHeap as)"
    by auto

  {
    fix x' e
    assume "e \<in> snd ` set \<Gamma>"

    have simp1: " fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) \<inter> insert x (fdom \<rho> \<union> heapVars \<Gamma>) = insert x (fdom \<rho> \<union> heapVars \<Gamma>)"
      by auto

    have simp2: "fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) - insert x (fdom \<rho> \<union> heapVars \<Gamma>) = heapVars (asToHeap as)"
      using disjoint
      by auto

    have fresh_e: "atom ` heapVars (asToHeap as) \<sharp>* e"
      by (rule fresh_star_heap_expr'[OF fresh_Gamma `_ \<in> snd\` set \<Gamma>`])

    have "\<lbrakk> e \<rbrakk>\<^bsub>fmap_restr (insert x (fdom \<rho> \<union> heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
      apply (rule ESem_ignores_fresh[OF fmap_restr_less])
      apply (subst fdom_fmap_restr)
        apply simp
      apply (subst simp1)
      apply (subst simp2)
      apply (rule fresh_e)
      done
  } note Gamma_eq = this

case goal1
  have "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho> = fmap_restr (insert x (fdom \<rho> \<union> heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>)"
  proof(rule below_antisym)
    show below: "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> fmap_restr (insert x (fdom \<rho> \<union> heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>)"
    proof (rule HSem_ind'[OF cond1])
    case goal1 show ?case by (auto intro: adm_is_adm_on)
    case goal2 show ?case by (auto simp add: to_bot_fmap_def)
    case (goal3 \<rho>')
      have fdom: "fdom \<rho>' = insert x (fdom \<rho> \<union> heapVars \<Gamma>)"
        using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond1] goal3(1)]
        by simp

      hence [simp]: "set (bn as) \<sharp>* \<rho>'"
        using disjoint
        by (auto simp add: set_bn_to_atom_heapVars fresh_star_def sharp_Env)

      note compat1 = rho_F_compat_fjc[OF cond1 goal3(1)]
      note compat2 = rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]
      show ?case
      proof(rule fmap_belowI)
      case goal1 show ?case by (auto simp add: fdom_join[OF compat1, simplified])
      case (goal2 x')
        hence x': "x' \<in> insert x (fdom \<rho> \<union> heapVars \<Gamma>)"
          by (auto simp add: fdom_join[OF compat1, simplified])

        hence x'_not_as:"x' \<notin> heapVars (asToHeap as)"
          using disjoint
          by auto

        have "\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<rho>'\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>'\<^esub>" by simp
        also have "... \<sqsubseteq> \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(fmap_restr (insert x (fdom \<rho> \<union> heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>))\<^esub>"
          apply (rule cont2monofunE[OF ESem_cont])
          apply (rule HSem_mono[OF _ _ goal3(2)])
          apply (rule disjoint_is_HSem_cond)
          apply (subst fdom)
          using disjoint apply auto[1]
          apply (rule disjoint_is_HSem_cond)
          using disjoint apply auto[1]
          done
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(fmap_restr (insert x (fdom \<rho> \<union> heapVars \<Gamma>)) (\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<rho>))\<^esub>"
          by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as]])
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<rho>\<^esub>"
          apply (rule arg_cong) back
          apply (rule HSem_redo[OF cond3, simplified (no_asm)])
          apply (rule disjoint_is_HSem_cond)
          using disjoint by auto
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
          by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as], symmetric])
        also note x = calculation

        show ?case
          apply (subst lookup_fmap_restr[OF _ x', simplified])
          apply (subst HSem_eq[OF cond2])
          apply (subst the_lookup_join[OF compat1])
          apply (subst the_lookup_join[OF compat2])
          apply (rule join_mono[OF the_lookup_compatible[OF compat1] the_lookup_compatible[OF compat2]])
            using x' apply (cases "x' \<in> fdom \<rho>", simp_all)[1]
          apply (cases "x' \<in> insert x (heapVars \<Gamma>)")
          defer
            using x' apply simp
          apply (cases "x' = x")
            using x apply simp
          apply (subst lookup_fmap_expand1)
            apply simp_all[3]
          apply (subst lookup_fmap_expand1)
            apply auto[3]
          apply (simp add: lookupHeapToEnvNotAppend[OF x'_not_as])
          apply (subst lookupHeapToEnv, assumption)
          apply (subst lookupHeapToEnv, assumption)
          apply (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] eq_imp_below])
          apply (erule Gamma_eq[OF the_map_of_snd])
          done
      qed
    qed

    have [simp]: "set (bn as) \<sharp>* (\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho>)"
      apply (rule HSem_fresh_star)
      using fresh by (auto simp add: fresh_star_Pair fresh_star_Cons)

    have "(\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) \<sqsubseteq> \<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho>"
    proof (rule HSem_below)
    case goal1
      show ?case
        apply (rule fmap_expand_belowI)
          apply auto[1]
        apply (rule below_trans[OF HSem_refines_lookup[OF cond1]], assumption)
        apply (rule HSem_refines_lookup)
          apply (rule disjoint_is_HSem_cond)
          using disjoint apply auto[1]
        apply simp
        done
    case (goal2 x')
      have body: "\<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho> f! x"
        apply (subst ESem.simps(4)[symmetric])
        apply simp
        apply (subst the_lookup_HSem_other)
        apply (metis x_not_as)
        apply (rule below_trans[OF eq_imp_below HSem_heap_below[OF cond1]])
        apply auto
        done
      show ?case
        apply (cases "x' = x")
          apply simp
          apply (rule body)
        
        apply (subst (1 2) HSem_merge)
          apply (metis distinct1 distinct2 distinctVars.intros(2) distinctVars_Cons distinctVars_ConsD(1) distinctVars_appendI inf_commute notInAs)
          using fresh apply (metis fresh_star_Pair fresh_star_Cons set_bn_to_atom_heapVars)
          using too_lazy_to_do_it_for_more_than_fempty apply simp
        apply (rule below_trans[OF eq_imp_below HSem_heap_below, rotated])
          apply (rule disjoint_is_HSem_cond) using too_lazy_to_do_it_for_more_than_fempty apply simp
          using goal2 apply simp
        apply (rule arg_cong) back
          apply (cases "x' \<in> heapVars (asToHeap as)")
          apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
          apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
        done
    qed
    thus "fmap_restr (insert x (fdom \<rho> \<union> heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) \<sqsubseteq> \<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho>"
      apply (rule below_trans[OF cont2monofunE[OF fmap_restr_cont] eq_imp_below])
      apply (rule fmap_restr_HSem_noop[of _ "\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho>", simplified (no_asm)])
      using disjoint apply auto
      done
  qed
  thus ?case
    by (rule subst[where s = "insert q Q", standard, rotated], auto)
qed
end
