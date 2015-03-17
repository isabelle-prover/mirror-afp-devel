theory ResourcedAdequacy
imports "ResourcedDenotational" "Launchbury" "AList-Utils" "CorrectnessResourced"
begin

lemma demand_not_0: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> \<bottom>"
proof
  assume "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<bottom>"
  with demand_suffices'[where n = 0, simplified, OF this]
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>\<bottom> \<noteq> \<bottom>" by simp
  thus False by simp
qed

text {*
The semantics of an expression, given only @{term r} resources, will only use values from the
environment with less resources.
*}

lemma restr_can_restrict_env: "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^bsub>r\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)|\<^bsub>r\<^esub>"
proof(induction e arbitrary: \<rho> r rule: exp_induct)
  case (Var x)
  show ?case
  proof(rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      assume "r' = C\<cdot>r''" with `r' \<sqsubseteq> r`
      have "(Cpred\<cdot>r \<sqinter> r'') = r''"
        by (metis Cpred.simps below_refl is_meetI monofun_cfun_arg)
      hence "\<rho> x\<cdot>r'' = (\<rho> x|\<^bsub>Cpred\<cdot>r\<^esub>)\<cdot>r''" by simp
    }
    thus "(\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
next
  case (Lam x e)
  show ?case
  proof(rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      fix v
      assume "r' = C\<cdot>r''"
      with `r' \<sqsubseteq> r`
      have [simp]: "r'' \<sqinter> Cpred\<cdot>r = r''"
        by (metis C.inverts C_Cpred_id below_refl is_meetI meet_above_iff meet_bot2)

      have "r'' \<sqsubseteq> r" by (metis `r' = C\<cdot>r''` `r' \<sqsubseteq> r` below_C below_trans)
      hence "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v|\<^bsub>r''\<^esub>)\<^esub>)|\<^bsub>r''\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>(\<rho>(x := v|\<^bsub>r''\<^esub>))|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)|\<^bsub>r''\<^esub>"
        by (rule C_restr_eq_lower[OF Lam])
      also have "(\<rho>(x := v|\<^bsub>r''\<^esub>))|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = (\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>)(x := v|\<^bsub>r''\<^esub>)"  by simp
      finally
      have "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v|\<^bsub>r''\<^esub>)\<^esub>)|\<^bsub>r''\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>(\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>)(x := v|\<^bsub>r''\<^esub>)\<^esub>)|\<^bsub>r''\<^esub>".
    }
    thus "(\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
next
  case (App e x)
  show ?case
  proof (rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      assume "r' = C\<cdot>r''" with `r' \<sqsubseteq> r`
      have ** : "(Cpred\<cdot>r \<sqinter> r'') = r''"
        by (metis Cpred.simps below_refl is_meetI monofun_cfun_arg)

      have "r'' \<sqsubseteq> r" by (metis `r' = C\<cdot>r''` `r' \<sqsubseteq> r` below_C below_trans)
      hence *: "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r'' = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r''"
        by (rule C_restr_eqD[OF App])

      note * **
    }
    thus "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
next
  case (Bool b)
  show ?case by simp
next
  case (IfThenElse scrut e\<^sub>1 e\<^sub>2)
  show ?case
  proof (rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      assume "r' = C\<cdot>r''" with `r' \<sqsubseteq> r`
      have ** : "(Cpred\<cdot>r \<sqinter> r'') = r''"
        by (metis Cpred.simps below_refl is_meetI monofun_cfun_arg)

      have "r'' \<sqsubseteq> r" by (metis `r' = C\<cdot>r''` `r' \<sqsubseteq> r` below_C below_trans)
      have eq1: "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r'' = (\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r''"
        using `r'' \<sqsubseteq> r` by (rule C_restr_eqD[OF IfThenElse(1)])
      have eq2: "(\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r'' = (\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r''"
        using `r'' \<sqsubseteq> r` by (rule C_restr_eqD[OF IfThenElse(2)])
      have eq3: "(\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r'' = (\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r''"
        using `r'' \<sqsubseteq> r` by (rule C_restr_eqD[OF IfThenElse(3)])

      note eq1 eq2 eq3 **
    }
    thus "(\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
next
  case (Let as e)

  txt {* The lemma, lifted to heaps *}
  have restr_can_restrict_env_heap : "\<And> r. (\<N>\<lbrace>as\<rbrace>\<rho>)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<N>\<lbrace>as\<rbrace>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>"
  proof(rule has_ESem.parallel_HSem_ind)
    fix \<rho>\<^sub>1 \<rho>\<^sub>2 :: CEnv and r :: C
    assume "\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>r\<^esub>"
    hence "\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>" by (metis env_restr_eq_Cpred)

    show " (\<rho> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>"
    proof(rule env_C_restr_cong)
      fix x and r'
      assume "r' \<sqsubseteq> r"

      show "(\<rho> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>) x\<cdot>r' = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>) x\<cdot>r'"
      proof(cases "x \<in> domA as")
        case True
        have "(\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>)\<cdot>r' = (\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
          by (rule C_restr_eqD[OF Let(1)[OF True] `r' \<sqsubseteq> r`])
        also have "\<dots> = (\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
          unfolding `\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>`..
        also have "\<dots>   = (\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>)\<cdot>r'"
          by (rule C_restr_eqD[OF Let(1)[OF True] `r' \<sqsubseteq> r`, symmetric])
        finally
        show ?thesis using True by (simp add: lookupEvalHeap)
      next
        case False
        from `r' \<sqsubseteq> r` have "(r \<sqinter> r') = r'" by (metis below_refl is_meetI)
        thus ?thesis using False by simp
      qed
    qed
  qed simp_all

  show ?case
  proof (rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      assume "r' = C\<cdot>r''" with `r' \<sqsubseteq> r`
      have ** : "(Cpred\<cdot>r \<sqinter> r'') = r''"
        by (metis Cpred.simps below_refl is_meetI monofun_cfun_arg)

      have "r'' \<sqsubseteq> r" by (metis `r' = C\<cdot>r''` `r' \<sqsubseteq> r` below_C below_trans)

      have "(\<N>\<lbrace>as\<rbrace>\<rho>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = (\<N>\<lbrace>as\<rbrace>(\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>))|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>"
        by (rule restr_can_restrict_env_heap)
      hence "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<rho>\<^esub>)\<cdot>r'' = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r''"
        by (subst (1 2)  C_restr_eqD[OF Let(2) `r'' \<sqsubseteq> r`]) simp
    }
    thus " (\<N>\<lbrakk> Let as e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> Let as e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
qed

lemma can_restrict_env:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r"
  by (rule C_restr_eqD[OF restr_can_restrict_env below_refl])

text {*
When an expression @{term e} terminates, then we can remove such an expression from the heap and it
still terminates. This is the crucial trick to handle black-holing in the resourced semantics.
*}

lemma add_BH:
  assumes "map_of \<Gamma> x = Some e"
  assumes  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  def r \<equiv> "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)"
  have "r \<noteq> \<bottom>" unfolding r_def by (rule demand_not_0)

  from  assms(2)
  have "r \<sqsubseteq> C\<^bsup>n\<^esup>" unfolding r_def not_bot_demand by simp

  from assms(1)
  have [simp]: "the (map_of \<Gamma> x) = e" by (metis option.sel)

  from assms(1)
  have [simp]: "x \<in> domA \<Gamma>" by (metis domIff dom_map_of_conv_domA not_Some_eq)

  def ub \<equiv> "\<N>\<lbrace>\<Gamma>\<rbrace>" -- "An upper bound for the induction"

  have heaps: "(\<N>\<lbrace>\<Gamma>\<rbrace>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>" and "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> ub"
  proof (induction rule: HSem_bot_ind) 
    fix \<rho>'
    assume "\<rho>'|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>"
    assume "\<rho>' \<sqsubseteq> ub"

    show "(\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>"
    proof (rule fun_belowI)
      fix y
      show "((\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>) y \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>) y"
      proof (cases "y = x")
        case True
        have "((\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>) x = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)|\<^bsub>Cpred\<cdot>r\<^esub>"
          by (simp add: lookupEvalHeap)
        also have "\<dots> \<sqsubseteq> (\<N>\<lbrakk> e \<rbrakk>\<^bsub>ub\<^esub>)|\<^bsub>Cpred\<cdot>r\<^esub>"
          using `\<rho>' \<sqsubseteq> ub` by (intro monofun_cfun_arg)
        also have "\<dots> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)|\<^bsub>Cpred\<cdot>(demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>))\<^esub>"
          unfolding ub_def r_def..
        also have "\<dots> = \<bottom>"
          by (rule C_restr_bot_demand) (simp add:  demand_not_0)
        also have "\<dots> =  (\<N>\<lbrace>delete x \<Gamma>\<rbrace>) x"
          by (simp add: lookup_HSem_other)
        finally
        show ?thesis unfolding True.
      next
        case False
        show ?thesis
        proof (cases "y \<in> domA \<Gamma>")
          case True
          have "(\<N>\<lbrakk> the (map_of \<Gamma> y) \<rbrakk>\<^bsub>\<rho>'\<^esub>)|\<^bsub>Cpred\<cdot>r\<^esub> = (\<N>\<lbrakk> the (map_of \<Gamma> y) \<rbrakk>\<^bsub>\<rho>'|\<^sup>\<circ>\<^bsub>Cpred\<cdot>(Cpred\<cdot>r)\<^esub>\<^esub>)|\<^bsub>Cpred\<cdot>r\<^esub>"
            by (rule restr_can_restrict_env)
          also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> the (map_of \<Gamma> y) \<rbrakk>\<^bsub>\<rho>'|\<^sup>\<circ>\<^bsub>Cpred\<cdot>(Cpred\<cdot>r)\<^esub>\<^esub>"
            by (rule C_restr_below)
          also have "\<rho>'|\<^sup>\<circ>\<^bsub>Cpred\<cdot>(Cpred\<cdot>r)\<^esub> \<sqsubseteq> \<rho>'|\<^sup>\<circ>\<^bsub>(Cpred\<cdot>r)\<^esub>"
            by (intro monofun_cfun_arg monofun_cfun_fun Cpred_below)
          also note `\<dots> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>`
          finally
          show ?thesis
            using `y \<in> domA \<Gamma>` `y \<noteq> x`
            by (simp add: lookupEvalHeap lookup_HSem_heap)
        next
          case False
          thus ?thesis by simp
        qed
      qed
    qed

    from `\<rho>' \<sqsubseteq> ub`
    have "(\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>) \<sqsubseteq> (\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>ub\<^esub>)" 
      by (rule cont2monofunE[rotated]) simp
    also have "\<dots> = ub"
      unfolding ub_def HSem_bot_eq[symmetric]..
    finally     
    show "(\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>) \<sqsubseteq> ub".
  qed simp_all

  from assms(2)
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>"
    unfolding r_def
    by (rule demand_suffices[OF infinite_resources_suffice])
  also
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Gamma>\<rbrace>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r"
    by (rule can_restrict_env)
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>r"
    by (intro monofun_cfun_arg monofun_cfun_fun heaps )
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
    using `r \<sqsubseteq> C\<^bsup>n\<^esup>` by (rule monofun_cfun_arg)
  finally
  show ?thesis by this (intro cont2cont)+
qed

text {*
If we get a result with finitely many resources, we can perform induction on that numbers.
*}

lemma adequacy_finite:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
using assms
proof(induction n arbitrary: \<Gamma> e S)
  case 0
  hence False by auto
  thus ?case..
next
  case (Suc n)
  from Suc.prems
  show ?case
  proof(cases e rule:exp_strong_exhaust(1)[where c = "(\<Gamma>,S)", case_names Var App Let Lam Bool IfThenElse])
  case (Var x)
    let ?e = "the (map_of \<Gamma> x)"
    from Suc.prems[unfolded Var]
    have "x \<in> domA \<Gamma>" 
      by (auto intro: ccontr simp add: lookup_HSem_other)
    hence "map_of \<Gamma> x = Some ?e" by (rule domA_map_of_Some_the)
    moreover
    from Suc.prems[unfolded Var] `map_of \<Gamma> x = Some ?e` `x \<in> domA \<Gamma>`
    have "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp add: lookup_HSem_heap  simp del: app_strict)
    hence "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (rule add_BH[OF `map_of \<Gamma> x = Some ?e`])
    from Suc.IH[OF this]
    obtain \<Delta> v where "delete x \<Gamma> : ?e \<Down>\<^bsub>x # S\<^esub> \<Delta> : v" by blast
    ultimately
    have "\<Gamma> : (Var x) \<Down>\<^bsub>S\<^esub> (x,v) #  \<Delta> : v" by (rule Variable)
    thus ?thesis using Var by auto
  next
  case (App e' x)
    have "finite (set S \<union> fv (\<Gamma>, e'))" by simp
    from finite_list[OF this]
    obtain S' where S': "set S' = set S \<union> fv (\<Gamma>, e')"..

    from Suc.prems[unfolded App]
    have prem: "((\<N>\<lbrakk> e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>C\<^bsup>n\<^esup>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp del: app_strict)
    hence "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by auto
    from Suc.IH[OF this]
    obtain \<Delta> v where lhs': "\<Gamma> : e' \<Down>\<^bsub>S'\<^esub> \<Delta> : v" by blast 

    have "fv (\<Gamma>, e') \<subseteq> set S'" using S' by auto
    from correctness_empty_env[OF lhs' this]
    have correct1: "\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>v\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and correct2: "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by auto

    from prem
    have "((\<N>\<lbrakk> v \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>C\<^bsup>n\<^esup>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
      by (rule not_bot_below_trans)(intro correct1 monofun_cfun_fun  monofun_cfun_arg)
    with result_evaluated[OF lhs']
    have "isLam v" by (cases n, auto, cases v rule: isVal.cases, auto)
    then  obtain y e'' where n': "v = (Lam [y]. e'')" and "atom y \<sharp> (x, \<Delta>)"
      by (rule isLam_obtain_fresh)
    with lhs'
    have lhs: "\<Gamma> : e' \<Down>\<^bsub>S'\<^esub> \<Delta> : Lam [y]. e''" by simp

    from `atom y \<sharp> _` have "y \<notin> domA \<Delta>" by (metis (full_types) fresh_Pair domA_not_fresh)
    from `atom y \<sharp> _` have "y \<noteq> x" by (metis (full_types) fresh_Pair fresh_at_base(2))
   
    have "((\<N>\<lbrakk> e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>C\<^bsup>n\<^esup>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" using prem.
    also have "(\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>C\<^bsup>n\<^esup>\<^esub> \<sqsubseteq> (\<N>\<lbrace>\<Gamma>\<rbrace>) x" by (rule C_restr_below)
    also note `\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>v\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>`
    also note `v = _`
    also note `(\<N>\<lbrace>\<Gamma>\<rbrace>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>)`
    also have "(\<N>\<lbrakk> Lam [y]. e'' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<sqsubseteq> CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := v)\<^esub>)"
      by (rule CELam_no_restr)
    also have "(\<dots> \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace>) x)\<cdot>C\<^bsup>n\<^esup> = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      using `y \<notin> domA \<Delta>` by simp
    also have "\<dots> = (\<N>\<lbrakk>e''[y::=x]\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      unfolding ESem_subst[OF `y \<noteq> x`]..
    finally
    have "\<dots> \<noteq> \<bottom>" by this (intro cont2cont cont_fun)+
    then
    obtain \<Theta> v' where rhs: "\<Delta> : e''[y::=x] \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" using Suc.IH by blast
    
    have "\<Gamma> : App e' x \<Down>\<^bsub>S'\<^esub> \<Theta> : v'"
      by (rule reds_ApplicationI[OF lhs rhs])
    hence "\<Gamma> : App e' x \<Down>\<^bsub>S\<^esub> \<Theta> : v'"
      apply (rule reds_smaller_L) using S' by auto
    thus ?thesis using App by auto
  next
  case (Lam v e')
    have "\<Gamma> : Lam [v]. e' \<Down>\<^bsub>S\<^esub> \<Gamma> : Lam [v]. e'" ..
    thus ?thesis using Lam by blast
  next
  case (Bool b)
    have "\<Gamma> : Bool b \<Down>\<^bsub>S\<^esub> \<Gamma> : Bool b" by rule
    thus ?thesis using Bool by blast
  next
  case (IfThenElse scrut e\<^sub>1 e\<^sub>2)

    from Suc.prems[unfolded IfThenElse]
    have prem: "CB_project\<cdot>((\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>)\<cdot>((\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>)\<cdot>((\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>) \<noteq> \<bottom>" by (auto simp del: app_strict)
    then obtain b where
      is_CB: "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> = CB\<cdot>(Discr b)"
      and not_bot2: "((\<N>\<lbrakk> (if b then e\<^sub>1 else e\<^sub>2) \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>) \<noteq> \<bottom>"
    unfolding CB_project_not_bot by (auto split: if_splits)

    have "finite (set S \<union> fv (\<Gamma>, scrut))" by simp
    from finite_list[OF this]
    obtain S' where S': "set S' = set S \<union> fv (\<Gamma>, scrut)"..


    from is_CB have "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by simp
    from Suc.IH[OF this]
    obtain \<Delta> v where lhs': "\<Gamma> : scrut \<Down>\<^bsub>S'\<^esub> \<Delta> : v" by blast
    then have "isVal v" by (rule result_evaluated)

    have "fv (\<Gamma>, scrut) \<subseteq> set S'" using S' by simp
    from correctness_empty_env[OF lhs' this]
    have correct1: "\<N>\<lbrakk>scrut\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>v\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and correct2: "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by auto

    from correct1
    have "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<sqsubseteq> (\<N>\<lbrakk> v \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>" by (rule monofun_cfun_fun)
    with is_CB
    have "(\<N>\<lbrakk> v \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> = CB\<cdot>(Discr b)" by simp
    with `isVal v`
    have "v = Bool b" by (cases v rule: isVal.cases) (case_tac n, auto)+

    from not_bot2 `\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>`
    have "(\<N>\<lbrakk> (if b then e\<^sub>1 else e\<^sub>2) \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
      by (rule not_bot_below_trans[OF _ monofun_cfun_fun[OF monofun_cfun_arg]])
    from Suc.IH[OF this]
    obtain \<Theta> v' where rhs: "\<Delta> : (if b then e\<^sub>1 else e\<^sub>2) \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" by blast

    from lhs'[unfolded `v = _`] rhs
    have "\<Gamma> : (scrut ? e\<^sub>1 : e\<^sub>2) \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" by rule
    hence "\<Gamma> : (scrut ? e\<^sub>1 : e\<^sub>2) \<Down>\<^bsub>S\<^esub> \<Theta> : v'"
      apply (rule reds_smaller_L) using S' by auto
    thus ?thesis unfolding IfThenElse by blast
  next
  case (Let as e')
    from Suc.prems[unfolded Let(2)]
    have prem: "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" 
      by (simp  del: app_strict)
    also
      have "atom ` domA as \<sharp>* \<Gamma>" using Let(1) by (simp add: fresh_star_Pair)
      hence "\<N>\<lbrace>as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace> = \<N>\<lbrace>as @ \<Gamma>\<rbrace>" by (rule HSem_merge)
    finally 
    have "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>as @ \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>".
    then
    obtain \<Delta> v where "as @ \<Gamma> : e' \<Down>\<^bsub>S\<^esub> \<Delta> : v" using Suc.IH by blast
    hence "\<Gamma> : Let as e' \<Down>\<^bsub>S\<^esub> \<Delta> : v"
      by (rule reds.Let[OF Let(1)])
    thus ?thesis using Let by auto
  qed
qed

theorem resourced_adequacy:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
  by (rule finite_resources_suffice[OF infinite_resources_suffice[OF assms(1)]])
     (erule adequacy_finite)
end
