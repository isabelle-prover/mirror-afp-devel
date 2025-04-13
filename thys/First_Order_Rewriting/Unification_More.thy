subsubsection\<open>A Concrete Unification Algorithm\<close>

theory Unification_More
  imports
    First_Order_Terms.Unification
    First_Order_Rewriting.Term_Impl
begin

lemma set_subst_list [simp]:
  "set (subst_list \<sigma> E) = subst_set \<sigma> (set E)"
  by (simp add: subst_list_def subst_set_def)

lemma mgu_var_disjoint_right:
  fixes s t :: "('f, 'v) term" and \<sigma> \<tau> :: "('f, 'v) subst" and T 
  assumes s: "vars_term s \<subseteq> S"
    and inj: "inj T"
    and ST: "S \<inter> range T = {}"
    and id: "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists> \<mu> \<delta>. mgu s (map_vars_term T t) = Some \<mu> \<and>
    s \<cdot> \<sigma> = s \<cdot> \<mu> \<cdot> \<delta> \<and>
    (\<forall>t::('f, 'v) term. t \<cdot> \<tau> = map_vars_term T t \<cdot> \<mu> \<cdot> \<delta>) \<and>
    (\<forall>x\<in>S. \<sigma> x = \<mu> x \<cdot> \<delta>)"
proof -
  let ?\<sigma> = "\<lambda> x. if x \<in> S then \<sigma> x else \<tau> ((the_inv T) x)"
  let ?t = "map_vars_term T t"
  have ids: "s \<cdot> \<sigma> = s \<cdot> ?\<sigma>"
    by (rule term_subst_eq, insert s, auto)
  have "t \<cdot> \<tau> = map_vars_term (the_inv T) ?t \<cdot> \<tau>"
    unfolding map_vars_term_compose o_def using the_inv_f_f[OF inj] by (auto simp: term.map_ident)
  also have "... = ?t \<cdot> (\<tau> \<circ> the_inv T)" unfolding apply_subst_map_vars_term ..
  also have "... = ?t \<cdot> ?\<sigma>"
  proof (rule term_subst_eq)
    fix x
    assume "x \<in> vars_term ?t"
    then have "x \<in> T ` UNIV" unfolding term.set_map by auto
    then have "x \<notin> S" using ST by auto
    then show "(\<tau> \<circ> the_inv T) x = ?\<sigma> x" by simp
  qed
  finally have idt: "t \<cdot> \<tau> = ?t \<cdot> ?\<sigma>" by simp
  from id[unfolded ids idt] have id: "s \<cdot> ?\<sigma> = ?t \<cdot> ?\<sigma>" .
  with mgu_complete[of s ?t] id obtain \<mu> where \<mu>: "mgu s ?t = Some \<mu>"
    unfolding unifiers_def  by (cases "mgu s ?t", auto)
  from the_mgu[OF id] have id: "s \<cdot> \<mu> = map_vars_term T t \<cdot> \<mu>" and \<sigma>: "?\<sigma> = \<mu> \<circ>\<^sub>s ?\<sigma>"
    unfolding the_mgu_def \<mu> by auto
  have "s \<cdot> \<sigma> = s \<cdot> (\<mu> \<circ>\<^sub>s ?\<sigma>)" unfolding ids using \<sigma> by simp
  also have "... = s \<cdot> \<mu> \<cdot> ?\<sigma>" by simp
  finally have ids: "s \<cdot> \<sigma> = s \<cdot> \<mu> \<cdot> ?\<sigma>" .
  {
    fix x
    have "\<tau> x = ?\<sigma> (T x)" using ST unfolding the_inv_f_f[OF inj] by auto
    also have "... = (\<mu> \<circ>\<^sub>s ?\<sigma>) (T x)" using \<sigma> by simp
    also have "... = \<mu> (T x) \<cdot> ?\<sigma>" unfolding subst_compose_def by simp
    finally have "\<tau> x = \<mu> (T x) \<cdot> ?\<sigma>" .
  } note \<tau> = this
  {
    fix t :: "('f,'v)term"
    have "t \<cdot> \<tau> = t \<cdot> (\<lambda> x. \<mu> (T x) \<cdot> ?\<sigma>)" unfolding \<tau>[symmetric] ..
    also have "... = map_vars_term T t \<cdot> \<mu> \<cdot> ?\<sigma>" unfolding apply_subst_map_vars_term 
        subst_subst by (rule term_subst_eq, simp add: subst_compose_def)
    finally have "t \<cdot> \<tau> = map_vars_term T t \<cdot> \<mu> \<cdot> ?\<sigma>" .
  } note idt = this
  {
    fix x 
    assume "x \<in> S"
    then have "\<sigma> x = ?\<sigma> x" by simp
    also have "... = (\<mu> \<circ>\<^sub>s ?\<sigma>) x" using \<sigma> by simp
    also have "... = \<mu> x \<cdot> ?\<sigma>" unfolding subst_compose_def ..
    finally have "\<sigma> x = \<mu> x \<cdot> ?\<sigma>" .
  } note \<sigma> = this
  show ?thesis 
    by (rule exI[of _ \<mu>], rule exI[of _ ?\<sigma>], insert \<mu> ids idt \<sigma>, auto)
qed

abbreviation (input) x_var :: "string \<Rightarrow> string" where "x_var \<equiv> Cons (CHR ''x'')"
abbreviation (input) y_var :: "string \<Rightarrow> string" where "y_var \<equiv> Cons (CHR ''y'')"
abbreviation (input) z_var :: "string \<Rightarrow> string" where "z_var \<equiv> Cons (CHR ''z'')"

lemma mgu_var_disjoint_right_string:
  fixes s t :: "('f, string) term" and \<sigma> \<tau> :: "('f, string) subst"
  assumes s: "vars_term s \<subseteq> range x_var \<union> range z_var"
    and id: "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists> \<mu> \<delta>. mgu s (map_vars_term y_var t) = Some \<mu> \<and>
    s \<cdot> \<sigma> = s \<cdot> \<mu> \<cdot> \<delta> \<and> (\<forall>t::('f, string) term. t \<cdot> \<tau> = map_vars_term y_var t \<cdot> \<mu> \<cdot> \<delta>) \<and>
    (\<forall>x \<in> range x_var \<union> range z_var. \<sigma> x = \<mu> x \<cdot> \<delta>)"
proof -
  have inj: "inj y_var" unfolding inj_on_def by simp
  show ?thesis
    by (rule mgu_var_disjoint_right[OF s inj _ id], auto)
qed

lemma not_elem_subst_of:
  assumes "x \<notin> set (map fst xs)"
  shows "(subst_of xs) x = Var x"
  using assms proof (induct xs)
  case (Cons y xs)
  then show ?case unfolding subst_of_simps
    by (metis Term.term.simps(17) insert_iff list.simps(15) list.simps(9) singletonD subst_compose subst_ident)
qed simp

lemma subst_of_id:
  assumes "\<And>s. s \<in> (set ss) \<longrightarrow> (\<exists>x t. s = (x, t) \<and> t = Var x)" 
  shows "subst_of ss = Var" 
  using assms proof(induct ss)
  case (Cons s ss)
  then obtain y t where s:"s = (y, t)" and t:"t = Var y"
    by (metis list.set_intros(1))
  from Cons have "subst_of ss = Var"
    by simp 
  then show ?case 
    unfolding subst_of_def foldr.simps o_apply s t by simp
qed simp

(*The variable x is mapped to term t if (x, t) appears in the list given to subst_of
and no variable of t is bound to another value by the constructed substitution.*)
lemma subst_of_apply:
  assumes "(x, t) \<in> set ss"
    and "\<forall>(y,s) \<in> set ss. (y = x \<longrightarrow> s = t)"
    and "set (map fst ss) \<inter> vars_term t = {}"
  shows "subst_of ss x = t"
  using assms proof(induct ss)
  case (Cons a ss)
  show ?case proof(cases "(x,t) \<in> set ss")
    case True
    from Cons(1)[OF True] Cons(3,4) have sub:"subst_of ss x = t"
      by (simp add: disjoint_iff) 
    from Cons(2,4) have "fst a \<notin> vars_term t"
      by fastforce 
    then show ?thesis 
      unfolding subst_of_simps subst_compose sub by simp 
  next
    case False
    then have "x \<notin> set (map fst ss)"
      using Cons(3) by auto
    then have sub:"subst_of ss x = Var x"
      by (meson not_elem_subst_of) 
    from Cons(2) False have "a = (x, t)"
      by simp 
    then show ?thesis 
      unfolding subst_of_simps subst_compose sub by simp 
  qed
qed simp

lemma unify_equation_same:
  assumes "fst e = snd e" 
  shows "unify (E1@e#E2) ys = unify (E1@E2) ys" 
  using assms proof (induction "E1@e#E2" ys arbitrary: E1 E2 e ys rule: unify.induct)
  case (2 f ss g ts E bs)
  show ?case proof(cases E1)
    case Nil
    with 2(3) show ?thesis
      by (simp add: unify_Cons_same)
  next
    case (Cons e1 es1)
    then have e1:"e1 = (Fun f ss, Fun g ts)" 
      using 2(2) by simp 
    show ?thesis proof(cases "decompose (Fun f ss) (Fun g ts)")
      case None
      then show ?thesis unfolding Cons e1 by simp
    next
      case (Some us)
      have us:"us @ E = (us @ es1) @ e # E2" 
        using 2(2) Cons e1 by simp  
      from 2(1)[OF Some us 2(3)] show ?thesis unfolding Cons e1 append_Cons unify.simps Some by simp
    qed
  qed
next
  case (3 x t E bs)
  show ?case proof(cases E1)
    case Nil
    with 3(4) show ?thesis
      by (simp add: unify_Cons_same)
  next
    case (Cons e1 es1)
    with 3(3) have e1:"e1 = (Var x, t)" 
      by simp
    with 3(3) Cons have E:"E = es1 @ e # E2" 
      by simp
    show ?thesis proof(cases "t = Var x")
      case True
      from 3(1)[OF True E 3(4)] show ?thesis 
        unfolding Cons e1 True by simp
    next
      case False
      then show ?thesis proof(cases "x \<notin> vars_term t")
        case True
        let ?\<sigma>="(subst x t)"
        have substs:"subst_list ?\<sigma> E = (subst_list ?\<sigma> es1) @ (fst e \<cdot> ?\<sigma>,  snd e \<cdot> ?\<sigma>) # (subst_list ?\<sigma> E2)"
          unfolding E by (simp add: subst_list_def)
        from 3(2)[OF False True substs] 3(4) show ?thesis 
          unfolding Cons e1 append_Cons unify.simps using False True
          by (smt (verit, ccfv_SIG) E fst_eqD snd_eqD subst_list_append substs) 
      next
        case False
        then show ?thesis 
          unfolding Cons e1 append_Cons unify.simps using 3 Cons by auto 
      qed
    qed
  qed
next
  case (4 f ts x E bs)
  show ?case proof(cases E1)
    case Nil
    with 4(3) show ?thesis
      by (simp add: unify_Cons_same)
  next
    case (Cons e1 es1)
    with 4(2) have e1:"e1 = (Fun f ts, Var x)" 
      by simp
    with 4(2) Cons have E:"E = es1 @ e # E2" 
      by simp
    show ?thesis proof(cases "x \<notin> vars_term (Fun f ts)")
      case True
      let ?\<sigma>="(subst x (Fun f ts))"
      have substs:"subst_list ?\<sigma> E = (subst_list ?\<sigma> es1) @ (fst e \<cdot> ?\<sigma>,  snd e \<cdot> ?\<sigma>) # (subst_list ?\<sigma> E2)"
        unfolding E by (simp add: subst_list_def)
      from 4(1)[OF True substs] 4(3) show ?thesis 
        unfolding Cons e1 append_Cons unify.simps using True
        by (metis E fst_conv snd_conv subst_list_append substs) 
    next
      case False
      then show ?thesis 
        unfolding Cons e1 append_Cons unify.simps using 4 Cons by auto 
    qed
  qed
qed simp

lemma unify_filter_same: (*put into Unification.thy*)
  shows "unify (filter (\<lambda>e. fst e \<noteq> snd e) E) ys = unify E ys" 
proof(induction "length E" arbitrary:E rule:full_nat_induct)
  case 1
  show ?case proof(cases E)
    case (Cons e es)
    then show ?thesis proof(cases "filter (\<lambda>e. fst e \<noteq> snd e) E = E")
      case False
      then obtain E1 e E2 where E:"E = E1 @ e # E2" and eq:"fst e = snd e"
        by (meson filter_True split_list) 
      with unify_equation_same have "unify E ys = unify (E1 @ E2) ys"
        by blast 
      moreover from 1 E have "unify (filter (\<lambda>e. fst e \<noteq> snd e) (E1 @ E2)) ys = unify (E1 @ E2) ys"
        by (metis (no_types, lifting) add_Suc_right length_append length_nth_simps(2) order_refl) 
      moreover have "filter (\<lambda>e. fst e \<noteq> snd e) E = filter (\<lambda>e. fst e \<noteq> snd e) (E1 @ E2)" 
        unfolding E using eq by auto 
      ultimately show ?thesis
        by presburger 
    qed simp
  qed simp
qed

lemma unify_ctxt_same:
  shows "unify ((C\<langle>s\<rangle>, C\<langle>t\<rangle>)#xs) ys = unify ((s, t)#xs) ys" 
proof(induct C)
  case (More f ss1 C ss2)
  let ?us="zip (ss1 @ C\<langle>s\<rangle> # ss2) (ss1 @ C\<langle>t\<rangle> # ss2)" 
  have decomp:"decompose (Fun f (ss1 @ C\<langle>s\<rangle> # ss2)) (Fun f (ss1 @ C\<langle>t\<rangle> # ss2)) = Some ?us" 
    unfolding decompose_def by (simp add: zip_option_zip_conv)
  have unif:"unify (((More f ss1 C ss2)\<langle>s\<rangle>, (More f ss1 C ss2)\<langle>t\<rangle>) # xs) ys = unify (?us @ xs) ys" 
    unfolding intp_actxt.simps unify.simps decomp by simp
  have *:"?us = (zip ss1 ss1) @ (C\<langle>s\<rangle>, C\<langle>t\<rangle>) # (zip ss2 ss2)"
    by simp 
  have filter_us:"filter (\<lambda>e. fst e \<noteq> snd e) ?us = filter (\<lambda>e. fst e \<noteq> snd e) [(C\<langle>s\<rangle>, C\<langle>t\<rangle>)]" 
    unfolding * filter_append filter.simps by (smt (verit, ccfv_SIG) filter_False in_set_zip self_append_conv2) 
  have "filter (\<lambda>e. fst e \<noteq> snd e) (?us@xs) = filter (\<lambda>e. fst e \<noteq> snd e) ((C\<langle>s\<rangle>, C\<langle>t\<rangle>)#xs)"
    unfolding filter_append filter_us filter.simps by simp
  with More have "unify (?us @ xs) ys = unify ((s, t)#xs) ys" 
    using unify_filter_same by (smt (verit, ccfv_threshold))
  with unif show ?case by simp
qed simp

subsubsection\<open>Unification of Linear and variable disjoint terms\<close>

(*Substitutions from variable positions of term on the left to subterms of term on the right.*)
definition left_substs :: "('f, 'v) term \<Rightarrow> ('f, 'w) term \<Rightarrow> ('v \<times> ('f, 'w) term) list"
  where "left_substs s t = (let filtered_vars = filter (\<lambda>(_, p). p \<in> poss t) (zip (vars_term_list s)(var_poss_list s))
          in map (\<lambda>(x, p). (x, t|_p)) filtered_vars)"

(*Substitutions from variable positions of term on the right to subterms of the term on the left. 
Almost symmetric definition to the one above. Difference is that if there is a variable x at position
p on the left and a variable y at the same position on the right then we don't add mapping y \<mapsto> x!.*)
definition right_substs :: "('f, 'v) term \<Rightarrow> ('f, 'w) term \<Rightarrow> ('w \<times> ('f, 'v) term) list"
  where "right_substs s t = (let filtered_vars = filter (\<lambda>(_, q). q \<in> fun_poss s) (zip (vars_term_list t)(var_poss_list t))
          in map (\<lambda>(y, q). (y, s|_q)) filtered_vars)"

abbreviation "linear_unifier s t \<equiv> subst_of ((left_substs s t) @ (right_substs s t))"

lemma left_substs_imp_props:
  assumes "(x, u) \<in> set (left_substs s t)"
  shows "\<exists>p. p \<in> poss s \<and> s|_p = Var x \<and> p \<in> poss t \<and> t|_p = u"
proof-
  from assms obtain p where 1:"(x, p) \<in> set (zip (vars_term_list s)(var_poss_list s))" and 2:"p \<in> poss t" "t|_p = u"
    unfolding left_substs_def Let_def using Pair_inject case_prodE filter_set in_set_idx length_map map_nth_eq_conv member_filter nth_mem old.prod.case by auto 
  from 1 have p:"p \<in> poss s"
    by (metis set_zip_rightD var_poss_imp_poss var_poss_list_sound) 
  from 1 obtain i where "i < length (zip (vars_term_list s)(var_poss_list s))" and "(vars_term_list s)!i = x" and "(var_poss_list s)!i = p"
    by (smt (z3) Pair_inject length_zip mem_Collect_eq set_zip)
  then have "s|_p = Var x"
    by (metis length_zip min_less_iff_conj vars_term_list_var_poss_list)
  with 2 p show ?thesis
    by blast 
qed

lemma props_imp_left_substs:
  assumes "p \<in> poss s" and "s|_p = Var x" and "p \<in> poss t" and "t|_p = u"
  shows "(x, u) \<in> set (left_substs s t)"
proof-
  from assms obtain i where "(var_poss_list s)!i = p" and "(vars_term_list s)!i = x"
    by (metis in_set_conv_nth length_var_poss_list term.inject(1) var_poss_iff var_poss_list_sound vars_term_list_var_poss_list) 
  then have "(x, p) \<in> set (zip (vars_term_list s)(var_poss_list s))"
    by (metis assms(1) assms(2) in_set_idx in_set_zip length_var_poss_list prod.sel(1) prod.sel(2) term.inject(1) var_poss_iff var_poss_list_sound vars_term_list_var_poss_list)
  with assms(3) have "(x, p) \<in> set (filter (\<lambda>(_, p). p \<in> poss t) (zip (vars_term_list s) (var_poss_list s)))"
    by simp 
  then show ?thesis unfolding left_substs_def Let_def assms(4)[symmetric] 
    by (smt (z3) case_prod_conv in_set_conv_nth length_map map_nth_eq_conv)
qed

lemma right_substs_imp_props:
  assumes "(x, u) \<in> set (right_substs s t)"
  shows "\<exists>q. q \<in> fun_poss s \<and> s|_q = u \<and> q \<in> poss t \<and> t|_q = Var x"
proof-
  from assms obtain q where 1:"(x, q) \<in> set (zip (vars_term_list t)(var_poss_list t))" and 2:"q \<in> fun_poss s" "s|_q = u"
    unfolding right_substs_def Let_def using Pair_inject case_prodE filter_set in_set_idx length_map map_nth_eq_conv member_filter nth_mem old.prod.case by auto 
  from 1 have q:"q \<in> poss t"
    by (metis set_zip_rightD var_poss_imp_poss var_poss_list_sound)
  from 1 obtain i where "i < length (zip (vars_term_list t)(var_poss_list t))" and "(vars_term_list t)!i = x" and "(var_poss_list t)!i = q"
    by (smt (z3) Pair_inject length_zip mem_Collect_eq set_zip)
  then have "t|_q = Var x"
    by (metis length_zip min_less_iff_conj vars_term_list_var_poss_list)
  with 2 q show ?thesis 
    by blast 
qed

lemma props_imp_right_substs:
  assumes "q \<in> fun_poss s" and "s|_q = u" and "q \<in> poss t" and "t|_q = Var x"
  shows "(x, u) \<in> set (right_substs s t)"
proof-
  from assms obtain i where "(var_poss_list t)!i = q" and "(vars_term_list t)!i = x"
    by (metis in_set_conv_nth length_var_poss_list term.inject(1) var_poss_iff var_poss_list_sound vars_term_list_var_poss_list)  
  then have "(x, q) \<in> set (zip (vars_term_list t)(var_poss_list t))"
    by (metis assms(3) assms(4) in_set_conv_nth in_set_zip length_var_poss_list prod.sel(1) prod.sel(2) term.inject(1) var_poss_iff var_poss_list_sound vars_term_list_var_poss_list)
  with assms(1) have "(x, q) \<in> set (filter (\<lambda>(_, p). p \<in> fun_poss s) (zip (vars_term_list t) (var_poss_list t)))"
    by simp 
  then show ?thesis unfolding right_substs_def Let_def assms(2)[symmetric] 
    by (smt (z3) case_prod_conv in_set_conv_nth length_map map_nth_eq_conv)
qed

lemma map_fst_left_substs: 
  "set (map fst (left_substs s t)) \<subseteq> vars_term s" 
  unfolding left_substs_def using zip_fst by fastforce

lemma map_snd_left_substs: 
  assumes "t' \<in> set (map snd (left_substs s t))"
  shows "vars_term t' \<subseteq> vars_term t" 
proof-
  from assms obtain x where "(x, t') \<in> set (left_substs s t)"
    by force 
  then show ?thesis 
    using left_substs_imp_props by (metis vars_term_subt_at)
qed

lemma map_fst_right_substs: 
  "set (map fst (right_substs s t)) \<subseteq> vars_term t" 
  unfolding right_substs_def using zip_fst by fastforce

lemma map_snd_right_substs: 
  assumes "t' \<in> set (map snd (right_substs s t))"
  shows "vars_term t' \<subseteq> vars_term s" 
proof-
  from assms obtain x where "(x, t') \<in> set (right_substs s t)"
    by force 
  then show ?thesis 
    using right_substs_imp_props by (metis fun_poss_imp_poss vars_term_subt_at)
qed

lemma distinct_map_fst_left_substs:
  assumes "linear_term t"
  shows "distinct (map fst (left_substs t s))"
proof-
  from linear_term_distinct_vars[OF assms] have dist:"distinct (map fst (filter (\<lambda>(x, p). p \<in> poss s) (zip (vars_term_list t) (var_poss_list t))))"
    by (simp add: distinct_map_filter length_var_poss_list)
  have "map fst (left_substs t s) = (map fst (filter (\<lambda>(x, p). p \<in> poss s) (zip (vars_term_list t) (var_poss_list t))))" 
    unfolding left_substs_def Let_def by auto 
  with dist show ?thesis
    by presburger 
qed

lemma distinct_map_fst_right_substs:
  assumes "linear_term t"
  shows "distinct (map fst (right_substs s t))"
proof-
  from linear_term_distinct_vars[OF assms] have dist:"distinct (map fst (filter (\<lambda>(x, p). p \<in> fun_poss s) (zip (vars_term_list t) (var_poss_list t))))"
    by (simp add: distinct_map_filter length_var_poss_list)
  have "map fst (right_substs s t) = (map fst (filter (\<lambda>(x, p). p \<in> fun_poss s) (zip (vars_term_list t) (var_poss_list t))))" 
    unfolding right_substs_def Let_def by auto 
  with dist show ?thesis
    by presburger 
qed

lemma is_partition_map_snd_left_substs:
  assumes "linear_term s" "linear_term t"
  shows "is_partition (map (vars_term \<circ> snd) (left_substs t s))"
proof-
  {fix i j assume j:"j < length (left_substs t s)" and i:"i < j" 
    from i j obtain x u where xu:"(x, u) = (left_substs t s)!i"
      by (metis surj_pair) 
    from i j obtain y v where yv:"(y, v) = (left_substs t s)!j"
      by (metis surj_pair) 
    from xu i j obtain p where p:"p \<in> poss t"  "t|_p = Var x"  "p \<in> poss s"  "s|_p = u" 
      using left_substs_imp_props by (metis Suc_lessD less_trans_Suc nth_mem) 
    from yv i j obtain q where q:"q \<in> poss t"  "t|_q = Var y"  "q \<in> poss s"  "s|_q = v" 
      using left_substs_imp_props by (metis nth_mem) 
    from assms(2) have "distinct (map fst (left_substs t s))" 
      using distinct_map_fst_left_substs by blast
    with xu yv i j have "x \<noteq> y"
      by (metis (mono_tags, lifting) Suc_lessD distinct_map eq_key_imp_eq_value less_trans_Suc nat_neq_iff nth_eq_iff_index_eq nth_mem)  
    with p(1,2) q(1,2) have "p \<bottom> q"
      by (metis term.inject(1) var_poss_iff var_poss_parallel) 
    with assms(1) p(3,4) q(3,4) have "vars_term (snd ((left_substs t s)!i)) \<inter> vars_term (snd ((left_substs t s)!j)) = {}"
      by (metis linear_subterms_disjoint_vars snd_eqD xu yv) 
  }
  then show ?thesis unfolding is_partition_def map_map[symmetric] by auto  
qed

lemma is_partition_map_snd_right_substs:
  assumes "linear_term s" "linear_term t"
  shows "is_partition (map (vars_term \<circ> snd) (right_substs t s))"
proof-
  {fix i j assume j:"j < length (right_substs t s)" and i:"i < j" 
    from i j obtain x u where xu:"(x, u) = (right_substs t s)!i"
      by (metis surj_pair) 
    from i j obtain y v where yv:"(y, v) = (right_substs t s)!j"
      by (metis surj_pair) 
    from xu i j obtain p where p:"p \<in> poss s"  "s|_p = Var x"  "p \<in> fun_poss t"  "t|_p = u" 
      using right_substs_imp_props by (metis Suc_lessD less_trans_Suc nth_mem) 
    from yv i j obtain q where q:"q \<in> poss s"  "s|_q = Var y"  "q \<in> fun_poss t"  "t|_q = v" 
      using right_substs_imp_props by (metis nth_mem) 
    from assms(1) have "distinct (map fst (right_substs t s))" 
      using distinct_map_fst_right_substs by blast
    with xu yv i j have "x \<noteq> y"
      by (metis (mono_tags, lifting) Suc_lessD distinct_map eq_key_imp_eq_value less_trans_Suc nat_neq_iff nth_eq_iff_index_eq nth_mem)  
    with p(1,2) q(1,2) have "p \<bottom> q"
      by (metis term.inject(1) var_poss_iff var_poss_parallel) 
    with assms(2) p(3,4) q(3,4) have "vars_term (snd ((right_substs t s)!i)) \<inter> vars_term (snd ((right_substs t s)!j)) = {}"
      by (metis fun_poss_imp_poss linear_subterms_disjoint_vars snd_eqD xu yv) 
  }
  then show ?thesis unfolding is_partition_def map_map[symmetric] by auto  
qed

lemma distinct_fst_lsubsts_snd_rsubsts:
  assumes "linear_term s"
  shows "(set (map fst (left_substs s t))) \<inter> \<Union> (set (map (vars_term \<circ> snd) (right_substs s t))) = {}"
proof-
  {fix x u assume "(x,u) \<in> set (left_substs s t)"
    then obtain p where p:"p \<in> poss s" "s|_p = Var x" "p \<in> poss t"  "t|_p = u"
      by (meson left_substs_imp_props) 
    {fix y v assume "(y,v) \<in> set (right_substs s t)"
      then obtain q where q:"q \<in> poss t" "t|_q = Var y" "q \<in> fun_poss s"  "s|_q = v"
        by (meson right_substs_imp_props) 
      with p have "p \<bottom> q"
        by (metis Term.term.simps(4) append.right_neutral fun_poss_fun_conv fun_poss_imp_poss parallel_pos prefix_pos_diff var_pos_maximal)
      with assms p(1,2) q(3,4) have "x \<notin> vars_term v"
        using fun_poss_imp_poss linear_subterms_disjoint_vars by fastforce
    }
    then have "x \<notin> \<Union> (set (map (vars_term \<circ> snd) (right_substs s t)))"
      by fastforce
  }
  then show ?thesis by fastforce
qed

lemma distinct_fst_rsubsts_snd_lsubsts:
  assumes "linear_term t"
  shows "(set (map fst (right_substs s t))) \<inter> \<Union> (set (map (vars_term \<circ> snd) (left_substs s t))) = {}"
proof-
  {fix x u assume "(x,u) \<in> set (right_substs s t)"
    then obtain p where p:"p \<in> poss t" "t|_p = Var x" "p \<in> fun_poss s"  "s|_p = u"
      by (meson right_substs_imp_props) 
    {fix y v assume "(y,v) \<in> set (left_substs s t)"
      then obtain q where q:"q \<in> poss s" "s|_q = Var y" "q \<in> poss t"  "t|_q = v"
        by (meson left_substs_imp_props) 
      with p have "p \<bottom> q"
        by (metis Term.term.simps(4) append.right_neutral fun_poss_fun_conv fun_poss_imp_poss parallel_pos prefix_pos_diff var_pos_maximal)
      with assms p(1,2) q(3,4) have "x \<notin> vars_term v"
        using fun_poss_imp_poss linear_subterms_disjoint_vars by fastforce
    }
    then have "x \<notin> \<Union> (set (map (vars_term \<circ> snd) (left_substs s t)))"
      by fastforce
  }
  then show ?thesis by fastforce
qed

lemma linear_unifier_same:
  shows "(linear_unifier t t) = Var"
proof-
  let ?vars_left="filter (\<lambda>(_, p). p \<in> poss t) (zip (vars_term_list t)(var_poss_list t))"
  have left:"?vars_left = zip (vars_term_list t)(var_poss_list t)"
    by (metis (no_types, lifting) filter_True split_beta var_poss_imp_poss var_poss_list_sound zip_snd) 
  let ?vars_right="filter (\<lambda>(_, q). q \<in> fun_poss t) (zip (vars_term_list t)(var_poss_list t))"
  have right:"?vars_right = []"
    by (metis (mono_tags, lifting) DiffE filter_False poss_simps(4) split_beta var_poss_list_sound zip_snd) 
  {fix i assume i:"i < length (left_substs t t)" 
    let ?xi="vars_term_list t ! i"
    from i have "i < length (vars_term_list t)" 
      unfolding left_substs_def Let_def length_map left by simp
    then have "left_substs t t ! i = (?xi, Var ?xi)" 
      unfolding left_substs_def left Let_def nth_map[OF i[unfolded left_substs_def Let_def length_map left]]
      by (simp add: length_var_poss_list vars_term_list_var_poss_list) 
  }note left_subst=this
  {fix x 
    from left_subst have "subst_of (left_substs t t) x = Var x" 
      using subst_of_id by (metis left_substs_imp_props prod.collapse) 
  }
  then show ?thesis 
    unfolding right_substs_def right left_substs_def left by auto
qed

lemma linear_unifier_var1:
  shows "linear_unifier (Var x) t = subst x t"
proof-
  have "left_substs (Var x) t = [(x, t)]" 
    unfolding left_substs_def Let_def vars_term_list.simps var_poss_list.simps by simp 
  moreover have "right_substs (Var x) t = []" 
    unfolding right_substs_def by simp 
  ultimately show ?thesis
    by simp 
qed

lemma linear_unifier_var2:
  shows "linear_unifier (Fun f ts) (Var x) = subst x (Fun f ts)"
proof-
  have "left_substs (Fun f ts) (Var x) = []" 
    unfolding left_substs_def Let_def poss.simps
    by (metis (no_types, lifting) case_prodE filter_False map_is_Nil_conv set_zip_rightD singletonD subt_at.simps(1) term.distinct(1) var_poss_iff var_poss_list_sound) 
  moreover have "right_substs (Fun f ts) (Var x) = [(x, Fun f ts)]" 
    unfolding right_substs_def by (simp add: vars_term_list.simps(1))
  ultimately show ?thesis
    by simp 
qed

lemma linear_unifier_id:
  assumes "x \<notin> vars_term s" and "x \<notin> vars_term t" 
  shows "(linear_unifier s t) x = Var x"
  using assms by (metis (no_types, lifting) Set.basic_monos(7) eval_term.simps(1) map_fst_left_substs map_fst_right_substs not_elem_subst_of subst_compose subst_of_append) 

lemma vars_subst_of:
  "vars_subst (subst_of ts) \<subseteq> set (map fst ts) \<union> \<Union> (set (map (vars_term \<circ> snd) ts))"
proof(induct ts)
  case Nil
  show ?case unfolding subst_of_simps list.map vars_subst_def by simp
next
  case (Cons t ts)
  have "vars_subst (subst (fst t) (snd t)) \<subseteq> {fst t} \<union> (vars_term (snd t))"
    unfolding vars_subst_def by auto
  with Cons show ?case unfolding subst_of_simps using vars_subst_compose
    by (smt (verit, del_insts) Un_iff UnionI Union_mono comp_apply empty_iff insert_iff list.set_intros(1) list.simps(9) set_subset_Cons subset_iff) 
qed

lemma vars_subst_linear_unifier: "vars_subst (linear_unifier s t) \<subseteq> vars_term s \<union> vars_term t" 
proof-
  have "vars_subst (linear_unifier s t) \<subseteq> (vars_subst (subst_of (left_substs s t))) \<union> (vars_subst (subst_of (right_substs s t)))"
    unfolding subst_of_append using vars_subst_compose by force 
  moreover have "vars_subst (subst_of (left_substs s t)) \<subseteq> vars_term s \<union> vars_term t" 
  proof-
    {fix i assume "i < length (left_substs s t)"
      then have "map (vars_term \<circ> snd) (left_substs s t) ! i \<subseteq> vars_term t" 
        using map_snd_left_substs nth_mem by fastforce 
    }
    then have "\<Union> (set (map (vars_term \<circ> snd) (left_substs s t))) \<subseteq> vars_term t"
      by (metis Union_least in_set_conv_nth length_map)
    then show ?thesis
      using vars_subst_of[of "left_substs s t"] map_fst_left_substs
      by (metis (no_types, lifting) subset_trans sup.mono)
  qed
  moreover have "vars_subst (subst_of (right_substs s t)) \<subseteq> vars_term s \<union> vars_term t" 
  proof-
    {fix i assume "i < length (right_substs s t)"
      then have "map (vars_term \<circ> snd) (right_substs s t) ! i \<subseteq> vars_term s" 
        using map_snd_right_substs nth_mem by fastforce 
    }
    then have "\<Union> (set (map (vars_term \<circ> snd) (right_substs s t))) \<subseteq> vars_term s"
      by (metis Union_least in_set_conv_nth length_map)
    then show ?thesis
      using vars_subst_of[of "right_substs s t"] map_fst_right_substs by fastforce
  qed
  ultimately show ?thesis by blast
qed

lemma decompose_is_partition_vars_subst:
  assumes lin:"linear_term (Fun f ss)" "linear_term (Fun g ts)" 
    and disj:"vars_term (Fun f ss) \<inter> vars_term (Fun g ts) = {}"
    and ds:"decompose (Fun f ss) (Fun g ts) = Some ds"
  shows "is_partition (map vars_subst (map (\<lambda>(s,t). linear_unifier s t) ds))"
proof-
  from assms have zip:"ds = zip ss ts" and l:"length ss = length ts"
    using decompose_Some by blast+
  {fix i j assume j:"j < length ss" and i:"i < j" 
    from i j obtain si ti where s_t_i:"(si, ti) = ds ! i" "ss ! i = si" "ts ! i = ti"
      using l zip by force 
    from j obtain sj tj where s_t_j:"(sj, tj) = ds ! j" "ss ! j = sj" "ts ! j = tj"
      using l zip by force 
    have "vars_term si \<inter> vars_term tj = {}"
      using i j s_t_i s_t_j disj l by fastforce 
    moreover have "vars_term si \<inter> vars_term sj = {}" 
      using lin(1) s_t_i s_t_j i j var_in_linear_args by fastforce
    moreover have "vars_term ti \<inter> vars_term tj = {}"
      using lin(2) s_t_i s_t_j i j l var_in_linear_args by fastforce
    moreover have "vars_term ti \<inter> vars_term sj = {}" 
      using i j s_t_i s_t_j disj l by fastforce 
    ultimately have "vars_subst (linear_unifier si ti) \<inter> vars_subst (linear_unifier sj tj) = {}"
      using vars_subst_linear_unifier by (smt (verit, ccfv_threshold) Un_iff disjoint_iff in_mono) 
    then have "vars_subst (map (\<lambda>(s,t). linear_unifier s t) ds ! i) \<inter> vars_subst (map (\<lambda>(s,t). linear_unifier s t) ds ! j) = {}" 
      using i j s_t_j s_t_i l zip by auto
  }
  then show ?thesis unfolding is_partition_def map_map[symmetric] length_map zip using l by auto  
qed

lemma compose_exists_subst:
  assumes "compose \<sigma>s x \<noteq> Var x" 
  shows "\<exists>i < length \<sigma>s. (\<forall>j < i. (\<sigma>s!j) x = Var x) \<and> (\<sigma>s!i) x \<noteq> Var x" 
  using assms proof(induct \<sigma>s)
  case (Cons \<sigma> \<sigma>s)
  then show ?case proof(cases "\<sigma> x = Var x")
    case True
    from Cons(2) have "compose \<sigma>s x \<noteq> Var x" 
      unfolding compose_simps subst_compose True by simp
    with Cons(1) obtain i where i:"i<length \<sigma>s" "\<forall>j<i. (\<sigma>s ! j) x = Var x" "(\<sigma>s ! i) x \<noteq> Var x" by blast
    with True have "\<forall>j < Suc i. ((\<sigma>#\<sigma>s) ! j) x = Var x"
      by (metis less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc) 
    with i show ?thesis by auto 
  qed auto
qed simp

lemma subst_of_exists_binding:
  assumes "subst_of xs y \<noteq> Var y"
  shows "\<exists>i < length xs. fst (xs!i) = y \<and> (\<forall>x \<in> set (drop (i+1) xs). fst x \<noteq> y)" 
  using assms proof(induct xs rule:rev_induct)
  case (snoc x xs)
  then show ?case proof(cases "fst x = y")
    case False
    with snoc(2) have "subst_of xs y \<noteq> Var y" 
      unfolding subst_of_append subst_compose
      by (metis (no_types, lifting) empty_iff eval_term.simps(1) insert_iff subst_compose subst_ident subst_of_simps(1,3) term.set(3))
    with snoc(1) obtain i where i:"i < length xs" "fst (xs!i) = y" "\<forall>z \<in> set (drop (i+1) xs). fst z \<noteq> y" by blast
    from i(1) have "drop (i+1) (xs@[x]) = drop (i+1) xs @ [x]" by auto 
    with i(3) False have "\<forall>z \<in> set (drop (i+1) (xs@[x])). fst z \<noteq> y" by simp 
    with i(1,2) show ?thesis
      by (metis append_Cons_nth_left length_append_singleton less_Suc_eq_le less_imp_le_nat)
  qed auto
qed simp

lemma linear_unifier_obtain_binding:
  assumes disj:"vars_term s \<inter> vars_term t = {}" and lin_s:"linear_term s" and lin_t:"linear_term t"
    and u:"(linear_unifier s t) x = u" "u \<noteq> Var x" 
  shows "(x \<in> vars_term s \<and> (x,u) \<in> set (left_substs s t)) \<or> (x \<in> vars_term t \<and> (x,u) \<in> set (right_substs s t))"
proof-
  consider "x \<in> vars_term s" | "x \<in> vars_term t" | "x \<notin> vars_term s \<and> x \<notin> vars_term t"
    by fastforce 
  then show ?thesis proof(cases)
    case 1
    with disj have "x \<notin> vars_term t" by blast 
    then have right:"subst_of (right_substs s t) x = Var x"
      by (meson in_mono map_fst_right_substs not_elem_subst_of) 
    with u have "subst_of (left_substs s t) x \<noteq> Var x"
      by (simp add: subst_compose) 
    then obtain i u' where i:"i < length (left_substs s t)" "(left_substs s t)!i = (x, u')" "\<forall>subst \<in> set (drop (i+1) (left_substs s t)). fst subst \<noteq> x"
      using subst_of_exists_binding by (metis (mono_tags, opaque_lifting) eq_fst_iff) 
    then obtain l1 l2 where l1:"l1 = take i (left_substs s t)" and l2:"l2 = drop (i+1) (left_substs s t)" 
      and l1l2:"left_substs s t = l1 @ [(x,u')] @ l2" using id_take_nth_drop by fastforce 
    from i(3) have l2_subst:"subst_of l2 x = Var x" unfolding l2 by (meson nth_mem subst_of_exists_binding)
    then have 1:"subst_of (left_substs s t) x = u' \<cdot> (subst_of l1)" 
      unfolding l1l2 subst_of_append subst_compose l2_subst eval_term.simps by simp
    from i(1,2) obtain p where p:"p \<in> poss t" "t|_p = u'" using left_substs_imp_props by (metis nth_mem)
    from disj p have "set (map fst (left_substs s t)) \<inter> (vars_term u') = {}"
      by (meson disjoint_iff map_fst_left_substs subsetD vars_term_subt_at)  
    then have 2:"u' \<cdot> (subst_of l1) = u'" 
      unfolding l1 by (smt (verit, best) disjoint_iff in_set_takeD not_elem_subst_of subst_apply_term_empty take_map term_subst_eq) 
    then have u':"subst_of (left_substs s t) x = u'" 
      using 1 2 by simp  
    from i(1,2) have u'_elem:"(x, u') \<in> set (left_substs s t)" by (metis nth_mem)  
    with u' u show ?thesis
      unfolding subst_of_append subst_compose right eval_term.simps
      by (meson map_fst_left_substs not_elem_subst_of subset_iff) 
  next
    case 2
    with disj have "x \<notin> vars_term s" by blast 
    then have "subst_of (left_substs s t) x = Var x"
      by (meson in_mono map_fst_left_substs not_elem_subst_of) 
    with u have "subst_of (right_substs s t) x \<noteq> Var x"
      by (metis subst_compose subst_monoid_mult.mult.left_neutral subst_of_append)
    then obtain i u' where i:"i < length (right_substs s t)" "(right_substs s t)!i = (x, u')" "\<forall>subst \<in> set (drop (i+1) (right_substs s t)). fst subst \<noteq> x"
      using subst_of_exists_binding by (metis (mono_tags, opaque_lifting) eq_fst_iff) 
    then obtain l1 l2 where l1:"l1 = take i (right_substs s t)" and l2:"l2 = drop (i+1) (right_substs s t)" 
      and l1l2:"right_substs s t = l1 @ [(x,u')] @ l2" using id_take_nth_drop by fastforce 
    from i(3) have l2_subst:"subst_of l2 x = Var x" unfolding l2 by (meson nth_mem subst_of_exists_binding)
    then have 1:"subst_of (right_substs s t) x = u' \<cdot> (subst_of l1)" 
      unfolding l1l2 subst_of_append subst_compose l2_subst eval_term.simps by simp
    from i(1,2) obtain p where p:"p \<in> poss s" "s|_p = u'" 
      using right_substs_imp_props by (metis fun_poss_imp_poss nth_mem)
    from disj p have "set (map fst (right_substs s t)) \<inter> (vars_term u') = {}"
      by (meson disjoint_iff map_fst_right_substs subsetD vars_term_subt_at)  
    then have 2:"u' \<cdot> (subst_of l1) = u'" 
      unfolding l1 by (smt (verit, best) disjoint_iff in_set_takeD not_elem_subst_of subst_apply_term_empty take_map term_subst_eq) 
    then have u':"subst_of (right_substs s t) x = u'" 
      using 1 2 by simp  
    from i(1,2) have u'_elem:"(x, u') \<in> set (right_substs s t)" by (metis nth_mem) 
    then have "set (map fst (left_substs s t)) \<inter> (vars_term u') = {}" 
      using distinct_fst_lsubsts_snd_rsubsts[OF lin_s] by (smt (verit, ccfv_SIG) Union_iff comp_apply disjoint_iff in_set_conv_nth length_map nth_map snd_conv) 
    then have "u' \<cdot> (subst_of (left_substs s t)) = u'"
      by (metis disjoint_iff not_elem_subst_of subst_apply_term_empty term_subst_eq) 
    with u u'_elem show ?thesis 
      unfolding subst_of_append subst_compose u' by (metis map_fst_right_substs not_elem_subst_of subset_eq u')
  next
    case 3
    then have "x \<notin> set (map fst ((left_substs s t) @ (right_substs s t)))" 
      using map_fst_left_substs map_fst_right_substs by fastforce 
    then have "(linear_unifier s t) x = Var x"
      by (meson not_elem_subst_of)
    with u show ?thesis by simp
  qed
qed

text\<open>connection between @{const left_substs} and @{const right_substs} and decomposition of functions\<close>
lemma decompose_left_substs:
  assumes "decompose (Fun f ss) (Fun g ts) = Some ds"
  shows "set (left_substs (Fun f ss) (Fun g ts)) = (\<Union>e\<in>set ds. set (left_substs (fst e) (snd e)))" (is "?left = ?right") 
proof
  from assms have ds:"ds = zip ss ts" 
    using decompose_Some by auto
  show "?left \<subseteq> ?right" proof
    fix x t assume "(x,t) \<in> set (left_substs (Fun f ss) (Fun g ts))"
    then obtain p where 1:"p \<in> poss (Fun f ss)" and 2:"(Fun f ss)|_p = Var x" and 3:"p \<in> poss (Fun g ts)" and 4:"(Fun g ts)|_p = t"
      by (meson left_substs_imp_props) 
    from 1 2 obtain j p' where j1:"j < length ss" and "p = j#p'" and "p' \<in> poss (ss!j)" and "(ss!j)|_p' = Var x"
      by auto 
    moreover with 3 4 have j2:"j < length ts" and "p' \<in> poss (ts!j)" and "(ts!j)|_p' = t" 
      by auto
    ultimately have "(x,t) \<in> set (left_substs (ss!j) (ts!j))"
      by (meson props_imp_left_substs)
    moreover have "((ss!j),(ts!j)) \<in> set ds" 
      unfolding ds using j1 j2 by (metis length_zip min_less_iff_conj nth_mem nth_zip) 
    ultimately show "(x,t) \<in> (\<Union>e\<in>set ds. set (left_substs (fst e) (snd e)))"
      by force    
  qed
  show "?right \<subseteq> ?left" proof
    fix x t assume "(x,t) \<in> (\<Union>e\<in>set ds. set (left_substs (fst e) (snd e)))"
    then obtain j where j1:"j < length ss" and j2:"j < length ts" and "(x,t) \<in> set (left_substs (ss!j) (ts!j))" 
      unfolding ds by (metis (no_types, lifting) UN_E in_set_zip) 
    then obtain p where 1:"p \<in> poss (ss!j)" and 2:"(ss!j)|_p = Var x" and 3:"p \<in> poss (ts!j)" and 4:"(ts!j)|_p = t"
      by (meson left_substs_imp_props)
    then have "j#p \<in> poss (Fun f ss)" and "(Fun f ss)|_(j#p) = Var x" and "(j#p) \<in> poss (Fun g ts)" and "(Fun g ts)|_(j#p) = t" 
      using j1 j2 by auto
    then show "(x,t) \<in> set (left_substs (Fun f ss) (Fun g ts))"
      by (meson props_imp_left_substs)
  qed
qed 

lemma decompose_right_substs:
  assumes "decompose (Fun f ss) (Fun g ts) = Some ds"
  shows "set (right_substs (Fun f ss) (Fun g ts)) = (\<Union>e\<in>set ds. set (right_substs (fst e) (snd e)))" (is "?left = ?right") 
proof
  from assms have ds:"ds = zip ss ts" 
    using decompose_Some by auto
  show "?left \<subseteq> ?right" proof
    fix x t assume "(x,t) \<in> set (right_substs (Fun f ss) (Fun g ts))"
    then obtain q where 1:"q \<in> fun_poss (Fun f ss)" and 2:"(Fun f ss)|_q = t" and 3:"q \<in> poss (Fun g ts)" and 4:"(Fun g ts)|_q = Var x"
      by (meson right_substs_imp_props) 
    from 3 4 obtain j q' where j1:"j < length ts" and "q = j#q'" and "q' \<in> poss (ts!j)" and "(ts!j)|_q' = Var x" 
      by auto 
    moreover with 1 2 have j2:"j < length ss" and "q' \<in> fun_poss (ss!j)" and "(ss!j)|_q' = t" 
      by auto
    ultimately have "(x,t) \<in> set (right_substs (ss!j) (ts!j))"
      by (meson props_imp_right_substs)
    moreover have "((ss!j),(ts!j)) \<in> set ds" 
      unfolding ds using j1 j2 by (metis length_zip min_less_iff_conj nth_mem nth_zip) 
    ultimately show "(x,t) \<in> (\<Union>e\<in>set ds. set (right_substs (fst e) (snd e)))"
      by force    
  qed
  show "?right \<subseteq> ?left" proof
    fix x t assume "(x,t) \<in> (\<Union>e\<in>set ds. set (right_substs (fst e) (snd e)))"
    then obtain j where j1:"j < length ss" and j2:"j < length ts" and "(x,t) \<in> set (right_substs (ss!j) (ts!j))" 
      unfolding ds by (metis (no_types, lifting) UN_E in_set_zip) 
    then obtain q where 1:"q \<in> fun_poss (ss!j)" and 2:"(ss!j)|_q = t" and 3:"q \<in> poss (ts!j)" and 4:"(ts!j)|_q = Var x"
      by (meson right_substs_imp_props)
    then have "j#q \<in> fun_poss (Fun f ss)" and "(Fun f ss)|_(j#q) = t" and "(j#q) \<in> poss (Fun g ts)" and "(Fun g ts)|_(j#q) = Var x" 
      using j1 j2 by auto
    then show "(x,t) \<in> set (right_substs (Fun f ss) (Fun g ts))"
      by (meson props_imp_right_substs)
  qed
qed 

lemma subst_compose_id:
  assumes "\<And>\<tau>. \<tau> \<in> set \<tau>s \<Longrightarrow> t \<cdot> \<tau> = t" 
  shows "t \<cdot> (compose \<tau>s) = t" 
  using assms by(induct \<tau>s) simp_all

lemma subst_compose_distinct_vars:
  assumes "\<sigma> = compose \<tau>s" and part:"is_partition (map vars_subst \<tau>s)" 
    and \<tau>i:"\<tau>i \<in> set \<tau>s" and s:"\<tau>i x = s" "s \<noteq> Var x" 
  shows "\<sigma> x = s" 
proof-
  from \<tau>i obtain i where i:"i < length \<tau>s" "\<tau>s ! i = \<tau>i"
    by (metis in_set_idx) 
  then have \<tau>s:"\<tau>s = (take i \<tau>s) @ \<tau>i # (drop (Suc i ) \<tau>s)"
    using id_take_nth_drop by blast 
  from s have x_vars_subst:"x \<in> vars_subst \<tau>i"
    by (metis fun_upd_same fun_upd_triv subst_apply_term_empty subst_compose vars_subst_compose_update) 
  {fix j assume "j < i" 
    with part i x_vars_subst have "x \<notin> vars_subst (\<tau>s ! j)" 
      unfolding is_partition_alt is_partition_alt_def
      by (metis (no_types, lifting) Int_iff dual_order.strict_trans equals0D is_partition_def length_map nth_map part) 
    then have "(\<tau>s ! j) x = Var x" 
      unfolding vars_subst_def by (meson UnI1 notin_subst_domain_imp_Var)
  }
  then have take_i_\<tau>s:"compose (take i \<tau>s) x = Var x"
    using subst_compose_id[of "take i \<tau>s" "Var x"] using in_set_idx by force
  {fix y assume "y \<in> vars_term s" 
    with s have y_vars_subst:"y \<in> vars_subst \<tau>i" 
      unfolding vars_subst_def by (metis UnI2 Union_iff image_eqI notin_subst_domain_imp_Var subst_range.simps)
    {fix j assume "i < j" "j < length \<tau>s" 
      with part i y_vars_subst have "y \<notin> vars_subst (\<tau>s ! j)" 
        unfolding is_partition_alt is_partition_alt_def 
        by (metis (no_types, lifting) Int_iff equals0D is_partition_def length_map nth_map part) 
      then have "(\<tau>s ! j) y = Var y" 
        unfolding vars_subst_def by (meson UnI1 notin_subst_domain_imp_Var)
    }
    then have "compose (drop (Suc i) \<tau>s) y = Var y"
      using subst_compose_id[of "drop (Suc i) \<tau>s" "Var y"] using in_set_idx by force
  }
  then have "s \<cdot> (compose (drop (Suc i) \<tau>s)) = s"
    by (simp add: term_subst_eq) 
  with take_i_\<tau>s s(1) i show ?thesis
    by (metis \<tau>s assms(1) compose_append compose_simps(3) eval_term.simps(1) subst_compose) 
qed

lemma subst_id_compose:
  assumes "\<sigma> = compose \<tau>s" and part:"is_partition (map vars_subst \<tau>s)" 
    and "t \<cdot> \<sigma> = t" 
    and "\<tau> \<in> set \<tau>s"
  shows "t \<cdot> \<tau> = t"
  using assms subst_compose_distinct_vars by (metis (full_types) subst_apply_term_empty term_subst_eq_conv) 

lemma compose_subst_of:
  assumes "set ss = \<Union> (set ` set ss')"
    and "is_partition (map (vars_term \<circ> snd) ss)" and "distinct (map fst ss)" 
    and "set (map fst ss) \<inter> \<Union> (set (map (vars_term \<circ> snd) ss)) = {}"
    and "is_partition (map vars_subst (map subst_of ss'))"
  shows "subst_of ss = compose (map subst_of ss')" (is "?\<sigma> = ?\<tau>") 
proof
  fix x 
  show "?\<sigma> x = ?\<tau> x" proof(cases "x \<in> set (map fst ss)")
    case True
    then obtain s where s:"(x, s) \<in> set ss"
      by fastforce 
    then have \<sigma>_x:"?\<sigma> x = s" 
      using assms(3) by (smt (verit) UN_I assms(4) case_prodI2 disjoint_iff eq_key_imp_eq_value list.set_map o_apply prod.sel(2) subst_of_apply) 
    from s have s_x:"s \<noteq> Var x" 
      using assms(4) by fastforce 
    from s obtain ssi where ssi:"(x, s) \<in> set ssi" "ssi \<in> set ss'"
      using assms(1) by auto
    then have "subst_of ssi x = s"
      using assms(1,3,4) by (smt (verit, ccfv_threshold) UN_I case_prodI2 disjoint_iff eq_key_imp_eq_value image_iff list.set_map o_apply snd_conv subst_of_apply)
    with assms(5) have "?\<tau> x = s" 
      using subst_compose_distinct_vars ssi(2) s_x by (smt (verit, del_insts) in_set_idx length_map nth_map nth_mem) 
    with \<sigma>_x show ?thesis by simp
  next
    case False
    then have \<sigma>_x:"?\<sigma> x = Var x"
      by (simp add: not_elem_subst_of)  
    {fix ssi assume "ssi \<in> set ss'" 
      with False assms(1) have "x \<notin> set (map fst ssi)"
        by auto 
      then have "(subst_of ssi) x = Var x"
        by (simp add: not_elem_subst_of)  
    }
    then have "?\<tau> x = Var x" 
      using subst_compose_id by (smt (verit, ccfv_SIG) eval_term.simps(1) image_iff list.set_map)
    with \<sigma>_x show ?thesis by simp
  qed
qed

lemma linear_term_decompose_subst_id:
  assumes lin:"linear_term (Fun f ss)" "linear_term (Fun g ts)"
    and disj:"vars_term (Fun f ss) \<inter> vars_term (Fun g ts) = {}"
    and "decompose (Fun f ss) (Fun g ts) = Some ds"
    and i:"i < length ds" and \<sigma>:"\<sigma> = linear_unifier (fst (ds!i)) (snd (ds!i))" 
    and j:"j < length ds" "j \<noteq> i"
  shows "fst (ds!j) \<cdot> \<sigma> = fst (ds!j) \<and> snd (ds!j) \<cdot> \<sigma> = snd (ds!j)"
proof- 
  from assms have zip:"ds = zip ss ts" and l:"length ss = length ts"
    using decompose_Some by blast+
  from i j obtain si ti where s_t_i:"ds ! i = (si, ti)" "ss ! i = si" "ts ! i = ti"
    using l zip by force 
  from j obtain sj tj where s_t_j:"ds ! j = (sj, tj)" "ss ! j = sj" "ts ! j = tj"
    using l zip by force 
  have "vars_term sj \<inter> vars_term ti = {}"
    using i j s_t_i s_t_j disj l zip by fastforce 
  moreover have "vars_term sj \<inter> vars_term si = {}" 
    using lin(1) s_t_i s_t_j i j var_in_linear_args
    by (metis Int_emptyI l length_map map_fst_zip zip)
  moreover have "vars_term tj \<inter> vars_term ti = {}"
    using lin(2) s_t_i s_t_j i j l var_in_linear_args 
    by (metis Int_emptyI l length_map map_fst_zip zip)
  moreover have "vars_term tj \<inter> vars_term si = {}" 
    using i j s_t_i s_t_j disj l zip by fastforce 
  moreover from \<sigma> s_t_i have "vars_subst \<sigma> \<subseteq> vars_term si \<union> vars_term ti"
    by (metis fst_conv snd_conv vars_subst_linear_unifier)  
  ultimately show ?thesis 
    unfolding s_t_i s_t_j fst_conv snd_conv
    by (metis inf_sup_distrib1 subst_apply_term_ident sup.absorb_iff2 sup_bot.neutr_eq_iff vars_subst_def) 
qed

lemma linear_unifier_decompose:
  assumes "linear_term (Fun f ss)" "linear_term (Fun g ts)" 
    and disj:"vars_term (Fun f ss) \<inter> vars_term (Fun g ts) = {}"
    and ds:"decompose (Fun f ss) (Fun g ts) = Some ds"
  shows "linear_unifier (Fun f ss) (Fun g ts) = compose (map (\<lambda>(s,t). linear_unifier s t) ds)" 
proof-
  let ?ls="left_substs (Fun f ss) (Fun g ts)" and ?rs="right_substs (Fun f ss) (Fun g ts)"
  have left:"set ?ls = (\<Union>(s, t)\<in>set ds. set (left_substs s t))" 
    using decompose_left_substs[OF ds] by auto
  have right:"set ?rs = (\<Union>(s, t)\<in>set ds. set (right_substs s t))" 
    using decompose_right_substs[OF ds] by auto
  from left right have sets:"set (?ls @ ?rs) = \<Union> (set ` set (map (\<lambda>(s, t). left_substs s t @ right_substs s t) ds))" 
    by auto
  {fix l assume "l \<in> (set (map (vars_term \<circ> snd) ?ls))"
    then obtain t' where "t' \<in> set (map snd ?ls)" and "vars_term t' = l"
      by auto  
    then have "l \<subseteq> vars_term (Fun g ts)" 
      using map_snd_left_substs by blast
  }
  then have 1:"\<Union> (set (map (vars_term \<circ> snd) ?ls)) \<subseteq> vars_term (Fun g ts)" 
    using Union_least by blast 
  {fix r assume "r \<in> (set (map (vars_term \<circ> snd) ?rs))"
    then obtain t' where "t' \<in> set (map snd ?rs)" and "vars_term t' = r"
      by auto  
    then have "r \<subseteq> vars_term (Fun f ss)" 
      using map_snd_right_substs by blast
  }
  then have 2:"\<Union> (set (map (vars_term \<circ> snd) ?rs)) \<subseteq> vars_term (Fun f ss)" 
    using Union_least by blast 
  have snd_disj:"\<Union> (set (map (vars_term \<circ> snd) ?ls)) \<inter> \<Union> (set (map (vars_term \<circ> snd) ?rs)) = {}"
    using 1 2 assms(3) by blast
  then have part:"is_partition (map (vars_term \<circ> snd) (?ls @ ?rs))"
    using is_partition_append[OF is_partition_map_snd_left_substs[OF assms(2,1)] is_partition_map_snd_right_substs[OF assms(2,1)]] 
    unfolding length_map map_append by (simp add: Union_disjoint)
  have dist:"distinct (map fst (?ls @ ?rs))"
    using distinct_append distinct_map_fst_left_substs[OF assms(1)] distinct_map_fst_right_substs[OF assms(2)] map_fst_left_substs map_fst_right_substs
    by (smt (verit, del_insts) disj inf.orderE inf_assoc inf_bot_right inf_left_commute map_append)
  have "set (map fst ?ls) \<inter> \<Union> (set (map (vars_term \<circ> snd) ?ls)) = {}"
    by (meson "1" disj disjoint_iff map_fst_left_substs subsetD) 
  moreover have "set (map fst ?ls) \<inter> \<Union> (set (map (vars_term \<circ> snd) ?rs)) = {}"
    using assms(1) distinct_fst_lsubsts_snd_rsubsts by blast
  moreover have "set (map fst ?rs) \<inter> \<Union> (set (map (vars_term \<circ> snd) ?rs)) = {}"
    by (meson "2" disj disjoint_iff map_fst_right_substs subsetD)
  moreover have "set (map fst ?rs) \<inter> \<Union> (set (map (vars_term \<circ> snd) ?ls)) = {}"
    using assms(2) distinct_fst_rsubsts_snd_lsubsts by blast 
  ultimately have disj:"set (map fst (?ls @ ?rs)) \<inter> \<Union> (set (map (vars_term \<circ> snd) (?ls @ ?rs))) = {}" 
    unfolding map_append set_append by (simp add: boolean_algebra.conj_disj_distrib boolean_algebra.conj_disj_distrib2)
  have part2:"is_partition (map vars_subst (map subst_of (map (\<lambda>(s, t). left_substs s t @ right_substs s t) ds)))" 
    using decompose_is_partition_vars_subst[OF assms(1,2,3,4)]
    by (metis (mono_tags, lifting) case_prod_beta length_map map_nth_eq_conv)  
  show ?thesis using compose_subst_of[OF sets part dist disj part2] 
    by (smt (verit, del_insts) case_prod_unfold length_map map_nth_eq_conv) 
qed

text\<open>Main lemma: for a list of unifiable terms that are linear and have distinct variables, 
 the unification algorithm yields the same result as composing the list of substitutions 
 obtained by @{const linear_unifier}.\<close>
lemma unify_linear_terms:
  assumes "unify es substs = Some res"
    and "compose (subst_of substs # (map (\<lambda>(s,t). linear_unifier s t) es)) = \<tau>"
    and "\<forall>t \<in> set (map fst es) \<union> set (map snd es). linear_term t"
    and "\<And>i j \<sigma>. i < j \<Longrightarrow> j < length es \<Longrightarrow> \<sigma> = linear_unifier (fst (es!i)) (snd (es!i)) \<Longrightarrow> 
          (fst (es!j)) \<cdot> \<sigma> = fst (es!j) \<and> (snd (es!j)) \<cdot> \<sigma> = snd (es!j)"
    and "\<And>i. i < length es \<Longrightarrow> vars_term (fst (es!i)) \<inter> vars_term (snd (es!i)) = {}"
  shows "subst_of res = \<tau>" 
  using assms proof(induct arbitrary: res substs \<tau> rule:unify.induct)
  case (2 f ss g ts E)
  from 2(2) obtain ds where ds':"decompose (Fun f ss) (Fun g ts) = Some ds" 
    unfolding unify.simps by fastforce 
  then have ds:"ds = zip ss ts" and l:"length ss = length ts"
    by fastforce+
  with 2(4) have "\<forall>t \<in> set (map fst ds). linear_term t" 
    using map_fst_zip by (metis (no_types, lifting) UnCI fst_conv linear_term.simps(2) list.set_intros(1) list.simps(9))
  moreover from 2(4) ds l have "\<forall>t \<in> set (map snd ds). linear_term t" 
    using map_snd_zip by (metis (no_types, lifting) UnCI linear_term.simps(2) list.set_intros(1) list.simps(9) snd_conv) 
  ultimately have lin:"\<forall>a\<in>set (map fst (ds @ E)) \<union> set (map snd (ds @ E)). linear_term a" 
    using 2(4) by (metis UnE UnI1 UnI2 list.set_intros(2) list.simps(9) map_append set_append) 
  have lin_f_g:"linear_term (Fun f ss)" "linear_term (Fun g ts)" 
    using 2(4) by auto
  from 2(6) have vars:"vars_term (Fun f ss) \<inter> vars_term (Fun g ts) = {}"
    by fastforce 
  from ds' 2(2) have unif:"unify (ds @ E) substs = Some res"
    by auto 
  have "compose (map (\<lambda>a. case a of (s, t) \<Rightarrow> linear_unifier s t) ds) = linear_unifier (Fun f ss) (Fun g ts)" 
    using linear_unifier_decompose[OF lin_f_g vars ds'] by fastforce
  then have \<tau>2:"compose (subst_of substs # map (\<lambda>a. case a of (s, t) \<Rightarrow> linear_unifier s t) (ds @ E)) = \<tau>" 
    using 2(3) compose_append by simp
  {fix i j \<sigma> assume i:"i < j" and j:"j < length (ds @ E)" and \<sigma>:"\<sigma> = linear_unifier (fst ((ds @ E) ! i)) (snd ((ds @ E) ! i))"
    have "fst ((ds @ E) ! j) \<cdot> \<sigma> = fst ((ds @ E) ! j) \<and> snd ((ds @ E) ! j) \<cdot> \<sigma> = snd ((ds @ E) ! j)"
    proof(cases "i < length ds")
      case True
      then have \<sigma>:"\<sigma> = linear_unifier (fst (ds ! i)) (snd (ds ! i))"
        by (simp add: \<sigma> dual_order.strict_trans i nth_append)
      show ?thesis proof(cases "j < length ds")
        case True
        have lin:"linear_term (Fun f ss)" "linear_term (Fun g ts)"
          using 2(4) by simp+
        show ?thesis 
          using linear_term_decompose_subst_id[OF lin vars ds' \<open>i < length ds\<close> \<sigma> True] i True
          by (simp add: j nat_neq_iff nth_append)
      next
        case False
        let ?j'="j - length ds"
        let ?\<tau>="linear_unifier (Fun f ss) (Fun g ts)" 
        from False j have "?j' < length E" 
          by fastforce
        then have fst:"fst (E ! ?j') \<cdot> ?\<tau> = fst (E ! ?j')" and snd:"snd (E ! ?j') \<cdot> ?\<tau> = snd (E ! ?j')" 
          using 2(5) by force+
        have "fst (E ! ?j') \<cdot> \<sigma> = fst (E ! ?j')" 
          using subst_id_compose[OF linear_unifier_decompose[OF lin_f_g vars ds'] decompose_is_partition_vars_subst[OF lin_f_g vars ds']]
          by (smt (verit, best) True \<sigma> ds fst in_set_conv_nth l length_map map2_map_map map_fst_zip map_snd_zip nth_map) 
        moreover have "snd (E ! ?j') \<cdot> \<sigma> = snd (E ! ?j')" 
          using subst_id_compose[OF linear_unifier_decompose[OF lin_f_g vars ds'] decompose_is_partition_vars_subst[OF lin_f_g vars ds']] 
          by (smt (verit, best) True \<sigma> ds snd in_set_conv_nth l length_map map2_map_map map_fst_zip map_snd_zip nth_map) 
        ultimately show ?thesis
          by (simp add: False nth_append)
      qed
    next
      case False
      let ?i'="i - length ds"
      have i':"?i' < length E"
        using False i j by force 
      from \<sigma> have \<sigma>':"\<sigma> = linear_unifier (fst (E ! ?i')) (snd (E ! ?i'))"
        by (simp add: False nth_append) 
      let ?j'="j - length ds"
      from False i j have "?i' < ?j'" 
        by simp
      moreover with j have "?j' < length E" 
        by fastforce
      ultimately show ?thesis
        using 2(5) i' \<sigma>' by (smt (verit, best) length_nth_simps(2) nat_diff_split not_less_eq not_less_zero nth_Cons_Suc nth_append) 
    qed
  }
  moreover 
  { fix i assume i:"i < length (ds @ E)" 
    have "vars_term (fst ((ds @ E) ! i)) \<inter> vars_term (snd ((ds @ E) ! i)) = {}" 
    proof(cases "i < length ds")
      case True
      with ds have "vars_term (fst (ds!i)) \<subseteq> vars_term (Fun f ss)"
        using nth_mem by auto 
      moreover from True ds have "vars_term (snd (ds!i)) \<subseteq> vars_term (Fun g ts)"
        using nth_mem by auto 
      ultimately show ?thesis 
        using 2(6) True by (metis Int_mono bot.extremum_uniqueI nth_append vars)
    next
      case False
      let ?i'="i - length ds"
      have i':"?i' < length E"
        using False i by force 
      with 2(6) have "vars_term (fst (E ! ?i')) \<inter> vars_term (snd (E ! ?i')) = {}"
        by force 
      then show ?thesis
        by (simp add: False nth_append)  
    qed
  }
  ultimately show ?case
    using 2(1)[OF ds' unif \<tau>2 lin] by blast
next
  case (3 x t E)
  show ?case proof(cases "t = Var x")
    case True
    from 3(3) have unif:"unify E substs = Some res" 
      unfolding True unify.simps by simp
    from 3(4) have \<tau>2:"compose (subst_of substs # map (\<lambda>a. case a of (s, t) \<Rightarrow> linear_unifier s t) E) = \<tau>"
      unfolding True append_Cons list.map compose_simps using linear_unifier_same by (metis Var_subst_compose old.prod.case)
    from 3(5) have lin:"\<forall>a\<in>set (map fst E) \<union> set (map snd E). linear_term a"
      by simp 
    from 3(6) have "\<And>i \<sigma>. i < length E \<Longrightarrow> \<sigma> = linear_unifier (fst (E ! i)) (snd (E ! i)) \<Longrightarrow>
            (\<forall>j<length E. i < j \<longrightarrow> fst (E ! j) \<cdot> \<sigma> = fst (E ! j) \<and> snd (E ! j) \<cdot> \<sigma> = snd (E ! j))"
      by (metis length_nth_simps(2) not_less_eq nth_Cons_Suc)
    moreover have "(\<And>i. i < length E \<Longrightarrow> vars_term (fst (E ! i)) \<inter> vars_term (snd (E ! i)) = {})" 
      using 3(7) by fastforce 
    ultimately show ?thesis using 3(1)[OF True unif \<tau>2 lin] by simp
  next
    case False
    with 3(3) have x:"x \<notin> vars_term t"
      by fastforce
    with 3(3) False have unif:"unify (subst_list (subst x t) E) ((x, t) # substs) = Some res"
      by simp
    let ?\<sigma>="(subst x t)"
    have \<sigma>:"linear_unifier (Var x) t = ?\<sigma>" 
      using linear_unifier_var1 by simp
    from 3(7) have subst_list:"subst_list (subst x t) E = E" 
    proof-
      {fix j assume "j < length E" 
        then have j:"Suc j < length ((Var x, t) # E)" 
          by simp
        with 3(6)[of 0 "Suc j" ?\<sigma>] \<sigma> have "fst (E ! j) \<cdot> ?\<sigma> = fst (E ! j) \<and> snd (E ! j) \<cdot> ?\<sigma> = snd (E ! j)"
          by (metis fst_conv length_nth_simps(2) nth_Cons_0 nth_Cons_Suc snd_conv zero_less_Suc)  
      }
      then show ?thesis 
        unfolding subst_list_def by (simp add: map_nth_eq_conv) 
    qed
    have \<tau>2:"compose (subst_of ((x, t) # substs) # map (\<lambda>a. case a of (s, t) \<Rightarrow> linear_unifier s t) (subst_list (subst x t) E)) = \<tau>" 
      using 3(4) unfolding subst_list list.map prod.case \<sigma> subst_of_simps(3) compose_append fst_conv snd_conv compose_simps(1,3)
      using subst_compose_assoc by blast
    from 3(5) have lin:"\<forall>a\<in>set (map fst (subst_list (subst x t) E)) \<union> set (map snd (subst_list (subst x t) E)). linear_term a" 
      unfolding subst_list by simp
    {fix i j \<sigma> assume i:"i < j" and j:"j < length E" and \<sigma>'':"\<sigma> = linear_unifier (fst (E ! i)) (snd (E ! i))" 
      with 3(6) have 1:" fst (E ! j) \<cdot> \<sigma> = fst (E ! j) \<and> snd (E ! j) \<cdot> \<sigma> = snd (E ! j)"
        by (metis length_nth_simps(2) not_less_eq nth_Cons_Suc) 
    }
    moreover have "(\<And>i. i < length E \<Longrightarrow> vars_term (fst (E ! i)) \<inter> vars_term (snd (E ! i)) = {})" 
      using 3(7) by fastforce 
    ultimately show ?thesis 
      using 3(2)[OF False x unif \<tau>2 lin] 3(7) unfolding subst_list subst_of_simps(3) by simp
  qed
next
  case (4 f ts x E)
  from 4(2) have x:"x \<notin> vars_term (Fun f ts)"
    by fastforce 
  with 4(2) have unif:"unify (subst_list (subst x (Fun f ts)) E) ((x, Fun f ts) # substs) = Some res" 
    by auto
  let ?\<sigma>="(subst x (Fun f ts))"
  have \<sigma>:"linear_unifier (Fun f ts) (Var x)  = ?\<sigma>" 
    using linear_unifier_var2 by simp
  have subst_list:"subst_list (subst x (Fun f ts)) E = E"
  proof-
    {fix j assume "j < length E" 
      then have "Suc j < length ((Fun f ts, Var x) # E)" 
        by simp
      with 4(5) \<sigma> have "fst (E ! j) \<cdot> ?\<sigma> = fst (E ! j) \<and> snd (E ! j) \<cdot> ?\<sigma> = snd (E ! j)"
        by (metis fst_conv length_nth_simps(2) nth_Cons_0 nth_Cons_Suc snd_conv zero_less_Suc)  
    }
    then show ?thesis 
      unfolding subst_list_def by (simp add: map_nth_eq_conv) 
  qed
  have \<tau>2:"compose (subst_of ((x, Fun f ts) # substs) # map (\<lambda>a. case a of (s, t) \<Rightarrow> linear_unifier s t) (subst_list (subst x (Fun f ts)) E)) = \<tau>"
    using 4(3) unfolding subst_list list.map prod.case \<sigma> subst_of_simps(3) compose_append fst_conv snd_conv compose_simps(1,3) by (simp add: subst_compose_assoc)
  from 4(4) have lin:"\<forall>a\<in>set (map fst (subst_list (subst x (Fun f ts)) E)) \<union> set (map snd (subst_list (subst x (Fun f ts)) E)). linear_term a" 
    unfolding subst_list by simp 
  {fix i j \<sigma> assume i:"i < j" and j:"j < length E" and \<sigma>'':"\<sigma> = linear_unifier (fst (E ! i)) (snd (E ! i))" 
    with 4(5) have 1:"fst (E ! j) \<cdot> \<sigma> = fst (E ! j) \<and> snd (E ! j) \<cdot> \<sigma> = snd (E ! j)"
      by (metis length_nth_simps(2) not_less_eq nth_Cons_Suc)
  }
  moreover have "(\<And>i. i < length E \<Longrightarrow> vars_term (fst (E ! i)) \<inter> vars_term (snd (E ! i)) = {})" 
    using 4(6) by fastforce 
  ultimately show ?case 
    using 4(1)[OF x unif \<tau>2 lin] 4(6) unfolding subst_list by simp
qed auto

lemma mgu_distinct_vars_term_list:
  assumes unif:"unifiers {(s, t)} \<noteq> {}"
    and distinct:"distinct ((vars_term_list s) @ (vars_term_list t))"
  shows "mgu s t = Some (linear_unifier s t)"
proof-
  let ?tau="linear_unifier s t"
  from unif have "mgu s t \<noteq> None"
    by (meson mgu_complete) 
  then obtain us where us:"unify [(s, t)] [] = Some us" 
    unfolding mgu_def by fastforce
  have tau:"compose (subst_of [] # map (\<lambda>(s, t). linear_unifier s t) [(s, t)]) = ?tau"
    by simp
  have lin:"\<forall>t\<in>set (map fst [(s, t)]) \<union> set (map snd [(s, t)]). linear_term t" 
    using distinct distinct_vars_linear_term by auto  
  have "vars_term s \<inter> vars_term t = {}" 
    using distinct by simp
  then have "subst_of us = ?tau" 
    using unify_linear_terms[OF us tau lin] by simp
  then show ?thesis 
    using us by (simp add: mgu_def) 
qed

end