section\<open>Orthogonal Proof Terms\<close>

theory Orthogonal_PT
imports
  Residual_Join_Deletion
begin

inductive orthogonal::"('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm \<Rightarrow> bool" (infixl "\<bottom>\<^sub>p" 50)
  where
  "Var x \<bottom>\<^sub>p Var x"
| "length As = length Bs \<Longrightarrow> \<forall> i < length As. As!i \<bottom>\<^sub>p Bs!i \<Longrightarrow> Fun f As \<bottom>\<^sub>p Fun f Bs"
| "length As = length Bs \<Longrightarrow> \<forall>(a,b) \<in> set(zip As Bs). a \<bottom>\<^sub>p b \<Longrightarrow> (Prule \<alpha> As) \<bottom>\<^sub>p (to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>"
| "length As = length Bs \<Longrightarrow> \<forall>(a,b) \<in> set(zip As Bs). a \<bottom>\<^sub>p b \<Longrightarrow> (to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha> \<bottom>\<^sub>p (Prule \<alpha> Bs)"
lemmas orthogonal.intros[intro]

lemma orth_symp: "symp (\<bottom>\<^sub>p)"
proof
  {fix A B::"('f, 'v) pterm" assume "A \<bottom>\<^sub>p B"
    then show "B \<bottom>\<^sub>p A" proof(induct)
      case (3 As Bs \<alpha>)
      then show ?case using orthogonal.intros(4)[where \<alpha>=\<alpha> and Bs=As and As=Bs]
        using zip_symm by fastforce
    next
      case (4 As Bs \<alpha>)
      then show ?case using orthogonal.intros(3)[where \<alpha>=\<alpha> and As=Bs and Bs=As]
        using zip_symm by fastforce
    qed (simp_all add:orthogonal.intros)
  }
qed

lemma equal_imp_orthogonal:
  shows "A \<bottom>\<^sub>p A" 
  by(induct A) (simp_all add: orthogonal.intros) 

lemma source_orthogonal:
  assumes "source A = t"
  shows "A \<bottom>\<^sub>p to_pterm t"
  using assms proof(induct A arbitrary:t)
  case (Prule \<alpha> As)
  then have t:"to_pterm t = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>map (to_pterm \<circ> source) As\<rangle>\<^sub>\<alpha>"
    by (metis fun_mk_subst list.map_comp source.simps(3) to_pterm.simps(1) to_pterm_subst)
  from Prule(1) have "\<forall>(a,b) \<in> set (zip As (map (to_pterm \<circ> source) As)). a \<bottom>\<^sub>p b"
    by (metis (mono_tags, lifting) case_prod_beta' comp_def in_set_zip nth_map zip_fst)
  with t show ?case
    using orthogonal.intros(3) by (metis length_map)
qed (simp_all add:orthogonal.intros)

lemma orth_imp_co_initial:
  assumes "A \<bottom>\<^sub>p B"
  shows "co_initial A B"
  using assms proof(induct rule: orthogonal.induct)
  case (2 As Bs f)
  show ?case proof(cases f)
    case (Inr g)
    with 2 show ?thesis unfolding Inr
      by (simp add: nth_map_conv)
  next
    case (Inl \<alpha>)
    with 2 show ?thesis unfolding Inl
      by (metis nth_map_conv source.simps(3))
  qed
next
  case (3 As Bs \<alpha>)
  then have l:"length (zip As Bs) = length As"
    by simp
  with 3 have IH:"\<forall>i < length As. source (As!i) = source (Bs!i)"
    by (metis (mono_tags, lifting) case_prod_conv nth_mem nth_zip)
  have src:"source ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) = (lhs \<alpha>) \<cdot> \<langle>map source Bs\<rangle>\<^sub>\<alpha>"
    by (simp add: source_apply_subst)
  from 3(1) l IH show ?case unfolding src source.simps
    by (metis nth_map_conv)
next
  case (4 As Bs \<alpha>)
  then have l:"length (zip As Bs) = length As"
    by simp
  with 4 have IH:"\<forall>i < length As. source (As!i) = source (Bs!i)"
    by (metis (mono_tags, lifting) case_prod_conv nth_mem nth_zip)
  have src:"source ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) = (lhs \<alpha>) \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>"
    by (simp add: source_apply_subst)
  from 4(1) l IH show ?case unfolding src source.simps
    by (metis nth_map_conv)
qed simp

text\<open>If two proof terms are orthogonal then residual and join are well-defined.\<close>
lemma orth_imp_residual_defined:
  assumes varcond:"\<And>l r. (l, r) \<in> R \<Longrightarrow> is_Fun l" "\<And>l r. (l, r) \<in> S \<Longrightarrow> is_Fun l"
    and "A \<bottom>\<^sub>p B"
    and "A \<in> wf_pterm R" and "B \<in> wf_pterm S"
  shows "A re B \<noteq> None"
  using assms(3-) proof(induct)
  case (2 As Bs f)
  from 2(3) have wellAs:"\<forall>a \<in> set As. a \<in> wf_pterm R"
    by blast
  from 2(4) have wellBs:"\<forall>b \<in> set Bs. b \<in> wf_pterm S"
    by blast
  from 2(1,2) wellAs wellBs  have c:"\<forall>i < length As. (\<exists>C. As!i re Bs!i = Some C)"
    by auto
  from 2(1) have l:"length As = length (map2 (re) As Bs)"
    by simp
  from 2(1) have "\<forall>i < length As. As!i re Bs!i = (map2 (re) As Bs)!i"
    by simp
  with c obtain Cs where "\<forall>i < length As. As!i re Bs!i = Some (Cs!i)" and "length Cs = length As"
    using exists_some_list l by (metis (no_types, lifting))
  with 2 have *:"those (map2 (re) As Bs) = Some Cs"
    by (simp add: those_some)
  show ?case proof(cases f)
    case (Inr g)
    show ?thesis unfolding Inr residual.simps 2(1) * by simp
  next
    case (Inl \<alpha>)
    show ?thesis unfolding Inl residual.simps 2(1) * by simp
  qed
next
  case (3 As Bs \<alpha>)
  from 3(3) varcond obtain g ts where g:"lhs \<alpha> = Fun g ts"
    by (metis Inl_inject is_Fun_Fun_conv sum.simps(4) term.distinct(1) term.sel(2) wf_pterm.cases)
  then have *:"to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha> = Pfun g (map (\<lambda>t. t \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) (map to_pterm ts))"
    by simp
  from 3(3) have l1:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  from 3(3) have wellAs:"\<forall>a \<in> set As. a \<in> wf_pterm R"
    by blast
  from 3(1,4) l1 have wellBs:"\<forall>b \<in> set Bs. b \<in> wf_pterm S"
    by (simp add: lhs_subst_args_wf_pterm)
  from 3(1) have l2:"length (zip As Bs) = length As"
    by simp
  with 3(1,2) wellAs wellBs have "\<forall>i < length As. As ! i re Bs ! i \<noteq> None"
    by (metis (mono_tags, lifting) case_prod_conv nth_mem nth_zip)
  then have c:"\<forall>i < length As. (\<exists>C. As!i re Bs!i = Some C)"
    by blast
  from 3(1) have "\<forall>i < length As. As!i re Bs!i = (map2 (re) As Bs)!i"
    by simp
  with c obtain Cs where "\<forall>i < length As. As!i re Bs!i = Some (Cs!i)" and "length Cs = length As"
    using exists_some_list l2 by (metis (no_types, lifting) length_map)
  with 3 have cs:"those (map2 (re) As Bs) = Some Cs"
    by (simp add: those_some)
  have bs:"match (to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) (to_pterm (lhs \<alpha>)) = Some (\<langle>Bs\<rangle>\<^sub>\<alpha>)"
    using lhs_subst_trivial by blast
  then have "(map (\<langle>Bs\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>)) = Bs"
    using 3(1) l1 apply_lhs_subst_var_rule by force
  then show ?case using residual.simps(5) using bs cs g unfolding *
    by simp
next
  case (4 As Bs \<alpha>)
  from 4(4) varcond obtain g ts where g:"lhs \<alpha> = Fun g ts"
    by (metis Inl_inject is_Fun_Fun_conv sum.simps(4) term.distinct(1) term.sel(2) wf_pterm.cases)
  then have *:"to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha> = Pfun g (map (\<lambda>t. t \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) (map to_pterm ts))"
    by simp
  from 4(4) have l1:"length Bs = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  from 4(1,3) l1 have wellAs:"\<forall>a \<in> set As. a \<in> wf_pterm R"
    by (simp add: lhs_subst_args_wf_pterm)
  from 4(4)  have wellBs:"\<forall>b \<in> set Bs. b \<in> wf_pterm S"
    by blast
  from 4(1) have l2:"length (zip As Bs) = length As"
    by simp
  with 4(1,2) wellAs wellBs have "\<forall>i < length As. As ! i re Bs ! i \<noteq> None"
    by (metis (mono_tags, lifting) case_prod_conv nth_mem nth_zip)
  then have c:"\<forall>i < length As. (\<exists>C. As!i re Bs!i = Some C)"
    by blast
  from 4(1) have "\<forall>i < length As. As!i re Bs!i = (map2 (re) As Bs)!i"
    by simp
  with c obtain Cs where "\<forall>i < length As. As!i re Bs!i = Some (Cs!i)" and "length Cs = length As"
    using exists_some_list l2 by (metis (no_types, lifting) length_map)
  with 4 have cs:"those (map2 (re) As Bs) = Some Cs"
    by (simp add: those_some)
  have bs:"match (to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) (to_pterm (lhs \<alpha>)) = Some (\<langle>As\<rangle>\<^sub>\<alpha>)"
    using lhs_subst_trivial by blast
  have "(map (\<langle>As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>)) = As"
    using 4(1) l1 apply_lhs_subst_var_rule by force
  then show ?case using residual.simps(7) using bs cs g unfolding *
    by simp
qed simp

(*The proof is almost word for word copied from orth_imp_residual_defined. Can this be combined?*)
lemma orth_imp_join_defined:
  assumes varcond:"\<And>l r. (l, r) \<in> R \<Longrightarrow> is_Fun l"
    and "A \<bottom>\<^sub>p B"
    and "A \<in> wf_pterm R" and "B \<in> wf_pterm R"
  shows "A \<squnion> B \<noteq> None"
  using assms(2-) proof(induct)
  case (2 As Bs f)
  from 2(3) have wellAs:"\<forall>a \<in> set As. a \<in> wf_pterm R"
    by blast
  from 2(4) have wellBs:"\<forall>b \<in> set Bs. b \<in> wf_pterm R"
    by blast
  from 2(1,2) wellAs wellBs  have c:"\<forall>i < length As. (\<exists>C. As!i \<squnion> Bs!i = Some C)"
    by auto
  from 2(1) have l:"length As = length (map2 (\<squnion>) As Bs)"
    by simp
  from 2(1) have "\<forall>i < length As. As!i \<squnion> Bs!i = (map2 (\<squnion>) As Bs)!i"
    by simp
  with c obtain Cs where "\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)" and "length Cs = length As"
    using exists_some_list l by (metis (no_types, lifting))
  with 2 have *:"those (map2 (\<squnion>) As Bs) = Some Cs"
    by (simp add: those_some)
  show ?case proof(cases f)
    case (Inr g)
    show ?thesis unfolding Inr join.simps 2(1) * by simp
  next
    case (Inl \<alpha>)
    show ?thesis unfolding Inl join.simps 2(1) * by simp
  qed
next
  case (3 As Bs \<alpha>)
  from 3(3) varcond obtain g ts where g:"lhs \<alpha> = Fun g ts"
    by (metis Inl_inject is_Fun_Fun_conv sum.simps(4) term.distinct(1) term.sel(2) wf_pterm.cases)
  then have *:"to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha> = Pfun g (map (\<lambda>t. t \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) (map to_pterm ts))"
    by simp
  from 3(3) have l1:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  from 3(3) have wellAs:"\<forall>a \<in> set As. a \<in> wf_pterm R"
    by blast
  from 3(1,4) l1 have wellBs:"\<forall>b \<in> set Bs. b \<in> wf_pterm R"
    by (simp add: lhs_subst_args_wf_pterm)
  from 3(1) have l2:"length (zip As Bs) = length As"
    by simp
  with 3(1,2) wellAs wellBs have "\<forall>i < length As. As ! i \<squnion> Bs ! i \<noteq> None"
    by (metis (mono_tags, lifting) case_prod_conv nth_mem nth_zip)
  then have c:"\<forall>i < length As. (\<exists>C. As!i \<squnion> Bs!i = Some C)"
    by blast
  from 3(1) have "\<forall>i < length As. As!i \<squnion> Bs!i = (map2 (\<squnion>) As Bs)!i"
    by simp
  with c obtain Cs where "\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)" and "length Cs = length As"
    using exists_some_list l2 by (metis (no_types, lifting) length_map)
  with 3 have cs:"those (map2 (\<squnion>) As Bs) = Some Cs"
    by (simp add: those_some)
  have bs:"match (to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) (to_pterm (lhs \<alpha>)) = Some (\<langle>Bs\<rangle>\<^sub>\<alpha>)"
    using lhs_subst_trivial by blast
  then have "(map (\<langle>Bs\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>)) = Bs"
    using 3(1) l1 apply_lhs_subst_var_rule by force
  then show ?case using residual.simps(5) using bs cs g unfolding *
    by simp
next
  case (4 As Bs \<alpha>)
  from 4(4) varcond obtain g ts where g:"lhs \<alpha> = Fun g ts"
    by (metis Inl_inject is_Fun_Fun_conv sum.simps(4) term.distinct(1) term.sel(2) wf_pterm.cases)
  then have *:"to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha> = Pfun g (map (\<lambda>t. t \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) (map to_pterm ts))"
    by simp
  from 4(4) have l1:"length Bs = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  from 4(1,3) l1 have wellAs:"\<forall>a \<in> set As. a \<in> wf_pterm R"
    by (simp add: lhs_subst_args_wf_pterm)
  from 4(4)  have wellBs:"\<forall>b \<in> set Bs. b \<in> wf_pterm R"
    by blast
  from 4(1) have l2:"length (zip As Bs) = length As"
    by simp
  with 4(1,2) wellAs wellBs have "\<forall>i < length As. As ! i \<squnion> Bs ! i \<noteq> None"
    by (metis (mono_tags, lifting) case_prod_conv nth_mem nth_zip)
  then have c:"\<forall>i < length As. (\<exists>C. As!i \<squnion> Bs!i = Some C)"
    by blast
  from 4(1) have "\<forall>i < length As. As!i \<squnion> Bs!i = (map2 (\<squnion>) As Bs)!i"
    by simp
  with c obtain Cs where "\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)" and "length Cs = length As"
    using exists_some_list l2 by (metis (no_types, lifting) length_map)
  with 4 have cs:"those (map2 (\<squnion>) As Bs) = Some Cs"
    by (simp add: those_some)
  have bs:"match (to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) (to_pterm (lhs \<alpha>)) = Some (\<langle>As\<rangle>\<^sub>\<alpha>)"
    using lhs_subst_trivial by blast
  have "(map (\<langle>As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>)) = As"
    using 4(1) l1 apply_lhs_subst_var_rule by force
  then show ?case using residual.simps(7) using bs cs g unfolding *
    by simp
qed simp

context no_var_lhs
begin
lemma orth_imp_residual_defined:
  assumes "A \<bottom>\<^sub>p B" and "A \<in> wf_pterm R" and "B \<in> wf_pterm R"
  shows "A re B \<noteq> None"
  using orth_imp_residual_defined assms no_var_lhs by fastforce 

lemma orth_imp_join_defined:
  assumes "A \<bottom>\<^sub>p B" and "A \<in> wf_pterm R" and "B \<in> wf_pterm R"
  shows "A \<squnion> B \<noteq> None"
  using orth_imp_join_defined assms no_var_lhs by fastforce 

lemma orthogonal_ctxt:
  assumes "C\<langle>A\<rangle> \<bottom>\<^sub>p C\<langle>B\<rangle>" "C \<in> wf_pterm_ctxt R"
  shows "A \<bottom>\<^sub>p B"
  using assms proof(induct C)
  case (Cfun f ss1 C ss2)
  from Cfun(2) have "\<forall>i<length (ss1 @ C\<langle>A\<rangle> # ss2). (ss1 @ C\<langle>A\<rangle> # ss2) ! i \<bottom>\<^sub>p (ss1 @ C\<langle>B\<rangle> # ss2) ! i"
    unfolding intp_actxt.simps using orthogonal.simps by (smt (verit) is_Prule.simps(1) is_Prule.simps(3) term.distinct(1) term.sel(4)) 
  then have "C\<langle>A\<rangle> \<bottom>\<^sub>p C\<langle>B\<rangle>"
    by (metis append.right_neutral length_append length_greater_0_conv length_nth_simps(1) list.discI nat_add_left_cancel_less nth_append_length) 
  with Cfun(1,3) show ?case by auto
next
  case (Crule \<alpha> ss1 C ss2)
  from Crule(3) obtain f ts where "lhs \<alpha> = Fun f ts" 
    using no_var_lhs by (smt (verit, del_insts) Inl_inject Inr_not_Inl case_prodD actxt.distinct(1) actxt.inject term.collapse(2) wf_pterm_ctxt.simps) 
  with Crule(2) have "\<forall>i<length (ss1 @ C\<langle>A\<rangle> # ss2). (ss1 @ C\<langle>A\<rangle> # ss2) ! i \<bottom>\<^sub>p (ss1 @ C\<langle>B\<rangle> # ss2) ! i"
    unfolding intp_actxt.simps using orthogonal.simps
    by (smt (verit, ccfv_threshold) Inl_inject Inr_not_Inl eval_term.simps(2) term.distinct(1) term.inject(2) to_pterm.simps(2))
  then have "C\<langle>A\<rangle> \<bottom>\<^sub>p C\<langle>B\<rangle>"
    by (metis intp_actxt.simps(2) hole_pos.simps(2) hole_pos_poss nth_append_length poss_Cons_poss term.sel(4)) 
  with Crule(1,3) show ?case by auto
qed simp

end

context left_lin_no_var_lhs
begin

lemma orthogonal_subst:
  assumes "A \<cdot> \<sigma> \<bottom>\<^sub>p B \<cdot> \<sigma>" "source A = source B" (*co-initial needed to ensure that A and B share the same variables*)
    and "A \<in> wf_pterm R" "B \<in> wf_pterm R"
  shows "A \<bottom>\<^sub>p B"
  using assms(3,4,1,2) proof(induct A  arbitrary:B rule:subterm_induct)
  case (subterm A)
  show ?case proof(cases A)
    case (Var x)
    with subterm no_var_lhs have "B = Var x"
      by (metis Inl_inject Inr_not_Inl case_prodD co_initial_Var is_VarI term.distinct(1) term.inject(2) wf_pterm.simps) 
    then show ?thesis
      unfolding Var by (simp add: orthogonal.intros(1))
  next
    case (Pfun f As)
    with subterm(5) show ?thesis proof(cases B)
      case (Pfun g Bs)
      from subterm(5) have f:"f = g"
        unfolding \<open>A = Pfun f As\<close> Pfun by simp
      from subterm(5) have l:"length As = length Bs"
        unfolding \<open>A = Pfun f As\<close> Pfun using map_eq_imp_length_eq by auto 
      {fix i assume i:"i < length As"
        with subterm(4) have "As!i \<cdot> \<sigma> \<bottom>\<^sub>p Bs!i \<cdot> \<sigma>" 
          unfolding \<open>A = Pfun f As\<close> Pfun eval_term.simps f
          by (smt (verit) is_Prule.simps(1) is_Prule.simps(3) length_map nth_map orthogonal.simps term.distinct(1) term.sel(4)) 
        moreover from i subterm(5) have "source (As!i) = source (Bs!i)" 
          unfolding \<open>A = Pfun f As\<close> Pfun eval_term.simps f by (simp add: map_equality_iff) 
        moreover from i l subterm(2,3) have "As!i \<in> wf_pterm R" "Bs!i \<in> wf_pterm R" 
          unfolding \<open>A = Pfun f As\<close> Pfun by auto
        moreover from i have "As!i \<lhd> A" 
          unfolding \<open>A = Pfun f As\<close> by simp
        ultimately have "As!i \<bottom>\<^sub>p Bs!i"
          using subterm(1) by simp
      }      
      with l show ?thesis 
        unfolding f \<open>A = Pfun f As\<close> Pfun by (simp add: orthogonal.intros(2))
    next
      case (Prule \<beta> Bs)
      with subterm(3) have lin:"linear_term (lhs \<beta>)"
        using left_lin left_linear_trs_def wf_pterm.cases by fastforce 
      from subterm(3) obtain g ts where lhs:"lhs \<beta> = Fun g ts" 
        unfolding Prule using no_var_lhs by (metis Inl_inject case_prodD is_FunE is_Prule.simps(1) is_Prule.simps(3) term.distinct(1) term.inject(2) wf_pterm.simps) 
      with subterm(4) obtain \<tau>1 where "A \<cdot> \<sigma> = to_pterm (lhs \<beta>) \<cdot> \<tau>1"
        unfolding Prule Pfun eval_term.simps using orthogonal.simps by (smt (verit, ccfv_SIG) Inl_inject Inr_not_Inl term.inject(2))
      with subterm(4,5) obtain \<tau> where \<tau>2:"A = to_pterm (lhs \<beta>) \<cdot> \<tau>"
        unfolding Prule Pfun source.simps using simple_pterm_match lin by (metis matches_iff source.simps(2)) 
      let ?As="map \<tau> (var_rule \<beta>)" 
      have l:"length Bs = length (var_rule \<beta>)"
        using Prule subterm.prems(2) wf_pterm.simps by fastforce 
      from \<tau>2 have A:"A = to_pterm (lhs \<beta>) \<cdot> \<langle>?As\<rangle>\<^sub>\<beta>"
        by (metis lhs_subst_var_rule set_vars_term_list subsetI vars_to_pterm)  
      {fix i assume i:"i < length Bs"
        have subt:"?As!i \<lhd> A" 
          using i l by (metis (no_types, lifting) \<tau>2 comp_apply lhs nth_map nth_mem set_remdups set_rev set_vars_term_list subst_image_subterm to_pterm.simps(2) vars_to_pterm)
        have wf:"?As!i \<in> wf_pterm R" 
          using i l by (metis A length_map lhs_subst_args_wf_pterm nth_mem subterm.prems(1))
        have l':"length (var_rule \<beta>) = length ?As" 
          by simp
        from subterm(4) A Prule lhs have orth:"?As!i \<cdot> \<sigma> \<bottom>\<^sub>p Bs!i \<cdot> \<sigma>" proof(cases)
          case (4 As' Bs' \<beta>')
          then have Bs':"Bs' = map (\<lambda>s. s \<cdot> \<sigma>) Bs" and \<beta>':"\<beta>' = \<beta>"
            unfolding Prule by simp_all
          have As':"As' = map (\<lambda>s. s \<cdot> \<sigma>) ?As" proof-
            have l'':"length As' = length ?As" using 4(3) l unfolding Bs' length_map by simp
            {fix j assume j:"j < length As'" and neq:"As'!j \<noteq> map (\<lambda>s. s \<cdot> \<sigma>) ?As ! j" 
              let ?x="var_rule \<beta>!j" 
              from j have x:"?x \<in> vars_term (lhs \<beta>)"
                by (metis comp_apply l' l'' nth_mem set_remdups set_rev set_vars_term_list) 
              then obtain p where p:"p \<in> poss (lhs \<beta>)" "lhs \<beta> |_p = Var ?x"
                by (meson vars_term_poss_subt_at) 
              from j have 1:"(\<langle>As'\<rangle>\<^sub>\<beta>') ?x = As'!j" 
                using \<beta>' l'' lhs_subst_var_i by force
              from j have 2:"(\<langle>map (\<lambda>s. s \<cdot> \<sigma>) ?As\<rangle>\<^sub>\<beta>) ?x = map (\<lambda>s. s \<cdot> \<sigma>) ?As ! j" 
                using lhs_subst_var_i by (metis l'' length_map)
              then have False using 4(1) 1 2 p unfolding A eval_lhs_subst[OF l'] \<beta>'
                by (smt (verit, del_insts) x neq set_vars_term_list term_subst_eq_rev vars_to_pterm)
            }
            then show ?thesis 
              using l'' by (metis (mono_tags, lifting) map_nth_eq_conv nth_map)
          qed
          have i':"i < length (zip (map (\<lambda>a. a \<cdot> \<sigma>) (map \<tau> (var_rule \<beta>))) (map (\<lambda>b. b \<cdot> \<sigma>) Bs))"
            using i l by simp 
          from 4(4) have "map (\<lambda>a. a \<cdot> \<sigma>) (map \<tau> (var_rule \<beta>)) ! i \<bottom>\<^sub>p map (\<lambda>b. b \<cdot> \<sigma>) Bs !i"
            unfolding As' Bs' using i' by (metis case_prodD i l length_map nth_mem nth_zip)
          then show ?thesis
            using i l by auto 
        qed simp_all
        have co_init:"source (?As!i) = source (Bs!i)" proof(rule ccontr)
          assume neq:"source (?As!i) \<noteq> source (Bs!i)"
          let ?x="var_rule \<beta>!i" 
          from i l have x:"?x \<in> vars_term (lhs \<beta>)"
            by (metis comp_apply nth_mem set_remdups set_rev set_vars_term_list) 
          then obtain p where p:"p \<in> poss (lhs \<beta>)" "lhs \<beta> |_p = Var ?x"
            by (meson vars_term_poss_subt_at) 
          from i have 1:"(\<langle>map source ?As\<rangle>\<^sub>\<beta>) ?x = source (?As!i)" 
            using l lhs_subst_var_i by (metis length_map nth_map)
          from i have 2:"(\<langle>map source Bs\<rangle>\<^sub>\<beta>) ?x = source (Bs!i)" 
            using l lhs_subst_var_i by (metis length_map nth_map)
          from subterm(5) show False using neq 1 2 p 
            unfolding Prule A source.simps source_apply_subst[OF to_pterm_wf_pterm[of "lhs \<beta>"]] source_to_pterm
            using term_subst_eq_rev x by fastforce
        qed
        from subterm(1) subt wf orth co_init have "?As!i \<bottom>\<^sub>p Bs!i" 
          using i subterm(3) unfolding Prule by (meson fun_well_arg nth_mem) 
      }
      then show ?thesis unfolding A Prule
        by (smt (verit, best) case_prodI2 in_set_idx l length_map length_zip min_less_iff_conj nth_zip orthogonal.intros(4) prod.sel(1) snd_conv)
    qed simp
  next
    case (Prule \<alpha> As)
    with subterm(2) have lin:"linear_term (lhs \<alpha>)" 
      using left_lin left_linear_trs_def wf_pterm.cases by fastforce 
    from subterm(2) obtain f ts where lhs:"lhs \<alpha> = Fun f ts"
      by (metis Inr_not_Inl Prule case_prodD is_FunE no_var_lhs sum.inject(1) term.distinct(1) term.inject(2) wf_pterm.simps) 
    with subterm(5) show ?thesis proof(cases B)
      case (Var x)
      then show ?thesis
        using source_orthogonal subterm.prems(4) by fastforce
    next
      case (Pfun g Bs) (*case is symmetric to above \<rightarrow> generalize and simplify*)
      with subterm(4) obtain \<tau>1 where "B \<cdot> \<sigma> = to_pterm (lhs \<alpha>) \<cdot> \<tau>1"
        unfolding Prule Pfun eval_term.simps using orthogonal.simps by (smt (verit, ccfv_SIG) Inl_inject Inr_not_Inl term.inject(2))
      with subterm(4,5) obtain \<tau> where \<tau>2:"B = to_pterm (lhs \<alpha>) \<cdot> \<tau>"
        unfolding Prule Pfun source.simps using simple_pterm_match lin by (metis matches_iff source.simps(2)) 
      let ?Bs="map \<tau> (var_rule \<alpha>)" 
      have l:"length As = length (var_rule \<alpha>)"
        using Prule subterm.prems(1) wf_pterm.simps by fastforce 
      from \<tau>2 have B:"B = to_pterm (lhs \<alpha>) \<cdot> \<langle>?Bs\<rangle>\<^sub>\<alpha>"
        by (metis lhs_subst_var_rule set_vars_term_list subsetI vars_to_pterm)  
      have l':"length (var_rule \<alpha>) = length ?Bs" 
        by simp
      {fix i assume i:"i < length As"
        from subterm(4) B Prule lhs have orth:"As!i \<cdot> \<sigma> \<bottom>\<^sub>p ?Bs!i \<cdot> \<sigma>" proof(cases)
          case (3 As' Bs' \<alpha>')
          then have As':"As' = map (\<lambda>s. s \<cdot> \<sigma>) As" and \<alpha>':"\<alpha>' = \<alpha>"
            unfolding Prule by simp_all
          have Bs':"Bs' = map (\<lambda>s. s \<cdot> \<sigma>) ?Bs" proof-
            have l'':"length Bs' = length ?Bs" using 3(3) l unfolding As' length_map by simp
            {fix j assume j:"j < length Bs'" and neq:"Bs'!j \<noteq> map (\<lambda>s. s \<cdot> \<sigma>) ?Bs ! j" 
              let ?x="var_rule \<alpha>!j" 
              from j have x:"?x \<in> vars_term (lhs \<alpha>)"
                by (metis comp_apply l'' length_map nth_mem set_remdups set_rev set_vars_term_list)
              then obtain p where p:"p \<in> poss (lhs \<alpha>)" "lhs \<alpha> |_p = Var ?x"
                by (meson vars_term_poss_subt_at) 
              from j have 1:"(\<langle>Bs'\<rangle>\<^sub>\<alpha>') ?x = Bs'!j" 
                using \<alpha>' l'' lhs_subst_var_i by force
              from j have 2:"(\<langle>map (\<lambda>s. s \<cdot> \<sigma>) ?Bs\<rangle>\<^sub>\<alpha>) ?x = map (\<lambda>s. s \<cdot> \<sigma>) ?Bs ! j" 
                using lhs_subst_var_i by (metis l'' length_map)
              then have False using 3(1) 1 2 p unfolding B eval_lhs_subst[OF l'] \<alpha>'
                by (smt (verit, ccfv_SIG) "3"(2) B \<alpha>' eval_lhs_subst l' map_eq_conv neq set_vars_term_list term_subst_eq_rev vars_to_pterm x)
            }
            then show ?thesis 
              using l'' by (metis (mono_tags, lifting) map_nth_eq_conv nth_map)
          qed
          have i':"i < length (zip (map (\<lambda>b. b \<cdot> \<sigma>) As) (map (\<lambda>a. a \<cdot> \<sigma>) (map \<tau> (var_rule \<alpha>))))"
            using i l by simp 
          from 3(4) have "map (\<lambda>b. b \<cdot> \<sigma>) As ! i \<bottom>\<^sub>p map (\<lambda>a. a \<cdot> \<sigma>) (map \<tau> (var_rule \<alpha>)) ! i "
            unfolding As' Bs' using i' by (metis case_prodD i l length_map nth_mem nth_zip)
          then show ?thesis
            using i l by auto 
        qed simp_all
        have co_init:"source (As!i) = source (?Bs!i)" proof(rule ccontr)
          assume neq:"source (As!i) \<noteq> source (?Bs!i)"
          let ?x="var_rule \<alpha>!i" 
          from i l have x:"?x \<in> vars_term (lhs \<alpha>)"
            by (metis comp_apply nth_mem set_remdups set_rev set_vars_term_list) 
          then obtain p where p:"p \<in> poss (lhs \<alpha>)" "lhs \<alpha> |_p = Var ?x"
            by (meson vars_term_poss_subt_at) 
          from i have 1:"(\<langle>map source ?Bs\<rangle>\<^sub>\<alpha>) ?x = source (?Bs!i)" 
            using l lhs_subst_var_i by (metis length_map nth_map)
          from i have 2:"(\<langle>map source As\<rangle>\<^sub>\<alpha>) ?x = source (As!i)" 
            using l lhs_subst_var_i by (metis length_map nth_map)
          from subterm(5) show False using neq 1 2 p 
            unfolding Prule B source.simps source_apply_subst[OF to_pterm_wf_pterm[of "lhs \<alpha>"]] source_to_pterm
            using term_subst_eq_rev x by fastforce
        qed
        from subterm(1,2,3) co_init have "As!i \<bottom>\<^sub>p ?Bs!i" 
          using i l' orth unfolding Prule by (metis B fun_well_arg l lhs_subst_args_wf_pterm nth_mem orth supt.arg)
      }
      then show ?thesis unfolding B Prule
        by (smt (verit, best) case_prodI2 fst_conv in_set_zip l l' orthogonal.intros(3) snd_conv)
    next
      case (Prule \<beta> Bs)
      from subterm(4) have \<alpha>:"\<alpha> = \<beta>"
        unfolding Prule \<open>A = Prule \<alpha> As\<close> eval_term.simps using orthogonal.simps
        by (smt (verit) Inl_inject Prule eval_term.simps(2) is_Prule.simps(1) is_Prule.simps(3) lhs no_var_lhs.lhs_is_Fun 
            no_var_lhs_axioms subterm.prems(2) term.collapse(2) term.sel(2) to_pterm.simps(2))
      from subterm(2,3) have l:"length As = length Bs"
        unfolding \<open>A = Prule \<alpha> As\<close> Prule using \<alpha> length_args_well_Prule by blast 
      {fix i assume i:"i < length As"
        with subterm(4) have "As!i \<cdot> \<sigma> \<bottom>\<^sub>p Bs!i \<cdot> \<sigma>" 
          unfolding \<open>A = Prule \<alpha> As\<close> Prule eval_term.simps \<alpha> by (smt (verit, ccfv_threshold) Inl_inject 
          Inr_not_Inl \<alpha> eval_term.simps(2) length_map lhs nth_map orthogonal.simps term.distinct(1) term.inject(2) to_pterm.simps(2))
        moreover from i subterm(5) have "source (As!i) = source (Bs!i)" 
          using Prule \<alpha> \<open>A = Prule \<alpha> As\<close> co_init_prule subterm.prems(1) subterm.prems(2) by blast
        moreover from i l subterm(2,3) have "As!i \<in> wf_pterm R" "Bs!i \<in> wf_pterm R" 
          unfolding Prule \<open>A = Prule \<alpha> As\<close> by auto
        moreover from i have "As!i \<lhd> A" 
          unfolding \<open>A = Prule \<alpha> As\<close> by simp
        ultimately have "As!i \<bottom>\<^sub>p Bs!i"
          using subterm(1) by simp
      }      
      with l show ?thesis 
        unfolding \<alpha> \<open>A = Prule \<alpha> As\<close> Prule by (simp add: orthogonal.intros(2))
    qed
  qed
qed

end

end
