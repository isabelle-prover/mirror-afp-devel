section\<open>Redex Patterns\<close>

theory Redex_Patterns
imports
  Labels_and_Overlaps    
begin

text\<open>Collect all rule symbols of a proof term together with the position in its source where they 
appear. This is used to split a proof term into a set of single steps, whose union 
(@{const join_list}) is the whole proof term again. 

The redex patterns are collected in leftmost outermost order.\<close>

fun redex_patterns :: "('f, 'v) pterm \<Rightarrow> (('f, 'v) prule \<times> pos) list"
  where
  "redex_patterns (Var x) = []" 
| "redex_patterns (Pfun f ss) = concat (map (\<lambda> (i, rps). map (\<lambda> (\<alpha>, p). (\<alpha>, i#p)) rps)
    (zip [0 ..< length ss] (map redex_patterns ss)))"
| "redex_patterns (Prule \<alpha> ss) = (\<alpha>, []) # concat (map (\<lambda> (p1, rps). map (\<lambda> (\<alpha>, p2). (\<alpha>, p1@p2)) rps)
    (zip (var_poss_list (lhs \<alpha>)) (map redex_patterns ss)))"

interpretation lexord_linorder: 
  linorder "ord.lexordp_eq ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)" 
           "ord.lexordp ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"
  using linorder.lexordp_linorder[OF linorder_class.linorder_axioms] by simp

lemma lexord_prefix_diff:
  assumes "(ord.lexordp ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)) xs ys" and "\<not> prefix xs ys" 
  shows "(ord.lexordp (<)) (xs@us) (ys@vs)" 
using assms proof(induct xs arbitrary:ys)
  case (Cons x xs')
  from Cons(2) obtain y ys' where ys:"ys = y#ys'"
    by (metis list.exhaust_sel ord.lexordp_simps(2)) 
  consider "x < y" | "x = y \<and> ord.lexordp (<) xs' ys'" 
    using Cons(2) ord.lexordp_eq.simps unfolding Cons ys by force 
  then show ?case proof(cases)
    case 1
    then show ?thesis unfolding ys by simp
  next
    case 2
    with Cons(3) have "\<not> prefix xs' ys'" 
      unfolding ys by simp 
    with Cons(1) 2 have "(ord.lexordp (<)) (xs'@us) (ys'@vs)"
      by auto 
    then show ?thesis unfolding ys using 2 by simp
  qed
qed simp

lemma var_poss_list_sorted: "sorted_wrt (ord.lexordp ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)) (var_poss_list t)"
proof(induct t)
  case (Fun f ts)
  let ?poss="(map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts))"
  {fix i j assume i:"i < length (var_poss_list (Fun f ts))" and j:"j < i"
    let ?p="concat ?poss ! i" 
    let ?q="concat ?poss ! j"
    from i obtain i' i'' where p:"?p = ?poss!i'!i''" and i':"i' < length ts" and i'':"i'' < length (?poss!i')"
        and i_sum:"i = sum_list (map length (take i' ?poss)) + i''"
      using less_length_concat[OF i[unfolded var_poss_list.simps]] unfolding length_map by auto
    from p have p2:"?p = i'# (var_poss_list (ts!i') ! i'')" 
      using i' i'' by simp
    from j obtain j' j'' where q:"?q = ?poss!j'!j''" and j':"j' < length ts" and j'':"j'' < length (?poss!j')"
        and j_sum:"j = sum_list (map length (take j' ?poss)) + j''"
      using less_length_concat i j length_map unfolding var_poss_list.simps
      by (smt (verit, ccfv_threshold) diff_le_self length_take length_upt length_zip map_upt_len_conv order.strict_trans take_all) 
    from q have q2:"?q = j'# (var_poss_list (ts!j') ! j'')" 
      using j' j'' by simp
    have "(ord.lexordp (<)) (var_poss_list (Fun f ts) ! j) (var_poss_list (Fun f ts) ! i)" proof(cases "i' = j'")
      case True
      have l:"length (map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts) ! j') = length (var_poss_list (ts!j'))" 
        using j' by auto
      from True j j_sum i_sum have "j'' < i''"
        using nat_add_left_cancel_less by blast 
      with Fun(1)[of "ts!j'"] i' i'' j'' have "(ord.lexordp (<)) (var_poss_list (ts!j') ! j'') (var_poss_list (ts!i') ! i'')"
        unfolding True l by (simp add: sorted_wrt_iff_nth_less)  
      then have "(ord.lexordp (<)) ?q ?p" 
        unfolding p2 q2 True by simp
      then show ?thesis unfolding var_poss_list.simps by fastforce
    next
      case False
      then have "j' < i'"
        using  i'' i' j' i_sum j_sum sum_list_less[OF j]
        by (smt (verit, best) i j le_neq_implies_less length_concat linorder_le_less_linear not_add_less1 order.strict_trans take_all var_poss_list.simps(2))
      then have "(ord.lexordp (<)) ?q ?p" 
        unfolding p2 q2 by simp
      then show ?thesis unfolding var_poss_list.simps by fastforce
    qed
  }
  then show ?case
    using sorted_wrt_iff_nth_less by blast
qed simp
  
context left_lin_no_var_lhs
begin

lemma redex_patterns_sorted:
  assumes  "A \<in> wf_pterm R"
  shows "sorted_wrt (ord.lexordp (<)) (map snd (redex_patterns A))"
proof-
  {fix i j assume "i < j" "j < length (redex_patterns A)" 
    with assms have "(ord.lexordp (<)) (snd (redex_patterns A ! i)) (snd (redex_patterns A ! j))"
    proof(induct A arbitrary: i j)
      case (2 As f)
      let ?poss="map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length As] (map redex_patterns As)"
      from 2(2,3) obtain \<alpha> p1 where ap:"redex_patterns (Pfun f As) ! i = (\<alpha>, p1)"
        by (metis surj_pair) 
      from 2(3) obtain \<beta> p2 where bp:"redex_patterns (Pfun f As) ! j = (\<beta>, p2)"
        by (metis surj_pair) 
      have l:"length (zip [0..<length As] (map redex_patterns As)) = length As" by simp
      from 2(2,3) have *:"i < length (concat ?poss)" by simp
      from ap obtain i' i'' where ap1:"(\<alpha>, p1) = ?poss!i'!i''" and i':"i' < length As" and i'':"i'' < length (?poss!i')"
        and i:"i = sum_list (map length (take i' ?poss)) + i''"
        unfolding redex_patterns.simps using less_length_concat[OF *] by (metis l length_map)
      have poss_i':"?poss!i' = map (\<lambda>(\<alpha>, p). (\<alpha>, i' # p)) (redex_patterns (As!i'))"
        using i' nth_zip[of i'] by fastforce  
      from ap1 i'' obtain p1' where p1':"p1 = i'#p1'" "(\<alpha>, p1') = redex_patterns (As!i') ! i''"  
        unfolding poss_i' by (smt (z3) case_prod_conv length_map nth_map old.prod.inject surj_pair) 
      from bp obtain j' j'' where ap2:"(\<beta>, p2) = ?poss!j'!j''" and j':"j' < length As" and j'':"j'' < length (?poss!j')"
        and j:"j = sum_list (map length (take j' ?poss)) + j''"
        unfolding redex_patterns.simps using less_length_concat[OF 2(3)[unfolded redex_patterns.simps]] by (metis l length_map)
      have poss_j':"?poss!j' = map (\<lambda>(\<alpha>, p). (\<alpha>, j' # p)) (redex_patterns (As!j'))"
        using j' nth_zip[of j'] by fastforce  
      from ap2 j'' obtain p2' where p2':"p2 = j'#p2'" "(\<beta>, p2') = redex_patterns (As!j') ! j''"  
        unfolding poss_j' by (smt (z3) case_prod_conv length_map nth_map old.prod.inject surj_pair) 
      show ?case proof(cases "i' = j'")
        case True
        from i j 2 have "i'' < j''" unfolding True by linarith
        moreover from j'' have "j'' < length (redex_patterns (As!j'))" unfolding poss_j' by auto    
        ultimately have "ord.lexordp (<) p1' p2'" using  2(1) j' True p1'(2) p2'(2) by (metis nth_mem snd_eqD)
        then show ?thesis unfolding ap bp p1' p2' True by auto
      next
        case False
        with 2(2) i j have "i' < j'" using sum_list_less[OF 2(2)] i' j' j''
          by (smt (verit, best) "*" "2.prems"(2) le_neq_implies_less length_concat linorder_le_less_linear not_add_less1 redex_patterns.simps(2) take_all)
        then show ?thesis unfolding ap bp p1' p2' by fastforce 
      qed
    next
      case (3 \<gamma> As)
      from 3(2,3) obtain \<alpha> p1 where ap:"redex_patterns (Prule \<gamma> As) ! i = (\<alpha>, p1)"
        by (metis surj_pair) 
      from 3(3) obtain \<beta> p2 where bp:"redex_patterns (Prule \<gamma> As) ! j = (\<beta>, p2)"
        by (metis surj_pair) 
      show ?case proof(cases "i")
        case 0
        from 3(1) no_var_lhs obtain f ts where lhs:"lhs \<gamma> = Fun f ts"
          by fastforce 
        from bp 3(4) 0 obtain j' where "concat (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As)) ! j' = (\<beta>, p2)" 
          "j' < length (concat (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As)))" 
          unfolding redex_patterns.simps using "3.prems"(2) by force
        then obtain j1 j2 where j1:"j1 < length (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As))" 
            and j2:"j2 < length (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As) ! j1)"
            and j1j2:"(map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As) ! j1) ! j2 = (\<beta>, p2)" 
          using nth_concat_split by metis 
        let ?p'="var_poss_list (lhs \<gamma>)!j1" 
        let ?rdp="(map redex_patterns As ! j1)" 
        from j1 have zip:"zip (var_poss_list (lhs \<gamma>)) (map redex_patterns As) ! j1 = (?p', ?rdp)" 
          unfolding length_map length_zip using nth_zip by force
        with j1j2 have "(\<beta>, p2) = map (\<lambda>(\<alpha>, p2). (\<alpha>, ?p' @ p2)) ?rdp !j2" 
          using nth_map j1 unfolding length_map by force
        moreover from j2 have "j2 < length (map (\<lambda>(\<alpha>, p2). (\<alpha>, ?p' @ p2)) ?rdp)" 
          unfolding nth_map[OF j1[unfolded length_map]] zip by force
        ultimately have "(\<beta>, p2) \<in> set (map (\<lambda>(\<alpha>, p2). (\<alpha>, ?p' @ p2)) ?rdp)" 
          by simp
        moreover have "?p' \<noteq> []" proof-
          from j1 have "?p' \<in> var_poss (lhs \<gamma>)"  
            unfolding length_map length_zip using nth_mem by fastforce
          then show ?thesis unfolding lhs var_poss.simps by force 
        qed
        ultimately have "p2 \<noteq> []"
          by auto 
        moreover from 0 ap have "p1 = []" by simp
        ultimately show ?thesis unfolding ap bp by simp
      next
        case (Suc n)
        let ?poss="(map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As))"
        from 3(1,2) have l:"length (var_poss_list (lhs \<gamma>)) = length As" 
          using linear_term_var_vars_term_list left_lin unfolding left_linear_trs_def using length_var_poss_list length_var_rule by auto  
        from 3(4,5) have *:"n < length (concat ?poss)" unfolding Suc by simp
        from ap have "concat (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As)) ! n = (\<alpha>, p1)" 
          unfolding Suc by simp
        then obtain i' i'' where ap1:"(\<alpha>, p1) = ?poss!i'!i''" and i':"i' < length ?poss" and i'':"i'' < length (?poss!i')"
          and n:"n = sum_list (map length (take i' ?poss)) + i''"
          using less_length_concat[OF *] by metis
        from i' have i'2:"i' < length (var_poss_list (lhs \<gamma>))" by simp
        obtain p11 where p11:"?poss!i' = map (\<lambda>(\<alpha>, p). (\<alpha>, p11 @ p)) (redex_patterns (As!i'))" "var_poss_list (lhs \<gamma>) !i' = p11" 
          using i' nth_zip[of i'] by fastforce  
        from ap1 i'' obtain p12 where p12:"p1 = p11@p12" "(\<alpha>, p12) = redex_patterns (As!i') ! i''"  
          unfolding p11 by (smt (z3) case_prod_conv length_map nth_map old.prod.inject surj_pair) 
        from 3(4,5) Suc obtain n' where j:"j = Suc n'" by (meson Suc_lessE) 
        from 3(5) have *:"n' < length (concat ?poss)" unfolding j by simp
        from bp have "concat (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<gamma>)) (map redex_patterns As)) ! n' = (\<beta>, p2)" 
          unfolding j by simp
        then obtain j' j'' where ap2:"(\<beta>, p2) = ?poss!j'!j''" and j':"j' < length ?poss" and j'':"j'' < length (?poss!j')"
          and n':"n' = sum_list (map length (take j' ?poss)) + j''"
          using less_length_concat[OF *] by metis
        from j' have j'2:"j' < length (var_poss_list (lhs \<gamma>))" by simp
        obtain p21 where p21:"?poss!j' = map (\<lambda>(\<alpha>, p). (\<alpha>, p21 @ p)) (redex_patterns (As!j'))" "var_poss_list (lhs \<gamma>) !j' = p21" 
          using j' nth_zip[of j'] by fastforce  
        from ap2 j'' obtain p22 where p22:"p2 = p21@p22" "(\<beta>, p22) = redex_patterns (As!j') ! j''"  
         unfolding p21 by (smt (z3) case_prod_conv length_map nth_map old.prod.inject surj_pair) 
        show ?thesis proof(cases "i' = j'")
          case True
          from n n' 3(4) have ij:"i'' < j''" unfolding True Suc j by linarith
          moreover from j'' have "j'' < length (redex_patterns (As!j'))" unfolding p21 by auto 
          moreover from j' l have "j' < length As" unfolding length_map by simp
          ultimately have "ord.lexordp (<) p12 p22" using 3(3) p22 p12 j' unfolding True by (metis nth_mem snd_conv)
          with p21(2) p11(2) show ?thesis unfolding ap bp p22 p12 True by (simp add: ord.lexordp_append_leftI)  
        next
          case False
          then have "i' < j'"
            using  sum_list_less[OF 3(4), where i'=i' and j'=j']
            by (smt (verit) "3.prems"(1) Suc Suc_less_SucD i' j j' j'' le_neq_implies_less n n' sum_list_less)
          then have "ord.lexordp (<) p11 p21" 
            using p11(2) p21(2) var_poss_list_sorted[of "lhs \<gamma>"] i'2 j'2 using sorted_wrt_nth_less by blast 
          moreover have "\<not> prefix p11 p21" proof-
            from False j' i' have "parallel_pos (var_poss_list (lhs \<gamma>) !i') (var_poss_list (lhs \<gamma>) !j')"
              unfolding length_map length_zip using var_poss_parallel var_poss_list_sound distinct_var_poss_list 
              by (metis l min.idem nth_eq_iff_index_eq nth_mem)
            then show ?thesis using p11(2) p21(2)
              by (metis less_eq_pos_simps(1) parallel_pos prefix_def)
          qed
          ultimately show ?thesis unfolding ap bp p12 p22 using lexord_prefix_diff by simp
        qed
      qed
    qed simp
  }
  then show ?thesis
    by (metis (mono_tags, lifting) sorted_wrt_iff_nth_less sorted_wrt_map) 
qed

corollary distinct_snd_rdp:
  assumes "A \<in> wf_pterm R"
  shows "distinct (map snd (redex_patterns A))" 
  using redex_patterns_sorted[OF assms] lexord_linorder.strict_sorted_iff by simp

lemma redex_patterns_equal:
  assumes wf:"A \<in> wf_pterm R" 
    and sorted:"sorted_wrt (ord.lexordp (<)) (map snd xs)" and eq:"set xs = set (redex_patterns A)"
  shows "xs = redex_patterns A" 
proof-
  have linord:"class.linorder (ord.lexordp_eq ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)) (ord.lexordp (<))" 
    using linorder.lexordp_linorder[OF linorder_class.linorder_axioms] by simp
  then have "map snd xs = map snd (redex_patterns A)" 
    using linorder.strict_sorted_equal[OF linord redex_patterns_sorted[OF wf] sorted] eq by simp
  with eq distinct_snd_rdp[OF wf] show ?thesis 
    using distinct_map by (metis (mono_tags, opaque_lifting) inj_onD list.inj_map_strong) 
qed

lemma redex_patterns_order:
  assumes "A \<in> wf_pterm R" and "i < j" and "j < length (redex_patterns A)" 
    and "redex_patterns A ! i = (\<alpha>, p1)" and "redex_patterns A ! j = (\<beta>, p2)"
  shows "\<not> p2 \<le>\<^sub>p p1" 
proof-
  have "(ord.lexordp (<)) p1 p2 " 
    using redex_patterns_sorted[OF assms(1)] assms sorted_wrt_nth_less by fastforce 
  then show ?thesis
    by (metis less_eq_pos_def lexord_linorder.less_le_not_le ord.lexordp_eq_pref) 
qed

end

context left_lin_no_var_lhs
begin 
lemma redex_patterns_label:
  assumes "A \<in> wf_pterm R"
  shows "(\<alpha>, p) \<in> set (redex_patterns A) \<longleftrightarrow> p \<in> poss (source A) \<and> get_label (labeled_source A |_ p) = Some (\<alpha>, 0)"
proof
  {assume "(\<alpha>, p) \<in> set (redex_patterns A)"
    with assms show "p \<in> poss (source A) \<and> get_label (labeled_source A |_ p) = Some (\<alpha>, 0)" proof(induct arbitrary:p)
      case (2 ts f)
      have l:"length (map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length ts] (map redex_patterns ts)) = length ts" 
        unfolding length_map length_zip by simp
      with 2(2) obtain i where i:"i < length ts" and ap:"(\<alpha>, p) \<in> set ((map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length ts] (map redex_patterns ts))!i)" 
        unfolding redex_patterns.simps using in_set_idx by (metis nth_concat_split nth_mem) 
      have "(map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length ts] (map redex_patterns ts))!i = map (\<lambda>(\<alpha>, p). (\<alpha>, i # p)) (redex_patterns (ts!i))" 
        using nth_zip i by fastforce
      with ap obtain p' where p':"p = i#p'" and "(\<alpha>, p') \<in> set (redex_patterns (ts !i))" by auto 
      with 2(1) i have "p' \<in> poss (source (ts!i))" and "get_label (labeled_source (ts!i)|_p') = Some (\<alpha>, 0)"
        using nth_mem by blast+
      with i show ?case unfolding p' by simp
    next
      case (3 \<beta> As)
      from no_var_lhs 3(1) obtain f ts where lhs:"lhs \<beta> = Fun f ts" by fastforce 
      from 3(2) have l:"length (var_poss_list (lhs \<beta>)) = length As" 
        using left_lin.length_var_rule[OF left_lin_axioms 3(1)] by (simp add: length_var_poss_list) 
      from 3(4) consider (root) "(\<alpha>, p) = (\<beta>, [])" | (arg) "(\<alpha>, p) \<in> set (concat (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<beta>)) (map redex_patterns As)))" 
        unfolding redex_patterns.simps by (meson set_ConsD) 
      then show ?case proof(cases)
        case root
        then have "\<alpha> = \<beta>" and "p = []" by simp+
        then show ?thesis by (simp add: lhs) 
      next
        case arg
        then obtain i where i:"i < length As" and ap:"(\<alpha>, p) \<in> set ((map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<beta>)) (map redex_patterns As))!i)" 
          using in_set_idx l by (metis (no_types, lifting) length_map map_snd_zip nth_concat_split nth_mem)
        let ?p1="(var_poss_list (lhs \<beta>))!i" 
        have "(map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<beta>)) (map redex_patterns As))!i = map (\<lambda>(\<alpha>, p). (\<alpha>, ?p1 @ p)) (redex_patterns (As!i))" 
          using nth_zip i l by fastforce
        with ap obtain p2 where p2:"p = ?p1@p2" and ap2:"(\<alpha>, p2) \<in> set (redex_patterns (As !i))" by auto 
        with 3(3) i have poss:"p2 \<in> poss (source (As!i))" and label:"get_label (labeled_source (As!i)|_p2) = Some (\<alpha>, 0)"
          using nth_mem by blast+
        have p1_poss:"?p1 \<in> poss (lhs \<beta>)" using i l
          by (metis nth_mem var_poss_imp_poss var_poss_list_sound) 
        then have 1:"p \<in> poss (source (Prule \<beta> As))" 
          using poss 3(2) i l unfolding source.simps p2 
          by (smt (verit, ccfv_SIG)  append_eq_append_conv2 comp_apply length_map length_remdups_eq length_rev length_var_poss_list nth_map poss_append_poss poss_imp_subst_poss rev_swap var_rule_pos_subst vars_term_list_var_poss_list)
        have "labeled_source (Prule \<beta> As) |_p = labeled_source (As!i) |_p2" proof-
          have "(\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) (var_rule \<beta> ! i) = labeled_source (As!i)" 
            using i 3(2) by (metis length_map lhs_subst_var_i nth_map) 
          moreover have "labeled_lhs \<beta> |_ ?p1 = Var (var_rule \<beta> ! i)"
            using 3(1) i l by (metis case_prodD left_lin left_linear_trs_def length_var_poss_list linear_term_var_vars_term_list p1_poss var_label_term vars_term_list_var_poss_list) 
          ultimately show ?thesis unfolding p2 labeled_source.simps
            by (smt (verit, best) eval_term.simps(1) label_term_to_term p1_poss poss_imp_subst_poss poss_term_lab_to_term subt_at_append subt_at_subst)
        qed
        with label have 2:"get_label (labeled_source (Prule \<beta> As)|_p) = Some (\<alpha>, 0)"
          by presburger
        from 1 2 show ?thesis by simp
      qed 
    qed simp
  }
  {assume "p \<in> poss (source A) \<and> get_label (labeled_source A |_ p) = Some (\<alpha>, 0)"
    with assms show "(\<alpha>, p) \<in> set (redex_patterns A)" proof(induct arbitrary:p)
      case (2 ts f)
      from 2(2) have "p \<noteq> []" unfolding labeled_source.simps by auto 
      with 2(2) obtain i p' where p':"p = i#p'" "p' \<in> poss (source (ts!i))" and i:"i < length ts"
        unfolding source.simps by fastforce
      with 2(2) have "get_label (labeled_source (ts!i) |_ p') = Some (\<alpha>, 0)" 
        unfolding p' labeled_source.simps by auto 
      with 2(1) i p' have IH:"(\<alpha>, p') \<in> set (redex_patterns (ts!i))"
        using nth_mem by blast 
      from i have i_zip:"i < length (zip [0..<length ts] (map redex_patterns ts))" by simp 
      from i have "zip [0..<length ts] (map redex_patterns ts) ! i = (i, redex_patterns (ts!i))" 
        using nth_zip by simp
      then have "(map2 (\<lambda>x. map (\<lambda>(\<alpha>, p). (\<alpha>, x # p))) [0..<length ts] (map redex_patterns ts)) ! i = map (\<lambda>(\<alpha>, p). (\<alpha>, i # p)) (redex_patterns (ts!i))"
        unfolding nth_map[OF i_zip] by simp
      with p'(2) IH have "(\<alpha>, p) \<in> set ((map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length ts] (map redex_patterns ts))!i)"
        unfolding p' by auto 
      with i_zip show ?case using i unfolding redex_patterns.simps set_concat by (metis (no_types, lifting) UN_I length_map nth_mem)  
    next
      case (3 \<beta> As)
      with get_label_Prule consider (1)"p = [] \<and> \<alpha> = \<beta>" | "(\<exists>p1 p2 i. p = p1 @ p2 \<and> i < length As \<and> var_poss_list (lhs \<beta>) ! i = p1 
          \<and> p2 \<in> poss (source (As ! i)) \<and> get_label (labeled_source (As ! i) |_ p2) = Some (\<alpha>, 0))"
        by (metis wf_pterm.intros(3))
      then show ?case proof(cases)
        case 1
        then show ?thesis unfolding redex_patterns.simps by simp
      next
        case 2
        from 3(1,2) left_lin have l:"length (var_poss_list (lhs \<beta>)) = length As"
          using length_var_poss_list length_var_rule by auto 
        from 2 obtain p1 p2 i where p:"p = p1 @ p2" and i:"i < length As" and p1:"var_poss_list (lhs \<beta>) ! i = p1" 
          and p2:"p2 \<in> poss (source (As ! i))" and lab:"get_label (labeled_source (As ! i) |_ p2) = Some (\<alpha>, 0)"
          by blast
        from i l have i':"i < length (zip (var_poss_list (lhs \<beta>)) (map redex_patterns As))" by simp
        from i p2 lab 3(3) have "(\<alpha>, p2) \<in> set (redex_patterns (As!i))" using nth_mem by blast  
        then have "(\<alpha>, p) \<in> set (map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2)) (redex_patterns (As!i)))" using p by force  
        then have "(\<alpha>, p) \<in> set ((map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<beta>)) (map redex_patterns As))!i)" 
          unfolding nth_map[OF i'] p using p1 by (simp add: i l) 
        then have "(\<alpha>, p) \<in> set (concat (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<beta>)) (map redex_patterns As)))"
          unfolding set_concat by (metis (no_types, lifting) UN_I i' length_map nth_mem) 
        then show ?thesis unfolding redex_patterns.simps by (meson list.set_intros(2))
      qed
    qed simp
   }
 qed

lemma redex_pattern_rule_symbol:
  assumes "A \<in> wf_pterm R" "(\<alpha>, p) \<in> set (redex_patterns A)" 
  shows "to_rule \<alpha> \<in> R" 
proof-
  from redex_patterns_label[OF assms(1)] have "p \<in> poss (source A)" and "get_label (labeled_source A |_ p) = Some (\<alpha>, 0)" 
    using assms(2) by simp+
  then show ?thesis
    using assms(1) labeled_wf_pterm_rule_in_TRS by fastforce 
qed

lemma redex_patterns_subset_possL:
  assumes "A \<in> wf_pterm R"
  shows "set (map snd (redex_patterns A)) \<subseteq> possL A"
  using redex_patterns_label[OF assms]
  by (smt (verit) get_label_imp_labelposs imageE labeled_source_to_term list.set_map option.simps(3) poss_term_lab_to_term prod.collapse subsetI)  
end

lemma redex_poss_empty_imp_empty_step:
  assumes "redex_patterns A = []"
  shows "is_empty_step A" 
  using assms proof(induct A)
  case (Pfun f As)
  {fix i assume i:"i < length As" 
    then have i_zip:"i < length (zip [0..<length As] (map redex_patterns As))" by simp  
    {fix x xs assume "redex_patterns (As!i) = x#xs"
      with i have "zip [0..<length As] (map redex_patterns As) ! i = (i, x#xs)" by simp
      then have "(map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length As] (map redex_patterns As))!i \<noteq> []" 
        using nth_map i_zip by simp
      with Pfun(2) have False unfolding redex_patterns.simps using i_zip concat_nth_length
        by (metis (no_types, lifting) length_0_conv length_greater_0_conv length_map less_nat_zero_code)
    }
    then have "redex_patterns (As!i) = []"
      by (meson list.exhaust) 
    with Pfun(1) i have "is_empty_step (As!i)"
      by simp
  }
  then show ?case 
    by (simp add: list_all_length) 
qed simp_all

lemma overlap_imp_redex_poss:
  assumes "A \<in> wf_pterm R" "B \<in> wf_pterm R" 
    and "measure_ov A B \<noteq> 0"
  shows "redex_patterns A \<noteq> []"
proof
  assume "redex_patterns A = []"
  then have "is_empty_step A"
    by (simp add: redex_poss_empty_imp_empty_step) 
  with assms(3) show False
    by (simp add: empty_step_imp_measure_zero) 
qed

lemma redex_patterns_to_pterm:
  shows "redex_patterns (to_pterm s) = []" 
proof(induct s)
  case (Fun f ts)
  have l:"length (map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length (map to_pterm ts)] (map redex_patterns (map to_pterm ts))) = length ts"
    by simp
  {fix i assume "i < length ts"
    with Fun have "(map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length (map to_pterm ts)] (map redex_patterns (map to_pterm ts)))!i = []" 
      by simp
  }
  with l show ?case unfolding to_pterm.simps redex_patterns.simps
    by (metis length_greater_0_conv length_nth_simps(1) less_nat_zero_code nth_concat_split)
qed simp

(*some of this might make older lemmas about labeled_pos/Possl redundant*)
lemma redex_patterns_elem_fun:
  assumes "(\<alpha>, p) \<in> set (redex_patterns (Pfun f As))"
  shows "\<exists>i p'. i < length As \<and> p = i#p' \<and> (\<alpha>, p') \<in> set (redex_patterns (As!i))" 
proof-
  let ?xs="map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length As] (map redex_patterns As)"
  from assms obtain k where k:"k < length (redex_patterns (Pfun f As))" "redex_patterns (Pfun f As) ! k = (\<alpha>, p)"
    by (metis in_set_idx)
  then obtain i j where "i < length ?xs" and j:"j < length (?xs!i)" "?xs ! i ! j = (\<alpha>, p)" 
    using nth_concat_split[OF k(1)[unfolded redex_patterns.simps]] by force  
  then have i:"i < length As" by auto 
  then have "zip [0..<length As] (map redex_patterns As) !i = (i, redex_patterns (As!i))" 
    using nth_zip by auto
  then have "?xs!i = map (\<lambda>(\<alpha>, p). (\<alpha>, i#p)) (redex_patterns (As!i))" using nth_map i by auto
  with j obtain p' where "p = i#p'" and "(\<alpha>, p') \<in> set (redex_patterns (As!i))"
    by (smt (verit, ccfv_threshold) case_prod_beta fst_conv imageE list.set_map nth_mem prod.collapse snd_conv) 
  with i show ?thesis by simp
qed

lemma redex_patterns_elem_rule:
  assumes "(\<alpha>, p) \<in> set (redex_patterns (Prule \<beta> As))"
  shows "p = [] \<or> (\<exists>i p'. i < length As \<and> i < length (var_poss_list (lhs \<beta>)) 
       \<and> p = (var_poss_list (lhs \<beta>)!i)@p' \<and> (\<alpha>, p') \<in> set (redex_patterns (As!i)))" 
proof-
  let ?xs="map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<beta>)) (map redex_patterns As)"
  from assms obtain k where k:"k < length (redex_patterns (Prule \<beta> As))" "redex_patterns (Prule \<beta> As) ! k = (\<alpha>, p)"
    by (metis in_set_idx)
  show ?thesis proof(cases "p = []")
    case False 
    with k have "k \<noteq> 0" 
      unfolding redex_patterns.simps by (metis nth_Cons_0 prod.inject) 
    with k obtain i j where "i < length ?xs" and j:"j < length (?xs!i)" "?xs ! i ! j = (\<alpha>, p)" 
      using nth_concat_split less_Suc_eq_0_disj unfolding redex_patterns.simps by force
    then have i:"i < length As" "i < length (var_poss_list (lhs \<beta>))" by auto 
    let ?p="(var_poss_list (lhs \<beta>))!i"
    from i have "zip (var_poss_list (lhs \<beta>)) (map redex_patterns As) !i = (?p, redex_patterns (As!i))" 
      using nth_zip by auto
    then have "?xs!i = map (\<lambda>(\<alpha>, p). (\<alpha>, ?p@p)) (redex_patterns (As!i))" using nth_map i by auto
    with j obtain p' where "p = ?p@p'" and "(\<alpha>, p') \<in> set (redex_patterns (As!i))"
      by (smt (verit, ccfv_threshold) case_prod_beta fst_conv imageE list.set_map nth_mem prod.collapse snd_conv) 
    with i show ?thesis by blast
  qed simp
qed

lemma redex_patterns_elem_fun':
  assumes "(\<alpha>, p) \<in> set (redex_patterns (As!i))" and i:"i < length As"
  shows "(\<alpha>, i#p) \<in> set (redex_patterns (Pfun f As))" 
proof-
  let ?xs="map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length As] (map redex_patterns As)"
  from i have "zip [0..<length As] (map redex_patterns As) !i = (i, redex_patterns (As!i))" 
    using nth_zip by auto
  then have "?xs!i = map (\<lambda>(\<alpha>, p). (\<alpha>, i#p)) (redex_patterns (As!i))" using nth_map i by auto
  with assms have "(\<alpha>, i#p) \<in> set (?xs!i)" by fastforce 
  moreover from i have "i < length ?xs" by simp
  ultimately have *:"(\<alpha>, i#p) \<in> set (concat ?xs)" 
    unfolding set_concat by (meson UN_iff nth_mem) 
  then show ?thesis by simp
qed

lemma redex_patterns_elem_rule':
  assumes "(\<beta>, p) \<in> set (redex_patterns (As!i))" and i:"i < length As" "i < length (var_poss_list (lhs \<alpha>))"
  shows "(\<beta>, (var_poss_list (lhs \<alpha>) ! i)@p) \<in> set (redex_patterns (Prule \<alpha> As))" 
proof-
  let ?xs="map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<alpha>)) (map redex_patterns As)"
  let ?p="var_poss_list (lhs \<alpha>) ! i"
  from i have "zip (var_poss_list (lhs \<alpha>)) (map redex_patterns As) !i = (?p, redex_patterns (As!i))" 
    using nth_zip by auto
  then have "?xs!i = map (\<lambda>(\<alpha>, p). (\<alpha>, ?p@p)) (redex_patterns (As!i))" using nth_map i by auto
  with assms have "(\<beta>, ?p@p) \<in> set (?xs!i)" by fastforce 
  moreover from i have "i < length ?xs" by simp
  ultimately have *:"(\<beta>, ?p@p) \<in> set (concat ?xs)" 
    unfolding set_concat by (meson UN_iff nth_mem) 
  then show ?thesis by simp
qed

lemma redex_patterns_elem_subst: 
  assumes "(\<alpha>, p) \<in> set (redex_patterns ((to_pterm t) \<cdot> \<sigma>))" 
  shows "\<exists>p1 p2 x. p = p1@p2 \<and> (\<alpha>, p2) \<in> set (redex_patterns (\<sigma> x)) \<and> p1 \<in> var_poss t \<and> t|_p1 = Var x" 
  using assms proof(induct t arbitrary: p)
  case (Var x)
  then show ?case unfolding to_pterm.simps eval_term.simps by force
next
  case (Fun f ts)
  from Fun(2) obtain j where j:"j < length (redex_patterns (to_pterm (Fun f ts) \<cdot> \<sigma>))" "(redex_patterns (to_pterm (Fun f ts) \<cdot> \<sigma>))!j = (\<alpha>, p)" 
    by (metis in_set_idx) 
  from j obtain i k where i:"i < length ts" 
    and k:"k < length (map (\<lambda>(\<alpha>, p). (\<alpha>, i # p)) (redex_patterns (to_pterm (ts!i) \<cdot> \<sigma>)))"
    and rdp:"(map (\<lambda>(\<alpha>, p). (\<alpha>, i # p)) (redex_patterns (to_pterm (ts!i) \<cdot> \<sigma>)))!k = (\<alpha>, p)"
    using nth_concat_split unfolding length_map to_pterm.simps eval_term.simps redex_patterns.simps by force 
  from rdp k obtain p' where p:"p = i#p'" 
    by (smt (verit, del_insts) case_prod_conv list.sel(3) map_eq_imp_length_eq map_ident nth_map prod.inject surj_pair) 
  from k rdp have "(\<alpha>, p') \<in> set (redex_patterns (to_pterm (ts!i) \<cdot> \<sigma>))" 
    unfolding p by (smt (verit, del_insts) case_prod_conv list.sel(3) map_eq_imp_length_eq map_ident nth_map nth_mem prod.inject surj_pair) 
  with Fun(1) i obtain p1 p2 x where p':"p' = p1@p2" and rdp2:"(\<alpha>, p2) \<in> set (redex_patterns (\<sigma> x))" and "p1 \<in> var_poss (ts!i)" and "(ts!i)|_p1 = Var x"
    by (meson nth_mem) 
  with i have "i#p1 \<in> var_poss (Fun f ts)" "Fun f ts |_ (i#p1) = Var x" 
    by auto 
  with p' rdp2 show ?case 
    unfolding p by (meson Cons_eq_appendI)
qed

context left_lin_no_var_lhs
begin

lemma redex_patterns_rule'':
  assumes rdp:"(\<beta>, p @ q) \<in> set (redex_patterns (Prule \<alpha> As))" 
    and wf:"Prule \<alpha> As \<in> wf_pterm R" 
    and p:"p = var_poss_list (lhs \<alpha>)!i" 
    and i:"i < length As" 
  shows "(\<beta>, q) \<in> set (redex_patterns (As!i))" 
proof-
  from wf obtain f ts where lhs:"lhs \<alpha> = Fun f ts"
    by (metis Inl_inject case_prodD is_FunE is_Prule.simps(1) is_Prule.simps(3) no_var_lhs term.distinct(1) term.inject(2) wf_pterm.simps) 
  from wf i have l:"length As = length (var_poss_list (lhs \<alpha>))"
    by (metis Inl_inject is_Prule.simps(1) is_Prule.simps(3) length_var_poss_list length_var_rule term.distinct(1) term.inject(2) wf_pterm.simps) 
  with i p have "p \<in> var_poss (Fun f ts)"
    by (metis lhs nth_mem var_poss_list_sound) 
  then have "p \<noteq> []" by force
  then obtain j p' where j:"j < length As" and p':"p@q = var_poss_list (lhs \<alpha>) ! j @ p'" "(\<beta>, p') \<in> set (redex_patterns (As!j))" 
    using redex_patterns_elem_rule[OF rdp] by blast  
  {assume "j \<noteq> i" 
    then have "p \<bottom> var_poss_list (lhs \<alpha>) ! j" 
      unfolding p using i j by (metis distinct_var_poss_list l nth_eq_iff_index_eq nth_mem var_poss_list_sound var_poss_parallel) 
    with p'(1) have False
      by (metis less_eq_pos_simps(1) pos_less_eq_append_not_parallel) 
  }
  with p'(1) p have "j = i" and "p' = q" by fastforce+
  with p'(2) show ?thesis by simp
qed

lemma redex_patterns_elem_subst': 
  assumes "(\<alpha>, p2) \<in> set (redex_patterns (\<sigma> x))" and p1:"p1 \<in> poss t" "t|_p1 = Var x"
  shows "(\<alpha>, p1@p2) \<in> set (redex_patterns ((to_pterm t) \<cdot> \<sigma>))" 
using assms proof(induct t arbitrary: p1)
  case (Var x)
  then show ?case unfolding to_pterm.simps eval_term.simps by force
next
  case (Fun f ts)
  from Fun(3,4) obtain i p1' where i:"i < length ts" and p1:"p1 = i#p1'" and p1':"p1' \<in> poss (ts!i)" "(ts!i)|_p1' = Var x"
    by auto 
  with Fun(1,2) have "(\<alpha>, p1' @ p2) \<in> set (redex_patterns (to_pterm (ts!i) \<cdot> \<sigma>))"
    using nth_mem by blast
  then obtain j where j:"j < length (redex_patterns (to_pterm (ts!i) \<cdot> \<sigma>))" "redex_patterns (to_pterm (ts!i) \<cdot> \<sigma>)!j = (\<alpha>, p1' @ p2)"
    by (metis in_set_idx) 
  let ?xs="map2 (\<lambda>i. map (\<lambda>(\<alpha>, p). (\<alpha>, i # p))) [0..<length (map (\<lambda>s. s \<cdot> \<sigma>) (map to_pterm ts))] (map redex_patterns (map (\<lambda>s. s \<cdot> \<sigma>) (map to_pterm ts)))"
  from i j have rdp:"?xs!i!j = (\<alpha>, p1@p2)"
    unfolding p1 by auto
  let ?i="sum_list (map length (take i ?xs)) + j"
  from rdp i j(1) have "(redex_patterns ((to_pterm (Fun f ts)) \<cdot> \<sigma>)) ! ?i = (\<alpha>, p1@p2)" 
    using concat_nth[of i ?xs j] unfolding length_map by force
  moreover from i j(1) have "?i < length (redex_patterns (to_pterm (Fun f ts) \<cdot> \<sigma>))" 
    using concat_nth_length[of i ?xs j] unfolding length_map by force
  ultimately show ?case
    using nth_mem by fastforce 
qed
 
lemma redex_patterns_join: 
  assumes "A \<in> wf_pterm R" "B \<in> wf_pterm R" "A \<squnion> B = Some C"
  shows "set (redex_patterns C) = set (redex_patterns A) \<union> set (redex_patterns B)"  
  using assms proof(induct A arbitrary: B C rule:subterm_induct)
  case (subterm A)
  from subterm(2) show ?case proof(cases A)
    case (1 x)
    from subterm(2,3,4) var_join show ?thesis 
      unfolding 1 by auto
  next
    case (2 As f)
    with subterm(4) consider (Pfun) "\<exists>g Bs. B = Pfun g Bs" | (Prule) "\<exists>\<alpha> Bs. B = Prule \<alpha> Bs" by (meson fun_join) 
    then show ?thesis proof(cases)
      case Pfun
      then obtain g Bs where B:"B = Pfun g Bs" by blast
      from subterm(4) join_fun_fun obtain Cs where fg:"f = g" and l_As_Bs:"length As = length Bs" and  
        C:"C = Pfun f Cs" and l_Cs_As:"length Cs = length As" and Cs:"(\<forall>i<length As. As ! i \<squnion> Bs ! i = Some (Cs ! i))"
        unfolding 2 B by force 
      {fix i assume i:"i < length As" 
        with subterm(3) have "Bs!i \<in> wf_pterm R"
          using B l_As_Bs by auto 
        with subterm(1) i 2 Cs have "set (redex_patterns (Cs!i)) = set (redex_patterns (As!i)) \<union> set (redex_patterns (Bs!i))"
          by (meson nth_mem supt.arg)
      }note IH=this
      {fix \<alpha> p assume "(\<alpha>, p) \<in> set (redex_patterns C)" 
        then obtain i p' where i:"i < length Cs" and p:"p = i#p'" and "(\<alpha>, p') \<in> set (redex_patterns (Cs!i))" 
          unfolding C by (meson redex_patterns_elem_fun)
        with IH consider "(\<alpha>, p') \<in> set (redex_patterns (As!i))" | "(\<alpha>, p') \<in> set (redex_patterns (Bs!i))"
          using l_Cs_As by fastforce
        then have "(\<alpha>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)" proof(cases)
          case 1
          with i have "(\<alpha>, p) \<in> set (redex_patterns A)" 
            unfolding 2 p l_Cs_As by (meson redex_patterns_elem_fun')
          then show ?thesis by simp
        next
          case 2
          with i have "(\<alpha>, p) \<in> set (redex_patterns B)" 
            unfolding B l_Cs_As l_As_Bs p by (meson redex_patterns_elem_fun')
          then show ?thesis by simp
        qed
      }
      moreover 
      {fix \<alpha> p assume "(\<alpha>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)"
        then consider "(\<alpha>, p) \<in> set (redex_patterns A)" | "(\<alpha>, p) \<in> set (redex_patterns B)" by force
        then have "(\<alpha>, p) \<in> set (redex_patterns C)" proof(cases)
          case 1
          then obtain i p' where i:"i < length As" and p:"p = i#p'" and "(\<alpha>, p') \<in> set (redex_patterns (As!i))" 
            unfolding 2 by (meson redex_patterns_elem_fun)
          with IH have "(\<alpha>, p') \<in> set (redex_patterns (Cs!i))" by blast 
          with i l_Cs_As show ?thesis unfolding C p
            by (metis redex_patterns_elem_fun')
        next
          case 2
          then obtain i p' where i:"i < length Bs" and p:"p = i#p'" and "(\<alpha>, p') \<in> set (redex_patterns (Bs!i))" 
            unfolding B by (meson redex_patterns_elem_fun)
          with IH l_As_Bs have "(\<alpha>, p') \<in> set (redex_patterns (Cs!i))" by simp 
          with i l_Cs_As l_As_Bs show ?thesis unfolding C p
            by (metis redex_patterns_elem_fun')
        qed
      }
      ultimately show ?thesis by auto
    next
      case Prule
      then obtain \<alpha> Bs where B:"B = Prule \<alpha> Bs" by blast
      from B subterm(3) have alpha:"to_rule \<alpha> \<in> R"
        using wf_pterm.simps by fastforce 
      then obtain f' ts where lhs:"lhs \<alpha> = Fun f' ts" 
        using no_var_lhs by fastforce 
      from alpha have lin:"linear_term (lhs \<alpha>)"
        using left_lin left_linear_trs_def by fastforce 
      from B subterm(3,4) obtain \<sigma> Cs where sigma:"match A (to_pterm (lhs \<alpha>)) = Some \<sigma>"
        and C:"C = Prule \<alpha> Cs" and l_Cs_Bs:"length Cs = length Bs" and Cs:"(\<forall>i<length Bs. \<sigma> (var_rule \<alpha> ! i) \<squnion> (Bs ! i) = Some (Cs ! i))"
        unfolding 2 using join_rule_fun join_sym by (smt (verit, best)) 
      from B subterm(3) have l_Bs:"length Bs = length (var_rule \<alpha>)"
        using wf_pterm.simps by fastforce 
      from sigma have A:"A = (to_pterm (lhs \<alpha>) \<cdot> \<sigma>)"
        by (simp add: match_matches)
      {fix i assume i:"i < length Bs" 
        with sigma lhs l_Bs have "\<sigma> (var_rule \<alpha> ! i) \<lhd> A"
          by (smt (verit, best) comp_def match_lhs_subst nth_mem set_remdups set_rev set_vars_term_list subst_image_subterm to_pterm.simps(2) vars_to_pterm) 
        moreover have "\<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
          using subterm(2) by (metis i l_Bs match_well_def sigma vars_to_pterm) 
        moreover from i subterm(3) have "Bs!i \<in> wf_pterm R"
          using B nth_mem by blast 
        ultimately have "set (redex_patterns (Cs!i)) = set (redex_patterns (\<sigma> (var_rule \<alpha> ! i))) \<union> set (redex_patterns (Bs!i))"
          using subterm(1) Cs l_Cs_Bs i by presburger
      }note IH=this
      {fix \<beta> p assume rdp:"(\<beta>, p) \<in> set (redex_patterns C)" 
        then have "(\<beta>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)" proof(cases "p=[]")
          case True
          with rdp have "\<alpha> = \<beta>"  
            unfolding C using lhs by (metis (no_types, lifting) C join_wf_pterm list.set_intros(1) option.sel 
                prod.inject redex_patterns.simps(3) redex_patterns_label subterm.prems(1) subterm.prems(2) subterm.prems(3)) 
          then show ?thesis unfolding B redex_patterns.simps True by simp
        next
          case False
          with rdp obtain i p' where i:"i < length Cs" "i < length (var_poss_list (lhs \<alpha>))" 
            and p:"p = (var_poss_list (lhs \<alpha>) ! i)@p'" and *:"(\<beta>, p') \<in> set (redex_patterns (Cs!i))" 
            unfolding C by (meson redex_patterns_elem_rule)
          let ?p="var_poss_list (lhs \<alpha>) ! i"
          from * i IH consider "(\<beta>, p') \<in> set (redex_patterns (\<sigma> (var_rule \<alpha> ! i)))" | "(\<beta>, p') \<in> set (redex_patterns (Bs!i))"
            using l_Cs_Bs by fastforce
          then show ?thesis proof(cases)
            case 1
            let ?x="var_rule \<alpha> ! i"
            from i(2) have p_pos:"?p \<in> poss (lhs \<alpha>)"
              by (metis nth_mem var_poss_iff var_poss_list_sound) 
            from i(2) have p_x:"(lhs \<alpha>)|_?p = Var ?x"
              by (metis \<open>to_rule \<alpha> \<in> R\<close> case_prodD left_lin left_linear_trs_def length_var_poss_list linear_term_var_vars_term_list vars_term_list_var_poss_list) 
            from i(2) have "(\<beta>, p) \<in> set (redex_patterns A)" 
              unfolding p A using redex_patterns_elem_subst'[of \<beta> p' \<sigma> ?x, OF 1 p_pos p_x] by simp
            then show ?thesis by simp
          next
            case 2
            from i have "(\<beta>, p) \<in> set (redex_patterns B)" 
              unfolding B p l_Cs_Bs using redex_patterns_elem_rule'[OF 2] by presburger
            then show ?thesis by simp
        qed
        qed
      }
      moreover 
      {fix \<beta> p assume "(\<beta>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)"
        then consider "(\<beta>, p) \<in> set (redex_patterns A)" | "(\<beta>, p) \<in> set (redex_patterns B)" by force
        then have "(\<beta>, p) \<in> set (redex_patterns C)" proof(cases)
          case 1
          then obtain p1 p2 x where p:"p = p1@p2" and rdp2:"(\<beta>, p2) \<in> set (redex_patterns (\<sigma> x))" 
            and p1:"p1 \<in> var_poss (lhs \<alpha>)" "lhs \<alpha>|_p1 = Var x" 
            unfolding A using redex_patterns_elem_subst by metis 
          then obtain i where i:"i < length (var_rule \<alpha>)" "(var_rule \<alpha>)!i = x" 
            using lin by (metis in_set_conv_nth length_var_poss_list linear_term_var_vars_term_list term.inject(1) var_poss_list_sound vars_term_list_var_poss_list) 
          with p1 lin have p1:"p1 = var_poss_list (lhs \<alpha>) ! i"
            by (metis length_var_poss_list linear_term_unique_vars linear_term_var_vars_term_list nth_mem var_poss_imp_poss var_poss_list_sound vars_term_list_var_poss_list) 
          from i IH rdp2 have "(\<beta>, p2) \<in> set (redex_patterns (Cs!i))"
            by (simp add: l_Bs) 
          with i(1) show ?thesis unfolding C p
            using redex_patterns_elem_rule' p1 by (metis alpha l_Bs l_Cs_Bs length_var_poss_list length_var_rule) 
        next
          case 2 
          show ?thesis proof(cases "p=[]")
            case True
            from 2 have "\<alpha> = \<beta>"  
            unfolding B True using lhs by (metis (no_types, lifting) B list.set_intros(1) option.sel 
                prod.inject redex_patterns.simps(3) redex_patterns_label subterm.prems(2)) 
            then show ?thesis unfolding C redex_patterns.simps True by simp
          next
            case False
            with 2 obtain i p' where i:"i < length Bs" "i < length (var_poss_list (lhs \<alpha>))" 
              and p:"p = (var_poss_list (lhs \<alpha>) ! i)@p'" and *:"(\<beta>, p') \<in> set (redex_patterns (Bs!i))" 
              unfolding B by (meson redex_patterns_elem_rule)
            with IH l_Cs_Bs have "(\<beta>, p') \<in> set (redex_patterns (Cs!i))" by simp 
            with i l_Cs_Bs show ?thesis unfolding C p
              by (metis redex_patterns_elem_rule')
          qed
        qed
      }
      ultimately show ?thesis by auto
    qed
  next
    case (3 \<alpha> As)
    from 3(2) obtain f' ts where lhs:"lhs \<alpha> = Fun f' ts" 
      using no_var_lhs by fastforce 
    from 3(2) have lin:"linear_term (lhs \<alpha>)"
      using left_lin left_linear_trs_def by fastforce 
    from 3 subterm(2,4) consider (Pfun) "\<exists>g Bs. B = Pfun g Bs" | (Prule) "\<exists>\<beta> Bs. B = Prule \<beta> Bs" by (meson rule_join) 
    then show ?thesis proof(cases)
      case Pfun
      then obtain f Bs where B:"B = Pfun f Bs" by blast
      from subterm(2,4) obtain \<sigma> Cs where sigma:"match B (to_pterm (lhs \<alpha>)) = Some \<sigma>"
        and C:"C = Prule \<alpha> Cs" and l_Cs_As:"length Cs = length As" and As:"(\<forall>i<length As. (As ! i) \<squnion> \<sigma> (var_rule \<alpha> ! i) = Some (Cs ! i))"
        unfolding 3 B using 3(3) join_rule_fun by metis
      {fix i assume i:"i < length As" 
        have "\<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
          using subterm(3) by (metis "3"(3) i match_well_def sigma vars_to_pterm)
        then have "set (redex_patterns (Cs!i)) = set (redex_patterns (As!i)) \<union> set (redex_patterns (\<sigma> (var_rule \<alpha> ! i)))"
          using subterm(1) 3 by (meson As i nth_mem supt.arg) 
      }note IH=this
      {fix \<beta> p assume rdp:"(\<beta>, p) \<in> set (redex_patterns C)" 
        then have "(\<beta>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)" proof(cases "p=[]")
          case True
          with rdp have "\<alpha> = \<beta>"  
            unfolding C using lhs by (metis (no_types, lifting) C join_wf_pterm list.set_intros(1) option.sel 
                prod.inject redex_patterns.simps(3) redex_patterns_label subterm.prems(1) subterm.prems(2) subterm.prems(3)) 
          then show ?thesis unfolding 3 redex_patterns.simps True by simp
        next
          case False
          with rdp obtain i p' where i:"i < length Cs" "i < length (var_poss_list (lhs \<alpha>))" 
            and p:"p = (var_poss_list (lhs \<alpha>) ! i)@p'" and *:"(\<beta>, p') \<in> set (redex_patterns (Cs!i))" 
            unfolding C by (meson redex_patterns_elem_rule)
          let ?p="var_poss_list (lhs \<alpha>) ! i"
          from * i IH consider "(\<beta>, p') \<in> set (redex_patterns (\<sigma> (var_rule \<alpha> ! i)))" | "(\<beta>, p') \<in> set (redex_patterns (As!i))"
            using l_Cs_As by auto
          then show ?thesis proof(cases)
            case 1
            let ?x="var_rule \<alpha> ! i"
            from i(2) have p_pos:"?p \<in> poss (lhs \<alpha>)"
              by (metis nth_mem var_poss_iff var_poss_list_sound) 
            from i(2) have p_x:"(lhs \<alpha>)|_?p = Var ?x"
              by (metis 3(2) case_prodD left_lin left_linear_trs_def length_var_poss_list linear_term_var_vars_term_list vars_term_list_var_poss_list) 
            from sigma have "(\<beta>, p) \<in> set (redex_patterns B)" 
              unfolding p using redex_patterns_elem_subst'[of \<beta> p' \<sigma> ?x, OF 1 p_pos p_x] by (simp add: match_matches)
            then show ?thesis by simp
          next
            case 2
            from i have "(\<beta>, p) \<in> set (redex_patterns A)" 
              unfolding 3(1) p l_Cs_As using redex_patterns_elem_rule'[OF 2] by presburger
            then show ?thesis by simp
          qed
        qed
      }
      moreover 
      {fix \<beta> p assume "(\<beta>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)"
        then consider "(\<beta>, p) \<in> set (redex_patterns B)" | "(\<beta>, p) \<in> set (redex_patterns A)"  by force
        then have "(\<beta>, p) \<in> set (redex_patterns C)" proof(cases)
          case 1
          then obtain p1 p2 x where p:"p = p1@p2" and rdp2:"(\<beta>, p2) \<in> set (redex_patterns (\<sigma> x))" 
            and p1:"p1 \<in> var_poss (lhs \<alpha>)" "lhs \<alpha>|_p1 = Var x" 
            using sigma redex_patterns_elem_subst using match_matches by blast
          then obtain i where i:"i < length (var_rule \<alpha>)" "(var_rule \<alpha>)!i = x" 
            using lin by (metis in_set_conv_nth length_var_poss_list linear_term_var_vars_term_list term.inject(1) var_poss_list_sound vars_term_list_var_poss_list) 
          with p1 lin have p1:"p1 = var_poss_list (lhs \<alpha>) ! i"
            by (metis length_var_poss_list linear_term_unique_vars linear_term_var_vars_term_list nth_mem var_poss_imp_poss var_poss_list_sound vars_term_list_var_poss_list) 
          from i IH rdp2 have "(\<beta>, p2) \<in> set (redex_patterns (Cs!i))"
            by (simp add: "3"(3))
          with i(1) show ?thesis unfolding C p
            using redex_patterns_elem_rule' p1 by (metis "3"(2) "3"(3) l_Cs_As length_var_poss_list length_var_rule)
        next
          case 2 
          show ?thesis proof(cases "p=[]")
            case True
            from 2 have "\<alpha> = \<beta>"  
              unfolding True using lhs by (metis "3"(1) list.set_intros(1) option.sel prod.sel(1) redex_patterns.simps(3) redex_patterns_label subterm.prems(1))
            then show ?thesis unfolding C redex_patterns.simps True by simp
          next
            case False
            with 2 obtain i p' where i:"i < length As" "i < length (var_poss_list (lhs \<alpha>))" 
              and p:"p = (var_poss_list (lhs \<alpha>) ! i)@p'" and *:"(\<beta>, p') \<in> set (redex_patterns (As!i))"
              using "3"(1) redex_patterns_elem_rule by blast 
            with IH l_Cs_As have "(\<beta>, p') \<in> set (redex_patterns (Cs!i))" by simp 
            with i l_Cs_As show ?thesis unfolding C p
              by (metis redex_patterns_elem_rule')
          qed
        qed
      }
      ultimately show ?thesis by auto
    next
      case Prule
      then obtain \<beta> Bs where B:"B = Prule \<beta> Bs" by blast
      obtain Cs where alpha_beta:"\<alpha> = \<beta>" and l_As_Bs:"length As = length Bs" 
        and C:"C = Prule \<alpha> Cs" and l_Cs_As:"length Cs = length As" and args:"\<forall>i < length As. As ! i \<squnion> Bs ! i = Some (Cs ! i)" 
        using join_rule_rule[OF subterm(4,2,3)[unfolded B 3]] using "3"(3) by fastforce 
      {fix i assume "i < length As" 
        from subterm(1) have "set (redex_patterns (Cs!i)) = set (redex_patterns (As!i)) \<union> set (redex_patterns (Bs!i))"
          by (metis "3"(1) "3"(4) B \<open>i < length As\<close> fun_well_arg l_As_Bs local.args nth_mem subterm.prems(2) supt.arg)
      }note IH=this
      {fix \<gamma> p assume rdp:"(\<gamma>, p) \<in> set (redex_patterns C)" 
        have "(\<gamma>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)" proof(cases "p = []")
          case True
          from rdp have "\<alpha> = \<gamma>" unfolding C True using lhs
            by (metis (no_types, lifting) C join_wf_pterm list.set_intros(1) option.sel prod.inject redex_patterns.simps(3) redex_patterns_label subterm(2,3,4)) 
          then show ?thesis unfolding 3 True by simp
        next
          case False
          then obtain p2 i where i:"i < length Cs" "i < length (var_poss_list (lhs \<alpha>))" 
            and p:"p = var_poss_list (lhs \<alpha>) ! i @p2" and "(\<gamma>, p2) \<in> set (redex_patterns (Cs!i))" 
            using C rdp redex_patterns_elem_rule by blast
          with IH consider "(\<gamma>, p2) \<in> set (redex_patterns (As!i))" | "(\<gamma>, p2) \<in> set (redex_patterns (Bs!i))"
            using l_Cs_As by fastforce
          then show ?thesis proof(cases)
            case 1
            with i have "(\<gamma>, p) \<in> set (redex_patterns A)" 
              unfolding 3 p l_Cs_As by (metis "3"(3) redex_patterns_elem_rule')
            then show ?thesis by simp
          next
            case 2
            with i have "(\<gamma>, p) \<in> set (redex_patterns B)" 
              unfolding B l_Cs_As l_As_Bs p alpha_beta using redex_patterns_elem_rule' by blast
            then show ?thesis by simp
          qed
        qed
      }
      moreover 
      {fix \<gamma> p assume rdp:"(\<gamma>, p) \<in> set (redex_patterns A) \<union> set (redex_patterns B)"
        have "(\<gamma>, p) \<in> set (redex_patterns C)" proof(cases "p = []")
          case True
          from rdp lhs have "\<gamma> = \<alpha>" 
            unfolding 3 B alpha_beta True
            by (metis "3"(1) B Un_iff alpha_beta list.set_intros(1) option.inject prod.inject redex_patterns.simps(3) redex_patterns_label subterm.prems(1) subterm.prems(2)) 
          then show ?thesis unfolding C True by simp 
        next
          case False
          from rdp consider "(\<gamma>, p) \<in> set (redex_patterns A)" | "(\<gamma>, p) \<in> set (redex_patterns B)" by force
          then show ?thesis proof(cases) 
            case 1
            then obtain p2 i where i:"i < length As" "i < length (var_poss_list (lhs \<alpha>))" 
              and p:"p = var_poss_list (lhs \<alpha>) ! i @p2" and "(\<gamma>, p2) \<in> set (redex_patterns (As!i))" 
              using 3 redex_patterns_elem_rule False by blast
            with IH have "(\<gamma>, p2) \<in> set (redex_patterns (Cs!i))" by blast 
            with i l_Cs_As show ?thesis unfolding C p
              by (metis redex_patterns_elem_rule')
          next
            case 2
            then obtain p2 i where i:"i < length Bs" "i < length (var_poss_list (lhs \<alpha>))" 
              and p:"p = var_poss_list (lhs \<alpha>) ! i @p2" and "(\<gamma>, p2) \<in> set (redex_patterns (Bs!i))" 
              using B alpha_beta redex_patterns_elem_rule False by blast
            with IH have "(\<gamma>, p2) \<in> set (redex_patterns (Cs!i))" using l_As_Bs by simp 
            with i l_Cs_As l_As_Bs show ?thesis unfolding C p
              by (metis redex_patterns_elem_rule')
          qed
        qed 
      }
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma redex_patterns_join_list: 
  assumes "join_list As = Some A" and "\<forall>a \<in> set As. a \<in> wf_pterm R"
  shows "set (redex_patterns A) = \<Union> (set (map (set \<circ> redex_patterns) As))"  
  using assms proof(induct As arbitrary:A)
  case (Cons a As)
  show ?case proof(cases "As = []")
    case True
    from Cons(2,3) have "a = A" 
      unfolding True join_list.simps by (simp add: join_with_source) 
    then show ?thesis unfolding True by simp
  next
    case False
    then have *:"join_list (a#As) = join_opt a (join_list As)"
      using join_list.elims by blast 
    with Cons(2) obtain A' where A':"join_list As = Some A'" by fastforce
    with Cons(1,3) have "set (redex_patterns A') = \<Union> (set (map (set \<circ> redex_patterns) As))"  
      by simp
    then show ?thesis using redex_patterns_join * Cons(2,3) unfolding A' join_opt.simps
      by (metis (no_types, opaque_lifting) A' Sup_insert insert_iff join_list_wf_pterm list.set(2) list.simps(9) o_apply) 
  qed
qed simp

lemma redex_patterns_context:
  assumes "p \<in> poss s"
  shows "redex_patterns ((ctxt_of_pos_term p (to_pterm s)) \<langle>A\<rangle>) = map (\<lambda>(\<alpha>, q). (\<alpha>,p@q)) (redex_patterns A)" 
  using assms proof(induct p arbitrary:s)
  case (Cons i p')
  from Cons(2) obtain f ss where s:"s = Fun f ss"
    by (meson args_poss)
  from Cons(2) have i:"i < length ss" and p':"p' \<in> poss (ss!i)" 
    unfolding s by auto
  with Cons(1) have IH:"redex_patterns (ctxt_of_pos_term p' (to_pterm (ss!i)))\<langle>A\<rangle> =
    map (\<lambda>(\<alpha>, q). (\<alpha>,p'@q)) (redex_patterns A)" by simp
  from i have l:"length (take i (map to_pterm ss) @ (ctxt_of_pos_term p' (map to_pterm ss ! i))\<langle>A\<rangle> # drop (Suc i) (map to_pterm ss)) = length ss" 
    by simp
  let ?take_i="take i (map to_pterm ss)"
  let ?ith="(ctxt_of_pos_term p' (map to_pterm ss ! i))\<langle>A\<rangle>"
  let ?drop_i="drop (Suc i) (map to_pterm ss)"
  let ?xs="take i (map to_pterm ss) @ (ctxt_of_pos_term p' (map to_pterm ss ! i))\<langle>A\<rangle> # drop (Suc i) (map to_pterm ss)"
  let ?zip="zip [0..<length ss] (map redex_patterns ?xs)" 
  from i have l_zip:"length ?zip = length ss" by auto
  let ?zip1="zip [0..<i] (map redex_patterns ?take_i)" 
  let ?zip2="zip [Suc i..<length ss] (map redex_patterns ?drop_i)"
  have zip:"?zip = ?zip1 @ ((i, redex_patterns ?ith) # ?zip2)"
    unfolding map_append zip_append2 using i by (simp add: upt_conv_Cons)  
  {fix j assume j:"j < length (map (\<lambda>(x, y). map (\<lambda>(\<alpha>, p). (\<alpha>, x # p)) y) ?zip1)" 
    with i have "(map redex_patterns ?take_i)!j = []"
      by (simp add: redex_patterns_to_pterm) 
    with j have "?zip1 ! j = (j, [])" 
      by simp
    with j have "map (\<lambda>(x, y). map (\<lambda>(\<alpha>, p). (\<alpha>, x # p)) y) ?zip1 ! j = []" 
      by simp 
  }
  then have 1:"concat (map (\<lambda>(x, y). map (\<lambda>(\<alpha>, p). (\<alpha>, x # p)) y) ?zip1) = []"
    by (metis length_0_conv length_greater_0_conv less_nat_zero_code nth_concat_split) 
  {fix j assume j:"j < length (map (\<lambda>(x, y). map (\<lambda>(\<alpha>, p). (\<alpha>, x # p)) y) ?zip2)" 
    with i have "(map redex_patterns ?drop_i)!j = []"
      by (simp add: redex_patterns_to_pterm) 
    with j have "?zip2 ! j = (j+Suc i, [])" 
      by simp
    with j have "map (\<lambda>(x, y). map (\<lambda>(\<alpha>, p). (\<alpha>, x # p)) y) ?zip2 ! j = []" 
      by simp 
  }
  then have 2:"concat (map (\<lambda>(x, y). map (\<lambda>(\<alpha>, p). (\<alpha>, x # p)) y) ?zip2) = []"
    by (metis length_0_conv length_greater_0_conv less_nat_zero_code nth_concat_split) 
  show ?case unfolding s to_pterm.simps ctxt_of_pos_term.simps intp_actxt.simps redex_patterns.simps l zip 
    unfolding map_append concat_append 1 list.map(2) concat.simps 2 using IH i by simp
qed simp

lemma redex_patterns_prule:
  assumes l:"length ts = length (var_poss_list (lhs \<alpha>))" 
  shows "redex_patterns (Prule \<alpha> (map to_pterm ts)) = [(\<alpha>, [])]"
proof-
  {fix x assume x:"x \<in> set (map2 (\<lambda>x. map (\<lambda>(\<alpha>, p2). (\<alpha>, x @ p2))) (var_poss_list (lhs \<alpha>)) (map redex_patterns (map to_pterm ts)))"
    from l have "length (map2 (\<lambda>x. map (\<lambda>(\<alpha>, p2). (\<alpha>, x @ p2))) (var_poss_list (lhs \<alpha>)) (map redex_patterns (map to_pterm ts))) = length (var_poss_list (lhs \<alpha>))" 
      by simp
    with x obtain i where i:"i < length (var_poss_list (lhs \<alpha>))" "x = (map2 (\<lambda>x. map (\<lambda>(\<alpha>, p2). (\<alpha>, x @ p2))) (var_poss_list (lhs \<alpha>)) (map redex_patterns (map to_pterm ts)))!i"
      by (metis in_set_idx) 
    from i l have "x = []" 
      using redex_patterns_to_pterm by simp
  }
  then show ?thesis
    unfolding redex_patterns.simps using concat_eq_Nil_conv by blast
qed

lemma redex_patterns_single:
  assumes "p \<in> poss s" and "to_rule \<alpha> \<in> R"
  shows "redex_patterns (ll_single_redex s p \<alpha>) = [(\<alpha>, p)]"
proof-
  let ?As="map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>))"
  let ?A="Prule \<alpha> ?As" 
  have "redex_patterns ?A = [(\<alpha>, [])]" 
    using redex_patterns_prule using length_map by fastforce 
  moreover have "set (redex_patterns (ll_single_redex s p \<alpha>)) = set (map (\<lambda> (\<alpha>, q). (\<alpha>,p@q)) (redex_patterns ?A))"
    using redex_patterns_context assms redex_patterns_to_pterm[of s] unfolding ll_single_redex_def using p_in_poss_to_pterm by fastforce
  ultimately have set:"set (redex_patterns (ll_single_redex s p \<alpha>)) = {(\<alpha>, p)}" 
    by simp
  have wf:"ll_single_redex s p \<alpha> \<in> wf_pterm R"
    using assms left_lin left_linear_trs_def single_redex_wf_pterm by fastforce 
  have sorted:"sorted_wrt (ord.lexordp (<)) (map snd [(\<alpha>, p)])" by simp
  show ?thesis using redex_patterns_equal[OF wf sorted] set by simp
qed  

lemma get_label_imp_rdp:
  assumes "get_label (labeled_source A |_ p) = Some (\<alpha>, 0)"
    and "A \<in> wf_pterm R"
    and "p \<in> poss (labeled_source A)"
  shows "(\<alpha>, p) \<in> set (redex_patterns A)" 
  using assms proof(induct A arbitrary:p)
  case (Pfun f As)
  then show ?case proof(cases p)
    case (Cons i p')
    from Pfun(4) have i:"i < length As" 
      unfolding Cons by simp
    moreover from Pfun(2,4) have "get_label (labeled_source (As!i) |_ p') = Some (\<alpha>, 0)" 
      unfolding Cons by simp
    moreover from Pfun(4) have "p' \<in> poss (labeled_source (As!i))" 
      unfolding Cons using i by simp
    ultimately have "(\<alpha>, p') \<in> set (redex_patterns (As!i))"
      using Pfun(1,3) using nth_mem by blast 
    then show ?thesis 
      unfolding Cons redex_patterns.simps using i by (metis redex_patterns.simps(2) redex_patterns_elem_fun')
  qed simp
next
  case (Prule \<beta> As)
  from Prule(3) obtain f ts where lhs:"lhs \<beta> = Fun f ts"
    by (metis Inl_inject Term.term.simps(4) case_prodD is_Prule.simps(1) is_Prule.simps(3) no_var_lhs term.collapse(2) term.sel(2) wf_pterm.simps) 
  then show ?case proof(cases p)
    case Nil
    from Prule(2,3,4) show ?thesis 
      unfolding Nil labeled_source.simps lhs label_term.simps eval_term.simps subt_at.simps get_label.simps by simp
  next
    case (Cons i' p')
    from Prule(3) have l:"length As = length (var_poss_list (lhs \<beta>))"
      by (metis Inl_inject is_Prule.simps(1) is_Prule.simps(3) length_var_poss_list length_var_rule term.distinct(1) term.inject(2) wf_pterm.simps) 
    from Prule obtain i p2 where p:"p = var_poss_list (lhs \<beta>)!i @ p2" and i:"i < length As" and p2:"p2 \<in> poss (labeled_source (As!i))"
      by (smt (verit) labeled_source_to_term left_lin_no_var_lhs.get_label_Prule left_lin_no_var_lhs_axioms list.distinct(1) local.Cons poss_term_lab_to_term)
    let ?x="vars_term_list (lhs \<beta>) ! i" 
    let ?p1="var_poss_list (lhs \<beta>) ! i" 
    have p1:"?p1 \<in> poss (labeled_lhs \<beta>)"
      by (metis i l label_term_to_term nth_mem poss_term_lab_to_term var_poss_imp_poss var_poss_list_sound) 
    have "labeled_lhs \<beta> |_ ?p1 = Var ?x" 
      using i l by (metis length_var_poss_list var_poss_list_labeled_lhs vars_term_list_labeled_lhs vars_term_list_var_poss_list)
    then have "labeled_source (Prule \<beta> As) |_ ?p1 = labeled_source (As!i)" 
      unfolding labeled_source.simps subt_at_subst[OF p1]
      by (smt (verit) Inl_inject Prule.prems(2) apply_lhs_subst_var_rule comp_eq_dest_lhs eval_term.simps(1) i is_Prule.simps(1) is_Prule.simps(3) 
          l length_map length_remdups_eq length_rev length_var_poss_list map_nth_conv rev_rev_ident term.distinct(1) term.inject(2) wf_pterm.simps) 
    with Prule(2,4) have "get_label (labeled_source (As!i)|_p2) = Some (\<alpha>, 0)" 
      unfolding p labeled_source.simps by auto
    then have "(\<alpha>, p2) \<in> set (redex_patterns (As!i))"
      using Prule(1)[of "As!i" p2] p2 Prule(3) i by (meson fun_well_arg nth_mem)   
    then show ?thesis unfolding p redex_patterns.simps using i
      by (metis l redex_patterns.simps(3) redex_patterns_elem_rule')
  qed
qed simp

lemma redex_pattern_proof_term_equality:
  assumes "A \<in> wf_pterm R" "B \<in> wf_pterm R" 
    and "set (redex_patterns A) = set (redex_patterns B)" 
    and "source A = source B"
  shows "A = B" 
  using assms proof(induct A arbitrary:B)
  case (1 x)
  then show ?case
    using redex_poss_empty_imp_empty_step source_empty_step by force
next
  case (2 As f)
  then show ?case proof(cases B)
    case (Pfun g Bs)
    from 2(4) have f:"f = g" 
      unfolding Pfun by fastforce
    from 2(4) have len:"length As = length Bs"
      unfolding Pfun f by (metis length_map source.simps(2) term.inject(2))
    {fix i assume i:"i < length As" 
      have "set (redex_patterns (As!i)) = set (redex_patterns (Bs!i))" proof(rule ccontr)
        assume "set (redex_patterns (As!i)) \<noteq> set (redex_patterns (Bs!i))" 
        then consider "\<exists>r. r \<in> set (redex_patterns (As!i)) \<and> r \<notin> set (redex_patterns (Bs!i))" | 
                      "\<exists>r. r \<in> set (redex_patterns (Bs!i)) \<and> r \<notin> set (redex_patterns (As!i))"
          by blast
        then show False proof(cases)
          case 1
          then obtain p \<alpha> where "(\<alpha>, p) \<in> set (redex_patterns (As!i))" and B:"(\<alpha>, p) \<notin> set (redex_patterns (Bs!i))"
            by force
          then have "(\<alpha>, i#p) \<in> set (redex_patterns (Pfun f As))"
            by (meson i redex_patterns_elem_fun') 
          moreover from B have "(\<alpha>, i#p) \<notin> set (redex_patterns (Pfun f Bs))"
            by (metis list.inject redex_patterns_elem_fun) 
          ultimately show ?thesis
            using "2.prems"(2) Pfun f by blast
        next
          case 2
           then obtain p \<alpha> where "(\<alpha>, p) \<in> set (redex_patterns (Bs!i))" and A:"(\<alpha>, p) \<notin> set (redex_patterns (As!i))"
            by force
          then have "(\<alpha>, i#p) \<in> set (redex_patterns (Pfun f Bs))"
            by (metis i len redex_patterns_elem_fun')
          moreover from A have "(\<alpha>, i#p) \<notin> set (redex_patterns (Pfun f As))"
            by (metis list.inject redex_patterns_elem_fun) 
          ultimately show ?thesis
            using "2.prems"(2) Pfun f by blast
        qed
      qed
      moreover have "(Bs!i) \<in> wf_pterm R"
        using 2(2) Pfun i len by auto
      ultimately have "As!i = Bs!i" 
        using 2(1,4) by (metis Pfun i len nth_map nth_mem source.simps(2) term.inject(2)) 
    }
    then show ?thesis 
      unfolding Pfun f using len using nth_equalityI by blast
  next
    case (Prule \<alpha> Bs)
    with 2(3) show ?thesis
      by (metis list.distinct(1) list.set_intros(1) redex_patterns.simps(3) redex_patterns_elem_fun) 
  qed simp
next
  case (3 \<alpha> As)
  then show ?case proof(cases B)
    case (Pfun g Bs)
    with 3(5) show ?thesis
      by (metis list.distinct(1) list.set_intros(1) redex_patterns.simps(3) redex_patterns_elem_fun)
  next
    case (Prule \<beta> Bs)
    from 3(5) have \<alpha>:"\<alpha> = \<beta>" 
      unfolding Prule using distinct_snd_rdp
      by (metis "3.prems"(1) Pair_inject Prule left_lin_no_var_lhs.redex_patterns_label 
          left_lin_no_var_lhs_axioms list.set_intros(1) option.inject redex_patterns.simps(3))
    from 3 have len:"length As = length Bs"
      using Prule \<alpha> by (metis length_args_well_Prule wf_pterm.intros(3)) 
    have len2:"length (var_poss_list (lhs \<beta>)) = length Bs"
      by (metis "3.hyps"(1) "3.hyps"(2) \<alpha> len length_var_poss_list length_var_rule)
    {fix i assume i:"i < length As" 
      obtain pi where pi:"var_poss_list (lhs \<beta>) ! i = pi"
        by auto 
      have "set (redex_patterns (As!i)) = set (redex_patterns (Bs!i))" proof(rule ccontr)
        assume "set (redex_patterns (As!i)) \<noteq> set (redex_patterns (Bs!i))" 
        then consider "\<exists>r. r \<in> set (redex_patterns (As!i)) \<and> r \<notin> set (redex_patterns (Bs!i))" | 
                      "\<exists>r. r \<in> set (redex_patterns (Bs!i)) \<and> r \<notin> set (redex_patterns (As!i))"
          by blast
        then show False proof(cases)
          case 1
          then obtain p \<beta> where "(\<beta>, p) \<in> set (redex_patterns (As!i))" and B:"(\<beta>, p) \<notin> set (redex_patterns (Bs!i))"
            by force
          then show False
            using 3(4,5) by (metis Prule \<alpha> i len len2 redex_patterns_elem_rule' redex_patterns_rule'') 
        next
          case 2
           then obtain p \<beta> where "(\<beta>, p) \<in> set (redex_patterns (Bs!i))" and A:"(\<beta>, p) \<notin> set (redex_patterns (As!i))"
            by force
          then show False
            using 3 by (metis Prule \<alpha> i len len2 redex_patterns_elem_rule' redex_patterns_rule'' wf_pterm.intros(3)) 
        qed
      qed
      moreover have "(Bs!i) \<in> wf_pterm R"
        using "3.prems"(1) Prule i len by auto
      moreover have "co_initial (As!i) (Bs!i)"
        using 3 by (metis Prule \<alpha> co_init_prule i wf_pterm.intros(3))
      ultimately have "As!i = Bs!i" 
        using 3(3) by (simp add: i)
    }
    then show ?thesis 
      unfolding Prule \<alpha> using len using nth_equalityI by blast
  qed simp
qed


end

abbreviation single_steps :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm list" 
  where "single_steps A \<equiv> map (\<lambda> (\<alpha>, p). ll_single_redex (source A) p \<alpha>) (redex_patterns A)"

context left_lin_wf_trs
begin

lemma ll_no_var_lhs: "left_lin_no_var_lhs R"
  by (simp add: left_lin_axioms left_lin_no_var_lhs_def no_var_lhs_axioms)

lemma single_step_redex_patterns:
  assumes "A \<in> wf_pterm R" "\<Delta> \<in> set (single_steps A)" 
  shows "\<exists>p \<alpha>. \<Delta> = ll_single_redex (source A) p \<alpha> \<and> (\<alpha>, p) \<in> set (redex_patterns A) \<and> redex_patterns \<Delta> = [(\<alpha>, p)]"
proof-
  from assms obtain p \<alpha> where \<Delta>:"\<Delta> = ll_single_redex (source A) p \<alpha>" and rdp:"(\<alpha>, p) \<in> set (redex_patterns A)"
    by auto
  moreover have "to_rule \<alpha> \<in> R"
    using rdp assms(1) labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by fastforce 
  moreover have "p \<in> poss (source A)"
    using assms rdp left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by blast 
  ultimately show ?thesis 
    using \<Delta> left_lin_no_var_lhs.redex_patterns_single[OF ll_no_var_lhs] by blast
qed

lemma single_step_wf:
  assumes "A \<in> wf_pterm R" and "\<Delta> \<in> set (single_steps A)"
  shows "\<Delta> \<in> wf_pterm R" 
proof-
  from assms obtain p \<alpha> where p:"p \<in> poss (source A)" "\<Delta> = ll_single_redex (source A) p \<alpha>" and "get_label ((labeled_source A)|_p) = Some (\<alpha>, 0)" 
    using left_lin_no_var_lhs.redex_patterns_label left_lin_no_var_lhs.redex_patterns_subset_possL possL_subset_poss_source ll_no_var_lhs by fastforce
  then have "to_rule \<alpha> \<in> R"
    using assms(1) labeled_wf_pterm_rule_in_TRS by fastforce   
  with p show ?thesis using single_redex_wf_pterm
    using left_lin left_linear_trs_def by fastforce
qed

lemma source_single_step:
  assumes \<Delta>:"\<Delta> \<in> set (single_steps A)" and wf:"A \<in> wf_pterm R"
  shows "source \<Delta> = source A" 
proof-
  let ?s="source A"
  from \<Delta> obtain p \<alpha> where pa:"\<Delta> = ll_single_redex ?s p \<alpha>" "(\<alpha>, p) \<in> set (redex_patterns A)"
    by auto 
  from pa have lab_p:"get_label (labeled_source A |_p) = Some (\<alpha>, 0)" and p:"p \<in> poss ?s" 
    using left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs wf by blast+
  from lab_p p obtain p' where p':"p'\<in>poss A" and ctxt:"ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term p' A)" 
    and Ap':"A |_ p' = Prule \<alpha> (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)])"
    using poss_labeled_source wf by force
  have l:"length (var_rule \<alpha>) = length (var_poss_list (lhs \<alpha>))"
    using wf by (metis Ap' Inl_inject Term.term.simps(4) is_Prule.simps(1) is_Prule.simps(3) length_var_poss_list length_var_rule p' subt_at_is_wf_pterm term.inject(2) wf_pterm.simps)
  {fix i assume i:"i < length (var_rule \<alpha>)" 
    let ?pi="var_poss_list (lhs \<alpha>)!i" 
    obtain x where x:"lhs \<alpha> |_ ?pi = Var x" "var_rule \<alpha>!i = x"
      by (metis comp_apply i l length_remdups_eq length_rev length_var_poss_list rev_rev_ident vars_term_list_var_poss_list) 
    have "?s|_p = lhs \<alpha> \<cdot> \<langle>map source (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)])\<rangle>\<^sub>\<alpha>" 
      using Ap' ctxt by (metis ctxt_of_pos_term_well ctxt_supt_id local.wf p p' replace_at_subt_at source.simps(3) source_ctxt_apply_term) 
    moreover have "lhs \<alpha> \<cdot> \<langle>map source (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)])\<rangle>\<^sub>\<alpha> |_ ?pi = map source (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)])!i" 
      using x by (smt (verit, ccfv_SIG) diff_zero eval_term.simps(1) i l length_upt lhs_subst_var_i map_eq_imp_length_eq map_nth nth_mem subt_at_subst var_poss_imp_poss var_poss_list_sound) 
    ultimately have "?s|_(p@?pi) = source (A |_ (p' @ [i]))" using i p by auto 
    then have "map source (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)]) !i = map (\<lambda>pi. source A |_ (p @ pi)) (var_poss_list (lhs \<alpha>)) ! i" 
      using l i by auto
  }
  with l have "map source (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)]) = map (\<lambda>pi. source A |_ (p @ pi)) (var_poss_list (lhs \<alpha>))"
    by (simp add: map_equality_iff) 
  then have "source (A|_p') = lhs \<alpha> \<cdot> \<langle>map (\<lambda>pi. ?s |_ (p @ pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>" 
    unfolding Ap' source.simps by simp
  with ctxt show ?thesis unfolding pa(1) source_single_redex[OF p] using p'
    by (metis ctxt_of_pos_term_well ctxt_supt_id wf source_ctxt_apply_term) 
qed

lemma single_redex_single_step:
  assumes \<Delta>:"\<Delta> = ll_single_redex s p \<alpha>" 
    and p:"p \<in> poss s" and \<alpha>:"to_rule \<alpha> \<in> R"
    and src:"source \<Delta> = s"
  shows "single_steps \<Delta> = [\<Delta>]" 
  using src unfolding \<Delta> left_lin_no_var_lhs.redex_patterns_single[OF ll_no_var_lhs p \<alpha>] by simp 

lemma single_step_label_imp_label:
  assumes \<Delta>:"\<Delta> \<in> set (single_steps A)" and q:"q \<in> poss (labeled_source \<Delta>)" and wf:"A \<in> wf_pterm R"
    and lab:"get_label (labeled_source \<Delta>|_q) = Some l"
  shows "get_label (labeled_source A |_q) = Some l"
proof-
  let ?s="source A"
  from \<Delta> obtain p \<alpha> where pa:"\<Delta> = ll_single_redex ?s p \<alpha>" "(\<alpha>, p) \<in> set (redex_patterns A)"
    by auto 
  from pa have lab_p:"get_label (labeled_source A |_p) = Some (\<alpha>, 0)" and p:"p \<in> poss (source A)" 
    using left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs wf by blast+
  from pa lab obtain q' where l:"l = (\<alpha>, size q')" and q':"q = p@q'" "q' \<in> fun_poss (lhs \<alpha>)" 
    using single_redex_label[OF pa(1) p] q pa(2) wf
    by (metis labeled_source_to_term labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs poss_term_lab_to_term prod.collapse)   
  from lab_p p obtain p' where "p'\<in>poss A" and "ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term p' A)" and "A |_ p' = Prule \<alpha> (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)])"
    using poss_labeled_source wf by force
  then have "labeled_source A = (ctxt_of_pos_term p (labeled_source A))\<langle>labeled_source (Prule \<alpha> (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)]))\<rangle>" 
    using label_source_ctxt p wf by (metis ctxt_supt_id) 
  then have "labeled_source A|_q = labeled_lhs \<alpha> \<cdot> \<langle>map labeled_source (map (\<lambda>i. A |_ (p' @ [i])) [0..<length (var_rule \<alpha>)])\<rangle>\<^sub>\<alpha> |_q'"
    unfolding q' labeled_source.simps by (metis labeled_source.simps(3) labeled_source_to_term p poss_term_lab_to_term subt_at_append subt_at_ctxt_of_pos_term) 
  then have "get_label (labeled_source A|_q) = Some (\<alpha>, size q')" 
    using q'(2) by (simp add: label_term_increase) 
  with l show ?thesis by simp
qed

lemma single_steps_measure:
  assumes \<Delta>1 :"\<Delta>1 \<in> set (single_steps A)" and \<Delta>2:"\<Delta>2 \<in> set (single_steps A)" 
    and wf:"A \<in> wf_pterm R" and neq:"\<Delta>1 \<noteq> \<Delta>2" 
  shows "measure_ov \<Delta>1 \<Delta>2 = 0" 
proof-
  let ?s="source A"
  from \<Delta>1 obtain p \<alpha> where pa:"\<Delta>1 = ll_single_redex ?s p \<alpha>" "(\<alpha>, p) \<in> set (redex_patterns A)"
    by auto 
  from \<Delta>2 obtain q \<beta> where qb:"\<Delta>2 = ll_single_redex ?s q \<beta>" "(\<beta>, q) \<in> set (redex_patterns A)"
    by auto  
  from neq have pq:"p \<noteq> q \<or> \<alpha> \<noteq> \<beta>"
    using pa(1) qb(1) by force 
  {assume "measure_ov \<Delta>1 \<Delta>2 \<noteq> 0" 
    then obtain r where r1:"r \<in> possL \<Delta>1" and r2:"r \<in> possL \<Delta>2"
      by (metis card.empty disjoint_iff) 
    from r1 obtain p' where p':"r = p@p'" and l1:"get_label (labeled_source \<Delta>1 |_r) = Some (\<alpha>, size p')" 
      using single_redex_label[OF pa(1)] wf
      by (smt (verit, ccfv_SIG) labeled_source_to_term labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs pa(2) possL_obtain_label possL_subset_poss_source poss_term_lab_to_term subsetD)  
    from r2 obtain q' where q':"r = q@q'" and l2:"get_label (labeled_source \<Delta>2 |_r) = Some (\<beta>, size q')" 
      using single_redex_label[OF qb(1)] wf
      by (smt (verit, ccfv_SIG) labeled_source_to_term labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs qb(2) possL_obtain_label possL_subset_poss_source poss_term_lab_to_term subsetD)  
    from l1 have "get_label (labeled_source A |_r) = Some (\<alpha>, size p')"
      using \<Delta>1 labelposs_subs_poss wf r1 single_step_label_imp_label by blast
    moreover from l2 have "get_label (labeled_source A |_r) = Some (\<beta>, size q')"
      using \<Delta>2 labelposs_subs_poss wf r2 single_step_label_imp_label by blast 
    moreover from pq have "p' \<noteq> q' \<or> \<alpha> \<noteq> \<beta>" 
      using p' q' by blast
    ultimately have False using p' q' by auto
  }
  then show ?thesis by auto
qed

lemma single_steps_orth:
  assumes \<Delta>1:"\<Delta>1 \<in> set (single_steps A)" and \<Delta>2:"\<Delta>2 \<in> set (single_steps A)" and wf:"A \<in> wf_pterm R"
  shows "\<Delta>1 \<bottom>\<^sub>p \<Delta>2" 
  using single_steps_measure[OF \<Delta>1 \<Delta>2 wf] equal_imp_orthogonal
  by (metis \<Delta>1 \<Delta>2 ll_no_var_lhs local.wf measure_zero_imp_orthogonal single_step_wf source_single_step) 

lemma redex_patterns_below:
  assumes wf:"A \<in> wf_pterm R" 
  and "(\<alpha>, p) \<in> set (redex_patterns A)" 
  and "(\<beta>, p@q) \<in> set (redex_patterns A)" and "q \<noteq> []"
shows "q \<notin> fun_poss (lhs \<alpha>)" 
proof-
  let ?\<Delta>1="ll_single_redex (source A) p \<alpha>" 
  let ?\<Delta>2="ll_single_redex (source A) (p@q) \<beta>"
  from assms have \<Delta>1:"?\<Delta>1 \<in> set (single_steps A)"
    by force  
  from assms have \<Delta>2:"?\<Delta>2 \<in> set (single_steps A)"
    by force  
  from assms(1,2) have possL1:"possL ?\<Delta>1 = {p@p' | p'. p' \<in> fun_poss (lhs \<alpha>)}"
    by (metis (no_types, lifting) left_lin_no_var_lhs.redex_pattern_rule_symbol left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs single_redex_possL) 
  from assms(1,3) have possL2:"possL ?\<Delta>2 = {(p@q)@p' | p'. p' \<in> fun_poss (lhs \<beta>)}"
    using left_lin.single_redex_possL left_lin_axioms left_lin_no_var_lhs.redex_pattern_rule_symbol left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by blast 
  from assms have neq:"?\<Delta>1 \<noteq> ?\<Delta>2"
    by (metis Pair_inject left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs self_append_conv single_redex_neq) 
  from single_steps_measure[OF \<Delta>1 \<Delta>2 wf neq] have "possL ?\<Delta>1 \<inter> possL ?\<Delta>2 = {}"
    by (simp add: finite_possL) 
  moreover have "[] \<in> fun_poss (lhs \<beta>)" proof-
    have "to_rule \<beta> \<in> R"
      using assms(1) assms(3) left_lin_no_var_lhs.redex_pattern_rule_symbol ll_no_var_lhs by blast
    then show ?thesis
      using wf_trs_alt wf_trs_imp_lhs_Fun by fastforce 
  qed
  ultimately show ?thesis 
    unfolding possL1 possL2 by auto
qed

lemma single_steps_singleton:
  assumes A_wf:"A \<in> wf_pterm R" and \<Delta>:"single_steps A = [\<Delta>]" 
  shows "A = \<Delta>" 
proof-
  obtain p \<alpha> where rdp_\<Delta>:"\<Delta> = ll_single_redex (source A) p \<alpha>" "(\<alpha>, p) \<in> set (redex_patterns A)" "redex_patterns \<Delta> = [(\<alpha>, p)]"
    using single_step_redex_patterns[OF A_wf] \<Delta> by auto
  then have rdp_A:"redex_patterns A = [(\<alpha>, p)]"
    by (smt (verit) \<Delta> in_set_simps(2) list.map_disc_iff map_eq_Cons_D) 
  then show ?thesis 
    using left_lin_no_var_lhs.redex_pattern_proof_term_equality[OF ll_no_var_lhs A_wf]
    by (metis A_wf \<Delta> list.set_intros(1) rdp_\<Delta>(3) single_step_wf source_single_step) 
qed
end

context left_lin_no_var_lhs
begin
lemma measure_ov_imp_single_step_ov: 
  assumes "measure_ov A B \<noteq> 0" and wf:"A \<in> wf_pterm R"
  shows "\<exists>\<Delta> \<in> set (single_steps A). measure_ov \<Delta> B \<noteq> 0" 
proof-
  from assms obtain r where r1:"r \<in> possL A" and r2:"r \<in> possL B"
    by (metis card.empty disjoint_iff) 
  then obtain \<alpha> n where lab:"get_label (labeled_source A |_ r) = Some (\<alpha>, n)"
    using possL_obtain_label by blast 
  with wf r1 obtain r1 r2 where r:"r = r1@r2" and lab_r1:"get_label (labeled_source A |_r1) = Some (\<alpha>, 0)" and n:"length r2 = n"
    by (metis (no_types, lifting) append_take_drop_id diff_diff_cancel label_term_max_value labelposs_subs_poss length_drop obtain_label_root subsetD) 
  from r r1 have r1_pos:"r1 \<in> poss (labeled_source A)"
    using labelposs_subs_poss poss_append_poss by blast 
  then obtain q where q:"q\<in>poss A" and ctxt:"ctxt_of_pos_term r1 (source A) = source_ctxt (ctxt_of_pos_term q A)"  
    and Aq:"A |_ q = Prule \<alpha> (map (\<lambda>i. A |_ (q @ [i])) [0..<length (var_rule \<alpha>)])" 
    using poss_labeled_source wf lab_r1 by blast
  with r r1 have r2_pos:"r2 \<in> poss (source (Prule \<alpha> (map (\<lambda>i. A |_ (q @ [i])) [0..<length (var_rule \<alpha>)])))"
    by (metis (no_types, lifting) ctxt_supt_id fun_poss_imp_poss label_source_ctxt labeled_source_to_term labelposs_subs_fun_poss_source local.wf poss_term_lab_to_term r1_pos replace_at_subt_at subterm_poss_conv) 
  from Aq q wf have "Prule \<alpha> (map (\<lambda>i. A |_ (q @ [i])) [0..<length (var_rule \<alpha>)]) \<in> wf_pterm R"
    using subt_at_is_wf_pterm by auto 
  moreover then have "is_Fun (lhs \<alpha>)" using no_var_lhs
    using wf_pterm.cases by fastforce 
  moreover from lab ctxt have "get_label (labeled_source (Prule \<alpha> (map (\<lambda>i. A |_ (q @ [i])) [0..<length (var_rule \<alpha>)])) |_r2) = Some (\<alpha>, n)"
    by (metis (no_types, lifting) Aq ctxt_supt_id label_source_ctxt labeled_source_to_term local.wf poss_term_lab_to_term q r r1_pos replace_at_subt_at subt_at_append) 
  ultimately have r2_funposs:"r2 \<in> fun_poss (lhs \<alpha>)"
    using labeled_poss_in_lhs[OF r2_pos] n by blast
  let ?\<Delta>="ll_single_redex (source A) r1 \<alpha>"
  from lab_r1 r1_pos have rdp:"(\<alpha>, r1) \<in> set (redex_patterns A)" 
    using redex_patterns_label wf by auto
  then have \<Delta>:"?\<Delta> \<in> set (single_steps A)" by force 
  from r2 have "measure_ov ?\<Delta> B \<noteq> 0"
    by (smt (verit, ccfv_threshold) rdp labeled_sources_imp_measure_not_zero labeled_wf_pterm_rule_in_TRS labelposs_subs_poss wf mem_Collect_eq option.simps(3) possL_obtain_label r r1_pos r2_funposs redex_patterns_label rel_simps(70) single_redex_possL subsetD) 
  with \<Delta> show ?thesis by blast 
qed
end

context left_lin_no_var_lhs
begin
lemma label_single_step: 
  assumes "p \<in> poss (labeled_source A)" "A \<in> wf_pterm R" 
    and "get_label (labeled_source A |_ p) = Some (\<alpha>, n)"
  shows "\<exists>Ai. Ai \<in> set (single_steps A) \<and> get_label (labeled_source Ai |_ p) = Some (\<alpha>, n)" 
proof- 
  let ?p1="take (length p - n) p"
  let ?p2="drop (length p - n) p"
  let ?xs="map (to_pterm \<circ> (\<lambda>pi. (source A)|_(p@pi))) (var_poss_list (lhs \<alpha>))"
  from assms(1) have p1_pos:"?p1 \<in> poss (labeled_source A)"
    by (metis append_take_drop_id poss_append_poss) 
  have lab:"get_label (labeled_source A |_ ?p1) = Some (\<alpha>, 0)"
    using obtain_label_root[OF assms(1) assms(3) assms(2)] by simp
  with assms have rdp:"(\<alpha>, ?p1) \<in> set (redex_patterns A)"
    using redex_patterns_label[OF assms(2)] by (metis labeled_source_to_term obtain_label_root poss_term_lab_to_term) 
  then have "ll_single_redex (source A) ?p1 \<alpha> \<in> set (single_steps A)" by force
  then obtain Ai where Ai:"Ai \<in> set (single_steps A)" "Ai = ll_single_redex (source A) ?p1 \<alpha>" 
    by presburger
  from rdp obtain p' As where p':"A|_p' = Prule \<alpha> As" "p' \<in> poss A" "ctxt_of_pos_term ?p1 (source A) = source_ctxt (ctxt_of_pos_term p' A)"
    using poss_labeled_source[OF p1_pos] lab assms(2) by blast
  from p' assms(2) have "A|_p' \<in> wf_pterm R"
    using subt_at_is_wf_pterm by blast 
  moreover from p' assms have "get_label (labeled_source (A|_p') |_ ?p2) = Some (\<alpha>, n)"
    by (smt (verit, ccfv_SIG) append_take_drop_id ctxt_supt_id label_source_ctxt p1_pos rdp redex_patterns_label replace_at_subt_at subterm_poss_conv) 
  ultimately have p2_pos:"?p2 \<in> fun_poss (lhs \<alpha>)"
    using labeled_poss_in_lhs no_var_lhs assms p'
    by (smt (verit, ccfv_threshold) append_take_drop_id case_prod_conv ctxt_of_pos_term_well ctxt_supt_id diff_diff_cancel label_term_max_value 
        labeled_source_to_term labeled_wf_pterm_rule_in_TRS length_drop  poss_append_poss poss_term_lab_to_term replace_at_subt_at source_ctxt_apply_term)
  then have l:"get_label (labeled_source (Prule \<alpha> ?xs) |_ ?p2) = Some (\<alpha>, n)"
    using label_term_increase assms by (metis (no_types, lifting) add_0  diff_diff_cancel label_term_max_value labeled_source.simps(3) length_drop)
  from p1_pos have "?p1 \<in> poss (source A)" by simp
  then have "get_label (labeled_source Ai |_ p) = Some (\<alpha>, n)" 
    unfolding Ai(2) by (metis p2_pos append_take_drop_id l label_ctxt_apply_term label_term_increase labeled_source.simps(3) ll_single_redex_def)
  with Ai show ?thesis
    by blast 
qed

lemma proof_term_matches:
  assumes "A \<in> wf_pterm R" "B \<in> wf_pterm R" "linear_term A" 
    and "\<And>\<alpha> r. (\<alpha>, r) \<in> set (redex_patterns A) = ((\<alpha>, r) \<in> set (redex_patterns B) \<and> r \<in> fun_poss (source A))"  
    and "source A \<cdot> \<sigma> = source B"
  shows "A \<cdot> (mk_subst Var (match_substs A B)) = B" 
proof-
  {fix p g ts assume "p \<in> poss A" "A|_p = Fun g ts" 
    with assms have "\<exists> Bs. length ts = length Bs \<and> B|_p = Fun g Bs" 
      using assms proof(induct A arbitrary: B p rule:pterm_induct)
      case (Pfun f As)
      then have "\<And>\<alpha>. (\<alpha>, []) \<notin> set (redex_patterns (Pfun f As))"
        by (meson list.distinct(1) redex_patterns_elem_fun) 
      with Pfun(5) have "\<not> (is_Prule B)"
        by (metis empty_pos_in_poss is_FunI is_Prule.elims(2) list.set_intros(1) poss_is_Fun_fun_poss redex_patterns.simps(3) source.simps(2) subt_at.simps(1)) 
      with Pfun(6) obtain Bs where B:"B = Pfun f Bs" and l:"length Bs = length As"
        by (smt (verit, del_insts) eval_term.simps(2) is_Prule.elims(3) length_map source.simps(1) source.simps(2) term.distinct(1) term.inject(2))
      then show ?case proof(cases p)
        case Nil
        from Pfun(8) show ?thesis unfolding Nil B using l by simp
      next
        case (Cons i p')
        from Pfun(7) have i:"i < length As" and p':"p' \<in> poss (As!i)" and a:"As!i \<in> set As"
          unfolding Cons by simp_all
        from Pfun(8) have at_p':"(As!i)|_p' = Fun g ts" 
          unfolding Cons by simp
        from Pfun(2) have a_wf:"As!i \<in> wf_pterm R"
          using i nth_mem by blast 
        from Pfun(3) have b_wf:"Bs!i \<in> wf_pterm R" 
          unfolding B using i l by auto
        from Pfun(4) have a_lin:"linear_term (As!i)" 
          using i by simp
        {fix \<alpha> r assume "(\<alpha>, r) \<in> set (redex_patterns (As!i))" 
          then have "(\<alpha>, i#r) \<in> set (redex_patterns (Pfun f As))"
            by (meson i redex_patterns_elem_fun') 
          with Pfun(5) have "(\<alpha>, r) \<in> set (redex_patterns (Bs!i)) \<and> i#r \<in> fun_poss (source (Pfun f As))" 
            unfolding B by (metis list.inject redex_patterns_elem_fun) 
          then have "(\<alpha>, r) \<in> set (redex_patterns (Bs!i)) \<and> r \<in> fun_poss (source (As!i))" 
            using i by simp
        } moreover {fix \<alpha> r assume "(\<alpha>, r) \<in> set (redex_patterns (Bs!i))" and r:"r \<in> fun_poss (source (As!i))" 
          then have "(\<alpha>, i#r) \<in> set (redex_patterns B)"
            unfolding B using i l by (metis redex_patterns_elem_fun') 
          moreover from r have "i#r \<in> fun_poss (source (Pfun f As))" 
            using i unfolding source.simps fun_poss.simps length_map by simp
          ultimately have "(\<alpha>, r) \<in> set (redex_patterns (As!i))" 
            using Pfun(5) i by (metis list.inject redex_patterns_elem_fun) 
        }
        ultimately have rdp:"\<And>\<alpha> r. ((\<alpha>, r) \<in> set (redex_patterns (As ! i))) = ((\<alpha>, r) \<in> set (redex_patterns (Bs ! i)) \<and> r \<in> fun_poss (source (As ! i)))" 
          by blast
        from Pfun(6) have sigma:"source (As!i) \<cdot> \<sigma> = source (Bs!i)"
          unfolding B source.simps eval_term.simps using i l using map_nth_conv by fastforce 
        from Pfun(1)[OF a a_wf b_wf a_lin rdp sigma p' at_p' a_wf b_wf a_lin rdp sigma] 
          obtain ss where "length ts = length ss" and "Bs!i |_ p' = Fun g ss" by blast
        then show ?thesis unfolding B Cons using i l by simp
      qed
    next
      case (Prule \<alpha> As)
      from Prule(5) have "(\<alpha>, []) \<in> set (redex_patterns B)" 
        by auto 
      then obtain Bs where B:"B = Prule \<alpha> Bs"
        by (smt (verit, ccfv_threshold) Prule.prems(2) in_set_idx in_set_simps(3) redex_patterns_elem_fun less_nat_zero_code list.distinct(1) 
            nat_neq_iff nth_Cons_0 order_pos.dual_order.refl prod.inject redex_patterns.simps(1) redex_patterns.simps(3) redex_patterns_order wf_pterm.simps) 
      with Prule(2,3) have l:"length As = length Bs"
        using length_args_well_Prule by blast 
      show ?case proof(cases p)
        case Nil
        from Prule(8) show ?thesis unfolding Nil B using l by simp
      next
        case (Cons i p')
        from Prule(7) have i:"i < length As" and p':"p' \<in> poss (As!i)" and a:"As!i \<in> set As"
          unfolding Cons by simp_all
        from Prule(8) have at_p':"(As!i)|_p' = Fun g ts" 
          unfolding Cons by simp
        from Prule(2) have a_wf:"As!i \<in> wf_pterm R"
          using i nth_mem by blast 
        from Prule(3) have b_wf:"Bs!i \<in> wf_pterm R" 
          unfolding B using i l by auto
        from Prule(4) have a_lin:"linear_term (As!i)" 
          using i by simp
        let ?pi="var_poss_list (lhs \<alpha>) ! i" 
        let ?xi="vars_term_list (lhs \<alpha>) ! i"
        have i':"i < length (var_poss_list (lhs \<alpha>))" 
          using i Prule(2) by (metis Inl_inject is_Prule.simps(1) is_Prule.simps(3) length_var_poss_list length_var_rule term.distinct(1) term.inject(2) wf_pterm.simps) 
        have eval_lhs':"\<And>\<sigma>. lhs \<alpha> \<cdot> \<sigma> |_ ?pi = \<sigma> ?xi"
          by (metis eval_term.simps(1) i' length_var_poss_list nth_mem subt_at_subst var_poss_imp_poss var_poss_list_sound vars_term_list_var_poss_list)
        then have eval_lhs:"\<And>\<sigma> q. lhs \<alpha> \<cdot> \<sigma> |_ (?pi@q) = \<sigma> ?xi |_ q"
          by (smt (verit) i' nth_mem poss_imp_subst_poss subt_at_append var_poss_imp_poss var_poss_list_sound) 
        have "i < length (map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<alpha>)) (map redex_patterns Bs))" 
          unfolding length_map length_zip using i l i' by simp
        moreover have "zip (var_poss_list (lhs \<alpha>)) (map redex_patterns Bs) ! i = (?pi, redex_patterns (Bs!i))"
          using i i' l by force  
        ultimately have map_rdp:"(map2 (\<lambda>p1. map (\<lambda>(\<alpha>, p2). (\<alpha>, p1 @ p2))) (var_poss_list (lhs \<alpha>)) (map redex_patterns Bs))!i =  map (\<lambda>(\<alpha>, p2). (\<alpha>, ?pi @ p2)) (redex_patterns (Bs!i))"
          by simp
        have l':"length (var_rule \<alpha>) = length (vars_term_list (lhs \<alpha>))"
          using B Prule.prems(2) left_lin.length_var_rule left_lin_axioms wf_pterm.simps by fastforce 
        {fix \<beta> r assume \<beta>r:"(\<beta>, r) \<in> set (redex_patterns (As!i))" 
          from i' have "(\<beta>, ?pi@r) \<in> set (redex_patterns (Prule \<alpha> As))"
            using redex_patterns_elem_rule'[OF \<beta>r i] by simp
          with Prule(5) have 1:"(\<beta>, ?pi@r) \<in> set (redex_patterns B)" and 2:"?pi@r \<in> fun_poss (source (Prule \<alpha> As))"
            by presburger+  
          from 1 have "(\<beta>, r) \<in> set (redex_patterns (Bs!i))"
            using redex_patterns_rule'' by (metis B Prule.prems(2) i l) 
          moreover have "r \<in> fun_poss (source (As!i))"
            by (metis \<beta>r a_wf get_label_imp_labelposs labeled_source_to_term labelposs_subs_fun_poss_source left_lin_no_var_lhs.redex_patterns_label left_lin_no_var_lhs_axioms option.distinct(1) poss_term_lab_to_term) 
          ultimately have "(\<beta>, r) \<in> set (redex_patterns (Bs!i)) \<and> r \<in> fun_poss (source (As!i))" 
            by simp
        } moreover {fix \<beta> r assume \<beta>r:"(\<beta>, r) \<in> set (redex_patterns (Bs!i))" and r:"r \<in> fun_poss (source (As!i))" 
          let ?x="var_rule \<alpha> ! i" 
          from l' have x:"lhs \<alpha> |_ ?pi = Var ?x" 
            using i by (metis comp_apply eval_lhs' length_remdups_eq length_rev rev_rev_ident subst_apply_term_empty) 
          with r have r:"r \<in> fun_poss (lhs \<alpha> |_ ?pi \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>)"
            using lhs_subst_var_i l' i i' by (metis (mono_tags, lifting) eval_term.simps(1) length_map length_var_poss_list nth_map) 
          from \<beta>r have "(\<beta>, ?pi@r) \<in> set (redex_patterns B)"
            unfolding B using i l using redex_patterns_elem_rule'[OF \<beta>r i[unfolded l] i'] by simp
          moreover from r x have "?pi@r \<in> fun_poss (source (Prule \<alpha> As))" 
            using i unfolding source.simps fun_poss.simps
            by (metis (no_types, lifting) eval_lhs eval_lhs' fun_poss_fun_conv fun_poss_imp_poss i' is_FunI nth_mem 
                pos_append_poss poss_imp_subst_poss poss_is_Fun_fun_poss subt_at_subst var_poss_imp_poss var_poss_list_sound)
          ultimately have "(\<beta>, ?pi @ r) \<in> set (redex_patterns (Prule \<alpha> As))" 
            using Prule(5) by presburger
          then have "(\<beta>, r) \<in> set (redex_patterns (As!i))" 
            using i redex_patterns_rule'' Prule.prems(1) by blast 
        }
        ultimately have rdp:"\<And>\<alpha> r. ((\<alpha>, r) \<in> set (redex_patterns (As ! i))) = ((\<alpha>, r) \<in> set (redex_patterns (Bs ! i)) \<and> r \<in> fun_poss (source (As ! i)))" 
          by blast
        from Prule(6) have sigma:"source (As!i) \<cdot> \<sigma> = source (Bs!i)"
          unfolding B source.simps eval_term.simps using i l map_nth_conv
          by (smt (verit, best) B Inl_inject Prule.prems(2) apply_lhs_subst_var_rule comp_apply eval_lhs' i' is_Prule.simps(1) is_Prule.simps(3) length_map length_remdups_eq length_rev length_var_rule nth_mem poss_imp_subst_poss rev_swap subt_at_subst term.distinct(1) term.inject(2) var_poss_imp_poss var_poss_list_sound wf_pterm.simps)
        from Prule(1)[OF a a_wf b_wf a_lin rdp sigma p' at_p' a_wf b_wf a_lin rdp sigma] 
          obtain ss where "length ts = length ss" and "Bs!i |_ p' = Fun g ss" by blast
        then show ?thesis unfolding B Cons using i l by simp
      qed
    qed simp
  }
  then show ?thesis using fun_poss_eq_imp_matches[OF assms(3)] by simp
qed 
end

context left_lin_wf_trs
begin
lemma join_single_steps_wf:
  assumes "A \<in> wf_pterm R"
  and "As = filter f (single_steps A)" and "As \<noteq> []"
  shows "\<exists>D. join_list As = Some D \<and> D \<in> wf_pterm R"
proof-
  {fix a1 a2 assume a1:"a1 \<in> set (single_steps A)" and a2:"a2 \<in> set (single_steps A)"
    with assms(1,2) have "a1 \<bottom>\<^sub>p a2 \<or> a1 = a2" 
      using single_steps_orth by presburger
    moreover from a1 have "a1 \<in> wf_pterm R" 
      using single_step_wf[OF assms(1)] assms(2) by presburger
    moreover from a2 have "a2 \<in> wf_pterm R" 
      using single_step_wf[OF assms(1)] assms(2) by presburger
    ultimately have "a1 \<squnion> a2 \<noteq> None" 
      using join_same orth_imp_join_defined no_var_lhs by fastforce
  } 
  then show ?thesis using left_lin_no_var_lhs.join_list_defined[OF ll_no_var_lhs] assms(2,3) single_step_wf[OF assms(1)] by simp
qed

lemma single_steps_join_list:
  assumes "join_list As = Some A" and "\<forall>a \<in> set As. a \<in> wf_pterm R"
  shows "set (single_steps A) = \<Union> (set (map (set \<circ> single_steps) As))"  
proof-
  have rdp:"set (redex_patterns A) = \<Union> (set (map (set \<circ> redex_patterns) As))" 
    using left_lin_no_var_lhs.redex_patterns_join_list assms ll_no_var_lhs by blast 
  {fix a assume "a \<in> set (single_steps A)" 
    then obtain \<alpha> p where a:"a = ll_single_redex (source A) p \<alpha>" and "(\<alpha>, p) \<in> set (redex_patterns A)" by auto
    with rdp obtain Ai where Ai:"Ai \<in> set As" and "(\<alpha>, p) \<in> set (redex_patterns Ai)" by auto
    then have "a \<in> set (single_steps Ai)" 
      unfolding a using left_lin_no_var_lhs.source_join_list[OF ll_no_var_lhs assms] by force
    with Ai have "a \<in> \<Union> (set (map (set \<circ> single_steps) As))" by auto
  } moreover 
  {fix a assume "a \<in> \<Union> (set (map (set \<circ> single_steps) As))"
    then obtain Ai where Ai:"Ai \<in> set As" "a \<in> set (single_steps Ai)"
      by (smt (verit, best) UnionE comp_def in_set_idx length_map map_nth_eq_conv nth_mem)
    then obtain \<alpha> p where a:"a = ll_single_redex (source Ai) p \<alpha>" and "(\<alpha>, p) \<in> set (redex_patterns Ai)" by auto
    with rdp Ai have "(\<alpha>, p) \<in> set (redex_patterns A)" by auto
    then have "a \<in> set (single_steps A)" 
      unfolding a using left_lin_no_var_lhs.source_join_list[OF ll_no_var_lhs assms] Ai by force
  }
  ultimately show ?thesis by fastforce
qed
end

end