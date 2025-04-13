subsubsection\<open>Matching of Linear Terms\<close>

theory Linear_Matching
  imports Proof_Term_Utils
begin

text\<open>For a linear term the matching substitution can simply be computed with the following definition.\<close>
definition match_substs :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('v \<times> ('f, 'v) term) list"
  where "match_substs t s = (zip (vars_term_list t) (map (\<lambda>p. s|_p) (var_poss_list t)))"

lemma mk_subst_partition_special: 
assumes "length ss = length ts"
  and "is_partition (map vars_term ts)"
shows "\<forall>i < length ts. (ts!i) \<cdot> (mk_subst f (zip (vars_term_list (ts!i)) (ss!i))) = (ts!i) \<cdot> (mk_subst f (concat (map2 zip (map vars_term_list ts) ss)))"
proof-
  let ?xs="map vars_term_list ts"
  have xs:"map vars_term ts = map set (map vars_term_list ts)" by simp 
  from assms(1) have l:"length ?xs = length ss" by simp 
  {fix i assume i:"i < length ts" 
    {fix x assume "x \<in> vars_term (ts!i)" 
      then have "mk_subst f (zip (map vars_term_list ts ! i) (ss ! i)) x = mk_subst f (concat (map2 zip (map vars_term_list ts) ss)) x"
        using i mk_subst_partition[OF l assms(2)[unfolded xs]] by simp  
    }
    then have "ts!i \<cdot> (mk_subst f (zip (vars_term_list (ts!i)) (ss!i))) = (ts!i) \<cdot> (mk_subst f (concat (map2 zip (map vars_term_list ts) ss)))"
      by (simp add: i term_subst_eq_conv)
  }
  then show ?thesis by fastforce 
qed

lemma match_substs_Fun: 
  assumes l:"length ts = length ss"  
  shows "match_substs (Fun f ts) (Fun g ss) = concat (map2 zip (map vars_term_list ts) (map2 (\<lambda>t s. map ((|_) s) (var_poss_list t)) ts ss))"
    (is "match_substs (Fun f ts) (Fun g ss) = concat (map2 zip ?xs ?terms)")   
proof-
  have l':"length ?xs = length ?terms" using l by simp
  {fix i assume "i < length ?xs" 
    then have i:"i < length ts" by simp
    with l have zip:"(zip ts ss)!i = (ts!i, ss!i)" by simp
    from i l have "length (map vars_term_list ts ! i) = length (map (\<lambda>p. (ss!i)|_p) (var_poss_list (ts!i)))"
      by (simp add: length_var_poss_list) 
    with zip have "length (?xs!i) = length (?terms!i)"
      using i l' by auto
  }note l_i=this
  have "vars_term_list (Fun f ts) = concat ?xs"
    unfolding vars_term_list.simps by simp
  moreover have "map ((|_) (Fun g ss)) (var_poss_list (Fun f ts)) = concat ?terms" proof- (*this part is incredibly cluttered \<Rightarrow> if possible clean up*)
    have l_map2:"length (map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts)) = length ts" 
      unfolding length_map length_zip by simp
    {fix i assume i:"i < length ts" 
      with l have "length (map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts) !i) = length (map var_poss_list ts!i)"
        unfolding nth_map[OF i] by simp
    } 
    with l_map2 have "length (map ((|_) (Fun g ss)) (var_poss_list (Fun f ts))) = length (concat (map var_poss_list ts))"
      unfolding var_poss_list.simps length_map length_concat by (smt (verit, del_insts) length_map map_nth_eq_conv)
    moreover have "length (concat ?terms) = length (concat (map var_poss_list ts))" proof-
      {fix i assume "i < length ts"
        with l have "length (map2 (\<lambda>t s. map ((|_) s) (var_poss_list t)) ts ss ! i) = length (map var_poss_list ts!i)" by simp
      }
      moreover have "length (map2 (\<lambda>t s. map ((|_) s) (var_poss_list t)) ts ss) = length ts" using l by simp
      ultimately show ?thesis unfolding length_concat  by (smt (verit, del_insts) length_map map_nth_eq_conv)
    qed
    ultimately have l'':"length (map ((|_) (Fun g ss)) (var_poss_list (Fun f ts))) = length (concat ?terms)" by presburger
    {fix i assume i:"i < length (var_poss_list (Fun f ts))" 
      let ?ps="map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts)" 
      let ?p="var_poss_list (Fun f ts) ! i"
      from l have l_terms:"length ?terms = length ts" by auto
      from l have l_ps:"length ?ps = length ts" by auto
      obtain j k where j:"j < length ts" and k:"k < length (var_poss_list (ts!j))" and i_sum_list:"i = sum_list (map length (take j ?ps)) + k" 
        and *:"?p = map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts) ! j ! k"
        using less_length_concat[OF i[unfolded var_poss_list.simps]] by auto 
      let ?p'="(var_poss_list (ts!j)) ! k" 
      from * k j have p:"?p = j # ?p'" by simp
      from j l have 1:"(Fun g ss) |_ ?p = (ss!j) |_ ?p'" unfolding p by simp 
      have i_sum_list2:"i = sum_list (map length (take j ?terms)) + k" proof-
        {fix n assume "n < length ts" 
          with l have "length (?terms!n) = length (?ps!n)" by auto
        }
        then have "map length ?terms = map length ?ps" 
          using l_terms l_ps by (simp add: map_eq_conv') 
        then show ?thesis unfolding i_sum_list by (metis take_map)   
      qed
      from j k have "k < length (?terms ! j)" by (smt (verit) l_i length_map length_var_poss_list nth_map)
      with j i_sum_list2 have "concat ?terms ! i = ?terms ! j ! k" 
        using concat_nth[of j ?terms k i]  unfolding length_map length_zip l min.idem by auto
      then have 2:"concat ?terms ! i = (ss!j) |_ ?p'" using k j l by auto
      from 1 2 have "map ((|_) (Fun g ss)) (var_poss_list (Fun f ts)) ! i  = concat ?terms ! i"
        unfolding var_poss_list.simps nth_map[OF i[unfolded var_poss_list.simps]] by simp
    } 
    with l'' show ?thesis by (metis length_map nth_equalityI) 
  qed
  ultimately show ?thesis 
    unfolding match_substs_def using concat_map2_zip[OF l'] l_i by presburger 
qed

text\<open>If all function symbols in term @{term t} coincide with function symbols in term @{term s}, 
then @{term t} matches @{term s}.\<close>
lemma fun_poss_eq_imp_matches: 
  fixes s t :: "('f, 'v) term"
  assumes "linear_term t" and "\<forall>p \<in> poss t. \<forall>f ts. t|_p = Fun f ts \<longrightarrow> (\<exists> ss. length ts = length ss \<and> s|_p = Fun f ss)"
  shows "t \<cdot> (mk_subst Var (match_substs t s)) = s"
using assms proof(induct t arbitrary:s)
  case (Var x)
  have "match_substs (Var x) s = [(x, s)]" 
    unfolding match_substs_def var_poss_list.simps vars_term_list.simps by simp
  then show ?case by simp
next
  case (Fun f ts)
  from Fun(3) obtain ss where l:"length ts = length ss" and s:"s = Fun f ss" by auto
  let ?\<sigma>="mk_subst Var (match_substs (Fun f ts) (Fun f ss))"
  let ?xs="map vars_term_list ts"
  let ?ss="map (\<lambda>(t, s). map (\<lambda>p. s|_p) (var_poss_list t)) (zip ts ss)" 
  have concat_zip:"match_substs (Fun f ts) (Fun f ss) = concat (map2 zip ?xs ?ss)"
    unfolding match_substs_Fun[OF l] by simp
  from Fun(2) have part:"is_partition (map set ?xs)"
    by (smt (verit, ccfv_SIG) length_map linear_term.elims(2) map_nth_eq_conv set_vars_term_list term.distinct(1) term.sel(4))
  have l':"length ?xs = length ?ss" using l by simp
  {fix i assume i:"i < length ts"
    with Fun(2) have lin:"linear_term (ts!i)" by simp 
    let ?\<sigma>i="mk_subst Var (match_substs (ts!i) (ss!i))" 
    {fix p f' ts' assume p:"p \<in> poss (ts!i)" "ts!i |_ p = Fun f' ts'"
      from p(1) i have "i#p \<in> poss (Fun f ts)" by simp
      moreover from p(2) i have "(Fun f ts)|_(i#p) = Fun f' ts'" by simp
      ultimately obtain ss' where "length ts' = length ss'" and "s|_(i#p) = Fun f' ss'" using Fun(3) by blast
      then have "\<exists>ss'. length ts' = length ss' \<and> (ss!i)|_p = Fun f' ss'" unfolding s by simp
    }
    then have "\<forall>p \<in> poss (ts!i). \<forall>f' ts'. (ts!i)|_p = Fun f' ts' \<longrightarrow> (\<exists> ss'. length ts' = length ss' \<and> (ss!i)|_p = Fun f' ss')" by simp
    with Fun(1) lin i have IH:"(ts!i) \<cdot> ?\<sigma>i = ss!i" using nth_mem by blast 
    have "(ts!i) \<cdot> ?\<sigma> = (ts!i) \<cdot> ?\<sigma>i" proof-
      {fix x assume x:"x \<in> vars_term (ts!i)" 
        from i l have *:"map2 (\<lambda>t s. map ((|_) s) (var_poss_list t)) ts ss ! i = map ((|_) (ss ! i)) (var_poss_list (ts ! i))" by auto
        with i x have "?\<sigma> x = ?\<sigma>i x" 
          unfolding concat_zip using mk_subst_partition[OF l' part] unfolding s match_substs_Fun[OF l] match_substs_def length_map
          by (smt (verit, best) nth_map set_vars_term_list) 
      }
      then show ?thesis by (simp add: term_subst_eq_conv) 
    qed
    then have "(ts!i) \<cdot> ?\<sigma> = ss!i" using IH i by presburger 
  }
  then show ?case unfolding s by (simp add: l map_nth_eq_conv) 
qed 

end