(* solving pattern problems in finite constructor form:
  - all l-terms are variables (so these can be deleted)
  - all t-terms are constructor terms of finite sorts
 *)

(* this theory has set-based transformation rules *)

theory FCF_Set
  imports 
    Pattern_Completeness_Multiset
    FCF_Problem
begin


text \<open>A problem is in finite variable form, if only variables occur in the problem and
   these variable all have a finite sort. Moreover, comparison of variables is only done
   if they have the same sort.
\<close>

definition finite_var_form_match :: "('f,'s) ssig \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "finite_var_form_match C mp \<longleftrightarrow> var_form_match mp \<and>
  (\<forall>l x y. (Var x, l) \<in> mp \<longrightarrow> (Var y, l) \<in> mp \<longrightarrow> snd x = snd y) \<and>
  (\<forall>l x. (Var x, l) \<in> mp \<longrightarrow> finite_sort C (snd x))"

lemma finite_var_form_matchD:
  assumes "finite_var_form_match C mp" and "(t,l) \<in> mp"
  shows "\<exists>x \<iota> y. t = Var (x,\<iota>) \<and> l = Var y \<and> finite_sort C \<iota> \<and>
    (\<forall>z. (Var z, Var y) \<in> mp \<longrightarrow> snd z = \<iota>)"
  using assms by (auto simp: finite_var_form_match_def var_form_match_def)

definition finite_var_form_pat :: "('f,'s) ssig \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "finite_var_form_pat C p = (\<forall> mp \<in> p. finite_var_form_match C mp)"

lemma finite_var_form_patD:
  assumes "finite_var_form_pat C pp" "mp \<in> pp" "(t,l) \<in> mp"
  shows "\<exists>x \<iota> y. t = Var (x,\<iota>) \<and> l = Var y \<and> finite_sort C \<iota> \<and>
    (\<forall>z. (Var z, Var y) \<in> mp \<longrightarrow> snd z = \<iota>)"
  using assms[unfolded finite_var_form_pat_def] finite_var_form_matchD by metis

lemma finite_var_form_imp_of_var_form_pat:
  "finite_var_form_pat C pp \<Longrightarrow> var_form_pat pp"
  by (auto simp: finite_var_form_pat_def var_form_pat_def finite_var_form_match_def)

lemma finite_var_form_pat_UNIQ_sort:
  assumes fvf: "finite_var_form_pat C pp"
    and f: "f \<in> var_form_of_pat pp"
  shows "UNIQ (snd ` f x)"
proof (intro Uniq_I, clarsimp)
  from f obtain mp where mp: "mp \<in> pp" and f: "f = var_form_of_match mp"
    by (auto simp: var_form_of_pat_def)
  fix y \<iota> z \<kappa> assume "(y,\<iota>) \<in> f x" "(z,\<kappa>) \<in> f x"
  with f have y: "(Var (y,\<iota>), Var x) \<in> mp" and z: "(Var (z,\<kappa>), Var x) \<in> mp"
    by (auto simp: var_form_of_match_def)
  from finite_var_form_patD[OF fvf mp y] z
  show "\<iota> = \<kappa>" by auto
qed

lemma finite_var_form_pat_pat_complete:
  assumes fvf: "finite_var_form_pat C pp"
  shows "pat_complete C pp \<longleftrightarrow>
    (\<forall>\<alpha>. (\<forall>v \<in> tvars_pat pp. \<alpha> v < card_of_sort C (snd v)) \<longrightarrow>
    (\<exists>mp \<in> pp. \<forall>x. UNIQ {\<alpha> y |y. (Var y, Var x) \<in> mp}))"
proof-
  note vf = finite_var_form_imp_of_var_form_pat[OF fvf]
  note pat_complete_var_form_nat[of "var_form_of_pat pp" C]
  note this[unfolded tvars_var_form_pat[OF vf]]
  note * = this[unfolded pat_of_var_form_pat[OF vf]]
  show ?thesis
    apply (subst *)
    subgoal
    proof
      fix y \<iota>
      assume y: "(y,\<iota>) \<in> tvars_pat pp"
      from y obtain mp t l where mp: "mp \<in> pp" and tl:"(t,l) \<in> mp" and yt: "(y, \<iota>) \<in> vars t"
        by (auto simp: tvars_pat_def tvars_match_def)
      from finite_var_form_patD[OF fvf mp tl] yt
      show "finite_sort C \<iota>" by auto
    qed
    subgoal using finite_var_form_pat_UNIQ_sort[OF fvf] by force
    subgoal 
      apply (rule all_cong)
      apply (unfold ex_var_form_pat)
      apply (rule bex_cong[OF refl])
      apply (rule all_cong1)
      apply (rule arg_cong[of _ _ UNIQ])
      by (auto simp: var_form_of_match_def)
    done
qed


context pattern_completeness_context
begin


(* all subterms of some sort of cardinality 1 will be replaced by the same variable (which is here fixed to 0) *)
fun flatten_triv_sort_main :: "('f,nat \<times> 's)term \<Rightarrow> ('f,nat \<times> 's)term \<times> 's" where
  "flatten_triv_sort_main (Var x) = (if cd_sort (snd x) = 1 then (Var (0, snd x), snd x) else (Var x, snd x))" 
| "flatten_triv_sort_main (Fun f ts) = (let tss = map flatten_triv_sort_main ts in
     case C (f,map snd tss) of Some s \<Rightarrow> if cd_sort s = 1 then (Var (0,s), s) else (Fun f (map fst tss), s))" 

definition flatten_triv_sort :: "('f,nat \<times> 's)term \<Rightarrow> ('f,nat \<times> 's)term" where
  "flatten_triv_sort = fst o flatten_triv_sort_main" 

definition flatten_triv_sort_pat :: "('f,'s)simple_pat_problem \<Rightarrow> ('f,'s)simple_pat_problem" where
  "flatten_triv_sort_pat = image (image (image flatten_triv_sort))" 

end

context pattern_completeness_context_with_assms
begin

lemma flatten_triv_sort_spp: assumes "finite_constructor_form_pat p"
  shows "finite_constructor_form_pat (flatten_triv_sort_pat p)" 
    "simple_pat_complete C SS (flatten_triv_sort_pat p) \<longleftrightarrow> simple_pat_complete C SS p" 
proof -
  show "simple_pat_complete C SS (flatten_triv_sort_pat p) \<longleftrightarrow> simple_pat_complete C SS p"
    unfolding simple_pat_complete_def flatten_triv_sort_pat_def bex_simps simple_match_complete_wrt_def ball_simps
      UNIQ_subst_def
  proof (intro all_cong bex_cong refl ball_cong arg_cong[of _ _ UNIQ])
    fix \<sigma> mp eqc
    assume \<sigma>: "\<sigma> :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
      and mp: "mp \<in> p" 
      and eqc: "eqc \<in> mp" 
    {
      fix t
      assume "t \<in> eqc" 
      with assms(1)[unfolded finite_constructor_form_defs, rule_format, OF mp eqc]
      obtain \<iota> where "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
      hence "map_prod (\<lambda> t. t \<cdot> \<sigma>) id (flatten_triv_sort_main t) = (t \<cdot> \<sigma>, \<iota>)" 
      proof (induct)
        case (Var x \<iota>)
        then obtain v where xv: "x = (v,\<iota>)" and \<iota>: "\<iota> \<in> S" 
          by (auto simp: sorted_map_def restrict_map_def hastype_def split: if_splits)
        show ?case
        proof (cases "cd_sort \<iota> = 1")
          case False
          thus ?thesis using xv by auto
        next
          case True
          from cd[OF \<iota>] True k1
          have "card_of_sort C \<iota> = 1" by auto
          from this[unfolded card_of_sort_def] obtain s where s: "{s. s : \<iota> in \<T>(C)} = {s}" 
            by (metis card_1_singletonE)
          {
            fix y
            have "\<sigma> (y, \<iota>) : \<iota> in \<T>(C)" using \<sigma> \<iota>
              by (simp add: hastype_restrict sorted_map_def)
            with s have "\<sigma> (y, \<iota>) = s" by auto
          }
          thus ?thesis using True xv by simp
        qed
      next
        case (Fun f ts \<iota>s \<iota>) 
        from Fun(1) have C: "C (f, \<iota>s) = Some \<iota>" by (rule fun_hastypeD)
        from Fun(3) have map_snd: "map snd (map flatten_triv_sort_main ts) = \<iota>s"
          apply (intro nth_equalityI) 
          subgoal by (auto simp: list_all2_conv_all_nth)
          subgoal for i using arg_cong[OF list_all2_nthD[OF Fun(3), of i], of snd] by auto
          done  
        show ?case
        proof (cases "cd_sort \<iota> = 1")
          case False
          hence "map_prod (\<lambda>t. t \<cdot> \<sigma>) id (flatten_triv_sort_main (Fun f ts)) = 
               (Fun f (map (\<lambda> t. t \<cdot> \<sigma>) (map fst (map flatten_triv_sort_main ts))), \<iota>)" 
            using map_snd C by simp
          also have "(map (\<lambda> t. t \<cdot> \<sigma>) (map fst (map flatten_triv_sort_main ts)))
               = (map (\<lambda> t. t \<cdot> \<sigma>) ts)" unfolding map_map o_def
            apply (intro nth_equalityI, force)
            subgoal for i using arg_cong[OF list_all2_nthD[OF Fun(3), of i], of fst] by auto
            done
          finally show ?thesis by simp
        next
          case True
          hence id: "map_prod (\<lambda>t. t \<cdot> \<sigma>) id (flatten_triv_sort_main (Fun f ts)) = (\<sigma> (0,\<iota>), \<iota>)" 
            using C map_snd by simp
          from C_sub_S[OF Fun(1)] have \<iota>: "\<iota> \<in> S" by auto
          from True[unfolded cd[OF \<iota>] card_of_sort_def] k1
          have "card {s. s : \<iota> in \<T>(C)} = 1" by auto
          then obtain s where s: "{s. s : \<iota> in \<T>(C)} = {s}" 
            by (metis card_1_singletonE)
          have var: "Var (0, \<iota>) : \<iota> in \<T>(C, \<V> |` SS)" using \<iota> by (simp add: hastype_def)            
          have f: "Fun f ts : \<iota> in \<T>(C, \<V> |` SS)" using Fun(1-2) by (metis Fun_hastypeI)
          {
            fix t
            assume "t : \<iota> in \<T>(C, \<V> |` SS)" 
            hence "t \<cdot> \<sigma> : \<iota> in \<T>(C)" using \<sigma> by (metis subst_hastype)
            with s have "t \<cdot> \<sigma> = s" by blast
          } note subst = this 
          from subst[OF var] subst[OF f]
          show ?thesis unfolding id by auto
        qed
      qed          
      from arg_cong[OF this, of fst]
      have "flatten_triv_sort t \<cdot> \<sigma> = t \<cdot> \<sigma>" unfolding flatten_triv_sort_def by simp
    }
    thus "flatten_triv_sort ` eqc \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> = eqc \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
      by (metis (no_types, lifting) image_cong image_image)
  qed
  show "finite_constructor_form_pat (flatten_triv_sort_pat p)" 
    unfolding flatten_triv_sort_pat_def ball_simps finite_constructor_form_defs
  proof (intro ballI conjI)
    fix mp eqc
    assume "mp \<in> p" "eqc \<in> mp" 
    from assms[unfolded finite_constructor_form_defs, rule_format, OF this] obtain \<iota>
      where fin: "finite_sort C \<iota>" and t: "\<And> t. t \<in> eqc \<Longrightarrow> t : \<iota> in \<T>(C,\<V> |` SS)" 
         and ne: "eqc \<noteq> {}" by auto
    show "flatten_triv_sort ` eqc \<noteq> {}" using ne by auto
    show "\<exists>\<iota>. finite_sort C \<iota> \<and> (\<forall> t \<in> eqc. flatten_triv_sort t : \<iota> in \<T>(C,\<V> |` SS))" 
    proof (intro exI[of _ \<iota>] conjI fin ballI)
      fix t
      assume "t \<in> eqc" 
      from t[OF this] have "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
      hence "fst (flatten_triv_sort_main t) : \<iota> in \<T>(C,\<V> |` SS) \<and> snd (flatten_triv_sort_main t) = \<iota>" 
      proof (induct)
        case (Var x \<iota>)
        thus ?case by (auto simp: hastype_def restrict_map_def split: if_splits)
      next
        case (Fun f ts \<iota>s \<iota>)
        from Fun(1) have C: "C (f, \<iota>s) = Some \<iota>" by (rule fun_hastypeD)
        from C_sub_S[OF Fun(1)] have \<iota>: "\<iota> \<in> S" by auto
        from Fun(3) have map_snd: "map snd (map flatten_triv_sort_main ts) = \<iota>s"
          apply (intro nth_equalityI) 
          subgoal by (auto simp: list_all2_conv_all_nth)
          subgoal for i using list_all2_nthD[OF Fun(3), of i] by auto
          done  
        show ?case
        proof (cases "cd_sort \<iota> = 1")
          case False
          hence id: "flatten_triv_sort_main (Fun f ts) = 
             (Fun f (map fst (map flatten_triv_sort_main ts)), \<iota>)" 
            using map_snd C by simp
          show ?thesis unfolding id fst_conv snd_conv
            apply (intro conjI refl Fun_hastypeI[OF Fun(1)] list_all2_all_nthI)
            subgoal using Fun(3) by (auto simp: list_all2_conv_all_nth)
            subgoal for i using list_all2_nthD[OF Fun(3), of i] by auto
            done
        next
          case True
          hence id: "flatten_triv_sort_main (Fun f ts) = (Var (0,\<iota>), \<iota>)" 
            using C map_snd by auto
          thus ?thesis using \<iota> by (simp add: hastype_def restrict_map_def)
        qed
      qed
      thus "flatten_triv_sort t : \<iota> in \<T>(C,\<V> |` SS)" unfolding flatten_triv_sort_def by auto
    qed
  qed
qed

lemma eliminate_uniq_spp: assumes "finite_constructor_form_pat p" 
  and "p = insert mp p'" 
  and "mp = insert eqc mp'" 
  and "pn = insert mp' p'" 
  and "UNIQ eqc" 
shows "simple_pat_complete C SS p \<longleftrightarrow> simple_pat_complete C SS pn" 
  "finite_constructor_form_pat pn"
proof 
  show "simple_pat_complete C SS p \<Longrightarrow> simple_pat_complete C SS pn" unfolding assms
    by (auto simp: simple_pat_complete_def simple_match_complete_wrt_def)
  show "finite_constructor_form_pat pn"
    using assms unfolding finite_constructor_form_defs by auto
  from \<open>UNIQ eqc\<close> have "UNIQ_subst \<sigma> eqc" for \<sigma> :: "_ \<Rightarrow> ('f, unit)term" 
    unfolding UNIQ_subst_def by (rule image_Uniq)
  thus "simple_pat_complete C SS pn \<Longrightarrow> simple_pat_complete C SS p" unfolding assms
    by (auto simp: simple_pat_complete_def simple_match_complete_wrt_def)
qed

(* note that a decomposition step might create equivalence classes with
   different sorts, so these need to be filtered. Example: consider 
     f : [Int,Int] \<rightarrow> Bool and f : [Nat,Nat] \<rightarrow> Bool, then
     decomposing f(xI,yI) = f(xN,yN) would lead to xI = xN and yI = yN *)
lemma decompose_spp: assumes "finite_constructor_form_pat p" 
  and p: "p = insert mp p'" 
  and mp: "mp = insert eqc mp'" 
  and root: "\<And> t. t \<in> eqc \<Longrightarrow> root t = Some (f,n)" 
  and eqcn: "eqcn = (\<lambda> i. (\<lambda> t. args t ! i) ` eqc) ` {0..<n}" 
  and pn: "pn = (if Ball eqcn (\<lambda> eq. UNIQ (\<T>(C,\<V>) ` eq)) then insert (eqcn \<union> mp') p' else p')" 
shows "simple_pat_complete C SS p \<longleftrightarrow> simple_pat_complete C SS pn" 
  "finite_constructor_form_pat pn"
proof -
  {
    fix t
    assume "t \<in> eqc" 
    from root[OF this]
    have "t = Fun f (map (\<lambda> i. args t ! i) [0..<n])" 
      by (cases t; auto intro: nth_equalityI)
  } note to_args = this
  from assms(1)[unfolded finite_constructor_form_pat_def p]
  have "finite_constructor_form_mp mp" by auto
  from this[unfolded mp finite_constructor_form_mp_def]
  obtain \<iota> where typed: "\<And> t. t \<in> eqc \<Longrightarrow> t : \<iota> in \<T>(C,\<V> |` SS)" by auto
  have "simple_pat_complete C SS p \<longleftrightarrow> simple_pat_complete C SS (insert (eqcn \<union> mp') p')" 
    unfolding simple_pat_complete_def p pn bex_simps mp simple_match_complete_wrt_def ball_simps ball_Un
  proof (intro all_cong disj_cong refl conj_cong) 
    fix \<sigma> :: "_ \<Rightarrow> (_,unit)term" 
    show "UNIQ_subst \<sigma> eqc = Ball eqcn (UNIQ_subst \<sigma>)" 
    proof 
      assume uniq: "UNIQ_subst \<sigma> eqc" 
      show "Ball eqcn (UNIQ_subst \<sigma>)" unfolding eqcn
      proof clarsimp
        fix i
        assume i: "i < n" 
        show "UNIQ_subst \<sigma> {args t ! i |. t \<in> eqc}" (is "UNIQ_subst _ ?args")
        proof (intro UNIQ_subst_pairI)
          fix si ti
          assume *: "si \<in> ?args" "ti \<in> ?args" 
          from * obtain s where s: "s \<in> eqc" and si: "si = args s ! i" by auto
          from * obtain t where t: "t \<in> eqc" and ti: "ti = args t ! i" by auto
          from arg_cong[OF UNIQ_subst_pairD[OF uniq s t], of "\<lambda> t. args t ! i"] i
          show "si \<cdot> \<sigma> = ti \<cdot> \<sigma>" unfolding si ti using root[OF s] root[OF t] by (cases s; cases t; auto)
        qed
      qed
    next
      assume "Ball eqcn (UNIQ_subst \<sigma>)" 
      from this[unfolded eqcn, simplified]
      have uniq: "i < n \<Longrightarrow> UNIQ_subst \<sigma> {args t ! i |. t \<in> eqc}" for i by auto
      show "UNIQ_subst \<sigma> eqc" 
      proof (intro UNIQ_subst_pairI)
        fix s t
        assume s: "s \<in> eqc" and t: "t \<in> eqc" 
        show "s \<cdot> \<sigma> = t \<cdot> \<sigma>" 
          apply (subst to_args[OF s], subst to_args[OF t])
          apply clarsimp
          subgoal for i using UNIQ_subst_pairD[OF uniq[of i]] s t by auto
          done
      qed
    qed
  qed
  also have "\<dots> = simple_pat_complete C SS pn" 
  proof (cases "\<forall>eq\<in>eqcn. UNIQ (\<T>(C,\<V>) ` eq)")
    case True
    thus ?thesis unfolding pn by auto
  next
    case False
    hence pn: "pn = p'" unfolding pn by auto
    from False obtain eq where eq_mem: "eq \<in> eqcn" and nuniq: "\<not> UNIQ (\<T>(C,\<V>) ` eq)" by auto
    from nuniq[unfolded Uniq_def] obtain si ti where 
      st: "si \<in> eq" "ti \<in> eq" and diff: "\<T>(C,\<V>) si \<noteq> \<T>(C,\<V>) ti" by auto
    from eq_mem[unfolded eqcn] obtain i where i: "i < n" and eq: "eq = {args t ! i |. t \<in> eqc}" by auto
    {
      fix ti
      assume "ti \<in> eq" 
      from this[unfolded eq] obtain t where ti: "ti = args t ! i" and t: "t \<in> eqc" by auto
      from typed[OF t] have "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
      with to_args[OF t] have "Fun f (map ((!) (args t)) [0..<n]) : \<iota> in \<T>(C,\<V> |` SS)" by auto
      from this[unfolded Fun_hastype list_all2_conv_all_nth] i 
      have "\<exists> \<iota>. ti : \<iota> in \<T>(C,\<V> |` SS)" unfolding ti by force
    }
    from this[OF st(1)] this[OF st(2)] obtain \<iota>s \<iota>t where 
      typed: "si : \<iota>s in \<T>(C,\<V> |` SS)" "ti : \<iota>t in \<T>(C,\<V> |` SS)" by auto
    hence "si : \<iota>s in \<T>(C,\<V>)" "ti : \<iota>t in \<T>(C,\<V>)" 
      by (meson hastype_in_Term_mono_right restrict_submap)+
    with diff have diff: "\<iota>s \<noteq> \<iota>t" unfolding hastype_def by auto
    show ?thesis unfolding simple_pat_complete_def pn
    proof (intro all_cong)
      fix \<sigma>
      assume sig: "\<sigma> :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
      have "\<not> simple_match_complete_wrt \<sigma> (eqcn \<union> mp')" 
      proof
        assume "simple_match_complete_wrt \<sigma> (eqcn \<union> mp')" 
        hence "simple_match_complete_wrt \<sigma> eqcn" unfolding simple_match_complete_wrt_def by auto
        from this[unfolded simple_match_complete_wrt_def] eq_mem
        have "UNIQ_subst \<sigma> eq" by auto
        with st have equiv: "si \<cdot> \<sigma> = ti \<cdot> \<sigma>" by (metis UNIQ_subst_pairD)
        from typed sig 
        have typed: "si \<cdot> \<sigma> : \<iota>s in \<T>(C)" "ti \<cdot> \<sigma> : \<iota>t in \<T>(C)" by (metis subst_hastype)+
        hence "si \<cdot> \<sigma> \<noteq> ti \<cdot> \<sigma>" using diff unfolding hastype_def by auto
        with equiv show False by simp
      qed
      thus "Bex (insert (eqcn \<union> mp') p') (simple_match_complete_wrt \<sigma>) = Bex p' (simple_match_complete_wrt \<sigma>)" 
        by simp
    qed
  qed
  finally show "simple_pat_complete C SS p = simple_pat_complete C SS pn" .
  show "finite_constructor_form_pat pn" using assms(1)
    unfolding pn p mp finite_constructor_form_pat_def ball_simps
  proof (simp, intro impI)
    assume fin: "finite_constructor_form_mp (insert eqc mp') \<and> Ball p' finite_constructor_form_mp" 
      and uniq: "\<forall>eq\<in>eqcn. UNIQ (\<T>(C,\<V>) ` eq)" 
    show "finite_constructor_form_mp (eqcn \<union> mp')" unfolding finite_constructor_form_mp_def
    proof
      fix eqc'
      assume "eqc' \<in> eqcn \<union> mp'" 
      thus "eqc' \<noteq> {} \<and> (\<exists>\<iota>. finite_sort C \<iota> \<and> (\<forall> t \<in> eqc'. t : \<iota> in \<T>(C,\<V> |` SS)))" 
      proof
        assume "eqc' \<in> mp'" 
        thus ?thesis using fin unfolding finite_constructor_form_mp_def by auto
      next
        assume eqc'_mem: "eqc' \<in> eqcn" 
        from this[unfolded eqcn] obtain i where i: "i < n" and 
           eqc': "eqc' = {args t ! i |. t \<in> eqc}" by auto
        from fin[unfolded finite_constructor_form_mp_def] obtain \<iota>
          where fin: "finite_sort C \<iota>" and ne: "eqc \<noteq> {}" and typed: "t \<in> eqc \<Longrightarrow> t : \<iota> in \<T>(C,\<V> |` SS)" for t
          by auto
        from ne obtain t where t: "t \<in> eqc" by auto
        from typed[OF t] have "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
        with to_args[OF t] 
        have "Fun f (map ((!) (args t)) [0..<n]) : \<iota> in \<T>(C,\<V> |` SS)" by auto
        from finite_arg_sorts[OF fin this, of "args t ! i"] i
        obtain \<iota>i where ti: "args t ! i : \<iota>i in \<T>(C, \<V> |` SS)" and fin: "finite_sort C \<iota>i" by auto  
        have ti_mem: "args t ! i \<in> eqc'" unfolding eqc' using i t by auto
        have wti: "args t ! i : \<iota>i in \<T>(C, \<V>)" using ti 
          by (meson hastype_in_Term_mono_right restrict_submap)
        from ti_mem ti wti obtain ti where 
          ti: "ti : \<iota>i in \<T>(C, \<V> |` SS)" "ti : \<iota>i in \<T>(C, \<V>)" "ti \<in> eqc'" by auto
        show ?thesis
        proof (intro exI[of _ \<iota>i] conjI ballI fin)
          show "eqc' \<noteq> {}" using ne unfolding eqc' by auto
          fix si
          assume si: "si \<in> eqc'"
          with uniq[rule_format, OF eqc'_mem] ti 
          have type_si: "si : \<iota>i in \<T>(C,\<V>)" 
            unfolding Uniq_def hastype_def by auto
          from si[unfolded eqc'] obtain s where si: "si = args s ! i" and s: "s \<in> eqc" by auto
          from typed[OF s] to_args[OF s]
          have "Fun f (map ((!) (args s)) [0..<n]) : \<iota> in \<T>(C,\<V> |` SS)" by auto
          from this[unfolded Fun_hastype list_all2_conv_all_nth] i si
          have "\<exists> \<iota>i. si : \<iota>i in \<T>(C, \<V> |` SS)" by auto
          then obtain \<iota>2 where si: "si : \<iota>2 in \<T>(C, \<V> |` SS)" by auto
          hence "si : \<iota>2 in \<T>(C, \<V>)"
            by (meson hastype_in_Term_mono_right restrict_submap)
          with type_si have "\<iota>i = \<iota>2" by (auto simp: hastype_def)    
          thus "si : \<iota>i in \<T>(C,\<V> |` SS)" using si by auto
        qed
      qed
    qed
  qed
qed        

lemma eliminate_clash_spp: assumes "finite_constructor_form_pat p" 
  and "p = insert mp pn" 
  and "mp = insert eqc mp'" 
  and "eqc = {s,t} \<union> eqc'" 
  and "Conflict_Clash s t" 
shows "simple_pat_complete C SS p \<longleftrightarrow> simple_pat_complete C SS pn" 
  "finite_constructor_form_pat pn"
proof 
  from mp_fail_pcorrect1[OF match_fail_mp_fail[OF match_fail.match_clash'[OF assms(5)]], 
      of _ undefined "{#}" "\<lambda> _. None", unfolded match_complete_wrt_def tvars_match_def, simplified]
  have clash: "\<sigma> :\<^sub>s \<V> |` (vars s \<union> vars t) \<rightarrow> \<T>(C) \<Longrightarrow> s \<cdot> \<sigma> \<noteq> t \<cdot> \<sigma>" for \<sigma> by metis
  from assms(1)[unfolded finite_constructor_form_pat_def finite_constructor_form_mp_def] assms
  obtain \<iota> where typed: "u \<in> {s,t} \<Longrightarrow>  u : \<iota> in \<T>(C,\<V> |` SS)" for u by auto
  have "vars u \<subseteq> dom (\<V> |` SS)" if "u \<in> {s,t}" for u using typed[OF that] 
    by (rule hastype_in_Term_imp_vars_subset)
  hence st: "vars s \<union> vars t \<subseteq> SS" by auto
  {
    fix \<sigma>
    assume sig: "\<sigma> :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
    have "s \<cdot> \<sigma> \<noteq> t \<cdot> \<sigma>" 
    proof (rule clash)
      show "\<sigma> :\<^sub>s \<V> |` (vars s \<union> vars t) \<rightarrow> \<T>(C)" 
        using sig st by (meson restrict_map_mono_right sorted_map_cmono)
    qed
    hence "\<not> UNIQ_subst \<sigma> eqc" unfolding assms UNIQ_subst_def Uniq_def by auto 
  }
  thus "simple_pat_complete C SS p \<Longrightarrow> simple_pat_complete C SS pn" unfolding assms(2-3)
    by (auto simp: simple_pat_complete_def simple_match_complete_wrt_def)
  show "finite_constructor_form_pat pn"
    using assms unfolding finite_constructor_form_defs by auto
  show "simple_pat_complete C SS pn \<Longrightarrow> simple_pat_complete C SS p" unfolding assms
    by (auto simp: simple_pat_complete_def simple_match_complete_wrt_def)
qed


lemma detect_sat_spp: 
  assumes "p = insert {} p'" 
  shows "simple_pat_complete C SS p" 
  unfolding assms by (auto simp: simple_pat_complete_def simple_match_complete_wrt_def)

lemma detect_unsat_spp:
  shows "\<not> simple_pat_complete C SS {}" 
  using \<sigma>g' by (auto simp: simple_pat_complete_def simple_match_complete_wrt_def)

lemma separate_var_fun_spp: assumes "finite_constructor_form_pat p"
  and p: "p = insert mp p'" 
  and mp: "mp = insert eqc mp'" 
  and eqc: "eqc = {x,t} \<union> eqcV \<union> eqcF" 
  and Pn: "Pn = {insert {{x,t}} p', insert ({insert x eqcV}) p', insert ({insert t eqcF} \<union> mp') p'}" 
shows "simple_pat_complete C SS p \<longleftrightarrow> (\<forall> pn \<in> Pn. simple_pat_complete C SS pn)" 
  "Ball Pn finite_constructor_form_pat" 
proof -
  let ?spc = "simple_pat_complete C SS" 
  note spc = simple_pat_complete_def simple_match_complete_wrt_def
  have main: "UNIQ_subst \<sigma> eqc \<longleftrightarrow> UNIQ_subst \<sigma> {x,t} \<and> UNIQ_subst \<sigma> (insert x eqcV) \<and> UNIQ_subst \<sigma> (insert t eqcF)"   
    (is "?l = ?r") for \<sigma> :: "_ \<Rightarrow> (_,unit)term"
  proof 
    assume ?l
    show ?r 
      by (intro conjI; rule UNIQ_subst_mono[OF _ \<open>?l\<close>], auto simp: eqc)
  next
    assume ?r
    hence *: "UNIQ_subst \<sigma> {x, t}" "UNIQ_subst \<sigma> (insert x eqcV)" "UNIQ_subst \<sigma> (insert t eqcF)" by auto
    show ?l 
    proof (intro UNIQ_subst_pairI)
      fix a b
      assume "a \<in> eqc" "b \<in> eqc" 
      with
        UNIQ_subst_pairD[OF *(1), of x t]
        UNIQ_subst_pairD[OF *(2), of x]
        UNIQ_subst_pairD[OF *(2), of a b]
        UNIQ_subst_pairD[OF *(3), of t]
        UNIQ_subst_pairD[OF *(3), of a b]
      show "a \<cdot> \<sigma> = b \<cdot> \<sigma>" unfolding eqc by fastforce
    qed
  qed
  have "?spc p \<longleftrightarrow> (?spc (insert {eqc} p') \<and> ?spc (insert mp' p'))" 
    unfolding p mp spc by auto
  also have "\<dots> \<longleftrightarrow>
     ?spc (insert {{x,t}} p') \<and> (?spc (insert mp' p') \<and> ?spc (insert {insert x eqcV} p') \<and> ?spc (insert {insert t eqcF} p'))" 
    (is "_ \<longleftrightarrow> _ \<and> ?sub")
    unfolding spc by (auto simp: main)
  also have "?sub \<longleftrightarrow> ?spc (insert ({insert x eqcV}) p') \<and> ?spc (insert ({insert t eqcF} \<union> mp') p')" 
    by (auto simp: spc) 
  finally show "?spc p \<longleftrightarrow> (\<forall> pn \<in> Pn. ?spc pn)" unfolding Pn by auto
  show "Ball Pn finite_constructor_form_pat" using assms(1) unfolding assms
    by (auto simp: finite_constructor_form_pat_def finite_constructor_form_mp_def)
qed

lemma separate_var_fun_spp_single: assumes "finite_constructor_form_pat p"
  and p: "p = insert mp p'" 
  and mp: "mp = insert eqc mp'" 
  and eqc: "eqc = {x,t} \<union> eqc'" 
  and Pn: "Pn = {insert {{x,t}} p', insert ({insert x eqc'} \<union> mp') p'}" 
shows "simple_pat_complete C SS p \<longleftrightarrow> (\<forall> pn \<in> Pn. simple_pat_complete C SS pn)" 
  "Ball Pn finite_constructor_form_pat" 
proof -
  let ?spc = "simple_pat_complete C SS" 
  have swap: "{t, x} = {x,t}" by auto
  from eqc have eqc: "eqc = {t,x} \<union> {} \<union> eqc'" by auto
  note step = separate_var_fun_spp[OF assms(1) p mp eqc refl]
  from step(2) show "Ball Pn finite_constructor_form_pat" unfolding Pn swap by auto
  show  "simple_pat_complete C SS p \<longleftrightarrow> (\<forall> pn \<in> Pn. simple_pat_complete C SS pn)" 
    unfolding step(1) unfolding swap Pn
    by (simp, auto simp: simple_pat_complete_def simple_match_complete_wrt_def)
qed
     


lemma instantiate_spp: assumes "finite_constructor_form_pat p"
  and disj: "fst ` tvars_spat p \<inter> {n..<n + m} = {}" 
  and x: "x \<in> tvars_spat p" 
  and Pn: "Pn = (\<lambda> \<tau>. (`) ((`) (\<lambda> t. t \<cdot> \<tau>)) ` p) ` \<tau>s n x" 
shows "simple_pat_complete C SS p \<longleftrightarrow> (\<forall> pn \<in> Pn. simple_pat_complete C SS pn)" 
  "Ball Pn finite_constructor_form_pat" 
proof 
  assume comp: "simple_pat_complete C SS p" 
  show "(\<forall> pn \<in> Pn. simple_pat_complete C SS pn)" 
    unfolding simple_pat_complete_def
  proof (intro ballI allI impI)
    fix pn \<sigma>
    assume "pn \<in> Pn" and sig: "\<sigma> :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
    from this[unfolded Pn] obtain \<tau> where tau: "\<tau> \<in> \<tau>s n x" 
      and pn: "pn = (`) ((`) (\<lambda>t. t \<cdot> \<tau>)) ` p" by auto
    from tau[unfolded \<tau>s_def] obtain f \<iota>s where
      tau: "\<tau> = \<tau>c n x (f,\<iota>s)" and f: "f : \<iota>s \<rightarrow> snd x in C" by auto
    define t where "t = Fun f (map (\<lambda> i. \<sigma> (n + i, \<iota>s ! i)) [0 ..< length \<iota>s])" 
    from C_sub_S[OF f] have x: "snd x \<in> S" and \<iota>s: "set \<iota>s \<subseteq> S" by auto
    have t: "t : snd x in \<T>(C)" 
      unfolding t_def
    proof (intro Fun_hastypeI[OF f] list_all2_all_nthI, force, clarsimp)
      fix i
      assume "i < length \<iota>s" 
      hence "\<iota>s ! i \<in> S" using \<iota>s by auto
      with sig show "\<sigma> (n + i, \<iota>s ! i) : \<iota>s ! i in \<T>(C)"
        by (simp add: restrict_map_eq_restrict_sset sorted_map_def)
    qed        
    define \<sigma>' where "\<sigma>' = \<sigma>(x := t)" 
    from sig t have sig': "\<sigma>' :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" unfolding \<sigma>'_def sorted_map_def
      by (metis comp_apply fun_upd_apply hastypeD hastypeI hastype_restrict)
    from comp[unfolded simple_pat_complete_def, rule_format, OF this]
    obtain mp where mp: "mp \<in> p" and comp: "simple_match_complete_wrt \<sigma>' mp" by auto
    let ?mp = "(`) (\<lambda>t. t \<cdot> \<tau>) ` mp" 
    from mp have mem: "?mp \<in> pn" unfolding pn by auto
    {
      fix i
      assume i: "i < length \<iota>s" and 
        x: "x = (n + i, \<iota>s ! i)" 
      from m[OF f] i have "i < m" by auto
      with disj x assms(3) have False by fastforce
    } note x_disj = this

    have xtau: "x \<notin> vars (s \<cdot> \<tau>)" for s 
    proof
      assume "x \<in> vars (s \<cdot> \<tau>)" 
      from this[unfolded tau \<tau>c_def split vars_term_subst subst_def]
      obtain i where i: "i < length \<iota>s" and 
        x: "x = (n + i, \<iota>s ! i)" by (auto simp: set_conv_nth split: if_splits)
      with x_disj show False by auto
    qed

    show "Bex pn (simple_match_complete_wrt \<sigma>)" 
    proof (intro bexI[OF _ mem])
      have "simple_match_complete_wrt \<sigma> ?mp = simple_match_complete_wrt \<sigma>' ?mp" 
      proof (rule tvars_spat_cong[of pn])
        show "?mp \<in> pn" unfolding pn  using mp by auto
        fix y
        assume "y \<in> tvars_spat pn" 
        thus "\<sigma> y = \<sigma>' y" 
          unfolding \<sigma>'_def pn by (auto simp: xtau)
      qed
      also have \<dots>
        unfolding simple_match_complete_wrt_def
      proof (intro ballI UNIQ_subst_pairI, clarsimp)
        fix eqc s s'
        assume eqc: "eqc \<in> mp" and st: "s \<in> eqc" "s' \<in> eqc" 
        from comp[unfolded simple_match_complete_wrt_def UNIQ_subst_alt_def, rule_format, OF this]
        have eq: "s \<cdot> \<sigma>' = s' \<cdot> \<sigma>'" .
        {
          fix y
          have "(\<tau> \<circ>\<^sub>s \<sigma>') y = \<sigma>' y" 
          proof (cases "y = x")
            case False
            thus ?thesis unfolding subst_compose_def tau \<tau>c_def split by (simp add: subst_def)
          next
            case True
            show ?thesis unfolding True using x_disj 
              by (auto simp add: tau \<tau>c_def subst_compose_def \<sigma>'_def t_def intro!: nth_equalityI)
          qed
        }
        thus "s \<cdot> \<tau> \<cdot> \<sigma>' = s' \<cdot> \<tau> \<cdot> \<sigma>'" using eq
          by (metis subst_same_vars subst_subst_compose)
      qed
      finally show "simple_match_complete_wrt \<sigma> ?mp" by auto
    qed
  qed
next
  {
    from x obtain eqc mp t where *: "eqc \<in> mp" "mp \<in> p" "t \<in> eqc" and x: "x \<in> vars t" by auto
    from * assms(1)[unfolded finite_constructor_form_pat_def] 
    have "finite_constructor_form_mp mp" by auto
    from this[unfolded finite_constructor_form_mp_def] * obtain \<iota> 
      where "t : \<iota> in \<T>(C, \<V> |` SS)" by auto
    from hastype_in_Term_imp_vars[OF this x]
    have "snd x \<in> S" unfolding restrict_map_def by (auto split: if_splits)
  } note xS = this

  assume comp: "\<forall>pn\<in>Pn. simple_pat_complete C SS pn" 
  show "simple_pat_complete C SS p" unfolding simple_pat_complete_def
  proof (intro impI allI)
    fix \<sigma>
    assume sig: "\<sigma> :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
    have "x : snd x in \<V> |` SS" using xS by (cases x, auto simp: hastype_def restrict_map_def)
    with sig have sigx: "\<sigma> x : snd x in \<T>(C)" by (rule sorted_mapD)
    then obtain f ts where sigxF: "\<sigma> x = Fun f ts" 
      by (cases "\<sigma> x", auto)
    from sigx[unfolded this Fun_hastype] obtain \<iota>s 
      where f: "f : \<iota>s \<rightarrow> snd x in C" and ts: "ts :\<^sub>l \<iota>s in \<T>(C)" by auto
    define \<tau> where "\<tau> = \<tau>c n x (f,\<iota>s)" 
    define cond where "cond y = (fst y \<in> {n..<n+length \<iota>s} \<and> snd y = \<iota>s ! (fst y - n))" for y 
    define \<sigma>' where "\<sigma>' y = (if cond y then ts ! (fst y - n) else \<sigma> y)" for y
    {
      fix y
      assume "cond y" 
      hence "\<exists> i. y = (n + i, \<iota>s ! i) \<and> \<sigma>' y = ts ! i \<and> i < length \<iota>s" 
        unfolding cond_def \<sigma>'_def by (cases y, auto intro!: exI[of _ "fst y - n"])
    } note cond = this
    have sig': "\<sigma>' :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
    proof
      fix y \<iota>
      assume y: "y : \<iota> in \<V> |` SS" 
      show "\<sigma>' y : \<iota> in \<T>(C)" 
      proof (cases "cond y")
        case False
        hence "\<sigma>' y = \<sigma> y" unfolding \<sigma>'_def by auto
        with y sig show ?thesis by (metis sorted_mapE)
      next
        case True
        from cond[OF this]
        obtain i where *: "i < length \<iota>s" "\<sigma>' y = ts ! i" "y = (n + i, \<iota>s ! i)" by auto
        from *(3) y have "\<iota> = \<iota>s ! i" 
          by (auto simp: hastype_def restrict_map_def split: if_splits)
        with y * show ?thesis using list_all2_nthD2[OF ts, of i] by auto
      qed
    qed
    let ?p = "(`) ((`) (\<lambda> t. t \<cdot> \<tau>)) ` p" 
    from f have "\<tau> \<in> \<tau>s n x" unfolding \<tau>s_def \<tau>_def by auto
    hence "?p \<in> Pn" by (auto simp: assms)
    from comp[rule_format, OF this, unfolded simple_pat_complete_def, rule_format, OF sig']
    obtain mp where mp: "mp \<in> p" and comp: "simple_match_complete_wrt \<sigma>' ((`) (\<lambda>t. t \<cdot> \<tau>) ` mp)" by auto
    show "Bex p (simple_match_complete_wrt \<sigma>)" 
    proof (intro bexI[OF _ mp])
      have "simple_match_complete_wrt \<sigma> mp = simple_match_complete_wrt \<sigma>' mp" 
      proof (rule tvars_spat_cong[OF _ mp])
        fix y
        assume yp: "y \<in> tvars_spat p" 
        show "\<sigma> y = \<sigma>' y" 
        proof (cases "cond y")
          case False
          thus ?thesis unfolding \<sigma>'_def by auto
        next
          case True
          from cond[OF this] obtain i where y: "y = (n + i, \<iota>s ! i)" and i: "i < length \<iota>s" by auto
          from disj yp have "fst y \<notin> {n ..< n + m}" by fastforce
          with y have "i \<ge> m" by auto
          with m[OF f] i have False by auto
          thus ?thesis ..
        qed
      qed
      also have \<dots> unfolding simple_match_complete_wrt_def UNIQ_subst_alt_def
      proof clarify
        fix eqc s t
        assume "eqc \<in> mp" "s \<in> eqc" "t \<in> eqc" 
        from comp[unfolded simple_match_complete_wrt_def UNIQ_subst_alt_def, rule_format, OF imageI imageI imageI, OF this]
        have eq: "s \<cdot> \<tau> \<cdot> \<sigma>' = t \<cdot> \<tau> \<cdot> \<sigma>'" .
        {
          fix y
          have "(\<tau> \<circ>\<^sub>s \<sigma>') y = \<sigma>' y" 
          proof (cases "y = x")
            case False
            thus ?thesis unfolding subst_compose_def \<tau>_def \<tau>c_def split by (simp add: subst_def)
          next
            case True
            have cx: "\<not> cond x" 
            proof
              assume "cond x" 
              from cond[OF this] m[OF f] have "fst x \<in> {n ..< n + m}" by auto
              with disj x show False by blast
            qed
            hence sig'x: "\<sigma>' x = \<sigma> x" unfolding \<sigma>'_def by auto
            show ?thesis unfolding True sig'x sigxF using cx ts[unfolded list_all2_conv_all_nth]
              by (auto simp add: \<tau>c_def subst_compose_def \<sigma>'_def \<tau>_def cond_def intro!: nth_equalityI)
          qed
        }
        with eq show "s \<cdot> \<sigma>' = t \<cdot> \<sigma>'" by (metis eval_same_vars_cong eval_subst)
      qed
      finally show "simple_match_complete_wrt \<sigma> mp" .
    qed
  qed
next
  show "Ball Pn finite_constructor_form_pat" 
    unfolding finite_constructor_form_pat_def finite_constructor_form_mp_def
  proof (intro ballI, goal_cases)
    case (1 pn mpn eqcn)
    from this[unfolded Pn] obtain \<tau> mp eqc where
      mem: "mp \<in> p" "eqc \<in> mp" and eqcn: "eqcn = (\<lambda> t. t \<cdot> \<tau>) ` eqc" 
      and tau: "\<tau> \<in> \<tau>s n x" 
      by auto
    from tau[unfolded \<tau>s_def] obtain f \<sigma>s where f: "f : \<sigma>s \<rightarrow> snd x in C" and tau: "\<tau> = \<tau>c n x (f,\<sigma>s)" by auto
    from assms(1)[unfolded finite_constructor_form_pat_def finite_constructor_form_mp_def, rule_format, OF mem]
    obtain \<iota> where ne: "eqc \<noteq> {}" and fin: "finite_sort C \<iota>" and typed: " t \<in> eqc \<Longrightarrow> t : \<iota> in \<T>(C,\<V> |` SS)" for t by auto 
    show "eqcn \<noteq> {} \<and> (\<exists>\<iota>. finite_sort C \<iota> \<and> (\<forall>t\<in>eqcn. t : \<iota> in \<T>(C,\<V> |` SS)))" 
    proof (intro conjI exI[of _ \<iota>] fin ballI)
      show "eqcn \<noteq> {}" using ne unfolding eqcn by auto
      fix tt
      assume "tt \<in> eqcn" 
      then obtain t where t: "t \<in> eqc" and tt: "tt = t \<cdot> \<tau>" unfolding eqcn by auto
      from typed[OF t] have t: "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
      show "tt : \<iota> in \<T>(C, \<V> |` SS)" unfolding tt
      proof (rule subst_hastype[OF _ t], standard)
        fix y \<sigma>
        assume y: "y : \<sigma> in \<V> |` SS" 
        show "\<tau> y : \<sigma> in \<T>(C,\<V> |` SS)" 
        proof (cases "y = x")
          case False
          with y show ?thesis unfolding tau \<tau>c_def split subst_def by simp
        next
          case True
          with y have \<sigma>: "\<sigma> = snd x" by (auto simp: hastype_def restrict_map_def split: if_splits)
          {
            fix i
            assume "i < length \<sigma>s"
            hence "\<sigma>s ! i \<in> S" using C_sub_S[OF f] by auto
            hence "(n + i, \<sigma>s ! i) : \<sigma>s ! i in \<V> |` SS" by (auto simp: hastype_def restrict_map_def)
          }
          thus ?thesis unfolding \<sigma> True tau \<tau>c_def split subst_def
            by (auto intro!: Fun_hastypeI[OF f] list_all2_all_nthI)
        qed
      qed
    qed
  qed
qed

lemma typed_restrict_imp_typed: "t : s in \<T>(D, W |` F) \<Longrightarrow> t : s in \<T>(D, W)"
  by (meson Term_mono_right restrict_submap subssetD)

lemma eliminate_large_sort: assumes
  cond: "\<And> i. i \<le> (n :: nat) \<Longrightarrow> snd (x i) = \<iota> \<and> eq i \<in> mp i \<and> Var (x i) \<noteq> t i \<and> {Var (x i), t i} \<subseteq> eq i" and
  vars: "x ` {0..n} \<inter> tvars_spat p = {}" and
  large: "card (t ` {0..n}) < card_of_sort C \<iota>" and
  fin: "finite_constructor_form_pat (p \<union> mp ` {0..n})" 
shows "simple_pat_complete C SS (p \<union> mp ` {0..n}) = simple_pat_complete C SS p" 
proof 
  assume comp: "simple_pat_complete C SS p"
  thus "simple_pat_complete C SS (p \<union> mp ` {0..n})" 
    unfolding simple_pat_complete_def by blast
next
  let ?p' = "p \<union> mp ` {0..n}"
  assume comp: "simple_pat_complete C SS ?p'"
  show "simple_pat_complete C SS p" 
    unfolding simple_pat_complete_def
  proof (intro allI impI, goal_cases)
    case \<sigma>: (1 \<sigma>)
    let ?T = "t ` {0..n}" 
    let ?X = "x ` {0..n}"  
    let ?TX = "?T \<union> (Var o x) ` {0..n}" 
    define Tf where "Tf = (?T - Var ` ?X)" (* T-terms that are fixed, i.e., where substitution is not modified *)
    define DomT where "DomT = {x. Var x \<in> ?T \<and> Var x \<notin> Tf}" (* variables of T whose substitution is modified *)
    have DomT_alt: "DomT = ?X \<inter> {x. Var x \<in> ?T}" unfolding DomT_def Tf_def by auto
    define Dom where "Dom = ?X" 
    define Avoid where "Avoid = {t \<cdot> \<sigma> |t. t \<in> Tf}"
    define Ran where "Ran = {t. t : \<iota> in \<T>(C)} - Avoid"
    {
      fix i
      assume i: "i \<le> n" 
      note cond = cond[OF this]
      from cond have eq: "eq i \<in> mp i" by auto
      from i fin have "finite_constructor_form_mp (mp i)" 
        unfolding finite_constructor_form_pat_def by auto
      from this[unfolded finite_constructor_form_mp_def, rule_format, OF eq]
      obtain \<iota>' where fin: "finite_sort C \<iota>'" and sort: "\<And> s. s\<in>eq i \<Longrightarrow> s : \<iota>' in \<T>(C,\<V> |` SS)" 
        by auto
      from cond have terms: "Var (x i) \<in> eq i" "t i \<in> eq i" "x i : \<iota> in \<V>" by auto
      from sort[OF this(1)] this(3) have id: "\<iota>' = \<iota>"
        by (metis Var_hastype typed_S_eq)
      note fin = fin[unfolded id]
      note sort = sort[unfolded id]
      from sort[OF terms(1)] have iota: "\<iota> \<in> S" by (rule typed_imp_S)
      note sort[OF terms(1)] sort[OF terms(2)] fin iota
    } note terms = this
  
    have fin\<iota>: "finite_sort C \<iota>" using terms[of 0] by auto
    have "\<iota> \<in> S" using terms[of 0] by auto
    note terms = terms(1,2)
    {
      fix s
      assume "s \<in> ?TX" 
      with terms have "s : \<iota> in \<T>(C,\<V> |` SS)" by auto
    } note TX = this
    hence T: "s \<in> ?T \<Longrightarrow> s : \<iota> in \<T>(C,\<V> |` SS)" for s by auto
        
    {
      define Terms where "Terms = ?T" 
      define GTerms where "GTerms = {s. s : \<iota> in \<T>(C)}" 
      from fin\<iota> have finG: "finite GTerms" unfolding GTerms_def finite_sort_def by auto
      from large[unfolded cd[OF \<open>\<iota> \<in> S\<close>] card_of_sort_def]
      have fin: "finite Terms" 
        and card: "card Terms < card GTerms" 
        by (auto simp: Terms_def GTerms_def)
      let ?Var = "Var :: nat \<times> 's \<Rightarrow> ('f, nat \<times> 's)term"
      have splitTerms: "?Var ` DomT \<union> Tf \<subseteq> Terms" "?Var ` DomT \<inter> Tf = {}"  
        unfolding DomT_def Terms_def Tf_def by auto
      from splitTerms finite_subset[OF _ fin] 
      have fin': "finite (?Var ` DomT)" "finite Tf" 
        by auto
      from card_mono[OF fin splitTerms(1)] card card_Un_disjoint[OF fin'] splitTerms
      have "card (?Var ` DomT) + card Tf < card GTerms" 
        by auto
      hence "card DomT < card GTerms - card Tf" using card_image[of ?Var]
        by simp
      also have "\<dots> \<le> card GTerms - card (Tf  \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>)" using fin'(2)
        by (meson card_image_le diff_le_mono2)
      also have "\<dots> = card (GTerms - (Tf  \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>))" 
      proof (rule card_Diff_subset[symmetric, OF finite_imageI[OF fin'(2)]])
        {
          fix ts
          assume "ts \<in> Tf \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
          then obtain t where "t \<in> ?T" and ts: "ts = t \<cdot> \<sigma>" 
            unfolding Tf_def by auto
          with terms have "t : \<iota> in \<T>(C, \<V> |` SS)" by auto
          with \<sigma> have "ts \<in> GTerms" unfolding ts GTerms_def by (simp add: subst_hastype)
        }
        thus "Tf \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> GTerms" by auto
      qed
      also have "Tf  \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> = Avoid" unfolding Avoid_def by auto
      also have id: "GTerms - Avoid = Ran" unfolding Ran_def GTerms_def by simp
      finally have main: "card DomT < card Ran" .      
      from finG have finR: "finite Ran" unfolding id[symmetric] by blast
      have finD: "finite DomT" using finite_imageD[OF fin'(1)] by auto
      from main obtain fresh where fresh: "fresh \<in> Ran" by (cases "Ran = {}", auto)
      define RanT where "RanT = Ran - {fresh}" 
      have "card RanT = card Ran - 1" using fresh finR unfolding RanT_def by auto
      with main have main: "card DomT \<le> card RanT" by auto
      from finR have finRT: "finite RanT" unfolding RanT_def by auto
      from card_le_inj[OF finD finRT main]
      obtain h where h: "h \<in> DomT \<rightarrow> RanT" and hinj: "inj_on h DomT" by auto
      define g where "g y = (if y \<in> DomT then h y else fresh)" for y
      have gRan: "g \<in> Dom \<rightarrow> Ran" unfolding g_def using fresh h RanT_def by auto
      have gInj: "inj_on g DomT" unfolding g_def using hinj by (auto simp: inj_on_def)
      {
        fix y
        assume "y \<in> Dom - DomT" 
        hence "g y = fresh" unfolding g_def by auto
        hence "g y \<notin> RanT" unfolding RanT_def by auto
        hence "g y \<notin> g ` DomT" using h unfolding g_def by auto
      }
      with gRan gInj have "\<exists> g. g \<in> Dom \<rightarrow> Ran \<and> inj_on g DomT \<and> (\<forall> y \<in> Dom - DomT. g y \<notin> g ` DomT)" 
        by blast
    }
    then obtain \<delta> where \<delta>Ran: "\<delta> \<in> Dom \<rightarrow> Ran" 
      and inj: "inj_on \<delta> DomT"
      and inj': "y \<in> Dom - DomT \<Longrightarrow> \<delta> y \<notin> \<delta> ` DomT" for y
      by blast


    {
      fix y
      assume "y \<in> Dom" 
      hence "Var y \<in> ?TX" unfolding DomT_def Dom_def by auto
      from TX[OF this] have "snd y = \<iota>"
        by (simp add: hastype_restrict)
    } note Dom = this

    define \<sigma>' where "\<sigma>' x = (if x \<in> Dom then \<delta> x else \<sigma> x)" for x


    {
      fix s
      assume "s \<in> Tf" 
      hence s: "s \<in> ?T" and cond: "is_Fun s \<or> the_Var s \<notin> Dom" 
        unfolding Tf_def Dom_def by auto
      have "s \<cdot> \<sigma>' = s \<cdot> \<sigma>" 
      proof (intro term_subst_eq)
        fix y
        assume y: "y \<in> vars s"
        show "\<sigma>' y = \<sigma> y" using cond
        proof (cases s)
          case (Fun f ts)
          with y have "s \<rhd> Var y" by fastforce
          then obtain c where c: "c \<noteq> Hole" and sc: "s = c \<langle> Var y \<rangle>" by blast
          from T[OF s] have s: "s : \<iota> in \<T>(C,\<V> |` SS)" .
          with \<sigma> have s\<sigma>: "s \<cdot> \<sigma> : \<iota> in \<T>(C)" by (rule subst_hastype)
          have "y \<notin> Dom" 
          proof
            assume "y \<in> Dom" 
            hence "Var y \<in> ?TX" unfolding Dom_def DomT_def by auto
            from TX[OF this]
            have "Var y : \<iota> in \<T>(C,\<V> |` SS) " .
            hence \<sigma>y: "\<sigma> y : \<iota> in \<T>(C)" using \<sigma>
              by (simp add: sorted_mapD)
            obtain t1 d t2 where id: "t1 = s \<cdot> \<sigma>" "d = c \<cdot>\<^sub>c \<sigma>" "t2 = \<sigma> y" by auto
            from sc have eq: "t1 = d \<langle> t2 \<rangle>" 
              by (simp add: id)
            from \<sigma>y s\<sigma> have t1: "t1 : \<iota> in \<T>(C)" "t2 : \<iota> in \<T>(C)" by (auto simp: id)
            from c have dh: "d \<noteq> Hole" by (cases c, auto simp: id)
            from dh have size: "size (d \<langle> t \<rangle>) > size t" for t by (rule size_ne_ctxt)
            define stack where "stack i = ((\<lambda> t. d \<langle>t\<rangle>) ^^ i) t2" for i
            from t1[unfolded eq]
            have d: "d : \<iota> \<rightarrow> \<iota> in \<C>(C,\<lambda>x. None)" by (rule apply_ctxt_hastype_imp_hastype_context)
            {
              fix i
              have "stack i : \<iota> in \<T>(C) \<and> size (stack i) \<ge> i" 
              proof (induct i)
                case 0
                thus ?case by (simp add: stack_def t1)
              next
                case (Suc i)
                have "stack (Suc i) = d \<langle>stack i\<rangle>" unfolding stack_def by simp
                with Suc d size[of "stack i"] show ?case by (auto intro: apply_ctxt_hastype)
              qed
            } note stack = this
            have inf: "infinite (range stack)" 
            proof
              assume "finite (range stack)" 
              hence "finite (size ` range stack)" by auto
              then obtain n where "\<And> i. size (stack i) \<le> n"
                by (meson UNIV_I finite_nat_set_iff_bounded_le image_eqI)
              from this[of "Suc n"] stack[of "Suc n"] show False by auto
            qed
            from stack have "range stack \<subseteq> {t . t : \<iota> in \<T>(C)}" by auto
            with inf have "infinite {t. t : \<iota> in \<T>(C)}" by (metis infinite_super)
            with fin\<iota>
            show False unfolding finite_sort_def by blast
          qed
          thus "\<sigma>' y = \<sigma> y" unfolding \<sigma>'_def by auto
        next
          case (Var y)
          with cond y show ?thesis unfolding \<sigma>'_def by auto
        qed
      qed
    } note \<sigma>'\<sigma> = this

    {
      fix x
      assume "x \<in> Dom" 
      with \<delta>Ran have "\<delta> x \<in> Ran" by auto
      from this[unfolded Ran_def]
      have "\<delta> x \<in> {t. t : \<iota> in \<T>(C)} - Avoid" .
    } note \<delta> = this

    from Dom \<delta> \<sigma> have \<sigma>': "\<sigma>' :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
      unfolding \<sigma>'_def sorted_map_def restrict_map_def by (auto split: if_splits)
    from comp[unfolded simple_pat_complete_def, rule_format, OF this]
    obtain mp' where mp: "mp' \<in> ?p'" and comp: "simple_match_complete_wrt \<sigma>' mp'" 
      by auto

    from mp show ?case
    proof
      assume mp': "mp' \<in> p" 
      have "simple_match_complete_wrt \<sigma>' mp' = simple_match_complete_wrt \<sigma> mp'" 
        unfolding simple_match_complete_wrt_def
      proof (intro ball_cong refl)
        fix eqc
        assume eqc: "eqc \<in> mp'" 
        {
          fix s
          assume s: "s \<in> eqc" 
          define V where "V = tvars_spat p" 
          have "s \<cdot> \<sigma> = s \<cdot> \<sigma>'" 
          proof (rule term_subst_eq)
            fix y
            assume "y \<in> vars s" 
            with eqc s mp' have "y \<in> tvars_spat p" by auto
            with vars have "y \<notin> Dom" unfolding V_def[symmetric] Dom_def by fastforce
            thus "\<sigma> y = \<sigma>' y" unfolding \<sigma>'_def by auto
          qed
        }
        thus "UNIQ_subst \<sigma>' eqc = UNIQ_subst \<sigma> eqc" unfolding UNIQ_subst_alt_def by auto
      qed
      with comp show ?thesis using mp' by auto
    next
      assume "mp' \<in> mp ` {0..n}" 
      then obtain i where "mp' = mp i" and i: "i \<in> {0..n}" by auto
      with comp[unfolded simple_match_complete_wrt_def] cond[of i]
      have "UNIQ_subst \<sigma>' (eq i)" by auto
      from this[unfolded UNIQ_subst_alt_def] cond[of i] i
      have eq: "\<sigma>' (x i) = t i \<cdot> \<sigma>'" by auto
      from cond[of i] i have diff: "Var (x i) \<noteq> t i" by auto
      from i have xi: "x i \<in> Dom" unfolding Dom_def by auto
      with \<delta>[OF this] have "\<sigma>' (x i) \<notin> Avoid" unfolding \<sigma>'_def by auto
      with eq have "t i \<cdot> \<sigma>' \<notin> Avoid" by auto
      with \<sigma>'\<sigma> have "t i \<notin> Tf" unfolding Avoid_def by auto
      from this[unfolded Tf_def] i obtain j where j: "j \<in> {0..n}" and ti: "t i = Var (x j)" 
        by auto
      from diff[unfolded ti] have diff: "x i \<noteq> x j" by auto
      from eq[unfolded ti] have eq: "\<sigma>' (x i) = \<sigma>' (x j)" by auto
      from i j have inDom: "{x i, x j} \<subseteq> Dom" unfolding Dom_def by auto
      with eq have eq: "\<delta> (x i) = \<delta> (x j)" unfolding \<sigma>'_def by auto
      with inj inj' inDom diff 
      have False
        by (metis (mono_tags, lifting) Diff_iff DomT_def Dom_def \<open>t i \<notin> Tf\<close> i image_eqI inj_onD
            mem_Collect_eq ti)
      thus ?thesis ..
    qed
  qed
qed

end

end