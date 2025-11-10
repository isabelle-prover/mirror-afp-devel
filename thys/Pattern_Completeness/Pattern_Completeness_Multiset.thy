section \<open>A Multiset-Based Inference System to Decide Pattern Completeness\<close>

theory Pattern_Completeness_Multiset
  imports 
    Pattern_Completeness_Set
    LP_Duality.Minimum_Maximum
    Polynomial_Factorization.Missing_List (* list_all2_map_map *)
    First_Order_Terms.Term_Pair_Multiset
    FCF_Problem
begin

subsection \<open>Definition of the Inference Rules\<close>

text \<open>We next switch to a multiset based implementation of the inference rules.
  At this level, termination is proven and further, that the evaluation cannot get stuck.
  The inference rules closely mimic the ones in the paper, though there is one additional
  inference rule for getting rid of duplicates (which are automatically removed when working
  on sets).\<close>

type_synonym ('f,'v,'s)match_problem_mset = "(('f,nat \<times> 's)term \<times> ('f,'v)term) multiset" 
type_synonym ('f,'v,'s)pat_problem_mset = "('f,'v,'s)match_problem_mset multiset" 
type_synonym ('f,'v,'s)pats_problem_mset = "('f,'v,'s)pat_problem_mset multiset"

abbreviation mp_mset :: "('f,'v,'s)match_problem_mset \<Rightarrow> ('f,'v,'s)match_problem_set" 
  where "mp_mset \<equiv> set_mset" 

abbreviation pat_mset :: "('f,'v,'s)pat_problem_mset \<Rightarrow> ('f,'v,'s)pat_problem_set"
  where "pat_mset \<equiv> image mp_mset o set_mset" 

abbreviation pats_mset :: "('f,'v,'s)pats_problem_mset \<Rightarrow> ('f,'v,'s)pats_problem_set" 
  where "pats_mset \<equiv> image pat_mset o set_mset" 

abbreviation (input) bottom_mset :: "('f,'v,'s)pats_problem_mset" where "bottom_mset \<equiv> {# {#} #}" 

context pattern_completeness_context
begin
text \<open>A terminating version of @{const P_step_set} working on multisets 
  that also treats the transformation on a more modular basis.\<close>

definition subst_match_problem_mset :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)match_problem_mset \<Rightarrow> ('f,'v,'s)match_problem_mset" where
  "subst_match_problem_mset \<tau> = image_mset (subst_left \<tau>)" 

definition subst_pat_problem_mset :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)pat_problem_mset \<Rightarrow> ('f,'v,'s)pat_problem_mset" where
  "subst_pat_problem_mset \<tau> = image_mset (subst_match_problem_mset \<tau>)" 

definition \<tau>s_list :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> ('f,nat \<times> 's)subst list" where 
  "\<tau>s_list n x = map (\<tau>c n x) (Cl (snd x))" 

inductive mp_step_mset :: "('f,'v,'s)match_problem_mset \<Rightarrow> ('f,'v,'s)match_problem_mset \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sub>m\<close> 50)where
  match_decompose: "(f,length ts) = (g,length ls)
    \<Longrightarrow> add_mset (Fun f ts, Fun g ls) mp \<rightarrow>\<^sub>m mp + mset (zip ts ls)" 
| match_match: "x \<notin> \<Union> (vars ` snd ` set_mset mp)
    \<Longrightarrow> add_mset (t, Var x) mp \<rightarrow>\<^sub>m mp" 
| match_duplicate: "add_mset pair (add_mset pair mp) \<rightarrow>\<^sub>m add_mset pair mp"
| match_decompose': "mp + mp' \<rightarrow>\<^sub>m (\<Sum>(t, l) \<in># mp. mset (zip (args t) (map Var ys))) + mp'"
  if "\<And> t l. (t,l) \<in># mp \<Longrightarrow> l = Var y \<and> root t = Some (f,n)" 
     "\<And> t l. (t,l) \<in># mp' \<Longrightarrow> y \<notin> vars l"
     "lvars_disj_mp ys (mp_mset (mp + mp'))" "length ys = n"
     "size mp \<ge> 2" (* for size = 0 get non-termination, for size = 1, use match_match instead *)
     improved

inductive match_fail :: "('f,'v,'s)match_problem_mset \<Rightarrow> bool" where
  match_clash: "(f,length ts) \<noteq> (g,length ls)  
    \<Longrightarrow> match_fail (add_mset (Fun f ts, Fun g ls) mp)" 
| match_clash': "Conflict_Clash s t \<Longrightarrow> match_fail (add_mset (s, Var x) (add_mset (t, Var x) mp))"       
| match_clash_sort: "\<T>(C,\<V>) s \<noteq> \<T>(C,\<V>) t \<Longrightarrow> match_fail (add_mset (s, Var x) (add_mset (t, Var x) mp))"       

inductive pp_step_mset :: "('f,'v,'s)pat_problem_mset \<Rightarrow> ('f,'v,'s)pats_problem_mset \<Rightarrow> bool"
  (infix \<open>\<Rightarrow>\<^sub>m\<close> 50) where
  pat_remove_pp: "add_mset {#} pp \<Rightarrow>\<^sub>m {#}" 
| pat_simp_mp: "mp_step_mset mp mp' \<Longrightarrow> add_mset mp pp \<Rightarrow>\<^sub>m {# (add_mset mp' pp) #}" 
| pat_remove_mp: "match_fail mp \<Longrightarrow> add_mset mp pp \<Rightarrow>\<^sub>m {# pp #}"
| pat_instantiate: "tvars_disj_pp {n ..< n+m} (pat_mset (add_mset mp pp)) \<Longrightarrow>
   (Var x, l) \<in> mp_mset mp \<and> is_Fun l \<or>
   \<not> improved \<and> (s,Var y) \<in> mp_mset mp \<and> (t,Var y) \<in> mp_mset mp \<and> Conflict_Var s t x \<and> \<not> inf_sort (snd x)
    \<Longrightarrow>
  add_mset mp pp \<Rightarrow>\<^sub>m mset (map (\<lambda> \<tau>. subst_pat_problem_mset \<tau> (add_mset mp pp)) (\<tau>s_list n x))"
| pat_inf_var_conflict: "Ball (pat_mset pp) inf_var_conflict \<Longrightarrow> pp \<noteq> {#}
    \<Longrightarrow> Ball (tvars_pat (pat_mset pp')) (\<lambda> x. \<not> inf_sort (snd x)) \<Longrightarrow> 
    (\<not> improved \<Longrightarrow> pp' = {#})
    \<Longrightarrow> pp + pp' \<Rightarrow>\<^sub>m {# pp' #}" 

inductive_set pp_nd_step_mset :: "('f,'v,'s)pat_problem_mset rel" (\<open>\<Rightarrow>\<^sub>n\<^sub>d\<close>) where
  "pp \<Rightarrow>\<^sub>m P \<Longrightarrow> p' \<in># P \<Longrightarrow> (pp,p') \<in> \<Rightarrow>\<^sub>n\<^sub>d"  


inductive P_step_mset :: "('f,'v,'s)pats_problem_mset \<Rightarrow> ('f,'v,'s)pats_problem_mset \<Rightarrow> bool"
  (infix \<open>\<Rrightarrow>\<^sub>m\<close> 50)where
  P_failure: "add_mset {#} P \<noteq> bottom_mset \<Longrightarrow> add_mset {#} P \<Rrightarrow>\<^sub>m bottom_mset" 
| P_simp_pp: "pp \<Rightarrow>\<^sub>m pp' \<Longrightarrow> add_mset pp P \<Rrightarrow>\<^sub>m pp' + P"

text \<open>The relation (encoded as predicate) is finally wrapped in a set\<close>
definition P_step :: "(('f,'v,'s)pats_problem_mset \<times> ('f,'v,'s)pats_problem_mset)set" (\<open>\<Rrightarrow>\<close>) where
  "\<Rrightarrow> = {(P,P'). P \<Rrightarrow>\<^sub>m P'}" 


subsection \<open>The evaluation cannot get stuck\<close>

lemmas subst_defs = 
  subst_pat_problem_mset_def 
  subst_pat_problem_set_def
  subst_match_problem_mset_def
  subst_match_problem_set_def

lemma pat_mset_fresh_vars: 
  "\<exists> n. tvars_disj_pp {n..<n + m} (pat_mset p)" 
proof -  
  define p' where "p' = pat_mset p" 
  define V where "V = fst ` \<Union> (vars ` (fst ` \<Union> p'))" 
  have "finite V" unfolding V_def p'_def by auto
  define n where "n = Suc (Max V)" 
  {
    fix mp t l
    assume "mp \<in> p'" "(t,l) \<in> mp" 
    hence sub: "fst ` vars t \<subseteq> V" unfolding V_def by force
    {
      fix x
      assume "x \<in> fst ` vars t" 
      with sub have "x \<in> V" by auto
      with \<open>finite V\<close> have "x \<le> Max V" by simp
      also have "\<dots> < n" unfolding n_def by simp
      finally have "x < n" .
    }
    hence "fst ` vars t \<inter> {n..<n + m} = {}" by force
  }
  thus ?thesis unfolding tvars_disj_pp_def p'_def[symmetric]
    by (intro exI[of _ n] ballI, force)
qed

lemma mp_mset_in_pat_mset: "mp \<in># pp \<Longrightarrow> mp_mset mp \<in> pat_mset pp"
  by auto
lemma mp_step_mset_cong: 
  assumes "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* mp mp'"
  shows "(add_mset (add_mset mp p) P, add_mset (add_mset mp' p) P) \<in> \<Rrightarrow>\<^sup>*" 
  using assms
proof induct
  case (step mp' mp'')
  from P_simp_pp[OF pat_simp_mp[OF step(2), of p], of P]
  have "(add_mset (add_mset mp' p) P, add_mset (add_mset mp'' p) P) \<in> P_step" 
    unfolding P_step_def by auto
  with step(3)
  show ?case by simp
qed auto

lemma mp_step_mset_vars: assumes "mp \<rightarrow>\<^sub>m mp'"
  shows "tvars_match (mp_mset mp) \<supseteq> tvars_match (mp_mset mp')" 
  using assms 
proof induct 
  case *: (match_decompose' mp y f n mp' ys)
  {
    let ?mset = "mset :: _ \<Rightarrow> ('f,'v,'s)match_problem_mset"
    fix x
    assume "x \<in> tvars_match (mp_mset ((\<Sum>(t, l)\<in>#mp. ?mset (zip (args t) (map Var ys)))))" 
    from this[unfolded tvars_match_def, simplified]
    obtain t l ti yi where tl: "(t,l) \<in># mp" and tiyi: "(ti,yi) \<in># ?mset (zip (args t) (map Var ys))" 
      and x: "x \<in> vars ti" 
      by auto
    from *(1)[OF tl] obtain ts where l: "l = Var y" and t: "t = Fun f ts" and lts: "length ts = n"
      by (cases t, auto)
    from tiyi[unfolded t] have "ti \<in> set ts"
      using set_zip_leftD by fastforce
    with x t have "x \<in> vars t" by auto
    hence "x \<in> tvars_match (mp_mset mp)" using tl unfolding tvars_match_def by auto
  }
  thus ?case unfolding tvars_match_def by force
qed (auto simp: tvars_match_def set_zip)

lemma mp_step_mset_steps_vars: assumes "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* mp mp'"
  shows "tvars_match (mp_mset mp) \<supseteq> tvars_match (mp_mset mp')" 
  using assms by (induct, insert mp_step_mset_vars, auto)

end

lemma count_le_size: "count A x \<le> size A" 
  by (induct A, auto)

lemma Max_le_MaxI: assumes "finite A" "A \<noteq> {}" "finite B" 
  "\<And> a. a \<in> A \<Longrightarrow> \<exists> b \<in> B. a \<le> b" 
shows "Max A \<le> Max B" 
  using assms by (metis Max_ge_iff Max_in empty_iff)

lemma steps_bound: assumes "\<And> x y. (x,y) \<in> r \<Longrightarrow> f x > f y" 
  and "(x,y) \<in> r^^n" 
shows "f x \<ge> f y + n" 
  using assms(2)
proof (induct n arbitrary: x y)
  case (Suc n x z)
  then obtain y where "(x,y) \<in> r^^n" and "(y,z) \<in> r" by auto
  from Suc(1)[OF this(1)] assms(1)[OF this(2)]
  show ?case by auto
qed auto

context pattern_completeness_context_with_assms begin

lemma pat_empty_or_trans_or_finite_constr_form:
  fixes p :: "('f,'v,'s) pat_problem_mset"
  assumes inf: "improved \<Longrightarrow> infinite (UNIV :: 'v set)" and wf: "wf_pat (pat_mset p)"
  shows "p = {#} \<or> (\<exists> ps. p \<Rightarrow>\<^sub>m ps) \<or> (improved \<and> finite_constr_form_pat C (pat_mset p))" 
proof (cases "p = {#}")
  case True
  thus ?thesis by auto
next
  case pne: False
  from pat_mset_fresh_vars obtain n where fresh: "tvars_disj_pp {n..<n + m} (pat_mset p)" by blast
  show ?thesis
  proof (cases "{#} \<in># p")
    case True
    then obtain p' where "p = add_mset {#} p'" by (rule mset_add)
    with pat_remove_pp show ?thesis by auto
  next
    case empty_p: False
    show ?thesis
    proof (cases "\<exists> mp s t. mp \<in># p \<and> (s,t) \<in># mp \<and> is_Fun t")
      case True
      then obtain mp s t where mp: "mp \<in># p" and "(s,t) \<in># mp" and "is_Fun t" by auto
      then obtain g ts where mem: "(s,Fun g ts) \<in># mp" by (cases t, auto)
      from mp obtain p' where p: "p = add_mset mp p'" by (rule mset_add)
      from mem obtain mp' where mp: "mp = add_mset (s, Fun g ts) mp'" by (rule mset_add)
      show ?thesis
      proof (cases s)
        case s: (Fun f ss)
        from pat_simp_mp[OF match_decompose, of f ss] pat_remove_mp[OF match_clash, of f ss]
        show ?thesis unfolding p mp s by blast
      next
        case (Var x)
        from Var mem obtain l where "(Var x, l) \<in># mp \<and> is_Fun l" by auto
        from pat_instantiate[OF fresh[unfolded p] disjI1[OF this]]
        show ?thesis unfolding p by auto
      qed
    next
      case False
      hence rhs_vars: "\<And> mp s l. mp \<in># p \<Longrightarrow> (s,l) \<in># mp \<Longrightarrow> is_Var l" by auto
      let ?single_var = "(\<exists> mp t x. add_mset (t,Var x) mp \<in># p \<and> x \<notin> \<Union> (vars ` snd ` set_mset mp))"
      let ?duplicate = "(\<exists> mp pair. add_mset pair (add_mset pair mp) \<in># p)" 
      show ?thesis
      proof (cases "?single_var \<or> ?duplicate")
        case True
        thus ?thesis
        proof
          assume ?single_var
          then obtain mp t x where mp: "add_mset (t,Var x) mp \<in># p" and x: "x \<notin> \<Union> (vars ` snd ` set_mset mp)" 
            by auto
          from mp obtain p' where "p = add_mset (add_mset (t,Var x) mp) p'" by (rule mset_add)
          with pat_simp_mp[OF match_match[OF x]] show ?thesis by auto
        next
          assume ?duplicate
          then obtain mp pair where "add_mset pair (add_mset pair mp) \<in># p" (is "?dup \<in># p") by auto
          from mset_add[OF this] obtain p' where
            p: "p = add_mset ?dup p'" . 
          from pat_simp_mp[OF match_duplicate[of pair]] show ?thesis unfolding p by auto
        qed
      next
        case False
        hence ndup: "\<not> ?duplicate" and nsvar: "\<not> ?single_var" by auto
        {
          fix mp s x
          assume mpp: "mp \<in># p" and sx: "(s, Var x) \<in># mp" 
          from mpp obtain p' where p: "p = add_mset mp p'" by (rule mset_add)
          from sx obtain mp' where mp: "mp = add_mset (s, Var x) mp'" by (rule mset_add)
          from nsvar[simplified, rule_format, OF mpp[unfolded mp]] 
          obtain t l where "(t,l) \<in># mp'" and "x \<in> vars (snd (t,l))" by force
          with rhs_vars[OF mpp, of t l] have tx: "(t,Var x) \<in># mp'" unfolding mp by auto
          then obtain mp'' where mp': "mp' = add_mset (t, Var x) mp''" by (rule mset_add)
          from ndup[simplified, rule_format] mpp have "s \<noteq> t" unfolding mp mp' by auto 
          hence "\<exists> t mp'. mp = add_mset (s, Var x) (add_mset (t, Var x) mp') \<and> s \<noteq> t" unfolding mp mp' by auto
        } note twoX = this
        {
          fix mp
          assume mpp: "mp \<in># p" 
          with empty_p have mp_e: "mp \<noteq> {#}" by auto
          obtain s l where sl: "(s,l) \<in># mp" using mp_e by auto
          from rhs_vars[OF mpp sl] sl obtain x where sx: "(s, Var x) \<in># mp" by (cases l, auto)
          from twoX[OF mpp sx] 
          have "\<exists> s t x mp'. mp = add_mset (s, Var x) (add_mset (t, Var x) mp') \<and> s \<noteq> t" by blast
        } note two = this
        show ?thesis
        proof (cases "\<exists> mp s t x. add_mset (s, Var x) (add_mset (t, Var x) mp) \<in># p \<and> Conflict_Clash s t")
          case True
          then obtain mp s t x where 
            mp: "add_mset (s, Var x) (add_mset (t, Var x) mp) \<in># p" (is "?mp \<in># _") and conf: "Conflict_Clash s t" 
            by blast
          from pat_remove_mp[OF match_clash'[OF conf, of x mp]] 
          show ?thesis using mset_add[OF mp] by metis
        next
          case no_clash: False
          show ?thesis
          proof (cases improved)
            case not_impr: False
            show ?thesis 
            proof (cases "\<exists> mp s t x y. add_mset (s, Var x) (add_mset (t, Var x) mp) \<in># p \<and> Conflict_Var s t y \<and> \<not> inf_sort (snd y)") 
              case True
              from True obtain mp s t x y where 
                mp: "add_mset (s, Var x) (add_mset (t, Var x) mp) \<in># p" (is "?mp \<in># _") and conf: "Conflict_Var s t y" and y: "\<not> inf_sort (snd y)" 
                by blast
              from mp obtain p' where p: "p = add_mset ?mp p'" by (rule mset_add)
              let ?mp = "add_mset (s, Var x) (add_mset (t, Var x) mp)" 
              from pat_instantiate[OF _ disjI2, of n ?mp p' s x t y, folded p, OF fresh]
              show ?thesis using y conf not_impr by auto
            next
              case no_non_inf: False
              have "\<exists> ps. p + {#} \<Rightarrow>\<^sub>m ps"
              proof (intro exI, rule pat_inf_var_conflict[OF _ pne], intro ballI)
                fix mp
                assume mp: "mp \<in> pat_mset p"
                then obtain mp' where mp': "mp' \<in># p" and mp: "mp = mp_mset mp'" by auto 
                from two[OF mp']
                obtain s t x mp''
                  where mp'': "mp' = add_mset (s, Var x) (add_mset (t, Var x) mp'')" and diff: "s \<noteq> t" by auto
                from conflicts(3)[OF diff] obtain y where "Conflict_Clash s t \<or> Conflict_Var s t y" by auto
                with no_clash mp'' mp' have conf: "Conflict_Var s t y" by force
                with no_non_inf mp'[unfolded mp''] have inf: "inf_sort (snd y)" by blast
                show "inf_var_conflict mp" unfolding inf_var_conflict_def mp mp'' 
                  apply (rule exI[of _ s], rule exI[of _ t])
                  apply (intro exI[of _ x] exI[of _ y])
                  using insert inf conf by auto
              qed (auto simp: tvars_pat_def)
              thus ?thesis by auto
            qed
          next
            case impr: True
            define exVar where "exVar mp = (\<forall> x t. (t, Var x) \<in># mp \<longrightarrow> (\<exists> y. (Var y, Var x) \<in># mp))" 
              for mp :: "('f,'v,'s)match_problem_mset" 
            show ?thesis
            proof (cases "\<forall> mp \<in># p. exVar mp")
              case False
              then obtain mp where mpp: "mp \<in># p" and "\<not> exVar mp" by auto
              from this[unfolded exVar_def] obtain s x where sx: "(s, Var x) \<in># mp" and 
                no_var: "\<And> y. (Var y, Var x) \<notin># mp" 
                by auto
              from no_var have allFun: "(t, Var x) \<in># mp \<Longrightarrow> is_Fun t" for t by (cases t, auto)
              from sx no_var obtain f ss where s: "s = Fun f ss" by (cases s, auto)
              from twoX[OF mpp sx] obtain t mp' where stx: "mp = add_mset (s, Var x) (add_mset (t, Var x) mp')" 
                and st: "s \<noteq> t" by auto
              let ?Var = "Var :: 'v \<Rightarrow> ('f, 'v)term" 
              let ?f = "\<lambda> tl. snd tl = ?Var x"
              define mp1 where "mp1 = filter_mset ?f mp" 
              have size: "size mp1 \<ge> 2" unfolding mp1_def stx by auto
              define mp2 where "mp2 = filter_mset (Not o ?f) mp" 
              {
                fix t l
                assume "(t,l) \<in># mp2" 
                hence "(t,l) \<in># mp" and "l \<noteq> Var x" unfolding mp2_def by auto
                from rhs_vars[OF mpp this(1)] this(2) have "x \<notin> vars l" by (cases l, auto)
              } note mp2 = this
              define n where "n = length ss" 
              with s have rtS: "root s = Some (f,n)" unfolding n_def by auto
              from stx have smp: "(s, Var x) \<in># mp" by auto
              {
                fix t l
                assume "(t,l) \<in># mp1" 
                from this[unfolded mp1_def]
                have l: "l = Var x" and tmp: "(t,Var x) \<in># mp"  by auto
                from allFun tmp obtain g ts where t: "t = Fun g ts" by (cases t, auto)
                {
                  assume rtT: "root t \<noteq> Some (f,n)" 
                  hence st: "s \<noteq> t" using rtS by auto
                  from rtS rtT have clash: "Conflict_Clash s t" unfolding s t
                    by (auto simp: conflicts.simps)
                  from smp tmp st have "\<exists> mp'. mp = add_mset (s, Var x) (add_mset (t, Var x) mp')" 
                    by (metis insert_noteq_member multi_member_split prod.inject)
                  with clash no_clash mpp have False by blast
                }
                hence "l = Var x \<and> root t = Some (f,n)" using l by auto
              } note mp1 = this

              define VV where "VV = \<Union> (vars ` snd ` mp_mset mp)" 
              have "finite VV" by (auto simp: VV_def)
              with inf[OF impr] have "infinite (UNIV - VV)" by auto
              then obtain Ys where Ys: "Ys \<subseteq> UNIV - VV" "card Ys = n" "finite Ys"
                by (meson infinite_arbitrarily_large)
              from Ys(2-3) obtain ys where ys: "distinct ys" "length ys = n" "set ys = Ys"
                by (metis distinct_card finite_distinct_list)
              with Ys have dist: "VV \<inter> set ys = {}" by auto
              have disj: "lvars_disj_mp ys (mp_mset mp)" "length ys = n" 
                unfolding lvars_disj_mp_def using ys dist unfolding VV_def by auto
              have "mp = mp1 + mp2" unfolding mp1_def mp2_def by simp
              from match_decompose'[of mp1 x _ _ mp2, folded this, OF mp1 mp2 disj size impr]
              obtain mp' where "mp \<rightarrow>\<^sub>m mp'" by fast
              from pat_simp_mp[OF this] mpp
              show ?thesis by (metis mset_add)
            next
              case exVar: True
              show ?thesis
              proof (cases "\<forall> mp \<in># p. (\<forall> t l. (t,l) \<in># mp \<longrightarrow> is_Var l \<and> \<T>(C,\<V>) t \<noteq> None)")
                case False
                then obtain mp s l where mpp: "mp \<in># p" and sl: "(s,l) \<in># mp" and 
                  ch: "\<not> is_Var l \<or> \<T>(C,\<V>) s = None" 
                  by auto
                from rhs_vars[OF mpp sl] obtain x where l: "l = Var x" by auto
                with ch have None: "\<T>(C,\<V>) s = None" by auto
                from None obtain f ss where s: "s = Fun f ss" by (cases s, auto)
                from sl l have sx: "(s, Var x) \<in># mp" by auto
                from exVar[unfolded exVar_def, rule_format, OF mpp sx] obtain y
                  where "(Var y, Var x) \<in># mp" by auto
                with sx obtain mp' where "mp = add_mset (Var y, Var x) (add_mset (s, Var x) mp')" 
                  unfolding s by (metis insert_noteq_member is_FunI is_VarI mset_add prod.inject)
                from match_clash_sort[of "Var y" s x mp', unfolded None, folded this]
                have "match_fail mp" by auto
                from pat_remove_mp[OF this] mpp
                show ?thesis by (metis mset_add)
              next
                case constr_form: True
                define finmp where "finmp mp = (\<forall> t l. (t, l) \<in># mp \<longrightarrow> (\<exists> \<iota>. finite_sort C \<iota> \<and> t : \<iota> in \<T>(C,\<V>)))" 
                  for mp :: "('f,'v,'s)match_problem_mset"
                show ?thesis
                proof (cases "\<forall> mp \<in># p. finmp mp")
                  case True
                  {
                    fix mp
                    assume mp: "mp \<in># p" 
                    hence "finmp mp" using True by auto
                    with constr_form mp have "finite_constr_form_mp C (mp_mset mp)" 
                      unfolding finmp_def by (simp add: finite_constr_form_mp_def)
                  }
                  thus ?thesis using impr unfolding finite_constr_form_pat_def by auto
                next
                  case someInf: False
                  show ?thesis
                  proof (cases "\<exists> s t x mp. mp \<in># p \<and> (s, Var x) \<in># mp \<and> (t, Var x) \<in># mp \<and> \<T>(C,\<V>) s \<noteq> \<T>(C,\<V>) t") 
                    case True
                    then obtain s t x mp where mp: "mp \<in># p" and s: "(s, Var x) \<in># mp" and t: "(t, Var x) \<in># mp" 
                      and sort_clash: "\<T>(C,\<V>) s \<noteq> \<T>(C,\<V>) t"
                      by auto
                    from sort_clash have st: "s \<noteq> t" by auto
                    with s t obtain mp' where "mp = add_mset (s, Var x) (add_mset (t, Var x) mp')" 
                      by (metis insert_noteq_member mset_add prod.inject)
                    from match_clash_sort[of s t x mp', folded this] sort_clash
                    have "match_fail mp" by auto
                    from pat_remove_mp[OF this] show ?thesis using mp
                      by (metis mset_add)
                  next
                    case False
                    hence noSortClash: "\<And> s t x mp. mp \<in># p  \<Longrightarrow> (s, Var x) \<in># mp \<Longrightarrow> (t, Var x) \<in># mp \<Longrightarrow> \<T>(C,\<V>) s = \<T>(C,\<V>) t" 
                      by blast

                    define p1 where "p1 = filter_mset (Not o finmp) p" 
                    define p2 where "p2 = filter_mset finmp p" 
                    have p: "p = p1 + p2" unfolding p1_def p2_def by simp
                    have "p \<Rightarrow>\<^sub>m {#p2#}" unfolding p 
                    proof (rule pat_inf_var_conflict[of p1 p2]; (intro ballI, clarsimp)?)
                      {
                        from someInf obtain mp where "mp \<in># p" and "\<not> finmp mp" by auto
                        hence "mp \<in># p1" unfolding p1_def by auto
                        thus "p1 \<noteq> {#}" by auto
                      }
                      {
                        fix mp
                        assume "mp \<in># p1" 
                        from this[unfolded p1_def] have nfin: "\<not> finmp mp" and mp: "mp \<in># p" by auto
                        from nfin[unfolded finmp_def, simplified]
                        obtain t l where tl: "(t, l) \<in># mp" and inf: "\<And> \<iota>. finite_sort C \<iota> \<Longrightarrow> \<not> t : \<iota> in \<T>(C,\<V>)" 
                          by auto
                        from constr_form[rule_format, OF mp tl] have l: "is_Var l" and sorted: "\<T>(C,\<V>) t \<noteq> None" 
                          by auto
                        from l obtain x where l: "l = Var x" by auto
                        from sorted obtain \<iota> where sorted: "t : \<iota> in \<T>(C,\<V>)" by (cases "\<T>(C,\<V>) t", auto simp: hastype_def)
                        from inf sorted have inf: "\<not> finite_sort C \<iota>" by auto
                        from tl l have tx: "(t, Var x) \<in># mp" by auto
                        from exVar[unfolded exVar_def, rule_format, OF mp tx] obtain y 
                          where yx: "(Var y, Var x) \<in># mp" by auto
                        have y: "Var y : snd y in \<T>(C,\<V>)" by simp
                        from noSortClash[OF mp yx tx] sorted y inf
                        have inf: "\<not> finite_sort C (snd y)" by (auto simp: hastype_def)
                        from wf[unfolded wf_pat_def wf_match_def tvars_match_def, simplified, rule_format, OF mp]
                          yx 
                        have "snd y \<in> S" by force
                        with inf have  inf: "inf_sort (snd y)" using inf_sort by auto
                        from twoX[OF mp yx]
                        obtain t mp' where mp': "mp = add_mset (Var y, Var x) (add_mset (t, Var x) mp')"
                          and yt: "Var y \<noteq> t" by auto
                        from mp' have tx:  "(t, Var x) \<in># mp" by auto
                        from noSortClash[OF mp yx tx] y 
                        have t: "t : snd y in \<T>(C,\<V>)" by (auto simp: hastype_def)
                        obtain cs where conf: "conflicts (Var y) t = Some cs" "y \<in> set cs"  
                          using t yt by (cases t, auto simp: conflicts.simps)
                        show "inf_var_conflict (mp_mset mp)" 
                          unfolding inf_var_conflict_def
                          by (intro exI conjI, rule yx, rule tx, insert inf conf, auto)
                      }
                      {
                        fix x
                        assume x: "x \<in> tvars_pat (mp_mset ` set_mset p2)" and inf: "inf_sort (snd x)" 
                        from x[unfolded tvars_pat_def tvars_match_def]
                        obtain mp t l where mp: "mp \<in># p2" and tl: "(t,l) \<in># mp" and x: "x \<in> vars t" by auto
                        from mp[unfolded p2_def] have fin: "finmp mp" and mp: "mp \<in># p" by auto
                        from wf[unfolded wf_pat_def wf_match_def, simplified, rule_format, OF mp] x tl
                        have xS: "snd x \<in> S" unfolding tvars_match_def by auto
                        from inf_sort[OF this] inf have inf: "\<not> finite_sort C (snd x)" by auto
                        from constr_form[rule_format, OF mp tl] obtain y where l: "l = Var y" 
                          and sorted: "\<T>(C,\<V>) t \<noteq> None" by auto
                        note ty = tl[unfolded l]
                        from fin[unfolded finmp_def, rule_format, OF tl] obtain \<iota> where
                          fin: "finite_sort C \<iota>" and sorted: "t : \<iota> in \<T>(C,\<V>)" by auto
                        from sorted x fin have "finite_sort C (snd x)" 
                        proof (induct)
                          case (Fun f ss \<sigma>s \<tau>)
                          then obtain s where s: "s \<in> set ss" and x: "x \<in> vars s" by auto
                          from s obtain i where i: "i < length ss" and si: "s = ss ! i" by (auto simp: set_conv_nth)
                          from Fun(2) si i have "s : \<sigma>s ! i in \<T>(C,\<V>)" 
                            and "i < length \<sigma>s" unfolding list_all2_conv_all_nth by auto
                          hence "\<sigma>s ! i \<in> set \<sigma>s" by auto
                          from finite_arg_sort[OF Fun(5,1) this] have "finite_sort C (\<sigma>s ! i)" by auto
                          with Fun(3) x show "finite_sort C (snd x)" unfolding si using i 
                            unfolding list_all2_conv_all_nth by auto
                        qed auto
                        with inf have False by simp
                      }
                      thus "\<And> x \<iota>. (x, \<iota>) \<in> tvars_pat (mp_mset ` set_mset p2) \<Longrightarrow> inf_sort \<iota> \<Longrightarrow> False"
                        by auto
                    qed (insert impr, auto)
                    thus ?thesis by auto
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed


context
  assumes non_improved: "\<not> improved"
begin

lemma pat_empty_or_trans: "wf_pat (pat_mset p) \<Longrightarrow> p = {#} \<or> (\<exists> ps. p \<Rightarrow>\<^sub>m ps)" 
  using pat_empty_or_trans_or_finite_constr_form[of p] non_improved by auto

text \<open>Pattern problems just have two normal forms: 
  empty set (solvable) or bottom (not solvable)\<close>
theorem P_step_NF: 
  assumes wf: "wf_pats (pats_mset P)" and NF: "P \<in> NF \<Rrightarrow>" 
  shows "P \<in> {{#}, bottom_mset}" 
proof (rule ccontr)
  assume nNF: "P \<notin> {{#}, bottom_mset}"
  from NF have NF: "\<not> (\<exists> Q. P \<Rrightarrow>\<^sub>m Q)" unfolding P_step_def by blast
  from nNF obtain p P' where P: "P = add_mset p P'"
    using multiset_cases by auto
  with wf have "wf_pat (pat_mset p)" by (auto simp: wf_pats_def)
  with pat_empty_or_trans
  obtain ps where "p = {#} \<or> p \<Rightarrow>\<^sub>m ps" by auto
  with P_simp_pp[of p ps] NF
  have "p = {#}" unfolding P by auto
  from P_failure[of P'] P this nNF NF show False by blast
qed
end


context
  assumes improved: "improved"
    and inf: "infinite (UNIV :: 'v set)" 
begin

lemma pat_empty_or_trans_or_fvf:
  fixes p :: "('f,'v,'s) pat_problem_mset"
  assumes "wf_pat (pat_mset p)"
  shows "p = {#} \<or> (\<exists> ps. p \<Rightarrow>\<^sub>m ps) \<or> finite_constr_form_pat C (pat_mset p)"
  using assms pat_empty_or_trans_or_finite_constr_form[of p, OF inf] by auto

text \<open>Normal forms only consist of finite-var-form pattern problems\<close>
theorem P_step_NF_fvf: 
  assumes wf: "wf_pats (pats_mset P)"
    and NF: "(P::('f,'v,'s) pats_problem_mset) \<in> NF \<Rrightarrow>" 
    and p: "p \<in># P"
  shows "finite_constr_form_pat C (pat_mset p)"  
proof (rule ccontr)
  assume nfvf: "\<not> ?thesis"
  from wf p have wfp: "wf_pat (pat_mset p)" by (auto simp: wf_pats_def)
  from mset_add[OF p] obtain P' where P: "P = add_mset p P'" by auto
  from NF have NF: "\<not> (\<exists> Q. P \<Rrightarrow>\<^sub>m Q)" unfolding P_step_def by blast
  from pat_empty_or_trans_or_fvf[OF wfp] nfvf
  obtain ps where "p = {#} \<or> p \<Rightarrow>\<^sub>m ps" by auto
  with P_simp_pp[of p ps] NF
  have "p = {#}" unfolding P by auto
  with nfvf show False unfolding finite_constr_form_pat_def by auto
qed

lemma pp_step_mset_empty_cong: assumes improved
  shows "p \<Rightarrow>\<^sub>m P \<Longrightarrow> p + replicate_mset n {#} \<Rightarrow>\<^sub>m image_mset (\<lambda> p'. p' + replicate_mset n {#}) P"
proof (induct rule: pp_step_mset.induct)
  case (pat_remove_pp pp)
  show ?case by simp (rule pat_remove_pp) 
next
  case *: (pat_simp_mp mp mp' pp)
  show ?case using pat_simp_mp[OF *] by auto
next
  case *: (pat_remove_mp mp pp)
  show ?case using pat_remove_mp[OF *] by auto
next
  case *: (pat_instantiate n' mp pp x l s y t)
  define tau where "tau = mset (\<tau>s_list n' x)" 
  define p where "p = add_mset mp pp" 
  from *(1) have "tvars_disj_pp {n'..<n' + m} (pat_mset (add_mset mp (pp + replicate_mset n {#})))"
    by (fastforce simp: tvars_disj_pp_def)
  from pat_instantiate[OF this *(2)]
  have "add_mset mp (pp + replicate_mset n {#}) \<Rightarrow>\<^sub>m
    mset (map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> (p + replicate_mset n {#})) (\<tau>s_list n' x))" 
    by (simp add: p_def)
  also have "mset (map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> (p + replicate_mset n {#})) (\<tau>s_list n' x))
   = {#p' + replicate_mset n {#}
    . p' \<in># mset (map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> p) (\<tau>s_list n' x))#}" 
    unfolding tau_def[symmetric] subst_pat_problem_mset_def subst_match_problem_mset_def mset_map
      image_mset.compositionality o_def by auto
  finally show ?case by (auto simp: p_def)
next
  case *: (pat_inf_var_conflict pp pp')
  have "pp + (pp' + replicate_mset n {#}) \<Rightarrow>\<^sub>m {#pp' + replicate_mset n {#}#}" 
    by (rule pat_inf_var_conflict[OF *(1-2)],
        insert *(3) \<open>improved\<close>, auto simp: tvars_pat_def tvars_match_def)
  thus ?case by (auto simp: ac_simps)
qed

theorem nd_step_NF_fvf: fixes p :: "('f,'v,'s) pat_problem_mset" 
  assumes "wf_pat (pat_mset p)" 
    and "p \<in> NF \<Rightarrow>\<^sub>n\<^sub>d" 
  shows "finite_constr_form_pat C (pat_mset p)" 
proof -
  define p1 where "p1 = filter_mset ((=) {#}) p" 
  define p2 where "p2 = filter_mset ((\<noteq>) {#}) p" 
  have p: "p = p1 + p2" by (auto simp: p1_def p2_def)
  from assms(1) have wf: "wf_pat (pat_mset p2)" unfolding p2_def wf_pat_def by auto
  define n where "n = size p1" 
  have p1: "p1 = replicate_mset n {#}" unfolding n_def p1_def
    by (metis (mono_tags, lifting) count_conv_size_mset filter_eq_replicate_mset filter_mset_cong0)
  with p have p: "p = p2 + replicate_mset n {#}" by simp
  {
    fix q
    assume "(p2,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d" 
    then obtain Q where "p2 \<Rightarrow>\<^sub>m Q" "q \<in># Q" by cases
    from pp_nd_step_mset.intros[OF pp_step_mset_empty_cong[OF \<open>improved\<close> this(1), of n, folded p]] 
      this(2)
    have "\<exists> q'. (p,q') \<in> \<Rightarrow>\<^sub>n\<^sub>d" by auto
    with assms have False by auto
  }
  hence NF: "p2 \<in> NF \<Rightarrow>\<^sub>n\<^sub>d" by auto
  from pat_empty_or_trans_or_fvf[OF wf]
  have "finite_constr_form_pat C (pat_mset p2)" 
  proof (elim disjE)
    show "p2 = {#} \<Longrightarrow> ?thesis" by (auto simp: finite_constr_form_pat_def)
    assume "\<exists>P. p2 \<Rightarrow>\<^sub>m P" 
    then obtain P where step: "p2 \<Rightarrow>\<^sub>m P" by auto
    with NF have P: "P = {#}"
      by (meson NF_no_step multiset_nonemptyE pattern_completeness_context.pp_nd_step_mset.simps)
    from step[unfolded P]
    show ?thesis
    proof (cases)
      case (pat_remove_pp pp)
      hence "{#} \<in># p2" by auto
      from this[unfolded p2_def] have False by simp
      then show ?thesis by auto
    next
      case *: (pat_instantiate n mp pp x l s y t)
      from * have "set (\<tau>s_list n x) = {}" by auto
      from this[unfolded \<tau>s_list_def] have "set (Cl (snd x)) = {}" by auto
      from this[unfolded Cl] have empty: "{(f, ss). f : ss \<rightarrow> snd x in C} = {}" by auto
      from * \<open>improved\<close> have "(Var x, l) \<in># mp" by auto
      with *(1) have "x \<in> tvars_pat (pat_mset p2)" 
        by (force simp: tvars_pat_def tvars_match_def)
      with wf have "snd x \<in> S" unfolding wf_pat_def wf_match_def tvars_pat_def by force
      hence "\<not> empty_sort C (snd x)" by (rule not_empty_sort)
      then obtain t where "t : snd x in \<T>(C)" unfolding empty_sort_def by auto
      from this empty have False by (induct, auto)
      then show ?thesis by auto
    qed auto
  qed auto
  thus ?thesis unfolding p finite_constr_form_pat_def
    by (auto simp: finite_constr_form_mp_def)
qed
end
end

subsection \<open>Termination\<close>

text \<open>A measure to count the number of function symbols of the first argument that don't
  occur in the second argument\<close>
fun fun_diff :: "('f,'v)term \<Rightarrow> ('f,'w)term \<Rightarrow> nat" where
  "fun_diff l (Var x) = num_funs l" 
| "fun_diff (Fun g ls) (Fun f ts) = (if f = g \<and> length ts = length ls then
     sum_list (map2 fun_diff ls ts) else 0)" 
| "fun_diff l t = 0" 

lemma fun_diff_Var[simp]: "fun_diff (Var x) t = 0" 
  by (cases t, auto)

lemma add_many_mult: "(\<And> y. y \<in># N \<Longrightarrow> (y,x) \<in> R) \<Longrightarrow> (N + M, add_mset x M) \<in> mult R"
  by (metis add.commute add_mset_add_single multi_member_last multi_self_add_other_not_self one_step_implies_mult)

lemma fun_diff_num_funs: "fun_diff l t \<le> num_funs l" 
proof (induct l t rule: fun_diff.induct)
  case (2 f ls g ts)
  show ?case
  proof (cases "f = g \<and> length ts = length ls")
    case True
    have "sum_list (map2 fun_diff ls ts) \<le> sum_list (map num_funs ls)"
      by (intro sum_list_mono2, insert True 2, (force simp: set_zip)+)
    with 2 show ?thesis by auto
  qed auto
qed auto

lemma fun_diff_subst: "fun_diff l (t \<cdot> \<sigma>) \<le> fun_diff l t" 
proof (induct l arbitrary: t)
  case l: (Fun f ls)
  show ?case
  proof (cases t)
    case t: (Fun g ts)
    show ?thesis unfolding t using l by (auto intro: sum_list_mono2)
  next
    case t: (Var x)
    show ?thesis unfolding t using fun_diff_num_funs[of "Fun f ls"] by auto
  qed
qed auto

lemma fun_diff_num_funs_lt: assumes t': "t' = Fun c cs" 
  and "is_Fun l" 
shows "fun_diff l t' < num_funs l"
proof -
  from assms obtain g ls where l: "l = Fun g ls" by (cases l, auto)
  show ?thesis 
  proof (cases "c = g \<and> length cs = length ls")
    case False 
    thus ?thesis unfolding t' l by auto
  next
    case True
    have "sum_list (map2 fun_diff ls cs) \<le> sum_list (map num_funs ls)" 
      apply (rule sum_list_mono2; (intro impI)?)
      subgoal using True by auto
      subgoal for i using True by (auto intro: fun_diff_num_funs)
      done  
    thus ?thesis unfolding t' l using True by auto
  qed
qed

lemma sum_union_le_nat: "sum (f :: 'a \<Rightarrow> nat) (A \<union> B) \<le> sum f A + sum f B" 
  by (metis finite_Un le_iff_add sum.infinite sum.union_inter zero_le)

lemma sum_le_sum_list_nat: "sum f (set xs) \<le> (sum_list (map f xs) :: nat)" 
proof (induct xs)
  case (Cons x xs)
  thus ?case 
    by (cases "x \<in> set xs", auto simp: insert_absorb)
qed auto

lemma bdd_above_has_Maximum_nat: "bdd_above (A :: nat set) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> has_Maximum A" 
  unfolding has_Maximum_def
  by (meson Max_ge Max_in bdd_above_nat)

fun syms_term :: "('f,'v)term \<Rightarrow> ('v + 'f)multiset" where
  "syms_term (Var x) = {# Inl x #}" 
| "syms_term (Fun f ts) = add_mset (Inr f) (sum_mset (image_mset syms_term (mset ts)))" 

lemma vars_term_syms_term: "x \<in> vars_term t \<longleftrightarrow> Inl x \<in># syms_term t" 
  by (induct t, auto)

lemma replicate_mset_add: "replicate_mset (n + m) a = replicate_mset n a + replicate_mset m a"
  by (metis repeat_mset_distrib repeat_mset_replicate_mset)

lemma syms_term_subst: "syms_term (t \<cdot> subst x s) + replicate_mset (count (syms_term t) (Inl x)) (Inl x)
  = syms_term t + repeat_mset (count (syms_term t) (Inl x)) (syms_term s)" (is "?l t = ?r t")
proof (induct t)
  case (Var y)
  show ?case unfolding subst_def by auto
next
  case (Fun f ts)
  have "?case \<longleftrightarrow> 
     (\<Sum>\<^sub># (image_mset syms_term {#sa \<cdot> subst x s. sa \<in># mset ts#}) +
     replicate_mset (count (\<Sum>\<^sub># (image_mset syms_term (mset ts))) (Inl x)) (Inl x) =
     \<Sum>\<^sub># (image_mset syms_term (mset ts)) +
     repeat_mset (count (\<Sum>\<^sub># (image_mset syms_term (mset ts))) (Inl x)) (syms_term s))" 
    (is "_ \<longleftrightarrow> ?ls ts = ?rs ts") by simp
  also have "\<dots>" using Fun
  proof (induct ts)
    case (Cons t ts)
    have "?rs (t # ts) = ?r t + ?rs ts" by auto
    also have "\<dots> = ?l t + ?ls ts" using Cons by auto
    also have "\<dots> = ?ls (t # ts)" by (simp add: replicate_mset_add)
    finally show ?case ..
  qed auto
  finally show ?case by simp
qed  


definition num_syms :: "('f,'v)term \<Rightarrow> nat" where
  "num_syms t = size (syms_term t)" 

lemma num_syms_pos[simp]: "num_syms t > 0" 
  unfolding num_syms_def by (cases t, auto)

lemma num_syms_0[simp]: "num_syms t \<noteq> 0" 
  unfolding num_syms_def by (cases t, auto)

lemma num_syms_subst: "num_syms (t \<cdot> subst x s) = num_syms t + count (syms_term t) (Inl x) * (num_syms s - 1)" 
proof -
  let ?cx = "count (syms_term t) (Inl x)" 
  from arg_cong[OF syms_term_subst[of t x s], of size]
  have "num_syms (t \<cdot> subst x s) + ?cx = num_syms t + ?cx * num_syms s" 
    unfolding size_union num_syms_def by simp
  from arg_cong[OF this, of "\<lambda> n . n - ?cx"]
  have "num_syms (t \<cdot> subst x s) = num_syms t + ?cx * num_syms s - ?cx" by auto
  also have "\<dots> = num_syms t + ?cx * (num_syms s - 1)" 
    using num_syms_pos[of s] by (cases "num_syms s", auto)
  finally show ?thesis .
qed

lemma num_syms_Fun[simp]: "num_syms (Fun f ts) = Suc (sum_list (map num_syms ts))" 
  unfolding num_syms_def
  by (simp, induct ts, auto)

abbreviation (input) sum_ms :: "('a \<Rightarrow> 'b :: comm_monoid_add) \<Rightarrow> 'a multiset \<Rightarrow> 'b" where
  "sum_ms f ms \<equiv> sum_mset (image_mset f ms)" 

lemma sum_ms_image: "sum_ms f (image_mset g ms) = sum_ms (f o g) ms"
  by (simp add: multiset.map_comp)

context pattern_completeness_context_with_assms
begin

lemma \<tau>s_list: "set (\<tau>s_list n x) = \<tau>s n x" 
  unfolding \<tau>s_list_def \<tau>s_def using Cl by auto

lemma num_syms_\<tau>c: "num_syms (t \<cdot> \<tau>c n x (f,\<sigma>s)) = num_syms t + count (syms_term t) (Inl x) * length \<sigma>s" 
  unfolding num_syms_subst \<tau>c_def split
  by (simp add: num_syms_def image_mset.compositionality o_def)

lemma num_syms_\<tau>s: assumes "\<tau> \<in> \<tau>s n x" 
  shows "num_syms (t \<cdot> \<tau>) \<le> num_syms t + count (syms_term t) (Inl x) * m" 
proof -
  from assms[unfolded \<tau>s_def]
  obtain f ss where \<tau>: "\<tau> = \<tau>c n x (f, ss)" and "f : ss \<rightarrow> snd x in C" by auto
  from m[OF this(2)] have len: "length ss \<le> m" . 
  hence "count (syms_term t) (Inl x) * length ss \<le> count (syms_term t) (Inl x) * m" by auto
  thus ?thesis unfolding \<tau> num_syms_\<tau>c by auto
qed

definition meas_diff_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> nat" where
  "meas_diff_mp = sum_ms (\<lambda> (t,l). fun_diff l t)" 

definition meas_diff :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_diff = sum_ms meas_diff_mp" 

definition max_size :: "'s \<Rightarrow> nat" where
  "max_size s = (if s \<in> S \<and> \<not> inf_sort s then Maximum (size ` {t. t : s in \<T>(C)}) else 0)" 

definition tsyms_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> (nat \<times> 's + 'f) multiset" where
  "tsyms_mp mp = sum_ms (syms_term o fst) mp" 

definition num_tsyms_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> nat" where
  "num_tsyms_mp mp = sum_ms (num_syms o fst) mp" 

definition num_lsyms_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> nat" where
  "num_lsyms_mp mp = sum_ms (num_syms o snd) mp" 

definition num_syms_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> nat" where
  "num_syms_mp mp = num_tsyms_mp mp + num_lsyms_mp mp" 

definition num_syms_pat :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "num_syms_pat = sum_ms num_syms_mp" 

definition meas_finvars_mp :: "('f,'v,'s)match_problem_mset \<Rightarrow> nat" where
  "meas_finvars_mp mp = sum (max_size o snd) (tvars_match (mp_mset mp))" 

definition max_dupl_mp where
  "max_dupl_mp mp = Max (insert 0 ((\<lambda> x. (\<Sum> t\<in># image_mset fst mp. count (syms_term t) (Inl x))) ` tvars_match (mp_mset mp)))" 

lemma max_dupl_mp_le_num_tsyms_mp: "max_dupl_mp mp \<le> num_tsyms_mp mp" 
  unfolding max_dupl_mp_def
proof (subst Max_le_iff, force intro!: finite_imageI simp: tvars_match_def, force, intro ballI)
  fix n
  assume n: "n \<in> insert 0 {\<Sum>t\<in>#image_mset fst mp. count (syms_term t) (Inl x) |. x \<in> tvars_match (mp_mset mp)}" 
  show "n \<le> num_tsyms_mp mp" 
  proof (cases "n = 0")
    case False
    with n obtain x where x: "x \<in> tvars_match (mp_mset mp)" 
      and n: "n = (\<Sum>t\<in>#image_mset fst mp. count (syms_term t) (Inl x))" by auto
    have nt: "num_tsyms_mp mp = (\<Sum>t\<in>#image_mset fst mp. num_syms t)" 
      unfolding num_tsyms_mp_def image_mset.compositionality ..
    show ?thesis unfolding n nt
    proof (rule sum_mset_mono, goal_cases)
      case (1 t)
      show "count (syms_term t) (Inl x) \<le> num_syms t" 
        unfolding num_syms_def by (rule count_le_size)
    qed
  qed auto
qed

lemma num_funs_le_num_syms: "num_funs t \<le> num_syms t" 
  by (induct t, auto intro: sum_list_mono)

lemma fun_diff_le_num_syms: "fun_diff l t \<le> num_syms l"
proof (induct l t rule: fun_diff.induct)
  case (1 l x)
  then show ?case by (auto intro: num_funs_le_num_syms)
next
  case (2 g ls f ts)
  show ?case
  proof (cases "f = g \<and> length ts = length ls")
    case True
    have "sum_list (map2 fun_diff ls ts) \<le> sum_list (map2 (\<lambda> l t. num_syms l) ls ts)" 
      by (rule sum_list_mono, insert 2[OF True], auto)
    also have "\<dots> = sum_list (map num_syms ls)" 
      by (rule arg_cong[of _ _ sum_list], insert True, auto intro!: nth_equalityI)
    finally show ?thesis by auto
  qed auto
qed auto

lemma meas_diff_mp_le_num_lsyms_mp: "meas_diff_mp mp \<le> num_lsyms_mp mp" 
  unfolding meas_diff_mp_def num_lsyms_mp_def o_def
  by (rule sum_mset_mono, auto intro: fun_diff_le_num_syms)


definition meas_finvars :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_finvars = sum_ms meas_finvars_mp"  

definition meas_tsymbols :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_tsymbols = sum_ms num_tsyms_mp"

definition meas_lsymbols :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_lsymbols = sum_ms num_lsyms_mp"

definition meas_dupl :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_dupl = sum_ms max_dupl_mp"

lemma tsyms_mp_num_tsyms: "num_tsyms_mp mp = size (tsyms_mp mp)" 
  by (induct mp, auto simp: num_tsyms_mp_def tsyms_mp_def num_syms_def)

lemma meas_dupl_le_num_syms_pat: "meas_dupl p \<le> num_syms_pat p" 
  unfolding meas_dupl_def num_syms_pat_def num_syms_mp_def
  by (rule sum_mset_mono, rule le_trans[OF max_dupl_mp_le_num_tsyms_mp], auto)

lemma meas_diff_le_num_syms_pat: "meas_diff p \<le> num_syms_pat p" 
  unfolding meas_diff_def num_syms_pat_def num_syms_mp_def
  by (rule sum_mset_mono, rule le_trans[OF meas_diff_mp_le_num_lsyms_mp], auto)

lemma tsyms_mp_subset_num_tsyms: "tsyms_mp mp \<subset># tsyms_mp mp' \<Longrightarrow> num_tsyms_mp mp < num_tsyms_mp mp'"
  unfolding tsyms_mp_num_tsyms by (rule mset_subset_size)

lemma tsyms_mp_mono: assumes "mp \<subseteq># mp'" shows "tsyms_mp mp \<subseteq># tsyms_mp mp'" 
proof -
  from assms obtain mp2 where "mp' = mp + mp2" 
    by (metis subset_mset.less_eqE)
  thus ?thesis unfolding tsyms_mp_def by auto
qed

lemma tsyms_mp_strict_mono: assumes "mp \<subset># mp'" shows "tsyms_mp mp \<subset># tsyms_mp mp'" 
proof -
  from subset_mset.lessE[OF assms] obtain mp1 where "mp' = mp + mp1" and "mp1 \<noteq> {#}" 
    by blast
  then obtain tl mp2 where "mp' = add_mset tl (mp + mp2)" by (cases mp1, auto)
  thus ?thesis unfolding tsyms_mp_def by (cases tl, cases "fst tl"; auto)
qed

definition measure_pat_poly :: "nat \<Rightarrow> ('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "measure_pat_poly c p = (c + meas_diff p) * (meas_dupl p * m + 1) + meas_tsymbols p" 

lemma measure_pat_poly: "measure_pat_poly c p \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)"
proof -
  have "measure_pat_poly c p \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 1) + num_syms_pat p" 
    unfolding measure_pat_poly_def
  proof (intro add_mono mult_mono le_refl meas_dupl_le_num_syms_pat meas_diff_le_num_syms_pat)
    show "meas_tsymbols p \<le> num_syms_pat p" unfolding meas_tsymbols_def num_syms_pat_def num_syms_mp_def
      by (intro sum_mset_mono, auto)
  qed auto
  also have "\<dots> \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" by simp
  finally show ?thesis .
qed

lemma measure_expr_decrease: assumes "d1 < (d2 :: nat)" "du1 \<le> du2" "sym1 \<le> sym2 + du2 * m" 
  shows "d1 * (du1 * m + 1) + sym1 < d2 * (du2 * m + 1) + sym2" 
proof -
  have "1 + (d1 * (du1 * m + 1) + sym1) \<le> 1 + (d1 * (du2 * m + 1) + (sym2 + du2 * m))" 
    by (intro add_mono mult_mono, insert assms, auto)
  also have "\<dots> = (1 + d1) * (du2 * m + 1) + sym2" 
    by (simp add: algebra_simps)
  also have "\<dots> \<le> d2 * (du2 * m + 1) + sym2" 
    by (intro mult_mono add_mono, insert assms, auto)
  finally show ?thesis by simp
qed

lemma measure_pat_poly_meas_diff: assumes "meas_diff p < meas_diff p'" 
  and "meas_dupl p \<le> meas_dupl p'" 
  and "meas_tsymbols p \<le> meas_tsymbols p' + meas_dupl p' * m" 
shows "measure_pat_poly c p < measure_pat_poly c p'"
  unfolding measure_pat_poly_def
  by (rule measure_expr_decrease, insert assms, auto)

lemma measure_pat_poly_num_syms: assumes "meas_diff p \<le> meas_diff p'" 
  and "meas_dupl p \<le> meas_dupl p'" 
  and "meas_tsymbols p < meas_tsymbols p'" 
shows "measure_pat_poly c p < measure_pat_poly c p'" 
  unfolding measure_pat_poly_def
  by (intro add_le_less_mono mult_mono, insert assms, auto)


definition rel_pat :: "('f,'v,'s)pat_problem_mset rel" (\<open>\<prec>\<close>) where
  "(\<prec>) = inv_image ({(x, y). x < y} <*lex*> {(x, y). x < y} <*lex*> {(x, y). x < y}) 
  (\<lambda> mp. (meas_diff mp, meas_finvars mp, meas_tsymbols mp))" 

abbreviation gt_rel_pat (infix \<open>\<succ>\<close> 50) where
  "pp \<succ> pp' \<equiv> (pp',pp) \<in> \<prec>" 

definition meas_setsize :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_setsize p = sum_ms (sum_ms (\<lambda> _. 1)) p + size p" 


(* for Pstep we need to also consider the set-size because of the failure rule *)
definition rel_pat' :: "('f,'v,'s)pat_problem_mset rel" where
  "rel_pat' = inv_image ({(x, y). x < y} <*lex*> {(x, y). x < y} <*lex*> {(x, y). x < y} <*lex*> {(x, y). x < y}) 
  (\<lambda> mp. (meas_diff mp, meas_finvars mp, meas_tsymbols mp, meas_setsize mp))" 

definition rel_pats :: "(('f,'v,'s)pats_problem_mset \<times> ('f,'v,'s)pats_problem_mset)set" (\<open>\<prec>mul\<close>) where
  "\<prec>mul = mult rel_pat'" 

abbreviation gt_rel_pats (infix \<open>\<succ>mul\<close> 50) where
  "P \<succ>mul P' \<equiv> (P',P) \<in> \<prec>mul" 

lemma wf_rel_pat: "wf \<prec>" 
  unfolding rel_pat_def
  by (intro wf_inv_image wf_lex_prod wf_less)

lemma wf_rel_pat': "wf rel_pat'" 
  unfolding rel_pat'_def
  by (intro wf_inv_image wf_lex_prod wf_less)

lemma wf_rel_pats: "wf \<prec>mul" 
  unfolding rel_pats_def
  by (intro wf_inv_image wf_mult wf_rel_pat')

lemma rel_pat_sub_rel_pat': "rel_pat \<subseteq> rel_pat'" 
  unfolding rel_pat_def rel_pat'_def by auto

lemma tvars_match_fin: 
  "finite (tvars_match (mp_mset mp))"  
  unfolding tvars_match_def by auto

lemmas meas_def = meas_finvars_def meas_diff_def meas_tsymbols_def meas_setsize_def
  meas_finvars_mp_def meas_diff_mp_def meas_dupl_def

lemma tvars_match_mono: "mp \<subseteq># mp' \<Longrightarrow> tvars_match (mp_mset mp) \<subseteq> tvars_match (mp_mset mp')" 
  unfolding tvars_match_def 
  by (intro image_mono subset_refl set_mset_mono UN_mono)

lemma meas_finvars_mp_mono: assumes "tvars_match (mp_mset mp) \<subseteq> tvars_match (mp_mset mp')" 
  shows "meas_finvars_mp mp \<le> meas_finvars_mp mp'" 
  using tvars_match_fin[of mp'] assms
  unfolding meas_def by (auto intro: sum_mono2)

lemma rel_mp_sub: "{# add_mset p mp#} \<succ> {# mp #}"
proof - 
  let ?mp' = "add_mset p mp" 
  have "mp \<subseteq># ?mp'" by auto
  from meas_finvars_mp_mono[OF tvars_match_mono[OF this]]
  show ?thesis unfolding meas_def rel_pat_def num_tsyms_mp_def by (cases p, auto)
qed

lemma mp_step_tsyms_mp_psubset:
  fixes mp :: "('f,'v,'s) match_problem_mset"
  assumes "mp \<rightarrow>\<^sub>m mp'"
  shows "tsyms_mp mp' \<subset># tsyms_mp mp"  
  using assms
proof cases
  case *: (match_decompose f ts g ls mp'')
  hence len: "length ls = length ts" by auto
  have "tsyms_mp mp' = tsyms_mp mp'' + (\<Sum>p\<in># mset (zip ts ls). syms_term (fst p))" 
    unfolding tsyms_mp_def * o_def by auto
  also have "(\<Sum>p\<in># mset (zip ts ls). syms_term (fst p)) = (\<Sum>t\<in># mset ts. syms_term t)" 
    using len proof (induct ts arbitrary: ls)
    case (Cons t ts ls)
    thus ?case by (cases ls, auto)
  qed auto
  also have "tsyms_mp mp'' + \<dots> \<subset># tsyms_mp mp'' + syms_term (Fun f ts)" 
    by auto
  also have "\<dots> = tsyms_mp mp" 
    unfolding tsyms_mp_def * by auto
  finally show ?thesis . 
next
  case *: (match_decompose' mp1 y f n mp2 ys)
  let ?Var = "Var :: 'v \<Rightarrow> ('f, 'v) term" 
  from * obtain t l mp1' where mp1: "mp1 = add_mset (t,l) mp1'" by (cases mp1, auto)
  from *(3)[of t l] *(6) mp1 obtain ts where t: "t = Fun f ts" and lents: "length ts = length ys" 
    by (cases t, auto)
  let ?TS = "(\<Sum>\<^sub># (image_mset syms_term (mset ts)))" 
  have "tsyms_mp mp = tsyms_mp mp1 + tsyms_mp mp2" unfolding * tsyms_mp_def by auto
  also have "\<dots> = syms_term t + tsyms_mp mp1' + tsyms_mp mp2" unfolding mp1 tsyms_mp_def o_def by auto
  also have "syms_term t = add_mset (Inr f) ?TS" unfolding t by auto
  finally have mp: "tsyms_mp mp \<supset># ?TS + tsyms_mp mp1' + tsyms_mp mp2" by auto

  have "tsyms_mp mp' = sum_ms (syms_term o fst) (sum_ms (\<lambda> (t, l). mset (zip (args t) (map ?Var ys))) mp1)
    + tsyms_mp mp2" unfolding * tsyms_mp_def 
    by simp
  also have "image_mset (syms_term o fst) (sum_ms (\<lambda> (t, l). mset (zip (args t) (map ?Var ys))) mp1)
    = (sum_ms (\<lambda> (t, l). image_mset (syms_term o fst) (mset (zip (args t) (map ?Var ys)))) mp1)" 
    by (induct mp1, auto)
  also have "\<dots> = sum_ms (\<lambda> p. image_mset syms_term (mset (args (fst p)))) mp1"
  proof (rule arg_cong[of _ _ sum_mset], rule image_mset_cong, goal_cases)
    case (1 p)
    {
      fix t l
      assume "(t,l) \<in># mp1" 
      from *(3)[OF this] *(6) obtain ts where args: "args t = ts" and len: "length ts = length ys" by (cases t, auto)
      have "image_mset (syms_term \<circ> fst) (mset (zip (args t) (map ?Var ys))) =
           image_mset syms_term (mset (args t))"
        unfolding args  using len 
      proof (induct ts arbitrary: ys)
        case (Cons t ts ys)
        thus ?case by (cases ys, auto)
      qed auto
    }
    thus ?case using 1 by (cases p, auto)
  qed
  finally have mp': "tsyms_mp mp' = ?TS + \<Sum>\<^sub># (\<Sum>p\<in>#mp1'. image_mset syms_term (mset (args (fst p)))) + tsyms_mp mp2" 
    by (auto simp: mp1 t)

  have mp1': "\<Sum>\<^sub># (\<Sum>p\<in>#mp1'. image_mset syms_term (mset (args (fst p)))) \<subseteq># tsyms_mp mp1'" 
    unfolding tsyms_mp_def image_mset.compositionality sum_ms_image o_def
  proof (induct mp1')
    case (add tl mp)
    then obtain t l where tl: "tl = (t,l)" by force
    show ?case unfolding tl 
      apply simp 
      apply (rule subset_mset.add_mono)
      subgoal by (cases t, auto)
      subgoal using add by auto
      done
  qed auto
  show ?thesis unfolding mp' using mp mp1' 
      subset_mset.dual_order.strict_trans2 by fastforce
next
  case *: (match_match x t)
  show ?thesis unfolding * by (rule tsyms_mp_strict_mono, auto)
next
  case *: (match_duplicate pair mp)
  show ?thesis unfolding * by (rule tsyms_mp_strict_mono, auto)
qed


lemma tvars_match_tsyms_mp: "tvars_match (mp_mset mp) = { x. Inl x \<in># tsyms_mp mp }" 
  unfolding tsyms_mp_def tvars_match_def o_def
  by (force simp: vars_term_syms_term)

lemma max_dupl_mp_mono: assumes "tsyms_mp mp \<subseteq># tsyms_mp mp'"
  shows "max_dupl_mp mp \<le> max_dupl_mp mp'"
  unfolding max_dupl_mp_def
proof (rule Max_le_MaxI, goal_cases)
  case 1
  show ?case by (auto intro: tvars_match_fin)
next
  case 2 
  show ?case by auto
next
  case 3
  show ?case by (auto intro: tvars_match_fin)
next
  case (4 d)
  show ?case
  proof (cases "d = 0")
    case True
    thus ?thesis by auto
  next
    case False
    let ?Inl = "Inl :: nat \<times> 's \<Rightarrow> nat \<times> 's + 'f" 
    from 4 False obtain x where x: "x \<in> tvars_match (mp_mset mp)" 
      and d: "d = (\<Sum>t\<in>#image_mset fst mp. count (syms_term t) (?Inl x))" by auto
    have eq: "(\<Sum>t\<in>#image_mset fst mp. count (syms_term t) (?Inl x)) = count (tsyms_mp mp) (?Inl x)" for 
      mp :: "(('f, nat \<times> 's) term \<times> ('f, 'v) term) multiset" 
      unfolding tsyms_mp_def o_def by (induct mp, auto)
    from assms x have x': "x \<in> tvars_match (mp_mset mp')" unfolding tvars_match_tsyms_mp 
      using set_mset_mono by auto
    have "d \<le> (\<Sum>t\<in>#image_mset fst mp'. count (syms_term t) (?Inl x))" 
      unfolding d eq using assms by (rule mset_subset_eq_count)
    with x' show ?thesis by auto
  qed
qed

lemma mp_step_mset_meas_max_dupl: assumes "mp \<rightarrow>\<^sub>m mp'"
  shows "max_dupl_mp mp' \<le> max_dupl_mp mp"
  by (rule max_dupl_mp_mono, insert mp_step_tsyms_mp_psubset[OF assms], auto)

lemma mp_step_mset_meas_finvars: assumes "mp \<rightarrow>\<^sub>m mp'"
  shows "meas_finvars_mp mp' \<le> meas_finvars_mp mp" 
proof (rule meas_finvars_mp_mono)
  from mp_step_tsyms_mp_psubset[OF assms]
  have "tsyms_mp mp' \<subseteq># tsyms_mp mp" by auto
  thus "tvars_match (mp_mset mp') \<subseteq> tvars_match (mp_mset mp)" 
    unfolding tvars_match_tsyms_mp
    by (meson Collect_mono set_mset_mono subsetD)
qed

lemma mp_step_mset_num_tsyms_mp: assumes "mp \<rightarrow>\<^sub>m mp'"
  shows "num_tsyms_mp mp' < num_tsyms_mp mp" 
proof -
  from mp_step_tsyms_mp_psubset[OF assms]
  have "tsyms_mp mp' \<subset># tsyms_mp mp" by auto
  thus ?thesis by (rule tsyms_mp_subset_num_tsyms)
qed

lemma mp_step_mset_meas_diff_mp:
  fixes mp :: "('f,'v,'s) match_problem_mset"
  assumes "mp \<rightarrow>\<^sub>m mp'"
  shows "meas_diff_mp mp' \<le> meas_diff_mp mp" 
  using assms
proof cases
  case *: (match_decompose f ts g ls mp'')
  have id: "(case case x of (x, y) \<Rightarrow> (y, x) of (t, l) \<Rightarrow> f t l) = (case x of (a,b) \<Rightarrow> f b a)" for 
    x :: "('f, 'v) Term.term \<times> ('f, nat \<times> 's) Term.term" and f :: "_ \<Rightarrow> _ \<Rightarrow> nat" 
    by (cases x, auto)
  show "meas_diff_mp mp' \<le> meas_diff_mp mp" 
    unfolding meas_def * using *(3) 
    by (auto simp: sum_mset_sum_list[symmetric] zip_commute[of ts ls] image_mset.compositionality o_def id)
next
  case *: (match_decompose' mp1 y f n mp2 ys)
  let ?Var = "Var :: 'v \<Rightarrow> ('f, 'v) term" 
  have "meas_diff_mp mp' \<le> meas_diff_mp mp
    \<longleftrightarrow> (\<Sum>(ti, yi)\<in>#(\<Sum>(t, l)\<in>#mp1. mset (zip (args t) (map ?Var ys))). fun_diff yi ti)
    \<le> (\<Sum>(t, l)\<in>#mp1. fun_diff l t)" (is "_ \<longleftrightarrow> ?sum \<le> _")
    unfolding * meas_diff_mp_def by simp
  also have "?sum = 0" 
    by (intro sum_mset.neutral ballI, auto simp: set_zip)
  finally show ?thesis by simp
qed (auto simp: meas_def)


lemma rel_mp_mp_step_mset:
  fixes mp :: "('f,'v,'s) match_problem_mset"
  assumes step: "mp \<rightarrow>\<^sub>m mp'"
  shows "{#mp#} \<succ> {#mp'#}"  
proof -
  from 
    mp_step_mset_meas_finvars[OF step] 
    mp_step_mset_num_tsyms_mp[OF step]
    mp_step_mset_meas_diff_mp[OF step]
  show ?thesis by (auto simp: rel_pat_def meas_diff_def meas_finvars_def meas_tsymbols_def)
qed

lemma mp_step_measure_pat_poly:
  fixes mp :: "('f,'v,'s) match_problem_mset"
  assumes step: "mp \<rightarrow>\<^sub>m mp'"
  shows "measure_pat_poly c (add_mset mp p) > measure_pat_poly c (add_mset mp' p)"   
proof (rule measure_pat_poly_num_syms)
  show "meas_diff (add_mset mp' p) \<le> meas_diff (add_mset mp p)" 
    using mp_step_mset_meas_diff_mp[OF step] unfolding meas_diff_def by auto
  show "meas_dupl (add_mset mp' p) \<le> meas_dupl (add_mset mp p)" 
    using mp_step_mset_meas_max_dupl[OF step] unfolding meas_dupl_def by auto
  show "meas_tsymbols (add_mset mp' p) < meas_tsymbols (add_mset mp p)" 
    using mp_step_mset_num_tsyms_mp[OF step] unfolding meas_tsymbols_def by auto
qed

lemma meas_diff_subst_le: "meas_diff (subst_pat_problem_mset \<tau> p) \<le> meas_diff p"
  unfolding meas_def subst_match_problem_set_def subst_defs subst_left_def
  unfolding sum_ms_image o_def
  apply (rule sum_mset_mono, rule sum_mset_mono)
  apply clarify
  unfolding map_prod_def split id_apply
  by (rule fun_diff_subst)

lemma meas_sub: assumes sub: "p' \<subseteq># p" 
  shows "meas_diff p' \<le> meas_diff p"
    "meas_finvars p' \<le> meas_finvars p"
    "meas_tsymbols p' \<le> meas_tsymbols p"
    "meas_dupl p' \<le> meas_dupl p" 
proof -
  from sub obtain p'' where p: "p = p' + p''" by (metis subset_mset.less_eqE)
  show "meas_diff p' \<le> meas_diff p" "meas_finvars p' \<le> meas_finvars p" 
    "meas_tsymbols p' \<le> meas_tsymbols p" "meas_dupl p' \<le> meas_dupl p"
    unfolding meas_def p by auto
qed

lemma meas_sub_rel_pat: assumes sub: "p' \<subset># p" 
  shows "(p', p) \<in> rel_pat'"
proof -
  from sub obtain x p'' where p: "p = add_mset x p' + p''"
    by (metis multi_nonempty_split subset_mset.lessE union_mset_add_mset_left union_mset_add_mset_right)
  hence lt: "meas_setsize p' < meas_setsize p" unfolding meas_def by auto
  from sub have "p' \<subseteq># p" by auto
  from lt meas_sub[OF this]
  show ?thesis unfolding rel_pat'_def by auto
qed

lemma max_size_term_of_sort: assumes sS: "s \<in> S" and inf: "\<not> inf_sort s" 
  shows "\<exists> t. t : s in \<T>(C) \<and> max_size s = size t \<and> (\<forall> t'. t' : s in \<T>(C) \<longrightarrow> size t' \<le> size t)" 
proof -
  let ?set = "\<lambda> s. size ` {t. t : s in \<T>(C)}" 
  have m: "max_size s = Maximum (?set s)" unfolding o_def max_size_def using inf sS by auto
  from inf inf_sort_not_bdd[OF sS] have "bdd_above (?set s)" by auto
  moreover have "?set s \<noteq> {}" by (auto intro!: sorts_non_empty sS) 
  ultimately have "has_Maximum (?set s)" by (rule bdd_above_has_Maximum_nat) 
  from has_MaximumD[OF this, folded m] show ?thesis by auto
qed

lemma max_size_max: assumes sS: "s \<in> S" 
  and inf: "\<not> inf_sort s" 
  and sort: "t : s in \<T>(C)" 
shows "size t \<le> max_size s"  
  using max_size_term_of_sort[OF sS inf] sort by auto

lemma finite_sort_size: assumes c: "c : map snd vs \<rightarrow> s in C"
  and inf: "\<not> inf_sort s"  
shows "sum (max_size o snd) (set vs) < max_size s" 
proof -
  from c have vsS: "insert s (set (map snd vs)) \<subseteq> S" using C_sub_S
    by (metis (mono_tags))
  hence sS: "s \<in> S" by auto
  let ?m = "max_size s" 
  show ?thesis
  proof (cases "\<exists> v \<in> set vs. inf_sort (snd v)")
    case True
    {
      fix v
      assume "v \<in> set vs" 
      with vsS have v: "snd v \<in> S" by auto
      note sorts_non_empty[OF this]
    }
    hence "\<forall> v. \<exists> t. v \<in> set vs \<longrightarrow> t : snd v in \<T>(C)" by auto
    from choice[OF this] obtain t where 
      t: "\<And> v. v \<in> set vs \<Longrightarrow> t v : snd v in \<T>(C)" by blast
    from True vsS obtain vl where vl: "vl \<in> set vs" and vlS: "snd vl \<in> S" and inf_vl: "inf_sort (snd vl)" by auto
    note nbdd = inf_sort_not_bdd[OF vlS, THEN iffD2, OF inf_vl]
    from not_bdd_above_natD[OF nbdd, of ?m] t[OF vl]
    obtain tl where 
      tl: "tl : snd vl in \<T>(C)" and large: "?m \<le> size tl" by fastforce
    let ?t = "Fun c (map (\<lambda> v. if v = vl then tl else t v) vs)" 
    have "?t : s in \<T>(C)" 
      by (intro Fun_hastypeI[OF c] list_all2_map_map, insert tl t, auto)
    from max_size_max[OF sS inf this] 
    have False using large split_list[OF vl] by auto
    thus ?thesis ..
  next
    case False
    {
      fix v
      assume v: "v \<in> set vs" 
      with False have inf: "\<not> inf_sort (snd v)" by auto
      from vsS v have "snd v \<in> S" by auto
      from max_size_term_of_sort[OF this inf]
      have "\<exists> t. t : snd v in \<T>(C) \<and> size t = max_size (snd v)" by auto
    }
    hence "\<forall> v. \<exists> t. v \<in> set vs \<longrightarrow> t : snd v in \<T>(C) \<and> size t = max_size (snd v)" by auto
    from choice[OF this] obtain t where 
      t: "v \<in> set vs \<Longrightarrow> t v : snd v in \<T>(C) \<and> size (t v) = max_size (snd v)" for v by blast
    let ?t = "Fun c (map t vs)" 
    have "?t : s in \<T>(C)" 
      by (intro Fun_hastypeI[OF c] list_all2_map_map, insert t, auto)
    from max_size_max[OF sS inf this]
    have "size ?t \<le> max_size s" . (* the important step *)

    have "sum (max_size \<circ> snd) (set vs) = sum (size o t) (set vs)" 
      by (rule sum.cong[OF refl], unfold o_def, insert t, auto)
    also have "\<dots> \<le> sum_list (map (size o t) vs)" 
      by (rule sum_le_sum_list_nat)
    also have "\<dots> \<le> size_list (size o t) vs" by (induct vs, auto)
    also have "\<dots> < size ?t" by simp
    also have "\<dots> \<le> max_size s" by fact
    finally show ?thesis .
  qed
qed

lemma add_mset_rel_pat: assumes sub: "mp \<noteq> {#}" 
  shows "add_mset mp p \<succ> p" 
proof -
  from sub obtain t l mp' where mp: "mp = add_mset (t,l) mp'" by (cases mp, auto)
  hence lt: "meas_tsymbols p < meas_tsymbols (add_mset mp p)" unfolding meas_def num_tsyms_mp_def by auto
  from lt meas_sub[of p "add_mset mp p"]
  show ?thesis unfolding rel_pat_def by auto
qed

lemma add_mset_measure_pat_poly: assumes sub: "mp \<noteq> {#}" 
  shows "measure_pat_poly c (add_mset mp p) > measure_pat_poly c p" 
proof -
  from sub obtain t l mp' where mp: "mp = add_mset (t,l) mp'" by (cases mp, auto)
  hence lt: "meas_tsymbols p < meas_tsymbols (add_mset mp p)" unfolding meas_def num_tsyms_mp_def by auto
  show ?thesis 
    by (rule measure_pat_poly_num_syms[OF _ _ lt], auto simp: meas_def)
qed

lemma meas_dupl_inst: fixes p :: "('f,'v,'s) pat_problem_mset" 
  assumes "\<tau> \<in> \<tau>s n x" 
    and disj: "tvars_disj_pp {n..<n + m} (pat_mset p)" 
  shows "meas_dupl (subst_pat_problem_mset \<tau> p) \<le> meas_dupl p" 
proof -
  let ?tau_mset = "subst_pat_problem_mset \<tau> :: ('f,'v,'s) pat_problem_mset \<Rightarrow> _"
  let ?tau = "subst_match_problem_mset \<tau> :: ('f,'v,'s) match_problem_mset \<Rightarrow> _"
  from assms[unfolded \<tau>s_def] obtain f ss  
    where f: "f : ss \<rightarrow> snd x in C" and \<tau>: "\<tau> = \<tau>c n x (f,ss)" by auto
  define vs where "vs = (zip [n..<n + length ss] ss)" 
  define s where "s = (Fun f (map Var vs))" 
  have tau: "\<tau> = subst x s" unfolding \<tau> \<tau>c_def s_def vs_def by auto
  have "meas_dupl (?tau_mset p) = sum_ms (max_dupl_mp o ?tau) p" 
    unfolding meas_dupl_def subst_pat_problem_mset_def o_def image_mset.compositionality ..
  also have "\<dots> \<le> sum_ms max_dupl_mp p" unfolding o_def
  proof (rule sum_mset_mono)
    fix mp
    assume mp: "mp \<in># p" 
    show "max_dupl_mp (?tau mp) \<le> max_dupl_mp mp" 
    proof (cases "x \<in> tvars_match (mp_mset mp)")
      case False
      have "(?tau mp) = image_mset id mp" unfolding subst_match_problem_mset_def subst_left_def
      proof (rule image_mset_cong, clarsimp, goal_cases)
        case (1 t l)
        with False have "x \<notin> vars t" unfolding tvars_match_def by force
        thus "t \<cdot> \<tau> = t" unfolding tau by simp
      qed
      thus ?thesis by simp
    next
      case x: True
      show ?thesis unfolding max_dupl_mp_def
      proof (rule Max_le_MaxI, force intro: tvars_match_fin, force, force intro: tvars_match_fin, goal_cases)
        case (1 d)
        show ?case
        proof (cases "d = 0")
          case True
          thus ?thesis by blast
        next
          case False
          with 1 obtain y where y: "y \<in> tvars_match (mp_mset (?tau mp))" 
            and d: "d = (\<Sum>t\<in>#image_mset fst (?tau mp). count (syms_term t) (Inl y))" 
            by auto
          have syms_s: "syms_term s = add_mset (Inr f) (mset (map Inl vs))" unfolding s_def
            by (simp, induct vs, auto)
          have "tvars_match (mp_mset (?tau mp)) = \<Union> (vars ` \<tau> ` tvars_match (mp_mset mp))" 
            unfolding tvars_match_def subst_match_problem_mset_def subst_left_def
            by (force simp: vars_term_subst)
          also have "\<dots> = vars (\<tau> x) \<union> \<Union> (vars ` \<tau> ` (tvars_match (mp_mset mp) - {x}))"
            using x by auto
          also have "vars (\<tau> x) = set vs" unfolding tau s_def by auto
          also have "\<Union> (vars ` \<tau> ` (tvars_match (mp_mset mp) - {x})) = tvars_match (mp_mset mp) - {x}" 
            unfolding tau by (auto simp: subst_def)
          finally have "tvars_match (mp_mset (?tau mp)) = set vs \<union> (tvars_match (mp_mset mp) - {x})" .
          with y have y: "y \<in> set vs \<or> y \<in> tvars_match (mp_mset mp) - {x}" by auto
          define repl :: "('f, nat \<times> 's) Term.term \<Rightarrow> (nat \<times> 's + 'f) multiset"  
            where "repl t = replicate_mset (count (syms_term t) (Inl x)) (Inl x)" for t
          define terms where "terms = image_mset fst mp" 
          let ?add = "(\<Sum>t\<in>#terms. count (repl t) (Inl y))" 
          let ?symsy = "(\<Sum>t\<in>#terms. count (syms_term t) (Inl y))" 
          let ?symsxy = "(\<Sum>t\<in>#terms. count (syms_term t) (Inl x) * count (syms_term s) (Inl y))" 
          let ?symsx = "(\<Sum>t\<in>#terms. count (syms_term t) (Inl x))" 
          have "d = (\<Sum>t\<in>#terms. count (syms_term (t \<cdot> \<tau>)) (Inl y))" 
            unfolding d terms_def subst_match_problem_mset_def subst_left_def
            by (induct mp, auto)
          also have "\<dots> \<le> \<dots> + ?add" by simp
          also have "\<dots> = 
           (\<Sum>t\<in>#terms. count (syms_term (t \<cdot> \<tau>) + repl t) (Inl y))" 
            unfolding sum_mset.distrib[symmetric]
            by (rule arg_cong[of _ _ sum_mset], rule image_mset_cong, simp)
          also have "\<dots> = ?symsy + ?symsxy" 
            unfolding repl_def tau syms_term_subst sum_mset.distrib[symmetric] by simp
          finally have d: "d \<le> ?symsy + ?symsxy" .
          show ?thesis
          proof (cases "y \<in> set vs")
            case False
            hence "?symsxy = 0" unfolding syms_s by auto
            with d have d: "d \<le> ?symsy" by auto
            from y[simplified] False 
            have "y \<in> tvars_match (mp_mset mp)" by auto
            with d show ?thesis unfolding terms_def by auto
          next
            case True
            have dist: "distinct vs" unfolding vs_def
              by (metis distinct_enumerate enumerate_eq_zip)
            from split_list[OF True] obtain vs1 vs2 where vs: "vs = vs1 @ y # vs2" by auto
            with dist have nmem: "y \<notin> set vs1" "y \<notin> set vs2" by auto
            have "count (syms_term s) (Inl y) = 1" unfolding syms_s vs using nmem
              by (auto simp: count_eq_zero_iff) 
            with d have d: "d \<le> ?symsy + ?symsx" by auto
            from True have ynm: "fst y \<in> {n..<n + m}" unfolding vs_def using m[OF f] 
              by (auto simp: set_zip)
            from mp have "mp_mset mp \<in> pat_mset p" by auto
            from assms(2)[unfolded tvars_disj_pp_def, rule_format, OF this] ynm
            have "y \<notin> tvars_match (mp_mset mp)" unfolding tvars_match_def by force
            hence "y \<notin> (\<Union> (vars ` set_mset terms))" unfolding tvars_match_def terms_def
              by auto
            hence "?symsy = 0" 
              by (auto simp: count_eq_zero_iff vars_term_syms_term)
            with d have "d \<le> ?symsx" by auto
            with x show ?thesis unfolding terms_def by auto
          qed
        qed
      qed
    qed
  qed  
  finally show "meas_dupl p \<ge> meas_dupl (?tau_mset p)" unfolding meas_dupl_def by auto
qed

lemma meas_tsymbols_inst: fixes p :: "('f,'v,'s) pat_problem_mset" 
  assumes "\<tau> \<in> \<tau>s n x" 
  shows "meas_tsymbols (subst_pat_problem_mset \<tau> p) \<le> meas_tsymbols p + meas_dupl p * m" 
proof -
  let ?tau_mset = "subst_pat_problem_mset \<tau> :: ('f,'v,'s) pat_problem_mset \<Rightarrow> _"
  let ?tau = "subst_match_problem_mset \<tau> :: ('f,'v,'s) match_problem_mset \<Rightarrow> _"
  have "meas_tsymbols (?tau_mset p) = sum_ms (num_tsyms_mp o ?tau) p" 
    unfolding meas_tsymbols_def subst_pat_problem_mset_def o_def image_mset.compositionality ..
  also have "\<dots> \<le> sum_ms (\<lambda> mp. num_tsyms_mp mp + max_dupl_mp mp * m) p" unfolding o_def
  proof (rule sum_mset_mono)
    fix mp
    have "num_tsyms_mp (?tau mp) = sum_ms (num_syms o (\<lambda> t. t \<cdot> \<tau>)) (image_mset fst mp)" 
      unfolding num_tsyms_mp_def o_def subst_match_problem_mset_def subst_left_def
      by (induct mp, auto)
    also have "\<dots> \<le> sum_ms (\<lambda> p. num_syms p + count (syms_term p) (Inl x) * m) (image_mset fst mp)" 
      unfolding o_def
      by (rule sum_mset_mono[OF num_syms_\<tau>s[OF assms]])
    also have "\<dots> = num_tsyms_mp mp + sum_ms (\<lambda> p. count (syms_term p) (Inl x)) (image_mset fst mp) * m" 
      unfolding num_tsyms_mp_def o_def
      by (induct mp, auto simp: algebra_simps)
    also have "\<dots> \<le> num_tsyms_mp mp + max_dupl_mp mp * m" 
    proof (intro add_left_mono mult_right_mono)
      show "(\<Sum>p\<in>#image_mset fst mp. count (syms_term p) (Inl x)) \<le> max_dupl_mp mp" 
      proof (cases "x \<in> tvars_match (mp_mset mp)")
        case True
        show ?thesis unfolding max_dupl_mp_def
          by (rule Max_ge, insert True, auto intro: tvars_match_fin)
      next
        case False
        have "(\<Sum>p\<in>#image_mset fst mp. count (syms_term p) (Inl x)) = 0"
        proof (clarsimp)
          fix t l
          assume "(t,l) \<in># mp" 
          with False have "x \<notin> vars t" unfolding tvars_match_def by auto
          thus "count (syms_term t) (Inl x) = 0"
            unfolding vars_term_syms_term
            by (simp add: count_eq_zero_iff)
        qed
        thus ?thesis by linarith
      qed
    qed auto
    finally show "num_tsyms_mp (?tau mp) \<le> num_tsyms_mp mp + max_dupl_mp mp * m" .
  qed
  also have "\<dots> = meas_tsymbols p + meas_dupl p * m" unfolding meas_tsymbols_def meas_dupl_def
    by (induct p, auto simp: algebra_simps)
  finally show "meas_tsymbols p + meas_dupl p * m \<ge> meas_tsymbols (?tau_mset p)" .
qed

lemma pp_step_le_size: assumes "p \<Rightarrow>\<^sub>m ps" and "p' \<in># ps"
  shows "size p' \<le> size p" 
  using assms by induct (auto simp: subst_pat_problem_mset_def)

lemma decrease_pp_step_mset:
  fixes p :: "('f,'v,'s) pat_problem_mset"
  assumes "p \<Rightarrow>\<^sub>m ps"
    and "p' \<in># ps"
  shows "p \<succ> p'" "improved \<Longrightarrow> measure_pat_poly c p > measure_pat_poly c p'"  
  using assms
proof (atomize(full), induct)
  case *: (pat_simp_mp mp mp' p)
  hence p': "p' = add_mset mp' p" by auto
  from rel_mp_mp_step_mset[OF *(1)] mp_step_measure_pat_poly[OF *(1)]
  show ?case unfolding p' rel_pat_def meas_def by auto
next
  case *: (pat_remove_mp mp p)
  hence p': "p' = p" by auto
  from *(1) have mp: "mp \<noteq> {#}" by (cases, auto)
  show ?case unfolding p' 
    by (intro conjI impI, rule add_mset_rel_pat, rule mp, rule add_mset_measure_pat_poly, rule mp)
next
  case *: (pat_instantiate n mp p x l s y t)
  let ?c = c
  from *(2) have "\<exists> s t. (s,t) \<in># mp \<and>  (s = Var x \<and> is_Fun t
          \<or> (\<not> improved \<and> x \<in> vars s \<and> \<not> inf_sort (snd x)))"
  proof
    assume *: "\<not> improved \<and> (s, Var y) \<in># mp \<and> (t, Var y) \<in># mp \<and> Conflict_Var s t x \<and> \<not> inf_sort (snd x)" 
    hence "Conflict_Var s t x" and "\<not> inf_sort (snd x)" by auto
    from conflicts(4)[OF this(1)] this(2) *
    show ?thesis by auto
  qed auto
  then obtain s t where st: "(s,t) \<in># mp" and choice: "s = Var x \<and> is_Fun t \<or> \<not> improved \<and> x \<in> vars s \<and> \<not> inf_sort (snd x)" 
    by auto
  let ?p = "add_mset mp p" 
  let ?s = "snd x" 
  from *(3) \<tau>s_list
  obtain \<tau> where \<tau>s: "\<tau> \<in> \<tau>s n x" and p': "p' = subst_pat_problem_mset \<tau> ?p" by auto

  let ?tau_mset = "subst_pat_problem_mset \<tau> :: ('f,'v,'s) pat_problem_mset \<Rightarrow> _"
  let ?tau = "subst_match_problem_mset \<tau> :: ('f,'v,'s) match_problem_mset \<Rightarrow> _"
  from \<tau>s[unfolded \<tau>s_def \<tau>c_def]
  obtain c sorts where c: "c : sorts \<rightarrow> ?s in C" and tau: "\<tau> = subst x (Fun c (map Var (zip [n..<n + length sorts] sorts)))" 
    by (clarsimp simp add: \<tau>s_def \<tau>c_def)
  with C_sub_S have sS: "?s \<in> S" and sorts: "set sorts \<subseteq> S" by auto
  define vs where "vs = zip [n..<n + length sorts] sorts" 
  have \<tau>: "\<tau> = subst x (Fun c (map Var vs))" unfolding tau vs_def by auto
  have "snd ` vars (\<tau> y) \<subseteq> insert (snd y) S" for y
    using sorts unfolding tau by (auto simp: subst_def set_zip set_conv_nth)
  hence vars_sort: "(a,b) \<in> vars (\<tau> y) \<Longrightarrow> b \<in> insert (snd y) S" for a b y by fastforce 
  from st obtain mp' where mp: "mp = add_mset (s,t) mp'" by (rule mset_add)
  from choice have "?p \<succ> ?tau_mset ?p \<and> (improved \<longrightarrow> measure_pat_poly ?c ?p > measure_pat_poly ?c (?tau_mset ?p))" 
  proof
    assume "s = Var x \<and> is_Fun t" 
    then obtain f ts where s: "s = Var x" and t: "t = Fun f ts" by (cases t, auto)
    have "meas_diff (?tau_mset ?p) = 
      meas_diff (?tau_mset (add_mset mp' p)) + fun_diff t (s \<cdot> \<tau>)" 
      unfolding meas_def subst_defs subst_left_def mp by simp
    also have "\<dots> \<le> meas_diff (add_mset mp' p) + fun_diff t (\<tau> x)" using meas_diff_subst_le[of \<tau>] s by auto
    also have "\<dots> < meas_diff (add_mset mp' p) + fun_diff t s"
    proof (rule add_strict_left_mono)
      have "fun_diff t (\<tau> x) < num_funs t" 
        unfolding tau subst_simps fun_diff.simps
        by (rule fun_diff_num_funs_lt[OF refl], auto simp: t)
      thus "fun_diff t (\<tau> x) < fun_diff t s" by (auto simp: s t)
    qed
    also have "\<dots> = meas_diff ?p" unfolding mp meas_def by auto
    finally have md: "meas_diff (?tau_mset ?p) < meas_diff ?p" .
    show ?thesis 
    proof (intro conjI impI)
      show "?p \<succ> ?tau_mset ?p" using md unfolding rel_pat_def by auto 
      show "measure_pat_poly ?c ?p > measure_pat_poly ?c (?tau_mset ?p)" 
      proof (rule measure_pat_poly_meas_diff[OF md])
        show "meas_dupl ?p \<ge> meas_dupl (?tau_mset ?p)" 
          by (rule meas_dupl_inst[OF \<tau>s], insert *, auto)
        show "meas_tsymbols ?p + meas_dupl ?p * m \<ge> meas_tsymbols (?tau_mset ?p)" 
          by (rule meas_tsymbols_inst[OF \<tau>s])
      qed
    qed
  next
    assume "\<not> improved \<and> x \<in> vars s \<and> \<not> inf_sort (snd x)" 
    hence x: "x \<in> vars s" and inf: "\<not> inf_sort (snd x)" and impr: "\<not> improved" by auto
    from meas_diff_subst_le[of \<tau>]  
    have fd: "meas_diff p' \<le> meas_diff ?p" unfolding p' .
    have "meas_finvars (?tau_mset ?p) = meas_finvars (?tau_mset {#mp#}) + meas_finvars (?tau_mset p)" 
      unfolding subst_defs meas_def by auto
    also have "\<dots> < meas_finvars {#mp#} + meas_finvars p"
    proof (rule add_less_le_mono)
      have vars_\<tau>_var: "vars (\<tau> y) = (if x = y then set vs else {y})" for y unfolding \<tau> subst_def by auto
      have vars_\<tau>: "vars (t \<cdot> \<tau>) = vars t - {x} \<union> (if x \<in> vars t then set vs else {})" for t
        unfolding vars_term_subst image_comp o_def vars_\<tau>_var by auto
      have tvars_match_subst: "tvars_match (mp_mset (?tau mp)) = 
          tvars_match (mp_mset mp) - {x} \<union> (if x \<in> tvars_match (mp_mset mp) then set vs else {})" for mp
        unfolding subst_defs subst_left_def tvars_match_def
        by (auto simp:vars_\<tau> split: if_splits prod.split)
      have id1: "meas_finvars (?tau_mset {#mp#}) = (\<Sum>x\<in> tvars_match (mp_mset (?tau mp)). max_size (snd x))"  for mp
        unfolding meas_def subst_defs by auto
      have id2: "meas_finvars {#mp#} = (\<Sum>x\<in>tvars_match (mp_mset mp). max_size (snd x))"
        for mp :: "('f,'v,'s) match_problem_mset"
        unfolding meas_def subst_defs by simp
      have eq: "x \<notin> tvars_match (mp_mset mp) \<Longrightarrow> meas_finvars (?tau_mset {# mp #}) = meas_finvars {#mp#}" for mp
        unfolding id1 id2 by (rule sum.cong[OF _ refl], auto simp: tvars_match_subst)
      {
        fix mp :: "('f,'v,'s) match_problem_mset"
          (* if x occurs in the matching problem, then we get a strict decrease *)
        assume xmp: "x \<in> tvars_match (mp_mset mp)" 
        let ?mp = "(mp_mset mp)" 
        have fin: "finite (tvars_match ?mp)" by (rule tvars_match_fin)
        define Mp where "Mp = tvars_match ?mp - {x}" 
        from xmp have 1: "tvars_match (mp_mset (?tau mp)) = set vs \<union> Mp" 
          unfolding tvars_match_subst Mp_def by auto
        from xmp have 2: "tvars_match ?mp = insert x Mp" and xMp: "x \<notin> Mp" unfolding Mp_def by auto
        from fin have fin: "finite Mp" unfolding Mp_def by auto
        have "meas_finvars (?tau_mset {# mp #}) = sum (max_size \<circ> snd) (set vs \<union> Mp)" (is "_ = sum ?size _")
          unfolding id1 id2 using 1 by auto
        also have "\<dots> \<le> sum ?size (set vs) + sum ?size Mp" by (rule sum_union_le_nat)
        also have "\<dots> < ?size x + sum ?size Mp"
        proof -
          have sS: "?s \<in> S" by fact
          have sorts: "sorts = map snd vs" unfolding vs_def by (intro nth_equalityI, auto)
          have "sum ?size (set vs) < ?size x" 
            using finite_sort_size[OF c[unfolded sorts] inf] by auto
          thus ?thesis by auto
        qed
        also have "\<dots> = meas_finvars {#mp#}" unfolding id2 2 using fin xMp by auto
        finally have "meas_finvars (?tau_mset {# mp #}) < meas_finvars {#mp#}" .
      } note less = this
      have le: "meas_finvars (?tau_mset {# mp #}) \<le> meas_finvars {#mp#}" for mp 
        using eq[of mp] less[of mp] by linarith

      show "meas_finvars (?tau_mset {#mp#}) < meas_finvars {#mp#}" using x
        by (intro less, unfold mp, force simp: tvars_match_def)

      show "meas_finvars (?tau_mset p) \<le> meas_finvars p" 
        unfolding subst_pat_problem_mset_def meas_finvars_def sum_ms_image o_def
        apply (rule sum_mset_mono)
        subgoal for mp using le[of mp] unfolding meas_finvars_def o_def subst_defs by auto
        done
    qed
    also have "\<dots> = meas_finvars ?p" unfolding p' meas_def by simp
    finally show ?thesis using fd impr unfolding rel_pat_def p' by auto
  qed
  thus ?case unfolding p' .
next
  case *: (pat_remove_pp p)
  thus ?case by auto
next
  case *: (pat_inf_var_conflict pp pp')
  hence p': "p' = pp'" by auto
  have "p' \<subseteq># pp + pp'" unfolding p' by auto
  note mono = meas_sub[OF this]
  from *(2) obtain mp pp2 where pp: "pp = add_mset mp pp2" by (cases pp, auto)
  with *(1) have "inf_var_conflict (mp_mset mp)" by auto
  hence "mp \<noteq> {#}" unfolding inf_var_conflict_def by auto
  hence "meas_tsymbols p' < meas_tsymbols (pp + pp')" unfolding p' pp using num_syms_pos 
    by (cases mp, auto simp: meas_tsymbols_def num_tsyms_mp_def)
  thus ?case using mono by (auto simp: rel_pat_def intro: measure_pat_poly_num_syms)
qed

text \<open>finally: the transformation is terminating w.r.t. @{term "(\<succ>mul)"}\<close>
lemma rel_P_trans: 
  assumes "P \<Rrightarrow>\<^sub>m P'" 
  shows "P \<succ>mul P'" 
  using assms
proof induct
  case *: (P_failure P)
  from * have "P \<noteq> {#}" by auto
  then obtain p' P' where P: "P = add_mset p' P'" by (cases P, auto)
  show ?case unfolding P unfolding rel_pats_def 
    by (simp add: subset_implies_mult)
next
  case *: (P_simp_pp p ps P)
  from set_mp[OF rel_pat_sub_rel_pat'] decrease_pp_step_mset[OF *]
  show ?case unfolding rel_pats_def by (metis add_many_mult)
qed

text \<open>termination of the multiset based implementation, poly-complexity in improved case\<close>

lemma nd_step_le_size: assumes "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d" 
  shows "size q \<le> size p" 
  using assms by induct (auto simp: pp_step_le_size)

lemma nd_steps_le_size: assumes "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" 
  shows "size q \<le> size p" 
  using assms by (induct, auto dest: nd_step_le_size)

lemma nd_step_decrease: assumes "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d" 
  shows "p \<succ> q" 
    "improved \<Longrightarrow> measure_pat_poly c p > measure_pat_poly c q" 
proof -
  from assms
  obtain P where "p \<Rightarrow>\<^sub>m P" and "q \<in># P" 
    by cases auto
  from decrease_pp_step_mset[OF this]
  show "p \<succ> q" "improved \<Longrightarrow> measure_pat_poly c p > measure_pat_poly c q" by auto
qed

lemma nd_steps_bound: assumes improved
  and "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d^^n" 
shows "n \<le> measure_pat_poly c p" (is ?A)
  "measure_pat_poly c q + n \<le> measure_pat_poly c p" (is ?B)
proof -
  from steps_bound[of _ "measure_pat_poly c", OF nd_step_decrease(2)[OF _ assms(1)] assms(2)]
  have "measure_pat_poly c q + n \<le> measure_pat_poly c p" by auto
  thus ?A ?B by auto
qed

theorem SN_nd_pstep: "SN \<Rightarrow>\<^sub>n\<^sub>d" 
proof (rule SN_subset[of "{(p,q). p \<succ> q}"], rule wf_imp_SN)
  show "wf ({(p, q). p \<succ> q}\<inverse>)" using wf_rel_pat 
    by (simp add: converse_unfold)
qed (insert nd_step_decrease, auto)


theorem SN_P_step: "SN \<Rrightarrow>" 
proof -
  have sub: "\<Rrightarrow> \<subseteq> \<prec>mul^-1"
    using rel_P_trans unfolding P_step_def by auto
  show ?thesis
    apply (rule SN_subset[OF _ sub])
    apply (rule wf_imp_SN)
    using wf_rel_pats by simp
qed

subsection \<open>Partial Correctness via Refinement\<close>

text \<open>Obtain partial correctness via a simulation property, that the multiset-based 
  implementation is a refinement of the set-based implementation.\<close>

lemma mp_step_cong: "mp1 \<rightarrow>\<^sub>s mp2 \<Longrightarrow> mp1 = mp1' \<Longrightarrow> mp2 = mp2' \<Longrightarrow> mp1' \<rightarrow>\<^sub>s mp2'" by auto

lemma mp_step_mset_mp_trans: "mp \<rightarrow>\<^sub>m mp' \<Longrightarrow> mp_mset mp \<rightarrow>\<^sub>s mp_mset mp'" 
proof (induct mp mp' rule: mp_step_mset.induct)
  case *: (match_decompose f ts g ls mp)
  show ?case by (rule mp_step_cong[OF mp_decompose], insert *, auto)
next
  case *: (match_match x mp t)
  show ?case by (rule mp_step_cong[OF mp_match], insert *, auto)
next
  case (match_duplicate pair mp)
  show ?case by (rule mp_step_cong[OF mp_identity], auto)
next
  case *: (match_decompose' mp y f n mp' ys) 
  show ?case by (rule mp_step_cong[OF mp_decompose'[OF *(1,2) *(3)[unfolded set_mset_union] *(4,6)]], auto)
qed

lemma mp_fail_cong: "mp_fail mp \<Longrightarrow> mp = mp' \<Longrightarrow> mp_fail mp'" by auto

lemma match_fail_mp_fail: "match_fail mp \<Longrightarrow> mp_fail (mp_mset mp)" 
proof (induct mp rule: match_fail.induct)
  case *: (match_clash f ts g ls mp)
  show ?case by (rule mp_fail_cong[OF mp_clash], insert *, auto)
next
  case *: (match_clash' s t x mp)
  show ?case by (rule mp_fail_cong[OF mp_clash'], insert *, auto)
next
  case *: (match_clash_sort s t x mp)
  show ?case by (rule mp_fail_cong[OF mp_clash_sort], insert *, auto)
qed

lemma pp_step_set_cong: "P \<Rightarrow>\<^sub>s Q \<Longrightarrow> P = P' \<Longrightarrow> Q = Q' \<Longrightarrow> P' \<Rightarrow>\<^sub>s Q'" by auto


lemma p_step_mset_imp_set: assumes "p \<Rightarrow>\<^sub>m Q"
  shows "pat_mset p \<Rightarrow>\<^sub>s pats_mset Q" 
  using assms
proof -
  note conv = o_def image_mset_union image_empty image_mset_add_mset Un_empty_left
    set_mset_add_mset_insert set_mset_union image_Un image_insert set_mset_empty
    set_mset_mset set_image_mset
    set_map image_comp insert_is_Un[symmetric]
  show ?thesis using assms(1) unfolding conv
  proof induction
    case (pat_remove_pp p)
    show ?case unfolding conv using pp_success by auto
  next
    case *: (pat_simp_mp mp mp' p)
    from pp_simp_mp[OF mp_step_mset_mp_trans[OF *]]
    show ?case by auto
  next
    case *: (pat_remove_mp mp p)
    from pp_remove_mp[OF match_fail_mp_fail[OF *]]
    show ?case by simp
  next
    case *: (pat_instantiate n mp p x l s y t)
    from *(2) have "x \<in> tvars_match (mp_mset mp)" 
      using conflicts(4)[of s t x] unfolding tvars_match_def
      by (auto intro!:term.set_intros(3))
    hence x: "x \<in> tvars_pat (pat_mset (add_mset mp p))" unfolding tvars_pat_def 
      using *(2) by auto
    show ?case unfolding conv \<tau>s_list
      apply (rule pp_step_set_cong[OF pp_instantiate[OF *(1) x]])
      by (unfold conv subst_defs set_map image_comp, auto)
  next
    case *: (pat_inf_var_conflict pp pp')
    from pp_inf_var_conflict[OF *(1), of "pat_mset pp'"] 
    have "pat_mset (pp + pp') \<Rightarrow>\<^sub>s {pat_mset pp'}" 
      using * by (auto simp: tvars_pat_def image_Un)
    thus ?case by auto
  qed
qed

lemma pp_step_mset_pcorrect: "p \<Rightarrow>\<^sub>m P' \<Longrightarrow> wf_pat (pat_mset p) \<Longrightarrow> 
  pat_complete C (pat_mset p) = pats_complete C (pats_mset P')" 
  by (rule pp_step_pcorrect[OF p_step_mset_imp_set])

lemma P_step_mset_imp_set: assumes "P \<Rrightarrow>\<^sub>m Q"
  shows "pats_mset P \<Rrightarrow>\<^sub>s pats_mset Q" 
  using assms
proof (induction)
  case *: (P_failure P)
  from *(1) show ?case 
    by (induct, auto intro: P_fail)
next
  case (P_simp_pp pp pp' P)
  from P_simp[OF p_step_mset_imp_set[OF this]]
  show ?case by (simp add: image_Un)
qed

lemma nd_step_mset_pcorrect: assumes "p \<notin> NF \<Rightarrow>\<^sub>n\<^sub>d" "wf_pat (pat_mset p)"
  shows "pat_complete C (pat_mset p) \<longleftrightarrow> (\<forall> q. (p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d \<longrightarrow> pat_complete C (pat_mset q))" 
proof -
  from assms(1) obtain q where "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d" by auto
  then obtain Q where "p \<Rightarrow>\<^sub>m Q" by cases
  from pp_step_mset_pcorrect[OF this assms(2)] pp_nd_step_mset.intros[OF this]
  have "(\<forall> q. (p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d \<longrightarrow> pat_complete C (pat_mset q)) \<Longrightarrow> pat_complete C (pat_mset p)" by simp
  moreover {
    fix q
    assume "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d" 
    then obtain Q where "p \<Rightarrow>\<^sub>m Q" and "q \<in># Q" by cases
    from pp_step_mset_pcorrect[OF this(1) assms(2)] pp_nd_step_mset.intros[OF this] this(2)
    have "pat_complete C (pat_mset p) \<Longrightarrow> pat_complete C (pat_mset q)" by auto
  }
  ultimately show ?thesis by blast
qed


lemma P_step_pp_trans: assumes "(P,Q) \<in> \<Rrightarrow>"
  shows "pats_mset P \<Rrightarrow>\<^sub>s pats_mset Q" 
  by (rule P_step_mset_imp_set, insert assms, unfold P_step_def, auto)

theorem P_step_pcorrect: assumes wf: "wf_pats (pats_mset P)" and step: "(P,Q) \<in> \<Rrightarrow>"
  shows "wf_pats (pats_mset Q) \<and> (pats_complete C (pats_mset P) = pats_complete C (pats_mset Q))" 
proof -
  note step = P_step_pp_trans[OF step]
  from P_step_set_pcorrect[OF step] P_step_set_wf[OF step] wf
  show ?thesis by auto
qed

corollary P_steps_pcorrect: assumes wf: "wf_pats (pats_mset P)" 
  and step: "(P,Q) \<in> \<Rrightarrow>\<^sup>*" 
shows "wf_pats (pats_mset Q) \<and> (pats_complete C (pats_mset P) \<longleftrightarrow> pats_complete C (pats_mset Q))"
  using step by induct (insert wf P_step_pcorrect, auto) 

lemma nd_step_to_P_step: assumes "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d"
  shows "\<exists> Q. add_mset p P \<Rrightarrow>\<^sub>m add_mset q Q" 
  using assms
proof cases
  case (1 Q)
  then show ?thesis using P_simp_pp[of p Q P] 
    by (metis mset_add union_iff)
qed

lemma nd_steps_to_P_steps: assumes "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*"
  shows "\<exists> Q. (\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* (add_mset p P) (add_mset q Q)" 
  using assms
proof (induct arbitrary: P)
  case *: (step y z)
  from nd_step_to_P_step[OF *(2)] *(3) show ?case
    by (meson r_into_rtranclp rtranclp_trans)
qed auto

lemma P_step_to_nd_step: assumes "P \<Rrightarrow>\<^sub>m Q" 
  and "q \<in># Q" shows "\<exists> p \<in># P. (p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>=" 
  using assms(1)
proof cases
  case *: (P_simp_pp pp P' P)
  with assms have "q \<in># P' \<or> q \<in># P" by auto
  thus ?thesis
  proof
    assume "q \<in># P" 
    thus ?thesis using * by auto
  next
    assume "q \<in># P'" 
    with * have "(pp, q) \<in> \<Rightarrow>\<^sub>n\<^sub>d" by (intro pp_nd_step_mset.intros)
    with * show ?thesis by auto
  qed
qed (insert assms, auto)

lemma P_steps_to_nd_steps: assumes "(\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* P Q" 
  and "q \<in># Q" shows "\<exists> p \<in># P. (p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*"
  using assms
proof (induct arbitrary: q)
  case *: (step Q R r)
  from P_step_to_nd_step[OF *(2,4)]
  obtain q where "q \<in># Q" and "(q,r) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>=" by auto
  from *(3)[OF this(1)] this(2) show ?case
    by (metis (no_types, lifting) UnE pair_in_Id_conv rtrancl.rtrancl_into_rtrancl)
qed auto

lemma nd_steps_fail_iff_Psteps_fail: "(p,{#}) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>* \<longleftrightarrow> (\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* {#p#} bottom_mset" 
proof 
  assume "(p,{#}) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" 
  from nd_steps_to_P_steps[OF this] obtain P
    where steps: "(\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* {#p#} (add_mset {#} P)" by auto
  from P_failure[of P] have "(\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* (add_mset {#} P) bottom_mset" 
    by (cases "add_mset {#} P = bottom_mset", auto)
  with steps show "(\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* {#p#} bottom_mset" by simp
next
  assume "(\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* {#p#} bottom_mset" 
  from P_steps_to_nd_steps[OF this, of "{#}"] 
  show "(p,{#}) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" by auto
qed

text \<open>Gather all results for the multiset-based implementation: 
    decision procedure on well-formed inputs (termination was proven before)\<close>

theorem P_step:
  assumes non_improved: "\<not> improved" 
    and wf: "wf_pats (pats_mset P)" and NF: "(P,Q) \<in> \<Rrightarrow>\<^sup>!"
  shows "Q = {#} \<and> pats_complete C (pats_mset P) \<comment> \<open>either the result is {} and input P is complete\<close>
  \<or> Q = bottom_mset \<and> \<not> pats_complete C (pats_mset P) \<comment> \<open>or the result = bot and P is not complete\<close>" 
proof -
  from NF have steps: "(P,Q) \<in> \<Rrightarrow>\<^sup>*" and NF: "Q \<in> NF P_step" by auto
  from P_steps_pcorrect[OF wf steps]
  have wf: "wf_pats (pats_mset Q)" and 
    sound: "pats_complete C (pats_mset P) = pats_complete C (pats_mset Q)" 
    by blast+
  from P_step_NF[OF non_improved wf NF] have "Q \<in> {{#},bottom_mset}" .
  thus ?thesis unfolding sound by auto
qed

theorem nd_pstep:
  assumes non_improved: "\<not> improved" 
    and wf: "wf_pat (pat_mset p)" 
  shows "\<not> pat_complete C (pat_mset p) \<longleftrightarrow> (p,{#}) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" 
proof -
  from wf have wf: "wf_pats (pats_mset {#p#})" by (auto simp: wf_pats_def)
  have "\<not> pat_complete C (pat_mset p) \<longleftrightarrow> ({#p#}, bottom_mset) \<in> \<Rrightarrow>\<^sup>*" 
  proof -
    {
      assume "({#p#}, {#{#}#}) \<in> \<Rrightarrow>\<^sup>*" 
      from P_steps_pcorrect[OF wf this]
      have "\<not> pat_complete C (pat_mset p)" 
        by auto
    } note bot = this
    from SN_P_step obtain Q where NF: "({#p#}, Q) \<in> \<Rrightarrow>\<^sup>!" 
      by (metis SN_def SN_on_imp_normalizability)
    from P_step[OF non_improved wf NF] 
    have res: "Q = {#} \<and> pat_complete C (pat_mset p) \<or> Q = {#{#}#} \<and> \<not> pat_complete C (pat_mset p)" by auto
    hence pcQ: "pat_complete C (pat_mset p) = (Q = {#})" by auto
    from NF have "({#p#},Q) \<in> \<Rrightarrow>\<^sup>*" by auto
    thus ?thesis unfolding pcQ using res bot by auto
  qed
  also have "\<dots> \<longleftrightarrow> (\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* ({#p#}) bottom_mset" 
    unfolding P_step_def by (meson Enum.rtranclp_rtrancl_eq)
  also have "\<dots> \<longleftrightarrow> (p,{#}) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" 
    unfolding nd_steps_fail_iff_Psteps_fail ..
  finally show ?thesis by auto
qed

theorem P_step_improved:
  fixes P :: "('f,'v,'s) pats_problem_mset"
  assumes improved 
    and inf: "infinite (UNIV :: 'v set)" 
    and wf: "wf_pats (pats_mset P)" and NF: "(P,Q) \<in> \<Rrightarrow>\<^sup>!"
  shows "pats_complete C (pats_mset P) \<longleftrightarrow> pats_complete C (pats_mset Q)" \<comment> \<open>equivalence\<close>
    "p \<in># Q \<Longrightarrow> finite_constr_form_pat C (pat_mset p)" \<comment> \<open>all remaining problems are in finite-constr-form\<close>
proof -
  from NF have steps: "(P,Q) \<in> \<Rrightarrow>\<^sup>*" and NF: "Q \<in> NF P_step" by auto
  note * = P_steps_pcorrect[OF wf steps]
  from *
  show "pats_complete C (pats_mset P) = pats_complete C (pats_mset Q)" ..
  from * have wfQ: "wf_pats (pats_mset Q)" by auto
  from P_step_NF_fvf[OF \<open>improved\<close> inf this NF]
  show "p \<in># Q \<Longrightarrow> finite_constr_form_pat C (pat_mset p)" .
qed

theorem nd_step_improved:
  fixes p :: "('f,'v,'s) pat_problem_mset"
  assumes improved 
    and inf: "infinite (UNIV :: 'v set)" 
    and wf: "wf_pat (pat_mset p)" 
  shows "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d ^^ n \<Longrightarrow> n \<le> num_syms_pat p * (num_syms_pat p * m + 2)"
    "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d ^^ n \<Longrightarrow> measure_pat_poly c q + n \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" 
    "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>! \<Longrightarrow> finite_constr_form_pat C (pat_mset q)"
    "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>* \<Longrightarrow> pat_complete C (pat_mset p) \<Longrightarrow> pat_complete C (pat_mset q)" 
    "\<not> pat_complete C (pat_mset p) \<Longrightarrow> \<exists> q. (p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>! \<and> \<not> pat_complete C (pat_mset q)" 
    "\<not> pat_complete C (pat_mset p) \<longleftrightarrow> (\<exists> q. (p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>! \<and> \<not> pat_complete C (pat_mset q))" 
proof -
  {
    fix n c
    assume "(p,q) \<in> (\<Rightarrow>\<^sub>n\<^sub>d)^^n" 
    from nd_steps_bound[OF \<open>improved\<close> this, of c] measure_pat_poly[of c p]
    have res: "measure_pat_poly c q + n \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" by auto
  } note measure = this
  from this[of n c] this[of n 0]
  show "(p, q) \<in> \<Rightarrow>\<^sub>n\<^sub>d ^^ n \<Longrightarrow> measure_pat_poly c q + n \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" 
    "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d ^^ n \<Longrightarrow> n \<le> num_syms_pat p * (num_syms_pat p * m + 2)" by auto
  from wf have wf': "wf_pats (pats_mset {#p#})" by (auto simp: wf_pats_def)
  {
    fix q
    assume "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" 
    from nd_steps_to_P_steps[OF this, of "{#}"] obtain Q where "(\<Rrightarrow>\<^sub>m)\<^sup>*\<^sup>* {#p#} (add_mset q Q)" by auto
    hence "({#p#}, add_mset q Q) \<in> \<Rrightarrow>\<^sup>*" unfolding P_step_def by (meson Enum.rtranclp_rtrancl_eq) 
    from P_steps_pcorrect[OF wf' this] have wfq: "wf_pats (pats_mset (add_mset q Q))"
      and "pats_complete C (pats_mset {#p#}) = pats_complete C (pats_mset (add_mset q Q))" by auto
    hence "pat_complete C (pat_mset p) \<Longrightarrow> pat_complete C (pat_mset q)" 
      by (auto simp: wf_pats_def)
    moreover {
      assume "q \<in> NF \<Rightarrow>\<^sub>n\<^sub>d" 
      from nd_step_NF_fvf[OF \<open>improved\<close> inf _ this] wfq 
      have "finite_constr_form_pat C (pat_mset q)" by (auto simp: wf_pats_def)
    }
    ultimately have "pat_complete C (pat_mset p) \<Longrightarrow> pat_complete C (pat_mset q)"
      "q \<in> NF \<Rightarrow>\<^sub>n\<^sub>d \<Longrightarrow> finite_constr_form_pat C (pat_mset q)" by auto
  } note result1 = this
  thus result1b: "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>! \<Longrightarrow> finite_constr_form_pat C (pat_mset q)" for q by blast
  from result1 show "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>* \<Longrightarrow> pat_complete C (pat_mset p) \<Longrightarrow> pat_complete C (pat_mset q)" by blast
  {
    assume "\<not> pat_complete C (pat_mset p)" 
    with wf
    show "\<exists>q. (p, q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>! \<and> \<not> pat_complete C (pat_mset q)" 
    proof (induct p rule: wf_induct[OF wf_measure[of "measure_pat_poly 0"]])
      case (1 p)
      show ?case
      proof (cases "p \<in> NF (\<Rightarrow>\<^sub>n\<^sub>d)")
        case True
        thus ?thesis using 1 by auto
      next
        case False
        from nd_step_mset_pcorrect[OF False 1(2)] 1(3)
        obtain q where step: "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d" and inc: "\<not> pat_complete C (pat_mset q)" by auto
        from nd_step_decrease(2)[OF this(1) \<open>improved\<close>] 
        have "(q,p) \<in> measure (measure_pat_poly 0)" by auto
        note IH = 1(1)[rule_format, OF this _ inc]
        from nd_step_to_P_step[OF step, of "{#}"] obtain Q where
          "({#p#}, add_mset q Q) \<in> \<Rrightarrow>" by (auto simp: P_step_def)
        from P_step_pcorrect[OF _ this] 1(2) have "wf_pat (pat_mset q)" by (auto simp: wf_pats_def)
        from IH[OF this] step show ?thesis by auto
      qed
    qed
  } note result2 = this
  show "\<not> pat_complete C (pat_mset p) \<longleftrightarrow> (\<exists> q. (p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>! \<and> \<not> pat_complete C (pat_mset q))" 
    (is "?L = ?R")
  proof
    assume ?L 
    from result2[OF this] obtain q where pq: "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>!" and inc: "\<not> pat_complete C (pat_mset q)" by auto
    hence "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" by auto
    with pq inc show ?R by auto
  next
    assume ?R
    then obtain q where "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" and "\<not> pat_complete C (pat_mset q)" by auto
    from result1[OF this(1)] this(2) show ?L by auto
  qed
qed
end
end