section \<open>A Multiset-Based Inference System to Decide Pattern Completeness\<close>

theory Pattern_Completeness_Multiset
  imports 
    Pattern_Completeness_Set
    LP_Duality.Minimum_Maximum
    Polynomial_Factorization.Missing_List (* list_all2_map_map *)
    First_Order_Terms.Term_Pair_Multiset
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

inductive mp_step_mset :: "('f,'v,'s)match_problem_mset \<Rightarrow> ('f,'v,'s)match_problem_mset \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>m" 50)where
  match_decompose: "(f,length ts) = (g,length ls)
    \<Longrightarrow> add_mset (Fun f ts, Fun g ls) mp \<rightarrow>\<^sub>m mp + mset (zip ts ls)" 
| match_match: "x \<notin> \<Union> (vars ` snd ` set_mset mp)
    \<Longrightarrow> add_mset (t, Var x) mp \<rightarrow>\<^sub>m mp" 
| match_duplicate: "add_mset pair (add_mset pair mp) \<rightarrow>\<^sub>m add_mset pair mp"  


inductive match_fail :: "('f,'v,'s)match_problem_mset \<Rightarrow> bool" where
  match_clash: "(f,length ts) \<noteq> (g,length ls)  
    \<Longrightarrow> match_fail (add_mset (Fun f ts, Fun g ls) mp)" 
| match_clash': "Conflict_Clash s t \<Longrightarrow> match_fail (add_mset (s, Var x) (add_mset (t, Var x) mp))"       

inductive pp_step_mset :: "('f,'v,'s)pat_problem_mset \<Rightarrow> ('f,'v,'s)pats_problem_mset \<Rightarrow> bool"
  (infix "\<Rightarrow>\<^sub>m" 50) where
  pat_remove_pp: "add_mset {#} pp \<Rightarrow>\<^sub>m {#}" 
| pat_simp_mp: "mp_step_mset mp mp' \<Longrightarrow> add_mset mp pp \<Rightarrow>\<^sub>m {# (add_mset mp' pp) #}" 
| pat_remove_mp: "match_fail mp \<Longrightarrow> add_mset mp pp \<Rightarrow>\<^sub>m {# pp #}"
| pat_instantiate: "tvars_disj_pp {n ..< n+m} (pat_mset (add_mset mp pp)) \<Longrightarrow>
   (Var x, l) \<in> mp_mset mp \<and> is_Fun l \<or>
   (s,Var y) \<in> mp_mset mp \<and> (t,Var y) \<in> mp_mset mp \<and> Conflict_Var s t x \<and> \<not> inf_sort (snd x) \<Longrightarrow>
  add_mset mp pp \<Rightarrow>\<^sub>m mset (map (\<lambda> \<tau>. subst_pat_problem_mset \<tau> (add_mset mp pp)) (\<tau>s_list n x))"

inductive pat_fail :: "('f,'v,'s)pat_problem_mset \<Rightarrow> bool" where
  pat_failure': "Ball (pat_mset pp) inf_var_conflict \<Longrightarrow> pat_fail pp" 
| pat_empty: "pat_fail {#}" 

inductive P_step_mset :: "('f,'v,'s)pats_problem_mset \<Rightarrow> ('f,'v,'s)pats_problem_mset \<Rightarrow> bool"
  (infix "\<Rrightarrow>\<^sub>m" 50)where
  P_failure: "pat_fail pp \<Longrightarrow> add_mset pp P \<noteq> bottom_mset \<Longrightarrow> add_mset pp P \<Rrightarrow>\<^sub>m bottom_mset" 
| P_simp_pp: "pp \<Rightarrow>\<^sub>m pp' \<Longrightarrow> add_mset pp P \<Rrightarrow>\<^sub>m pp' + P"

text \<open>The relation (encoded as predicate) is finally wrapped in a set\<close>
definition P_step :: "(('f,'v,'s)pats_problem_mset \<times> ('f,'v,'s)pats_problem_mset)set" ("\<Rrightarrow>") where
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

lemma pat_fail_or_trans: 
  "pat_fail p \<or> (\<exists> ps. p \<Rightarrow>\<^sub>m ps)" 
proof (cases "p = {#}")
  case True
  with pat_empty show ?thesis by auto
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
          fix mp
          assume mpp: "mp \<in># p" 
          with empty_p have mp_e: "mp \<noteq> {#}" by auto
          obtain s l where sl: "(s,l) \<in># mp" using mp_e by auto
          from rhs_vars[OF mpp sl] sl obtain x where sx: "(s, Var x) \<in># mp" by (cases l, auto)
          from mpp obtain p' where p: "p = add_mset mp p'" by (rule mset_add)
          from sx obtain mp' where mp: "mp = add_mset (s, Var x) mp'" by (rule mset_add)
          from nsvar[simplified, rule_format, OF mpp[unfolded mp]] 
          obtain t l where "(t,l) \<in># mp'" and "x \<in> vars (snd (t,l))" by force
          with rhs_vars[OF mpp, of t l] have tx: "(t,Var x) \<in># mp'" unfolding mp by auto
          then obtain mp'' where mp': "mp' = add_mset (t, Var x) mp''" by (rule mset_add)
          from ndup[simplified, rule_format] mpp have "s \<noteq> t" unfolding mp mp' by auto 
          hence "\<exists> s t x mp'. mp = add_mset (s, Var x) (add_mset (t, Var x) mp') \<and> s \<noteq> t" unfolding mp mp' by auto
        } note two = this
        show ?thesis
        proof (cases "\<exists> mp s t x y. add_mset (s, Var x) (add_mset (t, Var x) mp) \<in># p \<and> Conflict_Var s t y \<and> \<not> inf_sort (snd y)") 
          case True
          then obtain mp s t x y where 
            mp: "add_mset (s, Var x) (add_mset (t, Var x) mp) \<in># p" (is "?mp \<in># _") and conf: "Conflict_Var s t y" and y: "\<not> inf_sort (snd y)" 
            by blast
          from conflicts(4)[OF conf] have "y \<in> vars s \<union> vars t" by auto
          with mp have "y \<in> tvars_mp (mp_mset ?mp)" unfolding tvars_mp_def by auto
          from mp obtain p' where p: "p = add_mset ?mp p'" by (rule mset_add)
          let ?mp = "add_mset (s, Var x) (add_mset (t, Var x) mp)" 
          from pat_instantiate[OF _ disjI2, of n ?mp p' s x t y, folded p, OF fresh]
          show ?thesis using y conf by auto
        next
          case no_non_inf: False
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
            proof (intro disjI1 pat_failure' ballI)
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
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Pattern problems just have two normal forms: 
  empty set (solvable) or bottom (not solvable)\<close>
theorem P_step_NF: 
  assumes NF: "P \<in> NF \<Rrightarrow>" 
  shows "P \<in> {{#}, bottom_mset}" 
proof (rule ccontr)
  assume nNF: "P \<notin> {{#}, bottom_mset}"
  from NF have NF: "\<not> (\<exists> Q. P \<Rrightarrow>\<^sub>m Q)" unfolding P_step_def by blast
  from nNF obtain p P' where P: "P = add_mset p P'"
    using multiset_cases by auto
  from pat_fail_or_trans
  obtain ps where "pat_fail p \<or> p \<Rightarrow>\<^sub>m ps" by auto
  with P_simp_pp[of p ps] NF
  have "pat_fail p" unfolding P by auto
  from P_failure[OF this, of P', folded P] nNF NF show False by auto
qed
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


context pattern_completeness_context_with_assms
begin

lemma \<tau>s_list: "set (\<tau>s_list n x) = \<tau>s n x" 
  unfolding \<tau>s_list_def \<tau>s_def using Cl by auto

abbreviation (input) sum_ms :: "('a \<Rightarrow> nat) \<Rightarrow> 'a multiset \<Rightarrow> nat" where
  "sum_ms f ms \<equiv> sum_mset (image_mset f ms)" 

definition meas_diff :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_diff = sum_ms (sum_ms (\<lambda> (t,l). fun_diff l t))" 

definition max_size :: "'s \<Rightarrow> nat" where
  "max_size s = (if s \<in> S \<and> \<not> inf_sort s then Maximum (size ` {t. t : s in \<T>(C,EMPTYn)}) else 0)" 

definition meas_finvars :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_finvars = sum_ms (\<lambda> mp. sum (max_size o snd) (tvars_mp (mp_mset mp)))" 

definition meas_symbols :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_symbols = sum_ms size_mset" 

definition meas_setsize :: "('f,'v,'s)pat_problem_mset \<Rightarrow> nat" where
  "meas_setsize p = sum_ms (sum_ms (\<lambda> _. 1)) p + size p" 

definition rel_pat :: "(('f,'v,'s)pat_problem_mset \<times> ('f,'v,'s)pat_problem_mset)set" ("\<prec>") where
  "(\<prec>) = inv_image ({(x, y). x < y} <*lex*> {(x, y). x < y} <*lex*> {(x, y). x < y} <*lex*> {(x, y). x < y}) 
  (\<lambda> mp. (meas_diff mp, meas_finvars mp, meas_symbols mp, meas_setsize mp))" 
 
abbreviation gt_rel_pat (infix "\<succ>" 50) where
  "pp \<succ> pp' \<equiv> (pp',pp) \<in> \<prec>" 

definition rel_pats :: "(('f,'v,'s)pats_problem_mset \<times> ('f,'v,'s)pats_problem_mset)set" ("\<prec>mul") where
  "\<prec>mul = mult (\<prec>)" 

abbreviation gt_rel_pats (infix "\<succ>mul" 50) where
  "P \<succ>mul P' \<equiv> (P',P) \<in> \<prec>mul" 

lemma wf_rel_pat: "wf \<prec>" 
  unfolding rel_pat_def
  by (intro wf_inv_image wf_lex_prod wf_less)

lemma wf_rel_pats: "wf \<prec>mul" 
  unfolding rel_pats_def
  by (intro wf_inv_image wf_mult wf_rel_pat)


lemma tvars_mp_fin: 
  "finite (tvars_mp (mp_mset mp))"  
  unfolding tvars_mp_def by auto

lemmas meas_def = meas_finvars_def meas_diff_def meas_symbols_def meas_setsize_def

lemma tvars_mp_mono: "mp \<subseteq># mp' \<Longrightarrow> tvars_mp (mp_mset mp) \<subseteq> tvars_mp (mp_mset mp')" 
  unfolding tvars_mp_def 
  by (intro image_mono subset_refl set_mset_mono UN_mono)

lemma meas_finvars_mono: assumes "tvars_mp (mp_mset mp) \<subseteq> tvars_mp (mp_mset mp')" 
  shows "meas_finvars {#mp#} \<le> meas_finvars {#mp'#}" 
  using tvars_mp_fin[of mp'] assms
  unfolding meas_def by (auto intro: sum_mono2)

lemma rel_mp_sub: "{# add_mset p mp#} \<succ> {# mp #}"
proof - 
  let ?mp' = "add_mset p mp" 
  have "mp \<subseteq># ?mp'" by auto
  from meas_finvars_mono[OF tvars_mp_mono[OF this]]
  show ?thesis unfolding meas_def rel_pat_def by auto
qed

lemma rel_mp_mp_step_mset: 
  assumes "mp \<rightarrow>\<^sub>m mp'" 
  shows "{#mp#} \<succ> {#mp'#}"  
  using assms
proof cases
  case *: (match_decompose f ts g ls mp'')
  have "meas_finvars {#mp'#} \<le> meas_finvars {#mp#}" 
  proof (rule meas_finvars_mono)
    show "tvars_mp (mp_mset mp') \<subseteq> tvars_mp (mp_mset mp)" 
      unfolding tvars_mp_def * using *(3) by (auto simp: set_zip set_conv_nth)
  qed
  moreover 
  have id: "(case case x of (x, y) \<Rightarrow> (y, x) of (t, l) \<Rightarrow> f t l) = (case x of (a,b) \<Rightarrow> f b a)" for 
    x :: "('f, 'v) Term.term \<times> ('f, nat \<times> 's) Term.term" and f :: "_ \<Rightarrow> _ \<Rightarrow> nat" 
    by (cases x, auto)
  have "meas_diff {#mp'#} \<le> meas_diff {#mp#}" 
    unfolding meas_def * using *(3) 
    by (auto simp: sum_mset_sum_list[symmetric] zip_commute[of ts ls] image_mset.compositionality o_def id)
  moreover have "meas_symbols {#mp'#} < meas_symbols {#mp#}" 
    unfolding meas_def * using *(3) size_mset_Fun_less[of ts ls g g]
    by (auto simp: sum_mset_sum_list)
  ultimately show ?thesis unfolding rel_pat_def by auto
next
  case *: (match_match x t)
  show ?thesis unfolding *
    by (rule rel_mp_sub)
next
  case *: (match_duplicate pair mp)
  show ?thesis unfolding *
    by (rule rel_mp_sub)  
qed

lemma sum_ms_image: "sum_ms f (image_mset g ms) = sum_ms (f o g) ms"
  by (simp add: multiset.map_comp)

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
  "meas_symbols p' \<le> meas_symbols p"
proof -
  from sub obtain p'' where p: "p = p' + p''" by (metis subset_mset.less_eqE)
  show "meas_diff p' \<le> meas_diff p" "meas_finvars p' \<le> meas_finvars p" "meas_symbols p' \<le> meas_symbols p" 
    unfolding meas_def p by auto
qed

lemma meas_sub_rel_pat: assumes sub: "p' \<subset># p" 
  shows "p \<succ> p'" 
proof -
  from sub obtain x p'' where p: "p = add_mset x p' + p''"
    by (metis multi_nonempty_split subset_mset.lessE union_mset_add_mset_left union_mset_add_mset_right)
  hence lt: "meas_setsize p' < meas_setsize p" unfolding meas_def by auto
  from sub have "p' \<subseteq># p" by auto
  from lt meas_sub[OF this]
  show ?thesis unfolding rel_pat_def by auto
qed

lemma max_size_term_of_sort: assumes sS: "s \<in> S" and inf: "\<not> inf_sort s" 
  shows "\<exists> t. t : s in \<T>(C,EMPTYn) \<and> max_size s = size t \<and> (\<forall> t'. t' : s in \<T>(C,EMPTYn) \<longrightarrow> size t' \<le> size t)" 
proof -
  let ?set = "\<lambda> s. size ` {t. t : s in \<T>(C,EMPTYn)}" 
  have m: "max_size s = Maximum (?set s)" unfolding o_def max_size_def using inf  sS by auto
  
  from inf[unfolded inf_sort_def[OF sS]] have "bdd_above (?set s)" by auto
  moreover from sorts_non_empty[OF sS] type_conversion2 have "?set s \<noteq> {}" by auto
  ultimately have "has_Maximum (?set s)" by (rule bdd_above_has_Maximum_nat) 
  from has_MaximumD[OF this, folded m] show ?thesis by auto
qed

lemma max_size_max: assumes sS: "s \<in> S" 
  and inf: "\<not> inf_sort s" 
  and sort:  "t : s in \<T>(C,EMPTYn)" 
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
      note term_of_sort[OF this]
    }
    hence "\<forall> v. \<exists> t. v \<in> set vs \<longrightarrow> t : snd v in \<T>(C,EMPTYn)" by auto
    from choice[OF this] obtain t where 
      t: "\<And> v. v \<in> set vs \<Longrightarrow> t v : snd v in \<T>(C,EMPTYn)" by blast
    from True vsS obtain vl where vl: "vl \<in> set vs" and vlS: "snd vl \<in> S" and inf_vl: "inf_sort (snd vl)" by auto
    from not_bdd_above_natD[OF inf_vl[unfolded inf_sort_def[OF vlS]], of ?m] t[OF vl]
     obtain tl where 
      tl: "tl : snd vl in \<T>(C,EMPTYn)" and large: "?m \<le> size tl" by fastforce
    let ?t = "Fun c (map (\<lambda> v. if v = vl then tl else t v) vs)" 
    have "?t : s in \<T>(C,EMPTYn)" 
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
      have "\<exists> t. t : snd v in \<T>(C,EMPTYn) \<and> size t = max_size (snd v)" by auto
    }
    hence "\<forall> v. \<exists> t. v \<in> set vs \<longrightarrow> t : snd v in \<T>(C,EMPTYn) \<and> size t = max_size (snd v)" by auto
    from choice[OF this] obtain t where 
      t: "v \<in> set vs \<Longrightarrow> t v : snd v in \<T>(C,EMPTYn) \<and> size (t v) = max_size (snd v)" for v by blast
    let ?t = "Fun c (map t vs)" 
    have "?t : s in \<T>(C,EMPTYn)" 
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

lemma rel_pp_step_mset:
  assumes "p \<Rightarrow>\<^sub>m ps" 
  and "p' \<in># ps"
shows "p \<succ> p'" 
  using assms
proof induct
  case *: (pat_simp_mp mp mp' p)
  hence p': "p' = add_mset mp' p" by auto
  from rel_mp_mp_step_mset[OF *(1)]
  show ?case unfolding p' rel_pat_def meas_def by auto
next
  case (pat_remove_mp mp p)
  hence p': "p' = p" by auto 
  show ?case unfolding p' 
    by (rule meas_sub_rel_pat, auto)
next
  case *: (pat_instantiate n mp p x l s y t)
  from *(2) have "\<exists> s t. (s,t) \<in># mp \<and>  (s = Var x \<and> is_Fun t
          \<or> (x \<in> vars s \<and> \<not> inf_sort (snd x)))"
  proof
    assume *: "(s, Var y) \<in># mp \<and> (t, Var y) \<in># mp \<and> Conflict_Var s t x \<and> \<not> inf_sort (snd x)" 
    hence "Conflict_Var s t x" and "\<not> inf_sort (snd x)" by auto
    from conflicts(4)[OF this(1)] this(2) *
    show ?thesis by auto
  qed auto
  then obtain s t where st: "(s,t) \<in># mp" and choice: "s = Var x \<and> is_Fun t \<or> x \<in> vars s \<and> \<not> inf_sort (snd x)" 
    by auto
  let ?p = "add_mset mp p" 
  let ?s = "snd x" 
  from *(3) \<tau>s_list
  obtain \<tau> where \<tau>: "\<tau> \<in> \<tau>s n x" and p': "p' = subst_pat_problem_mset \<tau> ?p" by auto
  
  let ?tau_mset = "subst_pat_problem_mset \<tau>" 
  let ?tau = "subst_match_problem_mset \<tau>" 
  from \<tau>[unfolded \<tau>s_def \<tau>c_def List.maps_def]
  obtain c sorts where c: "c : sorts \<rightarrow> ?s in C" and tau: "\<tau> = subst x (Fun c (map Var (zip [n..<n + length sorts] sorts)))" 
    by auto
  with C_sub_S have sS: "?s \<in> S" and sorts: "set sorts \<subseteq> S" by auto
  define vs where "vs = zip [n..<n + length sorts] sorts" 
  have \<tau>: "\<tau> = subst x (Fun c (map Var vs))" unfolding tau vs_def by auto
  have "snd ` vars (\<tau> y) \<subseteq> insert (snd y) S" for y
    using sorts unfolding tau by (auto simp: subst_def set_zip set_conv_nth)
  hence vars_sort: "(a,b) \<in> vars (\<tau> y) \<Longrightarrow> b \<in> insert (snd y) S" for a b y by fastforce 
  from st obtain mp' where mp: "mp = add_mset (s,t) mp'" by (rule mset_add)
  from choice have "?p \<succ> ?tau_mset ?p" 
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
    finally show ?thesis unfolding rel_pat_def by auto
  next
    assume "x \<in> vars s \<and> \<not> inf_sort (snd x)" 
    hence x: "x \<in> vars s" and inf: "\<not> inf_sort (snd x)" by auto
    from meas_diff_subst_le[of \<tau>]  
    have fd: "meas_diff p' \<le> meas_diff ?p" unfolding p' .
    have "meas_finvars (?tau_mset ?p) = meas_finvars (?tau_mset {#mp#}) + meas_finvars (?tau_mset p)" 
      unfolding subst_defs meas_def by auto
    also have "\<dots> < meas_finvars {#mp#} + meas_finvars p"
    proof (rule add_less_le_mono)
      have vars_\<tau>_var: "vars (\<tau> y) = (if x = y then set vs else {y})" for y unfolding \<tau> subst_def by auto
      have vars_\<tau>: "vars (t \<cdot> \<tau>) = vars t - {x} \<union> (if x \<in> vars t then set vs else {})" for t
        unfolding vars_term_subst image_comp o_def vars_\<tau>_var by auto
      have tvars_mp_subst: "tvars_mp (mp_mset (?tau mp)) = 
          tvars_mp (mp_mset mp) - {x} \<union> (if x \<in> tvars_mp (mp_mset mp) then set vs else {})" for mp
        unfolding subst_defs subst_left_def tvars_mp_def
        by (auto simp:vars_\<tau> split: if_splits prod.split)
      have id1: "meas_finvars (?tau_mset {#mp#}) = (\<Sum>x\<in> tvars_mp (mp_mset (?tau mp)). max_size (snd x))"  for mp
        unfolding meas_def subst_defs by auto
      have id2: "meas_finvars {#mp#} = (\<Sum>x\<in>tvars_mp (mp_mset mp). max_size (snd x))" for mp
        unfolding meas_def subst_defs by simp
      have eq: "x \<notin> tvars_mp (mp_mset mp) \<Longrightarrow> meas_finvars (?tau_mset {# mp #}) = meas_finvars {#mp#}" for mp
        unfolding id1 id2 by (rule sum.cong[OF _ refl], auto simp: tvars_mp_subst)
      {
        fix mp
        (* if x occurs in the matching problem, then we get a strict decrease *)
        assume xmp: "x \<in> tvars_mp (mp_mset mp)" 
        let ?mp = "(mp_mset mp)" 
        have fin: "finite (tvars_mp ?mp)" by (rule tvars_mp_fin)
        define Mp where "Mp = tvars_mp ?mp - {x}" 
        from xmp have 1: "tvars_mp (mp_mset (?tau mp)) = set vs \<union> Mp" 
          unfolding tvars_mp_subst Mp_def by auto
        from xmp have 2: "tvars_mp ?mp = insert x Mp" and xMp: "x \<notin> Mp" unfolding Mp_def by auto
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
        by (intro less, unfold mp, force simp: tvars_mp_def)

      show "meas_finvars (?tau_mset p) \<le> meas_finvars p" 
        unfolding subst_pat_problem_mset_def meas_finvars_def sum_ms_image o_def
        apply (rule sum_mset_mono)
        subgoal for mp using le[of mp] unfolding meas_finvars_def o_def subst_defs by auto
        done
    qed
    also have "\<dots> = meas_finvars ?p" unfolding p' meas_def by simp
    finally show ?thesis using fd unfolding rel_pat_def p' by auto
  qed
  thus ?case unfolding p' .
next
  case *: (pat_remove_pp p)
  thus ?case by (intro meas_sub_rel_pat, auto)
qed

text \<open>finally: the transformation is terminating w.r.t. @{term "(\<succ>mul)"}\<close>
lemma rel_P_trans: 
  assumes "P \<Rrightarrow>\<^sub>m P'" 
  shows "P \<succ>mul P'" 
  using assms
proof induct
  case *: (P_failure p P)
  from * have "p \<noteq> {#} \<or> p = {#} \<and> P \<noteq> {#}" by auto
  thus ?case
  proof
    assume "p \<noteq> {#}" 
    then obtain mp p' where p: "p = add_mset mp p'" by (cases p, auto)
    have "p \<succ> {#}" unfolding p by (intro meas_sub_rel_pat, auto)
    thus ?thesis unfolding rel_pats_def using 
        one_step_implies_mult[of "add_mset p P" "{#{#}#}" _ "{#}"]
      by auto
  next
    assume *: "p = {#} \<and> P \<noteq> {#}" then obtain p' P' where p: "p = {#}" and P: "P = add_mset p' P'" by (cases P, auto)
    show ?thesis unfolding P p unfolding rel_pats_def 
      by (simp add: subset_implies_mult)
  qed
next
  case *: (P_simp_pp p ps P)
  from rel_pp_step_mset[OF *]
  show ?case unfolding rel_pats_def by (metis add_many_mult)
qed

text \<open>termination of the multiset based implementation\<close>
theorem SN_P_step: "SN \<Rrightarrow>" 
proof -
  have sub: "\<Rrightarrow> \<subseteq> \<prec>mul^-1"
    using rel_P_trans unfolding P_step_def by auto
  show ?thesis
    apply (rule SN_subset[OF _ sub])
    using wf_rel_pats by (simp add: wf_imp_SN)
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
qed

lemma mp_fail_cong: "mp_fail mp \<Longrightarrow> mp = mp' \<Longrightarrow> mp_fail mp'" by auto

lemma match_fail_mp_fail: "match_fail mp \<Longrightarrow> mp_fail (mp_mset mp)" 
proof (induct mp rule: match_fail.induct)
  case *: (match_clash f ts g ls mp)
  show ?case by (rule mp_fail_cong[OF mp_clash], insert *, auto)
next
  case *: (match_clash' s t x mp)
  show ?case by (rule mp_fail_cong[OF mp_clash'], insert *, auto)
qed

lemma P_step_set_cong: "P \<Rrightarrow>\<^sub>s Q \<Longrightarrow> P = P' \<Longrightarrow> Q = Q' \<Longrightarrow> P' \<Rrightarrow>\<^sub>s Q'" by auto

lemma P_step_mset_imp_set: assumes "P \<Rrightarrow>\<^sub>m Q"
  shows "pats_mset P \<Rrightarrow>\<^sub>s pats_mset Q" 
  using assms
proof (induct)
  case *: (P_failure p P)
  let ?P = "insert (pat_mset p) (pats_mset P)" 
  from *(1)
  have "?P \<Rrightarrow>\<^sub>s bottom"
  proof induct
    case (pat_failure' p)
    from P_failure'[OF this]
    show ?case by auto
  next
    case pat_empty
    show ?case using P_fail by auto
  qed
  thus ?case by auto
next
  case *: (P_simp_pp p ps P)  
  note conv = o_def image_mset_union image_empty image_mset_add_mset Un_empty_left
    set_mset_add_mset_insert set_mset_union image_Un image_insert set_mset_empty
    set_mset_mset set_image_mset
    set_map image_comp insert_is_Un[symmetric]
  define P' where "P' = {mp_mset ` set_mset x |. x \<in> set_mset P}" 
  from *(1)
  have "insert (pat_mset p) (pats_mset P) \<Rrightarrow>\<^sub>s pats_mset ps \<union> pats_mset P"
    unfolding conv P'_def[symmetric]
  proof induction
    case (pat_remove_pp p)
    show ?case unfolding conv
      by (intro P_remove_pp pp_success.intros)
  next
    case *: (pat_simp_mp mp mp' p)
    from P_simp[OF pp_simp_mp[OF mp_step_mset_mp_trans[OF *]]]
    show ?case by auto
  next
    case *: (pat_remove_mp mp p)
    from P_simp[OF pp_remove_mp[OF match_fail_mp_fail[OF *]]]
    show ?case by simp
  next
    case *: (pat_instantiate n mp p x l s y t)
    from *(2) have "x \<in> tvars_mp (mp_mset mp)" 
      using conflicts(4)[of s t x] unfolding tvars_mp_def
      by (auto intro!:term.set_intros(3))
    hence x: "x \<in> tvars_pp (pat_mset (add_mset mp p))" unfolding tvars_pp_def 
      using *(2) by auto
    show ?case unfolding conv \<tau>s_list
      apply (rule P_step_set_cong[OF P_instantiate[OF *(1) x]])
      by (unfold conv subst_defs set_map image_comp, auto)
  qed
  thus ?case unfolding conv .
qed

lemma P_step_pp_trans: assumes "(P,Q) \<in> \<Rrightarrow>"
  shows "pats_mset P \<Rrightarrow>\<^sub>s pats_mset Q" 
  by (rule P_step_mset_imp_set, insert assms, unfold P_step_def, auto)

theorem P_step_pcorrect: assumes wf: "wf_pats (pats_mset P)" and step: "(P,Q) \<in> P_step"
shows "wf_pats (pats_mset Q) \<and> (pats_complete (pats_mset P) = pats_complete (pats_mset Q))" 
proof -
  note step = P_step_pp_trans[OF step]
  from P_step_set_pcorrect[OF step] P_step_set_wf[OF step] wf
  show ?thesis by auto
qed

corollary P_steps_pcorrect: assumes wf: "wf_pats (pats_mset P)" 
  and step: "(P,Q) \<in> \<Rrightarrow>\<^sup>*" 
shows "wf_pats (pats_mset Q) \<and> (pats_complete (pats_mset P) \<longleftrightarrow> pats_complete (pats_mset Q))"
  using step by induct (insert wf P_step_pcorrect, auto)

text \<open>Gather all results for the multiset-based implementation: 
    decision procedure on well-formed inputs (termination was proven before)\<close>

theorem P_step:
  assumes wf: "wf_pats (pats_mset P)" and NF: "(P,Q) \<in> \<Rrightarrow>\<^sup>!"
  shows "Q = {#} \<and> pats_complete (pats_mset P) \<comment> \<open>either the result is {} and input P is complete\<close>
  \<or> Q = bottom_mset \<and> \<not> pats_complete (pats_mset P) \<comment> \<open>or the result = bot and P is not complete\<close>" 
proof -
  from NF have steps: "(P,Q) \<in> \<Rrightarrow>^*" and NF: "Q \<in> NF P_step" by auto
  from P_steps_pcorrect[OF wf steps]
  have wf: "wf_pats (pats_mset Q)" and 
    sound: "pats_complete (pats_mset P) = pats_complete (pats_mset Q)" 
    by blast+
  from P_step_NF[OF NF] have "Q \<in> {{#},bottom_mset}" .
  thus ?thesis unfolding sound by auto
qed

end
end