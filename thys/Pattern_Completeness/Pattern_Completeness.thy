section \<open>Pattern-Completeness and Related Properties\<close>

text \<open>We use the core decision procedure for pattern completeness 
  and connect it to other properties like pattern completeness of programs (where the lhss are given), 
  or (strong) quasi-reducibility.\<close>

theory Pattern_Completeness
  imports 
    Pattern_Completeness_List
    Show.Shows_Literal
    Certification_Monads.Check_Monad
begin


text \<open>A pattern completeness decision procedure for a set of lhss\<close>

definition basic_terms :: "('f,'s)ssig \<Rightarrow> ('f,'s)ssig \<Rightarrow> ('v \<rightharpoonup> 's) \<Rightarrow> ('f,'v)term set" (\<open>\<B>'(_,_,_')\<close>) where
  "\<B>(C,D,V) = { Fun f ts | f ss s ts . f : ss \<rightarrow> s in D \<and> ts :\<^sub>l ss in \<T>(C,V)}" 

definition matches :: "('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool" (infix \<open>matches\<close> 50) where
  "l matches t = (\<exists> \<sigma>. t = l \<cdot> \<sigma>)"

definition pat_complete_lhss :: "('f,'s)ssig \<Rightarrow> ('f,'s)ssig \<Rightarrow> ('f,'v)term set \<Rightarrow> bool" where
  "pat_complete_lhss C D L = (\<forall> t \<in> \<B>(C,D,\<emptyset>). \<exists>l \<in> L. l matches t)" 


definition decide_pat_complete_lhss :: 
  "(('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl + bool" where
  "decide_pat_complete_lhss C D lhss = do {
    check (distinct (map fst C)) (showsl_lit (STR ''constructor information contains duplicate''));
    check (distinct (map fst D)) (showsl_lit (STR ''defined symbol information contains duplicate''));
    let S = sorts_of_ssig_list C;
    check_allm (\<lambda> ((f,ss),_). check_allm (\<lambda> s. check (s \<in> set S) 
      (showsl_lit (STR ''a defined symbol has argument sort that is not known in constructors''))) ss) D;
    (case (decide_nonempty_sorts S C) of None \<Rightarrow> return () | Some s \<Rightarrow> error (showsl_lit (STR ''some sort is empty'')));
    let pats = [Fun f (map Var (zip [0..<length ss] ss)). ((f,ss),s) \<leftarrow> D];
    let P = [[[(pat,lhs)]. lhs \<leftarrow> lhss]. pat \<leftarrow> pats];
    return (decide_pat_complete C P)
  }" 

theorem decide_pat_complete_lhss: 
  assumes "decide_pat_complete_lhss C D (lhss :: ('f,'v)term list) = return b" 
  shows "b = pat_complete_lhss (map_of C) (map_of D) (set lhss)" 
proof -
  let ?EMPTY = "pattern_completeness_context.EMPTY" 
  let ?cg_subst = "pattern_completeness_context.cg_subst" 
  let ?C = "map_of C"
  let ?D = "map_of D" 
  define S where "S = sorts_of_ssig_list C" 
  define pats where "pats = map (\<lambda> ((f,ss),s). Fun f (map Var (zip [0..<length ss] ss))) D" 
  define P where "P = map (\<lambda> pat. map (\<lambda> lhs. [(pat,lhs)]) lhss) pats" 
  let ?match_lhs = "\<lambda>t. \<exists>l \<in> set lhss. l matches t" 
  note ass = assms(1)[unfolded decide_pat_complete_lhss_def, folded S_def, 
      unfolded Let_def, folded pats_def, folded P_def, simplified]
  from ass have dec: "decide_nonempty_sorts S C = None" (is "?e = _") by (cases ?e, auto) 
  note ass = ass[unfolded dec, simplified]
  from ass have b: "b = decide_pat_complete C P" and dist: "distinct (map fst C)" "distinct (map fst D)" by auto
  have "b = decide_pat_complete C P" by fact
  also have "\<dots> = pats_complete (set S) ?C (pat_list ` set P)" 
  proof (rule decide_pat_complete[OF refl dist(1) dec[unfolded S_def]], unfold S_def[symmetric])
    {
      fix i si f ss s
      assume mem: "((f, ss), s) \<in> set D" and isi: "(i, si) \<in> set (zip [0..<length ss] ss)" 
      from isi have si: "si \<in> set ss" by (metis in_set_zipE)
      from mem si ass
      have "si \<in> set S" by auto
    }
    thus "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> set S" unfolding P_def pats_def by force
  qed simp
  also have "pat_list ` set P = { { {(pat,lhs)} | lhs. lhs \<in> set lhss} | pat. pat \<in> set pats}" 
    unfolding pat_list_def P_def by (auto simp: image_comp)
  also have "pats_complete (set S) ?C \<dots> \<longleftrightarrow>
     Ball { pat \<cdot> \<sigma> | pat \<sigma>. pat \<in> set pats \<and> ?cg_subst (set S) ?C \<sigma>} ?match_lhs" (is "_ = Ball ?L _")
    unfolding pattern_completeness_context.pat_complete_def 
      pattern_completeness_context.match_complete_wrt_def matches_def 
    by auto (smt (verit, best) case_prod_conv mem_Collect_eq singletonI, blast)
  also have "?L = \<B>(?C,?D,\<emptyset>)" (is "_ = ?R")
  proof 
    {
      fix pat and \<sigma> :: "('f,_,'v)gsubst" 
      assume pat: "pat \<in> set pats" and subst: "?cg_subst (set S) ?C \<sigma>"
      from pat[unfolded pats_def] obtain f ss s where pat: "pat = Fun f (map Var (zip [0..<length ss] ss))" 
        and inDs: "((f,ss),s) \<in> set D" by auto
      from dist(2) inDs have f: "f : ss \<rightarrow> s in ?D" unfolding fun_hastype_def by simp
      {
        fix i
        assume i: "i < length ss" 
        hence "ss ! i \<in> set ss" by auto
        with inDs ass have "ss ! i \<in> set S" by auto
        with subst have "\<sigma> (i, ss ! i) : ss ! i in \<T>(?C,\<emptyset>)" unfolding pattern_completeness_context.cg_subst_def 
            pattern_completeness_context.EMPTY_def by auto
      } note ssigma = this
      define ts where "ts = (map (\<lambda> i. \<sigma> (i, ss ! i)) [0..<length ss])" 
      have ts: "ts :\<^sub>l ss in \<T>(?C,\<emptyset>)" unfolding list_all2_conv_all_nth ts_def using ssigma by auto
      have pat: "pat \<cdot> \<sigma> = Fun f ts" 
        unfolding pat ts_def by (auto intro: nth_equalityI)
      from pat f ts have "pat \<cdot> \<sigma> \<in> ?R" unfolding basic_terms_def by auto
    }
    thus "?L \<subseteq> ?R" by blast
    {
      fix f ss s and ts :: "('f,'v)term list" 
      assume f: "f : ss \<rightarrow> s in ?D" and ts: "ts :\<^sub>l ss in \<T>(?C,\<emptyset>)" 
      from ts have len: "length ts = length ss" by (metis list_all2_lengthD)
      define pat where "pat = Fun f (map Var (zip [0..<length ss] ss))"
      from f have "((f,ss),s) \<in> set D" unfolding fun_hastype_def by (metis map_of_SomeD)
      hence pat: "pat \<in> set pats" unfolding pat_def pats_def by force
      define \<sigma> where "\<sigma> x = (case x of (i,s) \<Rightarrow> if i < length ss \<and> s = ss ! i then ts ! i else 
        (SOME t. t : s in \<T>(?C,?EMPTY)))" for x
      have id: "Fun f ts = pat \<cdot> \<sigma>" unfolding pat_def using len
        by (auto intro!: nth_equalityI simp: \<sigma>_def)
      have ssigma: "?cg_subst (set S) ?C \<sigma>" 
        unfolding pattern_completeness_context.cg_subst_def
      proof (intro allI impI)
        fix x :: "nat \<times> _" 
        assume "snd x \<in> set S" 
        then obtain i s where x: "x = (i,s)" and s: "s \<in> set S" by (cases x, auto)
        show "\<sigma> x : snd x in \<T>(?C,?EMPTY)" 
        proof (cases "i < length ss \<and> s = ss ! i")
          case True
          hence id: "\<sigma> x = ts ! i" unfolding x \<sigma>_def by auto
          from ts True show ?thesis unfolding id unfolding x snd_conv pattern_completeness_context.EMPTY_def 
            by (simp add: list_all2_conv_all_nth)
        next
          case False
          hence id: "\<sigma> x = (SOME t. t : s in \<T>(?C,?EMPTY))" unfolding x \<sigma>_def by auto
          from decide_nonempty_sorts(1)[OF dist(1) refl dec] s
          have "\<exists> t. t : s in \<T>(?C,?EMPTY)" unfolding pattern_completeness_context.EMPTY_def by auto
          from someI_ex[OF this] have "\<sigma> x : s in \<T>(?C,?EMPTY)" unfolding id .
          thus ?thesis unfolding x by auto
        qed
      qed
      from pat id ssigma
      have "Fun f ts \<in> ?L" by auto
    }
    thus "?R \<subseteq> ?L" unfolding basic_terms_def by auto
  qed
  finally show ?thesis unfolding pat_complete_lhss_def by blast
qed

text \<open>Definition of strong quasi-reducibility and a corresponding decision procedure\<close>

definition strong_quasi_reducible :: "('f,'s)ssig \<Rightarrow> ('f,'s)ssig \<Rightarrow> ('f,'v)term set \<Rightarrow> bool" where
  "strong_quasi_reducible C D L =
  (\<forall> t \<in> \<B>(C,D,\<emptyset>). \<exists> ti \<in> set (t # args t). \<exists>l \<in> L. l matches ti)" 


definition term_and_args :: "'f \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term list" where
  "term_and_args f ts = Fun f ts # ts"  

definition decide_strong_quasi_reducible :: 
  "(('f \<times> 's list) \<times> 's)list \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl + bool" where
  "decide_strong_quasi_reducible C D lhss = do {
    check (distinct (map fst C)) (showsl_lit (STR ''constructor information contains duplicate''));
    check (distinct (map fst D)) (showsl_lit (STR ''defined symbol information contains duplicate''));
    let S = sorts_of_ssig_list C;
    check_allm (\<lambda> ((f,ss),_). check_allm (\<lambda> s. check (s \<in> set S) 
      (showsl_lit (STR ''defined symbol f has argument sort s that is not known in constructors''))) ss) D;
    (case (decide_nonempty_sorts S C) of None \<Rightarrow> return () | Some s \<Rightarrow> error (showsl_lit (STR ''sort s is empty'')));
    let pats = map (\<lambda> ((f,ss),s). term_and_args f (map Var (zip [0..<length ss] ss))) D;
    let P = map (List.maps (\<lambda> pat. map (\<lambda> lhs. [(pat,lhs)]) lhss)) pats;
    return (decide_pat_complete C P)
  }" 

lemma decide_strong_quasi_reducible: 
  assumes "decide_strong_quasi_reducible C D (lhss :: ('f,'v)term list) = return b" 
  shows "b = strong_quasi_reducible (map_of C) (map_of D) (set lhss)" 
proof -
  let ?EMPTY = "pattern_completeness_context.EMPTY" 
  let ?cg_subst = "pattern_completeness_context.cg_subst" 
  let ?C = "map_of C"
  let ?D = "map_of D" 
  define S where "S = sorts_of_ssig_list C" 
  define pats where "pats = map (\<lambda> ((f,ss),s). term_and_args f (map Var (zip [0..<length ss] ss))) D" 
  define P where "P = map (List.maps (\<lambda> pat. map (\<lambda> lhs. [(pat,lhs)]) lhss)) pats" 
  let ?match_lhs = "\<lambda>t. \<exists>l \<in> set lhss. l matches t" 
  note ass = assms(1)[unfolded decide_strong_quasi_reducible_def, folded S_def, folded pats_def, 
      unfolded Let_def, folded P_def]
  from ass have dec: "decide_nonempty_sorts S C = None" (is "?e = _") by (cases ?e, auto) 
  note ass = ass[unfolded dec, simplified]
  from ass have b: "b = decide_pat_complete C P" and dist: "distinct (map fst C)" "distinct (map fst D)" by auto
  have "b = decide_pat_complete C P" by fact
  also have "\<dots> = pats_complete (set S) ?C (pat_list ` set P)" 
  proof (rule decide_pat_complete[OF refl dist(1) dec[unfolded S_def]], unfold S_def[symmetric])
    {
      fix f ss s i si
      assume mem: "((f, ss), s) \<in> set D" and isi: "(i, si) \<in> set (zip [0..<length ss] ss)"
      from isi have si: "si \<in> set ss" by (metis in_set_zipE)
      from mem si ass
      have "si \<in> set S" by auto
    }
    thus "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> set S" unfolding P_def pats_def term_and_args_def List.maps_def
      by fastforce
  qed simp
  also have "pat_list ` set P = { { {(pat,lhs)} | lhs pat. pat \<in> set patL \<and> lhs \<in> set lhss} | patL. patL \<in> set pats}" 
    unfolding pat_list_def P_def List.maps_def by (auto simp: image_comp) force+
  also have "pats_complete (set S) ?C \<dots> \<longleftrightarrow>
     (\<forall> patsL \<sigma>. patsL \<in> set pats \<longrightarrow> ?cg_subst (set S) ?C \<sigma> \<longrightarrow> (\<exists> pat \<in> set patsL. ?match_lhs (pat \<cdot> \<sigma>)))" (is "_ \<longleftrightarrow> ?L")
    unfolding pattern_completeness_context.pat_complete_def 
      pattern_completeness_context.match_complete_wrt_def matches_def 
    by auto 
      (smt (verit, best) case_prod_conv mem_Collect_eq singletonI, 
        metis (mono_tags, lifting) case_prod_conv singleton_iff)
  also have "?L 
    \<longleftrightarrow> (\<forall> f ss s (ts :: ('f,'v)term list). f : ss \<rightarrow> s in ?D \<longrightarrow> ts :\<^sub>l ss in \<T>(?C,\<emptyset>) \<longrightarrow> 
           (\<exists> ti \<in> set (term_and_args f ts). ?match_lhs ti))" (is "_ = ?R")
  proof (standard; intro allI impI)  
    fix patL and \<sigma> :: "('f,_,'v)gsubst" 
    assume patL: "patL \<in> set pats" and subst: "?cg_subst (set S) ?C \<sigma>" and R: ?R
    from patL[unfolded pats_def] obtain f ss s where patL: "patL = term_and_args f (map Var (zip [0..<length ss] ss))" 
      and inDs: "((f,ss),s) \<in> set D" by auto
    from dist(2) inDs have f: "f : ss \<rightarrow> s in ?D" unfolding fun_hastype_def by simp
    {
      fix i
      assume i: "i < length ss" 
      hence "ss ! i \<in> set ss" by auto
      with inDs ass have "ss ! i \<in> set S" by auto
      with subst have "\<sigma> (i, ss ! i) : ss ! i in \<T>(?C,\<emptyset>)" 
        unfolding pattern_completeness_context.cg_subst_def pattern_completeness_context.EMPTY_def by auto
    } note ssigma = this
    define ts where "ts = (map (\<lambda> i. \<sigma> (i, ss ! i)) [0..<length ss])" 
    have ts: "ts :\<^sub>l ss in \<T>(?C,\<emptyset>)" unfolding list_all2_conv_all_nth ts_def using ssigma by auto
    from R[rule_format, OF f ts] obtain ti where ti: "ti \<in> set (term_and_args f ts)" and match: "?match_lhs ti" by auto
    have "map (\<lambda> pat. pat \<cdot> \<sigma>) patL = term_and_args f ts" unfolding patL term_and_args_def ts_def
      by (auto intro: nth_equalityI)
    from ti[folded this] match
    show "\<exists>pat\<in>set patL. ?match_lhs (pat \<cdot> \<sigma>)" by auto
  next
    fix f ss s and ts :: "('f,'v)term list" 
    assume f: "f : ss \<rightarrow> s in ?D" and ts: "ts :\<^sub>l ss in \<T>(?C,\<emptyset>)" and L: ?L
    from ts have len: "length ts = length ss" by (metis list_all2_lengthD)
    define patL where "patL = term_and_args f (map Var (zip [0..<length ss] ss))" 
    from f have "((f,ss),s) \<in> set D" unfolding fun_hastype_def by (metis map_of_SomeD)
    hence patL: "patL \<in> set pats" unfolding patL_def pats_def by force
    define \<sigma> where "\<sigma> x = (case x of (i,s) \<Rightarrow> if i < length ss \<and> s = ss ! i then ts ! i else 
      (SOME t. t : s in \<T>(?C,?EMPTY)))" for x
    have ssigma: "?cg_subst (set S) ?C \<sigma>" 
      unfolding pattern_completeness_context.cg_subst_def
    proof (intro allI impI)
      fix x :: "nat \<times> _" 
      assume "snd x \<in> set S" 
      then obtain i s where x: "x = (i,s)" and s: "s \<in> set S" by (cases x, auto)
      show "\<sigma> x : snd x in \<T>(?C,?EMPTY)" 
      proof (cases "i < length ss \<and> s = ss ! i")
        case True
        hence id: "\<sigma> x = ts ! i" unfolding x \<sigma>_def by auto
        from ts True show ?thesis unfolding id unfolding x snd_conv pattern_completeness_context.EMPTY_def 
          by (simp add: list_all2_conv_all_nth)
      next
        case False
        hence id: "\<sigma> x = (SOME t. t : s in \<T>(?C,?EMPTY))" unfolding x \<sigma>_def by auto
        from decide_nonempty_sorts(1)[OF dist(1) refl dec] s
        have "\<exists> t. t : s in \<T>(?C,?EMPTY)" unfolding pattern_completeness_context.EMPTY_def by auto
        from someI_ex[OF this] have "\<sigma> x : s in \<T>(?C,?EMPTY)" unfolding id .
        thus ?thesis unfolding x by auto
      qed
    qed
    from L[rule_format, OF patL ssigma]
    obtain pat where pat: "pat \<in> set patL" and match: "?match_lhs (pat \<cdot> \<sigma>)" by auto
    have id: "map (\<lambda> pat. pat \<cdot> \<sigma>) patL = term_and_args f ts" unfolding patL_def term_and_args_def using len
      by (auto intro!: nth_equalityI simp: \<sigma>_def)      
    show "\<exists>ti \<in> set (term_and_args f ts). ?match_lhs ti" unfolding id[symmetric] using pat match by auto
  qed
  also have "\<dots> = (\<forall>t. t \<in> \<B>(?C,?D,\<emptyset>) \<longrightarrow> (\<exists> ti \<in> set (t # args t). ?match_lhs ti))" 
    unfolding basic_terms_def term_and_args_def by force
  finally show ?thesis unfolding strong_quasi_reducible_def by blast
qed

subsection \<open>Connecting Pattern-Completeness, Strong Quasi-Reducibility and Quasi-Reducibility\<close>

definition quasi_reducible :: "('f,'s)ssig \<Rightarrow> ('f,'s)ssig \<Rightarrow> ('f,'v)term set \<Rightarrow> bool" where
  "quasi_reducible C D L = (\<forall> t \<in> \<B>(C,D,\<emptyset>). \<exists> tp \<unlhd> t. \<exists>l \<in> L. l matches tp)" 

lemma pat_complete_imp_strong_quasi_reducible:
  "pat_complete_lhss C D L \<Longrightarrow> strong_quasi_reducible C D L" 
  unfolding pat_complete_lhss_def strong_quasi_reducible_def by force

lemma arg_imp_subt: "s \<in> set (args t) \<Longrightarrow> t \<unrhd> s" 
  by (cases t, auto)

lemma strong_quasi_reducible_imp_quasi_reducible:
  "strong_quasi_reducible C D L \<Longrightarrow> quasi_reducible C D L" 
  unfolding strong_quasi_reducible_def quasi_reducible_def 
  by (force dest: arg_imp_subt)

text \<open>If no root symbol of a left-hand sides is a constructor, then pattern completeness and 
  quasi-reducibility coincide.\<close>
lemma quasi_reducible_iff_pat_complete: fixes L :: "('f,'v)term set" 
  assumes "\<And> l f ls \<tau>s \<tau>. l \<in> L \<Longrightarrow> l = Fun f ls \<Longrightarrow> \<not> f : \<tau>s \<rightarrow> \<tau> in C" 
  shows "pat_complete_lhss C D L \<longleftrightarrow> quasi_reducible C D L" 
proof (standard, rule strong_quasi_reducible_imp_quasi_reducible[OF pat_complete_imp_strong_quasi_reducible])
  assume q: "quasi_reducible C D L" 
  show "pat_complete_lhss C D L" 
    unfolding pat_complete_lhss_def
  proof 
    fix t :: "('f,'v)term" 
    assume t: "t \<in> \<B>(C,D,\<emptyset>)" 
    from q[unfolded quasi_reducible_def, rule_format, OF this]
    obtain tp where tp: "t \<unrhd> tp" and match: "\<exists>l \<in> L. l matches tp" by auto
    show "\<exists>l \<in> L. l matches t" 
    proof (cases "t = tp")
      case True
      thus ?thesis using match by auto
    next
      case False
      from t[unfolded basic_terms_def] obtain f ts ss where t: "t = Fun f ts" and ts: "ts :\<^sub>l ss in \<T>(C,\<emptyset>)" by auto
      from t False tp obtain ti where ti: "ti \<in> set ts" and subt: "ti \<unrhd> tp"
        by (meson Fun_supteq)
      from subt obtain CC where ctxt: "ti = CC \<langle> tp \<rangle>" by auto
      from ti ts obtain s where "ti : s in \<T>(C,\<emptyset>)" unfolding list_all2_conv_all_nth set_conv_nth by auto
      from hastype_context_decompose[OF this[unfolded ctxt]] obtain s where tp: "tp : s in \<T>(C,\<emptyset>)" by blast
      from match[unfolded matches_def] obtain l \<sigma> where l: "l \<in> L" and match: "tp = l \<cdot> \<sigma>" by auto
      show ?thesis
      proof (cases l)
        case (Var x)
        with l show ?thesis unfolding matches_def by (auto intro!: bexI[of _ l])
      next
        case (Fun f ls)
        from tp[unfolded match this, simplified] obtain ss where "f : ss \<rightarrow> s in C" 
          by (meson Fun_hastype hastype_def fun_hastype_def)
        with assms[OF l Fun, of ss s] show ?thesis by auto
      qed
    qed
  qed
qed

end