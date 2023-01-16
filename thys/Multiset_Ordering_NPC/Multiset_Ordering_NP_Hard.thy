section \<open>Deciding the Generalized Multiset Ordering is NP-hard\<close>

text \<open>We prove that satisfiability of conjunctive normal forms (a NP-hard problem) can
  be encoded into a multiset-comparison problem of linear size. Therefore multiset-set comparisons
  are NP-hard as well.\<close>

theory
  Multiset_Ordering_NP_Hard
imports
  Multiset_Ordering_More 
  Propositional_Formula
  Weighted_Path_Order.Multiset_Extension2_Impl (* for executability *)
begin

subsection \<open>Definition of the Encoding\<close>

text \<open>The multiset-elements are either annotated variables or indices (of clauses).
  We basically follow the proof in \<^cite>\<open>"RPO_NPC"\<close> where these elements are encoded as terms 
  (and the relation is some fixed recursive path order).\<close>

datatype Annotation = Unsigned | Positive | Negative

type_synonym 'a ms_elem = "('a \<times> Annotation) + nat" 

fun ms_elem_of_lit :: "'a \<times> bool \<Rightarrow> 'a ms_elem" where
  "ms_elem_of_lit (x,True) = Inl (x,Positive)" 
| "ms_elem_of_lit (x,False) = Inl (x,Negative)" 

definition vars_of_cnf :: "'a cnf \<Rightarrow> 'a list" where
  "vars_of_cnf = (remdups o concat o map (map fst))" 

text \<open>We encode a CNF into a multiset-problem, i.e., a quadruple (xs, ys, S, NS) where
  xs and ys are the lists to compare, and S and NS are underlying relations of the generalized multiset ordering.
  In the encoding, we add the strict relation S to the non-strict relation NS as this is a somewhat more
  natural order. In particular, the relations S and NS are precisely those that are obtained when using
  the mentioned recursive path order of \<^cite>\<open>"RPO_NPC"\<close>.\<close>

definition multiset_problem_of_cnf :: "'a cnf \<Rightarrow> 
  ('a ms_elem list \<times> 
   'a ms_elem list \<times> 
   ('a ms_elem \<times> 'a ms_elem)list \<times> 
   ('a ms_elem \<times> 'a ms_elem)list)" where
  "multiset_problem_of_cnf cnf = (let 
     xs = vars_of_cnf cnf;
     cs = [0 ..< length cnf];
     S = List.maps (\<lambda> i. map (\<lambda> l. (ms_elem_of_lit l, Inr i)) (cnf ! i)) cs;
     NS = List.maps (\<lambda> x. [(Inl (x,Positive), Inl (x,Unsigned)), (Inl (x,Negative), Inl (x,Unsigned))]) xs
     in (List.maps (\<lambda> x. [Inl (x,Positive), Inl (x,Negative)]) xs, 
         map (\<lambda> x. Inl (x,Unsigned)) xs @ map Inr cs,
         S, NS @ S))" 

subsection \<open>Soundness of the Encoding\<close>

lemma multiset_problem_of_cnf:
  assumes "multiset_problem_of_cnf cnf = (left, right, S, NSS)"
  shows "(\<exists> \<beta>. eval_cnf \<beta> cnf)
     \<longleftrightarrow> ((mset left, mset right) \<in> ns_mul_ext (set NSS) (set S))"
  "cnf \<noteq> [] \<Longrightarrow> (\<exists> \<beta>. eval_cnf \<beta> cnf)
     \<longleftrightarrow> ((mset left, mset right) \<in> s_mul_ext (set NSS) (set S))"
proof -
  define xs where "xs = vars_of_cnf cnf" 
  define cs where "cs = [0 ..< length cnf]"
  define NS :: "('a ms_elem \<times> 'a ms_elem)list" where "NS = concat (map (\<lambda> x. [(Inl (x,Positive), Inl (x,Unsigned)), (Inl (x,Negative), Inl (x,Unsigned))]) xs)" 
  note res = assms[unfolded multiset_problem_of_cnf_def Let_def List.maps_def, folded xs_def cs_def]
  have S: "S = concat (map (\<lambda> i. map (\<lambda> l. (ms_elem_of_lit l, Inr i)) (cnf ! i)) cs)" 
    using res by auto
  have NSS: "NSS = NS @ S" unfolding S NS_def using res by auto
  have left: "left = concat (map (\<lambda> x. [Inl (x,Positive), Inl (x,Negative)]) xs)" 
    using res by auto
  let ?nsright = "map (\<lambda> x. Inl (x,Unsigned)) xs" 
  let ?sright = "map Inr cs :: 'a ms_elem list" 
  have right: "right = ?nsright @ ?sright" 
    using res by auto

  text \<open>We first consider completeness: if the formula is sat, then the lists are decreasing w.r.t. the multiset-order.\<close>
  {
    assume "(\<exists> \<beta>. eval_cnf \<beta> cnf)" 
    then obtain \<beta> where sat: "eval \<beta> (formula_of_cnf cnf)" unfolding eval_cnf_def by auto
    define f :: "'a ms_elem \<Rightarrow> bool" where 
      "f = (\<lambda> c. case c of (Inl (x,sign)) \<Rightarrow> (\<beta> x \<longleftrightarrow> sign = Negative))" 
    let ?nsleft = "filter f left" 
    let ?sleft = "filter (Not o f) left" 
    have id_left: "mset left = mset ?nsleft + mset ?sleft" by simp
    have id_right: "mset right = mset ?nsright + mset ?sright" unfolding right by auto
    have nsleft: "?nsleft = map (\<lambda> x. ms_elem_of_lit (x, \<not> (\<beta> x))) xs" 
      unfolding left f_def by (induct xs, auto)
    have sleft: "?sleft = map (\<lambda> x. ms_elem_of_lit (x,\<beta> x)) xs" 
      unfolding left f_def by (induct xs, auto)
    have len: "length ?nsleft = length ?nsright" unfolding nsleft by simp
    {
      fix i
      assume i: "i < length ?nsright" 
      define x where "x = xs ! i" 
      have x: "x \<in> set xs" unfolding x_def using i by auto
      have "(?nsleft ! i, ?nsright ! i) = (ms_elem_of_lit (x,\<not> \<beta> x), Inl (x,Unsigned))" 
        unfolding nsleft x_def using i by auto
      also have "\<dots> \<in> set NS" unfolding NS_def using x by (cases "\<beta> x", auto)
      finally have "(?nsleft ! i, ?nsright ! i) \<in> set NSS" unfolding NSS by auto
    } note non_strict = this
    {
      fix t
      assume "t \<in> set ?sright" 
      then obtain i where i: "i \<in> set cs" and t: "t = Inr i" by auto
      define c where "c = cnf ! i" 
      from i have ii: "i < length cnf" unfolding cs_def by auto
      have c: "c \<in> set cnf" using i unfolding c_def cs_def by auto
      from sat[unfolded formula_of_cnf_def] c 
      have "eval \<beta> (Disj (map formula_of_lit c))" unfolding o_def by auto
      then obtain l where l: "l \<in> set c" and eval: "eval \<beta> (formula_of_lit l)" 
        by auto
      obtain x b where "l = (x, b)" by (cases l, auto)
      with eval have lx: "l = (x, \<beta> x)" by (cases b, auto)
      from l c lx have x: "x \<in> set xs" unfolding xs_def vars_of_cnf_def by force
      have mem: "(ms_elem_of_lit l) \<in> set ?sleft" unfolding sleft lx using x by auto 
      have "\<exists> s \<in> set ?sleft. (s,t) \<in> set S" 
      proof (intro bexI[OF _ mem])
        show "(ms_elem_of_lit l, t) \<in> set S" 
          unfolding t S cs_def using ii l c_def
          by (auto intro!: bexI[of _ i])
      qed
    } note strict = this

    have NS: "((mset left, mset right) \<in> ns_mul_ext (set NSS) (set S))" 
      by (intro ns_mul_ext_intro[OF id_left id_right len non_strict strict])
    {
      assume ne: "cnf \<noteq> []"
      then obtain c where c: "c \<in> set cnf" by (cases cnf, auto)
      with sat[unfolded formula_of_cnf_def]
      have "eval \<beta> (Disj (map formula_of_lit c))" by auto
      then obtain x where x: "x \<in> set xs" 
        using c unfolding vars_of_cnf_def xs_def by (cases c; cases "snd (hd c)"; force)
      have S: "((mset left, mset right) \<in> s_mul_ext (set NSS) (set S))" 
      proof (intro s_mul_ext_intro[OF id_left id_right len non_strict _ strict])
        show "?sleft \<noteq> []"  unfolding sleft using x by auto
      qed
    } note S = this
    note NS S
  } note one_direction = this

  text \<open>We next consider soundness: if the lists are decreasing w.r.t. the multiset-order, then
    the cnf is sat.\<close>
  {   
    assume "((mset left, mset right) \<in> ns_mul_ext (set NSS) (set S))
      \<or> ((mset left, mset right) \<in> s_mul_ext (set NSS) (set S))" 
    hence "((mset left, mset right) \<in> ns_mul_ext (set NSS) (set S))"
      using s_ns_mul_ext by auto
    also have "ns_mul_ext (set NSS) (set S) = ns_mul_ext (set NS) (set S)" 
      unfolding NSS set_append by (rule ns_mul_ext_NS_union_S)
    finally have "(mset left, mset right) \<in> ns_mul_ext (set NS) (set S)" .
    from ns_mul_ext_elim[OF this]
    obtain ns_left s_left ns_right s_right
      where id_left: "mset left = mset ns_left + mset s_left"
       and id_right: "mset right = mset ns_right + mset s_right"
       and len: "length ns_left = length ns_right"
       and ns: "\<And> i. i<length ns_right \<Longrightarrow> (ns_left ! i, ns_right ! i) \<in> set NS"
       and s: "\<And> t. t\<in>set s_right \<Longrightarrow> \<exists>s\<in>set s_left. (s, t) \<in> set S" by blast    

    text \<open>This is the satisfying assignment\<close>
    define \<beta> where "\<beta> x = (ms_elem_of_lit (x,True) \<in> set s_left)" for x 
    {
      fix c
      assume ccnf: "c \<in> set cnf" 
      then obtain i where i: "i \<in> set cs" 
        and c_def: "c = cnf ! i" 
        and ii: "i < length cnf"  
        unfolding cs_def set_conv_nth by force

      from i have "Inr i \<in># mset right" unfolding right by auto
      from this[unfolded id_right] have "Inr i \<in> set ns_right \<or> Inr i \<in> set s_right" by auto
      hence "Inr i \<in> set s_right" using ns[unfolded NSS NS_def] 
        unfolding set_conv_nth[of ns_right] by force
      from s[OF this] obtain s where sleft: "s \<in> set s_left" and si: "(s, Inr i) \<in> set S" by auto
      from si[unfolded S, simplified] obtain l where
        lc: "l \<in> set c" and sl: "s = ms_elem_of_lit l" unfolding c_def cs_def using ii by blast
      obtain x b where lxb: "l = (x,b)" by force
      from lc lxb ccnf have x: "x \<in> set xs" unfolding xs_def vars_of_cnf_def by force
      have "\<exists>l\<in>set c. eval \<beta> (formula_of_lit l)"
      proof (intro bexI[OF _ lc])
        from sleft[unfolded sl lxb] 
        have mem: "ms_elem_of_lit (x, b) \<in> set s_left" by auto
        have "\<beta> x = b" 
        proof (cases b)
          case True
          thus ?thesis unfolding \<beta>_def using mem by auto
        next
          case False
          show ?thesis
          proof (rule ccontr)
            assume "\<beta> x \<noteq> b" 
            with False have "\<beta> x" by auto
            with False mem 
            have "ms_elem_of_lit (x, True) \<in> set s_left"
              "ms_elem_of_lit (x, False) \<in> set s_left"
              unfolding \<beta>_def by auto
            hence mem: "ms_elem_of_lit (x, b) \<in> set s_left" for b by (cases b, auto)

            have dist: "distinct left" unfolding left
              by (intro distinct_concat, auto simp: distinct_map xs_def vars_of_cnf_def cs_def intro!: inj_onI)
            from id_left have "mset left = mset (ns_left @ s_left)" by auto
            from mset_eq_imp_distinct_iff[OF this] dist have "set ns_left \<inter> set s_left = {}" by auto
            with mem have nmem: "ms_elem_of_lit (x,b) \<notin> set ns_left" for b by auto
            have "Inl (x, Unsigned) \<in># mset right" unfolding right using x by auto
            from this[unfolded id_right] 
            have "Inl (x, Unsigned) \<in> set ns_right \<union> set s_right" by auto
            with s[unfolded S] have "Inl (x, Unsigned) \<in> set ns_right" by auto
            with ns obtain s where pair: "(s, Inl (x, Unsigned)) \<in> set NS" and sns: "s \<in> set ns_left" 
              unfolding set_conv_nth[of ns_right] using len by force
            from pair[unfolded NSS] have pair: "(s, Inl (x, Unsigned)) \<in> set NS" by auto
            from pair[unfolded NS_def, simplified] have "s = Inl (x, Positive) \<or> s = Inl (x, Negative)" by auto
            from sns this nmem[of True] nmem[of False] show False by auto
          qed
        qed
        thus "eval \<beta> (formula_of_lit l)" unfolding lxb by (cases b, auto)
      qed
    }
    hence "eval \<beta> (formula_of_cnf cnf)" unfolding formula_of_cnf_def o_def by auto
    hence "\<exists> \<beta>. eval_cnf \<beta> cnf" unfolding eval_cnf_def by auto
  } note other_direction = this

  from one_direction other_direction show "(\<exists> \<beta>. eval_cnf \<beta> cnf)
     \<longleftrightarrow> ((mset left, mset right) \<in> ns_mul_ext (set NSS) (set S))" 
    by blast
  show "cnf \<noteq> [] \<Longrightarrow> (\<exists> \<beta>. eval_cnf \<beta> cnf)
     \<longleftrightarrow> ((mset left, mset right) \<in> s_mul_ext (set NSS) (set S))" 
    using one_direction other_direction by blast
qed

lemma multiset_problem_of_cnf_mul_ext:
  assumes "multiset_problem_of_cnf cnf = (xs, ys, S, NS)"
  and non_trivial: "cnf \<noteq> []" 
  shows "(\<exists> \<beta>. eval_cnf \<beta> cnf)
     \<longleftrightarrow> mul_ext (\<lambda> a b. ((a,b) \<in> set S, (a,b) \<in> set NS)) xs ys = (True,True)"
proof -
  have "(\<exists> \<beta>. eval_cnf \<beta> cnf) = ((\<exists> \<beta>. eval_cnf \<beta> cnf) \<and> (\<exists> \<beta>. eval_cnf \<beta> cnf))" 
    by simp
  also have "\<dots> = (((mset xs, mset ys) \<in> s_mul_ext (set NS) (set S)) \<and> ((mset xs, mset ys) \<in> ns_mul_ext (set NS) (set S)))" 
    by (subst multiset_problem_of_cnf(1)[symmetric, OF assms(1)], subst multiset_problem_of_cnf(2)[symmetric, OF assms], simp)
  also have "\<dots> = (mul_ext (\<lambda> a b. ((a,b) \<in> set S, (a,b) \<in> set NS)) xs ys = (True,True))" 
    unfolding mul_ext_def Let_def by auto
  finally show ?thesis .
qed

subsection \<open>Size of Encoding is Linear\<close>

lemma size_of_multiset_problem_of_cnf: assumes "multiset_problem_of_cnf cnf = (xs, ys, S, NS)" 
  and "size_cnf cnf = s" 
shows "length xs \<le> 2 * s" "length ys \<le> 2 * s" "length S \<le> s" "length NS \<le> 3 * s" 
proof -
  define vs where "vs = vars_of_cnf cnf" 
  have lvs: "length vs \<le> s" unfolding assms(2)[symmetric] vs_def vars_of_cnf_def o_def size_cnf_def
    by (rule order.trans[OF length_remdups_leq], induct cnf, auto)
  have lcnf: "length cnf \<le> s" using assms(2) unfolding size_cnf_def by auto
  note res = assms(1)[unfolded multiset_problem_of_cnf_def Let_def List.maps_def, folded vs_def, simplified]
  have xs: "xs = concat (map (\<lambda>x. [Inl (x, Positive), Inl (x, Negative)]) vs)" using res by auto
  have "length xs \<le> length vs + length vs" unfolding xs by (induct vs, auto)
  also have "\<dots> \<le> 2 * s" using lvs by auto
  finally show "length xs \<le> 2 * s" .
  have "length ys = length (map (\<lambda>x. Inl (x, Unsigned)) vs @ map Inr [0..<length cnf])" using res by auto
  also have "\<dots> \<le> 2 * s" using lvs lcnf by auto
  finally show "length ys \<le> 2 * s" .
  have S: "S = concat (map (\<lambda>i. map (\<lambda>l. (ms_elem_of_lit l, Inr i)) (cnf ! i)) [0..<length cnf])" 
    using res by simp
  have "length S = sum_list (map length cnf)" 
    unfolding S length_concat map_map o_def length_map 
    by (rule arg_cong[of _ _ sum_list], intro nth_equalityI, auto)
  also have "\<dots> \<le> s" using assms(2) unfolding size_cnf_def by auto
  finally show S: "length S \<le> s" .
  have NS: "NS = concat (map (\<lambda>x. [(Inl (x, Positive), Inl (x, Unsigned)), (Inl (x, Annotation.Negative), Inl (x, Unsigned))]) vs) @ S" 
    using res by auto
  have "length NS = 2 * length vs + length S" 
    unfolding NS by (induct vs, auto)
  also have "\<dots> \<le> 3 * s" using lvs S by auto
  finally show "length NS \<le> 3 * s" .
qed

subsection \<open>Check Executability\<close>

value (code) "case multiset_problem_of_cnf [
  [(''x'',True),(''y'',False)],              \<comment> \<open>clause 0\<close>
  [(''x'',False)],                           \<comment> \<open>clause 1\<close>
  [(''y'',True),(''z'',True)],               \<comment> \<open>clause 2\<close>
  [(''x'',True),(''y'',True),(''z'',False)]] \<comment> \<open>clause 3\<close> 
   of (left,right,S,NS) \<Rightarrow> (''SAT: '', mul_ext (\<lambda> x y. ((x,y) \<in> set S, (x,y) \<in> set NS)) left right = (True,True), 
      ''Encoding: '', left, '' >mul '', right, ''strict element order: '', S,''non-strict: '', NS)" 

end
