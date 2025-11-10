theory Finite_Constr_Nondet_Alg
  imports Pattern_Completeness.Pattern_Completeness_List
begin

lemma diff_ground_term_to_diff_pos: assumes "s \<noteq> t" "vars s = {}" "vars t = {}" 
  shows "\<exists> p f g. p \<in> poss s \<inter> poss t \<and> root (s |_ p) = Some f \<and> root (t |_ p) = Some g \<and> f \<noteq> g" 
  using assms
proof (induct s arbitrary: t)
  case (Fun f ss t)
  from Fun(4) obtain g ts where t: "t = Fun g ts" by (cases t, auto)
  show ?case 
  proof (cases "(f,length ss) = (g,length ts)")
    case False
    thus ?thesis unfolding t by (intro exI[of _ Nil], auto)
  next
    case True
    with Fun(2)[unfolded t] True obtain i where i: "i < length ss" and "ss ! i \<noteq> ts ! i" 
      by (auto simp: list_eq_nth_eq)
    with True Fun(3-) t
    have "ss ! i \<in> set ss" "ss ! i \<noteq> ts ! i"  "vars (ss ! i) = {}" "vars (ts ! i) = {}" 
      by auto
    from Fun(1)[OF this] obtain p f g where "p \<in> poss (ss ! i) \<inter> poss (ts ! i)" 
      "root (ss ! i |_ p) = Some f" "root (ts ! i |_ p) = Some g \<and> f \<noteq> g" by blast
    thus ?thesis 
      unfolding t using i True by (intro exI[of _ "i # p"], auto)
  qed
qed auto


definition lhs_var_form_match :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "lhs_var_form_match mp = (mp \<subseteq> UNIV \<times> range Var)" 

definition lhs_var_form_pat :: "('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "lhs_var_form_pat p = (\<forall> mp \<in> p. lhs_var_form_match mp)"


context pattern_completeness_context
begin

lemma lhs_var_form_match_choice: assumes "lhs_var_form_match mp" 
  shows "\<not> match_complete_wrt \<sigma> mp \<longleftrightarrow> (\<exists> s t x. {(s,x), (t,x)} \<subseteq> mp \<and> s \<cdot> \<sigma> \<noteq> t \<cdot> \<sigma>) " (is "?l = ?r")
proof 
  assume ?r
  then obtain s t x where *: "(s,x) \<in> mp" "(t,x) \<in> mp" "s \<cdot> \<sigma> \<noteq> t \<cdot> \<sigma>" by auto
  show ?l
  proof
    assume "match_complete_wrt \<sigma> mp" 
    from this[unfolded match_complete_wrt_def] obtain \<mu> 
      where "(t, l) \<in> mp \<Longrightarrow> t \<cdot> \<sigma> = l \<cdot> \<mu>" for t l by auto
    from this[of s x] this[of t x] * show False by auto
  qed
next
  define \<mu> where "\<mu> x = (let s = (SOME s. (s,Var x) \<in> mp) in s \<cdot> \<sigma>)" for x
  assume ?l
  from this[unfolded match_complete_wrt_def] obtain 
    t l where tl: "(t,l) \<in> mp" and diff: "t \<cdot> \<sigma> \<noteq> l \<cdot> \<mu>" by blast
  from assms[unfolded lhs_var_form_match_def] tl obtain x 
    where l: "l = Var x" by auto
  from tl l have tx: "(t,Var x) \<in> mp" by auto
  from diff l have diff: "\<mu> x \<noteq> t \<cdot> \<sigma>" by auto
  define s where "s = (SOME s. (s,Var x) \<in> mp)" 
  have s: "(s,Var x) \<in> mp" unfolding s_def by (rule someI[of _ t], rule tx)
  have eq: "\<mu> x = s \<cdot> \<sigma>" unfolding \<mu>_def Let_def s_def ..
  have "s \<cdot> \<sigma> \<noteq> t \<cdot> \<sigma>" using eq diff by auto
  with s tx show ?r by auto
qed


lemma not_pat_compl_witness: "\<not> pat_complete C pp \<longleftrightarrow> 
  (\<exists> \<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C). \<forall> mp \<in> pp. \<not> match_complete_wrt \<sigma> mp)" 
  unfolding pat_complete_def by auto

lemma lhs_var_form_pat_choice: assumes "lhs_var_form_pat pp" 
  shows "\<not> pat_complete C pp \<longleftrightarrow> 
     (\<exists> \<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C). \<forall> mp \<in> pp. \<exists> s t x. {(s,x), (t,x)} \<subseteq> mp \<and> s \<cdot> \<sigma> \<noteq> t \<cdot> \<sigma>)" 
  unfolding not_pat_compl_witness
proof (intro ex_cong ball_cong refl, goal_cases)
  case (1 \<sigma> mp)
  with assms have mp: "lhs_var_form_match mp" unfolding lhs_var_form_pat_def by auto
  show ?case unfolding lhs_var_form_match_choice[OF mp] ..
qed

text \<open>This lemma shows that for constructor-finite-var-forms, one can disprove pattern completeness
  by finding witness terms and positions for each mp within some pp that result in a clash'-application.
  Hence, one can non-deterministically choose to instantiate' along these positions to
  quickly find the counter-examples. (A rough bound on the number
  of required instantiations is @{term "2 * card pp * card (dom C)"}:
   one needs 1 position for each mp in pp, and each position is at most @{term "dom C"} long, and
   we need 2 expansions, namely for s and for t)
  Thus, in a non-deterministic algorithm one can limit the number of instantiate' steps by a polynomial
  bound, and therefore obtains an overall non-deterministic poly-time algorithm.\<close>
lemma lhs_var_form_pat_pos_diff: assumes "lhs_var_form_pat pp" 
  shows "\<not> pat_complete C pp \<longleftrightarrow> (\<exists> \<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C). \<forall> mp \<in> pp. \<exists> s t x p f g. 
      {(s,x), (t,x)} \<subseteq> mp \<and> p \<in> poss (s \<cdot> \<sigma>) \<inter> poss (t \<cdot> \<sigma>) \<and> root (s \<cdot> \<sigma> |_ p) = Some f
           \<and> root (t \<cdot> \<sigma> |_ p) = Some g \<and> f \<noteq> g)" 
  unfolding lhs_var_form_pat_choice[OF assms] ex_simps
proof (intro ex_cong ball_cong refl ex_cong1, goal_cases)
  case (1 \<sigma> mp s t)
  {
    fix u
    assume "u \<in> {s,t}" 
    with 1 have "vars u \<subseteq> tvars_pat pp" unfolding tvars_pat_def tvars_match_def by auto
    hence "vars (u \<cdot> \<sigma>) \<subseteq> \<Union> (vars ` \<sigma> ` tvars_pat pp)" 
      unfolding vars_term_subst by auto
    also have "\<dots> = {}" 
    proof -
      {
        fix x 
        assume "x \<in> tvars_pat pp"
        hence "\<sigma> x : snd x in \<T>(C)" using \<open>\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C)\<close>
          by (simp add: hastypeI sorted_map.sorted_map)
        hence "vars (\<sigma> x) = {}" by (rule hastype_in_Term_empty_imp_vars)
      }
      thus ?thesis by auto
    qed
    finally have "vars (u \<cdot> \<sigma>) = {}" by auto
  } note ground = this
  show ?case (is "?l = ?r")
  proof
    assume "s \<cdot> \<sigma> \<noteq> t \<cdot> \<sigma>" 
    from diff_ground_term_to_diff_pos[OF this ground ground]
    show ?r by auto
  qed auto
qed

end
  
end
