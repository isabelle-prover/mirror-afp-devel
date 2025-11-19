section\<open>Orthogonality\<close>

theory Orthogonality
  imports 
    Critical_Pairs
    Parallel_Rewriting
begin

text \<open>This theory contains the result, that weak orthogonality implies confluence.\<close>

text \<open>We prove the diamond property of @{const par_rstep} for weakly orthogonal systems.\<close>       
context
  fixes ren :: "'v :: infinite renaming2" 
begin
lemma weakly_orthogonal_main: fixes R :: "('f,'v)trs"
  assumes st1: "(s,t1) \<in> par_rstep R" and st2: "(s,t2) \<in> par_rstep R" and weak_ortho:
    "left_linear_trs R" "\<And> b l r. (b,l,r) \<in> critical_pairs ren R R \<Longrightarrow> l = r" 
    and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "\<exists> u. (t1,u) \<in> par_rstep R \<and> (t2,u) \<in> par_rstep R"
proof -
  let ?R = "par_rstep R"
  let ?CP = "critical_pairs ren R R"
  {
    fix ls ts \<sigma> f r
    assume below: "\<And> i. i < length ls \<Longrightarrow> ((map (\<lambda> l. l \<cdot> \<sigma>) ls) ! i, ts ! i) \<in> ?R"
      and rule: "(Fun f ls, r) \<in> R"
      and len: "length ts = length ls"
    let ?ls = "map (\<lambda> l. l \<cdot> \<sigma>) ls"
    from weak_ortho(1) rule have lin: "linear_term (Fun f ls)" unfolding left_linear_trs_def by auto
    let ?p1 = "\<lambda> \<tau> i. ts ! i = ls ! i \<cdot> \<tau> \<and> (\<forall> x \<in> vars_term (ls ! i). (\<sigma> x, \<tau> x) \<in> par_rstep R)"
    let ?p2 = "\<lambda> \<tau> i. (\<exists> C l'' l' r'. ls ! i = C\<langle>l''\<rangle> \<and> is_Fun l'' \<and> (l',r') \<in> R \<and> (l'' \<cdot> \<sigma> = l' \<cdot> \<tau>) \<and> ((C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> \<tau> \<rangle>, ts ! i) \<in> par_rstep R)"
    {
      fix i
      assume i: "i < length ls"
      then have i2: "i < length ts" using len by simp
      from below[OF i] have step: "(ls ! i \<cdot> \<sigma>, ts ! i) \<in> ?R" using i by auto
      from i have mem: "ls ! i \<in> set ls" by auto
      from lin i have lin: "linear_term (ls ! i)" by auto
      from par_rstep_linear_subst[OF lin step] have "\<exists> \<tau>. ?p1 \<tau> i \<or> ?p2 \<tau> i" .
    } note p12 = this
    have "\<exists> u. (r \<cdot> \<sigma>, u) \<in> ?R \<and> (Fun f ts, u) \<in> ?R"
    proof (cases "\<exists> i \<tau>. i < length ls \<and> ?p2 \<tau> i")
      case True
      then obtain i \<tau> where i: "i < length ls" and p2: "?p2 \<tau> i" by blast
      from p2 obtain C l'' l' r' where lsi: "ls ! i = C \<langle> l'' \<rangle>" and l'': "is_Fun (l'')" and lr': "(l',r') \<in> R"
        and unif: "l'' \<cdot> \<sigma> = l' \<cdot> \<tau>" and tsi: "((C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> \<tau> \<rangle>, ts ! i) \<in> ?R"  by blast
      from id_take_nth_drop[OF i] obtain bef aft where ls: "ls = bef @ C \<langle> l'' \<rangle> # aft" and bef: "bef = take i ls" unfolding lsi by auto
      from i bef have bef: "length bef = i" by auto
      let ?C = "More f bef C aft"
      from bef have hp: "hole_pos ?C = i # hole_pos C" by simp
      have fls: "Fun f ls = ?C \<langle> l'' \<rangle>" unfolding ls by simp
      from mgu_vd_complete[OF unif] obtain \<mu>1 \<mu>2 \<delta> where 
        mgu: "mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)" and id: "l'' \<cdot> \<mu>1 = l' \<cdot> \<mu>2" 
        and sigma: "\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and tau: "\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" by blast
      let ?sig = "map (\<lambda> s. s \<cdot> \<sigma>)"
      let ?r = "(C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> \<tau>\<rangle>"
      let ?bra = "?sig bef @ ?r # ?sig aft"
      from weak_ortho(2)[OF critical_pairsI[OF rule lr' fls l'' mgu refl refl refl]]      
      have id: "r \<cdot> \<sigma> = (?C \<cdot>\<^sub>c \<sigma>) \<langle>r' \<cdot> \<tau> \<rangle>" unfolding sigma tau by simp
      also have "... = Fun f ?bra" by simp
      also have "(..., Fun f ts) \<in> ?R"
      proof (rule par_rstep.par_step_fun)
        show "length ?bra = length ts" unfolding len unfolding ls by simp
      next
        fix j
        assume j: "j < length ts"
        show "(?bra ! j, ts ! j) \<in> ?R"
        proof (cases "j = i")
          case True
          then have "?bra ! j = ?r" using bef i by (simp add: nth_append)
          then show ?thesis using tsi True by simp
        next
          case False
          then have "?bra ! j = (?sig bef @ (C \<langle> l'' \<rangle> \<cdot> \<sigma>) # ?sig aft) ! j" using False bef i by (simp add: nth_append)
          also have "... = ?sig ls ! j" unfolding ls by simp
          finally show ?thesis
            using below[OF j[unfolded len]] by auto
        qed
      qed
      finally have step: "(r \<cdot> \<sigma>, Fun f ts) \<in> ?R" .
      show "\<exists> u. (r \<cdot> \<sigma>, u) \<in> ?R \<and> (Fun f ts, u) \<in> ?R" 
        by (rule exI, rule conjI[OF step par_rstep_refl])
    next
      case False
      with p12
      have "\<forall> i. (\<exists> \<tau>. i < length ls \<longrightarrow> ?p1 \<tau> i)" by blast
      from choice[OF this] obtain tau where tau: "\<And> i. i < length ls \<Longrightarrow> ?p1 (tau i) i" by blast
      from lin have "is_partition (map vars_term ls)" by auto
      from subst_merge[OF this, of tau] obtain \<tau> where \<tau>: "\<And> i x. i < length ls \<Longrightarrow> x \<in> vars_term (ls ! i) \<Longrightarrow> \<tau> x = tau i x"
        by blast
      obtain \<delta> where delta: "\<delta> = (\<lambda> x. if x \<in> vars_term (Fun f ls) then \<tau> x else \<sigma> x)" by auto
      {
        fix i
        assume i: "i < length ls"
        from tau[OF i] have p: "?p1 (tau i) i" .
        have id1: "ls ! i \<cdot> tau i = ls ! i \<cdot> \<tau>"
          by (rule term_subst_eq[OF \<tau>[OF i, symmetric]])
        have id2: "... = ls ! i \<cdot> \<delta>"
          by (rule term_subst_eq, unfold delta, insert i, auto)
        have p: "?p1 \<delta> i" using p using \<tau>[OF i] unfolding id1 id2 using id2 unfolding delta by auto
      } note delt = this
      have r_delt: "(r \<cdot> \<sigma>, r \<cdot> \<delta>) \<in> ?R"
      proof (rule all_ctxt_closed_subst_step)
        fix x
        assume x: "x \<in> vars_term r"
        show "(\<sigma> x, \<delta> x) \<in> ?R" 
        proof (cases "x \<in> vars_term (Fun f ls)")
          case True
          then obtain l where l: "l \<in> set ls" and x: "x \<in> vars_term l" by auto
          from l[unfolded set_conv_nth] obtain i where i: "i < length ls" and l: "l = ls ! i" by auto
          from delt[OF i] x l show ?thesis by auto
        next
          case False
          then have "\<delta> x = \<sigma> x" unfolding delta by auto
          then show ?thesis by auto
        qed
      qed auto
      {
        let ?ls = "map (\<lambda> l. l \<cdot> \<delta>) ls"
        have "ts = map (\<lambda> i. ts ! i) [0 ..< length ts]" by (rule map_nth[symmetric])
        also have "... = map (\<lambda> i. ts ! i) [0 ..< length ls]" unfolding len by simp
        also have "... = map (\<lambda> i. ?ls ! i) [0 ..< length ?ls]"
          by (rule nth_map_conv, insert delt[THEN conjunct1], auto)
        also have "... = ?ls"
          by (rule map_nth)
        finally have "Fun f ts = Fun f ls \<cdot> \<delta>" by simp
      } note id = this
      have l_delt: "(Fun f ts, r \<cdot> \<delta>) \<in> ?R" unfolding id
        by (rule par_rstep.root_step[OF rule])
      show "\<exists> u. (r \<cdot> \<sigma>, u) \<in> ?R \<and> (Fun f ts, u) \<in> ?R"
        by (intro exI conjI, rule r_delt, rule l_delt)
    qed
  } note root_arg = this
  from st1 st2 show ?thesis
  proof (induct arbitrary: t2 rule: par_rstep.induct)
    case (par_step_var x t2)
    have t2: "t2 = Var x" 
      by (rule wf_trs_par_rstep[OF wf par_step_var])
    show "\<exists> u. (Var x,u) \<in> ?R \<and> (t2, u) \<in> ?R" unfolding t2
      by (intro conjI exI par_rstep.par_step_var, auto)
  next
    case (par_step_fun ts1 ss f t2)
    note IH = this
    show ?case using IH(4)
    proof (cases rule: par_rstep.cases)
      case (par_step_fun ts2)
      from IH(3) par_step_fun(3) have len: "length ts2 = length ts1" by simp
      {
        fix i
        assume i: "i < length ts1"
        then have i2: "i < length ts2" using len by simp
        from par_step_fun(2)[OF i2] have step2: "(ss ! i, ts2 ! i) \<in> ?R" .
        from IH(2)[OF i step2] have "\<exists> u. (ts1 ! i, u) \<in> ?R \<and> (ts2 ! i, u) \<in> ?R" .
      }
      then have "\<forall> i. \<exists> u. (i < length ts1 \<longrightarrow> (ts1 ! i, u) \<in> ?R \<and> (ts2 ! i, u) \<in> ?R)" by blast
      from choice[OF this] obtain us where join: "\<And> i. i < length ts1 \<Longrightarrow> (ts1 ! i, us i) \<in> ?R \<and> (ts2 ! i, us i) \<in> ?R" by blast
      let ?us = "map us [0 ..< length ts1]"
      {
        fix i
        assume i: "i < length ts1"
        from join[OF this] i have " (ts1 ! i, ?us ! i) \<in> ?R" "(ts2 ! i, ?us ! i) \<in> ?R" by auto 
      } note join = this
      let ?u = "Fun f ?us"
      have step1: "(Fun f ts1, ?u) \<in> ?R"
        by (rule par_rstep.par_step_fun[OF join(1)], auto)
      have step2: "(Fun f ts2, ?u) \<in> ?R"
        by (rule par_rstep.par_step_fun[OF join(2)], insert len, auto)
      show ?thesis unfolding par_step_fun(1) using step1 step2 by blast
    next
      case (root_step l r \<sigma>)
      from wf[OF root_step(3)] root_step(1) obtain ls where l: "l = Fun f ls"
        by auto
      from root_step(1) l have ss: "ss = map (\<lambda> l. l \<cdot> \<sigma>) ls" (is "_ = ?ls") by simp
      from root_step(3) l have rule: "(Fun f ls, r) \<in> R" by simp
      from root_step(2) have t2: "t2 = r \<cdot> \<sigma>" .
      from par_step_fun(3) ss have len: "length ts1 = length ls" by simp
      from root_arg[OF par_step_fun(1)[unfolded ss len] rule len]
      show ?thesis unfolding t2 by blast
    qed
  next
    case (root_step l r \<sigma>)
    note IH = this
    from wf[OF IH(1)] IH(1) obtain f ls where l: "l = Fun f ls" and rule: "(Fun f ls,r) \<in> R" 
      by (cases l, auto)
    from IH(2)[unfolded l] show ?case
    proof (cases rule: par_rstep.cases)
      case (par_step_var x)
      then show ?thesis by simp
    next
      case (root_step l' r' \<tau>)
      then have t2: "t2 = r' \<cdot> \<tau>" by auto
      have id: "Fun f ls = \<box>\<langle>Fun f ls\<rangle>" by simp
      from mgu_vd_complete[OF root_step(1), of ren] obtain mu1 mu2 delta where 
        mgu: "mgu_vd ren (Fun f ls) l' = Some (mu1, mu2)" and sigma: "\<sigma> = mu1 \<circ>\<^sub>s delta"
        and tau: "\<tau> = mu2 \<circ>\<^sub>s delta" by auto
      from weak_ortho(2)[OF critical_pairsI[OF rule root_step(3) id _ mgu refl refl]]
      have "r \<cdot> mu1 = r' \<cdot> mu2" by simp
      then have id: "r \<cdot> \<sigma> = r' \<cdot> \<tau>" unfolding sigma tau by simp
      show ?thesis unfolding t2 id by auto
    next
      case (par_step_fun ts ls' g)
      then have ls': "ls' = map (\<lambda> l. l \<cdot> \<sigma>) ls" and g: "g = f" and len: "length ts = length ls" by auto
      note par_step_fun = par_step_fun[unfolded ls' g len]
      from root_arg[OF par_step_fun(3) rule len]
      show ?thesis unfolding par_step_fun(2) .
    qed
  qed
qed


lemma weakly_orthogonal_par_rstep_CR:
  assumes weak_ortho: "left_linear_trs R" "\<And> b l r. (b,l,r) \<in> critical_pairs ren R R \<Longrightarrow> l = r" 
    and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "CR (par_rstep R)"
proof -
  let ?R = "par_rstep R"
  from weakly_orthogonal_main[OF _ _ weak_ortho wf] 
  have diamond: "\<And> s t1 t2. (s,t1) \<in> ?R \<Longrightarrow> (s,t2) \<in> ?R \<Longrightarrow> \<exists> u. (t1,u) \<in> ?R \<and> (t2,u) \<in> ?R" .
  show ?thesis
    by (rule diamond_imp_CR, rule diamond_I, insert diamond, blast)
qed

lemma weakly_orthogonal_rstep_CR:
  assumes weak_ortho: "left_linear_trs R" "\<And> b l r. (b,l,r) \<in> critical_pairs ren R R \<Longrightarrow> l = r" 
    and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "CR (rstep R)"
proof -
  from weakly_orthogonal_par_rstep_CR[OF assms] have "CR (par_rstep R)" .
  then show ?thesis unfolding CR_on_def join_def rtrancl_converse par_rsteps_rsteps .
qed

end
end