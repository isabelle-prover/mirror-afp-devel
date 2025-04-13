(* This theory provides executable versions for various rewrite relations, including
  parallel rewriting, multistep rewriting and parallel rewriting with variable restrictions
  *)

subsection \<open>Implementation of Parallel Rewriting With Variable Restriction\<close>

theory Rewrite_Relations_Impl
  imports 
    Trs_Impl
    Parallel_Rewriting
    Multistep
begin 

subsubsection\<open>Checking a Single Parallel Rewrite Step with Variable Restriction\<close>

context 
  fixes R :: "('f,'v)rules" and V :: "'v set"  
begin
fun is_par_rstep_var_restr :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "is_par_rstep_var_restr (Fun f ss) (Fun g ts) =
    (Fun f ss = Fun g ts \<or> 
    vars_term (Fun g ts) \<inter> V = {} \<and> (Fun f ss, Fun g ts) \<in> rrstep (set R) \<or>
    (f = g \<and> length ss = length ts \<and> list_all2 is_par_rstep_var_restr ss ts))"
  | "is_par_rstep_var_restr s t = (s = t \<or> vars_term t \<inter> V = {} \<and> (s,t) \<in> rrstep (set R))"

lemma is_par_rstep_code_helper: "vars_term t \<inter> V = {} \<longleftrightarrow>
  (\<forall> x \<in> set (vars_term_list t). x \<notin> V)" 
  by auto

lemmas is_par_rstep_var_restr_code[code] = is_par_rstep_var_restr.simps[unfolded is_par_rstep_code_helper]

lemma is_par_rstep_var_restr[simp]:
  "is_par_rstep_var_restr s t \<longleftrightarrow> (s, t) \<in> par_rstep_var_restr (set R) V"
proof 
  let ?Prop = "\<lambda> s t. s = t \<or> vars_term t \<inter> V = {} \<and> (s,t) \<in> rrstep (set R)" 
  {
    fix s t
    assume "?Prop s t" 
    hence "\<exists> C infos. (s, t) \<in> par_rstep_mctxt (set R) C infos \<and> vars_below_hole t C \<inter> V = {}"
    proof 
      assume "s = t" 
      thus ?thesis by (intro exI[of _ "mctxt_of_term s"] exI[of _ Nil], auto simp: par_rstep_mctxt_reflI)
    next
      assume "vars_term t \<inter> V = {} \<and> (s,t) \<in> rrstep (set R)"      
      then obtain l r \<sigma> where id: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" and 
        lr: "(l,r) \<in> set R" and
        vars: "vars_term t \<inter> V = {}" 
        by (metis rrstepE)      
      thus ?thesis by (intro exI[of _ MHole] exI[of _ "[Par_Info s t (l,r)]"], auto intro: par_rstep_mctxt_MHoleI)
    qed
  } note Prop = this  
  {
    assume "is_par_rstep_var_restr s t" 
    hence "\<exists> C infos. (s, t) \<in> par_rstep_mctxt (set R) C infos \<and> vars_below_hole t C \<inter> V = {}"
    proof (induct rule: is_par_rstep_var_restr.induct[])
      case "2_1" 
      thus ?case by (intro Prop, auto)
    next
      case "2_2" 
      thus ?case by (intro Prop, auto)
    next
      case (1 f ss g ts)
      show ?case
      proof (cases "?Prop (Fun f ss) (Fun g ts)")
        case True
        thus ?thesis using Prop by auto
      next
        case False
        with 1 have args: "f = g" "length ss = length ts" "list_all2 is_par_rstep_var_restr ss ts"
          by (auto split: if_splits)
        let ?P = "\<lambda> i C infos. (ss ! i, ts ! i) \<in> par_rstep_mctxt (set R) C infos \<and> vars_below_hole (ts ! i) C \<subseteq> (UNIV - V)" 
        { fix i
          assume i:"i < length ss"
          then have si:"ss ! i \<in> set ss" by auto
          from i args(2) have ti:"ts ! i \<in> set ts" by auto
          from args(3) have iprv:"is_par_rstep_var_restr (ss ! i) (ts ! i)" using i list_all2_nthD by blast
          with 1(1)[of "ss!i" "ts!i"] have pp:"\<exists>C infos. ?P i C infos" 
            using local.args(1) local.args(2) using si ti by blast
        } 
        hence "\<forall> i. \<exists> C infos. i < length ss \<longrightarrow> ?P i C infos" by blast
        from choice[OF this] obtain C where "\<forall> i. \<exists> infos. i < length ss \<longrightarrow> ?P i (C i) infos" by blast
        from choice[OF this] obtain infos where IH: "\<And> i. i < length ss \<Longrightarrow> ?P i (C i) (infos i)" by blast
        let ?C = "MFun f (map C [0..<length ss])" 
        let ?infos = "concat (map infos [0..<length ss])" 
        show ?thesis 
        proof (intro exI[of _ ?C] exI[of _ ?infos] conjI)
          show "vars_below_hole (Fun g ts) ?C \<inter> V = {}" using IH args(2) unfolding args(1)
            by (subst vars_below_hole_Fun; force)
          show "(Fun f ss, Fun g ts) \<in> par_rstep_mctxt (set R) ?C ?infos" unfolding args(1) using args(2) IH
            by (intro par_rstep_mctxt_funI, auto)
        qed
      qed
    qed
    thus " (s, t) \<in> par_rstep_var_restr (set R) V" unfolding par_rstep_var_restr_def by auto
  }
  {
    assume "(s, t) \<in> par_rstep_var_restr (set R) V" 
    from this[unfolded par_rstep_var_restr_def] obtain C infos where
      st: "(s, t) \<in> par_rstep_mctxt (set R) C infos" and vars: "vars_below_hole t C \<inter> V = {}" by auto
    thus "is_par_rstep_var_restr s t" 
    proof (induct C arbitrary: s t infos)
      case (MVar x)
      from par_rstep_mctxt_MVarE[OF MVar(1)]
      have "s = Var x" "t = Var x" by auto
      thus ?case by simp
    next
      case MHole
      from par_rstep_mctxt_MHoleE[OF MHole(1)]
      have "(s,t) \<in> rrstep (set R)" by auto  
      then show ?case using MHole(2) by (cases s; cases t; auto)
    next
      case (MFun f Cs)
      from par_rstep_mctxt_MFunD[OF MFun(2)]
      obtain ss ts Infos
        where s: "s = Fun f ss" and
          t: "t = Fun f ts" and 
          len: "length ss = length Cs" 
          "length ts = length Cs"
          "length Infos = length Cs" and
          infos: "infos = concat Infos" and
          steps: "\<And> i. i < length Cs \<Longrightarrow>(ss ! i, ts ! i) \<in> par_rstep_mctxt (set R) (Cs ! i) (Infos ! i)"
        by auto
      show ?case unfolding s t is_par_rstep_var_restr.simps
      proof (intro disjI2 conjI refl list_all2_all_nthI, unfold len)
        fix i
        assume i: "i < length Cs" 
        hence mem: "Cs ! i \<in> set Cs" by auto
        show "is_par_rstep_var_restr (ss ! i) (ts ! i)" 
        proof (rule MFun(1)[OF mem steps[OF i]])
          have "vars_below_hole (ts ! i) (Cs ! i) \<subseteq> vars_below_hole t (MFun f Cs)" 
            unfolding t using i len 
            by (subst vars_below_hole_Fun, auto)
          with MFun(3) show "vars_below_hole (ts ! i) (Cs ! i) \<inter> V = {}" by auto
        qed
      qed auto
    qed
  }
qed
end

lemma par_rstep_var_restr_code[code_unfold]: 
  "(s, t) \<in> par_rstep_var_restr (set R) V \<longleftrightarrow> is_par_rstep_var_restr R V s t" 
  by simp


subsection \<open>Implementation of Parallel Rewriting\<close>

subsubsection\<open>Checking a Single Parallel Rewrite Step\<close>

fun is_par_rstep :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "is_par_rstep R (Fun f ss) (Fun g ts) =
    (Fun f ss = Fun g ts \<or> (Fun f ss, Fun g ts) \<in> rrstep (set R) \<or>
    (f = g \<and> length ss = length ts \<and> list_all2 (is_par_rstep R) ss ts))"
  | "is_par_rstep R s t = (s = t \<or> (s,t) \<in> rrstep (set R))"

lemma is_par_rstep[simp]:
  "is_par_rstep R s t \<longleftrightarrow> (s, t) \<in> par_rstep (set R)"
proof -
  have "is_par_rstep R s t = is_par_rstep_var_restr R {} s t"
    by (induct R s t rule: is_par_rstep.induct, auto simp del: is_par_rstep_var_restr simp: list_all2_conv_all_nth)
  also have "\<dots> \<longleftrightarrow> (s, t) \<in> par_rstep_var_restr (set R) {}" by simp
  also have "\<dots> \<longleftrightarrow> (s, t) \<in> par_rstep (set R)" 
    unfolding par_rstep_var_restr_def par_rstep_par_rstep_mctxt_conv by auto
  finally show ?thesis .
qed

lemma par_rstep_code[code_unfold]: "(s, t) \<in> par_rstep (set R) \<longleftrightarrow> is_par_rstep R s t" by simp

subsubsection\<open>Generate All Parallel Rewrite Steps\<close>

fun root_rewrite :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "root_rewrite R s = concat (map (\<lambda> (l, r).
    (case match s l of
      None \<Rightarrow> []
    | Some \<sigma> \<Rightarrow> [(r \<cdot> \<sigma>)])) R)"

lemma root_rewrite_sound:
  assumes "t \<in> set (root_rewrite R s)"
  shows "(s, t) \<in> rrstep (set R)"
proof -
  from assms
  have "\<exists> l r.  (l,r) \<in> set R \<and> t \<in> set (case match s l of None \<Rightarrow> [] | Some \<sigma> \<Rightarrow> [r \<cdot> \<sigma>])"
    by auto
  from this obtain l r where one:
    "(l,r) \<in> set R \<and> t \<in> set (case match s l of None \<Rightarrow> [] | Some \<sigma> \<Rightarrow> [r \<cdot> \<sigma>])"
    by auto
  from this obtain \<sigma> where two: "match s l = Some \<sigma> \<and> t \<in> {r \<cdot> \<sigma>}" by (cases "match s l", auto)
  then have match: "l \<cdot> \<sigma> = s" using match_sound by auto
  with one match one two have "(s,t) \<in> rstep_r_p_s (set R) (l,r) [] \<sigma>" unfolding rstep_r_p_s_def by (simp add: Let_def ctxt_supt_id)
  then show "(s,t) \<in> rrstep (set R)" unfolding rstep_iff_rstep_r_p_s rrstep_def by blast
qed

text\<open>Generate all possible parallel rewrite steps for a given term, assuming that 
the underlying TRS is well-formed.\<close>

fun parallel_rewrite :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "parallel_rewrite R (Var x) = [Var x]"
  | "parallel_rewrite R (Fun f ss) = remdups
     (root_rewrite R (Fun f ss) @ map (\<lambda>ss. Fun f ss) (product_lists (map (parallel_rewrite R) ss)))"

lemma parallel_rewrite_par_step:
  assumes "t \<in> set (parallel_rewrite R s)"
  shows "(s, t) \<in> par_rstep (set R)"
  using assms
proof (induct s arbitrary: t)
  case (Fun f ss)
  then consider (root) "t \<in> set (root_rewrite R (Fun f ss))"
    | (args) "t \<in> set (map (\<lambda>ss. Fun f ss) (product_lists (map (parallel_rewrite R) ss)))"
    by force
  then show ?case
  proof (cases)
    case root
    from root_rewrite_sound[OF this] obtain l r \<sigma> where "(l, r) \<in> set R"
      and "l \<cdot> \<sigma> = Fun f ss" and "r \<cdot> \<sigma> = t"
      unfolding rrstep_def rstep_r_p_s_def by auto
    then show ?thesis using par_rstep.intros(1) by metis
  next
    case args
    then obtain ts where t:"t = Fun f ts" and ts:"ts \<in> set (product_lists (map (parallel_rewrite R) ss))"
      by auto
    then have len:"length ss = length ts" using in_set_product_lists_length by force
    { fix i
      assume i:"i < length ts"
      have "ts ! i \<in> set (parallel_rewrite R (ss ! i))"
        using ts[unfolded product_lists_set[of "_ ss"]]
        by (auto simp: list_all2_map2[of "(\<lambda>x ys. x \<in> set ys)"] intro: list_all2_nthD[OF _ i])
      with Fun(1) len i have "(ss ! i, ts ! i) \<in> par_rstep (set R)" by auto
    }
    from par_rstep.intros(2)[OF this len] show ?thesis using t by auto
  qed
qed auto

subsection \<open>Implementation of Multi-Step Rewriting\<close>

subsubsection\<open>Checking a Single Multi-Step Rewrite\<close>
  (*Takes a list of rewrite rules and two terms and checks for each rule whether the first term matches
the lhs and the second term the rhs of the rule. For each rule where this is the case,
returns the lists of terms corresponding to the matching substitutions. 
Terms that correspond to variables that only appear on one side of the rule 
don't play a role in the remainder of the computation for multisteps. Hence, they can be ignored.*) 
fun root_steps_substs :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> (('f, 'v) term list \<times> ('f, 'v) term list) list"
  where
    "root_steps_substs R s t = concat (map (\<lambda> (l, r).
    (case match s l of
      None \<Rightarrow> []
    | Some \<sigma> \<Rightarrow> (case match t r of 
        None \<Rightarrow> []
      | Some \<tau> \<Rightarrow> (let var_list = filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l) in [(map \<sigma> var_list, map \<tau> var_list)])))) 
  R)"

lemma root_steps_substs_exists:
  assumes "(ss, ts) \<in> set (root_steps_substs R s t)"
  shows "\<exists> l r \<sigma> \<tau> vl. (l, r) \<in> set R \<and> vl = filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l) \<and> 
        l \<cdot> \<sigma> = s \<and> r \<cdot> \<tau> = t \<and> (ss, ts) = (map \<sigma> vl, map \<tau> vl)"
proof-
  from assms obtain l r where lr:"(l,r) \<in> set R" "(ss, ts) \<in> set (case match s l of
        None \<Rightarrow> []
      | Some \<sigma> \<Rightarrow> (case match t r of 
          None \<Rightarrow> []
        | Some \<tau> \<Rightarrow> [(map \<sigma> (filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l)), map \<tau> (filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l)))]))"
    unfolding root_steps_substs.simps Let_def by auto
  let ?var_list="filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l)"  
  from lr obtain \<sigma> where \<sigma>:"match s l = Some \<sigma>"
    by fastforce 
  from lr obtain \<tau> where \<tau>:"match t r = Some \<tau>" 
    by fastforce
  from lr \<sigma> \<tau> have "(ss, ts) = (map \<sigma> ?var_list, map \<tau> ?var_list)"
    by simp 
  with lr(1) \<sigma> \<tau> show ?thesis
    using match_matches by blast
qed

lemma size_match_subst_Fun: (*used for termination_simps*)
  assumes "is_Fun l" and "x \<in> vars_term l"
    and match:"match s l = Some \<tau>"
  shows "size (\<tau> x) < size s"
proof-
  from assms(1) obtain f ts where l:"l = Fun f ts"
    by blast 
  from match have *:"l \<cdot> \<tau> = s"
    by (simp add: match_matches) 
  then obtain ss where s:"s = Fun f ss"
    unfolding l by force
  from assms(2) obtain i where i:"i < length ts" and x:"x \<in> vars_term (ts!i)" 
    unfolding l by (metis term.sel(4) var_imp_var_of_arg) 
  from * have le:"length ts = length ss" 
    unfolding s l by auto 
  moreover from * i l s have "ts!i \<cdot> \<tau> = ss!i" 
    by fastforce
  then have "size (\<tau> x) \<le> size (ss!i)"
    using vars_term_size x by metis
  with i show ?thesis unfolding s term.size le
    by (metis add.commute add_0 add_Suc in_set_conv_nth less_Suc_eq_le size_list_estimation')
qed

abbreviation "remove_trivial_rules R \<equiv> filter (\<lambda> (l, r). \<not> (is_Var l) \<or> \<not> (is_Var r)) R"

lemma trivial_rrstep:
  assumes "\<exists> x y. (Var x, Var y) \<in> R \<and> x \<noteq> y" 
  shows "(s, t) \<in> rrstep R" 
proof-
  from assms obtain x y where xy:"(Var x, Var y) \<in> R" "x \<noteq> y" by blast
  let ?\<sigma>="(subst x s) (y := t)"
  from xy have "(?\<sigma> x, ?\<sigma> y) \<in> rrstep R"
    by (metis eval_term.simps(1) rrstepI)   
  then show ?thesis
    by (simp add: xy(2)) 
qed

lemma size_root_steps_substs: (*used for termination proof*)
  assumes "(ss, ts) \<in> set (root_steps_substs (remove_trivial_rules R) s t)"
    and "s' \<in> set ss" "t' \<in> set ts"
  shows "size s' + size t' < size s + size t"
proof-
  let ?R="remove_trivial_rules R" 
  from assms(1) obtain l r vl \<sigma> \<tau> where lr:"(l, r) \<in> set ?R" and vl:"vl = filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l)" 
    and s:"s = l \<cdot> \<sigma>" and t:"t = r \<cdot> \<tau>" and ss_ts:"(ss, ts) = (map \<sigma> vl, map \<tau> vl)"
    using root_steps_substs_exists by blast
  from ss_ts assms(2) obtain x where s':"s' = \<sigma> x" and x:"x \<in> set vl" 
    by auto
  with s have s1:"size s' \<le> size s" 
    unfolding vl by (simp add: vars_term_size) 
  from ss_ts assms(3) obtain y where t':"t' = \<tau> y" and y:"y \<in> set vl" 
    by auto
  with t have s2:"size t' \<le> size t" 
    unfolding vl by (simp add: vars_term_size) 
  from lr consider "\<not> is_Var l" | "\<not> is_Var r"
    by force 
  then show ?thesis proof(cases)
    case 1
    then obtain f ls where l:"l = Fun f ls" 
      by blast
    from x obtain i where "i < length ls" and "x \<in> vars_term (ls!i)" 
      unfolding vl l by (metis comp_apply filter_is_subset set_remdups set_rev set_vars_term_list subsetD term.sel(4) var_imp_var_of_arg)  
    then have "s' \<lhd> s"
      unfolding s s' l by (meson nth_mem subst_image_subterm term.set_intros(4))
    then have "size s' < size s"
      by (simp add: supt_size) 
    then show ?thesis using s2 by simp
  next
    case 2
    then obtain f rs where r:"r = Fun f rs" 
      by blast
    from y obtain i where "i < length rs" and "y \<in> vars_term (rs!i)" 
      unfolding vl r using var_imp_var_of_arg by force 
    then have "t' \<lhd> t"
      unfolding t t' r by (meson nth_mem subst_image_subterm term.set_intros(4))
    then have "size t' < size t"
      by (simp add: supt_size) 
    then show ?thesis using s1 by simp 
  qed
qed

function (sequential) is_mstep :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "is_mstep R (Fun f ss) (Fun g ts) =
    (Fun f ss = Fun g ts \<or> (Fun f ss, Fun g ts) \<in> rrstep (set R) \<or>
    list_ex (\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) (root_steps_substs (remove_trivial_rules R) (Fun f ss) (Fun g ts)) \<or> 
    (f = g \<and> length ss = length ts \<and> list_all2 (is_mstep R) ss ts))" 
  | "is_mstep R s t = (s = t \<or> (s, t) \<in> rrstep (set R) \<or>
    list_ex (\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) (root_steps_substs (remove_trivial_rules R) s t))"
  by pat_completeness auto

termination proof (relation "measure (\<lambda> (R, s, t). size s + size t)", goal_cases)
  case (2 R f ss g ts x ls rs l r)
  then show ?case using size_root_steps_substs 
    unfolding in_measure by (metis case_prod_conv)
next
  case (3 R f ss g ts s t)
  then have "size s < size (Fun f ss)" and "size t < size (Fun g ts)"
    by (simp add: elem_size_size_list_size less_Suc_eq)+
  then show ?case by simp
next
  case (4 R v t x xa y z yb)
  then show ?case using size_root_steps_substs 
    unfolding in_measure by (metis case_prod_conv)
next
  case (5 R s v x xa y z yb)
  then show ?case using size_root_steps_substs 
    unfolding in_measure by (metis case_prod_conv)
qed auto

text\<open>Show that all multi-steps are covered by the definition above.\<close>
lemma mstep_is_mstep:
  assumes "(s, t) \<in> mstep (set R)"
  shows "is_mstep R s t"
  using assms proof(induct)
  case (args f n ss ts)
  then have "list_all2 (is_mstep R) ss ts"
    by (simp add: list_all2_all_nthI) 
  with args show ?case
    by simp 
next
  case (rule l r \<sigma> \<tau>)
  show ?case proof(cases "(l \<cdot> \<sigma>, r \<cdot> \<tau>) \<in> rrstep (set R)")
    case True
    then show ?thesis using is_mstep.simps by (metis (no_types, opaque_lifting) funas_term.cases)
  next
    case False
    then show ?thesis proof(cases "is_Var l \<and> is_Var r")
      case True
      with False have "\<not> (\<exists>x y. (Var x, Var y) \<in> set R \<and> x \<noteq> y)" 
        using trivial_rrstep by metis
      with True obtain x where l:"l = Var x" and r:"r = Var x"
        using rule.hyps(1) by blast 
      show ?thesis 
        unfolding l r using rule(2) l by simp
    next
      case False
      let ?R="remove_trivial_rules R" 
      let ?vl="filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l)"
      from rule(1) False obtain i where i:"i < length ?R" "?R!i = (l, r)"
        by (metis (no_types, lifting) case_prodI2 fst_conv in_set_conv_nth mem_Collect_eq prod.sel(2) set_filter)
      obtain \<sigma>' where sigma:"match (l \<cdot> \<sigma>) l = Some \<sigma>'" "(\<forall>x\<in>vars_term l. \<sigma> x = \<sigma>' x)" 
        by (meson match_complete')
      obtain \<tau>' where tau:"match (r \<cdot> \<tau>) r = Some \<tau>'" "(\<forall>x\<in>vars_term r. \<tau> x = \<tau>' x)" 
        by (meson match_complete')
      let ?matches="(map (\<lambda>(l', r'). case 
          match (l \<cdot> \<sigma>) l' of None \<Rightarrow> [] | Some \<sigma> \<Rightarrow> (case match (r \<cdot> \<tau>) r' of None \<Rightarrow> [] 
        | Some \<tau> \<Rightarrow> (let var_list = filter (\<lambda>x. x \<in> vars_term r') (vars_distinct l') 
                    in [(map \<sigma> var_list, map \<tau> var_list)]))) ?R)"
      have "i < length ?matches"
        using i(1) by auto 
      moreover have "(map \<sigma>' ?vl, map \<tau>' ?vl) \<in> set (?matches ! i)"
        using sigma(1) tau(1) i unfolding Let_def by simp
      ultimately have "(map \<sigma>' ?vl, map \<tau>' ?vl) \<in> set (root_steps_substs ?R (l\<cdot>\<sigma>) (r\<cdot>\<tau>))"
        unfolding root_steps_substs.simps by (metis (no_types, lifting) concat_nth concat_nth_length in_set_conv_nth) 
      then obtain j where j:"j < length (root_steps_substs ?R (l\<cdot>\<sigma>) (r\<cdot>\<tau>))" "root_steps_substs ?R (l\<cdot>\<sigma>) (r\<cdot>\<tau>) ! j = (map \<sigma>' ?vl, map \<tau>' ?vl)"
        by (metis in_set_idx)
      have "(\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) ((root_steps_substs ?R (l\<cdot>\<sigma>) (r\<cdot>\<tau>))!j)"
      proof-
        {fix i assume i:"i < length ?vl"
          from i have vr:"?vl!i \<in> vars_term r"
            using nth_mem by force  
          from i have vl:"?vl!i \<in> vars_term l" 
            using nth_mem by force  
          moreover have "\<sigma>' (?vl ! i) = \<sigma> (?vl ! i)" 
            using sigma(2) vr vl by simp
          moreover have "\<tau>' (?vl ! i) = \<tau> (?vl ! i)"
            using vl vr tau(2) by simp
          ultimately have "is_mstep R (\<sigma>' (?vl !i)) (\<tau>' (?vl !i))" 
            using rule(2) by force
        }
        then have "list_all2 (is_mstep R) (map \<sigma>' ?vl) (map \<tau>' ?vl)"
          by (simp add: list_all2_conv_all_nth) 
        then show ?thesis 
          unfolding j(2) by fastforce 
      qed
      then have *:"list_ex (\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) (root_steps_substs ?R (l\<cdot>\<sigma>) (r\<cdot>\<tau>))"
        using j by (meson list_ex_length)
      then show ?thesis
        by (smt (verit) is_mstep.elims(3))
    qed
  qed
qed simp

lemma mstep_root_helper:
  assumes "list_ex (\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) (root_steps_substs (remove_trivial_rules R) s t)"
    and "\<And> ss ts s' t'. (ss, ts) \<in> set (root_steps_substs (remove_trivial_rules R) s t) \<Longrightarrow> s' \<in> set ss \<Longrightarrow> t' \<in> set ts \<Longrightarrow> is_mstep R s' t' \<Longrightarrow> (s', t') \<in> mstep (set R)"
  shows "(s, t) \<in> mstep (set R)" 
proof-
  let ?R="(remove_trivial_rules R)"
  from assms obtain i where "i < length (root_steps_substs ?R s t)" "(\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) ((root_steps_substs ?R s t)!i)"
    using list_ex_length by blast
  then obtain ss' ts' where ss'ts':"(ss' , ts') \<in> set (root_steps_substs ?R s t)" "list_all2 (is_mstep R) ss' ts'"
    using nth_mem by fastforce 
  with root_steps_substs_exists obtain l r vl \<sigma> \<tau> where lr:"(l, r) \<in> set R" 
    and vl:"vl = filter (\<lambda>x. x \<in> vars_term r) (vars_distinct l)"
    and l:"l \<cdot> \<sigma> = s" and r:"r \<cdot> \<tau> = t" 
    and \<sigma>\<tau>:"(ss', ts') = (map \<sigma> vl, map \<tau> vl)"
    by (smt (verit, best) mem_Collect_eq set_filter)
  let ?\<tau>="\<lambda>x. (if x \<in> vars_term r then \<tau> x else \<sigma> x)"
  from r have r':"r \<cdot> ?\<tau> = t"
    by (smt (verit, del_insts) term_subst_eq) 
  { fix x assume x:"x \<in> vars_term l"
    then have "(\<sigma> x, ?\<tau> x) \<in> mstep (set R)" proof(cases "x \<in> set vl")
      case True
      then obtain i where i:"i < length vl" "vl ! i = x"
        using in_set_idx by force  
      then have i1:"i < length ss'" 
        using \<sigma>\<tau> by simp 
      from i have i2:"i < length ts'"
        using \<sigma>\<tau> by simp
      from ss'ts'(2) i1 i2 have "is_mstep R (ss' ! i) (ts' ! i)"
        using list_all2_nthD by blast
      with assms(2)[OF ss'ts'(1)] i1 i2 have "(ss' ! i, ts' ! i) \<in> mstep (set R)"
        by auto
      then show ?thesis 
        using i \<sigma>\<tau> by auto 
    next 
      case False 
      with vl x show ?thesis by simp
    qed 
  }
  then show ?thesis 
    using mstep.rule[OF lr] l r' by force 
qed

lemma is_mstep_mstep:
  assumes "is_mstep R s t"
  shows "(s, t) \<in> mstep (set R)"
  using assms proof (induct rule: is_mstep.induct)
  case (1 R f ss g ts)
  from 1 consider "Fun f ss = Fun g ts"
    | (rrstep) "(Fun f ss, Fun g ts) \<in> rrstep (set R)"
    | (root) "list_ex (\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) (root_steps_substs (remove_trivial_rules R) (Fun f ss) (Fun g ts))"
    | (args) "f = g" and "length ss = length ts" and "list_all2 (is_mstep R) ss ts"
    by (auto split: if_splits)
  then show ?case proof(cases)
    case root
    show ?thesis using mstep_root_helper[OF root] 1(1) by simp
  next
    case args
    { fix i
      assume i:"i < length ss"
      then have si:"ss ! i \<in> set ss" by auto
      from i args(2) have ti:"ts ! i \<in> set ts" by auto
      from args(3) have "is_mstep R (ss ! i) (ts ! i)" using i list_all2_nthD by blast
      with 1(2)[of "ss ! i" "ts ! i"] args(1,2) si ti have "(ss ! i, ts ! i) \<in> mstep (set R)"
        by auto
    }
    then show ?thesis using args(1,2)
      by (simp add: mstep.args)
  qed (simp_all add: rrstep_imp_rstep rstep_imp_mstep)
next
  case ("2_1" R v t) 
  from "2_1" consider "Var v = t"
    | "(Var v, t) \<in> rrstep (set R)"
    | (root) "list_ex (\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) (root_steps_substs (remove_trivial_rules R) (Var v) t)"
    by auto
  then show ?case proof(cases)
    case root
    show ?thesis using mstep_root_helper[OF root] "2_1"(1) by simp
  qed (simp_all add: rrstep_imp_rstep rstep_imp_mstep)
next
  case ("2_2" R s v)
  from "2_2" consider "s = Var v"
    | "(s, Var v) \<in> rrstep (set R)"
    | (root) "list_ex (\<lambda> (ss, ts). list_all2 (is_mstep R) ss ts) (root_steps_substs (remove_trivial_rules R) s (Var v))"
    by auto
  then show ?case proof(cases)
    case root
    show ?thesis using mstep_root_helper[OF root] "2_2"(1) by simp
  qed (simp_all add:rrstep_imp_rstep rstep_imp_mstep)
qed

lemma is_mstep[simp]:
  "is_mstep R s t \<longleftrightarrow> (s, t) \<in> mstep (set R)"
  using is_mstep_mstep mstep_is_mstep by blast

lemma mstep_code[code_unfold]: "(s, t) \<in> mstep (set R) \<longleftrightarrow> is_mstep R s t" by simp

subsubsection\<open>Generate All Multi-Step Rewrites\<close>

fun root_subst_with_rhs :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term list) list"
  where
    "root_subst_with_rhs R s = concat (map (\<lambda> (l, r).
    (case match s l of
      None \<Rightarrow> []
    | Some \<sigma> \<Rightarrow> [(r, map \<sigma> (vars_distinct r))]))
  R)"

lemma root_steps_subst_rhs_exists:
  assumes "(r, ss) \<in> set (root_subst_with_rhs R s)"
  shows "\<exists> l \<sigma>. (l, r) \<in> set R \<and> l \<cdot> \<sigma> = s \<and> ss = map \<sigma> (vars_distinct r)"
proof-
  from assms obtain l where lr:"(l,r) \<in> set R" "(r, ss) \<in> set (case match s l of
      None \<Rightarrow> []
    | Some \<sigma> \<Rightarrow> [(r, map \<sigma> (vars_distinct r))])"
    by auto
  then obtain \<sigma> where \<sigma>:"match s l = Some \<sigma>"
    by fastforce
  with lr show ?thesis
    using match_matches by force
qed

context
  fixes R :: "('f, 'v) rules"
  assumes "wf_trs (set R)"
begin

private lemma *: "list_all (\<lambda>(l, r). is_Fun l \<and> (vars_term r \<subseteq> vars_term l)) R" 
  using \<open>wf_trs (set R)\<close> unfolding wf_trs_def by (auto simp: list_all_iff)

lemma varcond:
  "\<And>l r. (l, r) \<in> set R \<Longrightarrow> is_Fun l \<and> vars_term r \<subseteq> vars_term l"
  using * Ball_set_list_all case_prodD by (metis (no_types, lifting)) 

lemma [termination_simp]:
  assumes "(l, r) \<in> set R" 
    and "Some \<sigma> = match (Fun g ts) l" 
    and "x \<in> vars_term r"
  shows "size (\<sigma> x) < Suc (size_list size ts)"
  using assms size_match_subst_Fun varcond
  by (metis (no_types, lifting) add.right_neutral add_Suc_right subsetD term.size(4))

text\<open>Compute the list of terms reachable in multi-step from a given term.\<close>
fun mstep_rewrite_main :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "mstep_rewrite_main (Var x) = [Var x]"
  | "mstep_rewrite_main (Fun f ss) = remdups (
     (concat (map (\<lambda>(r, ts). 
        (map (\<lambda>args. r \<cdot> (mk_subst Var (zip (vars_distinct r) args))) (product_lists (map mstep_rewrite_main ts))))
      (root_subst_with_rhs R (Fun f ss))))
    @(map (\<lambda>ss. Fun f ss) (product_lists (map mstep_rewrite_main ss))))"

lemma mstep_rewrite_main_mstep:
  assumes "t \<in> set (mstep_rewrite_main s)"
  shows "(s, t) \<in> mstep (set R)"
  using assms
proof (induct s arbitrary: t rule:subterm_induct)
  case (subterm s)
  then show ?case proof(cases s)
    case (Var x)
    with subterm(2) show ?thesis by simp
  next
    case (Fun f ss)
    with subterm consider (root) "t \<in> set (concat (map (\<lambda>(r,ts).(map (\<lambda>args. r \<cdot> (mk_subst Var (zip (vars_distinct r) args))) 
          (product_lists (map mstep_rewrite_main ts)))) (root_subst_with_rhs R (Fun f ss))))"
      | (args) "t \<in> set (map (\<lambda>ss. Fun f ss) (product_lists (map mstep_rewrite_main ss)))"
      by force 
    then show ?thesis
    proof (cases)
      case root
      then obtain r ts where rhs_subst:"(r,ts) \<in> set (root_subst_with_rhs R (Fun f ss))" 
        "t \<in> set (map (\<lambda>args. r \<cdot> (mk_subst Var (zip (vars_distinct r) args))) (product_lists (map mstep_rewrite_main ts)))"
        by force
      from root_steps_subst_rhs_exists[OF rhs_subst(1)] obtain l \<sigma> where lr:"(l, r) \<in> set R"
        and sigma:"l \<cdot> \<sigma> = Fun f ss" "ts = map \<sigma> (vars_distinct r)" by auto
      from rhs_subst(2) obtain args where args:"t = r \<cdot> (mk_subst Var (zip (vars_distinct r) args))"
        "args \<in> set (product_lists (map mstep_rewrite_main ts))"
        by auto    
      then have len:"length args = length ts"
        using in_set_product_lists_length by fastforce 
      then have len':"length args = length (vars_distinct r)"
        by (simp add: sigma(2)) 
      let ?\<tau>="\<lambda>x. if x \<in> vars_term r then (mk_subst Var (zip (vars_distinct r) args)) x else \<sigma> x"
      from args(1) have t:"t = r \<cdot> ?\<tau>"
        by (simp add: term_subst_eq_conv) 
      { fix x
        assume x:"x \<in> vars_term l"
        have "(\<sigma> x, ?\<tau> x) \<in> mstep (set R)" proof(cases "x \<in> vars_term r")
          case True
          then obtain i where i:"i < length (vars_distinct r)" "x = vars_distinct r ! i"
            by (metis in_set_idx set_vars_term_list vars_term_list_vars_distinct)
          with True len' have tau_x:"?\<tau> x = args!i"
            by (simp add: mk_subst_distinct)
          from i sigma(2) have sigma_x:"\<sigma> x = ts!i"
            by simp 
          have "\<sigma> x \<lhd> Fun f ss"
            by (metis is_VarI lr sigma(1) subst_image_subterm term.set_cases(2) varcond x) 
          with sigma_x have "ts!i \<lhd> Fun f ss" by simp
          moreover have "args!i \<in> set (mstep_rewrite_main (ts!i))" using args(2) i(1) len' len 
            unfolding product_lists_set list_all2_conv_all_nth by force
          ultimately show ?thesis using subterm(1) sigma_x tau_x unfolding Fun by presburger
        next
          case False 
          then show ?thesis by simp
        qed
      }
      then show ?thesis using mstep.intros(3)[OF lr] sigma(1) unfolding Fun t
        by fastforce
    next
      case args
      then obtain ts where t:"t = Fun f ts" and ts:"ts \<in> set (product_lists (map mstep_rewrite_main ss))"
        by auto
      then have len:"length ss = length ts" using in_set_product_lists_length by force
      { fix i
        assume i:"i < length ts"
        have "ts ! i \<in> set (mstep_rewrite_main (ss ! i))"
          using ts[unfolded product_lists_set[of "_ ss"]]
          by (auto simp: list_all2_map2[of "(\<lambda>x ys. x \<in> set ys)"] intro: list_all2_nthD[OF _ i])
        with subterm len i have "(ss ! i, ts ! i) \<in> mstep (set R)" 
          unfolding Fun by auto
      }
      with mstep.intros(2) len t Fun show ?thesis
        by metis
    qed
  qed
qed

end

text\<open>We need to be able to export code for @{const mstep_rewrite_main}, hence the following definitions.\<close>
  (*adapted from template by Rene*)
  (*New type for well-formed TRSs*)
typedef ('f, 'v) wfTRS = "{R :: ('f, 'v) rules. wf_trs (set R)}"
  by (intro exI[of _ Nil], auto simp: wf_trs_def)

setup_lifting type_definition_wfTRS

lift_definition get_TRS :: "('f, 'v) wfTRS \<Rightarrow> ('f, 'v) rules" is "\<lambda> R. R" .

lemma is_wf_get_TRS: "wf_trs (set (get_TRS R'))" 
  by (transfer, auto)

definition "mstep_rewrite_wf R = mstep_rewrite_main (get_TRS R)" 

lemmas mstep_rewrite_wf_simps = mstep_rewrite_main.simps[OF is_wf_get_TRS, folded mstep_rewrite_wf_def]
declare mstep_rewrite_wf_simps[code]

(* one might use an implementation which does not require show-class *)
lift_definition (code_dt) get_wfTRS :: "('f :: showl, 'v :: showl) rules \<Rightarrow> ('f, 'v) wfTRS option" is
  "\<lambda> R. if isOK (check_wf_trs R) then Some R else None"
  by (force simp: wf_trs_def list.pred_set split: prod.splits)

definition err_wf where "err_wf = STR ''TRS is not well-formed''" 
  (*should actually never be printed, since TRS is checked before even calling is_mstep_main*) 

definition "mstep_dummy_impl R s t = ((s,t) \<in> mstep (set R))" 
lemma mstep_dummy_impl[code]: "mstep_dummy_impl R = Code.abort (STR ''mstep_dummy'') (\<lambda> _. mstep_dummy_impl R)" 
  by simp

lift_definition (code_dt) get_wfTRS_sub :: "('f :: showl, 'v :: showl) rules \<Rightarrow> ('f, 'v) wfTRS" is
  "\<lambda> R. if isOK (check_wf_trs R) then R else Code.abort err_wf (\<lambda> _. [])"
  by (auto simp: wf_trs_def)

definition "mstep_rewrite R = mstep_rewrite_wf (get_wfTRS_sub R)" 

lemma mstep_rewrite_mstep:
  assumes "t \<in> set (mstep_rewrite R s)"
  shows "(s, t) \<in> mstep (set R)"
proof -
  define R' where "R' = get_wfTRS_sub R" 
  have wf: "wf_trs (set (get_TRS R'))" 
    by (transfer, auto)
  have sub: "set (get_TRS R') \<subseteq> set R" unfolding R'_def by (transfer, auto)
  from mstep_rewrite_main_mstep[OF wf, folded mstep_rewrite_wf_def, OF assms(1)[unfolded mstep_rewrite_def, folded R'_def]]
  have "(s, t) \<in> mstep (set (get_TRS R'))" .
  with mstep_mono[OF sub] show ?thesis  by auto
qed

end