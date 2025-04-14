theory Residual_Join_Deletion

imports
  Proof_Terms
  Linear_Matching
begin

subsection\<open>Residuals\<close>

text \<open>Auxiliary lemma in preparation of termination simp rule.\<close>
lemma match_vars_term_size:
  assumes "match s t = Some \<sigma>"
    and "x \<in> vars_term t"
  shows "size (\<sigma> x) \<le> size s"
  using assms vars_term_size by (metis match_matches) 

lemma [termination_simp]: 
  assumes "match (Fun f ss) (to_pterm l) = Some \<sigma>"
    and *: "(s, t) \<in> set (zip (map \<sigma> (vars_distinct l)) ts)"
  shows "size s \<le> Suc (size_list size ss)"
proof - 
  from * have "s \<in> set (map \<sigma> (vars_distinct l))" by (blast elim: in_set_zipE)
  then obtain x where [simp]: "s = \<sigma> x"
    and x: "x \<in> vars_term (to_pterm l)" by (induct l) auto
  from match_vars_term_size [OF assms(1)  x]
    show ?thesis by simp
  qed

text\<open>Additional simp rule because we allow variable left-hand sides of rewrite rules at this point.
Then @{text "Var x / \<alpha>"} and @{text "\<alpha> / Var x"} are also possible when evaluating residuals. This 
might become important when we want to introduce the error rule for residuals of composed proof terms.\<close>
lemma [termination_simp]:
  assumes "match (Var x) (to_pterm l) = Some \<sigma>"
    and "(a, b) \<in> set (zip (map \<sigma> (vars_distinct l)) ts)"
  shows "size a = 1"
proof-
  from assms(1) have *:"(to_pterm l) \<cdot> \<sigma> = Var x" by (simp add: match_matches) 
  then obtain y where y:"l = Var y" by (metis subst_apply_eq_Var term.distinct(1) to_pterm.elims) 
  with * have **:"\<sigma> y = Var x" by simp 
  from y have "vars_distinct l = [y]" by (simp add: vars_term_list.simps(1))
  with assms(2) y have "a = Var x" by (simp add: "**" in_set_zip) 
  then show ?thesis by simp
qed

fun residual :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm option" (infixr "re" 70)
  where
  "Var x re Var y =
    (if x = y then Some (Var x) else None)"
| "Pfun f As re Pfun g Bs =  
    (if (f = g \<and> length As = length Bs) then
      (case those (map2 residual As Bs) of
        Some xs \<Rightarrow> Some (Pfun f xs)
      | None \<Rightarrow> None)
    else None)"
| "Prule \<alpha> As re Prule \<beta> Bs =
    (if \<alpha> = \<beta> then 
      (case those (map2 residual As Bs) of
        Some xs \<Rightarrow> Some ((to_pterm (rhs \<alpha>)) \<cdot> \<langle>xs\<rangle>\<^sub>\<alpha>)
      | None \<Rightarrow> None)
    else None)"
| "Prule \<alpha> As re B =
    (case match B (to_pterm (lhs \<alpha>)) of
      None \<Rightarrow> None
    | Some \<sigma> \<Rightarrow>
      (case those (map2 residual As (map \<sigma> (var_rule \<alpha>))) of
        Some xs \<Rightarrow> Some (Prule \<alpha> xs)
      | None \<Rightarrow> None))"
| "A re Prule \<alpha> Bs =
    (case match A (to_pterm (lhs \<alpha>)) of
      None \<Rightarrow> None
    | Some \<sigma> \<Rightarrow>
      (case those (map2 residual (map \<sigma> (var_rule \<alpha>)) Bs) of
        Some xs \<Rightarrow> Some ((to_pterm (rhs \<alpha>)) \<cdot> \<langle>xs\<rangle>\<^sub>\<alpha>)
      | None \<Rightarrow> None))"
| "A re B = None"


text\<open>Since the interesting proofs about residuals always follow the same pattern of induction on the 
definition, we introduce the following 6 lemmas corresponding to the step cases.\<close>
lemma residual_fun_fun:
  assumes "(Pfun f As) re (Pfun g Bs) = Some C"
  shows "f = g \<and> length As = length Bs \<and> 
        (\<exists>Cs. C = Pfun f Cs \<and> 
        length Cs = length As \<and>
        (\<forall>i < length As. As!i re Bs!i = Some (Cs!i)))" 
proof-
  have *:"f = g \<and> length As = length Bs" 
    using assms residual.simps(2) by (metis option.simps(3))
  then obtain Cs where Cs:"those (map2 (re) As Bs) = Some Cs" 
    using assms residual.simps(2) option.simps(3) option.simps(4) by fastforce 
  hence "\<forall>i < length As. As!i re Bs!i = Some (Cs!i)" 
    using * those_some2 by fastforce
  with * Cs assms(1) show ?thesis
    using length_those by fastforce
qed

lemma residual_rule_rule:
  assumes "(Prule \<alpha> As) re (Prule \<beta> Bs) = Some C" 
          "(Prule \<alpha> As) \<in> wf_pterm R" 
          "(Prule \<beta> Bs) \<in> wf_pterm S"
  shows "\<alpha> = \<beta> \<and> length As = length Bs \<and> 
        (\<exists>Cs. C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and>
        length Cs = length As \<and> 
        (\<forall>i < length As. As!i re Bs!i = Some (Cs!i)))"
proof-
  have "\<alpha> = \<beta>" 
    using assms(1) residual.simps(3) by (metis option.simps(3))
  with assms(2,3) have l: "length As = length Bs"
    using length_args_well_Prule by blast
  from \<open>\<alpha> = \<beta>\<close> obtain Cs where Cs:"those (map2 (re) As Bs) = Some Cs" 
    using assms by fastforce 
  hence "\<forall>i < length As. As!i re Bs!i = Some (Cs!i)" 
    using l those_some2 by fastforce
  with \<open>\<alpha> = \<beta>\<close> l Cs assms(1) show ?thesis 
    using length_those by fastforce
qed

lemma residual_rule_var:
  assumes "(Prule \<alpha> As) re (Var x) = Some C" 
          "(Prule \<alpha> As) \<in> wf_pterm R" 
  shows "\<exists>\<sigma>. match (Var x) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        (\<exists>Cs. C = Prule \<alpha> Cs \<and> 
        length Cs = length As \<and> 
        (\<forall>i < length As. As!i re (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)))" 
proof-
  from assms(2) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  obtain \<sigma> where \<sigma>:"match (Var x) (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
    using assms(1) by fastforce
  then obtain Cs where Cs:"those (map2 residual As (map \<sigma> (var_rule \<alpha>))) = Some Cs"  
    using assms(1) by fastforce
  with l have l2:"length Cs = length As" 
    using length_those by fastforce 
  from Cs have "\<forall>i < length As. As!i re (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)" 
    using l those_some2 by fastforce 
  with \<sigma> Cs assms(1) l2 show ?thesis by simp
qed

lemma residual_rule_fun:
  assumes "(Prule \<alpha> As) re (Pfun f Bs) = Some C" 
          "(Prule \<alpha> As) \<in> wf_pterm R" 
  shows "\<exists>\<sigma>. match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        (\<exists>Cs. C = Prule \<alpha> Cs \<and> 
        length Cs = length As \<and> 
        (\<forall>i < length As. As!i re (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)))"
proof-
  from assms(2) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  obtain \<sigma> where \<sigma>:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
    using assms(1) by fastforce
  then obtain Cs where Cs:"those (map2 residual As (map \<sigma> (var_rule \<alpha>))) = Some Cs"  
    using assms(1) by fastforce
  with l have l2:"length Cs = length As" 
    using length_those by fastforce
  from Cs have "\<forall>i < length As. As!i re (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)" 
    using l those_some2 by fastforce 
  with \<sigma> Cs assms(1) l2 show ?thesis by auto
qed

lemma residual_var_rule:
  assumes "(Var x) re (Prule \<alpha> As) = Some C" 
          "(Prule \<alpha> As) \<in> wf_pterm R" 
  shows "\<exists>\<sigma>. match (Var x) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        (\<exists>Cs. C = (to_pterm (rhs \<alpha>)) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and> 
        length Cs = length As \<and> 
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i) re As!i) = Some (Cs!i)))"
proof-
  from assms(2) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  obtain \<sigma> where \<sigma>:"match (Var x) (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
    using assms(1) by fastforce
  then obtain Cs where Cs:"those (map2 residual (map \<sigma> (var_rule \<alpha>)) As) = Some Cs"  
    using assms(1) by fastforce
  with l have l2:"length Cs = length As" 
    using length_those by fastforce 
  from Cs have "\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) re As!i = Some (Cs!i)" 
    using l those_some2 by fastforce 
  with \<sigma> Cs assms(1) l2 show ?thesis by auto
qed

lemma residual_fun_rule:
  assumes "(Pfun f Bs) re (Prule \<alpha> As) = Some C" 
          "(Prule \<alpha> As) \<in> wf_pterm R" 
  shows "\<exists>\<sigma>. match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        (\<exists>Cs. C = (to_pterm (rhs \<alpha>)) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and> 
        length Cs = length As \<and> 
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) re As!i = Some (Cs!i)))"
proof-
  from assms(2) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  obtain \<sigma> where \<sigma>:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
    using assms(1) by fastforce
  then obtain Cs where Cs:"those (map2 residual (map \<sigma> (var_rule \<alpha>)) As) = Some Cs"  
    using assms(1) by fastforce
  with l have l2:"length Cs = length As" 
    using length_those by fastforce 
  with Cs have "\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) re As!i = Some (Cs!i)" 
    using l those_some2 by fastforce 
  with \<sigma> Cs assms(1) l2 show ?thesis by auto
qed

text\<open>@{text "t / A = tgt(A)"}\<close>
lemma res_empty1:
  assumes "is_empty_step t" "co_initial A t" "A \<in> wf_pterm R"
  shows "t re A = Some (to_pterm (target A))"
proof - 
  from assms(1,2) have "t = to_pterm (source A)"
    by (simp add: empty_coinitial)
  then show ?thesis using assms(3) proof (induction A arbitrary: t)
    case (Var x)
    then show ?case by simp
  next
    case (Pfun f As)
    let ?ts = "(map (to_pterm \<circ> source) As)"
    from Pfun(3) have "\<forall>a \<in> set As. a \<in> wf_pterm R" by blast 
    with Pfun(1) have "those (map2 residual ?ts As) = Some (map (to_pterm \<circ> target) As)" by (simp add:those_some)
    then show ?case unfolding Pfun(2) by simp
  next
    case (Prule \<alpha> As)
    let ?ts = "(map (to_pterm \<circ> source) As)"
    from Prule(3) have l:"length ?ts = length (var_rule \<alpha>)" using wf_pterm.simps by fastforce 
    moreover from Prule(3) have well:"\<forall>a \<in> set As. a \<in> wf_pterm R" by blast 
    from Prule(1) have args:"those (map2 residual ?ts As) = Some (map (to_pterm \<circ> target) As)" using well by (simp add:those_some)
    from Prule(2) have t:"t = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>?ts\<rangle>\<^sub>\<alpha>" by (simp add: to_pterm_subst) 
    then obtain \<sigma> where \<sigma>:
      "match t (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
      "(\<forall>x\<in> set (var_rule \<alpha>). (\<langle>?ts\<rangle>\<^sub>\<alpha>) x = \<sigma> x)"
      using lhs_subst_trivial by blast 
    from \<sigma>(2) l have ts:"map \<sigma> (var_rule \<alpha>) = ?ts" by (smt apply_lhs_subst_var_rule map_eq_conv) 
    from Prule(1) have "those (map2 residual ?ts As) = Some (map (to_pterm \<circ> target) As)" using well by (simp add:those_some) 
    with ts have args:"those (map2 residual (map \<sigma> (var_rule \<alpha>)) As) = Some (map (to_pterm \<circ> target) As)" by simp
    show ?case proof (cases t rule:source.cases)
      case (1 x)
      then show ?thesis using args \<sigma>(1) by (simp add: to_pterm_subst) 
    next
      case (2 f As)
      then show ?thesis using args \<sigma>(1) by (simp add: to_pterm_subst) 
    next
      case (3 \<alpha> As)
      then show ?thesis using Prule(2) by (metis is_empty_step.simps(3) to_pterm_empty)
    qed
  qed
qed

text\<open>@{text "A / t = A"}\<close>
lemma res_empty2:
  assumes "A \<in> wf_pterm R"
  shows "A re (to_pterm (source A)) = Some A"
using assms proof (induction A)
  case (2 As f)
  then have "those (map2 residual As (map (to_pterm \<circ> source) As)) = Some As" by (simp add:those_some) 
  then show ?case by simp
next
  case (3 \<alpha> As)
  then have \<sigma>: "match (to_pterm (lhs \<alpha> \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>)) (to_pterm (lhs \<alpha>)) = Some (\<langle>map (to_pterm \<circ> source) As\<rangle>\<^sub>\<alpha>)"
    by (metis (no_types, lifting) fun_mk_subst lhs_subst_trivial map_map to_pterm.simps(1) to_pterm_subst) 
  from 3 have "those (map2 residual As (map (to_pterm \<circ> source) As)) = Some As" 
    by (simp add:those_some) 
  then have args:"those (map2 residual As (map (\<langle>map (to_pterm \<circ> source) As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>))) = Some As"
    by (metis "3.hyps"(2) apply_lhs_subst_var_rule length_map) 
  show ?case proof(cases "source (Prule \<alpha> As)")
    case (Var x)
    then show ?thesis 
      using \<sigma> residual.simps(4)[of \<alpha> As x] args by auto
  next
    case (Fun f ts)
    then show ?thesis 
      using \<sigma> residual.simps(5)[of \<alpha> As f] args by auto
  qed
qed simp

text\<open>@{text "A / A = tgt(A)"}\<close>
lemma res_same: "A re A = Some (to_pterm (target A))"
proof(induction A)
case (Var x)
then show ?case by simp
next
  case (Pfun f As)
  then have "list_all (\<lambda>x. x \<noteq> None) (map2 residual As As)" by (simp add: list_all_length)
  then obtain xs where xs:"those (map2 residual As As) = Some xs" using those_not_none_xs by fastforce
  then have l:"length As = length xs" using length_those by fastforce
  from xs have IH:"i < length As \<Longrightarrow> xs!i = to_pterm (target (As!i))" for i using Pfun those_some2 by force
  from IH l have "map (to_pterm\<circ>target) As = xs" by (simp add: map_nth_eq_conv)
  then have "to_pterm (target (Pfun f As)) = Pfun f xs" by simp 
  then show ?case using xs by simp
next
  case (Prule \<alpha> As)
  then have "list_all (\<lambda>x. x \<noteq> None) (map2 residual As As)" by (simp add: list_all_length)
  then obtain xs where xs:"those (map2 residual As As) = Some xs" using those_not_none_xs by fastforce
  then have l:"length As = length xs" using length_those by fastforce
  from xs have IH:"i < length As \<Longrightarrow> xs!i = to_pterm (target (As!i))" for i using Prule those_some2 by force
  from IH l have *:"map (to_pterm\<circ>target) As = xs" by (simp add: map_nth_eq_conv)
  have "to_pterm (target (Prule \<alpha> As)) = to_pterm (rhs \<alpha> \<cdot> \<langle>map target As\<rangle>\<^sub>\<alpha>)" by simp
  also have "... = (to_pterm (rhs \<alpha>)) \<cdot> (to_pterm \<circ> \<langle>map target As\<rangle>\<^sub>\<alpha>)" by (simp add: to_pterm_subst) 
  also have "... = (to_pterm (rhs \<alpha>)) \<cdot> \<langle>xs\<rangle>\<^sub>\<alpha>" using * by simp 
  finally show ?case using xs by simp
qed

lemma residual_src_tgt: 
  assumes "A re B = Some C" "A \<in> wf_pterm R" "B \<in> wf_pterm S"
  shows "source C = target B"
  using assms proof(induction A B arbitrary: C rule: residual.induct)
  case (1 x y)
  then show ?case
    by (metis option.distinct(1) option.sel residual.simps(1) source.simps(1) target.simps(1)) 
next
  case (2 f As g Bs)
  then obtain Cs where *:"f = g \<and> length As = length Bs \<and>
      C = Pfun f Cs \<and> length Cs = length As \<and> 
      (\<forall>i<length As. As ! i re Bs ! i = Some (Cs ! i))" 
    by (meson residual_fun_fun) 
  then have "length (zip As Bs) = length As" by simp 
  moreover from 2(3) have "\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  moreover from 2(4) have "\<forall>b \<in> set Bs. b \<in> wf_pterm S" by blast
  ultimately have "\<forall>i < length As. source (Cs!i) = target (Bs!i)" 
    using * 2 by (metis nth_mem nth_zip) 
  with * show ?case by (simp add: nth_map_conv)
next
  case (3 \<alpha> As \<beta> Bs)
  then obtain Cs where *:"\<alpha> = \<beta> \<and> length As = length Bs \<and>
      C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and> length Cs = length As \<and> 
      (\<forall>i<length As. As ! i re Bs ! i = Some (Cs ! i))" 
    by (meson residual_rule_rule) 
  then have "length (zip As Bs) = length As" by simp 
  moreover from 3(3) have "\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  moreover from 3(4) have "\<forall>b \<in> set Bs. b \<in> wf_pterm S" by blast
  ultimately have IH:"\<forall>i < length As. source (Cs!i) = target (Bs!i)" 
    using * 3 by (metis nth_mem nth_zip) 
  from * have "source C = (rhs \<beta>) \<cdot> \<langle>map source Cs\<rangle>\<^sub>\<beta>" 
     by (simp add: source_apply_subst)
  also have "... = (rhs \<beta>) \<cdot> \<langle>map target Bs\<rangle>\<^sub>\<beta>" 
    using * IH by (metis nth_map_conv)
  finally show ?case by simp
next
  case ("4_1" \<alpha> As v)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = Prule \<alpha> Cs \<and> length Cs = length As \<and> 
        (\<forall>i<length As. As ! i re \<sigma> (var_rule \<alpha> ! i) = Some (Cs ! i))"
    by (meson residual_rule_var) 
  then obtain Bs where Bs:"length Bs = length (var_rule \<alpha>) \<and> 
                          Var v = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha> \<and>
                          (\<forall>x \<in> set (var_rule \<alpha>). \<sigma> x = (\<langle>Bs\<rangle>\<^sub>\<alpha>) x)" 
    using match_lhs_subst by blast 
  from "4_1"(3) have as:"\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  from "4_1"(3) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  with * have well:"\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm S"  
    using "4_1"(4) by (metis match_well_def vars_to_pterm)  
  from l have "length (zip As (map \<sigma> (var_rule \<alpha>))) = length As" by simp   
  with "4_1"(1,3) well * l as have IH:"\<forall>i < length As. source (Cs!i) = target (map (\<langle>Bs\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>) !i)" 
    using Bs by (smt length_map nth_map nth_mem nth_zip)
  from * have "source C = (lhs \<alpha>) \<cdot> \<langle>map source Cs\<rangle>\<^sub>\<alpha>" 
     by (simp add: source_apply_subst)
  also have "... = (lhs \<alpha>) \<cdot> \<langle>map (target \<circ> (\<langle>Bs\<rangle>\<^sub>\<alpha>)) (var_rule \<alpha>)\<rangle>\<^sub>\<alpha>" 
    using * l IH by (smt map_eq_conv' map_map)
  also have "... = (lhs \<alpha>) \<cdot> (target \<circ> (\<langle>Bs\<rangle>\<^sub>\<alpha>))" 
    using Bs by (metis (no_types, lifting) apply_lhs_subst_var_rule fun_mk_subst map_map target.simps(1)) 
  also have "... = target (to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>)"
    by (metis target_empty_apply_subst target_to_pterm to_pterm_empty)
  finally show ?case
    using Bs by fastforce 
next
  case ("4_2" \<alpha> As f Bs)
  then obtain Cs \<sigma> where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = Prule \<alpha> Cs \<and> length Cs = length As \<and> 
        (\<forall>i<length As. As ! i re \<sigma> (var_rule \<alpha> ! i) = Some (Cs ! i))"
    by (meson residual_rule_fun) 
  then obtain Bs' where Bs':"length Bs' = length (var_rule \<alpha>) \<and> 
                          Pfun f Bs = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs'\<rangle>\<^sub>\<alpha> \<and>
                          (\<forall>x \<in> set (var_rule \<alpha>). \<sigma> x = (\<langle>Bs'\<rangle>\<^sub>\<alpha>) x)" 
    using match_lhs_subst by blast 
  from "4_2"(3) have as:"\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  from "4_2"(3) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  with * have well:"\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm S" 
    using "4_2"(4) by (metis match_well_def vars_to_pterm)  
  from l have "length (zip As (map \<sigma> (var_rule \<alpha>))) = length As" by simp   
  with "4_2"(1,3) well * l as have IH:"\<forall>i < length As. source (Cs!i) = target (map (\<langle>Bs'\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>) !i)" 
    using Bs' by (smt length_map nth_map nth_mem nth_zip)
  from * have "source C = (lhs \<alpha>) \<cdot> \<langle>map source Cs\<rangle>\<^sub>\<alpha>" 
     by (simp add: source_apply_subst)
  also have "... = (lhs \<alpha>) \<cdot> \<langle>map (target \<circ> (\<langle>Bs'\<rangle>\<^sub>\<alpha>)) (var_rule \<alpha>)\<rangle>\<^sub>\<alpha>" 
    using * l IH by (smt map_eq_conv' map_map)
  also have "... = (lhs \<alpha>) \<cdot> (target \<circ> (\<langle>Bs'\<rangle>\<^sub>\<alpha>))" 
    using Bs' by (metis (no_types, lifting) apply_lhs_subst_var_rule fun_mk_subst map_map target.simps(1)) 
  also have "... = target (to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs'\<rangle>\<^sub>\<alpha>)"
    by (metis target_empty_apply_subst target_to_pterm to_pterm_empty)
  finally show ?case
    using Bs' by fastforce 
next
  case ("5_1" v \<alpha> As)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and> length Cs = length As \<and> 
        (\<forall>i<length As. \<sigma> (var_rule \<alpha> ! i) re As ! i  = Some (Cs ! i))"
    by (meson residual_var_rule) 
  from "5_1"(4) have as:"\<forall>a \<in> set As. a \<in> wf_pterm S" by blast
  from "5_1"(4) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  with * have well:"\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
    using "5_1"(3) by (metis match_well_def vars_to_pterm)  
  from l have "length (zip (map \<sigma> (var_rule \<alpha>)) As) = length As" by simp   
  with "5_1"(1,4) well * l as have IH:"\<forall>i < length As. source (Cs!i) = target (As!i)" 
    by (smt length_map nth_map nth_mem nth_zip)
  from * have "source C = (rhs \<alpha>) \<cdot> \<langle>map source Cs\<rangle>\<^sub>\<alpha>" 
     by (simp add: source_apply_subst)
  also have "... = (rhs \<alpha>) \<cdot> \<langle>map target As\<rangle>\<^sub>\<alpha>" 
    using * IH by (metis (no_types, lifting) map_eq_conv')
  finally show ?case by simp
next
  case ("5_2" f Bs \<alpha> As)
    then obtain Cs \<sigma> where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and> length Cs = length As \<and> 
        (\<forall>i<length As. \<sigma> (var_rule \<alpha> ! i) re As ! i  = Some (Cs ! i))"
      by (meson residual_fun_rule) 
  from "5_2"(4) have as:"\<forall>a \<in> set As. a \<in> wf_pterm S" by blast
  from "5_2"(4) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  with * have well:"\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
    using "5_2"(3) by (metis match_well_def vars_to_pterm)  
  from l have "length (zip (map \<sigma> (var_rule \<alpha>)) As) = length As" by simp   
  with "5_2"(1,4) well * l as have IH:"\<forall>i < length As. source (Cs!i) = target (As!i)" 
    by (smt length_map nth_map nth_mem nth_zip)
  from * have "source C = (rhs \<alpha>) \<cdot> \<langle>map source Cs\<rangle>\<^sub>\<alpha>" 
     by (simp add: source_apply_subst)
  also have "... = (rhs \<alpha>) \<cdot> \<langle>map target As\<rangle>\<^sub>\<alpha>" 
    using * IH by (metis (no_types, lifting) map_eq_conv')
  finally show ?case by simp
qed simp_all

text\<open>The following two lemmas are used inside the induction proof for the result 
@{text "tgt(A / B) = tgt(B / A)"}. Defining them here, outside the main proof makes 
them reusable for the symmetric cases of the proof.\<close>
lemma tgt_tgt_rule_var:
  assumes "\<And>\<sigma> a b c d. match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<Longrightarrow>
           (a,b) \<in> set (zip As (map \<sigma> (var_rule \<alpha>))) \<Longrightarrow> 
            a re b = Some c \<Longrightarrow> b re a = Some d \<Longrightarrow> a \<in> wf_pterm R \<Longrightarrow> b \<in> wf_pterm S \<Longrightarrow> 
            target c = target d"
          "Prule \<alpha> As re Var v = Some C"
          "Var v re Prule \<alpha> As = Some D"
          "Prule \<alpha> As \<in> wf_pterm R" 
  shows "target C = target D"
proof-
  from assms(4) have l:"length As = length (var_rule \<alpha>)" 
    using wf_pterm.simps by fastforce 
  from assms(4) have as:"\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  from assms(2,4) obtain \<sigma> where \<sigma>:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
    by (meson residual_rule_var)
  with l have well_def:"\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm S" 
    using match_well_def by (metis vars_to_pterm wf_pterm.intros(1))
  from assms(2,4) \<sigma> obtain Cs where Cs: 
      "C = Prule \<alpha> Cs \<and> length Cs = length As"
      "(\<forall>i<length As. As ! i re \<sigma> (var_rule \<alpha> ! i) = Some (Cs ! i))"
    by (metis option.inject residual_rule_var)
  from assms(3,4) \<sigma> obtain Ds where Ds: 
      "D = to_pterm (rhs \<alpha>) \<cdot> \<langle>Ds\<rangle>\<^sub>\<alpha> \<and> length Ds = length As" 
      "(\<forall>i<length As. \<sigma> (var_rule \<alpha> ! i) re As ! i = Some (Ds ! i))"
    by (metis option.inject residual_var_rule)
  from l have "length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp 
  with assms(1,4) \<sigma> l Cs(2) Ds(2) well_def have IH:"\<forall>i < length As. target (Cs!i) = target (Ds!i)" 
    using as by (smt length_map nth_map nth_mem nth_zip)
  from Cs have "target C = (rhs \<alpha>) \<cdot> \<langle>map target Cs\<rangle>\<^sub>\<alpha>" by simp
  moreover from Ds(1) have "target D = (rhs \<alpha>) \<cdot> \<langle>map target Ds\<rangle>\<^sub>\<alpha>" 
    using target_empty_apply_subst to_pterm_empty by (metis fun_mk_subst target.simps(1) target_to_pterm)
  ultimately show ?thesis 
    using IH Cs(1) Ds(1) by (metis nth_map_conv)
qed

lemma tgt_tgt_rule_fun:
  assumes "\<And>\<sigma> a b c d. match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<Longrightarrow>
           (a,b) \<in> set (zip As (map \<sigma> (var_rule \<alpha>))) \<Longrightarrow> 
            a re b = Some c \<Longrightarrow> b re a = Some d \<Longrightarrow> a \<in> wf_pterm R \<Longrightarrow> b \<in> wf_pterm S \<Longrightarrow> 
            target c = target d"
          "Prule \<alpha> As re Pfun f Bs = Some C"
          "Pfun f Bs re Prule \<alpha> As = Some D"
          "Prule \<alpha> As \<in> wf_pterm R" 
          "Pfun f Bs \<in> wf_pterm S"
  shows "target C = target D"
proof-
  from assms(4) have l:"length As = length (var_rule \<alpha>)" 
    using wf_pterm.simps by fastforce 
  from assms(4) have as:"\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  from assms(2,4) obtain \<sigma> where \<sigma>:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
    by (meson residual_rule_fun)
  with assms(2,5) l have well_def:"\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm S" 
    using match_well_def by (metis vars_to_pterm)
  from assms(2,4) \<sigma> obtain Cs where Cs: 
      "C = Prule \<alpha> Cs \<and> length Cs = length As"
      "(\<forall>i<length As. As ! i re \<sigma> (var_rule \<alpha> ! i) = Some (Cs ! i))"
    by (metis option.inject residual_rule_fun)
  from assms(3,4) \<sigma> obtain Ds where Ds: 
      "D = to_pterm (rhs \<alpha>) \<cdot> \<langle>Ds\<rangle>\<^sub>\<alpha> \<and> length Ds = length As" 
      "(\<forall>i<length As. \<sigma> (var_rule \<alpha> ! i) re As ! i = Some (Ds ! i))"
    by (metis option.inject residual_fun_rule)
  from l have "length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp 
  with assms(1,4,5) \<sigma> l Cs(2) Ds(2) well_def have IH:"\<forall>i < length As. target (Cs!i) = target (Ds!i)" 
    using as by (smt length_map nth_map nth_mem nth_zip)
  from Cs have "target C = (rhs \<alpha>) \<cdot> \<langle>map target Cs\<rangle>\<^sub>\<alpha>" by simp
  moreover from Ds(1) have "target D = (rhs \<alpha>) \<cdot> \<langle>map target Ds\<rangle>\<^sub>\<alpha>" 
    using target_empty_apply_subst to_pterm_empty by (metis fun_mk_subst target.simps(1) target_to_pterm)
  ultimately show ?thesis 
    using IH Cs(1) Ds(1) by (metis nth_map_conv)
qed

lemma residual_tgt_tgt:
  assumes "A re B = Some C" "B re A = Some D" "A \<in> wf_pterm R" "B \<in> wf_pterm S"
  shows "target C = target D"
  using assms proof(induction A B arbitrary: C D rule:residual.induct)
  case (1 x y)
  then show ?case by (metis option.sel residual.simps(1)) 
next
  case (2 f As g Bs)
  from 2(4) have as:"\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  from 2(5) have bs:"\<forall>b \<in> set Bs. b \<in> wf_pterm S" by blast
  let ?l = "length As"
  from 2(2) have *: "f = g \<and> ?l = length Bs" 
    by (meson residual_fun_fun)
  from 2(2) obtain Cs where Cs:
    "C = Pfun f Cs \<and> length Cs = ?l \<and> (\<forall>i < ?l. As ! i re Bs ! i = Some (Cs ! i))" 
    by (meson residual_fun_fun)
  from 2(3) obtain Ds where Ds:
    "D = Pfun g Ds \<and> length Ds = ?l \<and> (\<forall>i < ?l. Bs ! i re As ! i = Some (Ds ! i))" 
    using * by (metis residual_fun_fun)
  from * have "length (zip As Bs) = ?l" by simp 
  with 2(1,4,5) * Cs Ds have "\<forall>i < ?l. target (Cs!i) = target (Ds!i)" 
    using as bs by (metis nth_mem nth_zip)   
  with * Cs Ds show ?case
    by (simp add: map_nth_eq_conv) 
next
  case (3 \<alpha> As \<beta> Bs)
  from 3(4) have as:"\<forall>a \<in> set As. a \<in> wf_pterm R" by blast
  from 3(5) have bs:"\<forall>b \<in> set Bs. b \<in> wf_pterm S" by blast
  let ?l = "length As"
  from 3(2,4,5) have *: "\<alpha> = \<beta> \<and> ?l = length Bs" 
    by (meson residual_rule_rule)
  from 3(2,4,5) obtain Cs where Cs:
    "C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and> length Cs = ?l \<and> (\<forall>i < ?l. As ! i re Bs ! i = Some (Cs ! i))" 
    by (meson residual_rule_rule)
  from 3(3,4,5) obtain Ds where Ds:
    "D = to_pterm (rhs \<alpha>) \<cdot> \<langle>Ds\<rangle>\<^sub>\<alpha> \<and> length Ds = ?l \<and> (\<forall>i < ?l. Bs ! i re As ! i = Some (Ds ! i))" 
    using * by (metis residual_rule_rule) 
  from * have "length (zip As Bs) = ?l" by simp 
  with 3(1,4,5) * Cs Ds have IH:"\<forall>i < ?l. target (Cs!i) = target (Ds!i)" 
    using as bs by (metis nth_mem nth_zip) 
  from Cs have "target C = (rhs \<alpha>) \<cdot> \<langle>map target Cs\<rangle>\<^sub>\<alpha>" 
    using target_empty_apply_subst to_pterm_empty by (metis fun_mk_subst target.simps(1) target_to_pterm)
  moreover from Ds have "target D = (rhs \<alpha>) \<cdot> \<langle>map target Ds\<rangle>\<^sub>\<alpha>" 
    using target_empty_apply_subst to_pterm_empty by (metis fun_mk_subst target.simps(1) target_to_pterm)
  ultimately show ?case 
    using IH Cs Ds by (metis nth_map_conv)
next 
  case ("4_1" \<alpha> As v)
  then show ?case using tgt_tgt_rule_var by fastforce
next
  case ("4_2" \<alpha> As f Bs)
  then show ?case using tgt_tgt_rule_fun by fastforce 
next
  case ("5_1" v \<alpha> As)
  from "5_1"(1) have "match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<Longrightarrow>
    (a,b) \<in> set (zip As (map \<sigma> (var_rule \<alpha>))) \<Longrightarrow>
    a re b = Some c \<Longrightarrow> b re a = Some d \<Longrightarrow> a \<in> wf_pterm S \<Longrightarrow> b \<in> wf_pterm R \<Longrightarrow> 
    target c = target d" for \<sigma> a b c d 
    using zip_symm by fastforce 
  with "5_1"(2,3,5) have "target D = target C" using tgt_tgt_rule_var by fastforce 
  then show ?case by simp
next
  case ("5_2" f Bs \<alpha> As)
  from "5_2"(1) have "match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<Longrightarrow>
    (a,b) \<in> set (zip As (map \<sigma> (var_rule \<alpha>))) \<Longrightarrow>
    a re b = Some c \<Longrightarrow> b re a = Some d \<Longrightarrow> a \<in> wf_pterm S \<Longrightarrow> b \<in> wf_pterm R \<Longrightarrow> 
    target c = target d" for \<sigma> a b c d 
    using zip_symm by fastforce 
  with "5_2"(2,3,4,5) have "target D = target C" using tgt_tgt_rule_fun by fastforce 
  then show ?case by simp
qed simp_all

lemma rule_residual_lhs:
  assumes args:"those (map2 (re) As Bs) = Some Cs"
    and is_Fun:"is_Fun (lhs \<alpha>)" and l:"length Bs = length (var_rule \<alpha>)" 
  shows "Prule \<alpha> As re (to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) = Some (Prule \<alpha> Cs)" 
proof-
  from is_Fun obtain f ts where "lhs \<alpha> = Fun f ts"
    by auto 
  then have f:"to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha> = Pfun f (map (\<lambda>t. t \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) (map to_pterm ts))" 
    by simp
  then have match:"match ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) (to_pterm (lhs \<alpha>)) = Some (\<langle>Bs\<rangle>\<^sub>\<alpha>)"
    using lhs_subst_trivial by blast 
  from l have "map (\<langle>Bs\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>) = Bs"
    using apply_lhs_subst_var_rule by blast  
  with args have "those (map2 (re) As (map (\<langle>Bs\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>))) = Some Cs"  
    by presburger
  then show ?thesis 
    using residual.simps(5) match unfolding f by auto 
qed

lemma residual_well_defined: 
  assumes "A \<in> wf_pterm R" "B \<in> wf_pterm S" "A re B = Some C"
  shows "C \<in> wf_pterm R"
  using assms proof(induction A B arbitrary:C rule:residual.induct)
  case (1 x y)
  then show ?case 
    by (metis option.distinct(1) option.sel residual.simps(1))
next
  case (2 f As g Bs)
  then obtain Cs where "f = g \<and> length As = length Bs \<and> 
        C = Pfun f Cs \<and> 
        length Cs = length As \<and> 
        (\<forall>i < length As. As!i re Bs!i = Some (Cs!i))" 
    by (meson residual_fun_fun)
  moreover with 2 have "i < length As \<Longrightarrow> Cs!i \<in> wf_pterm R" for i 
    using fun_well_arg by (metis (no_types, opaque_lifting) fst_conv in_set_zip nth_mem snd_conv) 
  ultimately show ?case
    by (metis in_set_conv_nth wf_pterm.intros(2))
next
  case (3 \<alpha> As \<beta> Bs)
  then obtain Cs where "\<alpha> = \<beta> \<and> length As = length Bs \<and> 
        (C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha> \<and>
        length Cs = length As \<and> 
        (\<forall>i < length As. As!i re Bs!i = Some (Cs!i)))"
    by (meson residual_rule_rule)
  moreover with 3 have "i < length As \<Longrightarrow> Cs!i \<in> wf_pterm R" for i 
    using fun_well_arg by (metis (no_types, opaque_lifting) fst_conv in_set_zip nth_mem snd_conv) 
  ultimately show ?case 
    by (metis to_pterm_wf_pterm lhs_subst_well_def) 
next
  case ("4_1" \<alpha> As v)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        C = Prule \<alpha> Cs \<and> 
        length Cs = length As \<and>
        (\<forall>i < length As. As!i re (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i))"
    by (meson residual_rule_var)
  from "4_1"(2) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "4_1"(2) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce  
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))" 
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm S" 
    using "4_1"(3) by (metis match_well_def vars_to_pterm)
  with "4_1"(1) * wellA l2 have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt (z3) l length_map nth_map nth_mem nth_zip)
  with "4_1"(2) * show ?case
    by (smt (verit) Inr_not_Inl in_set_conv_nth term.distinct(1) term.inject(2) wf_pterm.cases wf_pterm.intros(3)) 
next
  case ("4_2" \<alpha> As f Bs)
  then obtain \<sigma> Cs where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        (C = Prule \<alpha> Cs \<and> 
        length Cs = length As \<and>
        (\<forall>i < length As. As!i re (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)))"
    by (meson residual_rule_fun)
  from "4_2"(2) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "4_2"(2) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce  
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))" 
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm S" 
    using "4_2"(3) by (metis match_well_def vars_to_pterm)  
  with "4_2"(1) * wellA l2 have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt l length_map nth_map nth_mem nth_zip)
  with "4_2"(2) * show ?case
    by (smt (verit, ccfv_threshold) Inr_not_Inl in_set_conv_nth term.distinct(1) term.inject(2) wf_pterm.cases wf_pterm.intros(3))
next
  case ("5_1" v \<alpha> As)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha>  \<and> 
        length Cs = length As \<and>
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) re As!i = Some (Cs!i))"
    by (meson residual_var_rule)
  from "5_1"(3) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm S"
    by auto
  from "5_1"(3) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce  
  then have l2:"length As = length (zip (map \<sigma> (var_rule \<alpha>)) As)" 
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
    using "5_1"(2) by (metis match_well_def vars_to_pterm)  
  with "5_1"(1) * wellA l2 have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt l length_map nth_map nth_mem nth_zip)
  with * show ?case
    by (metis lhs_subst_well_def to_pterm_wf_pterm) 
next
  case ("5_2" f Bs \<alpha> As)
  then obtain Cs \<sigma> where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and> 
        C = to_pterm (rhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha>  \<and> 
        length Cs = length As \<and>
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) re As!i = Some (Cs!i))"
    by (meson residual_fun_rule)
  from "5_2"(3) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm S"
    by auto
  from "5_2"(3) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce  
  then have l2:"length As = length (zip (map \<sigma> (var_rule \<alpha>)) As)" 
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
    using "5_2"(2) by (metis match_well_def vars_to_pterm)  
  with "5_2"(1) * wellA l2 have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt l length_map nth_map nth_mem nth_zip)
  with * show ?case
    by (metis lhs_subst_well_def to_pterm_wf_pterm) 
qed simp_all

no_notation sup (infixl "\<squnion>" 65)

subsection\<open>Join\<close>
fun join :: "('f, 'v) pterm \<Rightarrow> ('f,'v) pterm \<Rightarrow> ('f,'v) pterm option" (infixr "\<squnion>" 70)
  where
  "Var x \<squnion> Var y =
    (if x = y then Some (Var x) else None)"
| "Pfun f As \<squnion> Pfun g Bs =
    (if (f = g \<and> length As = length Bs) then
      (case those (map2 (\<squnion>) As Bs) of
        Some xs \<Rightarrow> Some (Pfun f xs)
      | None \<Rightarrow> None)
    else None)"
| "Prule \<alpha> As \<squnion> Prule \<beta> Bs =
    (if \<alpha> = \<beta> then
      (case those (map2 (\<squnion>) As Bs) of
        Some xs \<Rightarrow> Some (Prule \<alpha> xs)
      | None \<Rightarrow> None)
    else None)"
| "Prule \<alpha> As \<squnion> B =
    (case match B (to_pterm (lhs \<alpha>)) of
      None \<Rightarrow> None
    | Some \<sigma> \<Rightarrow>
      (case those (map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) of
        Some xs \<Rightarrow> Some (Prule \<alpha> xs)
      | None \<Rightarrow> None))"
| "A \<squnion> Prule \<alpha> Bs =
    (case match A (to_pterm (lhs \<alpha>)) of
      None \<Rightarrow> None
    | Some \<sigma> \<Rightarrow>
      (case those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Bs) of
        Some xs \<Rightarrow> Some (Prule \<alpha> xs)
      | None \<Rightarrow> None))"
| "A \<squnion> B = None"

lemma join_sym: "A \<squnion> B = B \<squnion> A"
proof(induct rule:join.induct)
  case (2 f As g Bs)
  then show ?case proof(cases "f = g \<and> length As = length Bs")
    case True
    with 2 have "\<forall>(a,b) \<in> set (zip As Bs). a \<squnion> b = b \<squnion> a"
      by auto
    with True have "(map2 (\<squnion>) As Bs) = (map2 (\<squnion>) Bs As)"
      by (smt case_prod_unfold map_eq_conv' map_fst_zip map_snd_zip nth_mem)
    then show ?thesis using 2 unfolding join.simps
      by auto
  qed auto
next
  case (3 \<alpha> As \<beta> Bs)
  then show ?case proof(cases "\<alpha> = \<beta>")
    case True
    with 3 have *:"\<forall>(a,b) \<in> set (zip As Bs). a \<squnion> b = b \<squnion> a"
      by auto
    have "length (map2 (\<squnion>) As Bs) = length (map2 (\<squnion>) Bs As)"
      by auto
    with * have "(map2 (\<squnion>) As Bs) = (map2 (\<squnion>) Bs As)"
      by (smt fst_conv length_map length_zip map_eq_conv' min_less_iff_conj nth_mem nth_zip prod.case_eq_if snd_conv)
    then show ?thesis using 3 unfolding join.simps
      by auto
  qed auto
next
  case ("4_1" \<alpha> As v)
  then show ?case proof(cases "match (Var v) (to_pterm (lhs \<alpha>)) = None")
    case False
    then obtain \<sigma> where sigma:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
      by blast
    with "4_1" have *:"\<forall>(a,b) \<in> set (zip As (map \<sigma> (var_rule \<alpha>))). a \<squnion> b = b \<squnion> a"
      by auto
    have "length (map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) = length (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) As)"
      by auto
    with * have "(map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) = (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) As)"
      by (smt fst_conv length_map length_zip map_eq_conv' min_less_iff_conj nth_mem nth_zip prod.case_eq_if snd_conv)
    then show ?thesis unfolding join.simps sigma
      by simp
  qed simp
next
  case ("4_2" \<alpha> As f Bs)
  then show ?case proof(cases "match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = None")
    case False
    then obtain \<sigma> where sigma:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
      by blast
    with "4_2" have *:"\<forall>(a,b) \<in> set (zip As (map \<sigma> (var_rule \<alpha>))). a \<squnion> b = b \<squnion> a"
      by auto
    have "length (map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) = length (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) As)"
      by auto
    with * have "(map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) = (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) As)"
      by (smt fst_conv length_map length_zip map_eq_conv' min_less_iff_conj nth_mem nth_zip prod.case_eq_if snd_conv)
    then show ?thesis unfolding join.simps sigma
      by simp
  qed simp
next
  case ("5_1" v \<alpha> Bs)
  then show ?case proof(cases "match (Var v) (to_pterm (lhs \<alpha>)) = None")
    case False
    then obtain \<sigma> where sigma:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
      by blast
    with "5_1" have *:"\<forall>(a,b) \<in> set (zip (map \<sigma> (var_rule \<alpha>)) Bs). a \<squnion> b = b \<squnion> a"
      by auto
    have "length (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Bs) = length (map2 (\<squnion>) Bs (map \<sigma> (var_rule \<alpha>)))"
      by auto
    with * have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Bs) = (map2 (\<squnion>) Bs (map \<sigma> (var_rule \<alpha>)))"
      by (smt fst_conv length_map length_zip map_eq_conv' min_less_iff_conj nth_mem nth_zip prod.case_eq_if snd_conv)
    then show ?thesis unfolding join.simps sigma
      by simp
  qed simp
next
  case ("5_2" f As \<alpha> Bs)
  then show ?case proof(cases "match (Pfun f As) (to_pterm (lhs \<alpha>)) = None")
    case False
    then obtain \<sigma> where sigma:"match (Pfun f As) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
      by blast
    with "5_2" have *:"\<forall>(a,b) \<in> set (zip (map \<sigma> (var_rule \<alpha>)) Bs). a \<squnion> b = b \<squnion> a"
      by auto
    have "length (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Bs) = length (map2 (\<squnion>) Bs (map \<sigma> (var_rule \<alpha>)))"
      by auto
    with * have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Bs) = (map2 (\<squnion>) Bs (map \<sigma> (var_rule \<alpha>)))"
      by (smt fst_conv length_map length_zip map_eq_conv' min_less_iff_conj nth_mem nth_zip prod.case_eq_if snd_conv)
    then show ?thesis unfolding join.simps sigma
      by simp
  qed simp
qed simp_all

lemma join_with_source:
  assumes "A \<in> wf_pterm R"
  shows "A \<squnion> to_pterm (source A) = Some A"
using assms proof(induct A)
  case (2 As f)
  then have "\<forall>i < length As. (map2 (\<squnion>) As (map to_pterm (map source As)))!i = Some (As!i)"
    by simp
  then have "those (map2 (\<squnion>) As (map to_pterm (map source As))) = Some As"
    by (simp add: those_some)
  then show ?case
    by simp
next
  case (3 \<alpha> As)
  then have "\<forall>i < length As. (map2 (\<squnion>) As (map to_pterm (map source As)))!i = Some (As!i)"
    by simp
  then have IH:"those (map2 (\<squnion>) As (map to_pterm (map source As))) = Some As"
    by (simp add: those_some)
  from 3(1) have match:"match (to_pterm (source (Prule \<alpha> As))) (to_pterm (lhs \<alpha>)) = Some (\<langle>map (to_pterm \<circ> source) As\<rangle>\<^sub>\<alpha>)"
    by (metis (no_types, lifting) fun_mk_subst lhs_subst_trivial map_map source.simps(3) to_pterm.simps(1) to_pterm_subst)
  from 3(2) have "(map (\<langle>map (to_pterm \<circ> source) As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>)) = map (to_pterm \<circ> source) As"
    by (metis apply_lhs_subst_var_rule length_map)
  with IH match join.simps(4,5) show ?case by(cases "source (Prule \<alpha> As)") simp_all
qed simp

context no_var_lhs
begin

lemma join_subst:
assumes "B \<in> wf_pterm R" and "\<forall>x \<in> vars_term B. \<rho> x \<in> wf_pterm R"
    and "\<forall>x \<in> vars_term B. source (\<rho> x) = \<sigma> x"
  shows "(B \<cdot> (to_pterm \<circ> \<sigma>)) \<squnion> ((to_pterm (source B)) \<cdot> \<rho>) = Some (B \<cdot> \<rho>)"
  using assms proof(induct B)
  case (1 x)
  then show ?case unfolding eval_term.simps source.simps to_pterm.simps o_apply
    using join_with_source by (metis term.set_intros(3) join_sym)
next
  case (2 ts f)
  {fix i assume i:"i < length ts"
    with 2 have "((ts!i) \<cdot> (to_pterm \<circ> \<sigma>)) \<squnion> ((to_pterm (source (ts!i))) \<cdot> \<rho>) = Some (ts!i \<cdot> \<rho>)"
      by (meson nth_mem term.set_intros(4))
    then have "map2 (\<squnion>) (map (\<lambda>t. t \<cdot> (to_pterm \<circ> \<sigma>)) ts) (map (\<lambda>t. t \<cdot> \<rho>) (map to_pterm (map source ts)))!i = Some ((map (\<lambda>t. t \<cdot> \<rho>) ts)!i)"
      using i by fastforce
  }
  then have "those (map2 (\<squnion>) (map (\<lambda>t. t \<cdot> (to_pterm \<circ> \<sigma>)) ts) (map (\<lambda>t. t \<cdot> \<rho>) (map to_pterm (map source ts)))) = Some (map (\<lambda>t. t \<cdot> \<rho>) ts)"
    using those_some by (smt (verit) length_map length_zip min.idem)
  then show ?case
    unfolding source.simps to_pterm.simps eval_term.simps using join.simps(2) by auto
next
  case (3 \<alpha> As)
  from 3(1) no_var_lhs obtain f ts where f:"lhs \<alpha> = Fun f ts"
     by fastforce
  obtain \<tau> where match:"match (to_pterm (lhs \<alpha> \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>) \<cdot> \<rho>) (to_pterm (lhs \<alpha>)) = Some \<tau>"
    and \<tau>:"(\<forall>x\<in>vars_term (lhs \<alpha>). \<tau> x = ((to_pterm \<circ> \<langle>map source As\<rangle>\<^sub>\<alpha>) \<circ>\<^sub>s \<rho>) x)"
    using match_complete' unfolding to_pterm_subst by (smt (verit, best) set_vars_term_list subst_subst vars_to_pterm)
  {fix i assume i:"i < length (var_rule \<alpha>)"
    let ?x ="var_rule \<alpha> ! i"
    have "((to_pterm \<circ> \<langle>map source As\<rangle>\<^sub>\<alpha>) \<circ>\<^sub>s \<rho>) ?x = to_pterm (source (As!i)) \<cdot> \<rho>"
      using i 3(2) by (simp add: mk_subst_distinct subst_compose_def)
    moreover from 3 have "((As!i) \<cdot> (to_pterm \<circ> \<sigma>)) \<squnion> (to_pterm (source (As!i)) \<cdot> \<rho>) = Some ((As!i) \<cdot> \<rho>)"
      by (metis (mono_tags, lifting) i nth_mem term.set_intros(4))
    ultimately have "((As!i) \<cdot> (to_pterm \<circ> \<sigma>)) \<squnion> (\<tau> ?x) = Some ((As!i) \<cdot> \<rho>)"
      using \<tau> by (metis comp_apply i nth_mem set_remdups set_rev set_vars_term_list)
    then have "(map2 (\<squnion>) (map (\<lambda>t. t \<cdot> (to_pterm \<circ> \<sigma>)) As) (map \<tau> (var_rule \<alpha>)))!i = Some ((map (\<lambda>t. t \<cdot> \<rho>) As)!i)"
      using 3(2) i by auto
  }
  then have "those (map2 (\<squnion>) (map (\<lambda>t. t \<cdot> (to_pterm \<circ> \<sigma>)) As) (map \<tau> (var_rule \<alpha>))) = Some (map (\<lambda>t. t \<cdot> \<rho>) As)"
    by (simp add: 3(2) those_some)
  then show ?case
    using match unfolding source.simps to_pterm.simps eval_term.simps f using join.simps(5) f by auto
qed

end

lemma join_same:
  shows "A \<squnion> A = Some A" 
proof(induct A)
  case (Pfun f As)
  {fix i assume i:"i < length As" 
    with Pfun have "As!i \<squnion> As!i = Some (As!i)" by simp
    with i have "(map2 (\<squnion>) As As)!i = Some (As!i)" by simp
  }
  then have "those (map2 (\<squnion>) As As) = Some As"
    by (simp add: those_some) 
  then show ?case unfolding join.simps by simp
next
  case (Prule \<alpha> As)
  {fix i assume i:"i < length As" 
    with Prule have "As!i \<squnion> As!i = Some (As!i)" by simp
    with i have "(map2 (\<squnion>) As As)!i = Some (As!i)" by simp
  }
  then have "those (map2 (\<squnion>) As As) = Some As"
    by (simp add: those_some) 
  then show ?case unfolding join.simps by simp
qed simp

text\<open>Analogous to residuals there are 6 lemmas corresponding to the step cases in induction proofs for joins.\<close>
lemma join_fun_fun:
  assumes "(Pfun f As) \<squnion> (Pfun g Bs) = Some C"
  shows "f = g \<and> length As = length Bs \<and>
        (\<exists>Cs. C = Pfun f Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)))"
proof-
  have *:"f = g \<and> length As = length Bs"
    using assms join.simps(2) by (metis option.simps(3))
  then obtain Cs where Cs:"those (map2 (\<squnion>) As Bs) = Some Cs"
    using assms option.simps(3) option.simps(4) by fastforce
  hence "\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)"
    using * those_some2 by fastforce
  with * Cs assms(1) show ?thesis
    using length_those by fastforce
qed

lemma join_rule_rule:
  assumes "(Prule \<alpha> As) \<squnion> (Prule \<beta> Bs) = Some C"
          "(Prule \<alpha> As) \<in> wf_pterm R"
          "(Prule \<beta> Bs) \<in> wf_pterm R"
  shows "\<alpha> = \<beta> \<and> length As = length Bs \<and>
        (\<exists>Cs. C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)))"
proof-
  have "\<alpha> = \<beta>"
    using assms(1) join.simps(3) by (metis option.simps(3))
  with assms(2,3) have l: "length As = length Bs"
    using length_args_well_Prule by blast
  from \<open>\<alpha> = \<beta>\<close> obtain Cs where Cs:"those (map2 (\<squnion>) As Bs) = Some Cs"
    using assms by fastforce
  hence "\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)"
    using l those_some2 by fastforce
  with \<open>\<alpha> = \<beta>\<close> l Cs assms(1) show ?thesis
    using length_those by fastforce
qed

lemma join_rule_var:
  assumes "(Prule \<alpha> As) \<squnion> (Var x) = Some C"
          "(Prule \<alpha> As) \<in> wf_pterm R"
  shows "\<exists>\<sigma>. match (Var x) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        (\<exists>Cs. C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)))"
proof-
  from assms(2) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.cases by auto
  obtain \<sigma> where \<sigma>:"match (Var x) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
    using assms(1) by fastforce
  then obtain Cs where Cs:"those (map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) = Some Cs"
    using assms(1) by fastforce
  with l have l2:"length Cs = length As"
    using length_those by fastforce
  from Cs have "\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)"
    using l those_some2 by fastforce
  with \<sigma> Cs assms(1) l2 show ?thesis by simp
qed

lemma join_rule_fun:
  assumes "(Prule \<alpha> As) \<squnion> (Pfun f Bs) = Some C"
          "(Prule \<alpha> As) \<in> wf_pterm R"
  shows "\<exists>\<sigma>. match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        (\<exists>Cs. C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)))"
proof-
  from assms(2) have l:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  obtain \<sigma> where \<sigma>:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
    using assms(1) by fastforce
  then obtain Cs where Cs:"those (map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) = Some Cs"
    using assms(1) by fastforce
  with l have l2:"length Cs = length As"
    using length_those by fastforce
  from Cs have "\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)"
    using l those_some2 by fastforce
  with \<sigma> Cs assms(1) l2 show ?thesis by auto
qed

lemma join_wf_pterm:
  assumes "A \<squnion> B = Some C"
    and "A \<in> wf_pterm R" and "B \<in> wf_pterm R"
  shows "C \<in> wf_pterm R"
  using assms proof(induct A B arbitrary:C rule:join.induct)
  case (1 x y)
  then show ?case
    by (metis join.simps(1) option.distinct(1) option.sel)
next
  case (2 f As g Bs)
  then obtain Cs where "f = g \<and> length As = length Bs \<and>
        C = Pfun f Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i))"
    by (meson join_fun_fun)
  moreover with 2 have "i < length As \<Longrightarrow> Cs!i \<in> wf_pterm R" for i
    using fun_well_arg by (metis (no_types, opaque_lifting) fst_conv in_set_zip nth_mem snd_conv)
  ultimately show ?case
    by (metis in_set_conv_nth wf_pterm.intros(2))
next
  case (3 \<alpha> As \<beta> Bs)
  then obtain Cs where "\<alpha> = \<beta> \<and> length As = length Bs \<and>
        (C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)))"
    by (meson join_rule_rule)
  moreover with 3 have "i < length As \<Longrightarrow> Cs!i \<in> wf_pterm R" for i
    using fun_well_arg by (metis (no_types, opaque_lifting) fst_conv in_set_zip nth_mem snd_conv)
  moreover from 3(3) have "to_rule \<alpha> \<in> R"
    using wf_pterm.simps by fastforce
  ultimately show ?case
    by (smt (verit, best) "3.prems"(2) in_set_idx old.sum.distinct(2) term.distinct(1) term.inject(2) wf_pterm.cases wf_pterm.intros(3))
next
  case ("4_1" \<alpha> As v)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i))"
    by (meson join_rule_var)
  from "4_1"(3) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "4_1"(3) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "4_1"(4) by (metis match_well_def vars_to_pterm)
  with "4_1"(1) * wellA l2 have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt (z3) l length_map nth_map nth_mem nth_zip)
  with "4_1"(3) * show ?case
    by (smt (verit) Inr_not_Inl in_set_conv_nth term.distinct(1) term.inject(2) wf_pterm.cases wf_pterm.intros(3))
next
  case ("4_2" \<alpha> As f Bs)
  then obtain \<sigma> Cs where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        (C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)))"
    by (meson join_rule_fun)
  from "4_2"(3) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "4_2"(3) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "4_2"(4) by (metis match_well_def vars_to_pterm)
  with "4_2"(1) * wellA l2 have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt l length_map nth_map nth_mem nth_zip)
  with "4_2"(3) * show ?case
    by (smt (verit, ccfv_threshold) Inr_not_Inl in_set_conv_nth term.distinct(1) term.inject(2) wf_pterm.cases wf_pterm.intros(3))
next
  case ("5_1" v \<alpha> As)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) \<squnion> As!i = Some (Cs!i))"
    using join_rule_var by (metis join_sym)
  from "5_1"(4) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "5_1"(4) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "5_1"(3) by (metis match_well_def vars_to_pterm)
  with "5_1"(1) * wellA l2 l have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt (verit, del_insts) length_map nth_map nth_mem nth_zip zip_symm)
  with "5_1"(4) * show ?case
    by (smt (verit) Inr_not_Inl in_set_conv_nth term.distinct(1) term.inject(2) wf_pterm.cases wf_pterm.intros(3))
next
  case ("5_2" f Bs \<alpha> As)
  then obtain Cs \<sigma> where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = Prule \<alpha> Cs  \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) \<squnion> As!i = Some (Cs!i))"
    using join_sym join_rule_fun by metis
  from "5_2"(4) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "5_2"(4) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip (map \<sigma> (var_rule \<alpha>)) As)"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "5_2"(3) by (metis match_well_def vars_to_pterm)
  with "5_2"(1) * wellA l2 have "\<forall>i < length As. Cs!i \<in> wf_pterm R"
    by (smt l length_map nth_map nth_mem nth_zip)
  with * show ?case
    by (metis "5_2.prems"(3) Inl_inject Inr_not_Inl in_set_idx l term.distinct(1) term.sel(2) wf_pterm.cases wf_pterm.intros(3))
qed auto

lemma source_join:
  assumes "A \<squnion> B = Some C"
    and "A \<in> wf_pterm R" and "B \<in> wf_pterm R"
  shows "co_initial A C"
  using assms proof(induct A B arbitrary:C rule:join.induct)
  case (1 x y)
  then show ?case
    by (metis join.simps(1) option.discI option.sel)
next
  case (2 f As g Bs)
  then obtain Cs where "f = g \<and> length As = length Bs \<and>
        C = Pfun f Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i))"
    by (meson join_fun_fun)
  moreover with 2 have "i < length As \<Longrightarrow> co_initial (As!i) (Cs!i)" for i
    using fun_well_arg by (metis (no_types, opaque_lifting) fst_conv in_set_zip nth_mem snd_conv)
  ultimately show ?case
    by (simp add: nth_map_conv)
next
  case (3 \<alpha> As \<beta> Bs)
  then obtain Cs where "\<alpha> = \<beta> \<and> length As = length Bs \<and>
        (C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> Bs!i = Some (Cs!i)))"
    by (meson join_rule_rule)
  moreover with 3 have "i < length As \<Longrightarrow> co_initial (As!i) (Cs!i)" for i
    using fun_well_arg by (metis (no_types, opaque_lifting) fst_conv in_set_zip nth_mem snd_conv)
  ultimately show ?case
    by (metis (mono_tags, lifting) map_eq_conv' source.simps(3))
next
  case ("4_1" \<alpha> As v)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i))"
    by (meson join_rule_var)
  from "4_1"(3) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "4_1"(3) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "4_1"(4) by (metis match_well_def vars_to_pterm)
  with "4_1"(1) * wellA l2 have "\<forall>i < length As. co_initial (As!i) (Cs!i)"
    by (smt (z3) l length_map nth_map nth_mem nth_zip)
  with "4_1"(3) * show ?case
    by (metis nth_map_conv source.simps(3))
next
  case ("4_2" \<alpha> As f Bs)
  then obtain \<sigma> Cs where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma> \<and>
        (C = Prule \<alpha> Cs \<and>
        length Cs = length As \<and>
        (\<forall>i < length As. As!i \<squnion> (\<sigma> (var_rule \<alpha> ! i)) = Some (Cs!i)))"
    by (meson join_rule_fun)
  from "4_2"(3) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "4_2"(3) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "4_2"(4) by (metis match_well_def vars_to_pterm)
  with "4_2"(1) * wellA l2 have "\<forall>i < length As. co_initial (As!i) (Cs!i)"
    by (smt l length_map nth_map nth_mem nth_zip)
  with "4_2"(3) * show ?case
    by (metis nth_map_conv source.simps(3))
next
  case ("5_1" v \<alpha> As)
  then obtain Cs \<sigma> where *:"match (Var v) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
       "C = Prule \<alpha> Cs"
       "length Cs = length As \<and>
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) \<squnion> As!i = Some (Cs!i))"
    using join_rule_var by (metis join_sym)
  from "5_1"(4) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "5_1"(4) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "5_1"(3) by (metis match_well_def vars_to_pterm)
  with "5_1"(1) * wellA l2 l have IH:"\<forall>i < length As. co_initial ((map \<sigma> (var_rule \<alpha>))!i) (Cs!i)"
    by (smt (verit, del_insts) length_map nth_map nth_mem nth_zip zip_symm)
  moreover have v:"Var v = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>(map \<sigma> (var_rule \<alpha>))\<rangle>\<^sub>\<alpha>"
    using * by (smt (verit, ccfv_threshold) apply_lhs_subst_var_rule map_eq_conv match_lhs_subst)
  show ?case using IH l unfolding v *(2) source.simps
    by (metis "*"(1,3) fun_mk_subst length_map lhs_subst_trivial nth_map_conv option.inject source.simps(1) source_apply_subst source_to_pterm to_pterm_wf_pterm v)
next
  case ("5_2" f Bs \<alpha> As)
  then obtain Cs \<sigma> where *:"match (Pfun f Bs) (to_pterm (lhs \<alpha>)) = Some \<sigma>"
       "C = Prule \<alpha> Cs"
       "length Cs = length As \<and>
        (\<forall>i < length As. (\<sigma> (var_rule \<alpha> ! i)) \<squnion> As!i = Some (Cs!i))"
    using join_rule_fun by (metis join_sym)
  from "5_2"(4) have wellA:"\<forall>i < length As. As!i \<in> wf_pterm R"
    by auto
  from "5_2"(4) have l: "length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce
  then have l2:"length As = length (zip As (map \<sigma> (var_rule \<alpha>)))"
    by simp
  from l * have "\<forall>i < length As. \<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
    using "5_2"(3) by (metis match_well_def vars_to_pterm)
  with "5_2"(1) * wellA l2 l have IH:"\<forall>i < length As. co_initial ((map \<sigma> (var_rule \<alpha>))!i) (Cs!i)"
    by (smt (verit, del_insts) length_map nth_map nth_mem nth_zip zip_symm)
  moreover have f:"Pfun f Bs = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>(map \<sigma> (var_rule \<alpha>))\<rangle>\<^sub>\<alpha>"
    using * by (smt (verit, ccfv_threshold) apply_lhs_subst_var_rule map_eq_conv match_lhs_subst)
  show ?case using IH l unfolding f *(2) source.simps
    by (metis "*"(3) fun_mk_subst length_map nth_map_conv source.simps(1) source_apply_subst source_to_pterm to_pterm_wf_pterm)
qed auto

lemma join_pterm_subst_Some: 
  fixes A B::"('f, 'v) pterm"
  assumes "(A \<cdot> \<sigma>) \<squnion> (A \<cdot> \<tau>) = Some B"
  shows "\<exists>\<rho>. (\<forall>x \<in> vars_term A. \<sigma> x \<squnion> \<tau> x = Some (\<rho> x)) \<and> B = A \<cdot> \<rho> \<and> match B A = Some \<rho>" 
proof-
  let ?join_var="\<lambda>x. the (\<sigma> x \<squnion> \<tau> x)"
  let ?\<rho>="mk_subst Var (zip (vars_distinct A) (map ?join_var (vars_distinct A)))" 
  from assms have "B = A \<cdot> ?\<rho> \<and> (\<forall>x \<in> vars_term A. \<sigma> x \<squnion> \<tau> x = Some (?\<rho> x)) \<and> match B A = Some ?\<rho>" proof(induct A arbitrary: B)
    case (Var x)
    then show ?case
      by (smt (verit) comp_apply eval_term.simps(1) in_set_conv_nth in_set_simps(2) length_map map_nth_conv match_trivial mem_Collect_eq mk_subst_not_mem 
          mk_subst_same option.sel remdups_id_iff_distinct set_vars_term_list single_var singleton_rev_conv subsetI subst_domain_def vars_term_list.simps(1))
  next
    case (Pfun f As)
    let ?\<rho>="mk_subst Var (zip (vars_distinct (Pfun f As)) (map ?join_var (vars_distinct (Pfun f As))))" 
    have rho_domain:"subst_domain ?\<rho> \<subseteq> vars_term (Pfun f As)"
      by (smt (verit, del_insts) comp_apply mem_Collect_eq mk_subst_not_mem set_remdups set_rev set_vars_term_list subsetI subst_domain_def) 
    from Pfun(2) have "those (map2 (\<squnion>) (map (\<lambda>a. a \<cdot> \<sigma>) As) (map (\<lambda>a. a \<cdot> \<tau>) As)) \<noteq> None"
      unfolding eval_term.simps join.simps using option.simps(4) by fastforce 
    then obtain Bs where Bs:"those (map2 (\<squnion>) (map (\<lambda>a. a \<cdot> \<sigma>) As) (map (\<lambda>a. a \<cdot> \<tau>) As)) = Some Bs" "length As = length Bs"
      using length_those by fastforce 
    {fix i assume "i < length As" 
      with Bs have Bs_i:"((As!i) \<cdot> \<sigma>) \<squnion> ((As!i) \<cdot> \<tau>) = Some (Bs!i)"
        using those_some2 by fastforce 
    }note Bs_i=this
    {fix i assume i:"i < length As" 
      let ?\<rho>i="mk_subst Var (zip (vars_distinct (As!i)) (map ?join_var (vars_distinct (As!i))))"
      have "(As!i) \<cdot> ?\<rho> = (As!i) \<cdot> ?\<rho>i"
        by (smt (verit, ccfv_SIG) comp_apply i map_of_zip_map mk_subst_def nth_mem set_remdups set_rev set_vars_term_list term.set_intros(4) term_subst_eq_conv)
      with Pfun(1)[of "As!i"] i Bs_i have "(As!i) \<cdot> ?\<rho> = Bs!i"
        by fastforce  
    }note As_Bs=this 
    with Bs(2) have map_\<rho>:"map (\<lambda>a. a \<cdot> ?\<rho>) As = Bs"
      by (simp add: map_nth_eq_conv) 
    {fix x assume x:"x \<in> vars_term (Pfun f As)"
      then obtain i where "i < length As" "x \<in> vars_term (As!i)"
        by (metis term.sel(4) var_imp_var_of_arg) 
      with Pfun(1)[of "As!i"] Bs_i As_Bs have "\<sigma> x \<squnion> \<tau> x = Some (?\<rho> x)"
        using term_subst_eq_rev by fastforce
    }
    moreover then have "B = Pfun f As \<cdot> ?\<rho>" 
      using Pfun(2) unfolding eval_term.simps join.simps Bs using map_\<rho> by auto
    moreover then have "match B (Pfun f As) = Some ?\<rho>" 
      using match_trivial rho_domain by blast 
    ultimately show ?case by simp
  next
    case (Prule \<alpha> As)
    let ?\<rho>="mk_subst Var (zip (vars_distinct (Prule \<alpha> As)) (map ?join_var (vars_distinct (Prule \<alpha> As))))" 
    have rho_domain:"subst_domain ?\<rho> \<subseteq> vars_term (Prule \<alpha> As)" 
      by (smt (verit, del_insts) comp_apply mem_Collect_eq mk_subst_not_mem set_remdups set_rev set_vars_term_list subsetI subst_domain_def) 
    from Prule(2) have "those (map2 (\<squnion>) (map (\<lambda>a. a \<cdot> \<sigma>) As) (map (\<lambda>a. a \<cdot> \<tau>) As)) \<noteq> None"
      unfolding eval_term.simps join.simps using option.simps(4) by fastforce 
    then obtain Bs where Bs:"those (map2 (\<squnion>) (map (\<lambda>a. a \<cdot> \<sigma>) As) (map (\<lambda>a. a \<cdot> \<tau>) As)) = Some Bs" "length As = length Bs"
      using length_those by fastforce 
    {fix i assume "i < length As" 
      with Bs have Bs_i:"((As!i) \<cdot> \<sigma>) \<squnion> ((As!i) \<cdot> \<tau>) = Some (Bs!i)"
        using those_some2 by fastforce 
    }note Bs_i=this
    {fix i assume i:"i < length As" 
      let ?\<rho>i="mk_subst Var (zip (vars_distinct (As!i)) (map ?join_var (vars_distinct (As!i))))"
      have "(As!i) \<cdot> ?\<rho> = (As!i) \<cdot> ?\<rho>i"
        by (smt (verit, ccfv_SIG) comp_apply i map_of_zip_map mk_subst_def nth_mem set_remdups set_rev set_vars_term_list term.set_intros(4) term_subst_eq_conv)
      with Prule(1)[of "As!i"] i Bs_i have "(As!i) \<cdot> ?\<rho> = Bs!i"
        by fastforce  
    }note As_Bs=this 
    with Bs(2) have map_\<rho>:"map (\<lambda>a. a \<cdot> ?\<rho>) As = Bs"
      by (simp add: map_nth_eq_conv) 
    {fix x assume x:"x \<in> vars_term (Prule \<alpha> As)"
      then obtain i where "i < length As" "x \<in> vars_term (As!i)"
        by (metis term.sel(4) var_imp_var_of_arg) 
      with Prule(1)[of "As!i"] Bs_i As_Bs have "\<sigma> x \<squnion> \<tau> x = Some (?\<rho> x)"
        using term_subst_eq_rev by fastforce
    }
    moreover then have "B = Prule \<alpha> As \<cdot> ?\<rho>" 
      using Prule(2) unfolding eval_term.simps join.simps Bs using map_\<rho> by auto
    moreover then have "match B (Prule \<alpha> As) = Some ?\<rho>" 
      using match_trivial rho_domain by blast 
    ultimately show ?case by simp
  qed
  then show ?thesis by blast 
qed

lemma join_pterm_subst_None: 
  fixes A::"('f, 'v) pterm"
  assumes "(A \<cdot> \<sigma>) \<squnion> (A \<cdot> \<tau>) = None"
  shows "\<exists> x \<in> vars_term A. \<sigma> x \<squnion> \<tau> x = None"
using assms proof(induct A rule:pterm_induct)
  case (Pfun f As)
  from Pfun(2) obtain i where i:"i < length As" "(map2 (\<squnion>) (map (\<lambda>s. s \<cdot> \<sigma>) As) (map (\<lambda>s. s \<cdot> \<tau>) As))!i = None" 
    unfolding eval_term.simps join.simps length_map using those_not_none_xs
    by (smt (verit) length_map list_all_length map2_map_map option.case_eq_if option.distinct(1)) 
  then have "(As!i \<cdot> \<sigma>) \<squnion> (As!i \<cdot> \<tau>) = None" by simp
  with Pfun(1) i(1) obtain x where "x \<in> vars_term (As!i)" and "\<sigma> x \<squnion> \<tau> x = None"
    using nth_mem by blast 
  then show ?case using i(1) by auto
next
  case (Prule \<alpha> As)
  from Prule(2) obtain i where i:"i < length As" "(map2 (\<squnion>) (map (\<lambda>s. s \<cdot> \<sigma>) As) (map (\<lambda>s. s \<cdot> \<tau>) As))!i = None" 
    unfolding eval_term.simps join.simps length_map using those_not_none_xs
    by (smt (verit) length_map list_all_length map2_map_map option.case_eq_if option.distinct(1)) 
  then have "(As!i \<cdot> \<sigma>) \<squnion> (As!i \<cdot> \<tau>) = None" by simp
  with Prule(1) i(1) obtain x where "x \<in> vars_term (As!i)" and "\<sigma> x \<squnion> \<tau> x = None"
    using nth_mem by blast 
  then show ?case using i(1) by auto
qed simp

fun mk_subst_from_list :: "('v \<Rightarrow> ('f, 'v) term) list \<Rightarrow> ('v \<Rightarrow> ('f, 'v) term)" where
  "mk_subst_from_list [] = Var"
| "mk_subst_from_list (\<sigma> # \<sigma>s) = (\<lambda>x. case \<sigma> x of
      Var x \<Rightarrow> mk_subst_from_list \<sigma>s x
    | t \<Rightarrow> t)"

lemma join_is_Fun: 
  assumes join:"A \<squnion> B = Some (Pfun f Cs)"
  shows "\<exists>As. A = Pfun f As \<and> length As = length Cs" 
proof- 
  {assume "\<exists>x. A = Var x" 
    then obtain x where x:"A = Var x" by blast
    from join consider "B = Var x" | "\<exists>\<alpha> Bs. B = Prule \<alpha> Bs" 
      unfolding x by (metis is_Prule.elims(1) join.simps(1) join.simps(9) option.distinct(1)) 
    then have False 
      using join unfolding x by(cases) (simp, metis (mono_tags, lifting) Inl_Inr_False join.simps(6) option.case_eq_if option.distinct(1) option.sel term.inject(2))
  } moreover {assume "\<exists>\<alpha> As. A = Prule \<alpha> As" 
    then obtain \<alpha> As where A:"A = Prule \<alpha> As" by blast
    from join consider "\<exists>x. B = Var x" | "\<exists>g Bs. B = Pfun g Bs" 
      unfolding A by (smt (verit, del_insts) is_Prule.elims(1) join.simps(3) option.case_eq_if option.distinct(1) option.sel term.inject(2))
    then have False 
      using join unfolding A by(cases) (metis (mono_tags, lifting) Inl_Inr_False join.simps(4,5) option.case_eq_if option.distinct(1) option.sel term.inject(2))+ 
  }
  ultimately obtain g As where A:"A = Pfun g As"
    by (meson is_Prule.cases) 
  from join have "f = g" and "length As = length Cs" unfolding A
    by (smt (verit, ccfv_threshold) Inl_Inr_False Residual_Join_Deletion.join_sym join.simps(5) join.simps(8) join_fun_fun not_arg_cong_Inr option.case_eq_if option.inject option.simps(3) pterm_cases term.inject(2))+ 
  with A show ?thesis by force 
qed

lemma join_obtain_subst: 
  assumes join:"A \<squnion> B = Some (to_pterm t \<cdot> \<sigma>)" and "linear_term t"
  shows "(to_pterm t) \<cdot> mk_subst Var (match_substs (to_pterm t) A) = A" 
proof- 
  from assms(2) have lin:"linear_term (to_pterm t)"
    using to_pterm_linear by blast 
  have "\<forall>p\<in>poss (to_pterm t). \<forall>f ts. (to_pterm t) |_ p = Fun f ts \<longrightarrow> (\<exists>As. length ts = length As \<and> A |_ p = Fun f As)"
  using assms proof(induct t arbitrary: A B)
    case (Fun f ts)
    from Fun(2) obtain As where A:"A = Pfun f As" and l_As:"length ts = length As" 
      using join_is_Fun by force 
    from Fun(2) obtain Bs where B:"B = Pfun f Bs" and l_Bs:"length ts = length Bs" 
      using join_is_Fun join_sym by (smt (verit) eval_term.simps(2) length_map to_pterm.simps(2))
    {fix p g ts' assume p:"p \<in> poss (to_pterm (Fun f ts))" "(to_pterm (Fun f ts)) |_p = Fun g ts'"
      have "\<exists>As'. length ts' = length As' \<and> A|_p = Fun g As'" proof(cases p)
        case Nil
        from p(2) show ?thesis unfolding A Nil using l_As by force
      next
        case (Cons i p')
        from p(1) have i:"i < length ts" unfolding Cons by simp
        with p(1) have p':"p' \<in> poss (ts!i)" unfolding Cons
          by (metis poss_Cons_poss poss_list_sound poss_list_to_pterm term.sel(4)) 
        from Fun(2) have "As!i \<squnion> Bs!i = Some (to_pterm (ts!i) \<cdot> \<sigma>)"
          unfolding A B to_pterm.simps eval_term.simps using i l_As l_Bs
          by (smt (verit, ccfv_threshold) args_poss join_fun_fun local.Cons nth_map p(1) term.sel(4) to_pterm.simps(2))
        moreover from Fun(3) i have "linear_term (ts!i)" by simp
        ultimately obtain As' where "length ts' = length As'" and "(As!i)|_p' = Fun g As'" 
          using Fun(1) i p' by (smt (verit) local.Cons nth_map nth_mem p(2) p_in_poss_to_pterm subt_at.simps(2) to_pterm.simps(2)) 
        with i l_As show ?thesis unfolding A Cons by simp
      qed
    }
    then show ?case by simp
  qed  simp
  then show ?thesis using fun_poss_eq_imp_matches[OF lin] by presburger
qed

lemma join_pterm_linear_subst:
  assumes join:"A \<squnion> B = Some (to_pterm t \<cdot> \<sigma>)" and lin:"linear_term t"
  shows "\<exists> \<sigma>\<^sub>A \<sigma>\<^sub>B. A = (to_pterm t \<cdot> \<sigma>\<^sub>A) \<and> B = (to_pterm t \<cdot> \<sigma>\<^sub>B) \<and> (\<forall>x \<in> vars_term t. \<sigma>\<^sub>A x \<squnion> \<sigma>\<^sub>B x = Some (\<sigma> x))" 
proof- 
  let ?\<sigma>\<^sub>A="mk_subst Var (match_substs (to_pterm t) A)"
  let ?\<sigma>\<^sub>B="mk_subst Var (match_substs (to_pterm t) B)"
  from join_obtain_subst[OF join lin] have A:"A = (to_pterm t) \<cdot> ?\<sigma>\<^sub>A" by simp
  from join lin have B:"B = (to_pterm t) \<cdot> ?\<sigma>\<^sub>B" using join_sym join_obtain_subst by metis
  from join_pterm_subst_Some join A B obtain \<rho> 
    where "(\<forall>x\<in>vars_term t. ?\<sigma>\<^sub>A x \<squnion> ?\<sigma>\<^sub>B x = Some (\<rho> x))" and "to_pterm t \<cdot> \<sigma> = to_pterm t \<cdot> \<rho>"
    by (metis set_vars_term_list vars_to_pterm) 
  then show ?thesis
    by (smt (verit, best) A B set_vars_term_list term_subst_eq_rev vars_to_pterm) 
qed

context no_var_lhs
begin
lemma join_rule_lhs:
  assumes wf:"Prule \<alpha> As \<in> wf_pterm R" and args:"\<forall>i < length As. As!i \<squnion> Bs!i \<noteq> None" and l:"length Bs = length As" 
  shows "Prule \<alpha> As \<squnion> (to_pterm (lhs \<alpha>) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) \<noteq> None" 
proof- 
  from wf no_var_lhs obtain f ts where lhs:"lhs \<alpha> = Fun f ts"
    by (metis Inl_inject Term.term.simps(2) Term.term.simps(4) case_prodD is_Prule.simps(1) is_Prule.simps(3) term.collapse(2) wf_pterm.simps)
  from args l have "those (map2 (\<squnion>) As Bs) \<noteq> None"
    by (simp add: list_all_length those_not_none_xs) 
  with wf l have "those (map2 (\<squnion>) As (map (\<langle>Bs\<rangle>\<^sub>\<alpha>) (vars_distinct (Fun f ts)))) \<noteq> None"
    using apply_lhs_subst_var_rule by (metis Inl_inject is_Prule.simps(1) is_Prule.simps(3) lhs term.distinct(1) term.inject(2) wf_pterm.simps) 
  with lhs_subst_trivial[of \<alpha> Bs] show ?thesis 
    unfolding lhs to_pterm.simps eval_term.simps join.simps by force 
qed
end

subsubsection\<open>N-Fold Join\<close>
text\<open>We define a function to recursively join a list of @{term n} proof terms.
Since each individual join produces a @{typeof  "A::('f, 'v) pterm option"}
we first introduce the following helper function.\<close>
fun join_opt :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm option \<Rightarrow> ('f, 'v) pterm option"
  where 
    "join_opt A (Some B) = A \<squnion> B" 
  | "join_opt _ _ = None" 

fun join_list :: "('f, 'v) pterm list \<Rightarrow> ('f,'v) pterm option" ("\<Squnion>")
  where
    "join_list [] = None"
  | "join_list (A # []) = Some A"
  | "join_list (A # As) = join_opt A (join_list As)" 
        
context left_lin_no_var_lhs
begin

lemma join_var_rule:
  assumes "to_rule \<alpha> \<in> R"
  shows "Var x \<squnion> Prule \<alpha> As = None" 
proof-
  from assms obtain f ts where "lhs \<alpha> = Fun f ts"
    using no_var_lhs by fastforce 
  then show ?thesis
    by (metis (no_types, lifting) Residual_Join_Deletion.join_sym eval_term.simps(2) join.simps(4) match_lhs_subst option.case_eq_if option.exhaust term.distinct(1) to_pterm.simps(2))
qed

lemma var_join:
  assumes "Var x \<squnion> B = Some C" and "B \<in> wf_pterm R"
  shows "B = Var x \<and> C = Var x" 
  using assms proof(cases B)
  case (Var y)
  with assms(1) show ?thesis
    by (metis join.simps(1) option.sel option.simps(3))
next
  case (Prule \<alpha> As)
  with assms show ?thesis
    by (metis Residual_Join_Deletion.join_sym Term.term.simps(4) case_prodD co_initial_Var is_VarI join.simps(9) 
        no_var_lhs.no_var_lhs no_var_lhs_axioms option.distinct(1) source_join sum.inject(1) term.inject(2) wf_pterm.simps)
qed simp

lemma fun_join:
  assumes "Pfun f As \<squnion> B = Some C" 
  shows "(\<exists>g Bs. B = Pfun g Bs) \<or> (\<exists>\<alpha> Bs. B = Prule \<alpha> Bs)"
  using assms by(cases B) (simp_all)

lemma rule_join:
  assumes "Prule \<alpha> As \<squnion> B = Some C" and "Prule \<alpha> As \<in> wf_pterm R"
  shows "(\<exists>g Bs. B = Pfun g Bs) \<or> (\<exists>\<beta> Bs. B = Prule \<beta> Bs)"
  using assms proof(cases B)
  case (Var x)
  from assms have False unfolding Var
    by (metis Residual_Join_Deletion.join_sym term.distinct(1) var_join) 
  then show ?thesis by simp
qed simp_all

text\<open>Associativity of join is currently not used in any proofs. But it is still
a valuable result, hence included here.\<close>
lemma join_opt_assoc:
  assumes "A \<in> wf_pterm R" "B \<in> wf_pterm R" "C \<in> wf_pterm R"
  shows "join_opt A (B \<squnion> C) = join_opt C (A \<squnion> B)"
  using assms proof(induct A arbitrary:B C rule:subterm_induct)
  case (subterm A)
  from subterm(2) show ?case proof(cases A rule:wf_pterm.cases[case_names VarA FunA RuleA])
    case (VarA x)
    with subterm(3) show ?thesis proof(cases B rule:wf_pterm.cases[case_names VarB FunB RuleB])
      case (VarB y)
      show ?thesis proof(cases "x = y")
        case True
        then have AB:"A \<squnion> B = Some (Var y)" unfolding VarA VarB by simp
        with subterm(4) VarA VarB show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC z)
          with AB VarA VarB \<open>x = y\<close> show ?thesis by(cases "y = z") simp_all
        next
          case (RuleC \<alpha> As)
          then have "(Var y) \<squnion> C = None"
            using join_var_rule by presburger
          then show ?thesis unfolding AB unfolding VarA VarB by (simp add:join_sym)
        qed simp
      next
        case False
        then have AB:"A \<squnion> B = None" unfolding VarA VarB by simp
        with subterm(4) VarA VarB show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC z)
          with AB VarA VarB \<open>x \<noteq> y\<close> show ?thesis by(cases "y = z") simp_all
        next
          case (RuleC \<alpha> As)
          then have "(Var y) \<squnion> C = None"
            using join_var_rule by presburger
          then show ?thesis unfolding AB unfolding VarA VarB by (simp add:join_sym)
        qed simp
      qed 
    next
      case (FunB Bs f)
      then have AB:"A \<squnion> B = None"
        unfolding VarA by simp
      with subterm(4) VarA show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
        case (VarC z)
        with AB VarA FunB show ?thesis by(cases "x = z") simp_all
      next
        case (FunC Cs g)
        from AB VarA show ?thesis proof(cases "B \<squnion> C")
          case (Some BC)
          then obtain BCs where "BC = Pfun f BCs"
            by (metis FunB(1) FunC(1) join_fun_fun) 
          then show ?thesis unfolding AB unfolding VarA Some by simp
        qed simp
      next
        case (RuleC \<alpha> Cs)
        from AB VarA show ?thesis proof(cases "B \<squnion> C")
          case (Some BC)
          then obtain BCs where "BC = Prule \<alpha> BCs"
            by (metis FunB(1) Residual_Join_Deletion.join_sym RuleC(1) join_rule_fun subterm.prems(3))
          then have "Var x \<squnion> BC = None" 
            using RuleC(2) join_var_rule by presburger
          then show ?thesis unfolding AB unfolding VarA Some by simp
        qed simp
      qed
    next
      case (RuleB \<alpha> Bs)
      then have AB:"A \<squnion> B = None"
        using VarA join_var_rule by presburger
      with subterm(4) VarA show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
        case (VarC z)
        with RuleB have "B \<squnion> C = None" 
          using join_var_rule join_sym by metis
        with AB show ?thesis by simp
      next
        case (FunC Cs f)
        from AB VarA show ?thesis proof(cases "B \<squnion> C")
          case (Some BC)
          then obtain BCs where "BC = Prule \<alpha> BCs"
            by (metis FunC(1) RuleB(1) join_rule_fun subterm.prems(2))  
          then have "Var x \<squnion> BC = None" 
            using RuleB(2) join_var_rule by presburger
          then show ?thesis unfolding AB unfolding VarA Some by simp
        qed simp
      next
        case (RuleC \<beta> Cs)
        from AB VarA show ?thesis proof(cases "B \<squnion> C")
          case (Some BC)
          then obtain BCs where "BC = Prule \<alpha> BCs"
            using RuleB(1) RuleC(1) join_rule_rule subterm.prems(2) subterm.prems(3) by blast 
          then have "Var x \<squnion> BC = None" 
            using RuleB(2) join_var_rule by presburger
          then show ?thesis unfolding AB unfolding VarA Some by simp
        qed simp
      qed
    qed
  next
    case (FunA As f)
    from subterm(3) show ?thesis proof(cases B rule:wf_pterm.cases[case_names VarB FunB RuleB])
      case (VarB x)
      then show ?thesis
        by (metis FunA(1) join.simps(1) join.simps(8) join.simps(9) join_opt.elims join_opt.simps(2) join_var_rule option.sel subterm.prems(3) wf_pterm.simps) 
    next
      case (FunB Bs g)
      then show ?thesis proof(cases "A \<squnion> B")
        case None
        with subterm(4) FunB show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (FunC Cs h)
          from None show ?thesis proof(cases "B \<squnion> C")
            case (Some BC)
            then have gh:"g = h" and l_B_C:"length Bs = length Cs"  
              unfolding FunB FunC by (meson join_fun_fun)+
            from Some obtain BCs where BC:"BC = Pfun g BCs" and l_BC_B:"length BCs = length Bs" 
              and args_BC:"(\<forall>i<length Bs. Bs!i \<squnion> Cs!i = Some (BCs ! i))"
              unfolding FunC FunB using join_fun_fun by force
            {assume fg:"f = g" and l_A_B:"length As = length Bs" 
              {fix i assume i:"i < length As" 
                with subterm(1) FunA FunB(2) FunC(2) args_BC l_A_B l_B_C 
                have "join_opt (As!i) ((Bs!i) \<squnion> (Cs!i)) = join_opt (Cs!i) ((As!i) \<squnion> (Bs!i))"
                  by (metis nth_mem supt.arg) 
              } note IH=this
              from fg l_A_B None have "those (map2 (\<squnion>) As Bs) = None" 
                unfolding FunB FunA by (smt (verit) join.simps(2) option.case_eq_if option.distinct(1)) 
              then obtain i where i:"i < length (map2 (\<squnion>) As Bs)" "(map2 (\<squnion>) As Bs)!i = None"
                using those_not_none_xs list_all_length by blast 
              with l_A_B have A_B_i:"(As!i) \<squnion> (Bs!i) = None" by simp
              with IH i(1) l_B_C have "As!i \<squnion> BCs!i = None" using args_BC by fastforce
              with i(1) l_BC_B l_B_C l_A_B have "those (map2 (\<squnion>) As BCs) = None"
                using list_all_length those_some2 by fastforce
            }
            then show ?thesis 
              using l_B_C l_BC_B FunA FunB FunC BC gh None Some by auto
          qed simp
        next
          case (RuleC \<alpha> Cs)
          from None show ?thesis proof(cases "B \<squnion> C")
            case (Some BC)
            then obtain BCs \<tau> where \<tau>:"match B (to_pterm (lhs \<alpha>)) = Some \<tau>" and BC:"BC = Prule \<alpha> BCs"
              and l_BCs:"length BCs = length Cs" and args_BC:"\<forall>i < length Cs. Cs!i \<squnion> \<tau> (var_rule \<alpha> ! i) = Some (BCs ! i)"  
              by (metis FunB(1) join_sym RuleC(1) join_rule_fun subterm.prems(3))  
            with None Some FunA show ?thesis proof(cases "match A (to_pterm (lhs \<alpha>))")
              case (Some \<sigma>)
              with \<tau> None obtain x where x:"x \<in> vars_term (lhs \<alpha>)" "\<sigma> x \<squnion> \<tau> x = None" 
                using join_pterm_subst_None by (metis lhs_subst_trivial match_lhs_subst option.sel set_vars_term_list vars_to_pterm) 
              then obtain i where i:"i < length (var_rule \<alpha>)" "var_rule \<alpha> ! i = x"
                by (metis RuleC(2) case_prodD in_set_idx left_lin left_linear_trs_def linear_term_var_vars_term_list set_vars_term_list) 
              have subt:"A \<rhd> \<sigma> x" proof-
                obtain g ts where lhs:"lhs \<alpha> = Fun g ts"
                  using RuleC(2) no_var_lhs by fastforce 
                from Some i show ?thesis 
                  unfolding lhs by (metis (no_types, lifting) lhs match_matches set_vars_term_list subst_image_subterm to_pterm.simps(2) vars_to_pterm x(1))
              qed
              have wf_\<tau>_x:"\<tau> x \<in> wf_pterm R" 
                using FunB \<tau> i by (metis match_well_def subterm.prems(2) vars_to_pterm)
              have IH:"join_opt (\<sigma> x) (\<tau> x \<squnion> (Cs ! i)) = join_opt (Cs!i) (\<sigma> x \<squnion> \<tau> x)" 
                using subterm(1) RuleC(3,4) i wf_\<tau>_x by (metis Some match_well_def nth_mem subt subterm.prems(1) vars_to_pterm) 
              have "\<tau> x \<squnion> (Cs ! i) = Some (BCs ! i)" 
                using args_BC i by (metis Residual_Join_Deletion.join_sym RuleC(3)) 
              with IH x(2) have "(\<sigma> x) \<squnion> (BCs ! i) = None" by simp
              then have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) ! i = None" 
                using l_BCs i by (simp add: RuleC(3)) 
              then have "those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) = None" 
                using l_BCs i by (metis (no_types, opaque_lifting) RuleC(3) length_map length_zip min.idem not_Some_eq nth_mem those_not_none_x) 
              then have "A \<squnion> BC = None" 
                using Some i unfolding BC FunA join.simps by simp
              then show ?thesis 
                unfolding None \<open>B \<squnion> C = Some BC\<close> by auto
            qed simp
          qed simp
        qed simp
      next
        case (Some AB)
        then have fg:"f = g" and l_A_B:"length As = length Bs"  
          unfolding FunA FunB by (meson join_fun_fun)+
        from Some obtain ABs where AB:"AB = Pfun f ABs" and l_AB_A:"length ABs = length As" 
          and args_AB:"(\<forall>i<length Bs. As!i \<squnion>  Bs!i = Some (ABs ! i))"
          unfolding FunA FunB using join_fun_fun by force
        from subterm(4) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC x)
          show ?thesis unfolding Some AB unfolding FunA FunB VarC by simp
        next
          case (FunC Cs h)
          show ?thesis proof(cases "B \<squnion> C")
            case None
            {assume gh:"g = h" and l_B_C:"length Bs = length Cs" 
              {fix i assume i:"i < length As" 
                with subterm(1) FunA FunB(2) FunC(2) args_AB l_A_B l_B_C 
                have "join_opt (As!i) ((Bs!i) \<squnion> (Cs!i)) = join_opt (Cs!i) ((As!i) \<squnion> (Bs!i))"
                  by (metis nth_mem supt.arg) 
              } note IH=this
              from gh l_B_C None have "those (map2 (\<squnion>) Bs Cs) = None" 
                unfolding FunB FunC by (smt (verit) join.simps(2) option.case_eq_if option.distinct(1)) 
              then obtain i where i:"i < length (map2 (\<squnion>) Bs Cs)" "(map2 (\<squnion>) Bs Cs)!i = None"
                using those_not_none_xs list_all_length by blast 
              with l_B_C have B_C_i:"(Bs!i) \<squnion> (Cs!i) = None" by simp
              with IH i(1) l_A_B have "Cs!i \<squnion> ABs!i = None" using args_AB by fastforce
              with i(1) l_AB_A l_B_C l_A_B have "those (map2 (\<squnion>) Cs ABs) = None"
                using list_all_length those_some2 by fastforce
            }
            then show ?thesis 
              using l_A_B l_AB_A FunA FunB FunC AB fg None Some by auto
          next
            case (Some BC)
            then have gh:"g = h" and l_B_C:"length Bs = length Cs" 
              unfolding FunB FunC by(meson join_fun_fun)+
            from Some obtain BCs where BC:"BC = Pfun g BCs" and l_BC_B:"length BCs = length Bs" 
              and args_BC:"(\<forall>i<length Cs. Bs!i \<squnion> Cs!i = Some (BCs ! i))"
              unfolding FunB FunC using join_fun_fun by force
            {fix i assume i:"i < length As" 
              with subterm(1) FunA FunB(2) FunC(2) args_AB l_A_B l_B_C 
              have "join_opt (As!i) ((Bs!i) \<squnion> (Cs!i)) = (Cs!i) \<squnion> (ABs!i)"
                by (metis join_opt.simps(1) nth_mem supt.arg) 
              with args_BC i l_A_B l_B_C have "(As!i) \<squnion> (BCs!i) = (Cs!i) \<squnion> (ABs!i)" by simp
            } note IH=this
            then have "those (map2 (\<squnion>) As BCs) = those (map2 (\<squnion>) Cs ABs)"
              by (smt (verit, del_insts) l_AB_A l_A_B l_BC_B l_B_C length_zip map_equality_iff min_less_iff_conj nth_zip old.prod.case)  
            then show ?thesis unfolding Some BC \<open>A \<squnion> B = Some AB\<close> AB unfolding gh FunA FunC fg join_opt.simps using l_BC_B l_AB_A l_A_B l_B_C by simp
          qed
        next
          case (RuleC \<alpha> Cs)
          from RuleC(2) have lin:"linear_term (lhs \<alpha>)" 
            using left_lin left_linear_trs_def by fastforce
          from RuleC(2) obtain f' ts where lhs:"lhs \<alpha> = Fun f' ts" 
            using no_var_lhs by fastforce 
          consider "match A (to_pterm (lhs \<alpha>)) = None" | "match B (to_pterm (lhs \<alpha>)) = None" 
            | (matches) "match A (to_pterm (lhs \<alpha>)) \<noteq> None \<and> match B (to_pterm (lhs \<alpha>)) \<noteq> None" by linarith
          then show ?thesis proof(cases)
            case 1
            then have match:"match AB (to_pterm (lhs \<alpha>)) = None" 
              using lin by (smt (verit, ccfv_threshold) Some join_pterm_linear_subst match_complete' match_matches not_Some_eq) 
            then have "C \<squnion> AB = None " 
              unfolding RuleC AB join.simps by simp
            moreover have "join_opt A (B \<squnion> C) = None" proof-
              consider "(\<exists>BCs. B \<squnion> C = Some (Prule \<alpha> BCs))" | "B \<squnion> C = None" 
                unfolding FunB RuleC join.simps by (metis (no_types, lifting) option.case_eq_if)
              then show ?thesis using 1 FunA(1) by(cases) (force, simp)
            qed
            ultimately show ?thesis using Some by simp
          next
            case 2
            then have match:"match AB (to_pterm (lhs \<alpha>)) = None" 
              using lin by (smt (verit, ccfv_threshold) Some join_pterm_linear_subst match_complete' match_matches not_Some_eq)
            then have "C \<squnion> AB = None " 
              unfolding RuleC AB join.simps by simp
            moreover from 2 have "B \<squnion> C = None" 
              unfolding FunB RuleC join.simps by simp
            ultimately show ?thesis using Some by simp
          next
            case matches
            from matches obtain \<sigma> where sigma:"match A (to_pterm (lhs \<alpha>)) = Some \<sigma>" by force
            from matches obtain \<tau> where tau:"match B (to_pterm (lhs \<alpha>)) = Some \<tau>" by force
            from sigma tau obtain \<rho> where rho:"(\<forall>x\<in>vars_term (to_pterm (lhs \<alpha>)). \<sigma> x \<squnion> \<tau> x = Some (\<rho> x))" 
              and AB_rho:"AB = (to_pterm (lhs \<alpha>)) \<cdot> \<rho>" and match_rho:"match AB (to_pterm (lhs \<alpha>)) = Some \<rho>" 
              using join_pterm_subst_Some match_matches Some by blast
            {fix i assume i:"i < length Cs" 
              with sigma RuleC(3) have "(map \<sigma> (var_rule \<alpha>))!i \<lhd> A" 
                using lhs by (smt (verit, ccfv_threshold) lin linear_term_var_vars_term_list match_matches nth_map nth_mem set_vars_term_list subst_image_subterm to_pterm.simps(2) vars_to_pterm)
               moreover have "(map \<sigma> (var_rule \<alpha>))!i \<in> wf_pterm R"
                 using i match_well_def[OF subterm(2) sigma] RuleC(3) by (simp add: vars_to_pterm)
               moreover have "(map \<tau> (var_rule \<alpha>))!i \<in> wf_pterm R"
                 using i match_well_def[OF subterm(3) tau] RuleC(3) by (simp add: vars_to_pterm)
              ultimately have "join_opt (map \<sigma> (var_rule \<alpha>) ! i) (map \<tau> (var_rule \<alpha>) ! i \<squnion> Cs!i) = Cs ! i \<squnion> map \<rho> (var_rule \<alpha>) ! i"
                using subterm(1) RuleC(3,4) i by (smt (verit, best) join_opt.simps(1) lin linear_term_var_vars_term_list nth_map nth_mem rho set_vars_term_list vars_to_pterm) 
            }note IH=this
            show ?thesis proof(cases "those (map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) Cs)")
              case None
              then obtain i where i:"i < length Cs" "(map \<tau> (var_rule \<alpha>))!i \<squnion> Cs!i = None" 
                using those_not_none_xs by (smt (verit) length_map length_zip list_all_length map_nth_eq_conv min_less_iff_conj nth_zip old.prod.case)
              with IH have "Cs!i \<squnion> map \<rho> (var_rule \<alpha>) ! i = None" by force 
              with i RuleC(3) have "i < length (map2 (\<squnion>) Cs (map \<rho> (var_rule \<alpha>)))" "(map2 (\<squnion>) Cs (map \<rho> (var_rule \<alpha>))) ! i = None" by simp_all
              then have "those (map2 (\<squnion>) Cs (map \<rho> (var_rule \<alpha>))) = None"
                by (metis nth_mem option.exhaust those_not_none_x) 
              with None show ?thesis unfolding Some unfolding FunA FunB RuleC join.simps tau[unfolded FunB] using AB match_rho by auto
            next
              case (Some BCs)
              then have BC:"B \<squnion> C = Some (Prule \<alpha> BCs)" 
                unfolding FunB RuleC join.simps tau[unfolded FunB] by simp
              from Some have l_BCs:"length BCs = length Cs"
                using RuleC(3) length_those by fastforce 
              {fix i assume "i < length Cs" 
                with Some IH have "(map \<sigma> (var_rule \<alpha>)) ! i \<squnion> BCs ! i = Cs ! i \<squnion> (map \<rho> (var_rule \<alpha>)) ! i"
                  using RuleC(3) those_some2 by fastforce 
              }
              then have "map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs  = map2 (\<squnion>) Cs (map \<rho> (var_rule \<alpha>))" 
                using l_BCs by (simp add: RuleC(3) map_eq_conv') 
              then show ?thesis unfolding BC \<open>A \<squnion> B = Some AB\<close> unfolding FunA FunB RuleC join_opt.simps join.simps sigma[unfolded FunA] using AB match_rho by auto
            qed
          qed
        qed
      qed
    next
      case (RuleB \<alpha> Bs)
      from RuleB(2) have lin:"linear_term (lhs \<alpha>)" 
        using left_lin left_linear_trs_def by fastforce
      from RuleB(2) obtain f' ts where lhs:"lhs \<alpha> = Fun f' ts" 
        using no_var_lhs by fastforce
      show ?thesis proof(cases "A \<squnion> B")
        case None
        with subterm(4) RuleB show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC x)
          with subterm(4) RuleB FunA show ?thesis
            by (metis None join_sym join_opt.simps(2) join_var_rule) 
        next
          case (FunC Cs h)
          from None show ?thesis proof(cases "B \<squnion> C")
            case (Some BC)
            obtain BCs \<tau> where \<tau>:"match C (to_pterm (lhs \<alpha>)) = Some \<tau>" and BC:"BC = Prule \<alpha> BCs"
              and l_BCs:"length BCs = length Bs" and args_BC:"\<forall>i < length Bs. Bs!i \<squnion> \<tau> (var_rule \<alpha> ! i) = Some (BCs ! i)"  
              using join_rule_fun[OF Some[unfolded RuleB FunC] subterm(3)[unfolded RuleB]] FunC(1) by blast 
            with None Some FunA show ?thesis proof(cases "match A (to_pterm (lhs \<alpha>))")
              case (Some \<sigma>)
              from None obtain i where i:"i < length (var_rule \<alpha>)" "map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Bs ! i = None" 
                unfolding FunA RuleB join.simps Some[unfolded FunA] option.case
                by (smt (verit, ccfv_threshold) length_map length_zip list_all_length min_less_iff_conj option.case_eq_if option.distinct(1) those_not_none_xs) 
              let ?x="var_rule \<alpha> ! i"
              have subt:"A \<rhd> \<sigma> ?x" using lhs i Some
                by (smt (verit, ccfv_SIG) lin linear_term_var_vars_term_list match_matches nth_mem set_vars_term_list subst_image_subterm to_pterm.simps(2) vars_to_pterm) 
              have wf_\<tau>_x:"\<tau> ?x \<in> wf_pterm R" 
                using subterm(4) \<tau> i(1) by (metis match_well_def vars_to_pterm)
              have IH:"join_opt (\<sigma> ?x) (Bs ! i \<squnion> \<tau> ?x) = join_opt (\<tau> ?x) (\<sigma> ?x \<squnion> Bs ! i)" 
                using subterm(1) i wf_\<tau>_x by (metis RuleB(3) RuleB(4) Some match_well_def nth_mem subt subterm.prems(1) vars_to_pterm)
              have "(Bs ! i \<squnion> \<tau> ?x) = Some (BCs ! i)" 
                using args_BC i RuleB(3) by auto
              with IH i have "(\<sigma> ?x) \<squnion> (BCs ! i) = None"
                by (simp add: RuleB(3))
              then have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) ! i = None" 
                using l_BCs i by (simp add: RuleB(3))
              then have "those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) = None" 
                using l_BCs i by (metis (no_types, opaque_lifting) RuleB(3) length_map length_zip min.idem nth_mem option.exhaust those_not_none_x)
              then have "A \<squnion> BC = None" 
                using Some i unfolding BC FunA join.simps by simp
              then show ?thesis 
                unfolding None \<open>B \<squnion> C = Some BC\<close> by auto
            qed simp
          qed simp
        next
          case (RuleC \<beta> Cs)
          from None show ?thesis proof(cases "B \<squnion> C")
            case (Some BC)
            then have \<alpha>\<beta>:"\<alpha> = \<beta>" and l_B_C:"length Bs = length Cs" 
              using join_rule_rule[OF Some[unfolded RuleB RuleC] subterm(3,4)[unfolded RuleB RuleC]] by simp+
            from Some obtain BCs where BC:"BC = Prule \<alpha> BCs" and l_BC_B:"length BCs = length Bs" 
              and args_BC:"(\<forall>i<length Cs. Bs!i \<squnion> Cs!i = Some (BCs ! i))"
              using join_rule_rule[OF Some[unfolded RuleB RuleC] subterm(3,4)[unfolded RuleB RuleC]] by force
            from Some FunA RuleB BC show ?thesis proof(cases "match A (to_pterm (lhs \<alpha>))")
              case (Some \<sigma>)
              from None obtain i where i:"i < length (var_rule \<alpha>)" "map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Bs ! i = None" 
                unfolding FunA RuleB join.simps Some[unfolded FunA] option.case
                by (smt (verit, ccfv_threshold) length_map length_zip list_all_length min_less_iff_conj option.case_eq_if option.distinct(1) those_not_none_xs) 
              let ?x="var_rule \<alpha> ! i"
              have subt:"A \<rhd> \<sigma> ?x" using lhs i Some
                by (smt (verit, ccfv_SIG) lin linear_term_var_vars_term_list match_matches nth_mem set_vars_term_list subst_image_subterm to_pterm.simps(2) vars_to_pterm) 
              have IH:"join_opt (\<sigma> ?x) (Bs ! i \<squnion> Cs ! i) = join_opt (Cs ! i) (\<sigma> ?x \<squnion> Bs ! i)" 
                using subterm(1) i RuleC by (metis RuleB(3) RuleB(4) Some \<alpha>\<beta> match_well_def nth_mem subt subterm.prems(1) vars_to_pterm)      
              from IH i have "(\<sigma> ?x) \<squnion> (BCs ! i) = None"
                using RuleB(3) args_BC l_B_C by auto 
              then have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) ! i = None"
                using RuleB(3) i(1) l_BC_B by force 
              then have "those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) = None"
                by (metis (no_types, opaque_lifting) RuleB(3) i(1) l_BC_B length_map length_zip min.idem not_Some_eq nth_mem those_not_none_x) 
              then have "A \<squnion> BC = None" 
                using Some i unfolding BC FunA join.simps by simp
              then show ?thesis 
                unfolding None \<open>B \<squnion> C = Some BC\<close> by auto
            qed simp
          qed simp
        qed
      next
        case (Some AB)
        then obtain \<sigma> ABs where sigma:"match A (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
          and AB:"AB = Prule \<alpha> ABs" and l_ABs:"length ABs = length Bs" 
          and args_AB:"(\<forall>i<length Bs. \<sigma> (var_rule \<alpha> ! i) \<squnion> Bs ! i = Some (ABs ! i))"
          unfolding FunA RuleB using join_sym join_rule_fun subterm(2,3)[unfolded FunA RuleB] RuleB(3) by (smt (verit, del_insts))
        {fix i assume i:"i < length Bs" 
          with sigma RuleB(3) have "(map \<sigma> (var_rule \<alpha>))!i \<lhd> A" 
            using lhs by (smt (verit, ccfv_threshold) lin linear_term_var_vars_term_list match_matches nth_map nth_mem set_vars_term_list subst_image_subterm to_pterm.simps(2) vars_to_pterm)
        }note A_sub=this
        from subterm(4) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC x)
          have "match (Var x) (to_pterm (lhs \<alpha>)) = None"
            unfolding lhs to_pterm.simps using match_matches not_None_eq by fastforce 
          then show ?thesis 
            unfolding Some unfolding RuleB VarC AB by simp
        next
          case (FunC Cs g)
          show ?thesis proof(cases "match C (to_pterm (lhs \<alpha>))")
            case None
            then have "B \<squnion> C = None" 
              unfolding RuleB FunC by simp
            moreover from None have "AB \<squnion> C = None" 
              unfolding AB FunC by simp
            ultimately show ?thesis 
              unfolding Some by (simp add: join_sym)
          next
            case (Some \<tau>)
            {fix i assume i:"i < length Bs" 
               have "(map \<sigma> (var_rule \<alpha>))!i \<in> wf_pterm R"
                 using i match_well_def[OF subterm(2) sigma] RuleB(3) by (simp add: vars_to_pterm)
               moreover have "(map \<tau> (var_rule \<alpha>))!i \<in> wf_pterm R"
                 using i match_well_def[OF subterm(4) Some] RuleB(3) by (simp add: vars_to_pterm)
              ultimately have "join_opt (map \<sigma> (var_rule \<alpha>) ! i) (Bs!i \<squnion> map \<tau> (var_rule \<alpha>) ! i) = ABs ! i \<squnion> map \<tau> (var_rule \<alpha>) ! i"
                using subterm(1) RuleB(3,4) i args_AB A_sub join_sym by fastforce
            }note IH=this
            show ?thesis proof(cases "those (map2 (\<squnion>) Bs (map \<tau> (var_rule \<alpha>)))")
              case None
              then obtain i where i:"i < length Bs" "Bs!i \<squnion> (map \<tau> (var_rule \<alpha>))!i = None" 
                using those_not_none_xs by (smt (verit) length_map length_zip list_all_length map_nth_eq_conv min_less_iff_conj nth_zip old.prod.case)
              with IH have "map \<tau> (var_rule \<alpha>) ! i \<squnion> ABs ! i = None" 
                using join_sym by (metis join_opt.simps(2))
              with i RuleB(3) l_ABs have "i < length (map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) ABs)" "(map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) ABs) ! i = None" by simp_all
              then have "those (map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) ABs) = None" 
                by (metis nth_mem option.exhaust those_not_none_x) 
              with None show ?thesis 
                unfolding \<open>A \<squnion> B = Some AB\<close> AB unfolding RuleB FunC join_opt.simps join.simps Some[unfolded FunC] option.case None by simp
            next
              case (Some BCs)
              then have BC:"B \<squnion> C = Some (Prule \<alpha> BCs)" 
                unfolding RuleB FunC join.simps \<open>match C (to_pterm (lhs \<alpha>)) = Some \<tau>\<close>[unfolded FunC] by simp
              from Some have l_BCs:"length BCs = length Bs"
                using RuleB(3) length_those by fastforce 
              {fix i assume "i < length Bs" 
                with Some IH have "(map \<sigma> (var_rule \<alpha>)) ! i \<squnion> BCs!i = (map \<tau> (var_rule \<alpha>)) ! i \<squnion> ABs ! i"
                  using RuleB(3) those_some2 join_sym by fastforce 
              }
              then have "map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs = map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) ABs" 
                using l_BCs l_ABs by (simp add: RuleB(3) map_eq_conv') 
              then show ?thesis unfolding BC \<open>A \<squnion> B = Some AB\<close> AB unfolding FunA RuleB FunC AB join_opt.simps join.simps sigma[unfolded FunA] 
                  \<open>match C (to_pterm (lhs \<alpha>)) = Some \<tau>\<close>[unfolded FunC] option.case by simp
            qed
          qed
        next
          case (RuleC \<beta> Cs)
          show ?thesis proof(cases "\<alpha> = \<beta>")
            case True
            with RuleB(3) RuleC(3) have l_Bs_Cs:"length Bs = length Cs" by simp
            {fix i assume i:"i < length Bs" 
              have "(map \<sigma> (var_rule \<alpha>))!i \<in> wf_pterm R"
                using i match_well_def[OF subterm(2) sigma] RuleB(3) by (simp add: vars_to_pterm)
              then have "join_opt (map \<sigma> (var_rule \<alpha>) ! i) (Bs!i \<squnion> Cs ! i) =  Cs ! i \<squnion> ABs ! i"
                using subterm(1) RuleB(3,4) RuleC(3,4) i args_AB A_sub True by simp
            }note IH=this
            show ?thesis proof(cases "those (map2 (\<squnion>) Bs Cs)")
              case None
              then obtain i where i:"i < length Bs" "Bs!i \<squnion> Cs!i = None" 
                using those_not_none_xs by (smt (verit) length_map length_zip list_all_length map_nth_eq_conv min_less_iff_conj nth_zip old.prod.case)
              with IH have "Cs ! i \<squnion> ABs ! i = None" by force 
              with i RuleB(3) l_ABs l_Bs_Cs have "i < length (map2 (\<squnion>) Cs ABs)" "(map2 (\<squnion>) Cs ABs) ! i = None" by simp_all
              then have "those (map2 (\<squnion>) Cs ABs) = None"
                by (metis nth_mem option.exhaust those_not_none_x) 
              with None show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> AB unfolding RuleB RuleC by simp
            next
              case (Some BCs)
              then have BC:"B \<squnion> C = Some (Prule \<alpha> BCs)" 
                unfolding RuleB RuleC True by simp
              from Some have l_BCs:"length BCs = length Bs"
                using l_Bs_Cs length_those by fastforce 
              {fix i assume "i < length Bs" 
                with Some IH have "(map \<sigma> (var_rule \<alpha>)) ! i \<squnion> BCs!i = Cs ! i \<squnion> ABs ! i"
                  using those_some2 l_Bs_Cs by fastforce 
              }
              then have "map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs  = map2 (\<squnion>) Cs ABs" 
                using l_Bs_Cs RuleB(3) l_ABs l_BCs by (simp add: RuleC(3) map_eq_conv') 
              then show ?thesis 
                unfolding BC \<open>A \<squnion> B = Some AB\<close> AB unfolding FunA RuleB RuleC join_opt.simps join.simps sigma[unfolded FunA] unfolding True by simp
            qed
          next
            case False
            then show ?thesis 
              unfolding \<open>A \<squnion> B = Some AB\<close> unfolding RuleB RuleC AB join.simps by simp
          qed
        qed
      qed    
    qed 
  next
    case (RuleA \<alpha> As)
    from RuleA(2) have lin:"linear_term (lhs \<alpha>)" 
      using left_lin left_linear_trs_def by fastforce
    from RuleA(2) obtain f' ts where lhs:"lhs \<alpha> = Fun f' ts" 
      using no_var_lhs by fastforce
    from subterm(3,2) show ?thesis proof(cases B rule:wf_pterm.cases[case_names VarB FunB RuleB])
      case (VarB x)
      have "match (Var x) (to_pterm (lhs \<alpha>)) = None" 
        unfolding lhs using match_matches not_Some_eq by fastforce 
      then show ?thesis unfolding RuleA VarB
        by (metis join_sym RuleA(2) join.simps(1) join.simps(9) join_opt.simps(1) join_opt.simps(2) 
          left_lin_no_var_lhs.join_var_rule left_lin_no_var_lhs_axioms subterm.prems(3) wf_pterm.simps)
    next
      case (FunB Bs f)
      show ?thesis proof(cases "A \<squnion> B")
        case None
        with subterm(4) FunB show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC x)
          with subterm(4) FunB RuleA None show ?thesis
            by auto 
        next
          case (FunC Cs h)
          from None show ?thesis proof(cases "B \<squnion> C")
            case (Some BC)
            have fh:"f = h" and l_B_C:"length Bs = length Cs" 
              using join_fun_fun[OF Some[unfolded FunB FunC]] by simp+
            obtain BCs where BC:"BC = Pfun f BCs" and l_BC_B:"length BCs = length Bs" 
              and args_BC:"(\<forall>i<length Bs. Bs!i \<squnion> Cs!i = Some (BCs ! i))"
              using join_fun_fun[OF Some[unfolded FunB FunC]] by blast
            show ?thesis proof(cases "match B (to_pterm (lhs \<alpha>))")
              case None
              then have "\<not> matches BC (to_pterm (lhs \<alpha>))"
                using join_pterm_linear_subst \<open>B \<squnion> C = Some BC\<close> lin by (metis match_complete' matches_iff option.simps(3)) 
              then have "A \<squnion> BC = None" unfolding RuleA BC
                by (smt (verit) join.simps(5) match_matches matches_iff not_Some_eq option.simps(4))
              then show ?thesis 
                unfolding \<open>A \<squnion> B = None\<close> \<open>B \<squnion> C = Some BC\<close> by simp
            next
              case (Some \<sigma>)
              with None have "those (map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>))) = None" 
                unfolding RuleA FunB using not_None_eq by fastforce
              then obtain i where i:"i < length (var_rule \<alpha>)" "map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>)) ! i = None"
                by (smt (verit, best) RuleA(3) length_map length_zip list_all_length min.idem those_not_none_xs)  
              let ?x="var_rule \<alpha> ! i"  
              from i have none_at_i:"As ! i \<squnion> \<sigma> ?x = None" 
                using RuleA(3) by simp  
              show ?thesis proof(cases "match C (to_pterm (lhs \<alpha>))")
                case None
                then have "\<not> matches BC (to_pterm (lhs \<alpha>))"
                  using join_pterm_linear_subst \<open>B \<squnion> C = Some BC\<close> lin by (metis match_complete' matches_iff option.simps(3)) 
                then have "A \<squnion> BC = None" unfolding RuleA BC
                  by (smt (verit) join.simps(5) match_matches matches_iff not_Some_eq option.simps(4))
                then show ?thesis 
                  unfolding \<open>A \<squnion> B = None\<close> \<open>B \<squnion> C = Some BC\<close> by simp
              next
                case (Some \<tau>)
                then obtain \<rho> where rho:"(\<forall>x\<in>vars_term (to_pterm (lhs \<alpha>)). \<sigma> x \<squnion> \<tau> x = Some (\<rho> x))" 
                  and BC_rho:"BC = (to_pterm (lhs \<alpha>)) \<cdot> \<rho>" and match_rho:"match BC (to_pterm (lhs \<alpha>)) = Some \<rho>" 
                  using join_pterm_subst_Some match_matches \<open>match B (to_pterm (lhs \<alpha>)) = Some \<sigma>\<close> \<open>B \<squnion> C = Some BC\<close> by blast 
                have "\<sigma> ?x \<in> wf_pterm R" 
                  using i(1) \<open>match B (to_pterm (lhs \<alpha>)) = Some \<sigma>\<close> subterm(3) by (metis match_well_def vars_to_pterm) 
                moreover have "\<tau> ?x \<in> wf_pterm R" 
                  using i(1) Some subterm(4) by (metis match_well_def vars_to_pterm) 
                ultimately have IH:"join_opt (As ! i) (\<sigma> ?x \<squnion> \<tau> ?x) = join_opt (\<tau> ?x) (As ! i \<squnion> \<sigma> ?x)"
                  using subterm(1) i(1) RuleA(3) by (metis RuleA(1) RuleA(4) nth_mem supt.arg)
                then have "(As ! i) \<squnion> (\<rho> ?x) = None" 
                  using none_at_i rho by (metis i(1) join_opt.simps(1) join_opt.simps(2) lin linear_term_var_vars_term_list nth_mem set_vars_term_list vars_to_pterm) 
                then have "(map2 (\<squnion>) As (map \<rho> (var_rule \<alpha>))) ! i = None"
                  using RuleA(3) i(1) by auto 
                then have "those (map2 (\<squnion>) As (map \<rho> (var_rule \<alpha>))) = None"
                  by (metis (no_types, opaque_lifting) RuleA(3) i(1) length_map length_zip min.idem not_Some_eq nth_mem those_not_none_x) 
                then have "A \<squnion> BC = None" 
                  using BC RuleA(1) match_rho by force 
                then show ?thesis  
                  unfolding \<open>A \<squnion> B = None\<close> \<open>B \<squnion> C = Some BC\<close> by simp
              qed
            qed
          qed simp
        next
          case (RuleC \<beta> Cs)
          from None show ?thesis proof(cases "B \<squnion> C")
            case (Some BC)
            obtain BCs \<tau> where \<tau>:"match B (to_pterm (lhs \<beta>)) = Some \<tau>" and BC:"BC = Prule \<beta> BCs"
              and l_BCs:"length BCs = length Cs" and args_BC:"\<forall>i < length Cs. \<tau> (var_rule \<beta> ! i) \<squnion> Cs!i = Some (BCs ! i)"  
              using join_rule_fun Some[unfolded RuleC FunB] subterm(4)[unfolded RuleC] FunB(1) by (metis Residual_Join_Deletion.join_sym)
            show ?thesis proof(cases "match B (to_pterm (lhs \<alpha>))")
              case None
              with \<open>A \<squnion> B = None\<close> Some BC RuleA(1) \<tau> show ?thesis by fastforce
            next
              case (Some \<sigma>)
              from None obtain i where i:"i < length (var_rule \<alpha>)" "map2 (\<squnion>) As (map \<sigma> (var_rule \<alpha>)) ! i = None" 
                unfolding FunB RuleA join.simps Some[unfolded FunB] option.case
                by (smt (verit, ccfv_threshold) length_map length_zip list_all_length min_less_iff_conj option.case_eq_if option.distinct(1) those_not_none_xs) 
              let ?x="var_rule \<alpha> ! i"
              have wf_\<sigma>_x:"\<sigma> ?x \<in> wf_pterm R" 
                using subterm(3) Some i(1) by (metis match_well_def vars_to_pterm) 
              from BC None \<open>B \<squnion> C = Some BC\<close> RuleA show ?thesis proof(cases "\<alpha> = \<beta>")
                case True
                then have "\<sigma> = \<tau>" 
                  using Some \<tau> by auto
                have IH:"join_opt (As ! i) (\<tau> ?x \<squnion> Cs ! i) = join_opt (Cs ! i) (As ! i \<squnion> \<tau> ?x)" 
                  using subterm(1) i wf_\<sigma>_x args_BC by (metis RuleA(1) RuleA(3) RuleA(4) RuleC(3) RuleC(4) True \<open>\<sigma> = \<tau>\<close> nth_mem supt.arg)
                have "\<tau> ?x \<squnion> Cs ! i = Some (BCs ! i)" 
                  using args_BC i RuleC(3) True by force
                with IH i have "(As ! i) \<squnion> (BCs ! i) = None"
                  by (simp add: RuleA(3) \<open>\<sigma> = \<tau>\<close>) 
                then have "(map2 (\<squnion>) As BCs) ! i = None" 
                  using l_BCs i by (simp add: RuleA(3) RuleC(3) True)
                then have "those (map2 (\<squnion>) As BCs) = None" 
                  using l_BCs i those_not_none_x by (metis RuleA(3) RuleC(3) True length_map length_zip min.idem nth_mem option.exhaust)
                then have "A \<squnion> BC = None"
                  by (simp add: BC RuleA(1)) 
                then show ?thesis 
                  unfolding None \<open>B \<squnion> C = Some BC\<close> by auto
              qed simp
            qed
          qed simp
        qed
      next
        case (Some AB)
        obtain \<sigma> ABs where sigma:"match B (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
          and AB:"AB = Prule \<alpha> ABs" and l_ABs:"length ABs = length As" 
          and args_AB:"(\<forall>i<length As. As!i \<squnion> \<sigma> (var_rule \<alpha> ! i) = Some (ABs ! i))"
          using join_sym join_rule_fun[OF Some[unfolded FunB RuleA]] using FunB(1) RuleA(1) subterm.prems(1) by blast
        from subterm(4) FunB(1) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC x)
          have "match (Var x) (to_pterm (lhs \<alpha>)) = None" 
            unfolding lhs using match_matches not_Some_eq by fastforce 
          then show ?thesis unfolding Some unfolding RuleA FunB AB VarC by simp
        next
          case (FunC Cs g)
          show ?thesis proof(cases "f = g \<and> length Bs = length Cs")
            case True
            show ?thesis proof(cases "match C (to_pterm (lhs \<alpha>))")
              case None
              then have *:"C \<squnion> AB = None" 
                unfolding AB FunC by simp
              with Some show ?thesis proof(cases "B \<squnion> C")
                case (Some BC)
                with None have "match BC (to_pterm (lhs \<alpha>)) = None"
                  by (metis (no_types, lifting) domD domIff join_pterm_linear_subst lin match_complete' match_lhs_subst option.simps(3))
                moreover obtain BCs where "BC = Pfun f BCs"
                  by (metis FunB(1) FunC(1) Some join_fun_fun)  
                ultimately show ?thesis 
                  using * unfolding \<open>A \<squnion> B = Some AB\<close> AB unfolding RuleA Some unfolding FunC by (simp add: join_sym)
              qed simp
            next
              case (Some \<tau>)
              {fix i assume i:"i < length As" 
                have "(map \<sigma> (var_rule \<alpha>)) ! i \<in> wf_pterm R"
                  using i match_well_def[OF subterm(3) sigma] RuleA(3) by (simp add: vars_to_pterm)
                moreover have "(map \<tau> (var_rule \<alpha>)) ! i \<in> wf_pterm R"
                  using i match_well_def[OF subterm(4) Some] RuleA(3) by (simp add: vars_to_pterm)
                ultimately have "join_opt (As ! i) ((map \<sigma> (var_rule \<alpha>) ! i) \<squnion> (map \<tau> (var_rule \<alpha>) ! i)) = (map \<tau> (var_rule \<alpha>) ! i) \<squnion> ABs ! i"
                  using subterm(1) RuleA(1,3,4) i args_AB True by (metis (no_types, lifting) join_opt.simps(1) nth_map nth_mem supt.arg)
              }note IH=this
              show ?thesis proof(cases "B \<squnion> C")
                case None
                with sigma Some obtain x where "x \<in> vars_term (lhs \<alpha>)" and "\<sigma> x \<squnion> \<tau> x = None"
                  using join_pterm_subst_None by (metis lhs_subst_trivial match_lhs_subst option.sel set_vars_term_list vars_to_pterm) 
                then obtain i where i:"i < length (var_rule \<alpha>)" "(map \<sigma> (var_rule \<alpha>) ! i) \<squnion> (map \<tau> (var_rule \<alpha>) ! i) = None"
                  by (metis (no_types, opaque_lifting) in_set_idx lin linear_term_var_vars_term_list nth_map set_vars_term_list)
                with IH have "map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) ABs ! i = None"
                  using RuleA(3) l_ABs by fastforce 
                with i(1) have "those (map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) ABs) = None" 
                  using those_not_none_x by (metis (no_types, opaque_lifting) RuleA(3) l_ABs length_map length_zip min.idem nth_mem option.exhaust) 
                with Some show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> AB None unfolding FunC by simp
              next
                case (Some BC)
                from sigma Some obtain \<rho> where rho:"(\<forall>x\<in>vars_term (to_pterm (lhs \<alpha>)). \<sigma> x \<squnion> \<tau> x = Some (\<rho> x))" 
                  and BC_rho:"BC = (to_pterm (lhs \<alpha>)) \<cdot> \<rho>" and match_rho:"match BC (to_pterm (lhs \<alpha>)) = Some \<rho>" 
                  using join_pterm_subst_Some match_matches \<open>match C (to_pterm (lhs \<alpha>)) = Some \<tau>\<close> by blast 
                {fix i assume i:"i < length As" 
                  with rho have "(map \<sigma> (var_rule \<alpha>)) ! i \<squnion> (map \<tau> (var_rule \<alpha>)) ! i = Some ((map \<rho> (var_rule \<alpha>)) ! i)"
                    by (metis (no_types, lifting) RuleA(3) lin linear_term_var_vars_term_list nth_map nth_mem set_vars_term_list vars_to_pterm) 
                  with i IH have "As ! i \<squnion> (map \<rho> (var_rule \<alpha>)) ! i = (map \<tau> (var_rule \<alpha>)) ! i \<squnion> ABs ! i"
                    by force
                }
                then have "map2 (\<squnion>) As (map \<rho> (var_rule \<alpha>)) = map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) ABs"
                  by (simp add: RuleA(3) l_ABs map_equality_iff)
                with match_rho \<open>match C (to_pterm (lhs \<alpha>)) = Some \<tau>\<close>  
                show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> AB Some 
                  unfolding RuleA  BC_rho join_opt.simps to_pterm.simps FunC by (simp add: lhs)
              qed
            qed
          next
            case False
            then consider (fg) "f \<noteq> g" | (length) "length Bs \<noteq> length Cs" by fastforce 
            then show ?thesis proof(cases)
              case fg
              from sigma have "f' = f" 
                unfolding FunB lhs to_pterm.simps using match_matches by fastforce 
              with fg have "match C (to_pterm (lhs \<alpha>)) = None" 
                unfolding lhs FunC using domIff match_matches by fastforce
              with fg show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> unfolding RuleA FunB FunC AB by simp
            next
              case length
              from sigma have "length ts = length Bs"
                using FunB(1) lhs match_matches by fastforce 
              then have "match C (to_pterm (lhs \<alpha>)) = None" 
                unfolding FunC lhs using length
                by (smt (verit, del_insts) eval_term.simps(2) length_map match_matches option.exhaust term.inject(2) to_pterm.simps(2)) 
              with length show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> unfolding RuleA FunB FunC AB by simp
            qed
          qed 
        next
          case (RuleC \<beta> Cs)
          show ?thesis proof(cases "\<alpha> = \<beta>")
            case True
            {fix i assume i:"i < length As" 
              have "(map \<sigma> (var_rule \<alpha>))!i \<in> wf_pterm R"
                using i match_well_def[OF subterm(3) sigma] RuleA(3) by (simp add: vars_to_pterm)
              then have "join_opt (As!i) ((map \<sigma> (var_rule \<alpha>) ! i) \<squnion> Cs ! i) = Cs ! i \<squnion> ABs ! i"
                using subterm(1) RuleA(1,3,4) RuleC i args_AB True by (metis (no_types, lifting) join_opt.simps(1) nth_map nth_mem supt.arg)
            }note IH=this
            show ?thesis proof(cases "those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Cs)")
              case None
              with sigma have BC:"B \<squnion> C = None" 
                unfolding FunB RuleC True by simp
              from None obtain i where i:"i < length (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Cs)" and "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) Cs) ! i = None"
                using list_all_length those_not_none_xs by blast 
              with IH have "(map2 (\<squnion>) Cs ABs)!i = None"
                using RuleA(3) l_ABs RuleC(3) by fastforce  
              with i(1) have "those (map2 (\<squnion>) Cs ABs) = None"  
                using l_ABs RuleA(3) RuleC(3) those_not_none_x unfolding True
                by (metis length_map length_zip not_Some_eq nth_mem)  
              then show ?thesis unfolding BC \<open>A \<squnion> B = Some AB\<close> unfolding AB RuleC True by simp
            next
              case (Some BCs)
              with sigma have BC:"B \<squnion> C = Some (Prule \<alpha> BCs)" 
                unfolding FunB RuleC True by simp
              {fix i assume i:"i < length As" 
                with Some have "(map \<sigma> (var_rule \<alpha>)) ! i \<squnion> Cs ! i = Some (BCs ! i)"
                  using RuleA(3) RuleC(3) True those_some2 by fastforce 
                with i IH have "As ! i \<squnion> BCs ! i = Cs ! i \<squnion> ABs ! i"
                  by force
              }
              moreover have "length Cs = length BCs" 
                using RuleC(3) Some True length_those by fastforce
              ultimately have "map2 (\<squnion>) As BCs = map2 (\<squnion>) Cs ABs" 
                using RuleA(3) l_ABs map_equality_iff
                by (smt (verit, ccfv_threshold) RuleC(3) Some True length_map length_those length_zip nth_zip old.prod.case) 
              then show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> BC AB unfolding RuleA RuleC True by simp
            qed
          next
            case False
            show ?thesis proof(cases "B \<squnion> C")
              case None
              show ?thesis unfolding None \<open>A \<squnion> B = Some AB\<close> unfolding AB RuleC using False by simp
            next
              case (Some BC)
              then obtain BCs where "BC = Prule \<beta> BCs" 
                unfolding RuleC FunB by (metis Residual_Join_Deletion.join_sym RuleC(1) join_rule_fun subterm.prems(3)) 
              with False show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> Some AB unfolding RuleC RuleA by simp
            qed
          qed
        qed
      qed
    next
      case (RuleB \<beta> Bs)
      show ?thesis proof(cases "A \<squnion> B")
        case None
        then show ?thesis proof(cases "\<alpha> = \<beta>")
          case True
          then have l_As_Bs:"length As = length Bs"
            by (simp add: RuleA(3) RuleB(3))  
          with None obtain i where i:"i < length As" "As ! i \<squnion> Bs ! i = None" 
            unfolding True RuleA RuleB unfolding join.simps by (smt (verit) RuleB(3) length_map length_zip list_all_length 
            map_nth_eq_conv min_less_iff_conj nth_zip old.prod.case option.case_eq_if option.distinct(1) those_not_none_xs) 
          from subterm(4) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
            case (VarC x)
            show ?thesis unfolding RuleA RuleB VarC
              by (metis None Residual_Join_Deletion.join_sym RuleA(1) RuleB(1) RuleB(2) join_opt.simps(2) left_lin_no_var_lhs.join_var_rule left_lin_no_var_lhs_axioms)
          next
            case (FunC Cs f)
            from None show ?thesis proof(cases "B \<squnion> C")
              case (Some BC)
              obtain BCs \<tau> where \<tau>:"match C (to_pterm (lhs \<beta>)) = Some \<tau>" and BC:"BC = Prule \<beta> BCs"
              and l_BCs:"length BCs = length Bs" and args_BC:"\<forall>i < length Bs. Bs ! i \<squnion> \<tau> (var_rule \<beta> ! i) = Some (BCs ! i)"  
                using join_rule_fun Some[unfolded RuleB FunC] subterm(3)[unfolded RuleB] FunC(1) by metis
              let ?x="var_rule \<beta> ! i"
              have IH:"join_opt (As ! i) (Bs ! i \<squnion> \<tau> ?x) = join_opt (\<tau> ?x) (As ! i \<squnion> Bs ! i)"
                by (metis RuleA(1) RuleA(3) RuleA(4) RuleB(3) RuleB(4) True \<tau> i(1) match_well_def nth_mem subterm.hyps subterm.prems(3) supt.arg vars_to_pterm)
              with i have "join_opt (As ! i) (Bs ! i \<squnion> \<tau> ?x) = None"
                by simp 
              then have "As ! i \<squnion> BCs ! i = None" 
                using args_BC i(1) l_As_Bs by auto 
              then have "(map2 (\<squnion>) As BCs) ! i = None"
                using i(1) l_As_Bs l_BCs by force 
              then have "those (map2 (\<squnion>) As BCs) = None"
                by (metis i(1) l_As_Bs l_BCs length_map length_zip min.idem not_None_eq nth_mem those_not_none_x)
              then show ?thesis
                using None RuleA(1) True BC Some by auto
            qed simp
          next
            case (RuleC \<gamma> Cs)
            from None show ?thesis proof(cases "B \<squnion> C")
              case (Some BC)
              then have "\<beta> = \<gamma>" 
                unfolding RuleB RuleC by (metis join.simps(3) option.distinct(1)) 
              from Some obtain BCs where BC:"BC = Prule \<beta> BCs" and l_BCs:"length BCs = length Bs" and 
                args_BC:"\<forall>i < length Bs. Bs ! i \<squnion> Cs ! i = Some (BCs ! i)"
                using RuleB(1) RuleC(1) join_rule_rule subterm.prems(2) subterm.prems(3) by blast  
              have IH:"join_opt (As ! i) (Bs ! i \<squnion> Cs ! i) = join_opt (Cs ! i) (As ! i \<squnion> Bs ! i)" 
                using subterm(1) by (metis RuleA(1) RuleA(3) RuleA(4) RuleB(4) RuleC(3) RuleC(4) True \<open>\<beta> = \<gamma>\<close> i(1) l_As_Bs nth_mem supt.arg) 
              then have "As ! i \<squnion> BCs ! i = None" 
                using args_BC i(1) l_As_Bs i(2) by fastforce
              then have "(map2 (\<squnion>) As BCs) ! i = None"
                using i(1) l_As_Bs l_BCs by force 
              then have "those (map2 (\<squnion>) As BCs) = None"
                by (metis i(1) l_As_Bs l_BCs length_map length_zip min.idem not_None_eq nth_mem those_not_none_x)
              then show ?thesis
                using None RuleA(1) True BC Some by auto
            qed simp
          qed
        next
          case False
          then show ?thesis proof(cases C)
            case (Var x)
            show ?thesis unfolding RuleA RuleB Var
              by (metis None Residual_Join_Deletion.join_sym RuleA(1) RuleB(1) RuleB(2) join_opt.simps(2) join_var_rule)
          next
            case (Pfun f Cs)
            show ?thesis unfolding RuleA RuleB Pfun
              by (metis (no_types, lifting) False RuleB(1) join.simps(3) join_opt.elims join_opt.simps(2) join_rule_fun subterm.prems(2))
          next
            case (Prule \<gamma> Cs)
            show ?thesis unfolding RuleA RuleB Prule
              by (smt (verit, ccfv_threshold) False Prule RuleA(1) RuleB(1) join_opt.elims join_rule_rule join_wf_pterm subterm.prems(1) subterm.prems(2) subterm.prems(3)) 
          qed
        qed 
      next
        case (Some AB)
        then have alpha_beta:"\<beta> = \<alpha>" 
          unfolding RuleA RuleB by (metis join.simps(3) option.distinct(1)) 
        with Some obtain ABs where AB:"AB = Prule \<alpha> ABs" and l_AB_A:"length ABs = length As" 
          and args_AB:"(\<forall>i<length Bs. As!i \<squnion> Bs!i = Some (ABs ! i))"
          by (smt (verit, ccfv_SIG) RuleA(1) RuleB(1) join_rule_rule subterm.prems(1) subterm.prems(2))
        from subterm(4) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
          case (VarC x)
          have "match (Var x) (to_pterm (Fun f' ts)) = None"
            by (metis case_optionE match_matches option.disc_eq_case(2) subst_apply_eq_Var term.distinct(1) to_pterm.simps(2)) 
          then show ?thesis unfolding Some AB unfolding RuleB VarC join.simps alpha_beta by (simp add: lhs)
        next
          case (FunC Cs f)
          show ?thesis proof(cases "match C (to_pterm (lhs \<alpha>))")
            case None
            then show ?thesis unfolding Some AB unfolding RuleB alpha_beta FunC by simp
          next
            case (Some \<sigma>)
            {fix i assume i:"i < length As" 
              have "(map \<sigma> (var_rule \<alpha>))!i \<in> wf_pterm R"
                using i match_well_def[OF subterm(4) Some] RuleA(3) by (simp add: vars_to_pterm)
              with i have "join_opt (As ! i) (Bs ! i \<squnion> (map \<sigma> (var_rule \<alpha>) ! i)) = map \<sigma> (var_rule \<alpha>) ! i \<squnion> ABs ! i"
                using subterm(1) RuleA RuleB by (metis alpha_beta args_AB join_opt.simps(1) nth_mem supt.arg)
            }note IH=this
            show ?thesis proof(cases "those (map2 (\<squnion>) Bs (map \<sigma> (var_rule \<alpha>)))")
              case None
              from None obtain i where i:"i < length (map2 (\<squnion>) Bs (map \<sigma> (var_rule \<alpha>)))" and "(map2 (\<squnion>) Bs (map \<sigma> (var_rule \<alpha>))) ! i = None"
                using list_all_length those_not_none_xs by blast 
              with IH have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) ABs)!i = None"
                using RuleA(3) l_AB_A by fastforce  
              with i(1) have "those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) ABs) = None"  
                using l_AB_A RuleA(3) those_not_none_x by (metis RuleB(3) alpha_beta length_map length_zip nth_mem option.exhaust) 
              with \<open>A \<squnion> B = Some AB\<close> Some None show ?thesis unfolding AB RuleB FunC alpha_beta by fastforce
            next
              case (Some BCs)
              then have BC:"B \<squnion> C = Some (Prule \<alpha> BCs)" 
                unfolding RuleB FunC alpha_beta using \<open>match C (to_pterm (lhs \<alpha>)) = Some \<sigma>\<close> by (simp add: FunC(1))
              then have l_BCs:"length BCs = length As"
                using RuleA(3) RuleB(3) Some alpha_beta length_those by force  
              {fix i assume "i < length As" 
                then have "As!i \<squnion> BCs!i = (map \<sigma> (var_rule \<alpha>)) ! i \<squnion> ABs ! i" 
                  using IH Some l_BCs length_those those_some2 by fastforce 
              }
              then have "map2 (\<squnion>) As BCs = map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) ABs"
                by (simp add: RuleA(3) l_AB_A l_BCs map_equality_iff)
              then show ?thesis using \<open>match C (to_pterm (lhs \<alpha>)) = Some \<sigma>\<close> 
                unfolding \<open>A \<squnion> B = Some AB\<close> AB BC unfolding RuleA FunC join_opt.simps join.simps by simp
            qed
          qed
        next
          case (RuleC \<gamma> Cs)
          show ?thesis proof(cases "\<alpha> = \<gamma>")
            case True
            {fix i assume i:"i < length As" 
              then have "join_opt (As ! i) (Bs ! i \<squnion> Cs ! i) = Cs ! i \<squnion> ABs ! i"
                using subterm(1) RuleA RuleB RuleC True alpha_beta args_AB by (metis join_opt.simps(1) nth_mem supt.arg)
            }note IH=this
            show ?thesis proof(cases "those (map2 (\<squnion>) Bs Cs)")
              case None
              then obtain i where i:"i < length (map2 (\<squnion>) Bs Cs)" "(map2 (\<squnion>) Bs Cs)!i = None"
                using list_all_length those_not_none_xs by blast 
              with IH have "map2 (\<squnion>) Cs ABs ! i = None"
                using RuleA(3) RuleC(3) True l_AB_A by fastforce 
              with i(1) have "those (map2 (\<squnion>) Cs ABs) = None"
                by (metis RuleA(3) RuleB(3) RuleC(3) True alpha_beta l_AB_A length_map length_zip not_Some_eq nth_mem those_not_none_x)
              with None show ?thesis unfolding Some AB unfolding RuleC RuleB True alpha_beta by simp
            next
              case (Some BCs)
              then have BC:"B \<squnion> C = Some (Prule \<alpha> BCs)"
                by (simp add: RuleB(1) RuleC(1) True alpha_beta) 
              {fix i assume "i < length As" 
                with IH have "As!i \<squnion> BCs!i = Cs!i \<squnion> ABs!i"
                  using RuleA(3) RuleB(3) RuleC(3) Some True alpha_beta those_some2 by fastforce 
              }
              moreover have "length BCs = length As"
                using RuleA(3) RuleB(3) RuleC(3) Some True alpha_beta length_those by force
              ultimately have "those (map2 (\<squnion>) As BCs) = those (map2 (\<squnion>) Cs ABs)"
                by (smt (verit, ccfv_SIG) RuleA(3) RuleB(3) RuleC(3) Some True alpha_beta l_AB_A length_map length_those length_zip map_equality_iff nth_zip old.prod.case)
              then show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> AB BC unfolding RuleA RuleC True alpha_beta by simp
            qed
          next
            case False
            then show ?thesis unfolding \<open>A \<squnion> B = Some AB\<close> AB unfolding RuleA RuleB RuleC
              by (simp add: alpha_beta)
          qed 
        qed
      qed
    qed
  qed
qed

text\<open>Preparation for well-definedness result for @{const join_list}.\<close>
lemma join_triple_defined: 
  assumes "A \<in> wf_pterm R" "B \<in> wf_pterm R" "C \<in> wf_pterm R" 
    and "A \<squnion> B \<noteq> None" "B \<squnion> C \<noteq> None" "A \<squnion> C \<noteq> None" 
  shows "join_opt A (B \<squnion> C) \<noteq> None" 
  using assms proof(induct A arbitrary:B C rule:subterm_induct)
  case (subterm A)
  from subterm(5) obtain AB where joinAB:"A \<squnion> B = Some AB" by blast
  from subterm(6) obtain BC where joinBC:"B \<squnion> C = Some BC" by blast
  from subterm(7) obtain AC where joinAC:"A \<squnion> C = Some AC" by blast
  from subterm(2) show ?case proof(cases A rule:wf_pterm.cases[case_names VarA FunA RuleA])
    case (VarA x)
    from subterm(3,5) show ?thesis proof(cases B rule:wf_pterm.cases[case_names VarB FunB RuleB])
      case (VarB y)
      from subterm(5) have x:"x = y" unfolding VarA VarB by (meson join.simps(1)) 
      from subterm(4,6) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
        case (VarC z)
        from subterm(6) show ?thesis unfolding VarA VarB x VarC
          by (metis join.simps(1) join_opt.simps(1)) 
      next
        case (RuleC \<alpha> Cs)
        from subterm(5-) show ?thesis unfolding VarA VarB RuleC x
          by (metis Residual_Join_Deletion.join_sym RuleC(1) VarA join_opt.elims join_with_source option.sel source.simps(1) source_join subterm.prems(1) subterm.prems(3) to_pterm.simps(1) x)
      qed (simp add: VarB)
    next
      case (RuleB \<alpha> Bs)
      from subterm(2-) VarA no_var_lhs RuleB show ?thesis
        by (metis join_sym join_opt.elims join_wf_pterm join_with_source source.simps(1) source_join to_pterm.simps(1)) 
    qed (simp add: VarA)
  next
    case (FunA As f)
    from subterm(3,5) show ?thesis proof(cases B rule:wf_pterm.cases[case_names VarB FunB RuleB])
      case (FunB Bs g)
      from subterm(5) have fg:"f = g" and l_A_B:"length As = length Bs"  
        unfolding FunA FunB by (meson join.simps(2))+
      obtain ABs where AB:"AB = Pfun f ABs" and l_AB_A:"length ABs = length As" 
        and args_AB:"(\<forall>i<length Bs. As!i \<squnion>  Bs!i = Some (ABs ! i))"
        using join_fun_fun[OF joinAB[unfolded FunA FunB]] by fastforce  
      from subterm(4,6) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
        case (FunC Cs h)
        from subterm(6) have gh:"g = h" and l_B_C:"length Bs = length Cs" 
          unfolding FunB FunC by (meson join.simps(2))+ 
        from subterm(7) have fh:"f = h" and l_A_C:"length As = length Cs" 
          unfolding FunA FunC by (meson join.simps(2))+ 
        obtain BCs where BC:"BC = Pfun g BCs" and l_BC_B:"length BCs = length Bs" 
          and args_BC:"(\<forall>i<length BCs. Bs!i \<squnion>  Cs!i = Some (BCs ! i))"
          using join_fun_fun[OF joinBC[unfolded FunB FunC]] by fastforce  
        obtain ACs where AC:"AC = Pfun h ACs" and l_AC_C:"length ACs = length Cs" 
          and args_AC:"(\<forall>i<length ACs. As!i \<squnion>  Cs!i = Some (ACs ! i))"
          using join_fun_fun[OF joinAC[unfolded FunA FunC]] by fastforce 
        have "those (map2 (\<squnion>) As BCs) \<noteq> None" proof-
          {fix i assume i:"i < length (zip As BCs)"
            from FunA FunB FunC i have "join_opt (As!i) ((Bs!i) \<squnion> (Cs!i)) \<noteq> None" 
              using subterm(1) l_A_B l_B_C l_AC_C by (smt (verit, ccfv_threshold) args_AB args_AC args_BC length_zip min_less_iff_conj nth_mem option.distinct(1) supt.arg)
            then have "(map2 (\<squnion>) As BCs)!i \<noteq> None" 
              using i args_BC by simp 
          }
          then show ?thesis
            by (simp add: list_all_length those_not_none_xs)
        qed
        then show ?thesis 
          unfolding joinBC BC unfolding FunA fg gh join_opt.simps
          by (simp add: l_A_B l_BC_B option.case_eq_if)  
      next
        case (RuleC \<alpha> Cs)
        from joinBC subterm(4) obtain \<sigma> BCs where match_lhs_B:"match B (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
          and BC:"BC = Prule \<alpha> BCs" and l_BC_C:"length BCs = length Cs" 
          and args_BC:"(\<forall>i<length Cs. Cs ! i \<squnion> \<sigma> (var_rule \<alpha> ! i) = Some (BCs ! i))"
          unfolding FunB RuleC using join_rule_fun RuleC(1,2,3) join_sym by metis
        from joinAC subterm(4) obtain \<tau> ACs where match_lhs_A:"match A (to_pterm (lhs \<alpha>)) = Some \<tau>" 
          and AC:"AC = Prule \<alpha> ACs" and l_AC_C:"length ACs = length Cs" 
          and args_AC:"(\<forall>i<length Cs. Cs ! i \<squnion> \<tau> (var_rule \<alpha> ! i) = Some (ACs ! i))"
          unfolding FunA RuleC using join_rule_fun RuleC(3) join_sym by metis 
        have "those (map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) BCs) \<noteq> None" proof-
          {fix i assume i:"i < length (zip (map \<tau> (var_rule \<alpha>)) BCs)"
            from i obtain x where x:"var_rule \<alpha> ! i = x" "x \<in> vars_term (to_pterm (lhs \<alpha>))"
                by (metis (no_types, lifting) comp_apply length_map length_zip min_less_iff_conj nth_mem set_remdups set_rev set_vars_term_list vars_to_pterm)
            have "\<tau> (var_rule \<alpha> ! i) \<lhd> A" proof-
              from RuleC(2) no_var_lhs obtain f' ts where "lhs \<alpha> = Fun f' ts" by fastforce 
              with x show ?thesis 
                using subst_image_subterm[of x] match_lhs_A unfolding FunA
                by (smt (verit) match_matches to_pterm.simps(2)) 
            qed
            moreover have "\<tau> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
              using i match_well_def[OF subterm(2) match_lhs_A] by (simp add: vars_to_pterm) 
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
              using i match_well_def[OF subterm(3) match_lhs_B] by (simp add: vars_to_pterm) 
            moreover have "\<tau> (var_rule \<alpha> ! i) \<squnion> \<sigma> (var_rule \<alpha> ! i) \<noteq> None" 
              using join_pterm_subst_Some x match_lhs_B match_lhs_A match_matches subterm.prems(4) x by blast 
            moreover have "\<tau> (var_rule \<alpha> ! i) \<squnion> (Cs!i) \<noteq> None" 
              using args_AC by (metis join_sym RuleC(3) i length_map length_zip min_less_iff_conj option.distinct(1)) 
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<squnion> (Cs!i) \<noteq> None" 
              using args_BC by (metis join_sym RuleC(3) i length_map length_zip min_less_iff_conj option.distinct(1)) 
            ultimately have IH:"join_opt (\<tau> (var_rule \<alpha> ! i)) (\<sigma> (var_rule \<alpha> ! i) \<squnion> (Cs!i)) \<noteq> None" 
              using RuleC(3,4) subterm(1) i by simp
            from IH have "(\<tau> (var_rule \<alpha> ! i)) \<squnion> (BCs!i) \<noteq> None" 
              using i args_BC l_BC_C join_sym by (metis (no_types, opaque_lifting) join_opt.simps(1) length_zip min_less_iff_conj)
            then have "(map2 (\<squnion>) (map \<tau> (var_rule \<alpha>)) BCs)!i \<noteq> None" 
              unfolding nth_map[OF i] using i by auto
          }
          then show ?thesis by (simp add: list_all_length those_not_none_xs)
        qed
        with match_lhs_A show ?thesis 
          unfolding joinBC BC FunA unfolding fg join_opt.simps join.simps(7) by force 
      qed (simp add:FunB)
    next
      case (RuleB \<alpha> Bs)
      from joinAB have *:"Prule \<alpha> Bs \<squnion> Pfun f As = Some AB" unfolding FunA RuleB using join_sym by metis 
      obtain \<sigma> ABs where match_lhs_A:"match A (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
        and AB:"AB = Prule \<alpha> ABs" and l_A_AB:"length ABs = length Bs" 
        and args_AB:"(\<forall>i<length Bs. Bs ! i \<squnion> \<sigma> (var_rule \<alpha> ! i) = Some (ABs ! i))"
        unfolding FunA RuleB using join_rule_fun[OF * subterm(3)[unfolded FunA RuleB]] RuleB(3) by fastforce  
      from subterm(4,7) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
        case (FunC Cs g)
        from joinBC have *:"Prule \<alpha> Bs \<squnion> Pfun g Cs = Some BC" unfolding FunC RuleB by metis 
        from subterm(3) obtain \<tau> BCs where match_lhs_C:"match C (to_pterm (lhs \<alpha>)) = Some \<tau>" 
          and BC:"BC = Prule \<alpha> BCs" and l_BC_B:"length BCs = length Bs" 
          and args_BC:"(\<forall>i<length Bs. Bs ! i \<squnion> \<tau> (var_rule \<alpha> ! i) = Some (BCs ! i))"
          unfolding FunC RuleB using join_rule_fun[OF joinBC[unfolded FunC RuleB]] RuleB(3) by fastforce
        have "those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) \<noteq> None" proof-
          {fix i assume i:"i < length (zip (map \<tau> (var_rule \<alpha>)) BCs)"
            from i obtain x where x:"var_rule \<alpha> ! i = x" "x \<in> vars_term (to_pterm (lhs \<alpha>))"
                by (metis (no_types, lifting) comp_apply length_map length_zip min_less_iff_conj nth_mem set_remdups set_rev set_vars_term_list vars_to_pterm)
            have "\<sigma> (var_rule \<alpha> ! i) \<lhd> A" proof-
              from RuleB(2) no_var_lhs obtain f' ts where "lhs \<alpha> = Fun f' ts" by fastforce 
              with x show ?thesis 
                using subst_image_subterm[of x] match_lhs_A unfolding FunA
                by (smt (verit) match_matches to_pterm.simps(2)) 
            qed
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
              using i match_well_def[OF subterm(2) match_lhs_A] by (simp add: vars_to_pterm) 
            moreover have "\<tau> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
              using i match_well_def[OF subterm(4) match_lhs_C] by (simp add: vars_to_pterm) 
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<squnion> \<tau> (var_rule \<alpha> ! i) \<noteq> None" 
              using join_pterm_subst_Some x match_lhs_C match_lhs_A match_matches subterm.prems(6) x by blast 
            moreover have "(Bs!i) \<squnion> \<tau> (var_rule \<alpha> ! i) \<noteq> None" 
              using args_BC i by (metis RuleB(3) i length_map length_zip min_less_iff_conj option.distinct(1)) 
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<squnion> (Bs!i) \<noteq> None" 
              using args_AB by (metis join_sym RuleB(3) i length_map length_zip min_less_iff_conj option.distinct(1)) 
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<squnion> \<tau> (var_rule \<alpha> ! i) \<noteq> None" 
              using join_pterm_subst_Some x match_lhs_C match_lhs_A match_matches subterm.prems(6) x by blast 
            ultimately have IH:"join_opt (\<sigma> (var_rule \<alpha> ! i)) ((Bs!i) \<squnion> \<tau> (var_rule \<alpha> ! i)) \<noteq> None" 
              using RuleB(3,4) subterm(1) i by simp
            then have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs)!i \<noteq> None" 
              using i args_BC l_BC_B unfolding nth_map[OF i] using i by auto
          }
          then show ?thesis by (simp add: list_all_length those_not_none_xs)
        qed
        with match_lhs_A show ?thesis 
          unfolding joinBC BC FunA unfolding join_opt.simps join.simps(7) by force 
      next
        case (RuleC \<beta> Cs)
        obtain BCs where \<alpha>:"\<alpha> = \<beta>" and l_B_C:"length Bs = length Cs"  
          and BC:"BC = Prule \<alpha> BCs" and l_BC_B:"length BCs = length Bs" and args_BC:"(\<forall>i<length Bs. Bs ! i \<squnion> Cs ! i = Some (BCs ! i))" 
          using join_rule_rule joinBC subterm(3,4) unfolding RuleB(1) RuleC(1) by blast 
        from joinAC match_lhs_A have args_AC:"\<forall>i<length Cs. Cs ! i \<squnion> \<sigma> (var_rule \<alpha> ! i) \<noteq> None" 
          using join_rule_fun by (metis (no_types, lifting) FunA(1) Residual_Join_Deletion.join_sym RuleC(1) \<alpha> option.distinct(1) option.inject subterm.prems(3)) 
        have "those (map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs) \<noteq> None" proof-
          {fix i assume i:"i < length (zip (map \<sigma> (var_rule \<alpha>)) BCs)"
            from i obtain x where x:"var_rule \<alpha> ! i = x" "x \<in> vars_term (to_pterm (lhs \<alpha>))"
                by (metis (no_types, lifting) comp_apply length_map length_zip min_less_iff_conj nth_mem set_remdups set_rev set_vars_term_list vars_to_pterm)
            have "\<sigma> (var_rule \<alpha> ! i) \<lhd> A" proof-
              from RuleB(2) no_var_lhs obtain f' ts where "lhs \<alpha> = Fun f' ts" by fastforce 
              with x show ?thesis 
                using subst_image_subterm[of x] match_lhs_A unfolding FunA
                by (smt (verit) match_matches to_pterm.simps(2)) 
            qed
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
              using i match_well_def[OF subterm(2) match_lhs_A] by (simp add: vars_to_pterm) 
            moreover have "\<sigma> (var_rule \<alpha> ! i) \<squnion> (Bs!i) \<noteq> None" 
              using args_AB by (metis join_sym RuleB(3) i length_map length_zip min_less_iff_conj option.distinct(1))
            moreover have "(Bs!i) \<squnion> (Cs!i) \<noteq> None" 
              using args_BC i by (simp add: l_BC_B) 
             moreover have "\<sigma> (var_rule \<alpha> ! i) \<squnion> (Cs!i) \<noteq> None" 
              using args_AC by (metis join_sym RuleC(3) \<alpha> i length_map length_zip min_less_iff_conj)
            ultimately have IH:"join_opt (\<sigma> (var_rule \<alpha> ! i)) ((Bs!i) \<squnion> (Cs!i)) \<noteq> None" 
              using RuleB(3,4) RuleC(3,4) subterm(1) i l_B_C by auto
            then have "(map2 (\<squnion>) (map \<sigma> (var_rule \<alpha>)) BCs)!i \<noteq> None" 
              using i args_BC l_BC_B unfolding nth_map[OF i] using i by auto
          }
          then show ?thesis by (simp add: list_all_length those_not_none_xs)
        qed
        with match_lhs_A show ?thesis 
          unfolding joinBC BC FunA unfolding join_opt.simps join.simps(7) by force 
      qed (simp add: FunA)
    qed (simp add: FunA)
  next
    case (RuleA \<alpha> As)
    from subterm(3,5) show ?thesis proof(cases B rule:wf_pterm.cases[case_names VarB FunB RuleB])
      case (VarB x)
      from subterm(2-) show ?thesis
        by (metis join_sym VarB joinBC join_opt.simps(1) join_with_source source.simps(1) source_join to_pterm.simps(1))
    next
      case (FunB Bs f)
      from subterm(2) obtain \<sigma> ABs where match_lhs_B:"match B (to_pterm (lhs \<alpha>)) = Some \<sigma>" 
        and AB:"AB = Prule \<alpha> ABs" and l_A_AB:"length ABs = length As" 
        and args_AB:"(\<forall>i<length As. As ! i \<squnion> \<sigma> (var_rule \<alpha> ! i) = Some (ABs ! i))"
        unfolding RuleA FunB using join_rule_fun[OF joinAB[unfolded RuleA FunB]] RuleA(1,3) by fastforce
      from subterm(4,6) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
        case (FunC Cs g)
        from subterm(2) obtain \<tau> ACs where match_lhs_C:"match C (to_pterm (lhs \<alpha>)) = Some \<tau>" 
          and AC:"AC = Prule \<alpha> ACs" and l_A_AC:"length ACs = length As" 
          and args_AC:"(\<forall>i<length As. As ! i \<squnion> \<tau> (var_rule \<alpha> ! i) = Some (ACs ! i))"
          unfolding RuleA FunC using join_rule_fun[OF joinAC[unfolded RuleA FunC]] RuleA(1,3) by fastforce
        from joinBC obtain \<rho> where "\<forall>x\<in>vars_term (to_pterm (lhs \<alpha>)). \<sigma> x \<squnion> \<tau> x = Some (\<rho> x)" and "BC = to_pterm (lhs \<alpha>) \<cdot> \<rho>"
          using join_pterm_subst_Some[of "to_pterm (lhs \<alpha>)"] match_lhs_C match_lhs_B by (smt (verit) match_matches) 
        then obtain BCs where args_BC:"(\<forall>i<length As. \<sigma> (var_rule \<alpha> ! i) \<squnion> \<tau> (var_rule \<alpha> ! i) = Some (BCs ! i))"
          and BC:"BC = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>BCs\<rangle>\<^sub>\<alpha>" and l_A_BC:"length As = length BCs"
          using subst_imp_mk_subst[of "BC" "to_pterm (lhs \<alpha>)"] RuleA(3)
          by (smt (verit, del_insts) comp_apply nth_mem set_remdups set_rev set_vars_term_list vars_to_pterm)
        from RuleA(2) no_var_lhs obtain f' ts where lhs:"lhs \<alpha> = Fun f' ts" by fastforce
        {fix i assume i:"i < length As"
          from i obtain x where x:"var_rule \<alpha> ! i = x" "x \<in> vars_term (to_pterm (lhs \<alpha>))"
            by (metis RuleA(3) comp_apply nth_mem set_remdups set_rev set_vars_term_list vars_to_pterm)
          have "\<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
            using RuleA(3) i match_well_def[OF subterm(3) match_lhs_B] by (simp add: vars_to_pterm) 
          moreover have "\<tau> (var_rule \<alpha> ! i) \<in> wf_pterm R" 
            using RuleA(3) i match_well_def[OF subterm(4) match_lhs_C] by (simp add: vars_to_pterm) 
          moreover have "As!i \<squnion> \<sigma> (var_rule \<alpha> ! i) \<noteq> None" 
            using args_AB i by auto 
          moreover have "As!i \<squnion> \<tau> (var_rule \<alpha> ! i) \<noteq> None" 
            using args_AC i by auto 
          moreover have "\<sigma> (var_rule \<alpha> ! i) \<squnion> \<tau> (var_rule \<alpha> ! i) \<noteq> None"
            using args_BC i by auto 
          ultimately have IH:"join_opt (As!i) (\<sigma> (var_rule \<alpha> ! i) \<squnion> \<tau> (var_rule \<alpha> ! i)) \<noteq> None" 
            using RuleA(3,4) subterm(1) i by (metis RuleA(1) nth_mem supt.arg) 
          then have "As!i \<squnion> BCs!i \<noteq> None" 
            using i args_BC by auto 
        }
        with subterm(2) show ?thesis 
          unfolding joinBC BC RuleA(1) unfolding join_opt.simps using join_rule_lhs l_A_BC by auto 
      next
        case (RuleC \<beta> Cs)
        from joinBC subterm(4) obtain \<tau> BCs where match_lhs_B2:"match B (to_pterm (lhs \<beta>)) = Some \<tau>" 
          and BC:"BC = Prule \<beta> BCs" and l_BC_C:"length BCs = length Cs" 
          and args_BC:"(\<forall>i<length Cs. Cs ! i \<squnion> \<tau> (var_rule \<beta> ! i) = Some (BCs ! i))"
          unfolding FunB RuleC using join_rule_fun RuleC(1,2,3) join_sym by metis
        from joinAC have \<alpha>:"\<alpha> = \<beta>" and l_A_C:"length As = length Cs" 
          unfolding RuleA RuleC by(metis join.simps(3) option.distinct(1))+
        have "those (map2 (\<squnion>) As BCs) \<noteq> None" proof-
          {fix i assume i:"i < length (zip As BCs)" 
            moreover have "\<tau> (var_rule \<beta> ! i) \<in> wf_pterm R" 
              using i match_well_def[OF subterm(3) match_lhs_B2] by (simp add: RuleA(3) \<alpha> vars_to_pterm) 
            moreover have "As!i \<squnion> \<tau> (var_rule \<beta> ! i) \<noteq> None" 
              using join_pterm_subst_Some match_lhs_B subterm(5) \<alpha> args_AB i match_lhs_B2 by auto
            moreover have "(As!i) \<squnion> (Cs!i) \<noteq> None" 
              using joinAC RuleA(1) RuleC(1) i join_rule_rule subterm.prems(1) subterm.prems(3) by fastforce 
            moreover have "\<tau> (var_rule \<beta> ! i) \<squnion> (Cs!i) \<noteq> None" 
              using args_BC i by (simp add: join_sym l_A_C) 
            ultimately have IH:"join_opt (As!i) (\<tau> (var_rule \<beta> ! i) \<squnion> (Cs!i)) \<noteq> None" 
              using RuleA(1,3,4) RuleC(3,4) subterm(1) i \<alpha> by simp
            from IH have "(As!i) \<squnion> (BCs!i) \<noteq> None" 
              using i args_BC by (simp add: join_sym l_BC_C) 
            then have "(map2 (\<squnion>) As BCs)!i \<noteq> None" 
              unfolding nth_map[OF i] using i by auto
          }
          then show ?thesis by (simp add: list_all_length those_not_none_xs)
        qed
        then show ?thesis 
          unfolding joinBC BC RuleA \<alpha> unfolding join_opt.simps join.simps(7) by force
      qed (simp add:FunB)
    next
      case (RuleB \<beta> Bs)
      from joinAB have \<alpha>\<beta>:"\<alpha> = \<beta>" and l_A_B:"length As = length Bs" 
        unfolding RuleA RuleB by(metis join.simps(3) option.distinct(1))+
      obtain ABs where AB:"AB = Prule \<alpha> ABs" and l_AB_B:"length ABs = length Bs" 
        and args_AB:"(\<forall>i<length ABs. As!i \<squnion> Bs!i = Some (ABs ! i))"
        using join_rule_rule[OF joinAB[unfolded RuleA RuleB]] subterm(2,3) RuleA(1) RuleB(1) by metis 
      from subterm(4,6) show ?thesis proof(cases C rule:wf_pterm.cases[case_names VarC FunC RuleC])
        case (VarC x)
        from joinBC RuleB(2) no_var_lhs show ?thesis unfolding VarC RuleB
          by (metis Residual_Join_Deletion.join_sym RuleB(1) VarC join_opt.simps(1) join_with_source source.simps(1) source_join subterm.prems(2) subterm.prems(3) subterm.prems(4) to_pterm.simps(1)) 
      next
        case (FunC Cs f)
        from subterm(3) obtain \<sigma> BCs where match_lhs_C:"match C (to_pterm (lhs \<beta>)) = Some \<sigma>" 
          and BC:"BC = Prule \<beta> BCs" and l_BC_C:"length BCs = length Bs" 
          and args_BC:"(\<forall>i<length Bs. Bs ! i \<squnion> \<sigma> (var_rule \<beta> ! i) = Some (BCs ! i))"
          unfolding RuleB using join_rule_fun[OF joinBC[unfolded RuleB FunC]] RuleB(1,2,3) by (metis FunC(1)) 
        have "those (map2 (\<squnion>) As BCs) \<noteq> None" proof-
          {fix i assume i:"i < length (zip As BCs)" 
            have "\<sigma> (var_rule \<beta> ! i) \<in> wf_pterm R" 
              using i match_well_def[OF subterm(4) match_lhs_C] by (simp add: RuleA(3) \<alpha>\<beta> vars_to_pterm)
            moreover have "As!i \<squnion> \<sigma> (var_rule \<beta> ! i) \<noteq> None" 
              using match_lhs_C joinAC \<alpha>\<beta> args_AB i unfolding RuleA(1) FunC
              by (metis (no_types, lifting) RuleA(1) join_rule_fun length_zip min_less_iff_conj option.distinct(1) option.sel subterm.prems(1)) 
            ultimately have IH:"join_opt (As!i) ((Bs!i) \<squnion> (\<sigma> (var_rule \<beta> ! i))) \<noteq> None" 
              using RuleA(1,3,4) subterm(1) i args_AB args_BC
              by (metis (no_types, lifting) RuleB(4) l_AB_B l_A_B length_zip min_less_iff_conj nth_mem option.distinct(1) supt.arg) 
            from IH have "(As!i) \<squnion> (BCs!i) \<noteq> None" 
              using i args_BC by (simp add: join_sym l_BC_C) 
            then have "(map2 (\<squnion>) As BCs)!i \<noteq> None" 
              unfolding nth_map[OF i] using i by auto
          }
          then show ?thesis by (simp add: list_all_length those_not_none_xs)
        qed
        then show ?thesis 
          unfolding joinBC BC RuleA \<alpha>\<beta> unfolding join_opt.simps join.simps(7) by force
      next
        case (RuleC \<gamma> Cs)
        from joinBC have \<beta>\<gamma>:"\<beta> = \<gamma>" and l_B_C:"length Bs = length Cs" 
          using RuleB RuleC join_rule_rule by blast+
        obtain BCs where BC:"BC = Prule \<beta> BCs" and l_BC_B:"length BCs = length Bs" 
          and args_BC:"(\<forall>i<length BCs. Bs!i \<squnion>  Cs!i = Some (BCs ! i))"
          using join_rule_rule[OF joinBC[unfolded RuleB RuleC]] subterm(3,4) RuleB(1) RuleC(1) by metis 
        obtain ACs where AC:"AC = Prule \<alpha> ACs" and l_AC_C:"length ACs = length Cs" 
          and args_AC:"(\<forall>i<length ACs. As!i \<squnion>  Cs!i = Some (ACs ! i))"
          using join_rule_rule[OF joinAC[unfolded RuleA RuleC]] subterm(2,4) RuleA(1) RuleC(1) by metis 
        have "those (map2 (\<squnion>) As BCs) \<noteq> None" proof-
          {fix i assume i:"i < length (zip As BCs)"
            from RuleA(1,4) RuleB(1,4) RuleC(1,4) i have "join_opt (As!i) ((Bs!i) \<squnion> (Cs!i)) \<noteq> None" 
              using subterm(1) l_A_B l_B_C l_AC_C l_AB_B args_AB args_AC args_BC
              by (smt (verit) length_zip min_less_iff_conj nth_mem option.distinct(1) supt.arg)
            then have "(map2 (\<squnion>) As BCs)!i \<noteq> None" 
              using i args_BC by simp 
          }
          then show ?thesis
            by (simp add: list_all_length those_not_none_xs)
        qed
        then show ?thesis 
          unfolding joinBC BC unfolding RuleA \<alpha>\<beta> join_opt.simps by (simp add: option.case_eq_if)  
      qed
    qed
  qed
qed

lemma join_list_defined: 
  assumes "\<forall> a1 a2. a1 \<in> set As \<and> a2 \<in> set As \<longrightarrow> a1 \<squnion> a2 \<noteq> None"
    and "\<forall>a \<in> set As. a \<in> wf_pterm R" and "As \<noteq> []"
  shows "\<exists> D. join_list As = Some D \<and> D \<in> wf_pterm R" 
using assms proof(induct "length As" arbitrary:As rule:full_nat_induct)
  case 1
  then show ?case proof(cases As rule:list.exhaust[case_names empty As])
    case (As A1 As')
    with 1 show ?thesis proof(cases As' rule:list.exhaust[case_names empty As'])
      case (As' A2 As'')
      have A1_wf:"A1 \<in> wf_pterm R" and A2_wf:"A2 \<in> wf_pterm R" 
        using 1(3) unfolding As As' by auto
      from As' 1(2) obtain A12 where A12:"A1 \<squnion> A2 = Some A12" 
        unfolding As by fastforce
      with A1_wf A2_wf have A12_wf:"A12 \<in> wf_pterm R" 
        by (simp add: join_wf_pterm)
      show ?thesis proof(cases "As'' = []")
        case True
        show ?thesis 
          unfolding As As' True join_list.simps using A12 A12_wf by simp
      next
        case False  
        from 1 obtain D' where D':"join_list As'' = Some D'" "D' \<in> wf_pterm R"
          unfolding As As' by (metis False Suc_le_length_iff impossible_Cons list.set_intros(2) nat_le_linear)
        from 1(2) have "\<forall>a1 a2. a1 \<in> set (A2 # As'') \<and> a2 \<in> set (A2 # As'') \<longrightarrow> a1 \<squnion> a2 \<noteq> None" 
          unfolding As As' by force
        moreover have "Suc (length (A2 # As'')) \<le> length As" 
          unfolding As As' by simp
        moreover have "(\<forall>a\<in>set (A2 # As''). a \<in> wf_pterm R)" 
          using 1(3) unfolding As As' by simp 
        moreover have "A2 # As'' \<noteq> []" by simp
        ultimately obtain D where "join_list (A2 # As'') = Some D" and D_wf:"D \<in> wf_pterm R" 
          using 1(1) by blast
        then have D:"A2 \<squnion> D' = Some D" 
          using D' False using join_list.elims by force
        moreover have "A1 \<squnion> D' \<noteq> None" proof-
          from 1(2) have "\<forall>a1 a2. a1 \<in> set (A1 # As'') \<and> a2 \<in> set (A1 # As'') \<longrightarrow> a1 \<squnion> a2 \<noteq> None" 
            unfolding As As' by force
          moreover have "Suc (length (A1 # As'')) \<le> length As" 
            unfolding As As' by simp
          moreover have "(\<forall>a\<in>set (A1 # As''). a \<in> wf_pterm R)" 
            using 1(3) unfolding As As' by simp 
          moreover have "A1 # As'' \<noteq> []" by simp
          ultimately have "join_list (A1 # As'') \<noteq> None"
            using 1(1) by (metis option.simps(3)) 
          with D' show ?thesis
            by (metis False join_list.simps(3) join_opt.simps(1) list.exhaust) 
        qed
        moreover have "A1 \<squnion> A2 \<noteq> None" 
          using 1(2) unfolding As As' by simp
        ultimately have "join_opt A1 (A2 \<squnion> D') \<noteq> None"
          using join_triple_defined D' A1_wf A2_wf unfolding join_list.simps by blast
        moreover have "join_list As = join_opt A1 (A2 \<squnion> D')" 
          unfolding As As' using False by (metis D'(1) join_list.simps(3) join_opt.simps(1) neq_Nil_conv) 
        ultimately show ?thesis 
          unfolding D join_opt.simps using D_wf A1_wf join_wf_pterm by fastforce
      qed
    qed simp
  qed simp
qed

lemma join_list_wf_pterm:
  assumes "\<forall>a \<in> set As. a \<in> wf_pterm R" 
    and "join_list As = Some B"
  shows "B \<in> wf_pterm R"
  using assms proof(induct As arbitrary:B)
  case (Cons A As)
  then show ?case proof(cases "As = []")
    case True
    from Cons(2,3) show ?thesis unfolding join_list.simps True by simp
  next
    case False
    with Cons(3) obtain B' where B':"join_list As = Some B'"
      by (smt (verit, ccfv_threshold) join_list.elims join_opt.elims list.inject) 
    with Cons have "B' \<in> wf_pterm R"
      by simp
    then show ?thesis using B' Cons
      by (metis False join_list.simps(3) join_opt.simps(1) join_wf_pterm list.set_intros(1) neq_Nil_conv)
  qed
qed simp

lemma source_join_list:
  assumes "join_list As = Some B" and "\<forall>a \<in> set As. a \<in> wf_pterm R"
  shows "\<And>A. A \<in> set As \<Longrightarrow> source A = source B" 
proof-
  fix Ai assume "Ai \<in> set As" 
  then show "co_initial Ai B" using assms proof(induct As arbitrary: B)
    case Nil
    then show ?case by (simp add: source_join) 
  next
    case (Cons A As)
    show ?case proof(cases "As = []")
      case True
      from Cons show ?thesis unfolding True
        by (simp add: source_join)
    next
      case False
      have wf:"A \<in> wf_pterm R" "\<forall>a\<in>set As. a \<in> wf_pterm R" 
        using Cons(4) by simp_all
      from Cons(2,3)obtain B' where B':"join_list As = Some B'" "join_list (A#As) = join_opt A (Some B')"
        by (metis False join_list.simps(3) join_opt.simps(2) list.exhaust option.exhaust)
      show ?thesis proof(cases "Ai = A")
        case True
        show ?thesis unfolding True 
          using B' Cons(3) False source_join wf by (metis join_list_wf_pterm join_opt.simps(1))
      next
        case False
        then have "Ai \<in> set As" 
          using Cons(2) by simp
        with Cons(1) B'(1) wf(2) have "co_initial Ai B'" 
          by simp
        moreover from B'(1) wf have "B' \<in> wf_pterm R" 
          using join_list_wf_pterm by blast 
        ultimately show ?thesis 
          by (metis B'(2) Cons.prems(2) Residual_Join_Deletion.join_sym join_opt.simps(1) local.wf(1) source_join)
      qed 
    qed
  qed
qed 
 
end

subsection\<open>Deletion\<close>
fun deletion :: "('f, 'v) pterm \<Rightarrow> ('f,'v) pterm \<Rightarrow> ('f,'v) pterm option" (infixr "-\<^sub>p" 70)
  where
  "Var x -\<^sub>p Var y =
    (if x = y then Some (Var x) else None)"
| "Pfun f As -\<^sub>p Pfun g Bs =
    (if (f = g \<and> length As = length Bs) then
      (case those (map2 (-\<^sub>p) As Bs) of
        Some xs \<Rightarrow> Some (Pfun f xs)
      | None \<Rightarrow> None)
    else None)"
| "Prule \<alpha> As -\<^sub>p Prule \<beta> Bs =
    (if \<alpha> = \<beta> then
      (case those (map2 (-\<^sub>p) As Bs) of
        Some xs \<Rightarrow> Some ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>xs\<rangle>\<^sub>\<alpha>)
      | None \<Rightarrow> None)
    else None)"
| "Prule \<alpha> As -\<^sub>p B =
    (case match B (to_pterm (lhs \<alpha>)) of
      None \<Rightarrow> None
    | Some \<sigma> \<Rightarrow>
      (case those (map2 (-\<^sub>p) As (map \<sigma> (var_rule \<alpha>))) of
        Some xs \<Rightarrow> Some (Prule \<alpha> xs)
      | None \<Rightarrow> None))"
| "A -\<^sub>p B = None"

lemma del_empty:
  assumes "A \<in> wf_pterm R"
  shows "A -\<^sub>p (to_pterm (source A)) = Some A"
using assms proof (induction A)
  case (2 As f)
  then have "those (map2 deletion As (map (to_pterm \<circ> source) As)) = Some As" by (simp add:those_some)
  then show ?case by simp
next
  case (3 \<alpha> As)
  then have \<sigma>: "match (to_pterm (lhs \<alpha> \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>)) (to_pterm (lhs \<alpha>)) = Some (\<langle>map (to_pterm \<circ> source) As\<rangle>\<^sub>\<alpha>)"
    by (metis (no_types, lifting) fun_mk_subst lhs_subst_trivial map_map to_pterm.simps(1) to_pterm_subst)
  from 3 have "those (map2 deletion As (map (to_pterm \<circ> source) As)) = Some As"
    by (simp add:those_some)
  then have args:"those (map2 deletion As (map (\<langle>map (to_pterm \<circ> source) As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>))) = Some As"
    by (metis "3.hyps"(2) apply_lhs_subst_var_rule length_map)
  show ?case proof(cases "source (Prule \<alpha> As)")
    case (Var x)
    then show ?thesis
      using \<sigma> residual.simps(4)[of \<alpha> As x] args by auto
  next
    case (Fun f ts)
    then show ?thesis
      using \<sigma> residual.simps(5)[of \<alpha> As f] args by auto
  qed
qed simp

context no_var_lhs
begin
lemma deletion_source:
assumes "A \<in> wf_pterm R" "B \<in> wf_pterm R"
    and "A -\<^sub>p B = Some C"
  shows "source C = source A"
  using assms proof(induct A arbitrary:B C)
  case (1 x)
  then show ?case proof (cases B)
    case (1 y)
    then show ?thesis
      by (metis "1.prems"(2) deletion.simps(1) option.distinct(1) option.inject)
  next
    case (3 \<alpha> As)
    with 1 no_var_lhs show ?thesis
      by simp
  qed simp
next
  case (2 As f)
  then show ?case proof(cases B)
    case (Pfun g Bs)
    from 2(3) have f:"f = g"
      unfolding Pfun by (metis deletion.simps(2) not_None_eq)
    from 2(3) have l:"length As = length Bs"
      unfolding Pfun by (metis deletion.simps(2) not_None_eq)
    from 2(3) obtain Cs where cs:"those (map2 (-\<^sub>p) As Bs) = Some Cs"
      unfolding Pfun f using l by fastforce
    with 2(3) have c:"C = Pfun g Cs"
      unfolding Pfun by (simp add: f l)
    from cs l have l_cs:"length Cs = length As"
      using length_those by force
    {fix i assume i:"i < length As"
      with 2(2) have "Bs!i \<in> wf_pterm R"
        by (metis Pfun fun_well_arg l nth_mem)
      moreover from 2(3) i cs have "As!i -\<^sub>p Bs!i = Some (Cs!i)"
        using l those_some2 by fastforce
      ultimately have "source (Cs!i) = source (As!i)"
        using 2(1) using i nth_mem by blast
    }
    then show ?thesis unfolding c f
      using l_cs by (simp add: map_nth_eq_conv)
  qed simp_all
next
  case (3 \<alpha> As)
  from 3(1) no_var_lhs obtain f ts where f:"lhs \<alpha> = Fun f ts"
    by blast
  then show ?case proof(cases B)
    case (Var x)
    have "match (Var x) (to_pterm (lhs \<alpha>)) = None"
      unfolding f by (smt (verit, ccfv_SIG) Term.term.simps(4) match_matches not_Some_eq source.simps(1) source_to_pterm subst_apply_eq_Var)
    with 3(5) show ?thesis
      unfolding Var using f deletion.simps(4) by simp
  next
    case (Pfun g Bs)
    from 3(5) obtain \<sigma> where sigma:"match B (to_pterm (lhs \<alpha>)) = Some \<sigma>"
      unfolding Pfun using deletion.simps(5) by fastforce
    with 3(5) obtain Cs where cs:"those (map2 (-\<^sub>p) As (map \<sigma> (var_rule \<alpha>))) = Some Cs"
      unfolding Pfun by fastforce
    with 3(5) have c:"C = Prule \<alpha> Cs"
      using sigma unfolding Pfun by simp
    from cs 3(2) have l_cs:"length Cs = length As"
      using length_those by force
    {fix x assume "x \<in> vars_term (lhs \<alpha>)"
      then obtain i where i:"i < length (var_rule \<alpha>)" "var_rule \<alpha> !i = x"
        by (metis in_set_conv_nth set_vars_term_list vars_term_list_vars_distinct)
      then have "\<sigma> (var_rule \<alpha> ! i) \<in> wf_pterm R"
        using match_well_def[OF 3(4) sigma] by (metis vars_to_pterm)
      moreover from i cs have "As!i -\<^sub>p \<sigma> (var_rule \<alpha> ! i) = Some (Cs!i)"
        using those_some2 "3.hyps"(2) by fastforce
      ultimately have "source (Cs!i) = source (As!i)"
        using 3(3) using i nth_mem "3.hyps"(2) by force
      then have "source ((\<langle>As\<rangle>\<^sub>\<alpha>) x) = source ((\<langle>Cs\<rangle>\<^sub>\<alpha>) x)" using i
        by (metis "3.hyps"(2) l_cs lhs_subst_var_i)
    }
    then show ?thesis unfolding c using l_cs 3(2) unfolding source.simps
      by (smt (verit, best) apply_lhs_subst_var_rule comp_def in_set_conv_nth length_map nth_map set_remdups set_rev set_vars_term_list term_subst_eq_conv)
  next
    case (Prule \<beta> Bs)
    from 3(5) have alpha:"\<alpha> = \<beta>"
      unfolding Prule by (metis deletion.simps(3) option.distinct(1))
    with 3 have l:"length As = length Bs"
      unfolding Prule using wf_pterm.cases by force
    from 3(5) obtain Cs where cs:"those (map2 (-\<^sub>p) As Bs) = Some Cs"
      unfolding Prule alpha by fastforce
    with 3(5) have c:"C = to_pterm (lhs \<alpha>) \<cdot> \<langle>Cs\<rangle>\<^sub>\<alpha>"
      unfolding Prule alpha by simp
    from cs l have l_cs:"length Cs = length As"
      using length_those by force
    {fix i assume i:"i < length As"
      with 3(4) have "Bs!i \<in> wf_pterm R"
        unfolding Prule by (metis fun_well_arg l nth_mem)
      moreover from i cs have "As!i -\<^sub>p Bs!i = Some (Cs!i)"
        using l those_some2 by fastforce
      ultimately have "source (Cs!i) = source (As!i)"
        using 3(3) using i nth_mem by blast
    }
    then show ?thesis
      unfolding c using l_cs unfolding source.simps using source_apply_subst
      by (metis fun_mk_subst nth_map_conv source.simps(1) source_to_pterm to_pterm_wf_pterm)
  qed
qed
end

subsection\<open>Computations With Single Redexes\<close>
text\<open>When a proof term contains only a single rule symbol, we say it is a *\<open>single redex\<close>.\<close>
definition ll_single_redex :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f, 'v) prule \<Rightarrow> ('f, 'v) pterm"
  where "ll_single_redex s p \<alpha> = (ctxt_of_pos_term p (to_pterm s))\<langle>Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>)))\<rangle>"
text\<open>The @{text ll} in @{const ll_single_redex} stands for *\<open>left-linear\<close>, since this definition 
only makes sense for left-linear rules.\<close>

lemma source_single_redex:
  assumes "p \<in> poss s"
  shows "source (ll_single_redex s p \<alpha>) = (ctxt_of_pos_term p s)\<langle>(lhs \<alpha>) \<cdot> \<langle>map (\<lambda>pi. s|_(p@pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>\<rangle>"
proof-
  have "source (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>)))) = (lhs \<alpha>) \<cdot> \<langle>map (\<lambda>pi. s|_(p@pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>"
    unfolding source.simps using map_nth_eq_conv by fastforce 
  with assms show ?thesis
    unfolding ll_single_redex_def by (metis context_source source_to_pterm to_pterm_ctxt_of_pos_apply_term) 
qed

lemma target_single_redex:
  assumes "p \<in> poss s"
  shows "target (ll_single_redex s p \<alpha>) = (ctxt_of_pos_term p s)\<langle>(rhs \<alpha>) \<cdot> \<langle>map (\<lambda>pi. s|_(p@pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>\<rangle>"
proof-
  have "target (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>)))) = (rhs \<alpha>) \<cdot> \<langle>map (\<lambda>pi. s|_(p@pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>"
    unfolding target.simps by (metis (no_types, lifting) fun_mk_subst map_map target_empty_apply_subst target_to_pterm to_pterm.simps(1) to_pterm_empty to_pterm_subst)
  with assms show ?thesis
    unfolding ll_single_redex_def using target_to_pterm_ctxt to_pterm_ctxt_at_pos by metis
qed

lemma single_redex_rstep:
  assumes "to_rule \<alpha> \<in> R" "p \<in> poss s"
  shows "(source (ll_single_redex s p \<alpha>), target (ll_single_redex s p \<alpha>)) \<in> rstep R"
  using source_single_redex target_single_redex assms by blast

lemma single_redex_neq:
  assumes "(\<alpha>, p) \<noteq> (\<beta>, q)" "p \<in> poss s" "q \<in> poss s"
  shows "ll_single_redex s p \<alpha> \<noteq> ll_single_redex s q \<beta>" 
proof-
  from assms(1) consider "\<alpha> \<noteq> \<beta> \<and> p = q" | "p \<noteq> q"
    by fastforce 
  then show ?thesis proof(cases)
    case 1
    then have "Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>))) \<noteq> Prule \<beta> (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>)))" 
      by simp
    with 1 show ?thesis 
      using assms(2,3) unfolding ll_single_redex_def by simp
  next
    case 2
    show ?thesis proof(cases "p \<in> poss (ll_single_redex s q \<beta>)")
      case True
      from 2 consider (qp) "q <\<^sub>p p" | (par) "q \<bottom> p" | (pq) "p <\<^sub>p q"
        using pos_cases by force 
      then show ?thesis proof(cases)
        case qp
        then obtain i r where r:"q@(i#r) = p"
          using less_pos_def' by (metis neq_Nil_conv)
        with \<open>p \<in> poss (ll_single_redex s q \<beta>)\<close> have "i#r \<in> poss (Prule \<beta> (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>))))"
          unfolding ll_single_redex_def using assms(3) by (metis hole_pos_ctxt_of_pos_term hole_pos_poss_conv poss_list_sound poss_list_to_pterm) 
        then have i:"i < length (var_poss_list (lhs \<beta>))" and "r \<in> poss (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>))!i)"
          by auto
        then have "r \<in> poss (to_pterm (s |_ (q @ (var_poss_list (lhs \<beta>)!i))))" 
          by simp
        then obtain s' where "(Prule \<beta> (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>))))|_(i#r) = to_pterm s'"
          by (metis (no_types, lifting) comp_apply ctxt_supt_id i nth_map poss_list_sound poss_list_to_pterm subt_at.simps(2) subt_at_hole_pos to_pterm_ctxt_of_pos_apply_term) 
        then have "(Prule \<beta> (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>))))|_(i#r) \<noteq> Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>)))"
          using to_pterm.elims by auto          
        then show ?thesis using r assms(2,3) unfolding ll_single_redex_def
          by (smt (verit, del_insts) hole_pos_ctxt_of_pos_term hole_pos_poss p_in_poss_to_pterm replace_at_subt_at subt_at_append) 
      next
        case par
        then have "ll_single_redex s q \<beta> |_ p = to_pterm s |_p" 
          using True unfolding ll_single_redex_def
          by (simp add: assms(2,3) p_in_poss_to_pterm parallel_replace_at_subt_at) 
        then show ?thesis
          using assms(2,3) unfolding ll_single_redex_def
          by (metis ctxt_supt_id hole_pos_ctxt_of_pos_term is_empty_step.simps(3) p_in_poss_to_pterm subt_at_hole_pos to_pterm_ctxt_of_pos_apply_term to_pterm_empty)
      next 
        case pq
        then obtain r where r:"q = p@r" "r \<noteq> []"
          using less_pos_def' by blast 
        then have *:"ll_single_redex s q \<beta> |_ p = (ctxt_of_pos_term r (to_pterm (s|_p)))\<langle>Prule \<beta> (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>)))\<rangle>" 
          using True unfolding ll_single_redex_def r by (metis (no_types, lifting) assms(2) ctxt_apply_subt_at ctxt_supt_id p_in_poss_to_pterm replace_at_subt_at to_pterm_ctxt_of_pos_apply_term)
        from r(2) assms(3) obtain f ts i r' where f:"s|_p = Fun f ts" and r':"r = i#r'"
          unfolding r by (metis args_poss neq_Nil_conv poss_append_poss) 
        have "ll_single_redex s q \<beta> |_ p \<noteq> Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>)))"
          unfolding * unfolding ll_single_redex_def f to_pterm.simps r' ctxt_of_pos_term.simps intp_actxt.simps by simp
        then show ?thesis 
          using assms(2) unfolding ll_single_redex_def
          by (metis p_in_poss_to_pterm replace_at_subt_at) 
      qed
    next
      case False
      then show ?thesis unfolding ll_single_redex_def using assms(2)
        by (metis hole_pos_ctxt_of_pos_term hole_pos_poss p_in_poss_to_pterm)
    qed
  qed
qed

context left_lin_wf_trs
begin
lemma rstep_exists_single_redex:
  assumes "(s, t) \<in> rstep R" 
  shows "\<exists> A p \<alpha>. A = (ll_single_redex s p \<alpha>) \<and> source A = s \<and> target A = t  \<and> to_rule \<alpha> \<in> R \<and> p \<in> poss s"
proof-
  from assms obtain C \<sigma> l r where lr:"(l, r) \<in> R" and s:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t:" t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    by blast
  from s obtain p where p:"p \<in> poss s" and C:"C = ctxt_of_pos_term p s"
    using hole_pos_poss by fastforce 
  let ?subst="\<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list l)\<rangle>\<^sub>(l \<rightarrow>r)" 
  {fix x assume "x \<in> vars_term l"
    then obtain i where i:"i < length (vars_term_list l)" "vars_term_list l ! i = x"
      by (metis in_set_idx set_vars_term_list) 
    with left_lin lr have var_l:"vars_distinct l ! i = x" 
      using linear_term_var_vars_term_list left_linear_trs_def by fastforce
    let ?p="var_poss_list l ! i" 
    from i have "l |_ ?p = Var x" using vars_term_list_var_poss_list by auto 
    moreover have "l \<cdot> \<sigma> = s|_p" using s C p replace_at_subt_at by fastforce 
    ultimately have left:"\<sigma> x = (s |_p) |_ ?p"
      by (metis eval_term.simps(1) i(1) length_var_poss_list nth_mem subt_at_subst var_poss_imp_poss var_poss_list_sound) 
    from i have "map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list l) !i = (s |_p) |_ ?p"
      by (simp add: length_var_poss_list p) 
    with left var_l have "\<sigma> x = ?subst x" unfolding mk_subst_def prule.sel
      by (smt (verit, best) case_prodE comp_apply distinct_rev i(1) left_lin left_linear_trs_def length_map length_var_poss_list linear_term_var_vars_term_list lr mk_subst_def mk_subst_distinct prod.sel(1) remdups_id_iff_distinct rev_rev_ident)
  }note subst=this
  then have "(ctxt_of_pos_term p s)\<langle>l \<cdot> \<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list l)\<rangle>\<^sub>(l\<rightarrow>r)\<rangle> = C\<langle>l \<cdot> \<sigma>\<rangle>" 
    using C by (simp add: eval_same_vars) 
  then have "source (ll_single_redex s p (Rule l r)) = s" 
    using source_single_redex[OF p] s by auto
  moreover have "target (ll_single_redex s p (l \<rightarrow> r)) = t" 
    using subst varcond lr target_single_redex[OF p] eval_same_vars_cong unfolding t C
    by (smt (verit) case_prodD prule.sel(1) prule.sel(2) vars_term_subset_subst_eq)
  ultimately show ?thesis using lr p by fastforce
qed
end

lemma single_redex_wf_pterm:
  assumes "to_rule \<alpha> \<in> R" and lin:"linear_term (lhs \<alpha>)"
    and p:"p \<in> poss s"
  shows "ll_single_redex s p \<alpha> \<in> wf_pterm R"
proof-
  from lin have l:"length (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>))) = length (var_rule \<alpha>)"
    using length_var_poss_list linear_term_var_vars_term_list by fastforce 
  have "Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>))) \<in> wf_pterm R"  
    using wf_pterm.intros(3)[OF assms(1) l] to_pterm_wf_pterm by force 
  then show ?thesis unfolding ll_single_redex_def 
    using ctxt_wf_pterm p to_pterm_wf_pterm by (metis p_in_poss_to_pterm)
qed


text \<open>Interaction of a single redex @{term \<Delta>}, contained in @{term A} with the proof term  @{term A}.\<close>
locale single_redex = left_lin_no_var_lhs + 
  fixes A \<Delta> p q \<alpha>
  assumes a_well:"A \<in> wf_pterm R"
    and p:"p \<in> poss (source A)" and q:"q \<in> poss A"
    and pq:"ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term q A)"
    and delta:"\<Delta> = ll_single_redex (source A) p \<alpha>"
    and aq:"A|_q = Prule \<alpha> (map (\<lambda>i. A|_(q@[i])) [0..<length (var_rule \<alpha>)])"
begin

interpretation residual_op:op_proof_term "R" "residual"
  using op_proof_term.intro[OF left_lin_no_var_lhs_axioms] op_proof_term_axioms.intro[of R residual] res_empty2 by force

interpretation deletion_op:op_proof_term "R" "deletion"
  using op_proof_term.intro[OF left_lin_no_var_lhs_axioms] op_proof_term_axioms.intro[of R deletion] del_empty  by force

abbreviation "As \<equiv> (map (\<lambda>i. A|_(q@[i])) [0..<length (var_rule \<alpha>)])"

lemma length_as:"length As = length (var_rule \<alpha>)"
  by simp

lemma as_well:"\<forall>i < length As. As!i \<in> wf_pterm R"
  using subt_at_is_wf_pterm a_well aq q
  by (metis fun_well_arg nth_mem)

lemma a:"A = (ctxt_of_pos_term q A)\<langle>Prule \<alpha> As\<rangle>"
  using aq by (simp add: q replace_at_ident)

lemma rule_in_TRS: "to_rule \<alpha> \<in> R"
proof-
   from a_well a q have "Prule \<alpha> As \<in> wf_pterm R"
    by (metis subt_at_ctxt_of_pos_term subt_at_is_wf_pterm)
  then show ?thesis
    using wf_pterm.cases by force
qed

lemma lin_lhs:"linear_term (lhs \<alpha>)"
  using rule_in_TRS left_lin left_linear_trs_def by fastforce

lemma source_at_pq:"source (A|_q) = (source A)|_p"
proof-
  from a_well q have "(ctxt_of_pos_term q A) \<in> wf_pterm_ctxt R"
    by (simp add: ctxt_of_pos_term_well)
  then have "source A = (source_ctxt (ctxt_of_pos_term q A)) \<langle>source (A|_q)\<rangle>"
    using source_ctxt_apply_term q by (metis ctxt_supt_id)
  moreover from p have "source A = (ctxt_of_pos_term p (source A)) \<langle>(source A)|_p\<rangle>"
    by (simp add: replace_at_ident)
  ultimately show ?thesis
    using pq p q by simp
qed

lemma single_redex_pterm:
  shows "\<Delta> = (ctxt_of_pos_term p (to_pterm (source A)))\<langle>Prule \<alpha> (map (to_pterm \<circ> source) As)\<rangle>"
proof-
  from lin_lhs have l2:"length (var_poss_list (lhs \<alpha>)) = length (var_rule \<alpha>)"
      by (metis length_var_poss_list linear_term_var_vars_term_list)
  {fix i assume i:"i < length (var_poss_list (lhs \<alpha>))"
    let ?pi="var_poss_list (lhs \<alpha>)!i"
    from i have *:"(lhs \<alpha>)|_?pi = Var ((var_rule \<alpha>)!i)"
      using lin_lhs by (metis linear_term_var_vars_term_list length_var_poss_list vars_term_list_var_poss_list)
    from source_at_pq have "source A |_ (p @ ?pi) = source (Prule \<alpha> As)|_?pi"
      by (metis a p q subt_at_append subt_at_ctxt_of_pos_term)
    also have "... = Var ((var_rule \<alpha>)!i) \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>"
      unfolding source.simps using subt_at_subst * i nth_mem var_poss_imp_poss by fastforce
    also have "... = source (As!i)"
      unfolding eval_term.simps using i lhs_subst_var_i length_as l2 by (metis (no_types, lifting) length_map nth_map)
    finally have "source A |_ (p @ ?pi) = source (As!i)" .
  }
  with l2 show ?thesis
    unfolding delta ll_single_redex_def by (simp add: nth_map_conv)
qed

lemma delta_trs_wf_pterm:
 shows "\<Delta> \<in> wf_pterm R"
proof-
  have well2:"Prule \<alpha> (map (to_pterm \<circ> source) As) \<in> wf_pterm R" proof-
    from a_well a q have "Prule \<alpha> As \<in> wf_pterm R"
      by (metis subt_at_ctxt_of_pos_term subt_at_is_wf_pterm)
    then have "to_rule \<alpha> \<in> R"
      using wf_pterm.cases by auto
    then show ?thesis
      by (simp add: wf_pterm.intros(3))
  qed
  show ?thesis unfolding single_redex_pterm
    using p well2 by (simp add: p_in_poss_to_pterm ctxt_wf_pterm)
qed

lemma source_delta: "source \<Delta> = source A"
proof-
  have src:"source (Prule \<alpha> (map (to_pterm \<circ> source) As)) = source (Prule \<alpha> As)"
    unfolding source.simps by (metis (no_types, lifting) comp_eq_dest_lhs list.map_comp list.map_cong0 source_to_pterm)
  moreover have "source_ctxt (ctxt_of_pos_term p (to_pterm (source A))) = source_ctxt (ctxt_of_pos_term q A)"
    using pq by (metis p source_to_pterm_ctxt' to_pterm_ctxt_at_pos)
  ultimately show ?thesis unfolding single_redex_pterm
    using p p q by (metis aq p_in_poss_to_pterm pq replace_at_ident source_at_pq source_ctxt_apply_term to_pterm_trs_ctxt)
qed

lemma residual:
  shows "A re \<Delta> = Some ((ctxt_of_pos_term q A)\<langle>(to_pterm (rhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>\<rangle>)"
proof-
  have l:"length (map2 (re) As (map (to_pterm \<circ> source) As)) = length As"
    by simp
  {fix i assume i:"i < length As"
    with as_well have "As!i re (to_pterm \<circ> source) (As!i) = Some (As!i)"
      by (metis (no_types, lifting) o_apply res_empty2)
    then have "map2 (re) As (map (to_pterm \<circ> source) As) ! i = Some (As ! i)"
      using i by force
  }
  then have *:"those (map2 (re) As (map (to_pterm \<circ> source) As)) = Some As"
    using those_some[OF l] using l by presburger
  then have "(Prule \<alpha> As) re (Prule \<alpha> (map (to_pterm \<circ> source) As)) = Some ((to_pterm (rhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>)"
     using residual.simps(3)[of \<alpha> As \<alpha> "(map (to_pterm \<circ> source) As)"] by simp
  moreover from single_redex_pterm have "\<Delta> = (to_pterm_ctxt (source_ctxt (ctxt_of_pos_term q A)))\<langle>(Prule \<alpha> (map (to_pterm \<circ> source) As))\<rangle>"
    unfolding delta ll_single_redex_def pq[symmetric] by (simp add: p to_pterm_ctxt_at_pos)
  ultimately show ?thesis
    using a residual_op.apply_f_ctxt by (metis a_well ctxt_of_pos_term_well q)
qed

lemma residual_well:
 "the (A re \<Delta>) \<in> wf_pterm R"
  using a_well by (metis delta_trs_wf_pterm option.sel residual residual_well_defined)

lemma target_residual:"target (the (A re \<Delta>)) = target A"
  apply(subst (2) a)
  unfolding residual option.sel
  apply(subst (1 2) context_target)
  by (metis fun_mk_subst target.simps(1) target.simps(3) target_empty_apply_subst target_to_pterm to_pterm_empty)


lemma deletion:
  shows "A -\<^sub>p \<Delta> = Some ((ctxt_of_pos_term q A)\<langle>(to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>\<rangle>)"
proof-
   have l:"length (map2 (-\<^sub>p) As (map (to_pterm \<circ> source) As)) = length As"
    by simp
  {fix i assume i:"i < length As"
    with as_well have "As!i -\<^sub>p (to_pterm \<circ> source) (As!i) = Some (As!i)"
      by (metis (no_types, lifting) o_apply del_empty)
    then have "map2 (-\<^sub>p) As (map (to_pterm \<circ> source) As) ! i = Some (As ! i)"
      using i by force
  }
  then have *:"those (map2 (-\<^sub>p) As (map (to_pterm \<circ> source) As)) = Some As"
    using those_some[OF l] using l by presburger
  then have "(Prule \<alpha> As) -\<^sub>p (Prule \<alpha> (map (to_pterm \<circ> source) As)) = Some ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>)"
     using deletion.simps(3)[of \<alpha> As \<alpha> "(map (to_pterm \<circ> source) As)"] by simp
  moreover from single_redex_pterm have "\<Delta> = (to_pterm_ctxt (source_ctxt (ctxt_of_pos_term q A)))\<langle>(Prule \<alpha> (map (to_pterm \<circ> source) As))\<rangle>"
    unfolding delta ll_single_redex_def pq[symmetric] by (simp add: p to_pterm_ctxt_at_pos)
  ultimately show ?thesis
    using a deletion_op.apply_f_ctxt by (metis a_well ctxt_of_pos_term_well q)
qed

lemma deletion_well:
  shows "the (A -\<^sub>p \<Delta>) \<in> wf_pterm R"
proof-
  have "\<forall>a \<in> set As. a \<in> wf_pterm R"
    by (metis a a_well fun_well_arg q subt_at_ctxt_of_pos_term subt_at_is_wf_pterm)
  then have "to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha> \<in> wf_pterm R"
    by (meson lhs_subst_well_def nth_mem to_pterm_wf_pterm)
  then show ?thesis unfolding deletion option.sel
    by (simp add: a_well ctxt_wf_pterm q)
qed

end

locale single_redex' = left_lin_wf_trs + 
  fixes A \<Delta> p q \<alpha> \<sigma>
  assumes a_well:"A \<in> wf_pterm R" and rule_in_TRS:"to_rule \<alpha> \<in> R"
    and p:"p \<in> poss (source A)" and q:"q \<in> poss A"
    and pq:"ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term q A)"
    and delta:"\<Delta> = ll_single_redex (source A) p \<alpha>"
    and aq:"A|_q = (to_pterm (lhs \<alpha>)) \<cdot> \<sigma>"
begin

interpretation residual_op:op_proof_term "R" "residual" proof-
  have *:"left_lin_no_var_lhs R"
    by (simp add: left_lin_axioms left_lin_no_var_lhs.intro no_var_lhs_axioms)
  then show "op_proof_term R (re)"  
    using op_proof_term.intro[OF *] op_proof_term_axioms.intro[of R residual] res_empty2 by force
qed

lemma a:"A = (ctxt_of_pos_term q A)\<langle>(to_pterm (lhs \<alpha>)) \<cdot> \<sigma>\<rangle>"
  using aq by (simp add: q replace_at_ident)

lemma lin_lhs:"linear_term (lhs \<alpha>)"
  using rule_in_TRS left_lin left_linear_trs_def by fastforce

lemma is_fun_lhs:"is_Fun (lhs \<alpha>)"
  using rule_in_TRS using no_var_lhs by blast

abbreviation "As \<equiv> map \<sigma> (var_rule \<alpha>)"

lemma lhs_subst: "(to_pterm (lhs \<alpha>)) \<cdot> \<sigma> = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>"
proof-
  {fix x assume "x \<in> vars_term (to_pterm (lhs \<alpha>))"
    then obtain i where "x = var_rule \<alpha>!i" and "i < length (var_rule \<alpha>)"
      by (metis in_set_idx set_vars_term_list vars_term_list_vars_distinct vars_to_pterm)
    then have "\<sigma> x = (\<langle>As\<rangle>\<^sub>\<alpha>) x"
      by (metis (mono_tags, lifting) apply_lhs_subst_var_rule length_map nth_map)
  }
  then show ?thesis
    using term_subst_eq_conv by blast
qed

lemma rhs_subst: "(to_pterm (rhs \<alpha>)) \<cdot> \<sigma> = (to_pterm (rhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>"
proof-
  {fix x assume "x \<in> vars_term (to_pterm (rhs \<alpha>))"
    then have "x \<in> vars_term (to_pterm (lhs \<alpha>))"
      using no_var_lhs varcond rule_in_TRS set_vars_term_list subsetD vars_to_pterm by (metis case_prodD)
    then obtain i where "x = var_rule \<alpha>!i" and "i < length (var_rule \<alpha>)"
      by (metis in_set_idx set_vars_term_list vars_term_list_vars_distinct vars_to_pterm)
    then have "\<sigma> x = (\<langle>As\<rangle>\<^sub>\<alpha>) x"
      by (metis (mono_tags, lifting) apply_lhs_subst_var_rule length_map nth_map)
  }
  then show ?thesis
    using term_subst_eq_conv by blast
qed

lemma as_well:"\<forall>i < length As. As!i \<in> wf_pterm R"
  using a_well aq by (metis length_map lhs_subst lhs_subst_args_wf_pterm nth_mem q subt_at_is_wf_pterm)

lemma source_at_pq:"source (A|_q) = (source A)|_p"
proof-
  from a_well q have "(ctxt_of_pos_term q A) \<in> wf_pterm_ctxt R"
    by (simp add: ctxt_of_pos_term_well)
  then have "source A = (source_ctxt (ctxt_of_pos_term q A)) \<langle>source (A|_q)\<rangle>"
    using source_ctxt_apply_term q by (metis ctxt_supt_id)
  moreover from p have "source A = (ctxt_of_pos_term p (source A)) \<langle>(source A)|_p\<rangle>"
    by (simp add: replace_at_ident)
  ultimately show ?thesis
    using pq p q by simp
qed

lemma single_redex_pterm:
  shows "\<Delta> = (ctxt_of_pos_term p (to_pterm (source A)))\<langle>Prule \<alpha> (map (to_pterm \<circ> source) As)\<rangle>"
proof-
  from lin_lhs have l2:"length (var_poss_list (lhs \<alpha>)) = length (var_rule \<alpha>)"
      by (metis length_var_poss_list linear_term_var_vars_term_list)
  {fix i assume i:"i < length (var_poss_list (lhs \<alpha>))"
    let ?pi="var_poss_list (lhs \<alpha>)!i"
    from i have *:"(lhs \<alpha>)|_?pi = Var ((var_rule \<alpha>)!i)"
      using lin_lhs by (metis linear_term_var_vars_term_list length_var_poss_list vars_term_list_var_poss_list)
    from source_at_pq have "source A |_ (p @ ?pi) = source ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>)|_?pi"
      using lhs_subst by (metis a p q subt_at_append subt_at_ctxt_of_pos_term)
    also have "... = Var ((var_rule \<alpha>)!i) \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>"
      using subt_at_subst *
      by (metis (no_types, lifting) fun_mk_subst i nth_mem source.simps(1) source_apply_subst source_to_pterm to_pterm_wf_pterm var_poss_imp_poss var_poss_list_sound)
    also have "... = source (As!i)"
      unfolding eval_term.simps using i lhs_subst_var_i l2 by (metis (no_types, lifting) length_map nth_map)
    finally have "source A |_ (p @ ?pi) = source (As!i)" .
  }
  with l2 show ?thesis
    unfolding delta ll_single_redex_def by (simp add: map_eq_conv')
qed

lemma residual:
  shows "A re \<Delta> = Some ((ctxt_of_pos_term q A)\<langle>(to_pterm (rhs \<alpha>)) \<cdot> \<sigma>\<rangle>)"
proof-
  have l:"length (map2 (re) As (map (to_pterm \<circ> source) As)) = length As"
    by simp
  {fix i assume i:"i < length As"
    with as_well have "As!i re (to_pterm \<circ> source) (As!i) = Some (As!i)"
      by (metis comp_apply res_empty2)
    then have "map2 (re) As (map (to_pterm \<circ> source) As) ! i = Some (As ! i)"
      using i by force
  }
  then have *:"those (map2 (re) As (map (to_pterm \<circ> source) As)) = Some As"
    using those_some[OF l] using l by presburger
  from is_fun_lhs obtain f As' where f:"(to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) = Pfun f As'"
    by fastforce
  then have match:"match (Pfun f As') (to_pterm (lhs \<alpha>)) = Some (\<langle>As\<rangle>\<^sub>\<alpha>)"
    by (metis lhs_subst_trivial)
  have map:"map (\<langle>As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>) = As"
    using apply_lhs_subst_var_rule length_map by blast
  have "((to_pterm (lhs \<alpha>)) \<cdot> \<sigma>) re (Prule \<alpha> (map (to_pterm \<circ> source) As)) = Some ((to_pterm (rhs \<alpha>)) \<cdot> \<sigma>)"
    unfolding rhs_subst lhs_subst using residual.simps(7)[of f As' \<alpha> "(map (to_pterm \<circ> source) As)"]
    unfolding match f using * map by (metis option.simps(5))
  moreover from single_redex_pterm have "\<Delta> = (to_pterm_ctxt (source_ctxt (ctxt_of_pos_term q A)))\<langle>(Prule \<alpha> (map (to_pterm \<circ> source) As))\<rangle>"
    unfolding delta ll_single_redex_def pq[symmetric] by (simp add: p to_pterm_ctxt_at_pos)
  ultimately show ?thesis
    using a residual_op.apply_f_ctxt by (metis a_well ctxt_of_pos_term_well q) 
qed

end

end