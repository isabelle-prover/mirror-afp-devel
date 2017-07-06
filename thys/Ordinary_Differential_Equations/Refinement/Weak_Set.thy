theory Weak_Set
imports
  "Autoref_Misc"
begin

subsection \<open>generic things\<close>

lemma nres_rel_trans1: "a \<le> b \<Longrightarrow> (b, i) \<in> \<langle>R\<rangle>nres_rel \<Longrightarrow> (a, i) \<in> \<langle>R\<rangle>nres_rel"
  apply (rule nres_relI)
  using nres_relD order_trans by blast

lemma nres_rel_trans2: "a \<le> b \<Longrightarrow> (i, a) \<in> \<langle>R\<rangle>nres_rel \<Longrightarrow> (i, b) \<in> \<langle>R\<rangle>nres_rel"
  apply (rule nres_relI)
  using nres_relD ref_two_step by blast

lemma param_Union[param]: "(Union, Union) \<in> \<langle>\<langle>R\<rangle>set_rel\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel"
  by (fastforce simp: set_rel_def)

subsection \<open>relation\<close>

definition list_wset_rel_internal_def: "list_wset_rel R = br set top O \<langle>R\<rangle>set_rel"

lemma list_wset_rel_def: "\<langle>R\<rangle>list_wset_rel = br set top O \<langle>R\<rangle>set_rel"
  unfolding list_wset_rel_internal_def[abs_def] by (simp add: relAPP_def)

lemma list_set_rel_sv[relator_props]:
  "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>list_wset_rel)"
  unfolding list_wset_rel_def
  by tagged_solver

lemmas [autoref_rel_intf] = REL_INTFI[of list_wset_rel i_set]


subsection \<open>operations\<close>

definition "op_set_ndelete x X = RES {X - {x}, X}"

lemma op_set_ndelete_spec: "op_set_ndelete x X = SPEC(\<lambda>R. R = X - {x} \<or> R = X)"
  by (auto simp: op_set_ndelete_def)


subsection \<open>implementations\<close>

lemma list_wset_autoref_empty[autoref_rules]:
  "([],{})\<in>\<langle>R\<rangle>list_wset_rel"
  by (auto simp: list_wset_rel_def br_def relcompI)

context begin interpretation autoref_syn .

lemma mem_set_list_relE1:
  assumes "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  assumes "x \<in> set xs"
  obtains y where "y \<in> set ys" "(x, y) \<in> R"
  by (metis (no_types, lifting) assms in_set_conv_decomp list_relE3 list_rel_append1)

lemma mem_set_list_relE2:
  assumes "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  assumes "y \<in> set ys"
  obtains x where "x \<in> set xs" "(x, y) \<in> R"
  by (metis assms in_set_conv_decomp list_relE4 list_rel_append2)

lemma in_domain_list_relE:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<in> Domain R"
  obtains ys where "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
proof -
  obtain y where y: "\<And>x. x \<in> set xs \<Longrightarrow> (x, y x) \<in> R"
    using assms by (metis for_in_RI)
  have "(xs, map y xs) \<in> \<langle>R\<rangle>list_rel"
    by (auto simp: list_rel_def list_all2_iff in_set_zip intro!: y)
  then show ?thesis ..
qed

lemma list_rel_comp_list_wset_rel:
  assumes "single_valued R"
  shows "\<langle>R\<rangle>list_rel O \<langle>S\<rangle>list_wset_rel = \<langle>R O S\<rangle>list_wset_rel"
proof (safe, goal_cases)
  case hyps: (1 a b x y z)
  show ?case
    unfolding list_wset_rel_def
  proof (rule relcompI[where b = "set x"])
    show "(set x, z) \<in> \<langle>R O S\<rangle>set_rel"
      unfolding set_rel_def
      using hyps 
      apply (clarsimp simp: list_wset_rel_def br_def set_rel_def)  
      by (meson mem_set_list_relE1 mem_set_list_relE2 relcomp.relcompI)    
  qed (simp add: br_def)
next
  case hyps: (2 xs zs)
  then have "\<And>x. x \<in> set xs \<Longrightarrow> x \<in> Domain R"
    by (auto simp: list_wset_rel_def br_def set_rel_def)
  from in_domain_list_relE[OF this]
  obtain ys where ys: "(xs, ys) \<in> \<langle>R\<rangle>list_rel" .
  have set_rel: "(set ys, zs) \<in> \<langle>S\<rangle>set_rel"
    unfolding list_wset_rel_def set_rel_def
    using hyps 
    apply (clarsimp simp: list_wset_rel_def br_def set_rel_def)  
    apply safe
    apply (metis (full_types) assms mem_set_list_relE2 relcomp.cases single_valued_def ys)  
    by (metis mem_set_list_relE1 relcompEpair single_valuedD ys assms)
  from ys show ?case
    by (rule relcompI)
      (auto simp: list_wset_rel_def br_def intro!: relcompI[where b="set ys"] set_rel)
qed

lemma list_set_autoref_insert[autoref_rules]:
  assumes "PREFER single_valued R"
  shows "(Cons,Set.insert) \<in> R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
proof -
  have 1: "(Cons, Cons) \<in> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    by parametricity
  moreover have 2: "(Cons, Set.insert) \<in> Id \<rightarrow> \<langle>Id\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel"
    by (auto simp: list_wset_rel_def br_def)
  ultimately have "(Cons, Set.insert) \<in> (R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel) O (Id \<rightarrow> \<langle>Id\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel)"
    by auto
  also have "\<dots> \<subseteq> R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
    apply (rule order_trans[OF fun_rel_comp_dist])
    apply (rule fun_rel_mono)
    subgoal by simp
    subgoal
      apply (rule order_trans[OF fun_rel_comp_dist])
      by (rule fun_rel_mono)
        (simp_all add: list_rel_comp_list_wset_rel assms[unfolded autoref_tag_defs])
    done
  finally show ?thesis .
qed

lemma op_set_ndelete_wset_refine[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "(x, y) \<in> R" "(xs, Y) \<in> \<langle>R\<rangle>list_wset_rel"
  shows "(nres_of (dRETURN (List.remove1 x xs)),op_set_ndelete $ y $ Y) \<in> \<langle>\<langle>R\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding op_set_ndelete_spec autoref_tag_defs
  apply (safe intro!: nres_relI SPEC_refine det_SPEC elim!: relcompE)
  using assms(3)[unfolded list_wset_rel_def]
  apply (rule relcompE)
proof (cases "x \<in> set (remove1 x xs)", goal_cases)
  case (1 u v w)
  then have "set (remove1 x xs) = set xs"
    by (metis in_set_remove1 set_remove1_subset subsetI subset_antisym)
  then show ?case
    using 1
    by (auto intro!: exI[where x=w] simp: list_wset_rel_def br_def intro!: relcompI)
next
  case (2 u v w)
  then have r: "set (remove1 x u) = set xs - {x}"
    using in_set_remove1[of _ x xs]
    by (auto simp del: in_set_remove1 simp add: br_def)
      
  from assms old_set_rel_sv_eq[of R] have [simp]: "\<langle>R\<rangle>set_rel = \<langle>R\<rangle>old_set_rel" by simp    
      
  show ?case
    using 2 \<open>(x, y) \<in> R\<close> assms
    by (auto simp: relcomp_unfold r old_set_rel_def single_valued_def br_def list_wset_rel_def)
    
qed


subsection \<open>pick\<close>

lemma
  pick_wset_refine[autoref_rules]:
  assumes "SIDE_PRECOND (X \<noteq> {})"
  assumes "(XS, X) \<in> \<langle>A\<rangle>list_wset_rel"
  shows "(nres_of (dRETURN (hd XS)), op_set_pick $ X) \<in> \<langle>A\<rangle>nres_rel"
  unfolding op_set_pick_def[abs_def] autoref_tag_defs
  apply (rule nres_relI)
  apply (rule SPEC_refine)
  apply (rule det_SPEC)
  using assms
  apply (auto simp: Let_def list_wset_rel_def set_rel_def br_def)
  by (metis (full_types) DomainE ImageI empty_iff insertCI list.exhaust list.sel(1)
      list.set(1) list.set(2) subsetCE)


subsection \<open>pick remove\<close>

definition "op_set_npick_remove X = SPEC (\<lambda>(x, X'). x \<in> X \<and> (X' = X - {x} \<or> X' = X))"
lemma op_set_pick_remove_pat[autoref_op_pat]:
  "SPEC (\<lambda>(x, X'). x \<in> X \<and> (X' = X - {x} \<or> X' = X)) \<equiv> op_set_npick_remove $ X"
  "SPEC (\<lambda>(x, X'). x \<in> X \<and> (X' = X \<or> X' = X - {x})) \<equiv> op_set_npick_remove $ X"
  "do { x \<leftarrow> SPEC (\<lambda>x. x \<in> X); X' \<leftarrow> op_set_ndelete x X; f x X' } \<equiv> do { (x, X') \<leftarrow> op_set_npick_remove X; f x X'}"
  by (auto simp: op_set_npick_remove_def op_set_ndelete_def pw_eq_iff refine_pw_simps intro!: eq_reflection)

lemma op_set_npick_remove_def':
  "X \<noteq> {} \<Longrightarrow> op_set_npick_remove X =
    do { ASSERT (X \<noteq> {}); x \<leftarrow> op_set_pick X; X' \<leftarrow> op_set_ndelete x X; RETURN (x, X')}"
  by (auto simp: op_set_npick_remove_def op_set_ndelete_def pw_eq_iff refine_pw_simps )

lemma aux: "(a, c) \<in> R \<Longrightarrow> a = b \<Longrightarrow> (b, c) \<in> R"
  by simp

lemma
  op_set_npick_remove_refine[autoref_rules]:
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  assumes [autoref_rules]: "(XS, X) \<in> \<langle>A\<rangle>list_wset_rel"
  shows "(RETURN (hd XS, tl XS), op_set_npick_remove $ X) \<in> \<langle>A \<times>\<^sub>r \<langle>A\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs op_set_npick_remove_def'[OF assms(2)[unfolded autoref_tag_defs]]
  apply (subst remove1_tl[symmetric])
  subgoal  using assms by (force simp: list_wset_rel_def br_def set_rel_def)
  subgoal
    apply (rule aux)
     apply (autoref)
    apply (simp )
    done
  done

subsection \<open>emptiness check\<close>

lemma isEmpty_wset_refine[autoref_rules]:
  assumes "(xs, X) \<in> \<langle>A\<rangle>list_wset_rel"
  shows "(xs = [], op_set_isEmpty $ X) \<in> bool_rel"
  using assms
  by (auto simp: list_wset_rel_def br_def set_rel_def)


subsection \<open>union\<close>

lemma union_wset_refine[autoref_rules]:
  "(append, op \<union>) \<in> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  by (auto 0 3 simp: list_wset_rel_def set_rel_def relcomp_unfold br_def)


subsection \<open>of list\<close>

lemma set_wset_refine[autoref_rules]:
  assumes "PREFER single_valued R"
  shows "((\<lambda>x. x), set) \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  apply (rule fun_relI)
  unfolding list_wset_rel_def
  apply (rule_tac b = "set a" in relcompI)
  apply (simp add: br_def)
  using assms[THEN PREFER_sv_D]
  by parametricity


subsection \<open>filter set\<close>

lemma bCollect_param: "((\<lambda>y a. {x \<in> y. a x}), (\<lambda>z a'. {x \<in> z. a' x})) \<in> \<langle>R\<rangle>set_rel \<rightarrow> (R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>set_rel"
  unfolding set_rel_def
  apply safe
  subgoal using tagged_fun_relD_both by fastforce
  subgoal using tagged_fun_relD_both by fastforce
  done

lemma op_set_filter_list_wset_refine[autoref_rules]:
  "(filter, op_set_filter) \<in> (R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  by (force simp: list_wset_rel_def br_def bCollect_param[param_fo])


subsection \<open>bound on cardinality\<close>

definition "op_set_wcard X = SPEC (\<lambda>c. card X \<le> c)"

lemma op_set_wcard_refine[autoref_rules]: "PREFER single_valued R \<Longrightarrow> ((\<lambda>xs. RETURN (length xs)), op_set_wcard) \<in> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
proof (auto simp: list_wset_rel_def nres_rel_def br_def op_set_wcard_def, goal_cases)
  case (1 x z)
  thus ?case
    apply (induction x arbitrary: z) 
    apply (auto simp: old_set_rel_sv_eq[symmetric] old_set_rel_def Image_insert intro!: card_insert_le_m1)  
    done  
qed

lemmas op_set_wcard_spec[refine_vcg] = op_set_wcard_def[THEN eq_refl, THEN order_trans]

subsection \<open>big union\<close>

lemma Union_list_wset_rel[autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(concat, Union) \<in> \<langle>\<langle>A\<rangle>list_wset_rel\<rangle>list_wset_rel \<rightarrow> \<langle>A\<rangle>list_wset_rel"
proof -
  have "(concat, concat) \<in> \<langle>\<langle>A\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" (is "_ \<in> ?A")
    by parametricity
  moreover have "(concat, Union) \<in> \<langle>\<langle>Id\<rangle>list_wset_rel\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel" (is "_ \<in> ?B")
    by (auto simp: list_wset_rel_def br_def relcomp_unfold set_rel_def; meson)
  ultimately have "(concat, Union) \<in> ?A O ?B"
    by auto
  also note fun_rel_comp_dist
  finally show ?thesis
    using assms
    by (simp add: list_rel_comp_list_wset_rel list_rel_sv_iff)
qed


subsection \<open>image\<close>

lemma image_list_wset_rel[autoref_rules]:
  assumes "PREFER single_valued B"
  shows "(map, op `) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>B\<rangle>list_wset_rel"
  unfolding list_wset_rel_def relcomp_unfold
proof safe
  show "(a, a') \<in> A \<rightarrow> B \<Longrightarrow> (aa, y) \<in> br set top \<Longrightarrow> (y, a'a) \<in> \<langle>A\<rangle>set_rel \<Longrightarrow>
       \<exists>y. (map a aa, y) \<in> br set top \<and> (y, a' ` a'a) \<in> \<langle>B\<rangle>set_rel" for a a' aa a'a y
    apply (safe intro!: exI[where x = "a ` y"])
    subgoal by (rule brI) (auto simp: br_def)
    subgoal
      unfolding set_rel_def
      apply safe
      subgoal by (fastforce simp: fun_rel_def split: prod.split)
      subgoal using assms
        by (auto simp: fun_rel_def br_def)
          (metis (no_types, lifting) Domain.cases ImageI image_eqI single_valuedD old.prod.case subsetCE)
      done
    done
qed

subsection \<open>Ball\<close>

lemma Ball_list_wset_rel[autoref_rules]:
  "((\<lambda>xs p. foldli xs (\<lambda>x. x) (\<lambda>a _. p a) True), Ball) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> (A \<rightarrow> bool_rel) \<rightarrow> bool_rel"
proof -
  have "(\<lambda>xs. Ball (set xs), Ball) \<in> {(x, z). (set x, z) \<in> \<langle>A\<rangle>set_rel} \<rightarrow> (A \<rightarrow> bool_rel) \<rightarrow> bool_rel"
    apply (rule fun_relI)
    unfolding mem_Collect_eq split_beta' fst_conv snd_conv
    by parametricity
  then show ?thesis
    by (simp add: relcomp_unfold br_def foldli_ball_aux list_wset_rel_def)
qed


subsection \<open>weak foreach loop\<close>

definition FORWEAK :: "'a set \<Rightarrow> 'b nres \<Rightarrow> ('a \<Rightarrow> 'b nres) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b nres) \<Rightarrow> 'b nres"
where "FORWEAK X d f c =
  (if X = {} then d
  else do {
    (a, X) \<leftarrow> op_set_npick_remove X;
    b \<leftarrow> f a;
    (b, _) \<leftarrow> WHILE (\<lambda>(_, X). \<not> op_set_isEmpty X) (\<lambda>(b, X).
      do {
        ASSERT (X \<noteq> {});
        (a, X) \<leftarrow> op_set_npick_remove X;
        b' \<leftarrow> f a;
        b \<leftarrow> c b b';
        RETURN (b, X)
      }) (b, X);
    RETURN b
  })"

schematic_goal
  FORWEAK_wset_WHILE_refine:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]:
    "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
    "(di, d) \<in> \<langle>B\<rangle>nres_rel"
    "(fi, f) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel"
    "(ci, c) \<in> B \<rightarrow> B \<rightarrow> \<langle>B\<rangle>nres_rel"
  shows "(?f, FORWEAK X d f c) \<in> \<langle>B\<rangle>nres_rel"
  unfolding FORWEAK_def
  by autoref

lemma FORWEAK_LIST_transfer_nfoldli:
  "nfoldli xs (\<lambda>_. True) (\<lambda>x a. c a x) a \<le> do {
    (a, _) \<leftarrow>
      WHILE (\<lambda>(a, xs). xs \<noteq> []) (\<lambda>(a, xs). do {
        (x, xs) \<leftarrow> RETURN (hd xs, tl xs);
        a \<leftarrow> c a x;
        RETURN (a, xs)
      }) (a, xs);
    RETURN a}"
proof (induct xs arbitrary: a)
  case Nil thus ?case by (auto simp: WHILE_unfold)
next
  case (Cons x xs)
  show ?case
    by (auto simp: WHILE_unfold intro!: bind_mono Cons[THEN order.trans])
qed

lemma
  FORWEAK_wset_refine:
  assumes [relator_props]: "PREFER single_valued A"
  assumes [autoref_rules]:
    "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
    "(di, d) \<in> \<langle>B\<rangle>nres_rel"
    "(fi, f) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel"
    "(ci, c) \<in> B \<rightarrow> B \<rightarrow> \<langle>B\<rangle>nres_rel"
  shows
    "((if Xi = [] then di else do { b \<leftarrow> fi (hd Xi); nfoldli (tl Xi) (\<lambda>_. True) (\<lambda>x b. do {b' \<leftarrow> fi x; ci b b'}) b }),
      (OP FORWEAK ::: \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>B\<rangle>nres_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle>nres_rel) \<rightarrow> (B \<rightarrow> B \<rightarrow> \<langle>B\<rangle>nres_rel) \<rightarrow> \<langle>B\<rangle>nres_rel) $ X $ d $ f $ c) \<in> \<langle>B\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule nres_rel_trans1[OF _ FORWEAK_wset_WHILE_refine[OF assms[simplified autoref_tag_defs]]])
    (auto intro!: bind_mono FORWEAK_LIST_transfer_nfoldli[THEN order.trans])
concrete_definition FORWEAK_LIST for Xi di fi ci uses FORWEAK_wset_refine
lemmas [autoref_rules] = FORWEAK_LIST.refine

schematic_goal FORWEAK_LIST_transfer_nres:
  assumes [refine_transfer]: "nres_of d \<le> d'"
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  assumes [refine_transfer]: "\<And>x y. nres_of (g x y) \<le> g' x y"
  shows
  "nres_of (?f) \<le> FORWEAK_LIST xs d' f' g'"
  unfolding FORWEAK_LIST_def
  by refine_transfer
concrete_definition dFORWEAK_LIST for xs d f g uses FORWEAK_LIST_transfer_nres
lemmas [refine_transfer] = dFORWEAK_LIST.refine

schematic_goal FORWEAK_LIST_transfer_plain:
  assumes [refine_transfer]: "RETURN d \<le> d'"
  assumes [refine_transfer]: "\<And>x. RETURN (f x) \<le> f' x"
  assumes [refine_transfer]: "\<And>x y. RETURN (g x y) \<le> g' x y"
  shows "RETURN ?f \<le> FORWEAK_LIST xs d' f' g'"
  unfolding FORWEAK_LIST_def
  by refine_transfer
concrete_definition FORWEAK_LIST_plain for xs f g uses FORWEAK_LIST_transfer_plain
lemmas [refine_transfer] = FORWEAK_LIST_plain.refine

schematic_goal FORWEAK_LIST_transfer_ne_plain:
  assumes "SIDE_PRECOND (xs \<noteq> [])"
  assumes [refine_transfer]: "\<And>x. RETURN (f x) \<le> f' x"
  assumes [refine_transfer]: "\<And>x y. RETURN (g x y) \<le> g' x y"
  shows "RETURN ?f \<le> FORWEAK_LIST xs d' f' g'"
  using assms
  by (simp add: FORWEAK_LIST_def) refine_transfer
concrete_definition FORWEAK_LIST_ne_plain for xs f g uses FORWEAK_LIST_transfer_ne_plain
lemmas [refine_transfer] = FORWEAK_LIST_ne_plain.refine

lemma FORWEAK_empty[simp]: "FORWEAK {} = (\<lambda>d _ _. d)"
  by (auto simp: FORWEAK_def[abs_def])

lemma FORWEAK_WHILE_casesI:
  assumes "X = {} \<Longrightarrow> d \<le> SPEC P"
  assumes "\<And>a X'. a \<in> X \<Longrightarrow> X' = X - {a} \<Longrightarrow>
    f a \<le> SPEC (\<lambda>x. WHILE (\<lambda>(_, X). X \<noteq> {})
          (\<lambda>(b, X).
            do {
              ASSERT (X \<noteq> {});
              (a, X) \<leftarrow> op_set_npick_remove X;
              b' \<leftarrow> f a;
              b \<leftarrow> c b b';
              RETURN (b, X)
            })
          (x, X')
         \<le> SPEC (\<lambda>(b, _). RETURN b \<le> SPEC P))"
  assumes "\<And>a. a \<in> X \<Longrightarrow>
    f a \<le> SPEC (\<lambda>x. WHILE (\<lambda>(_, X). X \<noteq> {})
          (\<lambda>(b, X).
            do {
              ASSERT (X \<noteq> {});
              (a, X) \<leftarrow> op_set_npick_remove X;
              b' \<leftarrow> f a;
              b \<leftarrow> c b b';
              RETURN (b, X)
            })
          (x, X)
         \<le> SPEC (\<lambda>(b, _). RETURN b \<le> SPEC P))"
  shows "FORWEAK X d f c \<le> SPEC P"
  unfolding FORWEAK_def
  apply (cases "X = {}")
  subgoal by (simp add: assms(1))
  subgoal
    supply op_set_npick_remove_def[refine_vcg_def]
    apply (refine_vcg)
    apply clarsimp
    apply (erule disjE)
    subgoal
      by (refine_vcg assms(2))
    subgoal
      by (refine_vcg assms(3))
    done
  done

lemma FORWEAK_invarI:
  fixes I::"'b \<Rightarrow> 'a set \<Rightarrow> bool"
  assumes "X = {} \<Longrightarrow> d \<le> SPEC P"
  assumes fspec_init1[THEN order_trans]: "\<And>a. a \<in> X \<Longrightarrow> f a \<le> SPEC (\<lambda>x. I x (X - {a}))"
  assumes fspec_init2[THEN order_trans]: "\<And>a. a \<in> X \<Longrightarrow> f a \<le> SPEC (\<lambda>x. I x X)"
  assumes fspec_invar1[THEN order_trans]:
    "\<And>a aa b ba. I aa b \<Longrightarrow> a \<in> b \<Longrightarrow> f a \<le> SPEC (\<lambda>xb. c aa xb \<le> SPEC (\<lambda>r. I r (b - {a})))"
  assumes fspec_invar2[THEN order_trans]: "\<And>a aa b ba. I aa b \<Longrightarrow> a \<in> b \<Longrightarrow> f a \<le> SPEC (\<lambda>xb. c aa xb \<le> SPEC (\<lambda>r. I r b))"
  assumes fin: "\<And>aa. I aa {} \<Longrightarrow> P aa"
  shows "FORWEAK X d f c \<le> SPEC P"
  unfolding FORWEAK_def
  apply (cases "X = {}")
  subgoal by (simp add: assms(1))
  subgoal
    supply op_set_npick_remove_def[refine_vcg_def]
    apply (refine_vcg)
    apply clarsimp
    apply (erule disjE)
    subgoal
      apply (refine_vcg fspec_init1)
      apply (rule order_trans[OF WHILE_le_WHILEI[where I="\<lambda>(a, b). I a b"]])
      apply (refine_vcg)
      subgoal
        apply clarsimp
        apply (erule disjE)
        subgoal by (rule fspec_invar1, assumption, assumption)  (refine_vcg)
        subgoal by (rule fspec_invar2, assumption, assumption)  (refine_vcg)
        done
      subgoal by (simp add: fin)
      done
    subgoal
      apply (refine_vcg fspec_init2)
      apply (rule order_trans[OF WHILE_le_WHILEI[where I="\<lambda>(a, b). I a b"]])
      apply (refine_vcg)
      subgoal
        apply clarsimp
        apply (erule disjE)
        subgoal by (rule fspec_invar1, assumption, assumption)  (refine_vcg)
        subgoal by (rule fspec_invar2, assumption, assumption)  (refine_vcg)
        done
      subgoal by (simp add: fin)
      done
    done
  done

lemma FORWEAK_mono_rule:
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I0[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I {s})"
  assumes I_mono: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it' \<subseteq> it \<Longrightarrow> I it' \<sigma>"
  assumes IP[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>S; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I="\<lambda>b X. X \<subseteq> S \<and> I (S - X) b"])
  subgoal by (rule empty)
  subgoal by (auto simp: Diff_Diff_Int intro!: I0)
  subgoal by (drule I0) (auto simp: I_mono)
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: order_trans)
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: I_mono)
    done
  subgoal by (auto intro!: II)
  done

lemma FORWEAK_case_rule:
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I01[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I (S - {s}))"
  assumes I02[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I S)"
  assumes IP1[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (it-{x})))"
  assumes IP2[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I it))"
  assumes II: "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I = "\<lambda>a b. I b a \<and> b \<subseteq> S"])
  subgoal by (rule empty)
  subgoal by (rule I01) auto
  subgoal by (rule I02) auto
  subgoal for a b it
    apply (rule IP1[of a it b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      by (rule order_trans, assumption) auto
    done
  subgoal by (rule IP2) auto
  subgoal by (rule II) auto
  done

lemma FORWEAK_elementwise_rule:
  assumes "nofail d"
  assumes Inf_spec: "\<And>X. X \<in> XX \<Longrightarrow> Inf_spec X \<le> SPEC (Q X)"
  notes [refine_vcg] = order.trans[OF Inf_spec]
  assumes comb_spec1: "\<And>a b X Y. Q X a \<Longrightarrow> comb a b \<le> SPEC (Q X)"
  assumes comb_spec2: "\<And>a b X Y. Q X b \<Longrightarrow> comb a b \<le> SPEC (Q X)"
  shows "FORWEAK XX d Inf_spec comb \<le> SPEC (\<lambda>i. \<forall>x\<in>XX. Q x i)"
  apply (rule FORWEAK_mono_rule[where I="\<lambda>S i. \<forall>x\<in>S. Q x i"])
  subgoal using \<open>nofail d\<close> by (simp add: nofail_SPEC_iff)
  subgoal by (simp add: Diff_Diff_Int Inf_spec)
  subgoal by force
    subgoal for x it \<sigma>
      apply (refine_transfer refine_vcg)
      apply (rule SPEC_BallI)
      apply (rule SPEC_nofail)
      apply (rule comb_spec2)
      apply assumption
      subgoal for y z
        apply (cases "z = x")
        subgoal by simp (rule comb_spec2)
        subgoal by (rule comb_spec1) force
        done
      done
    subgoal by force
  done

end

lemma nofail_imp_RES_UNIV: "nofail s \<Longrightarrow> s \<le> RES UNIV"
  by (metis Refine_Basic.nofail_SPEC_triv_refine UNIV_I top_empty_eq top_set_def)

lemma FORWEAK_unit_rule[THEN order_trans, refine_vcg]:
  assumes "nofail d"
  assumes "\<And>s. nofail (f s)"
  assumes "nofail (c () ())"
  shows "FORWEAK XS d f c \<le> SPEC (\<lambda>(_::unit). True)"
  using assms
  by (intro order_trans[OF FORWEAK_elementwise_rule[where Q=top]])
    (auto simp: top_fun_def le_SPEC_UNIV_rule nofail_SPEC_triv_refine nofail_imp_RES_UNIV)

lemma FORWEAK_mono_rule':
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I0[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I {s})"
  assumes I_mono: "\<And>ab bb xb. ab \<in> bb \<Longrightarrow> bb \<subseteq> S \<Longrightarrow> I (insert ab (S - bb)) xb \<Longrightarrow> I (S - bb) xb"
  assumes IP[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>S; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I="\<lambda>b X. X \<subseteq> S \<and> I (S - X) b"])
  subgoal by (rule empty)
  subgoal by (auto simp: Diff_Diff_Int intro!: I0)
  subgoal
    apply (rule I0, assumption)
    apply (rule SPEC_rule)
    apply (rule conjI)
    subgoal by simp
    subgoal by (rule I_mono, assumption) auto
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: order_trans)
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: I_mono)
    done
  subgoal by (auto intro!: II)
  done

lemma
  op_set_npick_remove_refine_SPEC[refine_vcg]:
  assumes "\<And>x X'. x \<in> X1 \<Longrightarrow> X' = X1 - {x} \<Longrightarrow> Q (x, X')"
  assumes "\<And>x. x \<in> X1 \<Longrightarrow> Q (x, X1)"
  shows "op_set_npick_remove X1 \<le> SPEC Q"
  using assms
  by (auto simp: op_set_npick_remove_def )

context begin interpretation autoref_syn .
definition "op_set_pick_remove X \<equiv> SPEC (\<lambda>(x, X'). x \<in> X \<and> X' = X - {x})"
lemma op_set_pick_removepat[autoref_op_pat]:
  "SPEC (\<lambda>(x, X'). x \<in> X \<and> X' = X - {x}) \<equiv> op_set_pick_remove $ X"
  "do { x \<leftarrow> SPEC (\<lambda>x. x \<in> X); let X' = X - {x}; f x X' } \<equiv> do { (x, X') \<leftarrow> op_set_pick_remove X; f x X'}"
  by (auto simp: op_set_pick_remove_def pw_eq_iff refine_pw_simps intro!: eq_reflection)

lemma list_all2_tlI: "list_all2 A XS y \<Longrightarrow> list_all2 A (tl XS) (tl y)"
  by (metis list.rel_sel list.sel(2))

lemma
  op_set_pick_remove_refine[autoref_rules]:
  assumes "(XS, X) \<in> \<langle>A\<rangle>list_set_rel"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  shows "(nres_of (dRETURN (hd XS, tl XS)), op_set_pick_remove $ X) \<in> \<langle>A \<times>\<^sub>r \<langle>A\<rangle>list_set_rel\<rangle>nres_rel"
  using assms(1)
  unfolding op_set_pick_remove_def[abs_def] autoref_tag_defs list_set_rel_def list_rel_def br_def
  apply (intro nres_relI SPEC_refine det_SPEC)
  apply safe
  subgoal for x y z
    using assms(2)
    apply (safe intro!: exI[where x="(hd y, set (tl y))"])
    subgoal
      apply (rule prod_relI)
      subgoal by (induct XS y rule: list_all2_induct) auto
      subgoal
        apply (rule relcompI[where b = "tl y"])
        subgoal
          unfolding mem_Collect_eq split_beta' fst_conv snd_conv
          by (rule list_all2_tlI)
        subgoal
          unfolding mem_Collect_eq split_beta' fst_conv snd_conv
          apply (rule conjI)
          subgoal by (metis remove1_tl set_remove1_eq)
          subgoal by simp
          done
        done
      done
    subgoal by (subst (asm) list.rel_sel) simp
    subgoal by (simp add: in_set_tlD)
    subgoal by (simp add: distinct_hd_tl)
    subgoal by auto (meson in_hd_or_tl_conv)
    done
  done

end

end
