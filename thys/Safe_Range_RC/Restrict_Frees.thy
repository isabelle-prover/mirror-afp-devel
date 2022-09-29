(*<*)
theory Restrict_Frees
imports
  Restrict_Bounds
  "HOL-Library.Product_Lexorder"
  "HOL-Library.List_Lexorder"
  "HOL-Library.Multiset_Order"
begin

hide_const (open) SetIndex.index
(*>*)

section \<open>Restricting Free Variables\<close>

definition fixfree :: "(('a, 'b) fmla \<times> nat rel) set \<Rightarrow> (('a, 'b) fmla \<times> nat rel) set" where
  "fixfree \<Q>fin = {(Qfix, Qeq) \<in> \<Q>fin. nongens Qfix \<noteq> {}}"

definition "disjointvars Q Qeq = (\<Union>V \<in> classes Qeq. if V \<inter> fv Q = {} then V else {})"

fun Conjs where
  "Conjs Q [] = Q"
| "Conjs Q ((x, y) # xys) = Conjs (Conj Q (x \<approx> y)) xys"

function (sequential) Conjs_disjoint where
  "Conjs_disjoint Q xys = (case find (\<lambda>(x,y). {x, y} \<inter> fv Q \<noteq> {}) xys of
     None \<Rightarrow> Conjs Q xys
   | Some (x, y) \<Rightarrow> Conjs_disjoint (Conj Q (x \<approx> y)) (remove1 (x, y) xys))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(Q, xys). length xys)")
    (auto split: if_splits simp: length_remove1 neq_Nil_conv dest!: find_SomeD dest: length_pos_if_in_set)

declare Conjs_disjoint.simps[simp del]

definition CONJ where
  "CONJ = (\<lambda>(Q, Qeq). Conjs Q (sorted_list_of_set Qeq))"

definition CONJ_disjoint where
  "CONJ_disjoint = (\<lambda>(Q, Qeq). Conjs_disjoint Q (sorted_list_of_set Qeq))"

definition inf where
  "inf \<Q>fin Q = {(Q', Qeq) \<in> \<Q>fin. disjointvars Q' Qeq \<noteq> {} \<or> fv Q' \<union> Field Qeq \<noteq> fv Q}"

definition FV where
  "FV Q Qfin Qinf \<equiv> (fv Qfin = fv Q \<or> Qfin = Bool False) \<and> fv Qinf = {}"

definition EVAL where
  "EVAL Q Qfin Qinf \<equiv> (\<forall>I. finite (adom I) \<longrightarrow> (if eval Qinf I = {} then
     eval Qfin I = eval Q I else infinite (eval Q I)))"

definition EVAL' where
  "EVAL' Q Qfin Qinf \<equiv> (\<forall>I. finite (adom I) \<longrightarrow> (if eval Qinf I = {} then
     eval_on (fv Q) Qfin I = eval Q I else infinite (eval Q I)))"

definition (in simplification) split_spec :: "('a :: {infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> (('a, 'b) fmla \<times> ('a, 'b) fmla) nres" where
  "split_spec Q = SPEC (\<lambda>(Qfin, Qinf). sr Qfin \<and> sr Qinf \<and> FV Q Qfin Qinf \<and> EVAL Q Qfin Qinf \<and>
     simplified Qfin \<and> simplified Qinf)"

definition (in simplification) "assemble = (\<lambda>(\<Q>fin, \<Q>inf). (simp (DISJ (CONJ_disjoint ` \<Q>fin)), simp (DISJ (close ` \<Q>inf))))"

fun leftfresh where
  "leftfresh Q [] = True"
| "leftfresh Q ((x, y) # xys) = (x \<notin> fv Q \<and> leftfresh (Conj Q (x \<approx> y)) xys)"

definition (in simplification) "wf_state Q P =
   (\<lambda>(\<Q>fin, \<Q>inf). finite \<Q>fin \<and> finite \<Q>inf \<and>
     (\<forall>(Qfix, Qeq) \<in> \<Q>fin. P Qfix \<and> simplified Qfix \<and> (\<exists>xs. leftfresh Qfix xs \<and> distinct xs \<and> set xs = Qeq) \<and> fv Qfix \<union> Field Qeq \<subseteq> fv Q \<and> irrefl Qeq))"

definition (in simplification) "split_INV1 Q = (\<lambda>\<Q>pair. wf_state Q rrb \<Q>pair \<and> (let (Qfin, Qinf) = assemble \<Q>pair in EVAL' Q Qfin Qinf))"
definition (in simplification) "split_INV2 Q = (\<lambda>\<Q>pair. wf_state Q sr \<Q>pair \<and> (let (Qfin, Qinf) = assemble \<Q>pair in EVAL' Q Qfin Qinf))"

definition (in simplification) split :: "('a :: {infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> (('a, 'b) fmla \<times> ('a, 'b) fmla) nres" where
  "split Q = do {
     Q' \<leftarrow> rb Q;
     \<Q>pair \<leftarrow> WHILE\<^sub>T\<^bsup>split_INV1 Q\<^esup>
        (\<lambda>(\<Q>fin, _). fixfree \<Q>fin \<noteq> {}) (\<lambda>(\<Q>fin, \<Q>inf). do {
          (Qfix, Qeq) \<leftarrow> RES (fixfree \<Q>fin);
          x \<leftarrow> RES (nongens Qfix);
          G \<leftarrow> SPEC (cov x Qfix);
          let \<Q>fin = \<Q>fin - {(Qfix, Qeq)} \<union>
            {(simp (Conj Qfix (DISJ (qps G))), Qeq)} \<union>
            (\<Union>y \<in> eqs x G. {(cp (Qfix[x \<^bold>\<rightarrow> y]), Qeq \<union> {(x,y)})});
          let \<Q>inf = \<Q>inf \<union> {cp (Qfix \<^bold>\<bottom> x)};
          RETURN (\<Q>fin, \<Q>inf)})
        ({(Q', {})}, {});
     \<Q>pair \<leftarrow> WHILE\<^sub>T\<^bsup>split_INV2 Q\<^esup>
        (\<lambda>(\<Q>fin, _). inf \<Q>fin Q \<noteq> {}) (\<lambda>(\<Q>fin, \<Q>inf). do {
          Qpair \<leftarrow> RES (inf \<Q>fin Q);
          let \<Q>fin = \<Q>fin - {Qpair};
          let \<Q>inf = \<Q>inf \<union> {CONJ Qpair};
          RETURN (\<Q>fin, \<Q>inf)})
        \<Q>pair;
     let (Qfin, Qinf) = assemble \<Q>pair;
     Qinf \<leftarrow> rb Qinf;
     RETURN (Qfin, Qinf)}"

lemma finite_fixfree[simp]: "finite \<Q> \<Longrightarrow> finite (fixfree \<Q>)"
  unfolding fixfree_def by (auto elim!: finite_subset[rotated])

lemma (in simplification) split_step_in_mult:
  assumes "(Qfin, Qeq) \<in> \<Q>fin" "finite \<Q>fin" "x \<in> nongens Qfin" "cov x Qfin G" "fv Qfin \<subseteq> F"
  shows "((nongens \<circ> fst) `# mset_set (insert (simp (Conj Qfin (DISJ (qps G))), Qeq) (\<Q>fin - {(Qfin, Qeq)} \<union> (\<lambda>y. (cp (Qfin[x \<^bold>\<rightarrow> y]), insert (x, y) Qeq)) ` eqs x G)),
          (nongens \<circ> fst) `# mset_set \<Q>fin) \<in> mult {(X, Y). X \<subset> Y \<and> Y \<subseteq> F}"
    (is "(?f (insert ?Q (?A \<union> ?B)), ?C) \<in> mult ?R")
proof (subst preorder.mult\<^sub>D\<^sub>M[where less_eq = "(in_rel ?R)\<^sup>=\<^sup>="])
  define X where "X = {(Qfin, Qeq)}"
  define Y where "Y = insert ?Q ?B - (?A \<inter> insert ?Q ?B)"
  have "?f X \<noteq> {#}"
    unfolding X_def by auto
  moreover from assms(1,2) have "?f X \<subseteq># ?C"
    unfolding X_def by (auto intro!: image_eqI[where x = "(Qfin, Qeq)"])
  moreover from assms(1,2,4) have XY:
    "insert ?Q (?A \<union> ?B) = \<Q>fin - X \<union> Y" "X \<subseteq> \<Q>fin" "(\<Q>fin - X) \<inter> Y = {}" "finite X" "finite Y"
    unfolding X_def Y_def by auto
  with assms(2) have "?f (insert ?Q (?A \<union> ?B)) = ?C - ?f X + ?f Y"
    by (force simp: mset_set_Union mset_set_Diff multiset.map_comp o_def
        dest: subset_imp_msubset_mset_set elim: subset_mset.trans
        intro!: subset_imp_msubset_mset_set image_mset_subseteq_mono subset_mset.diff_add_assoc2
        trans[OF image_mset_Diff])
  moreover
  { fix A
    assume "A \<in> Y"
    then have "A \<in> insert ?Q ?B"
      unfolding Y_def by blast
    with assms(3,4) have "nongens (fst A) \<subseteq> nongens Qfin - {x}"
      using Gen_cp_subst[of _ Qfin x] Gen_simp[OF cov_Gen_qps[OF assms(4)]]
        gen_Gen_simp[OF gen.intros(7)[OF disjI1], of _ Qfin _ "DISJ (qps G)"]
      by (fastforce simp: nongens_def fv_subst simp del: cp.simps
          intro!: gen.intros(7) dest!: fv_cp[THEN set_mp] fv_simp[THEN set_mp] fv_DISJ[THEN set_mp, rotated 1]
          elim: cov_fv[OF assms(4) _ qps_in, THEN conjunct2, THEN set_mp]
          cov_fv[OF assms(4) _ eqs_in, THEN conjunct2, THEN set_mp])
    with assms(3) have "nongens (fst A) \<subset> nongens Qfin"
      by auto
    with assms(5) have "\<exists>B \<in> X. nongens (fst A) \<subset> nongens (fst B) \<and> nongens (fst B) \<subseteq> F"
      by (auto simp: X_def nongens_def)
  }
  with XY have "\<And>A. A \<in># ?f Y \<Longrightarrow> \<exists>B. B \<in># ?f X \<and> A \<subset> B \<and> B \<subseteq> F"
    by auto
  ultimately
  show "\<exists>X Y. X \<noteq> {#} \<and> X \<subseteq># ?C \<and> ?f (insert ?Q (?A \<union> ?B)) = ?C - X + Y \<and> (\<forall>k. k \<in># Y \<longrightarrow> (\<exists>a. a \<in># X \<and> k \<subset> a \<and> a \<subseteq> F))"
    by blast
qed (unfold_locales, auto)

lemma EVAL_cong:
  "Qinf \<triangleq> Qinf' \<Longrightarrow> fv Qinf = fv Qinf' \<Longrightarrow> EVAL Q Qfin Qinf = EVAL Q Qfin Qinf'"
  using equiv_eval_eqI[of _ Qinf Qinf']
  by (auto simp: EVAL_def)

lemma EVAL'_cong:
  "Qinf \<triangleq> Qinf' \<Longrightarrow> fv Qinf = fv Qinf' \<Longrightarrow> EVAL' Q Qfin Qinf = EVAL' Q Qfin Qinf'"
  using equiv_eval_eqI[of _ Qinf Qinf']
  by (auto simp: EVAL'_def)

lemma fv_Conjs[simp]: "fv (Conjs Q xys) = fv Q \<union> Field (set xys)"
  by (induct Q xys rule: Conjs.induct) auto

lemma fv_Conjs_disjoint[simp]: "distinct xys \<Longrightarrow> fv (Conjs_disjoint Q xys) = fv Q \<union> Field (set xys)"
proof (induct Q xys rule: Conjs_disjoint.induct)
  case (1 Q xys)
  then show ?case
    by (subst Conjs_disjoint.simps)
      (auto split: option.splits simp: Field_def subset_eq dest: find_SomeD(2))
qed

lemma fv_CONJ[simp]: "finite Qeq \<Longrightarrow> fv (CONJ (Q, Qeq)) = fv Q \<union> Field Qeq"
  unfolding CONJ_def by (auto dest!: fv_cp[THEN set_mp])

lemma fv_CONJ_disjoint[simp]: "finite Qeq \<Longrightarrow> fv (CONJ_disjoint (Q, Qeq)) = fv Q \<union> Field Qeq"
  unfolding CONJ_disjoint_def by auto

lemma rrb_Conjs: "rrb Q \<Longrightarrow> rrb (Conjs Q xys)"
  by (induct Q xys rule: Conjs.induct) auto

lemma CONJ_empty[simp]: "CONJ (Q, {}) = Q"
  by (auto simp: CONJ_def)

lemma CONJ_disjoint_empty[simp]: "CONJ_disjoint (Q, {}) = Q"
  by (auto simp: CONJ_disjoint_def Conjs_disjoint.simps)

lemma Conjs_eq_False_iff[simp]: "irrefl (set xys) \<Longrightarrow> Conjs Q xys = Bool False \<longleftrightarrow> Q = Bool False \<and> xys = []"
  by (induct Q xys rule: Conjs.induct) (auto simp: Let_def is_Bool_def irrefl_def)

lemma CONJ_eq_False_iff[simp]: "finite Qeq \<Longrightarrow> irrefl Qeq \<Longrightarrow> CONJ (Q, Qeq) = Bool False \<longleftrightarrow> Q = Bool False \<and> Qeq = {}"
  by (auto simp: CONJ_def)

lemma Conjs_disjoint_eq_False_iff[simp]: "irrefl (set xys) \<Longrightarrow> Conjs_disjoint Q xys = Bool False \<longleftrightarrow> Q = Bool False \<and> xys = []"
proof (induct Q xys rule: Conjs_disjoint.induct)
  case (1 Q xys)
  then show ?case
    by (subst Conjs_disjoint.simps)
      (auto simp: Let_def is_Bool_def irrefl_def split: option.splits)
qed

lemma CONJ_disjoint_eq_False_iff[simp]: "finite Qeq \<Longrightarrow> irrefl Qeq \<Longrightarrow> CONJ_disjoint (Q, Qeq) = Bool False \<longleftrightarrow> Q = Bool False \<and> Qeq = {}"
  by (auto simp: CONJ_disjoint_def)

lemma sr_Conjs_disjoint:
  "distinct xys \<Longrightarrow> (\<forall>V\<in>classes (set xys). V \<inter> fv Q \<noteq> {}) \<Longrightarrow> sr Q \<Longrightarrow> sr (Conjs_disjoint Q xys)"
proof (induct Q xys rule: Conjs_disjoint.induct)
  case (1 Q xys)
  show ?case
  proof (cases "find (\<lambda>(x, y). {x, y} \<inter> fv Q \<noteq> {}) xys")
    case None
    with 1(2-) show ?thesis
      using classes_intersect_find_not_None[of xys "fv Q"]
      by (cases xys) (simp_all add: Conjs_disjoint.simps)
  next
    case (Some xy)
    then obtain x y where xy: "xy = (x, y)" and xy_in: "(x, y) \<in> set xys"
      by (cases xy) (auto dest!: find_SomeD)
    with Some 1(4) have "sr (Conj Q (x \<approx> y))"
      by (auto dest: find_SomeD simp: sr_Conj_eq)
    moreover from 1(2,3) have "\<forall>V\<in>classes (set (remove1 (x, y) xys)). V \<inter> fv (Conj Q (x \<approx> y)) \<noteq> {}"
      by (subst (asm) insert_remove_id[OF xy_in], unfold classes_insert)
        (auto simp: class_None_eq class_Some_eq split: option.splits if_splits)
    ultimately show ?thesis
      using 1(2-) Some xy 1(1)[OF Some xy[symmetric]]
      by (simp add: Conjs_disjoint.simps)
  qed
qed

lemma sr_CONJ_disjoint:
  "inf \<Q>fin Q = {} \<Longrightarrow> (Qfin, Qeq) \<in> \<Q>fin \<Longrightarrow> finite Qeq \<Longrightarrow> sr Qfin \<Longrightarrow> sr (CONJ_disjoint (Qfin, Qeq))"
  unfolding inf_def disjointvars_def CONJ_disjoint_def prod.case
  by (drule arg_cong[of _ _ "\<lambda>A. (Qfin, Qeq) \<in> A"], intro sr_cp sr_Conjs_disjoint)
    (auto simp only: mem_Collect_eq prod.case simp_thms distinct_sorted_list_of_set
       set_sorted_list_of_set SUP_bot_conv classes_nonempty split: if_splits)

lemma equiv_Conjs_cong: "Q \<triangleq> Q' \<Longrightarrow> Conjs Q xys \<triangleq> Conjs Q' xys"
  by (induct Q xys arbitrary: Q' rule: Conjs.induct) auto

lemma Conjs_pull_out: "Conjs Q (xys @ (x, y) # xys') \<triangleq> Conjs (Conj Q (x \<approx> y)) (xys @ xys')"
  by (induct Q xys rule: Conjs.induct)
    (auto elim!: equiv_trans intro!: equiv_Conjs_cong intro: equiv_def[THEN iffD2])

lemma Conjs_reorder: "distinct xys \<Longrightarrow> distinct xys' \<Longrightarrow> set xys = set xys' \<Longrightarrow> Conjs Q xys \<triangleq> Conjs Q xys'"
proof (induct Q xys arbitrary: xys' rule: Conjs.induct)
  case (2 Q x y xys)
  from 2(4) obtain i where i: "i < length xys'" "xys' ! i = (x, y)"
    by (auto simp: set_eq_iff in_set_conv_nth)
  with 2(2-4) have *: "set xys = set (take i xys') \<union> set (drop (Suc i) xys')"
    by (subst (asm) (1 2) id_take_nth_drop[of i xys'])
      (auto simp: set_eq_iff dest: in_set_takeD in_set_dropD)
  from i 2(2,3) show ?case
    by (subst id_take_nth_drop[OF i(1)], subst (asm) (3) id_take_nth_drop[OF i(1)])
      (auto simp: * intro!: equiv_trans[OF _ Conjs_pull_out[THEN equiv_sym]] 2(1))
qed simp

lemma ex_Conjs_disjoint_eq_Conjs:
  "distinct xys \<Longrightarrow> \<exists>xys'. distinct xys' \<and> set xys = set xys' \<and> Conjs_disjoint Q xys = Conjs Q xys'"
proof (induct Q xys rule: Conjs_disjoint.induct)
  case (1 Q xys)
  show ?case
  proof (cases "find (\<lambda>(x, y). {x, y} \<inter> fv Q \<noteq> {}) xys")
    case None
    with 1(2) show ?thesis
      by (subst Conjs_disjoint.simps) (auto intro!: exI[of _ xys])
  next
    case (Some xy)
    with 1(1)[of xy "fst xy" "snd xy"] 1(2)
    obtain xys' where "distinct xys'"
      "set xys - {xy} = set xys'"
      "Conjs_disjoint (Conj Q (fst xy \<approx> snd xy)) (remove1 xy xys) =
       Conjs (Conj Q (fst xy \<approx> snd xy)) xys'"
      by auto
    with Some show ?thesis
      by (subst Conjs_disjoint.simps, intro exI[of _ "xy # xys'"])
        (auto simp: set_eq_iff dest: find_SomeD)
  qed
qed

lemma Conjs_disjoint_equiv_Conjs:
  assumes "distinct xys"
  shows "Conjs_disjoint Q xys \<triangleq> Conjs Q xys"
proof -
  from assms obtain xys' where xys': "distinct xys'" "set xys = set xys'" and "Conjs_disjoint Q xys = Conjs Q xys'"
    using ex_Conjs_disjoint_eq_Conjs by blast
  note this(3)
  also have "\<dots> \<triangleq> Conjs Q xys"
    by (intro Conjs_reorder xys' sym assms)
  finally show ?thesis
    by blast
qed

lemma infinite_eval_Conjs: "infinite (eval Q I) \<Longrightarrow> leftfresh Q xys \<Longrightarrow> infinite (eval (Conjs Q xys) I)"
proof (induct Q xys rule: Conjs.induct)
  case (2 Q x y xys)
  then show ?case
    unfolding Conjs.simps
    by (intro 2(1) infinite_eval_Conj) auto
qed simp

lemma leftfresh_fv_subset: "leftfresh Q xys \<Longrightarrow> fv Q' \<subseteq> fv Q \<Longrightarrow> leftfresh Q' xys"
  by (induct Q xys arbitrary: Q' rule: leftfresh.induct) (auto simp: subset_eq)

lemma fun_upds_map: "(\<forall>x. x \<notin> set ys \<longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> \<sigma>[ys :=\<^sup>* map \<tau> ys] = \<tau>"
  by (induct ys arbitrary: \<sigma>) auto

lemma map_fun_upds: "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> map (\<sigma>[xs :=\<^sup>* ys]) xs = ys"
  by (induct xs ys arbitrary: \<sigma> rule: list_induct2) auto

lemma zip_map: "zip xs (map f xs) = map (\<lambda>x. (x, f x)) xs"
  by (induct xs) auto

lemma filter_sorted_list_of_set:
  "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> filter (\<lambda>x. x \<in> A) (sorted_list_of_set B) = sorted_list_of_set A"
proof (induct B arbitrary: A rule: finite_induct)
  case (insert x B)
  then have "finite A" by (auto simp: finite_subset)
  moreover
  from insert(1,2) have "filter (\<lambda>y. y \<in> A - {x}) (sorted_list_of_set B) =
             filter (\<lambda>x. x \<in> A) (sorted_list_of_set B)"
    by (intro filter_cong) auto
  ultimately  show ?case
    using insert(1,2,4) insert(3)[of "A - {x}"] sorted_list_of_set_insert_remove[of A x]
    by (cases "x \<in> A") (auto  simp: filter_insort filter_insort_triv subset_insert_iff insert_absorb)
qed simp

lemma infinite_eval_eval_on[rotated 2]:
  assumes "fv Q \<subseteq> X" "finite X"
  shows "infinite (eval Q I) \<Longrightarrow> infinite (eval_on X Q I)"
proof (erule infinite_surj[of _ "\<lambda>xs. map snd (filter (\<lambda>(x,_). x \<in> fv Q) (zip (sorted_list_of_set X) xs))"],
  unfold eval_deep_def Let_def, safe)
  fix xs \<sigma>
  assume len: "length (sorted_list_of_set (fv Q)) = length xs" and
    "sat Q I (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* xs])" (is "sat Q I ?\<tau>")
  moreover from assms len have "\<sigma>[sorted_list_of_set X :=\<^sup>* map ?\<tau> (sorted_list_of_set X)] = ?\<tau>"
    by (intro fun_upds_map) force
  ultimately show "xs \<in> (\<lambda>xs. map snd (filter (\<lambda>(x, _). x \<in> fv Q) (zip (sorted_list_of_set X) xs))) `
    eval_on X Q I" using assms
    by (auto simp: eval_on_def image_iff zip_map filter_map o_def filter_sorted_list_of_set map_fun_upds
      intro!: exI[of _ "map (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* xs]) (sorted_list_of_set X)"] exI[of _ \<sigma>])
qed

lemma infinite_eval_CONJ_disjoint:
  assumes "infinite (eval Q I)" "finite (adom I)" "fv Q \<subseteq> X" "Field Qeq \<subseteq> X" "finite X" "\<exists>xys. distinct xys \<and> leftfresh Q xys \<and> set xys = Qeq"
  shows "infinite (eval_on X (CONJ_disjoint (Q, Qeq)) I)"
proof -
  from assms(6) obtain xys where "distinct xys" "leftfresh Q xys" "set xys = Qeq"
    by blast
  with assms(1-5) show ?thesis
    using infinite_eval_eval_on[OF infinite_eval_Conjs[of Q I xys], of X] equiv_eval_on_eqI[of I  "Conjs_disjoint Q (sorted_list_of_set Qeq)" "Conjs Q xys" X]
      equiv_trans[OF Conjs_disjoint_equiv_Conjs[of "sorted_list_of_set Qeq" Q] Conjs_reorder[of _ xys]]
      fv_Conjs[of Q xys]
    by (force simp: CONJ_disjoint_def subset_eq equiv_eval_on_eqI[OF _ equiv_cp])
qed

lemma sat_Conjs: "sat (Conjs Q xys) I \<sigma> \<longleftrightarrow> sat Q I \<sigma> \<and> (\<forall>(x, y) \<in> set xys. sat (x \<approx> y) I \<sigma>)"
  by (induct Q xys rule: Conjs.induct) auto

lemma sat_Conjs_disjoint: "sat (Conjs_disjoint Q xys) I \<sigma> \<longleftrightarrow> sat Q I \<sigma> \<and> (\<forall>(x, y) \<in> set xys. sat (x \<approx> y) I \<sigma>)"
proof (induct Q xys rule: Conjs_disjoint.induct)
  case (1 Q xys)
  then show ?case
    by (subst Conjs_disjoint.simps)
      (auto simp: sat_Conjs dest: find_SomeD(2) set_remove1_subset[THEN set_mp] in_set_remove_cases[rotated] split: option.splits)
qed

lemma sat_CONJ: "finite Qeq \<Longrightarrow> sat (CONJ (Q, Qeq)) I \<sigma> \<longleftrightarrow> sat Q I \<sigma> \<and> (\<forall>(x, y) \<in> Qeq. sat (x \<approx> y) I \<sigma>)"
  unfolding CONJ_def by (auto simp: sat_Conjs)

lemma sat_CONJ_disjoint: "finite Qeq \<Longrightarrow> sat (CONJ_disjoint (Q, Qeq)) I \<sigma> \<longleftrightarrow> sat Q I \<sigma> \<and> (\<forall>(x, y) \<in> Qeq. sat (x \<approx> y) I \<sigma>)"
  unfolding CONJ_disjoint_def by (auto simp: sat_Conjs_disjoint)

lemma Conjs_inject: "Conjs Q xys = Conjs Q' xys \<longleftrightarrow> Q = Q'"
  by (induct Q xys arbitrary: Q' rule: Conjs.induct) auto

lemma nonempty_disjointvars_infinite:
  assumes "disjointvars (Qfin :: ('a :: infinite, 'b) fmla) Qeq \<noteq> {}"
    "finite Qeq" "fv Qfin \<union> Field Qeq \<subseteq> X" "finite X" "sat Qfin I \<sigma>" "\<forall>(x, y)\<in>Qeq. \<sigma> x = \<sigma> y"
  shows "infinite (eval_on X (CONJ_disjoint (Qfin, Qeq)) I)"
proof -
  from assms(1) obtain x V where xV: "V \<in> classes Qeq" "x \<in> V" "V \<inter> fv Qfin = {}"
    by (auto simp: disjointvars_def)
  show ?thesis
  proof (rule infinite_surj[OF infinite_UNIV, of "\<lambda>ds. ds ! index (sorted_list_of_set X) x"], safe)
    fix z
    let ?ds = "map (\<lambda>v. if v \<in> V then z else \<sigma> v) (sorted_list_of_set X)"
    from xV have "x \<in> Field Qeq"
      by (metis UnionI classes_cover)
    { fix a b
      assume *: "(a, b) \<in> Qeq"
      from this edge_same_class[OF xV(1) this] assms(3,6) have "a \<in> X" "b \<in> X" "a \<in> V \<longleftrightarrow> b \<in> V" "\<sigma> a = \<sigma> b"
        by (auto dest: FieldI1 FieldI2)
      with xV(1) assms(3,4) have "(\<sigma>[sorted_list_of_set X :=\<^sup>* ?ds]) a = (\<sigma>[sorted_list_of_set X :=\<^sup>* ?ds]) b"
        by (subst (1 2) fun_upds_in) auto
    }
    with assms(2-) xV  \<open>x \<in> Field Qeq\<close>
    show "z \<in> (\<lambda>ds. ds ! index (sorted_list_of_set X) x) ` eval_on X (CONJ_disjoint (Qfin, Qeq)) I"
      by (auto simp: eval_on_def CONJ_disjoint_def sat_Conjs_disjoint Let_def image_iff fun_upds_in subset_eq
         intro!: exI[of _ "map (\<lambda>v. if v \<in> V then z else \<sigma> v) (sorted_list_of_set X)"] exI[of _ \<sigma>]
         elim!: sat_fv_cong[THEN iffD1, rotated -1])
  qed
qed

lemma EVAL'_EVAL: "EVAL' Q Qfin Qinf \<Longrightarrow> FV Q Qfin Qinf \<Longrightarrow> EVAL Q Qfin Qinf"
  unfolding EVAL_def EVAL'_def FV_def
  by (subst (2) eval_def) auto

lemma cpropagated_Conjs_disjoint:
  "distinct xys \<Longrightarrow> irrefl (set xys) \<Longrightarrow> \<forall>V\<in>classes (set xys). V \<inter> fv Q \<noteq> {} \<Longrightarrow> cpropagated Q \<Longrightarrow> cpropagated (Conjs_disjoint Q xys)"
proof (induct Q xys rule: Conjs_disjoint.induct)
  case (1 Q xys)
  show ?case
  proof (cases "find (\<lambda>(x, y). {x, y} \<inter> fv Q \<noteq> {}) xys")
    case None
    with 1(2-) show ?thesis
      using classes_intersect_find_not_None[of xys "fv Q"]
      by (cases xys) (simp_all add: Conjs_disjoint.simps)
  next
    case (Some xy)
    then obtain x y where xy: "xy = (x, y)" and xy_in: "(x, y) \<in> set xys"
      by (cases xy) (auto dest!: find_SomeD)
    with Some 1(3,5) have "cpropagated (Conj Q (x \<approx> y))"
      by (auto dest: find_SomeD simp: cpropagated_def irrefl_def is_Bool_def)
    moreover from 1(2,4) have "\<forall>V\<in>classes (set (remove1 (x, y) xys)). V \<inter> fv (Conj Q (x \<approx> y)) \<noteq> {}"
      by (subst (asm) insert_remove_id[OF xy_in], unfold classes_insert)
        (auto simp: class_None_eq class_Some_eq split: option.splits if_splits)
    moreover from 1(3) have "irrefl (set xys - {(x, y)})"
      by (auto simp: irrefl_def)
    ultimately show ?thesis
      using 1(2-) Some xy 1(1)[OF Some xy[symmetric]]
      by (simp add: Conjs_disjoint.simps)
  qed
qed

lemma (in simplification) simplified_Conjs_disjoint:
  "distinct xys \<Longrightarrow> irrefl (set xys) \<Longrightarrow> \<forall>V\<in>classes (set xys). V \<inter> fv Q \<noteq> {} \<Longrightarrow> simplified Q \<Longrightarrow> simplified (Conjs_disjoint Q xys)"
proof (induct Q xys rule: Conjs_disjoint.induct)
  case (1 Q xys)
  show ?case
  proof (cases "find (\<lambda>(x, y). {x, y} \<inter> fv Q \<noteq> {}) xys")
    case None
    with 1(2-) show ?thesis
      using classes_intersect_find_not_None[of xys "fv Q"]
      by (cases xys) (simp_all add: Conjs_disjoint.simps)
  next
    case (Some xy)
    then obtain x y where xy: "xy = (x, y)" and xy_in: "(x, y) \<in> set xys"
      by (cases xy) (auto dest!: find_SomeD)
    with Some 1(3,5) have "simplified (Conj Q (x \<approx> y))"
      by (auto dest: find_SomeD simp: irrefl_def intro!: simplified_Conj_eq)
    moreover from 1(2,4) have "\<forall>V\<in>classes (set (remove1 (x, y) xys)). V \<inter> fv (Conj Q (x \<approx> y)) \<noteq> {}"
      by (subst (asm) insert_remove_id[OF xy_in], unfold classes_insert)
        (auto simp: class_None_eq class_Some_eq split: option.splits if_splits)
    moreover from 1(3) have "irrefl (set xys - {(x, y)})"
      by (auto simp: irrefl_def)
    ultimately show ?thesis
      using 1(2-) Some xy 1(1)[OF Some xy[symmetric]]
      by (simp add: Conjs_disjoint.simps)
  qed
qed

lemma disjointvars_empty_iff: "disjointvars Q Qeq = {} \<longleftrightarrow> (\<forall>V\<in>classes Qeq. V \<inter> fv Q \<noteq> {})"
  unfolding disjointvars_def UNION_empty_conv
  using classes_nonempty by auto

lemma cpropagated_CONJ_disjoint:
  "finite Qeq \<Longrightarrow> irrefl Qeq \<Longrightarrow> disjointvars Q Qeq = {} \<Longrightarrow> cpropagated Q \<Longrightarrow> cpropagated (CONJ_disjoint (Q, Qeq))"
  unfolding CONJ_disjoint_def prod.case disjointvars_empty_iff
  by (rule cpropagated_Conjs_disjoint) auto

lemma (in simplification) simplified_CONJ_disjoint:
  "finite Qeq \<Longrightarrow> irrefl Qeq \<Longrightarrow> disjointvars Q Qeq = {} \<Longrightarrow> simplified Q \<Longrightarrow> simplified (CONJ_disjoint (Q, Qeq))"
  unfolding CONJ_disjoint_def prod.case disjointvars_empty_iff
  by (rule simplified_Conjs_disjoint) auto

lemma (in simplification) split_INV1_init:
  "rrb Q' \<Longrightarrow> simplified Q' \<Longrightarrow> Q \<triangleq> Q' \<Longrightarrow> fv Q' \<subseteq> fv Q \<Longrightarrow> split_INV1 Q ({(Q', {})}, {})"
  by (auto simp add: split_INV1_def wf_state_def assemble_def FV_def EVAL'_def eval_def[symmetric] eval_simp_False irrefl_def
    sat_simp equiv_def intro!: equiv_eval_on_eval_eqI del: equalityI dest: fv_simp[THEN set_mp] split: prod.splits)

lemma (in simplification) split_INV1_I:
  "wf_state Q rrb (\<Q>fin, \<Q>inf) \<Longrightarrow> EVAL' Q (simp (DISJ (CONJ_disjoint ` \<Q>fin))) (simp (DISJ (close ` \<Q>inf))) \<Longrightarrow>
    split_INV1 Q (\<Q>fin, \<Q>inf)"
  unfolding split_INV1_def assemble_def by auto

lemma EVAL'_I: 
  "(\<And>I. finite (adom I) \<Longrightarrow> eval Qinf I = {} \<Longrightarrow> eval_on (fv Q) Qfin I = eval Q I) \<Longrightarrow>
   (\<And>I. finite (adom I) \<Longrightarrow> eval Qinf I \<noteq> {} \<Longrightarrow> infinite (eval Q I)) \<Longrightarrow> EVAL' Q Qfin Qinf"
  unfolding EVAL'_def by auto

lemma (in simplification) wf_state_Un:
  "wf_state Q P (\<Q>fin, \<Q>inf) \<Longrightarrow> wf_state Q P (insert Qpair \<Q>new, {Q'}) \<Longrightarrow>
   wf_state Q P (insert Qpair (\<Q>fin \<union> \<Q>new), insert Q' \<Q>inf)"
  by (auto simp: wf_state_def)

lemma (in simplification) wf_state_Diff:
  "wf_state Q P (\<Q>fin, \<Q>inf) \<Longrightarrow> wf_state Q P (\<Q>fin - \<Q>new, \<Q>inf)"
  by (auto simp: wf_state_def)

lemma (in simplification) split_INV1_step:
  assumes "split_INV1 Q (\<Q>fin, \<Q>inf)" "(Qfin, Qeq) \<in> fixfree \<Q>fin" "x \<in> nongens Qfin" "cov x Qfin G"
  shows "split_INV1 Q
    (insert (simp (Conj Qfin (DISJ (qps G))), Qeq)
      (\<Q>fin - {(Qfin, Qeq)} \<union> (\<lambda>y. (cp (Qfin[x \<^bold>\<rightarrow> y]), insert (x, y) Qeq)) ` eqs x G),
    insert (cp (Qfin \<^bold>\<bottom> x)) \<Q>inf)"
    (is "split_INV1 Q (?Qfin, ?Qinf)")
proof (intro split_INV1_I EVAL'_I, goal_cases wf fin inf)
  case wf
  from assms(1) have wf: "wf_state Q rrb (\<Q>fin, \<Q>inf)"
    by (auto simp: split_INV1_def)
  with assms(2,3) obtain xys where *:
    "x \<in> fv Qfin" "(Qfin, Qeq) \<in> \<Q>fin" "finite \<Q>fin" "finite Qeq" "finite \<Q>inf" "fv Qfin \<subseteq> fv Q" "Field Qeq \<subseteq> fv Q"
    "distinct xys" "leftfresh Qfin xys" "set xys = Qeq" "rrb Qfin" "irrefl Qeq"
    by (auto simp: fixfree_def nongens_def wf_state_def)
  moreover from * have "\<exists>xs. leftfresh (simp (Conj Qfin (DISJ (qps G)))) xs \<and> distinct xs \<and> set xs = set xys"
    using cov_fv[OF assms(4) _ qps_in] assms(4)
    by (intro exI[of _ xys])
      (force elim!: leftfresh_fv_subset dest!: fv_simp[THEN set_mp] fv_DISJ[THEN set_mp, rotated 1])
  moreover from * have "\<exists>xs. leftfresh (cp (Qfin[x \<^bold>\<rightarrow> z])) xs \<and> distinct xs \<and> set xs = insert (x, z) (set xys)"
    if "z \<in> eqs x G" for z
    using cov_fv[OF assms(4) _ eqs_in, of z x] assms(4) that
    by (intro exI[of _ "if (x, z) \<in> set xys then xys else (x, z) # xys"])
      (auto simp: fv_subst dest!: fv_cp[THEN set_mp] elim!: leftfresh_fv_subset)
  ultimately show ?case
    using cov_fv[OF assms(4) _ qps_in] cov_fv[OF assms(4) _ eqs_in] assms(4)
    by (intro wf_state_Un wf_state_Diff wf)
      (auto simp: wf_state_def rrb_simp simplified_simp simplified_cp rrb_cp_subst fv_subst
      subset_eq irrefl_def
      dest!: fv_cp[THEN set_mp] fv_simp[THEN set_mp] fv_DISJ[THEN set_mp, rotated 1])
next
  case (fin I)
  note eq = trans[OF sat_simp sat_DISJ, symmetric]
  from assms have *:
    "x \<in> fv Qfin" "(Qfin, Qeq) \<in> \<Q>fin" "fv Qfin \<subseteq> fv Q" "Field Qeq \<subseteq> fv Q" and
    finite[simp]: "finite \<Q>fin" "finite Qeq" "finite \<Q>inf"
    by (auto simp: split_INV1_def fixfree_def nongens_def wf_state_def)
  with fin have unsat: "\<forall>\<sigma>. \<not> sat (Qfin \<^bold>\<bottom> x) I \<sigma>" and "\<forall>x\<in>\<Q>inf. \<forall>\<sigma>. \<not> sat x I \<sigma>"
    by (auto simp: eval_empty_close eval_simp_DISJ_closed)
  with fin(1) assms(1) * have "eval_on (fv Q) (simp (DISJ (CONJ_disjoint ` \<Q>fin))) I = eval Q I"
    unfolding split_INV1_def Let_def assemble_def prod.case EVAL'_def
    by (auto simp: eval_empty_close eval_simp_DISJ_closed)
  with assms(4) show ?case
  proof (elim trans[rotated], intro eval_on_cong box_equals[OF _ eq eq])
    fix \<sigma>
    from * have "(\<exists>Q\<in>\<Q>fin. sat (CONJ_disjoint Q) I \<sigma>) \<longleftrightarrow>
        sat (CONJ_disjoint (Qfin, Qeq)) I \<sigma> \<or> (\<exists>Q\<in>\<Q>fin - {(Qfin, Qeq)}. sat (CONJ_disjoint Q) I \<sigma>)"
      using assms(4) by (auto simp: fixfree_def)
    also have "sat (CONJ_disjoint (Qfin, Qeq)) I \<sigma> \<longleftrightarrow>
        sat (CONJ_disjoint (simp (Conj Qfin (DISJ (qps G))), Qeq)) I \<sigma> \<or>
        (\<exists>Q\<in>(\<lambda>y. (cp (Qfin[x \<^bold>\<rightarrow> y]), insert (x, y) Qeq)) ` eqs x G. sat (CONJ_disjoint Q) I \<sigma>)"
      using cov_sat_fin[of x Qfin G I \<sigma>] assms(3,4) fin(1) unsat
      by (auto simp: eval_empty_close sat_CONJ_disjoint nongens_def)
    finally show "(\<exists>Q\<in>CONJ_disjoint ` ?Qfin. sat Q I \<sigma>) \<longleftrightarrow> (\<exists>Q\<in>CONJ_disjoint ` \<Q>fin. sat Q I \<sigma>)"
      by auto
  qed simp_all
next
  case (inf I)
  from assms have *:
    "x \<in> fv Qfin" "(Qfin, Qeq) \<in> \<Q>fin" "finite \<Q>fin" "finite Qeq" "finite \<Q>inf" "fv Qfin \<subseteq> fv Q" "Field Qeq \<subseteq> fv Q"
    "\<exists>xys. distinct xys \<and> leftfresh Qfin xys \<and> set xys = Qeq"
    by (auto simp: split_INV1_def fixfree_def nongens_def wf_state_def)
  with inf obtain \<sigma> where "sat (Qfin \<^bold>\<bottom> x) I \<sigma> \<or> (\<exists>Q \<in> \<Q>inf. sat Q I \<sigma>)"
    by (subst (asm) eval_simp_DISJ_closed) (auto simp: eval_empty_close sat_CONJ simp del: fv_CONJ)
  then show ?case
  proof (elim disjE)
    assume "sat (Qfin \<^bold>\<bottom> x) I \<sigma>"
    then have "infinite (eval Qfin I)"
      by (rule cov_eval_inf[OF assms(4) *(1) inf(1)])
    then have "infinite (eval_on (fv Q) (CONJ_disjoint (Qfin, Qeq)) I)"
      by (rule infinite_eval_CONJ_disjoint[OF _ inf(1) *(6,7) _ *(8)]) simp
    with * have "infinite (eval_on (fv Q) (simp (DISJ (CONJ_disjoint ` \<Q>fin))) I)"
      by (elim infinite_Implies_mono_on[rotated 3]) (auto simp: sat_simp)
    with inf assms(1) show ?case
      by (auto simp: split_INV1_def assemble_def EVAL'_def split: if_splits)
  next
    assume "\<exists>Q\<in>\<Q>inf. sat Q I \<sigma>"
    with inf(1) assms(1) * show ?case
      by (auto simp: split_INV1_def assemble_def EVAL'_def eval_simp_DISJ_closed eval_empty_close
          split: if_splits)
  qed
qed

lemma (in simplification) split_INV1_decreases:
  assumes "split_INV1 Q (\<Q>fin, \<Q>inf)" "(Qfin, Qeq) \<in> fixfree \<Q>fin" "x \<in> nongens Qfin" "cov x Qfin G"
  shows "((nongens \<circ> fst) `# mset_set (insert (simp (Conj Qfin (DISJ (qps G))), Qeq) (\<Q>fin - {(Qfin, Qeq)} \<union> (\<lambda>y. (cp (Qfin[x \<^bold>\<rightarrow> y]), insert (x, y) Qeq)) ` eqs x G)),
          (nongens \<circ> fst) `# mset_set \<Q>fin) \<in> mult {(X, Y). X \<subset> Y \<and> Y \<subseteq> fv Q}"
  using assms by (intro split_step_in_mult) (auto simp: fixfree_def split_INV1_def wf_state_def)

lemma (in simplification) split_INV2_init:
  "split_INV1 Q (\<Q>fin, \<Q>inf) \<Longrightarrow> fixfree \<Q>fin = {} \<Longrightarrow> split_INV2 Q (\<Q>fin, \<Q>inf)"
  by (auto simp: split_INV1_def split_INV2_def wf_state_def sr_def fixfree_def)

lemma (in simplification) split_INV2_I:
  "wf_state Q sr (\<Q>fin, \<Q>inf) \<Longrightarrow> EVAL' Q (simp (DISJ (CONJ_disjoint ` \<Q>fin))) (simp (DISJ (close ` \<Q>inf))) \<Longrightarrow>
    split_INV2 Q (\<Q>fin, \<Q>inf)"
  unfolding split_INV2_def assemble_def by auto

lemma (in simplification) split_INV2_step:
  assumes "split_INV2 Q (\<Q>fin, \<Q>inf)" "(Qfin, Qeq) \<in> inf \<Q>fin Q"
  shows "split_INV2 Q (\<Q>fin - {(Qfin, Qeq)}, insert (CONJ (Qfin, Qeq)) \<Q>inf)"
proof (intro split_INV2_I EVAL'_I, goal_cases wf fin inf)
  case wf
  with assms(1) show ?case 
    by (auto simp: split_INV2_def wf_state_def)
next
  case (fin I)
  with assms have finite[simp]: "finite \<Q>fin" "finite Qeq" and
    unsat: "\<And>\<sigma>. \<not> sat (CONJ (Qfin, Qeq)) I \<sigma>" and
    eval: "eval_on (fv Q) (simp (DISJ (CONJ_disjoint ` \<Q>fin))) I = eval Q I"
    by (auto simp: split_INV2_def inf_def wf_state_def assemble_def EVAL'_def eval_simp_DISJ_closed eval_empty_close)
  from eval show ?case
  proof (elim trans[rotated], unfold eval_on_simp, intro eval_DISJ_prune_unsat ballI allI; (elim DiffE imageE; hypsubst_thin)?)
    fix Qpair \<sigma>
    assume "Qpair \<in> \<Q>fin" "CONJ_disjoint Qpair \<notin> CONJ_disjoint ` (\<Q>fin - {(Qfin, Qeq)})"
    with unsat[of \<sigma>] show "\<not> sat (CONJ_disjoint Qpair) I \<sigma>"
      by (cases "Qeq = snd Qpair"; cases Qpair) (auto simp: sat_CONJ_disjoint sat_CONJ)
  qed auto
next
  case (inf I)
  from assms have *:
    "(Qfin, Qeq) \<in> \<Q>fin" "finite \<Q>fin" "finite Qeq" "finite \<Q>inf" "fv Qfin \<subseteq> fv Q" "Field Qeq \<subseteq> fv Q"
    by (auto simp: split_INV2_def inf_def wf_state_def)
  with inf obtain \<sigma> where "sat Qfin I \<sigma> \<and> (\<forall>(x, y) \<in> Qeq. \<sigma> x = \<sigma> y) \<or> (\<exists>Q \<in> \<Q>inf. sat Q I \<sigma>)"
    by (subst (asm) eval_simp_DISJ_closed) (auto simp: eval_empty_close sat_CONJ simp del: fv_CONJ)
  then show ?case
  proof (elim disjE conjE)
    assume "sat Qfin I \<sigma>" "\<forall>(x, y) \<in> Qeq. \<sigma> x = \<sigma> y"
    with assms * have "infinite (eval_on (fv Q) (CONJ_disjoint (Qfin, Qeq)) I)"
      using nonempty_disjointvars_infinite[of Qfin Qeq "fv Q" I \<sigma>]
        infinite_eval_on_extra_variables[of "fv Q" "CONJ_disjoint (Qfin, Qeq)" I, OF _ _ exI, of \<sigma>]
      by (cases "fv (CONJ_disjoint (Qfin, Qeq)) \<subset> fv Q") (auto simp: inf_def sat_CONJ sat_CONJ_disjoint)
    with * have "infinite (eval_on (fv Q) (simp (DISJ (CONJ_disjoint ` \<Q>fin))) I)"
      by (elim infinite_Implies_mono_on[rotated 3]) (auto simp: sat_simp)
    with inf assms(1) show ?case
      by (auto simp: split_INV2_def assemble_def EVAL'_def split: if_splits)
  next
    assume "\<exists>Q \<in> \<Q>inf. sat Q I \<sigma>"
    with inf(1) assms(1) * show "infinite (eval Q I)"
      by (auto simp: split_INV2_def assemble_def EVAL'_def eval_simp_DISJ_closed eval_empty_close
        split: if_splits)
  qed
qed

lemma (in simplification) split_INV2_decreases:
  "split_INV2 Q (\<Q>fin, \<Q>inf) \<Longrightarrow> (Qfin, Qeq) \<in> Restrict_Frees.inf \<Q>fin Q \<Longrightarrow> card (\<Q>fin - {(Qfin, Qeq)}) < card \<Q>fin"
  by (rule psubset_card_mono) (auto simp: inf_def split_INV2_def wf_state_def)

lemma (in simplification) split_INV2_stop_fin_sr:
  "inf \<Q>fin Q = {} \<Longrightarrow> split_INV2 Q (\<Q>fin, \<Q>inf) \<Longrightarrow> assemble (\<Q>fin, \<Q>inf) = (Qfin, Qinf) \<Longrightarrow> sr Qfin"
  by (auto 0 4 simp: split_INV2_def assemble_def wf_state_def inf_def
    intro!: sr_simp sr_DISJ[of _ "fv Q"] sr_CONJ_disjoint[of \<Q>fin Q])

lemma (in simplification) split_INV2_stop_inf_sr:
  "split_INV2 Q (\<Q>fin, \<Q>inf) \<Longrightarrow> assemble (\<Q>fin, \<Q>inf) = (Qfin, Qinf) \<Longrightarrow> fv Q' \<subseteq> fv Qinf \<Longrightarrow> rrb Q' \<Longrightarrow> sr Q'"
  using fv_DISJ_close[of \<Q>inf] fv_simp[of "DISJ (close ` \<Q>inf)"]
  by (auto simp: split_INV2_def assemble_def wf_state_def sr_def nongens_def)

lemma (in simplification) split_INV2_stop_FV:
  assumes "fv Q' \<subseteq> fv Qinf" "inf \<Q>fin Q = {}" "split_INV2 Q (\<Q>fin, \<Q>inf)" "assemble (\<Q>fin, \<Q>inf) = (Qfin, Qinf)"
  shows "FV Q Qfin Q'"
proof -
  have "simplified Q'" "fv Q' = fv Q" if "Q' \<in> CONJ_disjoint ` \<Q>fin" for Q'
    using that assms(2,3)
    by (auto simp: split_INV2_def wf_state_def inf_def simplified_CONJ_disjoint)
  with assms(1,3,4) show ?thesis
    using fv_simp_DISJ_eq[of "CONJ_disjoint ` \<Q>fin" "fv Q"] fv_DISJ_close[of \<Q>inf] fv_simp[of "DISJ (close ` \<Q>inf)"]
    by (auto simp: split_INV2_def assemble_def wf_state_def FV_def)
qed

lemma (in simplification) split_INV2_stop_EVAL:
  assumes "fv Q' \<subseteq> fv Qinf" "inf \<Q>fin Q = {}" "split_INV2 Q (\<Q>fin, \<Q>inf)" "assemble (\<Q>fin, \<Q>inf) = (Qfin, Qinf)" "Qinf \<triangleq> Q'"
  shows "EVAL Q Qfin Q'"
proof -
  have "simplified Q'" "fv Q' = fv Q" if "Q' \<in> CONJ_disjoint ` \<Q>fin" for Q'
    using that assms(2,3)
    by (auto simp: split_INV2_def wf_state_def inf_def simplified_CONJ_disjoint)
  with assms(1,3,4,5) show ?thesis
    using fv_simp_DISJ_eq[of "CONJ_disjoint ` \<Q>fin" "fv Q"] fv_DISJ_close[of \<Q>inf] fv_simp[of "DISJ (close ` \<Q>inf)"]
    by (auto simp: split_INV2_def assemble_def wf_state_def sr_def EVAL'_cong FV_def elim!: EVAL'_EVAL)
qed

lemma (in simplification) simplified_assemble:
  "assemble (\<Q>fin, \<Q>inf) = (Qfin, Qinf) \<Longrightarrow> simplified Qfin"
  by (auto simp: assemble_def simplified_simp)

lemma (in simplification) split_correct:
  notes cp.simps[simp del]
  shows "split Q \<le> split_spec Q"
  unfolding split_def split_spec_def Let_def
  by (refine_vcg rb_correct[THEN order_trans, unfolded rb_spec_def]
      WHILEIT_rule[where I="split_INV1 Q" and R="inv_image (mult {(X, Y). X \<subset> Y \<and> Y \<subseteq> fv Q}) (image_mset (nongens o fst) o mset_set o fst)"]
      WHILEIT_rule[where I="split_INV2 Q" and R="measure (\<lambda>(\<Q>fin, _). card \<Q>fin)"])
    (auto simp: wf_mult finite_subset_wf split_step_in_mult
      conj_disj_distribR ex_disj_distrib card_gt_0_iff image_image image_Un
      insert_commute ac_simps UNION_singleton_eq_range simplified_assemble
      split_INV1_init split_INV1_step split_INV1_decreases
      split_INV2_init split_INV2_step split_INV2_decreases
      split_INV2_stop_fin_sr split_INV2_stop_inf_sr split_INV2_stop_FV split_INV2_stop_EVAL)

(*<*)
end
(*>*)
