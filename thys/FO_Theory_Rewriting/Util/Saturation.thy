theory Saturation
  imports Main
begin

subsection \<open>Set operation closure for idempotent, associative, and commutative functions\<close>

lemma inv_to_set:
  "(\<forall> i < length ss. ss ! i \<in> S) \<longleftrightarrow> set ss \<subseteq> S"
  by (induct ss) (auto simp: nth_Cons split: nat.splits)

lemma ac_comp_fun_commute:
  assumes "\<And> x y. f x y = f y x" and "\<And> x y z. f x (f y z) = f (f x y) z"
  shows "comp_fun_commute f" using assms unfolding comp_fun_commute_def
  by (auto simp: comp_def) fastforce

lemma (in comp_fun_commute) fold_list_swap:
  "fold f xs (fold f ys y) = fold f ys (fold f xs y)"
  by (metis comp_fun_commute fold_commute fold_commute_apply)

lemma (in comp_fun_commute) foldr_list_swap:
  "foldr f xs (foldr f ys y) = foldr f ys (foldr f xs y)"
  by (simp add: fold_list_swap foldr_conv_fold)

lemma (in comp_fun_commute) foldr_to_fold:
  "foldr f xs = fold f xs"
  using comp_fun_commute foldr_fold[of _ f] 
  by (auto simp: comp_def)

lemma (in comp_fun_commute) fold_commute_f:
  "f x (foldr f xs y) = foldr f xs (f x y)"
  using comp_fun_commute unfolding foldr_to_fold
  by (auto simp: comp_def intro: fold_commute_apply)

lemma closure_sound:
  assumes cl: "\<And> s t. s \<in> S \<Longrightarrow> t \<in> S \<Longrightarrow> f s t \<in> S"
    and com: "\<And> x y. f x y = f y x" and ass: "\<And> x y z. f x (f y z) = f (f x y) z"
    and fin: "set ss \<subseteq> S" "ss \<noteq> []"
  shows "fold f (tl ss) (hd ss) \<in> S" using assms(4-)
proof (induct ss)
  case (Cons s ss) note IS = this show ?case
  proof (cases ss)
    case Nil
    then show ?thesis using IS by auto
  next
    case (Cons t ts) show ?thesis
      using IS assms(1) ac_comp_fun_commute[of f, OF com ass] unfolding Cons
      by (auto simp flip: comp_fun_commute.foldr_to_fold) (metis com comp_fun_commute.fold_commute_f)
  qed
qed auto

(* Writing a fold that does not take a base element may simplify the proves *)
locale set_closure_oprator =
  fixes f
  assumes com [ac_simps]: "\<And> x y. f x y = f y x"
    and ass [ac_simps]: "\<And> x y z. f x (f y z) = f (f x y) z"
    and idem: "\<And> x. f x x = x"

sublocale set_closure_oprator \<subseteq> comp_fun_idem
  using set_closure_oprator_axioms ac_comp_fun_commute
  by (auto simp: comp_fun_idem_def comp_fun_idem_axioms_def comp_def set_closure_oprator_def)

context set_closure_oprator
begin

inductive_set closure for S where
  base [simp]: "s \<in> S \<Longrightarrow> s \<in> closure S"
| step [intro]: "s \<in> closure S \<Longrightarrow> t \<in> closure S \<Longrightarrow> f s t \<in> closure S"

lemma closure_idem [simp]:
  "closure (closure S) = closure S" (is "?LS = ?RS")
proof -
  {fix s assume "s \<in> ?LS" then have "s \<in> ?RS" by induct auto}
  moreover
  {fix s assume "s \<in> ?RS" then have "s \<in> ?LS" by induct auto}
  ultimately show ?thesis by blast
qed

lemma fold_dist:
  assumes "xs \<noteq> []"
  shows "f (fold f (tl xs) (hd xs)) t = fold f xs t" using assms
proof (induct xs)
  case (Cons a xs)
  show ?case using Cons com ass fold_commute_f
    by (auto simp: comp_def foldr_to_fold)
qed auto

lemma closure_to_cons_list:
  assumes "s \<in> closure S"
  shows "\<exists> ss \<noteq> []. fold f (tl ss) (hd ss) = s \<and> (\<forall> i < length ss. ss ! i \<in> S)" using assms
proof (induct)
  case (base s) then show ?case by (auto intro: exI[of _ "[s]"])
next
  case (step s t)
  then obtain ss ts where
    s: "fold f (tl ss) (hd ss) = s" and inv_s: "ss \<noteq> []" "\<forall> i < length ss. ss ! i \<in> S" and
    t: "fold f (tl ts) (hd ts) = t" and inv_t: "ts \<noteq> []" "\<forall> i < length ts. ts ! i \<in> S"
    by auto
  then show ?case
    by (auto simp: fold_dist nth_append intro!: exI[of _ "ss @ ts"]) (metis com fold_dist)
qed

lemma sound_fold:
  assumes "set ss \<subseteq> closure S" and "ss \<noteq> []"
  shows "fold f (tl ss) (hd ss) \<in> closure S" using assms
  using closure_sound[of "closure S" f] assms step
  by (auto simp add: com fun_left_comm)

lemma closure_empty [simp]: "closure {} = {}"
  using closure_to_cons_list by auto

lemma closure_mono:
  "S \<subseteq> T \<Longrightarrow> closure S \<subseteq> closure T"
proof
  fix s assume ass: "s \<in> closure S"
  then show "S \<subseteq> T \<Longrightarrow> s \<in> closure T"
    by (induct) (auto simp: closure_to_cons_list)
qed

lemma closure_insert:
  "closure (insert x S) = {x} \<union> closure S \<union> {f x s | s. s \<in> closure S}"
proof -
  {fix t assume ass: "t \<in> closure (insert x S)" "t \<noteq> x" "t \<notin> closure S"
    from closure_to_cons_list[OF ass(1)] obtain ss where
      t: "fold f (tl ss) (hd ss) = t" and inv_t: "ss \<noteq> []" "\<forall> i < length ss. ss ! i \<in> insert x S"
      by auto
    then have mem: "x \<in> set ss" using ass(3) sound_fold[of ss] in_set_conv_nth
      by (force simp add: inv_to_set)
    have "\<exists> s. t = f x s \<and> s \<in> closure S"
    proof (cases "set ss = {x}")
      case True then show ?thesis using ass(2) t
        by (metis com finite.emptyI fold_dist fold_empty fold_insert_idem fold_set_fold idem inv_t(1))
    next
      case False
      from False inv_t(1) mem obtain ts where split: "insert x (set ts) = set ss" "x \<notin> set ts" "ts \<noteq> []"
        by auto (metis False List.finite_set Set.set_insert empty_set finite_insert finite_list)
      then have "\<forall> i < length ts. ts ! i \<in> S" using inv_t(2) split unfolding inv_to_set by auto 
      moreover have "t = f x (Finite_Set.fold f (hd ts) (set (tl ts)))"
        using split t inv_t(1)
        by (metis List.finite_set com fold_dist fold_insert_idem2 fold_set_fold fun_left_idem idem)   
      ultimately show ?thesis using sound_fold[OF _ split(3)] 
        by (auto simp: foldr_to_fold fold_set_fold inv_to_set) force
    qed}
  then show ?thesis
    by (auto simp: fold_set_fold in_mono[OF closure_mono[OF subset_insertI[of S x]]])
qed

lemma finite_S_finite_closure [intro]:
  "finite S \<Longrightarrow> finite (closure S)"
  by (induct rule: finite.induct) (auto simp: closure_insert)

end

locale semilattice_closure_operator =
  cl: set_closure_oprator f for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
fixes less_eq e
assumes neut_fun [simp]:"\<And> x. f e x = x"
  and neut_less [simp]: "\<And> x. less_eq e x"
  and sup_l: "\<And> x y. less_eq x (f x y)"
  and sup_r: "\<And> x y. less_eq y (f x y)"
  and upper_bound: "\<And> x y z. less_eq x z \<Longrightarrow> less_eq y z \<Longrightarrow> less_eq (f x y) z"
  and trans: "\<And> x y z. less_eq x y \<Longrightarrow> less_eq y z \<Longrightarrow> less_eq x z"
  and anti_sym: "\<And> x y. less_eq x y \<Longrightarrow> less_eq y x \<Longrightarrow> x = y"
begin

lemma unique_neut_elem [simp]:
  "f x y = e \<longleftrightarrow> x = e \<and> y = e"
  using neut_fun cl.fun_left_idem
  by (metis cl.com)

abbreviation "closure S \<equiv> cl.closure S"


lemma closure_to_cons_listE:
  assumes "s \<in> closure S"
  obtains ss where "ss \<noteq> []" "fold f ss e = s" "set ss \<subseteq> S"
  using cl.closure_to_cons_list[OF assms] cl.fold_dist
  by (auto simp: inv_to_set) (metis cl.com neut_fun)

lemma sound_fold:
  assumes "set ss \<subseteq> closure S" "ss \<noteq> []"
  shows "fold f ss e \<in> closure S"
  using cl.sound_fold[OF assms] cl.fold_dist[OF assms(2)]
  by (metis cl.com neut_fun)

abbreviation "supremum S \<equiv> Finite_Set.fold f e S"
definition "smaller_subset x S \<equiv> {y. less_eq y x \<and> y \<in> S}"

lemma smaller_subset_empty [simp]:
  "smaller_subset x {} = {}"
  by (auto simp: smaller_subset_def)

lemma finite_smaller_subset [simp, intro]:
  "finite S \<Longrightarrow> finite (smaller_subset x S)"
  by (auto simp: smaller_subset_def)

lemma smaller_subset_mono:
  "smaller_subset x S \<subseteq> S"
  by (auto simp: smaller_subset_def)

lemma sound_set_fold:
  assumes "set ss \<subseteq> closure S" and "ss \<noteq> []"
  shows "supremum (set ss) \<in> closure S"
  using sound_fold[OF assms]
  by (auto simp: cl.fold_set_fold)

lemma supremum_neutral [simp]:
  assumes "finite S" and "supremum S = e"
  shows "S \<subseteq> {e}" using assms
  by (induct) auto

lemma supremum_in_closure:
  assumes "finite S" and "R \<subseteq> closure S" and "R \<noteq> {}"
  shows "supremum R \<in> closure S"
proof -
  obtain L where [simp]: "R = set L"
    using cl.finite_S_finite_closure[OF assms(1)] assms(2) finite_list
    by (metis infinite_super)
  then show ?thesis using sound_set_fold[of L S] assms
    by (cases L) auto
qed

lemma supremum_sound:
  assumes "finite S"
  shows "\<And> t. t \<in> S \<Longrightarrow> less_eq t (supremum S)"
  using assms sup_l sup_r trans
  by induct (auto, blast)

lemma supremum_sound_list:
  "\<forall> i < length ss. less_eq (ss ! i) (fold f ss e)"
  unfolding cl.fold_set_fold[symmetric]
  using supremum_sound[of "set ss"]
  by auto

lemma smaller_subset_insert [simp]:
  "less_eq y x \<Longrightarrow> smaller_subset x (insert y S) = insert y (smaller_subset x S)"
  "\<not> less_eq y x \<Longrightarrow> smaller_subset x (insert y S) = smaller_subset x S"
  by (auto simp: smaller_subset_def)

lemma supremum_smaller_subset:
  assumes "finite S"
  shows "less_eq (supremum (smaller_subset x S)) x" using assms
proof (induct)
  case (insert y F) then show ?case
    by (cases "less_eq y x") (auto simp: upper_bound)
qed simp

lemma pre_subset_eq_pos_subset [simp]:
  shows "smaller_subset x (closure S) = closure (smaller_subset x S)" (is "?LS = ?RS")
proof -
  {fix s assume "s \<in> ?RS" then have "s \<in> ?LS"
      using upper_bound by induct (auto simp: smaller_subset_def)}
  moreover
  {fix s assume ass: "s \<in> ?LS"
    then have "s \<in> closure S" using smaller_subset_mono by auto
    then obtain ss where wit: "ss \<noteq> [] \<and> fold f ss e = s \<and> (set ss \<subseteq> S)"
      using closure_to_cons_listE by blast
    then have "\<forall> i < length ss. less_eq (ss ! i) x"
      using supremum_sound[of "set ss"] supremum_smaller_subset[of "set ss" x]
      unfolding cl.fold_set_fold[symmetric]
      by auto (metis ass local.trans mem_Collect_eq nth_mem smaller_subset_def) 
    then have "s \<in> ?RS" using wit sound_fold[of ss]
      by (auto simp: smaller_subset_def)
        (metis (mono_tags, lifting) cl.closure.base inv_to_set mem_Collect_eq)}
  ultimately show ?thesis by blast
qed


lemma supremum_in_smaller_closure:
  assumes "finite S"
  shows "supremum (smaller_subset x S) \<in> {e} \<union> (closure S)"
  using supremum_in_closure[OF assms, of "smaller_subset x S"]
  by (metis UnI1 UnI2 cl.closure.base fold_empty singletonI smaller_subset_mono subset_iff)


lemma supremum_subset_less_eq:
  assumes "finite S" and "R \<subseteq> S"
  shows "less_eq (supremum R) (supremum S)" using assms
proof (induct arbitrary: R)
  case (insert x F)
  from insert(1, 2, 4) insert(3)[of "R - {x}"]
  have "less_eq (supremum (R - {x})) (f x (supremum F))"
    by (metis Diff_subset_conv insert_is_Un local.trans sup_r)
  then show ?case using insert(1, 2, 4)
    by auto (metis Diff_empty Diff_insert0 cl.fold_rec finite.insertI finite_subset sup_l upper_bound)
qed (auto)


lemma supremum_smaller_closure [simp]:
  assumes "finite S"
  shows "supremum (smaller_subset x (closure S)) = supremum (smaller_subset x S)"
proof (cases "smaller_subset x S = {}")
  case [simp]: True show ?thesis by auto
next
  case False
  have "smaller_subset x S \<subseteq> smaller_subset x (closure S)"
    unfolding pre_subset_eq_pos_subset by auto
  then have l: "less_eq (supremum (smaller_subset x S)) (supremum (smaller_subset x (closure S)))"
    using assms unfolding pre_subset_eq_pos_subset
    by (intro supremum_subset_less_eq) auto
  from False have "supremum (closure (smaller_subset x S)) \<in> closure S"
    using assms cl.closure_mono[OF smaller_subset_mono]
    using \<open>smaller_subset x S \<subseteq> smaller_subset x (closure S)\<close>
    by (auto simp add: assms intro!: supremum_in_closure)
  from closure_to_cons_listE[OF this] obtain ss where
    dec : "supremum (smaller_subset x (closure S)) = Finite_Set.fold f e (set ss)"
    and inv: "ss \<noteq> []" "set ss \<subseteq> S"
    by (auto simp: cl.fold_set_fold) force
  then have "set ss \<subseteq> smaller_subset x S"
    using supremum_sound[OF assms]
    using supremum_smaller_subset[OF assms]
    by (auto simp: smaller_subset_def)
      (metis List.finite_set assms cl.finite_S_finite_closure dec trans supremum_smaller_subset supremum_sound)
  then have "less_eq (supremum (smaller_subset x (closure S))) (supremum (smaller_subset x S))"
    using inv assms unfolding dec
    by (intro supremum_subset_less_eq) auto 
  then show ?thesis using l anti_sym
    by auto  
qed

end

fun lift_f_total where
  "lift_f_total P f None _ = None"
| "lift_f_total P f _ None = None"
| "lift_f_total P f (Some s) (Some t) = (if P s t then Some (f s t) else None)"

fun lift_less_eq_total where
  "lift_less_eq_total f _ None = True"
| "lift_less_eq_total f None _ = False"
| "lift_less_eq_total f (Some s) (Some t) = (f s t)"


locale set_closure_partial_oprator =
  fixes P f
  assumes refl: "\<And> x. P x x"
    and sym: "\<And> x y. P x y \<Longrightarrow> P y x"
    and dist: "\<And> x y z. P y z \<Longrightarrow> P x (f y z) \<Longrightarrow> P x y"
    and assP: "\<And> x y z. P x (f y z) \<Longrightarrow> P y z \<Longrightarrow> P (f x y) z"
    and com [ac_simps]: "\<And> x y. P x y \<Longrightarrow> f x y = f y x"
    and ass [ac_simps]: "\<And> x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> f x (f y z) = f (f x y) z"
    and idem: "\<And> x. f x x = x"
begin

lemma lift_f_total_com:
  "lift_f_total P f x y = lift_f_total P f y x"
  using com by (cases x; cases y) (auto simp: sym)

lemma lift_f_total_ass:
  "lift_f_total P f x (lift_f_total P f y z) = lift_f_total P f (lift_f_total P f x y) z"
proof (cases x)
  case [simp]: (Some s) show ?thesis
  proof (cases y)
    case [simp]: (Some t) show ?thesis
    proof (cases z)
      case [simp]: (Some u) show ?thesis
        by (auto simp add: ass dist[of t u s])
          (metis com dist assP sym)+
    qed auto
  qed auto
qed auto

lemma lift_f_total_idem:
  "lift_f_total P f x x = x"
  by (cases x) (auto simp: idem refl)

lemma lift_f_totalE[elim]:
  assumes "lift_f_total P f s u = Some t"
  obtains v w where "s = Some v" "u = Some w"
  using assms by (cases s; cases u) auto

lemma lift_set_closure_oprator:
  "set_closure_oprator (lift_f_total P f)"
  using lift_f_total_com lift_f_total_ass lift_f_total_idem by unfold_locales blast+

end

sublocale set_closure_partial_oprator \<subseteq> lift_fun: set_closure_oprator "lift_f_total P f"
  by (simp add: lift_set_closure_oprator)


context set_closure_partial_oprator begin

abbreviation "lift_closure S \<equiv> lift_fun.closure (Some ` S)"

inductive_set pred_closure for S where
  base [simp]: "s \<in> S \<Longrightarrow> s \<in> pred_closure S"
| step [intro]: "s \<in> pred_closure S \<Longrightarrow> t \<in> pred_closure S \<Longrightarrow> P s t \<Longrightarrow> f s t \<in> pred_closure S"

lemma pred_closure_to_some_lift_closure:
  assumes "s \<in> pred_closure S"
  shows "Some s \<in> lift_closure S" using assms
proof (induct)
  case (step s t)
  then have "lift_f_total P f (Some s) (Some t) \<in> lift_closure S"
    by (intro lift_fun.closure.step) auto
  then show ?case using step(5)
    by (auto split: if_splits)
qed auto

lemma some_lift_closure_pred_closure:
  fixes t defines "s \<equiv> Some t"
  assumes "Some t \<in> lift_closure S"
  shows "t \<in> pred_closure S" using assms(2)
  unfolding assms(1)[symmetric] using assms(1)
proof (induct arbitrary: t)
  case (step s u)
  from step(5) obtain v w where [simp]: "s = Some v" "u = Some w" by auto
  show ?case using step by (auto split: if_splits)
qed auto

lemma pred_closure_lift_closure:
  "pred_closure S = the ` (lift_closure S - {None})" (is "?LS = ?RS")
proof
  {fix s assume "s \<in> ?LS"
    from pred_closure_to_some_lift_closure[OF this] have "s \<in> ?RS"
      by (metis DiffI empty_iff image_iff insertE option.distinct(1) option.sel)}
  then show "?LS \<subseteq> ?RS" by blast
next 
  {fix s assume ass: "s \<in> ?RS"
    then have "Some s \<in> lift_closure S"
      using option.collapse by fastforce
    from some_lift_closure_pred_closure[OF this] have "s \<in> ?LS"
      using option.collapse by auto}
  then show "?RS \<subseteq> ?LS" by blast
qed

lemma finite_S_finite_closure [simp, intro]:
  "finite S \<Longrightarrow> finite (pred_closure S)"
  using finite_subset[of "Some ` pred_closure S" "lift_closure S"]
  using pred_closure_to_some_lift_closure lift_fun.finite_S_finite_closure[of "Some ` S"]
  by (auto simp add: pred_closure_lift_closure set_closure_partial_oprator_axioms) 

lemma closure_mono:
  assumes "S \<subseteq> T"
  shows "pred_closure S \<subseteq> pred_closure T"
proof -
  have "Some ` S \<subseteq> Some ` T" using assms by auto
  from lift_fun.closure_mono[OF this] show ?thesis
    using pred_closure_to_some_lift_closure some_lift_closure_pred_closure set_closure_partial_oprator_axioms
    by fastforce
qed

lemma pred_closure_empty [simp]:
  "pred_closure {} = {}"
  using pred_closure_lift_closure by fastforce
end

locale semilattice_closure_partial_operator =
  cl: set_closure_partial_oprator P f for P and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
fixes less_eq e
assumes neut_elm :"\<And> x. f e x = x" 
  and neut_pred: "\<And> x. P e x"
  and neut_less: "\<And> x. less_eq e x" 
  and pred_less: "\<And> x y z. less_eq x y \<Longrightarrow> less_eq z y \<Longrightarrow> P x z"
  and sup_l: "\<And> x y. P x y \<Longrightarrow> less_eq x (f x y)"
  and sup_r: "\<And> x y. P x y \<Longrightarrow> less_eq y (f x y)"
  and upper_bound: "\<And> x y z. less_eq x z \<Longrightarrow> less_eq y z \<Longrightarrow> less_eq (f x y) z"
  and trans: "\<And> x y z. less_eq x y \<Longrightarrow> less_eq y z \<Longrightarrow> less_eq x z"
  and anti_sym: "\<And> x y. less_eq x y \<Longrightarrow> less_eq y x \<Longrightarrow> x = y"
begin

abbreviation "lifted_less_eq \<equiv> lift_less_eq_total less_eq"
abbreviation "lifted_fun \<equiv> lift_f_total P f"

lemma lift_less_eq_None [simp]:
  "lifted_less_eq None y \<longleftrightarrow> y = None"
  by (cases y) auto

lemma lift_less_eq_neut_elm [simp]:
  "lifted_fun (Some e) s = s"
  using neut_elm neut_pred by (cases s) auto

lemma lift_less_eq_neut_less [simp]:
  "lifted_less_eq (Some e) s \<longleftrightarrow> True"
  using neut_less by (cases s) auto

lemma lift_less_eq_sup_l [simp]:
  "lifted_less_eq x (lifted_fun x y) \<longleftrightarrow> True"
  using sup_l by (cases x; cases y) auto

lemma lift_less_eq_sup_r [simp]:
  "lifted_less_eq y (lifted_fun x y) \<longleftrightarrow> True"
  using sup_r by (cases x; cases y) auto

lemma lifted_less_eq_trans [trans]:
  "lifted_less_eq x y \<Longrightarrow> lifted_less_eq y z \<Longrightarrow> lifted_less_eq x z"
  using trans by (auto elim!: lift_less_eq_total.elims)

lemma lifted_less_eq_anti_sym [trans]:
  "lifted_less_eq x y \<Longrightarrow> lifted_less_eq y x \<Longrightarrow> x = y"
  using anti_sym by (auto elim!: lift_less_eq_total.elims)

lemma lifted_less_eq_upper:
  "lifted_less_eq x z \<Longrightarrow> lifted_less_eq y z \<Longrightarrow> lifted_less_eq (lifted_fun x y) z"
  using upper_bound pred_less by (auto elim!: lift_less_eq_total.elims)

lemma semilattice_closure_operator_axioms:
  "semilattice_closure_operator_axioms (lift_f_total P f) (lift_less_eq_total less_eq) (Some e)"
  using lifted_less_eq_upper lifted_less_eq_trans lifted_less_eq_anti_sym
  by unfold_locales (auto elim!: lift_f_total.cases)

end

sublocale semilattice_closure_partial_operator \<subseteq> lift_ord: semilattice_closure_operator "lift_f_total P f" "lift_less_eq_total less_eq" "Some e"
  by (simp add: cl.lift_set_closure_oprator semilattice_closure_operator.intro semilattice_closure_operator_axioms)


context semilattice_closure_partial_operator
begin

abbreviation "supremum \<equiv> lift_ord.supremum"
abbreviation "smaller_subset \<equiv> lift_ord.smaller_subset"


lemma supremum_impl:
  assumes "supremum (set (map Some ss)) = Some t"
  shows "foldr f ss e = t" using assms
proof (induct ss arbitrary: t)
  case (Cons a ss)
  then show ?case
    by auto (metis cl.lift_f_totalE lift_f_total.simps(3) option.distinct(1) option.sel) 
qed auto

lemma supremum_smaller_exists_unique:
  assumes "finite S"
  shows "\<exists>! p. supremum (smaller_subset (Some t) (Some ` S)) = Some p" using assms
proof (induct)
  case (insert x F) show ?case
  proof (cases "lifted_less_eq (Some x) (Some t)")
    case True
    obtain p where wit: "supremum (smaller_subset (Some t) (Some ` F)) = Some p"
      using insert by auto
    then have pred: "less_eq p t" "less_eq x t" using True insert(1)
      using lift_ord.supremum_smaller_subset
      by auto (metis finite_imageI lift_less_eq_total.simps(3)) 
    show ?thesis using insert pred wit pred_less
      by auto
  next
    case False then show ?thesis
      using insert by auto 
  qed
qed auto

lemma supremum_neut_or_in_closure:
  assumes "finite S"
  shows "the (supremum (smaller_subset (Some t) (Some ` S))) \<in> {e} \<union> cl.pred_closure S"
  using supremum_smaller_exists_unique[OF assms]
  using lift_ord.supremum_in_smaller_closure[of "Some ` S" "Some t"] assms
  by auto (metis cl.some_lift_closure_pred_closure option.sel)

end

(* At the moment we remove duplicates in each iteration,
   use data structure that can deal better with duplication i.e red black trees *)
fun closure_impl where
  "closure_impl f [] = []"
| "closure_impl f (x # S) = (let cS = closure_impl f S in remdups (x # cS @ map (f x) cS))"

lemma (in set_closure_oprator) closure_impl [simp]:
  "set (closure_impl f S) = closure (set S)"
  by (induct S, auto simp: closure_insert Let_def)

lemma (in set_closure_partial_oprator) closure_impl [simp]:
  "set (map the (removeAll None (closure_impl (lift_f_total P f) (map Some S)))) = pred_closure (set S)"
  using lift_set_closure_oprator set_closure_oprator.closure_impl pred_closure_lift_closure
  by auto

end