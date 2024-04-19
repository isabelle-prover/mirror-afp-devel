(*<*)
theory Prelim
imports Main
begin
(*>*)

section \<open>Auxiliary Lemmas\<close>

lemma Cons_eq_upt_conv: "x # xs = [m ..< n] \<longleftrightarrow> m < n \<and> x = m \<and> xs = [Suc m ..< n]"
  by (induct n arbitrary: xs) (force simp: Cons_eq_append_conv)+

lemma map_setE[elim_format]: "map f xs = ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = y"
  by (induct xs arbitrary: ys) auto

lemma set_Cons_eq: "set_Cons X XS = (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
  by (auto simp: set_Cons_def)

lemma set_Cons_empty_iff: "set_Cons X XS = {} \<longleftrightarrow> (X = {} \<or> XS = {})"
  by (auto simp: set_Cons_eq)

lemma infinite_set_ConsI:
  "XS \<noteq> {} \<Longrightarrow> infinite X \<Longrightarrow> infinite (set_Cons X XS)"
  "X \<noteq> {} \<Longrightarrow> infinite XS \<Longrightarrow> infinite (set_Cons X XS)"
proof(unfold set_Cons_eq)
  assume "infinite X" and "XS \<noteq> {}"
  then obtain xs where "xs \<in> XS"
    by blast
  hence "inj (\<lambda>x. x # xs)"
    by (clarsimp simp: inj_on_def)
  hence "infinite ((\<lambda>x. x # xs) ` X)"
    using \<open>infinite X\<close> finite_imageD inj_on_def
    by blast
  moreover have "((\<lambda>x. x # xs) ` X) \<subseteq> (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
    using \<open>xs \<in> XS\<close> by auto
  ultimately show "infinite (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
    by (simp add: infinite_super)
next
  assume "infinite XS" and "X \<noteq> {}"
  then show "infinite (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
    by (elim contrapos_nn finite_surj[of _ _ tl]) (auto simp: image_iff)
qed

primrec fst_pos :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option"
  where "fst_pos [] x = None"
  | "fst_pos (y#ys) x = (if x = y then Some 0 else
      (case fst_pos ys x of None \<Rightarrow> None | Some n \<Rightarrow> Some (Suc n)))"

lemma fst_pos_None_iff: "fst_pos xs x = None \<longleftrightarrow> x \<notin> set xs"
  by (induct xs arbitrary: x; force split: option.splits)

lemma nth_fst_pos: "x \<in> set xs \<Longrightarrow> xs ! (the (fst_pos xs x)) = x"
  by (induct xs arbitrary: x; fastforce simp: fst_pos_None_iff split: option.splits)

primrec positions :: "'a list \<Rightarrow> 'a \<Rightarrow> nat list"
  where "positions [] x = []"
  | "positions (y#ys) x = (\<lambda>ns. if x = y then 0 # ns else ns) (map Suc (positions ys x))"

lemma eq_positions_iff: "length xs = length ys
  \<Longrightarrow> positions xs x = positions ys y \<longleftrightarrow> (\<forall>n< length xs. xs ! n = x \<longleftrightarrow> ys ! n = y)"
  by (induct xs ys arbitrary: x y rule: list_induct2) (use less_Suc_eq_0_disj in auto)

lemma positions_eq_nil_iff: "positions xs x = [] \<longleftrightarrow> x \<notin> set xs"
  by (induct xs) simp_all

lemma positions_nth: "n \<in> set (positions xs x) \<Longrightarrow> xs ! n = x"
  by (induct xs arbitrary: n x)
    (auto simp: positions_eq_nil_iff[symmetric] split: if_splits)

lemma set_positions_eq: "set (positions xs x) = {n. xs ! n = x \<and> n < length xs}"
  by (induct xs arbitrary: x)
    (use less_Suc_eq_0_disj in \<open>auto simp: positions_eq_nil_iff[symmetric] image_iff split: if_splits\<close>)

lemma positions_length: "n \<in> set (positions xs x) \<Longrightarrow> n < length xs"
  by (induct xs arbitrary: n x)
    (auto simp: positions_eq_nil_iff[symmetric] split: if_splits)

lemma positions_nth_cong:
  "m \<in> set (positions xs x) \<Longrightarrow> n \<in> set (positions xs x) \<Longrightarrow> xs ! n = xs ! m"
  using positions_nth[of _ xs x] by simp

lemma fst_pos_in_positions: "x \<in> set xs \<Longrightarrow> the (fst_pos xs x) \<in> set (positions xs x)"
  by (induct xs arbitrary: x, simp)
    (fastforce simp: hd_map fst_pos_None_iff split: option.splits)

lemma hd_positions_eq_fst_pos: "x \<in> set xs \<Longrightarrow> hd (positions xs x) = the (fst_pos xs x)"
  by (induct xs arbitrary: x)
    (auto simp: hd_map fst_pos_None_iff positions_eq_nil_iff split: option.splits)

lemma sorted_positions: "sorted (positions xs x)"
  by (induct xs arbitrary: x) (auto simp add: sorted_iff_nth_Suc nth_Cons' gr0_conv_Suc)

lemma Min_sorted_list: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> Min (set xs) = hd xs"
  by (induct xs)
    (auto simp: Min_insert2)

lemma Min_positions: "x \<in> set xs \<Longrightarrow> Min (set (positions xs x)) = the (fst_pos xs x)"
  by (auto simp: Min_sorted_list[OF sorted_positions]
      positions_eq_nil_iff hd_positions_eq_fst_pos)

lemma subset_positions_map_fst: "set (positions tXs tX) \<subseteq> set (positions (map fst tXs) (fst tX))"
  by (induct tXs arbitrary: tX)
    (auto simp: subset_eq)

lemma subset_positions_map_snd: "set (positions tXs tX) \<subseteq> set (positions (map snd tXs) (snd tX))"
  by (induct tXs arbitrary: tX)
    (auto simp: subset_eq)

lemma Max_eqI: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> \<exists>a\<in>A. b \<le> a \<Longrightarrow> Max A = b"
  by (rule antisym[OF Max.boundedI Max_ge_iff[THEN iffD2]]; clarsimp)

lemma Max_Suc: "X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> Max (Suc ` X) = Suc (Max X)"
  using Max_ge Max_in
  by (intro Max_eqI) blast+

lemma Max_insert0: "X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> Max (insert (0::nat) X) = Max X"
  using Max_ge Max_in
  by (intro Max_eqI) blast+

lemma positions_Cons_notin_tail: "x \<notin> set xs \<Longrightarrow> positions (x # xs) x = [0::nat]"
  by (cases xs) (auto simp: positions_eq_nil_iff)

lemma Max_set_positions_Cons_hd:
  "x \<notin> set xs \<Longrightarrow> Max (set (positions (x # xs) x)) = 0"
  by (subst positions_Cons_notin_tail) simp_all

lemma Max_set_positions_Cons_tl:
  "y \<in> set xs \<Longrightarrow> Max (set (positions (x # xs) y)) = Suc (Max (set (positions xs y)))"
  by (auto simp: Max_Suc positions_eq_nil_iff)

lemma max_aux: "finite X \<Longrightarrow> Suc j \<in> X \<Longrightarrow> Max (insert (Suc j) (X - {j})) = Max (insert j X)"
  by (smt (verit) max.orderI Max.insert_remove Max_ge Max_insert empty_iff insert_Diff_single
      insert_absorb insert_iff max_def not_less_eq_eq)

lemma ball_swap: "(\<forall>x \<in> A. \<forall>y \<in> B. P x y) = (\<forall>y \<in> B. \<forall>x \<in> A. P x y)"
  by auto

lemma ball_triv_nonempty: "A \<noteq> {} \<Longrightarrow> (\<forall>x \<in> A. P) = P"
  by auto

(*<*)
end
(*>*)