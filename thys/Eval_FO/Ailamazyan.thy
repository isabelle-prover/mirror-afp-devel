theory Ailamazyan
  imports Eval_FO Cluster Mapping_Code
begin

fun SP :: "('a, 'b) fo_fmla \<Rightarrow> nat set" where
  "SP (Eqa (Var n) (Var n')) = (if n \<noteq> n' then {n, n'} else {})"
| "SP (Neg \<phi>) = SP \<phi>"
| "SP (Conj \<phi> \<psi>) = SP \<phi> \<union> SP \<psi>"
| "SP (Disj \<phi> \<psi>) = SP \<phi> \<union> SP \<psi>"
| "SP (Exists n \<phi>) = SP \<phi> - {n}"
| "SP (Forall n \<phi>) = SP \<phi> - {n}"
| "SP _ = {}"

lemma SP_fv: "SP \<phi> \<subseteq> fv_fo_fmla \<phi>"
  by (induction \<phi> rule: SP.induct) auto

lemma finite_SP: "finite (SP \<phi>)"
  using SP_fv finite_fv_fo_fmla finite_subset by fastforce

fun SP_list_rec :: "('a, 'b) fo_fmla \<Rightarrow> nat list" where
  "SP_list_rec (Eqa (Var n) (Var n')) = (if n \<noteq> n' then [n, n'] else [])"
| "SP_list_rec (Neg \<phi>) = SP_list_rec \<phi>"
| "SP_list_rec (Conj \<phi> \<psi>) = SP_list_rec \<phi> @ SP_list_rec \<psi>"
| "SP_list_rec (Disj \<phi> \<psi>) = SP_list_rec \<phi> @ SP_list_rec \<psi>"
| "SP_list_rec (Exists n \<phi>) = filter (\<lambda>m. n \<noteq> m) (SP_list_rec \<phi>)"
| "SP_list_rec (Forall n \<phi>) = filter (\<lambda>m. n \<noteq> m) (SP_list_rec \<phi>)"
| "SP_list_rec _ = []"

definition SP_list :: "('a, 'b) fo_fmla \<Rightarrow> nat list" where
  "SP_list \<phi> = remdups_adj (sort (SP_list_rec \<phi>))"

lemma SP_list_set: "set (SP_list \<phi>) = SP \<phi>"
  unfolding SP_list_def
  by (induction \<phi> rule: SP.induct) (auto simp: fv_fo_terms_set_list)

lemma sorted_distinct_SP_list: "sorted_distinct (SP_list \<phi>)"
  unfolding SP_list_def
  by (auto intro: distinct_remdups_adj_sort)

fun d :: "('a, 'b) fo_fmla \<Rightarrow> nat" where
  "d (Eqa (Var n) (Var n')) = (if n \<noteq> n' then 2 else 1)"
| "d (Neg \<phi>) = d \<phi>"
| "d (Conj \<phi> \<psi>) = max (d \<phi>) (max (d \<psi>) (card (SP (Conj \<phi> \<psi>))))"
| "d (Disj \<phi> \<psi>) = max (d \<phi>) (max (d \<psi>) (card (SP (Disj \<phi> \<psi>))))"
| "d (Exists n \<phi>) = d \<phi>"
| "d (Forall n \<phi>) = d \<phi>"
| "d _ = 1"

lemma d_pos: "1 \<le> d \<phi>"
  by (induction \<phi> rule: d.induct) auto

lemma card_SP_d: "card (SP \<phi>) \<le> d \<phi>"
  using dual_order.trans
  by (induction \<phi> rule: SP.induct) (fastforce simp: card_Diff1_le finite_SP)+

fun eval_eterm :: "('a + 'c) val \<Rightarrow> 'a fo_term \<Rightarrow> 'a + 'c" (infix "\<cdot>e" 60) where
  "eval_eterm \<sigma> (Const c) = Inl c"
| "eval_eterm \<sigma> (Var n) = \<sigma> n"

definition eval_eterms :: "('a + 'c) val \<Rightarrow> ('a fo_term) list \<Rightarrow>
  ('a + 'c) list" (infix "\<odot>e" 60) where
  "eval_eterms \<sigma> ts = map (eval_eterm \<sigma>) ts"

lemma eval_eterm_cong: "(\<And>n. n \<in> fv_fo_term_set t \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
  eval_eterm \<sigma> t = eval_eterm \<sigma>' t"
  by (cases t) auto

lemma eval_eterms_fv_fo_terms_set: "\<sigma> \<odot>e ts = \<sigma>' \<odot>e ts \<Longrightarrow> n \<in> fv_fo_terms_set ts \<Longrightarrow> \<sigma> n = \<sigma>' n"
proof (induction ts)
  case (Cons t ts)
  then show ?case
    by (cases t) (auto simp: eval_eterms_def fv_fo_terms_set_def)
qed (auto simp: eval_eterms_def fv_fo_terms_set_def)

lemma eval_eterms_cong: "(\<And>n. n \<in> fv_fo_terms_set ts \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
  eval_eterms \<sigma> ts = eval_eterms \<sigma>' ts"
  by (auto simp: eval_eterms_def fv_fo_terms_set_def intro: eval_eterm_cong)

lemma eval_terms_eterms: "map Inl (\<sigma> \<odot> ts) = (Inl \<circ> \<sigma>) \<odot>e ts"
proof (induction ts)
  case (Cons t ts)
  then show ?case
    by (cases t) (auto simp: eval_terms_def eval_eterms_def)
qed (auto simp: eval_terms_def eval_eterms_def)

fun ad_equiv_pair :: "'a set \<Rightarrow> ('a + 'c) \<times> ('a + 'c) \<Rightarrow> bool" where
  "ad_equiv_pair X (a, a') \<longleftrightarrow> (a \<in> Inl ` X \<longrightarrow> a = a') \<and> (a' \<in> Inl ` X \<longrightarrow> a = a')"

fun sp_equiv_pair :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "sp_equiv_pair (a, b) (a', b') \<longleftrightarrow> (a = a' \<longleftrightarrow> b = b')"

definition ad_equiv_list :: "'a set \<Rightarrow> ('a + 'c) list \<Rightarrow> ('a + 'c) list \<Rightarrow> bool" where
  "ad_equiv_list X xs ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>x \<in> set (zip xs ys). ad_equiv_pair X x)"

definition sp_equiv_list :: "('a + 'c) list \<Rightarrow> ('a + 'c) list \<Rightarrow> bool" where
  "sp_equiv_list xs ys \<longleftrightarrow> length xs = length ys \<and> pairwise sp_equiv_pair (set (zip xs ys))"

definition ad_agr_list :: "'a set \<Rightarrow> ('a + 'c) list \<Rightarrow> ('a + 'c) list \<Rightarrow> bool" where
  "ad_agr_list X xs ys \<longleftrightarrow> length xs = length ys \<and> ad_equiv_list X xs ys \<and> sp_equiv_list xs ys"

lemma ad_equiv_pair_refl[simp]: "ad_equiv_pair X (a, a)"
  by auto

declare ad_equiv_pair.simps[simp del]

lemma ad_equiv_pair_comm: "ad_equiv_pair X (a, a') \<longleftrightarrow> ad_equiv_pair X (a', a)"
  by (auto simp: ad_equiv_pair.simps)

lemma ad_equiv_pair_mono: "X \<subseteq> Y \<Longrightarrow> ad_equiv_pair Y (a, a') \<Longrightarrow> ad_equiv_pair X (a, a')"
  unfolding ad_equiv_pair.simps
  by fastforce

lemma sp_equiv_pair_comm: "sp_equiv_pair x y \<longleftrightarrow> sp_equiv_pair y x"
  by (cases x; cases y) auto

definition sp_equiv :: "('a + 'c) val \<Rightarrow> ('a + 'c) val \<Rightarrow> nat set \<Rightarrow> bool" where
  "sp_equiv \<sigma> \<tau> I \<longleftrightarrow> pairwise sp_equiv_pair ((\<lambda>n. (\<sigma> n, \<tau> n)) ` I)"

lemma sp_equiv_mono: "I \<subseteq> J \<Longrightarrow> sp_equiv \<sigma> \<tau> J \<Longrightarrow> sp_equiv \<sigma> \<tau> I"
  by (auto simp: sp_equiv_def pairwise_def)

definition ad_agr_sets :: "nat set \<Rightarrow> nat set \<Rightarrow> 'a set \<Rightarrow> ('a + 'c) val \<Rightarrow>
  ('a + 'c) val \<Rightarrow> bool" where
  "ad_agr_sets FV S X \<sigma> \<tau> \<longleftrightarrow> (\<forall>i \<in> FV. ad_equiv_pair X (\<sigma> i, \<tau> i)) \<and> sp_equiv \<sigma> \<tau> S"

lemma ad_agr_sets_comm: "ad_agr_sets FV S X \<sigma> \<tau> \<Longrightarrow> ad_agr_sets FV S X \<tau> \<sigma>"
  unfolding ad_agr_sets_def sp_equiv_def pairwise_def
  by (subst ad_equiv_pair_comm) auto

lemma ad_agr_sets_mono: "X \<subseteq> Y \<Longrightarrow> ad_agr_sets FV S Y \<sigma> \<tau> \<Longrightarrow> ad_agr_sets FV S X \<sigma> \<tau>"
  using ad_equiv_pair_mono
  by (fastforce simp: ad_agr_sets_def)

lemma ad_agr_sets_mono': "S \<subseteq> S' \<Longrightarrow> ad_agr_sets FV S' X \<sigma> \<tau> \<Longrightarrow> ad_agr_sets FV S X \<sigma> \<tau>"
  by (auto simp: ad_agr_sets_def sp_equiv_def pairwise_def)

lemma ad_equiv_list_comm: "ad_equiv_list X xs ys \<Longrightarrow> ad_equiv_list X ys xs"
  by (auto simp: ad_equiv_list_def) (smt (verit, del_insts) ad_equiv_pair_comm in_set_zip prod.sel(1) prod.sel(2))

lemma ad_equiv_list_mono: "X \<subseteq> Y \<Longrightarrow> ad_equiv_list Y xs ys \<Longrightarrow> ad_equiv_list X xs ys"
  using ad_equiv_pair_mono
  by (fastforce simp: ad_equiv_list_def)

lemma ad_equiv_list_trans:
  assumes "ad_equiv_list X xs ys" "ad_equiv_list X ys zs"
  shows "ad_equiv_list X xs zs"
proof -
  have lens: "length xs = length ys" "length xs = length zs" "length ys = length zs"
    using assms
    by (auto simp: ad_equiv_list_def)
  have "\<And>x z. (x, z) \<in> set (zip xs zs) \<Longrightarrow> ad_equiv_pair X (x, z)"
  proof -
    fix x z
    assume "(x, z) \<in> set (zip xs zs)"
    then obtain i where i_def: "i < length xs" "xs ! i = x" "zs ! i = z"
      by (auto simp: set_zip)
    define y where "y = ys ! i"
    have "ad_equiv_pair X (x, y)" "ad_equiv_pair X (y, z)"
      using assms lens i_def
      by (fastforce simp: set_zip y_def ad_equiv_list_def)+
    then show "ad_equiv_pair X (x, z)"
      unfolding ad_equiv_pair.simps
      by blast
  qed
  then show ?thesis
    using assms
    by (auto simp: ad_equiv_list_def)
qed

lemma ad_equiv_list_link: "(\<forall>i \<in> set ns. ad_equiv_pair X (\<sigma> i, \<tau> i)) \<longleftrightarrow>
  ad_equiv_list X (map \<sigma> ns) (map \<tau> ns)"
  by (auto simp: ad_equiv_list_def set_zip) (metis in_set_conv_nth nth_map)

lemma set_zip_comm: "(x, y) \<in> set (zip xs ys) \<Longrightarrow> (y, x) \<in> set (zip ys xs)"
  by (metis in_set_zip prod.sel(1) prod.sel(2))

lemma set_zip_map: "set (zip (map \<sigma> ns) (map \<tau> ns)) = (\<lambda>n. (\<sigma> n, \<tau> n)) ` set ns"
  by (induction ns) auto

lemma sp_equiv_list_comm: "sp_equiv_list xs ys \<Longrightarrow> sp_equiv_list ys xs"
  unfolding sp_equiv_list_def
  using set_zip_comm
  by (auto simp: pairwise_def) force+

lemma sp_equiv_list_trans:
  assumes "sp_equiv_list xs ys" "sp_equiv_list ys zs"
  shows "sp_equiv_list xs zs"
proof -
  have lens: "length xs = length ys" "length xs = length zs" "length ys = length zs"
    using assms
    by (auto simp: sp_equiv_list_def)
  have "pairwise sp_equiv_pair (set (zip xs zs))"
  proof (rule pairwiseI)
    fix xz xz'
    assume "xz \<in> set (zip xs zs)" "xz' \<in> set (zip xs zs)"
    then obtain x z i x' z' i' where xz_def: "i < length xs" "xs ! i = x" "zs ! i = z"
      "xz = (x, z)" "i' < length xs" "xs ! i' = x'" "zs ! i' = z'" "xz' = (x', z')"
      by (auto simp: set_zip)
    define y where "y = ys ! i"
    define y' where "y' = ys ! i'"
    have "sp_equiv_pair (x, y) (x', y')" "sp_equiv_pair (y, z) (y', z')"
      using assms lens xz_def
      by (auto simp: sp_equiv_list_def pairwise_def y_def y'_def set_zip) metis+
    then show "sp_equiv_pair xz xz'"
      by (auto simp: xz_def)
  qed
  then show ?thesis
    using assms
    by (auto simp: sp_equiv_list_def)
qed

lemma sp_equiv_list_link: "sp_equiv_list (map \<sigma> ns) (map \<tau> ns) \<longleftrightarrow> sp_equiv \<sigma> \<tau> (set ns)"
  apply (auto simp: sp_equiv_list_def sp_equiv_def pairwise_def set_zip in_set_conv_nth)
     apply (metis nth_map)
    apply (metis nth_map)
   apply fastforce+
  done

lemma ad_agr_list_comm: "ad_agr_list X xs ys \<Longrightarrow> ad_agr_list X ys xs"
  using ad_equiv_list_comm sp_equiv_list_comm
  by (fastforce simp: ad_agr_list_def)

lemma ad_agr_list_mono: "X \<subseteq> Y \<Longrightarrow> ad_agr_list Y ys xs \<Longrightarrow> ad_agr_list X ys xs"
  using ad_equiv_list_mono
  by (force simp: ad_agr_list_def)

lemma ad_agr_list_rev_mono:
  assumes "Y \<subseteq> X" "ad_agr_list Y ys xs" "Inl -` set xs \<subseteq> Y" "Inl -` set ys \<subseteq> Y"
  shows "ad_agr_list X ys xs"
proof -
  have "(a, b) \<in> set (zip ys xs) \<Longrightarrow> ad_equiv_pair Y (a, b) \<Longrightarrow> ad_equiv_pair X (a, b)" for a b
    using assms
    apply (cases a; cases b)
       apply (auto simp: ad_agr_list_def ad_equiv_list_def vimage_def set_zip)
    unfolding ad_equiv_pair.simps
       apply (metis Collect_mem_eq Collect_mono_iff imageI nth_mem)
      apply (metis Collect_mem_eq Collect_mono_iff imageI nth_mem)
     apply (metis Collect_mem_eq Collect_mono_iff imageI nth_mem)
    apply (metis Inl_Inr_False image_iff)
    done
  then show ?thesis
    using assms
    by (fastforce simp: ad_agr_list_def ad_equiv_list_def)
qed

lemma ad_agr_list_trans: "ad_agr_list X xs ys \<Longrightarrow> ad_agr_list X ys zs \<Longrightarrow> ad_agr_list X xs zs"
  using ad_equiv_list_trans sp_equiv_list_trans
  by (force simp: ad_agr_list_def)

lemma ad_agr_list_refl: "ad_agr_list X xs xs"
  by (auto simp: ad_agr_list_def ad_equiv_list_def set_zip ad_equiv_pair.simps
      sp_equiv_list_def pairwise_def)

lemma ad_agr_list_set: "ad_agr_list X xs ys \<Longrightarrow> y \<in> X \<Longrightarrow> Inl y \<in> set ys \<Longrightarrow> Inl y \<in> set xs"
  by (auto simp: ad_agr_list_def ad_equiv_list_def set_zip in_set_conv_nth)
     (metis ad_equiv_pair.simps image_eqI)

lemma ad_agr_list_length: "ad_agr_list X xs ys \<Longrightarrow> length xs = length ys"
  by (auto simp: ad_agr_list_def)

lemma ad_agr_list_eq: "set ys \<subseteq> AD \<Longrightarrow> ad_agr_list AD (map Inl xs) (map Inl ys) \<Longrightarrow> xs = ys"
  by (fastforce simp: ad_agr_list_def ad_equiv_list_def set_zip ad_equiv_pair.simps
      intro!: nth_equalityI)

lemma sp_equiv_list_subset:
  assumes "set ms \<subseteq> set ns" "sp_equiv_list (map \<sigma> ns) (map \<sigma>' ns)"
  shows "sp_equiv_list (map \<sigma> ms) (map \<sigma>' ms)"
  unfolding sp_equiv_list_def length_map pairwise_def
proof (rule conjI, rule refl, (rule ballI)+, rule impI)
  fix x y
  assume "x \<in> set (zip (map \<sigma> ms) (map \<sigma>' ms))" "y \<in> set (zip (map \<sigma> ms) (map \<sigma>' ms))" "x \<noteq> y"
  then have "x \<in> set (zip (map \<sigma> ns) (map \<sigma>' ns))" "y \<in> set (zip (map \<sigma> ns) (map \<sigma>' ns))" "x \<noteq> y"
    using assms(1)
    by (auto simp: set_zip) (metis in_set_conv_nth nth_map subset_iff)+
  then show "sp_equiv_pair x y"
    using assms(2)
    by (auto simp: sp_equiv_list_def pairwise_def)
qed

lemma ad_agr_list_subset: "set ms \<subseteq> set ns \<Longrightarrow> ad_agr_list X (map \<sigma> ns) (map \<sigma>' ns) \<Longrightarrow>
  ad_agr_list X (map \<sigma> ms) (map \<sigma>' ms)"
  by (auto simp: ad_agr_list_def ad_equiv_list_def sp_equiv_list_subset set_zip)
     (metis (no_types, lifting) in_set_conv_nth nth_map subset_iff)

lemma ad_agr_list_link: "ad_agr_sets (set ns) (set ns) AD \<sigma> \<tau> \<longleftrightarrow>
  ad_agr_list AD (map \<sigma> ns) (map \<tau> ns)"
  unfolding ad_agr_sets_def ad_agr_list_def
  using ad_equiv_list_link sp_equiv_list_link
  by fastforce

definition ad_agr :: "('a, 'b) fo_fmla \<Rightarrow> 'a set \<Rightarrow> ('a + 'c) val \<Rightarrow> ('a + 'c) val \<Rightarrow> bool" where
  "ad_agr \<phi> X \<sigma> \<tau> \<longleftrightarrow> ad_agr_sets (fv_fo_fmla \<phi>) (SP \<phi>) X \<sigma> \<tau>"

lemma ad_agr_sets_restrict:
  "ad_agr_sets (set (fv_fo_fmla_list \<phi>)) (set (fv_fo_fmla_list \<phi>)) AD \<sigma> \<tau> \<Longrightarrow> ad_agr \<phi> AD \<sigma> \<tau>"
  using sp_equiv_mono SP_fv
  unfolding fv_fo_fmla_list_set
  by (auto simp: ad_agr_sets_def ad_agr_def) blast

lemma finite_Inl: "finite X \<Longrightarrow> finite (Inl -` X)"
  using finite_vimageI[of X Inl]
  by (auto simp: vimage_def)

lemma ex_out:
  assumes "finite X"
  shows "\<exists>k. k \<notin> X \<and> k < Suc (card X)"
  using card_mono[OF assms, of "{..<Suc (card X)}"]
  by auto

lemma extend_\<tau>:
  assumes "ad_agr_sets (FV - {n}) (S - {n}) X \<sigma> \<tau>" "S \<subseteq> FV" "finite S" "\<tau> ` (FV - {n}) \<subseteq> Z"
    "Inl ` X \<union> Inr ` {..<max 1 (card (Inr -` \<tau> ` (S - {n})) + (if n \<in> S then 1 else 0))} \<subseteq> Z"
  shows "\<exists>k \<in> Z. ad_agr_sets FV S X (\<sigma>(n := x)) (\<tau>(n := k))"
proof (cases "n \<in> S")
  case True
  note n_in_S = True
  show ?thesis
  proof (cases "x \<in> Inl ` X")
    case True
    show ?thesis
      using assms n_in_S True
      apply (auto simp: ad_agr_sets_def sp_equiv_def pairwise_def intro!: bexI[of _ "x"])
      unfolding ad_equiv_pair.simps
         apply (metis True insert_Diff insert_iff subsetD)+
      done
  next
    case False
    note \<sigma>_n_not_Inl = False
    show ?thesis
    proof (cases "\<exists>m \<in> S - {n}. x = \<sigma> m")
      case True
      obtain m where m_def: "m \<in> S - {n}" "x = \<sigma> m"
        using True
        by auto
      have \<tau>_m_in: "\<tau> m \<in> Z"
        using assms m_def
        by auto
      show ?thesis
        using assms n_in_S \<sigma>_n_not_Inl True m_def
        by (auto simp: ad_agr_sets_def sp_equiv_def pairwise_def intro!: bexI[of _ "\<tau> m"])
    next
      case False
      have out: "x \<notin> \<sigma> ` (S - {n})"
        using False
        by auto
      have fin: "finite (Inr -` \<tau> ` (S - {n}))"
        using assms(3)
        by (simp add: finite_vimageI)
      obtain k where k_def: "Inr k \<notin> \<tau> ` (S - {n})" "k < Suc (card (Inr -` \<tau> ` (S - {n})))"
        using ex_out[OF fin] True
        by auto
      show ?thesis
        using assms n_in_S \<sigma>_n_not_Inl out k_def assms(5)
        apply (auto simp: ad_agr_sets_def sp_equiv_def pairwise_def intro!: bexI[of _ "Inr k"])
        unfolding ad_equiv_pair.simps
         apply fastforce
        apply (metis image_eqI insertE insert_Diff)
        done
    qed
  qed
next
  case False
  show ?thesis
  proof (cases "x \<in> Inl ` X")
    case x_in: True
    then show ?thesis
      using assms False
      by (auto simp: ad_agr_sets_def sp_equiv_def pairwise_def intro!: bexI[of _ "x"])
  next
    case x_out: False
    then show ?thesis
      using assms False
      apply (auto simp: ad_agr_sets_def sp_equiv_def pairwise_def intro!: bexI[of _ "Inr 0"])
      unfolding ad_equiv_pair.simps
      apply fastforce
      done
  qed
qed

lemma esat_Pred:
  assumes "ad_agr_sets FV S (\<Union>(set ` X)) \<sigma> \<tau>" "fv_fo_terms_set ts \<subseteq> FV" "\<sigma> \<odot>e ts \<in> map Inl ` X"
    "t \<in> set ts"
  shows "\<sigma> \<cdot>e t = \<tau> \<cdot>e t"
proof (cases t)
  case (Var n)
  obtain vs where vs_def: "\<sigma> \<odot>e ts = map Inl vs" "vs \<in> X"
    using assms(3)
    by auto
  have "\<sigma> n \<in> set (\<sigma> \<odot>e ts)"
    using assms(4)
    by (force simp: eval_eterms_def Var)
  then have "\<sigma> n \<in> Inl ` \<Union> (set ` X)"
    using vs_def(2)
    unfolding vs_def(1)
    by auto
  moreover have "n \<in> FV"
    using assms(2,4)
    by (fastforce simp: Var fv_fo_terms_set_def)
  ultimately show ?thesis
    using assms(1)
    unfolding ad_equiv_pair.simps ad_agr_sets_def Var
    by fastforce
qed auto

lemma sp_equiv_list_fv:
  assumes "(\<And>i. i \<in> fv_fo_terms_set ts \<Longrightarrow> ad_equiv_pair X (\<sigma> i, \<tau> i))"
    "\<Union>(set_fo_term ` set ts) \<subseteq> X" "sp_equiv \<sigma> \<tau> (fv_fo_terms_set ts)"
  shows "sp_equiv_list (map ((\<cdot>e) \<sigma>) ts) (map ((\<cdot>e) \<tau>) ts)"
  using assms
proof (induction ts)
  case (Cons t ts)
  have ind: "sp_equiv_list (map ((\<cdot>e) \<sigma>) ts) (map ((\<cdot>e) \<tau>) ts)"
    using Cons
    by (auto simp: fv_fo_terms_set_def sp_equiv_def pairwise_def)
  show ?case
  proof (cases t)
    case (Const c)
    have c_X: "c \<in> X"
      using Cons(3)
      by (auto simp: Const)
    have fv_t: "fv_fo_term_set t = {}"
      by (auto simp: Const)
    have "t' \<in> set ts \<Longrightarrow> sp_equiv_pair (\<sigma> \<cdot>e t, \<tau> \<cdot>e t) (\<sigma> \<cdot>e t', \<tau> \<cdot>e t')" for t'
      using c_X Const Cons(2)
      apply (cases t')
       apply (auto simp: fv_fo_terms_set_def)
      unfolding ad_equiv_pair.simps
      by (metis Cons(2) ad_equiv_pair.simps fv_fo_terms_setI image_insert insert_iff list.set(2)
          mk_disjoint_insert)+
    then show "sp_equiv_list (map ((\<cdot>e) \<sigma>) (t # ts)) (map ((\<cdot>e) \<tau>) (t # ts))"
      using ind pairwise_insert[of sp_equiv_pair "(\<sigma> \<cdot>e t, \<tau> \<cdot>e t)"]
      unfolding sp_equiv_list_def set_zip_map
      by (auto simp: sp_equiv_pair_comm fv_fo_terms_set_def fv_t)
  next
    case (Var n)
    have ad_n: "ad_equiv_pair X (\<sigma> n, \<tau> n)"
      using Cons(2)
      by (auto simp: fv_fo_terms_set_def Var)
    have sp_equiv_Var: "\<And>n'. Var n' \<in> set ts \<Longrightarrow> sp_equiv_pair (\<sigma> n, \<tau> n) (\<sigma> n', \<tau> n')"
      using Cons(4)
      by (auto simp: sp_equiv_def pairwise_def fv_fo_terms_set_def Var)
    have "t' \<in> set ts \<Longrightarrow> sp_equiv_pair (\<sigma> \<cdot>e t, \<tau> \<cdot>e t) (\<sigma> \<cdot>e t', \<tau> \<cdot>e t')" for t'
      using Cons(2,3) sp_equiv_Var  
      apply (cases t')
       apply (auto simp: Var)
       apply (metis SUP_le_iff ad_equiv_pair.simps ad_n fo_term.set_intros imageI subset_eq)
      apply (metis SUP_le_iff ad_equiv_pair.simps ad_n fo_term.set_intros imageI subset_eq)
      done
    then show ?thesis
      using ind pairwise_insert[of sp_equiv_pair "(\<sigma> \<cdot>e t, \<tau> \<cdot>e t)" "(\<lambda>n. (\<sigma> \<cdot>e n, \<tau> \<cdot>e n)) ` set ts"]
      unfolding sp_equiv_list_def set_zip_map
      by (auto simp: sp_equiv_pair_comm)
  qed
qed (auto simp: sp_equiv_def sp_equiv_list_def fv_fo_terms_set_def)

lemma esat_Pred_inf:
  assumes "fv_fo_terms_set ts \<subseteq> FV" "fv_fo_terms_set ts \<subseteq> S"
    "ad_agr_sets FV S AD \<sigma> \<tau>" "ad_agr_list AD (\<sigma> \<odot>e ts) vs"
    "\<Union>(set_fo_term ` set ts) \<subseteq> AD"
  shows "ad_agr_list AD (\<tau> \<odot>e ts) vs"
proof -
  have sp: "sp_equiv \<sigma> \<tau> (fv_fo_terms_set ts)"
    using assms(2,3) sp_equiv_mono
    unfolding ad_agr_sets_def
    by auto
  have "(\<And>i. i \<in> fv_fo_terms_set ts \<Longrightarrow> ad_equiv_pair AD (\<sigma> i, \<tau> i))"
    using assms(1,3)
    by (auto simp: ad_agr_sets_def)
  then have "sp_equiv_list (map ((\<cdot>e) \<sigma>) ts) (map ((\<cdot>e) \<tau>) ts)"
    using sp_equiv_list_fv[OF _ assms(5) sp]
    by auto
  moreover have "t \<in> set ts \<Longrightarrow> \<forall>i\<in>fv_fo_terms_set ts. ad_equiv_pair AD (\<sigma> i, \<tau> i) \<Longrightarrow> sp_equiv \<sigma> \<tau> S \<Longrightarrow> ad_equiv_pair AD (\<sigma> \<cdot>e t, \<tau> \<cdot>e t)" for t
    by (cases t) (auto simp: ad_equiv_pair.simps intro!: fv_fo_terms_setI)
  ultimately have ad_agr_list:
    "ad_agr_list AD (\<sigma> \<odot>e ts) (\<tau> \<odot>e ts)"
    unfolding eval_eterms_def ad_agr_list_def ad_equiv_list_link[symmetric]
    using assms(1,3)
    by (auto simp: ad_agr_sets_def)
  show ?thesis
    by (rule ad_agr_list_comm[OF ad_agr_list_trans[OF ad_agr_list_comm[OF assms(4)] ad_agr_list]])
qed

type_synonym ('a, 'c) fo_t = "'a set \<times> nat \<times> ('a + 'c) table"

fun esat :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> ('a + nat) val \<Rightarrow> ('a + nat) set \<Rightarrow> bool" where
  "esat (Pred r ts) I \<sigma> X \<longleftrightarrow> \<sigma> \<odot>e ts \<in> map Inl ` I (r, length ts)"
| "esat (Bool b) I \<sigma> X \<longleftrightarrow> b"
| "esat (Eqa t t') I \<sigma> X \<longleftrightarrow> \<sigma> \<cdot>e t = \<sigma> \<cdot>e t'"
| "esat (Neg \<phi>) I \<sigma> X \<longleftrightarrow> \<not>esat \<phi> I \<sigma> X"
| "esat (Conj \<phi> \<psi>) I \<sigma> X \<longleftrightarrow> esat \<phi> I \<sigma> X \<and> esat \<psi> I \<sigma> X"
| "esat (Disj \<phi> \<psi>) I \<sigma> X \<longleftrightarrow> esat \<phi> I \<sigma> X \<or> esat \<psi> I \<sigma> X"
| "esat (Exists n \<phi>) I \<sigma> X \<longleftrightarrow> (\<exists>x \<in> X. esat \<phi> I (\<sigma>(n := x)) X)"
| "esat (Forall n \<phi>) I \<sigma> X \<longleftrightarrow> (\<forall>x \<in> X. esat \<phi> I (\<sigma>(n := x)) X)"

fun sz_fmla :: "('a, 'b) fo_fmla \<Rightarrow> nat" where
  "sz_fmla (Neg \<phi>) = Suc (sz_fmla \<phi>)"
| "sz_fmla (Conj \<phi> \<psi>) = Suc (sz_fmla \<phi> + sz_fmla \<psi>)"
| "sz_fmla (Disj \<phi> \<psi>) = Suc (sz_fmla \<phi> + sz_fmla \<psi>)"
| "sz_fmla (Exists n \<phi>) = Suc (sz_fmla \<phi>)"
| "sz_fmla (Forall n \<phi>) = Suc (Suc (Suc (Suc (sz_fmla \<phi>))))"
| "sz_fmla _ = 0"

lemma sz_fmla_induct[case_names Pred Bool Eqa Neg Conj Disj Exists Forall]:
  "(\<And>r ts. P (Pred r ts)) \<Longrightarrow> (\<And>b. P (Bool b)) \<Longrightarrow>
  (\<And>t t'. P (Eqa t t')) \<Longrightarrow> (\<And>\<phi>. P \<phi> \<Longrightarrow> P (Neg \<phi>)) \<Longrightarrow>
  (\<And>\<phi> \<psi>. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Conj \<phi> \<psi>)) \<Longrightarrow> (\<And>\<phi> \<psi>. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Disj \<phi> \<psi>)) \<Longrightarrow>
  (\<And>n \<phi>. P \<phi> \<Longrightarrow> P (Exists n \<phi>)) \<Longrightarrow> (\<And>n \<phi>. P (Exists n (Neg \<phi>)) \<Longrightarrow> P (Forall n \<phi>)) \<Longrightarrow> P \<phi>"
proof (induction "sz_fmla \<phi>" arbitrary: \<phi> rule: nat_less_induct)
  case 1
  have IH: "\<And>\<psi>. sz_fmla \<psi> < sz_fmla \<phi> \<Longrightarrow> P \<psi>"
    using 1
    by auto
  then show ?case
    using 1(2,3,4,5,6,7,8,9)
    by (cases \<phi>) auto
qed

lemma esat_fv_cong: "(\<And>n. n \<in> fv_fo_fmla \<phi> \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow> esat \<phi> I \<sigma> X \<longleftrightarrow> esat \<phi> I \<sigma>' X"
proof (induction \<phi> arbitrary: \<sigma> \<sigma>' rule: sz_fmla_induct)
  case (Pred r ts)
  then show ?case
    by (auto simp: eval_eterms_def fv_fo_terms_set_def)
       (smt comp_apply eval_eterm_cong fv_fo_term_set_cong image_insert insertCI map_eq_conv
        mk_disjoint_insert)+
next
  case (Eqa t t')
  then show ?case
    by (cases t; cases t') auto
next
  case (Neg \<phi>)
  show ?case
    using Neg(1)[of \<sigma> \<sigma>'] Neg(2) by auto
next
  case (Conj \<phi>1 \<phi>2)
  show ?case
    using Conj(1,2)[of \<sigma> \<sigma>'] Conj(3) by auto
next
  case (Disj \<phi>1 \<phi>2)
  show ?case
    using Disj(1,2)[of \<sigma> \<sigma>'] Disj(3) by auto
next
  case (Exists n \<phi>)
  show ?case
  proof (rule iffI)
    assume "esat (Exists n \<phi>) I \<sigma> X"
    then obtain x where x_def: "x \<in> X" "esat \<phi> I (\<sigma>(n := x)) X"
      by auto
    from x_def(2) have "esat \<phi> I (\<sigma>'(n := x)) X"
      using Exists(1)[of "\<sigma>(n := x)" "\<sigma>'(n := x)"] Exists(2) by fastforce
    with x_def(1) show "esat (Exists n \<phi>) I \<sigma>' X"
      by auto
  next
    assume "esat (Exists n \<phi>) I \<sigma>' X"
    then obtain x where x_def: "x \<in> X" "esat \<phi> I (\<sigma>'(n := x)) X"
      by auto
    from x_def(2) have "esat \<phi> I (\<sigma>(n := x)) X"
      using Exists(1)[of "\<sigma>(n := x)" "\<sigma>'(n := x)"] Exists(2) by fastforce
    with x_def(1) show "esat (Exists n \<phi>) I \<sigma> X"
      by auto
  qed
next
  case (Forall n \<phi>)
  then show ?case
    by auto
qed auto

fun ad_terms :: "('a fo_term) list \<Rightarrow> 'a set" where
  "ad_terms ts = \<Union>(set (map set_fo_term ts))"

fun act_edom :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> 'a set" where
  "act_edom (Pred r ts) I = ad_terms ts \<union> \<Union>(set ` I (r, length ts))"
| "act_edom (Bool b) I = {}"
| "act_edom (Eqa t t') I = set_fo_term t \<union> set_fo_term t'"
| "act_edom (Neg \<phi>) I = act_edom \<phi> I"
| "act_edom (Conj \<phi> \<psi>) I = act_edom \<phi> I \<union> act_edom \<psi> I"
| "act_edom (Disj \<phi> \<psi>) I = act_edom \<phi> I \<union> act_edom \<psi> I"
| "act_edom (Exists n \<phi>) I = act_edom \<phi> I"
| "act_edom (Forall n \<phi>) I = act_edom \<phi> I"

lemma finite_act_edom: "wf_fo_intp \<phi> I \<Longrightarrow> finite (act_edom \<phi> I)"
  using finite_Inl
  by (induction \<phi> I rule: wf_fo_intp.induct)
     (auto simp: finite_set_fo_term vimage_def)

fun fo_adom :: "('a, 'c) fo_t \<Rightarrow> 'a set" where
  "fo_adom (AD, n, X) = AD"

theorem main: "ad_agr \<phi> AD \<sigma> \<tau> \<Longrightarrow> act_edom \<phi> I \<subseteq> AD \<Longrightarrow>
  Inl ` AD \<union> Inr ` {..<d \<phi>} \<subseteq> X \<Longrightarrow> \<tau> ` fv_fo_fmla \<phi> \<subseteq> X \<Longrightarrow>
  esat \<phi> I \<sigma> UNIV \<longleftrightarrow> esat \<phi> I \<tau> X"
proof (induction \<phi> arbitrary: \<sigma> \<tau> rule: sz_fmla_induct)
  case (Pred r ts)
  have fv_sub: "fv_fo_terms_set ts \<subseteq> fv_fo_fmla (Pred r ts)"
    by auto
  have sub_AD: "\<Union>(set ` I (r, length ts)) \<subseteq> AD"
    using Pred(2)
    by auto
  show ?case
    unfolding esat.simps
  proof (rule iffI)
    assume assm: "\<sigma> \<odot>e ts \<in> map Inl ` I (r, length ts)"
    have "\<sigma> \<odot>e ts = \<tau> \<odot>e ts"
      using esat_Pred[OF ad_agr_sets_mono[OF sub_AD Pred(1)[unfolded ad_agr_def]]
            fv_sub assm]
      by (auto simp: eval_eterms_def)
    with assm show "\<tau> \<odot>e ts \<in> map Inl ` I (r, length ts)"
      by auto
  next
    assume assm: "\<tau> \<odot>e ts \<in> map Inl ` I (r, length ts)"
    have "\<tau> \<odot>e ts = \<sigma> \<odot>e ts"
      using esat_Pred[OF ad_agr_sets_comm[OF ad_agr_sets_mono[OF
            sub_AD Pred(1)[unfolded ad_agr_def]]] fv_sub assm]
      by (auto simp: eval_eterms_def)
    with assm show "\<sigma> \<odot>e ts \<in> map Inl ` I (r, length ts)"
      by auto
  qed
next
  case (Eqa x1 x2)
  show ?case
  proof (cases x1; cases x2)
    fix c c'
    assume "x1 = Const c" "x2 = Const c'"
    with Eqa show ?thesis
      by auto
  next
    fix c m'
    assume assms: "x1 = Const c" "x2 = Var m'"
    with Eqa(1,2) have "\<sigma> m' = Inl c \<longleftrightarrow> \<tau> m' = Inl c"
      apply (auto simp: ad_agr_def ad_agr_sets_def)
      unfolding ad_equiv_pair.simps
      by fastforce+
    with assms show ?thesis
      by fastforce
  next
    fix m c'
    assume assms: "x1 = Var m" "x2 = Const c'"
    with Eqa(1,2) have "\<sigma> m = Inl c' \<longleftrightarrow> \<tau> m = Inl c'"
      apply (auto simp: ad_agr_def ad_agr_sets_def)
      unfolding ad_equiv_pair.simps
      by fastforce+
    with assms show ?thesis
      by auto
  next
    fix m m'
    assume assms: "x1 = Var m" "x2 = Var m'"
    with Eqa(1,2) have "\<sigma> m = \<sigma> m' \<longleftrightarrow> \<tau> m = \<tau> m'"
      by (auto simp: ad_agr_def ad_agr_sets_def sp_equiv_def pairwise_def split: if_splits)
    with assms show ?thesis
      by auto
  qed
next
  case (Neg \<phi>)
  from Neg(2) have "ad_agr \<phi> AD \<sigma> \<tau>"
    by (auto simp: ad_agr_def)
  with Neg show ?case
    by auto
next
  case (Conj \<phi>1 \<phi>2)
  have aux: "ad_agr \<phi>1 AD \<sigma> \<tau>" "ad_agr \<phi>2 AD \<sigma> \<tau>"
    "Inl ` AD \<union> Inr ` {..<d \<phi>1} \<subseteq> X" "Inl ` AD \<union> Inr ` {..<d \<phi>2} \<subseteq> X"
    "\<tau> ` fv_fo_fmla \<phi>1 \<subseteq> X" "\<tau> ` fv_fo_fmla \<phi>2 \<subseteq> X"
    using Conj(3,5,6)
    by (auto simp: ad_agr_def ad_agr_sets_def sp_equiv_def pairwise_def)
  show ?case
    using Conj(1)[OF aux(1) _ aux(3) aux(5)] Conj(2)[OF aux(2) _ aux(4) aux(6)] Conj(4)
    by auto
next
  case (Disj \<phi>1 \<phi>2)
  have aux: "ad_agr \<phi>1 AD \<sigma> \<tau>" "ad_agr \<phi>2 AD \<sigma> \<tau>"
    "Inl ` AD \<union> Inr ` {..<d \<phi>1} \<subseteq> X" "Inl ` AD \<union> Inr ` {..<d \<phi>2} \<subseteq> X"
    "\<tau> ` fv_fo_fmla \<phi>1 \<subseteq> X" "\<tau> ` fv_fo_fmla \<phi>2 \<subseteq> X"
    using Disj(3,5,6)
    by (auto simp: ad_agr_def ad_agr_sets_def sp_equiv_def pairwise_def)
  show ?case
    using Disj(1)[OF aux(1) _ aux(3) aux(5)] Disj(2)[OF aux(2) _ aux(4) aux(6)] Disj(4)
    by auto
next
  case (Exists m \<phi>)
  show ?case
  proof (rule iffI)
    assume "esat (Exists m \<phi>) I \<sigma> UNIV"
    then obtain x where assm: "esat \<phi> I (\<sigma>(m := x)) UNIV"
      by auto
    have "m \<in> SP \<phi> \<Longrightarrow> Suc (card (Inr -` \<tau> ` (SP \<phi> - {m}))) \<le> card (SP \<phi>)"
      by (metis Diff_insert_absorb card_image card_le_Suc_iff finite_Diff finite_SP
          image_vimage_subset inj_Inr mk_disjoint_insert surj_card_le)
    moreover have "card (Inr -` \<tau> ` SP \<phi>) \<le> card (SP \<phi>)"
      by (metis card_image finite_SP image_vimage_subset inj_Inr surj_card_le)
    ultimately have "max 1 (card (Inr -` \<tau> ` (SP \<phi> - {m})) + (if m \<in> SP \<phi> then 1 else 0)) \<le> d \<phi>"
      using d_pos card_SP_d[of \<phi>]
      by auto
    then have "\<exists>x' \<in> X. ad_agr \<phi> AD (\<sigma>(m := x)) (\<tau>(m := x'))"
      using extend_\<tau>[OF Exists(2)[unfolded ad_agr_def fv_fo_fmla.simps SP.simps]
            SP_fv[of \<phi>] finite_SP Exists(5)[unfolded fv_fo_fmla.simps]]
            Exists(4)
      by (force simp: ad_agr_def)
    then obtain x' where x'_def: "x' \<in> X" "ad_agr \<phi> AD (\<sigma>(m := x)) (\<tau>(m := x'))"
      by auto
    from Exists(5) have "\<tau>(m := x') ` fv_fo_fmla \<phi> \<subseteq> X"
      using x'_def(1) by fastforce
    then have "esat \<phi> I (\<tau>(m := x')) X"
      using Exists x'_def(1,2) assm
      by fastforce
    with x'_def show "esat (Exists m \<phi>) I \<tau> X"
      by auto
  next
    assume "esat (Exists m \<phi>) I \<tau> X"
    then obtain z where assm: "z \<in> X" "esat \<phi> I (\<tau>(m := z)) X"
      by auto
    have ad_agr: "ad_agr_sets (fv_fo_fmla \<phi> - {m}) (SP \<phi> - {m}) AD \<tau> \<sigma>"
      using Exists(2)[unfolded ad_agr_def fv_fo_fmla.simps SP.simps]
      by (rule ad_agr_sets_comm)
    have "\<exists>x. ad_agr \<phi> AD (\<sigma>(m := x)) (\<tau>(m := z))"
      using extend_\<tau>[OF ad_agr SP_fv[of \<phi>] finite_SP subset_UNIV subset_UNIV] ad_agr_sets_comm
      unfolding ad_agr_def
      by fastforce
    then obtain x where x_def: "ad_agr \<phi> AD (\<sigma>(m := x)) (\<tau>(m := z))"
      by auto
    have "\<tau>(m := z) ` fv_fo_fmla (Exists m \<phi>) \<subseteq> X"
      using Exists
      by fastforce
    with x_def have "esat \<phi> I (\<sigma>(m := x)) UNIV"
      using Exists assm
      by fastforce
    then show "esat (Exists m \<phi>) I \<sigma> UNIV"
      by auto
  qed
next
  case (Forall n \<phi>)
  have unfold: "act_edom (Forall n \<phi>) I = act_edom (Exists n (Neg \<phi>)) I"
    "Inl ` AD \<union> Inr ` {..<d (Forall n \<phi>)} = Inl ` AD \<union> Inr ` {..<d (Exists n (Neg \<phi>))}"
    "fv_fo_fmla (Forall n \<phi>) = fv_fo_fmla (Exists n (Neg \<phi>))"
    by auto
  have pred: "ad_agr (Exists n (Neg \<phi>)) AD \<sigma> \<tau>"
    using Forall(2)
    by (auto simp: ad_agr_def)
  show ?case
    using Forall(1)[OF pred Forall(3,4,5)[unfolded unfold]]
    by auto
qed auto

lemma main_cor_inf:
  assumes "ad_agr \<phi> AD \<sigma> \<tau>" "act_edom \<phi> I \<subseteq> AD" "d \<phi> \<le> n"
    "\<tau> ` fv_fo_fmla \<phi> \<subseteq> Inl ` AD \<union> Inr ` {..<n}"
  shows "esat \<phi> I \<sigma> UNIV \<longleftrightarrow> esat \<phi> I \<tau> (Inl ` AD \<union> Inr ` {..<n})"
proof -
  show ?thesis
    using main[OF assms(1,2) _ assms(4)] assms(3)
    by fastforce
qed

lemma esat_UNIV_cong:
  fixes \<sigma> :: "nat \<Rightarrow> 'a + nat"
  assumes "ad_agr \<phi> AD \<sigma> \<tau>" "act_edom \<phi> I \<subseteq> AD"
  shows "esat \<phi> I \<sigma> UNIV \<longleftrightarrow> esat \<phi> I \<tau> UNIV"
proof -
  show ?thesis
    using main[OF assms(1,2) subset_UNIV subset_UNIV]
    by auto
qed

lemma esat_UNIV_ad_agr_list:
  fixes \<sigma> :: "nat \<Rightarrow> 'a + nat"
  assumes "ad_agr_list AD (map \<sigma> (fv_fo_fmla_list \<phi>)) (map \<tau> (fv_fo_fmla_list \<phi>))"
    "act_edom \<phi> I \<subseteq> AD"
  shows "esat \<phi> I \<sigma> UNIV \<longleftrightarrow> esat \<phi> I \<tau> UNIV"
  using esat_UNIV_cong[OF iffD2[OF ad_agr_def, OF ad_agr_sets_mono'[OF SP_fv],
        OF iffD2[OF ad_agr_list_link, OF assms(1), unfolded fv_fo_fmla_list_set]] assms(2)] .

fun fo_rep :: "('a, 'c) fo_t \<Rightarrow> 'a table" where
  "fo_rep (AD, n, X) = {ts. \<exists>ts' \<in> X. ad_agr_list AD (map Inl ts) ts'}"

lemma sat_esat_conv:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes fin: "wf_fo_intp \<phi> I"
  shows "sat \<phi> I \<sigma> \<longleftrightarrow> esat \<phi> I (Inl \<circ> \<sigma> :: nat \<Rightarrow> 'a + nat) UNIV"
  using assms
proof (induction \<phi> arbitrary: I \<sigma> rule: sz_fmla_induct)
  case (Pred r ts)
  show ?case
    unfolding sat.simps esat.simps comp_def[symmetric] eval_terms_eterms[symmetric]
    by auto
next
  case (Eqa t t')
  show ?case
    by (cases t; cases t') auto
next
  case (Exists n \<phi>)
  show ?case
  proof (rule iffI)
    assume "sat (Exists n \<phi>) I \<sigma>"
    then obtain x where x_def: "esat \<phi> I (Inl \<circ> \<sigma>(n := x)) UNIV"
      using Exists
      by fastforce
    have Inl_unfold: "Inl \<circ> \<sigma>(n := x) = (Inl \<circ> \<sigma>)(n := Inl x)"
      by auto
    show "esat (Exists n \<phi>) I (Inl \<circ> \<sigma>) UNIV"
      using x_def
      unfolding Inl_unfold
      by auto
  next
    assume "esat (Exists n \<phi>) I (Inl \<circ> \<sigma>) UNIV"
    then obtain x where x_def: "esat \<phi> I ((Inl \<circ> \<sigma>)(n := x)) UNIV"
      by auto
    show "sat (Exists n \<phi>) I \<sigma>"
    proof (cases x)
      case (Inl a)
      have Inl_unfold: "(Inl \<circ> \<sigma>)(n := x) = Inl \<circ> \<sigma>(n := a)"
        by (auto simp: Inl)
      show ?thesis
        using x_def[unfolded Inl_unfold] Exists
        by fastforce
    next
      case (Inr b)
      obtain c where c_def: "c \<notin> act_edom \<phi> I \<union> \<sigma> ` fv_fo_fmla \<phi>"
        using arb_element finite_act_edom[OF Exists(2), simplified] finite_fv_fo_fmla
        by (metis finite_Un finite_imageI)
      have wf_local: "wf_fo_intp \<phi> I"
        using Exists(2)
        by auto
      have "(a, a') \<in> set (zip (map (\<lambda>x. if x = n then Inr b else (Inl \<circ> \<sigma>) x) (fv_fo_fmla_list \<phi>))
        (map (\<lambda>a. Inl (if a = n then c else \<sigma> a)) (fv_fo_fmla_list \<phi>))) \<Longrightarrow>
        ad_equiv_pair (act_edom \<phi> I) (a, a')" for a a'
        using c_def
        by (cases a; cases a') (auto simp: set_zip ad_equiv_pair.simps split: if_splits)
      then have "sat \<phi> I (\<sigma>(n := c))"
        using c_def[folded fv_fo_fmla_list_set]
        by (auto simp: ad_agr_list_def ad_equiv_list_def fun_upd_def sp_equiv_list_def pairwise_def set_zip split: if_splits
            intro!: Exists(1)[OF wf_local, THEN iffD2, OF esat_UNIV_ad_agr_list[OF _ subset_refl, THEN iffD1, OF _ x_def[unfolded Inr]]])
      then show ?thesis
        by auto
    qed
  qed
next
  case (Forall n \<phi>)
  show ?case
    using Forall(1)[of I \<sigma>] Forall(2)
    by auto
qed auto

lemma sat_ad_agr_list:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
    and J :: "(('a, nat) fo_t, 'b) fo_intp"
  assumes "wf_fo_intp \<phi> I"
    "ad_agr_list AD (map (Inl \<circ> \<sigma> :: nat \<Rightarrow> 'a + nat) (fv_fo_fmla_list \<phi>))
      (map (Inl \<circ> \<tau>) (fv_fo_fmla_list \<phi>))" "act_edom \<phi> I \<subseteq> AD"
  shows "sat \<phi> I \<sigma> \<longleftrightarrow> sat \<phi> I \<tau>"
  using esat_UNIV_ad_agr_list[OF assms(2,3)] sat_esat_conv[OF assms(1)]
  by auto

definition nfv :: "('a, 'b) fo_fmla \<Rightarrow> nat" where
  "nfv \<phi> = length (fv_fo_fmla_list \<phi>)"

lemma nfv_card: "nfv \<phi> = card (fv_fo_fmla \<phi>)"
proof -
  have "distinct (fv_fo_fmla_list \<phi>)"
    using sorted_distinct_fv_list
    by auto
  then have "length (fv_fo_fmla_list \<phi>) = card (set (fv_fo_fmla_list \<phi>))"
    using distinct_card by fastforce
  then show ?thesis
    unfolding fv_fo_fmla_list_set by (auto simp: nfv_def)
qed

fun rremdups :: "'a list \<Rightarrow> 'a list" where
  "rremdups [] = []"
| "rremdups (x # xs) = x # rremdups (filter ((\<noteq>) x) xs)"

lemma filter_rremdups_filter: "filter P (rremdups (filter Q xs)) =
  rremdups (filter (\<lambda>x. P x \<and> Q x) xs)"
  apply (induction xs arbitrary: Q)
   apply auto
  by metis

lemma filter_rremdups: "filter P (rremdups xs) = rremdups (filter P xs)"
  using filter_rremdups_filter[where Q="\<lambda>_. True"]
  by auto

lemma filter_take: "\<exists>j. filter P (take i xs) = take j (filter P xs)"
  apply (induction xs arbitrary: i)
   apply (auto)
   apply (metis filter.simps(1) filter.simps(2) take_Cons' take_Suc_Cons)
  apply (metis filter.simps(2) take0 take_Cons')
  done

lemma rremdups_take: "\<exists>j. rremdups (take i xs) = take j (rremdups xs)"
proof (induction xs arbitrary: i)
  case (Cons x xs)
  show ?case
  proof (cases i)
    case (Suc n)
    obtain j where j_def: "rremdups (take n xs) = take j (rremdups xs)"
      using Cons by auto
    obtain j' where j'_def: "filter ((\<noteq>) x) (take j (rremdups xs)) =
      take j' (filter ((\<noteq>) x) (rremdups xs))"
      using filter_take
      by blast
    show ?thesis
      by (auto simp: Suc filter_rremdups[symmetric] j_def j'_def intro: exI[of _ "Suc j'"])
  qed (auto simp add: take_Cons')
qed auto

lemma rremdups_app: "rremdups (xs @ [x]) = rremdups xs @ (if x \<in> set xs then [] else [x])"
  apply (induction xs)
   apply auto
   apply (smt filter.simps(1) filter.simps(2) filter_append filter_rremdups)+
  done

lemma rremdups_set: "set (rremdups xs) = set xs"
  by (induction xs) (auto simp: filter_rremdups[symmetric])

lemma distinct_rremdups: "distinct (rremdups xs)"
proof (induction "length xs" arbitrary: xs rule: nat_less_induct)
  case 1
  then have IH: "\<And>m ys. length (ys :: 'a list) < length xs \<Longrightarrow> distinct (rremdups ys)"
    by auto
  show ?case
  proof (cases xs)
    case (Cons z zs)
    show ?thesis
      using IH
      by (auto simp: Cons rremdups_set le_imp_less_Suc)
  qed auto
qed

lemma length_rremdups: "length (rremdups xs) = card (set xs)"
  using distinct_card[OF distinct_rremdups]
  by (subst eq_commute) (auto simp: rremdups_set)

lemma set_map_filter_sum: "set (List.map_filter (case_sum Map.empty Some) xs) = Inr -` set xs"
  by (induction xs) (auto simp: List.map_filter_simps split: sum.splits)

definition nats :: "nat list \<Rightarrow> bool" where
  "nats ns = (ns = [0..<length ns])"

definition fo_nmlzd :: "'a set \<Rightarrow> ('a + nat) list \<Rightarrow> bool" where
  "fo_nmlzd AD xs \<longleftrightarrow> Inl -` set xs \<subseteq> AD \<and>
    (let ns = List.map_filter (case_sum Map.empty Some) xs in nats (rremdups ns))"

lemma fo_nmlzd_all_AD:
  assumes "set xs \<subseteq> Inl ` AD"
  shows "fo_nmlzd AD xs"
proof -
  have "List.map_filter (case_sum Map.empty Some) xs = []"
    using assms
    by (induction xs) (auto simp: List.map_filter_simps)
  then show ?thesis
    using assms
    by (auto simp: fo_nmlzd_def nats_def Let_def)
qed

lemma card_Inr_vimage_le_length: "card (Inr -` set xs) \<le> length xs"
proof -
  have "card (Inr -` set xs) \<le> card (set xs)"
    by (meson List.finite_set card_inj_on_le image_vimage_subset inj_Inr)
  moreover have "\<dots> \<le> length xs"
    by (rule card_length)
  finally show ?thesis .
qed

lemma fo_nmlzd_set:
  assumes "fo_nmlzd AD xs"
  shows "set xs = set xs \<inter> Inl ` AD \<union> Inr ` {..<min (length xs) (card (Inr -` set xs))}"
proof -
  have "Inl -` set xs \<subseteq> AD"
    using assms
    by (auto simp: fo_nmlzd_def)
  moreover have "Inr -` set xs = {..<card (Inr -` set xs)}"
    using assms
    by (auto simp: Let_def fo_nmlzd_def nats_def length_rremdups set_map_filter_sum rremdups_set
        dest!: arg_cong[of _ _ set])
  ultimately have "set xs = set xs \<inter> Inl ` AD \<union> Inr ` {..<card (Inr -` set xs)}"
    by auto (metis (no_types, lifting) UNIV_I UNIV_sum UnE image_iff subset_iff vimageI)
  then show ?thesis
    using card_Inr_vimage_le_length[of xs]
    by (metis min.absorb2)
qed

lemma map_filter_take: "\<exists>j. List.map_filter f (take i xs) = take j (List.map_filter f xs)"
  apply (induction xs arbitrary: i)
   apply (auto simp: List.map_filter_simps split: option.splits)
   apply (metis map_filter_simps(1) option.case(1) take0 take_Cons')
  apply (metis map_filter_simps(1) map_filter_simps(2) option.case(2) take_Cons' take_Suc_Cons)
  done

lemma fo_nmlzd_take: assumes "fo_nmlzd AD xs"
  shows "fo_nmlzd AD (take i xs)"
proof -
  have aux: "rremdups zs = [0..<length (rremdups zs)] \<Longrightarrow> rremdups (take j zs) =
    [0..<length (rremdups (take j zs))]" for j zs
    using rremdups_take[of j zs]
    by (auto simp add: min_def) (metis add_0 linorder_le_cases take_upt)
  show ?thesis
    using assms map_filter_take[of "case_sum Map.empty Some" i xs] set_take_subset
    using aux[where ?zs="List.map_filter (case_sum Map.empty Some) xs"]
    by (fastforce simp: fo_nmlzd_def vimage_def nats_def Let_def)
qed

lemma map_filter_app: "List.map_filter f (xs @ [x]) = List.map_filter f xs @
  (case f x of Some y \<Rightarrow> [y] | _ \<Rightarrow> [])"
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma fo_nmlzd_app_Inr: "Inr n \<notin> set xs \<Longrightarrow> Inr n' \<notin> set xs \<Longrightarrow> fo_nmlzd AD (xs @ [Inr n]) \<Longrightarrow>
  fo_nmlzd AD (xs @ [Inr n']) \<Longrightarrow> n = n'"
  by (auto simp: List.map_filter_simps fo_nmlzd_def nats_def Let_def map_filter_app
      rremdups_app set_map_filter_sum)

fun all_tuples :: "'c set \<Rightarrow> nat \<Rightarrow> 'c table" where
  "all_tuples xs 0 = {[]}"
| "all_tuples xs (Suc n) = \<Union>((\<lambda>as. (\<lambda>x. x # as) ` xs) ` (all_tuples xs n))"

definition nall_tuples :: "'a set \<Rightarrow> nat \<Rightarrow> ('a + nat) table" where
  "nall_tuples AD n = {zs \<in> all_tuples (Inl ` AD \<union> Inr ` {..<n}) n. fo_nmlzd AD zs}"

lemma all_tuples_finite: "finite xs \<Longrightarrow> finite (all_tuples xs n)"
  by (induction xs n rule: all_tuples.induct) auto

lemma nall_tuples_finite: "finite AD \<Longrightarrow> finite (nall_tuples AD n)"
  by (auto simp: nall_tuples_def all_tuples_finite)

lemma all_tuplesI: "length vs = n \<Longrightarrow> set vs \<subseteq> xs \<Longrightarrow> vs \<in> all_tuples xs n"
proof (induction xs n arbitrary: vs rule: all_tuples.induct)
  case (2 xs n)
  then obtain w ws where "vs = w # ws" "length ws = n" "set ws \<subseteq> xs" "w \<in> xs"
    by (metis Suc_length_conv contra_subsetD list.set_intros(1) order_trans set_subset_Cons)
  with 2(1) show ?case
    by auto
qed auto

lemma nall_tuplesI: "length vs = n \<Longrightarrow> fo_nmlzd AD vs \<Longrightarrow> vs \<in> nall_tuples AD n"
  using fo_nmlzd_set[of AD vs]
  by (auto simp: nall_tuples_def intro!: all_tuplesI)

lemma all_tuplesD: "vs \<in> all_tuples xs n \<Longrightarrow> length vs = n \<and> set vs \<subseteq> xs"
  by (induction xs n arbitrary: vs rule: all_tuples.induct) auto+

lemma all_tuples_setD: "vs \<in> all_tuples xs n \<Longrightarrow> set vs \<subseteq> xs"
  by (auto dest: all_tuplesD)

lemma nall_tuplesD: "vs \<in> nall_tuples AD n \<Longrightarrow>
  length vs = n \<and> set vs \<subseteq> Inl ` AD \<union> Inr ` {..<n} \<and> fo_nmlzd AD vs"
  by (auto simp: nall_tuples_def dest: all_tuplesD)

lemma all_tuples_set: "all_tuples xs n = {ys. length ys = n \<and> set ys \<subseteq> xs}"
proof (induction xs n rule: all_tuples.induct)
  case (2 xs n)
  show ?case
  proof (rule subset_antisym; rule subsetI)
    fix ys
    assume "ys \<in> all_tuples xs (Suc n)"
    then show "ys \<in> {ys. length ys = Suc n \<and> set ys \<subseteq> xs}"
      using 2 by auto
  next
    fix ys
    assume "ys \<in> {ys. length ys = Suc n \<and> set ys \<subseteq> xs}"
    then have assm: "length ys = Suc n" "set ys \<subseteq> xs"
      by auto
    then obtain z zs where zs_def: "ys = z # zs" "z \<in> xs" "length zs = n" "set zs \<subseteq> xs"
      by (cases ys) auto
    with 2 have "zs \<in> all_tuples xs n"
      by auto
    with zs_def(1,2) show "ys \<in> all_tuples xs (Suc n)"
      by auto
  qed
qed auto

lemma nall_tuples_set: "nall_tuples AD n = {ys. length ys = n \<and> fo_nmlzd AD ys}"
  using fo_nmlzd_set[of AD] card_Inr_vimage_le_length
  by (auto simp: nall_tuples_def all_tuples_set) (smt UnE nall_tuplesD nall_tuplesI subsetD)

fun pos :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "pos a [] = None"
| "pos a (x # xs) =
    (if a = x then Some 0 else (case pos a xs of Some n \<Rightarrow> Some (Suc n) | _ \<Rightarrow> None))"

lemma pos_set: "pos a xs = Some i \<Longrightarrow> a \<in> set xs"
  by (induction a xs arbitrary: i rule: pos.induct) (auto split: if_splits option.splits)

lemma pos_length: "pos a xs = Some i \<Longrightarrow> i < length xs"
  by (induction a xs arbitrary: i rule: pos.induct) (auto split: if_splits option.splits)

lemma pos_sound: "pos a xs = Some i \<Longrightarrow> i < length xs \<and> xs ! i = a"
  by (induction a xs arbitrary: i rule: pos.induct) (auto split: if_splits option.splits)

lemma pos_complete: "pos a xs = None \<Longrightarrow> a \<notin> set xs"
  by (induction a xs rule: pos.induct) (auto split: if_splits option.splits)

fun rem_nth :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rem_nth _ [] = []"
| "rem_nth 0 (x # xs) = xs"
| "rem_nth (Suc n) (x # xs) = x # rem_nth n xs"

lemma rem_nth_length: "i < length xs \<Longrightarrow> length (rem_nth i xs) = length xs - 1"
  by (induction i xs rule: rem_nth.induct) auto

lemma rem_nth_take_drop: "i < length xs \<Longrightarrow> rem_nth i xs = take i xs @ drop (Suc i) xs"
  by (induction i xs rule: rem_nth.induct) auto

lemma rem_nth_sound: "distinct xs \<Longrightarrow> pos n xs = Some i \<Longrightarrow>
  rem_nth i (map \<sigma> xs) = map \<sigma> (filter ((\<noteq>) n) xs)"
  apply (induction xs arbitrary: i)
   apply (auto simp: pos_set split: option.splits)
  by (metis (mono_tags, lifting) filter_True)

fun add_nth :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "add_nth 0 a xs = a # xs"
| "add_nth (Suc n) a zs = (case zs of x # xs \<Rightarrow> x # add_nth n a xs)"

lemma add_nth_length: "i \<le> length zs \<Longrightarrow> length (add_nth i z zs) = Suc (length zs)"
  by (induction i z zs rule: add_nth.induct) (auto split: list.splits)

lemma add_nth_take_drop: "i \<le> length zs \<Longrightarrow> add_nth i v zs = take i zs @ v # drop i zs"
  by (induction i v zs rule: add_nth.induct) (auto split: list.splits)

lemma add_nth_rem_nth_map: "distinct xs \<Longrightarrow> pos n xs = Some i \<Longrightarrow>
  add_nth i a (rem_nth i (map \<sigma> xs)) = map (\<sigma>(n := a)) xs"
  by (induction xs arbitrary: i) (auto simp: pos_set split: option.splits)

lemma add_nth_rem_nth_self: "i < length xs \<Longrightarrow> add_nth i (xs ! i) (rem_nth i xs) = xs"
  by (induction i xs rule: rem_nth.induct) auto

lemma rem_nth_add_nth: "i \<le> length zs \<Longrightarrow> rem_nth i (add_nth i z zs) = zs"
  by (induction i z zs rule: add_nth.induct) (auto split: list.splits)

fun merge :: "(nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list" where
  "merge [] mys = mys"
| "merge nxs [] = nxs"
| "merge ((n, x) # nxs) ((m, y) # mys) =
    (if n \<le> m then (n, x) # merge nxs ((m, y) # mys)
    else (m, y) # merge ((n, x) # nxs) mys)"

lemma merge_Nil2[simp]: "merge nxs [] = nxs"
  by (cases nxs) auto

lemma merge_length: "length (merge nxs mys) = length (map fst nxs @ map fst mys)"
  by (induction nxs mys rule: merge.induct) auto

lemma insort_aux_le: "\<forall>x\<in>set nxs. n \<le> fst x \<Longrightarrow> \<forall>x\<in>set mys. m \<le> fst x \<Longrightarrow> n \<le> m \<Longrightarrow>
  insort n (sort (map fst nxs @ m # map fst mys)) = n # sort (map fst nxs @ m # map fst mys)"
  by (induction nxs) (auto simp: insort_is_Cons insort_left_comm)

lemma insort_aux_gt: "\<forall>x\<in>set nxs. n \<le> fst x \<Longrightarrow> \<forall>x\<in>set mys. m \<le> fst x \<Longrightarrow> \<not> n \<le> m \<Longrightarrow>
  insort n (sort (map fst nxs @ m # map fst mys)) =
    m # insort n (sort (map fst nxs @ map fst mys))"
  apply (induction nxs)
   apply (auto simp: insort_is_Cons)
  by (metis dual_order.trans insort_key.simps(2) insort_left_comm)

lemma map_fst_merge: "sorted_distinct (map fst nxs) \<Longrightarrow> sorted_distinct (map fst mys) \<Longrightarrow>
  map fst (merge nxs mys) = sort (map fst nxs @ map fst mys)"
  by (induction nxs mys rule: merge.induct)
     (auto simp add: sorted_sort_id insort_is_Cons insort_aux_le insort_aux_gt)

lemma merge_map': "sorted_distinct (map fst nxs) \<Longrightarrow> sorted_distinct (map fst mys) \<Longrightarrow>
  fst ` set nxs \<inter> fst ` set mys = {} \<Longrightarrow>
  map snd nxs = map \<sigma> (map fst nxs) \<Longrightarrow> map snd mys = map \<sigma> (map fst mys) \<Longrightarrow>
  map snd (merge nxs mys) = map \<sigma> (sort (map fst nxs @ map fst mys))"
  by (induction nxs mys rule: merge.induct)
     (auto simp: sorted_sort_id insort_is_Cons insort_aux_le insort_aux_gt)

lemma merge_map: "sorted_distinct ns \<Longrightarrow> sorted_distinct ms \<Longrightarrow> set ns \<inter> set ms = {} \<Longrightarrow>
  map snd (merge (zip ns (map \<sigma> ns)) (zip ms (map \<sigma> ms))) = map \<sigma> (sort (ns @ ms))"
  using merge_map'[of "zip ns (map \<sigma> ns)" "zip ms (map \<sigma> ms)" \<sigma>]
  by auto (metis length_map list.set_map map_fst_zip)

fun fo_nmlz_rec :: "nat \<Rightarrow> ('a + nat \<rightharpoonup> nat) \<Rightarrow> 'a set \<Rightarrow>
  ('a + nat) list \<Rightarrow> ('a + nat) list" where
  "fo_nmlz_rec i m AD [] = []"
| "fo_nmlz_rec i m AD (Inl x # xs) = (if x \<in> AD then Inl x # fo_nmlz_rec i m AD xs else
    (case m (Inl x) of None \<Rightarrow> Inr i # fo_nmlz_rec (Suc i) (m(Inl x \<mapsto> i)) AD xs
    | Some j \<Rightarrow> Inr j # fo_nmlz_rec i m AD xs))"
| "fo_nmlz_rec i m AD (Inr n # xs) = (case m (Inr n) of None \<Rightarrow>
    Inr i # fo_nmlz_rec (Suc i) (m(Inr n \<mapsto> i)) AD xs
  | Some j \<Rightarrow> Inr j # fo_nmlz_rec i m AD xs)"

lemma fo_nmlz_rec_sound: "ran m \<subseteq> {..<i} \<Longrightarrow> filter ((\<le>) i) (rremdups
  (List.map_filter (case_sum Map.empty Some) (fo_nmlz_rec i m AD xs))) = ns \<Longrightarrow>
  ns = [i..<i + length ns]"
proof (induction i m AD xs arbitrary: ns rule: fo_nmlz_rec.induct)
  case (2 i m AD x xs)
  then show ?case
  proof (cases "x \<in> AD")
    case False
    show ?thesis
    proof (cases "m (Inl x)")
      case None
      have pred: "ran (m(Inl x \<mapsto> i)) \<subseteq> {..<Suc i}"
        using 2(4) None
        by (auto simp: inj_on_def dom_def ran_def)
      have "ns = i # filter ((\<le>) (Suc i)) (rremdups
        (List.map_filter (case_sum Map.empty Some) (fo_nmlz_rec (Suc i) (m(Inl x \<mapsto> i)) AD xs)))"
        using 2(5) False None
        by (auto simp: List.map_filter_simps filter_rremdups)
           (metis Suc_leD antisym not_less_eq_eq)
      then show ?thesis
        by (auto simp: 2(2)[OF False None pred, OF refl])
           (smt Suc_le_eq Suc_pred le_add1 le_zero_eq less_add_same_cancel1 not_less_eq_eq
            upt_Suc_append upt_rec)
    next
      case (Some j)
      then have j_lt_i: "j < i"
        using 2(4)
        by (auto simp: ran_def)
      have ns_def: "ns = filter ((\<le>) i) (rremdups
        (List.map_filter (case_sum Map.empty Some) (fo_nmlz_rec i m AD xs)))"
        using 2(5) False Some j_lt_i
        by (auto simp: List.map_filter_simps filter_rremdups) (metis leD)
      show ?thesis
        by (rule 2(3)[OF False Some 2(4) ns_def[symmetric]])
    qed
  qed (auto simp: List.map_filter_simps split: option.splits)
next
  case (3 i m AD n xs)
  show ?case
  proof (cases "m (Inr n)")
    case None
    have pred: "ran (m(Inr n \<mapsto> i)) \<subseteq> {..<Suc i}"
      using 3(3) None
      by (auto simp: inj_on_def dom_def ran_def)
    have "ns = i # filter ((\<le>) (Suc i)) (rremdups
      (List.map_filter (case_sum Map.empty Some) (fo_nmlz_rec (Suc i) (m(Inr n \<mapsto> i)) AD xs)))"
      using 3(4) None
      by (auto simp: List.map_filter_simps filter_rremdups) (metis Suc_leD antisym not_less_eq_eq)
    then show ?thesis
      by (auto simp add: 3(1)[OF None pred, OF refl])
         (smt Suc_le_eq Suc_pred le_add1 le_zero_eq less_add_same_cancel1 not_less_eq_eq
          upt_Suc_append upt_rec)
  next
    case (Some j)
    then have j_lt_i: "j < i"
      using 3(3)
      by (auto simp: ran_def)
    have ns_def: "ns = filter ((\<le>) i) (rremdups
      (List.map_filter (case_sum Map.empty Some) (fo_nmlz_rec i m AD xs)))"
      using 3(4) Some j_lt_i
      by (auto simp: List.map_filter_simps filter_rremdups) (metis leD)
    show ?thesis
      by (rule 3(2)[OF Some 3(3) ns_def[symmetric]])
  qed
qed (auto simp: List.map_filter_simps)

definition id_map :: "nat \<Rightarrow> ('a + nat \<rightharpoonup> nat)" where
  "id_map n = (\<lambda>x. case x of Inl x \<Rightarrow> None | Inr x \<Rightarrow> if x < n then Some x else None)"

lemma fo_nmlz_rec_idem: "Inl -` set ys \<subseteq> AD \<Longrightarrow>
  rremdups (List.map_filter (case_sum Map.empty Some) ys) = ns \<Longrightarrow>
  set (filter (\<lambda>n. n < i) ns) \<subseteq> {..<i} \<Longrightarrow> filter ((\<le>) i) ns = [i..<i + k] \<Longrightarrow>
  fo_nmlz_rec i (id_map i) AD ys = ys"
proof (induction ys arbitrary: i k ns)
  case (Cons y ys)
  show ?case
  proof (cases y)
    case (Inl a)
    show ?thesis
      using Cons(1)[OF _ _ Cons(4,5)] Cons(2,3)
      by (auto simp: Inl List.map_filter_simps)
  next
    case (Inr j)
    show ?thesis
    proof (cases "j < i")
      case False
      have j_i: "j = i"
        using False Cons(3,5)
        by (auto simp: Inr List.map_filter_simps filter_rremdups in_mono split: if_splits)
           (metis (no_types, lifting) upt_eq_Cons_conv)
      obtain kk where k_def: "k = Suc kk"
        using Cons(3,5)
        by (cases k) (auto simp: Inr List.map_filter_simps j_i)
      define ns' where "ns' = rremdups (List.map_filter (case_sum Map.empty Some) ys)"
      have id_map_None: "id_map i (Inr i) = None"
        by (auto simp: id_map_def)
      have id_map_upd: "(id_map i)(Inr i \<mapsto> i) = id_map (Suc i)"
        by (auto simp: id_map_def split: sum.splits)
      have "set (filter (\<lambda>n. n < Suc i) ns') \<subseteq> {..<Suc i}"
        using Cons(2,3)
        by auto
      moreover have "filter ((\<le>) (Suc i)) ns' = [Suc i..<i + k]"
        using Cons(3,5)
        by (auto simp: Inr List.map_filter_simps j_i filter_rremdups[symmetric] ns'_def[symmetric])
           (smt One_nat_def Suc_eq_plus1 Suc_le_eq add_diff_cancel_left' diff_is_0_eq'
            dual_order.order_iff_strict filter_cong n_not_Suc_n upt_eq_Cons_conv)
      moreover have "Inl -` set ys \<subseteq> AD"
        using Cons(2)
        by (auto simp: vimage_def)
      ultimately have "fo_nmlz_rec (Suc i) ((id_map i)(Inr i \<mapsto> i)) AD ys = ys"
        using Cons(1)[OF _ ns'_def[symmetric], of "Suc i" kk]
        by (auto simp: ns'_def k_def id_map_upd split: if_splits)
      then show ?thesis
        by (auto simp: Inr j_i id_map_None)
    next
      case True
      define ns' where "ns' = rremdups (List.map_filter (case_sum Map.empty Some) ys)"
      have "set (filter (\<lambda>y. y < i) ns') \<subseteq> set (filter (\<lambda>y. y < i) ns)"
        "filter ((\<le>) i) ns' = filter ((\<le>) i) ns"
        using Cons(3) True
        by (auto simp: Inr List.map_filter_simps filter_rremdups[symmetric] ns'_def[symmetric])
           (smt filter_cong leD)
      then have "fo_nmlz_rec i (id_map i) AD ys = ys"
        using Cons(1)[OF _ ns'_def[symmetric]] Cons(3,5) Cons(2)
        by (auto simp: vimage_def)
      then show ?thesis
        using True
        by (auto simp: Inr id_map_def)
    qed
  qed
qed (auto simp: List.map_filter_simps intro!: exI[of _ "[]"])

lemma fo_nmlz_rec_length: "length (fo_nmlz_rec i m AD xs) = length xs"
  by (induction i m AD xs rule: fo_nmlz_rec.induct) (auto simp: fun_upd_def split: option.splits)

lemma insert_Inr: "\<And>X. insert (Inr i) (X \<union> Inr ` {..<i}) = X \<union> Inr ` {..<Suc i}"
  by auto

lemma fo_nmlz_rec_set: "ran m \<subseteq> {..<i} \<Longrightarrow> set (fo_nmlz_rec i m AD xs) \<union> Inr ` {..<i} =
  set xs \<inter> Inl ` AD \<union> Inr ` {..<i + card (set xs - Inl ` AD - dom m)}"
proof (induction i m AD xs rule: fo_nmlz_rec.induct)
  case (2 i m AD x xs)
  have fin: "finite (set (Inl x # xs) - Inl ` AD - dom m)"
    by auto
  show ?case
    using 2(1)[OF _ 2(4)]
  proof (cases "x \<in> AD")
    case True
    have "card (set (Inl x # xs) - Inl ` AD - dom m) = card (set xs - Inl ` AD - dom m)"
      using True
      by auto
    then show ?thesis
      using 2(1)[OF True 2(4)] True
      by auto
  next
    case False
    show ?thesis
    proof (cases "m (Inl x)")
      case None
      have pred: "ran (m(Inl x \<mapsto> i)) \<subseteq> {..<Suc i}"
        using 2(4) None
        by (auto simp: inj_on_def dom_def ran_def)
      have "set (Inl x # xs) - Inl ` AD - dom m =
        {Inl x} \<union> (set xs - Inl ` AD - dom (m(Inl x \<mapsto> i)))"
        using None False
        by (auto simp: dom_def)
      then have Suc: "Suc i + card (set xs - Inl ` AD - dom (m(Inl x \<mapsto> i))) =
        i + card (set (Inl x # xs) - Inl ` AD - dom m)"
        using None
        by auto
      show ?thesis
        using 2(2)[OF False None pred] False None
        unfolding Suc
        by (auto simp: fun_upd_def[symmetric] insert_Inr)
    next
      case (Some j)
      then have j_lt_i: "j < i"
        using 2(4)
        by (auto simp: ran_def)
      have "card (set (Inl x # xs) - Inl ` AD - dom m) = card (set xs - Inl ` AD - dom m)"
        by (auto simp: Some intro: arg_cong[of _ _ card])
      then show ?thesis
        using 2(3)[OF False Some 2(4)] False Some j_lt_i
        by auto
    qed
  qed
next
  case (3 i m AD k xs)
  then show ?case
  proof (cases "m (Inr k)")
    case None
    have preds: "ran (m(Inr k \<mapsto> i)) \<subseteq> {..<Suc i}"
      using 3(3)
      by (auto simp: ran_def)
    have "set (Inr k # xs) - Inl ` AD - dom m =
      {Inr k} \<union> (set xs - Inl ` AD - dom (m(Inr k \<mapsto> i)))"
      using None
      by (auto simp: dom_def)
    then have Suc: "Suc i + card (set xs - Inl ` AD - dom (m(Inr k \<mapsto> i))) =
      i + card (set (Inr k # xs) - Inl ` AD - dom m)"
      using None
      by auto
    show ?thesis
      using None 3(1)[OF None preds]
      unfolding Suc
      by (auto simp: fun_upd_def[symmetric] insert_Inr)
  next
    case (Some j)
    have fin: "finite (set (Inr k # xs) - Inl ` AD - dom m)"
      by auto
    have card_eq: "card (set xs - Inl ` AD - dom m) = card (set (Inr k # xs) - Inl ` AD - dom m)"
      by (auto simp: Some intro!: arg_cong[of _ _ card])
    have j_lt_i: "j < i"
      using 3(3) Some
      by (auto simp: ran_def)
    show ?thesis
      using 3(2)[OF Some 3(3)] j_lt_i
      unfolding card_eq
      by (auto simp: ran_def insert_Inr Some)
  qed
qed auto

lemma fo_nmlz_rec_set_rev: "set (fo_nmlz_rec i m AD xs) \<subseteq> Inl ` AD \<Longrightarrow> set xs \<subseteq> Inl ` AD"
  by (induction i m AD xs rule: fo_nmlz_rec.induct) (auto split: if_splits option.splits)

lemma fo_nmlz_rec_map: "inj_on m (dom m) \<Longrightarrow> ran m \<subseteq> {..<i} \<Longrightarrow> \<exists>m'. inj_on m' (dom m') \<and>
  (\<forall>n. m n \<noteq> None \<longrightarrow> m' n = m n) \<and> (\<forall>(x, y) \<in> set (zip xs (fo_nmlz_rec i m AD xs)).
    (case x of Inl x' \<Rightarrow> if x' \<in> AD then x = y else \<exists>j. m' (Inl x') = Some j \<and> y = Inr j
    | Inr n \<Rightarrow> \<exists>j. m' (Inr n) = Some j \<and> y = Inr j))"
proof (induction i m AD xs rule: fo_nmlz_rec.induct)
  case (2 i m AD x xs)
  show ?case
    using 2(1)[OF _ 2(4,5)]
  proof (cases "x \<in> AD")
    case False
    show ?thesis
    proof (cases "m (Inl x)")
      case None
      have preds: "inj_on (m(Inl x \<mapsto> i)) (dom (m(Inl x \<mapsto> i)))" "ran (m(Inl x \<mapsto> i)) \<subseteq> {..<Suc i}"
        using 2(4,5)
        by (auto simp: inj_on_def ran_def)
      show ?thesis
        using 2(2)[OF False None preds] False None
        apply safe
        subgoal for m'
          by (auto simp: fun_upd_def split: sum.splits intro!: exI[of _ m'])
        done
    next
      case (Some j)
      show ?thesis
        using 2(3)[OF False Some 2(4,5)] False Some
        apply safe
        subgoal for m'
          by (auto split: sum.splits intro!: exI[of _ m'])
        done
    qed
  qed auto
next
  case (3 i m AD n xs)
  show ?case
  proof (cases "m (Inr n)")
    case None
    have preds: "inj_on (m(Inr n \<mapsto> i)) (dom (m(Inr n \<mapsto> i)))" "ran (m(Inr n \<mapsto> i)) \<subseteq> {..<Suc i}"
      using 3(3,4)
      by (auto simp: inj_on_def ran_def)
    show ?thesis
      using 3(1)[OF None preds] None
      apply safe
      subgoal for m'
        by (auto simp: fun_upd_def intro!: exI[of _ m'] split: sum.splits)
      done
  next
    case (Some j)
    show ?thesis
      using 3(2)[OF Some 3(3,4)] Some
      apply safe
      subgoal for m'
        by (auto simp: fun_upd_def intro!: exI[of _ m'] split: sum.splits)
      done
  qed
qed auto

lemma ad_agr_map:
  assumes "length xs = length ys" "inj_on m (dom m)"
    "\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> (case x of Inl x' \<Rightarrow>
    if x' \<in> AD then x = y else m x = Some y \<and> (case y of Inl z \<Rightarrow> z \<notin> AD | Inr _ \<Rightarrow> True)
  | Inr n \<Rightarrow> m x = Some y \<and> (case y of Inl z \<Rightarrow> z \<notin> AD | Inr _ \<Rightarrow> True))"
  shows "ad_agr_list AD xs ys"
proof -
  have "ad_equiv_pair AD (a, b)" if "(a, b) \<in> set (zip xs ys)" for a b
    unfolding ad_equiv_pair.simps
    using assms(3)[OF that]
    by (auto split: sum.splits if_splits)
  moreover have "False" if "(a, c) \<in> set (zip xs ys)" "(b, c) \<in> set (zip xs ys)" "a \<noteq> b" for a b c
    using assms(3)[OF that(1)] assms(3)[OF that(2)] assms(2) that(3)
    by (auto split: sum.splits if_splits) (metis domI inj_onD that(3))+
  moreover have "False" if "(a, b) \<in> set (zip xs ys)" "(a, c) \<in> set (zip xs ys)" "b \<noteq> c" for a b c
    using assms(3)[OF that(1)] assms(3)[OF that(2)] assms(2) that(3)
    by (auto split: sum.splits if_splits)
  ultimately show ?thesis
    using assms
    by (fastforce simp: ad_agr_list_def ad_equiv_list_def sp_equiv_list_def pairwise_def)
qed

lemma fo_nmlz_rec_take: "take n (fo_nmlz_rec i m AD xs) = fo_nmlz_rec i m AD (take n xs)"
  by (induction i m AD xs arbitrary: n rule: fo_nmlz_rec.induct)
     (auto simp: take_Cons' split: option.splits)

definition fo_nmlz :: "'a set \<Rightarrow> ('a + nat) list \<Rightarrow> ('a + nat) list" where
  "fo_nmlz = fo_nmlz_rec 0 Map.empty"

lemma fo_nmlz_Nil[simp]: "fo_nmlz AD [] = []"
  by (auto simp: fo_nmlz_def)

lemma fo_nmlz_Cons: "fo_nmlz AD [x] =
  (case x of Inl x \<Rightarrow> if x \<in> AD then [Inl x] else [Inr 0] | _ \<Rightarrow> [Inr 0])"
  by (auto simp: fo_nmlz_def split: sum.splits)

lemma fo_nmlz_Cons_Cons: "fo_nmlz AD [x, x] =
  (case x of Inl x \<Rightarrow> if x \<in> AD then [Inl x, Inl x] else [Inr 0, Inr 0] | _ \<Rightarrow> [Inr 0, Inr 0])"
  by (auto simp: fo_nmlz_def split: sum.splits)

lemma fo_nmlz_sound: "fo_nmlzd AD (fo_nmlz AD xs)"
  using fo_nmlz_rec_sound[of Map.empty 0] fo_nmlz_rec_set[of Map.empty 0 AD xs]
  by (auto simp: fo_nmlzd_def fo_nmlz_def nats_def Let_def)

lemma fo_nmlz_length: "length (fo_nmlz AD xs) = length xs"
  using fo_nmlz_rec_length
  by (auto simp: fo_nmlz_def)

lemma fo_nmlz_map: "\<exists>\<tau>. fo_nmlz AD (map \<sigma> ns) = map \<tau> ns"
proof -
  obtain m' where m'_def: "\<forall>(x, y)\<in>set (zip (map \<sigma> ns) (fo_nmlz AD (map \<sigma> ns))).
    case x of Inl x' \<Rightarrow> if x' \<in> AD then x = y else \<exists>j. m' (Inl x') = Some j \<and> y = Inr j
    | Inr n \<Rightarrow> \<exists>j. m' (Inr n) = Some j \<and> y = Inr j"
    using fo_nmlz_rec_map[of Map.empty 0, of "map \<sigma> ns"]
    by (auto simp: fo_nmlz_def)
  define \<tau> where "\<tau> \<equiv> (\<lambda>n. case \<sigma> n of Inl x \<Rightarrow> if x \<in> AD then Inl x else Inr (the (m' (Inl x)))
    | Inr j \<Rightarrow> Inr (the (m' (Inr j))))"
  have "fo_nmlz AD (map \<sigma> ns) = map \<tau> ns"
  proof (rule nth_equalityI)
    show "length (fo_nmlz AD (map \<sigma> ns)) = length (map \<tau> ns)"
      using fo_nmlz_length[of AD "map \<sigma> ns"]
      by auto
    fix i
    assume "i < length (fo_nmlz AD (map \<sigma> ns))"
    then show "fo_nmlz AD (map \<sigma> ns) ! i = map \<tau> ns ! i"
      using m'_def fo_nmlz_length[of AD "map \<sigma> ns"]
      apply (auto simp: set_zip \<tau>_def split: sum.splits)
        apply (metis nth_map)
       apply (metis nth_map option.sel)+
      done
  qed
  then show ?thesis
    by auto
qed

lemma card_set_minus: "card (set xs - X) \<le> length xs"
  by (meson Diff_subset List.finite_set card_length card_mono order_trans)

lemma fo_nmlz_set: "set (fo_nmlz AD xs) =
  set xs \<inter> Inl ` AD \<union> Inr ` {..<min (length xs) (card (set xs - Inl ` AD))}"
  using fo_nmlz_rec_set[of Map.empty 0 AD xs]
  by (auto simp add: fo_nmlz_def card_set_minus)

lemma fo_nmlz_set_rev: "set (fo_nmlz AD xs) \<subseteq> Inl ` AD \<Longrightarrow> set xs \<subseteq> Inl ` AD"
  using fo_nmlz_rec_set_rev[of 0 Map.empty AD xs]
  by (auto simp: fo_nmlz_def)

lemma inj_on_empty: "inj_on Map.empty (dom Map.empty)" and ran_empty_upto: "ran Map.empty \<subseteq> {..<0}"
  by auto

lemma fo_nmlz_ad_agr: "ad_agr_list AD xs (fo_nmlz AD xs)"
  using fo_nmlz_rec_map[OF inj_on_empty ran_empty_upto, of xs AD]
  unfolding fo_nmlz_def
  apply safe
  subgoal for m'
    by (fastforce simp: inj_on_def dom_def split: sum.splits if_splits
        intro!: ad_agr_map[OF fo_nmlz_rec_length[symmetric], of "map_option Inr \<circ> m'"])
  done

lemma fo_nmlzd_mono: "Inl -` set xs \<subseteq> AD \<Longrightarrow> fo_nmlzd AD' xs \<Longrightarrow> fo_nmlzd AD xs"
  by (auto simp: fo_nmlzd_def)

lemma fo_nmlz_idem: "fo_nmlzd AD ys \<Longrightarrow> fo_nmlz AD ys = ys"
  using fo_nmlz_rec_idem[where ?i=0]
  by (auto simp: fo_nmlzd_def fo_nmlz_def id_map_def nats_def Let_def)

lemma fo_nmlz_take: "take n (fo_nmlz AD xs) = fo_nmlz AD (take n xs)"
  using fo_nmlz_rec_take
  by (auto simp: fo_nmlz_def)

fun nall_tuples_rec :: "'a set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a + nat) table" where
  "nall_tuples_rec AD i 0 = {[]}"
| "nall_tuples_rec AD i (Suc n) = \<Union>((\<lambda>as. (\<lambda>x. x # as) ` (Inl ` AD \<union> Inr ` {..<i})) `
    nall_tuples_rec AD i n) \<union> (\<lambda>as. Inr i # as) ` nall_tuples_rec AD (Suc i) n"

lemma nall_tuples_rec_Inl: "vs \<in> nall_tuples_rec AD i n \<Longrightarrow> Inl -` set vs \<subseteq> AD"
  by (induction AD i n arbitrary: vs rule: nall_tuples_rec.induct) (fastforce simp: vimage_def)+

lemma nall_tuples_rec_length: "xs \<in> nall_tuples_rec AD i n \<Longrightarrow> length xs = n"
  by (induction AD i n arbitrary: xs rule: nall_tuples_rec.induct) auto

lemma fun_upd_id_map: "(id_map i)(Inr i \<mapsto> i) = id_map (Suc i)"
  by (rule ext) (auto simp: id_map_def split: sum.splits)

lemma id_mapD: "id_map j (Inr i) = None \<Longrightarrow> j \<le> i" "id_map j (Inr i) = Some x \<Longrightarrow> i < j \<and> i = x"
  by (auto simp: id_map_def split: if_splits)

lemma nall_tuples_rec_fo_nmlz_rec_sound: "i \<le> j \<Longrightarrow> xs \<in> nall_tuples_rec AD i n \<Longrightarrow>
  fo_nmlz_rec j (id_map j) AD xs = xs"
  apply (induction n arbitrary: i j xs)
   apply (auto simp: fun_upd_id_map dest!: id_mapD split: option.splits)
    apply (meson dual_order.strict_trans2 id_mapD(1) not_Some_eq sup.strict_order_iff)
  using Suc_leI apply blast+
  done

lemma nall_tuples_rec_fo_nmlz_rec_complete:
  assumes "fo_nmlz_rec j (id_map j) AD xs = xs"
  shows "xs \<in> nall_tuples_rec AD j (length xs)"
  using assms
proof (induction xs arbitrary: j)
  case (Cons x xs)
  show ?case
  proof (cases x)
    case (Inl a)
    have a_AD: "a \<in> AD"
      using Cons(2)
      by (auto simp: Inl split: if_splits option.splits)
    show ?thesis
      using Cons a_AD
      by (auto simp: Inl)
  next
    case (Inr b)
    have b_j: "b \<le> j"
      using Cons(2)
      by (auto simp: Inr split: option.splits dest: id_mapD)
    show ?thesis
    proof (cases "b = j")
      case True
      have preds: "fo_nmlz_rec (Suc j) (id_map (Suc j)) AD xs = xs"
        using Cons(2)
        by (auto simp: Inr True fun_upd_id_map dest: id_mapD split: option.splits)
      show ?thesis
        using Cons(1)[OF preds]
        by (auto simp: Inr True)
    next
      case False
      have b_lt_j: "b < j"
        using b_j False
        by auto
      have id_map: "id_map j (Inr b) = Some b"
        using b_lt_j
        by (auto simp: id_map_def)
      have preds: "fo_nmlz_rec j (id_map j) AD xs = xs"
        using Cons(2)
        by (auto simp: Inr id_map)
      show ?thesis
        using Cons(1)[OF preds] b_lt_j
        by (auto simp: Inr)
    qed
  qed
qed auto

lemma nall_tuples_rec_fo_nmlz: "xs \<in> nall_tuples_rec AD 0 (length xs) \<longleftrightarrow> fo_nmlz AD xs = xs"
  using nall_tuples_rec_fo_nmlz_rec_sound[of 0 0 xs AD "length xs"]
    nall_tuples_rec_fo_nmlz_rec_complete[of 0 AD xs]
  by (auto simp: fo_nmlz_def id_map_def)

lemma fo_nmlzd_code[code]: "fo_nmlzd AD xs \<longleftrightarrow> fo_nmlz AD xs = xs"
  using fo_nmlz_idem fo_nmlz_sound
  by metis

lemma nall_tuples_code[code]: "nall_tuples AD n = nall_tuples_rec AD 0 n"
  unfolding nall_tuples_set
  using nall_tuples_rec_length trans[OF nall_tuples_rec_fo_nmlz fo_nmlzd_code[symmetric]]
  by fastforce

lemma exists_map: "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> \<exists>f. ys = map f xs"
proof (induction xs ys rule: list_induct2)
  case (Cons x xs y ys)
  then obtain f where f_def: "ys = map f xs"
    by auto
  with Cons(3) have "y # ys = map (f(x := y)) (x # xs)"
    by auto
  then show ?case
    by metis
qed auto

lemma exists_fo_nmlzd:
  assumes "length xs = length ys" "distinct xs" "fo_nmlzd AD ys"
  shows "\<exists>f. ys = fo_nmlz AD (map f xs)"
  using fo_nmlz_idem[OF assms(3)] exists_map[OF _ assms(2)] assms(1)
  by metis

lemma list_induct2_rev[consumes 1]: "length xs = length ys \<Longrightarrow> (P [] []) \<Longrightarrow>
  (\<And>x y xs ys. P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])) \<Longrightarrow> P xs ys"
proof (induction "length xs" arbitrary: xs ys)
  case (Suc n)
  then show ?case
    by (cases xs rule: rev_cases; cases ys rule: rev_cases) auto
qed auto

lemma ad_agr_list_fo_nmlzd:
  assumes "ad_agr_list AD vs vs'" "fo_nmlzd AD vs" "fo_nmlzd AD vs'"
  shows "vs = vs'"
  using ad_agr_list_length[OF assms(1)] assms
proof (induction vs vs' rule: list_induct2_rev)
  case (2 x y xs ys)
  have norms: "fo_nmlzd AD xs" "fo_nmlzd AD ys"
    using 2(3,4)
    by (auto simp: fo_nmlzd_def nats_def Let_def map_filter_app rremdups_app
        split: sum.splits if_splits)
  have ad_agr: "ad_agr_list AD xs ys"
    using 2(2)
    by (auto simp: ad_agr_list_def ad_equiv_list_def sp_equiv_list_def pairwise_def)
  note xs_ys = 2(1)[OF ad_agr norms]
  have "x = y"
  proof (cases "isl x \<or> isl y")
    case True
    then have "isl x \<longrightarrow> projl x \<in> AD" "isl y \<longrightarrow> projl y \<in> AD"
      using 2(3,4)
      by (auto simp: fo_nmlzd_def)
    then show ?thesis
      using 2(2) True
      apply (auto simp: ad_agr_list_def ad_equiv_list_def isl_def)
      unfolding ad_equiv_pair.simps
      by blast+
  next
    case False
    then obtain x' y' where inr: "x = Inr x'" "y = Inr y'"
      by (cases x; cases y) auto
    show ?thesis
      using 2(2) xs_ys
    proof (cases "x \<in> set xs \<or> y \<in> set ys")
      case False
      then show ?thesis
        using fo_nmlzd_app_Inr 2(3,4)
        unfolding inr xs_ys
        by auto
    qed (auto simp: ad_agr_list_def sp_equiv_list_def pairwise_def set_zip in_set_conv_nth)
  qed
  then show ?case
    using xs_ys
    by auto
qed auto

lemma fo_nmlz_eqI:
  assumes "ad_agr_list AD vs vs'"
  shows "fo_nmlz AD vs = fo_nmlz AD vs'"
  using ad_agr_list_fo_nmlzd[OF
        ad_agr_list_trans[OF ad_agr_list_trans[OF
        ad_agr_list_comm[OF fo_nmlz_ad_agr[of AD vs]] assms]
        fo_nmlz_ad_agr[of AD vs']] fo_nmlz_sound fo_nmlz_sound] .

lemma fo_nmlz_eqD:
  assumes "fo_nmlz AD vs = fo_nmlz AD vs'"
  shows "ad_agr_list AD vs vs'"
  using ad_agr_list_trans[OF fo_nmlz_ad_agr[of AD vs, unfolded assms]
        ad_agr_list_comm[OF fo_nmlz_ad_agr[of AD vs']]] .

lemma fo_nmlz_eq: "fo_nmlz AD vs = fo_nmlz AD vs' \<longleftrightarrow> ad_agr_list AD vs vs'"
  using fo_nmlz_eqI[where ?AD=AD] fo_nmlz_eqD[where ?AD=AD]
  by blast

lemma fo_nmlz_mono:
  assumes "AD \<subseteq> AD'" "Inl -` set xs \<subseteq> AD"
  shows "fo_nmlz AD' xs = fo_nmlz AD xs"
proof -
  have "fo_nmlz AD (fo_nmlz AD' xs) = fo_nmlz AD' xs"
    apply (rule fo_nmlz_idem[OF fo_nmlzd_mono[OF _ fo_nmlz_sound]])
    using assms
    by (auto simp: fo_nmlz_set)
  moreover have "fo_nmlz AD xs = fo_nmlz AD (fo_nmlz AD' xs)"
    apply (rule fo_nmlz_eqI)
    apply (rule ad_agr_list_mono[OF assms(1)])
    apply (rule fo_nmlz_ad_agr)
    done
  ultimately show ?thesis
    by auto
qed

definition proj_vals :: "'c val set \<Rightarrow> nat list \<Rightarrow> 'c table" where
  "proj_vals R ns = (\<lambda>\<tau>. map \<tau> ns) ` R"

definition proj_fmla :: "('a, 'b) fo_fmla \<Rightarrow> 'c val set \<Rightarrow> 'c table" where
  "proj_fmla \<phi> R = proj_vals R (fv_fo_fmla_list \<phi>)"

lemmas proj_fmla_map = proj_fmla_def[unfolded proj_vals_def]

definition "extends_subst \<sigma> \<tau> = (\<forall>x. \<sigma> x \<noteq> None \<longrightarrow> \<sigma> x = \<tau> x)"

definition ext_tuple :: "'a set \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
  ('a + nat) list \<Rightarrow> ('a + nat) list set" where
  "ext_tuple AD fv_sub fv_sub_comp as = (if fv_sub_comp = [] then {as}
    else (\<lambda>fs. map snd (merge (zip fv_sub as) (zip fv_sub_comp fs))) `
    (nall_tuples_rec AD (card (Inr -` set as)) (length fv_sub_comp)))"

lemma ext_tuple_eq: "length fv_sub = length as \<Longrightarrow>
  ext_tuple AD fv_sub fv_sub_comp as =
  (\<lambda>fs. map snd (merge (zip fv_sub as) (zip fv_sub_comp fs))) `
  (nall_tuples_rec AD (card (Inr -` set as)) (length fv_sub_comp))"
  using fo_nmlz_idem[of AD as]
  by (auto simp: ext_tuple_def)

lemma map_map_of: "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow>
  ys = map (the \<circ> (map_of (zip xs ys))) xs"
  by (induction xs ys rule: list_induct2) (auto simp: fun_upd_comp)

lemma id_map_empty: "id_map 0 = Map.empty"
  by (rule ext) (auto simp: id_map_def split: sum.splits)

lemma fo_nmlz_rec_shift:
  fixes xs :: "('a + nat) list"
  shows "fo_nmlz_rec i (id_map i) AD xs = xs \<Longrightarrow>
  i' = card (Inr -` (Inr ` {..<i} \<union> set (take n xs))) \<Longrightarrow> n \<le> length xs \<Longrightarrow>
  fo_nmlz_rec i' (id_map i') AD (drop n xs) = drop n xs"
proof (induction i "id_map i :: 'a + nat \<rightharpoonup> nat" AD xs arbitrary: n rule: fo_nmlz_rec.induct)
  case (2 i AD x xs)
  have preds: "x \<in> AD" "fo_nmlz_rec i (id_map i) AD xs = xs"
    using 2(4)
    by (auto split: if_splits option.splits)
  show ?case
    using 2(4,5)
  proof (cases n)
    case (Suc k)
    have k_le: "k \<le> length xs"
      using 2(6)
      by (auto simp: Suc)
    have i'_def: "i' = card (Inr -` (Inr ` {..<i} \<union> set (take k xs)))"
      using 2(5)
      by (auto simp: Suc vimage_def)
    show ?thesis
      using 2(1)[OF preds i'_def k_le]
      by (auto simp: Suc)
  qed (auto simp: inj_vimage_image_eq)
next
  case (3 i AD j xs)
  show ?case
    using 3(3,4)
  proof (cases n)
    case (Suc k)
    have k_le: "k \<le> length xs"
      using 3(5)
      by (auto simp: Suc)
    have j_le_i: "j \<le> i"
      using 3(3)
      by (auto split: option.splits dest: id_mapD)
    show ?thesis
    proof (cases "j = i")
      case True
      have id_map: "id_map i (Inr j) = None" "(id_map i)(Inr j \<mapsto> i) = id_map (Suc i)"
        unfolding True fun_upd_id_map
        by (auto simp: id_map_def)
      have norm_xs: "fo_nmlz_rec (Suc i) (id_map (Suc i)) AD xs = xs"
        using 3(3)
        by (auto simp: id_map split: option.splits dest: id_mapD)
      have i'_def: "i' = card (Inr -` (Inr ` {..<Suc i} \<union> set (take k xs)))"
        using 3(4)
        by (auto simp: Suc True inj_vimage_image_eq)
           (metis Un_insert_left image_insert inj_Inr inj_vimage_image_eq lessThan_Suc vimage_Un)
      show ?thesis
        using 3(1)[OF id_map norm_xs i'_def k_le]
        by (auto simp: Suc)
    next
      case False
      have id_map: "id_map i (Inr j) = Some j"
        using j_le_i False
        by (auto simp: id_map_def)
      have norm_xs: "fo_nmlz_rec i (id_map i) AD xs = xs"
        using 3(3)
        by (auto simp: id_map)
      have i'_def: "i' = card (Inr -` (Inr ` {..<i} \<union> set (take k xs)))"
        using 3(4) j_le_i False
        by (auto simp: Suc inj_vimage_image_eq insert_absorb)
      show ?thesis
        using 3(2)[OF id_map norm_xs i'_def k_le]
        by (auto simp: Suc)
    qed
  qed (auto simp: inj_vimage_image_eq)
qed auto

fun proj_tuple :: "nat list \<Rightarrow> (nat \<times> ('a + nat)) list \<Rightarrow> ('a + nat) list" where
  "proj_tuple [] mys = []"
| "proj_tuple ns [] = []"
| "proj_tuple (n # ns) ((m, y) # mys) =
    (if m < n then proj_tuple (n # ns) mys else
    if m = n then y # proj_tuple ns mys
    else proj_tuple ns ((m, y) # mys))"

lemma proj_tuple_idle: "proj_tuple (map fst nxs) nxs = map snd nxs"
  by (induction nxs) auto

lemma proj_tuple_merge: "sorted_distinct (map fst nxs) \<Longrightarrow> sorted_distinct (map fst mys) \<Longrightarrow>
  set (map fst nxs) \<inter> set (map fst mys) = {} \<Longrightarrow>
  proj_tuple (map fst nxs) (merge nxs mys) = map snd nxs"
  using proj_tuple_idle
  by (induction nxs mys rule: merge.induct) auto+

lemma proj_tuple_map:
  assumes "sorted_distinct ns" "sorted_distinct ms" "set ns \<subseteq> set ms"
  shows "proj_tuple ns (zip ms (map \<sigma> ms)) = map \<sigma> ns"
proof -
  define ns' where "ns' = filter (\<lambda>n. n \<notin> set ns) ms"
  have sd_ns': "sorted_distinct ns'"
    using assms(2) sorted_filter[of id]
    by (auto simp: ns'_def)
  have disj: "set ns \<inter> set ns' = {}"
    by (auto simp: ns'_def)
  have ms_def: "ms = sort (ns @ ns')"
    apply (rule sorted_distinct_set_unique)
    using assms
    by (auto simp: ns'_def)
  have zip: "zip ms (map \<sigma> ms) = merge (zip ns (map \<sigma> ns)) (zip ns' (map \<sigma> ns'))"
    unfolding merge_map[OF assms(1) sd_ns' disj, folded ms_def, symmetric]
    using map_fst_merge assms(1)
    by (auto simp: ms_def) (smt length_map map_fst_merge map_fst_zip sd_ns' zip_map_fst_snd)
  show ?thesis
    unfolding zip
    using proj_tuple_merge
    by (smt assms(1) disj length_map map_fst_zip map_snd_zip sd_ns')
qed

lemma proj_tuple_length:
  assumes "sorted_distinct ns" "sorted_distinct ms" "set ns \<subseteq> set ms" "length ms = length xs"
  shows "length (proj_tuple ns (zip ms xs)) = length ns"
proof -
  obtain \<sigma> where \<sigma>: "xs = map \<sigma> ms"
    using exists_map[OF assms(4)] assms(2)
    by auto
  show ?thesis
    unfolding \<sigma>
    by (auto simp: proj_tuple_map[OF assms(1-3)])
qed

lemma ext_tuple_sound:
  assumes "sorted_distinct fv_sub" "sorted_distinct fv_sub_comp" "sorted_distinct fv_all"
    "set fv_sub \<inter> set fv_sub_comp = {}" "set fv_sub \<union> set fv_sub_comp = set fv_all"
    "ass = fo_nmlz AD ` proj_vals R fv_sub"
    "\<And>\<sigma> \<tau>. ad_agr_sets (set fv_sub) (set fv_sub) AD \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> R \<longleftrightarrow> \<tau> \<in> R"
    "xs \<in> fo_nmlz AD ` \<Union>(ext_tuple AD fv_sub fv_sub_comp ` ass)"
  shows "fo_nmlz AD (proj_tuple fv_sub (zip fv_all xs)) \<in> ass"
    "xs \<in> fo_nmlz AD ` proj_vals R fv_all"
proof -
  have fv_all_sort: "fv_all = sort (fv_sub @ fv_sub_comp)"
    using assms(1,2,3,4,5)
    by (simp add: sorted_distinct_set_unique)
  have len_in_ass: "\<And>xs. xs \<in> ass \<Longrightarrow> xs = fo_nmlz AD xs \<and> length xs = length fv_sub"
    by (auto simp: assms(6) proj_vals_def fo_nmlz_length fo_nmlz_idem fo_nmlz_sound)
  obtain as fs where as_fs_def: "as \<in> ass"
    "fs \<in> nall_tuples_rec AD (card (Inr -` set as)) (length fv_sub_comp)"
    "xs = fo_nmlz AD (map snd (merge (zip fv_sub as) (zip fv_sub_comp fs)))"
    using fo_nmlz_sound len_in_ass assms(8)
    by (auto simp: ext_tuple_def split: if_splits)
  then have vs_norm: "fo_nmlzd AD xs"
    using fo_nmlz_sound
    by auto
  obtain \<sigma> where \<sigma>_def: "\<sigma> \<in> R" "as = fo_nmlz AD (map \<sigma> fv_sub)"
    using as_fs_def(1) assms(6)
    by (auto simp: proj_vals_def)
  then obtain \<tau> where \<tau>_def: "as = map \<tau> fv_sub" "ad_agr_list AD (map \<sigma> fv_sub) (map \<tau> fv_sub)"
    using fo_nmlz_map fo_nmlz_ad_agr
    by metis
  have \<tau>_R: "\<tau> \<in> R"
    using assms(7) ad_agr_list_link \<sigma>_def(1) \<tau>_def(2)
    by fastforce
  define \<sigma>' where "\<sigma>' \<equiv> \<lambda>n. if n \<in> set fv_sub_comp then the (map_of (zip fv_sub_comp fs) n)
      else \<tau> n"
  then have "\<forall>n \<in> set fv_sub. \<tau> n = \<sigma>' n"
    using assms(4) by auto
  then have \<sigma>'_S: "\<sigma>' \<in> R"
    using assms(7) \<tau>_R
    by (fastforce simp: ad_agr_sets_def sp_equiv_def pairwise_def ad_equiv_pair.simps)
  have length_as: "length as = length fv_sub"
    using as_fs_def(1) assms(6)
    by (auto simp: proj_vals_def fo_nmlz_length)
  have length_fs: "length fs = length fv_sub_comp"
    using as_fs_def(2)
    by (auto simp: nall_tuples_rec_length)
  have map_fv_sub: "map \<sigma>' fv_sub = map \<tau> fv_sub"
    using assms(4) \<tau>_def(2)
    by (auto simp: \<sigma>'_def)
  have fs_map_map_of: "fs = map (the \<circ> (map_of (zip fv_sub_comp fs))) fv_sub_comp"
    using map_map_of length_fs assms(2)
    by metis
  have fs_map: "fs = map \<sigma>' fv_sub_comp"
    using \<sigma>'_def length_fs by (subst fs_map_map_of) simp
  have vs_map_fv_all: "xs = fo_nmlz AD (map \<sigma>' fv_all)"
    unfolding as_fs_def(3) \<tau>_def(1) map_fv_sub[symmetric] fs_map fv_all_sort
    using merge_map[OF assms(1,2,4)]
    by metis
  show "xs \<in> fo_nmlz AD ` proj_vals R fv_all"
    using \<sigma>'_S vs_map_fv_all
    by (auto simp: proj_vals_def)
  obtain \<sigma>'' where \<sigma>''_def: "xs = map \<sigma>'' fv_all"
    using exists_map[of fv_all xs] fo_nmlz_map vs_map_fv_all
    by blast
  have proj: "proj_tuple fv_sub (zip fv_all xs) = map \<sigma>'' fv_sub"
    using proj_tuple_map assms(1,3,5)
    unfolding \<sigma>''_def
    by blast
  have \<sigma>''_\<sigma>': "fo_nmlz AD (map \<sigma>'' fv_sub) = as"
    using \<sigma>''_def vs_map_fv_all \<sigma>_def(2)
    by (metis \<tau>_def(2) ad_agr_list_subset assms(5) fo_nmlz_ad_agr fo_nmlz_eqI map_fv_sub sup_ge1)
  show "fo_nmlz AD (proj_tuple fv_sub (zip fv_all xs)) \<in> ass"
    unfolding proj \<sigma>''_\<sigma>' map_fv_sub
    by (rule as_fs_def(1))
qed

lemma ext_tuple_complete:
  assumes "sorted_distinct fv_sub" "sorted_distinct fv_sub_comp" "sorted_distinct fv_all"
    "set fv_sub \<inter> set fv_sub_comp = {}" "set fv_sub \<union> set fv_sub_comp = set fv_all"
    "ass = fo_nmlz AD ` proj_vals R fv_sub"
    "\<And>\<sigma> \<tau>. ad_agr_sets (set fv_sub) (set fv_sub) AD \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> R \<longleftrightarrow> \<tau> \<in> R"
    "xs = fo_nmlz AD (map \<sigma> fv_all)" "\<sigma> \<in> R"
  shows "xs \<in> fo_nmlz AD ` \<Union>(ext_tuple AD fv_sub fv_sub_comp ` ass)"
proof -
  have fv_all_sort: "fv_all = sort (fv_sub @ fv_sub_comp)"
    using assms(1,2,3,4,5)
    by (simp add: sorted_distinct_set_unique)
  note \<sigma>_def = assms(9,8)
  have vs_norm: "fo_nmlzd AD xs"
    using \<sigma>_def(2) fo_nmlz_sound
    by auto
  define fs where "fs = map \<sigma> fv_sub_comp"
  define as where "as = map \<sigma> fv_sub"
  define nos where "nos = fo_nmlz AD (as @ fs)"
  define as' where "as' = take (length fv_sub) nos"
  define fs' where "fs' = drop (length fv_sub) nos"
  have length_as': "length as' = length fv_sub"
    by (auto simp: as'_def nos_def as_def fo_nmlz_length)
  have length_fs': "length fs' = length fv_sub_comp"
    by (auto simp: fs'_def nos_def as_def fs_def fo_nmlz_length)
  have len_fv_sub_nos: "length fv_sub \<le> length nos"
    by (auto simp: nos_def fo_nmlz_length as_def)
  have norm_as': "fo_nmlzd AD as'"
    using fo_nmlzd_take[OF fo_nmlz_sound]
    by (auto simp: as'_def nos_def)
  have as'_norm_as: "as' = fo_nmlz AD as"
    by (auto simp: as'_def nos_def as_def fo_nmlz_take)
  have ad_agr_as': "ad_agr_list AD as as'"
    using fo_nmlz_ad_agr
    unfolding as'_norm_as .
  have nos_as'_fs': "nos = as' @ fs'"
    using length_as' length_fs'
    by (auto simp: as'_def fs'_def)
  obtain \<tau> where \<tau>_def: "as' = map \<tau> fv_sub" "fs' = map \<tau> fv_sub_comp"
    using exists_map[of "fv_sub @ fv_sub_comp" "as' @ fs'"] assms(1,2,4) length_as' length_fs'
    by auto
  have "length fv_sub + length fv_sub_comp \<le> length fv_all"
    using assms(1,2,3,4,5)
    by (metis distinct_append distinct_card eq_iff length_append set_append)
  then have nos_sub: "set nos \<subseteq> Inl ` AD \<union> Inr ` {..<length fv_all}"
    using fo_nmlz_set[of AD "as @ fs"]
    by (auto simp: nos_def as_def fs_def)
  have len_fs': "length fs' = length fv_sub_comp"
    by (auto simp: fs'_def nos_def fo_nmlz_length as_def fs_def)
  have norm_nos_idem: "fo_nmlz_rec 0 (id_map 0) AD nos = nos"
    using fo_nmlz_idem[of AD nos] fo_nmlz_sound
    by (auto simp: nos_def fo_nmlz_def id_map_empty)
  have fs'_all: "fs' \<in> nall_tuples_rec AD (card (Inr -` set as')) (length fv_sub_comp)"
    unfolding len_fs'[symmetric]
    by (rule nall_tuples_rec_fo_nmlz_rec_complete)
      (rule fo_nmlz_rec_shift[OF norm_nos_idem, simplified, OF refl len_fv_sub_nos,
          folded as'_def fs'_def])
  have "as' \<in> nall_tuples AD (length fv_sub)"
    using length_as'
    apply (rule nall_tuplesI)
    using norm_as' .
  then have as'_ass: "as' \<in> ass"
    using as'_norm_as \<sigma>_def(1) as_def
    unfolding assms(6)
    by (auto simp: proj_vals_def)
  have vs_norm: "xs = fo_nmlz AD (map snd (merge (zip fv_sub as) (zip fv_sub_comp fs)))"
    using assms(1,2,4) \<sigma>_def(2)
    by (auto simp: merge_map as_def fs_def fv_all_sort)
  have set_sort': "set (sort (fv_sub @ fv_sub_comp)) = set (fv_sub @ fv_sub_comp)"
    by auto
  have "xs = fo_nmlz AD (map snd (merge (zip fv_sub as') (zip fv_sub_comp fs')))"
    unfolding vs_norm as_def fs_def \<tau>_def
      merge_map[OF assms(1,2,4)]
    apply (rule fo_nmlz_eqI)
    apply (rule ad_agr_list_subset[OF equalityD1, OF set_sort'])
    using fo_nmlz_ad_agr[of AD "as @ fs", folded nos_def, unfolded nos_as'_fs']
    unfolding as_def fs_def \<tau>_def map_append[symmetric] .
  then show ?thesis
    using as'_ass fs'_all
    by (auto simp: ext_tuple_def length_as')
qed

definition "ext_tuple_set AD ns ns' X = (if ns' = [] then X else fo_nmlz AD ` \<Union>(ext_tuple AD ns ns' ` X))"

lemma ext_tuple_set_eq: "Ball X (fo_nmlzd AD) \<Longrightarrow> ext_tuple_set AD ns ns' X = fo_nmlz AD ` \<Union>(ext_tuple AD ns ns' ` X)"
  by (auto simp: ext_tuple_set_def ext_tuple_def fo_nmlzd_code)

lemma ext_tuple_set_mono: "A \<subseteq> B \<Longrightarrow> ext_tuple_set AD ns ns' A \<subseteq> ext_tuple_set AD ns ns' B"
  by (auto simp: ext_tuple_set_def)

lemma ext_tuple_correct:
  assumes "sorted_distinct fv_sub" "sorted_distinct fv_sub_comp" "sorted_distinct fv_all"
    "set fv_sub \<inter> set fv_sub_comp = {}" "set fv_sub \<union> set fv_sub_comp = set fv_all"
    "ass = fo_nmlz AD ` proj_vals R fv_sub"
    "\<And>\<sigma> \<tau>. ad_agr_sets (set fv_sub) (set fv_sub) AD \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> R \<longleftrightarrow> \<tau> \<in> R"
  shows "ext_tuple_set AD fv_sub fv_sub_comp ass = fo_nmlz AD ` proj_vals R fv_all"
proof (rule set_eqI, rule iffI)
  fix xs
  assume xs_in: "xs \<in> ext_tuple_set AD fv_sub fv_sub_comp ass"
  show "xs \<in> fo_nmlz AD ` proj_vals R fv_all"
    using ext_tuple_sound(2)[OF assms] xs_in
    by (auto simp: ext_tuple_set_def ext_tuple_def assms(6) fo_nmlz_idem[OF fo_nmlz_sound] image_iff
        split: if_splits)
next
  fix xs
  assume "xs \<in> fo_nmlz AD ` proj_vals R fv_all"
  then obtain \<sigma> where \<sigma>_def: "xs = fo_nmlz AD (map \<sigma> fv_all)" "\<sigma> \<in> R"
    by (auto simp: proj_vals_def)
  show "xs \<in> ext_tuple_set AD fv_sub fv_sub_comp ass"
    using ext_tuple_complete[OF assms \<sigma>_def]
    by (auto simp: ext_tuple_set_def ext_tuple_def assms(6) fo_nmlz_idem[OF fo_nmlz_sound] image_iff
        split: if_splits)
qed

lemma proj_tuple_sound:
  assumes "sorted_distinct fv_sub" "sorted_distinct fv_sub_comp" "sorted_distinct fv_all"
    "set fv_sub \<inter> set fv_sub_comp = {}" "set fv_sub \<union> set fv_sub_comp = set fv_all"
    "ass = fo_nmlz AD ` proj_vals R fv_sub"
    "\<And>\<sigma> \<tau>. ad_agr_sets (set fv_sub) (set fv_sub) AD \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> R \<longleftrightarrow> \<tau> \<in> R"
    "fo_nmlz AD xs = xs" "length xs = length fv_all"
    "fo_nmlz AD (proj_tuple fv_sub (zip fv_all xs)) \<in> ass"
  shows "xs \<in> fo_nmlz AD ` \<Union>(ext_tuple AD fv_sub fv_sub_comp ` ass)"
proof -
  have fv_all_sort: "fv_all = sort (fv_sub @ fv_sub_comp)"
    using assms(1,2,3,4,5)
    by (simp add: sorted_distinct_set_unique)
  obtain \<sigma> where \<sigma>_def: "xs = map \<sigma> fv_all"
    using exists_map[of fv_all xs] assms(3,9)
    by auto
  have xs_norm: "xs = fo_nmlz AD (map \<sigma> fv_all)"
    using assms(8)
    by (auto simp: \<sigma>_def)
  have proj: "proj_tuple fv_sub (zip fv_all xs) = map \<sigma> fv_sub"
    unfolding \<sigma>_def
    apply (rule proj_tuple_map[OF assms(1,3)])
    using assms(5)
    by blast
  obtain \<tau> where \<tau>_def: "fo_nmlz AD (map \<sigma> fv_sub) = fo_nmlz AD (map \<tau> fv_sub)" "\<tau> \<in> R"
    using assms(10)
    by (auto simp: assms(6) proj proj_vals_def)
  have \<sigma>_R: "\<sigma> \<in> R"
    using assms(7) fo_nmlz_eqD[OF \<tau>_def(1)] \<tau>_def(2)
    unfolding ad_agr_list_link[symmetric]
    by auto
  show ?thesis
    by (rule ext_tuple_complete[OF assms(1,2,3,4,5,6,7) xs_norm \<sigma>_R]) assumption
qed

lemma proj_tuple_correct:
  assumes "sorted_distinct fv_sub" "sorted_distinct fv_sub_comp" "sorted_distinct fv_all"
    "set fv_sub \<inter> set fv_sub_comp = {}" "set fv_sub \<union> set fv_sub_comp = set fv_all"
    "ass = fo_nmlz AD ` proj_vals R fv_sub"
    "\<And>\<sigma> \<tau>. ad_agr_sets (set fv_sub) (set fv_sub) AD \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> R \<longleftrightarrow> \<tau> \<in> R"
    "fo_nmlz AD xs = xs" "length xs = length fv_all"
  shows "xs \<in> fo_nmlz AD ` \<Union>(ext_tuple AD fv_sub fv_sub_comp ` ass) \<longleftrightarrow>
    fo_nmlz AD (proj_tuple fv_sub (zip fv_all xs)) \<in> ass"
  using ext_tuple_sound(1)[OF assms(1,2,3,4,5,6,7)] proj_tuple_sound[OF assms]
  by blast

fun unify_vals_terms :: "('a + 'c) list \<Rightarrow> ('a fo_term) list \<Rightarrow> (nat \<rightharpoonup> ('a + 'c)) \<Rightarrow>
  (nat \<rightharpoonup> ('a + 'c)) option" where
  "unify_vals_terms [] [] \<sigma> = Some \<sigma>"
| "unify_vals_terms (v # vs) ((Const c') # ts) \<sigma> =
    (if v = Inl c' then unify_vals_terms vs ts \<sigma> else None)"
| "unify_vals_terms (v # vs) ((Var n) # ts) \<sigma> =
    (case \<sigma> n of Some x \<Rightarrow> (if v = x then unify_vals_terms vs ts \<sigma> else None)
    | None \<Rightarrow> unify_vals_terms vs ts (\<sigma>(n := Some v)))"
| "unify_vals_terms _ _ _ = None"

lemma unify_vals_terms_extends: "unify_vals_terms vs ts \<sigma> = Some \<sigma>' \<Longrightarrow> extends_subst \<sigma> \<sigma>'"
  unfolding extends_subst_def
  by (induction vs ts \<sigma> arbitrary: \<sigma>' rule: unify_vals_terms.induct)
     (force split: if_splits option.splits)+

lemma unify_vals_terms_sound: "unify_vals_terms vs ts \<sigma> = Some \<sigma>' \<Longrightarrow> (the \<circ> \<sigma>') \<odot>e ts = vs"
  using unify_vals_terms_extends
  by (induction vs ts \<sigma> arbitrary: \<sigma>' rule: unify_vals_terms.induct)
     (force simp: eval_eterms_def extends_subst_def fv_fo_terms_set_def
      split: if_splits option.splits)+

lemma unify_vals_terms_complete: "\<sigma>'' \<odot>e ts = vs \<Longrightarrow> (\<And>n. \<sigma> n \<noteq> None \<Longrightarrow> \<sigma> n = Some (\<sigma>'' n)) \<Longrightarrow>
  \<exists>\<sigma>'. unify_vals_terms vs ts \<sigma> = Some \<sigma>'"
  by (induction vs ts \<sigma> rule: unify_vals_terms.induct)
     (force simp: eval_eterms_def extends_subst_def split: if_splits option.splits)+

definition eval_table :: "'a fo_term list \<Rightarrow> ('a + 'c) table \<Rightarrow> ('a + 'c) table" where
  "eval_table ts X = (let fvs = fv_fo_terms_list ts in
    \<Union>((\<lambda>vs. case unify_vals_terms vs ts Map.empty of Some \<sigma> \<Rightarrow>
      {map (the \<circ> \<sigma>) fvs} | _ \<Rightarrow> {}) ` X))"

lemma eval_table:
  fixes X :: "('a + 'c) table"
  shows "eval_table ts X = proj_vals {\<sigma>. \<sigma> \<odot>e ts \<in> X} (fv_fo_terms_list ts)"
proof (rule set_eqI, rule iffI)
  fix vs
  assume "vs \<in> eval_table ts X"
  then obtain as \<sigma> where as_def: "as \<in> X" "unify_vals_terms as ts Map.empty = Some \<sigma>"
    "vs = map (the \<circ> \<sigma>) (fv_fo_terms_list ts)"
    by (auto simp: eval_table_def split: option.splits)
  have "(the \<circ> \<sigma>) \<odot>e ts \<in> X"
    using unify_vals_terms_sound[OF as_def(2)] as_def(1)
    by auto
  with as_def(3) show "vs \<in> proj_vals {\<sigma>. \<sigma> \<odot>e ts \<in> X} (fv_fo_terms_list ts)"
    by (fastforce simp: proj_vals_def)
next
  fix vs :: "('a + 'c) list"
  assume "vs \<in> proj_vals {\<sigma>. \<sigma> \<odot>e ts \<in> X} (fv_fo_terms_list ts)"
  then obtain \<sigma> where \<sigma>_def: "vs = map \<sigma> (fv_fo_terms_list ts)" "\<sigma> \<odot>e ts \<in> X"
    by (auto simp: proj_vals_def)
  obtain \<sigma>' where \<sigma>'_def: "unify_vals_terms (\<sigma> \<odot>e ts) ts Map.empty = Some \<sigma>'"
    using unify_vals_terms_complete[OF refl, of Map.empty \<sigma> ts]
    by auto
  have "(the \<circ> \<sigma>') \<odot>e ts = (\<sigma> \<odot>e ts)"
    using unify_vals_terms_sound[OF \<sigma>'_def(1)]
    by auto
  then have "vs = map (the \<circ> \<sigma>') (fv_fo_terms_list ts)"
    using fv_fo_terms_set_list eval_eterms_fv_fo_terms_set
    unfolding \<sigma>_def(1)
    by fastforce
  then show "vs \<in> eval_table ts X"
    using \<sigma>_def(2) \<sigma>'_def
    by (force simp: eval_table_def)
qed

fun ad_agr_close_rec :: "nat \<Rightarrow> (nat \<rightharpoonup> 'a + nat) \<Rightarrow> 'a set \<Rightarrow>
  ('a + nat) list \<Rightarrow> ('a + nat) list set" where
  "ad_agr_close_rec i m AD [] = {[]}"
| "ad_agr_close_rec i m AD (Inl x # xs) = (\<lambda>xs. Inl x # xs) ` ad_agr_close_rec i m AD xs"
| "ad_agr_close_rec i m AD (Inr n # xs) = (case m n of None \<Rightarrow> \<Union>((\<lambda>x. (\<lambda>xs. Inl x # xs) `
    ad_agr_close_rec i (m(n := Some (Inl x))) (AD - {x}) xs) ` AD) \<union>
    (\<lambda>xs. Inr i # xs) ` ad_agr_close_rec (Suc i) (m(n := Some (Inr i))) AD xs
  | Some v \<Rightarrow> (\<lambda>xs. v # xs) ` ad_agr_close_rec i m AD xs)"

lemma ad_agr_close_rec_length: "ys \<in> ad_agr_close_rec i m AD xs \<Longrightarrow> length xs = length ys"
  by (induction i m AD xs arbitrary: ys rule: ad_agr_close_rec.induct) (auto split: option.splits)

lemma ad_agr_close_rec_sound: "ys \<in> ad_agr_close_rec i m AD xs \<Longrightarrow>
  fo_nmlz_rec j (id_map j) X xs = xs \<Longrightarrow> X \<inter> AD = {} \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> Y \<inter> AD = {} \<Longrightarrow>
  inj_on m (dom m) \<Longrightarrow> dom m = {..<j} \<Longrightarrow> ran m \<subseteq> Inl ` Y \<union> Inr ` {..<i} \<Longrightarrow> i \<le> j \<Longrightarrow>
  fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) ys = ys \<and>
  (\<exists>m'. inj_on m' (dom m') \<and> (\<forall>n v. m n = Some v \<longrightarrow> m' (Inr n) = Some v) \<and>
  (\<forall>(x, y) \<in> set (zip xs ys). case x of Inl x' \<Rightarrow>
      if x' \<in> X then x = y else m' x = Some y \<and> (case y of Inl z \<Rightarrow> z \<notin> X | Inr x \<Rightarrow> True)
  | Inr n \<Rightarrow> m' x = Some y \<and> (case y of Inl z \<Rightarrow> z \<notin> X | Inr x \<Rightarrow> True)))"
proof (induction i m AD xs arbitrary: Y j ys rule: ad_agr_close_rec.induct)
  case (1 i m AD)
  then show ?case
    by (auto simp: ad_agr_list_def ad_equiv_list_def sp_equiv_list_def inj_on_def dom_def
        split: sum.splits intro!: exI[of _ "case_sum Map.empty m"])
next
  case (2 i m AD x xs)
  obtain zs where ys_def: "ys = Inl x # zs" "zs \<in> ad_agr_close_rec i m AD xs"
    using 2(2)
    by auto
  have preds: "fo_nmlz_rec j (id_map j) X xs = xs" "x \<in> X"
    using 2(3)
    by (auto split: if_splits option.splits)
  show ?case
    using 2(1)[OF ys_def(2) preds(1) 2(4,5,6,7,8,9,10)] preds(2)
    by (auto simp: ys_def(1))
next
  case (3 i m AD n xs)
  show ?case
  proof (cases "m n")
    case None
    obtain v zs where ys_def: "ys = v # zs"
      using 3(4)
      by (auto simp: None)
    have n_ge_j: "j \<le> n"
      using 3(9,10) None
      by (metis domIff leI lessThan_iff)
    show ?thesis
    proof (cases v)
      case (Inl x)
      have zs_def: "zs \<in> ad_agr_close_rec i (m(n \<mapsto> Inl x)) (AD - {x}) xs" "x \<in> AD"
        using 3(4)
        by (auto simp: None ys_def Inl)
      have preds: "fo_nmlz_rec (Suc j) (id_map (Suc j)) X xs = xs" "X \<inter> (AD - {x}) = {}"
        "X \<inter> (Y \<union> {x}) = {}" "(Y \<union> {x}) \<inter> (AD - {x}) = {}" "dom (m(n \<mapsto> Inl x)) = {..<Suc j}"
        "ran (m(n \<mapsto> Inl x)) \<subseteq> Inl ` (Y \<union> {x}) \<union> Inr ` {..<i}"
        "i \<le> Suc j" "n = j"
        using 3(5,6,7,8,10,11,12) n_ge_j zs_def(2)
        by (auto simp: fun_upd_id_map ran_def dest: id_mapD split: option.splits)
      have inj: "inj_on (m(n \<mapsto> Inl x)) (dom (m(n \<mapsto> Inl x)))"
        using 3(8,9,10,11,12) preds(8) zs_def(2)
        by (fastforce simp: inj_on_def dom_def ran_def)
      have sets_unfold: "X \<union> (Y \<union> {x}) \<union> (AD - {x}) = X \<union> Y \<union> AD"
        using zs_def(2)
        by auto
      note IH = 3(1)[OF None zs_def(2,1) preds(1,2,3,4) inj preds(5,6,7), unfolded sets_unfold]
      have norm_ys: "fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) ys = ys"
        using conjunct1[OF IH] zs_def(2)
        by (auto simp: ys_def(1) Inl split: option.splits)
      show ?thesis
        using norm_ys conjunct2[OF IH] None zs_def(2) 3(6)
        unfolding ys_def(1)
        apply safe
        subgoal for m'
          apply (auto simp: Inl dom_def intro!: exI[of _ m'] split: if_splits)
           apply (metis option.distinct(1))
          apply (fastforce split: prod.splits sum.splits)
          done
        done
    next
      case (Inr k)
      have zs_def: "zs \<in> ad_agr_close_rec (Suc i) (m(n \<mapsto> Inr i)) AD xs" "i = k"
        using 3(4)
        by (auto simp: None ys_def Inr)
      have preds: "fo_nmlz_rec (Suc n) (id_map (Suc n)) X xs = xs"
        "dom (m(n \<mapsto> Inr i)) = {..<Suc n}"
        "ran (m(n \<mapsto> Inr i)) \<subseteq> Inl ` Y \<union> Inr ` {..<Suc i}" "Suc i \<le> Suc n"
        using 3(5,10,11,12) n_ge_j
        by (auto simp: fun_upd_id_map ran_def dest: id_mapD split: option.splits)
      have inj: "inj_on (m(n \<mapsto> Inr i)) (dom (m(n \<mapsto> Inr i)))"
        using 3(9,11)
        by (auto simp: inj_on_def dom_def ran_def)
      note IH = 3(2)[OF None zs_def(1) preds(1) 3(6,7,8) inj preds(2,3,4)]
      have norm_ys: "fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) ys = ys"
        using conjunct1[OF IH] zs_def(2)
        by (auto simp: ys_def Inr fun_upd_id_map dest: id_mapD split: option.splits)
      show ?thesis
        using norm_ys conjunct2[OF IH] None
        unfolding ys_def(1) zs_def(2)
        apply safe
        subgoal for m'
          apply (auto simp: Inr dom_def intro!: exI[of _ m'] split: if_splits)
           apply (metis option.distinct(1))
          apply (fastforce split: prod.splits sum.splits)
          done
        done
    qed
  next
    case (Some v)
    obtain zs where ys_def: "ys = v # zs" "zs \<in> ad_agr_close_rec i m AD xs"
      using 3(4)
      by (auto simp: Some)
    have preds: "fo_nmlz_rec j (id_map j) X xs = xs" "n < j"
      using 3(5,8,10) Some
      by (auto simp: dom_def split: option.splits)
    note IH = 3(3)[OF Some ys_def(2) preds(1) 3(6,7,8,9,10,11,12)]
    have norm_ys: "fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) ys = ys"
      using conjunct1[OF IH] 3(11) Some
      by (auto simp: ys_def(1) ran_def id_map_def)
    have "case v of Inl z \<Rightarrow> z \<notin> X | Inr x \<Rightarrow> True"
      using 3(7,11) Some
      by (auto simp: ran_def split: sum.splits)
    then show ?thesis
      using norm_ys conjunct2[OF IH] Some
      unfolding ys_def(1)
      apply safe
      subgoal for m'
        by (auto intro!: exI[of _ m'] split: sum.splits)
      done
  qed
qed

lemma ad_agr_close_rec_complete:
  fixes xs :: "('a + nat) list"
  shows "fo_nmlz_rec j (id_map j) X xs = xs \<Longrightarrow>
  X \<inter> AD = {} \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> Y \<inter> AD = {} \<Longrightarrow>
  inj_on m (dom m) \<Longrightarrow> dom m = {..<j} \<Longrightarrow> ran m = Inl ` Y \<union> Inr ` {..<i} \<Longrightarrow> i \<le> j \<Longrightarrow>
  (\<And>n b. (Inr n, b) \<in> set (zip xs ys) \<Longrightarrow> case m n of Some v \<Rightarrow> v = b | None \<Rightarrow> b \<notin> ran m) \<Longrightarrow>
  fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) ys = ys \<Longrightarrow> ad_agr_list X xs ys \<Longrightarrow>
  ys \<in> ad_agr_close_rec i m AD xs"
proof (induction j "id_map j :: 'a + nat \<Rightarrow> nat option" X xs arbitrary: m i ys AD Y
    rule: fo_nmlz_rec.induct)
  case (2 j X x xs)
  have x_X: "x \<in> X" "fo_nmlz_rec j (id_map j) X xs = xs"
    using 2(4)
    by (auto split: if_splits option.splits)
  obtain z zs where ys_def: "ys = Inl z # zs" "z = x"
    using 2(14) x_X(1)
    by (cases ys) (auto simp: ad_agr_list_def ad_equiv_list_def ad_equiv_pair.simps)
  have norm_zs: "fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) zs = zs"
    using 2(13) ys_def(2) x_X(1)
    by (auto simp: ys_def(1))
  have ad_agr: "ad_agr_list X xs zs"
    using 2(14)
    by (auto simp: ys_def ad_agr_list_def ad_equiv_list_def sp_equiv_list_def pairwise_def)
  show ?case
    using 2(1)[OF x_X 2(5,6,7,8,9,10,11) _ norm_zs ad_agr] 2(12)
    by (auto simp: ys_def)
next
  case (3 j X n xs)
  obtain z zs where ys_def: "ys = z # zs"
    using 3(13)
    apply (cases ys)
     apply (auto simp: ad_agr_list_def)
    done
  show ?case
  proof (cases "j \<le> n")
    case True
    then have n_j: "n = j"
      using 3(3)
      by (auto split: option.splits dest: id_mapD)
    have id_map: "id_map j (Inr n) = None" "(id_map j)(Inr n \<mapsto> j) = id_map (Suc j)"
      unfolding n_j fun_upd_id_map
      by (auto simp: id_map_def)
    have norm_xs: "fo_nmlz_rec (Suc j) (id_map (Suc j)) X xs = xs"
      using 3(3)
      by (auto simp: ys_def fun_upd_id_map id_map(1) split: option.splits)
    have None: "m n = None"
      using 3(8)
      by (auto simp: dom_def n_j)
    have z_out: "z \<notin> Inl ` Y \<union> Inr ` {..<i}"
      using 3(11) None
      by (force simp: ys_def 3(9))
    show ?thesis
    proof (cases z)
      case (Inl a)
      have a_in: "a \<in> AD"
        using 3(12,13) z_out
        by (auto simp: ys_def Inl ad_agr_list_def ad_equiv_list_def ad_equiv_pair.simps
            split: if_splits option.splits)
      have norm_zs: "fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) zs = zs"
        using 3(12) a_in
        by (auto simp: ys_def Inl)
      have preds: "X \<inter> (AD - {a}) = {}" "X \<inter> (Y \<union> {a}) = {}" "(Y \<union> {a}) \<inter> (AD - {a}) = {}"
        using 3(4,5,6) a_in
        by auto
      have inj: "inj_on (m(n := Some (Inl a))) (dom (m(n := Some (Inl a))))"
        using 3(6,7,9) None a_in
        by (auto simp: inj_on_def dom_def ran_def) blast+
      have preds': "dom (m(n \<mapsto> Inl a)) = {..<Suc j}"
        "ran (m(n \<mapsto> Inl a)) = Inl ` (Y \<union> {a}) \<union> Inr ` {..<i}" "i \<le> Suc j"
        using 3(6,8,9,10) None less_Suc_eq a_in
          apply (auto simp: n_j dom_def ran_def)
         apply (smt Un_iff image_eqI mem_Collect_eq option.simps(3))
        apply (smt 3(8) domIff image_subset_iff lessThan_iff mem_Collect_eq sup_ge2)
        done
      have a_unfold: "X \<union> (Y \<union> {a}) \<union> (AD - {a}) = X \<union> Y \<union> AD" "Y \<union> {a} \<union> (AD - {a}) = Y \<union> AD"
        using a_in
        by auto
      have ad_agr: "ad_agr_list X xs zs"
        using 3(13)
        by (auto simp: ys_def Inl ad_agr_list_def ad_equiv_list_def sp_equiv_list_def pairwise_def)
      have "zs \<in> ad_agr_close_rec i (m(n \<mapsto> Inl a)) (AD - {a}) xs"
        apply (rule 3(1)[OF id_map norm_xs preds inj preds' _ _ ad_agr])
        using 3(11,13) norm_zs
        unfolding 3(9) preds'(2) a_unfold
         apply (auto simp: None Inl ys_def ad_agr_list_def sp_equiv_list_def pairwise_def
            split: option.splits)
          apply (metis Un_iff image_eqI option.simps(4))
         apply (metis image_subset_iff lessThan_iff option.simps(4) sup_ge2)
        apply fastforce
        done
      then show ?thesis
        using a_in
        by (auto simp: ys_def Inl None)
    next
      case (Inr b)
      have i_b: "i = b"
        using 3(12) z_out
        by (auto simp: ys_def Inr split: option.splits dest: id_mapD)
      have norm_zs: "fo_nmlz_rec (Suc i) (id_map (Suc i)) (X \<union> Y \<union> AD) zs = zs"
        using 3(12)
        by (auto simp: ys_def Inr i_b fun_upd_id_map split: option.splits dest: id_mapD)
      have ad_agr: "ad_agr_list X xs zs"
        using 3(13)
        by (auto simp: ys_def ad_agr_list_def ad_equiv_list_def sp_equiv_list_def pairwise_def)
      define m' where "m' \<equiv> m(n := Some (Inr i))"
      have preds: "inj_on m' (dom m')" "dom m' = {..<Suc j}" "Suc i \<le> Suc j"
        using 3(7,8,9,10)
        by (auto simp: m'_def n_j inj_on_def dom_def ran_def image_iff)
           (metis 3(8) domI lessThan_iff less_SucI)
      have ran: "ran m' = Inl ` Y \<union> Inr ` {..<Suc i}"
        using 3(9) None
        by (auto simp: m'_def)
      have "zs \<in> ad_agr_close_rec (Suc i) m' AD xs"
        apply (rule 3(1)[OF id_map norm_xs 3(4,5,6) preds(1,2) ran preds(3) _ norm_zs ad_agr])
        using 3(11,13)
        unfolding 3(9) ys_def Inr i_b m'_def
        unfolding ran[unfolded m'_def i_b]
        apply (auto simp: ad_agr_list_def sp_equiv_list_def pairwise_def split: option.splits)
          apply (metis Un_upper1 image_subset_iff option.simps(4))
         apply (metis UnI1 image_eqI insert_iff lessThan_Suc lessThan_iff option.simps(4)
            sp_equiv_pair.simps sum.inject(2) sup_commute)
        apply fastforce
        done
      then show ?thesis
        by (auto simp: ys_def Inr None m'_def i_b)
    qed
  next
    case False
    have id_map: "id_map j (Inr n) = Some n"
      using False
      by (auto simp: id_map_def)
    have norm_xs: "fo_nmlz_rec j (id_map j) X xs = xs"
      using 3(3)
      by (auto simp: id_map)
    have Some: "m n = Some z"
      using False 3(11)[unfolded ys_def]
      by (metis (mono_tags) 3(8) domD insert_iff leI lessThan_iff list.simps(15)
          option.simps(5) zip_Cons_Cons)
    have z_in: "z \<in> Inl ` Y \<union> Inr ` {..<i}"
      using 3(9) Some
      by (auto simp: ran_def)
    have ad_agr: "ad_agr_list X xs zs"
      using 3(13)
      by (auto simp: ad_agr_list_def ys_def ad_equiv_list_def sp_equiv_list_def pairwise_def)
    show ?thesis
    proof (cases z)
      case (Inl a)
      have a_in: "a \<in> Y \<union> AD"
        using 3(12,13)
        by (auto simp: ys_def Inl ad_agr_list_def ad_equiv_list_def ad_equiv_pair.simps
            split: if_splits option.splits)
      have norm_zs: "fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) zs = zs"
        using 3(12) a_in
        by (auto simp: ys_def Inl)
      show ?thesis
        using 3(2)[OF id_map norm_xs 3(4,5,6,7,8,9,10) _ norm_zs ad_agr] 3(11) a_in
        by (auto simp: ys_def Inl Some split: option.splits)
    next
      case (Inr b)
      have b_lt: "b < i"
        using z_in
        by (auto simp: Inr)
      have norm_zs: "fo_nmlz_rec i (id_map i) (X \<union> Y \<union> AD) zs = zs"
        using 3(12) b_lt
        by (auto simp: ys_def Inr split: option.splits)
      show ?thesis
        using 3(2)[OF id_map norm_xs 3(4,5,6,7,8,9,10) _ norm_zs ad_agr] 3(11)
        by (auto simp: ys_def Inr Some)
    qed
  qed
qed (auto simp: ad_agr_list_def)

definition ad_agr_close :: "'a set \<Rightarrow> ('a + nat) list \<Rightarrow> ('a + nat) list set" where
  "ad_agr_close AD xs = ad_agr_close_rec 0 Map.empty AD xs"

lemma ad_agr_close_sound:
  assumes "ys \<in> ad_agr_close Y xs" "fo_nmlzd X xs" "X \<inter> Y = {}"
  shows "fo_nmlzd (X \<union> Y) ys \<and> ad_agr_list X xs ys"
  using ad_agr_close_rec_sound[OF assms(1)[unfolded ad_agr_close_def]
    fo_nmlz_idem[OF assms(2), unfolded fo_nmlz_def, folded id_map_empty] assms(3)
    Int_empty_right Int_empty_left]
    ad_agr_map[OF ad_agr_close_rec_length[OF assms(1)[unfolded ad_agr_close_def]], of _ X]
    fo_nmlzd_code[unfolded fo_nmlz_def, folded id_map_empty, of "X \<union> Y" ys]
  by (auto simp: fo_nmlz_def)

lemma ad_agr_close_complete:
  assumes "X \<inter> Y = {}" "fo_nmlzd X xs" "fo_nmlzd (X \<union> Y) ys" "ad_agr_list X xs ys"
  shows "ys \<in> ad_agr_close Y xs"
  using ad_agr_close_rec_complete[OF fo_nmlz_idem[OF assms(2),
        unfolded fo_nmlz_def, folded id_map_empty] assms(1) Int_empty_right Int_empty_left _ _ _
        order.refl _ _ assms(4), of Map.empty]
        fo_nmlzd_code[unfolded fo_nmlz_def, folded id_map_empty, of "X \<union> Y" ys]
        assms(3)
  unfolding ad_agr_close_def
  by (auto simp: fo_nmlz_def)

lemma ad_agr_close_empty: "fo_nmlzd X xs \<Longrightarrow> ad_agr_close {} xs = {xs}"
  using ad_agr_close_complete[where ?X=X and ?Y="{}" and ?xs=xs and ?ys=xs]
    ad_agr_close_sound[where ?X=X and ?Y="{}" and ?xs=xs] ad_agr_list_refl ad_agr_list_fo_nmlzd
  by fastforce

lemma ad_agr_close_set_correct:
  assumes "AD' \<subseteq> AD" "sorted_distinct ns"
  "\<And>\<sigma> \<tau>. ad_agr_sets (set ns) (set ns) AD' \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> R \<longleftrightarrow> \<tau> \<in> R"
  shows "\<Union>(ad_agr_close (AD - AD') ` fo_nmlz AD' ` proj_vals R ns) = fo_nmlz AD ` proj_vals R ns"
proof (rule set_eqI, rule iffI)
  fix vs
  assume "vs \<in> \<Union>(ad_agr_close (AD - AD') ` fo_nmlz AD' ` proj_vals R ns)"
  then obtain \<sigma> where \<sigma>_def: "vs \<in> ad_agr_close (AD - AD') (fo_nmlz AD' (map \<sigma> ns))" "\<sigma> \<in> R"
    by (auto simp: proj_vals_def)
  have vs: "fo_nmlzd AD vs" "ad_agr_list AD' (fo_nmlz AD' (map \<sigma> ns)) vs"
    using ad_agr_close_sound[OF \<sigma>_def(1) fo_nmlz_sound] assms(1) Diff_partition
    by fastforce+
  obtain \<tau> where \<tau>_def: "vs = map \<tau> ns"
    using exists_map[of ns vs] assms(2) vs(2)
    by (auto simp: ad_agr_list_def fo_nmlz_length)
  show "vs \<in> fo_nmlz AD ` proj_vals R ns"
    apply (subst fo_nmlz_idem[OF vs(1), symmetric])
    using iffD1[OF assms(3) \<sigma>_def(2), OF iffD2[OF ad_agr_list_link ad_agr_list_trans[OF
          fo_nmlz_ad_agr[of AD' "map \<sigma> ns"] vs(2), unfolded \<tau>_def]]]
    unfolding \<tau>_def
    by (auto simp: proj_vals_def)
next
  fix vs
  assume "vs \<in> fo_nmlz AD ` proj_vals R ns"
  then obtain \<sigma> where \<sigma>_def: "vs = fo_nmlz AD (map \<sigma> ns)" "\<sigma> \<in> R"
    by (auto simp: proj_vals_def)
  define xs where "xs = fo_nmlz AD' vs"
  have preds: "AD' \<inter> (AD - AD') = {}" "fo_nmlzd AD' xs" "fo_nmlzd (AD' \<union> (AD - AD')) vs"
    using assms(1) fo_nmlz_sound Diff_partition
    by (fastforce simp: \<sigma>_def(1) xs_def)+
  obtain \<tau> where \<tau>_def: "vs = map \<tau> ns"
    using exists_map[of "ns" vs] assms(2) \<sigma>_def(1)
    by (auto simp: fo_nmlz_length)
  have "vs \<in> ad_agr_close (AD - AD') xs"
    using ad_agr_close_complete[OF preds] ad_agr_list_comm[OF fo_nmlz_ad_agr]
    by (auto simp: xs_def)
  then show "vs \<in> \<Union>(ad_agr_close (AD - AD') ` fo_nmlz AD' ` proj_vals R ns)"
    unfolding xs_def \<tau>_def
    using iffD1[OF assms(3) \<sigma>_def(2), OF ad_agr_sets_mono[OF assms(1) iffD2[OF ad_agr_list_link
          fo_nmlz_ad_agr[of AD "map \<sigma> ns", folded \<sigma>_def(1), unfolded \<tau>_def]]]]
    by (auto simp: proj_vals_def)
qed

lemma ad_agr_close_correct:
  assumes "AD' \<subseteq> AD"
    "\<And>\<sigma> \<tau>. ad_agr_sets (set (fv_fo_fmla_list \<phi>)) (set (fv_fo_fmla_list \<phi>)) AD' \<sigma> \<tau> \<Longrightarrow>
    \<sigma> \<in> R \<longleftrightarrow> \<tau> \<in> R"
  shows "\<Union>(ad_agr_close (AD - AD') ` fo_nmlz AD' ` proj_fmla \<phi> R) = fo_nmlz AD ` proj_fmla \<phi> R"
  using ad_agr_close_set_correct[OF _ sorted_distinct_fv_list, OF assms]
  by (auto simp: proj_fmla_def)

definition "ad_agr_close_set AD X = (if Set.is_empty AD then X else \<Union>(ad_agr_close AD ` X))"

lemma ad_agr_close_set_eq: "Ball X (fo_nmlzd AD') \<Longrightarrow> ad_agr_close_set AD X = \<Union>(ad_agr_close AD ` X)"
  by (force simp: ad_agr_close_set_def Set.is_empty_def ad_agr_close_empty)

lemma Ball_fo_nmlzd: "Ball (fo_nmlz AD ` X) (fo_nmlzd AD)"
  by (auto simp: fo_nmlz_sound)

lemmas ad_agr_close_set_nmlz_eq = ad_agr_close_set_eq[OF Ball_fo_nmlzd]

definition eval_pred :: "('a fo_term) list \<Rightarrow> 'a table \<Rightarrow> ('a, 'c) fo_t" where
  "eval_pred ts X = (let AD = \<Union>(set (map set_fo_term ts)) \<union> \<Union>(set ` X) in
    (AD, length (fv_fo_terms_list ts), eval_table ts (map Inl ` X)))"

definition eval_bool :: "bool \<Rightarrow> ('a, 'c) fo_t" where
  "eval_bool b = (if b then ({}, 0, {[]}) else ({}, 0, {}))"

definition eval_eq :: "'a fo_term \<Rightarrow> 'a fo_term \<Rightarrow> ('a, nat) fo_t" where
  "eval_eq t t' = (case t of Var n \<Rightarrow>
  (case t' of Var n' \<Rightarrow>
    if n = n' then ({}, 1, {[Inr 0]})
    else ({}, 2, {[Inr 0, Inr 0]})
    | Const c' \<Rightarrow> ({c'}, 1, {[Inl c']}))
  | Const c \<Rightarrow>
    (case t' of Var n' \<Rightarrow> ({c}, 1, {[Inl c]})
    | Const c' \<Rightarrow> if c = c' then ({c}, 0, {[]}) else ({c, c'}, 0, {})))"

fun eval_neg :: "nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow> ('a, nat) fo_t" where
  "eval_neg ns (AD, _, X) = (AD, length ns, nall_tuples AD (length ns) - X)"

definition "eval_conj_tuple AD ns\<phi> ns\<psi> xs ys =
  (let cxs = filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> isl x) (zip ns\<phi> xs);
    nxs = map fst (filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> \<not>isl x) (zip ns\<phi> xs));
    cys = filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> isl y) (zip ns\<psi> ys);
    nys = map fst (filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> \<not>isl y) (zip ns\<psi> ys)) in
  fo_nmlz AD ` ext_tuple {} (sort (ns\<phi> @ map fst cys)) nys (map snd (merge (zip ns\<phi> xs) cys)) \<inter>
  fo_nmlz AD ` ext_tuple {} (sort (ns\<psi> @ map fst cxs)) nxs (map snd (merge (zip ns\<psi> ys) cxs)))"

definition "eval_conj_set AD ns\<phi> X\<phi> ns\<psi> X\<psi> = \<Union>((\<lambda>xs. \<Union>(eval_conj_tuple AD ns\<phi> ns\<psi> xs ` X\<psi>)) ` X\<phi>)"

definition "idx_join AD ns ns\<phi> X\<phi> ns\<psi> X\<psi> =
  (let idx\<phi>' = cluster (Some \<circ> (\<lambda>xs. fo_nmlz AD (proj_tuple ns (zip ns\<phi> xs)))) X\<phi>;
  idx\<psi>' = cluster (Some \<circ> (\<lambda>ys. fo_nmlz AD (proj_tuple ns (zip ns\<psi> ys)))) X\<psi> in
  set_of_idx (mapping_join (\<lambda>X\<phi>'' X\<psi>''. eval_conj_set AD ns\<phi> X\<phi>'' ns\<psi> X\<psi>'') idx\<phi>' idx\<psi>'))"

fun eval_conj :: "nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow> nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow>
  ('a, nat) fo_t" where
  "eval_conj ns\<phi> (AD\<phi>, _, X\<phi>) ns\<psi> (AD\<psi>, _, X\<psi>) = (let AD = AD\<phi> \<union> AD\<psi>; AD\<Delta>\<phi> = AD - AD\<phi>; AD\<Delta>\<psi> = AD - AD\<psi>; ns = filter (\<lambda>n. n \<in> set ns\<psi>) ns\<phi> in
    (AD, card (set ns\<phi> \<union> set ns\<psi>), idx_join AD ns ns\<phi> (ad_agr_close_set AD\<Delta>\<phi> X\<phi>) ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> X\<psi>)))"

fun eval_ajoin :: "nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow> nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow>
  ('a, nat) fo_t" where
  "eval_ajoin ns\<phi> (AD\<phi>, _, X\<phi>) ns\<psi> (AD\<psi>, _, X\<psi>) = (let AD = AD\<phi> \<union> AD\<psi>; AD\<Delta>\<phi> = AD - AD\<phi>; AD\<Delta>\<psi> = AD - AD\<psi>;
    ns = filter (\<lambda>n. n \<in> set ns\<psi>) ns\<phi>; ns\<phi>' = filter (\<lambda>n. n \<notin> set ns\<phi>) ns\<psi>;
    idx\<phi> = cluster (Some \<circ> (\<lambda>xs. fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> xs)))) (ad_agr_close_set AD\<Delta>\<phi> X\<phi>);
    idx\<psi> = cluster (Some \<circ> (\<lambda>ys. fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<psi> ys)))) X\<psi> in
    (AD, card (set ns\<phi> \<union> set ns\<psi>), set_of_idx (Mapping.map_values (\<lambda>xs X. case Mapping.lookup idx\<psi> xs of Some Y \<Rightarrow>
      idx_join AD ns ns\<phi> X ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {xs} - Y)) | _ \<Rightarrow> ext_tuple_set AD ns\<phi> ns\<phi>' X) idx\<phi>)))"

fun eval_disj :: "nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow> nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow>
  ('a, nat) fo_t" where
  "eval_disj ns\<phi> (AD\<phi>, _, X\<phi>) ns\<psi> (AD\<psi>, _, X\<psi>) = (let AD = AD\<phi> \<union> AD\<psi>;
    ns\<phi>' = filter (\<lambda>n. n \<notin> set ns\<phi>) ns\<psi>;
    ns\<psi>' = filter (\<lambda>n. n \<notin> set ns\<psi>) ns\<phi>;
    AD\<Delta>\<phi> = AD - AD\<phi>; AD\<Delta>\<psi> = AD - AD\<psi> in
    (AD, card (set ns\<phi> \<union> set ns\<psi>),
      ext_tuple_set AD ns\<phi> ns\<phi>' (ad_agr_close_set AD\<Delta>\<phi> X\<phi>) \<union>
      ext_tuple_set AD ns\<psi> ns\<psi>' (ad_agr_close_set AD\<Delta>\<psi> X\<psi>)))"

fun eval_exists :: "nat \<Rightarrow> nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow> ('a, nat) fo_t" where
  "eval_exists i ns (AD, _, X) = (case pos i ns of Some j \<Rightarrow>
    (AD, length ns - 1, fo_nmlz AD ` rem_nth j ` X)
  | None \<Rightarrow> (AD, length ns, X))"

fun eval_forall :: "nat \<Rightarrow> nat list \<Rightarrow> ('a, nat) fo_t \<Rightarrow> ('a, nat) fo_t" where
  "eval_forall i ns (AD, _, X) = (case pos i ns of Some j \<Rightarrow>
    let n = card AD in
    (AD, length ns - 1, Mapping.keys (Mapping.filter (\<lambda>t Z. n + card (Inr -` set t) + 1 \<le> card Z)
      (cluster (Some \<circ> (\<lambda>ts. fo_nmlz AD (rem_nth j ts))) X)))
    | None \<Rightarrow> (AD, length ns, X))"

lemma combine_map2: assumes "length ys = length xs" "length ys' = length xs'"
  "distinct xs" "distinct xs'" "set xs \<inter> set xs' = {}"
  shows "\<exists>f. ys = map f xs \<and> ys' = map f xs'"
proof -
  obtain f g where fg_def: "ys = map f xs" "ys' = map g xs'"
    using assms exists_map
    by metis
  show ?thesis
    using assms
    by (auto simp: fg_def intro!: exI[of _ "\<lambda>x. if x \<in> set xs then f x else g x"])
qed

lemma combine_map3: assumes "length ys = length xs" "length ys' = length xs'" "length ys'' = length xs''"
  "distinct xs" "distinct xs'" "distinct xs''" "set xs \<inter> set xs' = {}" "set xs \<inter> set xs'' = {}" "set xs' \<inter> set xs'' = {}"
  shows "\<exists>f. ys = map f xs \<and> ys' = map f xs' \<and> ys'' = map f xs''"
proof -
  obtain f g h where fgh_def: "ys = map f xs" "ys' = map g xs'" "ys'' = map h xs''"
    using assms exists_map
    by metis
  show ?thesis
    using assms
    by (auto simp: fgh_def intro!: exI[of _ "\<lambda>x. if x \<in> set xs then f x else if x \<in> set xs' then g x else h x"])
qed

lemma distinct_set_zip: "length nsx = length xs \<Longrightarrow> distinct nsx \<Longrightarrow>
  (a, b) \<in> set (zip nsx xs) \<Longrightarrow> (a, ba) \<in> set (zip nsx xs) \<Longrightarrow> b = ba"
  by (induction nsx xs rule: list_induct2) (auto dest: set_zip_leftD)

lemma fo_nmlz_idem_isl:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> (case x of Inl z \<Rightarrow> z \<in> X | _ \<Rightarrow> False)"
  shows "fo_nmlz X xs = xs"
proof -
  have F1: "Inl x \<in> set xs \<Longrightarrow> x \<in> X" for x
    using assms[of "Inl x"]
    by auto
  have F2: "List.map_filter (case_sum Map.empty Some) xs = []"
    using assms
    by (induction xs) (fastforce simp: List.map_filter_def split: sum.splits)+
  show ?thesis
    by (rule fo_nmlz_idem) (auto simp: fo_nmlzd_def nats_def F2 intro: F1)
qed

lemma set_zip_mapI: "x \<in> set xs \<Longrightarrow> (f x, g x) \<in> set (zip (map f xs) (map g xs))"
  by (induction xs) auto

lemma ad_agr_list_fo_nmlzd_isl:
  assumes "ad_agr_list X (map f xs) (map g xs)" "fo_nmlzd X (map f xs)" "x \<in> set xs" "isl (f x)"
  shows "f x = g x"
proof -
  have AD: "ad_equiv_pair X (f x, g x)"
    using assms(1) set_zip_mapI[OF assms(3)]
    by (auto simp: ad_agr_list_def ad_equiv_list_def split: sum.splits)
  then show ?thesis
    using assms(2-)
    by (auto simp: fo_nmlzd_def) (metis AD ad_equiv_pair.simps ad_equiv_pair_mono image_eqI sum.collapse(1) vimageI)
qed

lemma eval_conj_tuple_close_empty2:
  assumes "fo_nmlzd X xs" "fo_nmlzd Y ys"
    "length nsx = length xs" "length nsy = length ys"
    "sorted_distinct nsx" "sorted_distinct nsy"
    "sorted_distinct ns" "set ns \<subseteq> set nsx \<inter> set nsy"
    "fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsx xs)) \<noteq> fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsy ys)) \<or>
      (proj_tuple ns (zip nsx xs) \<noteq> proj_tuple ns (zip nsy ys) \<and>
      (\<forall>x \<in> set (proj_tuple ns (zip nsx xs)). isl x) \<and> (\<forall>y \<in> set (proj_tuple ns (zip nsy ys)). isl y))"
    "xs' \<in> ad_agr_close ((X \<union> Y) - X) xs" "ys' \<in> ad_agr_close ((X \<union> Y) - Y) ys"
  shows "eval_conj_tuple (X \<union> Y) nsx nsy xs' ys' = {}"
proof -
  define cxs where "cxs = filter (\<lambda>(n, x). n \<notin> set nsy \<and> isl x) (zip nsx xs')"
  define nxs where "nxs = map fst (filter (\<lambda>(n, x). n \<notin> set nsy \<and> \<not>isl x) (zip nsx xs'))"
  define cys where "cys = filter (\<lambda>(n, y). n \<notin> set nsx \<and> isl y) (zip nsy ys')"
  define nys where "nys = map fst (filter (\<lambda>(n, y). n \<notin> set nsx \<and> \<not>isl y) (zip nsy ys'))"
  define both where "both = sorted_list_of_set (set nsx \<union> set nsy)"
  have close: "fo_nmlzd (X \<union> Y) xs'" "ad_agr_list X xs xs'" "fo_nmlzd (X \<union> Y) ys'" "ad_agr_list Y ys ys'"
    using ad_agr_close_sound[OF assms(10) assms(1)] ad_agr_close_sound[OF assms(11) assms(2)]
    by (auto simp add: sup_left_commute)
  have close': "length xs' = length xs" "length ys' = length ys"
    using close
    by (auto simp: ad_agr_list_length)
  have len_sort: "length (sort (nsx @ map fst cys)) = length (map snd (merge (zip nsx xs') cys))"
    "length (sort (nsy @ map fst cxs)) = length (map snd (merge (zip nsy ys') cxs))"
    by (auto simp: merge_length assms(3,4) close')
  {
    fix zs
    assume "zs \<in> fo_nmlz (X \<union> Y) ` (\<lambda>fs. map snd (merge (zip (sort (nsx @ map fst cys)) (map snd (merge (zip nsx xs') cys))) (zip nys fs))) `
      nall_tuples_rec {} (card (Inr -` set (map snd (merge (zip nsx xs') cys)))) (length nys)"
    "zs \<in> fo_nmlz (X \<union> Y) ` (\<lambda>fs. map snd (merge (zip (sort (nsy @ map fst cxs)) (map snd (merge (zip nsy ys') cxs))) (zip nxs fs))) `
      nall_tuples_rec {} (card (Inr -` set (map snd (merge (zip nsy ys') cxs)))) (length nxs)"
    then obtain zxs zys where nall: "zxs \<in> nall_tuples_rec {} (card (Inr -` set (map snd (merge (zip nsx xs') cys)))) (length nys)"
      "zs = fo_nmlz (X \<union> Y) (map snd (merge (zip (sort (nsx @ map fst cys)) (map snd (merge (zip nsx xs') cys))) (zip nys zxs)))"
      "zys \<in> nall_tuples_rec {} (card (Inr -` set (map snd (merge (zip nsy ys') cxs)))) (length nxs)"
      "zs = fo_nmlz (X \<union> Y) (map snd (merge (zip (sort (nsy @ map fst cxs)) (map snd (merge (zip nsy ys') cxs))) (zip nxs zys)))"
      by auto
    have len_zs: "length zxs = length nys" "length zys = length nxs"
      using nall(1,3)
      by (auto dest: nall_tuples_rec_length)
    have aux: "sorted_distinct (map fst cxs)" "sorted_distinct nxs" "sorted_distinct nsy"
      "sorted_distinct (map fst cys)" "sorted_distinct nys" "sorted_distinct nsx"
      "set (map fst cxs) \<inter> set nsy = {}" "set (map fst cxs) \<inter> set nxs = {}" "set nsy \<inter> set nxs = {}"
      "set (map fst cys) \<inter> set nsx = {}" "set (map fst cys) \<inter> set nys = {}" "set nsx \<inter> set nys = {}"
      using assms(3,4,5,6) close' distinct_set_zip
      by (auto simp: cxs_def nxs_def cys_def nys_def sorted_filter distinct_map_fst_filter)
         (smt (z3) distinct_set_zip)+
    obtain xf where xf_def: "map snd cxs = map xf (map fst cxs)" "ys' = map xf nsy" "zys = map xf nxs"
      using combine_map3[where ?ys="map snd cxs" and ?xs="map fst cxs" and ?ys'=ys' and ?xs'=nsy and ?ys''=zys and ?xs''=nxs] assms(4) aux close'
      by (auto simp: len_zs)
    obtain ysf where ysf_def: "ys = map ysf nsy"
      using assms(4,6) exists_map
      by auto
    obtain xg where xg_def: "map snd cys = map xg (map fst cys)" "xs' = map xg nsx" "zxs = map xg nys"
      using combine_map3[where ?ys="map snd cys" and ?xs="map fst cys" and ?ys'=xs' and ?xs'=nsx and ?ys''=zxs and ?xs''=nys] assms(3) aux close'
      by (auto simp: len_zs)
    obtain xsf where xsf_def: "xs = map xsf nsx"
      using assms(3,5) exists_map
      by auto
    have set_cxs_nxs: "set (map fst cxs @ nxs) = set nsx - set nsy"
      using assms(3)
      unfolding cxs_def nxs_def close'[symmetric]
      by (induction nsx xs' rule: list_induct2) auto
    have set_cys_nys: "set (map fst cys @ nys) = set nsy - set nsx"
      using assms(4)
      unfolding cys_def nys_def close'[symmetric]
      by (induction nsy ys' rule: list_induct2) auto
    have sort_sort_both_xs: "sort (sort (nsy @ map fst cxs) @ nxs) = both"
      apply (rule sorted_distinct_set_unique)
      using assms(3,5,6) close' set_cxs_nxs
      by (auto simp: both_def nxs_def cxs_def intro: distinct_map_fst_filter)
         (metis (no_types, lifting) distinct_set_zip)
    have sort_sort_both_ys: "sort (sort (nsx @ map fst cys) @ nys) = both"
      apply (rule sorted_distinct_set_unique)
      using assms(4,5,6) close' set_cys_nys
      by (auto simp: both_def nys_def cys_def intro: distinct_map_fst_filter)
         (metis (no_types, lifting) distinct_set_zip)
    have "map snd (merge (zip nsy ys') cxs) = map xf (sort (nsy @ map fst cxs))"
      using merge_map[where ?\<sigma>=xf and ?ns=nsy and ?ms="map fst cxs"] assms(6) aux
      unfolding xf_def(1)[symmetric] xf_def(2)
      by (auto simp: zip_map_fst_snd)
    then have zs_xf: "zs = fo_nmlz (X \<union> Y) (map xf both)"
      using merge_map[where \<sigma>=xf and ?ns="sort (nsy @ map fst cxs)" and ?ms=nxs] aux
      by (fastforce simp: nall(4) xf_def(3) sort_sort_both_xs)
    have "map snd (merge (zip nsx xs') cys) = map xg (sort (nsx @ map fst cys))"
      using merge_map[where ?\<sigma>=xg and ?ns=nsx and ?ms="map fst cys"] assms(5) aux
      unfolding xg_def(1)[symmetric] xg_def(2)
      by (fastforce simp: zip_map_fst_snd)
    then have zs_xg: "zs = fo_nmlz (X \<union> Y) (map xg both)"
      using merge_map[where \<sigma>=xg and ?ns="sort (nsx @ map fst cys)" and ?ms=nys] aux
      by (fastforce simp: nall(2) xg_def(3) sort_sort_both_ys)
    have proj_map: "proj_tuple ns (zip nsx xs') = map xg ns" "proj_tuple ns (zip nsy ys') = map xf ns"
      "proj_tuple ns (zip nsx xs) = map xsf ns" "proj_tuple ns (zip nsy ys) = map ysf ns"
      unfolding xf_def(2) xg_def(2) xsf_def ysf_def
      using assms(5,6,7,8) proj_tuple_map
      by auto
    have "ad_agr_list (X \<union> Y) (map xg both) (map xf both)"
      using zs_xg zs_xf
      by (fastforce dest: fo_nmlz_eqD)
    then have "ad_agr_list (X \<union> Y) (proj_tuple ns (zip nsx xs')) (proj_tuple ns (zip nsy ys'))"
      using assms(8)
      unfolding proj_map
      by (fastforce simp: both_def intro: ad_agr_list_subset[rotated])
    then have fo_nmlz_Un: "fo_nmlz (X \<union> Y) (proj_tuple ns (zip nsx xs')) = fo_nmlz (X \<union> Y) (proj_tuple ns (zip nsy ys'))"
      by (auto intro: fo_nmlz_eqI)
    have "False"
      using assms(9)
    proof (rule disjE)
      assume c: "fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsx xs)) \<noteq> fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsy ys))"
      have fo_nmlz_Int: "fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsx xs')) = fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsy ys'))"
        using fo_nmlz_Un
        by (rule fo_nmlz_eqI[OF ad_agr_list_mono, rotated, OF fo_nmlz_eqD]) auto
      have proj_xs: "fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsx xs)) = fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsx xs'))"
        unfolding proj_map
        apply (rule fo_nmlz_eqI)
        apply (rule ad_agr_list_mono[OF Int_lower1])
        apply (rule ad_agr_list_subset[OF _ close(2)[unfolded xsf_def xg_def(2)]])
        using assms(8)
        apply (auto)
        done
      have proj_ys: "fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsy ys)) = fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsy ys'))"
        unfolding proj_map
        apply (rule fo_nmlz_eqI)
        apply (rule ad_agr_list_mono[OF Int_lower2])
        apply (rule ad_agr_list_subset[OF _ close(4)[unfolded ysf_def xf_def(2)]])
        using assms(8)
        apply (auto)
        done
      show "False"
        using c fo_nmlz_Int proj_xs proj_ys
        by auto
    next
      assume c: "proj_tuple ns (zip nsx xs) \<noteq> proj_tuple ns (zip nsy ys) \<and>
      (\<forall>x\<in>set (proj_tuple ns (zip nsx xs)). isl x) \<and> (\<forall>y\<in>set (proj_tuple ns (zip nsy ys)). isl y)"
      have "case x of Inl z \<Rightarrow> z \<in> X \<union> Y | Inr b \<Rightarrow> False" if "x \<in> set (proj_tuple ns (zip nsx xs'))" for x
        using close(2) assms(1,8) c that ad_agr_list_fo_nmlzd_isl[where ?X=X and ?f=xsf and ?g=xg and ?xs=nsx]
        unfolding proj_map
        unfolding xsf_def xg_def(2)
        apply (auto simp: fo_nmlzd_def split: sum.splits)
         apply (metis image_eqI subsetD vimageI)
        apply (metis subsetD sum.disc(2))
        done
      then have E1: "fo_nmlz (X \<union> Y) (proj_tuple ns (zip nsx xs')) = proj_tuple ns (zip nsx xs')"
        by (rule fo_nmlz_idem_isl)
      have "case y of Inl z \<Rightarrow> z \<in> X \<union> Y | Inr b \<Rightarrow> False" if "y \<in> set (proj_tuple ns (zip nsy ys'))" for y
        using close(4) assms(2,8) c that ad_agr_list_fo_nmlzd_isl[where ?X=Y and ?f=ysf and ?g=xf and ?xs=nsy]
        unfolding proj_map
        unfolding ysf_def xf_def(2)
        apply (auto simp: fo_nmlzd_def split: sum.splits)
         apply (metis image_eqI subsetD vimageI)
        apply (metis subsetD sum.disc(2))
        done
      then have E2: "fo_nmlz (X \<union> Y) (proj_tuple ns (zip nsy ys')) = proj_tuple ns (zip nsy ys')"
        by (rule fo_nmlz_idem_isl)
      have ad: "ad_agr_list X (map xsf ns) (map xg ns)"
        using assms(8) close(2)[unfolded xsf_def xg_def(2)] ad_agr_list_subset
        by blast
      have "\<forall>x\<in>set (proj_tuple ns (zip nsx xs)). isl x"
        using c
        by auto
      then have E3: "proj_tuple ns (zip nsx xs) = proj_tuple ns (zip nsx xs')"
        using assms(8)
        unfolding proj_map
        apply (induction ns)
        using ad_agr_list_fo_nmlzd_isl[OF close(2)[unfolded xsf_def xg_def(2)] assms(1)[unfolded xsf_def]]
        by auto
      have "\<forall>x\<in>set (proj_tuple ns (zip nsy ys)). isl x"
        using c
        by auto
      then have E4: "proj_tuple ns (zip nsy ys) = proj_tuple ns (zip nsy ys')"
        using assms(8)
        unfolding proj_map
        apply (induction ns)
        using ad_agr_list_fo_nmlzd_isl[OF close(4)[unfolded ysf_def xf_def(2)] assms(2)[unfolded ysf_def]]
        by auto
      show "False"
        using c fo_nmlz_Un
        unfolding E1 E2 E3 E4
        by auto
    qed
  }
  then show ?thesis
    by (auto simp: eval_conj_tuple_def Let_def cxs_def[symmetric] nxs_def[symmetric] cys_def[symmetric] nys_def[symmetric]
        ext_tuple_eq[OF len_sort(1)] ext_tuple_eq[OF len_sort(2)])
qed

lemma eval_conj_tuple_close_empty:
  assumes "fo_nmlzd X xs" "fo_nmlzd Y ys"
    "length nsx = length xs" "length nsy = length ys"
    "sorted_distinct nsx" "sorted_distinct nsy"
    "ns = filter (\<lambda>n. n \<in> set nsy) nsx"
    "fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsx xs)) \<noteq> fo_nmlz (X \<inter> Y) (proj_tuple ns (zip nsy ys))"
    "xs' \<in> ad_agr_close ((X \<union> Y) - X) xs" "ys' \<in> ad_agr_close ((X \<union> Y) - Y) ys"
  shows "eval_conj_tuple (X \<union> Y) nsx nsy xs' ys' = {}"
proof -
  have aux: "sorted_distinct ns" "set ns \<subseteq> set nsx \<inter> set nsy"
    using assms(5) sorted_filter[of id]
    by (auto simp: assms(7))
  show ?thesis
    using eval_conj_tuple_close_empty2[OF assms(1-6) aux] assms(8-)
    by auto
qed

lemma eval_conj_tuple_empty2:
  assumes "fo_nmlzd Z xs" "fo_nmlzd Z ys"
    "length nsx = length xs" "length nsy = length ys"
    "sorted_distinct nsx" "sorted_distinct nsy"
    "sorted_distinct ns" "set ns \<subseteq> set nsx \<inter> set nsy"
    "fo_nmlz Z (proj_tuple ns (zip nsx xs)) \<noteq> fo_nmlz Z (proj_tuple ns (zip nsy ys)) \<or>
      (proj_tuple ns (zip nsx xs) \<noteq> proj_tuple ns (zip nsy ys) \<and>
      (\<forall>x \<in> set (proj_tuple ns (zip nsx xs)). isl x) \<and> (\<forall>y \<in> set (proj_tuple ns (zip nsy ys)). isl y))"
  shows "eval_conj_tuple Z nsx nsy xs ys = {}"
  using eval_conj_tuple_close_empty2[OF assms(1-8)] assms(9) ad_agr_close_empty assms(1-2)
  by fastforce

lemma eval_conj_tuple_empty:
  assumes "fo_nmlzd Z xs" "fo_nmlzd Z ys"
    "length nsx = length xs" "length nsy = length ys"
    "sorted_distinct nsx" "sorted_distinct nsy"
    "ns = filter (\<lambda>n. n \<in> set nsy) nsx"
    "fo_nmlz Z (proj_tuple ns (zip nsx xs)) \<noteq> fo_nmlz Z (proj_tuple ns (zip nsy ys))"
  shows "eval_conj_tuple Z nsx nsy xs ys = {}"
proof -
  have aux: "sorted_distinct ns" "set ns \<subseteq> set nsx \<inter> set nsy"
    using assms(5) sorted_filter[of id]
    by (auto simp: assms(7))
  show ?thesis
    using eval_conj_tuple_empty2[OF assms(1-6) aux] assms(8-)
    by auto
qed

lemma nall_tuples_rec_filter:
  assumes "xs \<in> nall_tuples_rec AD n (length xs)" "ys = filter (\<lambda>x. \<not>isl x) xs"
  shows "ys \<in> nall_tuples_rec {} n (length ys)"
  using assms
proof (induction xs arbitrary: n ys)
  case (Cons x xs)
  then show ?case
  proof (cases x)
    case (Inr b)
    have b_le_i: "b \<le> n"
      using Cons(2)
      by (auto simp: Inr)
    obtain zs where ys_def: "ys = Inr b # zs" "zs = filter (\<lambda>x. \<not> isl x) xs"
      using Cons(3)
      by (auto simp: Inr)
    show ?thesis
    proof (cases "b < n")
      case True
      then show ?thesis
        using Cons(1)[OF _ ys_def(2), of n] Cons(2)
        by (auto simp: Inr ys_def(1))
    next
      case False
      then show ?thesis
        using Cons(1)[OF _ ys_def(2), of "Suc n"] Cons(2)
        by (auto simp: Inr ys_def(1))
    qed
  qed auto
qed auto

lemma nall_tuples_rec_filter_rev:
  assumes "ys \<in> nall_tuples_rec {} n (length ys)" "ys = filter (\<lambda>x. \<not>isl x) xs"
    "Inl -` set xs \<subseteq> AD"
  shows "xs \<in> nall_tuples_rec AD n (length xs)"
  using assms
proof (induction xs arbitrary: n ys)
  case (Cons x xs)
  show ?case
  proof (cases x)
    case (Inl a)
    have a_AD: "a \<in> AD"
      using Cons(4)
      by (auto simp: Inl)
    show ?thesis
      using Cons(1)[OF Cons(2)] Cons(3,4) a_AD
      by (auto simp: Inl)
  next
    case (Inr b)
    obtain zs where ys_def: "ys = Inr b # zs" "zs = filter (\<lambda>x. \<not> isl x) xs"
      using Cons(3)
      by (auto simp: Inr)
    show ?thesis
      using Cons(1)[OF _ ys_def(2)] Cons(2,4)
      by (fastforce simp: ys_def(1) Inr)
  qed
qed auto

lemma eval_conj_set_aux:
  fixes AD :: "'a set"
  assumes ns\<phi>'_def: "ns\<phi>' = filter (\<lambda>n. n \<notin> set ns\<phi>) ns\<psi>"
    and ns\<psi>'_def: "ns\<psi>' = filter (\<lambda>n. n \<notin> set ns\<psi>) ns\<phi>"
    and X\<phi>_def: "X\<phi> = fo_nmlz AD ` proj_vals R\<phi> ns\<phi>"
    and X\<psi>_def: "X\<psi> = fo_nmlz AD ` proj_vals R\<psi> ns\<psi>"
    and distinct: "sorted_distinct ns\<phi>" "sorted_distinct ns\<psi>"
    and cxs_def: "cxs = filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> isl x) (zip ns\<phi> xs)"
    and nxs_def: "nxs = map fst (filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> \<not>isl x) (zip ns\<phi> xs))"
    and cys_def: "cys = filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> isl y) (zip ns\<psi> ys)"
    and nys_def: "nys = map fst (filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> \<not>isl y) (zip ns\<psi> ys))"
    and xs_ys_def: "xs \<in> X\<phi>" "ys \<in> X\<psi>"
    and \<sigma>xs_def: "xs = map \<sigma>xs ns\<phi>" "fs\<phi> = map \<sigma>xs ns\<phi>'"
    and \<sigma>ys_def: "ys = map \<sigma>ys ns\<psi>" "fs\<psi> = map \<sigma>ys ns\<psi>'"
    and fs\<phi>_def: "fs\<phi> \<in> nall_tuples_rec AD (card (Inr -` set xs)) (length ns\<phi>')"
    and fs\<psi>_def: "fs\<psi> \<in> nall_tuples_rec AD (card (Inr -` set ys)) (length ns\<psi>')"
    and ad_agr: "ad_agr_list AD (map \<sigma>ys (sort (ns\<psi> @ ns\<psi>'))) (map \<sigma>xs (sort (ns\<phi> @ ns\<phi>')))"
  shows
    "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) =
      map snd (merge (zip (sort (ns\<phi> @ map fst cys)) (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))
    (zip nys (map \<sigma>xs nys)))" and
    "map snd (merge (zip ns\<phi> xs) cys) = map \<sigma>xs (sort (ns\<phi> @ map fst cys))" and
    "map \<sigma>xs nys \<in>
      nall_tuples_rec {} (card (Inr -` set (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))) (length nys)"
proof -
  have len_xs_ys: "length xs = length ns\<phi>" "length ys = length ns\<psi>"
    using xs_ys_def
    by (auto simp: X\<phi>_def X\<psi>_def proj_vals_def fo_nmlz_length)
  have len_fs\<phi>: "length fs\<phi> = length ns\<phi>'"
    using \<sigma>xs_def(2)
    by auto
  have set_ns\<phi>': "set ns\<phi>' = set (map fst cys) \<union> set nys"
    using len_xs_ys(2)
    by (auto simp: ns\<phi>'_def cys_def nys_def dest: set_zip_leftD)
       (metis (no_types, lifting) image_eqI in_set_impl_in_set_zip1 mem_Collect_eq
        prod.sel(1) split_conv)
  have "\<And>x. Inl x \<in> set xs \<union> set fs\<phi> \<Longrightarrow> x \<in> AD" "\<And>y. Inl y \<in> set ys \<union> set fs\<psi> \<Longrightarrow> y \<in> AD"
    using xs_ys_def fo_nmlz_set[of AD] nall_tuples_rec_Inl[OF fs\<phi>_def]
      nall_tuples_rec_Inl[OF fs\<psi>_def]
    by (auto simp: X\<phi>_def X\<psi>_def)
  then have Inl_xs_ys:
    "\<And>n. n \<in> set ns\<phi> \<union> set ns\<psi> \<Longrightarrow> isl (\<sigma>xs n) \<longleftrightarrow> (\<exists>x. \<sigma>xs n = Inl x \<and> x \<in> AD)"
    "\<And>n. n \<in> set ns\<phi> \<union> set ns\<psi> \<Longrightarrow> isl (\<sigma>ys n) \<longleftrightarrow> (\<exists>y. \<sigma>ys n = Inl y \<and> y \<in> AD)"
    unfolding \<sigma>xs_def \<sigma>ys_def ns\<phi>'_def ns\<psi>'_def
    by (auto simp: isl_def) (smt imageI mem_Collect_eq)+
  have sort_sort: "sort (ns\<phi> @ ns\<phi>') = sort (ns\<psi> @ ns\<psi>')"
    apply (rule sorted_distinct_set_unique)
    using distinct
    by (auto simp: ns\<phi>'_def ns\<psi>'_def)
  have isl_iff: "\<And>n. n \<in> set ns\<phi>' \<union> set ns\<psi>' \<Longrightarrow> isl (\<sigma>xs n) \<or> isl (\<sigma>ys n) \<Longrightarrow> \<sigma>xs n = \<sigma>ys n"
    using ad_agr Inl_xs_ys
    unfolding sort_sort[symmetric] ad_agr_list_link[symmetric]
    unfolding ns\<phi>'_def ns\<psi>'_def
    apply (auto simp: ad_agr_sets_def)
    unfolding ad_equiv_pair.simps
       apply (metis (no_types, lifting) UnI2 image_eqI mem_Collect_eq)
      apply (metis (no_types, lifting) UnI2 image_eqI mem_Collect_eq)
     apply (metis (no_types, lifting) UnI1 image_eqI)+
    done
  have "\<And>n. n \<in> set (map fst cys) \<Longrightarrow> isl (\<sigma>xs n)"
    "\<And>n. n \<in> set (map fst cxs) \<Longrightarrow> isl (\<sigma>ys n)"
    using isl_iff
    by (auto simp: cys_def ns\<phi>'_def \<sigma>ys_def(1) cxs_def ns\<psi>'_def \<sigma>xs_def(1) set_zip)
       (metis nth_mem)+
  then have Inr_sort: "Inr -` set (map \<sigma>xs (sort (ns\<phi> @ map fst cys))) = Inr -` set xs"
    unfolding \<sigma>xs_def(1) \<sigma>ys_def(1)
    by (auto simp: zip_map_fst_snd dest: set_zip_leftD)
       (metis fst_conv image_iff sum.disc(2))+
  have map_nys: "map \<sigma>xs nys = filter (\<lambda>x. \<not>isl x) fs\<phi>"
    using isl_iff[unfolded ns\<phi>'_def]
    unfolding nys_def \<sigma>ys_def(1) \<sigma>xs_def(2) ns\<phi>'_def filter_map
    by (induction ns\<psi>) force+
  have map_nys_in_nall: "map \<sigma>xs nys \<in> nall_tuples_rec {} (card (Inr -` set xs)) (length nys)"
    using nall_tuples_rec_filter[OF fs\<phi>_def[folded len_fs\<phi>] map_nys]
    by auto
  have map_cys: "map snd cys = map \<sigma>xs (map fst cys)"
    using isl_iff
    by (auto simp: cys_def set_zip ns\<phi>'_def \<sigma>ys_def(1)) (metis nth_mem)
  show merge_xs_cys: "map snd (merge (zip ns\<phi> xs) cys) = map \<sigma>xs (sort (ns\<phi> @ map fst cys))"
    apply (subst zip_map_fst_snd[of cys, symmetric])
    unfolding \<sigma>xs_def(1) map_cys
    apply (rule merge_map)
    using distinct
    by (auto simp: cys_def \<sigma>ys_def sorted_filter distinct_map_filter map_fst_zip_take)
  have merge_nys_prems: "sorted_distinct (sort (ns\<phi> @ map fst cys))" "sorted_distinct nys"
    "set (sort (ns\<phi> @ map fst cys)) \<inter> set nys = {}"
    using distinct len_xs_ys(2)
    by (auto simp: cys_def nys_def distinct_map_filter sorted_filter)
       (metis eq_key_imp_eq_value map_fst_zip)
  have map_snd_merge_nys: "map \<sigma>xs (sort (sort (ns\<phi> @ map fst cys) @ nys)) =
    map snd (merge (zip (sort (ns\<phi> @ map fst cys)) (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))
      (zip nys (map \<sigma>xs nys)))"
    by (rule merge_map[OF merge_nys_prems, symmetric])
  have sort_sort_nys: "sort (sort (ns\<phi> @ map fst cys) @ nys) = sort (ns\<phi> @ ns\<phi>')"
    apply (rule sorted_distinct_set_unique)
    using distinct merge_nys_prems set_ns\<phi>'
    by (auto simp: cys_def nys_def ns\<phi>'_def dest: set_zip_leftD)
  have map_merge_fs\<phi>: "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) = map \<sigma>xs (sort (ns\<phi> @ ns\<phi>'))"
    unfolding \<sigma>xs_def
    apply (rule merge_map)
    using distinct sorted_filter[of id]
    by (auto simp: ns\<phi>'_def)
  show "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) =
    map snd (merge (zip (sort (ns\<phi> @ map fst cys)) (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))
    (zip nys (map \<sigma>xs nys)))"
    unfolding map_merge_fs\<phi> map_snd_merge_nys[unfolded sort_sort_nys]
    by auto
  show "map \<sigma>xs nys \<in> nall_tuples_rec {}
    (card (Inr -` set (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))) (length nys)"
    using map_nys_in_nall
    unfolding Inr_sort[symmetric]
    by auto
qed

lemma eval_conj_set_aux':
  fixes AD :: "'a set"
  assumes ns\<phi>'_def: "ns\<phi>' = filter (\<lambda>n. n \<notin> set ns\<phi>) ns\<psi>"
    and ns\<psi>'_def: "ns\<psi>' = filter (\<lambda>n. n \<notin> set ns\<psi>) ns\<phi>"
    and X\<phi>_def: "X\<phi> = fo_nmlz AD ` proj_vals R\<phi> ns\<phi>"
    and X\<psi>_def: "X\<psi> = fo_nmlz AD ` proj_vals R\<psi> ns\<psi>"
    and distinct: "sorted_distinct ns\<phi>" "sorted_distinct ns\<psi>"
    and cxs_def: "cxs = filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> isl x) (zip ns\<phi> xs)"
    and nxs_def: "nxs = map fst (filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> \<not>isl x) (zip ns\<phi> xs))"
    and cys_def: "cys = filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> isl y) (zip ns\<psi> ys)"
    and nys_def: "nys = map fst (filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> \<not>isl y) (zip ns\<psi> ys))"
    and xs_ys_def: "xs \<in> X\<phi>" "ys \<in> X\<psi>"
    and \<sigma>xs_def: "xs = map \<sigma>xs ns\<phi>" "map snd cys = map \<sigma>xs (map fst cys)"
      "ys\<psi> = map \<sigma>xs nys"
    and \<sigma>ys_def: "ys = map \<sigma>ys ns\<psi>" "map snd cxs = map \<sigma>ys (map fst cxs)"
      "xs\<phi> = map \<sigma>ys nxs"
    and fs\<phi>_def: "fs\<phi> = map \<sigma>xs ns\<phi>'"
    and fs\<psi>_def: "fs\<psi> = map \<sigma>ys ns\<psi>'"
    and ys\<psi>_def: "map \<sigma>xs nys \<in> nall_tuples_rec {}
      (card (Inr -` set (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))) (length nys)"
    and Inl_set_AD: "Inl -` (set (map snd cxs) \<union> set xs\<phi>) \<subseteq> AD"
      "Inl -` (set (map snd cys) \<union> set ys\<psi>) \<subseteq> AD"
    and ad_agr: "ad_agr_list AD (map \<sigma>ys (sort (ns\<psi> @ ns\<psi>'))) (map \<sigma>xs (sort (ns\<phi> @ ns\<phi>')))"
  shows
    "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) =
      map snd (merge (zip (sort (ns\<phi> @ map fst cys)) (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))
      (zip nys (map \<sigma>xs nys)))" and
    "map snd (merge (zip ns\<phi> xs) cys) = map \<sigma>xs (sort (ns\<phi> @ map fst cys))"
    "fs\<phi> \<in> nall_tuples_rec AD (card (Inr -` set xs)) (length ns\<phi>')"
proof -
  have len_xs_ys: "length xs = length ns\<phi>" "length ys = length ns\<psi>"
    using xs_ys_def
    by (auto simp: X\<phi>_def X\<psi>_def proj_vals_def fo_nmlz_length)
  have len_fs\<phi>: "length fs\<phi> = length ns\<phi>'"
    by (auto simp: fs\<phi>_def)
  have set_ns: "set ns\<phi>' = set (map fst cys) \<union> set nys"
    "set ns\<psi>' = set (map fst cxs) \<union> set nxs"
    using len_xs_ys
    by (auto simp: ns\<phi>'_def cys_def nys_def ns\<psi>'_def cxs_def nxs_def dest: set_zip_leftD)
       (metis (no_types, lifting) image_eqI in_set_impl_in_set_zip1 mem_Collect_eq
        prod.sel(1) split_conv)+
  then have set_\<sigma>_ns: "\<sigma>xs ` set ns\<psi>' \<union> \<sigma>xs ` set ns\<phi>' \<subseteq> set xs \<union> set (map snd cys) \<union> set ys\<psi>"
    "\<sigma>ys ` set ns\<phi>' \<union> \<sigma>ys ` set ns\<psi>' \<subseteq> set ys \<union> set (map snd cxs) \<union> set xs\<phi>"
    by (auto simp: \<sigma>xs_def \<sigma>ys_def ns\<phi>'_def ns\<psi>'_def)
  have Inl_sub_AD: "\<And>x. Inl x \<in> set xs \<union> set (map snd cys) \<union> set ys\<psi> \<Longrightarrow> x \<in> AD"
    "\<And>y. Inl y \<in> set ys \<union> set (map snd cxs) \<union> set xs\<phi> \<Longrightarrow> y \<in> AD"
    using xs_ys_def fo_nmlz_set[of AD] Inl_set_AD
    by (auto simp: X\<phi>_def X\<psi>_def) (metis in_set_zipE set_map subset_eq vimageI zip_map_fst_snd)+
  then have Inl_xs_ys:
    "\<And>n. n \<in> set ns\<phi>' \<union> set ns\<psi>' \<Longrightarrow> isl (\<sigma>xs n) \<longleftrightarrow> (\<exists>x. \<sigma>xs n = Inl x \<and> x \<in> AD)"
    "\<And>n. n \<in> set ns\<phi>' \<union> set ns\<psi>' \<Longrightarrow> isl (\<sigma>ys n) \<longleftrightarrow> (\<exists>y. \<sigma>ys n = Inl y \<and> y \<in> AD)"
    using set_\<sigma>_ns
    by (auto simp: isl_def rev_image_eqI)
  have sort_sort: "sort (ns\<phi> @ ns\<phi>') = sort (ns\<psi> @ ns\<psi>')"
    apply (rule sorted_distinct_set_unique)
    using distinct
    by (auto simp: ns\<phi>'_def ns\<psi>'_def)
  have isl_iff: "\<And>n. n \<in> set ns\<phi>' \<union> set ns\<psi>' \<Longrightarrow> isl (\<sigma>xs n) \<or> isl (\<sigma>ys n) \<Longrightarrow> \<sigma>xs n = \<sigma>ys n"
    using ad_agr Inl_xs_ys
    unfolding sort_sort[symmetric] ad_agr_list_link[symmetric]
    unfolding ns\<phi>'_def ns\<psi>'_def
    apply (auto simp: ad_agr_sets_def)
    unfolding ad_equiv_pair.simps
       apply (metis (no_types, lifting) UnI2 image_eqI mem_Collect_eq)
      apply (metis (no_types, lifting) UnI2 image_eqI mem_Collect_eq)
     apply (metis (no_types, lifting) UnI1 image_eqI)+
    done
  have "\<And>n. n \<in> set (map fst cys) \<Longrightarrow> isl (\<sigma>xs n)"
    "\<And>n. n \<in> set (map fst cxs) \<Longrightarrow> isl (\<sigma>ys n)"
    using isl_iff
    by (auto simp: cys_def ns\<phi>'_def \<sigma>ys_def(1) cxs_def ns\<psi>'_def \<sigma>xs_def(1) set_zip)
       (metis nth_mem)+
  then have Inr_sort: "Inr -` set (map \<sigma>xs (sort (ns\<phi> @ map fst cys))) = Inr -` set xs"
    unfolding \<sigma>xs_def(1) \<sigma>ys_def(1)
    by (auto simp: zip_map_fst_snd dest: set_zip_leftD)
       (metis fst_conv image_iff sum.disc(2))+
  have map_nys: "map \<sigma>xs nys = filter (\<lambda>x. \<not>isl x) fs\<phi>"
    using isl_iff[unfolded ns\<phi>'_def]
    unfolding nys_def \<sigma>ys_def(1) fs\<phi>_def ns\<phi>'_def
    by (induction ns\<psi>) force+
  have map_cys: "map snd cys = map \<sigma>xs (map fst cys)"
    using isl_iff
    by (auto simp: cys_def set_zip ns\<phi>'_def \<sigma>ys_def(1)) (metis nth_mem)
  show merge_xs_cys: "map snd (merge (zip ns\<phi> xs) cys) = map \<sigma>xs (sort (ns\<phi> @ map fst cys))"
    apply (subst zip_map_fst_snd[of cys, symmetric])
    unfolding \<sigma>xs_def(1) map_cys
    apply (rule merge_map)
    using distinct
    by (auto simp: cys_def \<sigma>ys_def sorted_filter distinct_map_filter map_fst_zip_take)
  have merge_nys_prems: "sorted_distinct (sort (ns\<phi> @ map fst cys))" "sorted_distinct nys"
    "set (sort (ns\<phi> @ map fst cys)) \<inter> set nys = {}"
    using distinct len_xs_ys(2)
    by (auto simp: cys_def nys_def distinct_map_filter sorted_filter)
       (metis eq_key_imp_eq_value map_fst_zip)
  have map_snd_merge_nys: "map \<sigma>xs (sort (sort (ns\<phi> @ map fst cys) @ nys)) =
    map snd (merge (zip (sort (ns\<phi> @ map fst cys)) (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))
      (zip nys (map \<sigma>xs nys)))"
    by (rule merge_map[OF merge_nys_prems, symmetric])
  have sort_sort_nys: "sort (sort (ns\<phi> @ map fst cys) @ nys) = sort (ns\<phi> @ ns\<phi>')"
    apply (rule sorted_distinct_set_unique)
    using distinct merge_nys_prems set_ns
    by (auto simp: cys_def nys_def ns\<phi>'_def dest: set_zip_leftD)
  have map_merge_fs\<phi>: "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) = map \<sigma>xs (sort (ns\<phi> @ ns\<phi>'))"
    unfolding \<sigma>xs_def fs\<phi>_def
    apply (rule merge_map)
    using distinct sorted_filter[of id]
    by (auto simp: ns\<phi>'_def)
  show "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) =
    map snd (merge (zip (sort (ns\<phi> @ map fst cys)) (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))
    (zip nys (map \<sigma>xs nys)))"
    unfolding map_merge_fs\<phi> map_snd_merge_nys[unfolded sort_sort_nys]
    by auto
  have "Inl -` set fs\<phi> \<subseteq> AD"
    using Inl_sub_AD(1) set_\<sigma>_ns
    by (force simp: fs\<phi>_def)
  then show "fs\<phi> \<in> nall_tuples_rec AD (card (Inr -` set xs)) (length ns\<phi>')"
    unfolding len_fs\<phi>[symmetric]
    using nall_tuples_rec_filter_rev[OF _ map_nys] ys\<psi>_def[unfolded Inr_sort]
    by auto
qed

lemma eval_conj_set_correct:
  assumes ns\<phi>'_def: "ns\<phi>' = filter (\<lambda>n. n \<notin> set ns\<phi>) ns\<psi>"
    and ns\<psi>'_def: "ns\<psi>' = filter (\<lambda>n. n \<notin> set ns\<psi>) ns\<phi>"
    and X\<phi>_def: "X\<phi> = fo_nmlz AD ` proj_vals R\<phi> ns\<phi>"
    and X\<psi>_def: "X\<psi> = fo_nmlz AD ` proj_vals R\<psi> ns\<psi>"
    and distinct: "sorted_distinct ns\<phi>" "sorted_distinct ns\<psi>"
  shows "eval_conj_set AD ns\<phi> X\<phi> ns\<psi> X\<psi> = ext_tuple_set AD ns\<phi> ns\<phi>' X\<phi> \<inter> ext_tuple_set AD ns\<psi> ns\<psi>' X\<psi>"
proof -
  have aux: "ext_tuple_set AD ns\<phi> ns\<phi>' X\<phi> = fo_nmlz AD ` \<Union>(ext_tuple AD ns\<phi> ns\<phi>' ` X\<phi>)"
    "ext_tuple_set AD ns\<psi> ns\<psi>' X\<psi> = fo_nmlz AD ` \<Union>(ext_tuple AD ns\<psi> ns\<psi>' ` X\<psi>)"
    by (auto simp: ext_tuple_set_def ext_tuple_def X\<phi>_def X\<psi>_def image_iff fo_nmlz_idem[OF fo_nmlz_sound])
  show ?thesis
    unfolding aux
  proof (rule set_eqI, rule iffI)
    fix vs
    assume "vs \<in> fo_nmlz AD ` \<Union>(ext_tuple AD ns\<phi> ns\<phi>' ` X\<phi>) \<inter>
    fo_nmlz AD ` \<Union>(ext_tuple AD ns\<psi> ns\<psi>' ` X\<psi>)"
    then obtain xs ys where xs_ys_def: "xs \<in> X\<phi>" "vs \<in> fo_nmlz AD ` ext_tuple AD ns\<phi> ns\<phi>' xs"
      "ys \<in> X\<psi>" "vs \<in> fo_nmlz AD ` ext_tuple AD ns\<psi> ns\<psi>' ys"
      by auto
    have len_xs_ys: "length xs = length ns\<phi>" "length ys = length ns\<psi>"
      using xs_ys_def(1,3)
      by (auto simp: X\<phi>_def X\<psi>_def proj_vals_def fo_nmlz_length)
    obtain fs\<phi> where fs\<phi>_def: "vs = fo_nmlz AD (map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)))"
      "fs\<phi> \<in> nall_tuples_rec AD (card (Inr -` set xs)) (length ns\<phi>')"
      using xs_ys_def(1,2)
      by (auto simp: X\<phi>_def proj_vals_def ext_tuple_def split: if_splits)
        (metis fo_nmlz_map length_map map_snd_zip)
    obtain fs\<psi> where fs\<psi>_def: "vs = fo_nmlz AD (map snd (merge (zip ns\<psi> ys) (zip ns\<psi>' fs\<psi>)))"
      "fs\<psi> \<in> nall_tuples_rec AD (card (Inr -` set ys)) (length ns\<psi>')"
      using xs_ys_def(3,4)
      by (auto simp: X\<psi>_def proj_vals_def ext_tuple_def split: if_splits)
        (metis fo_nmlz_map length_map map_snd_zip)
    note len_fs\<phi> = nall_tuples_rec_length[OF fs\<phi>_def(2)]
    note len_fs\<psi> = nall_tuples_rec_length[OF fs\<psi>_def(2)]
    obtain \<sigma>xs where \<sigma>xs_def: "xs = map \<sigma>xs ns\<phi>" "fs\<phi> = map \<sigma>xs ns\<phi>'"
      using exists_map[of "ns\<phi> @ ns\<phi>'" "xs @ fs\<phi>"] len_xs_ys(1) len_fs\<phi> distinct
      by (auto simp: ns\<phi>'_def)
    obtain \<sigma>ys where \<sigma>ys_def: "ys = map \<sigma>ys ns\<psi>" "fs\<psi> = map \<sigma>ys ns\<psi>'"
      using exists_map[of "ns\<psi> @ ns\<psi>'" "ys @ fs\<psi>"] len_xs_ys(2) len_fs\<psi> distinct
      by (auto simp: ns\<psi>'_def)
    have map_merge_fs\<phi>: "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) = map \<sigma>xs (sort (ns\<phi> @ ns\<phi>'))"
      unfolding \<sigma>xs_def
      apply (rule merge_map)
      using distinct sorted_filter[of id]
      by (auto simp: ns\<phi>'_def)
    have map_merge_fs\<psi>: "map snd (merge (zip ns\<psi> ys) (zip ns\<psi>' fs\<psi>)) = map \<sigma>ys (sort (ns\<psi> @ ns\<psi>'))"
      unfolding \<sigma>ys_def
      apply (rule merge_map)
      using distinct sorted_filter[of id]
      by (auto simp: ns\<psi>'_def)
    define cxs where "cxs = filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> isl x) (zip ns\<phi> xs)"
    define nxs where "nxs = map fst (filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> \<not>isl x) (zip ns\<phi> xs))"
    define cys where "cys = filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> isl y) (zip ns\<psi> ys)"
    define nys where "nys = map fst (filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> \<not>isl y) (zip ns\<psi> ys))"
    note ad_agr1 = fo_nmlz_eqD[OF trans[OF fs\<phi>_def(1)[symmetric] fs\<psi>_def(1)],
        unfolded map_merge_fs\<phi> map_merge_fs\<psi>]
    note ad_agr2 = ad_agr_list_comm[OF ad_agr1]
    obtain \<sigma>xs where aux1:
      "map snd (merge (zip ns\<phi> xs) (zip ns\<phi>' fs\<phi>)) =
      map snd (merge (zip (sort (ns\<phi> @ map fst cys)) (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))
      (zip nys (map \<sigma>xs nys)))"
      "map snd (merge (zip ns\<phi> xs) cys) = map \<sigma>xs (sort (ns\<phi> @ map fst cys))"
      "map \<sigma>xs nys \<in> nall_tuples_rec {}
      (card (Inr -` set (map \<sigma>xs (sort (ns\<phi> @ map fst cys))))) (length nys)"
      using eval_conj_set_aux[OF ns\<phi>'_def ns\<psi>'_def X\<phi>_def X\<psi>_def distinct cxs_def nxs_def
          cys_def nys_def xs_ys_def(1,3) \<sigma>xs_def \<sigma>ys_def fs\<phi>_def(2) fs\<psi>_def(2) ad_agr2]
      by blast
    obtain \<sigma>ys where aux2:
      "map snd (merge (zip ns\<psi> ys) (zip ns\<psi>' fs\<psi>)) =
      map snd (merge (zip (sort (ns\<psi> @ map fst cxs)) (map \<sigma>ys (sort (ns\<psi> @ map fst cxs))))
      (zip nxs (map \<sigma>ys nxs)))"
      "map snd (merge (zip ns\<psi> ys) cxs) = map \<sigma>ys (sort (ns\<psi> @ map fst cxs))"
      "map \<sigma>ys nxs \<in> nall_tuples_rec {}
      (card (Inr -` set (map \<sigma>ys (sort (ns\<psi> @ map fst cxs))))) (length nxs)"
      using eval_conj_set_aux[OF ns\<psi>'_def ns\<phi>'_def X\<psi>_def X\<phi>_def distinct(2,1) cys_def nys_def
          cxs_def nxs_def xs_ys_def(3,1) \<sigma>ys_def \<sigma>xs_def fs\<psi>_def(2) fs\<phi>_def(2) ad_agr1]
      by blast
    have vs_ext_nys: "vs \<in> fo_nmlz AD ` ext_tuple {} (sort (ns\<phi> @ map fst cys)) nys
    (map snd (merge (zip ns\<phi> xs) cys))"
      using aux1(3)
      unfolding fs\<phi>_def(1) aux1(1)
      by (simp add: ext_tuple_eq[OF length_map[symmetric]] aux1(2))
    have vs_ext_nxs: "vs \<in> fo_nmlz AD ` ext_tuple {} (sort (ns\<psi> @ map fst cxs)) nxs
    (map snd (merge (zip ns\<psi> ys) cxs))"
      using aux2(3)
      unfolding fs\<psi>_def(1) aux2(1)
      by (simp add: ext_tuple_eq[OF length_map[symmetric]] aux2(2))
    show "vs \<in> eval_conj_set AD ns\<phi> X\<phi> ns\<psi> X\<psi>"
      using vs_ext_nys vs_ext_nxs xs_ys_def(1,3)
      by (auto simp: eval_conj_set_def eval_conj_tuple_def nys_def cys_def nxs_def cxs_def Let_def)
  next
    fix vs
    assume "vs \<in> eval_conj_set AD ns\<phi> X\<phi> ns\<psi> X\<psi>"
    then obtain xs ys cxs nxs cys nys where
      cxs_def: "cxs = filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> isl x) (zip ns\<phi> xs)" and
      nxs_def: "nxs = map fst (filter (\<lambda>(n, x). n \<notin> set ns\<psi> \<and> \<not>isl x) (zip ns\<phi> xs))" and
      cys_def: "cys = filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> isl y) (zip ns\<psi> ys)" and
      nys_def: "nys = map fst (filter (\<lambda>(n, y). n \<notin> set ns\<phi> \<and> \<not>isl y) (zip ns\<psi> ys))" and
      xs_def: "xs \<in> X\<phi>" "vs \<in> fo_nmlz AD ` ext_tuple {} (sort (ns\<phi> @ map fst cys)) nys
      (map snd (merge (zip ns\<phi> xs) cys))" and
      ys_def: "ys \<in> X\<psi>" "vs \<in> fo_nmlz AD ` ext_tuple {} (sort (ns\<psi> @ map fst cxs)) nxs
      (map snd (merge (zip ns\<psi> ys) cxs))"
      by (auto simp: eval_conj_set_def eval_conj_tuple_def Let_def) (metis (no_types, lifting) image_eqI)
    have len_xs_ys: "length xs = length ns\<phi>" "length ys = length ns\<psi>"
      using xs_def(1) ys_def(1)
      by (auto simp: X\<phi>_def X\<psi>_def proj_vals_def fo_nmlz_length)
    have len_merge_cys: "length (map snd (merge (zip ns\<phi> xs) cys)) =
    length (sort (ns\<phi> @ map fst cys))"
      using merge_length[of "zip ns\<phi> xs" cys] len_xs_ys
      by auto
    obtain ys\<psi> where ys\<psi>_def: "vs = fo_nmlz AD (map snd (merge (zip (sort (ns\<phi> @ map fst cys))
    (map snd (merge (zip ns\<phi> xs) cys))) (zip nys ys\<psi>)))"
      "ys\<psi> \<in> nall_tuples_rec {} (card (Inr -` set (map snd (merge (zip ns\<phi> xs) cys))))
      (length nys)"
      using xs_def(2)
      unfolding ext_tuple_eq[OF len_merge_cys[symmetric]]
      by auto
    have distinct_nys: "distinct (ns\<phi> @ map fst cys @ nys)"
      using distinct len_xs_ys
      by (auto simp: cys_def nys_def sorted_filter distinct_map_filter)
        (metis eq_key_imp_eq_value map_fst_zip)
    obtain \<sigma>xs where \<sigma>xs_def: "xs = map \<sigma>xs ns\<phi>" "map snd cys = map \<sigma>xs (map fst cys)"
      "ys\<psi> = map \<sigma>xs nys"
      using exists_map[OF _ distinct_nys, of "xs @ map snd cys @ ys\<psi>"] len_xs_ys(1)
        nall_tuples_rec_length[OF ys\<psi>_def(2)]
      by (auto simp: ns\<phi>'_def)
    have len_merge_cxs: "length (map snd (merge (zip ns\<psi> ys) cxs)) =
    length (sort (ns\<psi> @ map fst cxs))"
      using merge_length[of "zip ns\<psi> ys"] len_xs_ys
      by auto
    obtain xs\<phi> where xs\<phi>_def: "vs = fo_nmlz AD (map snd (merge (zip (sort (ns\<psi> @ map fst cxs))
    (map snd (merge (zip ns\<psi> ys) cxs))) (zip nxs xs\<phi>)))"
      "xs\<phi> \<in> nall_tuples_rec {} (card (Inr -` set (map snd (merge (zip ns\<psi> ys) cxs))))
      (length nxs)"
      using ys_def(2)
      unfolding ext_tuple_eq[OF len_merge_cxs[symmetric]]
      by auto
    have distinct_nxs: "distinct (ns\<psi> @ map fst cxs @ nxs)"
      using distinct len_xs_ys(1)
      by (auto simp: cxs_def nxs_def sorted_filter distinct_map_filter)
        (metis eq_key_imp_eq_value map_fst_zip)
    obtain \<sigma>ys where \<sigma>ys_def: "ys = map \<sigma>ys ns\<psi>" "map snd cxs = map \<sigma>ys (map fst cxs)"
      "xs\<phi> = map \<sigma>ys nxs"
      using exists_map[OF _ distinct_nxs, of "ys @ map snd cxs @ xs\<phi>"] len_xs_ys(2)
        nall_tuples_rec_length[OF xs\<phi>_def(2)]
      by (auto simp: ns\<psi>'_def)
    have sd_cs_ns: "sorted_distinct (map fst cxs)" "sorted_distinct nxs"
      "sorted_distinct (map fst cys)" "sorted_distinct nys"
      "sorted_distinct (sort (ns\<psi> @ map fst cxs))"
      "sorted_distinct (sort (ns\<phi> @ map fst cys))"
      using distinct len_xs_ys
      by (auto simp: cxs_def nxs_def cys_def nys_def sorted_filter distinct_map_filter)
    have set_cs_ns_disj: "set (map fst cxs) \<inter> set nxs = {}" "set (map fst cys) \<inter> set nys = {}"
      "set (sort (ns\<phi> @ map fst cys)) \<inter> set nys = {}"
      "set (sort (ns\<psi> @ map fst cxs)) \<inter> set nxs = {}"
      using distinct nth_eq_iff_index_eq
      by (auto simp: cxs_def nxs_def cys_def nys_def set_zip) blast+
    have merge_sort_cxs: "map snd (merge (zip ns\<psi> ys) cxs) = map \<sigma>ys (sort (ns\<psi> @ map fst cxs))"
      unfolding \<sigma>ys_def(1)
      apply (subst zip_map_fst_snd[of cxs, symmetric])
      unfolding \<sigma>ys_def(2)
      apply (rule merge_map)
      using distinct(2) sd_cs_ns
      by (auto simp: cxs_def)
    have merge_sort_cys: "map snd (merge (zip ns\<phi> xs) cys) = map \<sigma>xs (sort (ns\<phi> @ map fst cys))"
      unfolding \<sigma>xs_def(1)
      apply (subst zip_map_fst_snd[of cys, symmetric])
      unfolding \<sigma>xs_def(2)
      apply (rule merge_map)
      using distinct(1) sd_cs_ns
      by (auto simp: cys_def)
    have set_ns\<phi>': "set ns\<phi>' = set (map fst cys) \<union> set nys"
      using len_xs_ys(2)
      by (auto simp: ns\<phi>'_def cys_def nys_def dest: set_zip_leftD)
        (metis (no_types, lifting) image_eqI in_set_impl_in_set_zip1 mem_Collect_eq
          prod.sel(1) split_conv)
    have sort_sort_nys: "sort (sort (ns\<phi> @ map fst cys) @ nys) = sort (ns\<phi> @ ns\<phi>')"
      apply (rule sorted_distinct_set_unique)
      using distinct sd_cs_ns set_cs_ns_disj set_ns\<phi>'
      by (auto simp: cys_def nys_def ns\<phi>'_def dest: set_zip_leftD)
    have set_ns\<psi>': "set ns\<psi>' = set (map fst cxs) \<union> set nxs"
      using len_xs_ys(1)
      by (auto simp: ns\<psi>'_def cxs_def nxs_def dest: set_zip_leftD)
        (metis (no_types, lifting) image_eqI in_set_impl_in_set_zip1 mem_Collect_eq
          prod.sel(1) split_conv)
    have sort_sort_nxs: "sort (sort (ns\<psi> @ map fst cxs) @ nxs) = sort (ns\<psi> @ ns\<psi>')"
      apply (rule sorted_distinct_set_unique)
      using distinct sd_cs_ns set_cs_ns_disj set_ns\<psi>'
      by (auto simp: cxs_def nxs_def ns\<psi>'_def dest: set_zip_leftD)
    have ad_agr1: "ad_agr_list AD (map \<sigma>ys (sort (ns\<psi> @ ns\<psi>'))) (map \<sigma>xs (sort (ns\<phi> @ ns\<phi>')))"
      using fo_nmlz_eqD[OF trans[OF xs\<phi>_def(1)[symmetric] ys\<psi>_def(1)]]
      unfolding \<sigma>xs_def(3) \<sigma>ys_def(3) merge_sort_cxs merge_sort_cys
      unfolding merge_map[OF sd_cs_ns(5) sd_cs_ns(2) set_cs_ns_disj(4)]
      unfolding merge_map[OF sd_cs_ns(6) sd_cs_ns(4) set_cs_ns_disj(3)]
      unfolding sort_sort_nxs sort_sort_nys .
    note ad_agr2 = ad_agr_list_comm[OF ad_agr1]
    have Inl_set_AD: "Inl -` (set (map snd cxs) \<union> set xs\<phi>) \<subseteq> AD"
      "Inl -` (set (map snd cys) \<union> set ys\<psi>) \<subseteq> AD"
      using xs_def(1) nall_tuples_rec_Inl[OF xs\<phi>_def(2)] ys_def(1)
        nall_tuples_rec_Inl[OF ys\<psi>_def(2)] fo_nmlz_set[of AD]
      by (fastforce simp: cxs_def X\<phi>_def cys_def X\<psi>_def dest!: set_zip_rightD)+
    note aux1 = eval_conj_set_aux'[OF ns\<phi>'_def ns\<psi>'_def X\<phi>_def X\<psi>_def distinct cxs_def nxs_def
        cys_def nys_def xs_def(1) ys_def(1) \<sigma>xs_def \<sigma>ys_def refl refl
        ys\<psi>_def(2)[unfolded \<sigma>xs_def(3) merge_sort_cys] Inl_set_AD ad_agr1]
    note aux2 = eval_conj_set_aux'[OF ns\<psi>'_def ns\<phi>'_def X\<psi>_def X\<phi>_def distinct(2,1) cys_def nys_def
        cxs_def nxs_def ys_def(1) xs_def(1) \<sigma>ys_def \<sigma>xs_def refl refl
        xs\<phi>_def(2)[unfolded \<sigma>ys_def(3) merge_sort_cxs] Inl_set_AD(2,1) ad_agr2]
    show "vs \<in> fo_nmlz AD ` \<Union>(ext_tuple AD ns\<phi> ns\<phi>' ` X\<phi>) \<inter>
    fo_nmlz AD ` \<Union>(ext_tuple AD ns\<psi> ns\<psi>' ` X\<psi>)"
      using xs_def(1) ys_def(1) ys\<psi>_def(1) xs\<phi>_def(1) aux1(3) aux2(3)
        ext_tuple_eq[OF len_xs_ys(1)[symmetric], of AD ns\<phi>']
        ext_tuple_eq[OF len_xs_ys(2)[symmetric], of AD ns\<psi>']
      unfolding aux1(2) aux2(2) \<sigma>ys_def(3) \<sigma>xs_def(3) aux1(1)[symmetric] aux2(1)[symmetric]
      by blast
  qed
qed

lemma esat_exists_not_fv: "n \<notin> fv_fo_fmla \<phi> \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
  esat (Exists n \<phi>) I \<sigma> X \<longleftrightarrow> esat \<phi> I \<sigma> X"
proof (rule iffI)
  assume assms: "n \<notin> fv_fo_fmla \<phi>" "esat (Exists n \<phi>) I \<sigma> X"
  then obtain x where "esat \<phi> I (\<sigma>(n := x)) X"
    by auto
  with assms(1) show "esat \<phi> I \<sigma> X"
    using esat_fv_cong[of \<phi> \<sigma> "\<sigma>(n := x)"] by fastforce
next
  assume assms: "n \<notin> fv_fo_fmla \<phi>" "X \<noteq> {}" "esat \<phi> I \<sigma> X"
  from assms(2) obtain x where x_def: "x \<in> X"
    by auto
  with assms(1,3) have "esat \<phi> I (\<sigma>(n := x)) X"
    using esat_fv_cong[of \<phi> \<sigma> "\<sigma>(n := x)"] by fastforce
  with x_def show "esat (Exists n \<phi>) I \<sigma> X"
    by auto
qed

lemma esat_forall_not_fv: "n \<notin> fv_fo_fmla \<phi> \<Longrightarrow> X \<noteq> {} \<Longrightarrow>
  esat (Forall n \<phi>) I \<sigma> X \<longleftrightarrow> esat \<phi> I \<sigma> X"
  using esat_exists_not_fv[of n "Neg \<phi>" X I \<sigma>]
  by auto

lemma proj_sat_vals: "proj_sat \<phi> I =
  proj_vals {\<sigma>. sat \<phi> I \<sigma>} (fv_fo_fmla_list \<phi>)"
  by (auto simp: proj_sat_def proj_vals_def)

lemma fv_fo_fmla_list_Pred: "remdups_adj (sort (fv_fo_terms_list ts)) = fv_fo_terms_list ts"
  unfolding fv_fo_terms_list_def
  by (simp add: distinct_remdups_adj_sort remdups_adj_distinct sorted_sort_id)

lemma ad_agr_list_fv_list': "\<Union>(set (map set_fo_term ts)) \<subseteq> X \<Longrightarrow>
  ad_agr_list X (map \<sigma> (fv_fo_terms_list ts)) (map \<tau> (fv_fo_terms_list ts)) \<Longrightarrow>
  ad_agr_list X (\<sigma> \<odot>e ts) (\<tau> \<odot>e ts)"
proof (induction ts)
  case (Cons t ts)
  have IH: "ad_agr_list X (\<sigma> \<odot>e ts) (\<tau> \<odot>e ts)"
    using Cons
    by (auto simp: ad_agr_list_def ad_equiv_list_link[symmetric] fv_fo_terms_set_list
        fv_fo_terms_set_def sp_equiv_list_link sp_equiv_def pairwise_def) blast+
  have ad_equiv: "\<And>i. i \<in> fv_fo_term_set t \<union> \<Union>(fv_fo_term_set ` set ts) \<Longrightarrow>
    ad_equiv_pair X (\<sigma> i, \<tau> i)"
    using Cons(3)
    by (auto simp: ad_agr_list_def ad_equiv_list_link[symmetric] fv_fo_terms_set_list
        fv_fo_terms_set_def)
  have sp_equiv: "\<And>i j. i \<in> fv_fo_term_set t \<union> \<Union>(fv_fo_term_set ` set ts) \<Longrightarrow>
    j \<in> fv_fo_term_set t \<union> \<Union>(fv_fo_term_set ` set ts) \<Longrightarrow> sp_equiv_pair (\<sigma> i, \<tau> i) (\<sigma> j, \<tau> j)"
    using Cons(3)
    by (auto simp: ad_agr_list_def sp_equiv_list_link fv_fo_terms_set_list
        fv_fo_terms_set_def sp_equiv_def pairwise_def)
  show ?case
  proof (cases t)
    case (Const c)
    show ?thesis
      using IH Cons(2)
      apply (auto simp: ad_agr_list_def eval_eterms_def ad_equiv_list_def Const
          sp_equiv_list_def pairwise_def set_zip)
      unfolding ad_equiv_pair.simps
          apply (metis nth_map rev_image_eqI)+
      done
  next
    case (Var n)
    note t_def = Var
    have ad: "ad_equiv_pair X (\<sigma> n, \<tau> n)"
      using ad_equiv
      by (auto simp: Var)
    have "\<And>y. y \<in> set (zip (map ((\<cdot>e) \<sigma>) ts) (map ((\<cdot>e) \<tau>) ts)) \<Longrightarrow> y \<noteq> (\<sigma> n, \<tau> n) \<Longrightarrow>
      sp_equiv_pair (\<sigma> n, \<tau> n) y \<and> sp_equiv_pair y (\<sigma> n, \<tau> n)"
    proof -
      fix y
      assume "y \<in> set (zip (map ((\<cdot>e) \<sigma>) ts) (map ((\<cdot>e) \<tau>) ts))"
      then obtain t' where y_def: "t' \<in> set ts" "y = (\<sigma> \<cdot>e t', \<tau> \<cdot>e t')"
        using nth_mem
        by (auto simp: set_zip) blast
      show "sp_equiv_pair (\<sigma> n, \<tau> n) y \<and> sp_equiv_pair y (\<sigma> n, \<tau> n)"
      proof (cases t')
        case (Const c')
        have c'_X: "c' \<in> X"
          using Cons(2) y_def(1)
          by (auto simp: Const) (meson SUP_le_iff fo_term.set_intros subsetD)
        then show ?thesis
          using ad_equiv[of n] y_def(1)
          unfolding y_def
          apply (auto simp: Const t_def)
          unfolding ad_equiv_pair.simps
             apply fastforce+
           apply force
          apply (metis rev_image_eqI)
          done
      next
        case (Var n')
        show ?thesis
          using sp_equiv[of n n'] y_def(1)
          unfolding y_def
          by (fastforce simp: t_def Var)
      qed
    qed
    then show ?thesis
      using IH Cons(3)
      by (auto simp: ad_agr_list_def eval_eterms_def ad_equiv_list_def Var ad sp_equiv_list_def
          pairwise_insert)
  qed
qed (auto simp: eval_eterms_def ad_agr_list_def ad_equiv_list_def sp_equiv_list_def)

lemma ext_tuple_ad_agr_close:
  assumes S\<phi>_def: "S\<phi> \<equiv> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
    and AD_sub: "act_edom \<phi> I \<subseteq> AD\<phi>" "AD\<phi> \<subseteq> AD"
    and X\<phi>_def: "X\<phi> = fo_nmlz AD\<phi> ` proj_vals S\<phi> (fv_fo_fmla_list \<phi>)"
    and ns\<phi>'_def: "ns\<phi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<phi>) ns\<psi>"
    and sd_ns\<psi>: "sorted_distinct ns\<psi>"
    and fv_Un: "fv_fo_fmla \<psi> = fv_fo_fmla \<phi> \<union> set ns\<psi>"
  shows "ext_tuple_set AD (fv_fo_fmla_list \<phi>) ns\<phi>' (ad_agr_close_set (AD - AD\<phi>) X\<phi>) =
    fo_nmlz AD ` proj_vals S\<phi> (fv_fo_fmla_list \<psi>)"
    "ad_agr_close_set (AD - AD\<phi>) X\<phi> = fo_nmlz AD ` proj_vals S\<phi> (fv_fo_fmla_list \<phi>)"
proof -
  have ad_agr_\<phi>:
    "\<And>\<sigma> \<tau>. ad_agr_sets (set (fv_fo_fmla_list \<phi>)) (set (fv_fo_fmla_list \<phi>)) AD\<phi> \<sigma> \<tau> \<Longrightarrow>
      \<sigma> \<in> S\<phi> \<longleftrightarrow> \<tau> \<in> S\<phi>"
    using esat_UNIV_cong[OF ad_agr_sets_restrict, OF _ subset_refl] ad_agr_sets_mono AD_sub
    unfolding S\<phi>_def
    by blast
  show ad_close_alt: "ad_agr_close_set (AD - AD\<phi>) X\<phi> = fo_nmlz AD ` proj_vals S\<phi> (fv_fo_fmla_list \<phi>)"
    using ad_agr_close_correct[OF AD_sub(2) ad_agr_\<phi>] AD_sub(2)
    unfolding X\<phi>_def S\<phi>_def[symmetric] proj_fmla_def
    by (auto simp: ad_agr_close_set_def Set.is_empty_def)
  have fv_\<phi>: "set (fv_fo_fmla_list \<phi>) \<subseteq> set (fv_fo_fmla_list \<psi>)"
    using fv_Un
    by (auto simp: fv_fo_fmla_list_set)
  have sd_ns\<phi>': "sorted_distinct ns\<phi>'"
    using sd_ns\<psi> sorted_filter[of id]
    by (auto simp: ns\<phi>'_def)
  show "ext_tuple_set AD (fv_fo_fmla_list \<phi>) ns\<phi>' (ad_agr_close_set (AD - AD\<phi>) X\<phi>) =
    fo_nmlz AD ` proj_vals S\<phi> (fv_fo_fmla_list \<psi>)"
    apply (rule ext_tuple_correct)
    using sorted_distinct_fv_list ad_close_alt ad_agr_\<phi> ad_agr_sets_mono[OF AD_sub(2)]
      fv_Un sd_ns\<phi>'
    by (fastforce simp: ns\<phi>'_def fv_fo_fmla_list_set)+
qed

lemma proj_ext_tuple:
  assumes S\<phi>_def: "S\<phi> \<equiv> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
    and AD_sub: "act_edom \<phi> I \<subseteq> AD"
    and X\<phi>_def: "X\<phi> = fo_nmlz AD ` proj_vals S\<phi> (fv_fo_fmla_list \<phi>)"
    and ns\<phi>'_def: "ns\<phi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<phi>) ns\<psi>"
    and sd_ns\<psi>: "sorted_distinct ns\<psi>"
    and fv_Un: "fv_fo_fmla \<psi> = fv_fo_fmla \<phi> \<union> set ns\<psi>"
    and Z_props: "\<And>xs. xs \<in> Z \<Longrightarrow> fo_nmlz AD xs = xs \<and> length xs = length (fv_fo_fmla_list \<psi>)"
  shows "Z \<inter> ext_tuple_set AD (fv_fo_fmla_list \<phi>) ns\<phi>' X\<phi> =
    {xs \<in> Z. fo_nmlz AD (proj_tuple (fv_fo_fmla_list \<phi>) (zip (fv_fo_fmla_list \<psi>) xs)) \<in> X\<phi>}"
    "Z - ext_tuple_set AD (fv_fo_fmla_list \<phi>) ns\<phi>' X\<phi> =
    {xs \<in> Z. fo_nmlz AD (proj_tuple (fv_fo_fmla_list \<phi>) (zip (fv_fo_fmla_list \<psi>) xs)) \<notin> X\<phi>}"
proof -
  have ad_agr_\<phi>:
    "\<And>\<sigma> \<tau>. ad_agr_sets (set (fv_fo_fmla_list \<phi>)) (set (fv_fo_fmla_list \<phi>)) AD \<sigma> \<tau> \<Longrightarrow>
      \<sigma> \<in> S\<phi> \<longleftrightarrow> \<tau> \<in> S\<phi>"
    using esat_UNIV_cong[OF ad_agr_sets_restrict, OF _ subset_refl] ad_agr_sets_mono AD_sub
    unfolding S\<phi>_def
    by blast
  have sd_ns\<phi>': "sorted_distinct ns\<phi>'"
    using sd_ns\<psi> sorted_filter[of id]
    by (auto simp: ns\<phi>'_def)
  have disj: "set (fv_fo_fmla_list \<phi>) \<inter> set ns\<phi>' = {}"
    by (auto simp: ns\<phi>'_def fv_fo_fmla_list_set)
  have Un: "set (fv_fo_fmla_list \<phi>) \<union> set ns\<phi>' = set (fv_fo_fmla_list \<psi>)"
    using fv_Un
    by (auto simp: ns\<phi>'_def fv_fo_fmla_list_set)
  note proj = proj_tuple_correct[OF sorted_distinct_fv_list sd_ns\<phi>' sorted_distinct_fv_list
      disj Un X\<phi>_def ad_agr_\<phi>, simplified]
  have "fo_nmlz AD ` X\<phi> = X\<phi>"
    using fo_nmlz_idem[OF fo_nmlz_sound]
    by (auto simp: X\<phi>_def image_iff)
  then have aux: "ext_tuple_set AD (fv_fo_fmla_list \<phi>) ns\<phi>' X\<phi> = fo_nmlz AD ` \<Union>(ext_tuple AD (fv_fo_fmla_list \<phi>) ns\<phi>' ` X\<phi>)"
    by (auto simp: ext_tuple_set_def ext_tuple_def)
  show "Z \<inter> ext_tuple_set AD (fv_fo_fmla_list \<phi>) ns\<phi>' X\<phi> =
    {xs \<in> Z. fo_nmlz AD (proj_tuple (fv_fo_fmla_list \<phi>) (zip (fv_fo_fmla_list \<psi>) xs)) \<in> X\<phi>}"
    using Z_props proj
    by (auto simp: aux)
  show "Z - ext_tuple_set AD (fv_fo_fmla_list \<phi>) ns\<phi>' X\<phi> =
    {xs \<in> Z. fo_nmlz AD (proj_tuple (fv_fo_fmla_list \<phi>) (zip (fv_fo_fmla_list \<psi>) xs)) \<notin> X\<phi>}"
    using Z_props proj
    by (auto simp: aux)
qed

lemma fo_nmlz_proj_sub: "fo_nmlz AD ` proj_fmla \<phi> R \<subseteq> nall_tuples AD (nfv \<phi>)"
  by (auto simp: proj_fmla_map fo_nmlz_length fo_nmlz_sound nfv_def
      intro: nall_tuplesI)

lemma fin_ad_agr_list_iff:
  fixes AD :: "('a :: infinite) set"
  assumes "finite AD" "\<And>vs. vs \<in> Z \<Longrightarrow> length vs = n"
    "Z = {ts. \<exists>ts' \<in> X. ad_agr_list AD (map Inl ts) ts'}"
  shows "finite Z \<longleftrightarrow> \<Union>(set ` Z) \<subseteq> AD"
proof (rule iffI, rule ccontr)
  assume fin: "finite Z"
  assume "\<not>\<Union>(set ` Z) \<subseteq> AD"
  then obtain \<sigma> i vs where \<sigma>_def: "map \<sigma> [0..<n] \<in> Z" "i < n" "\<sigma> i \<notin> AD" "vs \<in> X"
    "ad_agr_list AD (map (Inl \<circ> \<sigma>) [0..<n]) vs"
    using assms(2)
    by (auto simp: assms(3) in_set_conv_nth) (metis map_map map_nth)
  define Y where "Y \<equiv> AD \<union> \<sigma> ` {0..<n}"
  have inf_UNIV_Y: "infinite (UNIV - Y)"
    using assms(1)
    by (auto simp: Y_def infinite_UNIV)
  have "\<And>y. y \<notin> Y \<Longrightarrow> map ((\<lambda>z. if z = \<sigma> i then y else z) \<circ> \<sigma>) [0..<n] \<in> Z"
    using \<sigma>_def(3)
    by (auto simp: assms(3) intro!: bexI[OF _ \<sigma>_def(4)] ad_agr_list_trans[OF _ \<sigma>_def(5)])
       (auto simp: ad_agr_list_def ad_equiv_list_def set_zip Y_def ad_equiv_pair.simps
        sp_equiv_list_def pairwise_def split: if_splits)
  then have "(\<lambda>x'. map ((\<lambda>z. if z = \<sigma> i then x' else z) \<circ> \<sigma>) [0..<n]) `
    (UNIV - Y) \<subseteq> Z"
    by auto
  moreover have "inj (\<lambda>x'. map ((\<lambda>z. if z = \<sigma> i then x' else z) \<circ> \<sigma>) [0..<n])"
    using \<sigma>_def(2)
    by (auto simp: inj_def)
  ultimately show "False"
    using inf_UNIV_Y fin
    by (meson inj_on_diff inj_on_finite)
next
  assume "\<Union>(set ` Z) \<subseteq> AD"
  then have "Z \<subseteq> all_tuples AD n"
    using assms(2)
    by (auto intro: all_tuplesI)
  then show "finite Z"
    using all_tuples_finite[OF assms(1)] finite_subset
    by auto
qed

lemma proj_out_list:
  fixes AD :: "('a :: infinite) set"
    and \<sigma> :: "nat \<Rightarrow> 'a + nat"
    and ns :: "nat list"
  assumes "finite AD"
  shows "\<exists>\<tau>. ad_agr_list AD (map \<sigma> ns) (map (Inl \<circ> \<tau>) ns) \<and>
    (\<forall>j x. j \<in> set ns \<longrightarrow> \<sigma> j = Inl x \<longrightarrow> \<tau> j = x)"
proof -
  have fin: "finite (AD \<union> Inl -` set (map \<sigma> ns))"
    using assms(1) finite_Inl[OF finite_set]
    by blast
  obtain f where f_def: "inj (f :: nat \<Rightarrow> 'a)"
    "range f \<subseteq> UNIV - (AD \<union> Inl -` set (map \<sigma> ns))"
    using arb_countable_map[OF fin]
    by auto
  define \<tau> where "\<tau> = case_sum id f \<circ> \<sigma>"
  have f_out: "\<And>i x. i < length ns \<Longrightarrow> \<sigma> (ns ! i) = Inl (f x) \<Longrightarrow> False"
    using f_def(2)
    by (auto simp: vimage_def)
       (metis (no_types, lifting) DiffE UNIV_I UnCI imageI image_subset_iff mem_Collect_eq nth_mem)
  have "(a, b) \<in> set (zip (map \<sigma> ns) (map (Inl \<circ> \<tau>) ns)) \<Longrightarrow> ad_equiv_pair AD (a, b)" for a b
    using f_def(2)
    by (auto simp: set_zip \<tau>_def ad_equiv_pair.simps split: sum.splits)+
  moreover have "sp_equiv_list (map \<sigma> ns) (map (Inl \<circ> \<tau>) ns)"
    using f_def(1) f_out
    by (auto simp: sp_equiv_list_def pairwise_def set_zip \<tau>_def inj_def split: sum.splits)+
  ultimately have "ad_agr_list AD (map \<sigma> ns) (map (Inl \<circ> \<tau>) ns)"
    by (auto simp: ad_agr_list_def ad_equiv_list_def)
  then show ?thesis
    by (auto simp: \<tau>_def intro!: exI[of _ \<tau>])
qed

lemma proj_out:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
    and J :: "(('a, nat) fo_t, 'b) fo_intp"
  assumes "wf_fo_intp \<phi> I" "esat \<phi> I \<sigma> UNIV"
  shows "\<exists>\<tau>. esat \<phi> I (Inl \<circ> \<tau>) UNIV \<and> (\<forall>i x. i \<in> fv_fo_fmla \<phi> \<and> \<sigma> i = Inl x \<longrightarrow> \<tau> i = x) \<and>
    ad_agr_list (act_edom \<phi> I) (map \<sigma> (fv_fo_fmla_list \<phi>)) (map (Inl \<circ> \<tau>) (fv_fo_fmla_list \<phi>))"
  using proj_out_list[OF finite_act_edom[OF assms(1)], of \<sigma> "fv_fo_fmla_list \<phi>"]
    esat_UNIV_ad_agr_list[OF _ subset_refl] assms(2)
  unfolding fv_fo_fmla_list_set
  by fastforce

lemma proj_fmla_esat_sat:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
    and J :: "(('a, nat) fo_t, 'b) fo_intp"
  assumes wf: "wf_fo_intp \<phi> I"
  shows "proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV} \<inter> map Inl ` UNIV =
    map Inl ` proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
  unfolding sat_esat_conv[OF wf]
proof (rule set_eqI, rule iffI)
  fix vs
  assume "vs \<in> proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV} \<inter> map Inl ` UNIV"
  then obtain \<sigma> where \<sigma>_def: "vs = map \<sigma> (fv_fo_fmla_list \<phi>)" "esat \<phi> I \<sigma> UNIV"
    "set vs \<subseteq> range Inl"
    by (auto simp: proj_fmla_map) (metis image_subset_iff list.set_map range_eqI)
  obtain \<tau> where \<tau>_def: "esat \<phi> I (Inl \<circ> \<tau>) UNIV"
    "\<And>i x. i \<in> fv_fo_fmla \<phi> \<Longrightarrow> \<sigma> i = Inl x \<Longrightarrow> \<tau> i = x"
    using proj_out[OF assms \<sigma>_def(2)]
    by fastforce
  have "vs = map (Inl \<circ> \<tau>) (fv_fo_fmla_list \<phi>)"
    using \<sigma>_def(1,3) \<tau>_def(2)
    by (auto simp: fv_fo_fmla_list_set)
  then show "vs \<in> map Inl ` proj_fmla \<phi> {\<sigma>. esat \<phi> I (Inl \<circ> \<sigma>) UNIV}"
    using \<tau>_def(1)
    by (force simp: proj_fmla_map)
qed (auto simp: proj_fmla_map)

lemma norm_proj_fmla_esat_sat:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes "wf_fo_intp \<phi> I"
  shows "fo_nmlz (act_edom \<phi> I) ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV} =
    fo_nmlz (act_edom \<phi> I) ` map Inl ` proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
proof -
  have "fo_nmlz (act_edom \<phi> I) (map \<sigma> (fv_fo_fmla_list \<phi>)) = fo_nmlz (act_edom \<phi> I) x"
    "x \<in> (\<lambda>\<tau>. map \<tau> (fv_fo_fmla_list \<phi>)) ` {\<sigma>. esat \<phi> I \<sigma> UNIV} \<inter> range (map Inl)"
    if "esat \<phi> I \<sigma> UNIV" "esat \<phi> I (Inl \<circ> \<tau>) UNIV" "x = map (Inl \<circ> \<tau>) (fv_fo_fmla_list \<phi>)"
      "ad_agr_list (act_edom \<phi> I) (map \<sigma> (fv_fo_fmla_list \<phi>)) (map (Inl \<circ> \<tau>) (fv_fo_fmla_list \<phi>))"
    for \<sigma> \<tau> x
    using that
    by (auto intro!: fo_nmlz_eqI) (metis map_map range_eqI)
  then show ?thesis
    unfolding proj_fmla_esat_sat[OF assms, symmetric]
    using proj_out[OF assms]
    by (fastforce simp: image_iff proj_fmla_map)
qed

lemma proj_sat_fmla: "proj_sat \<phi> I = proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
  by (auto simp: proj_sat_def proj_fmla_map)

fun fo_wf :: "('a, 'b) fo_fmla \<Rightarrow> ('b \<times> nat \<Rightarrow> 'a list set) \<Rightarrow> ('a, nat) fo_t \<Rightarrow> bool" where
  "fo_wf \<phi> I (AD, n, X) \<longleftrightarrow> finite AD \<and> finite X \<and> n = nfv \<phi> \<and>
    wf_fo_intp \<phi> I \<and> AD = act_edom \<phi> I \<and> fo_rep (AD, n, X) = proj_sat \<phi> I \<and>
    Inl -` \<Union>(set ` X) \<subseteq> AD \<and> (\<forall>vs \<in> X. fo_nmlzd AD vs \<and> length vs = n)"

fun fo_fin :: "('a, nat) fo_t \<Rightarrow> bool" where
  "fo_fin (AD, n, X) \<longleftrightarrow> (\<forall>x \<in> \<Union>(set ` X). isl x)"

lemma fo_rep_fin:
  assumes "fo_wf \<phi> I (AD, n, X)" "fo_fin (AD, n, X)"
  shows "fo_rep (AD, n, X) = map projl ` X"
proof (rule set_eqI, rule iffI)
  fix vs
  assume "vs \<in> fo_rep (AD, n, X)"
  then obtain xs where xs_def: "xs \<in> X" "ad_agr_list AD (map Inl vs) xs"
    by auto
  obtain zs where zs_def: "xs = map Inl zs"
    using xs_def(1) assms
    by auto (meson ex_map_conv isl_def)
  have "set zs \<subseteq> AD"
    using assms(1) xs_def(1) zs_def
    by (force simp: vimage_def)
  then have vs_zs: "vs = zs"
    using xs_def(2)
    unfolding zs_def
    by (fastforce simp: ad_agr_list_def ad_equiv_list_def set_zip ad_equiv_pair.simps
        intro!: nth_equalityI)
  show "vs \<in> map projl ` X"
    using xs_def(1) zs_def
    by (auto simp: image_iff comp_def vs_zs intro!: bexI[of _ "map Inl zs"])
next
  fix vs
  assume "vs \<in> map projl ` X"
  then obtain xs where xs_def: "xs \<in> X" "vs = map projl xs"
    by auto
  have xs_map_Inl: "xs = map Inl vs"
    using assms xs_def
    by (auto simp: map_idI)
  show "vs \<in> fo_rep (AD, n, X)"
    using xs_def(1)
    by (auto simp: xs_map_Inl intro!: bexI[of _ xs] ad_agr_list_refl)
qed

definition eval_abs :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> ('a, nat) fo_t" where
  "eval_abs \<phi> I = (act_edom \<phi> I, nfv \<phi>, fo_nmlz (act_edom \<phi> I) ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV})"

lemma map_projl_Inl: "map projl (map Inl xs) = xs"
  by (metis (mono_tags, lifting) length_map nth_equalityI nth_map sum.sel(1))

lemma fo_rep_eval_abs:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes "wf_fo_intp \<phi> I"
  shows "fo_rep (eval_abs \<phi> I) = proj_sat \<phi> I"
proof -
  obtain AD n X where AD_X_def: "eval_abs \<phi> I = (AD, n, X)" "AD = act_edom \<phi> I"
    "n = nfv \<phi>" "X = fo_nmlz (act_edom \<phi> I) ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
    by (cases "eval_abs \<phi> I") (auto simp: eval_abs_def)
  have AD_sub: "act_edom \<phi> I \<subseteq> AD"
    by (auto simp: AD_X_def)
  have X_def: "X = fo_nmlz AD ` map Inl ` proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
    using AD_X_def norm_proj_fmla_esat_sat[OF assms]
    by auto
  have "{ts. \<exists>ts' \<in> X. ad_agr_list AD (map Inl ts) ts'} = proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
  proof (rule set_eqI, rule iffI)
    fix vs
    assume "vs \<in> {ts. \<exists>ts' \<in> X. ad_agr_list AD (map Inl ts) ts'}"
    then obtain vs' where vs'_def: "vs' \<in> proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
      "ad_agr_list AD (map Inl vs) (fo_nmlz AD (map Inl vs'))"
      using X_def
      by auto
    have "length vs = length (fv_fo_fmla_list \<phi>)"
      using vs'_def
      by (auto simp: proj_fmla_map ad_agr_list_def fo_nmlz_length)
    then obtain \<sigma> where \<sigma>_def: "vs = map \<sigma> (fv_fo_fmla_list \<phi>)"
      using exists_map[of "fv_fo_fmla_list \<phi>" vs] sorted_distinct_fv_list
      by fastforce
    obtain \<tau> where \<tau>_def: "fo_nmlz AD (map Inl vs') = map \<tau> (fv_fo_fmla_list \<phi>)"
      using vs'_def fo_nmlz_map
      by (fastforce simp: proj_fmla_map)
    have ad_agr: "ad_agr_list AD (map (Inl \<circ> \<sigma>) (fv_fo_fmla_list \<phi>)) (map \<tau> (fv_fo_fmla_list \<phi>))"
      by (metis \<sigma>_def \<tau>_def map_map vs'_def(2))
    obtain \<tau>' where \<tau>'_def: "map Inl vs' = map (Inl \<circ> \<tau>') (fv_fo_fmla_list \<phi>)"
      "sat \<phi> I \<tau>'"
      using vs'_def(1)
      by (fastforce simp: proj_fmla_map)
    have ad_agr': "ad_agr_list AD (map \<tau> (fv_fo_fmla_list \<phi>))
        (map (Inl \<circ> \<tau>') (fv_fo_fmla_list \<phi>))"
      by (rule ad_agr_list_comm) (metis fo_nmlz_ad_agr \<tau>'_def(1) \<tau>_def map_map map_projl_Inl)
    have esat: "esat \<phi> I \<tau> UNIV"
      using esat_UNIV_ad_agr_list[OF ad_agr' AD_sub, folded sat_esat_conv[OF assms]] \<tau>'_def(2)
      by auto
    show "vs \<in> proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
      using esat_UNIV_ad_agr_list[OF ad_agr AD_sub, folded sat_esat_conv[OF assms]] esat
      unfolding \<sigma>_def
      by (auto simp: proj_fmla_map)
  next
    fix vs
    assume "vs \<in> proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
    then have vs_X: "fo_nmlz AD (map Inl vs) \<in> X"
      using X_def
      by auto
    then show "vs \<in> {ts. \<exists>ts' \<in> X. ad_agr_list AD (map Inl ts) ts'}"
      using fo_nmlz_ad_agr
      by auto
  qed
  then show ?thesis
    by (auto simp: AD_X_def proj_sat_fmla)
qed

lemma fo_wf_eval_abs:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes "wf_fo_intp \<phi> I"
  shows "fo_wf \<phi> I (eval_abs \<phi> I)"
  using fo_nmlz_set[of "act_edom \<phi> I"] finite_act_edom[OF assms(1)]
    finite_subset[OF fo_nmlz_proj_sub, OF nall_tuples_finite]
    fo_rep_eval_abs[OF assms] assms
  by (auto simp: eval_abs_def fo_nmlz_sound fo_nmlz_length nfv_def proj_sat_def proj_fmla_map) blast

lemma fo_fin:
  fixes t :: "('a :: infinite, nat) fo_t"
  assumes "fo_wf \<phi> I t"
  shows "fo_fin t = finite (fo_rep t)"
proof -
  obtain AD n X where t_def: "t = (AD, n, X)"
    using assms
    by (cases t) auto
  have fin: "finite AD" "finite X"
    using assms
    by (auto simp: t_def)
  have len_in_X: "\<And>vs. vs \<in> X \<Longrightarrow> length vs = n"
    using assms
    by (auto simp: t_def)
  have Inl_X_AD: "\<And>x. Inl x \<in> \<Union>(set ` X) \<Longrightarrow> x \<in> AD"
    using assms
    by (fastforce simp: t_def)
  define Z where "Z = {ts. \<exists>ts' \<in> X. ad_agr_list AD (map Inl ts) ts'}"
  have fin_Z_iff: "finite Z = (\<Union>(set ` Z) \<subseteq> AD)"
    using assms fin_ad_agr_list_iff[OF fin(1) _ Z_def, of n]
    by (auto simp: Z_def t_def ad_agr_list_def)
  moreover have "(\<Union>(set ` Z) \<subseteq> AD) \<longleftrightarrow> (\<forall>x \<in> \<Union>(set ` X). isl x)"
  proof (rule iffI, rule ccontr)
    fix x
    assume Z_sub_AD: "\<Union>(set ` Z) \<subseteq> AD"
    assume "\<not>(\<forall>x \<in> \<Union>(set ` X). isl x)"
    then obtain vs i m where vs_def: "vs \<in> X" "i < n" "vs ! i = Inr m"
      using len_in_X
      by (auto simp: in_set_conv_nth) (metis sum.collapse(2))
    obtain \<sigma> where \<sigma>_def: "vs = map \<sigma> [0..<n]"
      using exists_map[of "[0..<n]" vs] len_in_X[OF vs_def(1)]
      by auto
    obtain \<tau> where \<tau>_def: "ad_agr_list AD vs (map Inl (map \<tau> [0..<n]))"
      using proj_out_list[OF fin(1), of \<sigma> "[0..<n]"]
      by (auto simp: \<sigma>_def)
    have map_\<tau>_in_Z: "map \<tau> [0..<n] \<in> Z"
      using vs_def(1) ad_agr_list_comm[OF \<tau>_def]
      by (auto simp: Z_def)
    moreover have "\<tau> i \<notin> AD"
      using \<tau>_def vs_def(2,3)
      apply (auto simp: ad_agr_list_def ad_equiv_list_def set_zip comp_def \<sigma>_def)
      unfolding ad_equiv_pair.simps
      by (metis (no_types, lifting) Inl_Inr_False diff_zero image_iff length_upt nth_map nth_upt
          plus_nat.add_0)
    ultimately show "False"
      using vs_def(2) Z_sub_AD
      by fastforce
  next
    assume "\<forall>x \<in> \<Union>(set ` X). isl x"
    then show "\<Union>(set ` Z) \<subseteq> AD"
      using Inl_X_AD
      apply (auto simp: Z_def ad_agr_list_def ad_equiv_list_def set_zip in_set_conv_nth)
      unfolding ad_equiv_pair.simps
      by (metis image_eqI isl_def nth_map nth_mem)
  qed
  ultimately show ?thesis
    by (auto simp: t_def Z_def[symmetric])
qed

lemma eval_pred:
  fixes I :: "'b \<times> nat \<Rightarrow> 'a :: infinite list set"
  assumes "finite (I (r, length ts))"
  shows "fo_wf (Pred r ts) I (eval_pred ts (I (r, length ts)))"
proof -
  define \<phi> where "\<phi> = Pred r ts"
  have nfv_len: "nfv \<phi> = length (fv_fo_terms_list ts)"
    by (auto simp: \<phi>_def nfv_def fv_fo_fmla_list_def fv_fo_fmla_list_Pred)
  have vimage_unfold: "Inl -` (\<Union>x\<in>I (r, length ts). Inl ` set x) = \<Union>(set ` I (r, length ts))"
    by auto
  have "eval_table ts (map Inl ` I (r, length ts)) \<subseteq> nall_tuples (act_edom \<phi> I) (nfv \<phi>)"
    by (auto simp: \<phi>_def proj_vals_def eval_table nfv_len[unfolded \<phi>_def]
        fo_nmlz_length fo_nmlz_sound eval_eterms_def fv_fo_terms_set_list fv_fo_terms_set_def
        vimage_unfold intro!: nall_tuplesI fo_nmlzd_all_AD dest!: fv_fo_term_setD)
       (smt UN_I Un_iff eval_eterm.simps(2) imageE image_eqI list.set_map)
  then have eval: "eval_pred ts (I (r, length ts)) = eval_abs \<phi> I"
    by (force simp: eval_abs_def \<phi>_def proj_fmla_def eval_pred_def eval_table fv_fo_fmla_list_def
        fv_fo_fmla_list_Pred nall_tuples_set fo_nmlz_idem nfv_len[unfolded \<phi>_def])
  have fin: "wf_fo_intp (Pred r ts) I"
    using assms
    by auto
  show ?thesis
    using fo_wf_eval_abs[OF fin]
    by (auto simp: eval \<phi>_def)
qed

lemma ad_agr_list_eval: "\<Union>(set (map set_fo_term ts)) \<subseteq> AD \<Longrightarrow> ad_agr_list AD (\<sigma> \<odot>e ts) zs \<Longrightarrow>
  \<exists>\<tau>. zs = \<tau> \<odot>e ts"
proof (induction ts arbitrary: zs)
  case (Cons t ts)
  obtain w ws where zs_split: "zs = w # ws"
    using Cons(3)
    by (cases zs) (auto simp: ad_agr_list_def eval_eterms_def)
  obtain \<tau> where \<tau>_def: "ws = \<tau> \<odot>e ts"
    using Cons
    by (fastforce simp: zs_split ad_agr_list_def ad_equiv_list_def sp_equiv_list_def pairwise_def
        eval_eterms_def)
  show ?case
  proof (cases t)
    case (Const c)
    then show ?thesis
      using Cons(3)[unfolded zs_split] Cons(2)
      unfolding Const
      apply (auto simp: zs_split eval_eterms_def \<tau>_def ad_agr_list_def ad_equiv_list_def)
      unfolding ad_equiv_pair.simps
      by blast
  next
    case (Var n)
    show ?thesis
    proof (cases "n \<in> fv_fo_terms_set ts")
      case True
      obtain i where i_def: "i < length ts" "ts ! i = Var n"
        using True
        by (auto simp: fv_fo_terms_set_def in_set_conv_nth dest!: fv_fo_term_setD)
      have "w = \<tau> n"
        using Cons(3)[unfolded zs_split \<tau>_def] i_def
        using pairwiseD[of sp_equiv_pair _ "(\<sigma> n, w)" "(\<sigma> \<cdot>e (ts ! i), \<tau> \<cdot>e (ts ! i))"]
        by (force simp: Var eval_eterms_def ad_agr_list_def sp_equiv_list_def set_zip)
      then show ?thesis
        by (auto simp: Var zs_split eval_eterms_def \<tau>_def)
    next
      case False
      then have "ws = (\<tau>(n := w)) \<odot>e ts"
        using eval_eterms_cong[of ts \<tau> "\<tau>(n := w)"] \<tau>_def
        by fastforce
      then show ?thesis
        by (auto simp: zs_split eval_eterms_def Var fun_upd_def intro: exI[of _ "\<tau>(n := w)"])
    qed
  qed
qed (auto simp: ad_agr_list_def eval_eterms_def)

lemma sp_equiv_list_fv_list:
  assumes "sp_equiv_list (\<sigma> \<odot>e ts) (\<tau> \<odot>e ts)"
  shows "sp_equiv_list (map \<sigma> (fv_fo_terms_list ts)) (map \<tau> (fv_fo_terms_list ts))"
proof -
  have "sp_equiv_list (\<sigma> \<odot>e (map Var (fv_fo_terms_list ts)))
    (\<tau> \<odot>e (map Var (fv_fo_terms_list ts)))"
    unfolding eval_eterms_def
    by (rule sp_equiv_list_subset[OF _ assms[unfolded eval_eterms_def]])
       (auto simp: fv_fo_terms_set_list dest: fv_fo_terms_setD)
  then show ?thesis
    by (auto simp: eval_eterms_def comp_def)
qed

lemma ad_agr_list_fv_list: "ad_agr_list X (\<sigma> \<odot>e ts) (\<tau> \<odot>e ts) \<Longrightarrow>
  ad_agr_list X (map \<sigma> (fv_fo_terms_list ts)) (map \<tau> (fv_fo_terms_list ts))"
  using sp_equiv_list_fv_list
  by (auto simp: eval_eterms_def ad_agr_list_def ad_equiv_list_def sp_equiv_list_def set_zip)
     (metis (no_types, opaque_lifting) eval_eterm.simps(2) fv_fo_terms_setD fv_fo_terms_set_list
      in_set_conv_nth nth_map)

lemma eval_bool: "fo_wf (Bool b) I (eval_bool b)"
  by (auto simp: eval_bool_def fo_nmlzd_def nats_def Let_def List.map_filter_simps
      proj_sat_def fv_fo_fmla_list_def ad_agr_list_def ad_equiv_list_def sp_equiv_list_def nfv_def)

lemma eval_eq: fixes I :: "'b \<times> nat \<Rightarrow> 'a :: infinite list set"
  shows "fo_wf (Eqa t t') I (eval_eq t t')"
proof -
  define \<phi> :: "('a, 'b) fo_fmla" where "\<phi> = Eqa t t'"
  obtain AD n X where AD_X_def: "eval_eq t t' = (AD, n, X)"
    by (cases "eval_eq t t'") auto
  have AD_def: "AD = act_edom \<phi> I"
    using AD_X_def
    by (auto simp: eval_eq_def \<phi>_def split: fo_term.splits if_splits)
  have n_def: "n = nfv \<phi>"
    using AD_X_def
    by (cases t; cases t')
       (auto simp: \<phi>_def fv_fo_fmla_list_def eval_eq_def nfv_def split: if_splits)
  have fo_nmlz_empty_x_x: "fo_nmlz {} [x, x] = [Inr 0, Inr 0]" for x :: "'a + nat"
    by (cases x) (auto simp: fo_nmlz_def)
  have Inr_0_in_fo_nmlz_empty: "[Inr 0, Inr 0] \<in> fo_nmlz {} ` (\<lambda>x. [x n', x n']) ` {\<sigma> :: nat \<Rightarrow> 'a + nat. \<sigma> n = \<sigma> n'}" for n n'
    by (auto simp: image_def fo_nmlz_empty_x_x intro!: exI[of _ "[Inr 0, Inr 0]"])
  have X_def: "X = fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
  proof (rule set_eqI, rule iffI)
    fix vs
    assume assm: "vs \<in> X"
    define pes where "pes = proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
    have "\<And>c c'. t = Const c \<and> t' = Const c' \<Longrightarrow>
      fo_nmlz AD ` pes = (if c = c' then {[]} else {})"
      by (auto simp: \<phi>_def pes_def proj_fmla_map fo_nmlz_def fv_fo_fmla_list_def)
    moreover have "\<And>c n. (t = Const c \<and> t' = Var n) \<or> (t' = Const c \<and> t = Var n) \<Longrightarrow>
      fo_nmlz AD ` pes = {[Inl c]}"
      by (auto simp: \<phi>_def AD_def pes_def proj_fmla_map fo_nmlz_Cons fv_fo_fmla_list_def image_def
          split: sum.splits) (auto simp: fo_nmlz_def)
    moreover have "\<And>n. t = Var n \<Longrightarrow> t' = Var n \<Longrightarrow> fo_nmlz AD ` pes = {[Inr 0]}"
      by (auto simp: \<phi>_def AD_def pes_def proj_fmla_map fo_nmlz_Cons fv_fo_fmla_list_def image_def
          split: sum.splits)
    moreover have "\<And>n n'. t = Var n \<Longrightarrow> t' = Var n' \<Longrightarrow> n \<noteq> n' \<Longrightarrow>
      fo_nmlz AD ` pes = {[Inr 0, Inr 0]}"
      using Inr_0_in_fo_nmlz_empty
      by (auto simp: \<phi>_def AD_def pes_def proj_fmla_map fo_nmlz_Cons fv_fo_fmla_list_def fo_nmlz_empty_x_x
          split: sum.splits)
    ultimately show "vs \<in> fo_nmlz AD ` pes"
      using assm AD_X_def
      by (cases t; cases t') (auto simp: eval_eq_def split: if_splits)
  next
    fix vs
    assume assm: "vs \<in> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
    obtain \<sigma> where \<sigma>_def: "vs = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list \<phi>))"
      "esat (Eqa t t') I \<sigma> UNIV"
      using assm
      by (auto simp: \<phi>_def fv_fo_fmla_list_def proj_fmla_map)
    show "vs \<in> X"
      using \<sigma>_def AD_X_def
      by (cases t; cases t')
         (auto simp: \<phi>_def eval_eq_def fv_fo_fmla_list_def fo_nmlz_Cons fo_nmlz_Cons_Cons
          split: sum.splits)
  qed
  have eval: "eval_eq t t' = eval_abs \<phi> I"
    using X_def[unfolded AD_def]
    by (auto simp: eval_abs_def AD_X_def AD_def n_def)
  have fin: "wf_fo_intp \<phi> I"
    by (auto simp: \<phi>_def)
  show ?thesis
    using fo_wf_eval_abs[OF fin]
    by (auto simp: eval \<phi>_def)
qed

lemma fv_fo_terms_list_Var: "fv_fo_terms_list_rec (map Var ns) = ns"
  by (induction ns) auto

lemma eval_eterms_map_Var: "\<sigma> \<odot>e map Var ns = map \<sigma> ns"
  by (auto simp: eval_eterms_def)

lemma fo_wf_eval_table:
  fixes AD :: "'a set"
  assumes "fo_wf \<phi> I (AD, n, X)"
  shows "X = fo_nmlz AD ` eval_table (map Var [0..<n]) X"
proof -
  have AD_sup: "Inl -` \<Union>(set ` X) \<subseteq> AD"
    using assms
    by fastforce
  have fvs: "fv_fo_terms_list (map Var [0..<n]) = [0..<n]"
    by (auto simp: fv_fo_terms_list_def fv_fo_terms_list_Var remdups_adj_distinct)
  have "\<And>vs. vs \<in> X \<Longrightarrow> length vs = n"
    using assms
    by auto
  then have X_map: "\<And>vs. vs \<in> X \<Longrightarrow> \<exists>\<sigma>. vs = map \<sigma> [0..<n]"
    using exists_map[of "[0..<n]"]
    by auto
  then have proj_vals_X: "proj_vals {\<sigma>. \<sigma> \<odot>e map Var [0..<n] \<in> X} [0..<n] = X"
    by (auto simp: eval_eterms_map_Var proj_vals_def)
  then show "X = fo_nmlz AD ` eval_table (map Var [0..<n]) X"
    unfolding eval_table fvs proj_vals_X
    using assms fo_nmlz_idem image_iff
    by fastforce
qed

lemma fo_rep_norm:
  fixes AD :: "('a :: infinite) set"
  assumes "fo_wf \<phi> I (AD, n, X)"
  shows "X = fo_nmlz AD ` map Inl ` fo_rep (AD, n, X)"
proof (rule set_eqI, rule iffI)
  fix vs
  assume vs_in: "vs \<in> X"
  have fin_AD: "finite AD"
    using assms(1)
    by auto
  have len_vs: "length vs = n"
    using vs_in assms(1)
    by auto
  obtain \<tau> where \<tau>_def: "ad_agr_list AD vs (map Inl (map \<tau> [0..<n]))"
    using proj_out_list[OF fin_AD, of "(!) vs" "[0..<length vs]", unfolded map_nth]
    by (auto simp: len_vs)
  have map_\<tau>_in: "map \<tau> [0..<n] \<in> fo_rep (AD, n, X)"
    using vs_in ad_agr_list_comm[OF \<tau>_def]
    by auto
  have "vs = fo_nmlz AD (map Inl (map \<tau> [0..<n]))"
    using fo_nmlz_eqI[OF \<tau>_def] fo_nmlz_idem vs_in assms(1)
    by fastforce
  then show "vs \<in> fo_nmlz AD ` map Inl ` fo_rep (AD, n, X)"
    using map_\<tau>_in
    by blast
next
  fix vs
  assume "vs \<in> fo_nmlz AD ` map Inl ` fo_rep (AD, n, X)"
  then obtain xs xs' where vs_def: "xs' \<in> X" "ad_agr_list AD (map Inl xs) xs'"
    "vs = fo_nmlz AD (map Inl xs)"
    by auto
  then have "vs = fo_nmlz AD xs'"
    using fo_nmlz_eqI[OF vs_def(2)]
    by auto
  then have "vs = xs'"
    using vs_def(1) assms(1) fo_nmlz_idem
    by fastforce
  then show "vs \<in> X"
    using vs_def(1)
    by auto
qed

lemma fo_wf_X:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes wf: "fo_wf \<phi> I (AD, n, X)"
  shows "X = fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
proof -
  have fin: "wf_fo_intp \<phi> I"
    using wf
    by auto
  have AD_def: "AD = act_edom \<phi> I"
    using wf
    by auto
  have fo_wf: "fo_wf \<phi> I (AD, n, X)"
    using wf
    by auto
  have fo_rep: "fo_rep (AD, n, X) = proj_fmla \<phi> {\<sigma>. sat \<phi> I \<sigma>}"
    using wf
    by (auto simp: proj_sat_def proj_fmla_map)
  show ?thesis
    using fo_rep_norm[OF fo_wf] norm_proj_fmla_esat_sat[OF fin]
    unfolding fo_rep AD_def[symmetric]
    by auto
qed

lemma eval_neg:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes wf: "fo_wf \<phi> I t"
  shows "fo_wf (Neg \<phi>) I (eval_neg (fv_fo_fmla_list \<phi>) t)"
proof -
  obtain AD n X where t_def: "t = (AD, n, X)"
    by (cases t) auto
  have eval_neg: "eval_neg (fv_fo_fmla_list \<phi>) t = (AD, nfv \<phi>, nall_tuples AD (nfv \<phi>) - X)"
    by (auto simp: t_def nfv_def)
  have fv_unfold: "fv_fo_fmla_list (Neg \<phi>) = fv_fo_fmla_list \<phi>"
    by (auto simp: fv_fo_fmla_list_def)
  then have nfv_unfold: "nfv (Neg \<phi>) = nfv \<phi>"
    by (auto simp: nfv_def)
  have AD_def: "AD = act_edom (Neg \<phi>) I"
    using wf
    by (auto simp: t_def)
  note X_def = fo_wf_X[OF wf[unfolded t_def]]
  have esat_iff: "\<And>vs. vs \<in> nall_tuples AD (nfv \<phi>) \<Longrightarrow>
    vs \<in> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV} \<longleftrightarrow>
    vs \<notin> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat (Neg \<phi>) I \<sigma> UNIV}"
  proof (rule iffI; rule ccontr)
    fix vs
    assume "vs \<in> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
    then obtain \<sigma> where \<sigma>_def: "vs = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list \<phi>))"
      "esat \<phi> I \<sigma> UNIV"
      by (auto simp: proj_fmla_map)
    assume "\<not>vs \<notin> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat (Neg \<phi>) I \<sigma> UNIV}"
    then obtain \<sigma>' where \<sigma>'_def: "vs = fo_nmlz AD (map \<sigma>' (fv_fo_fmla_list \<phi>))"
      "esat (Neg \<phi>) I \<sigma>' UNIV"
      by (auto simp: proj_fmla_map)
    have "esat \<phi> I \<sigma> UNIV = esat \<phi> I \<sigma>' UNIV"
      using esat_UNIV_cong[OF ad_agr_sets_restrict[OF iffD2[OF ad_agr_list_link],
            OF fo_nmlz_eqD[OF trans[OF \<sigma>_def(1)[symmetric] \<sigma>'_def(1)]]]]
      by (auto simp: AD_def)
    then show "False"
      using \<sigma>_def(2) \<sigma>'_def(2) by simp
  next
    fix vs
    assume assms: "vs \<notin> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat (Neg \<phi>) I \<sigma> UNIV}"
      "vs \<notin> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
    assume "vs \<in> nall_tuples AD (nfv \<phi>)"
    then have l_vs: "length vs = length (fv_fo_fmla_list \<phi>)" "fo_nmlzd AD vs"
      by (auto simp: nfv_def dest: nall_tuplesD)
    obtain \<sigma> where "vs = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list \<phi>))"
      using l_vs sorted_distinct_fv_list exists_fo_nmlzd by metis
    with assms show "False"
      by (auto simp: proj_fmla_map)
  qed
  moreover have "\<And>R. fo_nmlz AD ` proj_fmla \<phi> R \<subseteq> nall_tuples AD (nfv \<phi>)"
    by (auto simp: proj_fmla_map nfv_def nall_tuplesI fo_nmlz_length fo_nmlz_sound)
  ultimately have eval: "eval_neg (fv_fo_fmla_list \<phi>) t = eval_abs (Neg \<phi>) I"
    unfolding eval_neg eval_abs_def AD_def[symmetric]
    by (auto simp: X_def proj_fmla_def fv_unfold nfv_unfold image_subset_iff)
  have wf_neg: "wf_fo_intp (Neg \<phi>) I"
    using wf
    by (auto simp: t_def)
  show ?thesis
    using fo_wf_eval_abs[OF wf_neg]
    by (auto simp: eval)
qed

definition "cross_with f t t' = \<Union>((\<lambda>xs. \<Union>(f xs ` t')) ` t)"

lemma mapping_join_cross_with:
  assumes "\<And>x x'. x \<in> t \<Longrightarrow> x' \<in> t' \<Longrightarrow> h x \<noteq> h' x' \<Longrightarrow> f x x' = {}"
  shows "set_of_idx (mapping_join (cross_with f) (cluster (Some \<circ> h) t) (cluster (Some \<circ> h') t')) = cross_with f t t'"
proof -
  have sub: "cross_with f {y \<in> t. h y = h x} {y \<in> t'. h' y = h x} \<subseteq> cross_with f t t'" for t t' x
    by (auto simp: cross_with_def)
  have "\<exists>a. a \<in> h ` t \<and> a \<in> h' ` t' \<and> z \<in> cross_with f {y \<in> t. h y = a} {y \<in> t'. h' y = a}" if z: "z \<in> cross_with f t t'" for z
  proof -
    obtain xs ys where wit: "xs \<in> t" "ys \<in> t'" "z \<in> f xs ys"
      using z
      by (auto simp: cross_with_def)
    have h: "h xs = h' ys"
      using assms(1)[OF wit(1-2)] wit(3)
      by auto
    have hys: "h' ys \<in> h ` t"
      using wit(1)
      by (auto simp: h[symmetric])
    show ?thesis
      apply (rule exI[of _ "h xs"])
      using wit hys h
      by (auto simp: cross_with_def)
  qed
  then show ?thesis
    using sub
    apply (transfer fixing: f h h')
    apply (auto simp: ran_def)
     apply fastforce+
    done
qed

lemma fo_nmlzd_mono_sub: "X \<subseteq> X' \<Longrightarrow> fo_nmlzd X xs \<Longrightarrow> fo_nmlzd X' xs"
  by (meson fo_nmlzd_def order_trans)

lemma idx_join:
  assumes X\<phi>_props: "\<And>vs. vs \<in> X\<phi> \<Longrightarrow> fo_nmlzd AD vs \<and> length vs = length ns\<phi>"
  assumes X\<psi>_props: "\<And>vs. vs \<in> X\<psi> \<Longrightarrow> fo_nmlzd AD vs \<and> length vs = length ns\<psi>"
  assumes sd_ns: "sorted_distinct ns\<phi>" "sorted_distinct ns\<psi>"
  assumes ns_def: "ns = filter (\<lambda>n. n \<in> set ns\<psi>) ns\<phi>"
  shows "idx_join AD ns ns\<phi> X\<phi> ns\<psi> X\<psi> = eval_conj_set AD ns\<phi> X\<phi> ns\<psi> X\<psi>"
proof -
  have ect_empty: "x \<in> X\<phi> \<Longrightarrow> x' \<in> X\<psi> \<Longrightarrow> fo_nmlz AD (proj_tuple ns (zip ns\<phi> x)) \<noteq> fo_nmlz AD (proj_tuple ns (zip ns\<psi> x')) \<Longrightarrow>
    eval_conj_tuple AD ns\<phi> ns\<psi> x x' = {}"
    if "X\<phi>' \<subseteq> X\<phi>" "X\<psi>' \<subseteq> X\<psi>" for X\<phi>' X\<psi>' and x x'
    apply (rule eval_conj_tuple_empty[where ?ns="filter (\<lambda>n. n \<in> set ns\<psi>) ns\<phi>"])
    using X\<phi>_props X\<psi>_props that sd_ns
    by (auto simp: ns_def ad_agr_close_set_def split: if_splits)
  have cross_eval_conj_tuple: "(\<lambda>X\<phi>''. eval_conj_set AD ns\<phi> X\<phi>'' ns\<psi>) = cross_with (eval_conj_tuple AD ns\<phi> ns\<psi>)" for AD :: "'a set" and ns\<phi> ns\<psi>
    by (rule ext)+ (auto simp: eval_conj_set_def cross_with_def)
  have "idx_join AD ns ns\<phi> X\<phi> ns\<psi> X\<psi> = cross_with (eval_conj_tuple AD ns\<phi> ns\<psi>) X\<phi> X\<psi>"
    unfolding idx_join_def Let_def cross_eval_conj_tuple
    by (rule mapping_join_cross_with[OF ect_empty]) auto
  moreover have "\<dots> = eval_conj_set AD ns\<phi> X\<phi> ns\<psi> X\<psi>"
    by (auto simp: cross_with_def eval_conj_set_def)
  finally show ?thesis .
qed

lemma proj_fmla_conj_sub:
  assumes AD_sub: "act_edom \<psi> I \<subseteq> AD"
  shows "fo_nmlz AD ` proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat \<phi> I \<sigma> UNIV} \<inter>
    fo_nmlz AD ` proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat \<psi> I \<sigma> UNIV} \<subseteq>
    fo_nmlz AD ` proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat (Conj \<phi> \<psi>) I \<sigma> UNIV}"
proof (rule subsetI)
  fix vs
  assume "vs \<in> fo_nmlz AD `  proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat \<phi> I \<sigma> UNIV} \<inter>
      fo_nmlz AD `  proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat \<psi> I \<sigma> UNIV}"
  then obtain \<sigma> \<sigma>' where \<sigma>_def:
    "\<sigma> \<in> {\<sigma>. esat \<phi> I \<sigma> UNIV}" "vs = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list (Conj \<phi> \<psi>)))"
    "\<sigma>' \<in> {\<sigma>. esat \<psi> I \<sigma> UNIV}" "vs = fo_nmlz AD (map \<sigma>' (fv_fo_fmla_list (Conj \<phi> \<psi>)))"
    unfolding proj_fmla_map
    by blast
  have ad_sub: "act_edom \<psi> I \<subseteq> AD"
    using assms(1)
    by auto
  have ad_agr: "ad_agr_list AD (map \<sigma> (fv_fo_fmla_list \<psi>)) (map \<sigma>' (fv_fo_fmla_list \<psi>))"
    by (rule ad_agr_list_subset[OF _ fo_nmlz_eqD[OF trans[OF \<sigma>_def(2)[symmetric] \<sigma>_def(4)]]])
       (auto simp: fv_fo_fmla_list_set)
  have "\<sigma> \<in> {\<sigma>. esat \<psi> I \<sigma> UNIV}"
    using esat_UNIV_cong[OF ad_agr_sets_restrict[OF iffD2[OF ad_agr_list_link]],
          OF ad_agr ad_sub] \<sigma>_def(3)
    by blast
  then show "vs \<in> fo_nmlz AD ` proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat (Conj \<phi> \<psi>) I \<sigma> UNIV}"
    using \<sigma>_def(1,2)
    by (auto simp: proj_fmla_map)
qed

lemma eval_conj:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes wf: "fo_wf \<phi> I t\<phi>" "fo_wf \<psi> I t\<psi>"
  shows "fo_wf (Conj \<phi> \<psi>) I (eval_conj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>)"
proof -
  obtain AD\<phi> n\<phi> X\<phi> AD\<psi> n\<psi> X\<psi> where ts_def:
    "t\<phi> = (AD\<phi>, n\<phi>, X\<phi>)" "t\<psi> = (AD\<psi>, n\<psi>, X\<psi>)"
    "AD\<phi> = act_edom \<phi> I" "AD\<psi> = act_edom \<psi> I"
    using assms
    by (cases t\<phi>, cases t\<psi>) auto
  have AD_sub: "act_edom \<phi> I \<subseteq> AD\<phi>" "act_edom \<psi> I \<subseteq> AD\<psi>"
    by (auto simp: ts_def(3,4))

  obtain AD n X where AD_X_def:
    "eval_conj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi> = (AD, n, X)"
    by (cases "eval_conj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>") auto
  have AD_def: "AD = act_edom (Conj \<phi> \<psi>) I" "act_edom (Conj \<phi> \<psi>) I \<subseteq> AD"
    "AD\<phi> \<subseteq> AD" "AD\<psi> \<subseteq> AD" "AD = AD\<phi> \<union> AD\<psi>"
    using AD_X_def
    by (auto simp: ts_def Let_def)
  have n_def: "n = nfv (Conj \<phi> \<psi>)"
    using AD_X_def
    by (auto simp: ts_def Let_def nfv_card fv_fo_fmla_list_set)

  define S\<phi> where "S\<phi> \<equiv> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
  define S\<psi> where "S\<psi> \<equiv> {\<sigma>. esat \<psi> I \<sigma> UNIV}"
  define AD\<Delta>\<phi> where "AD\<Delta>\<phi> = AD - AD\<phi>"
  define AD\<Delta>\<psi> where "AD\<Delta>\<psi> = AD - AD\<psi>"
  define ns\<phi> where "ns\<phi> = fv_fo_fmla_list \<phi>"
  define ns\<psi> where "ns\<psi> = fv_fo_fmla_list \<psi>"
  define ns where "ns = filter (\<lambda>n. n \<in> fv_fo_fmla \<phi>) (fv_fo_fmla_list \<psi>)"
  define ns\<phi>' where "ns\<phi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<phi>) (fv_fo_fmla_list \<psi>)"
  define ns\<psi>' where "ns\<psi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<psi>) (fv_fo_fmla_list \<phi>)"

  note X\<phi>_def = fo_wf_X[OF wf(1)[unfolded ts_def(1)], unfolded proj_fmla_def, folded S\<phi>_def]
  note X\<psi>_def = fo_wf_X[OF wf(2)[unfolded ts_def(2)], unfolded proj_fmla_def, folded S\<psi>_def]

  have sd_ns: "sorted_distinct ns\<phi>" "sorted_distinct ns\<psi>"
    by (auto simp: ns\<phi>_def ns\<psi>_def sorted_distinct_fv_list)
  have ad_agr_X\<phi>: "ad_agr_close_set AD\<Delta>\<phi> X\<phi> = fo_nmlz AD ` proj_vals S\<phi> ns\<phi>"
    unfolding X\<phi>_def ad_agr_close_set_nmlz_eq ns\<phi>_def[symmetric] AD\<Delta>\<phi>_def
    apply (rule ad_agr_close_set_correct[OF AD_def(3) sd_ns(1)])
    using AD_sub(1) esat_UNIV_ad_agr_list
    by (fastforce simp: ad_agr_list_link S\<phi>_def ns\<phi>_def)
  have ad_agr_X\<psi>: "ad_agr_close_set AD\<Delta>\<psi> X\<psi> = fo_nmlz AD ` proj_vals S\<psi> ns\<psi>"
    unfolding X\<psi>_def ad_agr_close_set_nmlz_eq ns\<psi>_def[symmetric] AD\<Delta>\<psi>_def
    apply (rule ad_agr_close_set_correct[OF AD_def(4) sd_ns(2)])
    using AD_sub(2) esat_UNIV_ad_agr_list
    by (fastforce simp: ad_agr_list_link S\<psi>_def ns\<psi>_def)

  have idx_join_eval_conj: "idx_join AD (filter (\<lambda>n. n \<in> set ns\<psi>) ns\<phi>) ns\<phi> (ad_agr_close_set AD\<Delta>\<phi> X\<phi>) ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> X\<psi>) =
    eval_conj_set AD ns\<phi> (ad_agr_close_set AD\<Delta>\<phi> X\<phi>) ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> X\<psi>)"
    apply (rule idx_join[OF _ _ sd_ns])
    unfolding ad_agr_X\<phi> ad_agr_X\<psi>
    by (auto simp: fo_nmlz_sound fo_nmlz_length proj_vals_def)

  have fv_sub: "fv_fo_fmla (Conj \<phi> \<psi>) = fv_fo_fmla \<phi> \<union> set (fv_fo_fmla_list \<psi>)"
    "fv_fo_fmla (Conj \<phi> \<psi>) = fv_fo_fmla \<psi> \<union> set (fv_fo_fmla_list \<phi>)"
    by (auto simp: fv_fo_fmla_list_set)
  note res_left_alt = ext_tuple_ad_agr_close[OF S\<phi>_def AD_sub(1) AD_def(3)
       X\<phi>_def(1)[folded S\<phi>_def] ns\<phi>'_def sorted_distinct_fv_list fv_sub(1)]
  note res_right_alt = ext_tuple_ad_agr_close[OF S\<psi>_def AD_sub(2) AD_def(4)
       X\<psi>_def(1)[folded S\<psi>_def] ns\<psi>'_def sorted_distinct_fv_list fv_sub(2)]

  note eval_conj_set = eval_conj_set_correct[OF ns\<phi>'_def[folded fv_fo_fmla_list_set]
       ns\<psi>'_def[folded fv_fo_fmla_list_set] res_left_alt(2) res_right_alt(2)
       sorted_distinct_fv_list sorted_distinct_fv_list]
  have "X = fo_nmlz AD ` proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat \<phi> I \<sigma> UNIV} \<inter>
     fo_nmlz AD ` proj_fmla (Conj \<phi> \<psi>) {\<sigma>. esat \<psi> I \<sigma> UNIV}"
    using AD_X_def
    apply (simp add: ts_def(1,2) Let_def ts_def(3,4)[symmetric] AD_def(5)[symmetric] idx_join_eval_conj[unfolded ns\<phi>_def ns\<psi>_def AD\<Delta>\<phi>_def AD\<Delta>\<psi>_def])
    unfolding eval_conj_set proj_fmla_def
    unfolding res_left_alt(1) res_right_alt(1) S\<phi>_def S\<psi>_def
    by auto
  then have eval: "eval_conj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi> =
    eval_abs (Conj \<phi> \<psi>) I"
    using proj_fmla_conj_sub[OF AD_def(4)[unfolded ts_def(4)], of \<phi>]
    unfolding AD_X_def AD_def(1)[symmetric] n_def eval_abs_def
    by (auto simp: proj_fmla_map)
  have wf_conj: "wf_fo_intp (Conj \<phi> \<psi>) I"
    using wf
    by (auto simp: ts_def)
  show ?thesis
    using fo_wf_eval_abs[OF wf_conj]
    by (auto simp: eval)
qed

lemma map_values_cluster: "(\<And>w z Z. Z \<subseteq> X \<Longrightarrow> z \<in> Z \<Longrightarrow> w \<in> f (h z) {z} \<Longrightarrow> w \<in> f (h z) Z) \<Longrightarrow>
  (\<And>w z Z. Z \<subseteq> X \<Longrightarrow> z \<in> Z \<Longrightarrow> w \<in> f (h z) Z \<Longrightarrow> (\<exists>z'\<in>Z. w \<in> f (h z) {z'})) \<Longrightarrow>
  set_of_idx (Mapping.map_values f (cluster (Some \<circ> h) X)) = \<Union>((\<lambda>x. f (h x) {x}) ` X)"
  apply transfer
  apply (auto simp: ran_def)
   apply (smt (verit, del_insts) mem_Collect_eq subset_eq)
  apply (smt (z3) imageI mem_Collect_eq subset_iff)
  done

lemma fo_nmlz_twice:
  assumes "sorted_distinct ns" "sorted_distinct ns'" "set ns \<subseteq> set ns'"
  shows "fo_nmlz AD (proj_tuple ns (zip ns' (fo_nmlz AD (map \<sigma> ns')))) = fo_nmlz AD (map \<sigma> ns)"
proof -
  obtain \<sigma>' where \<sigma>': "fo_nmlz AD (map \<sigma> ns') = map \<sigma>' ns'"
    using exists_map[where ?ys="fo_nmlz AD (map \<sigma> ns')" and ?xs=ns'] assms
    by (auto simp: fo_nmlz_length)
  have proj: "proj_tuple ns (zip ns' (map \<sigma>' ns')) = map \<sigma>' ns"
    by (rule proj_tuple_map[OF assms])
  show ?thesis
    unfolding \<sigma>' proj
    apply (rule fo_nmlz_eqI)
    using \<sigma>'
    by (metis ad_agr_list_comm ad_agr_list_subset assms(3) fo_nmlz_ad_agr)
qed

lemma map_values_cong:
  assumes "\<And>x y. Mapping.lookup t x = Some y \<Longrightarrow> f x y = f' x y"
  shows "Mapping.map_values f t = Mapping.map_values f' t"
proof -
  have "map_option (f x) (Mapping.lookup t x) = map_option (f' x) (Mapping.lookup t x)" for x
    using assms
    by (cases "Mapping.lookup t x") auto
  then show ?thesis
    by (auto simp: lookup_map_values intro!: mapping_eqI)
qed

lemma ad_agr_close_set_length: "z \<in> ad_agr_close_set AD X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> length x = n) \<Longrightarrow> length z = n"
  by (auto simp: ad_agr_close_set_def ad_agr_close_def split: if_splits dest: ad_agr_close_rec_length)

lemma ad_agr_close_set_sound: "z \<in> ad_agr_close_set (AD - AD') X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> fo_nmlzd AD' x) \<Longrightarrow> AD' \<subseteq> AD \<Longrightarrow> fo_nmlzd AD z"
  using ad_agr_close_sound[where ?X=AD' and ?Y="AD - AD'"]
  by (auto simp: ad_agr_close_set_def Set.is_empty_def split: if_splits) (metis Diff_partition Un_Diff_cancel)

lemma ext_tuple_set_length: "z \<in> ext_tuple_set AD ns ns' X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> length x = length ns) \<Longrightarrow> length z = length ns + length ns'"
  by (auto simp: ext_tuple_set_def ext_tuple_def fo_nmlz_length merge_length dest: nall_tuples_rec_length split: if_splits)

lemma eval_ajoin:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes wf: "fo_wf \<phi> I t\<phi>" "fo_wf \<psi> I t\<psi>"
  shows "fo_wf (Conj \<phi> (Neg \<psi>)) I
    (eval_ajoin (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>)"
proof -
  obtain AD\<phi> n\<phi> X\<phi> AD\<psi> n\<psi> X\<psi> where ts_def:
    "t\<phi> = (AD\<phi>, n\<phi>, X\<phi>)" "t\<psi> = (AD\<psi>, n\<psi>, X\<psi>)"
    "AD\<phi> = act_edom \<phi> I" "AD\<psi> = act_edom \<psi> I"
    using assms
    by (cases t\<phi>, cases t\<psi>) auto
  have AD_sub: "act_edom \<phi> I \<subseteq> AD\<phi>" "act_edom \<psi> I \<subseteq> AD\<psi>"
    by (auto simp: ts_def(3,4))

  obtain AD n X where AD_X_def:
    "eval_ajoin (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi> = (AD, n, X)"
    by (cases "eval_ajoin (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>") auto
  have AD_def: "AD = act_edom (Conj \<phi> (Neg \<psi>)) I"
    "act_edom (Conj \<phi> (Neg \<psi>)) I \<subseteq> AD" "AD\<phi> \<subseteq> AD" "AD\<psi> \<subseteq> AD" "AD = AD\<phi> \<union> AD\<psi>"
    using AD_X_def
    by (auto simp: ts_def Let_def)
  have n_def: "n = nfv (Conj \<phi> (Neg \<psi>))"
    using AD_X_def
    by (auto simp: ts_def Let_def nfv_card fv_fo_fmla_list_set)

  define S\<phi> where "S\<phi> \<equiv> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
  define S\<psi> where "S\<psi> \<equiv> {\<sigma>. esat \<psi> I \<sigma> UNIV}"
  define both where "both = remdups_adj (sort (fv_fo_fmla_list \<phi> @ fv_fo_fmla_list \<psi>))"
  define ns\<phi>' where "ns\<phi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<phi>) (fv_fo_fmla_list \<psi>)"
  define ns\<psi>' where "ns\<psi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<psi>) (fv_fo_fmla_list \<phi>)"

  define AD\<Delta>\<phi> where "AD\<Delta>\<phi> = AD - AD\<phi>"
  define AD\<Delta>\<psi> where "AD\<Delta>\<psi> = AD - AD\<psi>"
  define ns\<phi> where "ns\<phi> = fv_fo_fmla_list \<phi>"
  define ns\<psi> where "ns\<psi> = fv_fo_fmla_list \<psi>"
  define ns where "ns = filter (\<lambda>n. n \<in> set ns\<psi>) ns\<phi>"
  define X\<phi>' where "X\<phi>' = ext_tuple_set AD ns\<phi> ns\<phi>' (ad_agr_close_set AD\<Delta>\<phi> X\<phi>)"
  define idx\<phi> where "idx\<phi> = cluster (Some \<circ> (\<lambda>xs. fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> xs)))) (ad_agr_close_set AD\<Delta>\<phi> X\<phi>)"
  define idx\<psi> where "idx\<psi> = cluster (Some \<circ> (\<lambda>ys. fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<psi> ys)))) X\<psi>"
  define res where "res = Mapping.map_values (\<lambda>xs X. case Mapping.lookup idx\<psi> xs of
    Some Y \<Rightarrow> eval_conj_set AD ns\<phi> X ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {xs} - Y))
    | _ \<Rightarrow> ext_tuple_set AD ns\<phi> ns\<phi>' X) idx\<phi>"

  note X\<phi>_def = fo_wf_X[OF wf(1)[unfolded ts_def(1)], unfolded proj_fmla_def, folded S\<phi>_def]
  note X\<psi>_def = fo_wf_X[OF wf(2)[unfolded ts_def(2)], unfolded proj_fmla_def, folded S\<psi>_def]

  have fv_sub: "fv_fo_fmla (Conj \<phi> (Neg \<psi>)) = fv_fo_fmla \<psi> \<union> set (fv_fo_fmla_list \<phi>)"
    by (auto simp: fv_fo_fmla_list_set)
  have fv_sort: "fv_fo_fmla_list (Conj \<phi> (Neg \<psi>)) = both"
    unfolding both_def
    apply (rule sorted_distinct_set_unique)
    using sorted_distinct_fv_list
    by (auto simp: fv_fo_fmla_list_def distinct_remdups_adj_sort)

  have AD_disj: "AD\<phi> \<inter> AD\<Delta>\<phi> = {}" "AD\<psi> \<inter> AD\<Delta>\<psi> = {}"
    by (auto simp: AD\<Delta>\<phi>_def AD\<Delta>\<psi>_def)
  have AD_delta: "AD = AD\<phi> \<union> AD\<Delta>\<phi>" "AD = AD\<psi> \<union> AD\<Delta>\<psi>"
    by (auto simp: AD\<Delta>\<phi>_def AD\<Delta>\<psi>_def AD_def ts_def)
  have fo_nmlzd_X: "Ball X\<phi> (fo_nmlzd AD\<phi>)" "Ball X\<psi> (fo_nmlzd AD\<psi>)"
    using wf
    by (auto simp: ts_def)
  have Ball_ad_agr: "Ball (ad_agr_close_set AD\<Delta>\<phi> X\<phi>) (fo_nmlzd AD)"
    using ad_agr_close_sound[where ?X="AD\<phi>" and ?Y="AD\<Delta>\<phi>"] fo_nmlzd_X(1)
    by (auto simp: ad_agr_close_set_eq[OF fo_nmlzd_X(1)] AD_disj AD_delta)
  have ad_agr_\<phi>:
    "\<And>\<sigma> \<tau>. ad_agr_sets (set (fv_fo_fmla_list \<phi>)) (set (fv_fo_fmla_list \<phi>)) AD\<phi> \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> S\<phi> \<longleftrightarrow> \<tau> \<in> S\<phi>"
    "\<And>\<sigma> \<tau>. ad_agr_sets (set (fv_fo_fmla_list \<phi>)) (set (fv_fo_fmla_list \<phi>)) AD \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> S\<phi> \<longleftrightarrow> \<tau> \<in> S\<phi>"
    using esat_UNIV_cong[OF ad_agr_sets_restrict, OF _ subset_refl] ad_agr_sets_mono AD_sub(1) subset_trans[OF AD_sub(1) AD_def(3)]
    unfolding S\<phi>_def
    by blast+
  have ad_agr_S\<phi>: "\<tau>' \<in> S\<phi> \<Longrightarrow> ad_agr_list AD\<phi> (map \<tau>' ns\<phi>) (map \<tau>'' ns\<phi>) \<Longrightarrow> \<tau>'' \<in> S\<phi>" for \<tau>' \<tau>''
    using ad_agr_\<phi>
    by (auto simp: ad_agr_list_link ns\<phi>_def)
  have ad_agr_\<psi>:
    "\<And>\<sigma> \<tau>. ad_agr_sets (set (fv_fo_fmla_list \<psi>)) (set (fv_fo_fmla_list \<psi>)) AD\<psi> \<sigma> \<tau> \<Longrightarrow> \<sigma> \<in> S\<psi> \<longleftrightarrow> \<tau> \<in> S\<psi>"
    using esat_UNIV_cong[OF ad_agr_sets_restrict, OF _ subset_refl] ad_agr_sets_mono[OF AD_sub(2)]
    unfolding S\<psi>_def
    by blast+
  have ad_agr_S\<psi>: "\<tau>' \<in> S\<psi> \<Longrightarrow> ad_agr_list AD\<psi> (map \<tau>' ns\<psi>) (map \<tau>'' ns\<psi>) \<Longrightarrow> \<tau>'' \<in> S\<psi>" for \<tau>' \<tau>''
    using ad_agr_\<psi>
    by (auto simp: ad_agr_list_link ns\<psi>_def)
  have aux: "sorted_distinct ns\<phi>" "sorted_distinct ns\<phi>'" "sorted_distinct both" "set ns\<phi> \<inter> set ns\<phi>' = {}" "set ns\<phi> \<union> set ns\<phi>' = set both"
    by (auto simp: ns\<phi>_def ns\<phi>'_def fv_sort[symmetric] fv_fo_fmla_list_set sorted_distinct_fv_list intro: sorted_filter[where ?f=id, simplified])
  have aux2: "ns\<phi>' = filter (\<lambda>n. n \<notin> set ns\<phi>) ns\<phi>'" "ns\<phi> = filter (\<lambda>n. n \<notin> set ns\<phi>') ns\<phi>"
    by (auto simp: ns\<phi>_def ns\<phi>'_def ns\<psi>_def ns\<psi>'_def fv_fo_fmla_list_set)
  have aux3: "set ns\<phi>' \<inter> set ns = {}" "set ns\<phi>' \<union> set ns = set ns\<psi>"
    by (auto simp: ns\<phi>_def ns\<phi>'_def ns\<psi>_def ns_def fv_fo_fmla_list_set)
  have aux4: "set ns \<inter> set ns\<phi>' = {}" "set ns \<union> set ns\<phi>' = set ns\<psi>"
    by (auto simp: ns\<phi>_def ns\<phi>'_def ns\<psi>_def ns_def fv_fo_fmla_list_set)
  have aux5: "ns\<phi>' = filter (\<lambda>n. n \<notin> set ns\<phi>) ns\<psi>" "ns\<psi>' = filter (\<lambda>n. n \<notin> set ns\<psi>) ns\<phi>"
    by (auto simp: ns\<phi>_def ns\<phi>'_def ns\<psi>_def ns\<psi>'_def fv_fo_fmla_list_set)
  have aux6: "set ns\<psi> \<inter> set ns\<psi>' = {}" "set ns\<psi> \<union> set ns\<psi>' = set both"
    by (auto simp: ns\<phi>_def ns\<phi>'_def ns\<psi>_def ns\<psi>'_def both_def fv_fo_fmla_list_set)
  have ns_sd: "sorted_distinct ns" "sorted_distinct ns\<phi>" "sorted_distinct ns\<psi>" "set ns \<subseteq> set ns\<phi>" "set ns \<subseteq> set ns\<psi>" "set ns \<subseteq> set both" "set ns\<phi>' \<subseteq> set ns\<psi>" "set ns\<psi> \<subseteq> set both"
    by (auto simp: ns_def ns\<phi>_def ns\<phi>'_def ns\<psi>_def both_def sorted_distinct_fv_list intro: sorted_filter[where ?f=id, simplified])
  have ns_sd': "sorted_distinct ns\<psi>'"
    by (auto simp: ns\<psi>'_def sorted_distinct_fv_list intro: sorted_filter[where ?f=id, simplified])
  have ns: "ns = filter (\<lambda>n. n \<in> fv_fo_fmla \<phi>) (fv_fo_fmla_list \<psi>)"
    by (rule sorted_distinct_set_unique)
       (auto simp: ns_def ns\<phi>_def ns\<psi>_def fv_fo_fmla_list_set sorted_distinct_fv_list intro: sorted_filter[where ?f=id, simplified])
  have len_ns\<psi>: "length ns + length ns\<phi>' = length ns\<psi>"
    using sum_length_filter_compl[where ?P="\<lambda>n. n \<in> fv_fo_fmla \<phi>" and ?xs="fv_fo_fmla_list \<psi>"]
    by (auto simp: ns ns\<phi>_def ns\<phi>'_def ns\<psi>_def fv_fo_fmla_list_set)

  have res_eq: "res = Mapping.map_values (\<lambda>xs X. case Mapping.lookup idx\<psi> xs of
    Some Y \<Rightarrow> idx_join AD ns ns\<phi> X ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {xs} - Y))
    | _ \<Rightarrow> ext_tuple_set AD ns\<phi> ns\<phi>' X) idx\<phi>"
  proof -
    have ad_agr_X\<phi>: "ad_agr_close_set AD\<Delta>\<phi> X\<phi> = fo_nmlz AD ` proj_vals S\<phi> ns\<phi>"
      unfolding X\<phi>_def ad_agr_close_set_nmlz_eq ns\<phi>_def[symmetric]
      apply (rule ad_agr_close_set_correct[OF AD_def(3) aux(1), folded AD\<Delta>\<phi>_def])
      using ad_agr_S\<phi> ad_agr_list_comm
      by (fastforce simp: ad_agr_list_link)
    have idx_eval: "idx_join AD ns ns\<phi> y ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {x} - x2)) =
       eval_conj_set AD ns\<phi> y ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {x} - x2))"
      if lup: "Mapping.lookup idx\<phi> x = Some y" "Mapping.lookup idx\<psi> x = Some x2" for x y x2
    proof -
      have "vs \<in> y \<Longrightarrow> fo_nmlzd AD vs \<and> length vs = length ns\<phi>" for vs
        using lup(1)
        by (auto simp: idx\<phi>_def lookup_cluster' ad_agr_X\<phi> fo_nmlz_sound fo_nmlz_length proj_vals_def split: if_splits)
      moreover have "vs \<in> ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {x} - x2) \<Longrightarrow> fo_nmlzd AD vs" for vs
        apply (rule ad_agr_close_set_sound[OF _ _ AD_def(4), folded AD\<Delta>\<psi>_def, where ?X="ext_tuple_set AD\<psi> ns ns\<phi>' {x} - x2"])
        using lup(1)
        by (auto simp: idx\<phi>_def lookup_cluster' ext_tuple_set_def fo_nmlz_sound split: if_splits)
      moreover have "vs \<in> ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {x} - x2) \<Longrightarrow> length vs = length ns\<psi>" for vs
        apply (erule ad_agr_close_set_length)
        apply (rule ext_tuple_set_length[where ?AD=AD\<psi> and ?ns=ns and ?ns'=ns\<phi>' and ?X="{x}", unfolded len_ns\<psi>])
        using lup(1) ns_sd(1,2,4)
        by (auto simp: idx\<phi>_def lookup_cluster' fo_nmlz_length ad_agr_X\<phi> proj_vals_def intro!: proj_tuple_length split: if_splits)
      ultimately show ?thesis
        by (auto intro!: idx_join[OF _ _ ns_sd(2-3) ns_def])
    qed
    show ?thesis
      unfolding res_def
      by (rule map_values_cong) (auto simp: idx_eval split: option.splits)
  qed

  have eval_conj: "eval_conj_set AD ns\<phi> {x} ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))} - Y)) =
  ext_tuple_set AD ns\<phi> ns\<phi>' {x} \<inter> ext_tuple_set AD ns\<psi> ns\<psi>' (fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>)"
    if x_ns: "proj_tuple ns (zip ns\<phi> x) = map \<sigma>' ns"
      and x_proj_singleton: "{x} = fo_nmlz AD ` proj_vals {\<sigma>} ns\<phi>"
      and Some: "Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))) = Some Y"
    for x Y \<sigma> \<sigma>'
  proof -
    have "Y = {ys \<in> fo_nmlz AD\<psi> ` proj_vals S\<psi> ns\<psi>. fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<psi> ys)) = fo_nmlz AD\<psi> (map \<sigma>' ns)}"
      using Some
      apply (auto simp: X\<psi>_def idx\<psi>_def ns\<psi>_def x_ns lookup_cluster' split: if_splits)
      done
    moreover have "\<dots> = fo_nmlz AD\<psi> ` proj_vals {\<sigma> \<in> S\<psi>. fo_nmlz AD\<psi> (map \<sigma> ns) = fo_nmlz AD\<psi> (map \<sigma>' ns)} ns\<psi>"
      by (auto simp: proj_vals_def fo_nmlz_twice[OF ns_sd(1,3,5)])+
    moreover have "\<dots> = fo_nmlz AD\<psi> ` proj_vals {\<sigma> \<in> S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>"
      by (auto simp: fo_nmlz_eq)
    ultimately have Y_def: "Y = fo_nmlz AD\<psi> ` proj_vals {\<sigma> \<in> S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>"
      by auto
    have R_def: "{fo_nmlz AD\<psi> (map \<sigma>' ns)} = fo_nmlz AD\<psi> ` proj_vals {\<sigma>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns"
      using ad_agr_list_refl
      by (auto simp: proj_vals_def intro: fo_nmlz_eqI)
    have "ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (map \<sigma>' ns)} = fo_nmlz AD\<psi> ` proj_vals {\<sigma>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>"
      apply (rule ext_tuple_correct[OF ns_sd(1) aux(2) ns_sd(3) aux4 R_def])
      using ad_agr_list_trans ad_agr_list_comm
      apply (auto simp: ad_agr_list_link)
      by fast
    then have "ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (map \<sigma>' ns)} - Y = fo_nmlz AD\<psi> ` proj_vals {\<sigma> \<in> -S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>"
      apply (auto simp: Y_def proj_vals_def fo_nmlz_eq)
      using ad_agr_S\<psi> ad_agr_list_comm
      by blast+
    moreover have "ad_agr_close_set AD\<Delta>\<psi> (fo_nmlz AD\<psi> ` proj_vals {\<sigma> \<in> -S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>) =
      fo_nmlz AD ` proj_vals {\<sigma> \<in> -S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>"
      unfolding ad_agr_close_set_eq[OF Ball_fo_nmlzd]
      apply (rule ad_agr_close_set_correct[OF AD_def(4) ns_sd(3), folded AD\<Delta>\<psi>_def])
      apply (auto simp: ad_agr_list_link)
      using ad_agr_S\<psi> ad_agr_list_comm ad_agr_list_subset[OF ns_sd(5)] ad_agr_list_trans
      by blast+
    ultimately have comp_proj: "ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (map \<sigma>' ns)} - Y) =
          fo_nmlz AD ` proj_vals {\<sigma> \<in> -S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>"
      by simp
    have "ext_tuple_set AD ns\<psi> ns\<psi>' (fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>) = fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} both"
      apply (rule ext_tuple_correct[OF ns_sd(3) ns_sd'(1) aux(3) aux6 refl])
      apply (auto simp: ad_agr_list_link)
      using ad_agr_S\<psi> ad_agr_list_comm ad_agr_list_subset[OF ns_sd(5)] ad_agr_list_trans ad_agr_list_mono[OF AD_def(4)]
      by fast+
    show "eval_conj_set AD ns\<phi> {x} ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))} - Y)) =
      ext_tuple_set AD ns\<phi> ns\<phi>' {x} \<inter> ext_tuple_set AD ns\<psi> ns\<psi>' (fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>)"
      unfolding x_ns comp_proj
      using eval_conj_set_correct[OF aux5 x_proj_singleton refl aux(1) ns_sd(3)]
      by auto
  qed

  have "X = set_of_idx res"
    using AD_X_def
    unfolding eval_ajoin.simps ts_def(1,2) Let_def AD_def(5)[symmetric] fv_fo_fmla_list_set
      ns\<phi>'_def[symmetric] fv_sort[symmetric] proj_fmla_def S\<phi>_def[symmetric] S\<psi>_def[symmetric]
      AD\<Delta>\<phi>_def[symmetric] AD\<Delta>\<psi>_def[symmetric]
      ns\<phi>_def[symmetric] ns\<phi>'_def[symmetric, folded fv_fo_fmla_list_set[of \<phi>, folded ns\<phi>_def] ns\<psi>_def] ns\<psi>_def[symmetric] ns_def[symmetric]
      X\<phi>'_def[symmetric] idx\<phi>_def[symmetric] idx\<psi>_def[symmetric] res_eq[symmetric]
    by auto
  moreover have "\<dots> = (\<Union>x\<in>ad_agr_close_set AD\<Delta>\<phi> X\<phi>.
      case Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))) of None \<Rightarrow> ext_tuple_set AD ns\<phi> ns\<phi>' {x}
      | Some Y \<Rightarrow> eval_conj_set AD ns\<phi> {x} ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))} - Y)))"
    unfolding res_def[unfolded idx\<phi>_def]
    apply (rule map_values_cluster)
     apply (auto simp: eval_conj_set_def split: option.splits)
     apply (auto simp: ext_tuple_set_def split: if_splits)
    done
  moreover have "\<dots> = fo_nmlz AD ` proj_fmla (Conj \<phi> (Neg \<psi>)) {\<sigma>. esat \<phi> I \<sigma> UNIV} -
     fo_nmlz AD ` proj_fmla (Conj \<phi> (Neg \<psi>)) {\<sigma>. esat \<psi> I \<sigma> UNIV}"
    unfolding S\<phi>_def[symmetric] S\<psi>_def[symmetric] proj_fmla_def fv_sort
  proof (rule set_eqI, rule iffI)
    fix t
    assume "t \<in> (\<Union>x\<in>ad_agr_close_set AD\<Delta>\<phi> X\<phi>. case Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))) of
      None \<Rightarrow> ext_tuple_set AD ns\<phi> ns\<phi>' {x}
    | Some Y \<Rightarrow> eval_conj_set AD ns\<phi> {x} ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))} - Y)))"
    then obtain x where x: "x \<in> ad_agr_close_set AD\<Delta>\<phi> X\<phi>"
      "Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))) = None \<Longrightarrow> t \<in> ext_tuple_set AD ns\<phi> ns\<phi>' {x}"
      "\<And>Y. Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))) = Some Y \<Longrightarrow>
      t \<in> eval_conj_set AD ns\<phi> {x} ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))} - Y))"
      by (fastforce split: option.splits)
    obtain \<sigma> where val: "\<sigma> \<in> S\<phi>" "x = fo_nmlz AD (map \<sigma> ns\<phi>)"
      using ad_agr_close_correct[OF AD_def(3) ad_agr_\<phi>(1), folded AD\<Delta>\<phi>_def] X\<phi>_def[folded proj_fmla_def] ad_agr_close_set_eq[OF fo_nmlzd_X(1)] x(1)
      apply (auto simp: proj_fmla_def proj_vals_def ns\<phi>_def)
      apply fast
      done
    obtain \<sigma>' where \<sigma>': "x = map \<sigma>' ns\<phi>"
      using exists_map[where ?ys=x and ?xs=ns\<phi>] aux(1)
      by (auto simp: val(2) fo_nmlz_length)
    have x_proj_singleton: "{x} = fo_nmlz AD ` proj_vals {\<sigma>} ns\<phi>"
      by (auto simp: val(2) proj_vals_def)
    have x_ns: "proj_tuple ns (zip ns\<phi> x) = map \<sigma>' ns"
      unfolding \<sigma>'
      by (rule proj_tuple_map[OF ns_sd(1-2,4)])
    have ad_agr_\<sigma>_\<sigma>': "ad_agr_list AD (map \<sigma> ns\<phi>) (map \<sigma>' ns\<phi>)"
      using \<sigma>'
      by (auto simp: val(2)) (metis fo_nmlz_ad_agr)
    have x_proj_ad_agr: "{x} = fo_nmlz AD ` proj_vals {\<sigma>. ad_agr_list AD (map \<sigma> ns\<phi>) (map \<sigma>' ns\<phi>)} ns\<phi>"
      using ad_agr_\<sigma>_\<sigma>' ad_agr_list_comm ad_agr_list_trans
      by (auto simp: val(2) proj_vals_def fo_nmlz_eq) blast
    have "t \<in> fo_nmlz AD ` \<Union> (ext_tuple AD ns\<phi> ns\<phi>' ` {x}) \<Longrightarrow> fo_nmlz AD (proj_tuple ns\<phi> (zip both t)) \<in> {x}"
      apply (rule ext_tuple_sound(1)[OF aux x_proj_ad_agr])
       apply (auto simp: ad_agr_list_link)
      using ad_agr_list_comm ad_agr_list_trans
      by blast+
    then have x_proj: "t \<in> ext_tuple_set AD ns\<phi> ns\<phi>' {x} \<Longrightarrow> x = fo_nmlz AD (proj_tuple ns\<phi> (zip both t))"
      using ext_tuple_set_eq[where ?AD=AD] Ball_ad_agr x(1)
      by (auto simp: val(2) proj_vals_def)
    have x_S\<phi>: "t \<in> ext_tuple_set AD ns\<phi> ns\<phi>' {x} \<Longrightarrow> t \<in> fo_nmlz AD ` proj_vals S\<phi> both"
      using ext_tuple_correct[OF aux refl ad_agr_\<phi>(2)[folded ns\<phi>_def]] ext_tuple_set_mono[of "{x}" "fo_nmlz AD ` proj_vals S\<phi> ns\<phi>"] val(1)
      by (fastforce simp: val(2) proj_vals_def)
    show "t \<in> fo_nmlz AD ` proj_vals S\<phi> both - fo_nmlz AD ` proj_vals S\<psi> both"
    proof (cases "Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x)))")
      case None
      have "False" if t_in_S\<psi>: "t \<in> fo_nmlz AD ` proj_vals S\<psi> both"
      proof -
        obtain \<tau> where \<tau>: "\<tau> \<in> S\<psi>" "t = fo_nmlz AD (map \<tau> both)"
          using t_in_S\<psi>
          by (auto simp: proj_vals_def)
        obtain \<tau>' where t_\<tau>': "t = map \<tau>' both"
          using aux(3) exists_map[where ?ys=t and ?xs=both]
          by (auto simp: \<tau>(2) fo_nmlz_length)
        obtain \<tau>'' where \<tau>'': "fo_nmlz AD\<psi> (map \<tau> ns\<psi>) = map \<tau>'' ns\<psi>"
          using ns_sd exists_map[where ?ys="fo_nmlz AD\<psi> (map \<tau> ns\<psi>)" and xs=ns\<psi>]
          by (auto simp: fo_nmlz_length)
        have proj_\<tau>'': "proj_tuple ns (zip ns\<psi> (map \<tau>'' ns\<psi>)) = map \<tau>'' ns"
          apply (rule proj_tuple_map)
          using ns_sd
          by auto
        have "proj_tuple ns\<phi> (zip both t) = map \<tau>' ns\<phi>"
          unfolding t_\<tau>'
          apply (rule proj_tuple_map)
          using aux
          by auto
        then have x_\<tau>': "x = fo_nmlz AD (map \<tau>' ns\<phi>)"
          by (auto simp: x_proj[OF x(2)[OF None]])
        obtain \<tau>''' where \<tau>''': "x = map \<tau>''' ns\<phi>"
          using aux exists_map[where ?ys=x and ?xs=ns\<phi>]
          by (auto simp: x_\<tau>' fo_nmlz_length)
        have ad_\<tau>_\<tau>': "ad_agr_list AD (map \<tau> both) (map \<tau>' both)"
          using t_\<tau>'
          by (auto simp: \<tau>) (metis fo_nmlz_ad_agr)
        have ad_\<tau>_\<tau>'': "ad_agr_list AD\<psi> (map \<tau> ns\<psi>) (map \<tau>'' ns\<psi>)"
          using \<tau>''
          by (metis fo_nmlz_ad_agr)
        have ad_\<tau>'_\<tau>''': "ad_agr_list AD (map \<tau>' ns\<phi>) (map \<tau>''' ns\<phi>)"
          using \<tau>'''
          by (auto simp: x_\<tau>') (metis fo_nmlz_ad_agr)
        have proj_\<tau>''': "proj_tuple ns (zip ns\<phi> (map \<tau>''' ns\<phi>)) = map \<tau>''' ns"
          apply (rule proj_tuple_map)
          using aux ns_sd
          by auto
        have "fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x)) = fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<psi> (fo_nmlz AD\<psi> (map \<tau> ns\<psi>))))"
          unfolding \<tau>'' proj_\<tau>'' \<tau>''' proj_\<tau>'''
          apply (rule fo_nmlz_eqI)
          using ad_agr_list_trans ad_agr_list_subset ns_sd(4-6) ad_agr_list_mono[OF AD_def(4)] ad_agr_list_comm[OF ad_\<tau>'_\<tau>'''] ad_agr_list_comm[OF ad_\<tau>_\<tau>'] ad_\<tau>_\<tau>''
          by metis
        then show ?thesis
          using None \<tau>(1)
          by (auto simp: idx\<psi>_def lookup_cluster' X\<psi>_def ns\<psi>_def[symmetric] proj_vals_def split: if_splits)
      qed
      then show ?thesis
        using x_S\<phi>[OF x(2)[OF None]]
        by auto
    next
      case (Some Y)
      have t_in: "t \<in> ext_tuple_set AD ns\<phi> ns\<phi>' {x}" "t \<in> ext_tuple_set AD ns\<psi> ns\<psi>' (fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>)"
        using x(3)[OF Some] eval_conj[OF x_ns x_proj_singleton Some]
        by auto
      have "ext_tuple_set AD ns\<psi> ns\<psi>' (fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>) = fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} both"
        apply (rule ext_tuple_correct[OF ns_sd(3) ns_sd'(1) aux(3) aux6 refl])
        apply (auto simp: ad_agr_list_link)
        using ad_agr_S\<psi> ad_agr_list_comm ad_agr_list_subset[OF ns_sd(5)] ad_agr_list_trans ad_agr_list_mono[OF AD_def(4)]
        by fast+
      then have t_both: "t \<in> fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} both"
        using t_in(2)
        by auto
      {
        assume "t \<in> fo_nmlz AD ` proj_vals S\<psi> both"
        then obtain \<tau> where \<tau>: "\<tau> \<in> S\<psi>" "t = fo_nmlz AD (map \<tau> both)"
          by (auto simp: proj_vals_def)
        obtain \<tau>' where \<tau>': "\<tau>' \<notin> S\<psi>" "t = fo_nmlz AD (map \<tau>' both)"
          using t_both
          by (auto simp: proj_vals_def)
        have "False"
          using \<tau> \<tau>'
          apply (auto simp: fo_nmlz_eq)
          using ad_agr_S\<psi> ad_agr_list_comm ad_agr_list_subset[OF ns_sd(8)] ad_agr_list_mono[OF AD_def(4)]
          by blast
      }
      then show ?thesis
        using x_S\<phi>[OF t_in(1)]
        by auto
    qed
  next
    fix t
    assume t_in_asm: "t \<in> fo_nmlz AD ` proj_vals S\<phi> both - fo_nmlz AD ` proj_vals S\<psi> both"
    then obtain \<sigma> where val: "\<sigma> \<in> S\<phi>" "t = fo_nmlz AD (map \<sigma> both)"
      by (auto simp: proj_vals_def)
    define x where "x = fo_nmlz AD (map \<sigma> ns\<phi>)"
    obtain \<sigma>' where \<sigma>': "x = map \<sigma>' ns\<phi>"
      using exists_map[where ?ys=x and ?xs=ns\<phi>] aux(1)
      by (auto simp: x_def fo_nmlz_length)
    have x_proj_singleton: "{x} = fo_nmlz AD ` proj_vals {\<sigma>} ns\<phi>"
      by (auto simp: x_def proj_vals_def)
    have x_in_ad_agr_close: "x \<in> ad_agr_close_set AD\<Delta>\<phi> X\<phi>"
      using ad_agr_close_correct[OF AD_def(3) ad_agr_\<phi>(1), folded AD\<Delta>\<phi>_def] val(1)
      unfolding ad_agr_close_set_eq[OF fo_nmlzd_X(1)] x_def
      unfolding X\<phi>_def[folded proj_fmla_def] proj_fmla_map
      by (fastforce simp: x_def ns\<phi>_def)
    have ad_agr_\<sigma>_\<sigma>': "ad_agr_list AD (map \<sigma> ns\<phi>) (map \<sigma>' ns\<phi>)"
      using \<sigma>'
      by (auto simp: x_def) (metis fo_nmlz_ad_agr)
    have x_proj_ad_agr: "{x} = fo_nmlz AD ` proj_vals {\<sigma>. ad_agr_list AD (map \<sigma> ns\<phi>) (map \<sigma>' ns\<phi>)} ns\<phi>"
      using ad_agr_\<sigma>_\<sigma>' ad_agr_list_comm ad_agr_list_trans
      by (auto simp: x_def proj_vals_def fo_nmlz_eq) blast+
    have x_ns: "proj_tuple ns (zip ns\<phi> x) = map \<sigma>' ns"
      unfolding \<sigma>'
      by (rule proj_tuple_map[OF ns_sd(1-2,4)])
    have "ext_tuple_set AD ns\<phi> ns\<phi>' {x} = fo_nmlz AD ` proj_vals {\<sigma>. ad_agr_list AD (map \<sigma> ns\<phi>) (map \<sigma>' ns\<phi>)} both"
      apply (rule ext_tuple_correct[OF aux x_proj_ad_agr])
      using ad_agr_list_comm ad_agr_list_trans
      by (auto simp: ad_agr_list_link) blast+
    then have t_in_ext_x: "t \<in> ext_tuple_set AD ns\<phi> ns\<phi>' {x}"
      using ad_agr_\<sigma>_\<sigma>'
      by (auto simp: val(2) proj_vals_def)
    {
      fix Y
      assume Some: "Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (map \<sigma>' ns)) = Some Y"
      have tmp: "proj_tuple ns (zip ns\<phi> x) = map \<sigma>' ns"
        unfolding \<sigma>'
        by (rule proj_tuple_map[OF ns_sd(1) aux(1) ns_sd(4)])
      have unfold: "ext_tuple_set AD ns\<psi> ns\<psi>' (fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>) =
        fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} both"
        apply (rule ext_tuple_correct[OF ns_sd(3) ns_sd'(1) aux(3) aux6 refl])
        apply (auto simp: ad_agr_list_link)
        using ad_agr_S\<psi> ad_agr_list_mono[OF AD_def(4)] ad_agr_list_comm ad_agr_list_trans ad_agr_list_subset[OF ns_sd(5)]
        by blast+
      have "\<sigma> \<notin> S\<psi>"
        using t_in_asm
        by (auto simp: val(2) proj_vals_def)
      moreover have "ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)"
        using ad_agr_\<sigma>_\<sigma>' ad_agr_list_mono[OF AD_def(4)] ad_agr_list_subset[OF ns_sd(4)]
        by blast
      ultimately have "t \<in> ext_tuple_set AD ns\<psi> ns\<psi>' (fo_nmlz AD ` proj_vals {\<sigma> \<in> - S\<psi>. ad_agr_list AD\<psi> (map \<sigma> ns) (map \<sigma>' ns)} ns\<psi>)"
        unfolding unfold val(2)
        by (auto simp: proj_vals_def)
      then have "t \<in> eval_conj_set AD ns\<phi> {x} ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (map \<sigma>' ns)} - Y))"
        using eval_conj[OF tmp x_proj_singleton Some[folded x_ns]] t_in_ext_x
        by (auto simp: x_ns)
    }
    then show "t \<in> (\<Union>x\<in>ad_agr_close_set AD\<Delta>\<phi> X\<phi>. case Mapping.lookup idx\<psi> (fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))) of
      None \<Rightarrow> ext_tuple_set AD ns\<phi> ns\<phi>' {x}
    | Some Y \<Rightarrow> eval_conj_set AD ns\<phi> {x} ns\<psi> (ad_agr_close_set AD\<Delta>\<psi> (ext_tuple_set AD\<psi> ns ns\<phi>' {fo_nmlz AD\<psi> (proj_tuple ns (zip ns\<phi> x))} - Y)))"
      using t_in_ext_x
      by (intro UN_I[OF x_in_ad_agr_close]) (auto simp: x_ns split: option.splits)
  qed
  ultimately have X_def: "X = fo_nmlz AD ` proj_fmla (Conj \<phi> (Neg \<psi>)) {\<sigma>. esat \<phi> I \<sigma> UNIV} -
    fo_nmlz AD ` proj_fmla (Conj \<phi> (Neg \<psi>)) {\<sigma>. esat \<psi> I \<sigma> UNIV}"
    by simp

  have AD_Neg_sub: "act_edom (Neg \<psi>) I \<subseteq> AD"
    by (auto simp: AD_def(1))
  have "X = fo_nmlz AD ` proj_fmla (Conj \<phi> (Neg \<psi>)) {\<sigma>. esat \<phi> I \<sigma> UNIV} \<inter>
    fo_nmlz AD ` proj_fmla (Conj \<phi> (Neg \<psi>)) {\<sigma>. esat (Neg \<psi>) I \<sigma> UNIV}"
    unfolding X_def
    by (auto simp: proj_fmla_map dest!: fo_nmlz_eqD)
       (metis AD_def(4) ad_agr_list_subset esat_UNIV_ad_agr_list fv_fo_fmla_list_set fv_sub
        sup_ge1 ts_def(4))
  then have eval: "eval_ajoin (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi> =
    eval_abs (Conj \<phi> (Neg \<psi>)) I"
    using proj_fmla_conj_sub[OF AD_Neg_sub, of \<phi>]
    unfolding AD_X_def AD_def(1)[symmetric] n_def eval_abs_def
    by (auto simp: proj_fmla_map)
  have wf_conj_neg: "wf_fo_intp (Conj \<phi> (Neg \<psi>)) I"
    using wf
    by (auto simp: ts_def)
  show ?thesis
    using fo_wf_eval_abs[OF wf_conj_neg]
    by (auto simp: eval)
qed

lemma eval_disj:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes wf: "fo_wf \<phi> I t\<phi>" "fo_wf \<psi> I t\<psi>"
  shows "fo_wf (Disj \<phi> \<psi>) I
    (eval_disj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>)"
proof -
  obtain AD\<phi> n\<phi> X\<phi> AD\<psi> n\<psi> X\<psi> where ts_def:
    "t\<phi> = (AD\<phi>, n\<phi>, X\<phi>)" "t\<psi> = (AD\<psi>, n\<psi>, X\<psi>)"
    "AD\<phi> = act_edom \<phi> I" "AD\<psi> = act_edom \<psi> I"
    using assms
    by (cases t\<phi>, cases t\<psi>) auto
  have AD_sub: "act_edom \<phi> I \<subseteq> AD\<phi>" "act_edom \<psi> I \<subseteq> AD\<psi>"
    by (auto simp: ts_def(3,4))

  obtain AD n X where AD_X_def:
    "eval_disj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi> = (AD, n, X)"
    by (cases "eval_disj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>") auto
  have AD_def: "AD = act_edom (Disj \<phi> \<psi>) I" "act_edom (Disj \<phi> \<psi>) I \<subseteq> AD"
    "AD\<phi> \<subseteq> AD" "AD\<psi> \<subseteq> AD" "AD = AD\<phi> \<union> AD\<psi>"
    using AD_X_def
    by (auto simp: ts_def Let_def)
  have n_def: "n = nfv (Disj \<phi> \<psi>)"
    using AD_X_def
    by (auto simp: ts_def Let_def nfv_card fv_fo_fmla_list_set)

  define S\<phi> where "S\<phi> \<equiv> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
  define S\<psi> where "S\<psi> \<equiv> {\<sigma>. esat \<psi> I \<sigma> UNIV}"
  define ns\<phi>' where "ns\<phi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<phi>) (fv_fo_fmla_list \<psi>)"
  define ns\<psi>' where "ns\<psi>' = filter (\<lambda>n. n \<notin> fv_fo_fmla \<psi>) (fv_fo_fmla_list \<phi>)"

  note X\<phi>_def = fo_wf_X[OF wf(1)[unfolded ts_def(1)], unfolded proj_fmla_def, folded S\<phi>_def]
  note X\<psi>_def = fo_wf_X[OF wf(2)[unfolded ts_def(2)], unfolded proj_fmla_def, folded S\<psi>_def]
  have fv_sub: "fv_fo_fmla (Disj \<phi> \<psi>) = fv_fo_fmla \<phi> \<union> set (fv_fo_fmla_list \<psi>)"
    "fv_fo_fmla (Disj \<phi> \<psi>) = fv_fo_fmla \<psi> \<union> set (fv_fo_fmla_list \<phi>)"
    by (auto simp: fv_fo_fmla_list_set)
  note res_left_alt = ext_tuple_ad_agr_close[OF S\<phi>_def AD_sub(1) AD_def(3)
       X\<phi>_def(1)[folded S\<phi>_def] ns\<phi>'_def sorted_distinct_fv_list fv_sub(1)]
  note res_right_alt = ext_tuple_ad_agr_close[OF S\<psi>_def AD_sub(2) AD_def(4)
       X\<psi>_def(1)[folded S\<psi>_def] ns\<psi>'_def sorted_distinct_fv_list fv_sub(2)]

  have "X = fo_nmlz AD ` proj_fmla (Disj \<phi> \<psi>) {\<sigma>. esat \<phi> I \<sigma> UNIV} \<union>
     fo_nmlz AD ` proj_fmla (Disj \<phi> \<psi>) {\<sigma>. esat \<psi> I \<sigma> UNIV}"
    using AD_X_def
    apply (simp add: ts_def(1,2) Let_def AD_def(5)[symmetric])
    unfolding fv_fo_fmla_list_set proj_fmla_def ns\<phi>'_def[symmetric] ns\<psi>'_def[symmetric]
      S\<phi>_def[symmetric] S\<psi>_def[symmetric]
    using res_left_alt(1) res_right_alt(1)
    by auto
  then have eval: "eval_disj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi> =
    eval_abs (Disj \<phi> \<psi>) I"
    unfolding AD_X_def AD_def(1)[symmetric] n_def eval_abs_def
    by (auto simp: proj_fmla_map)
  have wf_disj: "wf_fo_intp (Disj \<phi> \<psi>) I"
    using wf
    by (auto simp: ts_def)
  show ?thesis
    using fo_wf_eval_abs[OF wf_disj]
    by (auto simp: eval)
qed

lemma fv_ex_all:
  assumes "pos i (fv_fo_fmla_list \<phi>) = None"
  shows "fv_fo_fmla_list (Exists i \<phi>) = fv_fo_fmla_list \<phi>"
    "fv_fo_fmla_list (Forall i \<phi>) = fv_fo_fmla_list \<phi>"
  using pos_complete[of i "fv_fo_fmla_list \<phi>"] fv_fo_fmla_list_eq[of "Exists i \<phi>" \<phi>]
    fv_fo_fmla_list_eq[of "Forall i \<phi>" \<phi>] assms
  by (auto simp: fv_fo_fmla_list_set)

lemma nfv_ex_all:
  assumes Some: "pos i (fv_fo_fmla_list \<phi>) = Some j"
  shows "nfv \<phi> = Suc (nfv (Exists i \<phi>))" "nfv \<phi> = Suc (nfv (Forall i \<phi>))"
proof -
  have "i \<in> fv_fo_fmla \<phi>" "j < nfv \<phi>" "i \<in> set (fv_fo_fmla_list \<phi>)"
    using fv_fo_fmla_list_set pos_set[of i "fv_fo_fmla_list \<phi>"]
      pos_length[of i "fv_fo_fmla_list \<phi>"] Some
    by (fastforce simp: nfv_def)+
  then show "nfv \<phi> = Suc (nfv (Exists i \<phi>))" "nfv \<phi> = Suc (nfv (Forall i \<phi>))"
    using nfv_card[of \<phi>] nfv_card[of "Exists i \<phi>"] nfv_card[of "Forall i \<phi>"]
    by (auto simp: finite_fv_fo_fmla)
qed

lemma fv_fo_fmla_list_exists: "fv_fo_fmla_list (Exists n \<phi>) = filter ((\<noteq>) n) (fv_fo_fmla_list \<phi>)"
  by (auto simp: fv_fo_fmla_list_def)
     (metis (mono_tags, lifting) distinct_filter distinct_remdups_adj_sort
      distinct_remdups_id filter_set filter_sort remdups_adj_set sorted_list_of_set_sort_remdups
      sorted_remdups_adj sorted_sort sorted_sort_id)

lemma eval_exists:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes wf: "fo_wf \<phi> I t"
  shows "fo_wf (Exists i \<phi>) I (eval_exists i (fv_fo_fmla_list \<phi>) t)"
proof -
  obtain AD n X where t_def: "t = (AD, n, X)"
    "AD = act_edom \<phi> I" "AD = act_edom (Exists i \<phi>) I"
    using assms
    by (cases t) auto
  note X_def = fo_wf_X[OF wf[unfolded t_def], folded t_def(2)]
  have eval: "eval_exists i (fv_fo_fmla_list \<phi>) t = eval_abs (Exists i \<phi>) I"
  proof (cases "pos i (fv_fo_fmla_list \<phi>)")
    case None
    note fv_eq = fv_ex_all[OF None]
    have "X = fo_nmlz AD ` proj_fmla (Exists i \<phi>) {\<sigma>. esat \<phi> I \<sigma> UNIV}"
      unfolding X_def
      by (auto simp: proj_fmla_def fv_eq)
    also have "\<dots> = fo_nmlz AD ` proj_fmla (Exists i \<phi>) {\<sigma>. esat (Exists i \<phi>) I \<sigma> UNIV}"
      using esat_exists_not_fv[of i \<phi> UNIV I] pos_complete[OF None]
      by (simp add: fv_fo_fmla_list_set)
    finally show ?thesis
      by (auto simp: t_def None eval_abs_def fv_eq nfv_def)
  next
    case (Some j)
    have "fo_nmlz AD ` rem_nth j ` X =
      fo_nmlz AD ` proj_fmla (Exists i \<phi>) {\<sigma>. esat (Exists i \<phi>) I \<sigma> UNIV}"
    proof (rule set_eqI, rule iffI)
      fix vs
      assume "vs \<in> fo_nmlz AD ` rem_nth j ` X"
      then obtain ws where ws_def: "ws \<in> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
        "vs = fo_nmlz AD (rem_nth j ws)"
        unfolding X_def
        by auto
      then obtain \<sigma> where \<sigma>_def: "esat \<phi> I \<sigma> UNIV"
        "ws = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list \<phi>))"
        by (auto simp: proj_fmla_map)
      obtain \<tau> where \<tau>_def: "ws = map \<tau> (fv_fo_fmla_list \<phi>)"
        using fo_nmlz_map \<sigma>_def(2)
        by blast
      have esat_\<tau>: "esat (Exists i \<phi>) I \<tau> UNIV"
        using esat_UNIV_ad_agr_list[OF fo_nmlz_ad_agr[of AD "map \<sigma> (fv_fo_fmla_list \<phi>)",
              folded \<sigma>_def(2), unfolded \<tau>_def]] \<sigma>_def(1)
        by (auto simp: t_def intro!: exI[of _ "\<tau> i"])
      have rem_nth_ws: "rem_nth j ws = map \<tau> (fv_fo_fmla_list (Exists i \<phi>))"
        using rem_nth_sound[of "fv_fo_fmla_list \<phi>" i j \<tau>] sorted_distinct_fv_list Some
        unfolding fv_fo_fmla_list_exists \<tau>_def
        by auto
      have "vs \<in> fo_nmlz AD ` proj_fmla (Exists i \<phi>) {\<sigma>. esat (Exists i \<phi>) I \<sigma> UNIV}"
        using ws_def(2) esat_\<tau>
        unfolding rem_nth_ws
        by (auto simp: proj_fmla_map)
      then show "vs \<in> fo_nmlz AD ` proj_fmla (Exists i \<phi>) {\<sigma>. esat (Exists i \<phi>) I \<sigma> UNIV}"
        by auto
    next
      fix vs
      assume assm: "vs \<in> fo_nmlz AD ` proj_fmla (Exists i \<phi>) {\<sigma>. esat (Exists i \<phi>) I \<sigma> UNIV}"
      from assm obtain \<sigma> where \<sigma>_def: "vs = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list (Exists i \<phi>)))"
        "esat (Exists i \<phi>) I \<sigma> UNIV"
        by (auto simp: proj_fmla_map)
      then obtain x where x_def: "esat \<phi> I (\<sigma>(i := x)) UNIV"
        by auto
      define ws where "ws \<equiv> fo_nmlz AD (map (\<sigma>(i := x)) (fv_fo_fmla_list \<phi>))"
      then have "length ws = nfv \<phi>"
        using nfv_def fo_nmlz_length by (metis length_map)
      then have ws_in: "ws \<in> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
        using x_def ws_def
        by (auto simp: fo_nmlz_sound proj_fmla_map)
      obtain \<tau> where \<tau>_def: "ws = map \<tau> (fv_fo_fmla_list \<phi>)"
        using fo_nmlz_map ws_def
        by blast
      have rem_nth_ws: "rem_nth j ws = map \<tau> (fv_fo_fmla_list (Exists i \<phi>))"
        using rem_nth_sound[of "fv_fo_fmla_list \<phi>" i j] sorted_distinct_fv_list Some
        unfolding fv_fo_fmla_list_exists \<tau>_def
        by auto
      have "set (fv_fo_fmla_list (Exists i \<phi>)) \<subseteq> set (fv_fo_fmla_list \<phi>)"
        by (auto simp: fv_fo_fmla_list_exists)
      then have ad_agr: "ad_agr_list AD (map (\<sigma>(i := x)) (fv_fo_fmla_list (Exists i \<phi>)))
        (map \<tau> (fv_fo_fmla_list (Exists i \<phi>)))"
        by (rule ad_agr_list_subset)
          (rule fo_nmlz_ad_agr[of AD "map (\<sigma>(i := x)) (fv_fo_fmla_list \<phi>)", folded ws_def,
              unfolded \<tau>_def])
      have map_fv_cong: "map (\<sigma>(i := x)) (fv_fo_fmla_list (Exists i \<phi>)) =
        map \<sigma> (fv_fo_fmla_list (Exists i \<phi>))"
        by (auto simp: fv_fo_fmla_list_exists)
      have vs_rem_nth: "vs = fo_nmlz AD (rem_nth j ws)"
        unfolding \<sigma>_def(1) rem_nth_ws
        apply (rule fo_nmlz_eqI)
        using ad_agr[unfolded map_fv_cong] .
      show "vs \<in> fo_nmlz AD ` rem_nth j ` X"
        using Some ws_in
        unfolding vs_rem_nth X_def
        by auto
    qed
    then show ?thesis
      using nfv_ex_all[OF Some]
      by (auto simp: t_def Some eval_abs_def nfv_def)
  qed
  have wf_ex: "wf_fo_intp (Exists i \<phi>) I"
    using wf
    by (auto simp: t_def)
  show ?thesis
    using fo_wf_eval_abs[OF wf_ex]
    by (auto simp: eval)
qed

lemma fv_fo_fmla_list_forall: "fv_fo_fmla_list (Forall n \<phi>) = filter ((\<noteq>) n) (fv_fo_fmla_list \<phi>)"
  by (auto simp: fv_fo_fmla_list_def)
     (metis (mono_tags, lifting) distinct_filter distinct_remdups_adj_sort
      distinct_remdups_id filter_set filter_sort remdups_adj_set sorted_list_of_set_sort_remdups
      sorted_remdups_adj sorted_sort sorted_sort_id)

lemma pairwise_take_drop:
  assumes "pairwise P (set (zip xs ys))" "length xs = length ys"
  shows "pairwise P (set (zip (take i xs @ drop (Suc i) xs) (take i ys @ drop (Suc i) ys)))"
  by (rule pairwise_subset[OF assms(1)]) (auto simp: set_zip assms(2))

lemma fo_nmlz_set_card:
  "fo_nmlz AD xs = xs \<Longrightarrow> set xs = set xs \<inter> Inl ` AD \<union> Inr ` {..<card (Inr -` set xs)}"
  by (metis fo_nmlz_sound fo_nmlzd_set card_Inr_vimage_le_length min.absorb2)

lemma ad_agr_list_take_drop: "ad_agr_list AD xs ys \<Longrightarrow>
  ad_agr_list AD (take i xs @ drop (Suc i) xs) (take i ys @ drop (Suc i) ys)"
  apply (auto simp: ad_agr_list_def ad_equiv_list_def sp_equiv_list_def)
    apply (metis take_zip in_set_takeD)
   apply (metis drop_zip in_set_dropD)
  using pairwise_take_drop
  by fastforce

lemma fo_nmlz_rem_nth_add_nth:
  assumes "fo_nmlz AD zs = zs" "i \<le> length zs"
  shows "fo_nmlz AD (rem_nth i (fo_nmlz AD (add_nth i z zs))) = zs"
proof -
  have ad_agr: "ad_agr_list AD (add_nth i z zs) (fo_nmlz AD (add_nth i z zs))"
    using fo_nmlz_ad_agr
    by auto
  have i_lt_add: "i < length (add_nth i z zs)" "i < length (fo_nmlz AD (add_nth i z zs))"
    using add_nth_length assms(2)
    by (fastforce simp: fo_nmlz_length)+
  show ?thesis
    using ad_agr_list_take_drop[OF ad_agr, of i, folded rem_nth_take_drop[OF i_lt_add(1)]
        rem_nth_take_drop[OF i_lt_add(2)], unfolded rem_nth_add_nth[OF assms(2)]]
    apply (subst eq_commute)
    apply (subst assms(1)[symmetric])
    apply (auto intro: fo_nmlz_eqI)
    done
qed

lemma ad_agr_list_add:
  assumes "ad_agr_list AD xs ys" "i \<le> length xs"
  shows "\<exists>z' \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set ys))} \<union> set ys.
    ad_agr_list AD (take i xs @ z # drop i xs) (take i ys @ z' # drop i ys)"
proof -
  define n where "n = length xs"
  have len_ys: "n = length ys"
    using assms(1)
    by (auto simp: ad_agr_list_def n_def)
  obtain \<sigma> where \<sigma>_def: "xs = map \<sigma> [0..<n]"
    unfolding n_def
    by (metis map_nth)
  obtain \<tau> where \<tau>_def: "ys = map \<tau> [0..<n]"
    unfolding len_ys
    by (metis map_nth)
  have i_le_n: "i \<le> n"
    using assms(2)
    by (auto simp: n_def)
  have set_n: "set [0..<n] = {..n} - {n}" "set ([0..<i] @ n # [i..<n]) = {..n}"
    using i_le_n
    by auto
  have ad_agr: "ad_agr_sets ({..n} - {n}) ({..n} - {n}) AD \<sigma> \<tau>"
    using iffD2[OF ad_agr_list_link, OF assms(1)[unfolded \<sigma>_def \<tau>_def]]
    unfolding set_n .
  have set_ys: "\<tau> ` ({..n} - {n}) = set ys"
    by (auto simp: \<tau>_def)
  obtain z' where z'_def: "z' \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set ys))} \<union> set ys"
    "ad_agr_sets {..n} {..n} AD (\<sigma>(n := z)) (\<tau>(n := z'))"
    using extend_\<tau>[OF ad_agr subset_refl,
        of "Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set ys))} \<union> set ys" z]
    by (auto simp: set_ys)
  have map_take: "map (\<sigma>(n := z)) ([0..<i] @ n # [i..<n]) = take i xs @ z # drop i xs"
    "map (\<tau>(n := z')) ([0..<i] @ n # [i..<n]) = take i ys @ z' # drop i ys"
    using i_le_n
    by (auto simp: \<sigma>_def \<tau>_def take_map drop_map)
  show ?thesis
    using iffD1[OF ad_agr_list_link, OF z'_def(2)[unfolded set_n[symmetric]]] z'_def(1)
    unfolding map_take
    by auto
qed

lemma add_nth_restrict:
  assumes "fo_nmlz AD zs = zs" "i \<le> length zs"
  shows "\<exists>z' \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}.
    fo_nmlz AD (add_nth i z zs) = fo_nmlz AD (add_nth i z' zs)"
proof -
  have "set zs \<subseteq> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}"
    using fo_nmlz_set_card[OF assms(1)]
    by auto
  then obtain z' where z'_def:
    "z' \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}"
    "ad_agr_list AD (take i zs @ z # drop i zs) (take i zs @ z' # drop i zs)"
    using ad_agr_list_add[OF ad_agr_list_refl assms(2), of AD z]
    by auto blast
  then show ?thesis
    unfolding add_nth_take_drop[OF assms(2)]
    by (auto intro: fo_nmlz_eqI)
qed

lemma fo_nmlz_add_rem:
  assumes "i \<le> length zs"
  shows "\<exists>z'. fo_nmlz AD (add_nth i z zs) = fo_nmlz AD (add_nth i z' (fo_nmlz AD zs))"
proof -
  have ad_agr: "ad_agr_list AD zs (fo_nmlz AD zs)"
    using fo_nmlz_ad_agr
    by auto
  have i_le_fo_nmlz: "i \<le> length (fo_nmlz AD zs)"
    using assms(1)
    by (auto simp: fo_nmlz_length)
  obtain x where x_def: "ad_agr_list AD (add_nth i z zs) (add_nth i x (fo_nmlz AD zs))"
    using ad_agr_list_add[OF ad_agr assms(1)]
    by (auto simp: add_nth_take_drop[OF assms(1)] add_nth_take_drop[OF i_le_fo_nmlz])
  then show ?thesis
    using fo_nmlz_eqI
    by auto
qed

lemma fo_nmlz_add_rem':
  assumes "i \<le> length zs"
  shows "\<exists>z'. fo_nmlz AD (add_nth i z (fo_nmlz AD zs)) = fo_nmlz AD (add_nth i z' zs)"
proof -
  have ad_agr: "ad_agr_list AD (fo_nmlz AD zs) zs"
    using ad_agr_list_comm[OF fo_nmlz_ad_agr]
    by auto
  have i_le_fo_nmlz: "i \<le> length (fo_nmlz AD zs)"
    using assms(1)
    by (auto simp: fo_nmlz_length)
  obtain x where x_def: "ad_agr_list AD (add_nth i z (fo_nmlz AD zs)) (add_nth i x zs)"
    using ad_agr_list_add[OF ad_agr i_le_fo_nmlz]
    by (auto simp: add_nth_take_drop[OF assms(1)] add_nth_take_drop[OF i_le_fo_nmlz])
  then show ?thesis
    using fo_nmlz_eqI
    by auto
qed

lemma fo_nmlz_add_nth_rem_nth:
  assumes "fo_nmlz AD xs = xs" "i < length xs"
  shows "\<exists>z. fo_nmlz AD (add_nth i z (fo_nmlz AD (rem_nth i xs))) = xs"
  using rem_nth_length[OF assms(2)] fo_nmlz_add_rem[of i "rem_nth i xs" AD "xs ! i",
      unfolded assms(1) add_nth_rem_nth_self[OF assms(2)]] assms(2)
  by (subst eq_commute) auto

lemma sp_equiv_list_almost_same: "sp_equiv_list (xs @ v # ys) (xs @ w # ys) \<Longrightarrow>
  v \<in> set xs \<union> set ys \<or> w \<in> set xs \<union> set ys \<Longrightarrow> v = w"
  by (auto simp: sp_equiv_list_def pairwise_def) (metis UnCI sp_equiv_pair.simps zip_same)+

lemma ad_agr_list_add_nth:
  assumes "i \<le> length zs" "ad_agr_list AD (add_nth i v zs) (add_nth i w zs)" "v \<noteq> w"
  shows "{v, w} \<inter> (Inl ` AD \<union> set zs) = {}"
  using assms(2)[unfolded add_nth_take_drop[OF assms(1)]] assms(1,3) sp_equiv_list_almost_same
  by (auto simp: ad_agr_list_def ad_equiv_list_def ad_equiv_pair.simps)
     (smt append_take_drop_id set_append sp_equiv_list_almost_same)+

lemma Inr_in_tuple:
  assumes "fo_nmlz AD zs = zs" "n < card (Inr -` set zs)"
  shows "Inr n \<in> set zs"
  using assms fo_nmlz_set_card[OF assms(1)]
  by (auto simp: fo_nmlzd_code[symmetric])

lemma card_wit_sub:
  assumes "finite Z" "card Z \<le> card {ts \<in> X. \<exists>z \<in> Z. ts = f z}"
  shows "f ` Z \<subseteq> X"
proof -
  have set_unfold: "{ts \<in> X. \<exists>z \<in> Z. ts = f z} = f ` Z \<inter> X"
    by auto
  show ?thesis
    using assms
    unfolding set_unfold
    by (metis Int_lower1 card_image_le card_seteq finite_imageI inf.absorb_iff1 le_antisym
        surj_card_le)
qed

lemma add_nth_iff_card:
  assumes "(\<And>xs. xs \<in> X \<Longrightarrow> fo_nmlz AD xs = xs)" "(\<And>xs. xs \<in> X \<Longrightarrow> i < length xs)"
    "fo_nmlz AD zs = zs" "i \<le> length zs" "finite AD" "finite X"
  shows "(\<forall>z. fo_nmlz AD (add_nth i z zs) \<in> X) \<longleftrightarrow>
    Suc (card AD + card (Inr -` set zs)) \<le> card {ts \<in> X. \<exists>z. ts = fo_nmlz AD (add_nth i z zs)}"
proof -
  have inj: "inj_on (\<lambda>z. fo_nmlz AD (add_nth i z zs))
    (Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))})"
    using ad_agr_list_add_nth[OF assms(4)] Inr_in_tuple[OF assms(3)] less_Suc_eq
    by (fastforce simp: inj_on_def dest!: fo_nmlz_eqD)
  have card_Un: "card (Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}) =
      Suc (card AD + card (Inr -` set zs))"
    using card_Un_disjoint[of "Inl ` AD" "Inr ` {..<Suc (card (Inr -` set zs))}"] assms(5)
    by (auto simp add: card_image disjoint_iff_not_equal)
  have restrict_z: "(\<forall>z. fo_nmlz AD (add_nth i z zs) \<in> X) \<longleftrightarrow>
    (\<forall>z \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}. fo_nmlz AD (add_nth i z zs) \<in> X)"
    using add_nth_restrict[OF assms(3,4)]
    by metis
  have restrict_z': "{ts \<in> X. \<exists>z. ts = fo_nmlz AD (add_nth i z zs)} =
    {ts \<in> X. \<exists>z \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}.
      ts = fo_nmlz AD (add_nth i z zs)}"
    using add_nth_restrict[OF assms(3,4)]
    by auto
  {
    assume "\<And>z. fo_nmlz AD (add_nth i z zs) \<in> X"
    then have image_sub: "(\<lambda>z. fo_nmlz AD (add_nth i z zs)) `
      (Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}) \<subseteq>
      {ts \<in> X. \<exists>z. ts = fo_nmlz AD (add_nth i z zs)}"
      by auto
    have "Suc (card AD + card (Inr -` set zs)) \<le>
      card {ts \<in> X. \<exists>z. ts = fo_nmlz AD (add_nth i z zs)}"
      unfolding card_Un[symmetric]
      using card_inj_on_le[OF inj image_sub] assms(6)
      by auto
    then have "Suc (card AD + card (Inr -` set zs)) \<le>
      card {ts \<in> X. \<exists>z. ts = fo_nmlz AD (add_nth i z zs)}"
      by (auto simp: card_image)
  }
  moreover
  {
    assume assm: "card (Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}) \<le>
      card {ts \<in> X. \<exists>z \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}.
        ts = fo_nmlz AD (add_nth i z zs)}"
    have "\<forall>z \<in> Inl ` AD \<union> Inr ` {..<Suc (card (Inr -` set zs))}. fo_nmlz AD (add_nth i z zs) \<in> X"
      using card_wit_sub[OF _ assm] assms(5)
      by auto
  }
  ultimately show ?thesis
    unfolding restrict_z[symmetric] restrict_z'[symmetric] card_Un
    by auto
qed

lemma set_fo_nmlz_add_nth_rem_nth:
  assumes "j < length xs" "\<And>x. x \<in> X \<Longrightarrow> fo_nmlz AD x = x"
    "\<And>x. x \<in> X \<Longrightarrow> j < length x"
  shows "{ts \<in> X. \<exists>z. ts = fo_nmlz AD (add_nth j z (fo_nmlz AD (rem_nth j xs)))} =
  {y \<in> X. fo_nmlz AD (rem_nth j y) = fo_nmlz AD (rem_nth j xs)}"
  using fo_nmlz_rem_nth_add_nth[where ?zs="fo_nmlz AD (rem_nth j xs)"] rem_nth_length[OF assms(1)] fo_nmlz_add_nth_rem_nth assms
  by (fastforce simp: fo_nmlz_idem[OF fo_nmlz_sound] fo_nmlz_length)

lemma eval_forall:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes wf: "fo_wf \<phi> I t"
  shows "fo_wf (Forall i \<phi>) I (eval_forall i (fv_fo_fmla_list \<phi>) t)"
proof -
  obtain AD n X where t_def: "t = (AD, n, X)" "AD = act_edom \<phi> I"
    "AD = act_edom (Forall i \<phi>) I"
    using assms
    by (cases t) auto
  have AD_sub: "act_edom \<phi> I \<subseteq> AD"
    by (auto simp: t_def(2))
  have fin_AD: "finite AD"
    using finite_act_edom wf
    by (auto simp: t_def)
  have fin_X: "finite X"
    using wf
    by (auto simp: t_def)
  note X_def = fo_wf_X[OF wf[unfolded t_def], folded t_def(2)]
  have eval: "eval_forall i (fv_fo_fmla_list \<phi>) t = eval_abs (Forall i \<phi>) I"
  proof (cases "pos i (fv_fo_fmla_list \<phi>)")
    case None
    note fv_eq = fv_ex_all[OF None]
    have "X = fo_nmlz AD ` proj_fmla (Forall i \<phi>) {\<sigma>. esat \<phi> I \<sigma> UNIV}"
      unfolding X_def
      by (auto simp: proj_fmla_def fv_eq)
    also have "\<dots> = fo_nmlz AD ` proj_fmla (Forall i \<phi>) {\<sigma>. esat (Forall i \<phi>) I \<sigma> UNIV}"
      using esat_forall_not_fv[of i \<phi> UNIV I] pos_complete[OF None]
      by (auto simp: fv_fo_fmla_list_set)
    finally show ?thesis
      by (auto simp: t_def None eval_abs_def fv_eq nfv_def)
  next
    case (Some j)
    have i_in_fv: "i \<in> fv_fo_fmla \<phi>"
      by (rule pos_set[OF Some, unfolded fv_fo_fmla_list_set])
    have fo_nmlz_X: "\<And>xs. xs \<in> X \<Longrightarrow> fo_nmlz AD xs = xs"
      by (auto simp: X_def proj_fmla_map fo_nmlz_idem[OF fo_nmlz_sound])
    have j_lt_len: "\<And>xs. xs \<in> X \<Longrightarrow> j < length xs"
      using pos_sound[OF Some]
      by (auto simp: X_def proj_fmla_map fo_nmlz_length)
    have rem_nth_j_le_len: "\<And>xs. xs \<in> X \<Longrightarrow> j \<le> length (fo_nmlz AD (rem_nth j xs))"
      using rem_nth_length j_lt_len
      by (fastforce simp: fo_nmlz_length)
    have img_proj_fmla: "Mapping.keys (Mapping.filter (\<lambda>t Z. Suc (card AD + card (Inr -` set t)) \<le> card Z)
      (cluster (Some \<circ> (\<lambda>ts. fo_nmlz AD (rem_nth j ts))) X)) =
      fo_nmlz AD ` proj_fmla (Forall i \<phi>) {\<sigma>. esat (Forall i \<phi>) I \<sigma> UNIV}"
    proof (rule set_eqI, rule iffI)
      fix vs
      assume "vs \<in> Mapping.keys (Mapping.filter (\<lambda>t Z. Suc (card AD + card (Inr -` set t)) \<le> card Z)
        (cluster (Some \<circ> (\<lambda>ts. fo_nmlz AD (rem_nth j ts))) X))"
      then obtain ws where ws_def: "ws \<in> X" "vs = fo_nmlz AD (rem_nth j ws)"
        "\<And>a. fo_nmlz AD (add_nth j a (fo_nmlz AD (rem_nth j ws))) \<in> X"
        using add_nth_iff_card[OF fo_nmlz_X j_lt_len fo_nmlz_idem[OF fo_nmlz_sound]
            rem_nth_j_le_len fin_AD fin_X] set_fo_nmlz_add_nth_rem_nth[OF j_lt_len fo_nmlz_X j_lt_len]
        by transfer (fastforce split: option.splits if_splits)
      then obtain \<sigma> where \<sigma>_def:
        "esat \<phi> I \<sigma> UNIV" "ws = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list \<phi>))"
        unfolding X_def
        by (auto simp: proj_fmla_map)
      obtain \<tau> where \<tau>_def: "ws = map \<tau> (fv_fo_fmla_list \<phi>)"
        using fo_nmlz_map \<sigma>_def(2)
        by blast
      have fo_nmlzd_\<tau>: "fo_nmlzd AD (map \<tau> (fv_fo_fmla_list \<phi>))"
        unfolding \<tau>_def[symmetric] \<sigma>_def(2)
        by (rule fo_nmlz_sound)
      have rem_nth_j_ws: "rem_nth j ws = map \<tau> (filter ((\<noteq>) i) (fv_fo_fmla_list \<phi>))"
        using rem_nth_sound[OF _ Some] sorted_distinct_fv_list
        by (auto simp: \<tau>_def)
      have esat_\<tau>: "esat (Forall i \<phi>) I \<tau> UNIV"
        unfolding esat.simps
      proof (rule ballI)
        fix x
        have "fo_nmlz AD (add_nth j x (rem_nth j ws)) \<in> X"
          using fo_nmlz_add_rem[of j "rem_nth j ws" AD x] rem_nth_length
            j_lt_len[OF ws_def(1)] ws_def(3)
          by fastforce
        then have "fo_nmlz AD (map (\<tau>(i := x)) (fv_fo_fmla_list \<phi>)) \<in> X"
          using add_nth_rem_nth_map[OF _ Some, of x] sorted_distinct_fv_list
          unfolding \<tau>_def
          by fastforce
        then show "esat \<phi> I (\<tau>(i := x)) UNIV"
          by (auto simp: X_def proj_fmla_map esat_UNIV_ad_agr_list[OF _ AD_sub]
              dest!: fo_nmlz_eqD)
      qed
      have rem_nth_ws: "rem_nth j ws = map \<tau> (fv_fo_fmla_list (Forall i \<phi>))"
        using rem_nth_sound[OF _ Some] sorted_distinct_fv_list
        by (auto simp: fv_fo_fmla_list_forall \<tau>_def)
      then show "vs \<in> fo_nmlz AD ` proj_fmla (Forall i \<phi>) {\<sigma>. esat (Forall i \<phi>) I \<sigma> UNIV}"
        using ws_def(2) esat_\<tau>
        by (auto simp: proj_fmla_map rem_nth_ws)
    next
      fix vs
      assume assm: "vs \<in> fo_nmlz AD ` proj_fmla (Forall i \<phi>) {\<sigma>. esat (Forall i \<phi>) I \<sigma> UNIV}"
      from assm obtain \<sigma> where \<sigma>_def: "vs = fo_nmlz AD (map \<sigma> (fv_fo_fmla_list (Forall i \<phi>)))"
        "esat (Forall i \<phi>) I \<sigma> UNIV"
        by (auto simp: proj_fmla_map)
      then have all_esat: "\<And>x. esat \<phi> I (\<sigma>(i := x)) UNIV"
        by auto
      define ws where "ws \<equiv> fo_nmlz AD (map \<sigma> (fv_fo_fmla_list \<phi>))"
      then have "length ws = nfv \<phi>"
        using nfv_def fo_nmlz_length by (metis length_map)
      then have ws_in: "ws \<in> fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
        using all_esat[of "\<sigma> i"] ws_def
        by (auto simp: fo_nmlz_sound proj_fmla_map)
      then have ws_in_X: "ws \<in> X"
        by (auto simp: X_def)
      obtain \<tau> where \<tau>_def: "ws = map \<tau> (fv_fo_fmla_list \<phi>)"
        using fo_nmlz_map ws_def
        by blast
      have rem_nth_ws: "rem_nth j ws = map \<tau> (fv_fo_fmla_list (Forall i \<phi>))"
        using rem_nth_sound[of "fv_fo_fmla_list \<phi>" i j] sorted_distinct_fv_list Some
        unfolding fv_fo_fmla_list_forall \<tau>_def
        by auto
      have "set (fv_fo_fmla_list (Forall i \<phi>)) \<subseteq> set (fv_fo_fmla_list \<phi>)"
        by (auto simp: fv_fo_fmla_list_forall)
      then have ad_agr: "ad_agr_list AD (map \<sigma> (fv_fo_fmla_list (Forall i \<phi>)))
        (map \<tau> (fv_fo_fmla_list (Forall i \<phi>)))"
        apply (rule ad_agr_list_subset)
        using fo_nmlz_ad_agr[of AD] ws_def \<tau>_def
        by metis
      have map_fv_cong: "\<And>x. map (\<sigma>(i := x)) (fv_fo_fmla_list (Forall i \<phi>)) =
        map \<sigma> (fv_fo_fmla_list (Forall i \<phi>))"
        by (auto simp: fv_fo_fmla_list_forall)
      have vs_rem_nth: "vs = fo_nmlz AD (rem_nth j ws)"
        unfolding \<sigma>_def(1) rem_nth_ws
        apply (rule fo_nmlz_eqI)
        using ad_agr[unfolded map_fv_cong] .
      have "\<And>a. fo_nmlz AD (add_nth j a (fo_nmlz AD (rem_nth j ws))) \<in>
        fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
      proof -
        fix a
        obtain x where add_rem: "fo_nmlz AD (add_nth j a (fo_nmlz AD (rem_nth j ws))) =
          fo_nmlz AD (map (\<tau>(i := x)) (fv_fo_fmla_list \<phi>))"
          using add_nth_rem_nth_map[OF _ Some, of _ \<tau>] sorted_distinct_fv_list
            fo_nmlz_add_rem'[of j "rem_nth j ws"] rem_nth_length[of j ws]
            j_lt_len[OF ws_in_X]
          by (fastforce simp: \<tau>_def)
        have "esat (Forall i \<phi>) I \<tau> UNIV"
          apply (rule iffD1[OF esat_UNIV_ad_agr_list \<sigma>_def(2), OF _ subset_refl, folded t_def])
          using fo_nmlz_ad_agr[of AD "map \<sigma> (fv_fo_fmla_list \<phi>)", folded ws_def, unfolded \<tau>_def]
          unfolding ad_agr_list_link[symmetric]
          by (auto simp: fv_fo_fmla_list_set ad_agr_sets_def sp_equiv_def pairwise_def)
        then have "esat \<phi> I (\<tau>(i := x)) UNIV"
          by auto
        then show "fo_nmlz AD (add_nth j a (fo_nmlz AD (rem_nth j ws))) \<in>
          fo_nmlz AD ` proj_fmla \<phi> {\<sigma>. esat \<phi> I \<sigma> UNIV}"
          by (auto simp: add_rem proj_fmla_map)
      qed
      then show "vs \<in> Mapping.keys (Mapping.filter (\<lambda>t Z. Suc (card AD + card (Inr -` set t)) \<le> card Z)
        (cluster (Some \<circ> (\<lambda>ts. fo_nmlz AD (rem_nth j ts))) X))"
        unfolding vs_rem_nth X_def[symmetric]
        using add_nth_iff_card[OF fo_nmlz_X j_lt_len fo_nmlz_idem[OF fo_nmlz_sound]
            rem_nth_j_le_len fin_AD fin_X] set_fo_nmlz_add_nth_rem_nth[OF j_lt_len fo_nmlz_X j_lt_len] ws_in_X
        by transfer (fastforce split: option.splits if_splits)
    qed
    show ?thesis
      using nfv_ex_all[OF Some]
      by (simp add: t_def Some eval_abs_def nfv_def img_proj_fmla[unfolded t_def(2)]
          split: option.splits)
  qed
  have wf_all: "wf_fo_intp (Forall i \<phi>) I"
    using wf
    by (auto simp: t_def)
  show ?thesis
    using fo_wf_eval_abs[OF wf_all]
    by (auto simp: eval)
qed

fun fo_res :: "('a, nat) fo_t \<Rightarrow> 'a eval_res" where
  "fo_res (AD, n, X) = (if fo_fin (AD, n, X) then Fin (map projl ` X) else Infin)"

lemma fo_res_fin:
  fixes t :: "('a :: infinite, nat) fo_t"
  assumes "fo_wf \<phi> I t" "finite (fo_rep t)"
  shows "fo_res t = Fin (fo_rep t)"
proof -
  obtain AD n X where t_def: "t = (AD, n, X)"
    using assms(1)
    by (cases t) auto
  show ?thesis
    using fo_fin assms
    by (fastforce simp only: t_def fo_res.simps fo_rep_fin split: if_splits)
qed

lemma fo_res_infin:
  fixes t :: "('a :: infinite, nat) fo_t"
  assumes "fo_wf \<phi> I t" "\<not>finite (fo_rep t)"
  shows "fo_res t = Infin"
proof -
  obtain AD n X where t_def: "t = (AD, n, X)"
    using assms(1)
    by (cases t) auto
  show ?thesis
    using fo_fin assms
    by (fastforce simp only: t_def fo_res.simps split: if_splits)
qed

lemma fo_rep: "fo_wf \<phi> I t \<Longrightarrow> fo_rep t = proj_sat \<phi> I"
  by (cases t) auto

global_interpretation Ailamazyan: eval_fo fo_wf eval_pred fo_rep fo_res
  eval_bool eval_eq eval_neg eval_conj eval_ajoin eval_disj
  eval_exists eval_forall
  defines eval_fmla = Ailamazyan.eval_fmla
      and eval = Ailamazyan.eval
  apply standard
             apply (rule fo_rep, assumption+)
            apply (rule fo_res_fin, assumption+)
           apply (rule fo_res_infin, assumption+)
          apply (rule eval_pred, assumption+)
         apply (rule eval_bool)
        apply (rule eval_eq)
       apply (rule eval_neg, assumption+)
      apply (rule eval_conj, assumption+)
     apply (rule eval_ajoin, assumption+)
    apply (rule eval_disj, assumption+)
   apply (rule eval_exists, assumption+)
  apply (rule eval_forall, assumption+)
  done

definition esat_UNIV :: "('a :: infinite, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> ('a + nat) val \<Rightarrow> bool" where
  "esat_UNIV \<phi> I \<sigma> = esat \<phi> I \<sigma> UNIV"

lemma esat_UNIV_code[code]: "esat_UNIV \<phi> I \<sigma> \<longleftrightarrow> (if wf_fo_intp \<phi> I then
  (case eval_fmla \<phi> I of (AD, n, X) \<Rightarrow>
    fo_nmlz (act_edom \<phi> I) (map \<sigma> (fv_fo_fmla_list \<phi>)) \<in> X)
  else esat_UNIV \<phi> I \<sigma>)"
proof -
  obtain AD n T where t_def: "Ailamazyan.eval_fmla \<phi> I = (AD, n, T)"
    by (cases "Ailamazyan.eval_fmla \<phi> I") auto
  {
    assume wf_fo_intp: "wf_fo_intp \<phi> I"
    note fo_wf = Ailamazyan.eval_fmla_correct[OF wf_fo_intp, unfolded t_def]
    note T_def = fo_wf_X[OF fo_wf]
    have AD_def: "AD = act_edom \<phi> I"
      using fo_wf
      by auto
    have "esat_UNIV \<phi> I \<sigma> \<longleftrightarrow>
      fo_nmlz (act_edom \<phi> I) (map \<sigma> (fv_fo_fmla_list \<phi>)) \<in> T"
      using esat_UNIV_ad_agr_list[OF _ subset_refl]
      by (force simp add: esat_UNIV_def T_def AD_def proj_fmla_map
          dest!: fo_nmlz_eqD)
  }
  then show ?thesis
    by (auto simp: t_def)
qed

lemma sat_code[code]:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  shows "sat \<phi> I \<sigma> \<longleftrightarrow> (if wf_fo_intp \<phi> I then
  (case eval_fmla \<phi> I of (AD, n, X) \<Rightarrow>
    fo_nmlz (act_edom \<phi> I) (map (Inl \<circ> \<sigma>) (fv_fo_fmla_list \<phi>)) \<in> X)
  else sat \<phi> I \<sigma>)"
  using esat_UNIV_code sat_esat_conv[folded esat_UNIV_def]
  by metis

end
