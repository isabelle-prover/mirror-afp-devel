theory Cluster
  imports Mapping_Code
begin

lemma these_Un[simp]: "Option.these (A \<union> B) = Option.these A \<union> Option.these B"
  by (auto simp: Option.these_def)

lemma these_insert[simp]: "Option.these (insert x A) = (case x of Some a \<Rightarrow> insert a | None \<Rightarrow> id) (Option.these A)"
  by (auto simp: Option.these_def split: option.splits) force

lemma these_image_Un[simp]: "Option.these (f ` (A \<union> B)) = Option.these (f ` A) \<union> Option.these (f ` B)"
  by (auto simp: Option.these_def)

lemma these_imageI: "f x = Some y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Option.these (f ` X)"
  by (force simp: Option.these_def)

lift_definition cluster :: "('b \<Rightarrow> 'a option) \<Rightarrow> 'b set \<Rightarrow> ('a, 'b set) mapping" is
  "\<lambda>f Y x. if Some x \<in> f ` Y then Some {y \<in> Y. f y = Some x} else None" .

lemma set_of_idx_cluster: "set_of_idx (cluster (Some \<circ> f) X) = X"
  by transfer (auto simp: ran_def)

lemma lookup_cluster': "Mapping.lookup (cluster (Some \<circ> h) X) y = (if y \<notin> h ` X then None else Some {x \<in> X. h x = y})"
  by transfer auto

context ord
begin

definition add_to_rbt :: "'a \<times> 'b \<Rightarrow> ('a, 'b set) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "add_to_rbt = (\<lambda>(a, b) t. case rbt_lookup t a of Some X \<Rightarrow> rbt_insert a (insert b X) t | None \<Rightarrow> rbt_insert a {b} t)"

abbreviation "add_option_to_rbt f \<equiv> (\<lambda>b _ t. case f b of Some a \<Rightarrow> add_to_rbt (a, b) t | None \<Rightarrow> t)"

definition cluster_rbt :: "('b \<Rightarrow> 'a option) \<Rightarrow> ('b, unit) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "cluster_rbt f t = RBT_Impl.fold (add_option_to_rbt f) t RBT_Impl.Empty"

end

context linorder
begin

lemma is_rbt_add_to_rbt: "is_rbt t \<Longrightarrow> is_rbt (add_to_rbt ab t)"
  by (auto simp: add_to_rbt_def split: prod.splits option.splits)

lemma is_rbt_fold_add_to_rbt: "is_rbt t' \<Longrightarrow>
  is_rbt (RBT_Impl.fold (add_option_to_rbt f) t t')"
  by (induction t arbitrary: t') (auto 0 0 simp: is_rbt_add_to_rbt split: option.splits)

lemma is_rbt_cluster_rbt: "is_rbt (cluster_rbt f t)"
  using is_rbt_fold_add_to_rbt Empty_is_rbt
  by (fastforce simp: cluster_rbt_def)

lemma rbt_insert_entries_None: "is_rbt t \<Longrightarrow> rbt_lookup t k = None \<Longrightarrow>
  set (RBT_Impl.entries (rbt_insert k v t)) = insert (k, v) (set (RBT_Impl.entries t))"
  by (auto simp: rbt_lookup_in_tree[symmetric] rbt_lookup_rbt_insert split: if_splits)

lemma rbt_insert_entries_Some: "is_rbt t \<Longrightarrow> rbt_lookup t k = Some v' \<Longrightarrow>
  set (RBT_Impl.entries (rbt_insert k v t)) = insert (k, v) (set (RBT_Impl.entries t) - {(k, v')})"
  by (auto simp: rbt_lookup_in_tree[symmetric] rbt_lookup_rbt_insert split: if_splits)

lemma keys_add_to_rbt: "is_rbt t \<Longrightarrow> set (RBT_Impl.keys (add_to_rbt (a, b) t)) = insert a (set (RBT_Impl.keys t))"
  by (auto simp: add_to_rbt_def RBT_Impl.keys_def rbt_insert_entries_None rbt_insert_entries_Some split: option.splits)

lemma keys_fold_add_to_rbt: "is_rbt t' \<Longrightarrow> set (RBT_Impl.keys (RBT_Impl.fold (add_option_to_rbt f) t t')) =
  Option.these (f ` set (RBT_Impl.keys t)) \<union> set (RBT_Impl.keys t')"
proof (induction t arbitrary: t')
  case (Branch col t1 k v t2)
  have valid: "is_rbt (RBT_Impl.fold (add_option_to_rbt f) t1 t')"
    using Branch(3)
    by (auto intro: is_rbt_fold_add_to_rbt)
  show ?case
  proof (cases "f k")
    case None
    show ?thesis
      by (auto simp: None Branch(2)[OF valid] Branch(1)[OF Branch(3)])
  next
    case (Some a)
    have valid': "is_rbt (add_to_rbt (a, k) (RBT_Impl.fold (add_option_to_rbt f) t1 t'))"
      by (auto intro: is_rbt_add_to_rbt[OF valid])
    show ?thesis
      by (auto simp: Some Branch(2)[OF valid'] keys_add_to_rbt[OF valid] Branch(1)[OF Branch(3)])
  qed
qed auto

lemma rbt_lookup_add_to_rbt: "is_rbt t \<Longrightarrow> rbt_lookup (add_to_rbt (a, b) t) x = (if a = x then Some (case rbt_lookup t x of None \<Rightarrow> {b} | Some Y \<Rightarrow> insert b Y) else rbt_lookup t x)"
  by (auto simp: add_to_rbt_def rbt_lookup_rbt_insert split: option.splits)

lemma rbt_lookup_fold_add_to_rbt: "is_rbt t' \<Longrightarrow> rbt_lookup (RBT_Impl.fold (add_option_to_rbt f) t t') x =
    (if x \<in> Option.these (f ` set (RBT_Impl.keys t)) \<union> set (RBT_Impl.keys t') then Some ({y \<in> set (RBT_Impl.keys t). f y = Some x}
    \<union> (case rbt_lookup t' x of None \<Rightarrow> {} | Some Y \<Rightarrow> Y)) else None)"
proof (induction t arbitrary: t')
  case Empty
  then show ?case
    using rbt_lookup_iff_keys(2,3)[OF is_rbt_rbt_sorted]
    by (fastforce split: option.splits)
next
  case (Branch col t1 k v t2)
  have valid: "is_rbt (RBT_Impl.fold (add_option_to_rbt f) t1 t')"
    using Branch(3)
    by (auto intro: is_rbt_fold_add_to_rbt)
  show ?case
  proof (cases "f k")
    case None
    have fold_set: "x \<in> Option.these (f ` set (RBT_Impl.keys t2)) \<union> ((Option.these (f ` set (RBT_Impl.keys t1)) \<union> set (RBT_Impl.keys t'))) \<longleftrightarrow>
      x \<in> Option.these (f ` set (RBT_Impl.keys (Branch col t1 k v t2))) \<union> set (RBT_Impl.keys t')"
      by (auto simp: None)
    show ?thesis
      unfolding fold_simps comp_def None option.case(1) Branch(2)[OF valid] keys_add_to_rbt[OF valid] keys_fold_add_to_rbt[OF Branch(3)]
        rbt_lookup_add_to_rbt[OF valid] Branch(1)[OF Branch(3)] fold_set
      using rbt_lookup_iff_keys(2,3)[OF is_rbt_rbt_sorted[OF Branch(3)]]
      by (auto simp: None split: option.splits) (auto dest: these_imageI)
  next
    case (Some a)
    have valid': "is_rbt (add_to_rbt (a, k) (RBT_Impl.fold (add_option_to_rbt f) t1 t'))"
      by (auto intro: is_rbt_add_to_rbt[OF valid])
    have fold_set: "x \<in> Option.these (f ` set (RBT_Impl.keys t2)) \<union> (insert a (Option.these (f ` set (RBT_Impl.keys t1)) \<union> set (RBT_Impl.keys t'))) \<longleftrightarrow>
    x \<in> Option.these (f ` set (RBT_Impl.keys (Branch col t1 k v t2))) \<union> set (RBT_Impl.keys t')"
      by (auto simp: Some)
    have F1: "(case if P then Some X else None of None \<Rightarrow> {k} | Some Y \<Rightarrow> insert k Y) =
    (if P then (insert k X) else {k})" for P X
      by auto
    have F2: "(case if a = x then Some X else if P then Some Y else None of None \<Rightarrow> {} | Some Y \<Rightarrow> Y) =
    (if a = x then X else if P then Y else {})"
      for P X and Y :: "'b set"
      by auto
    show ?thesis
      unfolding fold_simps comp_def Some option.case(2) Branch(2)[OF valid'] keys_add_to_rbt[OF valid] keys_fold_add_to_rbt[OF Branch(3)]
        rbt_lookup_add_to_rbt[OF valid] Branch(1)[OF Branch(3)] fold_set F1 F2
      using rbt_lookup_iff_keys(2,3)[OF is_rbt_rbt_sorted[OF Branch(3)]]
      by (auto simp: Some split: option.splits) (auto dest: these_imageI)
  qed
qed

end

context
  fixes c :: "'a comparator"
begin

definition add_to_rbt_comp :: "'a \<times> 'b \<Rightarrow> ('a, 'b set) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "add_to_rbt_comp = (\<lambda>(a, b) t. case rbt_comp_lookup c t a of None \<Rightarrow> rbt_comp_insert c a {b} t
  | Some X \<Rightarrow> rbt_comp_insert c a (insert b X) t)"

abbreviation "add_option_to_rbt_comp f \<equiv> (\<lambda>b _ t. case f b of Some a \<Rightarrow> add_to_rbt_comp (a, b) t | None \<Rightarrow> t)"

definition cluster_rbt_comp :: "('b \<Rightarrow> 'a option) \<Rightarrow> ('b, unit) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "cluster_rbt_comp f t = RBT_Impl.fold (add_option_to_rbt_comp f) t RBT_Impl.Empty"

context
  assumes c: "comparator c"
begin

lemma add_to_rbt_comp: "add_to_rbt_comp = ord.add_to_rbt (lt_of_comp c)"
  unfolding add_to_rbt_comp_def ord.add_to_rbt_def rbt_comp_lookup[OF c] rbt_comp_insert[OF c]
  by simp

lemma cluster_rbt_comp: "cluster_rbt_comp = ord.cluster_rbt (lt_of_comp c)"
  unfolding cluster_rbt_comp_def ord.cluster_rbt_def add_to_rbt_comp
  by simp

end

end

lift_definition mapping_of_cluster :: "('b \<Rightarrow> 'a :: ccompare option) \<Rightarrow> ('b, unit) rbt \<Rightarrow> ('a, 'b set) mapping_rbt" is
  "cluster_rbt_comp ccomp"
  using linorder.is_rbt_fold_add_to_rbt[OF comparator.linorder[OF ID_ccompare'] ord.Empty_is_rbt]
  by (fastforce simp: cluster_rbt_comp[OF ID_ccompare'] ord.cluster_rbt_def)

lemma cluster_code[code]:
  fixes f :: "'b :: ccompare \<Rightarrow> 'a :: ccompare option" and t :: "('b, unit) mapping_rbt"
  shows "cluster f (RBT_set t) = (case ID CCOMPARE('a) of None \<Rightarrow>
    Code.abort (STR ''cluster: ccompare = None'') (\<lambda>_. cluster f (RBT_set t))
    | Some c \<Rightarrow> (case ID CCOMPARE('b) of None \<Rightarrow>
    Code.abort (STR ''cluster: ccompare = None'') (\<lambda>_. cluster f (RBT_set t))
    | Some c' \<Rightarrow> (RBT_Mapping (mapping_of_cluster f (RBT_Mapping2.impl_of t)))))"
proof -
  {
    fix c c'
    assume assms: "ID ccompare = (Some c :: 'a comparator option)" "ID ccompare = (Some c' :: 'b comparator option)"
    have c_def: "c = ccomp"
      using assms(1)
      by auto
    have c'_def: "c' = ccomp"
      using assms(2)
      by auto
    have c: "comparator (ccomp :: 'a comparator)"
      using ID_ccompare'[OF assms(1)]
      by (auto simp: c_def)
    have c': "comparator (ccomp :: 'b comparator)"
      using ID_ccompare'[OF assms(2)]
      by (auto simp: c'_def)
    note c_class = comparator.linorder[OF c]
    note c'_class = comparator.linorder[OF c']
    have rbt_lookup_cluster: "ord.rbt_lookup cless (cluster_rbt_comp ccomp f t) =
      (\<lambda>x. if x \<in> Option.these (f ` (set (RBT_Impl.keys t))) then Some {y \<in> (set (RBT_Impl.keys t)). f y = Some x} else None)"
      if "ord.is_rbt cless (t :: ('b, unit) rbt) \<or> ID ccompare = (None :: 'b comparator option)" for t
    proof -
      have is_rbt_t: "ord.is_rbt cless t"
        using assms that
        by auto
      show ?thesis
        unfolding cluster_rbt_comp[OF c] ord.cluster_rbt_def linorder.rbt_lookup_fold_add_to_rbt[OF c_class ord.Empty_is_rbt]
        by (auto simp: ord.rbt_lookup.simps split: option.splits)
    qed
    have dom_ord_rbt_lookup: "ord.is_rbt cless t \<Longrightarrow> dom (ord.rbt_lookup cless t) = set (RBT_Impl.keys t)" for t :: "('b, unit) rbt"
      using linorder.rbt_lookup_keys[OF c'_class] ord.is_rbt_def
      by auto
    have "cluster f (Collect (RBT_Set2.member t)) = Mapping (RBT_Mapping2.lookup (mapping_of_cluster f (mapping_rbt.impl_of t)))"
      using assms(2)[unfolded c'_def]
      by (transfer fixing: f) (auto simp: in_these_eq rbt_comp_lookup[OF c] rbt_comp_lookup[OF c'] rbt_lookup_cluster dom_ord_rbt_lookup)
  }
  then show ?thesis
    unfolding RBT_set_def
    by (auto split: option.splits)
qed

end
