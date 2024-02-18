section \<open>K-dimensional Region Trees - Nested Trees\<close>

(*
Nested trees:
Each level of the k-d tree (kdt) is encapsulated in a separate splitting tree (tree1).
Experimental.
*)

theory KD_Region_Nested
imports "HOL-Library.NList"
begin

(* TODO: In Isabelle after 2023 - remove *)
lemma nlists_Suc: "nlists (Suc n) A = (\<Union>a\<in>A. (#) a ` nlists n A)"
  by(auto simp: set_eq_iff image_iff in_nlists_Suc_iff)
lemma nlists_singleton: "nlists n {a} = {replicate n a}"
  unfolding nlists_def by(auto simp: replicate_length_same dest!: subset_singletonD)

fun cube :: "nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "cube k n = nlists k {0..<2^n}"

datatype 'a tree1 = Lf 'a | Br "'a tree1" "'a tree1"
datatype 'a kdt = Cube 'a | Dims "'a kdt tree1"

(* For quickcheck: *)
datatype_compat tree1
datatype_compat kdt

type_synonym kdtb = "bool kdt"

lemma set_tree1_finite_ne: "finite (set_tree1 t) \<and> set_tree1 t \<noteq> {}"
  by(induction t) auto

lemma kdt_tree1_term[termination_simp]: "x \<in> set_tree1 t \<Longrightarrow> size_kdt f x < Suc (size_tree1 (size_kdt f) t)"
  by(induction t)(auto)

fun h_tree1 :: "'a tree1 \<Rightarrow> nat" where
  "h_tree1 (Lf _) = 0" |
  "h_tree1 (Br l r) = max (h_tree1 l) (h_tree1 r) + 1"

function (sequential) h_kdt :: "'a kdt \<Rightarrow> nat" where
  "h_kdt (Cube _) = 0" |
  "h_kdt (Dims t) = Max (h_kdt ` (set_tree1 t)) + 1"
  by pat_completeness auto
termination
  by(relation "measure (size_kdt (\<lambda>_. 1))")
    (auto simp add: wf_lex_prod kdt_tree1_term)

function (sequential) inv_kdt :: "nat \<Rightarrow> 'a kdt \<Rightarrow> bool" where
  "inv_kdt k (Cube b) = True" |
  "inv_kdt k (Dims t) = (h_tree1 t \<le> k \<and> (\<forall>kt \<in> set_tree1 t. inv_kdt k kt))"
  by pat_completeness auto
termination
  by(relation "{} <*lex*> measure (size_kdt (\<lambda>_. 1))")
    (auto simp add: wf_lex_prod kdt_tree1_term)

definition bits :: "nat \<Rightarrow> bool list set" where
  "bits n = nlists n UNIV"

lemma bits_0[code]: "bits 0 = {[]}"
  by (auto simp: bits_def)

lemma bits_Suc[code]: "bits (Suc n) = (let B = bits n in (#) True ` B \<union> (#) False ` B)"
  unfolding bits_def nlists_Suc UN_bool_eq by metis

fun leaf :: "'a tree1 \<Rightarrow> bool list \<Rightarrow> 'a" where
  "leaf (Lf x) _ = x" |
  "leaf (Br l r) (b#bs) = leaf (if b then r else l) bs" |
  "leaf (Br l r) [] = leaf l []" (* to avoid undefinedness *)

definition mv :: "bool list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "mv = map2 (\<lambda>b x. 2*x + (if b then 0 else 1))"

fun points :: "nat \<Rightarrow> nat \<Rightarrow> kdtb \<Rightarrow> nat list set" where
  "points k n (Cube b) = (if b then cube k n else {})" |
  "points k (Suc n) (Dims t) = (\<Union>bs \<in> bits k. mv bs ` points k n (leaf t bs))"

lemma bits_nonempty: "bits n \<noteq> {}"
  by(auto simp: bits_def Ex_list_of_length)

lemma finite_bits: "finite (bits n)"
  by (metis List.finite_set List.set_insert UNIV_bool bits_def empty_set nlists_set)

lemma mv_in_nlists:
  "\<lbrakk> p \<in> nlists k {0..<2 ^ n}; bs \<in> bits k \<rbrakk> \<Longrightarrow> mv bs p \<in> nlists k {0..<2 * 2 ^ n}"
  unfolding mv_def nlists_def bits_def
  by (fastforce dest: set_zip_rightD)

lemma leaf_append: "length bs \<ge> h_tree1 t  \<Longrightarrow> leaf t (bs@bs') = leaf t bs"
  by (induction t bs arbitrary: bs' rule: leaf.induct) auto

lemma leaf_take: "length bs \<ge> h_tree1 t  \<Longrightarrow> leaf t (bs) = leaf t (take (h_tree1 t) bs)"
  by (metis append_take_drop_id leaf_append length_take min.absorb2 order_refl)

lemma Union_bits_le:
  "h_tree1 t \<le> n \<Longrightarrow> (\<Union>bs\<in>bits n. {leaf t bs}) = (\<Union>bs\<in>bits (h_tree1 t). {leaf t bs})"
  unfolding bits_def nlists_def
  apply rule
  using leaf_take apply (force)
  by auto (metis Ex_list_of_length order.refl le_add_diff_inverse leaf_append length_append)

lemma set_tree1_leafs:
  "set_tree1 t = (\<Union>bs \<in> bits (h_tree1 t). {leaf t bs})"
proof(induction t)
  case (Lf x)
  then show ?case by (simp add: bits_nonempty)
next
  case (Br t1 t2)
  then show ?case using Union_bits_le[of t1 "h_tree1 t2"] Union_bits_le[of t2 "h_tree1 t1"]
    by (auto simp add: Let_def bits_Suc max_def)
qed

lemma points_subset: "inv_kdt k t \<Longrightarrow> h_kdt t \<le> n \<Longrightarrow> points k n t \<subseteq> nlists k {0..<2^n}"
proof(induction k n t rule: points.induct)
  case (2 k n t)
  have "mv bs ps \<in> nlists k {0..<2 * 2 ^ n}" if *: "bs \<in> bits k" "ps \<in> points k n (leaf t bs)" for bs ps
  proof -
    have "inv_kdt k (leaf t bs)" using *(1) "2.prems"(1)
      by(auto simp: set_tree1_leafs )
        (metis bits_def leaf_take length_take min.absorb2 nlistsE_length nlistsI subset_UNIV)
    moreover have "h_kdt (leaf t bs) \<le> n" using *(1) "2.prems"
        by(auto simp add: set_tree1_leafs bits_nonempty finite_bits)
          (metis bits_def leaf_take length_take min.absorb2 nlistsE_length nlistsI subset_UNIV)
    ultimately show ?thesis using * "2.IH"[of bs] mv_in_nlists by(auto)
  qed
  thus ?case by(auto)
qed auto

fun comb1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a tree1 \<Rightarrow> 'a tree1 \<Rightarrow> 'a tree1" where
"comb1 f (Lf x1) (Lf x2) = Lf (f x1 x2)" |
"comb1 f (Br l1 r1) (Br l2 r2) = Br (comb1 f l1 l2) (comb1 f r1 r2)" |
"comb1 f (Br l1 r1) (Lf x) = Br (comb1 f l1 (Lf x)) (comb1 f r1 (Lf x))" |
"comb1 f (Lf x) (Br l2 r2) = Br (comb1 f (Lf x) l2) (comb1 f (Lf x) r2)"

text \<open>The last two equations cover cases that do not arise but are needed to prove that @{const comb1}
only applies \<open>f\<close> to elements of the two trees, which implies this congruence lemma:\<close>

lemma comb1_cong[fundef_cong]:
  "\<lbrakk>s1 = t1; s2 = t2; \<And>x y. x \<in> set_tree1 t1 \<Longrightarrow> y \<in> set_tree1 t2 \<Longrightarrow> f x y = g x y\<rbrakk> \<Longrightarrow> comb1 f s1 s2 = comb1 g t1 t2"
apply(induction f t1 t2 arbitrary: s1 s2 rule: comb1.induct)
apply auto
done

text \<open>This congruence lemma in turn implies that \<open>union\<close> terminates because the recursive calls of
\<open>union\<close> via @{const comb1} only involve elements from the two trees, which are smaller.\<close>

function (sequential) union :: "kdtb \<Rightarrow> kdtb \<Rightarrow> kdtb" where
"union (Cube b) t = (if b then Cube True else t)" |
"union t (Cube b) = (if b then Cube True else t)" |
"union (Dims t1) (Dims t2) = Dims (comb1 union t1 t2)"
by pat_completeness auto
termination
by(relation "measure (size_kdt (\<lambda>_. 1)) <*lex*> {}")
  (auto simp add: wf_lex_prod kdt_tree1_term)

lemma leaf_comb1:
  "\<lbrakk> length bs \<ge> max (h_tree1 t1) (h_tree1 t2) \<rbrakk> \<Longrightarrow>
  leaf (comb1 f t1 t2) bs = f (leaf t1 bs) (leaf t2 bs)"
apply(induction f t1 t2 arbitrary: bs rule: comb1.induct)
apply (auto simp: Suc_le_length_iff split: if_splits)
done

lemma leaf_in_set_tree1: "\<lbrakk> length bs \<ge> h_tree1 t \<rbrakk> \<Longrightarrow> leaf t bs \<in> set_tree1 t"
apply(auto simp add: set_tree1_leafs bits_def intro: nlistsI)
by (metis leaf_take length_take min.absorb2 nlistsI subset_UNIV)
(* which one is used? both? *)
lemma leaf_in_set_tree2: "\<lbrakk>x \<in> nlists k UNIV; h_tree1 t1 \<le> k\<rbrakk> \<Longrightarrow> leaf t1 x \<in> set_tree1 t1"
by (metis leaf_in_set_tree1 leaf_take length_take min.absorb2 nlistsE_length)

lemma points_union:
  "\<lbrakk> inv_kdt k t1; inv_kdt k t2; n \<ge> max (h_kdt t1) (h_kdt t2) \<rbrakk> \<Longrightarrow>
  points k n (union t1 t2) = points k n t1 \<union> points k n t2"
proof(induction t1 t2 arbitrary: n rule: union.induct)
  case 1 thus ?case using Un_absorb2[OF points_subset] by simp
next
  case 2 thus ?case using Un_absorb1[OF points_subset] by simp
next
  case (3 t1 t2)
  from "3.prems" obtain m where "n = Suc m" by (auto dest: Suc_le_D)
  with 3 show ?case
    by (simp add: leaf_comb1 bits_def leaf_in_set_tree2 set_tree1_finite_ne image_Un UN_Un_distrib)
qed

lemma size_leaf[termination_simp]: "size (leaf t (map f ps)) < Suc (size_tree1 size t)"
apply(induction t "map f ps" arbitrary: ps rule: leaf.induct)
  apply simp
 apply fastforce
apply fastforce
done

fun get :: "'a kdt \<Rightarrow> nat list \<Rightarrow> 'a"  where
"get (Cube b) _ = b" |
"get (Dims t) ps = get (leaf t (map even ps)) (map (\<lambda>x. x div 2) ps)"

lemma map_zip1: "\<lbrakk> length xs = length ys; \<forall>p \<in> set(zip xs ys). f p = fst p \<rbrakk> \<Longrightarrow> map f (zip xs ys) = xs"
by (metis (no_types, lifting) map_eq_conv map_fst_zip)

lemma map_mv1: "\<lbrakk> length ps = length bs \<rbrakk> \<Longrightarrow> map even (mv bs ps) = bs"
unfolding nlists_def mv_def by(auto intro!: map_zip1 split: if_splits)

lemma map_zip2: "\<lbrakk> length xs = length ys; \<forall>p \<in> set(zip xs ys). f p = snd p \<rbrakk> \<Longrightarrow> map f (zip xs ys) = ys"
by (metis (no_types, lifting) map_eq_conv map_snd_zip)

lemma map_mv2: "\<lbrakk> length ps = length bs \<rbrakk> \<Longrightarrow> map (\<lambda>x. x div 2) (mv bs ps) = ps"
unfolding nlists_def mv_def by(auto intro!: map_zip2)

lemma mv_map_map: "mv (map even ps) (map (\<lambda>x. x div 2) ps) = ps"
unfolding nlists_def mv_def
by(auto simp add: map_eq_conv[where xs=ps and g=id,simplified] map2_map_map)

lemma in_mv_image: "\<lbrakk> ps \<in> nlists k {0..<2*2^n}; Ps \<subseteq> nlists k {0..<2^n}; bs \<in> bits k \<rbrakk> \<Longrightarrow>
  ps \<in> mv bs ` Ps \<longleftrightarrow> map (\<lambda>x. x div 2) ps \<in> Ps \<and> (bs = map even ps)"
by (auto simp: map_mv1 map_mv2 mv_map_map bits_def intro!: image_eqI)

lemma get_points: "\<lbrakk> inv_kdt k t; h_kdt t \<le> n; ps \<in> nlists k {0..<2^n} \<rbrakk> \<Longrightarrow>
  get t ps = (ps \<in> points k n t)"
proof(induction t ps arbitrary: n rule: get.induct)
  case (2 t ps)
  obtain m where [simp]: "n = Suc m" using \<open>h_kdt (Dims t) \<le> n\<close> by (auto dest: Suc_le_D)
  have "\<forall>bs. length bs = k \<longrightarrow> inv_kdt k (leaf t bs) \<and> h_kdt (leaf t bs) \<le> m"
    using "2.prems" by (auto simp add: leaf_in_set_tree1 set_tree1_finite_ne)
  moreover have "map (\<lambda>x. x div 2) ps \<in> nlists k {0..<2 ^ m}"
    using "2.prems"(3) by(fastforce intro!: nlistsI dest: nlistsE_set)
  ultimately show ?case using "2.prems" "2.IH"[of m] points_subset[of k _ m]
    by(auto simp add: in_mv_image bits_def intro: nlistsI)
qed auto

fun modify :: "('a \<Rightarrow> 'a) \<Rightarrow> bool list \<Rightarrow> 'a tree1 \<Rightarrow> 'a tree1" where
"modify f [] (Lf x) = Lf (f x)" |
"modify f (b#bs) (Lf x)   = (if b then Br (Lf x) (modify f bs (Lf x)) else Br (modify f bs (Lf x)) (Lf x))" |
"modify f (b#bs) (Br l r) = (if b then Br l      (modify f bs r)      else Br (modify f bs l)      r)"

(* not yet compressed *)
fun put  :: "'a \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a kdt \<Rightarrow> 'a kdt" where
"put b' 0 ps (Cube _) = Cube b'" |
"put b' (Suc n) ps t =
  Dims (modify (put b' n (map (\<lambda>i. i div 2) ps)) (map even ps)
          (case t of Cube b \<Rightarrow> Lf (Cube b) | Dims t \<Rightarrow> t))"

lemma leaf_modify: "\<lbrakk> h_tree1 t \<le> length bs; length bs' = length bs \<rbrakk> \<Longrightarrow>
  leaf (modify f bs t) bs' = (if bs' = bs then f(leaf t bs) else leaf t bs')"
apply(induction f bs t arbitrary: bs' rule: modify.induct)
apply(auto simp: length_Suc_conv split: if_splits)
done

lemma in_nlists2D: "xs \<in> nlists k {0..<2 * 2 ^ n} \<Longrightarrow> \<exists>bs\<in>nlists k UNIV. xs \<in> mv bs ` nlists k {0..<2 ^ n}"
unfolding nlists_def
apply(rule bexI[where x = "map even xs"])
 apply(auto simp: image_def)[1]
apply(rule exI[where x = "map (\<lambda>i. i div 2) xs"])
apply(auto simp add: mv_map_map)
done

lemma nlists2_simp: "nlists k {0..<2 * 2 ^ n} = (\<Union>bs\<in>nlists k UNIV. mv bs ` nlists k {0..<2 ^ n})"
by (auto simp: mv_in_nlists bits_def in_nlists2D)

lemma mv_diff:
  "\<lbrakk> length qs = length bs; \<forall>as \<in> A. length as = length bs \<rbrakk> \<Longrightarrow> mv bs ` (A - {qs}) = mv bs ` A - {mv bs qs}"
by (auto) (metis map_mv2 )

lemma put_points: "\<lbrakk> inv_kdt k t; h_kdt t \<le> n; ps \<in> nlists k {0..<2^n} \<rbrakk> \<Longrightarrow>
 points k n (put b n ps t) = (if b then points k n t \<union> {ps} else points k n t - {ps})"
proof(induction b n ps t rule: put.induct)
  case 1 thus ?case by (simp add: nlists_singleton)
next
  case (2 b' n ps t)
  have *: "\<forall>x bs. t = Dims x \<longrightarrow> length bs = length ps \<longrightarrow> inv_kdt k (leaf x bs)"
    using "2.prems"(1,3) leaf_in_set_tree1 by fastforce
  have **: "t = Dims x \<Longrightarrow> length bs = length ps \<Longrightarrow> h_kdt (leaf x bs) \<le> n" for x bs
    using leaf_in_set_tree1[of x] "2.prems" set_tree1_finite_ne[of x] by auto
  have ***: "\<lbrakk> t = Dims x; length bs = length ps \<rbrakk> \<Longrightarrow>
    (\<forall>qs \<in> points (length ps) n (leaf x bs). length qs = length ps) = True" for x bs
    using "2.prems"(3) by (metis * ** nlistsE_length points_subset subset_iff)

  have Union_diff_aux: "a \<in> A \<Longrightarrow> (\<Union>x \<in> A. F x) = F a \<union> (\<Union>x \<in> A - {a}. F x)" for a A F
    by blast
  have notin_aux: "\<forall>x\<in>nlists (length ps) UNIV - {map even ps}.\<forall>qs \<in> A x. length qs = length ps \<Longrightarrow>
    ps \<notin> (\<Union>x\<in>nlists (length ps) UNIV - {map even ps}. mv x ` A x)" for A
  by (smt (verit) DiffE UN_E image_iff insert_iff map_mv1 nlistsE_length)
  have set1: "\<And>x y. {x. x \<noteq> y} = UNIV - {y}" by blast
  have nlists_map: "\<And>n xs f A. n = size xs \<Longrightarrow> (map f xs \<in> nlists n A) = (f ` set xs \<subseteq> A)" by simp

  have "(\<lambda>i. i div 2) ` set ps \<subseteq> {0..<2 ^ n}" using nlistsE_set[OF "2.prems"(3)] by auto
  moreover have "\<forall>x. t = Dims x \<longrightarrow> inv_kdt k (Dims x)"
    using "2.prems"(1) by blast
  moreover have "t = Dims x \<Longrightarrow> length bs = length ps \<Longrightarrow> points (length ps) n (leaf x bs) \<subseteq> nlists (length ps) {0..<2 ^ n}" for x bs
    using "2.prems"(3) by (metis * ** nlistsE_length points_subset)
  moreover have "length ps = k" using "2.prems"(3) by simp
  moreover from 2 * ** calculation show ?case
    by(clarsimp simp: leaf_modify[of _ "map even ps"] mv_map_map nlists_map bits_def
  nlistsE_length[of "_::bool list" k UNIV] nlists2_simp Union_diff_aux[of "map even ps"]
  mv_diff *** Diff_insert0[OF notin_aux]
  insert_absorb Diff_insert_absorb Int_absorb1 set1 Diff_Int_distrib Un_Diff
  split: kdt.split)
qed simp

end
