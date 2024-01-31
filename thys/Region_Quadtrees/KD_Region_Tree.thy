section \<open>K-dimensional Region Trees\<close>

theory KD_Region_Tree
imports
  "HOL-Library.NList"
  "HOL-Library.Tree" (* only for \<open>height\<close> *)
begin                                         

(* TODO: In Isabelle after 2023 - remove *)
lemma nlists_Suc: "nlists (Suc n) A = (\<Union>a\<in>A. (#) a ` nlists n A)"
by(auto simp: set_eq_iff image_iff in_nlists_Suc_iff)
lemma in_nlists_UNIV: "xs \<in> nlists k UNIV \<longleftrightarrow> length xs = k"
unfolding nlists_def by(auto)
lemma nlists_singleton: "nlists n {a} = {replicate n a}"
unfolding nlists_def by(auto simp: replicate_length_same dest!: subset_singletonD)

text \<open>Generalizes quadtrees. Instead of having \<open>2^n\<close> direct children of a node,
the children are arranged in a binary tree where each \<open>Split\<close> splits along one dimension.\<close>

datatype 'a kdt = Box 'a | Split "'a kdt" "'a kdt"

(* For quickcheck: *)
datatype_compat kdt

type_synonym kdtb = "bool kdt"

text \<open>A \<open>kdt\<close> is most easily explained by showing how quad trees are represented:
\<open>Q t0 t1 t2 t3\<close> becomes @{term "Split (Split t0' t1') (Split t2' t3')"}
where \<open>ti'\<close> is the representation of \<open>ti\<close>; \<open>L a\<close> becomes @{term "Box a"}.
In general, each level of an abstract \<open>k\<close> dimensional tree subdivides space into \<open>2^k\<close>
subregions. This subdivision is represented by a \<open>kdt\<close> of depth at most \<open>k\<close>.
Further subdivisions of the subregions are seamlessly represented as the subtrees
at depth \<open>k\<close>. @{term "Box a"} represents a subregion entirely filled with \<open>a\<close>'s.
In contrast to quad trees, cubes can also occur half way down the subdivision.
For example, \<open>Q (L a) (L a) (L b) (L c)\<close> becomes @{term "Split (Box a) (Split (Box b) (Box c))"}.
\<close>

instantiation kdt :: (type)height
begin

fun height_kdt :: "'a kdt \<Rightarrow> nat" where
"height (Box _) = 0" |
"height (Split l r) = max (height l) (height r) + 1"

instance ..

end

lemma height_0_iff: "height t = 0 \<longleftrightarrow> (\<exists>x. t = Box x)"
by(cases t)auto

definition bits :: "nat \<Rightarrow> bool list set" where
"bits n = nlists n UNIV"

(* for quickcheck *)

lemma bits_0[code]: "bits 0 = {[]}"
by(simp add:bits_def)

lemma bits_Suc[code]:
  "bits (Suc n) = (let B = bits n in (#) True ` B \<union> (#) False ` B)"
by(simp_all add: bits_def nlists_Suc UN_bool_eq Let_def)


subsection \<open>Subtree\<close>

fun subtree :: "'a kdt \<Rightarrow> bool list \<Rightarrow> 'a kdt" where
"subtree t [] = t" |
"subtree (Box x) _ = Box x" |
"subtree (Split l r) (b#bs) = subtree (if b then r else l) bs"

lemma subtree_Box[simp]: "subtree (Box x) bs = Box x"
by(cases bs)auto

lemma height_subtree: "height (subtree t bs) \<le> height t - length bs"
by(induction t bs rule: subtree.induct) auto

lemma height_subtree2: "\<lbrakk> height t \<le> k * (Suc n); length bs = k\<rbrakk> \<Longrightarrow> height (subtree t bs) \<le> k * n"
using height_subtree[of t bs] by auto

lemma subtree_Split_Box: "length bs \<noteq> 0 \<Longrightarrow> subtree (Split (Box b) (Box b)) bs = Box b"
by(auto simp: neq_Nil_conv)

(* Surprisingly, points_SplitC is not needed:
lemma points_Split_Box: "Suc 0 \<le> k*n \<Longrightarrow> points k n (Split (Box b) (Box b)) = points k n (Box b)"
proof(induction n)
  case (Suc n)
  from \<open>Suc 0 \<le> k*Suc n\<close> have "k > 0" using neq0_conv by fastforce
  with Suc show ?case by(simp add: subtree_Split_Box nlists2_simp)
qed simp

lemma points_SplitC: "height (Split l r) \<le> k*n \<Longrightarrow> points k n (SplitC l r) = points k n (Split l r)"
by(induction l r rule: SplitC.induct)
  (simp_all add: points_Split_Box)
*)

subsection \<open>Shifting a coordinate by a boolean vector\<close>

definition mv :: "nat \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> nat list" where
"mv d = map2 (\<lambda>b x. x + (if b then 0 else d))"

lemma map_zip1: "\<lbrakk> length xs = length ys; \<forall>p \<in> set(zip xs ys). f p = fst p \<rbrakk> \<Longrightarrow> map f (zip xs ys) = xs"
by (metis (no_types, lifting) map_eq_conv map_fst_zip)

lemma map_mv1: "\<lbrakk> ps \<in> nlists (length bs) {0..<n}; length ps = length bs \<rbrakk>
 \<Longrightarrow> map (\<lambda>i. i < n) (mv (n) bs ps) = bs"
by(fastforce simp: mv_def intro!: map_zip1 dest: set_zip_rightD nlistsE_set split: if_splits)

lemma map_zip2: "\<lbrakk> length xs = length ys; \<forall>p \<in> set(zip xs ys). f p = snd p \<rbrakk> \<Longrightarrow> map f (zip xs ys) = ys"
by (metis (no_types, lifting) map_eq_conv map_snd_zip)

lemma map_mv2: "\<lbrakk> ps \<in> nlists (length bs) {0..<2^n} \<rbrakk> \<Longrightarrow> map (\<lambda>x. x mod 2^n) (mv (2^n) bs ps) = ps"
by(fastforce simp: mv_def dest: set_zip_rightD nlistsE_set intro!: map_zip2)

lemma mv_map_map: "set ps \<subseteq> {0..<2 * n} \<Longrightarrow> mv (n) (map (\<lambda>x. x < n) ps) (map (\<lambda>x. x mod n) ps) = ps"
unfolding nlists_def mv_def
by(auto simp: map_eq_conv[where xs=ps and g=id,simplified] map2_map_map not_less le_iff_add)

lemma mv_in_nlists:
  "\<lbrakk> p \<in> nlists k {0..<2 ^ n}; bs \<in> bits k \<rbrakk> \<Longrightarrow> mv (2^n) bs p \<in> nlists k {0..<2 * 2 ^ n}"
unfolding mv_def nlists_def bits_def
by (fastforce dest: set_zip_rightD)

lemma in_nlists2D: "xs \<in> nlists k {0..<2 * 2^n} \<Longrightarrow> \<exists>bs\<in> bits k. xs \<in> mv (2^n) bs ` nlists k {0..<2^n}"
unfolding nlists_def bits_def image_def
apply(rule bexI[where x  = "map (\<lambda>x. x < 2^n) xs"])
 apply(simp)
 apply(rule exI[where x = "map (\<lambda>i. i mod 2^n) xs"])
 apply (auto simp add: mv_map_map)
done

lemma nlists2_simp: "nlists k {0..<2 * 2 ^ n} = (\<Union>bs\<in> bits k. mv (2^n) bs ` nlists k {0..<2 ^ n})"
by (auto simp: mv_in_nlists in_nlists2D)

lemma in_mv_image: "\<lbrakk> ps \<in> nlists k {0..<2*2^n}; Ps \<subseteq> nlists k {0..<2^n}; bs \<in> bits k \<rbrakk> \<Longrightarrow>
  ps \<in> mv (2^n) bs ` Ps \<longleftrightarrow> map (\<lambda>x. x mod 2^n) ps \<in> Ps \<and> (bs = map (\<lambda>i. i < 2^n) ps)"
by (auto simp: map_mv1 map_mv2 mv_map_map bits_def intro!: image_eqI)


subsection \<open>Points in a tree\<close>

fun cube :: "nat \<Rightarrow> nat \<Rightarrow> nat list set" where
"cube k n = nlists k {0..<2^n}"

fun points :: "nat \<Rightarrow> nat \<Rightarrow> kdtb \<Rightarrow> nat list set" where
"points k n (Box b) = (if b then cube k n else {})" |
"points k (Suc n) t = (\<Union>bs \<in> bits k. mv (2^n) bs ` points k n (subtree t bs))"

lemma points_Suc: "points k (Suc n) t = (\<Union>bs \<in> bits k. mv (2^n) bs ` points k n (subtree t bs))"
by(cases t) (simp_all add: nlists2_simp)

lemma points_subset: "height t \<le> k*n \<Longrightarrow> points k n t \<subseteq> nlists k {0..<2^n}"
proof(induction k n t rule: points.induct)
  case (2 k n l r)
  have "\<And>bs. bs \<in> bits k \<Longrightarrow> height (subtree (Split l r) bs) \<le> k*n"
    unfolding bits_def using "2.prems" height_subtree2 in_nlists_UNIV by blast
  with "2.IH" show ?case
    by(auto intro: mv_in_nlists dest: subsetD)
qed auto


subsection \<open>Compression\<close>

text \<open>Compressing Split:\<close>

fun SplitC :: "'a kdt \<Rightarrow> 'a kdt \<Rightarrow> 'a kdt" where
"SplitC (Box b1) (Box b2) = (if b1=b2 then Box b1 else Split (Box b1) (Box b2))" |
"SplitC t1 t2 = Split t1 t2"

fun compressed :: "'a kdt \<Rightarrow> bool" where
"compressed (Box _) = True" |
"compressed (Split l r) = (compressed l \<and> compressed r \<and> \<not>(\<exists>b. l = Box b \<and> r = Box b))"

lemma compressedI: "\<lbrakk> compressed l; compressed r \<rbrakk> \<Longrightarrow> compressed (SplitC l r)"
by(induction l r rule: SplitC.induct) auto

lemma subtree_SplitC:
  "1 \<le> length bs \<Longrightarrow> subtree (SplitC l r) bs = subtree (Split l r) bs"
by(induction l r rule: SplitC.induct)
  (simp_all add: subtree_Split_Box Suc_le_eq)

lemma height_SplitC: "height(SplitC l r) \<le> Suc (max (height l) (height r))"
by(cases "(l,r)" rule: SplitC.cases)(auto)

lemma height_SplitC2: "\<lbrakk> height l \<le> n; height r \<le> n \<rbrakk> \<Longrightarrow> height(SplitC l r) \<le> Suc n"
using height_SplitC[of l r] by simp

subsection \<open>Extracting a point from a tree\<close>

text \<open>Also the abstraction function.\<close>

fun get :: "nat \<Rightarrow> 'a kdt \<Rightarrow> nat list \<Rightarrow> 'a"  where
"get _ (Box b) _ = b" |
"get (Suc n) t ps = get n (subtree t (map (\<lambda>i. i < 2^n) ps)) (map (\<lambda>i. i mod 2^n) ps)"

lemma get_Suc: "get (Suc n) t ps =
  get n (subtree t (map (\<lambda>i. i < 2 ^ n) ps)) (map (\<lambda>i. i mod 2 ^ n) ps)"
by(cases t)auto

lemma points_get: "\<lbrakk> height t \<le> k*n; ps \<in> nlists k {0..<2^n} \<rbrakk> \<Longrightarrow>
  get n t ps = (ps \<in> points k n t)"
proof(induction n arbitrary: k t ps)
  case 0
  then show ?case by(clarsimp simp add: height_0_iff)
next
  case (Suc n)
  show ?case
  proof (cases t)
    case Box
    thus ?thesis using Suc.prems(2) by(simp)
  next
    case (Split l r)
    obtain k0 where "k = Suc k0" using Suc.prems(1) Split
      by(cases k) auto
    hence "ps \<noteq> []"
      using Suc.prems(2) by (auto simp: in_nlists_Suc_iff)
    then show ?thesis using Suc.prems Split Suc.IH[OF height_subtree2[OF Suc.prems(1)]] in_nlists2D
      by(simp add: height_subtree2 in_mv_image points_subset bits_def)
  qed
qed


subsection \<open>Modifying a point in a tree\<close>

fun modify :: "('a kdt \<Rightarrow> 'a kdt) \<Rightarrow> bool list \<Rightarrow> 'a kdt \<Rightarrow> 'a kdt" where
"modify f [] t = f t" |
"modify f (b # bs) (Split l r) = (if b then SplitC l (modify f bs r) else SplitC (modify f bs l) r)" |
"modify f (b # bs) (Box a) =
  (let t = modify f bs (Box a) in if b then SplitC (Box a) t else SplitC t (Box a))"

fun put :: "nat list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a kdt \<Rightarrow> 'a kdt" where
"put ps a 0 (Box _) = Box a" |
"put ps a (Suc n) t = modify (put (map (\<lambda>i. i mod 2^n) ps) a n) (map (\<lambda>i. i < 2^n) ps) t"


lemma height_modify: "\<lbrakk> \<forall>t. height t \<le> nk \<longrightarrow> height (f t) \<le> nk;
     height t \<le> k + nk; length bs = k\<rbrakk>
    \<Longrightarrow> height (modify f bs t) \<le> k + nk"
apply(induction f bs t arbitrary: k rule: modify.induct)
by (auto simp: height_SplitC2 Let_def)

lemma height_put: "height t \<le> n * length ps \<Longrightarrow> height (put ps a n t) \<le> n * length ps"
proof(induction ps a n t rule: put.induct)
  case 2
  then show ?case by (auto simp: height_modify)
qed auto

lemma subtree_modify: "\<lbrakk> length bs' = length bs \<rbrakk>
    \<Longrightarrow> subtree (modify f bs t) bs' = (if bs' = bs then f(subtree t bs) else subtree t bs')"
apply(induction f bs t arbitrary: bs' rule: modify.induct)
apply(auto simp add: length_Suc_conv Let_def subtree_SplitC split: if_splits)
done

lemma mod_eq1: "\<lbrakk> y < 2 * n; ya < 2 * n; \<not> ya < n; \<not> y < n; ya mod n = y mod n\<rbrakk>
       \<Longrightarrow> ya = (y::nat)"
by(simp add: mod_if mult_2 split: if_splits)

lemma nlist_eq_mod: "\<lbrakk> ps \<in> nlists k {0..<(2::nat) * 2 ^ n}; ps' \<in> nlists k {0..<2 * 2 ^ n};
     map (\<lambda>i. i < 2 ^ n) ps' = map (\<lambda>i. i < 2 ^ n) ps; ps' \<noteq> ps \<rbrakk> \<Longrightarrow>
      map (\<lambda>i. i mod 2 ^ n) ps' \<noteq> map (\<lambda>i. i mod 2 ^ n) ps"
apply(induction k arbitrary: ps ps')
 apply simp
apply (fastforce simp: in_nlists_Suc_iff mod_eq1)
done

lemma get_put: "\<lbrakk> height t \<le> k*n; ps \<in> cube k n; ps' \<in> cube k n \<rbrakk> \<Longrightarrow>
  get n (put ps a n t) ps' = (if ps' = ps then a else get n t ps')"
proof(induction ps a n t arbitrary: ps' rule: put.induct)
  case 1
  then show ?case by (simp add: nlists_singleton)
next
  case 2
  thus ?case using in_nlists2D
    by(auto simp add: subtree_modify get_Suc height_subtree2 nlist_eq_mod in_mv_image)
qed auto

lemma compressed_modify: "\<lbrakk> compressed t; compressed (f (subtree t bs)) \<rbrakk> \<Longrightarrow> compressed (modify f bs t)"
by(induction f bs t rule: modify.induct) (auto simp: compressedI Let_def)

lemma compressed_subtree: "compressed t \<Longrightarrow> compressed (subtree t bs)"
by(induction t bs rule: subtree.induct) auto

lemma compressed_put:
  "\<lbrakk>  height t \<le> k*n; k = length ps; compressed t \<rbrakk> \<Longrightarrow> compressed (put ps a n t)"
proof(induction ps a n t rule: put.induct)
  case 1
  then show ?case by (simp)
next
  case 2
  thus ?case by (simp add: compressed_modify compressed_subtree height_subtree2)
qed auto


subsection \<open>Union\<close>

fun union :: "kdtb \<Rightarrow> kdtb \<Rightarrow> kdtb" where
"union (Box b) t = (if b then Box True else t)" |
"union t (Box b) = (if b then Box True else t)" |
"union (Split l1 r1) (Split l2 r2) = SplitC (union l1 l2) (union r1 r2)"

lemma union_Box2: "union t (Box b) = (if b then Box True else t)"
by(cases t) auto

lemma subtree_union: "subtree (union t1 t2) bs = union (subtree t1 bs) (subtree t2 bs)"
proof(induction t1 t2 arbitrary: bs rule: union.induct)
  case 2 thus ?case by(auto simp: union_Box2)
next
  case 3 thus ?case by(cases bs) (auto simp: subtree_SplitC)
qed auto

lemma points_union:
  "\<lbrakk> max (height t1) (height t2) \<le> k*n \<rbrakk> \<Longrightarrow>
  points k n (union t1 t2) = points k n t1 \<union> points k n t2"
proof(induction n arbitrary: t1 t2)
  case 0 thus ?case by(clarsimp simp add: height_0_iff)
next
  case (Suc n)
  have "height t1 \<le> k * Suc n" "height t2 \<le> k * Suc n"
    using Suc.prems by auto
  from height_subtree2[OF this(1)] height_subtree2[OF this(2)] show ?case
    by(auto simp: Suc.IH subtree_union points_Suc bits_def)
qed

lemma get_union:
  "\<lbrakk> max (height t1) (height t2) \<le> length ps * n \<rbrakk> \<Longrightarrow>
  get n (union t1 t2) ps = (get n t1 ps \<or> get n t2 ps)"
proof(induction n arbitrary: t1 t2 ps)
  case 0 thus ?case by(clarsimp simp add: height_0_iff)
next
  case (Suc n)
  have "height t1 \<le> length ps * Suc n" "height t2 \<le> length ps * Suc n"
    using Suc.prems(1) by auto
  from height_subtree2[OF this(1)] height_subtree2[OF this(2)] show ?case
    by(simp add: Suc.IH subtree_union get_Suc)
qed

lemma height_union: "height (union t1 t2) \<le> max (height t1) (height t2)"
by(induction t1 t2 rule: union.induct) (auto simp: height_SplitC2)

lemma compressed_union: "compressed t1 \<Longrightarrow> compressed t2 \<Longrightarrow> compressed(union t1 t2)"
by(induction t1 t2 rule: union.induct) (simp_all add: compressedI)

(*unused_thms*)

end
