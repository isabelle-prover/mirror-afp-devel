section \<open>Parallel Rewriting\<close>

subsection \<open>Multihole Contexts\<close>

theory Multihole_Context
  imports 
    Trs
    FOR_Preliminaries
    SubList
begin

unbundle lattice_syntax

subsubsection \<open>Partitioning lists into chunks of given length\<close>

fun partition_by
  where
    "partition_by xs [] = []" |
    "partition_by xs (y#ys) = take y xs # partition_by (drop y xs) ys"

lemma partition_by_map0_append [simp]:
  "partition_by xs (map (\<lambda>x. 0) ys @ zs) = replicate (length ys) [] @ partition_by xs zs"
  by (induct ys) simp_all

lemma concat_partition_by [simp]:
  "sum_list ys = length xs \<Longrightarrow> concat (partition_by xs ys) = xs"
  by (induct ys arbitrary: xs) simp_all

definition partition_by_idx where
  "partition_by_idx l ys i j = partition_by [0..<l] ys ! i ! j"

lemma partition_by_nth_nth_old:
  assumes "i < length (partition_by xs ys)"
    and "j < length (partition_by xs ys ! i)"
    and "sum_list ys = length xs"
  shows "partition_by xs ys ! i ! j = xs ! (sum_list (map length (take i (partition_by xs ys))) + j)"
  using concat_nth [OF assms(1, 2) refl]
  unfolding concat_partition_by [OF assms(3)] by simp

lemma map_map_partition_by:
  "map (map f) (partition_by xs ys) = partition_by (map f xs) ys"
  by (induct ys arbitrary: xs) (auto simp: take_map drop_map)

lemma length_partition_by [simp]:
  "length (partition_by xs ys) = length ys"
  by (induct ys arbitrary: xs) simp_all

lemma partition_by_Nil [simp]:
  "partition_by [] ys = replicate (length ys) []"
  by (induct ys) simp_all

lemma partition_by_concat_id [simp]:
  assumes "length xss = length ys"
    and "\<And>i. i < length ys \<Longrightarrow> length (xss ! i) = ys ! i"
  shows "partition_by (concat xss) ys = xss"
  using assms 
proof (induct ys arbitrary: xss)
  case (Cons y ys xss)
  then show ?case by (cases xss; fastforce)
qed simp


lemma partition_by_nth:
  "i < length ys \<Longrightarrow> partition_by xs ys ! i = take (ys ! i) (drop (sum_list (take i ys)) xs)"
proof (induct ys arbitrary: xs i) 
  case (Cons x xs i)
  thus ?case by (cases i, auto simp: ac_simps)
qed simp

lemma partition_by_nth_less:
  assumes "k < i" and "i < length zs"
    and "length xs = sum_list (take i zs) + j"
  shows "partition_by (xs @ y # ys) zs ! k = take (zs ! k) (drop (sum_list (take k zs)) xs)"
proof -
  have "partition_by (xs @ y # ys) zs ! k =
    take (zs ! k) (drop (sum_list (take k zs)) (xs @ y # ys))"
    using assms by (auto simp: partition_by_nth)
  moreover have "zs ! k + sum_list (take k zs) \<le> length xs"
    using assms by (simp add: sum_list_take_eq)
  ultimately show ?thesis by simp
qed

lemma partition_by_nth_greater:
  assumes "i < k" and "k < length zs" and "j < zs ! i"
    and "length xs = sum_list (take i zs) + j"
  shows "partition_by (xs @ y # ys) zs ! k =
    take (zs ! k) (drop (sum_list (take k zs) - 1) (xs @ ys))"
proof -
  have "partition_by (xs @ y # ys) zs ! k =
    take (zs ! k) (drop (sum_list (take k zs)) (xs @ y # ys))"
    using assms by (auto simp: partition_by_nth)
  moreover have "sum_list (take k zs) > length xs"
    using assms by (auto simp: sum_list_take_eq)
  ultimately show ?thesis by (auto) (metis Suc_diff_Suc drop_Suc_Cons)
qed

lemma length_partition_by_nth:
  "sum_list ys = length xs \<Longrightarrow> i < length ys \<Longrightarrow> length (partition_by xs ys ! i) = ys ! i"
proof (induct ys arbitrary: xs i)
  case (Cons y ys xs i)
  thus ?case by (cases i, auto)
qed simp

lemma partition_by_nth_nth_elem:
  assumes "sum_list ys = length xs" "i < length ys" "j < ys ! i"
  shows "partition_by xs ys ! i ! j \<in> set xs"
proof -
  from assms have "j < length (partition_by xs ys ! i)" by (simp only: length_partition_by_nth)
  then have "partition_by xs ys ! i ! j \<in> set (partition_by xs ys ! i)" by auto
  with assms(2) have "partition_by xs ys ! i ! j \<in> set (concat (partition_by xs ys))" by auto
  then show ?thesis using assms by simp
qed

lemma partition_by_nth_nth:
  assumes "sum_list ys = length xs" "i < length ys" "j < ys ! i"
  shows "partition_by xs ys ! i ! j = xs ! partition_by_idx (length xs) ys i j"
    "partition_by_idx (length xs) ys i j < length xs"
  unfolding partition_by_idx_def
proof -
  let ?n = "partition_by [0..<length xs] ys ! i ! j"
  show "?n < length xs"
    using partition_by_nth_nth_elem[OF _ assms(2,3), of "[0..<length xs]"] assms(1) by simp
  have li: "i < length (partition_by [0..<length xs] ys)" using assms(2) by simp
  have lj: "j < length (partition_by [0..<length xs] ys ! i)"
    using assms by (simp add: length_partition_by_nth)
  have "partition_by (map ((!) xs) [0..<length xs]) ys ! i ! j = xs ! ?n"
    by (simp only: map_map_partition_by[symmetric] nth_map[OF li] nth_map[OF lj])
  then show "partition_by xs ys ! i ! j = xs ! ?n" by (simp add: map_nth)
qed

lemma map_length_partition_by [simp]:
  "sum_list ys = length xs \<Longrightarrow> map length (partition_by xs ys) = ys"
  by (intro nth_equalityI, auto simp: length_partition_by_nth)

lemma map_partition_by_nth [simp]:
  "i < length ys \<Longrightarrow> map f (partition_by xs ys ! i) = partition_by (map f xs) ys ! i"
proof (induct ys arbitrary: i xs)
  case (Cons y ys i xs)
  thus ?case by (cases i, simp_all add: take_map drop_map)
qed simp

lemma sum_list_partition_by [simp]:
  "sum_list ys = length xs \<Longrightarrow>
    sum_list (map (\<lambda>x. sum_list (map f x)) (partition_by xs ys)) = sum_list (map f xs)"
  by (induct ys arbitrary: xs) (simp_all, metis append_take_drop_id sum_list_append map_append)

lemma partition_by_map_conv:
  "partition_by xs ys = map (\<lambda>i. take (ys ! i) (drop (sum_list (take i ys)) xs)) [0 ..< length ys]"
  by (rule nth_equalityI) (simp_all add: partition_by_nth)

lemma UN_set_partition_by_map:
  "sum_list ys = length xs \<Longrightarrow> (\<Union>x\<in>set (partition_by (map f xs) ys). \<Union> (set x)) = \<Union>(set (map f xs))"
  by (induct ys arbitrary: xs)
    (simp_all add: drop_map take_map, metis UN_Un append_take_drop_id set_append)

lemma UN_set_partition_by:
  "sum_list ys = length xs \<Longrightarrow> (\<Union>zs \<in> set (partition_by xs ys). \<Union>x \<in> set zs. f x) = (\<Union>x \<in> set xs. f x)"
  by (induct ys arbitrary: xs) (simp_all, metis UN_Un append_take_drop_id set_append)

lemma Ball_atLeast0LessThan_partition_by_conv:
  "(\<forall>i\<in>{0..<length ys}. \<forall>x\<in>set (partition_by xs ys ! i). P x) =
    (\<forall>x \<in> \<Union>(set (map set (partition_by xs ys))). P x)"
  by auto (metis atLeast0LessThan in_set_conv_nth length_partition_by lessThan_iff)

lemma Ball_set_partition_by:
  "sum_list ys = length xs \<Longrightarrow>
  (\<forall>x \<in> set (partition_by xs ys). \<forall>y \<in> set x. P y) = (\<forall>x \<in> set xs. P x)"
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  then show ?case
    apply (subst (2) append_take_drop_id [of y xs, symmetric])
    apply (simp only: set_append)
    apply auto
    done
qed simp

lemma partition_by_append2:
  "partition_by xs (ys @ zs) = partition_by (take (sum_list ys) xs) ys @ partition_by (drop (sum_list ys) xs) zs"
  by (induct ys arbitrary: xs) (auto simp: drop_take ac_simps split: split_min)

lemma partition_by_concat2:
  "partition_by xs (concat ys) =
   concat (map (\<lambda>i . partition_by (partition_by xs (map sum_list ys) ! i) (ys ! i)) [0..<length ys])"
proof -
  have *: "map (\<lambda>i . partition_by (partition_by xs (map sum_list ys) ! i) (ys ! i)) [0..<length ys] =
    map (\<lambda>(x,y). partition_by x y) (zip (partition_by xs (map sum_list ys)) ys)"
    using zip_nth_conv[of "partition_by xs (map sum_list ys)" ys] by auto
  show ?thesis unfolding * by (induct ys arbitrary: xs) (auto simp: partition_by_append2)
qed

lemma partition_by_partition_by:
  "length xs = sum_list (map sum_list ys) \<Longrightarrow>
   partition_by (partition_by xs (concat ys)) (map length ys) =
   map (\<lambda>i. partition_by (partition_by xs (map sum_list ys) ! i) (ys ! i)) [0..<length ys]"
  by (auto simp: partition_by_concat2 intro: partition_by_concat_id)

datatype ('f, vars_mctxt : 'v) mctxt = MVar 'v | MHole | MFun 'f "('f, 'v) mctxt list"


subsubsection \<open>Conversions from and to multihole contexts\<close>

primrec mctxt_of_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt"
  where
    "mctxt_of_term (Var x) = MVar x" |
    "mctxt_of_term (Fun f ts) = MFun f (map mctxt_of_term ts)"

primrec term_of_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term"
  where
    "term_of_mctxt (MVar x) = Var x" |
    "term_of_mctxt (MFun f Cs) = Fun f (map term_of_mctxt Cs)"

lemma term_of_mctxt_mctxt_of_term_id [simp]:
  "term_of_mctxt (mctxt_of_term t) = t"
  by (induct t) (simp_all add: map_idI)

fun num_holes :: "('f, 'v) mctxt \<Rightarrow> nat"
  where
    "num_holes (MVar _) = 0" |
    "num_holes MHole = 1" |
    "num_holes (MFun _ ctxts) = sum_list (map num_holes ctxts)"

lemma num_holes_o_mctxt_of_term [simp]:
  "num_holes \<circ> mctxt_of_term = (\<lambda>x. 0)"
  apply (intro ext)
  subgoal for x by (induct x, auto)
  done


lemma mctxt_of_term_term_of_mctxt_id [simp]:
  "num_holes C = 0 \<Longrightarrow> mctxt_of_term (term_of_mctxt C) = C"
  by (induct C) (simp_all add: map_idI)

lemma vars_mctxt_of_term[simp]: "vars_mctxt (mctxt_of_term t) = vars_term t" 
  by (induct t, auto)

lemma num_holes_mctxt_of_term [simp]:
  "num_holes (mctxt_of_term t) = 0"
  by (induct t) simp_all

fun funas_mctxt :: "('f, 'v) mctxt \<Rightarrow> 'f sig"
  where
    "funas_mctxt (MFun f Cs) = {(f, length Cs)} \<union> \<Union>(funas_mctxt ` set Cs)" |
    "funas_mctxt _ = {}"

fun funas_mctxt_list :: "('f, 'v) mctxt \<Rightarrow> ('f \<times> nat) list"
  where
    "funas_mctxt_list (MFun f Cs) = (f, length Cs) # concat (map funas_mctxt_list Cs)" |
    "funas_mctxt_list _ = []"

lemma funas_mctxt_list [simp]:
  "set (funas_mctxt_list C) = funas_mctxt C"
  by (induct C) simp_all

fun split_term :: "(('f, 'v) term \<Rightarrow> bool) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) mctxt \<times> ('f, 'v) term list"
  where
    "split_term P (Var x) = (if P (Var x) then (MHole, [Var x]) else (MVar x, []))" |
    "split_term P (Fun f ts) =
    (if P (Fun f ts) then (MHole, [Fun f ts])
    else let us = map (split_term P) ts in (MFun f (map fst us), concat (map snd us)))"

fun cap_till :: "(('f, 'v) term \<Rightarrow> bool) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) mctxt"
  where
    "cap_till P (Var x) = (if P (Var x) then MHole else MVar x)" |
    "cap_till P (Fun f ts) = (if P (Fun f ts) then MHole else MFun f (map (cap_till P) ts))"

fun uncap_till :: "(('f, 'v) term \<Rightarrow> bool) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "uncap_till P (Var x) = (if P (Var x) then [Var x] else [])" |
    "uncap_till P (Fun f ts) = (if P (Fun f ts) then [Fun f ts] else concat (map (uncap_till P) ts))"

lemma split_term [simp]:
  "split_term P t = (cap_till P t, uncap_till P t)"
  by (induct t) (simp_all cong: map_cong)

definition "if_Fun_in_set F = (\<lambda>t. is_Var t \<or> the (root t) \<in> F)"

lemma if_Fun_in_set_simps [simp]:
  "if_Fun_in_set F (Var x)"
  "if_Fun_in_set F (Fun f ts) \<longleftrightarrow> (f, length ts) \<in> F"
  "is_Var t \<Longrightarrow> if_Fun_in_set F t"
  "is_Fun t \<Longrightarrow> if_Fun_in_set F t \<longleftrightarrow> the (root t) \<in> F"
  by (simp_all add: if_Fun_in_set_def)

lemma if_Fun_in_set_mono:
  "F \<subseteq> G \<Longrightarrow> if_Fun_in_set F t \<Longrightarrow> if_Fun_in_set G t"
  by (auto simp: if_Fun_in_set_def)

abbreviation "split_term_funas F \<equiv> split_term (if_Fun_in_set F)"
abbreviation "cap_till_funas F \<equiv> cap_till (if_Fun_in_set F)"
abbreviation "uncap_till_funas F \<equiv> uncap_till (if_Fun_in_set F)"

lemma if_Fun_in_set_uncap_till_funas:
  "A \<subseteq> B \<Longrightarrow> if_Fun_in_set A t \<Longrightarrow> uncap_till_funas B t = [t]"
  by (cases t) auto

lemma cap_till_funasD [dest]:
  "fn \<in> funas_mctxt (cap_till_funas F t) \<Longrightarrow> fn \<in> F \<Longrightarrow> False"
proof (induct t)
  case (Fun f ts)
  then show ?case by (cases "(f, length ts) \<in> F") auto
qed simp

lemma cap_till_funas:
  "\<forall>fn \<in> funas_mctxt (cap_till_funas F t). fn \<notin> F"
  by auto

lemma uncap_till:
  "\<forall>s \<in> set (uncap_till P t). P s"
  by (induct t) simp_all

(*do not add to simpset, since it severely degrades simplifier performance*)
lemma uncap_till_singleton:
  assumes "s \<in> set (uncap_till P t)"
  shows "uncap_till P s = [s]"
  using assms
proof (induct t)
  case (Fun f ts)
  then show ?case by (cases "P (Fun f ts)") auto
qed simp

lemma uncap_till_idemp [simp]:
  "map (uncap_till P) (uncap_till P t) = map (\<lambda>s. [s]) (uncap_till P t)"
  by (intro map_cong [OF refl] uncap_till_singleton) simp_all

lemma uncap_till_Fun [simp]:
  "P (Fun f ts) \<Longrightarrow> uncap_till P (Fun f ts) = [Fun f ts]"
  by simp

abbreviation "partition_holes xs Cs \<equiv> partition_by xs (map num_holes Cs)"
abbreviation "partition_holes_idx l Cs \<equiv> partition_by_idx l (map num_holes Cs)"

fun fill_holes :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term"
  where
    "fill_holes (MVar x) _ = Var x" |
    "fill_holes MHole [t] = t" |
    "fill_holes (MFun f cs) ts = Fun f (map (\<lambda> i. fill_holes (cs ! i)
    (partition_holes ts cs ! i)) [0 ..< length cs])"

text \<open>The following induction scheme provides the @{term MFun} case with the list argument split
  according to the argument contexts. This feature is quite delicate: its benefit can be
  destroyed by premature simplification using the @{thm concat_partition_by} simplification rule.\<close>

lemma fill_holes_induct2[consumes 2, case_names MHole MVar MFun]:
  fixes P :: "('f,'v) mctxt \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"
  assumes len1: "num_holes C = length xs" and len2: "num_holes C = length ys"
    and Hole: "\<And>x y. P MHole [x] [y]"
    and Var: "\<And>v. P (MVar v) [] []"
    and Fun: "\<And>f Cs xs ys.  sum_list (map num_holes Cs) = length xs \<Longrightarrow>
    sum_list (map num_holes Cs) = length ys \<Longrightarrow>
    (\<And>i. i < length Cs \<Longrightarrow> P (Cs ! i) (partition_holes xs Cs ! i) (partition_holes ys Cs ! i)) \<Longrightarrow>
    P (MFun f Cs) (concat (partition_holes xs Cs)) (concat (partition_holes ys Cs))"
  shows "P C xs ys"
proof (insert len1 len2, induct C arbitrary: xs ys)
  case MHole then show ?case using Hole by (cases xs; cases ys) auto
next
  case (MVar v) then show ?case using Var by auto
next
  case (MFun f Cs) then show ?case using Fun[of Cs xs ys f] by (auto simp: length_partition_by_nth)
qed

lemma fill_holes_induct[consumes 1, case_names MHole MVar MFun]:
  fixes P :: "('f,'v) mctxt \<Rightarrow> 'a list \<Rightarrow> bool"
  assumes len: "num_holes C = length xs"
    and Hole: "\<And>x. P MHole [x]"
    and Var: "\<And>v. P (MVar v) []"
    and Fun: "\<And>f Cs xs. sum_list (map num_holes Cs) = length xs \<Longrightarrow>
    (\<And>i. i < length Cs \<Longrightarrow> P (Cs ! i) (partition_holes xs Cs ! i)) \<Longrightarrow>
    P (MFun f Cs) (concat (partition_holes xs Cs))"
  shows "P C xs"
  using fill_holes_induct2[of C xs xs "\<lambda> C xs _. P C xs"] assms by simp

lemma funas_term_fill_holes_iff: "num_holes C = length ts \<Longrightarrow>
   g \<in> funas_term (fill_holes C ts) \<longleftrightarrow> g \<in> funas_mctxt C \<or> (\<exists>t \<in> set ts. g \<in> funas_term t)"
proof (induct C ts rule: fill_holes_induct)
  case (MFun f Cs ts)
  have "(\<exists>i < length Cs. g \<in> funas_term (fill_holes (Cs ! i) (partition_holes (concat (partition_holes ts Cs)) Cs ! i)))
    \<longleftrightarrow> (\<exists>C \<in> set Cs. g \<in> funas_mctxt C) \<or> (\<exists>us \<in> set (partition_holes ts Cs). \<exists>t \<in> set us. g \<in> funas_term t)"
    using MFun by (auto simp: ex_set_conv_ex_nth)
  then show ?case by auto
qed auto

lemma fill_holes_MHole:
  "length ts = 1 \<Longrightarrow> ts ! 0 = u \<Longrightarrow> fill_holes MHole ts = u"
  by (cases ts) simp_all

(*some compatibility lemmas (which should be dropped eventually)*)
lemmas
  map_partition_holes_nth [simp] =
  map_partition_by_nth [of _ "map num_holes Cs" for Cs, unfolded length_map] and
  length_partition_holes [simp] =
  length_partition_by [of _ "map num_holes Cs" for Cs, unfolded length_map]

(*
lemma partition_holes_nth:
  "i < length Cs \<Longrightarrow>
    partition_holes xs Cs ! i =
      take (num_holes (Cs ! i)) (drop (sum_list (map num_holes (take i Cs))) xs)"
  using partition_by_nth [of i "map num_holes Cs" xs] by (simp add: take_map)
*)

lemma length_partition_holes_nth [simp]:
  assumes "sum_list (map num_holes cs) = length ts"
    and "i < length cs"
  shows "length (partition_holes ts cs ! i) = num_holes (cs ! i)"
  using assms by (simp add: length_partition_by_nth)

(*
lemma partition_holes_def:
  "partition_holes ts cs = map (\<lambda>i.
    take (num_holes (cs ! i)) (drop (sum_list (map num_holes (take i cs))) ts)) [0 ..< length cs]"
  by (simp add: partition_by_map_conv [of ts "map num_holes cs"] take_map)
*)

lemma concat_partition_holes_upt:
  assumes "i \<le> length cs"
  shows "concat [partition_holes ts cs ! j. j \<leftarrow> [0 ..< i]] =
    take (sum_list [num_holes (cs ! j). j \<leftarrow> [0 ..< i]]) ts"
  using assms
proof (induct i arbitrary: ts)
  case (Suc i)
  then have i': "i < length cs" by (metis less_eq_Suc_le)
  then have *: "i < length (map num_holes cs)" by simp
  then have i'':  "i \<le> length cs" by auto
  show ?case
    unfolding upt_Suc_append[OF le0] map_append concat_append Suc(1)[OF i''] concat.simps append_Nil2
    unfolding sum_list_append take_add 
    unfolding list.map(2)
    unfolding partition_by_nth [OF *]
    unfolding take_map nth_map [OF i']
    unfolding take_upt_idx[OF i']
    unfolding map_map o_def by auto
qed (auto)


lemma partition_holes_step:
  "partition_holes ts (C # Cs) = take (num_holes C) ts # partition_holes (drop (num_holes C) ts) Cs"
  by simp

lemma partition_holes_map_ctxt:
  assumes "length cs = length ds"
    and "\<And> i. i < length cs \<Longrightarrow> num_holes (cs ! i) = num_holes (ds ! i)"
  shows "partition_holes ts cs = partition_holes ts ds"
  using assms by (metis nth_map_conv)

lemma partition_holes_concat_id:
  assumes "length sss = length cs" 
    and "\<And> i. i < length cs \<Longrightarrow> num_holes (cs ! i) = length (sss ! i)"
  shows "partition_holes (concat sss) cs = sss"
  using assms by (intro partition_by_concat_id) auto

lemma partition_holes_fill_holes_conv:
  "fill_holes (MFun f cs) ts =
    Fun f [fill_holes (cs ! i) (partition_holes ts cs ! i). i \<leftarrow> [0 ..< length cs]]"
  by (simp add: partition_by_nth take_map)

lemma fill_holes_arbitrary:
  assumes lCs: "length Cs = length ts"
    and lss: "length ss = length ts"
    and rec: "\<And> i. i < length ts \<Longrightarrow> num_holes (Cs ! i) = length (ss ! i) \<and> f (Cs ! i) (ss ! i) = ts ! i"
  shows "map (\<lambda>i. f (Cs ! i) (partition_holes (concat ss) Cs ! i)) [0 ..< length Cs] = ts"
proof -
  have "sum_list (map num_holes Cs) = length (concat ss)" using assms
    by (auto simp: length_concat map_nth_eq_conv intro: arg_cong[of _ _ "sum_list"])
  moreover have "partition_holes (concat ss) Cs = ss"
    using assms by (auto intro: partition_by_concat_id)
  ultimately show ?thesis using assms by (auto intro: nth_equalityI)
qed

lemma fill_holes_MFun:
  assumes lCs: "length Cs = length ts"
    and lss: "length ss = length ts"
    and rec: "\<And> i. i < length ts \<Longrightarrow> num_holes (Cs ! i) = length (ss ! i) \<and> fill_holes (Cs ! i) (ss ! i) = ts ! i"
  shows "fill_holes (MFun f Cs) (concat ss) = Fun f ts" 
  unfolding fill_holes.simps term.simps
  by (rule conjI[OF refl], rule fill_holes_arbitrary[OF lCs lss rec])

inductive
  eq_fill ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt \<times> ('f, 'v) term list \<Rightarrow> bool" ("(_/ =\<^sub>f _)" [51, 51] 50)
  where
    eqfI [intro]: "t = fill_holes D ss \<Longrightarrow> num_holes D = length ss \<Longrightarrow> t =\<^sub>f (D, ss)"

lemma fill_holes_inj:
  assumes "num_holes C = length ss"
    and "num_holes C = length ts"
    and "fill_holes C ss = fill_holes C ts"
  shows "ss = ts"
  using assms
proof (induct C ss ts rule: fill_holes_induct2)
  case (MFun f Cs ss ts)
  then show ?case by (intro arg_cong[of _ _ "concat"] nth_equalityI) auto
qed auto

lemma eqf_refl [intro]:
  "num_holes C = length ts \<Longrightarrow> fill_holes C ts =\<^sub>f (C, ts)"
  by (auto)

lemma eqfE:
  assumes "t =\<^sub>f (D, ss)" shows "t = fill_holes D ss" "num_holes D = length ss"
  using assms[unfolded eq_fill.simps] by auto

lemma eqf_MFunI:
  assumes "length sss = length Cs"
    and "length ts = length Cs"
    and"\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)"
  shows "Fun f ts =\<^sub>f (MFun f Cs, concat sss)"
proof 
  have "num_holes (MFun f Cs) = sum_list (map num_holes Cs)" by simp
  also have "map num_holes Cs = map length sss"
    by (rule nth_equalityI, insert assms eqfE[OF assms(3)], auto)
  also have "sum_list (\<dots>) = length (concat sss)" unfolding length_concat ..
  finally show "num_holes (MFun f Cs) = length (concat sss)" .
  show "Fun f ts = fill_holes (MFun f Cs) (concat sss)"
    by (rule fill_holes_MFun[symmetric], insert assms(1,2) eqfE[OF assms(3)], auto)
qed

lemma eqf_MFunE:
  assumes "s =\<^sub>f (MFun f Cs,ss)"  
  obtains ts sss where "s = Fun f ts" "length ts = length Cs" "length sss = length Cs" 
    "\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)"
    "ss = concat sss"
proof -
  from eqfE[OF assms] have fh: "s = fill_holes (MFun f Cs) ss" 
    and nh: "sum_list (map num_holes Cs) = length ss" by auto
  from fh obtain ts where s: "s = Fun f ts" by (cases s, auto)
  from fh[unfolded s] 
  have ts: "ts = map (\<lambda>i. fill_holes (Cs ! i) (partition_holes ss Cs ! i)) [0..<length Cs]" 
    (is "_ = map (?f Cs ss) _")
    by auto
  let ?sss = "partition_holes ss Cs"
  from nh 
  have *: "length ?sss = length Cs" "\<And>i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, ?sss ! i)" "ss = concat ?sss"
    by (auto simp: ts)
  have len: "length ts = length Cs" unfolding ts by auto
  assume ass: "\<And>ts sss. s = Fun f ts \<Longrightarrow>
              length ts = length Cs \<Longrightarrow>
              length sss = length Cs \<Longrightarrow> (\<And>i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)) \<Longrightarrow> ss = concat sss \<Longrightarrow> thesis"
  show thesis
    by (rule ass[OF s len *])
qed

lemma eqf_MHoleE:
  assumes "s =\<^sub>f (MHole, ss)"  
  shows "ss = [s]"
  using assms
proof (cases ss)
  case (Cons x xs) with assms show ?thesis by (cases xs) (auto dest: eqfE) 
qed (auto dest: eqfE)

fun mctxt_of_ctxt :: "('f, 'v) ctxt \<Rightarrow> ('f, 'v) mctxt"
  where
    "mctxt_of_ctxt Hole = MHole" |
    "mctxt_of_ctxt (More f ss\<^sub>1 C ss\<^sub>2) =
    MFun f (map mctxt_of_term ss\<^sub>1 @ mctxt_of_ctxt C # map mctxt_of_term ss\<^sub>2)"

lemma num_holes_mctxt_of_ctxt [simp]:
  "num_holes (mctxt_of_ctxt C) = 1"
  by (induct C) simp_all

lemma mctxt_of_term: "t =\<^sub>f (mctxt_of_term t, [])"
proof (induct t)
  case (Var x)
  show ?case by auto
next
  case (Fun f ts)
  let ?ss = "map (\<lambda> _. []) ts"
  have id: "concat ?ss = []" by simp
  have "?case = (Fun f ts =\<^sub>f (MFun f (map mctxt_of_term ts), concat ?ss))" unfolding id by simp
  also have "\<dots>"
    by (rule eqf_MFunI, insert Fun[unfolded set_conv_nth], auto)
  finally show ?case .
qed

lemma mctxt_of_ctxt [simp]:
  "C\<langle>t\<rangle> =\<^sub>f (mctxt_of_ctxt C, [t])"
proof (induct C)
  case (More f bef C aft)
  let ?sss = "map (\<lambda> _. []) bef @ [t] # map (\<lambda> _. []) aft"
  let ?ts = "map mctxt_of_term bef @ mctxt_of_ctxt C # map mctxt_of_term aft"
  have id: "concat ?sss = [t]" by (induct bef, auto)
  have "?case = 
    (Fun f (bef @ C\<langle>t\<rangle> # aft) =\<^sub>f (MFun f ?ts, concat ?sss))"
    unfolding id by simp
  also have "\<dots>"
  proof (rule eqf_MFunI)
    fix i
    assume i: "i < length ?ts"
    show "(bef @ C\<langle>t\<rangle> # aft) ! i =\<^sub>f (?ts ! i, ?sss ! i)"
      using More i
      by (cases "i < length bef", simp add: nth_append mctxt_of_term,
          cases "i = length bef", auto simp: nth_append mctxt_of_term)
  qed auto
  finally show ?case .
qed auto

lemma fill_holes_ctxt_main':
  assumes "num_holes C = Suc (length bef + length aft)"
  shows "\<exists> D. (\<forall> s. fill_holes C (bef @ s # aft) = D \<langle>s\<rangle>) \<and> (C = MFun f cs \<longrightarrow> D \<noteq> \<box>)"
  using assms
proof (induct C arbitrary: bef aft)
  case MHole
  show ?case
    by (rule exI[of _ \<box>], insert MHole, auto)
next
  case (MFun f cs)
  note IH = MFun(1)
  note holes = MFun(2)
  let ?p = "\<lambda> bef aft b a D cs s. map (\<lambda>i. fill_holes (cs ! i)
               (partition_holes (bef @ s # aft) cs ! i)) [0..<length cs] =
              b @ D\<langle>s\<rangle> # a"
  from holes IH
  have "\<exists> b D a. \<forall>s. ?p bef aft b a D cs s"
  proof (induct cs arbitrary: bef)
    case (Cons c ccs)
    have len: "length (c # ccs) = Suc (length ccs)" by simp
    show ?case 
    proof (cases "num_holes c \<le> length bef")
      case True
      then have "bef = take (num_holes c) bef @ drop (num_holes c) bef 
        \<and> length (take (num_holes c) bef) = num_holes c" by auto
      then obtain bc ba where bef: "bef = bc @ ba" and lbc: "length bc = num_holes c" by blast
      from Cons(2) have nh: "num_holes (MFun f ccs) = Suc (length ba + length aft)" unfolding bef
        by (simp add: lbc)
      from Cons(1)[OF nh Cons(3)] obtain b D a where IH: "\<And> s. ?p ba aft b a D ccs s" by auto
      show ?thesis unfolding len map_upt_Suc bef
        by (intro exI[of _ "fill_holes c bc # b"] exI[of _ D] exI[of _ a], insert IH lbc, auto)
    next
      case False
      then have "\<exists> la. num_holes c = Suc (length bef + la)" by arith
      then obtain la where nhc: "num_holes c = Suc (length bef + la)" ..
      from Cons(2) nhc have "length (take la aft) = la" by auto
      from Cons(3)[of c bef "take la aft", unfolded this, OF _ nhc]
      obtain D where D: "\<forall>s. fill_holes c (bef @ s # take la aft) = D\<langle>s\<rangle>" by auto
      show ?thesis unfolding len map_upt_Suc
        by (rule exI[of _ Nil], rule exI[of _ D], simp add: nhc D) 
    qed
  qed auto
  then obtain b D a where main: "\<And> s. ?p bef aft b a D cs s" by blast
  show ?case by (rule exI[of _ "More f b D a"], insert main, auto)
qed simp

lemma fill_holes_ctxt_main:
  assumes "num_holes C = Suc (length bef + length aft)"
  shows "\<exists> D. \<forall> s. fill_holes C (bef @ s # aft) = D \<langle> s \<rangle>"
  using assms fill_holes_ctxt_main' by fast

lemma fill_holes_ctxt:
  assumes nh: "num_holes C = length ss"
    and i: "i < length ss"
  obtains D where "\<And> s. fill_holes C (ss[i := s]) = D \<langle> s \<rangle>"
proof -
  from id_take_nth_drop[OF i] obtain bef aft where ss: "ss = bef @ ss ! i # aft" 
    and bef: "bef = take i ss" by blast
  from bef i have bef: "length bef = i" by auto
  note len = arg_cong[OF ss, of length]
  from len nh
  have "num_holes C = Suc (length bef + length aft)" by simp
  from fill_holes_ctxt_main[OF this] obtain D where id: "\<And> s. fill_holes C (bef @ s # aft) = D \<langle> s \<rangle>" by blast
  {
    fix s
    have "ss[i := s] = bef @ s # aft" unfolding arg_cong[OF ss, of "\<lambda> ss. ss[i := s]"]
      using i bef by auto
    with id[of s] have "fill_holes C (ss[i := s]) = D \<langle>s \<rangle>" by simp
  }
  then have main: "\<exists> D. \<forall> s. fill_holes C (ss[i := s]) = D \<langle>s \<rangle>" by blast
  assume "\<And> D. \<lbrakk>\<And>s. fill_holes C (ss[i := s]) = D\<langle>s\<rangle>\<rbrakk> \<Longrightarrow> thesis"
  with main show thesis by blast
qed

fun map_vars_mctxt :: "('v \<Rightarrow> 'w) \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('f, 'w) mctxt"
  where
    "map_vars_mctxt vw MHole = MHole" |
    "map_vars_mctxt vw (MVar v) = (MVar (vw v))" |
    "map_vars_mctxt vw (MFun f Cs) = MFun f (map (map_vars_mctxt vw) Cs)"

lemma map_vars_mctxt_id [simp]:
  "map_vars_mctxt (\<lambda> x. x) C = C"
  by (induct C, auto intro: nth_equalityI)

lemma num_holes_map_vars_mctxt [simp]:
  "num_holes (map_vars_mctxt vw C) = num_holes C"
proof (induct C)
  case (MFun f Cs)
  then show ?case by (induct Cs, auto)
qed auto

lemma map_vars_term_eq_fill:
  "t =\<^sub>f (C,ss) \<Longrightarrow> map_vars_term vw t =\<^sub>f (map_vars_mctxt vw C, map (map_vars_term vw) ss)"
proof (induct C arbitrary: t ss)
  case (MFun f Cs s ss)
  from eqf_MFunE[OF MFun(2)] obtain ts sss where s: "s = Fun f ts" and len: "length ts = length Cs" "length sss = length Cs" 
    and IH: "\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)" and ss: "ss = concat sss" by metis
  {
    fix i
    assume i: "i < length Cs"
    then have "Cs ! i \<in> set Cs" by auto
    from MFun(1)[OF this IH[OF i]] have "map_vars_term vw (ts ! i) =\<^sub>f (map_vars_mctxt vw (Cs ! i), map (map_vars_term vw) (sss ! i))" .
  } note IH = this
  show ?case unfolding map_vars_mctxt.simps ss map_concat s term.map
    by (rule eqf_MFunI, insert IH len, auto)
next
  case (MHole t ss)
  from eqfE[OF this]
  show ?case by (cases ss, auto)
next
  case (MVar v t ss)
  from eqfE[OF this]
  show ?case by (cases ss, auto)
qed

lemma map_vars_term_fill_holes:
  assumes nh: "num_holes C = length ss"
  shows "map_vars_term vw (fill_holes C ss) =
    fill_holes (map_vars_mctxt vw C) (map (map_vars_term vw) ss)"
proof -
  from eqfE[OF map_vars_term_eq_fill[OF eqfI[OF refl nh]]]
  show ?thesis by simp
qed

lemma split_term_eqf:
  "t =\<^sub>f (cap_till P t, uncap_till P t)"
proof (induct t)
  case (Fun f ts)
  show ?case
  proof (cases "P (Fun f ts)")
    case False
    then have "?thesis = (Fun f ts =\<^sub>f (MFun f (map (cap_till P) ts), concat (map (uncap_till P) ts)))"
      by simp
    also have "\<dots>"
    proof (rule eqf_MFunI)
      fix i
      presume "i < length ts"
      moreover then have "ts ! i \<in> set ts" by auto
      ultimately show "ts ! i =\<^sub>f (map (cap_till P) ts ! i, map (uncap_till P) ts ! i)"
        using Fun by auto
    qed simp_all
    finally show ?thesis .
  qed auto
qed auto

lemma fill_holes_cap_till_uncap_till_id [simp]:
  "fill_holes (cap_till P t) (uncap_till P t) = t"
proof -
  have "t =\<^sub>f (cap_till P t, uncap_till P t)" by (metis split_term_eqf)
  from eqfE [OF this] show ?thesis by simp
qed

lemma num_holes_cap_till [simp]:
  "num_holes (cap_till P t) = length (uncap_till P t)"
  using eqfE [OF split_term_eqf] by auto

fun split_vars :: "('f, 'v) term \<Rightarrow> (('f, 'v) mctxt \<times> 'v list)"
  where
    "split_vars (Var x) = (MHole, [x])" |
    "split_vars (Fun f ts) = (MFun f (map (fst \<circ> split_vars) ts), concat (map (snd \<circ> split_vars) ts))"

lemma split_vars_num_holes: "num_holes (fst (split_vars t)) = length (snd (split_vars t))"
proof (induct t)
  case (Fun f ts)
  then show ?case by (induct ts, auto)
qed simp

lemma split_vars_vars_term_list: "snd (split_vars t) = vars_term_list t"
proof (induct t)
  case (Fun f ts)
  then show ?case by (auto simp: vars_term_list.simps o_def, induct ts, auto)
qed (auto simp: vars_term_list.simps)

lemma split_vars_vars_term: "set (snd (split_vars t)) = vars_term t"
  using arg_cong[OF split_vars_vars_term_list[of t], of set] by auto

lemma split_vars_eqf_subst_map_vars_term:
  "t \<cdot> \<sigma> =\<^sub>f (map_vars_mctxt vw (fst (split_vars t)), map \<sigma> (snd (split_vars t)))"
proof (induct t)
  case (Fun f ts)
  have "?case = (Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)
    =\<^sub>f (MFun f (map (map_vars_mctxt vw \<circ> (fst \<circ> split_vars)) ts), concat (map (map \<sigma> \<circ> (snd \<circ> split_vars)) ts)))"
    by (simp add: map_concat)
  also have "..." 
  proof (rule eqf_MFunI, unfold length_map)
    fix i
    assume i: "i < length ts"
    then have mem: "ts ! i \<in> set ts" by auto
    show "map (\<lambda>t. t \<cdot> \<sigma>) ts ! i =\<^sub>f (map (map_vars_mctxt vw \<circ> (fst \<circ> split_vars)) ts ! i, map (map \<sigma> \<circ> (snd \<circ> split_vars)) ts ! i)"
      using Fun[OF mem] i by auto
  qed auto
  finally show ?case by simp
qed auto

lemma split_vars_eqf_subst: "t \<cdot> \<sigma> =\<^sub>f (fst (split_vars t), (map \<sigma> (snd (split_vars t))))"
  using split_vars_eqf_subst_map_vars_term[of t \<sigma> "\<lambda> x. x"] by simp

lemma split_vars_into_subst_map_vars_term:
  assumes split: "split_vars l = (C,xs)"
    and len: "length ts = length xs"
    and id: "\<And> i. i < length xs \<Longrightarrow> \<sigma> (xs ! i) = ts ! i"
  shows "l \<cdot> \<sigma> =\<^sub>f (map_vars_mctxt vw C,ts)"
proof -
  from split_vars_eqf_subst_map_vars_term[of l \<sigma> vw, unfolded split]
  have "l \<cdot> \<sigma> =\<^sub>f (map_vars_mctxt vw C, map \<sigma> xs)" by simp
  also have "map \<sigma> xs = ts"
    by (rule nth_equalityI, insert len id, auto)
  finally show ?thesis .
qed

lemma split_vars_into_subst:
  assumes split: "split_vars l = (C,xs)"
    and len: "length ts = length xs"
    and id: "\<And> i. i < length xs \<Longrightarrow> \<sigma> (xs ! i) = ts ! i"
  shows "l \<cdot> \<sigma> =\<^sub>f (C,ts)"
  using split_vars_into_subst_map_vars_term[OF split len id, of "\<lambda> x. x"] by simp

lemma eqf_funas_term:
  "t =\<^sub>f (C,ss) \<Longrightarrow> funas_term t = funas_mctxt C \<union> \<Union>(funas_term ` set ss)"
proof (induct C arbitrary: t ss)
  case (MFun f Cs t ss)
  from eqf_MFunE[OF MFun(2)] obtain ts sss where
    t: "t = Fun f ts" and len: "length ts = length Cs" "length sss = length Cs" 
    and args: "\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)"
    and ss: "ss = concat sss"  by auto
  let ?lhs = "\<Union> {funas_term (ts ! i) | i. i < length Cs}"
  let ?f1 = "\<lambda> i. funas_mctxt (Cs ! i)"
  let ?f2 = "\<lambda> i. \<Union>(funas_term ` set (sss ! i))"
  let ?f = "\<lambda> i. ?f1 i \<union> ?f2 i"
  {
    fix i
    assume i: "i < length Cs"
    then have mem: "Cs ! i \<in> set Cs" by auto
    note MFun(1)[OF mem args[OF i]]
  } note IH = this
  have "funas_term t = insert (f,length Cs) ?lhs"
    unfolding t using len by (auto simp: set_conv_nth)
  also have "?lhs = \<Union> {?f i | i. i < length Cs}" using IH by blast 
  also have "\<dots> = \<Union> {?f1 i | i. i < length Cs} \<union> \<Union> {?f2 i | i. i < length Cs}" by auto
  also have "insert (f,length Cs) \<dots> = (insert (f,length Cs) (\<Union> {?f1 i | i. i < length Cs})) \<union> \<Union> {?f2 i | i. i < length Cs}" by auto
  also have "insert (f,length Cs) (\<Union> {?f1 i | i. i < length Cs}) = funas_mctxt (MFun f Cs)"
    by (auto simp: set_conv_nth)
  also have "\<Union> {?f2 i | i. i < length Cs} = \<Union>(funas_term ` set ss)" unfolding ss len(2)[symmetric] 
    using set_conv_nth[of sss] by auto
  finally show ?case .
next
  case MVar
  from eqfE[OF this]
  show ?case by auto
next
  case MHole
  from eqfE[OF this] show ?case by (cases ss, auto)
qed 

lemma eqf_all_ctxt_closed_step:
  assumes ctxt: "all_ctxt_closed F R"
    and ass: "t =\<^sub>f (D,ss)" "\<And> i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> R" "length ss = length ts" "funas_term t \<subseteq> F"
    "\<Union> (funas_term ` set ts) \<subseteq> F"
  shows "(t, fill_holes D ts) \<in> R \<and> fill_holes D ts =\<^sub>f (D, ts)"
  using ass
proof (induct t "(D,ss)" rule: eq_fill.induct)
  case (eqfI t)
  from eqfI(2) eqfI(4)[unfolded eqfI(2)[symmetric]] eqfI(3,5,6)
  show ?case unfolding eqfI(1)
  proof (induct D ss ts rule: fill_holes_induct2)
    case (MVar v) then show ?case using all_ctxt_closed_sig_reflE[OF ctxt] by auto
  next
    case (MHole s' t') then show ?case by auto
  next
    case (MFun f Cs ss ts)
    let ?ss = "(map (\<lambda>i. fill_holes (Cs ! i) (partition_holes ss Cs ! i)) [0..<length Cs])"
    let ?ts = "(map (\<lambda>i. fill_holes (Cs ! i) (partition_holes ts Cs ! i)) [0..<length Cs])"
    note * = all_ctxt_closedD[OF ctxt, of f ?ts ?ss, unfolded length_map length_upt minus_nat.diff_0]
    show ?case unfolding fill_holes.simps MFun(4) concat_partition_by[OF MFun(1)] concat_partition_by[OF MFun(2)]
    proof (intro conjI eqfI *)
      fix i assume i: "i < length Cs"
      then have *: "i < length ?ss" "i < length ?ts" by auto
      from *(1) MFun(1,5) have g1: "funas_term (fill_holes (Cs ! i) (partition_holes ss Cs ! i)) \<subseteq> F"
        by (auto simp: subset_eq)
      with *(1) show "funas_term (?ss ! i) \<subseteq> F" by auto
      from *(2) MFun(2,6) have g2: "(\<Union>a\<in>set (partition_holes ts Cs ! i). funas_term a) \<subseteq> F"
        unfolding set_concat
        by (auto simp: subset_eq all_set_conv_all_nth[of "partition_holes ts Cs"])
      with *(2) MFun(1,2,5) show "funas_term (?ts ! i) \<subseteq> F"
        by (auto simp: funas_term_fill_holes_iff subset_eq)
      {
        fix j assume j: "j < length (partition_holes ts Cs ! i)"
        from partition_by_nth_nth[of "map num_holes Cs" ss i j]
          partition_by_nth_nth[of "map num_holes Cs" ts i j]
          i j MFun(1,2,4)
        have "(partition_holes ss Cs ! i ! j, partition_holes ts Cs ! i ! j) \<in> R" by simp
      }
      with i show "(?ss ! i, ?ts ! i) \<in> R" by (auto intro!: conjunct1[OF MFun(3)[OF i _ g1 g2]])
    next
      show "(f, length Cs) \<in> F" using MFun(5) by auto
    next
      show "Fun f ?ts =\<^sub>f (MFun f Cs, ts)" using MFun(2) by (intro eq_fill.intros) auto
    qed simp
  qed
qed

fun map_mctxt :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('g, 'v) mctxt"
  where
    "map_mctxt _ (MVar x) = (MVar x)" |
    "map_mctxt _ (MHole) = MHole" |
    "map_mctxt fg (MFun f Cs) = MFun (fg f) (map (map_mctxt fg) Cs)"

fun ground_mctxt :: "('f, 'v) mctxt \<Rightarrow> bool"
  where 
    "ground_mctxt (MVar _) = False" |
    "ground_mctxt MHole = True" |
    "ground_mctxt (MFun f Cs) = Ball (set Cs) ground_mctxt"

lemma ground_cap_till_funas [intro]:
  "ground_mctxt (cap_till_funas F t)"
  by (induct t) simp_all

lemma ground_eq_fill: "t =\<^sub>f (C,ss) \<Longrightarrow> ground t = (ground_mctxt C \<and> (\<forall> s \<in> set ss. ground s))" 
proof (induct C arbitrary: t ss)
  case (MVar x)
  from eqfE[OF this] show ?case by simp
next
  case (MHole t ss)
  from eqfE[OF this] show ?case by (cases ss, auto)
next
  case (MFun f Cs s ss)
  from eqf_MFunE[OF MFun(2)] obtain ts sss where s: "s = Fun f ts" and len: "length ts = length Cs" "length sss = length Cs" 
    and IH: "\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)" and ss: "ss = concat sss" by metis
  {
    fix i
    assume i: "i < length Cs"
    then have "Cs ! i \<in> set Cs" by simp
    from MFun(1)[OF this IH[OF i]]
    have "ground (ts ! i) = (ground_mctxt (Cs ! i) \<and> (\<forall>a\<in>set (sss ! i). ground a))" .
  } note IH = this
  note conv = set_conv_nth
  have "?case = ((\<forall>x\<in>set ts. ground x) = ((\<forall>x\<in>set Cs. ground_mctxt x) \<and> (\<forall>a\<in>set sss. \<forall>x\<in>set a. ground x)))"
    unfolding s ss by simp
  also have "..." unfolding conv[of ts] conv[of Cs] conv[of sss] len using IH by auto
  finally show ?case by simp
qed

lemma ground_fill_holes:
  assumes nh: "num_holes C = length ss"
  shows "ground (fill_holes C ss) = (ground_mctxt C \<and> (\<forall> s \<in> set ss. ground s))"
  by (rule ground_eq_fill[OF eqfI[OF refl nh]])

lemma split_vars_ground: "split_vars t = (C,xs) \<Longrightarrow> ground_mctxt C"
proof (induct t arbitrary: C xs)
  case (Fun f ts C xs)
  from Fun(2)[simplified] obtain Cs where C: "C = MFun f Cs" and Cs: "Cs = map (fst \<circ> split_vars) ts" by auto
  show ?case unfolding C ground_mctxt.simps
  proof
    fix C
    assume "C \<in> set Cs"
    from this[unfolded Cs] obtain t where t: "t \<in> set ts" and C: "C = fst (split_vars t)" unfolding o_def by auto
    from C obtain xs where split: "split_vars t = (C,xs)" by (cases "split_vars t", auto)
    show "ground_mctxt C"
      by (rule Fun(1)[OF t split]) 
  qed
qed auto

lemma split_vars_ground_vars:
  assumes "ground_mctxt C" and "num_holes C = length xs" 
  shows "split_vars (fill_holes C (map Var xs)) = (C, xs)"
  using assms
proof (induct C arbitrary: xs)
  case (MHole xs)
  then show ?case by (cases xs, auto)
next
  case (MFun f Cs xs)
  have "fill_holes (MFun f Cs) (map Var xs) =\<^sub>f (MFun f Cs, map Var xs)"
    by (rule eqfI, insert MFun(3), auto)
  from eqf_MFunE[OF this] 
  obtain ts xss where fh: "fill_holes (MFun f Cs) (map Var xs) = Fun f ts"
    and lent: "length ts = length Cs"
    and lenx: "length xss = length Cs"
    and args: "\<And>i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, xss ! i)"
    and id: "map Var xs = concat xss" by auto
  from arg_cong[OF id, of "map the_Var"] have id2: "xs = concat (map (map the_Var) xss)" 
    by (metis map_concat length_map map_nth_eq_conv term.sel(1))    
  {
    fix i
    assume i: "i < length Cs"
    then have mem: "Cs ! i \<in> set Cs" by auto
    with MFun(2) have ground: "ground_mctxt (Cs ! i)" by auto
    have "map Var (map the_Var (xss ! i)) = map id (xss ! i)" unfolding map_map o_def map_eq_conv
    proof
      fix x
      assume "x \<in> set (xss ! i)"
      with lenx i have "x \<in> set (concat xss)" by auto
      from this[unfolded id[symmetric]] show "Var (the_Var x) = id x" by auto
    qed
    then have idxss: "map Var (map the_Var (xss ! i)) = xss ! i" by auto
    note rec = eqfE[OF args[OF i]]
    note IH = MFun(1)[OF mem ground, of "map the_Var (xss ! i)", unfolded rec(2) idxss rec(1)[symmetric]]
    from IH have "split_vars (ts ! i) = (Cs ! i, map the_Var (xss ! i))" by auto
    note this idxss
  }
  note IH = this
  have "?case = (map fst (map split_vars ts) = Cs \<and> concat (map snd (map split_vars ts)) = concat (map (map the_Var) xss))"
    unfolding fh unfolding id2 by auto
  also have "\<dots>"
  proof (rule conjI[OF nth_equalityI arg_cong[of _ _ concat, OF nth_equalityI, rule_format]], unfold length_map lent lenx)
    fix i
    assume i: "i < length Cs" 
    with arg_cong[OF IH(2)[OF this], of "map the_Var"]
      IH[OF this] show "map snd (map split_vars ts) ! i = map (map the_Var) xss ! i" using lent lenx by auto
  qed (insert IH lent, auto)
  finally show ?case .
qed auto

lemma ground_map_mctxt[simp]: "ground_mctxt (map_mctxt fg C) = ground_mctxt C"
  by (induct C, auto)

lemma num_holes_map_mctxt[simp]: "num_holes (map_mctxt fg C) = num_holes C"
proof (induct C)
  case (MFun f Cs)
  then show ?case by (induct Cs, auto)
qed auto

lemma split_vars_map_mctxt:
  assumes split: "split_vars t = (map_mctxt fg C, xs)"
  shows "split_vars (fill_holes C (map Var xs)) = (C, xs)"
proof -
  from split_vars_ground[OF split] have ground: "ground_mctxt C" by simp
  from split_vars_num_holes[of t, unfolded split] have nh: "num_holes C = length xs" by auto
  show ?thesis
    by (rule split_vars_ground_vars[OF ground nh])
qed

lemma subst_eq_map_decomp:
  assumes "t \<cdot> \<sigma> = map_funs_term fg s"
  shows "\<exists> C xs \<delta>s. s =\<^sub>f (C,\<delta>s) \<and> split_vars t = (map_mctxt fg C, xs) \<and> (\<forall> i < length xs. 
    \<sigma> (xs ! i) = map_funs_term fg (\<delta>s ! i))" 
  using assms
proof (induct t arbitrary: s)
  case (Var x s)
  show ?case
    by (intro exI[of _ MHole] exI[of _ "[x]"] exI[of _ "[s]"], insert Var, auto)
next
  case (Fun g ts s)
  from Fun(2) obtain f ss where s: "s = Fun f ss" and g: "g = fg f" by (cases s, auto)
  from Fun(2)[unfolded s] have id: "map (\<lambda> t. t \<cdot> \<sigma>) ts = map (map_funs_term fg) ss" by auto
  from arg_cong[OF this, of length] have len: "length ts = length ss" by auto
  from map_nth_conv[OF id] have args: "\<And> i. i < length ts \<Longrightarrow> ts ! i \<cdot> \<sigma> = map_funs_term fg (ss ! i)" by auto
  let ?P = "\<lambda> C xs \<delta>s i. ss ! i =\<^sub>f (C, \<delta>s) \<and>
          split_vars (ts ! i) = (map_mctxt fg C, xs) \<and>
          (\<forall>i<length xs. \<sigma> (xs ! i) = map_funs_term fg (\<delta>s ! i))"
  {
    fix i
    assume i: "i < length ts"
    then have mem: "ts ! i \<in> set ts" by auto
    note IH = Fun(1)[OF this args[OF i]]
  }
  then have "\<forall> i. \<exists> C xs \<delta>s. i < length ts \<longrightarrow> ?P C xs \<delta>s i" by blast
  from choice[OF this] obtain Cs where "\<forall> i. \<exists> xs \<delta>s. i < length ts \<longrightarrow> ?P (Cs i) xs \<delta>s i" by blast
  from choice[OF this] obtain xss where "\<forall> i. \<exists> \<delta>s. i < length ts \<longrightarrow> ?P (Cs i) (xss i) \<delta>s i" by blast
  from choice[OF this] obtain \<delta>ss where IH: "\<And> i. i < length ts \<Longrightarrow> ?P (Cs i) (xss i) (\<delta>ss i) i" by blast
  let ?n = "[0 ..< length ts]"
  let ?Cs = "map Cs ?n"
  let ?C = "MFun f ?Cs"
  let ?xs = "concat (map xss ?n)"
  let ?\<delta>s = "concat (map \<delta>ss ?n)"
  let ?g = "fg f"
  show ?case unfolding s g 
  proof (rule exI[of _ ?C], rule exI[of _ ?xs], rule exI[of _ ?\<delta>s], intro conjI)
    show "Fun f ss =\<^sub>f (?C, ?\<delta>s)" 
      by (rule eqf_MFunI, insert IH len, auto)
  next
    have 
      "(split_vars (Fun ?g ts) = (map_mctxt fg ?C, ?xs)) 
        = (map (fst \<circ> split_vars) ts = map (map_mctxt fg \<circ> Cs) [0..<length ss] 
          \<and>concat (map (snd \<circ> split_vars) ts) = ?xs)" 
      (is "?goal = _")
      using len by auto
    also have "\<dots>"
      by (rule conjI[OF nth_map_conv arg_cong[of _ _ concat, OF nth_equalityI]], insert IH len, auto)
    finally show ?goal .
  next
    show "\<forall> i < length ?xs. \<sigma> (?xs ! i) = map_funs_term fg (?\<delta>s ! i)"
    proof (rule concat_all_nth, unfold length_map length_upt)
      fix i
      assume "i < length ts - 0"
      then have i: "i < length ts" by auto
      from IH[OF i] have "split_vars (ts ! i) = (map_mctxt fg (Cs i), xss i)" by blast
      from split_vars_map_mctxt[OF this] split_vars_num_holes[of "fill_holes (Cs i) (map Var (xss i))"]
      have len: "length (xss i) = num_holes (Cs i)" by simp
      also have "\<dots> = length (\<delta>ss i)" by (rule eqfE(2), insert IH[OF i], auto)
      finally 
      show "length (map xss [0..<length ts] ! i) = length (map \<delta>ss [0..<length ts] ! i)" using i by auto
    qed (insert IH, auto)
  qed
qed

lemma map_funs_term_fill_holes:
  "num_holes C = length ss \<Longrightarrow>
    map_funs_term fg (fill_holes C ss) =\<^sub>f (map_mctxt fg C, map (map_funs_term fg) ss)"
proof (induct C arbitrary: ss)
  case (MHole ss)
  then show ?case by (cases ss, auto)
next
  case MVar then show ?case by auto
next
  case (MFun f Cs ss)
  from MFun(2) have "fill_holes (MFun f Cs) ss =\<^sub>f (MFun f Cs, ss)" by auto
  from eqf_MFunE[OF this] obtain ts sss where fh: "fill_holes (MFun f Cs) ss = Fun f ts"
    and lts: "length ts = length Cs"
    and lsss: "length sss = length Cs"
    and args: "\<And>i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)"
    and sss: "ss = concat sss" by auto
  {
    fix i
    assume i: "i < length Cs"
    then have mem: "Cs ! i \<in> set Cs" by auto
    from MFun(1)[OF mem]  eqfE[OF args[OF i]] have 
      "map_funs_term fg (ts ! i) =\<^sub>f (map_mctxt fg (Cs ! i), map (map_funs_term fg) (sss ! i))" by auto
  } note IH = this
  show ?case unfolding fh 
    unfolding map_mctxt.simps sss map_concat term.simps
  proof (rule eqf_MFunI, unfold length_map)
    fix i
    assume i: "i < length Cs"
    have "(map (map_funs_term fg) ts ! i =\<^sub>f (map (map_mctxt fg) Cs ! i, map (map (map_funs_term fg)) sss ! i)) =
      (map_funs_term fg (ts ! i) =\<^sub>f (map_mctxt fg (Cs ! i), map (map_funs_term fg) (sss ! i)))" (is "?goal = _")
      using i lts lsss by auto
    also have "\<dots>" by (rule IH[OF i])
    finally show ?goal .
  qed (auto simp: lsss lts)
qed

lemma eqf_MVarE:
  assumes "s =\<^sub>f (MVar x,ss)"  
  shows "s = Var x" "ss = []" 
  by (insert eqfE[OF assms], cases s; cases ss, auto)+


lemma eqf_imp_subt:
  assumes s: "s =\<^sub>f (C,ts)"
    and t: "t \<in> set ts"
  shows "s \<unrhd> t"
proof -
  from t obtain bef aft where ts: "ts = bef @ t # aft"
    by (metis split_list)
  note s = eqfE[OF s[unfolded ts], simplified]
  from fill_holes_ctxt_main[OF s(2)] obtain D where "fill_holes C (bef @ t # aft) = D\<langle>t\<rangle>" by auto
  from this[folded s(1)] show ?thesis by auto
qed

lemma eqf_MFun_imp_strict_subt:
  assumes s:"s =\<^sub>f (MFun f cs, ts)"
    and t:"t \<in> set ts"
  shows "s \<rhd> t"
proof -
  from t obtain bef aft where ts: "ts = bef @ t # aft"
    by (metis split_list)
  from eqfE[OF s[unfolded ts]] have s: "s = fill_holes (MFun f cs) (bef @ t # aft)"
    "num_holes (MFun f cs) = Suc (length bef + length aft)" by auto
  from fill_holes_ctxt_main'[OF s(2)] obtain D 
    where D:"fill_holes (MFun f cs) (bef @ t # aft) = D\<langle>t\<rangle>" and "D \<noteq> \<box>" by blast
  from this[folded s(1)] show ?thesis by auto
qed

fun poss_mctxt :: "('f, 'v) mctxt \<Rightarrow> pos set"
  where
    "poss_mctxt (MVar x) = {[]}" |
    "poss_mctxt MHole = {}" |
    "poss_mctxt (MFun f cs) = {[]} \<union> \<Union>(set (map (\<lambda> i. (\<lambda> p. i # p) ` poss_mctxt (cs ! i)) [0 ..< length cs]))"

lemma poss_mctxt_simp [simp]:
  "poss_mctxt (MFun f cs) = {[]} \<union> {i # p | i p. i < length cs \<and> p \<in> poss_mctxt (cs ! i)}"
  by auto
declare poss_mctxt.simps(3)[simp del]

lemma poss_mctxt_map_vars_mctxt [simp]:
  "poss_mctxt (map_vars_mctxt f C) = poss_mctxt C"
  by (induct C) auto

fun hole_poss :: "('f, 'v) mctxt \<Rightarrow> pos set"
  where
    "hole_poss (MVar x) = {}" |
    "hole_poss MHole = {[]}" |
    "hole_poss (MFun f cs) = \<Union>(set (map (\<lambda> i. (\<lambda> p. i # p) ` hole_poss (cs ! i)) [0 ..< length cs]))"

lemma hole_poss_simp [simp]:
  "hole_poss (MFun f cs) = {i # p | i p. i < length cs \<and> p \<in> hole_poss (cs ! i)}"
  by auto
declare hole_poss.simps(3)[simp del]

lemma hole_poss_empty_iff_num_holes_0: "hole_poss C = {} \<longleftrightarrow> num_holes C = 0" 
  by (induct C; fastforce simp: set_conv_nth)

lemma mctxt_of_term_fill_holes [simp]:
  "fill_holes (mctxt_of_term t) [] = t"
proof (induct t)
  case (Fun f ts) 
  then have "fill_holes (mctxt_of_term (Fun f ts)) [] = Fun f (map (\<lambda>i. (ts!i)) [0..<length ts])"
    unfolding mctxt_of_term.simps partition_holes_fill_holes_conv partition_by_Nil map_map by auto
  also have "... = Fun f ts" using map_nth by auto
  ultimately show ?case by auto
qed (auto)

lemma hole_pos_not_in_poss_mctxt:
  assumes "p \<in> hole_poss C"
  shows "p \<notin> poss_mctxt C"
  using assms
  by (induct C arbitrary: p) auto

lemma hole_pos_in_filled_fun_poss:
  assumes "is_Fun t"
  shows "hole_pos E \<in> fun_poss ((E \<cdot>\<^sub>c \<sigma>)\<langle>t \<cdot> \<sigma>\<rangle>)"
  using assms
  by (induct E) (auto simp: append_Cons_nth_middle)

fun
  subst_apply_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) mctxt" (infixl "\<cdot>mc" 67)
  where
    "MHole \<cdot>mc _ = MHole" |
    "(MVar x) \<cdot>mc \<sigma> = mctxt_of_term (\<sigma> x)" |
    "(MFun f cs) \<cdot>mc \<sigma> = MFun f [c \<cdot>mc \<sigma> . c \<leftarrow> cs]"

lemma subst_apply_mctxt_compose: "C \<cdot>mc \<sigma> \<cdot>mc \<delta> = C \<cdot>mc \<sigma> \<circ>\<^sub>s \<delta>"
proof (induct C)
  case (MVar x)
  define t where "t = \<sigma> x" 
  show ?case by (simp add: t_def[symmetric] subst_compose_def, induct t, auto)
qed auto

lemma subst_apply_mctxt_cong: "(\<And> x. x \<in> vars_mctxt C \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> C \<cdot>mc \<sigma> = C \<cdot>mc \<tau>"
  by (induct C, auto)  

lemma vars_mctxt_subst: "vars_mctxt (C \<cdot>mc \<sigma>) = \<Union> (vars_term ` \<sigma> ` vars_mctxt C)" 
  by (induct C, auto)


lemma subst_apply_mctxt_numholes: 
  shows "num_holes (c \<cdot>mc \<sigma>) = num_holes c"
proof (induct c arbitrary: \<sigma>) 
  case (MFun f cs)
  have "num_holes (MFun f cs \<cdot>mc \<sigma>) = sum_list [num_holes (c \<cdot>mc \<sigma>) . c \<leftarrow> cs]"
    unfolding subst_apply_mctxt.simps num_holes.simps map_map comp_def by auto
  also have "... = sum_list [num_holes c . c \<leftarrow> cs]" using MFun(1) 
    by (metis (lifting, no_types) map_cong)
  ultimately show ?case by auto
qed (auto)

lemma subst_apply_mctxt_fill_holes: 
  assumes nh: "num_holes c = length ts"
  shows "(fill_holes c ts) \<cdot> \<sigma> = fill_holes (c \<cdot>mc \<sigma>) [ ti \<cdot> \<sigma> . ti \<leftarrow> ts]"
  using nh
proof (induct c arbitrary: ts)
  case MHole 
  then obtain t where ts: "ts = [t]" 
    unfolding num_holes.simps unfolding One_nat_def using Suc_length_conv length_0_conv by metis
  show ?case unfolding ts by simp
next 
  case (MVar x)
  then have ts: "ts = []" using length_0_conv by auto 
  show ?case unfolding ts by auto
next
  case (MFun f cs) 
  note IH = MFun(1)
  note nh = MFun(2)[unfolded num_holes.simps]
  let ?c = "MFun f cs"
  let ?cs\<sigma> = "map (\<lambda>c. c \<cdot>mc \<sigma>) cs"

  {
    fix i
    assume i: "i < length cs"
    have nh_map: "\<And> j. j < length cs \<Longrightarrow> num_holes (cs!j) = num_holes (?cs\<sigma> ! j)" 
      using nth_map subst_apply_mctxt_numholes by metis

    have "fill_holes (cs ! i) (partition_holes ts cs ! i) \<cdot> \<sigma> = 
      fill_holes ((cs ! i) \<cdot>mc \<sigma>) (partition_holes [ ti \<cdot> \<sigma> . ti \<leftarrow> ts] cs ! i)"
      using IH [OF nth_mem [OF i]] and nh and i by auto
    also have "... = fill_holes (?cs\<sigma> ! i) (partition_holes [ti \<cdot> \<sigma> . ti \<leftarrow> ts] ?cs\<sigma> ! i)"
      unfolding nth_map[OF i] using partition_holes_map_ctxt[OF _ nh_map] length_map by metis
    ultimately have "fill_holes (cs ! i) (partition_holes ts cs ! i) \<cdot> \<sigma> = fill_holes (?cs\<sigma> ! i) (partition_holes [ti \<cdot> \<sigma> . ti \<leftarrow> ts] ?cs\<sigma> ! i)"
      by auto
  } note ith = this

  have "fill_holes ?c ts \<cdot> \<sigma> = Fun f [fill_holes (?cs\<sigma> ! i) (partition_holes [ ti \<cdot> \<sigma> . ti \<leftarrow> ts] ?cs\<sigma> ! i) . i \<leftarrow> [0..<length cs]]"  
    unfolding partition_holes_fill_holes_conv map_map using ith using comp_def  by auto 
  also have "... = fill_holes (?c \<cdot>mc \<sigma>) [ ti \<cdot> \<sigma> . ti \<leftarrow> ts]"  
    unfolding subst_apply_mctxt.simps partition_holes_fill_holes_conv length_map ..
  ultimately show ?case by auto
qed

lemma subst_apply_mctxt_sound: 
  assumes "t =\<^sub>f (c,ts)"
  shows "t \<cdot> \<sigma> =\<^sub>f (c \<cdot>mc \<sigma>, [ ti \<cdot> \<sigma> . ti \<leftarrow> ts])"
proof (rule eqfI, insert subst_apply_mctxt_numholes subst_apply_mctxt_fill_holes[OF eqfE(2)[OF assms]] eqfE[OF assms] eqfE(2)[OF assms, symmetric], auto) qed

fun fill_holes_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt list \<Rightarrow> ('f, 'v) mctxt"
  where
    "fill_holes_mctxt (MVar x) _ = MVar x" |
    "fill_holes_mctxt MHole [] = MHole" |
    "fill_holes_mctxt MHole [t] = t" |
    "fill_holes_mctxt (MFun f cs) ts = (MFun f (map (\<lambda> i. fill_holes_mctxt (cs ! i) 
    (partition_holes ts cs ! i)) [0 ..< length cs]))"

lemma fill_holes_mctxt_Nil [simp]:
  "fill_holes_mctxt C [] = C"
  by (induct C) (auto intro: nth_equalityI)

lemma map_fill_holes_mctxt_zip [simp]:
  assumes "length ts = n"
  shows "map (\<lambda>(x, y). fill_holes_mctxt x y) (zip (map mctxt_of_term ts) (replicate n [])) =
    map mctxt_of_term ts"
  using assms by (induct ts arbitrary: n) auto

lemma fill_holes_mctxt_MHole [simp]:
  "length ts = Suc 0 \<Longrightarrow> fill_holes_mctxt MHole ts = hd ts"
  by (cases ts) simp_all

lemma partition_holes_fill_holes_mctxt_conv:
  "fill_holes_mctxt (MFun f Cs) ts =
    MFun f [fill_holes_mctxt (Cs ! i) (partition_holes ts Cs ! i). i \<leftarrow> [0 ..< length Cs]]"
  by (simp add: partition_by_nth take_map)

lemma partition_holes_fill_holes_mctxt_conv':
  "fill_holes_mctxt (MFun f Cs) ts =
    MFun f (map (case_prod fill_holes_mctxt) (zip Cs (partition_holes ts Cs)))"
  unfolding zip_nth_conv [of Cs "partition_holes ts Cs", simplified]
    and partition_holes_fill_holes_mctxt_conv by simp

lemma fill_holes_mctxt_mctxt_of_ctxt_mctxt_of_term [simp]:
  "fill_holes_mctxt (mctxt_of_ctxt C) [mctxt_of_term t] = mctxt_of_term (C\<langle>t\<rangle>)"
  by (induct C arbitrary: t)
    (simp_all del: fill_holes_mctxt.simps add: partition_holes_fill_holes_mctxt_conv')

lemma fill_holes_mctxt_mctxt_of_ctxt_MHole [simp]:
  "fill_holes_mctxt (mctxt_of_ctxt C) [MHole] = mctxt_of_ctxt C"
  by (induct C) (simp_all del: fill_holes_mctxt.simps add: partition_holes_fill_holes_mctxt_conv')

lemma partition_holes_fill_holes_conv':
  "fill_holes (MFun f Cs) ts =
    Fun f (map (case_prod fill_holes) (zip Cs (partition_holes ts Cs)))"
  unfolding zip_nth_conv [of Cs "partition_holes ts Cs", simplified]
    and partition_holes_fill_holes_conv by simp

lemma fill_holes_mctxt_MFun_replicate_length [simp]:
  "fill_holes_mctxt (MFun c (replicate (length Cs) MHole)) Cs = MFun c Cs"
  unfolding partition_holes_fill_holes_mctxt_conv'
  by (induct Cs) simp_all

lemma fill_holes_MFun_replicate_length [simp]:
  "fill_holes (MFun c (replicate (length ts) MHole)) ts = Fun c ts"
  unfolding partition_holes_fill_holes_conv'
  by (induct ts) simp_all

lemma funas_mctxt_fill_holes_mctxt [simp]:
  assumes "num_holes C = length Ds"
  shows "funas_mctxt (fill_holes_mctxt C Ds) = funas_mctxt C \<union> \<Union>(set (map funas_mctxt Ds))"
    (is "?f C Ds = ?g C Ds")
  using assms
proof (induct C arbitrary: Ds)
  case MHole
  then show ?case by (cases Ds) simp_all
next
  case (MFun f Cs)
  then have num_holes: "sum_list (map num_holes Cs) = length Ds" by simp
  let ?ys = "partition_holes Ds Cs"
  have "\<And>i. i < length Cs \<Longrightarrow> ?f (Cs ! i) (?ys ! i) = ?g (Cs ! i) (?ys ! i)"
    using MFun by (metis nth_mem num_holes.simps(3) length_partition_holes_nth)
  then have "(\<Union>i \<in> {0 ..< length Cs}. ?f (Cs ! i) (?ys ! i)) =
    (\<Union>i \<in> {0 ..< length Cs}. ?g (Cs ! i) (?ys ! i))" by simp
  then show ?case
    using num_holes
    unfolding partition_holes_fill_holes_mctxt_conv
    by (simp add: UN_Un_distrib UN_upt_len_conv [of _ _ "\<lambda>x. \<Union>(set x)"] UN_set_partition_by_map)
qed simp

lemma fill_holes_mctxt_MFun:
  assumes lCs: "length Cs = length ts"
    and lss: "length ss = length ts"
    and rec: "\<And> i. i < length ts \<Longrightarrow> num_holes (Cs ! i) = length (ss ! i) \<and> fill_holes_mctxt (Cs ! i) (ss ! i) = ts ! i"
  shows "fill_holes_mctxt (MFun f Cs) (concat ss) = MFun f ts" 
  unfolding fill_holes_mctxt.simps mctxt.simps
  by (rule conjI[OF refl], rule fill_holes_arbitrary[OF lCs lss rec])

lemma num_holes_fill_holes_mctxt: 
  assumes "num_holes C = length Ds"
  shows "num_holes (fill_holes_mctxt C Ds) = sum_list (map num_holes Ds)"
  using assms
proof (induct C arbitrary: Ds)
  case MHole
  then show ?case by (cases Ds) simp_all
next
  case (MFun f Cs)
  then have *: "map (num_holes \<circ> (\<lambda>i. fill_holes_mctxt (Cs ! i) (partition_holes Ds Cs ! i))) [0..<length Cs] =
    map (\<lambda>i. sum_list (map num_holes (partition_holes Ds Cs ! i))) [0 ..< length Cs]"
    and "sum_list (map num_holes Cs) = length Ds"
    by simp_all
  then show ?case
    using map_upt_len_conv [of "\<lambda>x. sum_list (map num_holes x)" "partition_holes Ds Cs"]
    unfolding partition_holes_fill_holes_mctxt_conv by (simp add: *)
qed simp

lemma fill_holes_mctxt_fill_holes: 
  assumes len_ds: "length ds = num_holes c"
    and nh: "num_holes (fill_holes_mctxt c ds) = length ss"
  shows "fill_holes (fill_holes_mctxt c ds) ss =
    fill_holes c [fill_holes (ds ! i) (partition_holes ss ds ! i). i \<leftarrow> [0 ..< num_holes c]]"
  using assms(1)[symmetric] assms(2)
proof (induct c ds arbitrary: ss rule: fill_holes_induct)
  case (MFun f Cs ds ss)
  define qs where "qs = map (\<lambda>i. fill_holes_mctxt (Cs ! i) (partition_holes ds Cs ! i)) [0..<length Cs]"
  then have qs: "\<And>i. i < length Cs \<Longrightarrow> fill_holes_mctxt (Cs ! i) (partition_holes ds Cs ! i) = qs ! i"
    "length qs = length Cs" by auto
  define zs where "zs = map (\<lambda>i. fill_holes (ds ! i) (partition_holes ss ds ! i)) [0..<length ds]"
  {
    fix i assume i: "i < length Cs"
    from MFun(1) have *: "map length (partition_holes ds Cs) = map num_holes Cs" by auto
    have **: "length ss = sum_list (map sum_list (partition_holes (map num_holes ds) Cs))"
      using MFun(1) MFun(3)[symmetric] num_holes_fill_holes_mctxt[of "MFun f Cs" ds]
      by (auto simp: comp_def map_map_partition_by[symmetric])
    have "partition_by (partition_by ss
        (map (\<lambda>i. num_holes (fill_holes_mctxt (Cs ! i) (partition_holes ds Cs ! i))) [0..<length Cs]) ! i)
        (partition_holes (map num_holes ds) Cs ! i) = partition_holes (partition_holes ss ds) Cs ! i"
      using i MFun(1) MFun(3) partition_by_partition_by[OF **]
      by (auto simp: comp_def num_holes_fill_holes_mctxt
          intro!: arg_cong[of _ _ "\<lambda>x. partition_by (partition_by ss x ! _) _"] nth_equalityI)
    then have "map (\<lambda>j. fill_holes (partition_holes ds Cs ! i ! j)
        (partition_holes (partition_holes ss qs ! i)
        (partition_holes ds Cs ! i) ! j)) [0..<num_holes (Cs ! i)] =
        partition_holes zs Cs ! i"
      using MFun(1,3)
      by (auto simp: zs_def qs_def i comp_def partition_by_nth_nth intro: nth_equalityI)
  }
  then show ?case using MFun by (simp add: qs_def [symmetric] qs zs_def [symmetric])
qed auto

lemma fill_holes_mctxt_sound:
  assumes len_ds: "length ds = num_holes c"
    and len_sss: "length sss = num_holes c"
    and len_ts: "length ts = num_holes c"
    and insts: "\<And> i. i < length ds \<Longrightarrow> ts!i =\<^sub>f (ds!i, sss!i)"
  shows "fill_holes c ts =\<^sub>f (fill_holes_mctxt c ds, concat sss)"
proof (rule eqfI)
  note l_nh_i = eqfE(2)[OF insts]

  from partition_holes_concat_id[OF _ l_nh_i] len_ds len_sss
  have concat_sss: "partition_holes (concat sss) ds = sss" by auto

  then show nh: "num_holes (fill_holes_mctxt c ds) = length (concat sss)"
    unfolding num_holes_fill_holes_mctxt [OF len_ds [symmetric]] length_concat
    by (metis l_nh_i len_ds len_sss nth_map_conv)  

  have ts: "ts = [fill_holes (ds ! i) (partition_holes (concat sss) ds ! i) . i \<leftarrow> [0..<num_holes c]]" (is "_ = ?fhs")
  proof (rule nth_equalityI)
    show l_fhs: "length ts = length ?fhs" unfolding length_map
      by (metis diff_zero len_ts length_upt)
    fix i
    assume i: "i < length ts"
    then have i': "i < length [0..<num_holes c]" 
      by (metis diff_zero len_ts length_upt)
    show "ts!i = ?fhs ! i"
      unfolding nth_map[OF i']
      using eqfE(1)[OF insts[unfolded len_ds, OF i[unfolded len_ts]]] 
      by (metis concat_sss i' len_ds len_sss map_nth nth_map)
  qed 
  note ts = this

  show "fill_holes c ts = fill_holes (fill_holes_mctxt c ds) (concat sss)"
    unfolding fill_holes_mctxt_fill_holes[OF len_ds nh] ts ..
qed

lemma poss_mctxt_fill_holes_mctxt:
  assumes "p \<in> poss_mctxt C"
  shows "p \<in> poss_mctxt (fill_holes_mctxt C Cs)"
  using assms
proof (induct p arbitrary: C Cs)
  case (Cons a p C Cs)
  thus ?case by (cases C, auto)
next
  case (Nil C Cs)
  thus ?case by (cases C, auto)
qed

fun compose_mctxt :: "('f, 'v) mctxt \<Rightarrow> nat \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt"
  where
    "compose_mctxt C i Ci =
    fill_holes_mctxt C [(if i = j then Ci else MHole). j \<leftarrow> [0 ..< num_holes C]]"

lemma funas_mctxt_compose_mctxt [simp]:
  assumes "i < num_holes C"
  shows "funas_mctxt (compose_mctxt C i D) = funas_mctxt C \<union> funas_mctxt D"
proof -
  let ?Ds = "[(if i = j then D else MHole). j \<leftarrow> [0 ..< num_holes C]]"
  have "num_holes C = length ?Ds" by simp
  then show ?thesis using assms by (auto split: if_splits) 
qed

lemma compose_mctxt_sound:
  assumes s: "s =\<^sub>f (C, bef @ si # aft)"
    and si: "si =\<^sub>f (Ci, ts)"
    and i: "i = length bef"
  shows "s =\<^sub>f (compose_mctxt C i Ci, bef @ ts @ aft)"
proof -
  let ?Cs = "[ if i = j then Ci else MHole . j \<leftarrow> [0..<num_holes C]]"
  let ?ts = "bef @ si # aft"
  let ?sss = "[ [b]. b \<leftarrow> bef ] @ (ts # [ [a]. a \<leftarrow> aft])"

  have 
    l_Cs : "length ?Cs = num_holes C" and
    l_ts : "length ?ts = num_holes C" and
    l_sss : "length ?sss = num_holes C"
    unfolding length_append length_map list.size(4) using eqfE(2)[OF s] by auto

  have i_le_nh: "i < num_holes C" unfolding i eqfE(2)[OF s] length_append by (auto iff: trans_less_add1)
  have concat_sss: "concat ?sss = bef @ ts @ aft" by auto

  {
    fix j
    assume j: "j < i"
    then have j': "j < length [0..<num_holes C]" using i_le_nh length_upt by auto
    have "?sss!j = [bef!j]" by (metis append_Cons_nth_left i j length_map nth_map) 
    moreover have "?ts!j = bef!j" by (metis append_Cons_nth_left i j)
    moreover from nth_map[OF j'] j' j have "?Cs!j = MHole" by force
    ultimately have "?ts!j =\<^sub>f (?Cs!j,?sss!j)" using eqfI by auto
  } note j_le_i = this

  from i_le_nh have "?Cs!i = Ci" by auto
  moreover from i_le_nh have "?sss!i = ts" by (metis i length_map nth_append_length)
  moreover have "?ts!i = si" using nth_append_length i by auto
  ultimately have j_eq_i: "?ts!i =\<^sub>f (?Cs!i,?sss!i)" using si by auto

  {
    fix j
    assume j: "j > i" and j': "j < num_holes C"
    then have j'': "j < length [0..<num_holes C]" by auto

    have j''': "(j - i) - 1 < length aft" using 
        j'[unfolded eqfE(2)[OF s] length_append[of bef] list.size(4)] j 
      unfolding i by auto

    from nth_append[of "[ [b]. b \<leftarrow> bef ]" _ j, unfolded length_map[of _ bef] i[symmetric]] 
    have "?sss!j = (ts # [ [a]. a \<leftarrow> aft]) ! (j - i)"  using j by auto
    moreover have "... = [ [a]. a \<leftarrow> aft] ! ((j - i) - 1)" using nth_Cons_pos j by simp
    moreover have "... = [aft ! ((j - i) - 1)]" using j''' length_map nth_map by auto
    ultimately have sssj: "?sss!j = [aft ! ((j - i) - 1)]" by auto

    have Csj: "?Cs!j = MHole" using nth_map[OF j''] j'' j  by force

    have "?ts!j = (si # aft) ! (j - i)" unfolding nth_append[of bef] i[symmetric] using j by simp
    moreover have "... = aft ! ((j - i) - 1)" by (metis j neq0_conv nth_Cons' zero_less_diff)
    ultimately have "?ts!j = aft ! ((j - i) - 1)" by auto
    then have "?ts!j =\<^sub>f (?Cs!j,?sss!j)" using sssj Csj by auto
  } note j_gr_i = this  

  from j_le_i j_eq_i j_gr_i have "\<And> j. j < length ?Cs \<Longrightarrow> ?ts!j =\<^sub>f (?Cs!j,?sss!j)" 
    using l_Cs linorder_neqE_nat by metis

  from fill_holes_mctxt_sound[OF l_Cs l_sss l_ts this, unfolded concat_sss, folded compose_mctxt.simps]
  show ?thesis unfolding eqfE(1)[OF s] by simp
qed

fun mctxt_fill_partially_mctxts :: "('f, 'v) term list \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) mctxt list"
  where 
    "mctxt_fill_partially_mctxts [] ts = map mctxt_of_term ts" |
    "mctxt_fill_partially_mctxts (s # ss) (t # ts) = 
    (if s = t then (MHole # mctxt_fill_partially_mctxts ss ts) 
    else (mctxt_of_term t # mctxt_fill_partially_mctxts (s # ss) ts))"

fun
  mctxt_fill_partially_fills ::
  "('f, 'v) term list \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term list list"
  where 
    "mctxt_fill_partially_fills [] ts = map (const []) ts" |
    "mctxt_fill_partially_fills (s # ss) (t # ts) = 
    (if s = t then ([s] # mctxt_fill_partially_fills ss ts) 
    else ([] # mctxt_fill_partially_fills (s # ss) ts))"

lemma mctxt_fill_partially_mctxts_length [simp]:
  assumes "subseq ss ts"
  shows "length (mctxt_fill_partially_mctxts ss ts) = length ts"
  using assms by (induct rule: subseq_induct2, auto)

lemma mctxt_fill_partially_fills_length [simp]:
  assumes "subseq ss ts"
  shows "length (mctxt_fill_partially_fills ss ts) = length ts"
  using assms by (induct rule: subseq_induct2, auto)

lemma mctxt_fill_partially_numholes:
  assumes "subseq ss ts"
  shows "sum_list [num_holes ci . ci \<leftarrow> mctxt_fill_partially_mctxts ss ts] = length ss"
proof (induct ss ts rule: subseq_induct2, goal_cases)
  case (3 s ss ts)
  have ls_one: "\<And> as. sum_list (1 # as) = sum_list as + Suc 0" 
    by (metis One_nat_def Suc_eq_plus1 Suc_eq_plus1_left sum_list_simps(2))
  from 3 show ?case
    unfolding mctxt_fill_partially_mctxts.simps list.size
    by (metis (full_types) One_nat_def Suc_eq_plus1 ls_one list.map(2) num_holes.simps(2))
next
  case (4 s ss t ts)
  have ls_zero: "\<And> as. sum_list (0 # as) = sum_list as" by (metis sum_list_simps(2) monoid_add_class.add.left_neutral) 
  have else: 
    "mctxt_fill_partially_mctxts (s # ss) (t # ts) = mctxt_of_term t # mctxt_fill_partially_mctxts (s # ss) ts" 
    using 4(1) by auto
  show ?case 
    unfolding else list.map(2) num_holes_mctxt_of_term ls_zero 4(5) ..
qed (auto iff: assms)

lemma mctxt_fill_partially_sound:
  assumes sl: "subseq ss ts"
  shows "\<And> i. i < length ts \<Longrightarrow> ts!i =\<^sub>f (mctxt_fill_partially_mctxts ss ts ! i, mctxt_fill_partially_fills ss ts ! i)"
proof (rule eqfI, goal_cases)
  let ?zipped= "zip (mctxt_fill_partially_mctxts ss ts) (mctxt_fill_partially_fills ss ts)"

  have l: "length ?zipped = length ts" 
    unfolding length_zip mctxt_fill_partially_mctxts_length[OF sl] mctxt_fill_partially_fills_length[OF sl] by auto

  have fh: "ts = map (\<lambda> (ci,tsi) . fill_holes ci tsi) ?zipped" 
  proof (induct ss ts rule: subseq_induct2, goal_cases)
    case (2 ts) then show ?case
      by (induct ts, insert mctxt_of_term_fill_holes, auto)
  qed (insert sl, auto)

  have nh: "list_all (\<lambda> (ci,tsi) . num_holes ci = length tsi) ?zipped"
  proof (induct ss ts rule: subseq_induct2, goal_cases)
    case (2 ts) then show ?case
      by (induct ts, insert num_holes_mctxt_of_term, auto)
  qed (insert sl, auto)

  { 
    fix i
    assume "i < length ts"
    then have 
      i1: "i < length (mctxt_fill_partially_mctxts ss ts)" and
      i2: "i < length (mctxt_fill_partially_fills ss ts)" 
      unfolding mctxt_fill_partially_mctxts_length[OF sl] mctxt_fill_partially_fills_length[OF sl] by auto
  } note i = this

  case 1
  then show ?case using fh nth_zip[OF i(1) i(2)]
    by (metis (lifting, no_types) 1 list_update_id list_update_same_conv map_update split_conv)
  case 2 then show ?case using nh[unfolded list_all_length] nth_zip[OF i(1) i(2)]
    by (auto simp: i(1) i(2))
qed

lemma mctxt_fill_partially: 
  assumes ss: "subseq ss ts"
    and t: "t =\<^sub>f (c,ts)"
  shows "\<exists> d. t =\<^sub>f (d,ss)"
proof - 
  let ?ds = "mctxt_fill_partially_mctxts ss ts"
  let ?sss = "mctxt_fill_partially_fills ss ts"

  have "fill_holes c ts =\<^sub>f (fill_holes_mctxt c ?ds, concat ?sss)"
    using 
      fill_holes_mctxt_sound eqfE(2)[OF t,symmetric] mctxt_fill_partially_sound[OF ss] 
      mctxt_fill_partially_mctxts_length[OF ss] mctxt_fill_partially_fills_length[OF ss]
    by metis
  also have "concat ?sss = ss" by (induct ss ts rule: subseq_induct2, insert ss, auto)
  ultimately show ?thesis by (metis eqfE(1) t)
qed

lemma fill_holes_mctxt_map_mctxt_of_term_conv [simp]:
  assumes "num_holes C = length ts"
  shows "fill_holes_mctxt C (map mctxt_of_term ts) = mctxt_of_term (fill_holes C ts)"
  using assms
  by (induct C ts rule: fill_holes_induct) (auto)

lemma fill_holes_mctxt_of_ctxt [simp]:
  "fill_holes (mctxt_of_ctxt C) [t] = C\<langle>t\<rangle>"
proof -
  have "C\<langle>t\<rangle> =\<^sub>f (mctxt_of_ctxt C, [t])" by (metis mctxt_of_ctxt)
  from eqfE [OF this] show ?thesis by simp
qed

definition
  "compose_cap_till P t i C =
    fill_holes_mctxt (cap_till P t) (map mctxt_of_term (take i (uncap_till P t)) @
      C # map mctxt_of_term (drop (Suc i) (uncap_till P t)))"

abbreviation "compose_cap_till_funas F \<equiv> compose_cap_till (if_Fun_in_set F)"

lemma fill_holes_compose_cap_till:
  assumes "i < num_holes (cap_till P s)" and "num_holes C = length ts"
  shows "fill_holes (compose_cap_till P s i C) ts =
    fill_holes (cap_till P s) (take i (uncap_till P s) @ fill_holes C ts # drop (Suc i) (uncap_till P s))"
    (is "_ = fill_holes _ ?ss")
proof -
  have "fill_holes (cap_till P s) ?ss =\<^sub>f
    (fill_holes_mctxt (cap_till P s) (map mctxt_of_term (take i (uncap_till P s)) @
      C # map mctxt_of_term (drop (Suc i) (uncap_till P s))),
      concat (map (\<lambda>_. []) (take i (uncap_till P s)) @ ts #
              map (\<lambda>_. []) (drop (Suc i) (uncap_till P s))))"
    (is "_ =\<^sub>f (fill_holes_mctxt _ ?ts, concat ?us)")
  proof (rule fill_holes_mctxt_sound)
    show "length ?ss = num_holes (cap_till P s)"
      using assms by simp
  next
    show "length ?ts = num_holes (cap_till P s)"
      using assms by simp
  next
    show "length ?us = num_holes (cap_till P s)"
      using assms by simp
  next
    fix j
    assume "j < length ?ts"
    with assms have j: "j < length (uncap_till P s)" by simp
    show "?ss ! j =\<^sub>f (?ts ! j, ?us ! j)"
      using assms and j by (cases "j = i") (auto simp: nth_append)
  qed
  note * = eqfE(1) [OF this]
  show ?thesis by (simp add: compose_cap_till_def *)
qed

lemma in_uncap_till_funas:
  assumes root: "root u = Some fn" "fn \<in> F"
    and "t = C\<langle>u\<rangle>"
  shows "\<exists>i < length (uncap_till_funas F t). \<exists>D. uncap_till_funas F t ! i = D\<langle>u\<rangle> \<and>
    mctxt_of_ctxt C = compose_cap_till_funas F t i (mctxt_of_ctxt D)"
  using \<open>t = C\<langle>u\<rangle>\<close>
proof (induct t arbitrary: C)
  case (Var x)
  then show ?case using root by (cases C) (auto simp: wf_trs_def)
next
  case (Fun f ts)
  define t where [simp]: "t = Fun f ts"
  show ?case
  proof (cases "(f, length ts) \<in> F")
    case True
    then show ?thesis using Fun.prems by (auto simp: compose_cap_till_def)
  next
    case False
    show ?thesis
    proof (cases C)
      case Hole
      then show ?thesis using Fun.prems and False and root by auto
    next
      case (More _ ss\<^sub>1 D _)
      moreover define j where "j = length ss\<^sub>1"
      ultimately have j: "j < length ts" "ts ! j = D\<langle>u\<rangle>"
        and C: "C = More f (take j ts) D (drop (Suc j) ts)"
        using Fun.prems by (auto)
      then have "D\<langle>u\<rangle> \<in> set ts" by (auto simp: in_set_conv_nth)
      then obtain i and E
        where i: "i < length (uncap_till_funas F (D\<langle>u\<rangle>))" "uncap_till_funas F (D\<langle>u\<rangle>) ! i = E\<langle>u\<rangle>"
          and D: "mctxt_of_ctxt D = compose_cap_till_funas F (D\<langle>u\<rangle>) i (mctxt_of_ctxt E)"
        using Fun by blast
      obtain k where k: "take k (uncap_till_funas F t) =
        concat (map (uncap_till_funas F) (take j ts)) @ take i (uncap_till_funas F (D\<langle>u\<rangle>))"
        "k < length (uncap_till_funas F t)" "uncap_till_funas F t ! k = E\<langle>u\<rangle>"
        "drop (Suc k) ((uncap_till_funas F) t) = drop (Suc i) ((uncap_till_funas F) (D\<langle>u\<rangle>)) @ concat (map (uncap_till_funas F) (drop (Suc j) ts))"
        using False and i and j and take_nth_drop_concat [of j "map (uncap_till_funas F) ts" "(uncap_till_funas F) (D\<langle>u\<rangle>)" i "E\<langle>u\<rangle>"]
        by (auto simp: take_map drop_map)
      moreover have "mctxt_of_ctxt C = compose_cap_till_funas F t k (mctxt_of_ctxt E)"
      proof -
        have *: "compose_cap_till_funas F t k (mctxt_of_ctxt E) =
          fill_holes_mctxt (MFun f (map (cap_till_funas F) ts)) (concat (
            map (map mctxt_of_term \<circ> uncap_till_funas F) (take j ts) @
            (map mctxt_of_term (take i (uncap_till_funas F D\<langle>u\<rangle>)) @
            mctxt_of_ctxt E #
            map mctxt_of_term (drop (Suc i) (uncap_till_funas F D\<langle>u\<rangle>))) #
            map (map mctxt_of_term \<circ> uncap_till_funas F) (drop (Suc j) ts)))"
          (is "_ = fill_holes_mctxt _ (concat ?ss)")
          using False and k
          by (simp del: fill_holes_mctxt.simps add: compose_cap_till_def map_concat)
        also have "\<dots> = MFun f (map mctxt_of_term (take j ts) @ mctxt_of_ctxt D #
          map mctxt_of_term (drop (Suc j) ts))" (is "_ = MFun f ?ts")
        proof (rule fill_holes_mctxt_MFun)
          show "length (map (cap_till_funas F) ts) = length ?ts" using j by simp
        next
          show "length ?ss = length ?ts" by simp
        next
          fix n
          assume "n < length ?ts"
          then have n: "n < length ts" using j by simp
          show "num_holes (map (cap_till_funas F) ts ! n) = length (?ss ! n) \<and>
            fill_holes_mctxt (map (cap_till_funas F) ts ! n) (?ss ! n) = ?ts ! n"
          proof (cases "n = j")
            case False
            then have *: "?ss ! n = map mctxt_of_term (uncap_till_funas F (ts ! n))"
              "?ts ! n = mctxt_of_term (ts ! n)"
              using n and j by (auto simp: nth_append min_def)
            have "num_holes (map (cap_till_funas F) ts ! n) = length (?ss ! n)"
              using n by (simp add: * )
            moreover have "fill_holes_mctxt (map (cap_till_funas F) ts ! n) (?ss ! n) = ?ts ! n"
              using n by (auto simp: * )
            ultimately show ?thesis by blast
          next
            case True
            then have *: "?ss ! n =
              map mctxt_of_term (take i (uncap_till_funas F D\<langle>u\<rangle>)) @ mctxt_of_ctxt E #
                map mctxt_of_term (drop (Suc i) (uncap_till_funas F D\<langle>u\<rangle>))"
              "?ts ! n = mctxt_of_ctxt D"
              using n and j by (auto simp: nth_append)
            have "fill_holes_mctxt (map (cap_till_funas F) ts ! n) (?ss ! n) = ?ts ! n"
              unfolding * by (simp add: D compose_cap_till_def True j)
            moreover have "num_holes (map (cap_till_funas F) ts ! n) = length (?ss ! n)"
              unfolding * using i by (simp add: j True)
            ultimately show ?thesis by blast
          qed
        qed
        finally show ?thesis by (simp add: C)
      qed
      ultimately show ?thesis unfolding t_def by blast
    qed
  qed
qed

lemma uncap_till_funas_fill_holes_cancel [simp]:
  assumes "num_holes C = length ts" and "ground_mctxt C"
    and "funas_mctxt C \<subseteq> - F"
  shows "uncap_till_funas F (fill_holes C ts) = concat (map (uncap_till_funas F) ts)"
  using assms
proof (induct C arbitrary: ts)
  case MHole
  then show ?case by (cases ts) simp_all
next
  case (MFun f Cs)
  let ?ts = "partition_holes ts Cs"
  let ?us = "partition_holes (map (uncap_till_funas F) ts) Cs"
  have *: "fill_holes (MFun f Cs) ts =
    Fun f (map (\<lambda>i. fill_holes (Cs ! i) (?ts ! i)) [0 ..< length Cs])"
    unfolding partition_holes_fill_holes_conv ..
  have "\<forall>i < length Cs. uncap_till_funas F (fill_holes (Cs ! i) (?ts ! i)) = concat (?us ! i)"
  proof (intro allI impI)
    fix i
    assume "i < length Cs"
    then have "Cs ! i \<in> set Cs" by simp
    from MFun.hyps [OF this, of "?ts ! i"] and MFun.prems and \<open>i < length Cs\<close>
    show "uncap_till_funas F (fill_holes (Cs ! i) (?ts ! i)) = concat (?us ! i)"
      by (auto iff: UN_subset_iff)
  qed
  then have **: "map (uncap_till_funas F \<circ> (\<lambda>i. fill_holes (Cs ! i) (?ts ! i))) [0..<length Cs] =
    map (concat \<circ> (\<lambda>i. (?us ! i))) [0 ..<length Cs]" by simp
  have ***: "sum_list (map num_holes Cs) = length (map (uncap_till_funas F) ts)"
    using MFun.prems by simp
  show ?case
    using MFun.prems
    apply (simp add: * ** del: fill_holes.simps)
    by (auto simp: o_def map_upt_len_same_len_conv [OF length_partition_holes])
qed simp

lemma uncap_till_funas_fill_holes_cap_till_funas [simp]:
  assumes "num_holes (cap_till_funas F s) = length ts"
  shows "uncap_till_funas F (fill_holes (cap_till_funas F s) ts) =
    concat (map (uncap_till_funas F) ts)"
  by (rule uncap_till_funas_fill_holes_cancel [OF assms ground_cap_till_funas, of F]) auto

lemma Ball_atLeast0LessThan_partition_holes_conv [simp]:
  "(\<forall>i \<in> {0 ..< length Cs}. \<forall>x \<in> set (partition_holes xs Cs ! i). P x) =
    (\<forall>x \<in> \<Union>(set (map set (partition_holes xs Cs))). P x)"
  using Ball_atLeast0LessThan_partition_by_conv [of "map num_holes Cs" xs] by simp

lemma ground_fill_holes_mctxt [simp]:
  "num_holes C = length Ds \<Longrightarrow>
    ground_mctxt (fill_holes_mctxt C Ds) \<longleftrightarrow> ground_mctxt C \<and> (\<forall>D \<in> set Ds. ground_mctxt D)"
proof (induct C arbitrary: Ds)
  case MHole
  then show ?case by (cases Ds) simp_all
next
  case (MFun f Cs)
  then have *: "(\<forall>i\<in>{0..<length Cs}.
    ground_mctxt (fill_holes_mctxt (Cs ! i) (partition_holes Ds Cs ! i))) =
    (\<forall>i\<in>{0..<length Cs}.
      ground_mctxt (Cs ! i) \<and> (\<forall>a\<in>set (partition_holes Ds Cs ! i). ground_mctxt a))"
    and **: "sum_list (map num_holes Cs) = length Ds"
    by simp_all
  show ?case
    unfolding partition_holes_fill_holes_mctxt_conv
    by (simp add: * ball_conj_distrib Ball_set_partition_by [OF **])
qed simp

lemma concat_map_uncap_till_funas_map_subst_apply_uncap_till_funas [simp]:
  "concat (map (uncap_till_funas F) (map (\<lambda>s. s \<cdot> \<sigma>) (uncap_till_funas F t))) = uncap_till_funas F (t \<cdot> \<sigma>)"
proof (induct t)
  case (Fun f ts)
  then have *: "map (uncap_till_funas F \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts =
    map concat (map (map (uncap_till_funas F) \<circ> map (\<lambda>s. s \<cdot> \<sigma>) \<circ> uncap_till_funas F) ts)" by simp
  show ?case
    by (simp add: * map_concat concat_map_concat [symmetric])
qed simp

lemma concat_uncap_till_subst_conv:
  "concat (map (\<lambda>i. uncap_till_funas F ((uncap_till_funas F t ! i) \<cdot> \<sigma>)) [0 ..< length (uncap_till_funas F t)]) =
    uncap_till_funas F (t \<cdot> \<sigma>)"
proof -
  have "concat (map (uncap_till_funas F) (map (\<lambda>i.
    (uncap_till_funas F t ! i) \<cdot> \<sigma>) [0 ..< length (uncap_till_funas F t)])) = uncap_till_funas F (t \<cdot> \<sigma>)"
    unfolding map_upt_len_conv [of "\<lambda>s. s \<cdot> \<sigma>" "uncap_till_funas F t"]
    unfolding concat_map_uncap_till_funas_map_subst_apply_uncap_till_funas ..
  then show ?thesis by (simp add: o_def)
qed

lemma the_root_uncap_till_funas:
  "is_Fun t \<Longrightarrow> the (root t) \<in> F \<Longrightarrow> uncap_till_funas F t = [t]"
  by (cases t) simp_all

lemma funas_cap_till_subset:
  "funas_mctxt (cap_till P t) \<subseteq> funas_term t"
  by (induct t) auto

lemma funas_uncap_till_subset:
  "s \<in> set (uncap_till P t) \<Longrightarrow> funas_term s \<subseteq> funas_term t"
proof (induct t arbitrary: s)
  case (Fun f ts)
  then show ?case by (cases "P (Fun f ts)") auto
qed simp

lemma ground_mctxt_subst_apply_context [simp]:
  "ground_mctxt C \<Longrightarrow> C \<cdot>mc \<sigma> = C"
  by (induct C) (simp_all add: map_idI)

lemma vars_term_fill_holes [simp]:
  "num_holes C = length ts \<Longrightarrow> ground_mctxt C \<Longrightarrow>
    vars_term (fill_holes C ts) = \<Union>(vars_term ` set ts)"
proof (induct C arbitrary: ts)
  case MHole
  then show ?case by (cases ts) simp_all
next
  case (MFun f Cs)
  then have *: "length (partition_holes ts Cs) = length Cs" by simp
  let ?f = "\<lambda>x. \<Union>y \<in> set x. vars_term y"
  show ?case
    using MFun
    unfolding partition_holes_fill_holes_conv
    by (simp add: UN_upt_len_conv [OF *, of ?f] UN_set_partition_by)
qed simp

subsubsection \<open>Semilattice Structures\<close>

instantiation mctxt :: (type, type) inf
begin

fun inf_mctxt :: "('a, 'b) mctxt \<Rightarrow> ('a, 'b) mctxt \<Rightarrow> ('a, 'b) mctxt"
  where
    "MHole \<sqinter> D = MHole" |
    "C \<sqinter> MHole = MHole" |
    "MVar x \<sqinter> MVar y = (if x = y then MVar x else MHole)" |
    "MFun f Cs \<sqinter> MFun g Ds =
    (if f = g \<and> length Cs = length Ds then MFun f (map (case_prod (\<sqinter>)) (zip Cs Ds))
    else MHole)" |
    "C \<sqinter> D = MHole"

instance ..

end

lemma inf_mctxt_idem [simp]:
  fixes C :: "('f, 'v) mctxt"
  shows "C \<sqinter> C = C"
  by (induct C) (auto simp: zip_same_conv_map intro: map_idI)

lemma inf_mctxt_MHole2 [simp]:
  "C \<sqinter> MHole = MHole"
  by (induct C) simp_all

lemma inf_mctxt_comm [ac_simps]:
  "(C :: ('f, 'v) mctxt) \<sqinter> D = D \<sqinter> C"
  by (induct C D rule: inf_mctxt.induct) (fastforce simp: in_set_conv_nth intro!: nth_equalityI)+

lemma inf_mctxt_assoc [ac_simps]:
  fixes C :: "('f, 'v) mctxt"
  shows "C \<sqinter> D \<sqinter> E = C \<sqinter> (D \<sqinter> E)"
proof (induction C D arbitrary: E rule: inf_mctxt.induct)
  case (1 D E)
  then show ?case by (cases E, auto)
next
  case ("2_1" v E)
  then show ?case by (cases E, auto)
next
  case ("2_2" v va E)
  then show ?case by (cases E, auto)
next
  case (3 x y E)
  then show ?case by (cases E, auto)
next
  case (4 f Cs g Ds E)
  then show ?case 
    by (cases E; fastforce simp: in_set_conv_nth intro!: nth_equalityI)
next
  case ("5_1" v va vb E)
  then show ?case by (cases E, auto)
next
  case ("5_2" v va vb E)
  then show ?case by (cases E, auto)
qed

instantiation mctxt :: (type, type) order
begin

definition "(C :: ('a, 'b) mctxt) \<le> D \<longleftrightarrow> C \<sqinter> D = C"
definition "(C :: ('a, 'b) mctxt) < D \<longleftrightarrow> C \<le> D \<and> \<not> D \<le> C"

instance
  by (standard, simp_all add: less_eq_mctxt_def less_mctxt_def ac_simps, metis inf_mctxt_assoc)

end

inductive less_eq_mctxt' :: "('f, 'v) mctxt \<Rightarrow> ('f,'v) mctxt \<Rightarrow> bool" where
  "less_eq_mctxt' MHole u"
| "less_eq_mctxt' (MVar v) (MVar v)"
| "length cs = length ds \<Longrightarrow> (\<And>i. i < length cs \<Longrightarrow> less_eq_mctxt' (cs ! i) (ds ! i)) \<Longrightarrow> less_eq_mctxt' (MFun f cs) (MFun f ds)"

lemma less_eq_mctxt_prime: "C \<le> D \<longleftrightarrow> less_eq_mctxt' C D"
proof
  assume "less_eq_mctxt' C D" then show "C \<le> D"
    by (induct C D rule: less_eq_mctxt'.induct) (auto simp: less_eq_mctxt_def intro: nth_equalityI)
next
  assume "C \<le> D" then show "less_eq_mctxt' C D" unfolding less_eq_mctxt_def
    by (induct C D rule: inf_mctxt.induct)
      (auto split: if_splits simp: set_zip intro!: less_eq_mctxt'.intros nth_equalityI elim!: nth_equalityE, metis)
qed

lemmas less_eq_mctxt_induct = less_eq_mctxt'.induct[folded less_eq_mctxt_prime, consumes 1]
lemmas less_eq_mctxt_intros = less_eq_mctxt'.intros[folded less_eq_mctxt_prime]

lemma less_eq_mctxtI2:
  "C = MHole \<Longrightarrow> C \<le> MHole"
  "C = MHole \<or> C = MVar v \<Longrightarrow> C \<le> MVar v"
  "C = MHole \<or> C = MFun f cs \<and> length cs = length ds \<and> (\<forall>i. i < length cs \<longrightarrow> cs ! i \<le> ds ! i) \<Longrightarrow> C \<le> MFun f ds"
  unfolding less_eq_mctxt_prime by (cases C) (auto intro: less_eq_mctxt'.intros)

lemma less_eq_mctxt_MHoleE2:
  assumes "C \<le> MHole"
  obtains (MHole) "C = MHole"
  using assms unfolding less_eq_mctxt_prime by (cases C, auto)

lemma less_eq_mctxt_MVarE2:
  assumes "C \<le> MVar v"
  obtains (MHole) "C = MHole" | (MVar) "C = MVar v"
  using assms unfolding less_eq_mctxt_prime by (cases C) auto

lemma less_eq_mctxt_MFunE2:
  assumes "C \<le> MFun f ds"
  obtains (MHole) "C = MHole"
  | (MFun) cs where "C = MFun f cs" "length cs = length ds" "\<And>i. i < length cs \<Longrightarrow> cs ! i \<le> ds ! i"
  using assms unfolding less_eq_mctxt_prime by (cases C) auto

lemmas less_eq_mctxtE2 = less_eq_mctxt_MHoleE2 less_eq_mctxt_MVarE2 less_eq_mctxt_MFunE2

lemma less_eq_mctxtI1:
  "MHole \<le> D"
  "D = MVar v \<Longrightarrow> MVar v \<le> D"
  "D = MFun f ds \<Longrightarrow> length cs = length ds \<Longrightarrow> (\<And>i. i < length cs \<Longrightarrow> cs ! i \<le> ds ! i) \<Longrightarrow> MFun f cs \<le> D"
  by (cases D) (auto intro: less_eq_mctxtI2)

lemma less_eq_mctxt_MVarE1:
  assumes "MVar v \<le> D"
  obtains (MVar) "D = MVar v"
  using assms by (cases D) (auto elim: less_eq_mctxtE2)

lemma less_eq_mctxt_MFunE1:
  assumes "MFun f cs \<le> D"
  obtains (MFun) ds where "D = MFun f ds" "length cs = length ds" "\<And>i. i < length cs \<Longrightarrow> cs ! i \<le> ds ! i"
  using assms by (cases D) (auto elim: less_eq_mctxtE2)

lemmas less_eq_mctxtE1 = less_eq_mctxt_MVarE1 less_eq_mctxt_MFunE1


instance mctxt :: (type, type) semilattice_inf
  apply (intro_classes)
  by (auto simp: less_eq_mctxt_def inf_mctxt_assoc [symmetric])
    (metis inf_mctxt_comm inf_mctxt_assoc inf_mctxt_idem)+

fun inf_mctxt_args :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt list"
  where
    "inf_mctxt_args MHole D = [MHole]" |
    "inf_mctxt_args C MHole = [C]" |
    "inf_mctxt_args (MVar x) (MVar y) = (if x = y then [] else [MVar x])" |
    "inf_mctxt_args (MFun f Cs) (MFun g Ds) =
    (if f = g \<and> length Cs = length Ds then concat (map (case_prod inf_mctxt_args) (zip Cs Ds))
    else [MFun f Cs])" |
    "inf_mctxt_args C D = [C]"

lemma inf_mctxt_args_MHole2 [simp]:
  "inf_mctxt_args C MHole = [C]"
  by (cases C) simp_all

lemma fill_holes_mctxt_replicate_MHole [simp]:
  "fill_holes_mctxt C (replicate (num_holes C) MHole) = C"
proof (induct C)
  case (MFun f Cs)
  { fix i assume "i < length Cs"
    then have "partition_holes (replicate (sum_list (map num_holes Cs)) MHole) Cs ! i =
        replicate (num_holes (Cs ! i)) MHole"
      using partition_by_nth_nth[of "map num_holes Cs" "replicate (sum_list (map num_holes Cs)) MHole"]
      by (auto intro!: nth_equalityI)
  } note * = this
  show ?case using MFun[OF nth_mem] by (auto simp: * intro!: nth_equalityI)
qed auto

lemma num_holes_inf_mctxt:
  "num_holes (C \<sqinter> D) = length (inf_mctxt_args C D)"
  by (induct C D rule: inf_mctxt.induct)
    (auto simp: in_set_zip length_concat intro!: arg_cong [of _ _ sum_list])

lemma length_inf_mctxt_args:
  "length (inf_mctxt_args D C) = length (inf_mctxt_args C D)"
  by (metis inf.commute num_holes_inf_mctxt)

lemma inf_mctxt_args_same [simp]:
  "inf_mctxt_args C C = replicate (num_holes C) MHole"
proof (induct C)
  case (MFun f Cs)
  have *: "\<And>C. num_holes C = length (inf_mctxt_args C C)"
    using num_holes_inf_mctxt [of C C for C] by auto
  let ?xs = "map (case_prod inf_mctxt_args) (zip Cs Cs)"
  have "\<forall>i < length Cs.
    inf_mctxt_args (Cs ! i) (Cs ! i) = replicate (num_holes (Cs ! i)) MHole" using MFun by auto
  then have "\<forall>i < length ?xs. \<forall>j < length (?xs ! i). ?xs ! i ! j = MHole" by auto
  then have "\<forall>i < length (concat ?xs). concat ?xs ! i = MHole" by (metis nth_concat_two_lists) 
  then show ?case by (auto simp: * intro!: nth_equalityI)
qed simp_all

lemma inf_mctxt_inf_mctxt_args:
  "fill_holes_mctxt (C \<sqinter> D) (inf_mctxt_args C D) = C"
proof (induct C D rule: inf_mctxt.induct)
  case (4 f Cs g Ds)
  then show ?case
  proof (cases "f = g \<and> length Cs = length Ds")
    case True
    with 4 have "\<forall>i < length Cs.
      fill_holes_mctxt (Cs ! i \<sqinter> Ds ! i) (inf_mctxt_args (Cs ! i) (Ds ! i)) = Cs ! i"
      by (force simp: set_zip)
    moreover have "partition_holes (concat (map (case_prod inf_mctxt_args) (zip Cs Ds)))
      (map (case_prod (\<sqinter>)) (zip Cs Ds)) = map (case_prod inf_mctxt_args) (zip Cs Ds)"
      by (rule partition_by_concat_id) (simp_all add: num_holes_inf_mctxt)
    ultimately show ?thesis
      using fill_holes_mctxt.simps [simp del]
      by (auto simp: partition_holes_fill_holes_mctxt_conv intro!: nth_equalityI)
  qed auto
qed auto

lemma inf_mctxt_inf_mctxt_args2:
  "fill_holes_mctxt (C \<sqinter> D) (inf_mctxt_args D C) = D"
  unfolding inf_mctxt_comm [of C D] by (rule inf_mctxt_inf_mctxt_args)

instantiation mctxt :: (type, type) sup
begin

fun sup_mctxt :: "('a, 'b) mctxt \<Rightarrow> ('a, 'b) mctxt \<Rightarrow> ('a, 'b) mctxt"
  where
    "MHole \<squnion> D = D" |
    "C \<squnion> MHole = C" |
    "MVar x \<squnion> MVar y = (if x = y then MVar x else undefined)" |
    "MFun f Cs \<squnion> MFun g Ds =
    (if f = g \<and> length Cs = length Ds then MFun f (map (case_prod (\<squnion>)) (zip Cs Ds))
    else undefined)" |
    "(C :: ('a, 'b) mctxt) \<squnion> D = undefined"

instance ..

end

lemma sup_mctxt_idem [simp]:
  fixes C :: "('f, 'v) mctxt"
  shows "C \<squnion> C = C"
  by (induct C) (auto simp: zip_same_conv_map intro: map_idI)

lemma sup_mctxt_MHole [simp]: "C \<squnion> MHole = C"
  by (induct C) simp_all

lemma sup_mctxt_comm [ac_simps]:
  fixes C :: "('f, 'v) mctxt"
  shows "C \<squnion> D = D \<squnion> C"
  by (induct C D rule: sup_mctxt.induct) (fastforce simp: in_set_conv_nth intro!: nth_equalityI)+

text \<open>
  @{const sup} is defined on compatible multihole-contexts.
  Note that compatibility is not transitive.
\<close>
inductive_set comp_mctxt :: "(('a, 'b) mctxt \<times> ('a, 'b) mctxt) set"
  where
    MHole1: "(MHole, D) \<in> comp_mctxt" |
    MHole2: "(C, MHole) \<in> comp_mctxt" |
    MVar: "x = y \<Longrightarrow> (MVar x, MVar y) \<in> comp_mctxt" |
    MFun: "f = g \<Longrightarrow> length Cs = length Ds \<Longrightarrow> \<forall>i < length Ds. (Cs ! i, Ds ! i) \<in> comp_mctxt \<Longrightarrow>
    (MFun f Cs, MFun g Ds) \<in> comp_mctxt"

lemma comp_mctxt_refl:
  "(C, C) \<in> comp_mctxt"
  by (induct C) (auto intro: comp_mctxt.intros)

lemma comp_mctxt_sym:
  assumes "(C, D) \<in> comp_mctxt"
  shows "(D, C) \<in> comp_mctxt"
  using assms by (induct) (auto intro: comp_mctxt.intros)

lemma sup_mctxt_assoc [ac_simps]:
  assumes "(C, D) \<in> comp_mctxt" and "(D, E) \<in> comp_mctxt"
  shows "C \<squnion> D \<squnion> E = C \<squnion> (D \<squnion> E)"
  using assms by (induct C D arbitrary: E) (auto elim!: comp_mctxt.cases intro!: nth_equalityI)

text \<open>
  No instantiation to @{class semilattice_sup} possible, since @{const sup} is only
  partially defined on terms (e.g., it is not associative in general).
\<close>

interpretation mctxt_order_bot: order_bot MHole "(\<le>)" "(<)"
  by (standard) (simp add: less_eq_mctxt_def)

lemma sup_mctxt_ge1 [simp]:
  assumes "(C, D) \<in> comp_mctxt"
  shows "C \<le> C \<squnion> D"
  using assms by (induct C D) (auto simp: less_eq_mctxt_def intro: nth_equalityI)

lemma sup_mctxt_ge2 [simp]:
  assumes "(C, D) \<in> comp_mctxt"
  shows "D \<le> C \<squnion> D"
  using assms by (induct) (auto simp: less_eq_mctxt_def intro: nth_equalityI)

lemma sup_mctxt_least:
  assumes "(D, E) \<in> comp_mctxt"
    and "D \<le> C" and "E \<le> C"
  shows "D \<squnion> E \<le> C"
  using assms
proof (induct arbitrary: C)
  case (MFun f g Cs Ds)
  then show ?case
    apply (auto simp: less_eq_mctxt_def elim!: inf_mctxt.elims intro!: nth_equalityI)[1]
      apply (metis (erased, lifting) length_map nth_map nth_zip split_conv)
    by (metis mctxt.distinct(5))+
qed auto


lemma inf_mctxt_args_MHole:
  assumes "(C, D) \<in> comp_mctxt" and "i < length (inf_mctxt_args C D)"
  shows "inf_mctxt_args C D ! i = MHole \<or> inf_mctxt_args D C ! i = MHole"
  using assms
proof (induct C D arbitrary: i)
  case (MHole2 C)
  then show ?case by (cases C) simp_all
next
  case (MFun f g Cs Ds)
  then have [simp]: "f = g" "length Ds = length Cs" by auto
  let ?xs = "map (case_prod inf_mctxt_args) (zip Cs Ds)"
  let ?ys = "map (case_prod inf_mctxt_args) (zip Ds Cs)"
  obtain m and n where *: "i = sum_list (map length (take m ?xs)) + n"
    "m < length Cs" "n < length (inf_mctxt_args (Cs ! m) (Ds ! m))"
    and "inf_mctxt_args (MFun f Cs) (MFun g Ds) ! i = inf_mctxt_args (Cs ! m) (Ds ! m) ! n"
    using MFun.prems by (auto dest: less_length_concat)
  moreover have "concat ?ys ! i = (map (case_prod inf_mctxt_args) (zip Ds Cs)) ! m ! n"
    by (rule concat_nth)
      (insert *, auto intro: arg_cong [of _ _ sum_list] 
        simp: map_nth_eq_conv length_inf_mctxt_args)
  ultimately show ?case using MFun(3) by simp
qed auto

lemma rsteps_mctxt:
  assumes "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "\<forall>i<length ss. (ss ! i, ts ! i) \<in> (rstep R)\<^sup>*"
  shows "(s, t) \<in> (rstep R)\<^sup>*"
proof -
  have [simp]: "length ss = length ts" using assms by (auto dest!: eqfE)
  have [simp]: "t = fill_holes C ts" using assms by (auto dest: eqfE)
  have "(s, fill_holes C ts) \<in> (rstep R)\<^sup>*"
    using assms by (intro eqf_all_ctxt_closed_step [of UNIV _ s C ss, THEN conjunct1]) auto
  then show ?thesis by simp
qed

fun sup_mctxt_args :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt list"
  where
    "sup_mctxt_args MHole D = [D]" |
    "sup_mctxt_args C MHole = replicate (num_holes C) MHole" |
    "sup_mctxt_args (MVar x) (MVar y) = (if x = y then [] else undefined)" |
    "sup_mctxt_args (MFun f Cs) (MFun g Ds) =
    (if f = g \<and> length Cs = length Ds then concat (map (case_prod sup_mctxt_args) (zip Cs Ds))
    else undefined)" |
    "sup_mctxt_args C D = undefined"

lemma sup_mctxt_args_MHole2 [simp]:
  "sup_mctxt_args C MHole = replicate (num_holes C) MHole"
  by (cases C) simp_all

lemma num_holes_sup_mctxt_args:
  assumes "(C, D) \<in> comp_mctxt"
  shows "num_holes C = length (sup_mctxt_args C D)"
  using assms by (induct) (auto simp: length_concat intro!: arg_cong [of _ _ sum_list] nth_equalityI)

lemma sup_mctxt_sup_mctxt_args:
  assumes "(C, D) \<in> comp_mctxt"
  shows "fill_holes_mctxt C (sup_mctxt_args C D) = C \<squnion> D"
  using assms
proof (induct)
  note fill_holes_mctxt.simps [simp del]
  case (MFun f g Cs Ds)
  then show ?case
  proof (cases "f = g \<and> length Cs = length Ds")
    case True
    with MFun have "\<forall>i < length Cs.
      fill_holes_mctxt (Cs ! i) (sup_mctxt_args (Cs ! i) (Ds ! i)) = Cs ! i \<squnion> Ds ! i"
      and *: "\<forall>i < length Cs. (Cs ! i, Ds ! i) \<in> comp_mctxt" by (force simp: set_zip)+
    moreover have "partition_holes (concat (map (case_prod sup_mctxt_args) (zip Cs Ds)))
      Cs = map (case_prod sup_mctxt_args) (zip Cs Ds)"
      using True and * by (intro partition_by_concat_id) (auto simp: num_holes_sup_mctxt_args)
    ultimately show ?thesis
      using * and True by (auto simp: partition_holes_fill_holes_mctxt_conv intro!: nth_equalityI)
  qed auto
qed auto

lemma sup_mctxt_args:
  assumes "(C, D) \<in> comp_mctxt"
  shows "sup_mctxt_args C D = inf_mctxt_args (C \<squnion> D) C"
  using assms by (induct) (auto intro!: arg_cong [of _ _ concat] nth_equalityI)

lemma term_for_mctxt:
  fixes C :: "('f, 'v) mctxt"
  obtains t and ts where "t =\<^sub>f (C, ts)"
proof -
  obtain ts :: "('f, 'v) term list" where "num_holes C = length ts" by (metis Ex_list_of_length)
  then have "fill_holes C ts =\<^sub>f (C, ts)" by blast
  show ?thesis by (standard) fact
qed

lemma comp_mctxt_eqfE:
  assumes "(C, D) \<in> comp_mctxt"
  obtains s and ss and ts where "s =\<^sub>f (C, ss)" and "s =\<^sub>f (D, ts)"
proof (goal_cases)
  case 1
  obtain u and us where "u =\<^sub>f (C \<squnion> D, us)" by (metis term_for_mctxt)
  then have u: "u = fill_holes (C \<squnion> D) us"
    and *: "length us = num_holes (C \<squnion> D)" by (auto dest: eqfE)
  define Cs Ds where "Cs = sup_mctxt_args C D"
    and "Ds = sup_mctxt_args D C"
  then have sup1: "C \<squnion> D = fill_holes_mctxt C Cs" and sup2: "C \<squnion> D = fill_holes_mctxt D Ds"
    using assms by (auto simp: sup_mctxt_sup_mctxt_args comp_mctxt_sym ac_simps)
  then have u1: "u = fill_holes (fill_holes_mctxt C Cs) us"
    and u2: "u = fill_holes (fill_holes_mctxt D Ds) us" by (simp_all add: u)
  define ss ts where "ss = map (\<lambda>i. fill_holes (Cs ! i) (partition_holes us Cs ! i)) [0 ..< num_holes C]"
    and "ts = map (\<lambda>i. fill_holes (Ds ! i) (partition_holes us Ds ! i)) [0 ..< num_holes D]"
  have "u = fill_holes C ss"
    using assms
    by (simp add: * u1 sup1 ss_def fill_holes_mctxt_fill_holes Cs_def num_holes_sup_mctxt_args)
  moreover have "u = fill_holes D ts"
    using assms [THEN comp_mctxt_sym]
    by (simp add: * u2 sup2 ts_def fill_holes_mctxt_fill_holes Ds_def num_holes_sup_mctxt_args)
  ultimately have "u =\<^sub>f (C, ss)" and "u =\<^sub>f (D, ts)" by (auto simp: ss_def ts_def)
  from 1[OF this] show thesis .
qed

lemma eqf_comp_mctxt:
  assumes "s =\<^sub>f (C, ss)" and "s =\<^sub>f (D, ts)"
  shows "(C, D) \<in> comp_mctxt"
  using assms
proof (induct s arbitrary: C D ss ts)
  case (Var x C D)
  then show ?case
    by (cases C D rule: mctxt.exhaust [case_product mctxt.exhaust])
      (auto simp: eq_fill.simps intro: comp_mctxt.intros)
next
  case (Fun f ss C D us vs)
  { fix Cs and Ds
    assume *: "C = MFun f Cs" "D = MFun f Ds" and **: "length Cs = length Ds"
    have ?case
    proof (unfold *, intro comp_mctxt.MFun [OF refl **] allI impI)
      fix i
      assume "i < length Ds"
      then show "(Cs ! i, Ds ! i) \<in> comp_mctxt"
        using Fun by (auto simp: * ** elim!: eqf_MFunE) (metis nth_mem)
    qed }
  with Fun.prems show ?case
    by (cases C D rule: mctxt.exhaust [case_product mctxt.exhaust])
      (auto simp: eq_fill.simps dest: map_eq_imp_length_eq intro: comp_mctxt.intros)
qed

lemma comp_mctxt_iff:
  "(C, D) \<in> comp_mctxt \<longleftrightarrow> (\<exists>s ss ts. s =\<^sub>f (C, ss) \<and> s =\<^sub>f (D, ts))"
  by (blast elim!: comp_mctxt_eqfE intro: eqf_comp_mctxt)

lemma hole_poss_parallel_pos [simp]:
  assumes "p \<in> hole_poss C" and "q \<in> hole_poss C" and "p \<noteq> q"
  shows "parallel_pos p q"
  using assms by (induct C arbitrary: p q) (fastforce dest!: nth_mem)+

lemma eq_fill_induct [consumes 1, case_names MHole MVar MFun]:
  assumes "t =\<^sub>f (C, ts)"
    and "\<And>t. P t MHole [t]"
    and "\<And>x. P (Var x) (MVar x) []"
    and "\<And>f ss Cs ts. \<lbrakk>length Cs = length ss; sum_list (map num_holes Cs) = length ts;
      \<forall>i < length ss. ss ! i =\<^sub>f (Cs ! i, partition_holes ts Cs ! i) \<and>
        P (ss ! i) (Cs ! i) (partition_holes ts Cs ! i)\<rbrakk>
      \<Longrightarrow> P (Fun f ss) (MFun f Cs) ts"
  shows "P t C ts"
  using assms(1)
proof (induct t arbitrary: C ts)
  case (Var x)
  then show ?case
    using assms(2, 3) by (cases C; cases ts) (auto elim: eq_fill.cases)
next
  case (Fun f ss C ts)
  { assume "C = MHole" and "ts = [Fun f ss]"
    with Fun.hyps have ?case using assms(2) by auto }
  moreover
  { fix Cs
    assume C: "C = MFun f Cs" and "sum_list (map num_holes Cs) = length ts"
      and "length Cs = length ss"
      and "Fun f ss = fill_holes (MFun f Cs) ts"
    moreover then have "\<forall>i < length ss. ss ! i =\<^sub>f (Cs ! i, partition_holes ts Cs ! i)"
      by (auto simp del: fill_holes.simps
          simp: partition_holes_fill_holes_conv intro!: eq_fill.intros)
        (metis (no_types, lifting) add.left_neutral length_map length_upt nth_map_upt)
    moreover with Fun.hyps(1) have "\<forall>i < length ss. 
      P (ss ! i) (Cs ! i) (partition_holes ts Cs ! i)" by auto
    ultimately have ?case using assms(4) [of Cs ss ts f] by auto }
  ultimately show ?case
    using Fun.prems by (elim eq_fill.cases) (auto, cases C; cases ts, auto)
qed

lemma hole_poss_subset_poss:
  assumes "s =\<^sub>f (C, ss)"
  shows "hole_poss C \<subseteq> poss s"
  using assms by (induct rule: eq_fill_induct) auto

fun hole_num
  where
    "hole_num [] MHole = 0" |
    "hole_num (i # q) (MFun f Cs) = sum_list (map num_holes (take i Cs)) + hole_num q (Cs ! i)"

lemma hole_poss_nth_subt_at:
  assumes "t =\<^sub>f (C, ts)" and "p \<in> hole_poss C"
  shows "hole_num p C < length ts \<and> t |_ p = ts ! hole_num p C"
  using assms
proof (induct arbitrary: p rule: eq_fill_induct)
  case (MFun f ss Cs ts)
  let ?ts = "partition_holes ts Cs"
  from MFun obtain i and q where [simp]: "p = i # q"
    and "i < length ss" and "q \<in> hole_poss (Cs ! i)" by auto
  with MFun.hyps have "ss ! i =\<^sub>f (Cs ! i, ?ts ! i)"
    and j: "hole_num q (Cs ! i) < length (?ts ! i)" (is "?j < length _")
    and *: "?ts ! i ! hole_num q (Cs ! i) = ss ! i |_ q"
    by auto
  let ?k = "sum_list (map length (take i ?ts)) + ?j"
  have "i < length ?ts" using \<open>i < length ss\<close> and MFun by auto
  with partition_by_nth_nth_old [OF this j] and MFun and concat_nth_length [OF this j]
  have "?ts ! i ! ?j = ts ! ?k" and "?k < length ts" by (auto)
  moreover with * have "ts ! ?k = Fun f ss |_ p" using \<open>i < length ss\<close> by simp
  ultimately show ?case using MFun.hyps(2) by (auto simp: take_map [symmetric])
qed auto

lemma eqf_Fun_MFun:
  assumes "Fun f ss =\<^sub>f (MFun g Cs, ts)"
  shows "g = f \<and> length Cs = length ss \<and> sum_list (map num_holes Cs) = length ts \<and>
    (\<forall>i < length ss. ss ! i =\<^sub>f (Cs ! i, partition_holes ts Cs ! i))"
  using assms by (induct "Fun f ss" "MFun g Cs" ts rule: eq_fill_induct) auto

lemma fill_holes_eq_Var_cases:
  assumes "num_holes C = length ts"
    and "fill_holes C ts = Var x"
  obtains "C = MHole \<and> ts = [Var x]" | "C = MVar x \<and> ts = []"
  using assms by (induct C; cases ts) auto

lemma num_holes_inf_mctxt_le:
  assumes "s =\<^sub>f (C, ts)" and "s =\<^sub>f (D, us)"
  shows "num_holes (C \<sqinter> D) \<le> num_holes C + num_holes D"
  using assms
proof (induct C D arbitrary: s ts us rule: inf_mctxt.induct)
  case (4 f Cs g Ds)
  show ?case
  proof (cases "f = g \<and> length Cs = length Ds")
    case False
    with 4 show ?thesis by (auto elim!: eq_fill.cases dest!: map_eq_imp_length_eq)
  next
    case True
    then have [simp]: "g = f" "length Ds = length Cs" by simp_all
    have IH: "\<forall>(C, D) \<in> set (zip Cs Ds). num_holes (C \<sqinter> D) \<le> num_holes C + num_holes D"
    proof
      fix C D assume *: "(C, D) \<in> set (zip Cs Ds)"
      then obtain i where "i < length Cs" and "zip Cs Ds ! i = (C, D)" by (auto simp: in_set_zip)
      with "4.prems"
      have "fill_holes (Cs ! i) (partition_holes ts Cs ! i) =\<^sub>f (C, partition_holes ts Cs ! i)"
        and "fill_holes (Cs ! i) (partition_holes ts Cs ! i) =\<^sub>f (D, partition_holes us Ds ! i)"
        by (auto elim!: eq_fill.cases)
      from "4.hyps" [OF True * HOL.refl this]
      show "num_holes (C \<sqinter> D) \<le> num_holes C + num_holes D" .
    qed
    have "num_holes (MFun f Cs \<sqinter> MFun g Ds) = sum_list (map (num_holes \<circ> case_prod (\<sqinter>)) (zip Cs Ds))"
      using "4.prems" by (auto elim!: eq_fill.cases dest!: map_eq_imp_length_eq)
    moreover have "num_holes (MFun f Cs) + num_holes (MFun g Ds) =
      sum_list (map (\<lambda>(C, D). num_holes C + num_holes D) (zip Cs Ds))"
      using \<open>length Ds = length Cs\<close> by (induct rule: list_induct2) simp_all
    ultimately show ?thesis using IH by (auto intro!: sum_list_mono)
  qed
qed (auto elim!: eq_fill.cases)

lemma map_inf_mctxt_zip_mctxt_of_term [simp]:
  "map (\<lambda>(x, y). x \<sqinter> y) (zip (map mctxt_of_term ts) (map mctxt_of_term ts)) = map mctxt_of_term ts"
  by (induct ts) simp_all

lemma inf_mctxt_ctxt_apply_term [simp]:
  "mctxt_of_term (C\<langle>t\<rangle>) \<sqinter> mctxt_of_ctxt C = mctxt_of_ctxt C"
  "mctxt_of_ctxt C \<sqinter> mctxt_of_term (C\<langle>t\<rangle>) = mctxt_of_ctxt C"
  by (induct C) simp_all

lemma inf_fill_holes_mctxt_MHoles:
  "num_holes C = length Cs \<Longrightarrow> length Ds = length Cs \<Longrightarrow>
  \<forall>i<length Cs. Cs ! i = MHole \<or> Ds ! i = MHole \<Longrightarrow>
  fill_holes_mctxt C Cs \<sqinter> fill_holes_mctxt C Ds = C"
proof (induct C arbitrary: Cs Ds)
  case (MHole Cs Ds)
  then show ?case by (cases Cs; cases Ds; force)
next
  case (MFun f Bs Cs Ds)
  then show ?case 
    unfolding partition_holes_fill_holes_mctxt_conv'
    apply simp
    apply (rule nth_equalityI)
    by (auto simp: partition_by_nth_nth)
qed auto

lemma inf_fill_holes_mctxt_two_MHoles [simp]: "num_holes C = 2 \<Longrightarrow>
  fill_holes_mctxt C [MHole, D] \<sqinter> fill_holes_mctxt C [E, MHole] = C"
  by (simp add: inf_fill_holes_mctxt_MHoles nth_Cons')

lemma two_subterms_cases:
  assumes "s = C\<langle>t\<rangle>" and "s = D\<langle>u\<rangle>"
  obtains (eq) "C = D" and "t = u"
  | (nested1) C' where "C' \<noteq> \<box>" and "C = D \<circ>\<^sub>c C'"
  | (nested2) D' where "D' \<noteq> \<box>" and "D = C \<circ>\<^sub>c D'"
  | (parallel1) E where "num_holes E = 2"
    and "mctxt_of_ctxt C = fill_holes_mctxt E [MHole, mctxt_of_term u]"
    and "mctxt_of_ctxt D = fill_holes_mctxt E [mctxt_of_term t, MHole]"
  | (parallel2) E where "num_holes E = 2"
    and "mctxt_of_ctxt C = fill_holes_mctxt E [mctxt_of_term u, MHole]"
    and "mctxt_of_ctxt D = fill_holes_mctxt E [MHole, mctxt_of_term t]"
proof (atomize_elim, insert assms, induct s arbitrary: C t D u)
  case (Var x)
  then show ?case by (cases C; cases D; cases t; cases u) auto
next
  case (Fun f ss)
  { fix ts\<^sub>1 C' ts\<^sub>2 and us\<^sub>1 D' us\<^sub>2
    assume [simp]: "C = More f ts\<^sub>1 C' ts\<^sub>2" "D = More f us\<^sub>1 D' us\<^sub>2"
    then have len: "length (ts\<^sub>1 @ ts\<^sub>2) + 1 = length ss" "length (us\<^sub>1 @ us\<^sub>2) + 1 = length ss"
      using Fun.prems by (auto) (metis add_Suc_right length_Cons length_append nat.inject)
    { assume "length ts\<^sub>1 = length us\<^sub>1"
      with Fun have [simp]: "take (length ts\<^sub>1) ss = ts\<^sub>1" "drop (Suc (length ts\<^sub>1)) ss = ts\<^sub>2"
        and [simp]: "us\<^sub>1 = take (length ts\<^sub>1) ss" "us\<^sub>2 = drop (length ts\<^sub>1 + 1) ss"
        and nth: "C'\<langle>t\<rangle> = ss ! length ts\<^sub>1" and mem: "C'\<langle>t\<rangle> \<in> set ss"
        and eq: "C'\<langle>t\<rangle> = D'\<langle>u\<rangle>" by auto
      { assume "C' = D'" and "t = u"
        then have "C = D" and "t = u" by simp_all
        then have ?case by blast }
      moreover
      { fix C'' assume "C'' \<noteq> \<box>" and "C' = D' \<circ>\<^sub>c C''"
        then have "C'' \<noteq> \<box>" and "C = D \<circ>\<^sub>c C''" by auto
        then have ?case by blast }
      moreover
      { fix D'' assume "D'' \<noteq> \<box>" and "D' = C' \<circ>\<^sub>c D''"
        then have "D'' \<noteq> \<box>" and "D = C \<circ>\<^sub>c D''" by auto
        then have ?case by blast }
      moreover
      { fix E' assume [simp]: "mctxt_of_ctxt C' = fill_holes_mctxt E' [MHole, mctxt_of_term u]"
          "mctxt_of_ctxt D' = fill_holes_mctxt E' [mctxt_of_term t, MHole]"
          "num_holes E' = 2"
        define E where "E = MFun f (map mctxt_of_term ts\<^sub>1 @ E' # map mctxt_of_term ts\<^sub>2)"
        then have "num_holes E = 2" by simp
        moreover have "mctxt_of_ctxt C = fill_holes_mctxt E [MHole, mctxt_of_term u]"
          unfolding E_def and partition_holes_fill_holes_mctxt_conv' by simp
        moreover have "mctxt_of_ctxt D = fill_holes_mctxt E [mctxt_of_term t, MHole]"
          unfolding E_def and partition_holes_fill_holes_mctxt_conv' by simp
        ultimately have ?case by blast }
      moreover
      { fix E' assume [simp]: "mctxt_of_ctxt C' = fill_holes_mctxt E' [mctxt_of_term u, MHole]"
          "mctxt_of_ctxt D' = fill_holes_mctxt E' [MHole, mctxt_of_term t]"
          "num_holes E' = 2"
        define E where "E = MFun f (map mctxt_of_term ts\<^sub>1 @ E' # map mctxt_of_term ts\<^sub>2)"
        then have "num_holes E = 2" by simp
        moreover have "mctxt_of_ctxt C = fill_holes_mctxt E [mctxt_of_term u, MHole]"
          unfolding E_def and partition_holes_fill_holes_mctxt_conv' by simp
        moreover have "mctxt_of_ctxt D = fill_holes_mctxt E [MHole, mctxt_of_term t]"
          unfolding E_def and partition_holes_fill_holes_mctxt_conv' by simp
        ultimately have ?case by blast }
      ultimately have ?case using Fun.hyps [OF mem HOL.refl eq] by blast }
    moreover
    { assume *: "length ts\<^sub>1 < length us\<^sub>1"
      moreover then have us\<^sub>1: "us\<^sub>1 = ts\<^sub>1 @ C'\<langle>t\<rangle> # drop (length ts\<^sub>1 + 1) us\<^sub>1"
        using Fun.prems [simplified]
        apply (subst append_take_drop_id [symmetric, of _ "length ts\<^sub>1"])
        apply (rule arg_cong2 [where f = "(@)"])
         apply (force simp: append_eq_append_conv_if)
        apply (simp add: append_eq_append_conv_if)
        apply (cases us\<^sub>1)
        by auto
          (metis Cons_eq_appendI Cons_nth_drop_Suc calculation drop_Suc_Cons nth_append_length)
      ultimately have ss: "ss = ts\<^sub>1 @ C'\<langle>t\<rangle> # drop (length ts\<^sub>1 + 1) us\<^sub>1 @ D'\<langle>u\<rangle> # us\<^sub>2"
        using Fun.prems(2, 1) by auto
      have ts\<^sub>2: "ts\<^sub>2 = drop (length ts\<^sub>1 + 1) us\<^sub>1 @ D'\<langle>u\<rangle> # us\<^sub>2"
        using Fun.prems (2, 1) [simplified] and *
        apply (subst append_take_drop_id [symmetric, of _ "length (drop (length ts\<^sub>1 + 1) us\<^sub>1)"])
        apply (rule arg_cong2 [where f = "(@)"])
        by auto (metis Suc_eq_plus1 append_eq_conv_conj length_drop list.inject ss)+
      define E where "E = MFun f (map mctxt_of_term ts\<^sub>1 @ mctxt_of_ctxt C' #
        map mctxt_of_term (drop (length ts\<^sub>1 + 1) us\<^sub>1) @ mctxt_of_ctxt D' # map mctxt_of_term us\<^sub>2)"
      then have "num_holes E = 2" by simp
      moreover have "mctxt_of_ctxt C = fill_holes_mctxt E [MHole, mctxt_of_term u]"
        unfolding E_def and partition_holes_fill_holes_mctxt_conv' by (simp add: * ts\<^sub>2)
      moreover have "mctxt_of_ctxt D = fill_holes_mctxt E [mctxt_of_term t, MHole]"
        unfolding E_def and partition_holes_fill_holes_mctxt_conv' by (simp, subst us\<^sub>1, simp)
      ultimately have ?case by blast }
    moreover
    { assume *: "length us\<^sub>1 < length ts\<^sub>1"
      moreover then have ts\<^sub>1: "ts\<^sub>1 = us\<^sub>1 @ D'\<langle>u\<rangle> # drop (length us\<^sub>1 + 1) ts\<^sub>1"
        using Fun.prems [simplified]
        apply (subst append_take_drop_id [symmetric, of _ "length us\<^sub>1"])
        apply (rule arg_cong2 [where f = "(@)"])
         apply (force simp: append_eq_append_conv_if)
        apply (simp add: append_eq_append_conv_if)
        apply (cases ts\<^sub>1)
        by auto (metis Cons_eq_appendI Cons_nth_drop_Suc calculation drop_Suc_Cons nth_append_length)
      ultimately have ss: "ss = us\<^sub>1 @ D'\<langle>u\<rangle> # drop (length us\<^sub>1 + 1) ts\<^sub>1 @ C'\<langle>t\<rangle> # ts\<^sub>2"
        using Fun.prems by auto
      have us\<^sub>2: "us\<^sub>2 = drop (length us\<^sub>1 + 1) ts\<^sub>1 @ C'\<langle>t\<rangle> # ts\<^sub>2"
        using Fun.prems (2, 1) [simplified] and *
        apply (subst append_take_drop_id [symmetric, of _ "length (drop (length us\<^sub>1 + 1) ts\<^sub>1)"])
        apply (rule arg_cong2 [where f = "(@)"])                
        by auto (metis Suc_eq_plus1 append_eq_conv_conj length_drop list.inject ss)+
      define E where "E = MFun f (map mctxt_of_term us\<^sub>1 @ mctxt_of_ctxt D' #
        map mctxt_of_term (drop (length us\<^sub>1 + 1) ts\<^sub>1) @ mctxt_of_ctxt C' # map mctxt_of_term ts\<^sub>2)"
      then have "num_holes E = 2" by simp
      moreover have "mctxt_of_ctxt C = fill_holes_mctxt E [mctxt_of_term u, MHole]"
        unfolding E_def and partition_holes_fill_holes_mctxt_conv' by (simp, subst ts\<^sub>1, simp)
      moreover have "mctxt_of_ctxt D = fill_holes_mctxt E [MHole, mctxt_of_term t]"
        unfolding E_def and partition_holes_fill_holes_mctxt_conv' by (simp add: * us\<^sub>2)
      ultimately have ?case by blast }
    moreover
    have "length ts\<^sub>1 = length us\<^sub>1 \<or> length ts\<^sub>1 < length us\<^sub>1 \<or> length us\<^sub>1 < length ts\<^sub>1" by arith
    ultimately have ?case by blast }
  moreover
  { assume "C = \<box>" and "D \<noteq> \<box>" then have ?case by auto }
  moreover
  { assume "C \<noteq> \<box>" and "D = \<box>" then have ?case by auto }
  moreover
  { assume "C = \<box>" and "D = \<box>" then have ?case using Fun by simp }
  ultimately show ?case using Fun by (cases C; cases D) simp_all
qed

lemma two_hole_ctxt_inf_conv:
  "num_holes E = 2 \<Longrightarrow>
   mctxt_of_ctxt C = fill_holes_mctxt E [MHole, mctxt_of_term u] \<Longrightarrow>
   mctxt_of_ctxt D = fill_holes_mctxt E [mctxt_of_term t, MHole] \<Longrightarrow>
   mctxt_of_ctxt C \<sqinter> mctxt_of_ctxt D = E"
  by simp 

lemma map_length_take_partition_by:
  "i < length ys \<Longrightarrow> sum_list ys = length xs \<Longrightarrow>
    map length (take i (partition_by xs ys)) = take i ys"
  by (metis map_length_partition_by take_map)

text \<open>Closure under contexts can be lifted to multihole contexts.\<close>
lemma ctxt_imp_mctxt:
  assumes "\<forall>s t C. (s, t) \<in> R \<longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> R"
    and "(t, u) \<in> R"
    and "num_holes C = length ss\<^sub>1 + length ss\<^sub>2 + 1"
  shows "(fill_holes C (ss\<^sub>1 @ t # ss\<^sub>2), fill_holes C (ss\<^sub>1 @ u # ss\<^sub>2)) \<in> R"
  using assms
proof (induct C arbitrary: ss\<^sub>1 ss\<^sub>2)
  case (MFun f Cs)
  let ?f = "\<lambda>x. partition_holes (ss\<^sub>1 @ x # ss\<^sub>2) Cs"
  let ?ts = "?f t" and ?us = "?f u"
  have *: "\<And>x. concat (?f x) = ss\<^sub>1 @ x # ss\<^sub>2"
    using MFun.prems by (intro concat_partition_by) simp
  with less_length_concat [of "length ss\<^sub>1" ?ts]
  obtain i j where ij: "sum_list (map length (take i ?ts)) + j = length ss\<^sub>1"
    "i < length Cs" "j < length (?ts ! i)"
    and [simp]: "?ts ! i ! j = t" by auto
  have "length ss\<^sub>1 = sum_list (map length (take i ?us)) + j"
    using ij using MFun.prems(3) by (auto simp: take_map [symmetric])
  from concat_nth [OF _ _ this]
  have [simp]: "?us ! i ! j = u" using ij and MFun.prems(3) by auto
  have [simp]: "length ?us = length ?ts" by simp
  have [simp]: "take j (?us ! i) = take j (?ts ! i)"
    "drop (Suc j) (?us ! i) = drop (Suc j) (?ts ! i)"
    using ij and MFun.prems(3)
    by (auto intro: nth_equalityI simp: nth_append concat_nth [symmetric] take_map [symmetric])
  from MFun.hyps [of "Cs ! i", OF _ MFun.prems(1, 2), of "take j (?ts ! i)" "drop (Suc j) (?ts ! i)"]
  have step: "(fill_holes (Cs ! i) (?ts ! i), fill_holes (Cs ! i) (?us ! i)) \<in> R"
    using ij and MFun.prems
    apply simp
    apply (subst id_take_nth_drop [of j "?ts ! i"])
     apply simp
    apply (subst id_take_nth_drop [of j "?us ! i"])
     apply auto
    done

  let ?Cs = "map (case_prod fill_holes) (zip Cs ?ts)"
  let ?C = "More f (take i ?Cs) \<box> (drop (Suc i) ?Cs)"
  have [simp]:
    "take i (map (case_prod fill_holes) (zip Cs ?us)) = take i (map (case_prod fill_holes) (zip Cs ?ts))"
    "drop (Suc i) (map (case_prod fill_holes) (zip Cs ?us)) = drop (Suc i) (map (case_prod fill_holes) (zip Cs ?ts))"
    using ij and MFun.prems(3)
     apply (auto intro!: nth_equalityI)[2]
    subgoal 
      using partition_by_nth_less [of _ i "map num_holes Cs" ss\<^sub>1 j _ ss\<^sub>2]
      by (simp add: map_length_take_partition_by)
    subgoal using partition_by_nth_greater [of i "Suc (i + k)" for k, of _ "map num_holes Cs" j ss\<^sub>1 _ ss\<^sub>2]
      by (simp add: map_length_take_partition_by)
    done
  show ?case
    using MFun.prems(1) [rule_format, OF step, of ?C] and ij
    apply (clarsimp simp del: fill_holes.simps simp: partition_holes_fill_holes_conv')
    apply (subst id_take_nth_drop [of i "map (case_prod fill_holes) (zip Cs ?ts)"], simp)
    apply (subst id_take_nth_drop [of i "map (case_prod fill_holes) (zip Cs ?us)"], simp)
    by auto
qed auto

lemma mctxt_of_term_fill_holes':
  "num_holes C = length ts \<Longrightarrow> mctxt_of_term (fill_holes C ts) = fill_holes_mctxt C (map mctxt_of_term ts)"
  by (induct C ts rule: fill_holes_induct) auto

lemma vars_term_fill_holes':
  "num_holes C = length ts \<Longrightarrow> vars_term (fill_holes C ts) = \<Union>(vars_term ` set ts) \<union> vars_mctxt C"
proof (induct C ts rule: fill_holes_induct)
  case (MFun f Cs ts) then show ?case
    using UN_upt_len_conv[of "partition_holes ts Cs" "length Cs" "\<lambda>t. (\<Union>x\<in>set t. vars_term x)"]
    by (simp add: UN_Un_distrib UN_set_partition_by)
qed auto

lemma vars_mctxt_linear: assumes "t =\<^sub>f (C, ts)" 
  "linear_term t"
shows "vars_mctxt C \<inter> \<Union> (vars_term ` set ts) = {}" 
  using assms
proof (induct C arbitrary: t ts)
  case (MVar x)
  from eqf_MVarE[OF MVar(1)]  
  show ?case by auto
next
  case MHole
  from eqf_MHoleE[OF MHole(1)]
  show ?case by auto
next
  case (MFun f Cs t ss)
  from eqf_MFunE[OF MFun(2)] obtain ts sss where
    *: "t = Fun f ts" "length ts = length Cs" "length sss = length Cs" 
    "\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)"
    "ss = concat sss" by blast
  {
    fix i
    assume i: "i < length Cs" 
    hence mem: "Cs ! i \<in> set Cs" by auto
    from * i MFun(3) have lin: "linear_term (ts ! i)" by auto
    from MFun(1)[OF mem *(4)[OF i] lin]
    have "vars_mctxt (Cs ! i) \<inter> \<Union> (vars_term ` set (sss ! i)) = {}" by auto
  } note IH = this
  show ?case 
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    then obtain x where xC: "x \<in> vars_mctxt (MFun f Cs)" and xss: "x \<in> \<Union> (vars_term ` set ss)" 
      by auto
    from xC obtain i where i: "i < length Cs" and x: "x \<in> vars_mctxt (Cs ! i)" 
      by (auto simp: set_conv_nth)
    from IH[OF i] x have xni: "x \<notin> \<Union> (vars_term ` set (sss ! i))" by auto
    from *(4)[OF i] have "ts ! i =\<^sub>f (Cs ! i, sss ! i)" .
    from eqfE[OF this] x have xi: "x \<in> vars_term (ts ! i)"
      by (simp add: vars_term_fill_holes')
    from xss[unfolded * set_concat] * obtain j where 
      j: "j < length Cs" and xsj: "x \<in> \<Union> (vars_term ` set (sss ! j))" 
      unfolding set_conv_nth by auto
    from *(4)[OF j] have "ts ! j =\<^sub>f (Cs ! j, sss ! j)" by auto
    from eqfE[OF this] xsj j have xj: "x \<in> vars_term (ts ! j)" 
      by (simp add: vars_term_fill_holes')
    from xi xj i j \<open>linear_term t\<close>[unfolded *(1)]
    have "i = j" unfolding \<open>length ts = length Cs\<close>[symmetric]
      by (auto simp: is_partition_alt is_partition_alt_def)
    with xni xsj show False by auto
  qed
qed

lemma mctxt_of_term_var_subst:
  "mctxt_of_term (t \<cdot> (Var \<circ> f)) = map_vars_mctxt f (mctxt_of_term t)"
  by (induct t) auto

lemma subst_apply_mctxt_map_vars_mctxt_conv:
  "C \<cdot>mc (Var \<circ> f) = map_vars_mctxt f C"
  by (induct C) auto

lemma map_vars_mctxt_mono:
  "C \<le> D \<Longrightarrow> map_vars_mctxt f C \<le> map_vars_mctxt f D"
  by (induct C D rule: less_eq_mctxt_induct) (auto intro: less_eq_mctxtI1)

lemma map_vars_mctxt_less_eq_decomp:
  assumes "C \<le> map_vars_mctxt f D"
  obtains C' where "map_vars_mctxt f C' = C" "C' \<le> D"
  using assms
proof (induct D arbitrary: C thesis)
  case (MVar x) show ?case using MVar(1)[of MHole] MVar(1)[of "MVar _"] MVar(2)
    by (auto elim: less_eq_mctxtE2 intro: less_eq_mctxtI1)
next
  case MHole show ?case using MHole(1)[of MHole] MHole(2) by (auto elim: less_eq_mctxtE2)
next
  case (MFun g Ds) note MFun' = MFun
  show ?case using MFun(3) unfolding map_vars_mctxt.simps
  proof (cases rule: less_eq_mctxtE2(3))
    case MHole then show ?thesis using MFun(2)[of MHole] by auto
  next
    case (MFun Cs)
    define Cs' where "Cs' = map (\<lambda>i. SOME Ci'. map_vars_mctxt f Ci' = Cs ! i \<and> Ci' \<le> Ds ! i) [0..<length Cs]"
    { fix i assume "i < length Cs"
      obtain Ci' where "map_vars_mctxt f Ci' = Cs ! i" "Ci' \<le> Ds ! i"
        using \<open>i < length Cs\<close> MFun MFun'(1)[OF nth_mem, of i] MFun'(3) by (auto elim!: less_eq_mctxtE2)
      then have "\<exists>Ci'. map_vars_mctxt f Ci' = Cs ! i \<and> Ci' \<le> Ds ! i" by blast
    }
    from someI_ex[OF this] have
      "length Cs = length Cs'" and "i < length Cs \<Longrightarrow> map_vars_mctxt f (Cs' ! i) = Cs ! i"
      "i < length Cs \<Longrightarrow> Cs' ! i \<le> Ds ! i" for i by (auto simp: Cs'_def)
    then show ?thesis using MFun(1,2) MFun'(3)
      by (auto intro!: MFun'(2)[of "MFun g Cs'"] nth_equalityI less_eq_mctxtI2 elim!: less_eq_mctxtE2)
  qed
qed

subsubsection \<open>All positions of a multi-hole context\<close>

fun all_poss_mctxt :: "('f, 'v) mctxt \<Rightarrow> pos set"
  where
    "all_poss_mctxt (MVar x) = {[]}"
  | "all_poss_mctxt MHole = {[]}"
  | "all_poss_mctxt (MFun f cs) = {[]} \<union> \<Union>(set (map (\<lambda> i. (\<lambda> p. i # p) ` all_poss_mctxt (cs ! i)) [0 ..< length cs]))"

lemma all_poss_mctxt_simp [simp]:
  "all_poss_mctxt (MFun f cs) = {[]} \<union> {i # p | i p. i < length cs \<and> p \<in> all_poss_mctxt (cs ! i)}"
  by auto

declare all_poss_mctxt.simps(3)[simp del]

lemma all_poss_mctxt_conv:
  "all_poss_mctxt C = poss_mctxt C \<union> hole_poss C"
  by (induct C) auto

lemma root_in_all_poss_mctxt[simp]:
  "[] \<in> all_poss_mctxt C"
  by (cases C) auto

lemma hole_poss_mctxt_of_term[simp]:
  "hole_poss (mctxt_of_term t) = {}"
  by (induct t) auto

lemma poss_mctxt_mctxt_of_term[simp]:
  "poss_mctxt (mctxt_of_term t) = poss t"
  by (induct t) auto

lemma hole_poss_subst: "hole_poss (C \<cdot>mc \<sigma>) = hole_poss C"
  by (induct C, auto)


lemma all_poss_mctxt_mctxt_of_term[simp]:
  "all_poss_mctxt (mctxt_of_term t) = poss t"
  by (induct t) auto

lemma mctxt_of_term_leq_imp_eq:
  "mctxt_of_term t \<le> C \<longleftrightarrow> mctxt_of_term t = C"
  by (induct t arbitrary: C) (auto elim!: less_eq_mctxtE1 simp: map_nth_eq_conv)

lemma mctxt_of_term_inj:
  "mctxt_of_term s = mctxt_of_term t \<longleftrightarrow> s = t"
proof (induct s arbitrary: t)
  case (Var x t)
  show ?case by (cases t, auto)
next
  case (Fun f ss t)
  thus ?case by (cases t, auto simp: map_eq_conv' intro: nth_equalityI)
qed 

lemma all_poss_mctxt_map_vars_mctxt [simp]:
  "all_poss_mctxt (map_vars_mctxt f C) = all_poss_mctxt C"
  by (induct C) auto

lemma fill_holes_mctxt_extends_all_poss:
  assumes "length Ds = num_holes C" shows "all_poss_mctxt C \<subseteq> all_poss_mctxt (fill_holes_mctxt C Ds)"
  using assms[symmetric] by (induct C Ds rule: fill_holes_induct) force+


lemma eqF_substD:
  assumes "t \<cdot> \<sigma> =\<^sub>f (C, ss)"
    "hole_poss C \<subseteq> poss t" 
  shows "\<exists> D ts. t =\<^sub>f (D, ts) \<and> C = D \<cdot>mc \<sigma> \<and> ss = map (\<lambda> ti. ti \<cdot> \<sigma>) ts" 
  using assms
proof (induct C arbitrary: t ss)
  case (MVar x t ss)
  from eqfE[OF MVar(1)] obtain y where "t = Var y" "\<sigma> y = Var x" "ss = []" by (cases t, auto)
  thus ?case using MVar by (auto intro!: exI[of _ "MVar y"])
next
  case (MHole t ss)
  from eqfE[OF MHole(1)]
  show ?case by (cases ss, auto intro!: exI[of _ MHole] exI[of _ "[t]"])
next
  case (MFun f Cs t ss)
  show ?case
  proof (cases "is_Fun t")
    case True
    from eqf_MFunE[OF MFun(2)] obtain tss sss where
      tsigma: "t \<cdot> \<sigma> = Fun f tss" and len: "length tss = length Cs" "length sss = length Cs" 
      and args: "\<And> i. i < length Cs \<Longrightarrow> tss ! i =\<^sub>f (Cs ! i, sss ! i)"
      and ss: "ss = concat sss" by auto
    from True tsigma obtain ts where t: "t = Fun f ts" by (cases t, auto)
    from tsigma[unfolded t] have ts: "tss = map (\<lambda> t. t \<cdot> \<sigma>) ts" by auto
    from len ts have "length ts = length Cs" by auto
    note len = this len
    {
      fix i
      assume i: "i < length Cs" 
      hence "Cs ! i \<in> set Cs" by auto
      note IH = MFun(1)[OF this]
      from ts len i have "ts ! i \<cdot> \<sigma> = tss ! i" by auto
      also have "\<dots> =\<^sub>f (Cs ! i, sss ! i)" using args[OF i] .
      finally have "ts ! i \<cdot> \<sigma> =\<^sub>f (Cs ! i, sss ! i)" .
      note IH = IH[OF this]
      from MFun(3)[unfolded t] i len
      have "hole_poss (Cs ! i) \<subseteq> poss (ts ! i)" by auto
      note IH = IH[OF this]
    }
    hence "\<forall> i. \<exists> D tsi. i < length Cs \<longrightarrow> ts ! i =\<^sub>f (D, tsi) \<and> Cs ! i = D \<cdot>mc \<sigma> \<and> sss ! i = map (\<lambda>ti. ti \<cdot> \<sigma>) tsi" by blast
    from choice[OF this] obtain D where 
      "\<forall> i. \<exists> tsi. i < length Cs \<longrightarrow> ts ! i =\<^sub>f (D i, tsi) \<and> Cs ! i = D i \<cdot>mc \<sigma> \<and> sss ! i = map (\<lambda>ti. ti \<cdot> \<sigma>) tsi" ..
    from choice[OF this] obtain tsi where 
      IH: "i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (D i, tsi i) \<and> Cs ! i = D i \<cdot>mc \<sigma> \<and> sss ! i = map (\<lambda>ti. ti \<cdot> \<sigma>) (tsi i)" for i
      by auto
    let ?n = "[0 ..< length Cs]" 
    show ?thesis
    proof (rule exI[of _ "MFun f (map D ?n)"], rule exI[of _ "concat (map tsi ?n)"], intro conjI)
      show "MFun f Cs = MFun f (map D ?n) \<cdot>mc \<sigma>" using IH by (auto intro: nth_equalityI)
      show "ss = map (\<lambda>ti. ti \<cdot> \<sigma>) (concat (map tsi ?n))" unfolding ss
        using len(3) IH unfolding map_concat map_map o_def
        by (intro arg_cong[of _ _ concat], intro nth_equalityI, auto)
      show "t =\<^sub>f (MFun f (map D ?n), concat (map tsi ?n))" unfolding t
        by (intro eqf_MFunI, insert len IH, auto)
    qed
  next
    case False
    then obtain x where t: "t = Var x" by auto
    with MFun(3) have "hole_poss (MFun f Cs) = {}" by auto
    hence num: "num_holes (MFun f Cs) = 0" using hole_poss_empty_iff_num_holes_0 by blast
    with eqfE[OF MFun(2)] t have ss: "ss = []" "\<sigma> x = fill_holes (MFun f Cs) []" by auto
    show ?thesis unfolding t ss
    proof (intro exI[of _ "MVar x"] exI[of _ Nil] conjI)
      have "MVar x \<cdot>mc \<sigma> = mctxt_of_term (fill_holes (MFun f Cs) [])" using ss by simp
      also have "\<dots> = MFun f Cs" using num
        by (metis mctxt_of_term_fill_holes mctxt_of_term_term_of_mctxt_id)
      finally show "MFun f Cs = MVar x \<cdot>mc \<sigma>" ..
    qed auto
  qed
qed

subsubsection \<open>More operations on multi-hole contexts\<close>

fun root_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f \<times> nat) option" where
  "root_mctxt MHole = None"
| "root_mctxt (MVar x) = None"
| "root_mctxt (MFun f Cs) = Some (f, length Cs)"

fun mreplace_at :: "('f, 'v) mctxt \<Rightarrow> pos \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt" where
  "mreplace_at C [] D = D"
| "mreplace_at (MFun f Cs) (i # p) D = MFun f (take i Cs @ mreplace_at (Cs ! i) p D # drop (i+1) Cs)"
  (* Should use @{term "Cs[i := mreplace_at (Cs ! i)"}? see also @{thm upd_conv_take_nth_drop} *)

fun subm_at :: "('f, 'v) mctxt \<Rightarrow> pos \<Rightarrow> ('f, 'v) mctxt" where
  "subm_at C [] = C"
| "subm_at (MFun f Cs) (i # p) = subm_at (Cs ! i) p"

lemma subm_at_hole_poss[simp]:
  "p \<in> hole_poss C \<Longrightarrow> subm_at C p = MHole"
  by (induct C arbitrary: p) auto

lemma subm_at_mctxt_of_term:
  "p \<in> poss t \<Longrightarrow> subm_at (mctxt_of_term t) p = mctxt_of_term (subt_at t p)"
  by (induct t arbitrary: p) auto

lemma subm_at_mreplace_at[simp]:
  "p \<in> all_poss_mctxt C \<Longrightarrow> subm_at (mreplace_at C p D) p = D"
  by (induct C arbitrary: p) (auto simp: nth_append_take)

lemma replace_at_subm_at[simp]:
  "p \<in> all_poss_mctxt C \<Longrightarrow> mreplace_at C p (subm_at C p) = C"
  by (induct C arbitrary: p) (auto simp: id_take_nth_drop[symmetric])

lemma all_poss_mctxt_mreplace_atI1:
  "p \<in> all_poss_mctxt C \<Longrightarrow> q \<in> all_poss_mctxt C \<Longrightarrow> \<not> (p <\<^sub>p q) \<Longrightarrow> q \<in> all_poss_mctxt (mreplace_at C p D)"
proof (induct C arbitrary: p q)
  let ?hd = "\<lambda>p. (case p :: pos of i # _ \<Rightarrow> i)"
  case (MFun f Cs) then show ?case
    by (cases "?hd p = ?hd q") (auto simp: nth_append_take less_pos_def nth_append_drop_is_nth_conv nth_append_take_drop_is_nth_conv)
qed auto

lemma funas_mctxt_sup_mctxt:
  "(C, D) \<in> comp_mctxt \<Longrightarrow> funas_mctxt (C \<squnion> D) = funas_mctxt C \<union> funas_mctxt D"
  by (induct C D rule: comp_mctxt.induct) (auto simp: zip_nth_conv Un_Union_image)

lemma mctxt_of_term_not_hole [simp]:
  "mctxt_of_term t \<noteq> MHole"
  by (cases t) auto

lemma funas_mctxt_mctxt_of_term [simp]:
  "funas_mctxt (mctxt_of_term t) = funas_term t"
  by (induct t) auto

lemma funas_mctxt_mreplace_at:
  assumes "p \<in> all_poss_mctxt C"
  shows "funas_mctxt (mreplace_at C p D) \<subseteq> funas_mctxt C \<union> funas_mctxt D"
  using assms
proof (induct C p D rule: mreplace_at.induct)
  case (2 f Cs i p D) then have Cs: "Cs = take i Cs @ Cs ! i # drop (Suc i) Cs"
    by (auto simp: id_take_nth_drop)
  show ?case using 2 by (subst (2) Cs) auto
qed auto

lemma funas_mctxt_mreplace_at_hole:
  assumes "p \<in> hole_poss C"
  shows "funas_mctxt (mreplace_at C p D) = funas_mctxt C \<union> funas_mctxt D" (is "?L = ?R")
proof
  show "?R \<subseteq> ?L" using assms
  proof (induct C p D rule: mreplace_at.induct)
    case (1 C D) then show ?case by (cases C) auto
  next
    case (2 f Cs i p D) then have Cs: "Cs = take i Cs @ Cs ! i # drop (Suc i) Cs"
      by (auto simp: id_take_nth_drop)
    show ?case using 2 by (subst (1) Cs) auto
  qed auto
next
  show "?L \<subseteq> ?R" using assms by (auto simp: all_poss_mctxt_conv funas_mctxt_mreplace_at)
qed

lemma map_vars_mctxt_fill_holes_mctxt:
  assumes "num_holes C = length Cs"
  shows "map_vars_mctxt f (fill_holes_mctxt C Cs) = fill_holes_mctxt (map_vars_mctxt f C) (map (map_vars_mctxt f) Cs)"
  using assms by (induct C Cs rule: fill_holes_induct) (auto simp: comp_def)

lemma map_vars_mctxt_map_vars_mctxt[simp]:
  shows "map_vars_mctxt f (map_vars_mctxt g C) = map_vars_mctxt (f \<circ> g) C"
  by (induct C) auto

lemma funas_mctxt_fill_holes:
  assumes "num_holes C = length ts"
  shows "funas_term (fill_holes C ts) = funas_mctxt C \<union> \<Union>(set (map funas_term ts))"
  using funas_term_fill_holes_iff[OF assms] by auto

lemma mctxt_neq_mholeE:
  "x \<noteq> MHole \<Longrightarrow> (\<And>v. x = MVar v \<Longrightarrow> P) \<Longrightarrow> (\<And>f Cs. x = MFun f Cs \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases x) auto

lemma prefix_comp_mctxt:
  "C \<le> E \<Longrightarrow> D \<le> E \<Longrightarrow> (C, D) \<in> comp_mctxt"
proof (induct E arbitrary: C D)
  case (MFun f Es C D)
  then show ?case
  proof (elim less_eq_mctxtE2)
    fix Cs Ds
    assume C: "C = MFun f Cs" and D: "D = MFun f Ds"
      and lC: "length Cs = length Es" and lD: "length Ds = length Es"
      and Ci: "\<And>i. i < length Cs \<Longrightarrow> Cs ! i \<le> Es ! i" and Di: "\<And>i. i < length Ds \<Longrightarrow> Ds ! i \<le> Es ! i"
      and IH: "\<And>E' C' D'. E' \<in> set Es \<Longrightarrow> C' \<le> E' \<Longrightarrow> D' \<le> E' \<Longrightarrow> (C', D') \<in> comp_mctxt"
    show "(C, D) \<in> comp_mctxt"
      by (auto simp: C D lC lD intro!: comp_mctxt.intros IH[OF _ Ci Di])
  qed (auto intro: comp_mctxt.intros)
qed (auto elim: less_eq_mctxtE2(1,2) intro: comp_mctxt.intros)

lemma less_eq_mctxt_sup_conv1:
  "(C, D) \<in> comp_mctxt \<Longrightarrow> C \<le> D \<longleftrightarrow> C \<squnion> D = D"
  by (induct C D rule: comp_mctxt.induct) (auto elim!: less_eq_mctxtE2 nth_equalityE intro: nth_equalityI less_eq_mctxtI2(3))

lemma less_eq_mctxt_sup_conv2:
  "(C, D) \<in> comp_mctxt \<Longrightarrow> D \<le> C \<longleftrightarrow> C \<squnion> D = C"
  using less_eq_mctxt_sup_conv1[OF comp_mctxt_sym] by (auto simp: ac_simps)

lemma comp_mctxt_mctxt_of_term1[dest!]:
  "(C, mctxt_of_term t) \<in> comp_mctxt \<Longrightarrow> C \<le> mctxt_of_term t"
proof (induct C "mctxt_of_term t" arbitrary: t rule: comp_mctxt.induct)
  case (MHole2 C t)
  then show ?case by (cases t, auto)
next
  case (MFun f g Cs Ds)
  then show ?case by (cases t, auto intro: less_eq_mctxtI2)
qed auto

lemmas comp_mctxt_mctxt_of_term2[dest!] = comp_mctxt_mctxt_of_term1[OF comp_mctxt_sym]

lemma mfun_leq_mfunI:
  "f = g \<Longrightarrow> length Cs = length Ds \<Longrightarrow> (\<And>i. i < length Ds \<Longrightarrow> Cs ! i \<le> Ds ! i) \<Longrightarrow> MFun f Cs \<le> MFun g Ds"
  by (auto simp: less_eq_mctxt_def list_eq_iff_nth_eq)

lemma prefix_mctxt_sup:
  assumes "C \<le> (E :: ('f, 'v) mctxt)" "D \<le> E" shows "C \<squnion> D \<le> E"
  using assms
  by (induct E arbitrary: C D) (auto elim!: less_eq_mctxtE2 intro!: mfun_leq_mfunI)

lemma mreplace_at_leqI:
  "p \<in> all_poss_mctxt C \<Longrightarrow> C \<le> E \<Longrightarrow> D \<le> subm_at E p \<Longrightarrow> mreplace_at C p D \<le> E"
  by (induct C p D arbitrary: E rule: mreplace_at.induct)
    (auto elim!: less_eq_mctxtE1 intro!: less_eq_mctxtI1 simp: upd_conv_take_nth_drop[symmetric] nth_list_update)

lemma prefix_and_fewer_holes_implies_equal_mctxt:
  "C \<le> D \<Longrightarrow> hole_poss C \<subseteq> hole_poss D \<Longrightarrow> C = D"
proof (induct C D rule: less_eq_mctxt_induct)
  case (1 D) then show ?case by (cases D) auto
next
  case (3 Cs Ds f)
  have "i < length Ds \<Longrightarrow> hole_poss (Cs ! i) \<subseteq> hole_poss (Ds ! i)" for i using 3(1,4) by auto
  then show ?case using 3 by (auto intro!: nth_equalityI)
qed auto

lemma compare_mreplace_at:
  "p \<in> poss_mctxt C \<Longrightarrow> mreplace_at C p D \<le> mreplace_at C p E \<longleftrightarrow> D \<le> E"
proof (induct C arbitrary: p)
  case (MFun f Cs p)
  then show ?case 
    by (cases p, auto elim!: less_eq_mctxtE2(3) intro!: less_eq_mctxt_intros(3) simp: nth_append nth_Cons'
        split: if_splits) auto
qed auto


lemma merge_mreplace_at:
  "p \<in> poss_mctxt C \<Longrightarrow> mreplace_at C p (D \<squnion> E) =  mreplace_at C p D \<squnion> mreplace_at C p E"
proof (induct C arbitrary: p)
  case (MFun f Cs p)
  then show ?case by (cases p, auto intro: nth_equalityI)
qed auto


lemma compare_mreplace_atI':
  "C \<le> D \<Longrightarrow> C' \<le> D' \<Longrightarrow> p \<in> all_poss_mctxt C \<Longrightarrow> mreplace_at C p C' \<le> mreplace_at D p D'"
proof (induct C D arbitrary: p rule: less_eq_mctxt_induct)
  case (3 cs ds f p)
  then show ?case by (cases p, auto intro!: less_eq_mctxt_intros(3) simp: nth_append nth_Cons')
qed auto

lemma compare_mreplace_atI:
  "C \<le> D \<Longrightarrow> C' \<le> D' \<Longrightarrow> p \<in> poss_mctxt C \<Longrightarrow> mreplace_at C p C' \<le> mreplace_at D p D'"
  using compare_mreplace_atI' all_poss_mctxt_conv by blast

lemma all_poss_mctxt_mono:
  "C \<le> D \<Longrightarrow> all_poss_mctxt C \<subseteq> all_poss_mctxt D"
  by (induct C D rule: less_eq_mctxt_induct) force+

lemma all_poss_mctxt_inf_mctxt:
  "(C, D) \<in> comp_mctxt \<Longrightarrow> all_poss_mctxt (C \<sqinter> D) = all_poss_mctxt C \<inter> all_poss_mctxt D"
  by (induct C D rule: comp_mctxt.induct) auto

lemma less_eq_subm_at:
  "p \<in> all_poss_mctxt C \<Longrightarrow> C \<le> D \<Longrightarrow> subm_at C p \<le> subm_at D p"
  by (induct C arbitrary: p D) (auto elim: less_eq_mctxtE1)

lemma inf_subm_at:
  "p \<in> all_poss_mctxt (C \<sqinter> D) \<Longrightarrow> subm_at (C \<sqinter> D) p = subm_at C p \<sqinter> subm_at D p"
proof (induct C D arbitrary: p rule: inf_mctxt.induct)
  case (4 f Cs g Ds p) show ?case using 4(1) 4(2)
    by (auto 4 4 intro!: 4(1)[of "(Cs ! i, Ds ! i)" "Cs ! i" "Ds ! i" for i] simp: set_zip)
qed auto

lemma less_eq_fill_holesI:
  assumes "length Ds = num_holes C" "length Es = num_holes C"
    "\<And>i. i < num_holes C \<Longrightarrow> Ds ! i \<le> Es ! i"
  shows "fill_holes_mctxt C Ds \<le> fill_holes_mctxt C Es"
  using assms(1,2)[symmetric] assms(3)
  by (induct C Ds Es rule: fill_holes_induct2) (auto intro!: less_eq_mctxtI1 simp: partition_by_nth_nth)

lemma less_eq_fill_holesD:
  assumes "length Ds = num_holes C" "length Es = num_holes C"
    "fill_holes_mctxt C Ds \<le> fill_holes_mctxt C Es" "i < num_holes C"
  shows "Ds ! i \<le> Es ! i"
  using assms(1,2)[symmetric] assms(3,4)
proof (induct C Ds Es arbitrary: i rule: fill_holes_induct2)
  case (MFun f Cs Ds Es)
  obtain j k where "j < length Cs" "k < num_holes (Cs ! j)"
    "zip Ds Es ! i = partition_holes (zip Ds Es) Cs ! j ! k"
    using nth_concat_split[of i "partition_holes (zip Ds Es) Cs"] MFun(1,2,5) by auto
  moreover then have "f (zip Ds Es ! i) = partition_holes (map f (zip Ds Es)) Cs ! j ! k" for f
    using nth_map[of k "partition_holes (zip Ds Es) Cs ! j" f] MFun(1,2)
      length_partition_by_nth[of "map num_holes Cs" "zip Ds Es"] by simp
  from this[of fst] this[of snd] map_fst_zip[of Ds Es] map_snd_zip[of Ds Es]
  have "Ds ! i = partition_holes Ds Cs ! j ! k" "Es ! i = partition_holes Es Cs ! j ! k"
    using MFun(1,2,5) by simp_all
  ultimately show ?case using MFun(3)[of j k] MFun(1,2,4) by (auto elim: less_eq_mctxtE1)
qed auto

lemma less_eq_fill_holes_iff:
  assumes "length Ds = num_holes C" "length Es = num_holes C"
  shows "fill_holes_mctxt C Ds \<le> fill_holes_mctxt C Es \<longleftrightarrow> (\<forall>i < num_holes C. Ds ! i \<le> Es ! i)"
  using assms by (auto intro: less_eq_fill_holesI dest: less_eq_fill_holesD)

lemma fill_holes_mctxt_suffix[simp]:
  assumes "length Ds = num_holes C" shows "C \<le> fill_holes_mctxt C Ds"
  using assms(1)[symmetric]
  by (induct C Ds rule: fill_holes_induct) (auto simp: less_eq_mctxt_def intro: nth_equalityI)

lemma fill_holes_mctxt_id:
  assumes "length Ds = num_holes C" "C = fill_holes_mctxt C Ds" shows "set Ds \<subseteq> {MHole}"
  using assms(1)[symmetric] assms(2)
  apply (induct C Ds rule: fill_holes_induct)
  unfolding set_concat
  by (auto simp: set_conv_nth[of "partition_holes _ _"] list_eq_iff_nth_eq[of _ "map _ _"])

lemma fill_holes_suffix[simp]:
  "num_holes C = length ts \<Longrightarrow> C \<le> mctxt_of_term (fill_holes C ts)"
  by (induct C ts rule: fill_holes_induct) (auto intro: less_eq_mctxtI1)

subsubsection \<open>An inverse of @{term fill_holes}\<close>

fun unfill_holes :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list" where
  "unfill_holes MHole t = [t]"
| "unfill_holes (MVar w) (Var v) = (if v = w then [] else undefined)"
| "unfill_holes (MFun g Cs) (Fun f ts) = (if f = g \<and> length ts = length Cs then
    concat (map (\<lambda>i. unfill_holes (Cs ! i) (ts ! i)) [0..<length ts]) else undefined)"

lemma length_unfill_holes[simp]:
  assumes "C \<le> mctxt_of_term t"
  shows "length (unfill_holes C t) = num_holes C"
  using assms
proof (induct C t rule: unfill_holes.induct)
  case (3 f Cs g ts) with 3(1)[OF _ nth_mem] 3(2) show ?case
    by (auto simp: less_eq_mctxt_def length_concat
        intro!: cong[of sum_list, OF refl] nth_equalityI elim!: nth_equalityE)
qed (auto simp: less_eq_mctxt_def)

lemma fill_unfill_holes:
  assumes "C \<le> mctxt_of_term t"
  shows "fill_holes C (unfill_holes C t) = t"
  using assms
proof (induct C t rule: unfill_holes.induct)
  case (3 f Cs g ts) with 3(1)[OF _ nth_mem] 3(2) show ?case
    by (auto simp: less_eq_mctxt_def intro!: fill_holes_arbitrary elim!: nth_equalityE)
qed (auto simp: less_eq_mctxt_def split: if_splits)

lemma unfill_fill_holes:
  assumes "length ts = num_holes C"
  shows "unfill_holes C (fill_holes C ts) = ts"
  using assms[symmetric]
proof (induct C ts rule: fill_holes_induct)
  case (MFun f Cs ts) then show ?case
    by (auto intro!: arg_cong[of _ _ concat] nth_equalityI[of _ "partition_holes ts Cs"]
        simp del: concat_partition_by) auto
qed auto

lemma unfill_holes_subt:
  assumes "C \<le> mctxt_of_term t" and "t' \<in> set (unfill_holes C t)"
  shows "t' \<unlhd> t"
  using assms
proof (induct C t rule: unfill_holes.induct)
  case (3 f Cs g ts)
  obtain i where "i < length Cs" and "t' \<in> set (unfill_holes (Cs ! i) (ts ! i))"
    using 3 by (auto dest!: in_set_idx split: if_splits simp: less_eq_mctxt_def)
  then show ?case
    using 3(1)[OF _ nth_mem[of i]] 3(2,3) supteq.subt[of "ts ! i" ts t' g]
    by (auto simp: less_eq_mctxt_def elim!: nth_equalityE split: if_splits)
qed (auto simp: less_eq_mctxt_def split: if_splits)

lemma factor_hole_pos_by_prefix:
  assumes "C \<le> D" "p \<in> hole_poss D"
  obtains q where "q \<le>\<^sub>p p" "q \<in> hole_poss C"
  using assms
  by (induct C D arbitrary: p thesis rule: less_eq_mctxt_induct)
    (auto, metis less_eq_pos_simps(4))

lemma concat_map_zip_upt: assumes "\<And>i. i < n \<Longrightarrow> length (f i) = length (g i)" 
  shows "concat (map (\<lambda>i. zip (f i) (g i)) [0..<n]) = zip (concat (map f [0..<n])) (concat (map g [0..<n]))" 
  using assms by (induct n arbitrary: f g) (auto simp: map_upt_Suc simp del: upt.simps)

lemma unfill_holes_by_prefix':
  assumes "num_holes C = length Ds" "fill_holes_mctxt C Ds \<le> mctxt_of_term t"
  shows "unfill_holes (fill_holes_mctxt C Ds) t = concat (map (\<lambda>(D, t). unfill_holes D t) (zip Ds (unfill_holes C t)))"
  using assms
proof (induct C Ds arbitrary: t rule: fill_holes_induct)
  case (MVar v) then show ?case by (cases t) (auto elim: less_eq_mctxtE1)
next
  case (MFun f Cs Ds)
  have [simp]: "length ts = length Cs \<Longrightarrow> map (\<lambda>i. unfill_holes (map (\<lambda>i. fill_holes_mctxt (Cs ! i) (partition_holes Ds Cs ! i))
    [0..<length Cs] ! i) (ts ! i)) [0..<length Cs]
    =  map (\<lambda>i. unfill_holes (fill_holes_mctxt (Cs ! i) (partition_holes Ds Cs ! i)) (ts ! i)) [0..<length Cs]" for ts
    by (auto intro: nth_equalityI)
  obtain ts where lts: "length ts = length Cs" "t = Fun f ts" and
    pre: "i < length Cs \<Longrightarrow> fill_holes_mctxt (Cs ! i) (partition_holes Ds Cs ! i) \<le> mctxt_of_term (ts ! i)" for i
    using MFun(1,3) by (cases t) (auto elim!: less_eq_mctxtE2) 
  have *: "i \<in> set [0..<n] \<Longrightarrow> i < n" for i n by auto
  have ***: "i < length Cs \<Longrightarrow> Cs ! i \<le> mctxt_of_term (ts ! i)" for i
    using fill_holes_mctxt_suffix[of "partition_holes Ds Cs ! i" "Cs ! i", OF length_partition_holes_nth] MFun(1) pre[of i]
    by (auto simp del: fill_holes_mctxt_suffix)
  have [simp]: "concat (map (\<lambda>i. concat (map f (zip (partition_holes Ds Cs ! i) (unfill_holes (Cs ! i) (ts ! i)))))
    [0..<length Cs]) = concat (map f (zip Ds (concat (map (\<lambda>i. unfill_holes (Cs ! i) (ts ! i)) [0..<length Cs]))))" 
    for f
    unfolding concat_map_concat[of "map _ _", unfolded map_map comp_def]
    unfolding map_map[of "map f" "\<lambda>i. zip (_ i) (_ i)", symmetric, unfolded comp_def] map_concat[symmetric]
    using MFun(1) map_nth[of "partition_holes Ds Cs"] by (auto simp: length_unfill_holes[OF ***] concat_map_zip_upt)
  from lts pre show ?case using MFun(1) map_cong[OF refl MFun(2)[OF *], of "[0..<length Cs]" id "\<lambda>i. ts ! i"]    
    by (auto simp del: map_eq_conv)
qed auto

lemma unfill_holes_var_subst:
  "C \<le> mctxt_of_term t \<Longrightarrow> unfill_holes (map_vars_mctxt f C) (t \<cdot> (Var \<circ> f)) = map (\<lambda>t. t \<cdot> (Var \<circ> f)) (unfill_holes C t)"
  by (induct C t rule: unfill_holes.induct; (simp only: mctxt_of_term.simps; elim less_eq_mctxtE2)?)
    (auto simp: map_concat intro!: arg_cong[of _ _ concat])


subsubsection \<open>Ditto for @{term fill_holes_mctxt}\<close>

fun unfill_holes_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt list" where
  "unfill_holes_mctxt MHole D = [D]"
| "unfill_holes_mctxt (MVar w) (MVar v) = (if v = w then [] else undefined)"
| "unfill_holes_mctxt (MFun g Cs) (MFun f Ds) = (if f = g \<and> length Ds = length Cs then
    concat (map (\<lambda>i. unfill_holes_mctxt (Cs ! i) (Ds ! i)) [0..<length Ds]) else undefined)"

lemma length_unfill_holes_mctxt [simp]:
  assumes "C \<le> D"
  shows "length (unfill_holes_mctxt C D) = num_holes C"
  using assms
proof (induct C D rule: unfill_holes_mctxt.induct)
  case (3 f Cs g Ds) with 3(1)[OF _ nth_mem] 3(2) show ?case
    by (auto simp: less_eq_mctxt_def length_concat intro!: cong[of sum_list, OF refl] nth_equalityI elim!: nth_equalityE)
qed (auto simp: less_eq_mctxt_def)

lemma fill_unfill_holes_mctxt:
  assumes "C \<le> D"
  shows "fill_holes_mctxt C (unfill_holes_mctxt C D) = D"
  using assms
proof (induct C D rule: unfill_holes_mctxt.induct)
  case (3 f Cs g Ds) with 3(1)[OF _ nth_mem] 3(2) show ?case
    by (auto simp: less_eq_mctxt_def intro!: fill_holes_arbitrary elim!: nth_equalityE)
qed (auto simp: less_eq_mctxt_def split: if_splits)

lemma unfill_fill_holes_mctxt:
  assumes "length Ds = num_holes C"
  shows "unfill_holes_mctxt C (fill_holes_mctxt C Ds) = Ds"
  using assms[symmetric]
proof (induct C Ds rule: fill_holes_induct)
  case (MFun f Cs ts) then show ?case
    by (auto intro!: arg_cong[of _ _ concat] nth_equalityI[of _ "partition_holes ts Cs"]
        simp del: concat_partition_by) auto
qed auto

lemma unfill_holes_mctxt_mctxt_of_term:
  assumes "C \<le> mctxt_of_term t"
  shows "unfill_holes_mctxt C (mctxt_of_term t) = map mctxt_of_term (unfill_holes C t)"
  using assms
proof (induct C arbitrary: t)
  case (MVar x) then show ?case by (cases t) (auto elim: less_eq_mctxtE1)
next
  case MHole then show ?case by (cases t) (auto elim: less_eq_mctxtE1)
next
  case (MFun x1a x2) then show ?case
    by (cases t) (auto elim: less_eq_mctxtE1 simp: map_concat intro!: arg_cong[of _ _ concat])
qed

subsubsection \<open>Function symbols of prefixes\<close>

lemma funas_prefix[simp]:
  "C \<le> D \<Longrightarrow> fn \<in> funas_mctxt C \<Longrightarrow> fn \<in> funas_mctxt D"
  unfolding less_eq_mctxt_def
proof (induct C D rule: inf_mctxt.induct)
  case (4 f Cs g Ds)
  from 4(3) obtain i where "i < length Cs \<and> fn \<in> funas_mctxt (Cs ! i) \<or> fn = (f, length Cs)"
    by (auto dest!: in_set_idx)
  moreover {
    assume "i < length Cs \<and> fn \<in> funas_mctxt (Cs ! i)"
    then have "i < length Ds \<and> fn \<in> funas_mctxt (Ds ! i)" using 4(2)
      by (auto intro!: 4(1)[of _ "Cs ! i" "Ds ! i"] split: if_splits elim!: nth_equalityE simp: in_set_conv_nth)
    then have ?case by (auto)
  }
  ultimately show ?case using 4(2) by auto
qed auto

end