(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2016)
Author:  Martin Avanzini <martin.avanzini@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Preliminaries\<close>
subsection \<open>Multihole Contexts\<close>

theory Multihole_Context
imports 
  Utils
begin

unbundle lattice_syntax

subsubsection \<open>Partitioning lists into chunks of given length\<close>

lemma concat_nth:
  assumes "m < length xs" and "n < length (xs ! m)"
    and "i = sum_list (map length (take m xs)) + n"
  shows "concat xs ! i = xs ! m ! n"
using assms
proof (induct xs arbitrary: m n i)
  case (Cons x xs)
  show ?case
  proof (cases m)
    case 0
    then show ?thesis using Cons by (simp add: nth_append)
  next
    case (Suc k)
    with Cons(1) [of k n "i - length x"] and Cons(2-)
      show ?thesis by (simp_all add: nth_append)
  qed
qed simp

lemma sum_list_take_eq:
  fixes xs :: "nat list"
  shows "k < i \<Longrightarrow> i < length xs \<Longrightarrow> sum_list (take i xs) =
    sum_list (take k xs) + xs ! k + sum_list (take (i - Suc k) (drop (Suc k) xs))"
  by (subst id_take_nth_drop [of k]) (auto simp: min_def drop_take)

fun partition_by where
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
  using assms by (induct ys arbitrary: xss) (simp, case_tac xss, simp, fastforce)

lemma partition_by_nth:
  "i < length ys \<Longrightarrow> partition_by xs ys ! i = take (ys ! i) (drop (sum_list (take i ys)) xs)"
  by (induct ys arbitrary: xs i) (simp, case_tac i, simp_all add: ac_simps)

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
by (induct ys arbitrary: xs i; case_tac i) auto

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
  by (induct ys arbitrary: i xs) (simp, case_tac i, simp_all add: take_map drop_map)

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

subsubsection \<open>Multihole contexts definition and functionalities\<close>
datatype ('f, vars_mctxt : 'v) mctxt = MVar 'v | MHole | MFun 'f "('f, 'v) mctxt list"

subsubsection \<open>Conversions from and to multihole contexts\<close>

primrec mctxt_of_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt" where
  "mctxt_of_term (Var x) = MVar x" |
  "mctxt_of_term (Fun f ts) = MFun f (map mctxt_of_term ts)"

primrec term_of_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term" where
  "term_of_mctxt (MVar x) = Var x" |
  "term_of_mctxt (MFun f Cs) = Fun f (map term_of_mctxt Cs)"

fun num_holes :: "('f, 'v) mctxt \<Rightarrow> nat" where
  "num_holes (MVar _) = 0" |
  "num_holes MHole = 1" |
  "num_holes (MFun _ ctxts) = sum_list (map num_holes ctxts)"

fun ground_mctxt :: "('f, 'v) mctxt \<Rightarrow> bool" where 
  "ground_mctxt (MVar _) = False" |
  "ground_mctxt MHole = True" |
  "ground_mctxt (MFun f Cs) = Ball (set Cs) ground_mctxt"

fun map_mctxt :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('g, 'v) mctxt"
where
  "map_mctxt _ (MVar x) = (MVar x)" |
  "map_mctxt _ (MHole) = MHole" |
  "map_mctxt fg (MFun f Cs) = MFun (fg f) (map (map_mctxt fg) Cs)"

abbreviation "partition_holes xs Cs \<equiv> partition_by xs (map num_holes Cs)"
abbreviation "partition_holes_idx l Cs \<equiv> partition_by_idx l (map num_holes Cs)"

fun fill_holes :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term" where
  "fill_holes (MVar x) _ = Var x" |
  "fill_holes MHole [t] = t" |
  "fill_holes (MFun f cs) ts = Fun f (map (\<lambda> i. fill_holes (cs ! i)
    (partition_holes ts cs ! i)) [0 ..< length cs])"

fun fill_holes_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt list \<Rightarrow> ('f, 'v) mctxt" where
  "fill_holes_mctxt (MVar x) _ = MVar x" |
  "fill_holes_mctxt MHole [] = MHole" |
  "fill_holes_mctxt MHole [t] = t" |
  "fill_holes_mctxt (MFun f cs) ts = (MFun f (map (\<lambda> i. fill_holes_mctxt (cs ! i) 
    (partition_holes ts cs ! i)) [0 ..< length cs]))"


fun unfill_holes :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list" where
  "unfill_holes MHole t = [t]"
| "unfill_holes (MVar w) (Var v) = (if v = w then [] else undefined)"
| "unfill_holes (MFun g Cs) (Fun f ts) = (if f = g \<and> length ts = length Cs then
    concat (map (\<lambda>i. unfill_holes (Cs ! i) (ts ! i)) [0..<length ts]) else undefined)"

fun funas_mctxt where
  "funas_mctxt (MFun f Cs) = {(f, length Cs)} \<union> \<Union>(funas_mctxt ` set Cs)" |
  "funas_mctxt _ = {}"

fun split_vars :: "('f, 'v) term \<Rightarrow> (('f, 'v) mctxt \<times> 'v list)" where
  "split_vars (Var x) = (MHole, [x])" |
  "split_vars (Fun f ts) = (MFun f (map (fst \<circ> split_vars) ts), concat (map (snd \<circ> split_vars) ts))"


fun hole_poss_list :: "('f, 'v) mctxt \<Rightarrow> pos list" where
  "hole_poss_list (MVar x) = []" |
  "hole_poss_list MHole = [[]]" |
  "hole_poss_list (MFun f cs) = concat (poss_args hole_poss_list cs)"

fun map_vars_mctxt :: "('v \<Rightarrow> 'w) \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('f, 'w) mctxt"
where
  "map_vars_mctxt vw MHole = MHole" |
  "map_vars_mctxt vw (MVar v) = (MVar (vw v))" |
  "map_vars_mctxt vw (MFun f Cs) = MFun f (map (map_vars_mctxt vw) Cs)"

inductive eq_fill :: "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt \<times> ('f, 'v) term list \<Rightarrow> bool" ("(_/ =\<^sub>f _)" [51, 51] 50)
where
  eqfI [intro]: "t = fill_holes D ss \<Longrightarrow> num_holes D = length ss \<Longrightarrow> t =\<^sub>f (D, ss)"

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
  apply (induct C D arbitrary: E rule: inf_mctxt.induct)
  apply auto
  apply (case_tac E, auto)+
  apply (fastforce simp: in_set_conv_nth intro!: nth_equalityI)
  apply (case_tac E, auto)+
done

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


subsubsection \<open>Lemmata\<close>

lemma partition_holes_fill_holes_conv:
  "fill_holes (MFun f cs) ts =
    Fun f [fill_holes (cs ! i) (partition_holes ts cs ! i). i \<leftarrow> [0 ..< length cs]]"
  by (simp add: partition_by_nth take_map)

lemma partition_holes_fill_holes_mctxt_conv:
  "fill_holes_mctxt (MFun f Cs) ts =
    MFun f [fill_holes_mctxt (Cs ! i) (partition_holes ts Cs ! i). i \<leftarrow> [0 ..< length Cs]]"
  by (simp add: partition_by_nth take_map)

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

lemma length_partition_holes_nth [simp]:
  assumes "sum_list (map num_holes cs) = length ts"
    and "i < length cs"
  shows "length (partition_holes ts cs ! i) = num_holes (cs ! i)"
  using assms by (simp add: length_partition_by_nth)

(*some compatibility lemmas (which should be dropped eventually)*)
lemmas
  map_partition_holes_nth [simp] =
    map_partition_by_nth [of _ "map num_holes Cs" for Cs, unfolded length_map] and
  length_partition_holes [simp] =
    length_partition_by [of _ "map num_holes Cs" for Cs, unfolded length_map]

lemma fill_holes_term_of_mctxt:
  "num_holes C = 0 \<Longrightarrow> fill_holes C [] = term_of_mctxt C"
  by (induct C) (auto simp add: map_eq_nth_conv)

lemma fill_holes_MHole:
  "length ts = Suc 0 \<Longrightarrow> ts ! 0 = u \<Longrightarrow> fill_holes MHole ts = u"
  by (cases ts) simp_all

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

lemma eqfE:
  assumes "t =\<^sub>f (D, ss)" shows "t = fill_holes D ss" "num_holes D = length ss"
  using assms[unfolded eq_fill.simps] by auto

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

lemma split_vars_ground_vars:
  assumes "ground_mctxt C" and "num_holes C = length xs" 
  shows "split_vars (fill_holes C (map Var xs)) = (C, xs)" using assms
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


lemma split_vars_vars_term_list: "snd (split_vars t) = vars_term_list t"
proof (induct t)
  case (Fun f ts)
  then show ?case by (auto simp: vars_term_list.simps o_def, induct ts, auto)
qed (auto simp: vars_term_list.simps)


lemma split_vars_num_holes: "num_holes (fst (split_vars t)) = length (snd (split_vars t))"
proof (induct t)
  case (Fun f ts)
  then show ?case by (induct ts, auto)
qed simp

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

lemma split_vars_ground' [simp]:
  "ground_mctxt (fst (split_vars t))"
  by (induct t) auto

lemma split_vars_funas_mctxt [simp]:
  "funas_mctxt (fst (split_vars t)) = funas_term t"
  by (induct t) auto


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


lemma less_eq_mctxt_MVarE1:
  assumes "MVar v \<le> D"
  obtains (MVar) "D = MVar v"
  using assms by (cases D) (auto elim: less_eq_mctxtE2)

lemma MHole_Bot [simp]: "MHole \<le> D"
  by (simp add: less_eq_mctxt_intros(1))

lemma less_eq_mctxt_MFunE1:
  assumes "MFun f cs \<le> D"
  obtains (MFun) ds where "D = MFun f ds" "length cs = length ds" "\<And>i. i < length cs \<Longrightarrow> cs ! i \<le> ds ! i"
  using assms by (cases D) (auto elim: less_eq_mctxtE2)


lemma length_unfill_holes [simp]:
  assumes "C \<le> mctxt_of_term t"
  shows "length (unfill_holes C t) = num_holes C"
  using assms
proof (induct C t rule: unfill_holes.induct)
  case (3 f Cs g ts) with 3(1)[OF _ nth_mem] 3(2) show ?case
    by (auto simp: less_eq_mctxt_def length_concat
      intro!: cong[of sum_list, OF refl] nth_equalityI elim!: nth_equalityE)
qed (auto simp: less_eq_mctxt_def)

lemma map_vars_mctxt_id [simp]:
  "map_vars_mctxt (\<lambda> x. x) C = C"
  by (induct C, auto intro: nth_equalityI)


lemma split_vars_eqf_subst_map_vars_term:
  "t \<cdot> \<sigma> =\<^sub>f (map_vars_mctxt vw (fst (split_vars t)), map \<sigma> (snd (split_vars t)))"
proof (induct t)
  case (Fun f ts)
  have "?case = (Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)
    =\<^sub>f (MFun f (map (map_vars_mctxt vw \<circ> (fst \<circ> split_vars)) ts), concat (map (map \<sigma> \<circ> (snd \<circ> split_vars)) ts)))"
    by (simp add: map_concat)
  also have "..." 
  proof (rule eqf_MFunI, simp, simp, unfold length_map)
    fix i
    assume i: "i < length ts"
    then have mem: "ts ! i \<in> set ts" by auto
    show "map (\<lambda>t. t \<cdot> \<sigma>) ts ! i =\<^sub>f (map (map_vars_mctxt vw \<circ> (fst \<circ> split_vars)) ts ! i, map (map \<sigma> \<circ> (snd \<circ> split_vars)) ts ! i)"
      using Fun[OF mem] i by auto
  qed
  finally show ?case by simp
qed auto

lemma split_vars_eqf_subst: "t \<cdot> \<sigma> =\<^sub>f (fst (split_vars t), (map \<sigma> (snd (split_vars t))))"
  using split_vars_eqf_subst_map_vars_term[of t \<sigma> "\<lambda> x. x"] by simp

lemma split_vars_fill_holes:
  assumes "C = fst (split_vars s)" and "ss = map Var (snd (split_vars s))"
  shows "fill_holes C ss = s" using assms
  by (metis eqfE(1) split_vars_eqf_subst subst_apply_term_empty)


lemma fill_unfill_holes:
  assumes "C \<le> mctxt_of_term t"
  shows "fill_holes C (unfill_holes C t) = t"
  using assms
proof (induct C t rule: unfill_holes.induct)
  case (3 f Cs g ts) with 3(1)[OF _ nth_mem] 3(2) show ?case
    by (auto simp: less_eq_mctxt_def intro!: fill_holes_arbitrary elim!: nth_equalityE)
qed (auto simp: less_eq_mctxt_def split: if_splits)


lemma hole_poss_list_length:
  "length (hole_poss_list D) = num_holes D"
  by (induct D) (auto simp: length_concat intro!: nth_sum_listI)

lemma unfill_holles_hole_poss_list_length:
  assumes "C \<le> mctxt_of_term t"
  shows "length (unfill_holes C t) = length (hole_poss_list C)" using assms
proof (induct C arbitrary: t)
  case (MVar x)
  then have [simp]: "t = Var x" by (cases t) (auto dest: less_eq_mctxt_MVarE1)
  show ?case by simp
next
  case (MFun f ts) then show ?case
    by (cases t) (auto simp: length_concat comp_def
      elim!: less_eq_mctxt_MFunE1 less_eq_mctxt_MVarE1 intro!: nth_sum_listI)
qed auto

lemma unfill_holes_to_subst_at_hole_poss:
  assumes "C \<le> mctxt_of_term t"
  shows "unfill_holes C t = map ((|_) t) (hole_poss_list C)" using assms
proof (induct C arbitrary: t)
  case (MVar x)
  then show ?case by (cases t) (auto elim: less_eq_mctxt_MVarE1)
next
  case (MFun f ts)
  from MFun(2) obtain ss where [simp]: "t = Fun f ss" and l: "length ts = length ss"
    by (cases t) (auto elim: less_eq_mctxt_MFunE1)
  let ?ts = "map (\<lambda>i. unfill_holes (ts ! i) (ss ! i)) [0..<length ts]"
  let ?ss = "map (\<lambda> x. map ((|_) (Fun f ss)) (case x of (x, y) \<Rightarrow> map ((#) x) (hole_poss_list y))) (zip [0..<length ts] ts)"
  have eq_l [simp]: "length (concat ?ts) = length (concat ?ss)" using MFun
    by (auto simp: length_concat comp_def elim!: less_eq_mctxt_MFunE1 split!: prod.splits intro!: nth_sum_listI)
  {fix i assume ass: "i < length (concat ?ts)"
    then have lss: "i < length (concat ?ss)" by auto
    obtain m n where [simp]: "concat_index_split (0, i) ?ts = (m, n)" by fastforce
    then have [simp]: "concat_index_split (0, i) ?ss = (m, n)" using concat_index_split_unique[OF ass, of ?ss 0] MFun(2)
      by (auto simp: unfill_holles_hole_poss_list_length[of "ts ! i" "ss ! i" for i]
       simp del: length_unfill_holes elim!: less_eq_mctxt_MFunE1)
    from concat_index_split_less_length_concat(2-)[OF ass ] concat_index_split_less_length_concat(2-)[OF lss]
    have "concat ?ts ! i = concat ?ss! i" using MFun(1)[OF nth_mem, of m "ss ! m"] MFun(2)
      by (auto elim!: less_eq_mctxt_MFunE1)} note nth = this
  show ?case using MFun
    by (auto simp: comp_def map_concat length_concat
        elim!: less_eq_mctxt_MFunE1 split!: prod.splits
        intro!: nth_equalityI nth_sum_listI nth)
qed auto

lemma hole_poss_split_varposs_list_length [simp]:
  "length (hole_poss_list (fst (split_vars t))) = length (varposs_list t)"
  by (induct t)(auto simp: length_concat comp_def intro!: nth_sum_listI)

lemma hole_poss_split_vars_varposs_list:
  "hole_poss_list (fst (split_vars t)) = varposs_list t"
proof (induct t)
  case (Fun f ts)
  let ?ts = "poss_args hole_poss_list (map (fst \<circ> split_vars) ts)"
  let ?ss = "poss_args varposs_list ts"
  have len: "length (concat ?ts) = length (concat ?ss)" "length ?ts = length ?ss"
    "\<forall> i < length ?ts. length (?ts ! i) = length (?ss ! i)" by (auto intro: eq_length_concat_nth)
  {fix i assume ass: "i < length (concat ?ts)"
    then have lss: "i < length (concat ?ss)" using len by auto
    obtain m n where int: "concat_index_split (0, i) ?ts = (m, n)" by fastforce
    then have [simp]: "concat_index_split (0, i) ?ss = (m, n)" using concat_index_split_unique[OF ass len(2-)] by auto
    from concat_index_split_less_length_concat(2-)[OF ass int] concat_index_split_less_length_concat(2-)[OF lss]
    have "concat ?ts ! i = concat ?ss! i" using Fun[OF nth_mem, of m] by auto}
  then show ?case using len by (auto intro: nth_equalityI)
qed auto



lemma funas_term_fill_holes_iff: "num_holes C = length ts \<Longrightarrow>
   g \<in> funas_term (fill_holes C ts) \<longleftrightarrow> g \<in> funas_mctxt C \<or> (\<exists>t \<in> set ts. g \<in> funas_term t)"
proof (induct C ts rule: fill_holes_induct)
  case (MFun f Cs ts)
  have "(\<exists>i < length Cs. g \<in> funas_term (fill_holes (Cs ! i) (partition_holes (concat (partition_holes ts Cs)) Cs ! i)))
    \<longleftrightarrow> (\<exists>C \<in> set Cs. g \<in> funas_mctxt C) \<or> (\<exists>us \<in> set (partition_holes ts Cs). \<exists>t \<in> set us. g \<in> funas_term t)"
    using MFun by (auto simp: ex_set_conv_ex_nth) blast
  then show ?case by auto
qed auto

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



lemma funas_mctxt_fill_holes [simp]:
  assumes "num_holes C = length ts"
  shows "funas_term (fill_holes C ts) = funas_mctxt C \<union> \<Union>(set (map funas_term ts))"
  using funas_term_fill_holes_iff[OF assms] by auto

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

end
