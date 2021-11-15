(*<*)
theory Trivia
imports Main "HOL-Library.Sublist"
begin

lemma measure_induct2[case_names IH]:
fixes meas :: "'a \<Rightarrow> 'b \<Rightarrow> nat"
assumes "\<And>x1 x2. (\<And>y1 y2. meas y1 y2 < meas x1 x2 \<Longrightarrow> S y1 y2) \<Longrightarrow> S x1 x2"
shows "S x1 x2"
proof-
  let ?m = "\<lambda> x1x2. meas (fst x1x2) (snd x1x2)" let ?S = "\<lambda> x1x2. S (fst x1x2) (snd x1x2)"
  have "?S (x1,x2)"
  apply(rule measure_induct[of ?m ?S])
  using assms by (metis fst_conv snd_conv)
  thus ?thesis by auto
qed

text\<open>Right cons:\<close>

abbreviation Rcons (infix "##" 70) where "xs ## x \<equiv> xs @ [x]"

lemma two_singl_Rcons: "[a,b] = [a] ## b" by auto

lemma length_gt_1_Cons_snoc:
  assumes "length ys > 1"
  obtains x1 xs x2 where "ys = x1 # xs ## x2"
using assms
proof (cases ys)
  case (Cons x1 xs)
    with assms obtain xs' x2 where "xs = xs' ## x2" by (cases xs rule: rev_cases) auto
    with Cons show thesis by (intro that) auto
qed auto

abbreviation lmember ("(_/ \<in>\<in> _)" [50, 51] 50) where "x \<in>\<in> xs \<equiv> x \<in> set xs"

lemma right_cons_left[simp]: "i < length as \<Longrightarrow> (as ## a)!i = as!i"
by (metis butlast_snoc nth_butlast)+

definition "update2 f x y a \<equiv> \<lambda> x' y'. if x = x' \<and> y = y' then a else f x' y'"

fun fst3 where "fst3 (a,b,c) = a"
fun snd3 where "snd3 (a,b,c) = b"
fun trd3 where "trd3 (a,b,c) = c"

lemma subliteq_induct[consumes 1, case_names Nil Cons1 Cons2, induct pred: subseq]:
assumes 0: "subseq xs ys"
and Nil: "\<And> ys. \<phi> [] ys"
and Cons1: "\<And> xs ys y. \<lbrakk>subseq xs ys; \<phi> xs ys\<rbrakk> \<Longrightarrow> \<phi> xs (y#ys)"
and Cons2: "\<And> xs ys x. \<lbrakk>subseq xs ys; \<phi> xs ys\<rbrakk> \<Longrightarrow> \<phi> (x#xs) (x#ys)"
shows "\<phi> xs ys"
using assms by (induct) auto

lemma append_ex_unique_list_ex:
assumes e: "\<exists>!i. i < length as \<and> pred (as!i)"
and as: "as = as1 @ [a] @ as2" and pred: "pred a"
shows "\<not> list_ex pred as1 \<and> \<not> list_ex pred as2"
proof
  let ?i = "length as1"
  have a: "a = as!?i" using as by auto
  have i: "?i < length as" using as by auto
  {fix j assume jl: "j < length as1" and pj: "pred (as1!j)"
   hence "pred (as!j)" apply(subst as) by (metis nth_append)
   moreover have "?i \<noteq> j" and "j < length as" using jl as by auto
   ultimately have False using e pred[unfolded a] i by blast
  }
  thus  "\<not> list_ex pred as1" unfolding list_ex_length by auto
  {fix j assume jl: "j < length as2" and pj: "pred (as2!j)"
   define k where "k \<equiv> Suc (length as1) + j"
   have "pred (as!k)" unfolding k_def apply(subst as)
   using pj nth_append[of "as1 @ [a]" as2] by simp
   moreover have "?i \<noteq> k" and "k < length as" using jl as unfolding k_def by auto
   ultimately have False using e pred[unfolded a] i by blast
  }
  thus  "\<not> list_ex pred as2" unfolding list_ex_length by auto
qed

lemma list_ex_find:
assumes "list_ex P xs"
shows "List.find P xs \<noteq> None"
using assms by (induct xs) auto

lemma list_all_map: "list_all (h o i) l \<longleftrightarrow> list_all h (map i l)"
by (induction l) auto

lemma list_ex_list_all_inj:
  assumes "list_ex (Q u) l"
      and "list_all (Q v) l"
      and "\<And> u v x. Q u x \<Longrightarrow> Q v x \<Longrightarrow> u = v"
  shows "u = v"
using assms by (induction l) auto

definition fun_upd2 where
"fun_upd2 f a b c \<equiv> \<lambda> a' b'. if a = a' \<and> b = b' then c else f a' b'"

lemma fun_upd2_eq_but_a_b:
assumes "a' \<noteq> a \<or> b' \<noteq> b"
shows "(fun_upd2 f a b c) a' b' = f a' b'"
using assms unfolding fun_upd2_def by auto

lemma fun_upd2_comm:
assumes "a' = a \<and> b' = b \<longrightarrow> c' = c"
shows "fun_upd2 (fun_upd2 f a b c) a' b' c' = fun_upd2 (fun_upd2 f a' b' c') a b c"
using assms unfolding fun_upd2_def by (intro ext) auto

lemma fun_upd2_absorb:
shows "fun_upd2 (fun_upd2 f a b c) a b c' = fun_upd2 f a b c'"
unfolding fun_upd2_def by (intro ext) auto

definition "zip3 as bs cs \<equiv> zip as (zip bs cs)"
definition "zip4 as bs cs ds \<equiv> zip as (zip bs (zip cs ds))"

lemma set_map_fst: "set as \<subseteq> set bs \<Longrightarrow> set (map fst as) \<subseteq> set (map fst bs)"
by auto

lemma set_map_snd: "set as \<subseteq> set bs \<Longrightarrow> set (map snd as) \<subseteq> set (map snd bs)"
by auto

lemma filter_cong_empty:
assumes "\<forall> x. \<not> pred1 x \<and> \<not> pred2 x"
shows "filter pred1 xl1 = filter pred2 xl2"
using assms by auto

(*****************)
abbreviation "cmap ff aal \<equiv> concat (map ff aal)"

lemma cmap_empty:
assumes "\<forall> x. x \<in>\<in> xl \<longrightarrow> ff x = []"
shows "cmap ff xl = []"
using assms by (induct xl) auto

lemma cmap_cong_empty:
assumes "\<forall> x. ff x = [] \<and> gg x = []"
shows "cmap ff xl = cmap gg yl"
using assms by (auto simp: cmap_empty)

lemma list_ex_cmap:
"list_ex P (cmap f xs) \<longleftrightarrow> (\<exists> x. x \<in>\<in> xs \<and> list_ex P (f x))"
by (induction xs) auto

lemma not_list_ex_filter:
assumes "\<not> list_ex P xs" shows "filter P xs = []"
using assms by (induct xs) auto

lemma cmap_filter_cong:
assumes "\<And> x u. x \<in>\<in> xs \<Longrightarrow> u \<in>\<in> ff x \<Longrightarrow> (q x \<longleftrightarrow> p u)"
and "\<And> x. x \<in>\<in> xs \<Longrightarrow> q x \<Longrightarrow> gg x = ff x"
shows "cmap ((filter p) o ff) xs = cmap gg (filter q xs)"
using assms by (induction xs) fastforce+

lemma cmap_cong:
  assumes "xs = ys" and "\<And>x. x \<in>\<in> xs \<Longrightarrow> ff x = gg x"
  shows "cmap ff xs = cmap gg ys"
  using assms by (induction xs arbitrary: ys) auto

lemma cmap_empty_singl_filter[simp]:
"cmap (\<lambda>x. if pred x then [x] else []) xl = filter pred xl"
  by (induct xl) auto

lemma cmap_insort_empty:
  assumes "ff x = []"
  shows "cmap ff (insort_key f x xs) = cmap ff xs"
  using assms by (induction xs) auto

lemma cmap_insort_empty_cong:
  assumes "xs = ys" and "\<And>x. x \<in>\<in> xs \<Longrightarrow> ff x = gg x" and x: "ff x = []"
  shows "cmap ff (insort_key f x xs) = cmap gg ys"
  using assms by (auto intro: cmap_cong simp: cmap_insort_empty)

abbreviation never :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where "never U \<equiv> list_all (\<lambda> a. \<not> U a)"

lemma never_list_ex: "never pred tr \<longleftrightarrow> \<not> list_ex pred tr"
by (induction tr) auto

lemma notNil_list_all_list_ex:
assumes "xs \<noteq> Nil" and "list_all pred xs"
shows "list_ex pred xs"
using assms by (induct xs) auto

fun remove1ByFirst :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
"remove1ByFirst a [] = []"
|
"remove1ByFirst a ((a1,b1) # a_bs) = (if a = a1 then a_bs else (a1,b1) # (remove1ByFirst a a_bs))"

(* "insert2 a b ab_s" searches in the list of pairs ab_s for a the first component a and replaces the second component with b;
if no match is found, (a,b) is added at the end.
It's similar to a function update applied to a list of pairs, with adding if missing.  *)
definition "insert2 a b ab_s \<equiv>
  if a \<in>\<in> map fst ab_s
    then map (\<lambda> (a',b'). if a' = a then (a',b) else (a',b')) ab_s
    else ab_s ## (a,b)"

lemma test_insert2:
"insert2 (1::nat) (2::nat) [(2,3),(1,5)] = [(2,3),(1,2)]"
"insert2 (1::nat) (2::nat) [(2,3),(4,5)] = [(2,3),(4,5),(1,2)]"
unfolding insert2_def by simp_all

lemma map_prod_cong:
"map (fst o f) xys = map (fst o f2) xys' \<Longrightarrow>
 map (snd o f) xys = map (snd o f2) xys'
 \<Longrightarrow> map f xys = map f2 xys'"
by (simp add: pair_list_eqI)

lemma map_const_eq: "length xs = length xs' \<Longrightarrow> map (\<lambda> x. a) xs = map (\<lambda> x. a) xs'"
by (simp add: map_replicate_const)

fun these :: "'a option list \<Rightarrow> 'a list" where
  "these [] = []"
| "these (None # xs) = these xs"
| "these (Some x # xs) = x # these xs"

lemma [simp]: "these (map Some xs) = xs"
by (induction xs) auto

lemma these_map_Some[simp]: "these (map (Some o f) xs) = map f xs"
by (induction xs) auto

end
(*>*)
