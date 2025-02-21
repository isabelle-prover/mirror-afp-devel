(*
 Title: Differential_Privacy_Example_Report_Noisy_Max.thy
 Author: Tetsuya Sato
*)

theory Differential_Privacy_Example_Report_Noisy_Max
  imports "Differential_Privacy_Standard"
begin

section \<open> Report Noisy Max mechanism for counting query with Laplace noise\<close>

lemma measurable_let[measurable]:
  assumes [measurable]: "g \<in> M \<rightarrow>\<^sub>M L"
    and [measurable]: "(\<lambda>(x,y). f x y) \<in> M \<Otimes>\<^sub>M L \<rightarrow>\<^sub>M N"
  shows "(\<lambda>x. (Let (g x) (f x))) \<in> M \<rightarrow>\<^sub>M N"
  unfolding Let_def by auto

subsection \<open> Formalization of argmax procedure\<close>

primrec max_argmax :: "real list \<Rightarrow> (ereal \<times> nat)" where
  "max_argmax [] = (-\<infinity>,0)"|
  "max_argmax (x#xs) = (let (m, i) = max_argmax xs in if x > m then (x,0) else (m, Suc i))"

value "max_argmax []" (*(- \<infinity>, 0)*)
value "max_argmax [1]" (*(ereal 1, 0)*)
value "max_argmax [2,1]" (*(ereal 2, 0)*)
value "max_argmax [1,2,3,4,5]" (* (ereal 5, 4) *)
value "max_argmax [1,5,2,3,4]" (* (ereal 5, 1) *)
value "([1,2,3,4,5]::int list) ! 4"

(* inductive version *)
primrec max_argmax' :: "real list \<Rightarrow> (ereal \<times> nat)" where
  "max_argmax' [] = (-\<infinity>,0)"|
  "max_argmax' (x#xs) = (if x > fst (max_argmax' xs) then (x,0) else (fst (max_argmax' xs),Suc (snd (max_argmax' xs))))"

lemma max_argmax_is_max_argmax':
  shows "max_argmax xs = max_argmax' xs"
  by(induction xs,auto simp: case_prod_beta)

lemma measurable_max_argmax[measurable]:
  shows "max_argmax \<in> (listM (borel :: real measure)) \<rightarrow>\<^sub>M (borel :: (ereal measure)) \<Otimes>\<^sub>M count_space UNIV"
proof-
  have 1: "(- \<infinity>, 0) \<in> space (borel \<Otimes>\<^sub>M count_space UNIV)"
    by (metis iso_tuple_UNIV_I measurable_Pair1' measurable_space space_borel space_count_space)
  thus"max_argmax \<in> listM borel \<rightarrow>\<^sub>M (borel :: (ereal measure)) \<Otimes>\<^sub>M count_space UNIV"
    unfolding max_argmax_def using measurable_rec_list''' 1 by measurable
qed

definition argmax_list :: "real list \<Rightarrow> nat" where
  "argmax_list = snd o max_argmax "

lemma measurable_argmax_list[measurable]:
  shows "argmax_list \<in> (listM (borel :: real measure)) \<rightarrow>\<^sub>M count_space UNIV"
  by(unfold argmax_list_def, rule measurable_comp[where N = "(borel :: (ereal measure)) \<Otimes>\<^sub>M count_space UNIV"],auto)

lemma argmax_list_le_length:
  shows "length xs = Suc k \<Longrightarrow> (argmax_list xs) \<le> k"
proof(induction k arbitrary:xs)
  case 0
  then obtain x where xs: "xs = [x]"
    by (metis length_0_conv length_Suc_conv)
  then show ?case unfolding xs argmax_list_def comp_def max_argmax.simps by auto
next
  case (Suc k)
  then obtain y ys where xs: "xs = y # ys" and len:"length ys = Suc k"
    by (meson length_Suc_conv)
  from Suc.IH[of ys, OF len] obtain k' z where 1: "max_argmax ys = (z,k')" and 2: "k' \<le> k"
    unfolding argmax_list_def comp_def by (metis prod.collapse)
  then show ?case unfolding xs argmax_list_def comp_def max_argmax.simps 1 using 2 by auto
qed

lemma fst_max_argmax_append:
  shows "(fst (max_argmax (xs @ ys))) = max (fst (max_argmax xs)) (fst (max_argmax ys))"
  unfolding max_argmax_is_max_argmax' by(induction xs arbitrary: ys,auto)

lemma fst_max_argmax_is_max:
  shows "fst (max_argmax xs) = Max (set xs \<union> {-\<infinity>})"
  unfolding max_argmax_is_max_argmax'
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have 1: " Max (set (map ereal (a # xs)) \<union> {- \<infinity>}) = max a (Max (set (map ereal xs) \<union> {- \<infinity>}))"
    by (simp add: Un_ac(3))
  have "fst (max_argmax' (a # xs)) = ( if Max (set (map ereal xs) \<union> {- \<infinity>}) < ereal a then (ereal a) else (Max (set (map ereal xs) \<union> {- \<infinity>})))"
    unfolding max_argmax'.simps Cons.IH by auto
  also have "... = max a (Max (set (map ereal xs) \<union> {- \<infinity>}))"
    unfolding max_def
    by (meson Metric_Arith.nnf_simps(8))
  finally show ?case using 1 by auto
qed

lemma argmax_list_max_argmax:
  assumes "xs \<noteq> []"
  shows "(argmax_list xs) = m \<longleftrightarrow> max_argmax xs = (ereal (xs ! m), m)"
  using assms proof(induction xs arbitrary: m)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof(cases "xs = []")
    case True
    hence 1: "a # xs = [a]"
      by auto
    then show ?thesis unfolding 1 argmax_list_def comp_def max_argmax.simps by auto
  next
    case False
    then show ?thesis
      unfolding argmax_list_def comp_def max_argmax_is_max_argmax' max_argmax'.simps using less_ereal.simps(5) max_argmax'.simps(1) nth_Cons_0 nth_Cons_Suc split_pairs local.Cons(1) max_argmax_is_max_argmax' by fastforce
  qed
qed

lemma argmax_list_gives_max:
  assumes "xs \<noteq> []"
  shows "(argmax_list xs) = m \<Longrightarrow> \<forall>i \<in> {0..<length xs}. xs ! i \<le> xs ! m"
proof
  fix i assume 1: "(argmax_list xs) = m" and i: "i \<in> {0..<length xs}"
  hence "max_argmax xs = (ereal (xs ! m), m)"
    using argmax_list_max_argmax[OF assms] by blast
  with fst_max_argmax_is_max 1 have 0: " xs ! m = Max (set xs \<union> {-\<infinity>})"
    by (metis fst_eqD)
  have "xs ! i \<le> Max (set xs \<union> {-\<infinity>})"
    using i by auto
  thus "xs ! i \<le> xs ! m"
    using 0 by (metis ereal_less_eq(3))
qed

lemma argmax_list_gives_max2:
  assumes "xs \<noteq> []"
  shows "(x \<le> (xs ! m) \<and> argmax_list xs = m) = (max_argmax (x#xs) = ((xs ! m), (Suc m)))"
proof(induction m)
  case 0
  then show ?case
    unfolding argmax_list_max_argmax[of xs 0, OF assms] max_argmax_is_max_argmax' max_argmax'.simps
    by (metis (mono_tags, lifting) Suc_n_not_n diff_Suc_1' ereal_less_eq(3) not_le split_conv split_pairs)
next
  case (Suc m)
  then show ?case
    unfolding argmax_list_max_argmax[of xs m, OF assms] max_argmax_is_max_argmax' max_argmax'.simps
    by(split if_split) (metis Suc_inject Zero_neq_Suc argmax_list_max_argmax assms basic_trans_rules(20) ereal_less_eq(3) fst_conv le_cases less_eq_ereal_def max_argmax_is_max_argmax' old.prod.case snd_conv) (*takes long time*)
qed

lemma fst_max_argmax_adj:
  fixes xs ys rs :: "real list" and n :: nat
  assumes "length xs = n"
    and "length ys = n"
    and "length rs = n"
    and adj: "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys"
  shows "(fst (max_argmax (map2 (+) xs rs))) \<ge> (fst (max_argmax (map2 (+) ys rs))) \<and> (fst (max_argmax (map2 (+) xs rs))) \<le> (fst (max_argmax (map2 (+) ys rs))) + 1"
  using assms
proof(induction n arbitrary: xs ys rs)
  case 0
  hence q : "xs = []" "ys = []" "rs = []"
    by auto
  thus ?case unfolding q by auto
next
  case (Suc n)
  then obtain x2 y2 r2 ys2 xs2 rs2 where q: "xs = x2 # xs2" "ys = y2 # ys2" "rs = r2 # rs2"
    using length_Suc_conv by metis
  hence q2: "length xs2 = n" "length ys2 = n" "length rs2 = n"
    using Suc.prems(1,2,3) by auto
  from Suc.prems(4) have q3: "list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) xs2 ys2" and q4: "y2 \<le> x2 \<and> x2 \<le> y2 + 1"
    unfolding q by auto
  hence q5: "fst (max_argmax (map2 (+) ys2 rs2)) \<le> fst (max_argmax (map2 (+) xs2 rs2)) \<and>
 fst (max_argmax (map2 (+) xs2 rs2)) \<le> fst (max_argmax (map2 (+) ys2 rs2)) + 1"
    using Suc(1) q2 by auto
  from q4 have q6: "ereal (y2 + r2) \<le> ereal (x2 + r2) \<and> ereal (x2 + r2) \<le> ereal (y2 + r2) + 1"
    by auto
  have indx: "fst (max_argmax (map2 (+) xs rs)) = max (x2 + r2) (fst (max_argmax (map2 (+) xs2 rs2)))"
    unfolding q max_argmax_is_max_argmax' by auto
  have indy: "fst (max_argmax (map2 (+) ys rs)) = max (y2 + r2) (fst (max_argmax (map2 (+) ys2 rs2)))"
    unfolding q max_argmax_is_max_argmax' by auto
  show ?case
    unfolding indx indy proof(intro conjI)
    show "max (ereal (y2 + r2)) (fst (max_argmax (map2 (+) ys2 rs2))) \<le> max (ereal (x2 + r2)) (fst (max_argmax (map2 (+) xs2 rs2))) "
      using q5 q6 using ereal_less_eq(3) max.mono by blast
    have "max (ereal (x2 + r2)) (fst (max_argmax (map2 (+) xs2 rs2))) \<le> max (ereal (y2 + r2) + 1) (fst (max_argmax (map2 (+) ys2 rs2)) + 1)"
      using q5 q6 using ereal_less_eq(3) max.mono by auto
    also have "... \<le> (max (ereal (y2 + r2)) (fst (max_argmax (map2 (+) ys2 rs2)))) + 1"
      by (meson add_right_mono max.bounded_iff max.cobounded1 max.cobounded2)
    finally show "max (ereal (x2 + r2)) (fst (max_argmax (map2 (+) xs2 rs2))) \<le> max (ereal (y2 + r2)) (fst (max_argmax (map2 (+) ys2 rs2))) + 1".
  qed
qed

subsection \<open> An auxiliary function to calculate the argmax of a list where an element has been inserted. \<close>

definition argmax_insert :: "real \<Rightarrow> real list \<Rightarrow> nat \<Rightarrow> nat" where
  "argmax_insert k ks i = argmax_list (list_insert k ks i)"

lemma argmax_insert_i_i_0:
  shows "(argmax_insert k xs 0 = 0) \<longleftrightarrow> (k > (fst (max_argmax xs)))"
  unfolding argmax_insert_def argmax_list_def by (auto simp: max_argmax_is_max_argmax' list_insert_def)

lemma argmax_insert_i_i_expand:
  assumes "xs \<noteq> []"
    and "m \<le> n"
    and "length xs = n"
  shows "(argmax_insert k xs m = m) \<longleftrightarrow> (max_argmax ((take m xs) @ [k] @ (drop m xs))) = (k,m)"
  unfolding argmax_insert_def by(subst argmax_list_max_argmax) (auto simp:assms nth_append list_insert_def)

lemma argmax_insert_i_i_iterate:
  assumes "m \<le> n"
    and "length xs = n"
  shows "(argmax_insert k (x # xs) (Suc m) = (Suc m)) \<longleftrightarrow> ((x \<le> k) \<and> (argmax_insert k xs m = m))"
  unfolding argmax_insert_def list_insert_def
proof(subst argmax_list_max_argmax)
  show 0: "take (Suc m) (x # xs) @ [k] @ drop (Suc m) (x # xs) \<noteq> []"
    by auto
  have "m \<le> length xs"
    using assms by auto
  hence 1: "(take m xs @ [k] @ drop m xs) ! m = k"
    by(subst nth_append, auto)
  have 2: "take m xs @ [k] @ drop m xs \<noteq> []"
    by auto
  show "(max_argmax (take (Suc m) (x # xs) @ [k] @ drop (Suc m) (x # xs)) = (ereal ((take (Suc m) (x # xs) @ [k] @ drop (Suc m) (x # xs)) ! Suc m), Suc m)) =
 (x \<le> k \<and> argmax_list (take m xs @ [k] @ drop m xs) = m)"
    using argmax_list_gives_max2[of "take m xs @ [k] @ drop m xs" x " m", OF 2] unfolding 1 case_prod_beta
    by (metis "1" Cons_eq_appendI drop_Suc_Cons nth_Cons_Suc prod.sel(1) prod.sel(2) take_Suc_Cons)
qed

lemma argmax_insert_i_i:
  assumes "m \<le> n"
    and "length xs = n"
  shows "(argmax_insert k xs m = m) \<longleftrightarrow> (ereal k > (fst (max_argmax (drop m xs))) \<and> (ereal k \<ge> (fst (max_argmax (take m xs)))))"
  using assms unfolding max_argmax_is_max_argmax'
proof(induction xs arbitrary: n k m)
  case Nil
  thus ?case
    by (metis drop_Nil drop_eq_Nil2 argmax_insert_i_i_0 less_eq_ereal_def list.size(3) order_antisym_conv take_Nil max_argmax_is_max_argmax')
next
  case (Cons a zs)
  thus ?case
  proof(induction m arbitrary: n zs)
    case 0
    hence p: "\<And> xs. (take 0 xs) = []"
      by auto
    show ?case
      unfolding p max_argmax'.simps(1) by (metis drop0 ereal_less_eq(2) fst_conv argmax_insert_i_i_0 max_argmax_is_max_argmax')
  next
    case (Suc m)
    have a1: "(argmax_insert k (a # zs) (Suc m) = Suc m) \<longleftrightarrow> ((a \<le> k) \<and> (argmax_insert k zs m = m))"
      using argmax_insert_i_i_iterate Suc.prems(2) Suc.prems(3) by auto
    have a2: "(argmax_insert k zs m = m) \<longleftrightarrow> (fst (max_argmax' (drop m zs)) < ereal k \<and> fst (max_argmax' (take m zs)) \<le> ereal k)"
      using Suc.prems(1) Suc.prems(2) Suc.prems(3) by auto
    consider"fst (max_argmax' (take m zs)) < ereal a"|"fst (max_argmax' (take m zs)) > ereal a"| "fst (max_argmax' (take m zs)) = ereal a"
      using linorder_less_linear by auto
    hence a4: "((a \<le> k) \<and> fst (max_argmax' (take m zs)) \<le> ereal k) \<longleftrightarrow> fst (max_argmax' (take (Suc m) (a # zs))) \<le> ereal k"
    proof(cases)
      case 1
      thus ?thesis
        unfolding max_argmax'.simps(2) using less_eq_ereal_def order_less_le_trans by fastforce
    next
      case 2
      hence "(a \<le> k \<and> fst (max_argmax' (take m zs)) \<le> ereal k) \<longleftrightarrow> (a < k \<and> fst (max_argmax' (take m zs)) \<le> ereal k)"
        using leD nless_le by auto
      thus ?thesis
        unfolding max_argmax'.simps(2) using "2" le_ereal_less by auto
    next
      case 3
      thus ?thesis
        unfolding max_argmax'.simps(2) by auto
    qed
    from a1 a2 a4 show "(argmax_insert k (a # zs) (Suc m) = Suc m) \<longleftrightarrow> ((fst (max_argmax' (drop (Suc m) (a # zs))) < ereal k \<and> fst (max_argmax' (take (Suc m) (a # zs))) \<le> ereal k))"
      by auto
  qed
qed

lemma argmax_insert_i_i':
  assumes "m \<le> n"
    and "length xs = n"
  shows "(argmax_insert k xs m = m) \<longleftrightarrow> (ereal k \<ge> (fst (max_argmax xs)) \<and> (ereal k \<noteq> (fst (max_argmax (drop m xs)))))"
proof-
  have "(argmax_insert k xs m = m) \<longleftrightarrow> (ereal k > (fst (max_argmax (drop m xs))) \<and> (ereal k \<ge> (fst (max_argmax (take m xs)))))"
    by (rule argmax_insert_i_i[OF assms])
  also have "... \<longleftrightarrow> (ereal k \<ge> (fst (max_argmax xs)) \<and> (ereal k \<noteq> (fst (max_argmax (drop m xs)))))"
  proof-
    have "fst (max_argmax xs) = fst (max_argmax ((take m xs) @ (drop m xs)))"
      by auto
    also have "... = max (fst (max_argmax (take m xs))) (fst (max_argmax (drop m xs)))"
      using fst_max_argmax_append[symmetric] by auto
    finally show ?thesis by auto
  qed
  finally show ?thesis.
qed

lemma argmax_insert_i_i'_region:
  assumes "length xs = n" and "length ys = n" and "i \<le> n"
  shows "{r | r :: real. argmax_insert (r + d) ((map2 (+) xs ys)) i = i} = {r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) xs ys))) \<and> (ereal (r + d) \<noteq> (fst (max_argmax (drop i (map2 (+) xs ys))))))}"
  using assms argmax_insert_i_i' by auto

section \<open>Formal proof of DP of RNM\<close>

subsection \<open> A formal proof of the main part of differential privacy of report noisy max [Claim 3.9, AFDP] \<close>

locale Lap_Mechanism_RNM_mainpart =
  fixes M::"'a measure"
    and adj::"'a rel"
    and c::"'a \<Rightarrow> real list"
  assumes c: "c \<in> M \<rightarrow>\<^sub>M (listM borel)"
    and cond: "\<forall> (x,y) \<in> adj. list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) (c x) (c y) \<or> list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) (c y) (c x)"
    and adj: "adj \<subseteq> (space M) \<times> (space M)"
begin

text \<open> We define an abstracted version of report noisy max mechanism. We later instantiate @{term c} with the counting query. \<close>

definition LapMech_RNM :: "real \<Rightarrow> 'a \<Rightarrow> nat measure" where
  "LapMech_RNM \<epsilon> x = do {y \<leftarrow> Lap_dist_list (1 / \<epsilon>) (c x); return (count_space UNIV) (argmax_list y)}"

lemma measurable_LapMech_RNM[measurable]:
  shows "LapMech_RNM \<epsilon> \<in> M \<rightarrow>\<^sub>M prob_algebra(count_space UNIV)"
  unfolding LapMech_RNM_def argmax_list_def using c by auto

paragraph \<open> Calculating the density of the probability distributions sampled from the main part of @{term LapMech_RNM}\<close>

context
  fixes \<epsilon>::real
  assumes pose:"0 < \<epsilon>"
begin

paragraph \<open> The main part of @{term LapMech_RNM} \<close>

definition RNM' :: "real list \<Rightarrow> nat measure" where
  "RNM' zs = do {y \<leftarrow> Lap_dist_list (1 / \<epsilon>) (zs); return (count_space UNIV) (argmax_list y)}"

lemma RNM'_def2:
  shows "RNM' zs = do {rs \<leftarrow> Lap_dist0_list (1 / \<epsilon>) (length zs); y \<leftarrow> return (listM borel) (map2 (+) zs rs); return (count_space UNIV) (argmax_list y)}"
  by (unfold RNM'_def  Lap_dist_list_def2,subst bind_assoc[where N = "listM borel" and R = "count_space UNIV"],auto)

lemma measurable_RNM'[measurable]:
  shows "RNM' \<in> listM borel \<rightarrow>\<^sub>M prob_algebra(count_space UNIV)"
  unfolding RNM'_def argmax_list_def by auto

lemma LapMech_RNM_RNM'_c:
  shows "LapMech_RNM \<epsilon> = RNM' o c"
  unfolding RNM'_def LapMech_RNM_def by auto

lemma RNM'_Nil:
  shows "RNM' [] = return (count_space (UNIV :: nat set)) 0"
  by(unfold RNM'_def Lap_dist_list.simps(1), subst bind_return[where N = "(count_space UNIV)"],auto simp: argmax_list_def)

lemma RNM'_singleton:
  shows "RNM' [x] = return (count_space (UNIV :: nat set)) 0"
proof-
  have "RNM' [x] = (Lap_dist (1/\<epsilon>) x) \<bind> (\<lambda>x1. return (listM borel) [] \<bind> (\<lambda>x2. return (listM borel) (x1 # x2))) \<bind> (\<lambda>y. return (count_space UNIV) (argmax_list y))"
    unfolding RNM'_def by auto
  also have "... = (Lap_dist (1/\<epsilon>) x) \<bind> (\<lambda>x1. return (listM borel) (x1 # [])) \<bind> (\<lambda>y. return (count_space UNIV) (argmax_list y))"
    by(subst bind_return, measurable)
  also have "... = (Lap_dist (1/\<epsilon>) x) \<bind> (\<lambda>x1. return (count_space UNIV) (argmax_list [x1]))"
  proof(subst bind_assoc)
    show "Lap_dist (1 / \<epsilon>) x \<bind> (\<lambda>x. return (listM borel) [x] \<bind> (\<lambda>y. return (count_space UNIV) (argmax_list y))) = Lap_dist (1 / \<epsilon>) x \<bind> (\<lambda>x1. return (count_space UNIV) (argmax_list [x1]))"
      by(subst bind_return, measurable)
  qed measurable
  also have "... = return (count_space (UNIV :: nat set)) 0"
    by(auto simp: bind_const' subprob_space_return argmax_list_def)
  finally show ?thesis.
qed

lemma RNM'_support:
  assumes "i \<ge> length xs"
    and "xs \<noteq> []"
  shows "emeasure (RNM' xs){i} = 0"
  unfolding RNM'_def
proof-
  define n :: nat where n: "n = length xs"
  have 1: "emeasure (Lap_dist_list (1/\<epsilon>) xs) {zs. length zs = n} = 1"
    using emeasure_Lap_dist_list_length[of _ xs] n by auto
  show "emeasure (Lap_dist_list (1 / \<epsilon>) xs \<bind> (\<lambda>y. return (count_space UNIV) (argmax_list y))) {i} = 0"
  proof(subst Giry_Monad.emeasure_bind)
    show " space (Lap_dist_list (1 / \<epsilon>) xs) \<noteq> {}"
      by(auto simp: space_Lap_dist_list)
    show "{i} \<in> sets (count_space UNIV)"
      by auto
    show " (\<lambda>y. return (count_space UNIV) (argmax_list y)) \<in> Lap_dist_list (1 / \<epsilon>) xs \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)"
      by auto
    show "(\<integral>\<^sup>+ x. emeasure (return (count_space UNIV) (argmax_list x)) {i} \<partial>Lap_dist_list (1 / \<epsilon>) xs) = 0"
    proof(subst Giry_Monad.emeasure_return)
      show "(\<integral>\<^sup>+ x. indicator {i} (argmax_list x) \<partial>Lap_dist_list (1 / \<epsilon>) xs) = 0"
      proof(rule Distributions.nn_integral_zero',rule AE_mp)
        show "almost_everywhere (Lap_dist_list (1 / \<epsilon>) xs) (\<lambda>zs. zs \<in>{zs. length zs = n})"
          by(rule prob_space.AE_prob_1,auto simp: measure_def 1)
        show " AE x\<in>{zs. length zs = n} in Lap_dist_list (1 / \<epsilon>) xs. indicator {i} (argmax_list x) = 0"
        proof(rule AE_I2,rule impI)
          fix x :: "real list" assume "x \<in> {zs. length zs = n}"
          with n assms show "indicator {i} (argmax_list x) = 0"
            by (metis (mono_tags, lifting) One_nat_def Suc_diff_le argmax_list_le_length diff_Suc_1' diff_is_0_eq indicator_simps(2) length_0_conv mem_Collect_eq not_less_eq_eq singletonD)
        qed
      qed
    qed fact
  qed
qed

paragraph \<open> The conditional distribution of @{term RNM'} when @{term "n - 1"} values of noise are fixed. \<close>

definition RNM_M :: "real list \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat measure" where
  "RNM_M cs rs d i = do{r \<leftarrow> (Lap_dist0 (1/\<epsilon>)); return (count_space UNIV) (argmax_insert (r+d) ((\<lambda> (xs,ys). (map2 (+) xs ys))(cs, rs)) i)}"

lemma space_RNM_M:
  shows "space (RNM_M cs rs d i) = (UNIV :: nat set)"
  unfolding RNM_M_def Lap_dist0_def by (metis empty_not_UNIV sets_return space_count_space space_bind space_Lap_dist )

lemma sets_RNM_M[measurable_cong]:
  shows "sets (RNM_M cs rs d i) = sets (count_space (UNIV :: nat set))"
  unfolding RNM_M_def Lap_dist0_def by(metis sets_bind sets_return space_Lap_dist empty_not_UNIV)

lemma RNM_M_Nil:
  shows "emeasure (RNM_M [] [] d 0) {j \<in> UNIV. j = 0} = 1"
    and "k \<noteq> 0 \<Longrightarrow> emeasure (RNM_M [] [] d 0) {j \<in> UNIV. j = k} = 0"
proof-
  have b: "Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>r. return (count_space UNIV) (0 :: nat)) = return (count_space UNIV) (0 :: nat)"
  proof(rule measure_eqI)
    show "sets (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>r. return (count_space UNIV) 0)) = sets (return (count_space UNIV) 0)"
      unfolding Lap_dist0_def by (metis countable_empty sets_bind space_Lap_dist uncountable_UNIV_real)
    show "\<And>A. A \<in> sets (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>r. return (count_space UNIV) 0)) \<Longrightarrow>
 emeasure (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>r. return (count_space UNIV) 0)) A = emeasure (return (count_space UNIV) 0) A"
      unfolding Lap_dist0_def by(subst emeasure_bind_const_prob_space,auto simp: subprob_space_return_ne)
  qed
  {
    fix k :: nat
    have "measure (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>r. return (count_space UNIV) 0)) {j :: nat. j = k \<and> j \<in> space (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>r. return (count_space UNIV) 0))}
 = measure (return (count_space UNIV) 0) {j :: nat. j = k \<and> j \<in> space (return (count_space UNIV) 0)}"
      unfolding b by standard
    also have "... = measure (return (count_space UNIV) 0){k :: nat}"
      by auto
  }note * = this
  show "emeasure (RNM_M [] [] d 0) {j \<in> UNIV. j = 0} = 1"
    by(auto simp: RNM_M_def argmax_insert_def argmax_list_def b  list_insert_def)
  show "k \<noteq> 0 \<Longrightarrow> emeasure (RNM_M [] [] d 0) {j \<in> UNIV. j = k} = 0"
    by(auto simp: RNM_M_def argmax_insert_def argmax_list_def b  list_insert_def)
qed

lemma RNM_M_Nil_indicator:
  shows "emeasure (RNM_M [] [] d 0) = indicator {A :: nat set. A \<in> UNIV \<and> 0 \<in> A}"
proof
  fix B :: "nat set"
  have 1: "\<And> k :: nat. (if (k \<in> B \<and> k \<noteq> 0) then {k} else {}) \<in> null_sets (RNM_M [] [] d 0)"
  proof(split if_split, intro conjI impI)
    show "\<And>k. k \<in> B \<and> k \<noteq> 0 \<Longrightarrow> {k} \<in> null_sets (RNM_M [] [] d 0)"
      using RNM_M_Nil(2)[of _ d] by auto
    show "\<And>k. \<not> (k \<in> B \<and> k \<noteq> 0) \<Longrightarrow> {} \<in> null_sets (RNM_M [] [] d 0)"
      by auto
  qed
  have 2: "\<Union> (range (\<lambda> k. if (k \<in> B \<and> k \<noteq> 0) then {k} else {})) = {k :: nat. k \<in> B \<and> k \<noteq> 0}"
    by auto
  have "{k :: nat. k \<in> B \<and> k \<noteq> 0} \<in> null_sets (RNM_M [] [] d 0)"
    using null_sets_UN'[of"UNIV :: nat set" "(\<lambda> k. if (k \<in> B \<and> k \<noteq> 0) then {k} else {})" "(RNM_M [] [] d 0)",OF _ 1 ]
    unfolding 2[THEN sym] by auto
  hence b: "emeasure (RNM_M [] [] d 0) {k \<in> B. k \<noteq> 0} = 0"
    by blast
  have a: "emeasure (RNM_M [] [] d 0) {0} = 1"
    using RNM_M_Nil(1)[of d] by auto
  show "emeasure (RNM_M [] [] d 0) B = indicator {A \<in> UNIV. 0 \<in> A} B"
  proof(cases"0 \<in> B")
    case True
    hence B: "B = {0} \<union> {k. k \<in> B \<and> k \<noteq> 0}"by auto
    hence "emeasure (RNM_M [] [] d 0) B = emeasure (RNM_M [] [] d 0) ({0} \<union> {k. k \<in> B \<and> k \<noteq> 0})"
      by auto
    also have "... = emeasure (RNM_M [] [] d 0) {0} + emeasure (RNM_M [] [] d 0) {k. k \<in> B \<and> k \<noteq> 0}"
      by(rule plus_emeasure[THEN sym],auto simp: sets_RNM_M)
    also have "... = 1"
      using a b by auto
    finally show ?thesis using True by auto
  next
    case False
    hence B: "B = {k. k \<in> B \<and> k \<noteq> 0}"
      using Collect_mem_eq by fastforce
    hence "emeasure (RNM_M [] [] d 0) B = emeasure (RNM_M [] [] d 0) ({k. k \<in> B \<and> k \<noteq> 0})"
      by auto
    also have "... = 0"
      using b by auto
    finally show ?thesis using False by auto
  qed
qed

lemma RNM_M_Nil_is_return_0:
  shows "(RNM_M [] [] d 0) = return (count_space UNIV) 0"
proof(rule measure_eqI)
  show "sets (RNM_M [] [] d 0) = sets (return (count_space UNIV) 0)"
    by (auto simp: sets_RNM_M)
  show "\<And>A. A \<in> sets (RNM_M [] [] d 0) \<Longrightarrow> emeasure (RNM_M [] [] d 0) A = emeasure (return (count_space UNIV) 0) A"
    unfolding RNM_M_Nil_indicator sets_RNM_M emeasure_return
    by(split split_indicator,auto)
qed

lemma RNM_M_probability:
  fixes cs rs :: "real list"
  assumes "length cs = n" and "length rs = n"
    and "i \<le> n"
    and pose: "\<epsilon> > 0"
  shows "\<P>(j in (RNM_M cs rs d i). j = i) = \<P>(r in (Lap_dist0 (1/\<epsilon>)). ereal(r + d) \<ge> (fst (max_argmax (map2 (+) cs rs))))"
  using assms
proof-
  have "\<P>(j in (RNM_M cs rs d i). j = i) = measure (RNM_M cs rs d i) {j :: nat | j. j\<in> UNIV \<and> j = i}"
    using space_RNM_M by auto
  also have "... = measure (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>r. return (count_space (UNIV :: nat set)) (argmax_insert (r + d) (map (\<lambda>(x, y). x + y) (zip cs rs)) i))) {j :: nat | j. j\<in> UNIV \<and> j = i}"
    unfolding RNM_M_def by auto
  also have "... = LINT r|(Lap_dist0 (1/\<epsilon>)). measure (return (count_space (UNIV :: nat set)) (argmax_insert (r + d) (map (\<lambda>(x, y). x + y) (zip cs rs)) i)) {j :: nat | j. j\<in> UNIV \<and> j = i}"
  proof(intro subprob_space.measure_bind subprob_space_Lap_dist0)
    show "{j |j. j \<in> \<top> \<and> j = i} \<in> sets (count_space (UNIV :: nat set))"
      by auto
    have 1: "take i (map (\<lambda>(x, y). x + y) (zip cs rs)) \<in> space (listM borel)"
      unfolding space_listM by auto
    have 2: "drop i (map (\<lambda>(x, y). x + y) (zip cs rs)) \<in> space (listM borel)"
      unfolding space_listM by auto
    hence 3: "(\<lambda>x. drop i (map (\<lambda>(x, y). x + y) (zip cs rs))) \<in> Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M listM borel"
      by measurable
    have "(\<lambda>x. [x + d] @ drop i (map (\<lambda>(x, y). x + y) (zip cs rs))) \<in> Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M listM borel"
      using listM_Nil 2 by measurable
    show "(\<lambda>r. return (count_space \<top>) (argmax_insert (r + d) (map (\<lambda>(x, y). x + y) (zip cs rs)) i)) \<in> Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M subprob_algebra (count_space \<top>)"
      unfolding argmax_insert_def using space_listM sets_Lap_dist measurable_cong_sets 1 listM_Nil 2 by measurable
  qed
  also have "... = LINT r|(Lap_dist0 (1/\<epsilon>)). (\<lambda> r. indicator {j :: nat | j. j\<in> UNIV \<and> j = i} (argmax_insert (r + d) (map (\<lambda>(x, y). x + y) (zip cs rs)) i)) r"
    by(subst measure_return,auto)
  also have "... = LINT r|(Lap_dist0 (1/\<epsilon>)). indicator {r | r :: real. argmax_insert (r + d) ((map2 (+) cs rs)) i = i} r"
  proof(rule Bochner_Integration.integral_cong)
    show "Lap_dist0 (1/\<epsilon>) = Lap_dist0 (1/\<epsilon>)"
      by auto
    fix x :: real assume "x \<in> space (Lap_dist0 (1/\<epsilon>))"
    hence x: "x \<in> UNIV"
      by(auto simp: space_Lap_dist)
    thus "indicator {j |j. j \<in> \<top> \<and> j = i} (argmax_insert (x + d) (map (\<lambda>(x, y). x + y) (zip cs rs)) i) = indicator {r |r. argmax_insert (r + d) (map (\<lambda>(x, y). x + y) (zip cs rs)) i = i} x"
      by(split split_indicator,auto)
  qed
  also have "... = measure (Lap_dist0 (1/\<epsilon>)) ({r | r :: real. argmax_insert (r + d) ((map2 (+) cs rs)) i = i} \<inter> space (Lap_dist0 (1/\<epsilon>)))"
    by auto
  also have "... = measure (Lap_dist0 (1/\<epsilon>)) ({r | r :: real. argmax_insert (r + d) ((map2 (+) cs rs)) i = i})"
    unfolding space_Lap_dist0 by auto
  also have "... = measure (Lap_dist0 (1/\<epsilon>)) {r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs)))) \<and> ((ereal (r + d) \<noteq> (fst (max_argmax (drop i (map2 (+) cs rs))))))}"
    by(subst argmax_insert_i_i' assms ,auto simp: assms)
  also have "... = measure (Lap_dist0 (1/\<epsilon>)) ({r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs))))}
 - {r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs)))) \<and> (ereal (r + d) = (fst (max_argmax (drop i (map2 (+) cs rs)))))})"
  proof-
    have "{r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs)))) \<and> ((ereal (r + d) \<noteq> (fst (max_argmax (drop i (map2 (+) cs rs))))))}
 = ({r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs))))}
 - {r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs)))) \<and> (ereal (r + d) = (fst (max_argmax (drop i (map2 (+) cs rs)))))})"
      by auto
    thus ?thesis
      by auto
  qed
  also have "... = measure (Lap_dist0 (1/\<epsilon>)) {r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs))))}
 - measure (Lap_dist0 (1/\<epsilon>)) {r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs)))) \<and> (ereal (r + d) = (fst (max_argmax (drop i (map2 (+) cs rs)))))}"
    using subprob_space_Lap_dist by(intro finite_measure.finite_measure_Diff,auto simp: subprob_space.axioms(1))
  also have "... = measure (Lap_dist0 (1/\<epsilon>)) {r | (r :: real). (ereal (r + d) \<ge> (fst (max_argmax (map2 (+) cs rs))))}"
    (is"measure (Lap_dist0 (1/\<epsilon>)) ?A - measure (Lap_dist0 (1/\<epsilon>)) ?B = measure (Lap_dist0 (1/\<epsilon>)) ?A")
  proof-
    have "measure (Lap_dist0 (1/\<epsilon>)) ?B = 0"
    proof-
      from pose have "(Lap_dist0 (1/\<epsilon>)) = (density lborel (\<lambda>x. ennreal (laplace_density (1 div \<epsilon>) 0 x)))"
        unfolding Lap_dist_def Lap_dist0_def by auto
      hence 2: "absolutely_continuous lborel (Lap_dist0 (1/\<epsilon>))"
        by(auto intro: absolutely_continuousI_density)
      have 3: "?B = (UNIV :: real set) \<inter> (\<lambda>r. ereal (r + d)) -` {r . r \<ge> (fst (max_argmax (map2 (+) cs rs))) \<and> r = (fst (max_argmax (drop i (map2 (+) cs rs))))}"
        (is"?B = ?C")
        by auto
      have "?C \<in> null_sets lborel"
      proof(intro countable_imp_null_set_lborel countable_image_inj_Int_vimage)
        show "inj_on (\<lambda>r :: real. ereal (r + d)) \<top>"
          unfolding inj_on_def by (metis add.commute add_left_cancel ereal.inject)
        show "countable {r. fst (max_argmax (map (\<lambda>(x, y). x + y) (zip cs rs))) \<le> r \<and> r = fst (max_argmax (drop i (map (\<lambda>(x, y). x + y) (zip cs rs))))}"
          by(rule countable_subset,auto)
      qed
      hence 4: "?B \<in> null_sets (Lap_dist0 (1/\<epsilon>)) "
        using 3 2 unfolding absolutely_continuous_def by auto
      thus "measure (Lap_dist0 (1/\<epsilon>)) ?B = 0"
        unfolding null_sets_def using measure_eq_emeasure_eq_ennreal [of"0 :: real" "(Lap_dist0 (1/\<epsilon>))" "?B"] by auto
    qed
    thus ?thesis
      by auto
  qed
  also have "... = \<P>(r in (Lap_dist0 (1/\<epsilon>)). ereal(r + d) \<ge> (fst (max_argmax (map2 (+) cs rs))))"
    by (metis UNIV_I space_Lap_dist0)
  finally show ?thesis .
qed

paragraph \<open>differential privacy inequality on @{term RNM_M}\<close>

lemma DP_RNM_M_i:
  fixes xs ys rs :: "real list" and x y :: real and i n :: nat
  assumes "length xs = n" and "length ys = n" and "length rs = n"
    and adj': "x \<ge> y \<and> x \<le> y + 1"
    and adj: "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys"
    and "i \<le> n"
  shows "\<P>(j in (RNM_M xs rs x i). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM_M ys rs y i). j = i) \<and> \<P>(j in (RNM_M ys rs y i). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM_M xs rs x i). j = i)"
proof(cases"n = 0")
  case True
  hence xs: "xs = []" and ys: "ys = []" and rs: "rs = []" and i: "i = 0"
    using assms by blast+
  from pose have e: "exp \<epsilon> \<ge> 1"
    by auto
  thus ?thesis unfolding xs ys rs i RNM_M_Nil_is_return_0
    by (auto simp: measure_return)
next
  case False
  have eq1: "\<And>i :: nat. i \<le> n \<Longrightarrow> \<P>(j in (RNM_M xs rs x i). j = i) = \<P>(r in (Lap_dist0 (1/\<epsilon>)). ereal(r + x) \<ge> (fst (max_argmax (map2 (+) xs rs))))"
    using RNM_M_probability assms pose by auto
  have eq2: "\<And>i :: nat. i \<le> n \<Longrightarrow> \<P>(j in (RNM_M ys rs y i). j = i) = \<P>(r in (Lap_dist0 (1/\<epsilon>)). ereal(r + y) \<ge> (fst (max_argmax (map2 (+) ys rs))))"
    using RNM_M_probability assms pose by auto
  have fin: "finite_measure (Lap_dist0 (1/\<epsilon>))"
    using prob_space_Lap_dist0 by (metis prob_space.finite_measure)

  show ?thesis
    using False assms
  proof(intro conjI)
    show "\<P>(j in RNM_M xs rs x i. j = i) \<le> exp \<epsilon> * \<P>(j in RNM_M ys rs y i. j = i)"
      unfolding eq1[OF assms(6)] eq2[OF assms(6)]
    proof-
      have "{r :: real. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (r + x)} \<subseteq> {r :: real. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + x)}"
        using fst_max_argmax_adj[of"xs"_"ys" "rs"] assms by(intro subsetI, unfold mem_Collect_eq,auto)
      also have "... \<subseteq> {r :: real. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y + 1)}"
        using adj' Collect_mono_iff le_ereal_le by force
      also have "... = {r | v r :: real. v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
        by (auto simp: add.commute add.left_commute)
      finally have ineq1: "{r. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (r + x)} \<subseteq> {r | v r :: real. v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}".

      have meas1: "{z :: real. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} \<in> sets (Lap_dist0 (1/\<epsilon>))"
        by auto

      have "measure (Lap_dist0 (1/\<epsilon>)) {r. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (r + x)} \<le> measure (Lap_dist0 (1/\<epsilon>)) {r | v r :: real. v = r + 1 \<and> fst (max_argmax(map2 (+) ys rs)) \<le> ereal (v + y)}"
      proof(intro measure_mono_fmeasurable ineq1)
        show "{z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} \<in> fmeasurable (Lap_dist0 (1/\<epsilon>))"
          using prob_space_Lap_dist finite_measure.fmeasurable_eq_sets fin meas1 by blast
        show "{r. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (r + x)} \<in> sets (Lap_dist0 (1/\<epsilon>))"
          by auto
      qed
      also have "... \<le> (exp \<epsilon>) * measure (Lap_dist (1/\<epsilon>) (-1)) {r | v r :: real. v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} + (0 :: real)"
        using meas1 unfolding Lap_dist0_def by(intro DP_divergence_leE meas1 DP_divergence_Lap_dist'_eps pose, auto)
      also have "... = (exp \<epsilon>) * measure (Lap_dist (1/\<epsilon>) (-1)) {r | v r :: real. v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
        by auto
      also have "... = (exp \<epsilon>) * measure ((Lap_dist0 (1/\<epsilon>)) \<bind> (\<lambda> r. return borel (r + (-1)))) {r | v r :: real. v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
        unfolding Lap_dist_def2[of "(1 / \<epsilon>)" "-1"] Lap_dist0_def by auto
      also have "... = (exp \<epsilon>) * measure (Lap_dist0 (1/\<epsilon>)) {(r + 1)| v r :: real. v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
      proof(subst subprob_space.measure_bind)
        show "subprob_space (Lap_dist0 (1/\<epsilon>))"
          by auto
        show "(\<lambda>r. return borel (r + (-1))) \<in> Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M subprob_algebra borel"
          by auto
        show "exp \<epsilon> * (LINT x|Lap_dist0 (1/\<epsilon>). measure (return borel (x + (-1))) {z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)})
 = exp \<epsilon> * measure (Lap_dist0 (1/\<epsilon>)) {z. \<exists>v r. z = r + 1 \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
          using meas1 proof(subst measure_return)
          show "{z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} \<in> sets borel"
            by auto
          have "exp \<epsilon> * (LINT x|Lap_dist0 (1/\<epsilon>). indicat_real {z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} (x + (-1))) = exp \<epsilon> * (LINT x|Lap_dist0 (1/\<epsilon>). indicat_real {z + 1 | z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} x)"
          proof(subst Bochner_Integration.integral_cong)
            have 1: "\<And>x. \<forall>z. x = z + 1 \<longrightarrow> \<not> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (z + 1 + y) \<Longrightarrow> indicat_real {z. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (z + 1 + y)} (x - 1) = 0"
            proof-
              fix x :: real assume "\<forall>z :: real. x = z + 1 \<longrightarrow> \<not> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (z + 1 + y)"
              hence *: "\<And>z. x = z + 1 \<Longrightarrow> \<not> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (x + y)"by auto
              hence "\<not> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (x + y)"using *[of"x - 1"] by auto
              thus "indicat_real {z. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (z + 1 + y)} (x - 1) = 0"by auto
            qed
            show "\<And>x. indicat_real {z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} (x + - 1) = indicat_real {z + 1 | z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} x"
              by(split split_indicator, intro conjI impI allI,auto simp: 1)
          qed(auto)
          also have "... = exp \<epsilon> * measure (Lap_dist0 (1/\<epsilon>)) {z + 1 | z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
            using Bochner_Integration.integral_indicator space_Lap_dist0 by auto
          also have "... = exp \<epsilon> * measure (Lap_dist0 (1/\<epsilon>)) {z. \<exists>v r. z = r + 1 \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
            by (metis (no_types, lifting) add_cancel_right_right is_num_normalize(1) real_add_minus_iff)
          finally show "exp \<epsilon> * (LINT x|Lap_dist0 (1/\<epsilon>). indicat_real {z. \<exists>v r. z = r \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)} (x + - 1)) = exp \<epsilon> * Sigma_Algebra.measure (Lap_dist0 (1/\<epsilon>)) {z. \<exists>v r. z = r + 1 \<and> v = r + 1 \<and> fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}".
        qed
      qed(auto)
      also have "... = exp \<epsilon> * Sigma_Algebra.measure (Lap_dist0 (1/\<epsilon>)) {v. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (v + y)}"
        by (metis (no_types, lifting) add_cancel_right_right is_num_normalize(1) real_add_minus_iff)
      finally have "Sigma_Algebra.measure (Lap_dist0 (1/\<epsilon>)) {r. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (r + x)} \<le> exp \<epsilon> * Sigma_Algebra.measure (Lap_dist0 (1/\<epsilon>)) {r. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y)}"by auto
      thus"\<P>(r in Lap_dist0 (1/\<epsilon>). fst (max_argmax (map2 (+) xs rs)) \<le> ereal (r + x)) \<le> exp \<epsilon> * \<P>(r in Lap_dist0 (1/\<epsilon>). fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y))"
        using space_Lap_dist0 by auto
    qed
  next
    show "\<P>(j in RNM_M ys rs y i. j = i) \<le> exp \<epsilon> * \<P>(j in RNM_M xs rs x i. j = i)"
      unfolding eq1[OF assms(6)] eq2[OF assms(6)]
    proof-
      have "{r :: real. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y)} \<subseteq> {r :: real. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + x)}"
        using assms adj' Collect_mono_iff le_ereal_le by force
      also have "... \<subseteq> {r :: real. fst (max_argmax (map2 (+) xs rs)) - 1 \<le> ereal (r + x)}"
        using ereal_diff_add_transpose fst_max_argmax_adj[of"xs"_"ys" "rs"] assms by fastforce
      also have "... \<subseteq> {v - (1 :: real) |v :: real. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
      proof(rule subsetI)
        fix z :: real assume "z \<in> {r. fst (max_argmax (map2 (+) xs rs)) - 1 \<le> ereal (r + x)}"
        hence "fst (max_argmax (map2 (+) xs rs)) - 1 \<le> ereal (z + x)"
          by blast
        hence "fst (max_argmax (map2 (+) xs rs)) - 1 + 1 \<le> ereal (z + x) + 1"
          by (metis add.commute add_left_mono)
        hence "fst (max_argmax (map2 (+) xs rs)) - 1 + 1 \<le> ereal ((z + 1) + x)"
          by (auto simp: add.commute add.left_commute)
        hence "fst (max_argmax (map2 (+) xs rs)) \<le> ereal ((z + 1) + x)"
          by (metis add.commute add_0 add_diff_eq_ereal cancel_comm_monoid_add_class.diff_cancel ereal_minus(1) one_ereal_def zero_ereal_def)
        hence "z + (1 :: real) \<in> {v :: real. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
          by auto
        thus"z \<in> {v - (1 :: real) |v :: real. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
          by force
      qed
      finally have ineq2: "{r. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y)} \<subseteq> {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}".

      have "{v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} = (\<lambda>r. r + 1)-` {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
        by force
      also have "... \<in> sets (Lap_dist0 (1/\<epsilon>))"
        by auto
      finally have meas2[measurable]: "{v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} \<in> sets (Lap_dist0 (1/\<epsilon>))".

      hence "measure (Lap_dist0 (1/\<epsilon>)) {r. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y)} \<le> measure (Lap_dist0 (1/\<epsilon>)) {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
      proof(intro ineq2 measure_mono_fmeasurable)
        show "{r. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y)} \<in> sets (Lap_dist0 (1/\<epsilon>))"
          by auto
        thus "{v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} \<in> fmeasurable (Lap_dist0 (1/\<epsilon>))"
          using prob_space_Lap_dist finite_measure.fmeasurable_eq_sets fin meas2 by blast
      qed
      also have "... \<le> (exp \<epsilon>) * measure (Lap_dist (1/\<epsilon>) (-1)) {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} + 0"
        using meas2 unfolding Lap_dist0_def by (intro DP_divergence_leE DP_divergence_Lap_dist'_eps pose, auto)
      also have "... = (exp \<epsilon>) * measure ((Lap_dist0 (1/\<epsilon>)) \<bind> (\<lambda> r. return borel (r + (-1)))) {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
        unfolding Lap_dist_def2[of "(1 / \<epsilon>)" "-1"] Lap_dist0_def by auto
      also have "... = (exp \<epsilon>) * measure (Lap_dist0 (1/\<epsilon>)) {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
      proof(subst subprob_space.measure_bind)
        show "subprob_space (Lap_dist0 (1/\<epsilon>))"
          by auto
        show "(\<lambda>r. return borel (r + -1)) \<in> Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M subprob_algebra borel"
          by auto
        show meas22: "{v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} \<in> sets borel"
          using meas2 sets_Lap_dist0 by blast
        show "exp \<epsilon> * (LINT z|Lap_dist0 (1/\<epsilon>). measure (return borel (z + - 1)) {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}) =
 exp \<epsilon> * measure (Lap_dist0 (1/\<epsilon>)) {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
        proof(subst measure_return,intro meas22)
          have "exp \<epsilon> * (LINT z|Lap_dist0 (1/\<epsilon>). indicat_real {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} (z + - 1)) = exp \<epsilon> * (LINT z|Lap_dist0 (1/\<epsilon>). indicat_real {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} z)"
          proof(subst Bochner_Integration.integral_cong)
            fix z :: real
            show "indicat_real {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} (z + - 1) = indicat_real {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} z"
              unfolding indicator_def by auto
            show "exp \<epsilon> * integral\<^sup>L (Lap_dist0 (1/\<epsilon>)) (indicat_real {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}) =
 exp \<epsilon> * integral\<^sup>L (Lap_dist0 (1/\<epsilon>)) (indicat_real {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)})"
              by auto
          qed(auto)
          also have "... = exp \<epsilon> * measure (Lap_dist0 (1/\<epsilon>)) {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}"
            using Bochner_Integration.integral_indicator space_Lap_dist by auto

          finally show "exp \<epsilon> * (LINT z|Lap_dist0 (1/\<epsilon>). indicat_real {v - 1 |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)} (z + - 1)) =
 exp \<epsilon> * Sigma_Algebra.measure (Lap_dist0 (1/\<epsilon>)) {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}".
        qed
      qed

      finally have " Sigma_Algebra.measure (Lap_dist0 (1/\<epsilon>)) {r. fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y)}
 \<le> exp \<epsilon> * Sigma_Algebra.measure (Lap_dist0 (1/\<epsilon>)) {v |v. fst (max_argmax (map2 (+) xs rs)) \<le> ereal (v + x)}".
      thus"\<P>(r in Lap_dist0 (1/\<epsilon>). fst (max_argmax (map2 (+) ys rs)) \<le> ereal (r + y)) \<le> exp \<epsilon> * \<P>(r in Lap_dist0 (1/\<epsilon>). fst (max_argmax (map2 (+) xs rs)) \<le> ereal (r + x))"
        using space_Lap_dist0 by auto
    qed
  qed
qed

paragraph \<open> Aggregating the differential privacy inequalities on @{term RNM_M} to those of @{term RNM'} \<close>

lemma RNM'_expand:
  fixes n :: nat
  assumes "length xs = n" and "i \<le> n"
  shows "(RNM' (list_insert x xs i)) = do{rs \<leftarrow> (Lap_dist0_list (1 / \<epsilon>) (length xs)); (RNM_M xs rs x i)}"
  using assms
proof(induction n arbitrary: xs i)
  note [measurable del] = borel_measurable_count_space
  case 0
  hence xs: "xs = []" and i: "i = 0"
    by auto
  have "Lap_dist0_list (1 / \<epsilon>) 0 \<bind> (\<lambda>rs. RNM_M [] rs x i) = (return (listM borel) []) \<bind> (\<lambda>rs. RNM_M [] rs x i)"
    by auto
  also have "... = RNM_M [] [] x i"
    by(subst bind_return[where N = "(count_space UNIV)"],auto simp: space_listM RNM_M_def argmax_insert_def argmax_list_def comp_def case_prod_beta)
  also have "... = return (count_space UNIV) 0"
    using RNM_M_Nil_is_return_0 RNM_M_def argmax_insert_def unfolding  list_insert_def by force
  also have "... = RNM' (list_insert x [] i)"
    unfolding list_insert_def take.simps drop.simps append.simps RNM'_singleton by auto
  finally show ?case unfolding xs i by auto
next
  note borel_measurable_count_space[measurable del]
  case (Suc n)
  then obtain a ys where xs: "xs = a # ys" and n: "length ys = n"
    by (metis Suc_length_conv)
  have xxsl: "\<And>x. length (x # xs) = Suc (Suc n)"
    using n xs by auto

  have Lap_mechanism_multi_replicate_insert: "\<And>n k :: nat. k \<le> n \<Longrightarrow>( Lap_dist0_list (1 / \<epsilon>) (Suc n)) = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert z zs k)))"
  proof-
    fix n k :: nat assume "k \<le> n"
    thus"Lap_dist0_list (1 / \<epsilon>) (Suc n) = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert z zs k)))"
    proof(induction n arbitrary: k)
      case 0
      hence k: "k = 0"
        by auto
      thus ?case unfolding k list_insert_def unfolding Lap_dist0_def Lap_dist0_list.simps(2) append_Cons append_Nil drop_0 take_0 by auto
    next
      case (Suc n)
      thus ?case proof(induction k)
        case 0
        thus ?case unfolding list_insert_def unfolding Lap_dist0_def Lap_dist0_list.simps(2) append_Cons append_Nil drop_0 take_0 by auto
      next
        case (Suc k)
        hence "k \<le> n" by auto
        hence 1: " Lap_dist0_list (1 / \<epsilon>) (Suc n) = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert z zs k)))"
          using Suc.prems(1) by auto
        have "Lap_dist0_list (1 / \<epsilon>) (Suc (Suc n)) = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>ys. return (listM borel) (y # ys)))"
          unfolding Lap_dist0_list.simps(2) Lap_dist0_def by auto
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert z zs k)))) \<bind> (\<lambda>ys. return (listM borel) (y # ys)))"
          using 1 by auto
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. (return (listM borel) (list_insert z zs k)) \<bind> (\<lambda>ys. return (listM borel) (y # ys))))))"
        proof(subst bind_assoc)
          show "\<And>y. (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert z zs k))) \<in> Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
            unfolding list_insert_def by measurable
          show "\<And>y. (\<lambda>ys. return (listM borel) (y # ys)) \<in> listM borel \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
            by measurable
          show "Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert x zs k)) \<bind> (\<lambda>ys. return (listM borel) (y # ys)))) = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert z zs k) \<bind> (\<lambda>ys. return (listM borel) (y # ys)))))"
            by(subst bind_assoc,auto simp:list_insert_def) measurable
        qed
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (y # (list_insert z zs k))))))"
          by(subst bind_return,auto simp:list_insert_def space_listM) measurable
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) ((list_insert y (z # zs) (Suc k)))))))"
          unfolding list_insert_def by auto
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) ((list_insert y (z # zs) (Suc k)))))))"
        proof(subst Giry_Monad.pair_prob_space.bind_rotate)
          show "pair_prob_space (Lap_dist0 (1/\<epsilon>)) (Lap_dist0 (1/\<epsilon>))"
            unfolding pair_prob_space_def pair_sigma_finite_def prob_space_Lap_dist using prob_space_Lap_dist prob_space_imp_sigma_finite by auto
          show "(\<lambda>(x, y). Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. return (listM borel) (list_insert y (x # zs) (Suc k)))) \<in> Lap_dist0 (1/\<epsilon>) \<Otimes>\<^sub>M Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
            unfolding list_insert_def by auto
        qed(auto)
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. (return (listM borel) (z # zs)) \<bind> (\<lambda>zs2. return (listM borel) ((list_insert y zs2 (Suc k))))))))"
          by(subst bind_return,auto simp:space_listM list_insert_def) measurable
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>z. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>zs. (return (listM borel) (z # zs))) \<bind> (\<lambda>zs2. return (listM borel) ((list_insert y zs2 (Suc k)))))))"
          by(subst bind_assoc,auto simp:space_listM list_insert_def) measurable
        also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>y. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>zs2. return (listM borel) ((list_insert y zs2 (Suc k)))))"
          unfolding Lap_dist0_list.simps(2) by(subst bind_assoc[where N = "listM borel" and R = "listM borel",symmetric],auto simp:space_listM list_insert_def Lap_dist0_def)
        finally show ?case.
      qed
    qed
  qed

  {
    fix x :: real and xs :: "real list" assume lxs: "length xs = Suc n"
    have xxsl: "\<And>x. length (x # xs) = Suc (Suc n)"
      using lxs by auto

    have "RNM' (x # xs) = Lap_dist0_list (1 / \<epsilon>) (Suc (Suc n)) \<bind> (\<lambda>ys. return (listM borel) (map2 (+) (x # xs) ys)) \<bind> (\<lambda>ys. return (count_space UNIV) (snd (max_argmax ys)))"
      unfolding RNM'_def Lap_dist_list_def2 argmax_list_def lxs xxsl by auto
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. return (listM borel) (x1 # x2))) \<bind> (\<lambda>ys. return (listM borel) (map2 (+) (x # xs) ys)) \<bind> (\<lambda>ys. return (count_space UNIV) (snd (max_argmax ys)))"
      unfolding Lap_dist0_list.simps(2) Lap_dist0_def by auto
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. (return (listM borel) (x1 # x2)) \<bind> (\<lambda>ys. return (listM borel) (map2 (+) (x # xs) ys)))) \<bind> (\<lambda>ys. return (count_space UNIV) (snd (max_argmax ys)))"
      by(subst bind_assoc[where N ="(listM borel)" and R ="(listM borel)"],measurable)+
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. return (listM borel) (map2 (+) (x # xs) (x1 # x2)))) \<bind> (\<lambda>ys. return (count_space UNIV) (snd (max_argmax ys)))"
      by(subst bind_return,measurable)
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. return (listM borel) ((x + x1) # (map2 (+) xs x2)))) \<bind> (\<lambda>ys. return (count_space UNIV) (snd (max_argmax ys)))"
      unfolding list.map by auto
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. (return (listM borel) ((x + x1) # (map2 (+) xs x2))) \<bind> (\<lambda>ys. return (count_space UNIV) (snd (max_argmax ys)))))"
      by(subst bind_assoc[where N ="(listM borel)" and R ="(count_space UNIV)"],measurable)+
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. return (count_space UNIV) (snd (max_argmax ((x + x1) # (map2 (+) xs x2))))))"
      by(subst bind_return,measurable)
    also have "... = Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((x + x1) # (map2 (+) xs x2))))))"
    proof(subst Giry_Monad.pair_prob_space.bind_rotate)
      show "pair_prob_space (Lap_dist0 (1/\<epsilon>)) ( Lap_dist0_list (1 / \<epsilon>) (Suc n))"
        unfolding pair_prob_space_def pair_sigma_finite_def
        by (meson prob_space_Lap_dist0 prob_space_Lap_dist0_list prob_space_imp_sigma_finite)
      have "(\<lambda>(xa, y). return (count_space UNIV) (snd (max_argmax ((x + xa) # map2 (+) xs y)))) = (return (count_space UNIV)) o (\<lambda> zs. snd (max_argmax zs)) o (\<lambda>(xa, y). ((x + xa) # map2 (+) xs y))"
        by auto
      also have "... \<in> Lap_dist0 (1/\<epsilon>) \<Otimes>\<^sub>M Lap_dist0_list (1 / \<epsilon>) (Suc n) \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)"
        by(intro measurable_comp[where N = "listM borel"] measurable_comp[where N = "(count_space UNIV)"], measurable)
      finally show "(\<lambda>(xa, y). return (count_space UNIV) (snd (max_argmax ((x + xa) # map2 (+) xs y)))) \<in> Lap_dist0 (1/\<epsilon>) \<Otimes>\<^sub>M Lap_dist0_list (1 / \<epsilon>) (Suc n) \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)".
    qed(auto)
    finally have "RNM' (x # xs) = Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((x + x1) # map2 (+) xs x2)))))".
  }note * = this

  show ?case proof(cases"i = 0")
    case True
    hence xxs: "(list_insert x xs i) = x # xs"
      unfolding list_insert_def by auto
    have "RNM' (list_insert x xs i) = Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((x + x1) # (map2 (+) xs x2))))))"
      unfolding xxs using *[of xs x, OF Suc(2)] by auto
    also have "... = Lap_dist0_list (1 / \<epsilon>) (length xs) \<bind> (\<lambda>rs. RNM_M xs rs x i)"
      unfolding RNM_M_def argmax_insert_def True drop_0 take_0 Suc.prems argmax_list_def comp_def  list_insert_def
      by (metis (no_types, lifting) Cons_eq_appendI add.commute case_prod_conv ext self_append_conv2)
    finally show ?thesis.
  next
    case False
    then obtain k :: nat where i: "i = Suc k"
      by (metis list_decode.cases)
    hence insxxsi: "(list_insert x xs i) = a # (list_insert x ys k)"
      unfolding list_insert_def using xs by auto
    have klessn: "k \<le> n"
      using n i using Suc.prems(2) by auto
    have leninsxxsi: "length (list_insert x ys k) = Suc n"
      unfolding list_insert_def length_append length_drop length_take n using klessn by auto

    have "RNM' (list_insert x xs i) = Lap_dist0_list (1 / \<epsilon>) (Suc n)\<bind> (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((a + x1) # map2 (+) (list_insert x ys k) x2)))))"
      unfolding insxxsi *[of"(list_insert x ys k)"a,OF leninsxxsi] by auto
    also have "... = (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. return (listM borel) (list_insert p ps k)))) \<bind> (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((a + x1) # map2 (+) (list_insert x ys k) x2)))))"
      unfolding Lap_mechanism_multi_replicate_insert[of k n, OF klessn] by auto
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. (return (listM borel) (list_insert p ps k)) \<bind> (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((a + x1) # map2 (+) (list_insert x ys k) x2)))))))"
    proof(subst bind_assoc[where N ="(listM borel)" and R ="count_space UNIV"])
      show "(\<lambda>p. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. return (listM borel) (list_insert p ps k))) \<in> Lap_dist0 (1/\<epsilon>) \<rightarrow>\<^sub>M subprob_algebra (listM borel)"
        unfolding list_insert_def by measurable
      show 1: "(\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((a + x1) # map2 (+) (list_insert x ys k) x2))))) \<in> listM borel \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)"
        by(rule measurable_bind[where N = "borel"],auto)
      thus "Lap_dist0 (1/\<epsilon>) \<bind>
 (\<lambda>xa. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. return (listM borel) (list_insert xa ps k)) \<bind>
 (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((a + x1) # map2 (+) (list_insert x ys k) x2)))))) =
 Lap_dist0 (1/\<epsilon>) \<bind>
 (\<lambda>p. Lap_dist0_list (1 / \<epsilon>) n \<bind>
 (\<lambda>ps. return (listM borel) (list_insert p ps k) \<bind> (\<lambda>x2. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((a + x1) # map2 (+) (list_insert x ys k) x2)))))))"
        unfolding list_insert_def
        by(subst bind_assoc[where N ="listM borel" and R ="count_space UNIV"],auto)
    qed
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax ((a + x1) # map2 (+) (list_insert x ys k) (list_insert p ps k)))))))"
      by(subst bind_return[where N = "count_space UNIV"],auto)
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k))))))))"
      unfolding list_insert_def by auto
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k)))))))"
    proof-
      have "AE ps in Lap_dist0_list (1 / \<epsilon>) n. \<forall> x1 p. (snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k))))) = (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k))))"
      proof(rule AE_mp)
        show "\<And>x1 p. almost_everywhere (Lap_dist0_list (1 / \<epsilon>) n) (\<lambda>ps. ps \<in> {ps. length ps = n})"
        proof(rule prob_space.AE_prob_1)
          show "prob_space (Lap_dist0_list (1 / \<epsilon>) n)"
            by auto
          show "Sigma_Algebra.measure (Lap_dist0_list (1 / \<epsilon>) n) {ps. length ps = n} = 1"
            unfolding Lap_dist0_list_Lap_dist_list[symmetric] using emeasure_Lap_dist_list_length [of "(1 / \<epsilon>)" "(replicate n 0)"] unfolding measure_def length_replicate by auto
        qed
        show x: "AE ps\<in>{ps. length ps = n} in Lap_dist0_list (1 / \<epsilon>) n.
\<forall>x1 p.
 snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k)))) =
 snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k)))"
        proof(rule AE_I2,rule impI,intro allI)
          fix x1 p ps assume "ps \<in> space (Lap_dist0_list (1 / \<epsilon>) n)" and "ps \<in> {ps. length ps = n}"
          hence "length ps = n"by auto
          hence l: "length ps = length ys"using n by auto
          hence "(map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k))) = map (\<lambda> (x,y). x + y) (zip (take (Suc k) (a # ys) @ [x] @ drop (Suc k) (a # ys)) (take (Suc k) (p # ps) @ [x1] @ drop (Suc k) (p # ps)))"
            unfolding list_insert_def by auto
          also have "... = map (\<lambda> (x,y). x + y) ((zip (take (Suc k) (a # ys))(take (Suc k) (p # ps))) @ [(x,x1)] @ (zip (drop (Suc k) (a # ys)))(drop (Suc k) (p # ps)))"
            using l zip_append by auto
          also have "... = map (\<lambda> (x,y). x + y) ((take (Suc k) (zip (a # ys) (p # ps))) @ [(x,x1)] @ (drop (Suc k) (zip (a # ys)(p # ps))))"
            using l take_zip drop_zip by metis
          also have "... = list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k)"
            unfolding list_insert_def map_append drop_map take_map by auto
          finally have "map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k)) = list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k)".
          thus"snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k)))) = snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k)))"by auto
        qed
      qed
      hence x1: "\<And> x1. AE ps in Lap_dist0_list (1 / \<epsilon>) n. (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k))))))) = (Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k))))))"
        using AE_mp by auto
      hence "\<forall> x1. Lap_dist0_list (1 / \<epsilon>) n \<bind>
 (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k))))))) =
Lap_dist0_list (1 / \<epsilon>) n \<bind>
 (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k))))))"(is"\<forall> x1. ?P x1")
      proof(intro allI)
        fix x1 show "?P x1"
        proof(rule bind_cong_AE'[of"Lap_dist0_list (1 / \<epsilon>) n" "listM borel" "(\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k)))))))" "(count_space UNIV) :: nat measure" "(\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k))))))",OF _ _ _ x1])
          show "Lap_dist0_list (1 / \<epsilon>) n \<in> space (prob_algebra (listM borel))"
            by auto
          have 1: "take (Suc k) (a # ys) @ [x] @ drop (Suc k) (a # ys) \<in> space (listM borel)"
            using space_listM_borel_UNIV by auto
          have 2: "[x1] \<in> space (listM borel)"
            by auto
          show "(\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k))))))) \<in> listM borel \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)" unfolding list_insert_def
            using 1 2 by measurable
          have 3: "[x + x1] \<in> space (listM borel)"
            by auto
          show "(\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k)))))) \<in> listM borel \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
            unfolding list_insert_def using 1 3 by measurable
        qed
      qed
      thus"Lap_dist0 (1/\<epsilon>) \<bind>
 (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) n \<bind>
 (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (map2 (+) (list_insert x (a # ys) (Suc k)) (list_insert x1 (p # ps) (Suc k)))))))) =
 Lap_dist0 (1/\<epsilon>) \<bind>
 (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) n \<bind>
 (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) (p # ps)) (Suc k)))))))"
        by(auto elim!: bind_cong_AE')
    qed

    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. (return (listM borel)(p # ps)) \<bind> (\<lambda>rs. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) rs) (Suc k))))))))"
      unfolding list_insert_def by(subst bind_return,measurable)
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. ((Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. (return (listM borel)(p # ps))) \<bind> (\<lambda>rs. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) rs) (Suc k)))))))))"
      unfolding list_insert_def by(subst bind_assoc,measurable)
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. ((Lap_dist0_list (1 / \<epsilon>) n \<bind> (\<lambda>ps. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>p. (return (listM borel)(p # ps)))) \<bind> (\<lambda>rs. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) rs) (Suc k))))))))"
      unfolding list_insert_def
      by(subst bind_assoc[where N = "listM borel" and R = "count_space UNIV", THEN sym],auto)
    also have "... = Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. (Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>rs. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) rs) (Suc k)))))))"
      unfolding Lap_dist0_list.simps Lap_dist0_def proof(subst pair_prob_space.bind_rotate [where N = "listM borel"])
      show "pair_prob_space (Lap_dist0_list (1 / \<epsilon>) n) (Lap_dist (1 / \<epsilon>) 0)"
        unfolding pair_prob_space_def pair_sigma_finite_def Lap_dist_list_def2[symmetric] using prob_space_Lap_dist prob_space_Lap_dist
        by (auto simp: prob_space_imp_sigma_finite)
    qed auto
    also have "... = Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>rs. Lap_dist0 (1/\<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) rs) (Suc k))))))"
    proof(subst pair_prob_space.bind_rotate[where N = "count_space UNIV"])
      show "pair_prob_space (Lap_dist0 (1 / \<epsilon>)) (Lap_dist0_list (1 / \<epsilon>) (Suc n))"
        unfolding pair_prob_space_def pair_sigma_finite_def using prob_space_Lap_dist0 prob_space_Lap_dist0_list prob_space_imp_sigma_finite by metis
      show "(\<lambda>(xa, y). return (count_space UNIV) (snd (max_argmax (list_insert (x + xa) (map2 (+) (a # ys) y) (Suc k))))) \<in> Lap_dist0 (1/\<epsilon>) \<Otimes>\<^sub>M Lap_dist0_list (1 / \<epsilon>) (Suc n) \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)"
        unfolding list_insert_def listM_Nil by measurable
    qed(auto)
    finally have *: " RNM' (list_insert x xs i) = Lap_dist0_list (1 / \<epsilon>) (Suc n) \<bind> (\<lambda>rs. Lap_dist0 (1 / \<epsilon>) \<bind> (\<lambda>x1. return (count_space UNIV) (snd (max_argmax (list_insert (x + x1) (map2 (+) (a # ys) rs) (Suc k))))))" .

    show ?thesis unfolding RNM_M_def * argmax_insert_def case_prod_beta argmax_list_def comp_def
      by (simp add: i n xs Suc.prems list_insert_def Groups.add_ac(2))
  qed
qed

lemma DP_RNM'_M_i:
  fixes xs ys :: "real list" and i n :: nat
  assumes lxs: "length xs = n"
    and lys: "length ys = n"
    and adj: "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys"
  shows "\<P>(j in (RNM' xs). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM' ys). j = i) \<and> \<P>(j in (RNM' ys). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM' xs). j = i)"
  using assms proof(cases"n = 0")
  case True
  hence xs: "xs = []" and ys: "ys = []"
    using lxs lys by blast+
  have 0: "RNM' [] = return (count_space UNIV) 0"using RNM'_Nil by auto
  thus ?thesis proof(cases"i = 0")
    case True
    hence 02: "\<P>(j in local.RNM' []. j = 0) = 1"unfolding 0 measure_def by auto
    show ?thesis unfolding xs ys True 02 using pose by auto
  next
    case False
    hence 02: "\<P>(j in local.RNM' []. j = i) = 0"unfolding 0 measure_def by auto
    show ?thesis unfolding xs ys 02 by auto
  qed
next
  case False
  have space_Lap_dist_multi [simp]: "\<And> xs b. space (Lap_dist_list b xs) = UNIV"
    by (auto simp: sets_Lap_dist_list sets_eq_imp_space_eq)
  have space_RNM'_UNIV[simp]: "\<And>xs. space (local.RNM' xs) = UNIV"
    unfolding RNM'_def by (metis empty_not_UNIV sets_return space_Lap_dist_multi space_bind space_count_space)
  hence space_RNM'_UNIV2[simp]: "\<And>xs i. {j. j\<in> space (RNM' xs) \<and> j = i} = {i}"
    by auto

  thus ?thesis proof(cases"i < n")
    case True
    define x where x: "x = nth xs i"
    define y where y: "y = nth ys i"
    define xs2 where xs2: "xs2 = (list_exclude i xs)"
    define ys2 where ys2: "ys2 = (list_exclude i ys)"
    have xs: "xs = (list_insert x xs2 i)"
      by (metis length_0_conv length_greater_0_conv list_insert'_is_list_insert lxs cong_nth_total_nth False True insert_exclude x xs2)
    have ys: "ys = (list_insert y ys2 i)"
      by (metis length_0_conv length_greater_0_conv list_insert'_is_list_insert lys cong_nth_total_nth False True insert_exclude y ys2)
    obtain m :: nat where n: "n = Suc m"using True False not0_implies_Suc by blast
    have lxs2: "length xs2 = m"
      by (metis One_nat_def True add.assoc add.commute add_left_imp_eq id_take_nth_drop length_append list.size(4) list_exclude_def lxs n plus_1_eq_Suc xs2)
    have lys2: "length ys2 = m"
      by (metis One_nat_def True add.assoc add.commute add_left_imp_eq id_take_nth_drop length_append list.size(4) list_exclude_def lys n plus_1_eq_Suc ys2)
    have ilessm: "i \<le> m"
      using True n by auto
    have 1: "take i xs2 = take i xs"
      unfolding xs2 list_exclude_def by auto have 2: "take i ys2 = take i ys"
      unfolding ys2 list_exclude_def by auto
    have 3: "drop i xs2 = drop (Suc i) xs"
      by (metis"1"append_eq_append_conv append_take_drop_id list_exclude_def xs2)
    have 4: "drop i ys2 = drop (Suc i) ys"
      by (metis"2"append_eq_append_conv append_take_drop_id list_exclude_def ys2)
    from adj have 5: "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (take i xs2)(take i ys2)" and 6: "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (drop i xs2)(drop i ys2)"
      unfolding 1 2 3 4 using list_all2_takeI list_all2_dropI by blast+
    have adj': "x \<ge> y \<and> x \<le> y + 1"
      unfolding x y using list_all2_conv_all_nth True False lxs lys adj by (metis (mono_tags, lifting))
    have adj2: "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs2 ys2"
      using 5 6 lxs2 lys2 append_take_drop_id[of i xs2,THEN sym] append_take_drop_id[of i ys2,THEN sym] list_all2_appendI by fastforce
    note * = DP_RNM_M_i[of xs2 m ys2 _ y x, OF lxs2 lys2 _ adj' adj2 ilessm]
    have 7: "local.RNM' xs = (Lap_dist0_list (1 /\<epsilon>) m) \<bind> (\<lambda>rs. RNM_M xs2 rs x i)"
      using RNM'_expand[of xs2 m i x,OF lxs2 ilessm] unfolding xs lxs2 by auto
    have 8: "local.RNM' ys = (Lap_dist0_list (1 /\<epsilon>) m) \<bind> (\<lambda>rs. local.RNM_M ys2 rs y i)"
      using RNM'_expand[of ys2 m i y,OF lys2 ilessm] unfolding ys lys2 by auto

    have "\<P>(j in local.RNM' xs. j = i) = measure (Lap_dist0_list (1 /\<epsilon>) m \<bind> (\<lambda>rs. local.RNM_M xs2 rs x i)) {i}"
      by (metis"7"space_RNM'_UNIV2)
    also have "... = (LINT rs|Lap_dist0_list (1 /\<epsilon>) m. measure (local.RNM_M xs2 rs x i) {i})"
    proof(rule subprob_space.measure_bind)
      show "subprob_space (Lap_dist0_list (1 /\<epsilon>) m)"
        by (metis prob_space_Lap_dist0_list prob_space_imp_subprob_space)
      thus "(\<lambda>rs. local.RNM_M xs2 rs x i) \<in> (Lap_dist0_list (1 /\<epsilon>) m) \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)"
        unfolding RNM_M_def argmax_insert_def argmax_list_def using list_insert_def by auto
      show "{i} \<in> sets (count_space UNIV)"
        by auto
    qed
    also have "... = (\<integral> rs \<in> space (Lap_dist0_list (1 /\<epsilon>) m). measure (local.RNM_M xs2 rs x i) {i} \<partial>(Lap_dist0_list (1 /\<epsilon>) m))"
      unfolding set_lebesgue_integral_def
      by (metis (no_types, lifting) Bochner_Integration.integral_cong indicator_eq_1_iff scaleR_simps(12))
    also have "... = (\<integral> rs \<in> {xs. length xs = m} . measure (local.RNM_M xs2 rs x i) {i} \<partial>(Lap_dist0_list (1 /\<epsilon>) m))"
    proof(subst set_integral_null_delta)
      show "integrable (Lap_dist0_list (1 /\<epsilon>) m) (\<lambda>rs. Sigma_Algebra.measure (local.RNM_M xs2 rs x i) {i})"
        by(rule probability_kernel_evaluation_integrable[where M ="count_space UNIV"],auto simp: RNM_M_def argmax_insert_def prob_space.finite_measure)
      show 1: "{xs. length xs = m} \<in> sets (Lap_dist0_list (1 /\<epsilon>) m)"
        unfolding sets_Lap_dist0_list using sets_listM_length[of borel m] by auto
      show "space (Lap_dist0_list (1 /\<epsilon>) m) \<in> sets (Lap_dist0_list (1 /\<epsilon>) m)"
        by blast
      have "emeasure (Lap_dist0_list (1 /\<epsilon>) m) (space (Lap_dist0_list (1 /\<epsilon>) m)) = 1"
        by(rule prob_space.emeasure_space_1,auto)
      hence "emeasure (Lap_dist0_list (1 /\<epsilon>) m) (space (Lap_dist0_list (1 /\<epsilon>) m) - {xs. length xs = m}) = 0"
        using emeasure_Lap_dist_list_length[of " (1 /\<epsilon>)" "replicate m 0"] unfolding length_replicate length_map Lap_dist0_list_Lap_dist_list[symmetric] space_Lap_dist_multi
      proof(subst emeasure_Diff)
        have "space (Lap_dist_list (1 / \<epsilon>) (replicate m 0)) \<in> sets (Lap_dist_list (1 / \<epsilon>) (replicate m 0))"
          by blast
        thus " UNIV \<in> sets (Lap_dist_list (1 / \<epsilon>) (replicate m 0))"
          unfolding sets_Lap_dist_list by auto
        show "{xs. length xs = m} \<in> sets (Lap_dist_list (1 / \<epsilon>) (replicate m 0))"
          unfolding sets_Lap_dist_list using sets_listM_length[of borel m] space_borel lists_UNIV by auto
      qed(auto)
      thus "sym_diff (space (Lap_dist0_list (1 / \<epsilon>) m)) {xs. length xs = m} \<in> null_sets (Lap_dist0_list (1 / \<epsilon>) m)"
        by (metis"1"Diff_mono null_setsI sets.compl_sets sets.sets_into_space sup.orderE)
    qed(auto)
    finally have 9: " \<P>(j in RNM' xs. j = i) = (\<integral>rs\<in>{xs. length xs = m}. Sigma_Algebra.measure (RNM_M xs2 rs x i) {i}\<partial>Lap_dist0_list (1 / \<epsilon>) m)".


    have "\<P>(j in local.RNM' ys. j = i) = measure (Lap_dist0_list (1 /\<epsilon>) m \<bind> (\<lambda>rs. local.RNM_M ys2 rs y i)) {i}"
      by (metis"8"space_RNM'_UNIV2)
    also have "... = LINT rs| Lap_dist0_list (1 /\<epsilon>) m. measure (local.RNM_M ys2 rs y i) {i}"
    proof(rule subprob_space.measure_bind)
      show "subprob_space (Lap_dist0_list (1 /\<epsilon>) m)"
        by (metis prob_space_Lap_dist0_list prob_space_imp_subprob_space)
      show "(\<lambda>rs. local.RNM_M ys2 rs y i) \<in> Lap_dist0_list (1 /\<epsilon>) m \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)"
        unfolding RNM_M_def argmax_insert_def by(auto simp: list_insert_def)
      show "{i} \<in> sets (count_space UNIV)"by auto
    qed
    also have "... = (\<integral> rs \<in> space (Lap_dist0_list (1 /\<epsilon>) m) . measure (local.RNM_M ys2 rs y i) {i} \<partial>(Lap_dist0_list (1 /\<epsilon>) m))"
      unfolding set_lebesgue_integral_def
      by (metis (no_types, lifting) Bochner_Integration.integral_cong indicator_eq_1_iff scaleR_simps(12))
    also have "... = (\<integral> rs \<in> {ys. length ys = m} . measure (local.RNM_M ys2 rs y i) {i} \<partial>(Lap_dist0_list (1 /\<epsilon>) m))"
    proof(subst set_integral_null_delta)
      show "integrable (Lap_dist0_list (1 /\<epsilon>) m) (\<lambda>rs. Sigma_Algebra.measure (local.RNM_M ys2 rs y i) {i})"
        by(rule probability_kernel_evaluation_integrable[where M ="count_space UNIV"],auto simp: RNM_M_def argmax_insert_def prob_space.finite_measure)
      show 1: "{ys. length ys = m} \<in> sets (Lap_dist0_list (1 /\<epsilon>) m)"
        unfolding sets_Lap_dist0_list using sets_listM_length[of borel m] by auto
      show "space (Lap_dist0_list (1 /\<epsilon>) m) \<in> sets (Lap_dist0_list (1 /\<epsilon>) m)"
        by blast
      have "emeasure (Lap_dist0_list (1 /\<epsilon>) m) (space (Lap_dist0_list (1 /\<epsilon>) m)) = 1"
        by(rule prob_space.emeasure_space_1,auto)
      hence "emeasure (Lap_dist0_list (1 /\<epsilon>) m) (space (Lap_dist0_list (1 /\<epsilon>) m) - {ys. length ys = m}) = 0"
        using emeasure_Lap_dist_list_length[of " (1 /\<epsilon>)" "replicate m 0"]
        unfolding length_replicate length_map Lap_dist0_list_Lap_dist_list[symmetric] space_Lap_dist_multi
      proof(subst emeasure_Diff)
        have "space (Lap_dist_list (1 / \<epsilon>) (replicate m 0)) \<in> sets (Lap_dist_list (1 / \<epsilon>) (replicate m 0))"
          by blast
        thus " UNIV \<in> sets (Lap_dist_list (1 / \<epsilon>) (replicate m 0))"
          unfolding sets_Lap_dist_list[of "(1 / \<epsilon>)" "(replicate m 0)"] space_Lap_dist_list[of "(1 / \<epsilon>)" "(replicate m 0)"] space_listM space_borel lists_UNIV by auto
        show "{xs. length xs = m} \<in> sets (Lap_dist_list (1 / \<epsilon>) (replicate m 0))"
          unfolding sets_Lap_dist_list[of "(1 / \<epsilon>)" "(replicate m 0)"]
          using sets_listM_length[of borel m] space_borel lists_UNIV by auto
      qed(auto)
      thus "sym_diff (space (Lap_dist0_list (1 / \<epsilon>) m)) {xs. length xs = m} \<in> null_sets (Lap_dist0_list (1 / \<epsilon>) m)"
        by (metis"1"Diff_mono null_setsI sets.compl_sets sets.sets_into_space sup.orderE)
    qed(auto)
    finally have 10: "\<P>(j in local.RNM' ys. j = i) = (\<integral>rs\<in>{ys. length ys = m}. Sigma_Algebra.measure (local.RNM_M ys2 rs y i) {i}\<partial>Lap_dist0_list (1 / \<epsilon>) m)".

    have c: "finite_measure (Lap_dist0_list (1 / \<epsilon>) m)"
      by (auto simp: prob_space.finite_measure)

    show ?thesis
    proof(rule conjI)
      show "\<P>(j in local.RNM' xs. j = i) \<le> exp \<epsilon> * \<P>(j in local.RNM' ys. j = i)"
        unfolding 9 10
      proof(subst set_integral_mult_right[THEN sym],intro set_integral_mono)
        show "\<And>rs. rs \<in> {xs. length xs = m} \<Longrightarrow> Sigma_Algebra.measure (local.RNM_M xs2 rs x i) {i} \<le> exp \<epsilon> * Sigma_Algebra.measure (local.RNM_M ys2 rs y i) {i}"
          using conjunct1[OF *] space_RNM_M by auto

        show "set_integrable (Lap_dist0_list (1 / \<epsilon>) m) {xs. length xs = m} (\<lambda>xa. Sigma_Algebra.measure (local.RNM_M xs2 xa x i) {i})"
          unfolding set_integrable_def real_scaleR_def
        proof(intro integrable_ess_bounded_finite_measure c ess_bounded_mult indicat_real_ess_bounded probability_kernel_evaluation_ess_bounded)
          show "{xs. length xs = m} \<in> sets (Lap_dist0_list (1 / \<epsilon>) m)"
            unfolding Lap_dist0_list_Lap_dist_list[symmetric] sets_Lap_dist_list using sets_listM_length[of borel m] by auto
          show "(\<lambda>xa. local.RNM_M xs2 xa x i) \<in> Lap_dist0_list (1 / \<epsilon>) m \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
            unfolding RNM_M_def argmax_insert_def by(auto simp: list_insert_def)
        qed(auto)
        show "set_integrable (Lap_dist0_list (1 / \<epsilon>) m) {xs. length xs = m} (\<lambda>x. exp \<epsilon> * Sigma_Algebra.measure (local.RNM_M ys2 x y i) {i})"
          unfolding set_integrable_def real_scaleR_def
        proof(intro integrable_ess_bounded_finite_measure c ess_bounded_mult indicat_real_ess_bounded probability_kernel_evaluation_ess_bounded)
          show "{xs. length xs = m} \<in> sets (Lap_dist0_list (1 / \<epsilon>) m)"
            unfolding Lap_dist0_list_Lap_dist_list[symmetric] sets_Lap_dist_list using sets_listM_length[of borel m] by auto
          show "(\<lambda>x. local.RNM_M ys2 x y i) \<in> Lap_dist0_list (1 / \<epsilon>) m \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
            unfolding RNM_M_def argmax_insert_def by(auto simp: list_insert_def)
        qed(auto)
      qed
      show "\<P>(j in local.RNM' ys. j = i) \<le> exp \<epsilon> * \<P>(j in local.RNM' xs. j = i)"
        unfolding 9 10
      proof(subst set_integral_mult_right[THEN sym],intro set_integral_mono)
        show "\<And>rs. rs \<in> {ys. length ys = m} \<Longrightarrow> Sigma_Algebra.measure (local.RNM_M ys2 rs y i) {i} \<le> exp \<epsilon> * Sigma_Algebra.measure (local.RNM_M xs2 rs x i) {i}"
          using conjunct2[OF *] space_RNM_M by auto
        show "set_integrable (Lap_dist0_list (1 / \<epsilon>) m) {ys. length ys = m} (\<lambda>x. Sigma_Algebra.measure (local.RNM_M ys2 x y i) {i})"
          unfolding set_integrable_def real_scaleR_def
        proof(intro integrable_ess_bounded_finite_measure c ess_bounded_mult indicat_real_ess_bounded probability_kernel_evaluation_ess_bounded)
          show "{xs. length xs = m} \<in> sets (Lap_dist0_list (1 / \<epsilon>) m)"
            unfolding Lap_dist0_list_Lap_dist_list[symmetric] sets_Lap_dist_list using sets_listM_length[of borel m] by auto
          show "(\<lambda>x. local.RNM_M ys2 x y i) \<in> Lap_dist0_list (1 / \<epsilon>) m \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
            unfolding RNM_M_def argmax_insert_def by(auto simp: list_insert_def)
        qed(auto)
        show "set_integrable (Lap_dist0_list (1 / \<epsilon>) m) {ys. length ys = m} (\<lambda>xa. exp \<epsilon> * Sigma_Algebra.measure (local.RNM_M xs2 xa x i) {i})"
          unfolding set_integrable_def real_scaleR_def
        proof(intro integrable_ess_bounded_finite_measure c ess_bounded_mult indicat_real_ess_bounded probability_kernel_evaluation_ess_bounded)
          show "{xs. length xs = m} \<in> sets (Lap_dist0_list (1 / \<epsilon>) m)"
            unfolding Lap_dist0_list_Lap_dist_list[symmetric] sets_Lap_dist_list using sets_listM_length[of borel m] by auto
          show "(\<lambda>xa. local.RNM_M xs2 xa x i) \<in> Lap_dist0_list (1 / \<epsilon>) m \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
            unfolding RNM_M_def argmax_insert_def by(auto simp: list_insert_def)
        qed(auto)
      qed
    qed
  next
    case False
    hence xsl: "i \<ge> length xs" and ysl: "i \<ge> length ys"
      using lxs lys by auto
    have xs': "xs \<noteq> []" and ys': "ys \<noteq> []"using \<open>n \<noteq> 0\<close> assms by blast+
    hence 1: "\<P>(j in local.RNM' xs. j = i) = 0"using RNM'_support[of xs i, OF xsl xs'] unfolding measure_def by auto
    hence 2: "\<P>(j in local.RNM' ys. j = i) = 0"using RNM'_support[of ys i, OF ysl ys'] unfolding measure_def by auto
    show ?thesis unfolding 1 2 by auto
  qed
qed

lemma DP_divergence_RNM':
  fixes xs ys :: "real list"
  assumes adj: "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys"
  shows "DP_divergence (RNM' xs) (RNM' ys) \<epsilon> \<le> 0 \<and> DP_divergence (RNM' ys) (RNM' xs) \<epsilon> \<le> 0"
proof-
  have sets_RNM': "\<And>xs. sets (local.RNM' xs) = sets (count_space UNIV)"
    unfolding RNM'_def
    by (metis emeasure_empty indicator_eq_0_iff indicator_eq_1_iff prob_space.emeasure_space_1 prob_space_Lap_dist_list sets_bind sets_return)
  hence space_RNM': "\<And>xs. space (local.RNM' xs) = UNIV"
    by (metis sets_eq_imp_space_eq space_count_space)

  have 0: "\<And> xs A. emeasure (local.RNM' xs) A = ennreal (Sigma_Algebra.measure (local.RNM' xs) A)"
  proof(intro finite_measure.emeasure_eq_measure)
    fix xs :: "real list" and A :: "nat set"have "xs \<in> space(listM borel)"by auto
    show "finite_measure (local.RNM' xs)"
      by (meson \<open>xs \<in> space (listM borel)\<close> measurable_RNM' measurable_prob_algebraD subprob_space.axioms(1) subprob_space_kernel)
  qed

  have "length xs = length ys"
    using adj by(auto simp: list_all2_lengthD)
  then obtain n :: nat where lxs: "length xs = n" and lys: "length ys = n"
    by auto
  have 1: "\<And>i :: nat. \<P>(j in (RNM' xs). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM' ys). j = i)
 \<and> \<P>(j in (RNM' ys). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM' xs). j = i)"
    using DP_RNM'_M_i[OF lxs lys adj] by auto
  hence "\<And>i :: nat. \<P>(j in (RNM' xs). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM' ys). j = i)"
    by auto
  hence "\<And>n :: nat. enn2real(measure (local.RNM' xs) {n}) \<le> enn2real((exp \<epsilon>) * measure (local.RNM' ys){n})"
    unfolding measure_def by (auto simp: space_RNM')
  hence ineq1: "\<And>n :: nat. emeasure (local.RNM' xs) {n} \<le> (exp \<epsilon>) * emeasure (local.RNM' ys){n}"
    unfolding 0
    by (metis (no_types, opaque_lifting)"0"Sigma_Algebra.measure_def dual_order.trans enn2real_nonneg ennreal_enn2real ennreal_leI ennreal_mult'' linorder_not_le top_greatest)
  from 1 have "\<And>i :: nat. \<P>(j in (RNM' ys). j = i) \<le> (exp \<epsilon>) * \<P>(j in (RNM' xs). j = i)"
    by auto
  hence "\<And>n :: nat. enn2real(measure (local.RNM' ys) {n}) \<le> enn2real((exp \<epsilon>) * measure (local.RNM' xs){n})"
    unfolding measure_def by (auto simp: space_RNM')
  hence ineq2: "\<And>n :: nat. emeasure (local.RNM' ys) {n} \<le> (exp \<epsilon>) * emeasure (local.RNM' xs){n}"
    unfolding 0
    by (metis (no_types, opaque_lifting)"0"Sigma_Algebra.measure_def dual_order.trans enn2real_nonneg ennreal_enn2real ennreal_leI ennreal_mult'' linorder_not_le top_greatest)

  {
    fix A :: "nat set" and xs :: "real list"
    have "emeasure (local.RNM' xs) A = (\<Sum>i. emeasure (local.RNM' xs) ((\<lambda>j :: nat. if j \<in> A then {j} else {}) i))"
    proof(subst suminf_emeasure)
      show "range (\<lambda>i :: nat. if i \<in> A then {i} else {}) \<subseteq> sets (local.RNM' xs)"
        using sets_RNM' by auto
      show "disjoint_family (\<lambda>i. if i \<in> A then {i} else {})"
        unfolding disjoint_family_on_def by auto
      show "emeasure (local.RNM' xs) A = emeasure (local.RNM' xs) (\<Union>i. if i \<in> A then {i} else {})"by auto
    qed
    also have "... = (\<Sum>i. emeasure (local.RNM' xs){i} * indicator A i)"
      by(rule suminf_cong,auto)
    finally have "emeasure (local.RNM' xs) A = (\<Sum>i. emeasure (local.RNM' xs) {i} * indicator A i)".
  }note * = this

  show ?thesis proof(rule conjI)
    have "DP_divergence (local.RNM' xs) (local.RNM' ys) \<epsilon> \<le> (0 :: real)"
    proof(rule DP_divergence_leI)
      fix A assume "A \<in> sets (local.RNM' xs)"
      have "emeasure (local.RNM' xs) A = (\<Sum>i. emeasure (local.RNM' xs){i} * indicator A i)"
        using *[of xs A] by auto
      also have "... \<le> (\<Sum>i. (exp \<epsilon>) * (emeasure (local.RNM' ys){i} * indicator A i))"
      proof(rule suminf_le)
        show "summable (\<lambda>i. emeasure (local.RNM' xs) {i} * indicator A i)"by auto
        show "summable (\<lambda>i. ennreal (exp \<epsilon>) * (emeasure (local.RNM' ys){i} * indicator A i))"by auto
        show "\<And>n. emeasure (local.RNM' xs) {n} * indicator A n \<le> ennreal (exp \<epsilon>) * (emeasure (local.RNM' ys) {n} * indicator A n)"
          using ineq1
          by (metis ab_semigroup_mult_class.mult_ac(1) antisym_conv1 mult_right_mono nless_le zero_less_iff_neq_zero)
      qed
      also have "... = ennreal (exp \<epsilon>) * (\<Sum>i. (emeasure (local.RNM' ys) {i} * indicator A i))"
        by auto
      also have "... = ennreal (exp \<epsilon>) * emeasure (local.RNM' ys) A"
        using *[of ys A] by auto
      finally have "emeasure (local.RNM' xs) A \<le> ennreal (exp \<epsilon>) * emeasure (local.RNM' ys) A".
      thus"Sigma_Algebra.measure (local.RNM' xs) A \<le> exp \<epsilon> * Sigma_Algebra.measure (local.RNM' ys) A + 0"
        by (metis"0"add_cancel_right_right enn2real_eq_posreal_iff enn2real_leI ennreal_mult'' exp_ge_zero measure_nonneg split_mult_pos_le zero_less_measure_iff)
    qed
    thus"DP_divergence (local.RNM' xs) (local.RNM' ys) \<epsilon> \<le> 0"using zero_ereal_def by auto
  next
    have "DP_divergence (local.RNM' ys) (local.RNM' xs) \<epsilon> \<le> (0 :: real)"
    proof(rule DP_divergence_leI)
      fix A assume "A \<in> sets (local.RNM' ys)"
      have "emeasure (local.RNM' ys) A = (\<Sum>i. emeasure (local.RNM' ys){i} * indicator A i)"
        using *[of ys A] by auto
      also have "... \<le> (\<Sum>i. (exp \<epsilon>) * (emeasure (local.RNM' xs){i} * indicator A i))"
      proof(rule suminf_le)
        show "summable (\<lambda>i. emeasure (local.RNM' ys) {i} * indicator A i)"by auto
        show "summable (\<lambda>i. ennreal (exp \<epsilon>) * (emeasure (local.RNM' xs){i} * indicator A i))"by auto
        show "\<And>n. emeasure (local.RNM' ys) {n} * indicator A n \<le> ennreal (exp \<epsilon>) * (emeasure (local.RNM' xs) {n} * indicator A n)"
          using ineq2
          by (metis ab_semigroup_mult_class.mult_ac(1) antisym_conv1 mult_right_mono nless_le zero_less_iff_neq_zero)
      qed
      also have "... = ennreal (exp \<epsilon>) * (\<Sum>i. (emeasure (local.RNM' xs) {i} * indicator A i))"
        by auto
      also have "... = ennreal (exp \<epsilon>) * emeasure (local.RNM' xs) A"
        using *[of xs A] by auto
      finally have "emeasure (local.RNM' ys) A \<le> ennreal (exp \<epsilon>) * emeasure (local.RNM' xs) A".
      thus"Sigma_Algebra.measure (local.RNM' ys) A \<le> exp \<epsilon> * Sigma_Algebra.measure (local.RNM' xs) A + 0"
        by (metis"0"add_cancel_right_right enn2real_eq_posreal_iff enn2real_leI ennreal_mult'' exp_ge_zero measure_nonneg split_mult_pos_le zero_less_measure_iff)
    qed
    thus"DP_divergence (local.RNM' ys) (local.RNM' xs) \<epsilon> \<le> 0"using zero_ereal_def by auto
  qed
qed

lemma differential_privacy_LapMech_RNM':
  shows "differential_privacy RNM' {(xs, ys) | xs ys. list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys } \<epsilon> 0"
  unfolding differential_privacy_def DP_inequality_cong_DP_divergence
proof(rule ballI)
  fix x::"real list \<times> real list" assume " x \<in> {(xs, ys) |xs ys. list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) xs ys}"
  then obtain xs ys where x: "x = (xs,ys)" and 1: "list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) xs ys"
    by blast
  thus "case x of (d1, d2) \<Rightarrow> DP_divergence (RNM' d1) (RNM' d2) \<epsilon> \<le> ereal 0 \<and> DP_divergence (RNM' d2) (RNM' d1) \<epsilon> \<le> ereal 0"
    using DP_divergence_RNM'[of xs ys]
    by (simp add: zero_ereal_def)
qed

corollary differential_privacy_LapMech_RNM'_sym:
  shows "differential_privacy RNM' {(xs, ys) | xs ys. list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys \<or> list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) ys xs } \<epsilon> 0"
proof-
  have 1: " {(xs, ys) | xs ys. list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys \<or> list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) ys xs }
 = {(xs, ys) | xs ys. list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys } \<union> converse {(xs, ys) | xs ys. list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys }"
    by blast
  show ?thesis unfolding 1 proof(rule differential_privacy_symmetrize)
    show " differential_privacy RNM' {(xs, ys) |xs ys. list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) xs ys} \<epsilon> 0"
      by (rule differential_privacy_LapMech_RNM')
  qed
qed

theorem differential_privacy_LapMech_RNM:
  shows "differential_privacy (LapMech_RNM \<epsilon>) adj \<epsilon> 0"
  unfolding LapMech_RNM_RNM'_c
proof(rule differential_privacy_preprocessing)
  show "(0::real) \<le> \<epsilon>"
    using pose by auto
  show "differential_privacy RNM' {(xs, ys) | xs ys. list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) xs ys \<or> list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) ys xs } \<epsilon> 0"
    by (rule differential_privacy_LapMech_RNM'_sym)
  show "c \<in> M \<rightarrow>\<^sub>M listM borel"
    using c by auto
  show "\<forall>(x, y)\<in> adj. (c x, c y) \<in> {(xs, ys) |xs ys. list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) xs ys \<or> list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) ys xs}"
    using cond adj by auto
  show "adj \<subseteq> space M \<times> space M"
    using adj.
  show " {(xs, ys) |xs ys. list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) xs ys \<or> list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) ys xs} \<subseteq> space (listM borel) \<times> space (listM borel)"
    unfolding space_listM space_borel lists_UNIV by auto
qed

end (* end of context *)

end(* end of locale *)

subsection \<open> Formal Proof of Exact [Claim 3.9,AFDP]\<close>

text \<open>
 In the above theorem @{thm Lap_Mechanism_RNM_mainpart.differential_privacy_LapMech_RNM}, the query @{term c} to add noise is abstracted.
 We here instantiate it with the counting query. Thus we here formalize and show the monotonicity and Lipschitz property of it.
\<close>

locale Lap_Mechanism_RNM_counting =
  fixes n::nat
    and m::nat (* number of counting queries *)
    and Q :: "nat \<Rightarrow> nat \<Rightarrow> bool" (* count decision *)
  assumes "\<And>i. i \<in> {0..<m} \<Longrightarrow> (Q i) \<in> UNIV \<rightarrow> UNIV" (* Q is defined everywhere *)
begin

interpretation results_AFDP n
  by(unfold_locales)

interpretation L1_norm_list "(UNIV::nat set)" "(\<lambda> x y. \<bar>int x - int y\<bar>)" n
  by(unfold_locales,auto)

lemma adjacency_1_int_list:
  assumes "(xs,ys) \<in> adj_L1_norm"
  shows "(xs = ys) \<or> (\<exists> as a b bs. xs = as @ (a # bs) \<and> ys = as @ (b # bs) \<and> \<bar>int a - int b\<bar> = 1)"
  using assms unfolding adj_L1_norm_def sp_Dataset_def space_restrict_space dist_L1_norm_list_def space_L1_norm_list_def
proof(induction n arbitrary: xs ys)
  case 0
  hence "xs = []" and "ys = []" by auto
  then show ?case by auto
next
  case (Suc n)
  hence "length xs = Suc n"
    and "length ys = Suc n"
    and sum:"(\<Sum>i = 1..Suc n. real_of_int \<bar>int (xs ! (i - 1)) - int (ys ! (i - 1))\<bar>) \<le> 1"
    by blast+
  then obtain x y ::nat and xs2 ys2 ::"nat list"
    where xs: "xs = x # xs2"
      and ys: "ys = y # ys2"
      and xs2: "length xs2 = n"
      and ys2:"length ys2 = n"
    by (meson length_Suc_conv)
  hence 1: "\<bar>int x - int y\<bar> + (\<Sum>i = 1..n. real_of_int \<bar>int (xs2 ! (i - 1)) - int (ys2 ! (i - 1))\<bar>) = (\<Sum>i = 1..Suc n. real_of_int \<bar>int (xs ! (i - 1)) - int(ys ! (i - 1))\<bar>)"
    using L1_norm_list.list_sum_dist_Cons[symmetric, OF xs2 ys2] by auto
  then show ?case
  proof(cases "x = y")
    case True
    hence "\<bar>x - y\<bar> = 0"
      by auto
    with 1 sum have 2: "(\<Sum>i = 1..n. real_of_int \<bar>int(xs2 ! (i - 1)) - int(ys2 ! (i - 1))\<bar>) \<le> 1"
      by auto
    have *: "(xs2, ys2) \<in> {(xs, ys) |xs ys. xs \<in> {xs \<in> lists UNIV. length xs = n} \<and> ys \<in> {xs \<in> lists UNIV. length xs = n} \<and> (\<Sum>i = 1..n. real_of_int \<bar>int(xs ! (i - 1)) - int(ys ! (i - 1))\<bar>) \<le> 1}"
      using xs2 ys2 2 by auto
    from Suc.IH[of xs2 ys2] * have "(xs2 = ys2) \<or> (\<exists> as a b bs. xs2 = as @ (a # bs) \<and> ys2 = as @ (b # bs) \<and> \<bar>int a - int b\<bar> = 1)"
      unfolding space_listM space_count_space by auto
    with True xs ys show ?thesis
      by (meson Cons_eq_appendI)
  next
    case False
    hence 0: "1 \<le> \<bar>int x - int y\<bar>"
      by auto
    with 1 sum have 2: "(\<Sum>i = 1..n. real_of_int \<bar>int(xs2 ! (i - 1)) - int(ys2 ! (i - 1))\<bar>) \<le> 0"
      by auto
    have "(\<Sum>i = 1..n. real_of_int \<bar>int(xs2 ! (i - 1)) - int(ys2 ! (i - 1))\<bar>) \<ge> 0"
      by auto
    with 2 have 3:"(\<Sum>i = 1..n. real_of_int \<bar>int(xs2 ! (i - 1)) - int(ys2 ! (i - 1))\<bar>) = 0"
      by argo
    with sum 1 have " \<bar>int x - int y\<bar> \<le> 1"
      by auto
    with 0 have 4:" \<bar>int x - int y\<bar> = 1"
      by auto
    hence "xs2 = ys2" using xs2 ys2 3
    proof(subst L1_norm_list.dist_L1_norm_list_zero[of "UNIV" "\<lambda> x y. real_of_int \<bar>int x - int y\<bar>" xs2 n ys2 ,symmetric])
      show 1: " L1_norm_list UNIV (\<lambda>x y. real_of_int \<bar>int x - int y\<bar>)"
        by(unfold_locales)
      show " (\<Sum>i = 1..n. real_of_int \<bar>int(xs2 ! (i - 1)) - int(ys2 ! (i - 1))\<bar>) = 0 \<Longrightarrow> L1_norm_list.dist_L1_norm_list (\<lambda>x y. real_of_int \<bar>int x - int y\<bar>) n xs2 ys2 = 0 "
        unfolding L1_norm_list.dist_L1_norm_list_def[OF 1] by simp
    qed(auto)
    with False xs ys 4 show ?thesis by blast
  qed
qed

paragraph \<open> formalization of a list of counting query \<close>

(* preliminaries *)

primrec counting'::"nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "counting' i 0 _ = 0" |
  "counting' i (Suc k) xs = (if Q i k then (nth_total 0 xs k) else 0) + counting' i k xs"

lemma measurable_counting'[measurable]:
  shows "(\<lambda> xs. counting' i k xs) \<in> (listM (count_space (UNIV::nat set))) \<rightarrow>\<^sub>M (count_space (UNIV::nat set))"
  by(induction k,auto)

lemma counting'_sum:
  assumes "k \<le> length xs"
  shows "counting' i k xs = (\<Sum>j\<in>{0..<k}. (if Q i j then (xs ! j) else 0))"
proof-
  have "counting' i k xs = (\<Sum>j\<in>{0..<k}. (if Q i j then (nth_total 0 xs j) else 0))"
    by(induction k,auto)
  also have "... = (\<Sum>j\<in>{0..<k}. (if Q i j then (xs ! j) else 0))"
  proof(subst sum.cong)
    show "{0..<k} = {0..<k}" by auto
    show " \<And>x. x \<in> {0..<k} \<Longrightarrow> (if Q i x then (nth_total 0 xs x) else 0) = (if Q i x then xs ! x else 0)"
      using assms unfolding nth_total_def2 by auto
  qed(auto)
  finally show ?thesis by auto
qed

lemma sensitvity_counting':
  assumes "(xs,ys) \<in> adj_L1_norm"
    and len: "k \<le> n"
  shows "\<bar>int (counting' i k xs) - int (counting' i k ys)\<bar> \<le> 1"
proof-
  from assms have xsl: "length xs = n" and ysl: "length ys = n" and le: "dist_L1_norm_list xs ys \<le> 1" and i: "k \<le> length xs" and i2: "k \<le> length ys"
    by (auto simp:space_L1_norm_list_def adj_L1_norm_def sp_Dataset_def space_restrict_space dist_L1_norm_list_def space_listM)
  from adjacency_1_int_list[OF assms(1)]
  consider "xs = ys" | "(\<exists>as a b bs. xs = as @ a # bs \<and> ys = as @ b # bs \<and> \<bar>int a - int b\<bar> = 1)"
    by auto
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis by auto
  next
    case 2
    then obtain as a b bs
      where xs: "xs = as @ a # bs"
        and ys: "ys = as @ b # bs"
        and a: "\<bar>int a - int b\<bar> = 1"
      by blast
    then show ?thesis unfolding counting'_sum[OF i] counting'_sum[OF i2]
    proof-
      have "\<bar>int (\<Sum>j = 0..<k. if Q i j then xs ! j else 0) - int (\<Sum>j = 0..<k. if Q i j then ys ! j else 0)\<bar>
 = \<bar>(\<Sum>j = 0..<k. (if Q i j then int (xs ! j) else int 0)) - (\<Sum>j = 0..<k. if Q i j then int (ys ! j) else int 0)\<bar>"
        unfolding of_nat_sum if_distrib by auto
      also have "... = \<bar>(\<Sum>j = 0..<k. (if Q i j then int (xs ! j) else 0)) - (\<Sum>j = 0..<k. if Q i j then int (ys ! j) else 0)\<bar>"
        unfolding int_ops(1) by auto
      also have "... = \<bar>(\<Sum>j = 0..<k. (if Q i j then int (xs ! j) else 0) - (if Q i j then int (ys ! j) else 0))\<bar>"
        by (auto simp: sum_subtractf)
      also have "... = \<bar>(\<Sum>j = 0..<k. (if Q i j then int (xs ! j) - int (ys ! j) else 0))\<bar>"
        by (metis (full_types, opaque_lifting) cancel_comm_monoid_add_class.diff_cancel)
      also have "... \<le> (\<Sum>j = 0..<k. \<bar>(if Q i j then int (xs ! j) - int (ys ! j) else 0)\<bar>)"
        by(rule sum_abs)
      also have "... \<le> (\<Sum>j = 0..<k. (if Q i j then \<bar> int (xs ! j) - int (ys ! j)\<bar> else 0))"
        by(auto simp: if_distrib)
      also have "... \<le> (\<Sum>j = 0..<k. \<bar> int (xs ! j) - int (ys ! j)\<bar>)"
        by (auto simp: sum_mono)
      also have "... \<le> (\<Sum>j = 0..<n. \<bar> int (xs ! j) - int (ys ! j)\<bar>)"
        by(rule sum_mono2, auto simp:len)
      also have "... = (\<Sum>j = 1..n. \<bar> int (xs ! (j - 1)) - int (ys ! (j - 1))\<bar>)"
      proof(subst sum.reindex_cong[where l = "\<lambda> i. i - 1" and B = "{1..n}" and h = "\<lambda> x. \<bar>int (xs ! (x - 1)) - int (ys ! (x - 1))\<bar>"])
        show "inj_on (\<lambda>i. i - 1) {1..n}"
          unfolding inj_on_def by auto
        show "{0..<n} = (\<lambda>i. i - 1) ` {1..n}"
          unfolding image_def by force
      qed(auto)
      also have "... \<le> 1"
        using le of_int_le_1_iff unfolding dist_L1_norm_list_def by fastforce
      finally show "\<bar>int (\<Sum>j = 0..<k. if Q i j then xs ! j else 0) - int (\<Sum>j = 0..<k. if Q i j then ys ! j else 0)\<bar> \<le> 1".
    qed
  qed
qed

paragraph\<open>A component of a tuple of counting queries\<close>

definition counting::"nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "counting i xs = counting' i (length xs) xs"

lemma measurable_counting[measurable]:
  shows "(counting i ) \<in> (listM (count_space (UNIV::nat set))) \<rightarrow>\<^sub>M (count_space (UNIV::nat set))"
  unfolding counting_def by auto

lemma counting_sum:
  shows "counting i xs = (\<Sum>j\<in>{0..<length xs}. (if Q i j then (xs ! j) else 0))"
  unfolding counting_def by(rule counting'_sum,auto)

lemma sensitvity_counting:
  assumes "(xs,ys) \<in> adj_L1_norm"
  shows "\<bar>int (counting k xs) - int (counting k ys)\<bar> \<le> 1"
proof-
  from assms have xsl: "length xs = n" and ysl: "length ys = n" and le: " dist_L1_norm_list xs ys \<le> 1"
    by (auto simp:space_L1_norm_list_def adj_L1_norm_def sp_Dataset_def space_restrict_space dist_L1_norm_list_def space_listM)
  thus ?thesis unfolding counting_def using sensitvity_counting' assms
    by auto
qed

paragraph\<open>A list(tuple) of counting queries\<close>

definition counting_query::"nat list \<Rightarrow> nat list" where
  "counting_query xs = map (\<lambda> k. counting k xs) [0..<m]"

lemma measurable_counting_query[measurable]:
  shows "counting_query \<in> listM (count_space UNIV) \<rightarrow>\<^sub>M listM (count_space UNIV)"
  unfolding counting_query_def
proof(induction m)
  case 0
  then show ?case by auto
next
  case (Suc m)
  have " (\<lambda>xs. map (\<lambda>k. counting k xs) [0..<Suc m]) = (\<lambda>xs. (\<lambda>xs. map (\<lambda>k. counting k xs) [0..<m]) xs @ [counting m xs])"
    by auto
  also have "... \<in> listM (count_space UNIV) \<rightarrow>\<^sub>M listM (count_space UNIV)"
    using Suc by auto
  finally show ?case .
qed

lemma length_counting_query:
  shows "length(counting_query xs) = m"
  unfolding counting_query_def by auto

lemma counting_query_nth:
  fixes k::nat assumes "k < m"
  shows "counting_query xs ! k = counting k xs"
  unfolding counting_query_def by(subst nth_map_upt[of k m 0 "(\<lambda> k. counting k xs)"],auto simp: assms)

corollary counting_query_nth':
  fixes k::nat assumes "k < m"
  shows "map real (counting_query xs) ! k = real (counting k xs)"
  unfolding counting_query_def List.map.compositionality comp_def
  by(subst nth_map_upt[of k m 0 "(\<lambda> k. real (counting k xs))"],auto simp: assms)

end (* end of locale *)

paragraph \<open>A formalization of the report noisy max of noisy counting\<close>

context
  Lap_Mechanism_RNM_counting
begin

interpretation L1_norm_list "(UNIV::nat set)" "(\<lambda> x y. \<bar>int x - int y\<bar>)" n
  by(unfold_locales,auto)

interpretation results_AFDP n
  by(unfold_locales)

definition RNM_counting :: "real \<Rightarrow> nat list \<Rightarrow> nat measure" where
  "RNM_counting \<epsilon> x = do {
 y \<leftarrow> Lap_dist_list (1 / \<epsilon>) (counting_query x);
 return (count_space UNIV) (argmax_list y)
 }"

paragraph \<open> Naive evaluation of differential privacy of @{term RNM_counting} \<close>

text \<open> The naive proof is as follows:
 We first show that the counting query has the sensitivity @{term m}.
 @{term RNM_counting} adds the Laplace noise with scale @{term "1 / \<epsilon>"} to each element given by @{term counting_query}.
 Thanks to the postprocessing inequality, the final process @{term argmax_list} does not change the differential privacy.
 Therefore the differential privacy of @{term RNM_counting} is @{term "m * \<epsilon>"} \<close>

interpretation Lap_Mechanism_list "listM (count_space UNIV)" "counting_query" "adj_L1_norm" m
  unfolding counting_query_def
  by(unfold_locales,induction m, auto simp: space_listM)

lemma sensitvity_counting_query_part:
  fixes k::nat assumes "k < m"
    and "(xs,ys) \<in> adj_L1_norm"
  shows "\<bar>map real (counting_query xs) ! k - map real (counting_query ys) ! k \<bar> \<le> 1"
  unfolding counting_query_nth'[OF assms(1)] using sensitvity_counting[OF assms(2)]
  by (metis (mono_tags, opaque_lifting) of_int_abs of_int_diff of_int_le_1_iff of_int_of_nat_eq) (*takes long time*)

lemma sensitvity_counting_query:
  shows "sensitivity \<le> m"
proof(unfold sensitivity_def, rule Sup_least, elim CollectE exE)
  fix r::ereal and xs ys ::"nat list" assume r: "r = ereal (\<Sum>i = 1..m. \<bar>map real (counting_query xs) ! (i - 1) - map real (counting_query ys) ! (i - 1)\<bar>) \<and>
 xs \<in> space (listM (count_space UNIV)) \<and> ys \<in> space (listM (count_space UNIV)) \<and> (xs, ys) \<in> adj_L1_norm"
  hence "r = ereal (\<Sum>i = 1..m. \<bar>map real (counting_query xs) ! (i - 1) - map real (counting_query ys) ! (i - 1)\<bar>)"
    by auto
  also have "... = ereal (\<Sum>i = 0..<m. \<bar>map real (counting_query xs) ! i- map real (counting_query ys) ! i\<bar>)"
    by(subst sum.reindex_cong[where B = "{0..<m}" and l = Suc and h = "\<lambda>i. \<bar>map real (counting_query xs) ! i - map real (counting_query ys) ! i\<bar>" ],auto)
  also have "... \<le> ereal (\<Sum>i = 0..<m. (1::real) )"
    by(subst ereal_less_eq(3),subst sum_mono, auto intro !: sensitvity_counting_query_part simp: r)
  also have "... \<le> ereal m"
    by auto
  finally show "r \<le> ereal (real m)".
qed

corollary sensitvity_counting_query_finite:
  shows "sensitivity < \<infinity>"
  using sensitvity_counting_query by auto

theorem Naive_differential_privacy_LapMech_RNM_AFDP:
  assumes pose: "(\<epsilon>::real) > 0"
  shows "differential_privacy_AFDP (RNM_counting \<epsilon>) (real (m * \<epsilon>)) 0"
  unfolding RNM_counting_def
proof(rule differential_privacy_postprocessing[where R' = "count_space UNIV" and R = "listM borel" ])

  interpret Output: L1_norm_list "UNIV::real set" "\<lambda> m n. \<bar>m - n\<bar>" m
    by(unfold_locales,auto)

  show "0 \<le> real (m * \<epsilon>)"
    using pose by auto
  show "(\<lambda>x. Lap_dist_list (1 / real \<epsilon>) (map real (counting_query x))) \<in> (listM (count_space UNIV)) \<rightarrow>\<^sub>M prob_algebra (listM borel)"
    by auto
  show " (\<lambda>y. return (count_space UNIV) (argmax_list y)) \<in> listM borel \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    by auto
  show adj: " adj_L1_norm \<subseteq> space (listM (count_space UNIV)) \<times> space (listM (count_space UNIV))"
    unfolding space_listM space_count_space by auto
  have "differential_privacy ( (Lap_dist_list (1 / real \<epsilon>)) o (\<lambda>x. (map real (counting_query x))))
 adj_L1_norm (m * \<epsilon>) 0"
  proof(intro differential_privacy_preprocessing)
    show "0 \<le> real (m * \<epsilon>)"
      by fact
    show " (\<lambda>x. map real (counting_query x)) \<in> listM (count_space UNIV) \<rightarrow>\<^sub>M listM borel"
      by auto
    show "\<forall>(x, y)\<in>adj_L1_norm. (map real (counting_query x), map real (counting_query y))
 \<in> {(xs, ys) |xs ys. length xs = m \<and> length ys = m \<and> Output.dist_L1_norm_list xs ys \<le> real m}"
      unfolding adj_L1_norm_def Output.dist_L1_norm_list_def Int_def prod.case case_prod_beta
    proof(intro ballI, elim CollectE conjE exE )
      fix p xs ys assume p:"p = (xs, ys)" and "xs \<in> space sp_Dataset" and "ys \<in> space sp_Dataset" and adj:"dist_L1_norm_list xs ys \<le> 1"
      hence "length xs = n" and "length ys = n" and c: "(xs, ys) \<in> adj_L1_norm"
        by (auto simp:space_L1_norm_list_def adj_L1_norm_def sp_Dataset_def space_restrict_space dist_L1_norm_list_def space_listM)
      have "ereal (\<Sum>i = 1..m. \<bar>map real (counting_query xs) ! (i - 1) - map real (counting_query ys) ! (i - 1)\<bar>) \<le> \<Squnion> {ereal (\<Sum>i = 1..m. \<bar>map real (counting_query x) ! (i - 1) - map real (counting_query y) ! (i - 1)\<bar>) |x y. x \<in> UNIV \<and> y \<in> UNIV \<and> (x, y) \<in> adj_L1_norm}"
        by(auto intro!: Sup_upper c)
      also have "... \<le> ereal(real m)"
        using sensitvity_counting_query unfolding sensitivity_def space_listM space_count_space by auto
      finally show "(map real (counting_query (fst p)), map real (counting_query (snd p)))
 \<in> {(xs, ys) |xs ys. length xs = m \<and> length ys = m \<and> (\<Sum>i = 1..m. \<bar>xs ! (i - 1) - ys ! (i - 1)\<bar>) \<le> real m}"
        unfolding p using length_counting_query by auto
    qed
    show "differential_privacy (Lap_dist_list (1 / real \<epsilon>)) {(xs, ys) |xs ys. length xs = m \<and> length ys = m \<and> Output.dist_L1_norm_list xs ys \<le> real m} (real (m * \<epsilon>)) 0"
    proof(subst differential_privacy_adj_sym)
      show "sym {(xs, ys) |xs ys. length xs = m \<and> length ys = m \<and> Output.dist_L1_norm_list xs ys \<le> real m}"
        by(rule symI,auto simp:Output.MetL1.commute)
      show "\<forall>(d1, d2)\<in> {(xs, ys) |xs ys. length xs = m \<and> length ys = m \<and> Output.dist_L1_norm_list xs ys \<le> real m}.
 DP_inequality (Lap_dist_list (1 / real \<epsilon>) d1) (Lap_dist_list (1 / real \<epsilon>) d2) (real (m * \<epsilon>)) 0"
        unfolding Int_def prod.case case_prod_beta
      proof(intro ballI, elim CollectE exE conjE)
        fix p xs ys assume p: "p = (xs, ys)" and xs: "length xs = m " and ys: "length ys = m " and adj: "Output.dist_L1_norm_list xs ys \<le> real m"
        have 0: "(real m / (1 / real \<epsilon>)) = (real (m * \<epsilon>))"
          by auto
        from xs ys adj p DP_Lap_dist_list[of "(1 / real \<epsilon>)" xs m ys "real m",simplified 0]
        show " DP_inequality (Lap_dist_list (1 / real \<epsilon>) (fst p)) (Lap_dist_list (1 / real \<epsilon>) (snd p)) (real (m * \<epsilon>)) 0"
          unfolding DP_inequality_cong_DP_divergence Output.dist_L1_norm_list_def p fst_def snd_def
          by (metis assms(1) case_prod_conv ereal_eq_0(2) of_nat_0_le_iff zero_less_divide_1_iff)
      qed
    qed
  qed(auto simp: space_listM)
  thus "differential_privacy (\<lambda>x. Lap_dist_list (1 / real \<epsilon>) (map real (counting_query x))) adj_L1_norm (real (m * \<epsilon>)) 0"
    unfolding comp_def by auto
qed

paragraph \<open> True evaluation of differential privacy of @{term RNM_counting} \<close>

text \<open> in contrast to the naive proof, @{term counting_query} and @{term argmax_list} are essential. \<close>

lemma finer_sensitivity_counting_query:
  assumes "(xs,ys) \<in> adj_L1_norm"
  shows "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (counting_query xs) (counting_query ys) \<or> list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (counting_query ys) (counting_query xs)"
proof-
  note adjacency_1_int_list[OF assms]
  then consider "xs = ys" | "(\<exists>as a b bs. xs = as @ a # bs \<and> ys = as @ b # bs \<and> \<bar>int a - int b\<bar> = 1) \<and> xs \<noteq> ys"
    by auto
  then show ?thesis
  proof(cases)
    case 1
    define zs where zs: " zs = (counting_query ys)"
    have *: " list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) zs zs"
      by(induction zs,auto)
    thus ?thesis
      unfolding 1 zs by auto
  next
    case 2
    then obtain as a b bs
      where xs:"xs = as @ a # bs"
        and ys: "ys = as @ b # bs"
        and d:"a < b \<or> b < a"
        and diff:" \<bar>int a - int b\<bar> = 1"
      using linorder_less_linear by blast
    define m1::nat where m1: "m1 = length as"
    {
      fix k assume k: "k\<in>{0..<m}"
      have 1: "({0..<m1}\<union>{Suc m1..<length xs})\<union>{m1} = {0..<length xs}"
        unfolding m1 xs by auto
      have a: "xs ! m1 = a" and b: " ys ! m1 = b"
        unfolding m1 xs ys by auto

      have ***: "\<And>j. j \<in> ({0..<m1}\<union>{Suc m1..<length xs}) \<Longrightarrow> xs ! j = ys ! j"
      proof-
        fix j assume "j \<in> ({0..<m1}\<union>{Suc m1..<length xs})"
        hence 2: " j \<in> {0..<length xs}" and 3: " j \<noteq> m1"
          using 1 by auto
        have "\<And>j. j \<in> {0..<length xs} \<and> j \<noteq> m1 \<Longrightarrow> xs ! j = ys ! j"
          using m1 unfolding xs ys by (simp add: nth_Cons' nth_append)
        thus " xs ! j = ys ! j" using 2 3 by auto
      qed

      have " (\<Sum>j = 0..<length xs. if Q k j then xs ! j else 0) = (\<Sum>j\<in>({0..<m1}\<union>{Suc m1..<length xs})\<union>{m1}. if Q k j then xs ! j else 0)"
        using 1 by auto
      also have "... = (\<Sum>j\<in>{0..<m1}\<union>{Suc m1..<length xs}. if Q k j then xs ! j else 0) + (if Q k m1 then a else 0)"
        by(subst sum_Un_nat,auto simp: a)
      finally have A: "(\<Sum>j = 0..<length xs. if Q k j then xs ! j else 0) = (\<Sum>j\<in>{0..<m1}\<union>{Suc m1..<length xs}. if Q k j then xs ! j else 0) + (if Q k m1 then a else 0)" .

      have " (\<Sum>j = 0..<length ys. if Q k j then ys ! j else 0) = (\<Sum>j\<in>({0..<m1}\<union>{Suc m1..<length xs})\<union>{m1}. if Q k j then ys ! j else 0)"
        using 1 assms by (auto simp:space_L1_norm_list_def adj_L1_norm_def sp_Dataset_def space_restrict_space dist_L1_norm_list_def space_listM)
      also have "... = (\<Sum>j\<in>{0..<m1}\<union>{Suc m1..<length xs}. if Q k j then ys ! j else 0) + (if Q k m1 then b else 0)"
        by(subst sum_Un_nat,auto simp: b)
      also have "... = (\<Sum>j\<in>{0..<m1}\<union>{Suc m1..<length xs}. if Q k j then xs ! j else 0) + (if Q k m1 then b else 0)"
        using *** by(subst sum.cong[where B = "{0..<m1} \<union> {Suc m1..<length xs}" and h = "\<lambda> x. (if Q k x then xs ! x else 0) " ],auto)
      finally have B: "(\<Sum>j = 0..<length ys. if Q k j then ys ! j else 0) = (\<Sum>j\<in>{0..<m1} \<union> {Suc m1..<length xs}. if Q k j then xs ! j else 0) + (if Q k m1 then b else 0)" .

      note A B
    }note *** = this

    from d diff consider
      "b = a + 1" | "a = b + 1"
      by auto
    thus ?thesis proof(cases)
      case 1
      have " list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (counting_query ys) (counting_query xs)"
      proof(subst list_all2_conv_all_nth,rule conjI)
        show "length (counting_query ys) = length (counting_query xs)"
          using length_counting_query by auto
        show "\<forall>i<length (counting_query ys). counting_query xs ! i \<le> counting_query ys ! i \<and> counting_query ys ! i \<le> counting_query xs ! i + 1"
        proof(intro allI impI)
          fix i assume "i < length (counting_query ys)"
          hence i: "i < length [0..<m]" and i2: "i \<in> {0..<m}" and i3: "[0..<m] ! i = i"
            unfolding length_counting_query by auto
          thus "counting_query xs ! i \<le> counting_query ys ! i \<and> counting_query ys ! i \<le> counting_query xs ! i + 1"
            unfolding counting_query_def counting_sum list_all2_conv_all_nth length_map length_upt
              nth_map[of i "[0..<m]" "\<lambda>k. \<Sum>j = 0..<length xs. if Q k j then xs ! j else 0",OF i]
              nth_map[of i "[0..<m]" "\<lambda>k. \<Sum>j = 0..<length ys. if Q k j then ys ! j else 0",OF i]
              1 i3 ***(1)[OF i2] ***(2)[OF i2]
            by auto
        qed
      qed
      then show ?thesis by auto
    next
      case 2
      have " list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (counting_query xs) (counting_query ys)"
      proof(subst list_all2_conv_all_nth,rule conjI)
        show "length (counting_query xs) = length (counting_query ys)"
          using length_counting_query by auto
        show "\<forall>i<length (counting_query xs). counting_query ys ! i \<le> counting_query xs ! i \<and> counting_query xs ! i \<le> counting_query ys ! i + 1"
        proof(intro allI impI)
          fix i assume "i < length (counting_query xs)"
          hence i: "i < length [0..<m]" and i2: "i \<in> {0..<m}" and i3: "[0..<m] ! i = i"
            unfolding length_counting_query by auto
          thus "counting_query ys ! i \<le> counting_query xs ! i \<and> counting_query xs ! i \<le> counting_query ys ! i + 1"
            unfolding counting_query_def counting_sum list_all2_conv_all_nth length_map length_upt
              nth_map[of i "[0..<m]" "\<lambda>k. \<Sum>j = 0..<length xs. if Q k j then xs ! j else 0",OF i]
              nth_map[of i "[0..<m]" "\<lambda>k. \<Sum>j = 0..<length ys. if Q k j then ys ! j else 0",OF i]
              2 i3 ***(1)[OF i2] ***(2)[OF i2]
            by auto
        qed
      qed
      then show ?thesis by auto
    qed
  qed
qed

lemma list_all2_map_real_adj:
  assumes "list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) xs ys"
  shows "list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) (map real xs) (map real ys)"
  using assms nth_map[of _ xs real] nth_map[of _ ys real] unfolding list_all2_conv_all_nth length_map
  by force

lemma finer_sensitivity_counting_query':
  assumes "(xs,ys) \<in> adj_L1_norm"
  shows "list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (map real (counting_query xs))(map real (counting_query ys)) \<or> list_all2 (\<lambda> x y. x \<ge> y \<and> x \<le> y + 1) (map real (counting_query ys))(map real (counting_query xs))"
  using finer_sensitivity_counting_query[OF assms] list_all2_map_real_adj by auto

interpretation Lap_Mechanism_RNM_mainpart "(listM (count_space UNIV))" adj_L1_norm "counting_query"
proof(unfold_locales)
  show "(\<lambda>x. map real (counting_query x)) \<in> (listM (count_space UNIV)) \<rightarrow>\<^sub>M listM borel"
    by auto
  show " \<forall>(x, y)\<in> adj_L1_norm.
 list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) (map real (counting_query x)) (map real (counting_query y)) \<or>
 list_all2 (\<lambda>x y. y \<le> x \<and> x \<le> y + 1) (map real (counting_query y)) (map real (counting_query x))"
    using finer_sensitivity_counting_query' by auto
  show " adj_L1_norm \<subseteq> space (listM (count_space UNIV)) \<times> space (listM (count_space UNIV))"
    unfolding space_listM space_count_space by auto
qed

(* [Claim 3.9, AFDP] *)

theorem differential_privacy_LapMech_RNM_AFDP:
  assumes pose: "(\<epsilon>::real) > 0"
  shows "differential_privacy_AFDP (RNM_counting \<epsilon>) \<epsilon> 0"
  using differential_privacy_LapMech_RNM[OF assms]
  unfolding RNM_counting_def LapMech_RNM_def by auto

end (* end of context *)

end