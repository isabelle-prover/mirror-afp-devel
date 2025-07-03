theory More_Missing_Multiset
  imports
    "HOL-Combinatorics.Permutations"
    Polynomial_Factorization.Missing_Multiset
begin

lemma rel_mset_free:
  assumes rel: "rel_mset rel X Y" and xs: "mset xs = X"
  shows "\<exists>ys. mset ys = Y \<and> list_all2 rel xs ys"
proof-
  from rel[unfolded rel_mset_def] obtain xs' ys'
    where xs': "mset xs' = X" and ys': "mset ys' = Y" and xsys': "list_all2 rel xs' ys'" by auto
  from xs' xs have "mset xs = mset xs'" by auto
  from mset_eq_permutation[OF this]
  obtain f where perm: "f permutes {..<length xs'}" and xs': "permute_list f xs' = xs".
  then have [simp]: "length xs' = length xs" by auto
  from permute_list_nth[OF perm, unfolded xs'] have *: "\<And>i. i < length xs \<Longrightarrow> xs ! i = xs' ! f i" by auto
  note [simp] = list_all2_lengthD[OF xsys',symmetric]
  note [simp] = atLeast0LessThan[symmetric]
  note bij =  permutes_bij[OF perm]
  define ys where "ys \<equiv> map (nth ys' \<circ> f) [0..<length ys']"
  then have [simp]: "length ys = length ys'" by auto 
  have "mset ys = mset (map (nth ys') (map f [0..<length ys']))"
   unfolding ys_def by auto
  also have "... = image_mset (nth ys') (image_mset f (mset [0..<length ys']))"
    by (simp add: multiset.map_comp)
  also have "(mset [0..<length ys']) = mset_set {0..<length ys'}"
    by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set sorted_list_of_set_range) 
  also have "image_mset f (...) = mset_set (f ` {..<length ys'})"
    using inj_on_subset[OF bij_is_inj[OF bij]] by (subst image_mset_mset_set, auto)
  also have "... = mset [0..<length ys']" using perm by (simp add: permutes_image)
  also have "image_mset (nth ys') ... = mset ys'" by(fold mset_map, unfold map_nth, auto)
  finally have "mset ys = Y" using ys' by auto
  moreover have "list_all2 rel xs ys"
  proof(rule list_all2_all_nthI)
    fix i assume i: "i < length xs"
    with * have "xs ! i = xs' ! f i" by auto
    also from i permutes_in_image[OF perm]
    have "rel (xs' ! f i) (ys' ! f i)" by (intro list_all2_nthD[OF xsys'], auto)
    finally show "rel (xs ! i) (ys ! i)" unfolding ys_def using i by simp
  qed simp
  ultimately show ?thesis by auto
qed

lemma rel_mset_split:
  assumes rel: "rel_mset rel (X1+X2) Y"
  shows "\<exists>Y1 Y2. Y = Y1 + Y2 \<and> rel_mset rel X1 Y1 \<and> rel_mset rel X2 Y2"
proof-
  obtain xs1 where xs1: "mset xs1 = X1" using ex_mset by auto
  obtain xs2 where xs2: "mset xs2 = X2" using ex_mset by auto
  from xs1 xs2 have "mset (xs1 @ xs2) = X1 + X2" by auto
  from rel_mset_free[OF rel this] obtain ys
    where ys: "mset ys = Y" "list_all2 rel (xs1 @ xs2) ys" by auto
  then obtain ys1 ys2
    where ys12: "ys = ys1 @ ys2"
      and xs1ys1: "list_all2 rel xs1 ys1"
      and xs2ys2: "list_all2 rel xs2 ys2"
    using list_all2_append1 by blast
  from ys12 ys have "Y = mset ys1 + mset ys2" by auto
  moreover from xs1 xs1ys1 have "rel_mset rel X1 (mset ys1)" unfolding rel_mset_def by auto
  moreover from xs2 xs2ys2 have "rel_mset rel X2 (mset ys2)" unfolding rel_mset_def by auto
  ultimately show ?thesis by (subst exI[of _ "mset ys1"], subst exI[of _ "mset ys2"],auto)
qed

lemma rel_mset_OO:
  assumes AB: "rel_mset R A B" and BC: "rel_mset S B C"
  shows "rel_mset (R OO S) A C"
proof-
  from AB obtain as bs where A_as: "A = mset as" and B_bs: "B = mset bs" and as_bs: "list_all2 R as bs"
    by (auto simp: rel_mset_def)
  from rel_mset_free[OF BC] B_bs obtain cs where C_cs: "C = mset cs" and bs_cs: "list_all2 S bs cs"
    by auto
  from list_all2_trans[OF _ as_bs bs_cs, of "R OO S"] A_as C_cs
  show ?thesis by (auto simp: rel_mset_def)
qed

(* a variant for "right" *)
lemma ex_mset_zip_right:
  assumes "length xs = length ys" "mset ys' = mset ys"
  shows "\<exists>xs'. length ys' = length xs' \<and> mset (zip xs' ys') = mset (zip xs ys)"
using assms
proof (induct xs ys arbitrary: ys' rule: list_induct2)
  case Nil
  thus ?case
    by auto
next
  case (Cons x xs y ys ys')
  obtain j where j_len: "j < length ys'" and nth_j: "ys' ! j = y"
    by (metis Cons.prems in_set_conv_nth list.set_intros(1) mset_eq_setD)

  define ysa where "ysa = take j ys' @ drop (Suc j) ys'"
  have "mset ys' = {#y#} + mset ysa"
    unfolding ysa_def using j_len nth_j
    by (metis Cons_nth_drop_Suc union_mset_add_mset_right add_mset_remove_trivial add_diff_cancel_left'
        append_take_drop_id mset.simps(2) mset_append)
  hence ms_y: "mset ysa = mset ys"
    by (simp add: Cons.prems)
  then obtain xsa where
    len_a: "length ysa = length xsa" and ms_a: "mset (zip xsa ysa) = mset (zip xs ys)"
    using Cons.hyps(2) by blast

  define xs' where "xs' = take j xsa @ x # drop j xsa"
  have ys': "ys' = take j ysa @ y # drop j ysa"
    using ms_y j_len nth_j Cons.prems ysa_def
    by (metis append_eq_append_conv append_take_drop_id diff_Suc_Suc Cons_nth_drop_Suc length_Cons
      length_drop size_mset)
  have j_len': "j \<le> length ysa"
    using j_len ys' ysa_def
    by (metis add_Suc_right append_take_drop_id length_Cons length_append less_eq_Suc_le not_less)
  have "length ys' = length xs'"
    unfolding xs'_def using Cons.prems len_a ms_y
    by (metis add_Suc_right append_take_drop_id length_Cons length_append mset_eq_length)
  moreover have "mset (zip xs' ys') = mset (zip (x # xs) (y # ys))"
    unfolding ys' xs'_def
    apply (rule HOL.trans[OF mset_zip_take_Cons_drop_twice])
    using j_len' by (auto simp: len_a ms_a)
  ultimately show ?case
    by blast
qed

lemma list_all2_reorder_right_invariance:
  assumes rel: "list_all2 R xs ys" and ms_y: "mset ys' = mset ys"
  shows "\<exists>xs'. list_all2 R xs' ys' \<and> mset xs' = mset xs"
proof -
  have len: "length xs = length ys"
    using rel list_all2_conv_all_nth by auto
  obtain xs' where
    len': "length xs' = length ys'" and ms_xy: "mset (zip xs' ys') = mset (zip xs ys)"
    using len ms_y by (metis ex_mset_zip_right)
  have "list_all2 R xs' ys'"
    using assms(1) len' ms_xy unfolding list_all2_iff by (blast dest: mset_eq_setD)
  moreover have "mset xs' = mset xs"
    using len len' ms_xy map_fst_zip mset_map by metis
  ultimately show ?thesis
    by blast
qed

lemma rel_mset_via_perm: "rel_mset rel (mset xs) (mset ys) \<longleftrightarrow> (\<exists>zs. mset xs = mset zs \<and> list_all2 rel zs ys)"
proof (unfold rel_mset_def, intro iffI, goal_cases)
  case 1
  then obtain zs ws where zs: "mset zs = mset xs" and ws: "mset ws = mset ys" and zsws: "list_all2 rel zs ws" by auto
  note list_all2_reorder_right_invariance[OF zsws ws[symmetric], unfolded zs]
  then show ?case by (auto dest: sym)
next
  case 2
  from this show ?case by force
qed

end
