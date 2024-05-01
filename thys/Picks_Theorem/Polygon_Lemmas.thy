theory Polygon_Lemmas
imports
  Polygon_Jordan_Curve
  "HOL-Library.Sublist"
  HOL.Set_Interval
  HOL.Fun

begin

section "Properties of make polygonal path, pathstart and pathfinish of a polygon"

(* Induction rule for make_polygonal_path *)
lemma make_polygonal_path_induct[case_names Empty Single Two Multiple]:
  fixes ell :: "(real^2) list"
  assumes empty: "\<And>ell. ell = [] \<Longrightarrow> P ell"
    and single: "\<And>ell.  \<lbrakk>length ell = 1\<rbrakk>  \<Longrightarrow> P ell"
    and two: "\<And>ell. \<lbrakk>length ell = 2\<rbrakk> \<Longrightarrow> P ell"
    and multiple: "\<And>ell. 
        \<lbrakk>length ell > 2;
        P ([(ell!0), (ell!1)]);
        P ((ell!1)#(drop 2 ell))\<rbrakk> \<Longrightarrow> P ell"
  shows "P ell"
  apply(induct ell rule: make_polygonal_path.induct)
  using empty single two multiple by auto

lemma make_polygonal_path_gives_path:
  fixes v :: "(real^2) list"
  shows "path (make_polygonal_path v)"
proof(induction "length v" arbitrary: v)
  case 0
  thus "path (make_polygonal_path v)"
    by auto
next
  case (Suc x)
  show ?case
    by (smt (verit, best) Suc.hyps(1) Suc.hyps(2) Suc_length_conv list.distinct(1) list.inject make_polygonal_path.elims path_join_imp path_linepath pathfinish_linepath pathstart_join pathstart_linepath)
qed

corollary polygonal_path_is_path:
  fixes g :: "R_to_R2"
  assumes "polygonal_path g"
  shows "path g"
  using assms polygonal_path_def make_polygonal_path_gives_path by auto


lemma polygon_to_polygonal_path:
  fixes p :: "R_to_R2"
  assumes "polygon p"
  obtains ell where "p =  make_polygonal_path ell"
  using assms unfolding polygon_def polygonal_path_def 
  by auto 

lemma polygon_pathstart: 
  fixes g :: "R_to_R2"
  assumes "l \<noteq> []"
  assumes "g = make_polygonal_path l"
  shows "pathstart g = l!0"
  using assms make_polygonal_path.simps
  by (smt (verit) list.discI list.expand make_polygonal_path.elims nth_Cons_0 pathstart_join pathstart_linepath)

lemma polygon_pathfinish: 
  fixes g :: "R_to_R2"
  assumes "l \<noteq> []"
  assumes "g = make_polygonal_path l"
  shows "pathfinish g = l!(length l - 1)"
  using assms
proof (induct "length l"  arbitrary: g l)
  case 0
  then show ?case by auto
next
  case (Suc x)
  {assume *: "length l = 1"
    then obtain a where l_is: "l = [a]" 
      by (metis Suc.prems(1) Suc_neq_Zero diff_Suc_1 diff_self_eq_0 length_Cons remdups_adj.cases)
    then have "pathfinish g = a"
      using Suc make_polygonal_path.simps
      by (simp add: pathfinish_def) 
    then have "pathfinish g = l!(length l - 1)"
      using Suc l_is
      by auto 
   } moreover {assume *: "length l = 2"
     then obtain a b where l_is: "l = [a, b]"
       by (metis (no_types, opaque_lifting) One_nat_def Suc_eq_plus1 list.size(3) list.size(4) min_list.cases nat.simps(1) nat.simps(3) numeral_2_eq_2)
     then have g_is: "g = linepath a b"
       using Suc by auto
     have pf: "pathfinish g = b" using g_is by auto
     then have "pathfinish g = l!(length l - 1)"
       using Suc * l_is
       by auto
    }
    moreover {assume *: "length l > 2"
      then obtain a b c where l_is: "l = a # b # c"
        by (metis Suc.prems(1) Zero_neq_Suc length_Cons less_Suc0 list.size(3) numeral_2_eq_2 remdups_adj.cases)
      then have g_is: "g = (linepath a b) +++ make_polygonal_path (b # c)"
        using Suc l_is 
      proof -
        have "c \<noteq> []"
          using "*" l_is by auto
        then show ?thesis
          by (metis (full_types) Suc(4) l_is list.exhaust make_polygonal_path.simps(4))
      qed
      then have pf: "pathfinish g = pathfinish (make_polygonal_path (b # c))"
        by auto
      have len_x: "length (b # c) = x"
        using l_is Suc by auto 
      then have "pathfinish (make_polygonal_path (b # c)) = (b # c)!(length l - 2)"
        using Suc.hyps l_is 
        by simp
      then have "pathfinish g = l!(length l - 1)"
        using l_is pf 
        by auto
   }
   ultimately show ?case 
     using Suc 
     by (metis One_nat_def less_Suc_eq_0_disj less_antisym numeral_2_eq_2)
 qed

lemma make_polygonal_path_image_property:
  assumes "length vts \<ge> 2"
  assumes p_is_path: "x \<in> path_image (make_polygonal_path vts)"
  shows "\<exists> k < length vts - 1. x \<in> path_image (linepath (vts ! k) (vts ! (k + 1)))"
  using assms
proof (induct vts)
  case Nil
  then show ?case by auto
next
  case (Cons a vts)
  then have len_gteq: "length vts \<ge> 1"
    by simp
  {assume *: "length vts = 1"
    then obtain b where vts_is: "vts = [b]"
      by (metis One_nat_def \<open>1 \<le> length vts\<close> drop_eq_Nil id_take_nth_drop less_numeral_extra(1) self_append_conv2 take_eq_Nil2)
    then have "x \<in> path_image (make_polygonal_path [a, b])"
      using Cons by auto
    then have "x \<in> path_image (linepath a b)"
      by auto
    then have "x \<in> path_image (linepath ((a#vts) ! 0) ((a#vts) ! 1))"
      using Cons vts_is 
      by force
    then have "\<exists>k<length (a # vts) - 1. x \<in> path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1)))"
      using * 
      by simp
  } moreover {assume *: "length vts > 1"
    then obtain b vts' where vts_is: "vts = b # vts'"
      by (metis One_nat_def le_zero_eq len_gteq list.exhaust list.size(3) n_not_Suc_n)
    then have "x \<in> path_image ((linepath a b) +++ make_polygonal_path (b # vts'))"
      using Cons
      by (metis (no_types, lifting) "*" One_nat_def length_Cons list.exhaust list.size(3) make_polygonal_path.simps(4) nat_less_le)
    then have eo: "x \<in>path_image ((linepath a b)) \<or> x \<in> path_image (make_polygonal_path (b # vts'))"
      using not_in_path_image_join by blast
    {assume ** : "x \<in>path_image ((linepath a b))"
    then have "\<exists>k<length (a # vts) - 1. x \<in> path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1)))"
      using vts_is 
      by auto
  } moreover {assume ** : "x \<in> path_image (make_polygonal_path (b # vts'))"
    then have "\<exists>k<length vts - 1. x \<in> path_image (linepath (vts ! k) (vts ! (k + 1)))"
      using Cons.hyps(1) * 
      by (simp add: Suc_leI vts_is)
    then have "\<exists>k<length (a # vts) - 1. x \<in> path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1)))"

      using add.commute add_diff_cancel_left' length_Cons less_diff_conv nth_Cons_Suc plus_1_eq_Suc by auto
  }
    ultimately have "\<exists>k<length (a # vts) - 1. x \<in> path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1)))"
      using eo by auto
  }
  ultimately show ?case
    using len_gteq 
    by fastforce
qed

lemma linepaths_subset_make_polygonal_path_image:
  assumes "length vts \<ge> 2"
  assumes "k < length vts - 1"
  shows "path_image (linepath (vts ! k) (vts ! (k + 1))) \<subseteq> path_image (make_polygonal_path vts)"
  using assms
proof (induct vts arbitrary: k)
  case Nil
  then show ?case by auto 
next
  case (Cons a vts)
  { assume *: "length vts = 1"
    then have k_is: "k = 0"
      using Cons.prems(2) by auto
    obtain b where vts_is: "vts = [b]"
      using * 
      by (metis One_nat_def drop_eq_Nil id_take_nth_drop le_numeral_extra(4) self_append_conv2 take_eq_Nil2 zero_less_one)
    then have "path_image (make_polygonal_path (a # vts)) = path_image (linepath a b)"
      by auto
    then have "path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1)))
     \<subseteq> path_image (make_polygonal_path (a # vts))"
      using k_is vts_is 
      by simp
  } moreover
  { assume *: "length vts > 1" 
    then obtain b c vts' where vts_is: "vts = b#c#vts'" 
      by (metis diff_0_eq_0 diff_Suc_1 diff_is_0_eq leD length_Cons list.exhaust list.size(3))
    { assume **: "k = 0"
      then have same_path_image: "path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1))) = path_image (linepath a b)"
        using vts_is 
        by auto
      have "path_image (linepath a b) \<subseteq> path_image (make_polygonal_path (a # b #c#vts'))"
        using vts_is make_polygonal_path.simps path_image_join  
        by (metis (no_types, lifting) Un_iff list.discI nth_Cons_0 pathfinish_linepath polygon_pathstart subsetI) 
      then have "path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1))) \<subseteq> path_image (make_polygonal_path (a # vts))"
      using vts_is same_path_image 
      by presburger
  } moreover {assume **: "k > 0"
    then have k_minus_lt: "k-1 < length vts - 1"
      using Cons
      by auto
    then have path_image_is: "path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1))) = path_image (linepath (vts ! (k -1)) (vts ! k))"
      using ** 
      by auto
    then have path_im_subset1: "path_image (linepath (vts ! (k-1)) (vts ! k)) \<subseteq> path_image (make_polygonal_path vts)"
      using k_minus_lt Cons.hyps(1)[of "k-1"] * ** Suc_leI Suc_pred add.right_neutral add_Suc_right nat_1_add_1 plus_1_eq_Suc 
      by auto
    have path_im_subset2: "path_image (make_polygonal_path vts) \<subseteq> path_image (make_polygonal_path (a # vts))"
      using vts_is make_polygonal_path.simps(4) 
      by (metis dual_order.refl list.distinct(1) nth_Cons_0 path_image_join pathfinish_linepath polygon_pathstart sup.coboundedI2)
    then have "path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1))) \<subseteq> path_image (make_polygonal_path (a # vts))" 
      using path_image_is path_im_subset1 path_im_subset2
      by blast
      }
      ultimately have "path_image (linepath ((a # vts) ! k) ((a # vts) ! (k + 1))) \<subseteq> path_image (make_polygonal_path (a # vts))"
        by blast
  }
  ultimately show ?case 
    by (metis Cons.prems(1) Suc_1 leD length_Cons linorder_neqE_nat nat_add_left_cancel_less plus_1_eq_Suc)
qed

lemma vertices_on_path_image: shows "set vts \<subseteq> path_image (make_polygonal_path vts)"
proof (induct vts rule:make_polygonal_path.induct)
  case 1
  then show ?case by auto
next
  case (2 a)
  then show ?case by auto
next
  case (3 a b)
  then show ?case by auto
next
  case (4 a b v va)
  then have a_in_image: "a \<in> path_image (make_polygonal_path (a # b # v # va))"
    using make_polygonal_path.simps
    by (metis list.distinct(1) nth_Cons_0 pathstart_in_path_image polygon_pathstart) 
  have path_image_union:
    "path_image (make_polygonal_path (a # b # v # va))
      = path_image (linepath a b) \<union> path_image (make_polygonal_path (b # v # va))"
    by (metis make_polygonal_path.simps(4) linepath_1' list.discI nth_Cons_0 path_image_join pathfinish_def polygon_pathstart)
  have "set (a # b # v # va) = {a} \<union> set( b # v # va)"
    by auto
  then show ?case using a_in_image 4 make_polygonal_path.simps
    path_image_union by auto 
qed

lemma path_image_cons_union:
  assumes "p = make_polygonal_path vts"
  assumes "p' = make_polygonal_path vts'"
  assumes "vts' \<noteq> []"
  assumes "vts = a # vts' \<and> b = vts'!0"
  shows "path_image p = path_image (linepath a b) \<union> path_image p'"
proof-
  have "pathfinish (linepath a b) = pathstart p'" using assms polygon_pathstart by auto
  moreover have "length vts = 2 \<Longrightarrow> ?thesis"
    by (smt (verit) Cons_nth_drop_Suc One_nat_def Suc_1 assms(1) assms(2) assms(3) assms(4) closed_segment_idem diff_Suc_1 drop0 drop_eq_Nil insert_subset le_iff_sup le_numeral_extra(4) length_Cons length_greater_0_conv list.discI list.inject list.set(1) list.set(2) make_polygonal_path.elims path_image_linepath sup_commute vertices_on_path_image)
  moreover have "length vts > 2 \<Longrightarrow> ?thesis"
    by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_1 assms(1) assms(2) assms(3) assms(4) calculation(1) drop0 drop_Suc_Cons length_greater_0_conv make_polygonal_path.simps(4) path_image_join)
  moreover have "length vts \<ge> 2" using assms by (simp add: Suc_le_eq) 
  ultimately show ?thesis by linarith
qed

lemma polygonal_path_image_linepath_union:
  assumes "p = make_polygonal_path vts"
  assumes "n = length vts"
  assumes "n \<ge> 2"
  shows "path_image p = (\<Union> {path_image (linepath (vts!i) (vts!(i+1))) | i. i \<le> n - 2})"
  using assms
proof(induct n arbitrary: vts p)
  case 0
  then show ?case by linarith
next
  case (Suc n)
  { assume *: "Suc n = 2"
    then obtain a b where ab: "vts = [a, b]" 
      by (metis Suc.prems(2-3) Cons_nth_drop_Suc One_nat_def Suc_1 drop0 drop_eq_Nil lessI pos2)
    then have "path_image p = path_image (linepath a b)"
      using make_polygonal_path.simps Suc.prems by presburger
    moreover have "... = (\<Union> {path_image (linepath (vts!i) (vts!(i+1))) | i. i \<le> Suc n - 2})"
      using ab Suc.prems
      by (smt (verit, ccfv_threshold) Suc_eq_plus1 Sup_least Sup_upper * diff_is_0_eq diff_zero dual_order.refl mem_Collect_eq nth_Cons_0 nth_Cons_Suc subset_antisym)
    ultimately have ?case by presburger
  } moreover
  { assume *: "Suc n > 2"
    then obtain a b vts' where vts': "vts = a # vts' \<and> b = vts'!0 \<and> vts' = tl vts"
      by (metis Suc.prems(2) list.collapse list.size(3) nat.distinct(1))

    let ?p' = "make_polygonal_path vts'"
    let ?P' = "path_image ?p'"
    let ?P = "path_image p"
    let ?P_union = "(\<Union> {path_image (linepath (vts!i) (vts!(i+1))) | i. i \<le> n - 1})"

    have vts'_len: "length vts' = n" using vts' Suc.prems by fastforce
    then have "?P' = (\<Union> {path_image (linepath (vts'!i) (vts'!(i+1))) | i. i \<le> n - 2})"
      using Suc.prems Suc.hyps * by force
    moreover have "\<forall>i \<le> n-2. vts'!i = vts!(i+1) \<and> vts'!(i+1) = vts!(i+2)" using vts' by force
    ultimately have "?P' = (\<Union> {path_image (linepath (vts!(i+1)) (vts!(i+2))) | i. i \<le> n - 2})"
      by fastforce
    moreover have "... = (\<Union> {path_image (linepath (vts!i) (vts!(i+1))) | i. 1 \<le> i \<and> i \<le> n - 1})"
        (is "... = ?P'_union")
    proof- (* subgoals generated from applying auto *)
      have "\<And>x i. x \<in> {vts ! Suc i--vts ! Suc (Suc i)}
          \<Longrightarrow> i \<le> n - 2
          \<Longrightarrow> \<exists>xa. (\<exists>i. xa = {vts ! i--vts ! Suc i} \<and> Suc 0 \<le> i \<and> i \<le> n - Suc 0) \<and> x \<in> xa"
        by (metis "*" One_nat_def Suc_diff_Suc Suc_le_mono add_2_eq_Suc' bot_nat_0.extremum diff_Suc_Suc le_add_diff_inverse plus_1_eq_Suc)
      moreover have "\<And>x i. x \<in> {vts ! i--vts ! Suc i}
          \<Longrightarrow> Suc 0 \<le> i
          \<Longrightarrow> i \<le> n - Suc 0
          \<Longrightarrow> \<exists>xa. (\<exists>i. xa = {vts ! Suc i--vts ! Suc (Suc i)} \<and> i \<le> n - 2) \<and> x \<in> xa"
        by (metis "*" Suc_diff_Suc gr0_implies_Suc linorder_not_le not_less_eq_eq numeral_2_eq_2)
      ultimately show ?thesis by auto
    qed
    moreover have "path_image (linepath a b) \<union> ?P'_union = ?P_union"
    proof- (* subgoals generated from applying auto *)
      have "\<And>x. x \<in> {a--b} \<Longrightarrow> \<exists>xa. (\<exists>i. xa = {vts ! i--vts ! Suc i} \<and> i \<le> n - Suc 0) \<and> x \<in> xa"
        using vts' by fastforce
      moreover have "\<And>x i. x \<in> {vts ! i--vts ! Suc i}
          \<Longrightarrow> \<forall>xa. (\<forall>i\<ge>Suc 0. xa = {vts ! i--vts ! Suc i} \<longrightarrow> \<not> i \<le> n - Suc 0) \<or> x \<notin> xa
          \<Longrightarrow> i \<le> n - Suc 0
          \<Longrightarrow> x \<in> {a--b}"
        by (metis Suc_le_eq bot_nat_0.not_eq_extremum nth_Cons_0 nth_Cons_Suc vts')
      ultimately show ?thesis by auto
    qed
    moreover have "?P = (path_image (linepath a b)) \<union> ?P'"
      using Suc.prems vts' path_image_cons_union
      by (metis One_nat_def Suc_1 vts'_len bot_nat_0.extremum list.size(3) not_less_eq_eq)
    ultimately have ?case by force
  }
  ultimately show ?case using Suc.prems by linarith
qed

section "Loop Free Properties"

lemma constant_linepath_is_not_loop_free:
  shows "\<not>(loop_free ((linepath a a)::real \<Rightarrow> real^2))"
 proof - 
   have all_zero1: "\<And>x y::real. (1 - x) *\<^sub>R (a::real^2) + x *\<^sub>R a = a"
     by auto
   have all_zero2: "\<And>x y::real. (1 - y) *\<^sub>R (a::real^2) + y *\<^sub>R a = a"
     by auto  
   then have "\<exists>x::real\<in>{0..1}. \<exists>y::real\<in>{0..1}. x \<noteq> y \<and> (x = 0 \<longrightarrow> y \<noteq> 1) \<and> (x = 1 \<longrightarrow> y \<noteq> 0)"
     by (metis atLeastAtMost_iff field_lbound_gt_zero less_eq_real_def linorder_not_less zero_less_one)
 then show ?thesis
   unfolding loop_free_def linepath_def
   using all_zero1 all_zero2 by auto
qed

lemma doubling_back_is_not_loop_free:
  assumes "a \<noteq> b"
  shows "\<not>(loop_free ((make_polygonal_path [a, b, a])::real \<Rightarrow> real^2))"
proof - 
  let ?p1 = "(1/4::real)"
  let ?p2 = "(3/4::real)"
  have same_point: "((linepath a b) +++ (linepath b a)) (1/4::real) = ((linepath a b) +++ (linepath b a)) (3/4::real)"
    unfolding linepath_def joinpaths_def by auto 
  have "?p1 \<in> {0..1} \<and> ?p2 \<in> {0..1} \<and> ?p1 \<noteq> ?p2 \<and> (?p1 = 0 \<longrightarrow> ?p2 \<noteq> 1) \<and> (?p1 = 1 \<longrightarrow> ?p2 \<noteq> 0)"
    by auto
  then have "\<exists>x\<in>{0..1}. \<exists>y\<in>{0..1}.
        (linepath a b +++ linepath b a) x = (linepath a b +++ linepath b a) y
        \<and> x \<noteq> y \<and> (x = 0 \<longrightarrow> y \<noteq> 1) \<and> (x = 1 \<longrightarrow> y \<noteq> 0)"
    using same_point by blast
  then have "\<not>(loop_free ((linepath a b) +++ (linepath b a)))"
    unfolding loop_free_def by auto
  then show ?thesis using make_polygonal_path.simps
    by auto 
qed

lemma not_loop_free_first_component:
  assumes "\<not>(loop_free p1)"
  shows "\<not>(loop_free (p1+++p2))"
proof -
  obtain x y where xy_prop: "0 \<le> x" "x\<le> 1" "0 \<le> y" "y\<le> 1" "x \<noteq> y"
      "(x = 0 \<longrightarrow> y \<noteq> 1)" "(x = 1 \<longrightarrow> y \<noteq> 0)"
     "p1 x = p1 y"
    using assms unfolding loop_free_def 
    by auto
  then have xy_prop2: "0 \<le> x/2" "x/2\<le> 1/2" "0 \<le> y/2" "y/2\<le> 1/2" "x/2 \<noteq> y/2"
    by auto
  then have "(p1+++p2) (x/2) = (p1+++p2) (y/2)"
    unfolding joinpaths_def using xy_prop(8)
    by auto
  then have props: "(p1 +++ p2) (x/2) = (p1 +++ p2) (y/2) \<and>
          (x/2) \<noteq> (y/2) \<and> ((x/2) = 0 \<longrightarrow> (y/2) \<noteq> 1) \<and> ((x/2) = 1 \<longrightarrow> (y/2) \<noteq> 0)"
    using xy_prop2 by auto 
  have "x/2 \<in> {0..1} \<and> y/2 \<in> {0..1}"
    using xy_prop2 by auto 
  then have "\<exists>x\<in>{0..1}.
       \<exists>y\<in>{0..1}.
          (p1 +++ p2) x = (p1 +++ p2) y \<and>
          x \<noteq> y \<and> (x = 0 \<longrightarrow> y \<noteq> 1) \<and> (x = 1 \<longrightarrow> y \<noteq> 0)"
    using props 
    by blast
  then show ?thesis
    unfolding loop_free_def by auto
qed

lemma not_loop_free_second_component:
  assumes pathfinish_pathstart: "pathfinish p1 = pathstart p2"
  assumes "\<not>(loop_free p2)"
  shows "\<not>(loop_free (p1+++p2))"
proof -
  obtain x y where xy_prop: "0 \<le> x" "x\<le> 1" "0 \<le> y" "y\<le> 1" "x \<noteq> y"
      "(x = 0 \<longrightarrow> y \<noteq> 1)" "(x = 1 \<longrightarrow> y \<noteq> 0)"
     "p2 x = p2 y"
    using assms unfolding loop_free_def 
    by auto
  then have xy_prop2: "(x + 1)/2 \<ge> 1/2" "(x + 1)/2 \<le> 1" "(y + 1)/2 \<ge> 1/2" "(y + 1)/2 \<le> 1"
  "(x + 1)/2 \<noteq> (y + 1)/2" 
    by auto
  have x_same: "2*((x + 1)/2) - 1 = x"
    by (metis add.right_neutral add_diff_eq cancel_comm_monoid_add_class.diff_cancel class_dense_linordered_field.between_same mult_1 mult_2 times_divide_eq_left times_divide_eq_right)
  have y_same: "2*((y + 1)/2) - 1 = y"
    by (metis add.right_neutral add_diff_eq cancel_comm_monoid_add_class.diff_cancel class_dense_linordered_field.between_same mult_1 mult_2 times_divide_eq_left times_divide_eq_right)
  have "p2 (2*((x + 1)/2) - 1) = p2 (2*((y + 1)/2) -1 )" 
    using xy_prop(8) x_same y_same
    by auto
  have relate_start_finish: "p1 1 = p2 0"
    using pathfinish_pathstart 
    unfolding pathfinish_def pathstart_def
    by auto 
  then have xh1: "(x + 1)/2 = 1/2 \<Longrightarrow> (p1 +++ p2) ((x + 1)/2) = p2 x"
    unfolding joinpaths_def 
    by auto
  have xh2: "(x + 1)/2 > 1/2 \<Longrightarrow> (p1 +++ p2) ((x + 1)/2) = p2 x"
    using xy_prop2 unfolding joinpaths_def
    using x_same by force 
  then have xh: "(p1 +++ p2) ((x + 1)/2) = p2 x"
    using xh1 xh2 xy_prop2
    by linarith 
  have yh1: "(y + 1)/2 = 1/2 \<Longrightarrow> (p1 +++ p2) ((y + 1)/2) = p2 y"
    using relate_start_finish unfolding joinpaths_def 
    by auto
  have yh2: "(y + 1)/2 > 1/2 \<Longrightarrow> (p1 +++ p2) ((y + 1)/2) = p2 y"
    using xy_prop2 unfolding joinpaths_def
    using y_same by force 
  then have yh: "(p1 +++ p2) ((y + 1)/2) = p2 y"
    using yh1 yh2 xy_prop2
    by linarith 
  then have same_eval: "(p1+++p2) ((x + 1)/2)  = (p1+++p2) ((y + 1)/2)"
    using xh yh xy_prop(8) 
    by presburger 
  have inset1: "(x + 1)/2 \<in> {0..1}"
    using xy_prop2
    by simp
  have inset2: "(y + 1)/2 \<in> {0..1}"
    using xy_prop2 
    by simp
   have "\<exists>x\<in>{0..1}.
       \<exists>y\<in>{0..1}.
          (p1 +++ p2) x = (p1 +++ p2) y \<and>
          x \<noteq> y \<and> (x = 0 \<longrightarrow> y \<noteq> 1) \<and> (x = 1 \<longrightarrow> y \<noteq> 0)"
    using xy_prop2 same_eval inset1 inset2 
    by fastforce
  then show ?thesis
    unfolding loop_free_def by auto
qed

lemma loop_free_subpath: 
  assumes "path p"
  assumes u_and_v: "u \<in> {0..1}" "v \<in> {0..1}" "u < v"
  assumes "\<not> (loop_free (subpath u v p))" 
  shows "\<not> (loop_free p)"
proof -
  have "path (subpath u v p)"
    using path_subpath assms by auto 
  then show ?thesis using simple_path_subpath assms
    unfolding simple_path_def
    by blast 
qed

lemma loop_free_associative: 
  assumes "path p"
  assumes "path q"
  assumes "path r"
  assumes "pathfinish p = pathstart q"
  assumes "pathfinish q = pathstart r"
  shows "\<not> (loop_free ((p +++ q) +++ r)) \<longleftrightarrow> \<not> (loop_free (p +++ (q +++ r)))"
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) assms(5) path_join_imp pathfinish_join pathstart_join simple_path_assoc simple_path_def) 

lemma polygon_at_least_3_vertices:
  assumes "polygon p" and
          "p = make_polygonal_path vts"
        shows "card (set vts) \<ge> 3"
  using assms
proof (induct vts rule: make_polygonal_path.induct)
  case 1
  then show ?case unfolding polygon_def 
    using constant_linepath_is_not_loop_free make_polygonal_path.simps(1)
    by (metis simple_path_def)
next
  case (2 a)
  then show ?case unfolding polygon_def 
    using constant_linepath_is_not_loop_free make_polygonal_path.simps(2)
    by (metis simple_path_def)
next
  case (3 a b)
  { assume *: "a = b"
    then have "False" using 3  unfolding polygon_def 
      using constant_linepath_is_not_loop_free make_polygonal_path.simps(3)
      by (metis simple_path_def)
  } moreover {assume *: "a \<noteq> b"
    then have "False" using 3  unfolding polygon_def closed_path_def 
      pathstart_def pathfinish_def using make_polygonal_path.simps(3)
      by (simp add: linepath_0' linepath_1')
  }
  ultimately show ?case
    by auto
next
  case (4 a b v va)
  have finset: "finite (set (a # b # v # va))"
    by blast
  have subset: "{a, b, v} \<subseteq> set (a # b # v # va)"
    by auto
  have neq1: "a \<noteq> b"
    using constant_linepath_is_not_loop_free not_loop_free_first_component
    by (metis "4.prems"(2) make_polygonal_path.simps(4) polygon_def assms(1) simple_path_def) 
  have loop_free_2: "loop_free (make_polygonal_path (b # v # va))"
    using 4 not_loop_free_second_component 
    by (metis make_polygonal_path.simps(4) polygon_def list.distinct(1) nth_Cons_0 pathfinish_linepath polygon_pathstart simple_path_def)
  have contra: "b = v \<Longrightarrow> \<not>(loop_free (make_polygonal_path (b # v # va)))"
    using constant_linepath_is_not_loop_free[of b] make_polygonal_path.simps
    not_loop_free_first_component 
    by (metis neq_Nil_conv)
  then have neq2: "b \<noteq> v"
    using loop_free_2 contra
    by auto 
  (* Requires showing the path can't "double back"; then it wouldn't be loop free  *)
  have " \<not> loop_free ((linepath a b) +++ (linepath  b a))"
    using doubling_back_is_not_loop_free[of a b]  neq1
    by auto
  have make_path_is: "make_polygonal_path (a # b # a # va) = (linepath a b) +++ ((linepath  b a) +++ (make_polygonal_path (a#va)))"
    using make_polygonal_path.simps 
    by (metis (no_types, opaque_lifting) "4.prems"(1) "4.prems"(2) closed_path_def polygon_def \<open>\<not> loop_free (linepath a b +++ linepath b a)\<close> linepath_1' min_list.cases nth_Cons_0 pathfinish_def pathfinish_join polygon_pathstart simple_path_def)
  have "\<not> loop_free (((linepath a b) +++ (linepath  b a)) +++ (make_polygonal_path (a#va)))"
    using make_polygonal_path.simps not_loop_free_first_component
    using \<open>\<not> loop_free (linepath a b +++ linepath b a)\<close> 
    by auto
  then have "\<not> loop_free (make_polygonal_path (a # b # a # va))"
    using loop_free_associative
    by (metis make_polygonal_path_gives_path list.discI make_path_is nth_Cons_0 path_linepath pathfinish_linepath pathstart_linepath polygon_pathstart) 
  then have neq3: "v \<noteq> a"
    using 4 
    using polygon_def simple_path_def by blast
  have card_3: "card {a, b, v} = 3"
    using neq1 neq2 neq3
    by auto
  then show ?case 
    using subset finset
    by (metis card_mono)
qed

lemma polygon_vertices_length_at_least_4:
  assumes "polygon p" and
          "p = make_polygonal_path vts"
        shows "length vts \<ge> 4"
proof - 
  have card_set: "card (set vts) \<ge> 3"
    using polygon_at_least_3_vertices assms 
    by blast
  have len_gt3: "length vts \<ge> 3"
    using card_length local.card_set order_trans by blast
  then have non_empty: "vts \<noteq> []"
    using card_set
    by auto
  have eq: "p 0 = p 1"
    using assms unfolding polygon_def closed_path_def pathstart_def pathfinish_def by auto
  have p0: "p 0 = vts ! 0"
    using polygon_pathstart[OF non_empty] using assms unfolding pathstart_def
    by auto
  have p1: "p 1 = vts ! (length vts - 1)"
    using polygon_pathfinish[OF non_empty] using assms unfolding pathfinish_def
    by auto
  have "vts ! 0 = vts ! (length vts -1)"
    using assms unfolding polygon_def 
    using p0 p1 eq by auto
  then have "set vts = set (drop 1 vts)"
    using len_gt3 
    by (smt (verit, best) Cons_nth_drop_Suc Suc_eq_plus1 Suc_le_eq add.commute add_0 add_leD2 drop0 dual_order.refl insert_subset last.simps last_conv_nth last_in_set list.distinct(1) list.set(2) numeral_3_eq_3 order_antisym_conv)
  then have "length (drop 1 vts) \<ge> 3"
    using card_set 
    by (metis dual_order.trans length_remdups_card_conv length_remdups_leq)
  then show ?thesis
  using card_set 
  by (metis One_nat_def Suc_1 Suc_eq_plus1 Suc_pred add_Suc_right length_drop length_greater_0_conv non_empty not_less_eq_eq numeral_3_eq_3 numeral_Bit0)
qed

lemma linepath_loop_free: 
  assumes "a \<noteq> b"
  shows "loop_free (linepath a b)"
  unfolding loop_free_def linepath_def 
  by (smt (z3) add.assoc add.commute add_scaleR_degen assms diff_add_cancel scaleR_left_diff_distrib)


section "Explicit Linepath Characterization of Polygonal Paths"

lemma triangle_linepath_images:
  fixes x :: real
  assumes "vts = [a, b, c]"
  assumes "p = make_polygonal_path vts"
  shows "x \<in> {0..1/2} \<Longrightarrow> p x = ((linepath a b)) (2*x)"
   "x \<in> {1/2..1} \<Longrightarrow> p x = ((linepath b c)) (2*x - 1)"
proof-
  fix x :: real
  assume "x \<in> {0..1/2}"
  thus "p x = ((linepath a b)) (2*x)"
    unfolding assms
    using make_polygonal_path.simps(4)[of a b c Nil] unfolding joinpaths_def by presburger
next
  fix x :: real
  assume *: "x \<in> {1/2..1}"
  { assume "x > 1/2"
    then have "p x = ((linepath b c)) (2*x - 1)"
      unfolding assms
      using make_polygonal_path.simps(4)[of a b c Nil] unfolding joinpaths_def by force
  } moreover
  { assume "x = 1/2"
    then have "p x = b \<and> ((linepath b c)) (2*x - 1) = b"
      unfolding assms
      using make_polygonal_path.simps(4)[of a b c Nil] unfolding joinpaths_def
      by (simp add: linepath_def mult.commute)
  }
  ultimately show "p x = ((linepath b c)) (2*x - 1)" using * by fastforce
qed

lemma polygon_linepath_images1:
  fixes n:: "nat"
  assumes "n \<ge> 3"
  assumes "length ell = n"
  assumes "x \<in> {0..1/2}"
  shows "make_polygonal_path ell x = ((linepath (ell ! 0) (ell ! 1))) (2*x)"
proof - 
  have "make_polygonal_path ell = linepath (ell ! 0) (ell ! 1) +++ make_polygonal_path (drop 1 ell)"
    using make_polygonal_path.simps
    by (smt (verit, del_insts) numeral_3_eq_3 Cons_nth_drop_Suc One_nat_def Suc_1 Suc_eq_plus1 add_Suc_right assms(1) assms(2) drop0 length_greater_0_conv less_add_Suc2 list.size(3) not_numeral_le_zero nth_Cons_0 numeral_Bit0 order_less_le_trans plus_1_eq_Suc)
  then show ?thesis
    using assms make_polygonal_path.simps
    by (simp add: joinpaths_def)
qed

(* copied from AFP entry Isabelle_Marries_Dirac.Basics *)
lemma sum_insert [simp]:
  assumes "x \<notin> F" and "finite F"
  shows "(\<Sum>y\<in>insert x F. P y) = (\<Sum>y\<in>F. P y) + P x"
  using assms insert_def by(simp add: add.commute)

(* copied from AFP entry Isabelle_Marries_Dirac.Basics *)
lemma sum_of_index_diff [simp]:
  fixes f:: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<in>{a..<a+b}. f(i-a)) = (\<Sum>i\<in>{..<b}. f(i))"
proof (induction b)
  case 0
  then show ?case by simp
next
  case (Suc b)
  then show ?case by simp
qed

lemma sum_of_index_diff2 [simp]:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<in>{a+c..b+c}. f(i)) = (\<Sum>i\<in>{a..b}. f(i+c))"
  using Set_Interval.comm_monoid_add_class.sum.shift_bounds_cl_nat_ivl by blast

lemma sum_split [simp]:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  assumes "c \<in> {a..b}"
  shows "(\<Sum>i \<in> {a..b}. f i) = (\<Sum>i \<in> {a..c}. f i) + (\<Sum>i \<in> {c+1..b}. f i)"
  by (metis Suc_eq_plus1 Suc_le_mono assms atLeastAtMost_iff atLeastLessThanSuc_atLeastAtMost le_SucI sum.atLeastLessThan_concat)

lemma summation_helper:
  fixes x :: real
  fixes k :: nat
  assumes "1 \<le> k"
  shows "(2::real) * (\<Sum>i = 1..k. 1 / 2 ^ i) - 1 = (\<Sum>i = 1..(k-1). (1 / (2^i)))"
proof-
  have frac_cancel: "\<forall>i::nat \<ge> 1. 2 / (2^i) = 2 / (2 * (2::real)^(i-1))"
    using power.simps(2)[of "2::real"] by (metis Suc_diff_le diff_Suc_1)
  have "(2::real) * (\<Sum>i = 1..k. 1 / 2^i) = (\<Sum>i = 1..k. (2 / 2^i))"
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>i = 1..k. (2 / (2 * 2^(i-1))))" using frac_cancel by simp
  also have "... = (\<Sum>i = 1..k. (1 / (2^(i-1))))" by force
  also have "... = (\<Sum>i = 1..<(k+1). (1 / (2^(i-1))))"
    using Suc_eq_plus1 atLeastLessThanSuc_atLeastAtMost by presburger
  also have "... = (\<Sum>i \<in> {..<k}. (1 / (2^i)))"
    using sum_of_index_diff[of "\<lambda>i. (1 / 2^i)" 1 k] by simp
  finally have "(2::real) * (\<Sum>i = 1..k. 1 / 2 ^ i) = (\<Sum>i = 0..(k-1). (1 / (2^i)))"
    by (metis assms atLeast0AtMost diff_Suc_1 lessThan_Suc_atMost nat_le_iff_add plus_1_eq_Suc)
  then have "(2::real) * (\<Sum>i = 1..k. 1 / 2 ^ i) - 1 = (\<Sum>i = 0..(k-1). (1 / (2^i))) - 1"
    by auto
  also have "... = (\<Sum>i = 1..(k-1). (1 / (2^i))) + (1/2^0) - 1"
    using sum_insert[of 0 "{1..k-1}" "power (1/2)"]
    by (simp add: Icc_eq_insert_lb_nat add.commute)
  also have "... = (\<Sum>i = 1..(k-1). (1 / (2^i)))" by force
  finally show "(2::real) * (\<Sum>i = 1..k. 1 / 2 ^ i) - 1 = (\<Sum>i = 1..(k-1). (1 / (2^i)))" .
qed

lemma polygon_linepath_images2:
  fixes n k:: "nat"
  fixes ell:: "(real^2) list"
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes "n \<ge> 3"
  assumes "0 \<le> k \<and> k \<le> n - 3"
  assumes "length ell = n"
  assumes p: "p = make_polygonal_path ell"
  assumes "f = (\<lambda>k x. (x - (\<Sum>i \<in> {1..k}. 1/(2^i))) * (2^(k+1)))"
  assumes "x \<in> {(\<Sum>i \<in> {1..k}. 1/(2^i))..(\<Sum>i \<in> {1..(k + 1)}. 1/(2^i))}"
  shows "p x = ((linepath (ell ! k) (ell ! (k+1)) (f k x)))"
  using assms
proof (induct n arbitrary: ell k x p)
  case 0
  then show ?case by auto
next
  case (Suc n)
  { assume *: "k = 0"
    have x: "x \<in> {0..1/2}" using * Suc.prems(6) by simp
    moreover have "f k x = 2*x" using * Suc.prems(5) by simp
    ultimately have ?case
      using polygon_linepath_images1[of "Suc n" ell x, OF Suc.prems(1) Suc.prems(3) x] *
      by (simp add: Suc.prems(4))
  } moreover
  { assume *: "k \<ge> 1"
    then have suc_n: "Suc n > 3" using Suc.prems(2) by linarith
    then have ell_is: "ell = (ell!0) # (ell!1) # (ell!2) # (drop 3 ell)"
      using Suc.prems(3) 
      by (metis Cons_nth_drop_Suc One_nat_def Suc_1 Suc_le_lessD drop0 nat_less_le numeral_3_eq_3)
    then have ell'_is: "drop 1 ell = (ell!1) # (ell!2) # (drop 3 ell)"
      by (metis One_nat_def diff_Suc_1 drop0 drop_Cons_numeral numerals(1))
    let ?ell' = "drop 1 ell"
    have len_ell': "length ?ell' > 2" using suc_n Suc.prems(3) by simp
    let ?p' = "make_polygonal_path ?ell'"
    have p_tl: "p = (linepath (ell ! 0) (ell ! 1)) +++ make_polygonal_path (drop 1 ell)"
      using Suc.prems(4) Suc.prems(3) *  make_polygonal_path.simps ell_is ell'_is 
      by metis
    (* TODO: Could simplify this proof *)
    have "(\<Sum>i = 1..k. 1 / (2 ^ i::real)) \<ge> (\<Sum>i = 1..1. 1 / (2 ^ i::real))"
      using Suc.prems(2) *
    proof (induct k)
      case 0
      then show ?case by auto
    next
      case (Suc k)
      { assume *: " 1 = Suc k"
        then have ?case by auto
      } moreover {assume *: " 1 < Suc k"
        then have "1 \<le> k \<and> k \<le> Suc n - 3"
          using Suc.prems by auto
        then have ind_h: "(\<Sum>i = 1..1. 1 / (2 ^ i::real)) \<le> (\<Sum>i = 1..k. 1 / 2 ^ i)"
          using Suc.hyps Suc.prems(2) by blast
        have "(\<Sum>i = 1..Suc k. 1 /( 2 ^ i::real)) = 1/(2^(Suc k)) + (\<Sum>i = 1..k. 1 / (2 ^ i::real))"
          using * by simp
        then have "(\<Sum>i = 1..Suc k. 1 /( 2 ^ i::real)) > (\<Sum>i = 1..k. 1 / (2 ^ i::real))"
          by simp
        then have ?case using ind_h by linarith
      } 
      ultimately show ?case by linarith
    qed
    then have "(\<Sum>i = 1..k. 1 / (2 ^ i::real)) \<ge> 1/2"
      by auto
    then have x_gteq: "x \<ge> 1/2" using Suc.prems(2,6) 
      by (meson atLeastAtMost_iff order_trans)
    have xonehalf: "p x = ?p' (2*x - 1)" if x_is: "x = 1/2" using p_tl joinpaths_def
    proof - 
      have "p x = (linepath (ell ! 0) (ell ! 1)) 1"
        using p_tl joinpaths_def x_is 
        by (metis mult.commute nle_le nonzero_divide_eq_eq zero_neq_numeral)
      then have "p x = ell ! 1"
        using polygon_pathfinish[of "[(ell ! 0), (ell ! 1)]"] unfolding pathfinish_def 
        using make_polygonal_path.simps by simp
      then have "p x = make_polygonal_path (drop 1 ell) 0"
        using polygon_pathstart[of "drop 1 ell"] * len_ell' unfolding pathstart_def
        by simp
      then show ?thesis using x_is by force
    qed
      have x_gtonehalf: "x > 1/2 \<Longrightarrow> p x = ?p' (2*x - 1)" using p_tl joinpaths_def
      by (smt (verit, ccfv_threshold))
    then have px: "p x = ?p' (2*x - 1)" using xonehalf x_gtonehalf x_gteq 
      by linarith
    { assume k_eq: "k = 1"
      then have "f k x = (x - (\<Sum>i = 1..1. 1 / 2 ^ i)) * 2 ^ 2"
        using Suc.prems(5) by auto
      then have fkx: "f k x =  4*x - 2"
        by auto
      have "x \<in> {1/2..3/4}"
        using k_eq Suc.prems(6) by auto
      then have "2*x - 1 \<in> {0..1/2}" by simp
      then have "?p' (2*x - 1) = (linepath (?ell'!0) (?ell'!1)) (4*x - 2)" 
        using Suc.hyps[of k ?ell' ?p' "2*x - 1"] Suc.prems 
        by (smt (verit, ccfv_SIG) suc_n diff_Suc_1 leD le_Suc_eq length_drop polygon_linepath_images1)
      also have "... = (linepath (ell!1) (ell!2)) (4*x - 2)" 
        using * Suc.prems(3) 
        using ell'_is by fastforce
      also have "... = ((linepath (ell ! k) (ell ! (k+1)) (f k x)))" using k_eq 
          Suc.prems(5) fkx 
        by (smt (verit, del_insts) nat_1_add_1)
      finally have ?case using px by simp
    } moreover
    { assume k_gt: "k > 1"
      then have fkminus: " f (k-1) (2 * x - 1) = ((2 * x - 1) - (\<Sum>i = 1..(k-1). 1 / 2 ^ i)) * 2 ^ k"
        using Suc.prems(5) by force
      have fk: "f k x = (x - (\<Sum>i = 1..k. 1 / 2 ^ i)) * 2 ^ (k + 1)"
        using Suc.prems(5) by blast
      have f_is: "f (k - 1) (2 * x - 1) = f k x"
      proof-
        have i: "\<forall>i::nat \<in> {2..k}. i - 2 + 2 = i"
          by auto
        have "f (k - 1) (2 * x - 1) = (2 * x - 1 - (\<Sum>i = 1..k - 1. 1 / 2 ^ i)) * 2 ^ (k - 1 + 1)"
          unfolding Suc.prems(5) by auto
        also have "... = (x - 1/2 - (\<Sum>i = 1..k - 1. 1 / 2^i) / 2) * 2 ^ (k + 1)"
          using k_gt by fastforce
        also have "... = (x - 1/2 - (\<Sum>i = 1..k - 1. (1 / 2^i) / 2)) * 2 ^ (k + 1)"
          by (simp add: sum_divide_distrib)
        also have "... = (x - 1/2 - (\<Sum>i = 1..k - 1. (1 / 2)^i * 1/2)) * 2 ^ (k + 1)" 
          by (simp add: power_divide)
        also have "... = (x - 1/2 - (\<Sum>i = 1..k - 1. (1 / 2)^(i+1))) * 2 ^ (k + 1)" by force
        also have "... = (x - 1/2 - (\<Sum>i = 1..<1 + (k - 1). (1 / 2)^(i+1))) * 2 ^ (k + 1)"
          using Suc_eq_plus1_left atLeastLessThanSuc_atLeastAtMost by presburger
        also have "... = (x - 1/2 - (\<Sum>i = 1..<1 + (k - 1). (1 / 2)^(i - 1 + 2))) * 2 ^ (k + 1)"
          by auto
        also have "... = (x - 1/2 - (\<Sum>i \<in> {..<k - 1}. ((1 / 2)^(i+2)))) * 2 ^ (k + 1)"
          using sum_of_index_diff[of "(\<lambda>x. (1/2)^(x+2))" 1 "k-1"] by metis
        also have "... = (x - 1/2 - (\<Sum>i \<in> {2..<k - 1 + 2}. ((1 / 2)^(i - 2 + 2)))) * 2 ^ (k + 1)"
          using sum_of_index_diff[of "(\<lambda>x. (1/2)^(x+2))" 2 "k-1"] by (smt (verit) add.commute)
        also have "... = (x - 1/2 - (\<Sum>i \<in> {2..k}. ((1 / 2)^(i - 2 + 2)))) * 2 ^ (k + 1)"
          using k_gt atLeastLessThanSuc_atLeastAtMost by force
        also have "... = (x - 1/2 - (\<Sum>i \<in> {2..k}. ((1 / 2)^(i)))) * 2 ^ (k + 1)" using i by force
        also have "... = (x - (1/2 + (\<Sum>i \<in> {2..k}. ((1 / 2)^(i))))) * 2 ^ (k + 1)" by argo
        also have "... = (x - (\<Sum>i = 1..k. (1 / 2)^(i))) * 2 ^ (k + 1)"
          using sum_insert[of 1 "{2..k}" "\<lambda>x. (1/2)^x"]
          by (smt (verit, ccfv_SIG) Suc_1 Suc_n_not_le_n atLeastAtMost_iff atLeastAtMost_insertL finite_atLeastAtMost k_gt less_imp_le_nat power_one_right)
        also have "... = (x - (\<Sum>i = 1..k. 1 / (2^i))) * 2 ^ (k + 1)" by (meson power_one_over)
        also have "... = f k x" using fk by argo
        finally show ?thesis .
      qed

      have ih1: "3 \<le> n" using suc_n by force
      have ih2: "0 \<le> k - 1 \<and> k - 1 \<le> n - 3" using k_gt Suc.prems(2) Suc.prems(3) by auto
      have ih3: "length ?ell' = n" using Suc.prems(3) by auto
      have ih4: "?p' = make_polygonal_path ?ell'" by blast

      have "2*x - 1 \<ge> (\<Sum>i \<in> {1..k-1}. 1/(2^i))"
      proof-
        have "(2::real) * (\<Sum>i = 1..k. 1 / 2 ^ i) - 1 = (\<Sum>i = 1..(k-1). (1 / (2^i)))"
          using summation_helper k_gt by auto 
        moreover have "x \<ge> (\<Sum>i = 1..k. 1 / 2 ^ i)" using Suc.prems(6) by presburger
        ultimately show "2*x - 1 \<ge> (\<Sum>i \<in> {1..k-1}. 1/(2^i))" by linarith
      qed
      moreover have "2*x - 1 \<le> (\<Sum>i \<in> {1..k}. 1/(2^i))"
      proof-
        have "(2::real) * (\<Sum>i \<in> {1..(k + 1)}. 1/(2^i)) - 1 = (\<Sum>i \<in> {1..k}. 1/(2^i))"
          using summation_helper[of "k + 1"] k_gt by auto
        moreover have "x \<le> (\<Sum>i \<in> {1..(k + 1)}. 1/(2^i))" using Suc.prems(6) by presburger
        ultimately show ?thesis by linarith
      qed
      ultimately have "2*x - 1 \<in> {(\<Sum>i \<in> {1..k-1}. 1/(2^i))..(\<Sum>i \<in> {1..k}. 1/(2^i))}" by presburger
      then have ih5: "2*x - 1 \<in> {(\<Sum>i \<in> {1..k-1}. 1/(2^i))..(\<Sum>i \<in> {1..k-1+1}. 1/(2^i))}" 
        using k_gt by auto

      have "p = make_polygonal_path (ell!0 # ell!1 # ell!2 # (drop 3 ell))"
        using ell_is Suc.prems(4) by argo
      then have "p = (linepath (ell!0) (ell!1)) +++ make_polygonal_path (ell!1 # ell!2 # (drop 3 ell))"
        using make_polygonal_path.simps by auto
      then have "p x = ?p' (2*x - 1)" unfolding joinpaths_def using x_gteq px by fastforce
      also have "... = (linepath (?ell'!(k-1)) (?ell'!k)) (f (k-1) (2*x - 1))"
        using Suc.hyps[OF ih1 ih2 ih3 ih4 Suc.prems(5), of "2*x - 1", OF ih5] using k_gt by auto
      also have "... = (linepath (ell!k) (ell!(k+1))) (f (k-1) (2*x - 1))" 
        using Suc.prems(2) Suc.prems(3) 
        by (smt (verit, del_insts) add_implies_diff ell'_is ell_is k_gt nth_Cons_pos order_le_less_trans trans_less_add1 zero_less_one_class.zero_le_one)
      also have "... = (linepath (ell!k) (ell!(k+1))) (f k x)"
        using f_is by auto
      finally have ?case .
    }
    ultimately have ?case using Suc.prems(2) * by linarith
  }
  ultimately show ?case 
    using Suc.prems by linarith
qed

lemma polygon_linepath_images3:
  fixes n k:: "nat"
  fixes ell:: "(real^2) list"
  assumes "n \<ge> 3"
  assumes "length ell = n" 
  assumes "p = make_polygonal_path ell"
  assumes "x \<in> {(\<Sum>i \<in> {1..n-2}. 1/(2^i))..1}"
  assumes "f = (\<lambda>x. (x - (\<Sum>i \<in> {1..n-2}. 1/(2^i))) * (2^(n-2)))"
  shows "p x = (linepath (ell ! (n-2)) (ell ! (n-1))) (f x)"
  using assms
proof (induct n arbitrary: ell k x p f)
  case 0
  then show ?case by auto
next
  case (Suc n)
  { assume *: "Suc n = 3"
    then have ell_is: "ell = [ell ! 0, ell ! 1, ell ! 2]"
      using Suc.prems(2) 
      by (metis Cons_nth_drop_Suc One_nat_def Suc_1 cancel_comm_monoid_add_class.diff_cancel drop0 length_0_conv length_drop lessI less_add_Suc2 numeral_3_eq_3 plus_1_eq_Suc zero_less_Suc)
    have "(\<Sum>i = 1..(Suc n)-2. 1 / ((2 ^ i)::real)) = (\<Sum>i\<in>{1}. 1 / ((2 ^ i)::real))"
      by (simp add: "*")
    then have eq1: "(\<Sum>i = 1..(Suc n)-2. 1 / ((2 ^ i)::real)) = 1/2"
      by auto
    then have f_is: " f = (\<lambda>x. (x - (1/2)) * 2)" using * Suc.prems(5) by auto
    have "x \<in> {(1/2)::real..1}" using eq1 Suc.prems(4) by metis
    moreover then have "p x = linepath (ell ! 1) (ell ! 2) (2 * x - 1)"
      using triangle_linepath_images(2) using ell_is Suc.prems(3) by blast
    moreover have "f x = 2*x - 1" using f_is by simp
    ultimately have "p x = (linepath (ell ! ((Suc n)-2)) (ell ! ((Suc n)-1))) (f x)"
      using * Suc.prems ell_is 
      by (metis One_nat_def Suc_1 diff_Suc_1 diff_Suc_Suc numeral_3_eq_3)
  } moreover
  { assume *: "Suc n > 3"
    let ?ell' = "drop 1 ell"
    let ?p' = "make_polygonal_path ?ell'"
    let ?x' = "2*x - 1"
    let ?f' = "(\<lambda>x. (x - (\<Sum>i \<in> {1..n-2}. 1/(2^i))) * (2^(n-2)))"
    have ell_is: "ell = ell!0 # ell!1 # ell!2 # (drop 3 ell)"
      by (metis * Cons_nth_drop_Suc One_nat_def Suc.prems(2) Suc_1 drop0 le_Suc_eq linorder_not_less numeral_3_eq_3 zero_less_Suc)
    then have p_tl: "p = (linepath (ell ! 0) (ell ! 1)) +++ make_polygonal_path (drop 1 ell)"
      using make_polygonal_path.simps(4)[of "ell!0" "ell!1" "ell!2" "drop 3 ell"]
      by (metis One_nat_def Suc.prems(3) drop_0 drop_Suc_Cons)
    have sum_split: "(\<Sum>i = 1..Suc n - 2. 1 / (2 ^ i::real)) = 1/(2^1::real) + (\<Sum>i = 2..Suc n - 2. 1 / (2 ^ i::real))"
      using *
      by (metis Suc_1 Suc_eq_plus1 Suc_lessD add_le_imp_le_diff diff_Suc_Suc eval_nat_numeral(3) less_Suc_eq_le sum.atLeast_Suc_atMost)
    let ?k = "Suc n"
    have helper_arith: "\<And>i. i > 0 \<Longrightarrow> 1 / (2 ^ i::real) > 0" by simp
    have "k \<ge> 2 \<Longrightarrow> (\<Sum>i = 2..k. 1 / (2 ^ i::real)) > 0" for k
    proof (induct k)
      case 0
      then show ?case by auto
    next
      case (Suc k)
      {assume *: "Suc k = 2"
        then have "(\<Sum>i = 2..Suc k. 1 / (2 ^ i::real)) = (\<Sum>i = 2..2. 1 / (2 ^ i::real))"
          by presburger
        then have ?case
          using helper_arith 
          by (simp add: "*")
      } moreover {assume *: "Suc k > 2"
        then have ind_h: "0 < (\<Sum>i = 2..k. 1 / (2 ^ i::real))"
          using Suc.hyps less_Suc_eq_le by blast
        have "(\<Sum>i = 2..Suc k. 1 / (2 ^ i::real)) = (\<Sum>i = 2..k. 1 / (2 ^ i::real)) + 1 / (2 ^ (Suc k)::real)"
          using Suc.prems add.commute by auto
        then have ?case using ind_h helper_arith 
          by (smt (verit) divide_less_0_1_iff zero_le_power)
      }
      ultimately show ?case 
        using Suc.prems by linarith
    qed
    then  have "(\<Sum>i = 2..Suc n - 2. 1 / (2 ^ i::real)) > 0"
      using * by auto
    then have "(\<Sum>i = 1..Suc n - 2. 1 / (2 ^ i::real)) > 1/2"
      using sum_split by auto
    then have "x > 1/2" using Suc.prems(4)  
      by (smt (verit, del_insts) atLeastAtMost_iff linorder_not_le order_le_less_trans)
    then have p'x'_eq_px: "?p' ?x' = p x" unfolding joinpaths_def by (simp add: joinpaths_def p_tl)
  
    have 1: "n \<ge> 3" using * by auto
    have 2: "length ?ell' = n" using Suc.prems(2) by simp
    have 3: "?p' = make_polygonal_path ?ell'" by auto
    have "x \<le> 1" using Suc.prems(4) by auto
    then have x'_lteq: "2*x - 1 \<le> 1" by auto
    have "x \<ge> (\<Sum>i = 1..Suc n - 2. 1 / 2 ^ i)"
      using Suc.prems(4) by auto
    then have x'_gteq: "?x' \<ge> (\<Sum>i = 1..n - 2. 1 / 2 ^ i)"
      using summation_helper[of "Suc n - 2"] *
      by (smt (verit) Suc.prems(1) Suc_1 Suc_diff_le Suc_leD Suc_le_mono diff_Suc_1 diff_Suc_eq_diff_pred eval_nat_numeral(3))
    have 4: "?x' \<in> {(\<Sum>i = 1..n - 2. 1 / 2 ^ i)..1}" using Suc.prems(4)
      using summation_helper[of "Suc n - 2"] * x'_lteq x'_gteq atLeastAtMost_iff by blast
    have 5: "?f' = (\<lambda>x. (x - (\<Sum>i = 1..n - 2. 1 / 2 ^ i)) * 2 ^ (n - 2))" by auto
    have "f x = (x - (\<Sum>i = 1..Suc n - 2. 1 / 2 ^ i)) * 2 ^ (n - 2)*2"
    proof -
      have "(\<lambda>r. (r - (\<Sum>n = 1..n - 1. 1 / 2 ^ n)) * 2 ^ (n - 1)) = f"
        by (simp add: Suc.prems(5))
      then have "2 ^ (n - 1) * (x - (\<Sum>n = 1..n - 1. 1 / 2 ^ n)) = f x"
        using Groups.mult_ac(2) by blast
      then have "(x - (\<Sum>n = 1..n - 1. 1 / 2 ^ n)) * (2 ^ (n - Suc 1) * 2) = f x"
        by (metis (no_types) Groups.mult_ac(2) Suc.prems(2) diff_Suc_1 diff_Suc_Suc ell_is length_Cons power.simps(2))
      then show ?thesis
        by (metis (no_types) Groups.mult_ac(1) Suc_1 diff_Suc_Suc)
    qed
    then have fx_is: "f x = (2*x - 2*(\<Sum>i = 1..Suc n - 2. 1 / 2 ^ i))* 2 ^ (n - 2)"
      by argo
    have sum_is: "1 + (\<Sum>i = 1..n - 2. 1 /( 2 ^ i::real)) = 2*(\<Sum>i = 1..Suc n - 2. 1 / (2 ^ i::real))"
    proof - 
      have sum_ish1: "(\<Sum>i = 1..Suc n - 2. 1 / (2 ^ i::real)) = 1/2 + (\<Sum>i = 2..Suc n - 2. 1 / (2 ^ i::real))"
        by (metis power_one_right sum_split)
      have "n \<ge> 2 \<Longrightarrow> 2*(\<Sum>i = 2..n - 1. 1 / (2 ^ i::real)) = (\<Sum>i = 1..n - 2. 1 /( 2 ^ i::real))"
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        {assume *: "Suc n = 2"
          then have ?case by auto
        } moreover {assume *: "Suc n > 2"
          then have ind_h: " 2 * (\<Sum>i = 2..n - 1. 1 / (2 ^ i::real)) = (\<Sum>i = 1..n - 2. 1 / (2 ^ i::real))"
            using Suc by fastforce
          have mult: "2*1/(2^(Suc n - 1)::real) = 1/(2^(n - 1)::real)"
            using * 
            by (smt (z3) One_nat_def add_diff_inverse_nat bot_nat_0.not_eq_extremum diff_Suc_1 div_by_1 le_zero_eq less_Suc_eq_le mult.commute nonzero_mult_div_cancel_left nonzero_mult_divide_mult_cancel_left plus_1_eq_Suc power_Suc zero_less_numeral)
          have sum_prop: "\<And>a::nat. \<And>f::nat\<Rightarrow>real.(\<Sum>i = 1..a. (f i)) + (f (a+1)) = (\<Sum>i = 1..a+1. (f i)) "
            by auto
          have "n - 2 + 1 = n - 1"
            using * by auto
          then have sum_same: "(\<Sum>i = 1..n - 2. 1 / (2 ^ i::real)) + 1 / 2 ^ (n - 1) = (\<Sum>i = 1..n - 1. 1 / (2 ^ i::real))"
            using * sum_prop[of "\<lambda>i. 1 / (2 ^ i::real)" "n-2"] by metis
          have " 2 * (\<Sum>i = 2..Suc n - 1. 1 / (2 ^ i::real)) =  2 * ((\<Sum>i = 2..n - 1. 1 / (2 ^ i::real)) + 1/(2^(Suc n - 1)::real))"
            using *
            by (smt (z3) add_2_eq_Suc add_diff_inverse_nat diff_Suc_1 distrib_left_numeral ind_h not_less_eq sum.cl_ivl_Suc) 
          then have " 2 * (\<Sum>i = 2..Suc n - 1. 1 / (2 ^ i::real)) = (\<Sum>i = 1..n - 2. 1 / (2 ^ i::real)) + 2*1/(2^(Suc n - 1)::real)"
            using ind_h by argo
          then have " 2 * (\<Sum>i = 2..Suc n - 1. 1 / (2 ^ i::real)) = (\<Sum>i = 1..n - 2. 1 / (2 ^ i::real)) + 1/(2^(n - 1)::real)"
            using * mult by auto
            then have ?case using sum_same by auto
        }
        ultimately show ?case by fastforce
      qed
      then have sum_ish2:"2*(\<Sum>i = 2..Suc n - 2. 1 / (2 ^ i::real)) = (\<Sum>i = 1..n - 2. 1 /( 2 ^ i::real))"
        using * by auto
      show ?thesis using sum_ish1 sum_ish2 by simp
    qed
    have "?p' ?x' = (linepath (?ell' ! (n-2)) (?ell' ! (n-1))) (?f' ?x')"
      using Suc.hyps[OF 1 2 3 4 5] by blast
    moreover have "?f' ?x' = f x" 
      using Suc.prems(5) fx_is sum_is 
      by (smt (verit, best))
    moreover have "?ell' ! (n-2) = ell ! ((Suc n)-2)"
      by (metis Nat.diff_add_assoc One_nat_def Suc.prems(1) Suc.prems(2) Suc_1 add_diff_cancel_left le_add1 nth_drop numeral_3_eq_3 plus_1_eq_Suc)
    moreover have "?ell' ! (n-1) = ell ! ((Suc n)-1)"
      using Suc.prems(1) Suc.prems(2) by auto
    ultimately have ?case using p'x'_eq_px by presburger
  }
  ultimately show ?case using Suc.prems(1) by linarith
qed


section "A Triangle is a Polygon"

lemma not_collinear_linepaths_intersect_helper:
  assumes not_collinear: "\<not>collinear {a,b,c}"
  assumes "0 \<le> k1"
  assumes "k1 \<le> 1"
  assumes "0 \<le> k2"
  assumes "k2 \<le> 1"
  assumes eo: "k2 = 0 \<Longrightarrow> k1 \<noteq> 1"
  shows "\<not> ((linepath a b) k1 = (linepath b c) k2)"
proof - 
  have a_neq_b:"a \<noteq> b" 
    using not_collinear
    by auto 
  then have nonz_1: "a - b \<noteq> 0"   
    by auto
  have b_neq_c: "b \<noteq> c"
    using not_collinear
    by auto
  then have nonz_2: "b - c \<noteq> 0"
    by auto
  have "\<not> collinear {a-b, 0, c-b}"
    using not_collinear 
    by (metis NO_MATCH_def collinear_3 insert_commute)
  then have notcollinear: "\<not> collinear { 0, a-b, c-b}"
    by (simp add: insert_commute)
  have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> (a - k1*\<^sub>R a) + k1 *\<^sub>R b = (b - k2 *\<^sub>R b) + k2 *\<^sub>R c"
    by (metis add_diff_cancel scaleR_collapse)
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> (1 - k1) *\<^sub>R a + k1 *\<^sub>R b - b = - k2 *\<^sub>R b + k2 *\<^sub>R c"
    by (metis (no_types, lifting) add_diff_cancel_left scaleR_collapse scaleR_minus_left uminus_add_conv_diff)
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> (1 - k1) *\<^sub>R a + k1 *\<^sub>R b - b = k2 *\<^sub>R (c-b)"
    by (simp add: scaleR_right_diff_distrib)
  then have rewrite: "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> (1-k1)*\<^sub>R(a - b) = k2 *\<^sub>R (c-b)"
    by (metis add_diff_cancel_right scaleR_collapse scaleR_right_diff_distrib)
  {assume *: "k2 \<noteq> 0"
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> c - b = ((1-k1)/k2)*\<^sub>R(a - b)"
    using rewrite assms(2-3) 
    by (smt (verit, ccfv_SIG) vector_fraction_eq_iff)
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> collinear {0, a-b, c-b}"
    using collinear_lemma[of "a -b" "c-b"] by auto 
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c  \<Longrightarrow> False"
    using notcollinear by auto
} moreover   {assume *: "k2 = 0"
  then have "k1 \<noteq>1"
    using assms by auto
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> a - b =  (k2/(1-k1)) *\<^sub>R (c-b)"
    using rewrite 
    by (smt (verit, ccfv_SIG) vector_fraction_eq_iff)
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c \<Longrightarrow> collinear {0, a-b, c-b}"
    using collinear_lemma[of "c-b" "a-b"]
    by (simp add: insert_commute)
  then have "(1 - k1) *\<^sub>R a + k1 *\<^sub>R b = (1 - k2) *\<^sub>R b + k2 *\<^sub>R c  \<Longrightarrow> False"
    using notcollinear by auto
  }
  ultimately show ?thesis
    unfolding linepath_def 
    by blast
qed


lemma not_collinear_linepaths_intersect_helper_2:
  assumes not_collinear: "\<not>collinear {a,b,c}"
  assumes "0 \<le> k1"
  assumes "k1 \<le> 1"
  assumes "0 \<le> k2"
  assumes "k2 \<le> 1"
  assumes eo: "k1 = 0 \<Longrightarrow> k2 \<noteq> 1"
  shows "\<not> ((linepath a b) k1 = (linepath c a) k2)"
  using not_collinear_linepaths_intersect_helper[of c a b k2 k1] assms
  by (simp add: insert_commute)

lemma not_collinear_loopfree_path: "\<And>a b c::real^2. \<not>collinear {a,b,c} \<Longrightarrow> loop_free ((linepath a b) +++ (linepath b c))"
proof - 
  fix a b c::"real^2"
  assume not_collinear: "\<not>collinear {a,b,c}"
  then have a_neq_b:"a \<noteq> b"   
    by auto 
  have b_neq_c: "b \<noteq> c"
    using not_collinear
    by auto
  have "\<And>x y::real. (linepath a b +++ linepath b c) x = (linepath a b +++ linepath b c) y \<Longrightarrow>
           x < y \<Longrightarrow>
           x = 0 \<longrightarrow> y \<noteq> 1 \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> False"
  proof - 
    fix x y:: "real"
    assume same_eval: "(linepath a b +++ linepath b c) x = (linepath a b +++ linepath b c) y"
    assume x_neq_y: "x < y"
    assume x_zero_imp: "x = 0 \<longrightarrow> y \<noteq> 1" 
    assume x_gt: "0 \<le> x"
    assume x_lt: "x \<le> 1"
    assume y_gt: "0 \<le> y"
    assume y_lt: "y \<le> 1"
    {assume *: "x \<le> 1/2 \<and> y \<le> 1/2"
      then have "(1 - 2 * x) *\<^sub>R a + (2 * x) *\<^sub>R b = (1 - 2 * y) *\<^sub>R a + (2 * y) *\<^sub>R b \<Longrightarrow> False"
        using x_gt y_gt x_neq_y a_neq_b linepath_loop_free[of a b] 
        by (smt (z3) add_diff_cancel_left add_diff_cancel_right' add_diff_eq scaleR_cancel_left scaleR_left_diff_distrib)
      then have "False"
        using * same_eval unfolding joinpaths_def linepath_def
        by auto
    } moreover {assume *: "x > 1/2 \<and> y > 1/2"
      have "False"
        using x_lt y_lt x_neq_y b_neq_c linepath_loop_free[of b c] 
        using * same_eval unfolding joinpaths_def linepath_def 
        by (smt (z3) add_diff_cancel_left add_diff_cancel_right' add_diff_eq scaleR_cancel_left scaleR_collapse scaleR_left_diff_distrib)
    } moreover {assume *: "x \<le> 1/2 \<and> y > 1/2"
      (* Using that the lines are not collinear with not_collinear_linepaths_intersect_helper *)
      then have lp_eq: "(linepath a b) (2 * x) = (linepath b c) (2 * y - 1)"
        using * same_eval unfolding joinpaths_def
        by auto
      have "(2 * y - 1) = 0 \<longrightarrow> (2*x) \<noteq> 1 \<and> 0 \<le> (2*x) \<and> (2*x) \<le> 1 \<and> 0 \<le> (2 * y - 1) \<and> (2 * y - 1) \<le> 1"
        using x_lt x_gt x_neq_y * by auto
      then have "False"
        using lp_eq not_collinear_linepaths_intersect_helper[of a b c "2*x" "2 * y - 1"] 
        not_collinear
        using "*" x_gt y_lt by auto 
    }
    ultimately show "False"
      using x_lt y_lt x_neq_y 
      by linarith
  qed
  then have "\<And>x y::real. (linepath a b +++ linepath b c) x = (linepath a b +++ linepath b c) y \<Longrightarrow>
           x \<noteq> y \<Longrightarrow>
           x = 0 \<longrightarrow> y \<noteq> 1 \<Longrightarrow> x = 1 \<longrightarrow> y \<noteq> 0 \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> False"
    by (metis linorder_less_linear)
  then show "loop_free (linepath a b +++ linepath b c)"
    unfolding loop_free_def 
    by (metis atLeastAtMost_iff)
qed

lemma triangle_is_polygon: "\<And>a b c. \<not>collinear {a,b,c} \<Longrightarrow> polygon (make_triangle a b c)"
proof -
  fix a b c::"real^2"
  assume not_coll:"\<not>collinear {a,b,c}"
  then have a_neq_b:"a \<noteq> b"   
    by auto 
  have b_neq_c: "b \<noteq> c"
    using not_coll
    by auto
  have a_neq_c: "c \<noteq> a"
    using not_coll
    using collinear_3_eq_affine_dependent by blast 
  let ?vts = "[a, b, c, a]"
  have polygonal_path: "polygonal_path (make_polygonal_path [a, b, c, a])"
    by (metis Collect_const UNIV_I image_eqI polygonal_path_def)
  then have path: "path (make_polygonal_path [a, b, c, a])"
    by auto
  then have closed_path: "closed_path (make_polygonal_path [a, b, c, a])"
    unfolding closed_path_def using polygon_pathstart polygon_pathfinish
    by auto
  let ?seg1 = "(linepath a b) +++ (linepath b c)"
  have lf1: "loop_free ((linepath a b) +++ (linepath b c))"
    using not_collinear_loopfree_path not_coll 
    by auto
  then have "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. ?seg1 x = ?seg1 y \<longrightarrow> x = y"
    using a_neq_c unfolding loop_free_def 
    by (metis (no_types, lifting) path_defs(2) pathfinish_def pathfinish_join pathfinish_linepath pathstart_join pathstart_linepath)
  let ?seg2 = "(linepath b c) +++ (linepath c a)"
  have lf2: "loop_free ((linepath b c) +++ (linepath c a))"
    using not_collinear_loopfree_path not_coll 
    by (simp add: insert_commute)
  then have "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. ?seg2 x = ?seg2 y \<longrightarrow> x = y"
    using a_neq_b unfolding loop_free_def 
    by (metis (no_types, lifting) path_defs(2) pathfinish_def pathfinish_join pathfinish_linepath pathstart_join pathstart_linepath)
  let ?seg3 = "(linepath c a) +++ (linepath a b)"
  have lf3: "loop_free ((linepath c a) +++ (linepath a b))"
    using not_collinear_loopfree_path not_coll 
    by (simp add: insert_commute)
 then have "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. ?seg3 x = ?seg3 y \<longrightarrow> x = y"
    using b_neq_c unfolding loop_free_def 
    by (metis (no_types, lifting) path_defs(2) pathfinish_def pathfinish_join pathfinish_linepath pathstart_join pathstart_linepath)
  have mpp_is: "\<forall>x\<in>{0..1}. make_polygonal_path [a, b, c, a] x = ((linepath a b) +++ (linepath b c) +++ (linepath c a)) x" 
    by auto
  have x_in_int1: "\<forall>x\<in>{0..(1/2)}. make_polygonal_path [a, b, c, a] x = ((linepath a b)) (2*x)" 
    using mpp_is
    unfolding joinpaths_def by auto
  have x_in_int2: "\<forall>x\<in>{1/2<..(3/4)}. make_polygonal_path [a, b, c, a] x = ((linepath b c)) (2*(2*x - 1))" 
    using mpp_is unfolding joinpaths_def 
    by auto
  have x_in_int3: "\<forall>x\<in>{3/4<..1}. make_polygonal_path [a, b, c, a] x = ((linepath c a)) (2 * (2 * x - 1) - 1)" 
    using mpp_is unfolding joinpaths_def 
    by auto
  have "\<And>x y. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x \<noteq> y \<and> (x = 0 \<longrightarrow> y \<noteq> 1) \<and> (x = 1 \<longrightarrow> y \<noteq> 0) \<Longrightarrow> make_polygonal_path [a, b, c, a] x = make_polygonal_path [a, b, c, a] y \<Longrightarrow> False"
  proof -
    fix x y:: "real"
    assume big: "0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> x \<noteq> y \<and> (x = 0 \<longrightarrow> y \<noteq> 1) \<and> (x = 1 \<longrightarrow> y \<noteq> 0)"
    assume false_hyp: "make_polygonal_path [a, b, c, a] x = make_polygonal_path [a, b, c, a] y"
    {assume *: "x \<in> {0..(1/2)}"
      then have x_eval: "make_polygonal_path [a, b, c, a] x = ((linepath a b)) (2*x)"
        using x_in_int1 by auto
      {assume **: "y \<in> {0..(1/2)}"
             then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath a b)) (2*y)"
               using x_in_int1 by auto
             then have "((linepath a b)) (2*x) = ((linepath a b)) (2*y)"
               using false_hyp x_eval y_eval by auto 
             then have "False"
               using linepath_loop_free big * **
               unfolding loop_free_def
               using a_neq_b add_diff_cancel_left add_diff_cancel_right' add_diff_eq linepath_def scaleR_cancel_left scaleR_collapse scaleR_left_diff_distrib
               by (smt (verit))
           } moreover {assume **: "y \<in> {(1/2)<..(3/4)}"
             then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath b c)) (2*(2*y - 1))"
               using x_in_int2 by auto
             then have "((linepath a b)) (2*x) = ((linepath b c)) (2*(2*y - 1))"
               using false_hyp x_eval y_eval by auto 
            then have "False"
              using big * ** not_collinear_linepaths_intersect_helper[of a b c "2*x" "(2*(2*y - 1))"] not_coll
              by auto
          } moreover {assume **: "y \<in> {(3/4)<..1}"
             then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath c a)) ((2 * (2 * y - 1) - 1))"
               using x_in_int3 by auto
             then have "((linepath a b)) (2*x) = ((linepath c a)) ((2 * (2 * y - 1) - 1))"
               using false_hyp x_eval y_eval by auto 
            then have "False"
              using big * ** not_collinear_linepaths_intersect_helper_2[of a b c "(2*x)" "((2 * (2 * y - 1) - 1))"] not_coll 
              by auto
          }
          ultimately have "False"
            using big 
            by (metis atLeastAtMost_iff greaterThanAtMost_iff linorder_not_le)
        } moreover {assume *: "x \<in> {(1/2)<..(3/4)}"
          then have x_eval: "make_polygonal_path [a, b, c, a] x = ((linepath b c)) (2*(2*x - 1))"
               using x_in_int2 by auto
          {assume **: "y \<in> {0..(1/2)}"
            then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath a b)) (2*y)"
              using x_in_int1 by auto
            then have lp_eq: "((linepath a b)) (2*y) = ((linepath b c)) (2*(2*x - 1))"
              using false_hyp x_eval y_eval by auto
            have "2 * (2 * x - 1) \<noteq> 0"
              using * by auto
            then have "False"
              using lp_eq big * ** not_collinear_linepaths_intersect_helper[of a b c "2*y" "(2*(2*x - 1))"] not_coll
              by auto
          } moreover {assume **: "y \<in> {(1/2)<..(3/4)}"
            then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath b c)) (2*(2*y - 1))"
              using x_in_int2 by auto
            then have lp_eq: "((linepath b c)) (2*(2*y - 1)) = ((linepath b c)) (2*(2*x - 1))"
              using false_hyp x_eval y_eval by auto
            then have "False"
              using linepath_loop_free[OF b_neq_c] big * **
               unfolding loop_free_def
               using  add_diff_cancel_left add_diff_cancel_right' add_diff_eq linepath_def scaleR_cancel_left scaleR_collapse scaleR_left_diff_distrib
               by (smt (verit) b_neq_c)
          } moreover {assume **: "y \<in> {(3/4)<..1}"
            then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath c a)) ((2 * (2 * y - 1) - 1))"
              using x_in_int3 by auto
            then have lp_eq: "((linepath b c)) (2*(2*x - 1)) = ((linepath c a)) ((2 * (2 * y - 1) - 1))"
              using false_hyp x_eval y_eval 
              by auto
            have not_coll2: "\<not> collinear {b, c, a}"
              using not_coll 
              by (simp add: insert_commute)
            have "2 * (2 * x - 1) \<noteq> 0"
              using * by auto
            then have "False" using lp_eq
              using big * ** not_collinear_linepaths_intersect_helper[of b c a "2*(2*x - 1)" "(2 * (2 * y - 1) - 1)"] not_coll2 
              by auto
          } 
          ultimately have "False"
            using big 
            by (metis atLeastAtMost_iff greaterThanAtMost_iff linorder_not_le)
        }  moreover {assume *: "x \<in> {(3/4)<..1}"
          then have x_eval: "make_polygonal_path [a, b, c, a] x = ((linepath c a)) ((2 * (2 * x - 1) - 1))"
               using x_in_int3 by auto
          {assume **: "y \<in> {0..(1/2)}"
            then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath a b)) (2*y)"
              using x_in_int1 by auto
            then have lp_eq: "((linepath c a)) ((2 * (2 * x - 1) - 1)) = ((linepath a b)) (2*y)"
              using x_eval y_eval
              using false_hyp by presburger
            have not_coll2: "\<not> collinear {c, a, b}"
              using not_coll 
              by (simp add: insert_commute)
            have "((2 * (2 * x - 1) - 1)) \<noteq> 0"
              using * by auto 
            then have "False"
              using lp_eq big * ** not_coll2
              not_collinear_linepaths_intersect_helper[of c a b "(2 * (2 * x - 1) - 1)" "2*y"]
              by auto
          } moreover {assume **: "y \<in> {(1/2)<..(3/4)}"
            then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath b c)) (2*(2*y - 1))"
              using x_in_int2 by auto
            then have lp_eq: "((linepath b c)) (2*(2*y - 1)) = ((linepath c a)) ((2 * (2 * x - 1) - 1))"
              using x_eval y_eval false_hyp
              using false_hyp by presburger
            have not_coll2: "\<not> collinear {b, c, a}"
              using not_coll 
              by (simp add: insert_commute)
            have "((2 * (2 * x - 1) - 1)) \<noteq> 0"
              using * by auto 
            then have "False"
              using lp_eq big * ** not_coll2
              not_collinear_linepaths_intersect_helper[of b c a "(2*(2*y - 1))" "(2 * (2 * x - 1) - 1)"]
              by auto
          } moreover {assume **: "y \<in> {(3/4)<..1}"
            then have y_eval: "make_polygonal_path [a, b, c, a] y = ((linepath c a)) ((2 * (2 * y - 1) - 1))"
              using x_in_int3 by auto
            then have "((linepath c a)) ((2 * (2 * y - 1) - 1)) = ((linepath c a)) ((2 * (2 * x - 1) - 1))"
              using x_eval y_eval false_hyp
              using false_hyp by presburger
            then have "False"
              using linepath_loop_free[OF a_neq_c] big * **
               unfolding loop_free_def
               using  add_diff_cancel_left add_diff_cancel_right' add_diff_eq linepath_def scaleR_cancel_left scaleR_collapse scaleR_left_diff_distrib
               by (smt (verit) a_neq_c add_diff_cancel_left')
          } 
          ultimately have "False"
            using big 
            by (metis atLeastAtMost_iff greaterThanAtMost_iff linorder_not_le)
        }
        ultimately show "False" using big
          by (metis atLeastAtMost_iff greaterThanAtMost_iff linorder_not_le)
  qed
  then have loop_free: "loop_free (make_polygonal_path [a, b, c, a])"
    unfolding loop_free_def 
    by (meson atLeastAtMost_iff)
  show "polygon (make_triangle a b c)"
    unfolding make_triangle_def polygon_def simple_path_def
    using polygonal_path closed_path loop_free by auto
qed


lemma have_wraparound_vertex:
  assumes "polygon p"
  assumes "p = make_polygonal_path vts"
  shows "vts = (take (length vts -1) vts)@[vts ! 0]"
proof - 
  have "card (set vts) \<ge> 3"
    using polygon_at_least_3_vertices assms by auto
  then have nonempty: "vts \<noteq> []"
    by auto
  then have "vts = (take (length vts -1) vts)@[vts ! (length vts - 1)]"
    by (metis append_butlast_last_id butlast_conv_take last_conv_nth)
  then show ?thesis
    using assms(1) unfolding polygon_def closed_path_def
    using polygon_pathstart[OF nonempty assms(2)] polygon_pathfinish[OF nonempty assms(2)]
    by presburger
qed


lemma polygon_at_least_3_vertices_wraparound:
  assumes "polygon p"
  assumes "p = make_polygonal_path vts"
  shows "card (set (take (length vts -1) vts)) \<ge> 3"
proof - 
  let ?distinct_vts = "take (length vts -1) vts"
  have card_vts: "card (set vts) \<ge> 3"
    using polygon_at_least_3_vertices assms by auto
  then have vts_is: "vts = ?distinct_vts@[vts ! 0]"
    using have_wraparound_vertex assms by auto
  then have "?distinct_vts \<noteq> []"
    using card_vts 
    by (metis One_nat_def append_Nil distinct_card distinct_singleton eval_nat_numeral(3) length_append_singleton list.size(3) not_less_eq_eq one_le_numeral)
  then have "vts ! 0 \<in> set ?distinct_vts"
    by (metis \<open>vts = take (length vts - 1) vts @ [vts ! 0]\<close> length_greater_0_conv nth_append nth_mem)
  then have "card (set ?distinct_vts) = card (set vts)"
    using vts_is 
    by (metis Un_insert_right append.right_neutral insert_absorb list.set(2) set_append)
  then show ?thesis using card_vts by auto
qed

section "Polygon Vertex Rotation"

definition rotate_polygon_vertices:: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where "rotate_polygon_vertices ell i = 
    (let ell1 = rotate i (butlast ell) in ell1 @ [ell1 ! 0])"

lemma rotate_polygon_vertices_same_set:
  assumes "polygon (make_polygonal_path vts)"
  shows "set (rotate_polygon_vertices vts i) = set vts"
proof - 
  have card_gteq: "card (set vts) \<ge> 3"
    using polygon_at_least_3_vertices assms 
    by auto 
  then have len_gteq: "length vts \<ge> 3"
    using card_length order_trans by blast
  let ?ell1 = "rotate i (take (length vts - 1) vts)"
  have inset: "vts ! 0 = vts ! (length vts - 1)"
    using assms polygon_pathstart polygon_pathfinish unfolding polygon_def closed_path_def
    by (metis len_gteq list.size(3) not_numeral_le_zero)
  have "set vts = set (take (length vts - 1) vts) \<union> {vts ! (length vts - 1)}"
    by (metis Cons_nth_drop_Suc One_nat_def Un_insert_right assms card.empty diff_zero drop_rev length_greater_0_conv list.set(1) list.set(2) not_numeral_le_zero order.refl polygon_at_least_3_vertices rev_nth set_rev sup_bot.right_neutral take_all)
  then have "set vts = set (take (length vts - 1) vts)"
    using inset 
    by (metis (no_types, lifting) One_nat_def Suc_neq_Zero Suc_pred Un_insert_right add_diff_cancel_left' butlast_conv_take diff_is_0_eq' insert_absorb len_gteq length_butlast length_greater_0_conv list.size(3) nth_mem nth_take numeral_3_eq_3 plus_1_eq_Suc sup_bot.right_neutral)
  then have same_set: "set vts = set ?ell1"
    by auto
  then have "rotate i (take (length vts - 1) vts) ! 0 \<in> set vts"
    using len_gteq 
    by (metis card_gteq card_length le_zero_eq length_greater_0_conv list.size(3) nth_mem numeral_3_eq_3 zero_less_Suc)
  then have "set vts = set (?ell1 @ [?ell1 ! 0])"
    using same_set by auto
  then show ?thesis
    unfolding rotate_polygon_vertices_def 
    using card_gteq
    by (metis butlast_conv_take)
qed

lemma arb_rotation_as_single_rotation:
  fixes i:: "nat"
  shows "rotate_polygon_vertices vts (Suc i) = rotate_polygon_vertices (rotate_polygon_vertices vts i) 1"
  unfolding rotate_polygon_vertices_def 
  by (metis butlast_snoc plus_1_eq_Suc rotate_rotate)

lemma rotation_sum:
  fixes i j :: nat
  shows "rotate_polygon_vertices vts (i + j) = rotate_polygon_vertices (rotate_polygon_vertices vts i) j"
proof(induct j)
  case 0
  thus ?case by (metis Nat.add_0_right butlast_snoc id_apply rotate0 rotate_polygon_vertices_def)
next
  case (Suc j)
  have "rotate_polygon_vertices vts (i + (Suc j)) = rotate_polygon_vertices vts (Suc (i + j))" by simp
  also have "... = rotate_polygon_vertices (rotate_polygon_vertices vts (i + j)) 1"
    using arb_rotation_as_single_rotation by blast
  also have "... = rotate_polygon_vertices (rotate_polygon_vertices (rotate_polygon_vertices vts i) j) 1"
    using Suc.hyps by simp
  also have "... = rotate_polygon_vertices (rotate_polygon_vertices vts i) (Suc j)"
    using arb_rotation_as_single_rotation by metis
  finally show ?case .
qed

lemma rotated_polygon_vertices_helper:
  fixes p :: "R_to_R2"
  assumes poly_p: "polygon p"
  assumes p_is_path: "p = make_polygonal_path vts" 
  assumes p'_is: "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
  shows "(vts ! 0) = (rotate_polygon_vertices vts 1) ! (length (rotate_polygon_vertices vts 1) - 2)"
        "(rotate_polygon_vertices vts 1) ! (length (rotate_polygon_vertices vts 1) - 1) = (vts ! 1)"
proof - 
  have len_gteq: "length vts \<ge> 3"
    using polygon_at_least_3_vertices assms 
    using card_length order_trans by blast
  let ?rotated_vts = "rotate_polygon_vertices vts 1"
  have same_len: "length ?rotated_vts = length vts"
    unfolding rotate_polygon_vertices_def using length_rotate
    by (metis One_nat_def Suc_pred card.empty length_append_singleton length_butlast length_greater_0_conv list.set(1) not_numeral_le_zero p_is_path poly_p polygon_at_least_3_vertices)
  then have len_rotated_gt_eq3: "length ?rotated_vts \<ge> 3"
    using len_gteq by auto
  show vts1: "vts ! 0 = ?rotated_vts ! (length ?rotated_vts - 2)"
    unfolding rotate_polygon_vertices_def 
    using nth_rotate[of "length ?rotated_vts - 2" "butlast vts" 1]
      Suc_diff_Suc butlast_snoc length_butlast length_greater_0_conv lessI less_nat_zero_code list.size(3) mod_self nat_1_add_1 nth_butlast plus_1_eq_Suc rotate_polygon_vertices_def same_len zero_less_diff
    by (smt (z3) One_nat_def len_gteq length_append_singleton numeral_le_one_iff semiring_norm(70))  
    have "(rotate 1 (butlast vts)) ! 0 = vts ! 1"
    unfolding rotate_polygon_vertices_def 
    using nth_rotate[of 0 "butlast vts" 1] len_gteq len_rotated_gt_eq3
    by (metis (no_types, lifting) One_nat_def Suc_le_eq length_butlast less_diff_conv less_nat_zero_code mod_less not_gr_zero nth_butlast numeral_3_eq_3 plus_1_eq_Suc)
  then show vts2: "?rotated_vts ! (length ?rotated_vts - 1) = vts ! 1"
    unfolding rotate_polygon_vertices_def
    by (smt (verit, best) Suc_diff_Suc Suc_eq_plus1 butlast_snoc length_butlast length_greater_0_conv less_nat_zero_code list.size(3) nth_append_length one_add_one rotate_polygon_vertices_def zero_less_diff)     
qed

lemma rotate_polygon_vertices_same_length:
  fixes vts :: "(real^2) list"
  assumes "length vts \<ge> 1"
  shows "length vts = length (rotate_polygon_vertices vts i)"
  using assms
proof(induction "length vts" arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case using arb_rotation_as_single_rotation[of vts x]
    by (metis diff_Suc_1 length_append_singleton length_butlast length_rotate rotate_polygon_vertices_def)
qed

lemma rotated_polygon_vertices_helper2:
  assumes len_gteq: "length vts \<ge> 2"
  assumes "i < length vts - 1"
  assumes "hd vts = last vts"
  shows "(rotate_polygon_vertices vts 1) ! i = vts ! (i+1)"
proof - 
  let ?rotated_vts = "rotate_polygon_vertices vts 1"
  have "length (butlast vts) = length vts - 1"
    by auto
  then have same_len: "length ?rotated_vts = length vts"
    unfolding rotate_polygon_vertices_def using length_rotate len_gteq
    by (metis dual_order.trans le_add_diff_inverse length_append_singleton one_le_numeral plus_1_eq_Suc)
  then have len_rotated_gt_eq3: "length ?rotated_vts \<ge> 2"
    using len_gteq by auto
  let ?n = "length vts"
  {assume *: "i < length vts - 2"
  then have same_mod: "(1 + i) mod length (butlast vts) = 1+i"
    using assms by simp
  have "i < length (butlast vts) "
    using assms by simp
  then have "rotate 1 (butlast vts) ! i = butlast vts ! (i + 1)"
 using nth_rotate[of i "butlast vts" 1] same_mod  
  by (metis add.commute)
  then have "(rotate_polygon_vertices vts 1) ! i = vts ! (i+1)"
    by (metis (no_types, lifting) Suc_eq_plus1 \<open>i < length (butlast vts)\<close> butlast_snoc length_butlast length_greater_0_conv less_nat_zero_code list.size(3) mod_less_divisor nth_butlast plus_1_eq_Suc rotate_polygon_vertices_def same_len same_mod)
} moreover {assume *: "i = length vts - 2 "
then have same_mod: "(1 + i) mod length (butlast vts) = 0"
  using assms 
  by (metis Suc_diff_Suc \<open>length (butlast vts) = length vts - 1\<close> length_greater_0_conv less_nat_zero_code list.size(3) mod_Suc mod_if one_add_one plus_1_eq_Suc zero_less_diff)
  have "i < length (butlast vts) "
    using assms by simp
  then have rotate_prop: "rotate 1 (butlast vts) ! i = butlast vts ! 0"
 using nth_rotate[of i "butlast vts" 1] same_mod  
  by metis
  have "butlast vts ! 0 = vts ! 0"
    using assms(1)
    by (simp add: nth_butlast) 
  then have "butlast vts ! 0 = vts ! (length vts - 1)"
    by (metis assms(3) hd_conv_nth last_conv_nth length_0_conv zero_diff)
  then have "(rotate_polygon_vertices vts 1) ! i = vts ! (i+1)"
    by (metis * rotate_prop Suc_diff_Suc Suc_eq_plus1 \<open>butlast vts ! 0 = vts ! 0\<close> add_2_eq_Suc' le_add_diff_inverse2 len_gteq less_add_Suc2 one_add_one same_len butlast_snoc length_butlast lessI nth_butlast rotate_polygon_vertices_def)
  }
  ultimately show ?thesis
    using assms(2) by linarith
qed

lemma polygon_rotation_t_translation1:
  assumes "polygon_of p vts"
  assumes "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
    (is "p' = make_polygonal_path ?vts'")
  assumes "x' \<in> {(\<Sum>i \<in> {1..k}. 1/(2^i))..(\<Sum>i \<in> {1..k+1}. 1/(2^i))}"
  assumes "n = length vts"
  assumes "0 \<le> k \<and> k \<le> n - 4"
  assumes "l = x' - (\<Sum>i \<in> {1..k}. 1/(2^i))"
  assumes "x = l/2 + (\<Sum>i \<in> {1..(k + 1)}. 1/(2^i))"
  shows "x \<in> {(\<Sum>i \<in> {1..k+1}. 1/(2^i))..(\<Sum>i \<in> {1..k+2}. 1/(2^i))}"
        "p' x' = p x"
proof-
  let ?f = "\<lambda>(k::nat) (x::real). (x - (\<Sum>i \<in> {1..k}. 1/(2^i))) * (2^(k+1))"
  have "x \<ge> (\<Sum>i \<in> {1..k+1}. 1/(2^i))"
  proof-
    have "l \<ge> 0" using assms(3,6) by auto
    then show ?thesis using assms(7) by linarith
  qed
  moreover have "x \<le> (\<Sum>i \<in> {1..k+2}. 1/(2^i))"
  proof-
    have "x' \<le> (\<Sum>i \<in> {1..k+1}. 1/(2^i))" using assms(3) by presburger
    then have "l \<le> (\<Sum>i \<in> {1..k+1}. 1/(2^i)) - (\<Sum>i \<in> {1..k}. 1/(2^i))" using assms(6) by argo
    also have "... = (1/2^(k+1)) + (\<Sum>i \<in> {1..k}. 1/(2^i)) - (\<Sum>i \<in> {1..k}. 1/(2^i))"
      using sum_insert[of "k+1" "{1..k}" "\<lambda>i. 1/(2^i)"]
      by (smt (verit) Suc_eq_plus1 Suc_n_not_le_n add.commute atLeastAtMostSuc_conv atLeastAtMost_iff finite_atLeastAtMost le_add2 one_add_one)
    also have "... = (1/2^(k+1))" by argo
    finally have "l \<le> (1/2^(k+1))" .
    then have "x \<le> (1/2^(k+1))/2 + (\<Sum>i \<in> {1..k+1}. 1/(2^i))" using assms(7) by simp
    also have "... = 1/2^(k+2) + (\<Sum>i \<in> {1..k+1}. 1/(2^i))" by simp
    also have "... = (\<Sum>i \<in> {1..k+2}. 1/(2^i))"
      using sum_insert[of "k+2" "{1..k+2}" "\<lambda>i. 1/(2^i)"] by simp
    finally show ?thesis .
  qed
  ultimately show x: "x \<in> {(\<Sum>i \<in> {1..k+1}. 1/(2^i))..(\<Sum>i \<in> {1..k+2}. 1/(2^i))}" by presburger
  have 1: "n \<ge> 4" using polygon_vertices_length_at_least_4 assms 
    using polygon_of_def by blast
  then have 2: "length vts = length ?vts'"
    using assms rotate_polygon_vertices_same_length by auto
  then have 3: "length ?vts' = n" using assms by auto
  
  have "p' x' = ((linepath (?vts' ! k) (?vts' ! (k+1)) (?f k x')))"
    using polygon_linepath_images2[of n k ?vts' p' ?f x'] assms(2,3,5) 1 3 by fastforce
  moreover have "p x = ((linepath (vts ! (k+1)) (vts ! (k+2)) (?f (k+1) x)))"
    using polygon_linepath_images2[of n "k+1" vts p ?f x] assms(2,3,5) 1 2 3 x
    by (smt (verit, ccfv_threshold) Nat.diff_add_assoc add.commute add_diff_cancel_left add_le_imp_le_left add_left_mono assms(1) nat_add_1_add_1 one_plus_numeral polygon_of_def semiring_norm(2) semiring_norm(4) trans_le_add1)
  moreover have "?vts' ! k = vts ! (k+1)"
    using rotated_polygon_vertices_helper2
    by (smt (verit, best) "1" Nat.le_diff_conv2 Suc_pred' add_leD1 assms(1) assms(4) assms(5) diff_diff_cancel diff_less have_wraparound_vertex hd_conv_nth leD length_greater_0_conv less_Suc_eq nat_less_le numeral_Bit0 numeral_eq_one_iff polygon_of_def semiring_norm(83) snoc_eq_iff_butlast zero_less_numeral)
  moreover have "?vts' ! (k+1) = vts ! (k+2)"
    using rotated_polygon_vertices_helper2[of vts "k+1"]
    by (metis (no_types, lifting) assms(1,4,5) "1" One_nat_def Suc_diff_Suc add_Suc_right diff_zero have_wraparound_vertex hd_conv_nth le_add_diff_inverse2 less_add_Suc2 nat_less_le not_less_eq_eq numeral_Bit0 one_add_one plus_1_eq_Suc polygon_of_def snoc_eq_iff_butlast)
  moreover have "?f k x' = ?f (k+1) x" using assms(6) assms(7) by force
  ultimately show "p' x' = p x" by presburger
qed

lemma polygon_rotation_t_translation1_strict:
  assumes "polygon_of p vts"
  assumes "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
    (is "p' = make_polygonal_path ?vts'")
  assumes "x' \<in> {(\<Sum>i \<in> {1..k}. 1/(2^i))..<(\<Sum>i \<in> {1..k+1}. 1/(2^i))}"
  assumes "n = length vts"
  assumes "0 \<le> k \<and> k \<le> n - 4"
  assumes "l = x' - (\<Sum>i \<in> {1..k}. 1/(2^i))"
  assumes "x = l/2 + (\<Sum>i \<in> {1..(k + 1)}. 1/(2^i))"
  shows "x \<in> {(\<Sum>i \<in> {1..k+1}. 1/(2^i))..<(\<Sum>i \<in> {1..k+2}. 1/(2^i))}"
        "p' x' = p x"
proof - 
let ?f = "\<lambda>(k::nat) (x::real). (x - (\<Sum>i \<in> {1..k}. 1/(2^i))) * (2^(k+1))"
  have "x \<ge> (\<Sum>i \<in> {1..k+1}. 1/(2^i))"
  proof-
    have "l \<ge> 0" using assms(3,6) by auto
    then show ?thesis using assms(7) by linarith
  qed
  moreover have "x < (\<Sum>i \<in> {1..k+2}. 1/(2^i))"
  proof-
    have "x' < (\<Sum>i \<in> {1..k+1}. 1/(2^i))" using assms(3) by auto
    then have "l < (\<Sum>i \<in> {1..k+1}. 1/(2^i)) - (\<Sum>i \<in> {1..k}. 1/(2^i))" using assms(6) by argo
    also have "... = (1/2^(k+1)) + (\<Sum>i \<in> {1..k}. 1/(2^i)) - (\<Sum>i \<in> {1..k}. 1/(2^i))"
      using sum_insert[of "k+1" "{1..k}" "\<lambda>i. 1/(2^i)"]
      by (smt (verit) Suc_eq_plus1 Suc_n_not_le_n add.commute atLeastAtMostSuc_conv atLeastAtMost_iff finite_atLeastAtMost le_add2 one_add_one)
    also have "... = (1/2^(k+1))" by argo
    finally have "l < (1/2^(k+1))" .
    then have "x < (1/2^(k+1))/2 + (\<Sum>i \<in> {1..k+1}. 1/(2^i))" using assms(7) by simp
    also have "... = 1/2^(k+2) + (\<Sum>i \<in> {1..k+1}. 1/(2^i))" by simp
    also have "... = (\<Sum>i \<in> {1..k+2}. 1/(2^i))"
      using sum_insert[of "k+2" "{1..k+2}" "\<lambda>i. 1/(2^i)"] by simp
    finally show ?thesis .
  qed
  ultimately show "x \<in> {(\<Sum>i \<in> {1..k+1}. 1/(2^i))..<(\<Sum>i \<in> {1..k+2}. 1/(2^i))}"
    by auto
  show "p' x' = p x"
    using assms(3) polygon_rotation_t_translation1[OF assms(1) assms(2) _ assms(4) assms(5) assms(6) assms(7)] 
    by (meson atLeastAtMost_iff atLeastLessThan_iff less_eq_real_def)
qed

lemma polygon_rotation_t_translation2:
  assumes "polygon_of p vts"
  assumes "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
    (is "p' = make_polygonal_path ?vts'")
  assumes "n = length vts"
  assumes "x' \<in> {(\<Sum>i \<in> {1..(n-3)}. 1/(2^i))..(\<Sum>i \<in> {1..(n-2)}. 1/(2^i))}"
  assumes "x = x' + 1/(2^(n-2))"
  shows "x \<in> {(\<Sum>i \<in> {1..n-2}. 1/(2^i))..1}"
        "p' x' = p x"
proof-
  let ?k = "n-3"
  let ?f' = "(\<lambda>(k::nat) x::real. (x - (\<Sum>i \<in> {1..k}. 1/(2^i))) * (2^(k+1)))"
  have n_geq_4: "n \<ge> 4" using polygon_vertices_length_at_least_4 assms 
    using polygon_of_def by blast
  moreover then have same_len: "length vts = length ?vts'"
    using assms rotate_polygon_vertices_same_length[of vts] by auto
  moreover then have "length ?vts' = n" using assms(3) by auto
  ultimately have p'x': "p' x' = ((linepath (?vts' ! ?k) (?vts' ! (?k+1)) (?f' ?k x')))"
    using polygon_linepath_images2[of n ?k ?vts' p' ?f' x'] assms
    by (smt (verit, ccfv_threshold) One_nat_def Suc_diff_Suc diff_diff_left diff_is_0_eq' le_add2 le_add_diff_inverse2 linorder_not_le nat_le_linear numeral_3_eq_3 numeral_Bit0 numeral_le_iff numeral_le_one_iff numerals(1) one_plus_numeral plus_1_eq_Suc trans_le_add2)
  let ?f = "(\<lambda>x::real. (x - (\<Sum>i \<in> {1..n-2}. 1/(2^i))) * (2^(n-2)))"
  have sum_prop: "\<And>i::nat. \<And>f::nat\<Rightarrow>real. ( \<Sum>i = 1..i. f i) +  f (i + 1) = (\<Sum>i = 1..i+1. f i)"
    by auto
  have sum_upto: "(\<Sum>i = 1..n - 3. 1 / (2 ^ i::real)) +  1 / 2 ^ (n - 2) = (\<Sum>i = 1..n - 2. 1 / (2 ^ i::real))"
    using sum_prop[of "\<lambda>i. 1 / (2 ^ i::real)" "n-3"] n_geq_4 
    by (smt (verit, del_insts) Nat.add_diff_assoc2 add_numeral_left diff_cancel2 le_add_diff_inverse le_numeral_extra(4) nat_1_add_1 nat_add_left_cancel_le numeral_Bit1 numerals(1) semiring_norm(2) semiring_norm(8) trans_le_add1)
  have "x' \<ge> (\<Sum>i = 1..?k. 1 / 2 ^ i)"
    using assms by presburger
  then have x_geq: "x \<ge> (\<Sum>i \<in> {1..n-2}. 1/(2^i))"
    using assms(5)  sum_upto 
    by linarith
  have "x' \<le> (\<Sum>i = 1..n - 2. 1 / 2 ^ i)"
    using assms(4) by auto
  then have x_leq: "x \<le> 1"
    using assms(5) 
    by (smt (verit, del_insts) add.left_commute add_diff_cancel_left' diff_diff_eq le_add_diff_inverse2 le_numeral_extra(4) n_geq_4 nat_add_1_add_1 numeral_Bit0 numeral_Bit1 sum_upto summation_helper trans_le_add2)
  show "x \<in> {(\<Sum>i \<in> {1..n-2}. 1/(2^i))..1}"
    using  x_geq x_leq 
    by auto
  then have px: "p x = (linepath (vts ! (n-2)) (vts ! (n-1))) (?f x)"
    using polygon_linepath_images3[of n vts p x ?f] n_geq_4 assms polygon_of_def by fastforce
  moreover have "?vts' ! (n - 3) = vts ! (n-2)"
    using n_geq_4 assms(3) rotated_polygon_vertices_helper2 assms(1-3)
    unfolding polygon_of_def
    by (smt (verit) One_nat_def Suc_diff_Suc add.commute diff_is_0_eq diff_less dual_order.trans have_wraparound_vertex hd_conv_nth le_add_diff_inverse length_greater_0_conv linorder_not_le nat_1_add_1 not_add_less2 numeral_3_eq_3 plus_1_eq_Suc pos2 rotated_polygon_vertices_helper(1) same_len snoc_eq_iff_butlast)
  moreover have "?vts' ! (n - 2) = vts ! (n - 1)"
    using n_geq_4 assms(3) assms
    unfolding polygon_of_def
    by (metis closed_path_def list.size(3) not_numeral_le_zero polygon_def polygon_pathfinish polygon_pathstart rotated_polygon_vertices_helper(1) same_len)
  moreover have "?f' ?k x' = ?f x" using assms(4-5) n_geq_4 
    by (smt (verit, del_insts) One_nat_def Suc_diff_Suc Suc_eq_plus1 add_diff_cancel_right' add_numeral_left le_antisym linorder_not_le numeral_3_eq_3 numeral_code(2) numerals(1) semiring_norm(2) sum_upto trans_le_add2)
  ultimately show "p' x' = p x" using px p'x'
    by (smt (verit, ccfv_SIG) Nat.add_diff_assoc2 assms(5) diff_cancel2 le_add_diff_inverse le_add_diff_inverse2 le_numeral_extra(4) n_geq_4 nat_1_add_1 numeral_Bit0 numeral_Bit1 trans_le_add1)
qed


lemma polygon_rotation_t_translation2_strict:
  assumes "polygon_of p vts"
  assumes "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
    (is "p' = make_polygonal_path ?vts'")
  assumes "n = length vts"
  assumes "x' \<in> {(\<Sum>i \<in> {1..(n-3)}. 1/(2^i))..<(\<Sum>i \<in> {1..(n-2)}. 1/(2^i))}"
  assumes "x = x' + 1/(2^(n-2))"
  shows "x \<in> {(\<Sum>i \<in> {1..n-2}. 1/(2^i))..<1}"
        "p' x' = p x"
proof - 
 have n_geq_4: "n \<ge> 4" using polygon_vertices_length_at_least_4 assms 
   using polygon_of_def by blast
  have sum_prop: "\<And>i::nat. \<And>f::nat\<Rightarrow>real. ( \<Sum>i = 1..i. f i) +  f (i + 1) = (\<Sum>i = 1..i+1. f i)"
    by auto
 have sum_upto: "(\<Sum>i = 1..n - 3. 1 / (2 ^ i::real)) +  1 / 2 ^ (n - 2) = (\<Sum>i = 1..n - 2. 1 / (2 ^ i::real))"
    using sum_prop[of "\<lambda>i. 1 / (2 ^ i::real)" "n-3"] n_geq_4 
    by (smt (verit, del_insts) Nat.add_diff_assoc2 add_numeral_left diff_cancel2 le_add_diff_inverse le_numeral_extra(4) nat_1_add_1 nat_add_left_cancel_le numeral_Bit1 numerals(1) semiring_norm(2) semiring_norm(8) trans_le_add1)
  have x_geq: "x \<ge> (\<Sum>i \<in> {1..n-2}. 1/(2^i))"
     using assms(4) polygon_rotation_t_translation2[OF assms(1) assms(2) assms(3) _ assms(5)]
     by simp
  have "x' < (\<Sum>i = 1..n - 2. 1 / 2 ^ i)"
    using assms(4) by auto
  then have x_leq: "x < 1"
    using assms(5) 
    by (smt (verit, del_insts) add.left_commute add_diff_cancel_left' diff_diff_eq le_add_diff_inverse2 le_numeral_extra(4) n_geq_4 nat_add_1_add_1 numeral_Bit0 numeral_Bit1 sum_upto summation_helper trans_le_add2)
  show "x \<in> {(\<Sum>i \<in> {1..n-2}. 1/(2^i))..<1}"
    using x_geq x_leq by auto
  show "p' x' = p x"
    using assms(4) polygon_rotation_t_translation2[OF assms(1) assms(2) assms(3) _ assms(5)]
    by (meson atLeastAtMost_iff atLeastLessThan_iff less_eq_real_def)
qed

lemma polygon_rotation_t_translation3:
  assumes "polygon_of p vts"
  assumes "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
    (is "p' = make_polygonal_path ?vts'")
  assumes "x' \<in> {(\<Sum>i \<in> {1..n-2}. 1/(2^i))..1}"
  assumes "n = length vts"
  assumes "l = x' - (\<Sum>i \<in> {1..n-2}. 1/(2^i))"
  assumes "x = l * (2^(n-3))"
  shows "x \<in> {0..1/2}"
        "p' x' = p x"     
proof-
  let ?f = "(\<lambda>x::real. (x - (\<Sum>i \<in> {1..n-2}. 1/(2^i))) * (2^(n-2)))"
  have n_geq_4: "n \<ge> 4" using polygon_vertices_length_at_least_4 assms 
    using polygon_of_def by blast
  moreover then have same_len: "length vts = length ?vts'"
    using assms rotate_polygon_vertices_same_length by auto
  moreover have length_vts': "length ?vts' = n" 
    using assms(4) same_len by auto
  ultimately have p'x': "p' x' = (linepath (?vts' ! (n-2)) (?vts' ! (n-1))) (?f x')"
    using polygon_linepath_images3[of n ?vts' p' x' ?f] assms
    unfolding polygon_of_def by fastforce

  have x_is: "x = (x' - (\<Sum>i = 1..n - 2. 1 / 2 ^ i)) * 2 ^ (n - 3)"
    using assms(5-6) by auto
  then  have x_gt: "x \<ge> 0"
    using assms(3) by simp
  have sum_prop: "k \<ge> 1 \<Longrightarrow> 1 - (\<Sum>i = 1..k. 1 / (2 ^ i::real)) = 1/(2^k)" for k
  proof (induct k)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    { assume * :"Suc k = 1"
      then have ?case by auto
    } moreover
    { assume *: "Suc k > 1"
      then have " 1 - (\<Sum>i = 1..k. 1 / (2 ^ i::real)) = 1 / 2 ^ k"
        using Suc by linarith
      then have ?case by simp
    }
    ultimately show ?case
      by linarith 
  qed
  have "x' \<le> 1"
    using assms(3) by auto
  then have "x \<le> (1 - (\<Sum>i = 1..n - 2. 1 / (2 ^ i::real))) * 2 ^ (n - 3)"
    using x_is 
    using mult_right_mono zero_le_power by fastforce
  then have "x \<le> 1/(2^(n-2))*2^(n-3)"
    using sum_prop n_geq_4 
    by auto
  then have x_lt: "x \<le> 1/2"
    using n_geq_4 
    by (smt (verit, ccfv_SIG) One_nat_def Suc_1 Suc_diff_Suc add_diff_cancel_right' diff_is_0_eq dual_order.trans linorder_not_le nonzero_mult_divide_mult_cancel_right2 numeral_3_eq_3 numeral_code(2) power.simps(2) power_commutes power_not_zero times_divide_eq_left zero_neq_numeral)
  then show "x \<in> {0..1/2}" 
    using x_gt x_lt by auto
  moreover have "n \<ge> 3" using n_geq_4 by auto
  ultimately have px: "p x = (linepath (vts ! 0) (vts ! 1)) (2 * x)"
    using polygon_linepath_images1[of n vts] assms unfolding polygon_of_def by blast

  have "?vts' ! (n-2) = vts ! 0 \<and> ?vts' ! (n-1) = vts ! 1"
    unfolding rotate_polygon_vertices_def
    by (metis length_vts' assms(1) polygon_of_def rotate_polygon_vertices_def rotated_polygon_vertices_helper(1) rotated_polygon_vertices_helper(2))
  moreover have "?f x' = 2 * x"
  proof-
    have "2 * x = 2 * (x' - (\<Sum>i \<in> {1..n-2}. 1/(2^i))) * (2^(n-3))" using assms by auto
    moreover have "... = (x' - (\<Sum>i \<in> {1..n-2}. 1/(2^i))) * (2^(n-2))"
      using n_geq_4 Suc_1 Suc_diff_Suc Suc_le_eq bot_nat_0.not_eq_extremum diff_Suc_1 le_antisym mult.left_commute mult.right_neutral mult_cancel_left not_less_eq_eq num_double numeral_3_eq_3 numeral_eq_Suc numeral_times_numeral power.simps(2) pred_numeral_simps(2) zero_less_diff zero_neq_numeral
    proof -
      have f1: "\<forall>r ra. (ra::real) * r = r * ra"
        by simp
      have f2: "\<forall>r n ra. (r::real) * (r ^ n * ra) = r ^ Suc n * ra"
        by simp
      have f3: "pred_numeral (num.Bit1 num.One) = Suc (Suc 0)"
        by simp
      have f4: "Suc 0 = 1"
        by linarith
      have "Suc 1 < n"
        using n_geq_4 by linarith
      then have "2 * ((x' - (\<Sum>n = 1..n - Suc 1. 1 / 2 ^ n)) * 2 ^ (n - 3)) = (x' - (\<Sum>n = 1..n - Suc 1. 1 / 2 ^ n)) * 2 ^ (n - Suc 1)"
        using f4 f3 f2 f1 Suc_diff_Suc numeral_eq_Suc by presburger
      then show ?thesis
        by (metis (no_types) Suc_1 mult.assoc)
    qed
    moreover have "... = ?f x'" by auto
    ultimately show ?thesis by presburger
  qed
  ultimately show "p' x' = p x" using p'x' px by auto
qed

lemma polygon_rotation_t_translation3_strict:
  assumes "polygon_of p vts"
  assumes "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
    (is "p' = make_polygonal_path ?vts'")
  assumes "x' \<in> {(\<Sum>i \<in> {1..n-2}. 1/(2^i))..<1}"
  assumes "n = length vts"
  assumes "l = x' - (\<Sum>i \<in> {1..n-2}. 1/(2^i))"
  assumes "x = l * (2^(n-3))"
  shows "x \<in> {0..<1/2}"
        "p' x' = p x" 
proof -
  have n_geq_4: "n \<ge> 4" using polygon_vertices_length_at_least_4 assms 
    using polygon_of_def by blast
 have x_is: "x = (x' - (\<Sum>i = 1..n - 2. 1 / 2 ^ i)) * 2 ^ (n - 3)"
    using assms(5-6) by auto
  then  have x_gt: "x \<ge> 0"
    using assms(3) by simp
  have sum_prop: "k \<ge> 1 \<Longrightarrow> 1 - (\<Sum>i = 1..k. 1 / (2 ^ i::real)) = 1/(2^k)" for k
  proof (induct k)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    { assume * :"Suc k = 1"
      then have ?case by auto
    } moreover
    { assume *: "Suc k > 1"
      then have " 1 - (\<Sum>i = 1..k. 1 / (2 ^ i::real)) = 1 / 2 ^ k"
        using Suc by linarith
      then have ?case by simp
    }
    ultimately show ?case
      by linarith 
  qed
  have "x' < 1"
    using assms(3) by auto
  then have "x < (1 - (\<Sum>i = 1..n - 2. 1 / (2 ^ i::real))) * 2 ^ (n - 3)"
    using x_is 
    using mult_right_mono zero_le_power by fastforce
  then have "x < 1/(2^(n-2))*2^(n-3)"
    using sum_prop n_geq_4 
    by auto
  then have x_lt: "x < 1/2"
    using n_geq_4 
    by (smt (verit, ccfv_SIG) One_nat_def Suc_1 Suc_diff_Suc add_diff_cancel_right' diff_is_0_eq dual_order.trans linorder_not_le nonzero_mult_divide_mult_cancel_right2 numeral_3_eq_3 numeral_code(2) power.simps(2) power_commutes power_not_zero times_divide_eq_left zero_neq_numeral)
  show "x \<in> {0..<1/2}"
    using x_lt x_gt by auto
  show "p' x' = p x" 
    using assms(3) polygon_rotation_t_translation3[OF assms(1) assms(2)  _ assms(4) assms(5) assms(6)]
    by simp
qed

lemma f_gteq_0_sum_gt: "\<And>f::nat \<Rightarrow> real. (\<And>i::nat. (f i) > 0) \<Longrightarrow> a > b \<Longrightarrow> (\<Sum>i = 1..a. (f i)) > (\<Sum>i = 1..b. (f i))" for a b :: "nat"
  proof (induct a arbitrary: b)
    case 0
    then show ?case by auto
  next
    case (Suc a)
    {assume *: "b = a"
      then have "sum f {1..(Suc a)} = sum f {1.. b} + f (Suc a)"
        by force
      then have ?case
        using Suc(2)[of "Suc a"] * by linarith
    } moreover {assume *: "b < a"
      then have ?case using Suc
        by (smt (verit, ccfv_threshold) Suc_eq_plus1 dual_order.trans le_add2 sum.nat_ivl_Suc')
    }
    ultimately show ?case 
      using Suc.prems(2) less_antisym by blast
  qed

lemma rotation_intervals_disjoint:
  assumes "k1 \<noteq> k2"
  shows "{\<Sum>i = 1..k1. 1 / (2 ^ i::real)..<\<Sum>i = 1..k1+1. 1 / 2 ^ i} \<inter> {\<Sum>i = 1..k2. 1 / (2 ^ i::real)..<\<Sum>i = 1..k2+1. 1 / 2 ^ i} = {}"
proof - 
  have lambda_gt: "(\<And>i. 0 < 1 / (2 ^ i::real))"
    by simp
  have h1: ?thesis if *:"k1 < k2"
  proof - 
    have eo: "k1+1 \<le> k2"
      using * by auto
    have "k1+1 = k2 \<Longrightarrow> (\<Sum>i = 1..k1+1. 1 / 2 ^ i) \<le> (\<Sum>i = 1..k2. 1 / (2 ^ i::real))"
      by auto
    have "(\<Sum>i = 1..k1+1. 1 / 2 ^ i) \<le> (\<Sum>i = 1..k2. 1 / (2 ^ i::real))" if **: "k1+1 < k2"
      using f_gteq_0_sum_gt[OF lambda_gt **]
      using less_eq_real_def by presburger
    then have "(\<Sum>i = 1..k1+1. 1 / 2 ^ i) \<le> (\<Sum>i = 1..k2. 1 / (2 ^ i::real))"
      using * eo by fastforce
    then show ?thesis  by auto
  qed
  have h2: ?thesis if *: "k2 < k1"
      proof - 
    have eo: "k2+1 \<le> k1"
      using * by auto
    have "k2+1 = k1 \<Longrightarrow> (\<Sum>i = 1..k2+1. 1 / 2 ^ i) \<le> (\<Sum>i = 1..k1. 1 / (2 ^ i::real))"
      by auto
    have "(\<Sum>i = 1..k2+1. 1 / 2 ^ i) \<le> (\<Sum>i = 1..k1. 1 / (2 ^ i::real))" if **: "k2+1 < k1"
      using f_gteq_0_sum_gt[OF lambda_gt **]
      using less_eq_real_def by presburger
    then have "(\<Sum>i = 1..k2+1. 1 / 2 ^ i) \<le> (\<Sum>i = 1..k1. 1 / (2 ^ i::real))"
      using * eo by fastforce
    then show ?thesis  by auto
  qed
  show ?thesis 
    using h1 h2 assms by linarith
qed

lemma bounding_interval_helper1:
  shows "(\<Sum>i = 1..k. 1 / (2 ^ i::real)) = (2^k - 1)/(2^k)"
proof(induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have "(\<Sum>i = 1..(Suc k). 1 / (2 ^ i::real)) = (\<Sum>i = 1..k. 1 / (2 ^ i::real)) + 1/2^(Suc k)"
    by force
  also have "... = (2^k - 1)/(2^k) + 1/2^(Suc k)" using Suc.hyps by presburger
  also have "... = (2^k - 1)/(2^k) + 1/2^(k+1)" by simp
  also have "... = (2^(k+1) - 1)/(2^(k+1))"
    by (smt (verit, del_insts) Suc add.commute add_diff_cancel_right' add_divide_distrib calculation field_sum_of_halves le_add2 plus_1_eq_Suc power_divide power_one summation_helper)
  finally show ?case by force
qed

lemma bounding_interval_helper2:
  fixes x :: real
  assumes "x \<in> {0..<1}"
  shows "\<exists>k. x < (\<Sum>i = 1..k. 1 / (2 ^ i::real))"
proof-
  let ?f = "\<lambda>k::nat. (2^k - 1)/(2^k)"
  have lim: "\<forall>\<epsilon>::real>0. \<exists>k. (1 - (?f k)) < \<epsilon>"
  proof clarify
    fix \<epsilon>::real
    assume "\<epsilon> > 0"
    then obtain m where "m > 0 \<and> 1 / m < \<epsilon>"
      by (metis Groups.mult_ac(2) divide_less_eq linordered_field_no_ub order_less_trans zero_less_divide_1_iff)
    moreover obtain k where "2^k > m" using real_arch_pow by fastforce
    ultimately have "1 / (2^k) < \<epsilon>" by (smt (verit) frac_less2)
    moreover have "(1::real) - ((2^k - 1) / (2^k)) = (1/(2^k))" by (simp add: diff_divide_distrib)
    ultimately show "\<exists>k. 1 - (2^k - 1) / (2^k) < \<epsilon>" by (smt (verit))
  qed   
  have "\<exists>k. ?f k > x"
  proof-
    let ?\<epsilon> = "1 - x"
    obtain k where "1 - (?f k) < ?\<epsilon>" by (metis assms lim atLeastLessThan_iff diff_gt_0_iff_gt)
    thus ?thesis by auto
  qed
  thus ?thesis using bounding_interval_helper1 by presburger
qed

lemma bounding_interval_for_reals_btw01:
  fixes x::"real"
  assumes "x \<in> {0..<1}"
  shows "\<exists>k. x \<in> {(\<Sum>i \<in> {1..k}. 1/(2^i::real))..<(\<Sum>i \<in> {1..(k + 1)}. 1/(2^i))}"
proof - 
  let ?S = "\<lambda>k. (\<Sum>i = 1..k. 1 / (2 ^ i::real))"
  let ?A = "{k::nat. x < (\<Sum>i = 1..k. 1 / (2 ^ i::real))}"
  let ?m = "LEAST k. k \<in> ?A"
  have "\<exists>k. x < (\<Sum>i = 1..k. 1 / (2 ^ i::real))" using assms bounding_interval_helper2 by blast
  then have "?m \<in> ?A" by (metis (mono_tags, lifting) LeastI2_wellorder mem_Collect_eq)
  moreover then have "?m - 1 \<notin> ?A"
    by (smt (verit, ccfv_SIG) One_nat_def Suc_n_not_le_n Suc_pred' assms atLeastLessThan_iff atLeastatMost_empty' bot_nat_0.not_eq_extremum linorder_not_less mem_Collect_eq not_less_Least sum.empty)
  ultimately have "x < (\<Sum>i = 1..?m. 1 / (2 ^ i::real)) \<and> x \<ge> (\<Sum>i = 1..?m-1. 1 / (2 ^ i::real))"
    by simp
  thus ?thesis
    by (smt (verit, best) add.commute assms atLeastLessThan_iff le_add_diff_inverse linorder_not_less sum.head_if)
qed

lemma all_rotation_intervals_between_0and1:
  shows "{(\<Sum>i \<in> {1..k}. 1/(2^i::real))..(\<Sum>i \<in> {1..(k+1)}. 1/(2^i))} \<subseteq> {0..<1}"
proof - 
  have gt: "\<And>k. (\<Sum>i \<in> {1..k}. 1/(2^i::real)) \<ge> 0"
    by (simp add: sum_nonneg)
  have lt: "\<And>k. (\<Sum>i \<in> {1..k}. 1/(2^i::real)) < 1"
    by (smt (verit, ccfv_SIG) diff_Suc_1 f_gteq_0_sum_gt less_Suc_eq_le linorder_not_le summation_helper zero_less_divide_1_iff zero_less_power)
  show ?thesis
    using gt lt 
    by (meson atLeastAtMost_subseteq_atLeastLessThan_iff)
qed

lemma all_rotation_intervals_between_0and1_strict:
  shows "{(\<Sum>i \<in> {1..k}. 1/(2^i::real))..<(\<Sum>i \<in> {1..(k+1)}. 1/(2^i))} \<subseteq> {0..<1}"
  using all_rotation_intervals_between_0and1
  by (smt (verit, ccfv_SIG) atLeastAtMost_subseteq_atLeastLessThan_iff ivl_subset nle_le order_trans)

lemma one_polygon_rotation_is_loop_free:
  assumes "polygon_of p vts"
  assumes "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
    (is "p' = make_polygonal_path ?vts'")
  shows "loop_free p'"
proof(rule ccontr)
  assume "\<not> loop_free p'"
  moreover have "p' 0 = p' 1"
    using assms 
    by (smt (verit, ccfv_SIG) assms(2) butlast_snoc length_butlast linepath_0' linepath_1' make_polygonal_path.simps(1) not_gr_zero nth_append_length nth_butlast path_defs(2) path_defs(3) polygon_pathfinish polygon_pathstart rotate_polygon_vertices_def)
  ultimately obtain x' y' where x'y': "x' < y' \<and> {x', y'} \<subseteq> {0..<1} \<and> p' x' = p' y'"
    unfolding loop_free_def
    by (smt (verit, del_insts) atLeastAtMost_iff atLeastLessThan_iff bot_least insert_subset linorder_not_le order.refl order_antisym zero_less_one)

  let ?n = "length vts"
  have n_geq_4: "?n \<ge> 4" using polygon_vertices_length_at_least_4 assms 
    using polygon_of_def by blast
  obtain xk where x'_in: "x' \<in> {(\<Sum>i \<in> {1..xk}. 1/(2^i))..<(\<Sum>i \<in> {1..(xk + 1)}. 1/(2^i))}" using x'y'
    using bounding_interval_for_reals_btw01 x'y'
    by (metis insert_subset )
  then have xk_gteq: "xk \<ge> 0"
    by blast
  obtain yk where y'_in: "y' \<in> {(\<Sum>i \<in> {1..yk}. 1/(2^i))..<(\<Sum>i \<in> {1..(yk + 1)}. 1/(2^i))}"
     using bounding_interval_for_reals_btw01 x'y'
    by (metis insert_subset)
  then have yk_gteq: "yk \<ge> 0"
    by blast

  have all_pows_of_2_pos: "(\<And>i. 0 < 1 / (2 ^ i::real))"
    by simp

  (* Use all of the polygon_rotation_t_translation helper lemmas *)
  let ?x1 = "(x' - (\<Sum>i \<in> {1..xk}. 1/(2^i)))/2 + (\<Sum>i \<in> {1..(xk + 1)}. 1/(2^i))"
  have xk_lt_nminus3: "xk \<le> ?n - 4 \<Longrightarrow> ?x1 \<in> {(\<Sum>i \<in> {1..xk+1}. 1/(2^i))..<(\<Sum>i \<in> {1..xk+2}. 1/(2^i))} \<and> p ?x1 = p' x'"
    using polygon_rotation_t_translation1_strict[OF assms(1) assms(2) x'_in] xk_gteq
    by metis
  let ?y1 = "(y' - (\<Sum>i \<in> {1..yk}. 1/(2^i)))/2 + (\<Sum>i \<in> {1..(yk + 1)}. 1/(2^i))"
  have yk_lt_nminus3: "yk \<le> ?n - 4 \<Longrightarrow> ?y1 \<in> {(\<Sum>i \<in> {1..yk+1}. 1/(2^i))..<(\<Sum>i \<in> {1..yk+2}. 1/(2^i))} \<and> p ?y1 = p' y'"
    using polygon_rotation_t_translation1_strict[OF assms(1) assms(2) y'_in] yk_gteq 
    by metis

  let ?x2 = "x' + 1/(2^(?n-2))"
  have "xk = ?n-3 \<Longrightarrow> x' \<in> {\<Sum>i = 1..length vts - 3. 1 / (2 ^ i::real)..<\<Sum>i = 1..length vts - 2. 1 / 2 ^ i}"
    using x'_in 
    by (smt (verit, best) Nat.add_diff_assoc2 \<open>4 \<le> length vts\<close> diff_cancel2 le_add_diff_inverse nat_add_left_cancel_le nat_le_linear numeral_Bit0 numeral_Bit1 numerals(1) trans_le_add1)
  then have xk_eq_nminus3: "xk = ?n - 3 \<Longrightarrow> p ?x2 = p' x' \<and> ?x2 \<in> {(\<Sum>i \<in> {1..?n-2}. 1/(2^i))..<1}"
    using polygon_rotation_t_translation2_strict[OF assms(1) assms(2), of ?n "x'" ?x2] x'_in xk_gteq 
    by presburger
  let ?y2 = "y' + 1/(2^(?n-2))"
  have "yk = ?n-3 \<Longrightarrow> y' \<in> {\<Sum>i = 1..length vts - 3. 1 / (2 ^ i::real)..<\<Sum>i = 1..length vts - 2. 1 / 2 ^ i}"
    using y'_in 
    by (smt (verit, best) Nat.add_diff_assoc2 \<open>4 \<le> length vts\<close> diff_cancel2 le_add_diff_inverse nat_add_left_cancel_le nat_le_linear numeral_Bit0 numeral_Bit1 numerals(1) trans_le_add1)
  then have yk_eq_nminus3: "yk = ?n - 3 \<Longrightarrow> p ?y2 = p' y' \<and> ?y2 \<in> {(\<Sum>i \<in> {1..?n-2}. 1/(2^i))..<1}"
    using polygon_rotation_t_translation2_strict[OF assms(1) assms(2), of ?n "y'" ?y2] x'_in xk_gteq 
    by presburger
 
  let ?x3 = "(x' - (\<Sum>i \<in> {1..?n-2}. 1/(2^i)))*(2^(?n-3))"
  have x'_leq: "x' < 1"
    using x'y' by simp
  have x'_geq: "xk \<ge> ?n - 2 \<Longrightarrow> (\<Sum>i = 1..xk. 1 / (2 ^ i::real)) \<ge> (\<Sum>i = 1..length vts - 2. 1 / (2 ^ i::real))"
    using x'_in f_gteq_0_sum_gt[of "\<lambda>i.  1 / (2 ^ i::real)"]  
    by (metis le_antisym less_eq_real_def linorder_not_le zero_less_divide_1_iff zero_less_numeral zero_less_power)
   have "xk \<ge> ?n-2 \<Longrightarrow> x' \<in> {\<Sum>i = 1..length vts - 2. 1 / (2 ^ i::real)..<1}"
     using x'_leq x'_geq x'_in 
     by fastforce
  then have xk_gt_nminus3: "xk \<ge> ?n - 2 \<Longrightarrow> p ?x3 = p' x' \<and> ?x3 \<in> {0..<1/2}"
    using polygon_rotation_t_translation3_strict[OF assms(1) assms(2), of x' ?n]  xk_gteq 
    by presburger
  let ?y3 = "(y' - (\<Sum>i \<in> {1..?n-2}. 1/(2^i)))*(2^(?n-3))"
  have y'_leq: "y' < 1"
    using x'y' by simp
  have y'_geq: "yk \<ge> ?n - 2 \<Longrightarrow> (\<Sum>i = 1..yk. 1 / (2 ^ i::real)) \<ge> (\<Sum>i = 1..length vts - 2. 1 / (2 ^ i::real))"
    using y'_in f_gteq_0_sum_gt[of "\<lambda>i.  1 / (2 ^ i::real)"] 
    by (metis le_antisym less_eq_real_def linorder_not_le zero_less_divide_1_iff zero_less_numeral zero_less_power)
   have "yk \<ge> ?n-2 \<Longrightarrow> y' \<in> {\<Sum>i = 1..length vts - 2. 1 / (2 ^ i::real)..<1}"
     using y'_leq y'_geq y'_in 
     by fastforce
  then have yk_gt_nminus3: "yk \<ge> ?n - 2 \<Longrightarrow> p ?y3 = p' y' \<and> ?y3 \<in> {0..<1/2}"
    using polygon_rotation_t_translation3_strict[OF assms(1) assms(2), of y' ?n]  yk_gteq 
    by presburger

  have interval_helper: "a1 \<ge> b2 \<and>x \<in> {a1..<a2} \<and> y \<in> {b1..<b2} \<Longrightarrow> y < x" for a1 a2 b1 b2 x y::"real"
    by simp

  { assume xk_lt: "xk < ?n - 3" (* x not in last two intervals: has 3 subcases *)
    then have p_x': "p ?x1 = p' x'"
      using xk_lt_nminus3 by auto
    have x1_in: "?x1 \<in> {(\<Sum>i \<in> {1..(xk + 1)}. 1/(2^i))..<(\<Sum>i \<in> {1..(xk + 2)}. 1/(2^i))}"
      using xk_lt xk_lt_nminus3 
      by auto
   then have x1_in_01: "?x1 \<in> {0..<1}"
        using all_rotation_intervals_between_0and1_strict[of "xk+1"]
        by fastforce
    { assume yk_lt: "yk < ?n - 3" (* First subcase *)
      then have p_y': "p ?y1 = p' y'"
        using yk_lt_nminus3 by auto
      have y1_in: "?y1 \<in> {(\<Sum>i \<in> {1..(yk + 1)}. 1/(2^i))..<(\<Sum>i \<in> {1..(yk + 2)}. 1/(2^i))}"
        using yk_lt  yk_lt_nminus3 by auto
      then have y1_in_01: "?y1 \<in> {0..<1}"
        using all_rotation_intervals_between_0and1_strict[of "yk+1"]
        by fastforce
      have "{\<Sum>i = 1..xk + 1. 1 / 2 ^ i..<\<Sum>i = 1..xk + 2. 1 / (2 ^ i::real)} \<inter> {\<Sum>i = 1..yk + 1. 1 / (2 ^ i::real)..<\<Sum>i = 1..yk + 2. 1 / 2 ^ i} = {}" if xk_neq:"xk \<noteq> yk" 
        using rotation_intervals_disjoint[of "xk+1" "yk+1"] xk_neq 
        by fastforce
      then have eq_then_eq: "?x1 = ?y1 \<Longrightarrow> xk = yk"
        using x1_in y1_in  
        by (smt (verit) Int_iff empty_iff)
      have "xk = yk \<Longrightarrow> ?x1 \<noteq> ?y1"
        using x'y' x1_in y1_in by simp
      then have "?x1 \<noteq> ?y1"
        using eq_then_eq by blast
      moreover have "{?x1, ?y1} \<subseteq> {0..<1}"
        using x1_in_01 y1_in_01 by fast
     ultimately have " ?x1 \<noteq> ?y1 \<and> {?x1, ?y1} \<subseteq> {0..<1} \<and> p ?x1 = p ?y1"
        using  p_x' p_y'  x'y' by presburger
      then have "\<exists> x y . x \<noteq> y \<and> {x, y} \<subseteq> {0..<1} \<and> p x = p y"
        by auto
    then have "False"
      using assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
      by fastforce
  } moreover { assume "yk = ?n - 3" (* Second subcase *)
    then have y2: "p ?y2 = p' y' \<and> ?y2 \<in> {(\<Sum>i \<in> {1..?n-2}. 1/(2^i))..<1}"
      using yk_eq_nminus3
      by auto
    then have y2_in_01: "?y2 \<in> {0..<1}"
        using all_rotation_intervals_between_0and1_strict[of "?n-2"]
        by fastforce
    have xkplus_eq: "xk + 2 = ?n - 2 \<Longrightarrow> (\<Sum>i \<in> {1..(xk + 2)}. 1/(2^i::real)) \<le> (\<Sum>i \<in> {1..?n-2}. 1/(2^i))"
      by simp
    have xkplus_lt: "xk + 2 < ?n - 2 \<Longrightarrow> (\<Sum>i \<in> {1..(xk + 2)}. 1/(2^i::real)) \<le> (\<Sum>i \<in> {1..?n-2}. 1/(2^i))"
     using xk_lt f_gteq_0_sum_gt[OF all_pows_of_2_pos, of "xk + 2" "?n - 2"]
     by (smt (verit, best) f_gteq_0_sum_gt zero_less_divide_1_iff zero_less_power)
    then have "(\<Sum>i \<in> {1..(xk + 2)}. 1/(2^i::real)) \<le> (\<Sum>i \<in> {1..?n-2}. 1/(2^i))"
      using xkplus_eq xkplus_lt xk_lt 
      using One_nat_def Suc_diff_Suc Suc_eq_plus1 Suc_le_eq add_Suc_right le_neq_implies_less linorder_not_le nat_1_add_1 nat_diff_split numeral_3_eq_3 xk_gteq by linarith
    then have "?x1 \<noteq> ?y2"
      using x1_in y2 
      by (smt (verit, ccfv_SIG) interval_helper)
    moreover have "{?x1, ?y2} \<subseteq> {0..<1}"
        using x1_in_01 y2_in_01 by fast
     ultimately have " ?x1 \<noteq> ?y2 \<and> {?x1, ?y2} \<subseteq> {0..<1} \<and> p ?x1 = p ?y2"
        using  p_x' y2  x'y' by presburger
      then have "\<exists> x y . x \<noteq> y \<and> {x, y} \<subseteq> {0..<1} \<and> p x = p y"
        by auto
      then have False 
        using assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
        by fastforce
    }
    moreover { assume "yk > ?n - 3" (* Third subcase *)
      then have y3: "p ?y3 = p' y' \<and> ?y3 \<in> {0..<(1/2::real)}"
      using yk_gt_nminus3 
      by auto
    then have y3_in_01: "?y3 \<in> {0..<1}"
      by simp

    have simplify_interval: "(\<Sum>i = 1..1. 1 / (2 ^ i::real)) = 1/2"
      by simp
    then have xk_eq_0: "xk = 0 \<Longrightarrow> (\<Sum>i \<in> {1..(xk + 1)}. 1/(2^i::real)) \<ge> 1/2"
      by simp
    have "xk > 0 \<Longrightarrow> (\<Sum>i \<in> {1..(xk + 1)}. 1/(2^i::real)) \<ge> 1/2"
        using f_gteq_0_sum_gt[OF all_pows_of_2_pos, of "1" "xk +1"] 
        simplify_interval 
        by (smt (verit, ccfv_SIG) Suc_le_eq add.commute add.right_neutral all_pows_of_2_pos f_gteq_0_sum_gt linorder_not_le plus_1_eq_Suc)
    then have "(\<Sum>i \<in> {1..(xk + 1)}. 1/(2^i::real)) \<ge> 1/2"
      using xk_eq_0 xk_gteq by blast
    then have "?x1 \<noteq> ?y3"
      using x1_in y3  
      by (smt (verit, best) interval_helper)
    moreover have "{?x1, ?y3} \<subseteq> {0..<1}"
        using x1_in_01 y3_in_01 by fast
     ultimately have " ?x1 \<noteq> ?y3 \<and> {?x1, ?y3} \<subseteq> {0..<1} \<and> p ?x1 = p ?y3"
       using  p_x' y3  x'y' 
       by presburger
      then have "\<exists> x y . x \<noteq> y \<and> {x, y} \<subseteq> {0..<1} \<and> p x = p y"
        by auto
      then have False 
        using assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
        by fastforce
    }
    ultimately have False by linarith
  } moreover {assume xk_eq : "xk = ?n-3" (* Next big case: when xk = ?n - 3, has 3 subcases*)
    then have p_x': "p ?x2 = p' x'"
      using xk_eq_nminus3 by auto
    have x2_in: "?x2 \<in> {(\<Sum>i \<in> {1..?n-2}. 1/(2^i))..<1}"
      using xk_eq xk_eq_nminus3 
      by auto
    then have "?x2 \<ge> 0"
      using n_geq_4 
      by (metis add_sign_intros(4) atLeastLessThan_iff insert_subset leD nle_le power_one_over x'y' zero_le_power zero_less_divide_1_iff zero_less_numeral)
    then have x2_in_01: "?x2 \<in> {0..<1}"
      using x2_in by auto
    { assume "yk < ?n - 3" (* First subcase *)
      then have interval_helper_helper: "(\<Sum>i = 1..yk + 1. 1 / (2 ^ i::real)) \<le> (\<Sum>i = 1..xk. 1 / (2 ^ i::real))"
        using xk_eq f_gteq_0_sum_gt 
        by (metis Suc_eq_plus1 less_eq_real_def linorder_neqE_nat not_less_eq zero_less_divide_1_iff zero_less_numeral zero_less_power)
      then have "x' > y'"
        using x'_in y'_in  interval_helper[of "(\<Sum>i = 1..yk + 1. 1 / (2 ^ i::real))" "(\<Sum>i = 1..xk. 1 / (2 ^ i::real))"] 
        by blast
      then have False using x'y' 
        by auto
    } moreover { assume "yk = ?n - 3"  (* Second subcase *)
      then have y2: "p ?y2 = p' y' \<and> ?y2 \<in> {(\<Sum>i \<in> {1..?n-2}. 1/(2^i))..<1}"
      using yk_eq_nminus3
      by auto
    then have y2_in_01: "?y2 \<in> {0..<1}"
        using all_rotation_intervals_between_0and1_strict[of "?n-2"]
        by fastforce
      then have "?x2 \<noteq> ?y2"
        using x'y' by auto
    moreover have "{?x2, ?y2} \<subseteq> {0..<1}"
        using x2_in_01 y2_in_01 by fast
     ultimately have " ?x2 \<noteq> ?y2 \<and> {?x2, ?y2} \<subseteq> {0..<1} \<and> p ?x2 = p ?y2"
        using  p_x' y2  x'y' by presburger
      then have "\<exists> x y . x \<noteq> y \<and> {x, y} \<subseteq> {0..<1} \<and> p x = p y"
        by meson
      then have False 
        using assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
        by fastforce
    } moreover { assume yk_gt: "yk > ?n - 3" (* Third subcase *)
    then have y3: "p ?y3 = p' y'"
      using yk_gt_nminus3 by auto
    have y3_in: "?y3 \<in> {0..<1/2}"
      using yk_gt yk_gt_nminus3 
      by auto
    then have y3_in_01: "?y3 \<in> {0..<1}"
      by auto
    have   "(\<Sum>i = 1..length vts - 2. 1 / (2 ^ i::real)) > (\<Sum>i = 1..1. 1 / (2 ^ i::real))"
      using n_geq_4 f_gteq_0_sum_gt[OF all_pows_of_2_pos,of 1 "length vts - 2"]
      by fastforce
    then have "(\<Sum>i = 1..length vts - 2. 1 / (2 ^ i::real)) > 1/2"
      by simp
    then have "?x2 \<noteq> ?y3"
      using y3_in x2_in by auto
    moreover have "{?x2, ?y3} \<subseteq> {0..<1}"
        using x2_in_01 y3_in_01 by fast
     ultimately have " ?x2 \<noteq> ?y3 \<and> {?x2, ?y3} \<subseteq> {0..<1} \<and> p ?x2 = p ?y3"
       using  p_x' y3  x'y' by presburger
      then have "\<exists> x y . x \<noteq> y \<and> {x, y} \<subseteq> {0..<1} \<and> p x = p y"
        by meson
      then have False 
        using assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
        by fastforce
    }
    ultimately have False
      using not_less_iff_gr_or_eq by auto
  } moreover { assume xk_gt:  "xk > ?n - 3" (* Last big case: x in last interval, has 2 subcases *)
    then have p_x': "p ?x3 = p' x'"
      using xk_gt_nminus3 by auto
    have x3_in: "?x3 \<in> {0..<1/2}"
      using xk_gt xk_gt_nminus3 
      by auto
    then have x3_in_01: "?x3 \<in> {0..<1}"
      by auto
    { assume "yk \<le> ?n - 3" (* First subcase *)
      then have "(\<Sum>i = 1..xk. 1 / (2 ^ i::real)) \<ge> (\<Sum>i = 1..yk + 1. 1 / (2 ^ i::real))"
        using xk_gt f_gteq_0_sum_gt[of "\<lambda>i.  1 / (2 ^ i::real)" xk yk]
      proof -
        obtain rr :: "nat \<Rightarrow> real" where
          f1: "\<forall>B_x. rr B_x = 1 / 2 ^ B_x"
          by force
        then have f2: "\<forall>n. 0 < rr n"
          by simp
        have "yk < xk"
          using \<open>length vts - 3 < xk\<close> \<open>yk \<le> length vts - 3\<close> order_le_less_trans by blast
        then show ?thesis
          using f2 f1 by (metis (no_types) Suc_eq_plus1 f_gteq_0_sum_gt less_eq_real_def nat_neq_iff not_less_eq order.refl)
      qed
      then have "x' > y'"
        using x'_in y'_in interval_helper[of "(\<Sum>i = 1..yk + 1. 1 / (2 ^ i::real))" "(\<Sum>i = 1..xk. 1 / (2 ^ i::real))"]
        by blast
      then have False using x'y' 
        by auto
    } moreover
    { assume yk_gt: "yk > ?n - 3" (* Second subcase *)
      then have p_y': "p ?y3 = p' y'"
        using yk_gt_nminus3 by auto
      have y3_in: "?y3 \<in> {0..<1/2}"
        using yk_gt yk_gt_nminus3 
        by auto
      then have y3_in_01: "?y3 \<in> {0..<1}"
        by auto
      have "(x' - (\<Sum>i = 1..length vts - 2. 1 / 2 ^ i)) \<noteq>
          (y' - (\<Sum>i = 1..length vts - 2. 1 / 2 ^ i))"
        using x'y' by auto
      then have "?x3 \<noteq> ?y3" by auto
      moreover have "{?x3, ?y3} \<subseteq> {0..<1}"
        using x3_in_01 y3_in_01 by fast
      ultimately have " ?x3 \<noteq> ?y3 \<and> {?x3, ?y3} \<subseteq> {0..<1} \<and> p ?x3 = p ?y3"
        using  p_x' p_y'  x'y' 
        by presburger
      then have "\<exists> x y . x \<noteq> y \<and> {x, y} \<subseteq> {0..<1} \<and> p x = p y"
        by meson
      then have False 
        using assms(1) unfolding polygon_of_def polygon_def simple_path_def loop_free_def
        by fastforce
    }
    ultimately have False by linarith
  }
  ultimately show False by linarith
qed

lemma one_rotation_is_polygon:
  fixes p :: "R_to_R2"
  fixes i :: "nat"
  assumes poly_p: "polygon p" and
          p_is_path: "p = make_polygonal_path vts" and
          p'_is: "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
            (is "p' = make_polygonal_path ?vts'")
  shows "polygon p'"
proof-
  have "polygonal_path p'" using p'_is by (simp add: polygonal_path_def)
  moreover have "closed_path p'"
    using p'_is unfolding rotate_polygon_vertices_def closed_path_def
    by (metis (no_types, opaque_lifting) Nil_is_append_conv append_self_conv2 diff_Suc_1 hd_append2 hd_conv_nth length_append_singleton make_polygonal_path_gives_path not_Cons_self nth_Cons_0 nth_append_length pathfinish_def pathstart_def polygon_pathfinish polygon_pathstart)
  moreover have "simple_path p'"
    using one_polygon_rotation_is_loop_free
    by (metis make_polygonal_path_gives_path p'_is p_is_path poly_p polygon_of_def simple_path_def)
  ultimately show ?thesis unfolding polygon_def by simp
qed

lemma rotation_is_polygon:
  fixes p :: "R_to_R2"
  fixes i:: "nat"
  assumes "polygon p" and
          "p = make_polygonal_path vts" 
  shows "polygon (make_polygonal_path (rotate_polygon_vertices vts i))"
  using assms
proof (induct i)
  case 0
  then show ?case using rotate0 unfolding rotate_polygon_vertices_def 
    by (smt (z3) assms(2) butlast.simps(1) butlast_conv_take eq_id_iff have_wraparound_vertex hd_append2 hd_conv_nth rotate_polygon_vertices_def rotate_polygon_vertices_same_set self_append_conv2 the_elem_set)
next
  case (Suc i)
  then show ?case using one_rotation_is_polygon arb_rotation_as_single_rotation 
    by metis
qed

lemma polygon_rotate_mod:
  fixes vts :: "(real^2) list"
  assumes "n = length vts"
  assumes "n \<ge> 2"
  assumes "hd vts = last vts"
  shows "rotate_polygon_vertices vts (n - 1) = vts"
proof-
  let ?vts' = "rotate (n - 1) (butlast vts)"
  have "rotate_polygon_vertices vts (n - 1) = ?vts' @ [?vts'!0]"
    unfolding rotate_polygon_vertices_def by metis
  moreover have "?vts' = butlast vts" using assms by simp
  moreover have "... = rotate 0 (butlast vts)" by simp
  moreover then have "... @ [...!0] = rotate_polygon_vertices vts 0"
    unfolding rotate_polygon_vertices_def by metis
  moreover have "... = vts"
    unfolding rotate_polygon_vertices_def using assms
    by (metis (no_types, lifting) Suc_le_eq calculation(3) hd_conv_nth length_butlast length_greater_0_conv nat_1_add_1 nth_butlast order_less_le_trans plus_1_eq_Suc pos2 snoc_eq_iff_butlast zero_less_diff)
  ultimately show ?thesis by argo
qed

lemma polygon_rotate_mod_arb:
  fixes vts :: "(real^2) list"
  assumes "n = length vts"
  assumes "n \<ge> 2"
  assumes "hd vts = last vts"
  shows "rotate_polygon_vertices vts ((n - 1) * i) = vts"
proof(induct i)
  case 0
  then show ?case using polygon_rotate_mod
    by (metis append.right_neutral append_Nil assms(1) assms(2) assms(3) id_apply length_butlast mult_zero_right rotate0 rotate_append rotate_polygon_vertices_def)
next
  case (Suc i)
  then have "vts = rotate_polygon_vertices vts ((n - 1) * i)" using Suc.prems by argo
  also have "... = rotate_polygon_vertices vts ((n - 1) * Suc i)"
    using polygon_rotate_mod assms(1) assms(2) assms(3) calculation rotation_sum
    by (metis mult_Suc_right)
  finally show ?case by argo
qed

lemma unrotation_is_polygon:
  fixes p :: "R_to_R2"
  fixes i:: "nat"
  assumes "polygon (make_polygonal_path (rotate_polygon_vertices vts i))"
            (is "polygon (make_polygonal_path ?vts')")
          "p = make_polygonal_path vts"
          "hd vts = last vts"
  shows "polygon p"
proof-
  have len_vts: "length vts \<ge> 2"
    using assms polygon_vertices_length_at_least_4 rotate_polygon_vertices_same_length
    by (metis (no_types, opaque_lifting) Suc_1 Suc_eq_numeral Suc_le_lessD diff_is_0_eq' eval_nat_numeral(2) gr_implies_not0 length_append_singleton length_butlast length_rotate not_less_eq_eq rotate_polygon_vertices_def)

  let ?n = "length vts - 1"
  obtain k where k: "k*?n > i"
    using len_vts
    by (metis Suc_1 Suc_le_eq add_0 div_less_iff_less_mult le_add2 less_diff_conv)
  let ?j = "k*?n - i"
  have j_i_n: "?j + i = k*?n" using k by simp

  have "rotate_polygon_vertices ?vts' ?j = rotate_polygon_vertices vts (?j + i)"
    using rotation_sum[of vts i ?n] by (simp add: add.commute rotation_sum)
  also have "... = rotate_polygon_vertices vts (k*?n)" using assms j_i_n by presburger
  also have "... = vts" using polygon_rotate_mod_arb len_vts assms by (metis mult.commute)
  finally show ?thesis using rotation_is_polygon assms by metis
qed

lemma rotated_polygon_vertices:
  assumes "vts' = rotate_polygon_vertices vts j"
  assumes "hd vts = last vts"
  assumes "length vts \<ge> 2"
  assumes "j \<le> i \<and> i < length vts"
  shows "vts ! i = vts' ! (i - j)"
  using assms
proof(induct j arbitrary: vts vts')
  case 0
  then show ?case
    by (metis Suc_1 Suc_le_eq diff_is_0_eq diff_zero hd_conv_nth id_apply length_butlast linorder_not_le list.size(3) nth_butlast rotate0 rotate_polygon_vertices_def snoc_eq_iff_butlast)
next
  case (Suc j)
  then have "vts' = rotate_polygon_vertices (rotate_polygon_vertices vts 1) j"
    by (metis plus_1_eq_Suc rotation_sum)
  moreover have "...!(i - Suc j) = (rotate_polygon_vertices vts 1)!(i - 1)"
    using Suc.hyps Suc.prems(3) Suc.prems(4) Suc_1 Suc_diff_le Suc_leD diff_Suc_Suc hd_conv_nth length_append_singleton length_butlast length_rotate nth_butlast rotate_polygon_vertices_def snoc_eq_iff_butlast zero_less_Suc
    by (smt (z3) One_nat_def Suc.prems(1) Suc.prems(2) Suc_eq_plus1 Suc_le_eq arb_rotation_as_single_rotation calculation diff_diff_cancel diff_is_0_eq diff_less_mono diff_zero not_less_eq_eq plus_1_eq_Suc rotated_polygon_vertices_helper2)
  moreover have "... = vts!i" using rotated_polygon_vertices_helper2
    by (metis Suc.prems(2) Suc.prems(3) Suc.prems(4) add_leD1 le_add_diff_inverse2 less_diff_conv plus_1_eq_Suc)
  ultimately show ?case
    by presburger
qed

lemma polygon_path_image:
  assumes poly_p: "polygon p"
  assumes p_is_path: "p = make_polygonal_path vts"
  shows "path_image p = p` {0 ..< 1}"
proof - 
  have vts_nonempty: "vts \<noteq> []"
    using polygon_at_least_3_vertices[OF poly_p p_is_path]
    by auto 
  have at_0: "p ` {0}  = {pathstart p}"
    using p_is_path 
    by (metis image_empty image_insert pathstart_def)
  have at_1: "p ` {1} = {pathfinish p}" 
    using p_is_path 
    by (simp add: pathfinish_def)
  have same_point: "p 0 = p 1"
    using assms unfolding polygon_def closed_path_def using polygon_pathstart[OF vts_nonempty p_is_path]
    using polygon_pathfinish[OF vts_nonempty p_is_path]
    at_0 at_1 by auto
  have "\<And>x. x \<in> p ` {0..1} \<Longrightarrow> x \<in> p ` {0..<1}"
  proof - 
    fix x
    assume "x \<in> p ` {0..1}"
    then have "\<exists>k \<in> {0..1}. p k = x"
      by auto 
    then obtain k where k_prop: "k \<in> {0..1} \<and> p k = x"
      by auto
    {assume *: "k < 1"
      then have "\<exists>k \<in> {0..<1}. p k = x"
        using k_prop by auto 
    } moreover {assume *: "k = 1"
      then have "p 0 = x"
        using same_point k_prop by auto 
      then have "\<exists>k \<in> {0..<1}. p k = x"
        by auto 
    }
    ultimately have "\<exists>k \<in> {0..<1}. p k = x"
      using k_prop 
      by (metis atLeastAtMost_iff order_less_le)
    then show "x \<in> p ` {0..<1}"
      by auto 
  qed
  then show ?thesis
    unfolding path_image_def by auto
qed

lemma polygon_vts_one_rotation:
  fixes p :: "R_to_R2"
  assumes poly_p: "polygon p" and
          p_is_path: "p = make_polygonal_path vts" and
          p'_is: "p' = make_polygonal_path (rotate_polygon_vertices vts 1)"
  shows "path_image p = path_image p'"
proof - 
  let ?rotated_vts = "(rotate_polygon_vertices vts 1)"
  have "card (set vts) \<ge> 3"
    using polygon_at_least_3_vertices[OF poly_p p_is_path]
    by auto
  then have len_gt_eq3: "length vts \<ge> 3"
    using card_length order_trans by blast
  have same_len: "length ?rotated_vts = length vts"
    unfolding rotate_polygon_vertices_def using length_rotate
    by (metis One_nat_def Suc_pred card.empty length_append_singleton length_butlast length_greater_0_conv list.set(1) not_numeral_le_zero p_is_path poly_p polygon_at_least_3_vertices)
  then have len_rotated_gt_eq2: "length ?rotated_vts \<ge> 2"
    using len_gt_eq3 by auto
  have h1: "\<And>x. x \<in> (path_image p) \<Longrightarrow> x \<in> path_image p'"
  proof - 
    fix x
    assume "x \<in> (path_image p)"
    then have "\<exists>k<length vts - 1. x \<in> path_image (linepath (vts ! k) (vts ! (k + 1)))"
      using p_is_path len_gt_eq3 make_polygonal_path_image_property[of vts x]
      by auto
    then obtain k where k_prop: "k < length vts - 1 \<and> x \<in> path_image (linepath (vts ! k) (vts ! (k + 1)))"
      by auto
    {assume *: "k = 0"
      have vts1: "vts ! 0 = ?rotated_vts ! (length ?rotated_vts - 2)"
        unfolding rotate_polygon_vertices_def 
        using nth_rotate[of "length ?rotated_vts - 2" "butlast vts" 1]
        by (metis (no_types, lifting) "*" One_nat_def Suc_pred butlast_snoc diff_diff_left k_prop length_butlast lessI mod_self nat_1_add_1 nth_butlast plus_1_eq_Suc rotate_polygon_vertices_def same_len)
      have "(rotate 1 (butlast vts)) ! 0 = vts ! 1"
        using nth_rotate[of 0 "butlast vts" 1] len_gt_eq3 
        by (simp add: less_diff_conv mod_if nth_butlast)
      then have vts2: "vts ! 1 = ?rotated_vts ! (length ?rotated_vts - 1)"
        unfolding rotate_polygon_vertices_def 
        by (metis butlast_snoc length_butlast nth_append_length)
      then have "path_image (linepath (vts ! k) (vts ! (k + 1))) \<subseteq> path_image p'"
        using linepaths_subset_make_polygonal_path_image[of vts 0]
        len_rotated_gt_eq2 * 
        by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_pred diff_diff_left diff_less k_prop less_numeral_extra(1) linepaths_subset_make_polygonal_path_image nat_1_add_1 p'_is same_len vts1)
      then have "x \<in> path_image p'"
        using k_prop vts1 vts2 
        by auto
    } 
    moreover {assume *: "k > 0"
      then have k_minus_prop: "k - 1 < length (rotate_polygon_vertices vts 1) - 1"
        using same_len  k_prop less_imp_diff_less 
        by presburger
      then have vts1: "vts ! k = ?rotated_vts ! (k-1)"
        using nth_rotate[of "k-1" "butlast vts" 1] len_gt_eq3 
        same_len 
        by (metis "*" One_nat_def Suc_pred butlast_snoc k_prop length_butlast mod_less nth_butlast plus_1_eq_Suc rotate_polygon_vertices_def)
      have vts2: "vts ! (k+1) = ?rotated_vts ! k"
        using nth_rotate[of "k" "butlast vts" 1] len_gt_eq3 k_minus_prop
        by (metis (no_types, lifting) "*" Suc_eq_plus1 Suc_leI butlast_snoc have_wraparound_vertex k_prop le_imp_less_Suc length_butlast mod_less mod_self nat_less_le nth_append_length nth_butlast p_is_path plus_1_eq_Suc poly_p rotate_polygon_vertices_def same_len)
      have "path_image (linepath (?rotated_vts ! (k-1)) (?rotated_vts ! k)) \<subseteq> path_image p'"
        using linepaths_subset_make_polygonal_path_image[OF len_rotated_gt_eq2 k_minus_prop] p'_is 
        by (simp add: "*")
      then have "x \<in> path_image p'"
        using k_prop vts1 vts2 
        by auto
    }
    ultimately show "x \<in> path_image p'"
      by auto
  qed
  have h2: "\<And>x. x \<in> (path_image p') \<Longrightarrow> x \<in> path_image p"
  proof - 
    fix x
    assume "x \<in> (path_image p')"
    then have "\<exists>k<length ?rotated_vts - 1. x \<in> path_image (linepath (?rotated_vts ! k) (?rotated_vts ! (k + 1)))"
      using p'_is len_rotated_gt_eq2 make_polygonal_path_image_property[of ?rotated_vts x]
      by auto
    then obtain k where k_prop: "k < length ?rotated_vts - 1 \<and> x \<in> path_image (linepath (?rotated_vts ! k) (?rotated_vts ! (k + 1)))"
      by auto
    {assume *: "k = length ?rotated_vts - 2"
      have vts1: "vts ! 0 = ?rotated_vts ! (length ?rotated_vts - 2)"
        unfolding rotate_polygon_vertices_def 
        using nth_rotate[of "length ?rotated_vts - 2" "butlast vts" 1] 
        by (metis "*" Suc_diff_Suc Suc_le_eq butlast_snoc k_prop len_rotated_gt_eq2 length_butlast mod_self nat_1_add_1 nth_butlast plus_1_eq_Suc rotate_polygon_vertices_def same_len zero_less_Suc)
      have "(rotate 1 (butlast vts)) ! 0 = vts ! 1"
        unfolding rotate_polygon_vertices_def 
        using nth_rotate[of 0 "butlast vts" 1] len_gt_eq3 len_rotated_gt_eq2
        by (metis (no_types, lifting) One_nat_def Suc_le_eq diff_diff_left length_butlast less_nat_zero_code mod_less not_gr_zero nth_butlast numeral_3_eq_3 plus_1_eq_Suc zero_less_diff)
      then have vts2: "?rotated_vts ! (k+1) = vts ! 1"
        unfolding rotate_polygon_vertices_def 
        by (metis "*" Suc_diff_Suc Suc_eq_plus1 Suc_le_eq len_rotated_gt_eq2 length_butlast length_rotate nat_1_add_1 nth_append_length same_len)
      have "path_image (linepath (vts ! 0) (vts ! 1)) \<subseteq> path_image p"
        using linepaths_subset_make_polygonal_path_image[of vts "0"]
        len_gt_eq3 * less_diff_conv p_is_path same_len 
        by auto
      then have "x \<in> path_image p"
        using * vts1 vts2 k_prop 
        by auto
    } moreover {assume *: "k < length ?rotated_vts - 2"
      then have vts1: "?rotated_vts ! k = vts ! (k+1)"
        using nth_rotate[of "k" "butlast vts" 1] len_gt_eq3 *
          same_len 
        by (smt (z3) Suc_eq_plus1 butlast_snoc diff_diff_left k_prop length_butlast less_diff_conv mod_less nat_1_add_1 nth_butlast plus_1_eq_Suc rotate_polygon_vertices_def)
      have vts2: "?rotated_vts ! (k+1) = vts ! (k+2)"
        using nth_rotate[of "k+1" "butlast vts" 1] len_gt_eq3 *
        by (smt (verit, ccfv_threshold) One_nat_def Suc_le_eq add_Suc_right butlast_snoc diff_diff_left have_wraparound_vertex len_rotated_gt_eq2 length_butlast less_diff_conv mod_less mod_self nat_1_add_1 nat_less_le nth_append_length nth_butlast p_is_path plus_1_eq_Suc poly_p rotate_polygon_vertices_def same_len)
      have "path_image (linepath (vts ! (k+1)) (vts ! (k + 2))) \<subseteq> path_image p"
        using linepaths_subset_make_polygonal_path_image[of vts "k+1"]
        len_gt_eq3 * less_diff_conv p_is_path same_len 
        by auto
      then have "x \<in> path_image p"
        using vts1 vts2 k_prop 
        by auto
    }
    ultimately show "x \<in> path_image p"
      using k_prop Suc_eq_plus1 add_le_imp_le_diff diff_diff_left len_rotated_gt_eq2 less_diff_conv2 linorder_neqE_nat not_less_eq one_add_one 
      by linarith
  qed
  then show ?thesis 
    using h1 h2 by auto  
qed

lemma polygon_vts_arb_rotation:
  fixes p :: "R_to_R2"
  assumes "polygon p" and
          "p = make_polygonal_path vts"
  shows "path_image p = path_image (make_polygonal_path (rotate_polygon_vertices vts i))"
  using assms
proof (induct i)
  case 0
  then show ?case unfolding rotate_polygon_vertices_def 
    by (metis One_nat_def arb_rotation_as_single_rotation polygon_vts_one_rotation rotate_polygon_vertices_def rotation_is_polygon)
next
  case (Suc i)
  let ?p' = "make_polygonal_path (rotate_polygon_vertices vts (Suc i))"
  {assume *: "i = 0"
    have "path_image p = path_image ?p'"
      using Suc polygon_vts_one_rotation[of p vts]
      by (simp add: "*")
  }
  moreover  {assume *: "i > 0"
    have "path_image p = path_image ?p'"
      using polygon_vts_one_rotation arb_rotation_as_single_rotation rotation_is_polygon 
      by (metis Suc.hyps Suc.prems(1) assms(2))
  }
  ultimately show ?case by auto 
qed 

section "Translating a Polygon"

lemma linepath_translation:
  "linepath ((\<lambda>x. x + u) a) ((\<lambda>x. x + u) b) = (\<lambda>x. x + u) \<circ> (linepath a b)"
proof-
  let ?l = "linepath ((\<lambda>x. x + u) a) ((\<lambda>x. x + u) b)"
  let ?l' = "(\<lambda>x. x + u) \<circ> (linepath a b)"
  have "?l x = ?l' x" for x
  proof-
    have "?l x = (1 - x) *\<^sub>R (a + u) + x *\<^sub>R (b + u)" unfolding linepath_def by simp
    also have "... = ((1 - x) *\<^sub>R a + x *\<^sub>R b) + u" by (simp add: scaleR_right_distrib)
    also have "... = ?l' x" unfolding linepath_def by simp
    finally show ?thesis .
  qed 
  thus ?thesis by fast
qed

lemma make_polygonal_path_translate:
  assumes "length vts \<ge> 2"
  shows "make_polygonal_path (map (\<lambda>x. x + u) vts) = (\<lambda>x. x + u) \<circ> (make_polygonal_path vts)"
  using assms
proof(induct "length vts" arbitrary: u vts)
  case 0
  then show ?case by presburger
next
  case (Suc n)
  let ?vts' = "map (\<lambda>x. x + u) vts"
  let ?p' = "make_polygonal_path ?vts'"
  { assume "Suc n = 2"
    then obtain a b where ab: "vts = [a, b]"
      by (metis (no_types, lifting) One_nat_def Suc.hyps(2) Suc_1 Suc_length_conv length_0_conv)
    then have "?vts' = [(\<lambda>x. x + u) a, (\<lambda>x. x + u) b]" by simp
    then have "?p' = linepath ((\<lambda>x. x + u) a) ((\<lambda>x. x + u) b)"
      using make_polygonal_path.simps(3) by presburger
    also have "... = (\<lambda>x. x + u) \<circ> (linepath a b)" using linepath_translation by auto
    also have "... = (\<lambda>x. x + u) \<circ> (make_polygonal_path vts)" using ab by auto
    finally have ?case .
  } moreover
  { assume *: "Suc n > 2"
    then obtain a b c rest where abc: "vts = a # b # c # rest"
      by (metis One_nat_def Suc.hyps(2) Suc_1 Suc_leI Suc_le_length_iff)

    let ?vts_tl = "tl vts"
    let ?p_tl = "make_polygonal_path ?vts_tl"
    let ?vts'_tl = "map (\<lambda>x. x + u) ?vts_tl"
    let ?p'_tl = "make_polygonal_path ?vts'_tl"

    have "?vts'_tl = tl ?vts'" by (simp add: map_tl)
    then have "?p' = (linepath (?vts'!0) (?vts'!1)) +++ ?p'_tl"
      using make_polygonal_path.simps(4) abc by force
    moreover have "?p'_tl = (\<lambda>x. x + u) \<circ> (?p_tl)" using Suc.hyps(1) Suc.hyps(2) * by force
    moreover have "(linepath (?vts'!0) (?vts'!1)) = (\<lambda>x. x + u) \<circ> (linepath a b)"
      using abc linepath_translation by auto
    ultimately have ?case by (simp add: abc path_compose_join)
  }
  ultimately show ?case using Suc by linarith
qed

lemma translation_is_polygon:
  assumes "polygon_of p vts"
  shows "polygon_of ((\<lambda>x. x + u) \<circ> p) (map (\<lambda>x. x + u) vts)" (is "polygon_of ?p' ?vts'")
proof-
  have "length vts \<ge> 3"
    by (metis One_nat_def Suc_eq_plus1 Suc_le_eq add_Suc_right assms nat_less_le numeral_3_eq_3 numeral_Bit0 one_add_one polygon_of_def polygon_vertices_length_at_least_4)
  then have *: "?p' = make_polygonal_path ?vts'"
    using make_polygonal_path_translate assms unfolding polygon_of_def by force
  moreover have "polygon ?p'"
  proof-
    have "polygonal_path ?p'" unfolding polygonal_path_def using * by simp
    moreover have "simple_path ?p'"
      using assms unfolding polygon_of_def polygon_def
      using simple_path_translation_eq[of u p]
      by (metis add.commute fun.map_cong)
    moreover have "closed_path ?p'"
    proof-
      have "?p' 0 = p 0 + u" by simp
      moreover have "?p' 1 = p 1 + u" by simp
      moreover have "p 0 = p 1"
        using assms
        unfolding polygon_of_def polygon_def closed_path_def pathstart_def pathfinish_def
        by blast
      moreover have "path ?p'" using make_polygonal_path_gives_path * by simp
      ultimately show ?thesis
        unfolding closed_path_def pathstart_def pathfinish_def
        by argo
    qed
    ultimately show ?thesis unfolding polygon_def by blast
  qed
  ultimately show ?thesis unfolding polygon_of_def by blast
qed

section "Misc. properties"


lemma tail_of_loop_free_polygonal_path_is_loop_free:
  assumes "loop_free (make_polygonal_path (x#tail))" (is "loop_free ?p") and
          "length tail \<ge> 2"
  shows "loop_free (make_polygonal_path tail)" (is "loop_free ?p'")
proof-
  obtain y z tail' where tail': "tail = y # z # tail'"
    by (metis One_nat_def Suc_1 assms(2) length_Cons list.exhaust_sel list.size(3) not_less_eq_eq zero_le)
  have "path ?p \<and> path ?p'" using make_polygonal_path_gives_path by auto
  have "loop_free ?p" using assms unfolding simple_path_def by auto
  moreover have "?p = (linepath x y) +++ ?p'"
    using tail' make_polygonal_path.simps(4) by (simp add: tail')
  moreover from calculation have "loop_free ?p'"
    by (metis make_polygonal_path_gives_path not_loop_free_second_component path_join_path_ends)
  ultimately show ?thesis
    using make_polygonal_path_gives_path simple_path_def by blast
qed

lemma tail_of_simple_polygonal_path_is_simple:
  assumes "simple_path (make_polygonal_path (x#tail))" (is "simple_path ?p") and
          "length tail \<ge> 2"
  shows "simple_path (make_polygonal_path tail)" (is "simple_path ?p'")
  using tail_of_loop_free_polygonal_path_is_loop_free unfolding simple_path_def  
  using assms(1) assms(2) make_polygonal_path_gives_path simple_path_def by blast

lemma interior_vtx_in_path_image_interior:
  fixes vts :: "(real^2) list"
  assumes "x \<in> set (butlast (drop 1 vts))"
  shows "\<exists>t. t \<in> {0<..<1} \<and> (make_polygonal_path vts) t = x"
  using assms
proof(induct vts rule: make_polygonal_path.induct)
  case 1
  then show ?case by simp
next
  case (2 a)
  then show ?case by simp
next
  case (3 a b)
  then show ?case by simp
next
  case ih: (4 a b c tail')
  let ?vts = "a # b # c # tail'"
  let ?tl = "b # c # tail'"
  let ?p = "make_polygonal_path ?vts"
  let ?p_tl = "make_polygonal_path ?tl"
  { assume "x \<in> set (butlast (drop 1 ?tl))"
    then obtain t' where t': "t' \<in> {0<..<1} \<and> ?p_tl t' = x" using ih by blast
    then have "?p ((t' + 1) / 2) = x"
      unfolding make_polygonal_path.simps joinpaths_def
      by (smt (verit, del_insts) field_sum_of_halves greaterThanLessThan_iff mult_2_right not_numeral_le_zero zero_le_divide_iff)
    moreover have "(t' + 1) / 2 \<in> {0<..<1}" using t' by force
    ultimately have ?case
      by blast
  } moreover
  { assume "x \<notin> set (butlast (drop 1 ?tl))"
    then have "x = b"
      by (metis One_nat_def butlast.simps(2) drop0 drop_Suc_Cons ih.prems list.distinct(1) set_ConsD)
    then have "?p (1/2) = x" unfolding make_polygonal_path.simps joinpaths_def
      by (simp add: linepath_1')
    moreover have "((1/2)::(real)) \<in> ({0<..<1}::(real set))" by simp
    ultimately have ?case by blast
  }
  ultimately show ?case by auto
qed

lemma loop_free_polygonal_path_vts_distinct:
  assumes "loop_free (make_polygonal_path vts)"
  shows "distinct (butlast vts)"
  using assms
proof(induct vts rule: make_polygonal_path.induct)
  case 1
  then show ?case by simp
next
  case (2 a)
  then show ?case by simp
next
  case (3 a b)
  then show ?case by simp
next
  case ih: (4 a b c tail')
  let ?vts = "a # b # c # tail'"
  let ?tl = "b # c # tail'"
  let ?p = "make_polygonal_path ?vts"
  let ?p_tl = "make_polygonal_path ?tl"
  
  have "distinct (butlast ?tl)"
    using ih tail_of_loop_free_polygonal_path_is_loop_free by simp
  moreover have "a \<notin> set (butlast ?tl)" 
  proof(rule ccontr)
    assume a_in: "\<not> a \<notin> set (butlast ?tl)"
    then have "a \<in> set (butlast (drop 1 ?vts))" by simp
    then obtain t where t: "t \<in> {0<..<1} \<and> ?p t = a"
      using vertices_on_path_image interior_vtx_in_path_image_interior by metis
    then show False
      using ih.prems unfolding simple_path_def loop_free_def
      by (metis atLeastAtMost_iff greaterThanLessThan_iff less_eq_real_def less_numeral_extra(3) less_numeral_extra(4) list.distinct(1) nth_Cons_0 path_defs(2) polygon_pathstart zero_less_one_class.zero_le_one)
  qed
  ultimately show ?case by simp
qed


lemma loop_free_polygonal_path_vts_drop1_distinct:
  assumes "loop_free (make_polygonal_path vts)"
  shows "distinct (drop 1 vts)"
proof - 
  let ?p = "make_polygonal_path vts"
  let ?last_vts = "vts ! ((length vts) - 1)"
  have "distinct (butlast vts)"
  using assms loop_free_polygonal_path_vts_distinct
  by auto
  then have distinct_butlast: "distinct (butlast (drop 1 vts))"
    by (metis distinct_drop drop_butlast)
  {assume *: "length vts > 1"
    have len_drop1: "length (drop 1 vts) = (length vts) - 1"
      using * by simp 
    have simp_len: "1 + ((length vts) - 2) = (length vts) - 1"
      using * by simp
    then have vts_access: "vts ! (1 + (length vts - 2)) = vts ! ((length vts) - 1)"
      by argo
    have "drop 1 vts ! ((length vts) - 2) = vts ! (1 + (length vts - 2))"
      using * using nth_drop[of 1 vts "(length vts) - 2"]  by auto
    then have "?last_vts = (drop 1 vts) ! ((length vts) - 2)"
      using * simp_len vts_access by argo
    then have "?last_vts = (drop 1 vts) ! (length (drop 1 vts) - 1)"
      using * len_drop1 
      using diff_diff_left nat_1_add_1 by presburger
    then  have drop1_is: "drop 1 vts = (butlast (drop 1 vts))@[?last_vts]"
    using * 
    by (metis append_butlast_last_id drop_eq_Nil leD length_butlast nth_append_length)
  have last_vts_not_in: "?last_vts \<notin> set (butlast (drop 1 vts))"
  proof(rule ccontr)
    assume a_in: "\<not> ?last_vts \<notin>  set (butlast (drop 1 vts))"
    then have "?last_vts \<in> set (butlast (drop 1 vts))" by simp
    then obtain t where t: "t \<in> {0<..<1} \<and> ?p t = ?last_vts"
      using vertices_on_path_image interior_vtx_in_path_image_interior by metis
    have "vts ! (length vts - 1) = ?p 1"
      using polygon_pathfinish[of vts ?p] *
      by (metis list.size(3) not_one_less_zero pathfinish_def)
    then show False
      using t assms unfolding loop_free_def 
      by (metis atLeastAtMost_iff greaterThanLessThan_iff leD less_eq_real_def zero_less_one_class.zero_le_one)
  qed
  have "\<And>b::(real^2) list. distinct b \<and> a \<notin> set b \<Longrightarrow> distinct (b @[a]) " for a::"real^2"
    by simp
  then have ?thesis using last_vts_not_in drop1_is distinct_butlast by metis
  }
   then show ?thesis by force
qed


lemma simple_polygonal_path_vts_distinct:
  assumes "simple_path (make_polygonal_path vts)"
  shows "distinct (butlast vts)"
  using assms loop_free_polygonal_path_vts_distinct
  unfolding simple_path_def
  by blast 

lemma edge_subset_path_image:
  assumes "p = make_polygonal_path vts" and
          "(i::int) \<in> {0..<((length vts) - 1)}" and
          "x = vts!i" and
          "y = vts!(i+1)"
  shows "path_image (linepath x y) \<subseteq> path_image p" (is "?xy_img \<subseteq> ?p_img")
  using assms
proof(induct vts arbitrary: p i rule: make_polygonal_path.induct)
  case 1
  then show ?case by simp
next
  case (2 a)
  then show ?case by simp
next
  case (3 a b)
  then show ?case by (simp add: nth_Cons')
next
  case ih: (4 a b c tl)
  let ?tl = "b # c # tl"
  let ?p_tl = "make_polygonal_path (?tl)"
  { assume "i = 0"
    then have ?case
      by (metis (mono_tags, lifting) ih(2) ih(4) ih(5) Suc_eq_plus1 UnCI list.distinct(1) make_polygonal_path.simps(4) nth_Cons_0 nth_Cons_Suc path_image_join pathfinish_linepath polygon_pathstart subsetI)
  } moreover
  { assume "i > 0"
    then have "x = ?tl!(i-1)" by (simp add: ih.prems(3))
    moreover have "y = ?tl!i" by (simp add: ih.prems(4))
    moreover have "i - 1 \<in> {0..<(length (?tl) - 1)}" using ih.prems(2) by force
    ultimately have "?xy_img \<subseteq> path_image ?p_tl" using ih(1) by (simp add: \<open>0 < i\<close>)
    then have ?case
      unfolding ih(2) make_polygonal_path.simps
      by (smt (verit, ccfv_SIG) UnCI make_polygonal_path.simps(4) make_polygonal_path_gives_path path_image_join path_join_path_ends subsetI subset_iff)
  }
  ultimately show ?case by linarith
qed

section "Properties of Sublists of Polygonal Path Vertex Lists"

lemma make_polygonal_path_image_append_var:
  assumes "length vts1 \<ge> 2"
  shows "path_image (make_polygonal_path (vts1 @ [v])) = path_image (make_polygonal_path vts1 +++ (linepath (vts1 ! (length vts1 - 1)) v))"
  using assms
proof (induct vts1)
  case Nil
  then show ?case by auto
next
  case (Cons a vts1)
  {assume *: "length vts1 = 1"
    then obtain b where "vts1 = [b]" 
      by (metis Cons_nth_drop_Suc One_nat_def drop0 drop_eq_Nil le_numeral_extra(4) less_numeral_extra(1))
    then have "path_image (make_polygonal_path ((a # vts1) @ [v])) =
      path_image (make_polygonal_path (a # vts1) +++ linepath ((a # vts1) ! (length (a # vts1) - 1)) v)"
      using make_polygonal_path.simps 
      by simp
  } moreover {assume * : "length vts1 > 1"
    then obtain b c vts1' where "vts1 = b # c # vts1'"
       by (metis One_nat_def length_0_conv length_Cons less_numeral_extra(4) not_one_less_zero remdups_adj.cases)
     then have h1: "make_polygonal_path ((a # vts1) @ [v]) = (linepath a b) +++ (make_polygonal_path (vts1 @ [v]))"
       using make_polygonal_path.simps(4) 
       by auto
    have "path_image (make_polygonal_path (vts1 @ [v])) =
    path_image (make_polygonal_path vts1 +++ linepath (vts1 ! (length vts1 - 1)) v)"
      using * Cons by auto
    then have "path_image (make_polygonal_path ((a # vts1) @ [v])) =
    path_image (make_polygonal_path (a # vts1) +++ linepath ((a # vts1) ! (length (a # vts1) - 1)) v)"
      using h1 
      by (metis (no_types, lifting) Cons.prems Suc_1 Suc_le_eq Un_assoc \<open>vts1 = b # c # vts1'\<close> add_diff_cancel_left' append_Cons length_Cons list.discI make_polygonal_path.simps(4) nth_Cons_0 nth_Cons_pos path_image_join pathfinish_linepath pathstart_linepath plus_1_eq_Suc polygon_pathfinish polygon_pathstart zero_less_diff)
  }
  ultimately show ?case 
    by (metis Cons.prems Suc_1 add_diff_cancel_left' le_neq_implies_less length_Cons not_less_eq plus_1_eq_Suc)
qed

lemma make_polygonal_path_image_append_helper:
  assumes "length vts1 \<ge> 1 \<and> length vts2 \<ge> 1"
  shows "path_image (make_polygonal_path (vts1 @ [v] @ [v] @ vts2)) = path_image (make_polygonal_path (vts1 @ [v] @ vts2))"
  using assms
proof (induct vts1)
  case Nil
  then show ?case by auto
next
  case (Cons a vts1)
  { assume *: "length vts1 = 0"
    have "path_image (make_polygonal_path ([a] @ [v] @ vts2)) = 
        path_image ((linepath a v) +++ make_polygonal_path (v # vts2))"
      using make_polygonal_path.simps 
      by (metis Cons.prems One_nat_def append_Cons append_Nil append_take_drop_id linorder_not_le list.distinct(1) list.exhaust not_less_eq_eq take_hd_drop)
    then  have "path_image (make_polygonal_path ([a] @ [v] @ vts2)) = 
        path_image (linepath a v) \<union> path_image (make_polygonal_path (v # vts2))"
      by (metis list.discI nth_Cons_0 path_image_join pathfinish_linepath polygon_pathstart)
    have image_helper1: "path_image (make_polygonal_path ([a] @ [v] @ [v] @ vts2)) = path_image (linepath a v +++ make_polygonal_path (v # v # vts2))"
      by simp
    have "path_image (make_polygonal_path (v # v # vts2)) = path_image ((linepath v v) +++ make_polygonal_path (v # vts2))"
      using make_polygonal_path.simps 
      by (metis Cons.prems One_nat_def append_Cons append_Nil append_take_drop_id linorder_not_le list.distinct(1) list.exhaust not_less_eq_eq take_hd_drop)
    moreover have "... = path_image (linepath v v) \<union> path_image (make_polygonal_path (v # vts2))"
            by (metis list.discI nth_Cons_0 path_image_join pathfinish_linepath polygon_pathstart)
    ultimately have image_helper2: "path_image (make_polygonal_path (v # v # vts2)) = {v} \<union> path_image (make_polygonal_path (v # vts2))"
      by auto
    have "v \<in> path_image (make_polygonal_path (v # vts2))"
      using vertices_on_path_image by fastforce
    then have "path_image (make_polygonal_path ([a] @ [v] @ [v] @ vts2)) =
    path_image (make_polygonal_path ([a] @ [v] @ vts2))"
      using image_helper1 image_helper2 
      by (metis \<open>path_image (make_polygonal_path ([a] @ [v] @ vts2)) = path_image (linepath a v) \<union> path_image (make_polygonal_path (v # vts2))\<close> insert_absorb insert_is_Un list.simps(3) nth_Cons_0 path_image_join pathfinish_linepath polygon_pathstart)
  }
  moreover {assume *: "length vts1 > 0"
    then have ind_hyp: "path_image (make_polygonal_path (vts1 @ [v] @ [v] @ vts2)) =
    path_image (make_polygonal_path (vts1 @ [v] @ vts2))"
      using Cons.hyps Cons.prems by linarith
    obtain b vts3 where vts1_is: "vts1 = b#vts3" 
      using * 
      by (metis "*" Cons_nth_drop_Suc drop0)
    then have path_image1: "path_image (make_polygonal_path ((a # vts1) @ [v] @ [v] @ vts2)) = 
      path_image ((linepath a b) +++ make_polygonal_path (vts1 @ [v] @ [v] @ vts2))"
      by (smt (verit, best) Cons.prems Nil_is_append_conv append_Cons length_greater_0_conv less_numeral_extra(1) list.inject make_polygonal_path.elims order_less_le_trans)
    obtain c d where bcd: "vts1 @ [v] @ vts2 = b # c # d"
      using vts1_is 
      by (metis append_Cons append_Nil neq_Nil_conv)
    have path_image2: "path_image (make_polygonal_path ((a # vts1) @ [v] @ vts2)) = path_image ((linepath a b) +++ make_polygonal_path (vts1 @ [v] @ vts2))"
      using make_polygonal_path.simps bcd 
      by auto
    have "path_image (make_polygonal_path ((a # vts1) @ [v] @ [v] @ vts2)) =
    path_image (make_polygonal_path ((a # vts1) @ [v] @ vts2))"
      using ind_hyp path_image1 path_image2 
      by (smt (verit, del_insts) Nil_is_append_conv append_Cons nth_Cons_0 path_image_join pathfinish_linepath polygon_pathstart vts1_is)
  }
  ultimately show ?case 
    using Cons.prems 
    by blast
  qed

lemma make_polygonal_path_image_append:
  assumes "length vts1 \<ge> 2 \<and> length vts2 \<ge> 2"
  shows "path_image (make_polygonal_path (vts1 @ vts2)) = path_image (make_polygonal_path vts1 +++ (linepath (vts1 ! (length vts1 - 1)) (vts2 ! 0)) +++ make_polygonal_path vts2)"
  using assms
proof (induct vts1)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a vts1)
  {assume *: "length vts1 = 1"
    then obtain b where vts1_is: "vts1 = [b]"
      by (metis Cons_nth_drop_Suc One_nat_def drop0 drop_eq_Nil le_numeral_extra(4) less_numeral_extra(1))
    then have "make_polygonal_path ((a # vts1) @ vts2) = make_polygonal_path (a # b # vts2)"
      by simp
    then have "make_polygonal_path ((a # vts1) @ vts2) = (linepath a b) +++ (make_polygonal_path (b # vts2))"
      by (metis Cons.prems length_0_conv make_polygonal_path.simps(4) neq_Nil_conv not_numeral_le_zero)
     then have "make_polygonal_path ((a # vts1) @ vts2) = make_polygonal_path (a # vts1) +++ (make_polygonal_path (b # vts2))"
       using vts1_is make_polygonal_path.simps(3) 
       by simp
     then have "make_polygonal_path ((a # vts1) @ vts2) = make_polygonal_path (a # vts1) +++ linepath b (vts2 ! 0) +++ make_polygonal_path vts2"
       using Cons.prems
       by (smt (verit, ccfv_SIG) "*" Suc_1 add_diff_cancel_left' diff_is_0_eq' length_greater_0_conv list.size(4) make_polygonal_path.elims make_polygonal_path.simps(4) nth_Cons_0 order_less_le_trans plus_1_eq_Suc pos2 vts1_is zero_neq_one) 
     then have "make_polygonal_path ((a # vts1) @ vts2) =
    make_polygonal_path (a # vts1) +++
    linepath ((a # vts1) ! (length (a # vts1) - 1)) (vts2 ! 0) +++ make_polygonal_path vts2"
       using vts1_is 
       by simp
   } moreover {assume *: "length vts1 > 1"
     then obtain b c vts1' where "vts1 = b # c # vts1'"
       by (metis One_nat_def length_0_conv length_Cons less_numeral_extra(4) not_one_less_zero remdups_adj.cases)
     then have h1: "make_polygonal_path ((a # vts1) @ vts2) = (linepath a b) +++ (make_polygonal_path (vts1 @ vts2))"
       using make_polygonal_path.simps(4) 
       by auto
     have ind_h: "path_image (make_polygonal_path (vts1 @ vts2)) =
    path_image (make_polygonal_path vts1 +++
    linepath (vts1 ! (length vts1 - 1)) (vts2 ! 0) +++ make_polygonal_path vts2)"
       using Cons *
       by linarith
     then have "path_image (make_polygonal_path ((a # vts1) @ vts2)) = path_image ((linepath a b)) \<union> path_image((make_polygonal_path vts1 +++
    linepath (vts1 ! (length vts1 - 1)) (vts2 ! 0) +++ make_polygonal_path vts2))"
       using h1 
       by (metis (mono_tags, lifting) "*" Nil_is_append_conv \<open>vts1 = b # c # vts1'\<close> append_Cons length_greater_0_conv linordered_nonzero_semiring_class.zero_le_one nth_Cons_0 order_le_less_trans path_image_join pathfinish_linepath polygon_pathstart)
     then have "path_image (make_polygonal_path ((a # vts1) @ vts2)) = (path_image (linepath a b) \<union> path_image (make_polygonal_path vts1)) \<union>
    path_image((linepath (vts1 ! (length vts1 - 1)) (vts2 ! 0) +++ make_polygonal_path vts2))"
       by (metis (no_types, lifting) "*" Un_assoc length_greater_0_conv order_le_less_trans path_image_join pathstart_join pathstart_linepath polygon_pathfinish zero_less_one_class.zero_le_one)
   then have image_helper: "path_image (make_polygonal_path ((a # vts1) @ vts2)) = (path_image (make_polygonal_path (a # vts1))) \<union>
    path_image((linepath (vts1 ! (length vts1 - 1)) (vts2 ! 0) +++ make_polygonal_path vts2))"
     by (metis (no_types, lifting) "*" \<open>vts1 = b # c # vts1'\<close> length_greater_0_conv make_polygonal_path.simps(4) nth_Cons_0 order_le_less_trans path_image_join pathfinish_linepath polygon_pathstart zero_less_one_class.zero_le_one)
   have "vts1 ! (length vts1 - 1) = (a # vts1) ! (length (a # vts1) - 1)"
     using Cons.prems 
     by (simp add: Suc_le_eq)
   then have "path_image (make_polygonal_path ((a # vts1) @ vts2)) =
    path_image
     (make_polygonal_path (a # vts1) +++
      linepath ((a # vts1) ! (length (a # vts1) - 1)) (vts2 ! 0) +++ make_polygonal_path vts2)"
      using image_helper   
      by (metis (no_types, lifting) Cons.prems length_greater_0_conv order_less_le_trans path_image_join pathstart_join pathstart_linepath polygon_pathfinish pos2)
  }
  ultimately show ?case using Cons.prems
    by fastforce
qed

lemma make_polygonal_path_image_append_alt:
  assumes "p = make_polygonal_path vts"
  assumes "p1 = make_polygonal_path vts1"
  assumes "p2 = make_polygonal_path vts2"
  assumes "last vts1 = hd vts2"
  assumes "length vts1 \<ge> 2 \<and> length vts2 \<ge> 2"
  assumes "vts = vts1 @ (tl vts2)"
  shows "path_image p = path_image (p1 +++ p2)"
proof-
  have "path_image p = path_image p1 \<union> path_image p2"
    by (smt (z3) Nitpick.size_list_simp(2) One_nat_def Suc_1 assms diff_Suc_1 last_conv_nth length_greater_0_conv list.collapse list.sel(3) make_polygonal_path.elims make_polygonal_path.simps(3) make_polygonal_path_image_append make_polygonal_path_image_append_var nat_less_le not_less_eq_eq nth_Cons_0 order_less_le_trans path_image_join polygon_pathfinish polygon_pathstart pos2 length_Cons length_tl path_image_cons_union pathfinish_linepath pathstart_join sup.absorb_iff1 sup.absorb_iff2)
  thus ?thesis 
    by (metis assms(2) assms(3) assms(4) assms(5) hd_conv_nth last_conv_nth length_greater_0_conv order_less_le_trans path_image_join polygon_pathfinish polygon_pathstart pos2)
qed

lemma cont_incr_interval_image:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes "continuous_on {a..b} f"
  assumes "\<forall>x \<in> {a..b}. \<forall>y \<in> {a..b}. x \<le> y \<longrightarrow> f x \<le> f y"
  shows "f`{a..b} = {f a..f b}"
proof-
  have "f`{a..b} \<subseteq> {f a..f b}"
  proof(rule subsetI)
    fix x
    assume "x \<in> f`{a..b}"
    then obtain t where "t \<in> {a..b} \<and> f t = x" by blast
    moreover then have "a \<le> t \<and> t \<le> b" by presburger
    ultimately show "x \<in> {f a..f b}" using assms(3) by auto
  qed
  moreover have "{f a..f b} \<subseteq> f`{a..b}"
  proof-
    obtain c d where "f`{a..b} = {c..d}" using continuous_image_closed_interval assms by meson
    moreover then have "f a \<in> {c..d}" using assms(1) by auto
    moreover have "f b \<in> {c..d}" using assms(1) calculation by auto
    moreover have "{f a..f b} \<subseteq> {c..d}" using calculation by simp
    ultimately show ?thesis by presburger
  qed
  ultimately show ?thesis by blast
qed

lemma two_x_minus_one_image:
  assumes "f = (\<lambda>x::real. 2*x - 1)"
  assumes "a \<le> b"
  shows "f`{a..b} = {f a..f b}"
proof-
  have "continuous_on {a..b} f"
  proof-
    have "continuous_on {a..b} (\<lambda>x::real. x)" by simp
    then have "continuous_on {a..b} (\<lambda>x::real. 2*x)" using continuous_on_mult_const by blast
    thus "continuous_on {a..b} f"
      unfolding assms using continuous_on_translation_eq[of "{a..b}" "-1" "(\<lambda>x::real. 2*x)"] by auto
  qed                             
  thus ?thesis using cont_incr_interval_image assms by force
qed

lemma vts_split_path_image:
  assumes "p = make_polygonal_path vts"
  assumes "p1 = make_polygonal_path vts1"
  assumes "p2 = make_polygonal_path vts2"
  assumes "vts1 = take i vts"
  assumes "vts2 = drop (i-1) vts"
  assumes "n = length vts"
  assumes "1 \<le> i \<and> i < n"
  assumes "x = (2^(i-1) - 1)/(2^(i-1))"
  shows "path_image p1 = p`{0..x} \<and> path_image p2 = p`{x..1}"
  using assms
proof(induct i arbitrary: p p1 p2 vts vts1 vts2 n x)
  case 0
  then show ?case by linarith
next
  case (Suc i)
  { assume *: "Suc i = 1"
    then obtain a where a: "vts1 = [a]"
      using Suc.prems
      by (metis One_nat_def gr_implies_not0 list.collapse list.size(3) take_eq_Nil take_tl zero_neq_one)
    moreover have "vts2 = vts" using * Suc.prems by force
    ultimately have "p1 = linepath a a \<and> p2 = p"
      using Suc.prems make_polygonal_path.simps by meson
    moreover have "x = 0" using Suc.prems * by simp
    moreover have "path_image p1 = {a}" using calculation by simp
    moreover have "p`{0..0} = {p 0}" by auto
    moreover then have "p`{0..0} = {a}" using Suc.prems
      by (metis a gr0_conv_Suc list.discI nth_Cons_0 nth_take pathstart_def polygon_pathstart take_eq_Nil)
    moreover have "path_image p1 = p`{0..x}" using calculation by presburger
    moreover have "path_image p2 = p`{x..1}" using calculation unfolding path_image_def by fast
    ultimately have ?case by blast
  } moreover
  { assume *: "Suc i > 1"

    let ?a = "vts!0"
    let ?b = "vts!1"
    let ?l = "linepath ?a ?b"
    let ?L = "path_image ?l"
    let ?tl = "tl vts"
    let ?vts1' = "take i ?tl"
    let ?vts2' = "drop (i-1) ?tl"
    let ?p' = "make_polygonal_path ?tl"
    let ?p1' = "make_polygonal_path ?vts1'"
    let ?p2' = "make_polygonal_path ?vts2'"
    let ?x' = "((2::real)^(i-1)-1)/(2^(i-1))"
    let ?P1' = "path_image ?p1'"
    let ?P2' = "path_image ?p2'"

    have i: "1 \<le> i \<and> i < length ?tl"
      using Suc.prems * by (metis Suc_eq_plus1 length_tl less_Suc_eq_le less_diff_conv)
    then have ih: "?P1' = ?p'`{0..?x'} \<and> ?P2' = ?p'`{?x'..1}"
      using Suc.hyps[of ?p' ?tl ?p1' ?vts1' ?p2' ?vts2' "length ?tl" ?x'] by presburger

    let ?f = "\<lambda>x::real. 2*x - 1"
    
    have fx: "?f x = ?x'"
      by (metis i Suc.prems(8) bounding_interval_helper1 diff_Suc_1 summation_helper) 
    moreover have fhalf: "?f (1/2) = 0" by simp
    moreover have f1: "?f 1 = 1" by simp
    ultimately have f: "?f`{x..1} = {?x'..1} \<and> ?f`{1/2..x} = {0..?x'}"
      using two_x_minus_one_image by auto
    have x: "1/2 \<le> x \<and> x \<le> 1"
      by (smt (verit) divide_le_eq_1_pos divide_nonneg_nonneg fhalf fx two_realpow_ge_one) 

    have "n \<ge> 3" using Suc.prems * by linarith
    then have p: "p = ?l +++ ?p'"
    proof -
      have f1: "\<forall>vs. (vs::(real, 2) vec list) \<noteq> [] \<or> \<not> 1 < Suc (length vs)"
        by simp
      have "1 < Suc n"
        using Suc.prems(7) by linarith
      then show ?thesis
        by (smt (verit) f1 Suc_le_lessD i One_nat_def Suc.prems(6) Suc.prems(7) Suc_less_eq \<open>p = make_polygonal_path vts\<close> hd_conv_nth length_Cons length_tl less_Suc_eq list.collapse list.exhaust make_polygonal_path.simps(4) nth_Cons_Suc zero_order(3)) 
    qed
    have p_to_p': "\<forall>y \<ge> 1/2. p y = (?p' \<circ> ?f) y"
    proof clarify
      fix y :: real
      assume *: "y \<ge> 1/2"
      { assume **: "y = 1/2"
        then have "p y = ?b"
          by (smt (verit) fhalf joinpaths_def linepath_1' p)
        moreover have "?f y = 0" using ** by simp
        moreover have "?p' 0 = ?b"
          by (metis i One_nat_def Suc.prems(6) length_greater_0_conv length_tl list.size(3) nth_tl pathstart_def polygon_pathstart zero_order(3))
        ultimately have "p y = (?p' \<circ> ?f) y" by simp
      } moreover
      { assume **: "y > 1/2"
        then have "p y = ?p' (?f y)" unfolding p joinpaths_def by simp
        then have "p y = (?p' \<circ> ?f) y" by force
      }
      ultimately show "p y = (?p' \<circ> ?f) y" using * by fastforce
    qed

    have "{0..x} = {0..1/2} \<union> {1/2..x}" using x by (simp add: ivl_disj_un_two_touch(4))
    then have "p`{0..x} = p`{0..1/2} \<union> p`{1/2..x}" by blast
    also have "... = ?L \<union> p`{1/2..x}"
    proof-
      have "?L \<subseteq> p`{0..1/2}"
      proof(rule subsetI)
        fix a
        assume *: "a \<in> ?L"
        then obtain t where t: "t \<in> {0..1} \<and> ?l t = a" unfolding path_image_def by blast
        then have "p (t/2) = a" unfolding p joinpaths_def by auto
        moreover have "t/2 \<in> {0..1/2}" using t by simp
        ultimately show "a \<in> p`{0..1/2}" by blast
      qed
      moreover have "p`{0..1/2} \<subseteq> ?L"
      proof(rule subsetI)
        fix a
        assume *: "a \<in> p`{0..1/2}"
        then obtain t where "t \<in> {0..1/2} \<and> p t = a" by blast
        moreover then have "?l (2*t) = p t" unfolding p joinpaths_def by presburger
        moreover have "2*t \<in> {0..1}" using calculation by simp
        ultimately show "a \<in> ?L" unfolding path_image_def by auto
      qed
      ultimately have "?L = p`{0..1/2}" by blast
      thus ?thesis by presburger
    qed
    also have "... = ?L \<union> (?p' \<circ> ?f)`{1/2..x}" using p_to_p' by simp
    also have "... = ?L \<union> ?p'`{0..?x'}" using f by (metis image_comp)
    also have "... = ?L \<union> ?P1'" using ih by blast
    also have "... = path_image p1"
    proof-
      have "take i (tl vts) \<noteq> []" by (metis i less_zeroE list.size(3) not_one_le_zero take_eq_Nil2)
      thus ?thesis using path_image_cons_union[of p1 vts1 ?p1' ?vts1' ?a ?b]
        by (metis "*" Nitpick.size_list_simp(2) One_nat_def Suc.prems(2) Suc.prems(4) Suc.prems(6) Suc.prems(7) bot_nat_0.extremum_strict hd_conv_nth length_greater_0_conv nth_take nth_tl take_Suc take_tl)
    qed
    finally have 1: "path_image p1 = p`{0..x}" by argo

    have "p`{x..1} = (?p' \<circ> ?f)`{x..1}" using p_to_p' x by simp
    also have "... = ?p'`{?x'..1}" using f by (metis image_comp)
    also have "... = ?P2'" using ih by presburger
    also have "... = path_image p2"
      using path_image_cons_union
      by (metis Suc.prems(3) Suc.prems(5) diff_Suc_1 drop_Suc gr0_implies_Suc i linorder_neqE_nat not_less_zero not_one_le_zero)
    finally have 2: "path_image p2 = p`{x..1}" by argo

    have ?case using 1 2 by fast
  }
  ultimately show ?case using Suc.prems by linarith
qed

lemma drop_i_is_loop_free:
  fixes vts :: "(real^2) list"
  assumes "m = length vts"
  assumes "i \<le> m - 2"
  assumes "vts' = drop i vts"
  assumes "p = make_polygonal_path vts"
  assumes "p' = make_polygonal_path vts'"
  assumes "loop_free p"
  shows "loop_free p'"
  using assms
proof(induct i arbitrary: vts' p')
  case 0
  then show ?case by simp
next
  case (Suc i)

  let ?vts'' = "drop i vts"
  let ?p'' = "make_polygonal_path ?vts''"
  have ih: "loop_free ?p''"
    using Suc.hyps Suc.prems(2) Suc.prems(6) Suc_leD assms(1) assms(4) by blast

  obtain a b where ab: "?vts'' = a # vts' \<and> b = vts' ! 0"
    by (metis Cons_nth_drop_Suc Suc.prems(3) constant_linepath_is_not_loop_free drop_eq_Nil ih linorder_not_less make_polygonal_path.simps(1))
  then have "?vts'' = a # b # (vts' ! 1) # (drop 2 vts')"
    by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc Suc.prems(2) Suc.prems(3) Suc_1 Suc_diff_Suc Suc_le_eq assms(1) diff_Suc_1 diff_is_0_eq drop_drop le_add_diff_inverse length_drop nat_le_linear not_less_eq_eq zero_less_Suc)
  then have "?p'' = (linepath a b) +++ p'"
    using make_polygonal_path.simps(4)[of a b "vts' ! 1" "drop 2 vts'"] Suc.prems by (simp add: ab)
  moreover have "pathfinish (linepath a b) = pathstart p'"
    using Suc.prems ab
    by (metis constant_linepath_is_not_loop_free ih make_polygonal_path.simps(2) pathfinish_linepath polygon_pathstart)
  ultimately have "arc p'" using simple_path_joinE
    by (metis ih make_polygonal_path_gives_path simple_path_def)
  then show ?case using arc_imp_simple_path simple_path_def by blast
qed

lemma joinpaths_tl_transform:
  assumes "f = (\<lambda>x::real. 2*x - 1)"
  assumes "pathfinish g1 = pathstart g2"
  assumes "p = g1 +++ g2"
  assumes "x \<ge> 1/2"
  shows "p x = g2 (f x)"
proof-
  { assume "x = 1/2"
    moreover then have "f x = 0" using assms by fastforce
    ultimately have "p x = pathfinish g1 \<and> g2 (f x) = pathfinish g1"
      using assms unfolding pathfinish_def pathstart_def joinpaths_def by force
    then have "p x = g2 (f x)" using assms unfolding joinpaths_def by simp
  } moreover
  { assume "x > 1/2"
    then have "p x = g2 (f x)" using assms unfolding joinpaths_def by simp
  }
  ultimately show "p x = g2 (f x)" using assms by fastforce
qed

lemma joinpaths_tl_image_transform:
  assumes "f = (\<lambda>x::real. 2*x - 1)"
  assumes "pathfinish g1 = pathstart g2"
  assumes "p = g1 +++ g2"
  assumes "1/2 \<le> a \<and> a \<le> b"
  shows "p`{a..b} = g2`{f a..f b}"
proof-
  have "\<forall>x \<in> {a..b}. p x = g2 (f x)" using assms joinpaths_tl_transform[of f g1 g2 p] by force
  then have "p`{a..b} = (g2 \<circ> f)`{a..b}" by simp
  also have "... = g2`{f a..f b}" using two_x_minus_one_image by (metis assms(1,4) image_comp)
  finally show ?thesis .
qed

lemma vts_sublist_path_image:
  assumes "p = make_polygonal_path vts"
  assumes "p' = make_polygonal_path vts'"
  assumes "vts' = take j (drop i vts)"
  assumes "m = length vts"
  assumes "n = length vts'"
  assumes "k = i + j"
  assumes "k \<le> m - 1 \<and> 2 \<le> j"
  assumes "x1 = (2^i - 1)/(2^i)"
  assumes "x2 = (2^(k-1) - 1)/(2^(k-1))"
  shows "path_image p' = p`{x1..x2}"
  using assms
proof(induct i arbitrary: vts p p' vts' m k x1 x2)
  case 0
  then show ?case using vts_split_path_image[of p "drop 0 vts" p' vts' _ _ j m x2]
    by (metis (no_types, opaque_lifting) Suc_diff_le add_0 cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq div_by_1 drop.simps(1) drop_0 le_add_diff_inverse length_drop less_one linorder_not_le plus_1_eq_Suc pos2 power.simps(1))
next
  case (Suc i)

  let ?vts_tl = "tl vts"
  let ?vts_tl' = "take j (drop i ?vts_tl)"
  let ?p_tl = "make_polygonal_path ?vts_tl"
  let ?m' = "m-1"
  let ?k' = "i+j"
  let ?x1' = "(2^i - 1)/(2^i)"
  let ?x2' = "(2^(?k'-1) - 1)/(2^(?k'-1))"
  let ?f = "\<lambda>x. 2*x - 1"

  have "vts' = ?vts_tl'" using Suc.prems by (metis drop_Suc)
  then have "p' = make_polygonal_path ?vts_tl'" using Suc.prems by argo
  then have ih: "path_image p' = ?p_tl`{?x1'..?x2'}"
    using Suc.hyps[of ?p_tl ?vts_tl p' ?vts_tl' ?m' "?k'" ?x1' ?x2'] Suc.prems
    by (smt (verit, ccfv_SIG) Suc_eq_plus1 add_diff_cancel_right' add_leD1 diff_diff_left diff_is_0_eq drop_Suc le_add_diff_inverse length_tl linorder_not_le not_add_less2)

  let ?a = "vts!0"
  let ?b = "vts!1"
  let ?l = "linepath ?a ?b"
  have p: "p = ?l +++ ?p_tl"
  proof-
    have "length vts \<ge> 3" using Suc.prems by linarith
    then obtain c w where "vts = ?a # ?b # c # w"
      by (metis Cons_nth_drop_Suc One_nat_def Suc_le_eq drop0 numeral_3_eq_3 order_less_le)
    thus ?thesis
      using Suc.prems make_polygonal_path.simps(4)[of ?a ?b c w] by (metis list.sel(3))
  qed
  moreover have "x1 \<ge> 1/2" using Suc.prems by (simp add: plus_1_eq_Suc)
  moreover have "x2 \<ge> x1"
    using Suc.prems
    by (smt (verit, best) Nat.diff_add_assoc2 One_nat_def add_Suc_shift add_diff_cancel_left' add_mono_thms_linordered_semiring(2) diff_add_cancel dual_order.trans group_cancel.rule0 numeral_One one_le_numeral one_le_power plus_1_eq_Suc power_increasing real_shrink_le trans_le_add2)
  moreover have "pathfinish ?l = pathstart ?p_tl"
    by (metis One_nat_def Suc.prems(4) Suc.prems(6) Suc.prems(7) Suc_neq_Zero add_is_0 diff_is_0_eq' diff_zero length_tl linorder_not_less list.size(3) nth_tl pathfinish_linepath polygon_pathstart)
  ultimately have "p`{x1..x2} = ?p_tl`{?f x1..?f x2}"
    using joinpaths_tl_image_transform[of ?f ?l ?p_tl p x1 x2] by presburger
  also have "... = ?p_tl`{?x1'..?x2'}"
    by (metis (no_types, lifting) Nat.add_diff_assoc Suc.prems(6-9) add.commute add_leD1 bounding_interval_helper1 diff_Suc_1 le_add2 nat_1_add_1 plus_1_eq_Suc summation_helper)
  also have "... = path_image p'" using ih by blast
  finally show ?case by argo
qed

lemma one_append_simple_path:
  fixes vts :: "(real^2) list"
  assumes "vts = vts' @ [z]"
  assumes "n = length vts"
  assumes "n \<ge> 3"
  assumes "p = make_polygonal_path vts"
  assumes "p' = make_polygonal_path vts'"
  assumes "simple_path p"
  shows "simple_path p'"
  using assms
proof(induct n arbitrary: vts vts' p p')
  case 0
  then show ?case by linarith
next
  case (Suc n)
  { assume *: "Suc n = 3"
    then obtain a b c where abc: "vts = [a, b, c] \<and> vts' = [a, b]"
      using Suc.prems
      by (smt (z3) Suc_le_length_iff Suc_length_conv append_Cons diff_Suc_1 drop0 length_0_conv length_append_singleton numeral_3_eq_3)
    then have "p' = linepath a b"
      by (simp add: Suc.prems(5))
    moreover have "a \<noteq> b" using loop_free_polygonal_path_vts_distinct Suc.prems
      by (metis abc butlast_snoc distinct_length_2_or_more simple_path_def)
    ultimately have ?case by blast
  } moreover
  { assume *: "Suc n > 3"
    then obtain a b tl' where ab: "vts' = a # tl' \<and> b = tl'!0" using Suc.prems
      by (metis Suc_le_length_iff Suc_le_mono length_append_singleton numeral_3_eq_3)
    moreover then have "p = make_polygonal_path (a # (tl' @ [z]))" using Suc.prems by auto
    moreover then have p: "p = linepath a b +++ make_polygonal_path (tl' @ [z])"
      using make_polygonal_path.simps ab
      by (smt (verit, ccfv_threshold) "*" Cons_nth_drop_Suc One_nat_def Suc.prems(1) Suc.prems(2) Suc_1 Suc_less_eq append_Cons drop0 length_Cons length_append_singleton length_greater_0_conv list.size(3) not_numeral_less_one numeral_3_eq_3)
    moreover then have "simple_path ..." using Suc.prems by meson
    ultimately have pre_ih: "simple_path (make_polygonal_path (tl' @ [z]))"
      using Suc.prems(1) Suc.prems(2) Suc.prems(3) ab tail_of_simple_polygonal_path_is_simple by simp
    then have ih: "simple_path (make_polygonal_path tl')"
      using Suc.hyps "*" Suc.prems(1) Suc.prems(2) ab by force
    have "simple_path ((linepath a b) +++ make_polygonal_path tl')"
    proof-
      let ?g1 = "linepath a b"
      let ?g2 = "make_polygonal_path tl'"
      let ?G1 = "path_image ?g1"
      let ?G2 = "path_image ?g2"
      have "pathfinish ?g2 = last tl'"
        by (metis constant_linepath_is_not_loop_free ih last_conv_nth make_polygonal_path.simps(1) polygon_pathfinish simple_path_def)
      also have "... = vts ! (length vts - 2)" 
        by (metis ab Suc.prems(1) Suc_1 constant_linepath_is_not_loop_free diff_Suc_1 diff_Suc_Suc ih impossible_Cons last.simps last_conv_nth length_Cons length_append_singleton list.discI make_polygonal_path.simps(1) nle_le nth_append order_less_le simple_path_def)
      finally have pathfinish_g2: "pathfinish ?g2 = vts ! (length vts - 2)" .

      have "pathfinish ?g1 = pathstart ?g2"
        by (metis ab constant_linepath_is_not_loop_free ih linepath_1' make_polygonal_path.simps(1) pathfinish_def polygon_pathstart simple_path_def)
      moreover have "arc ?g1"
        by (metis Suc.prems(6) p arc_linepath constant_linepath_is_not_loop_free not_loop_free_first_component simple_path_def)
      moreover have "arc ?g2"
      proof-
        have "pathstart ?g2 = b"
          using calculation(1) by auto
        moreover have "b = vts!1" 
          by (metis ab One_nat_def Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc_le_eq length_append_singleton not_less_eq_eq nth_Cons_Suc nth_append numeral_3_eq_3)
        moreover have "last tl' \<noteq> vts!1"
          using loop_free_polygonal_path_vts_distinct Suc.prems
          by (metis pre_ih ab append_Nil append_butlast_last_id butlast_conv_take butlast_snoc calculation(2) constant_linepath_is_not_loop_free hd_conv_nth ih index_Cons index_last list.collapse make_polygonal_path.simps(2) simple_path_def take0)
        ultimately have "pathfinish ?g2 \<noteq> b"
          using pathfinish_g2 \<open>pathfinish (make_polygonal_path tl') = last tl'\<close> by presburger
        thus ?thesis
          using \<open>pathstart (make_polygonal_path tl') = b\<close> arc_simple_path ih by blast
      qed
      moreover have "?G1 \<inter> ?G2 \<subseteq> {pathstart ?g2}"
      proof(rule subsetI)
        let ?z = "((2::real)^(n-1) - 1)/(2^(n-1))"
        have g1: "?G1 = p`{0..1/2}"
        proof-
          have "take 2 vts = [a, b]"
            by (smt (verit) "*" One_nat_def Suc.prems(1) Suc.prems(2) Suc_1 ab append_Cons butlast_snoc drop0 drop_Suc_Cons length_append_singleton less_Suc_eq_le not_less_eq_eq nth_butlast numeral_3_eq_3 plus_1_eq_Suc same_append_eq take_Suc_Cons take_Suc_eq take_add take_all_iff)
          then have "?g1 = make_polygonal_path (take 2 vts)"
            using make_polygonal_path.simps by presburger
          moreover have "1 < n" using * by linarith
          ultimately have "?G1 = p`{0..(2^(2-1) - 1)/(2^(2-1))}"
            using vts_split_path_image
            by (metis "*" Suc.prems(2) Suc.prems(4) Suc_1 Suc_leD Suc_lessD eval_nat_numeral(3) order.refl)
          thus ?thesis by force
        qed
        have g2: "?G2 = p`{1/2..?z}"
        proof-
          have "tl' = take (n - 1) (drop 1 vts)"
            using ab Suc.prems(1) Suc.prems(2) by simp
          moreover then have "?g2 = make_polygonal_path (take (n - 1) (drop 1 vts))" by blast
          ultimately have "?G2 = p`{(2^1 - 1)/(2^1)..?z}"
            using vts_sublist_path_image[of p vts ?g2 tl' "n-1" 1 _ _ "n" "((2::real)^1 - 1)/(2^1)" ?z]
            by (metis "*" Suc.prems(1) Suc.prems(2) Suc.prems(4) Suc_eq_plus1 ab add_0 add_Suc_shift add_le_imp_le_diff diff_Suc_Suc diff_zero eval_nat_numeral(3) length_Cons length_append less_Suc_eq_le list.size(3) order.refl)
          thus ?thesis by simp
        qed
        have "1/2 \<le> ?z"
          using * bounding_interval_helper1[of "n-1"] Suc.prems
          by (smt (verit) One_nat_def diff_Suc_Suc less_diff_conv numeral_3_eq_3 one_le_power plus_1_eq_Suc power_one_right power_strict_increasing_iff real_shrink_le add_2_eq_Suc diff_add_inverse less_trans_Suc numeral_eq_Suc pos2 self_le_power zero_less_diff)
        moreover have "?z < 1" by auto
        ultimately have z: "1/2 \<le> ?z \<and> ?z < 1" by blast

        fix x
        assume "x \<in> ?G1 \<inter> ?G2"
        then obtain t1 t2 where t1t2: "t1 \<in> {0..1/2} \<and> t2 \<in> {1/2..?z} \<and> p t1 = x \<and> p t2 = x"
          by (smt (verit, del_insts) g1 g2 Int_iff imageE path_image_def)
        moreover have "(t1 = t2) \<or> (t1 = 0 \<and> t2 = 1) \<or> (t1 = 1 \<and> t2 = 0)"
        proof-
          have "t1 \<in> {0..1} \<and> t2 \<in> {0..1}"
            by (meson t1t2 z atLeastAtMost_iff dual_order.trans less_eq_real_def)
          thus ?thesis
            using Suc.prems(6) unfolding simple_path_def loop_free_def using t1t2 by presburger
        qed
        moreover have "t1 = 1/2" using calculation by force
        ultimately have "x = pathstart ?g2"
          by (metis ab constant_linepath_is_not_loop_free dual_order.refl eq_divide_eq_numeral1(1) ih joinpaths_def make_polygonal_path.simps(1) mult.commute p pathfinish_def pathfinish_linepath polygon_pathstart simple_path_def zero_neq_numeral)
        thus "x \<in> {pathstart ?g2}" by simp
      qed
      ultimately show ?thesis using arc_join_eq ih by (metis arc_imp_simple_path)
    qed
    moreover have "vts' = a # tl'" using Suc.prems ab by argo
    moreover have "p' = (linepath a b) +++ make_polygonal_path tl'"
    proof -
      have "Suc (length tl') = length vts'" by (simp add: ab)
      then show ?thesis
        by (metis (no_types) "*" Cons_nth_drop_Suc Suc.prems(1) Suc.prems(2) Suc.prems(5) Suc_lessD ab drop_0 length_append_singleton make_polygonal_path.simps(4) not_less_eq numeral_3_eq_3)
    qed
    ultimately have ?case by blast
  }
  ultimately show ?case using Suc.prems by linarith
qed

lemma take_i_is_loop_free:
  fixes vts :: "(real^2) list"
  assumes "n = length vts"
  assumes "2 \<le> i \<and> i \<le> n"
  assumes "vts' = take i vts"
  assumes "p = make_polygonal_path vts"
  assumes "p' = make_polygonal_path vts'"
  assumes "loop_free p"
  shows "loop_free p'"
  using assms
proof(induct "n-i" arbitrary: vts' i p p')
  case 0
  moreover then have "p = p'" by auto
  ultimately show ?case by argo
next
  case (Suc x)

  let ?i' = "i+1"
  let ?q_vts = "take (i+1) vts"
  let ?q = "make_polygonal_path ?q_vts"

  have "n-?i' = x" using Suc.hyps(2) by linarith
  then have "loop_free ?q" using Suc.hyps Suc.prems(2) Suc.prems(4) Suc.prems(6) assms(1) by auto
  moreover obtain z where "?q = make_polygonal_path (vts' @ [z])"
    unfolding Suc.prems(3)
    by (metis Suc.hyps(2) Suc_eq_plus1 assms(1) take_Suc_conv_app_nth zero_less_Suc zero_less_diff)
  ultimately show "loop_free p'"
    unfolding Suc.prems using one_append_simple_path unfolding simple_path_def
    by (metis One_nat_def Suc.prems(2) Suc_1 add_diff_cancel_right' append_take_drop_id assms(1) diff_diff_cancel length_append length_append_singleton length_drop make_polygonal_path_gives_path not_less_eq_eq numeral_3_eq_3)
qed

lemma sublist_is_loop_free:
  fixes vts :: "(real^2) list"
  assumes "p = make_polygonal_path vts"
  assumes "p' = make_polygonal_path vts'"
  assumes "loop_free p"
  assumes "m = length vts"
  assumes "n = length vts'"
  assumes "sublist vts' vts"
  assumes "n \<ge> 2 \<and> m \<ge> 2"
  shows "loop_free p'"
proof-
  obtain pre post where vts: "vts = pre @ vts' @ post" using assms(6) unfolding sublist_def by blast
  then have "vts' @ post = drop (length pre) vts" using vts by simp
  moreover have "vts' = take (length vts') (vts' @ post)" using vts by simp
  moreover have "loop_free (make_polygonal_path (vts' @ post))"
    using drop_i_is_loop_free assms calculation
    by (smt (verit, del_insts) One_nat_def Suc_1 Suc_leD diff_diff_cancel drop_all le_diff_iff' length_append length_drop list.size(3) nat_le_linear not_numeral_le_zero numeral_3_eq_3 trans_le_add1)
  ultimately show ?thesis
    using take_i_is_loop_free assms
    by (metis sublist_append_rightI sublist_length_le)
qed

lemma diff_points_path_image_set_property:
  fixes a b:: "real^2"
  assumes "a \<noteq> b"
  shows "path_image (linepath a b) \<noteq> {a, b}"
proof -
  have not_a: "(linepath a b) (1/2) \<noteq> a"
    by (smt (verit) add_diff_cancel_left' assms divide_eq_0_iff linepath_def scaleR_cancel_left scaleR_collapse)
  have not_b: "(linepath a b) (1/2) \<noteq> b"
    by (smt (verit, ccfv_SIG) add_diff_cancel_right' assms divide_eq_1_iff linepath_def scaleR_cancel_left scaleR_collapse)
  have "(linepath a b) (1/2) \<in> path_image (linepath a b)"
    unfolding path_image_def by simp
  then show ?thesis using not_a not_b by blast
qed

lemma polygonal_path_vertex_t:
  assumes "p = make_polygonal_path vts"
  assumes "n = length vts"
  assumes "n \<ge> 1"
  assumes "0 \<le> i \<and> i < n - 1"
  assumes "x = (2^i - 1)/(2^i)"
  shows "vts!i = p x"
  using assms
proof(induct i arbitrary: p vts n x)
  case 0
  then show ?case
    by (metis bot_nat_0.extremum cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq div_0 less_nat_zero_code list.size(3) pathstart_def polygon_pathstart power_0)
next
  case (Suc i)

  let ?vts' = "tl vts"
  let ?p' = "make_polygonal_path ?vts'"
  let ?x' = "(2^i - 1)/(2^i)"

  have "p x = ?p' ?x'"
  proof-
    let ?a = "vts!0"
    let ?b = "vts!1"
    let ?l = "linepath ?a ?b"
    have "n \<ge> 3" using Suc.prems by linarith
    then have "length ?vts' \<ge> 2" by (simp add: Suc.prems(2))
    then have "p = ?l +++ ?p'"
      using Suc.prems make_polygonal_path.simps(4)[of ?a ?b "?vts'!1" "drop 2 ?vts'"]
      by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc Suc_1 bot_nat_0.not_eq_extremum diff_Suc_1 diff_is_0_eq drop_0 drop_Suc less_Suc_eq zero_less_diff)
    moreover have "pathfinish ?l = pathstart ?p'"
      by (metis One_nat_def \<open>2 \<le> length (tl vts)\<close> length_greater_0_conv nth_tl order_less_le_trans pathfinish_linepath polygon_pathstart pos2)
    moreover have "(\<lambda>x::real. 2 * x - 1) x = ?x'"
      using Suc.prems(5) Suc_eq_plus1 bounding_interval_helper1 diff_Suc_1 le_add2 summation_helper
      by presburger
    ultimately show ?thesis using joinpaths_tl_transform[of "\<lambda>x. 2*x - 1" ?l ?p' p x]
      by (smt (verit, del_insts) divide_nonneg_nonneg half_bounded_equal two_realpow_ge_one)
  qed
  moreover have "vts!(i+1) = ?vts'!i" using Suc.prems by (simp add: nth_tl)
  moreover have "?vts'!i = ?p' ?x'" using Suc.hyps Suc.prems by force
  ultimately show ?case by simp
qed

lemma loop_free_split_int:
  assumes "p = make_polygonal_path vts \<and> loop_free p"
  assumes "vts1 = take i vts"
  assumes "vts2 = drop (i-1) vts"
  assumes "c1 = make_polygonal_path vts1"
  assumes "c2 = make_polygonal_path vts2"
  assumes "n = length vts"
  assumes "1 \<le> i \<and> i < n"
  shows "(path_image c1) \<inter> (path_image c2) \<subseteq> {pathstart c1, pathstart c2}"
    (is "?C1 \<inter> ?C2 \<subseteq> {pathstart c1, pathstart c2}")
proof(rule subsetI)
  let ?t = "((2::real)^(i-1) - 1)/(2^(i-1))"

  fix x
  assume "x \<in> ?C1 \<inter> ?C2"
  moreover have c1c2: "?C1 = p`{0..?t} \<and> ?C2 = p`{?t..1}"
    using vts_split_path_image assms polygon_of_def by metis
  ultimately obtain t1 t2 where t1t2: "t1 \<in> {0..?t} \<and> t2 \<in> {?t..1} \<and> p t1 = x \<and> p t2 = x" by auto
  moreover have "t1 \<in> {0..1} \<and> t2 \<in> {0..1}" using calculation by force
  moreover have "(t1 = t2) \<or> (t1 = 0 \<and> t2 = 1)"
    using assms(1) calculation unfolding polygon_of_def polygon_def simple_path_def loop_free_def
    by fastforce
  ultimately have "x \<in> {p ?t, p 0}" by fastforce
  moreover have "p ?t = pathstart c2"
    using assms polygonal_path_vertex_t
    by (smt (verit, ccfv_SIG) Cons_nth_drop_Suc diff_less_mono le_eq_less_or_eq length_drop less_imp_diff_less less_trans_Suc less_zeroE linorder_neqE_nat list.size(3) nth_Cons_0 numeral_1_eq_Suc_0 numerals(1) polygon_of_def polygon_pathstart)
  moreover have "p 0 = pathstart c1" using assms
    by (metis One_nat_def diff_is_0_eq diff_zero linorder_not_less nth_take pathstart_def polygon_pathstart take_eq_Nil zero_less_Suc)
  ultimately show "x \<in> {pathstart c1, pathstart c2}" by blast
qed

lemma loop_free_arc_split_int:
  assumes "p = make_polygonal_path vts \<and> loop_free p \<and> arc p"
  assumes "vts1 = take i vts"
  assumes "vts2 = drop (i-1) vts"
  assumes "c1 = make_polygonal_path vts1"
  assumes "c2 = make_polygonal_path vts2"
  assumes "n = length vts"
  assumes "1 \<le> i \<and> i < n"
  shows "(path_image c1) \<inter> (path_image c2) \<subseteq> {pathstart c2}"
    (is "?C1 \<inter> ?C2 \<subseteq> {pathstart c2}")
proof(rule subsetI)
  let ?t = "((2::real)^(i-1) - 1)/(2^(i-1))"

  fix x
  assume "x \<in> ?C1 \<inter> ?C2"
  moreover have c1c2: "?C1 = p`{0..?t} \<and> ?C2 = p`{?t..1}"
    using vts_split_path_image assms polygon_of_def by metis
  ultimately obtain t1 t2 where t1t2: "t1 \<in> {0..?t} \<and> t2 \<in> {?t..1} \<and> p t1 = x \<and> p t2 = x" by auto
  moreover have "t1 \<in> {0..1} \<and> t2 \<in> {0..1}" using calculation by force
  moreover have "(t1 = t2) \<or> (t1 = 0 \<and> t2 = 1)"
    using assms(1) calculation unfolding polygon_of_def polygon_def simple_path_def loop_free_def
    by fastforce
  moreover then have "t1 = t2"
    using assms(1) unfolding arc_def using calculation(1) inj_on_contraD by fastforce
  ultimately have "x \<in> {p ?t}" by fastforce
  moreover have "p ?t = pathstart c2"
    using assms polygonal_path_vertex_t
    by (smt (verit, ccfv_SIG) Cons_nth_drop_Suc diff_less_mono le_eq_less_or_eq length_drop less_imp_diff_less less_trans_Suc less_zeroE linorder_neqE_nat list.size(3) nth_Cons_0 numeral_1_eq_Suc_0 numerals(1) polygon_of_def polygon_pathstart)
  ultimately show "x \<in> {pathstart c2}" by fast
qed

lemma loop_free_append:
  assumes "p = make_polygonal_path vts"
  assumes "p1 = make_polygonal_path vts1"
  assumes "p2 = make_polygonal_path vts2"
  assumes "vts = vts1 @ (tl vts2)"
  assumes "loop_free p1 \<and> loop_free p2"
  assumes "path_image p1 \<inter> path_image p2 \<subseteq> {pathstart p1, pathstart p2}"
  assumes "last vts2 \<noteq> hd vts1 \<longrightarrow> path_image p1 \<inter> path_image p2 \<subseteq> {pathstart p2}"
  assumes "last vts1 = hd vts2"
  assumes "arc p1 \<and> arc p2"
  shows "loop_free p"
  using assms
proof(induct "length vts1" arbitrary: p p1 p2 vts vts1 vts2 rule: less_induct)
  case less
  have 1: "length vts1 \<ge> 2"
      using less
      by (metis Suc_1 arc_distinct_ends constant_linepath_is_not_loop_free diff_is_0_eq' make_polygonal_path.simps(1) not_less_eq_eq polygon_pathfinish polygon_pathstart)
  moreover have "length vts2 \<ge> 2"
    using less.prems
    by (metis One_nat_def Suc_1 Suc_leI arc_distinct_ends diff_Suc_1 length_greater_0_conv make_polygonal_path.simps(1) nat_less_le pathfinish_linepath pathstart_linepath polygon_pathfinish polygon_pathstart)
  ultimately have "length vts \<ge> 3" using less assms(4) by auto
  { assume *: "length vts1 = 2"
    then obtain a b where "vts1 = [a, b]"
      by (metis "1" Cons_nth_drop_Suc One_nat_def Suc_1 drop0 drop_eq_Nil lessI pos2)
    then have p1: "p1 = linepath a b"
      using less make_polygonal_path.simps(3) by metis
    have p: "p = p1 +++ p2"
      using p1 less
      by (smt (verit) \<open>vts1 = [a, b]\<close> append_Cons assms(4) constant_linepath_is_not_loop_free last_ConsL last_ConsR list.exhaust_sel list.inject list.simps(3) make_polygonal_path.elims self_append_conv2)
    have b: "pathstart p2 \<in> path_image p1 \<inter> path_image p2"
      by (metis IntI less(3,4,6,9) constant_linepath_is_not_loop_free hd_conv_nth last_conv_nth make_polygonal_path.simps(1) pathfinish_in_path_image pathstart_in_path_image polygon_pathfinish polygon_pathstart)
    { assume "pathstart p1 = pathfinish p2"
      then have ?case using simple_path_join_loop_eq[of p2 p1] less.prems
        by (metis make_polygonal_path_gives_path p path_join_eq simple_path_def)
    } moreover
    { assume **: "pathstart p1 \<noteq> pathfinish p2"
      then have "path_image p1 \<inter> path_image p2 = {pathstart p2}"
        using less.prems b
        by (metis constant_linepath_is_not_loop_free empty_subsetI hd_conv_nth insert_subset last_conv_nth make_polygonal_path.simps(1) polygon_pathfinish polygon_pathstart subset_antisym)
      then have ?case
        using arc_join_eq[of p1 p2]
        by (metis less(2,4,10) arc_imp_simple_path arc_join_eq_alt make_polygonal_path_gives_path p path_join_path_ends simple_path_def)
    }
    ultimately have ?case by blast
  } moreover
  { assume *: "length vts1 > 2"
    then have len_p1: "length vts1 \<ge> 3" by linarith
    then obtain a b vts_tl where ab: "vts = a # vts_tl \<and> b = hd vts_tl"
      by (metis \<open>3 \<le> length vts\<close> length_0_conv list.collapse not_numeral_le_zero)
    have vts1_char: "vts1 = (vts1 ! 0) # (vts1 ! 1) # (vts1 ! 2) # (drop 3 vts1)"
      using len_p1 
      by (metis "1" Cons_nth_drop_Suc One_nat_def Suc_1 drop0 length_greater_0_conv linorder_not_less list.size(3) not_less_eq_eq not_numeral_le_zero numeral_3_eq_3)
    then have tail_vts1_char: "tl vts1 = (vts1 ! 1) # (vts1 ! 2) # (drop 3 vts1)"
      by (metis list.sel(3))

    let ?l = "linepath a b"
    let ?vts1_tl = "tl vts1"
    let ?p1_tl = "make_polygonal_path ?vts1_tl"
    let ?vts2_tl = "tl vts2"
    let ?p2_tl = "make_polygonal_path ?vts2_tl"
    let ?p_tl = "make_polygonal_path vts_tl"

    have p: "p = ?l +++ ?p_tl"
      unfolding less.prems(1)
      by (smt (verit, ccfv_SIG) Suc_le_length_iff \<open>3 \<le> length vts\<close> ab list.discI list.sel(1) list.sel(3) make_polygonal_path.elims numeral_3_eq_3)
    have p1: "p1 = ?l +++ ?p1_tl"
      using ab unfolding less.prems(2)
      by (smt (verit, ccfv_SIG) "*" Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_le_eq hd_append2 less.prems(4) list.sel(1) list.sel(3) make_polygonal_path.elims nat_less_le tl_append2)

    have p1_img: "path_image ?l \<inter> path_image ?p1_tl = {pathstart ?p1_tl}"
      by (metis arc_join_eq_alt less.prems(2) less.prems(9) make_polygonal_path_gives_path p1 path_join_path_ends)

    have "vts_tl = ?vts1_tl @ (tl vts2)"
      using less.prems(4) ab
      by (metis "*" length_greater_0_conv list.sel(3) order.strict_trans pos2 tl_append2)
    moreover have "loop_free ?p1_tl \<and> loop_free p2"
      using \<open>3 \<le> length vts1\<close> less.prems(2) less.prems(5) sublist_is_loop_free by fastforce
    moreover have "path_image ?p1_tl \<inter> path_image p2 \<subseteq> {pathstart p2}"
    proof-
      have "path_image ?p1_tl \<subseteq> path_image p1"
        by (metis (no_types, opaque_lifting) "*" Suc_1 Suc_lessD length_tl less.prems(2) list.collapse list.size(3) order.refl path_image_cons_union sup.bounded_iff zero_less_diff zero_order(3))
      then have "path_image ?p1_tl \<inter> path_image p2 \<subseteq> {pathstart p1, pathstart p2}"
        using less by blast 
      moreover have "pathstart p1 \<notin> path_image ?p1_tl"
      proof(rule ccontr)
        assume "\<not> pathstart p1 \<notin> path_image ?p1_tl"
        then have "pathstart p1 \<in> path_image ?p1_tl" by blast
        thus False
          by (metis (no_types, lifting) IntI arc_def arc_simple_path less(10) make_polygonal_path_gives_path p1 p1_img path_join_path_ends pathstart_in_path_image pathstart_join simple_path_joinE singletonD)
      qed
      ultimately have "path_image ?p1_tl \<inter> path_image p2 \<subseteq> {pathstart p2}" by blast
      thus ?thesis by blast
    qed
    moreover then have "last vts2 \<noteq> hd ?vts1_tl
        \<longrightarrow> path_image ?p1_tl \<inter> path_image p2 \<subseteq> {pathstart p2}" by blast
    moreover have "last ?vts1_tl = hd vts2"
      by (metis "*" Suc_1 drop_Nil drop_Suc_Cons last_drop last_tl less.prems(8) list.collapse)
    moreover have "arc ?p1_tl \<and> arc p2"
      by (smt (verit, best) "*" Nitpick.size_list_simp(2) Suc_1 arc_imp_simple_path constant_linepath_is_not_loop_free diff_Suc_Suc diff_is_0_eq leD length_greater_0_conv length_tl less.prems(2) less.prems(5) less.prems(9) list.sel(3) make_polygonal_path.elims make_polygonal_path_gives_path order.strict_trans path_join_path_ends pos2 simple_path_joinE)
    ultimately have ih1: "loop_free ?p_tl"
      using less.hyps[of ?vts1_tl ?p_tl vts_tl ?p1_tl p2 vts2] "*" less.prems(3) by fastforce

    have p_tl_img: "path_image ?p_tl = path_image ?p1_tl \<union> path_image p2"
      by (metis (no_types, lifting) "*" Suc_1 Suc_le_eq \<open>2 \<le> length vts2\<close> \<open>last (tl vts1) = hd vts2\<close> \<open>vts_tl = tl vts1 @ tl vts2\<close> hd_conv_nth last_conv_nth length_greater_0_conv length_tl less.prems(3) less_diff_conv make_polygonal_path_image_append_alt order_less_le_trans path_image_join plus_1_eq_Suc polygon_pathfinish polygon_pathstart pos2)

    have 1: "length [a, b] < length vts1" using \<open>3 \<le> length vts1\<close> by fastforce
    moreover have 2: "p = make_polygonal_path vts" using less.prems(1) by auto
    moreover have 3: "?l = make_polygonal_path [a, b]" by simp
    moreover have 4: "?p_tl = make_polygonal_path vts_tl" using less by simp
    moreover have 5: "vts = [a, b] @ tl vts_tl"
      using ab \<open>3 \<le> length vts\<close> append_eq_Cons_conv by fastforce
    moreover have 6: "loop_free ?l \<and> loop_free ?p_tl"
    proof-
      have "sublist [a, b] vts1"
        by (metis (no_types, opaque_lifting) "1" Cons_nth_drop_Suc Suc_lessD ab append_Cons drop0 length_Cons less.prems(4) list.sel(1) list.sel(3) list.size(3) sublist_take take0 take_Suc_Cons)
      then have "loop_free (make_polygonal_path [a, b])"
        using sublist_is_loop_free "*" less.prems(2) less.prems(5) by fastforce
      then have "loop_free ?l" using make_polygonal_path.simps(3) by simp
      thus ?thesis using ih1 by simp
    qed
    moreover have 9: "last [a, b] = hd vts_tl" by (simp add: ab)
    moreover have 10: "arc ?l \<and> arc ?p_tl"
    proof-
      have "pathstart ?p_tl = b"
        by (metis "6" ab constant_linepath_is_not_loop_free hd_conv_nth make_polygonal_path.simps(1) polygon_pathstart)
      moreover have "pathfinish ?p_tl \<noteq> b"
      proof(rule ccontr)
        assume "\<not> pathfinish ?p_tl \<noteq> b"
        have "pathfinish ?p_tl = pathfinish p2"
          by (smt (verit) "5" "9" Nil_tl \<open>2 \<le> length vts2\<close> \<open>\<not> pathfinish (make_polygonal_path vts_tl) \<noteq> b\<close> ab arc_distinct_ends last_append last_conv_nth last_tl length_tl less.prems(3) less.prems(4) less.prems(9) list.size(3) not_numeral_le_zero polygon_pathfinish polygon_pathstart)
        moreover have "b \<in> path_image p1"
          by (metis list.size(3)"1" Cons_nth_drop_Suc Suc_lessD UnCI ab append_eq_conv_conj drop0 hd_append2 hd_conv_nth length_Cons less.prems(2) less.prems(4) list.distinct(1) list.sel(3) path_image_cons_union pathstart_in_path_image polygon_pathstart tl_append2)
        moreover have "b \<noteq> pathstart p1"
          by (metis (no_types, lifting) "1" "6" ab constant_linepath_is_not_loop_free dual_order.strict_trans hd_append2 hd_conv_nth length_greater_0_conv less.prems(2) less.prems(4) list.sel(1) list.size(3) polygon_pathstart)
        moreover have "b \<noteq> pathfinish p2"
          by (metis (no_types, lifting) Int_insert_right_if1 arc_distinct_ends calculation(2) calculation(3) insert_absorb insert_iff insert_not_empty less.prems(6) less.prems(9) pathfinish_in_path_image subset_iff)
        ultimately show False
          using \<open>\<not> pathfinish (make_polygonal_path vts_tl) \<noteq> b\<close> by fastforce
      qed
      ultimately have "pathstart ?p_tl \<noteq> pathfinish ?p_tl" by simp
      then have "arc ?p_tl"
        using ih1 arc_def loop_free_cases make_polygonal_path_gives_path by metis
      moreover have "arc ?l" by (metis "6" arc_linepath constant_linepath_is_not_loop_free)
      ultimately show ?thesis by blast
    qed
    moreover have 7: "path_image ?l \<inter> path_image ?p_tl \<subseteq> {pathstart ?l, pathstart ?p_tl}"
    proof-
      have "path_image ?l \<subseteq> path_image p1"
        by (metis Un_iff \<open>loop_free (make_polygonal_path (tl vts1)) \<and> loop_free p2\<close> \<open>vts_tl = tl vts1 @ tl vts2\<close> ab constant_linepath_is_not_loop_free hd_append2 hd_conv_nth make_polygonal_path.simps(1) p1 path_image_join pathfinish_linepath polygon_pathstart subsetI)
      then have "path_image ?l \<inter> path_image p2 \<subseteq> {pathstart p1, pathstart p2}"
        using less.prems(6) by auto
      moreover have "pathstart p2 \<notin> path_image ?l"
        by (smt (verit, ccfv_threshold) "10" Int_insert_left_if1 \<open>arc (make_polygonal_path (tl vts1)) \<and> arc p2\<close> \<open>last (tl vts1) = hd vts2\<close> \<open>loop_free (make_polygonal_path (tl vts1)) \<and> loop_free p2\<close> arc_def arc_distinct_ends arc_join_eq_alt constant_linepath_is_not_loop_free hd_conv_nth insert_absorb last_conv_nth less.prems(3) less.prems(9) make_polygonal_path.simps(1) p1 path_join_eq pathfinish_in_path_image polygon_pathfinish polygon_pathstart singleton_insert_inj_eq')
      ultimately have "path_image ?l \<inter> path_image ?p_tl \<subseteq> {pathstart p1, pathstart ?p1_tl}"
        using p1_img p_tl_img by blast
      moreover have "pathstart ?p1_tl = pathstart ?p_tl"
        by (metis "2" less.prems(2) make_polygonal_path_gives_path p p1 path_join_path_ends)
      moreover have "pathstart p1 = pathstart ?l" by (simp add: p1)
      ultimately show ?thesis by argo
    qed
    moreover have 8: "last vts_tl \<noteq> hd [a, b]
        \<longrightarrow> path_image ?l \<inter> path_image ?p_tl \<subseteq> {pathstart ?p_tl}"
    proof clarify
      fix x
      assume a1: "last vts_tl \<noteq> hd [a, b]"
      assume a2: "x \<in> path_image ?l"
      assume a3: "x \<in> path_image ?p_tl"
      
      have "hd vts1 \<noteq> last vts2"
        using less.prems
        by (metis a1 \<open>vts_tl = tl vts1 @ tl vts2\<close> ab arc_distinct_ends constant_linepath_is_not_loop_free hd_append2 last_appendR last_tl length_tl list.sel(1) list.size(3) make_polygonal_path.simps(1) polygon_pathfinish polygon_pathstart)
      then have p1_p2_int: "path_image p1 \<inter> path_image p2 \<subseteq> {pathstart p2}"
        using less.prems by argo

      have "x \<noteq> pathstart ?l"
      proof(rule ccontr)
        assume **: "\<not> x \<noteq> pathstart ?l"
        have "pathstart ?l \<notin> path_image ?p1_tl"
          by (metis Int_iff arc_distinct_ends arc_join_eq_alt empty_iff insertE less.prems(2) less.prems(9) make_polygonal_path_gives_path p1 path_join_path_ends pathstart_in_path_image)
        then have "pathstart ?l \<in> path_image p2" using p1_img p_tl_img ** a3 by blast
        then have "pathstart ?l \<in> path_image p1 \<inter> path_image p2"
          by (metis IntI p1 pathstart_in_path_image pathstart_join)
        moreover have "pathstart ?l \<noteq> pathstart p2"
          by (metis arc_distinct_ends constant_linepath_is_not_loop_free hd_conv_nth last_conv_nth less.prems(2) less.prems(3) less.prems(5) less.prems(8) less.prems(9) make_polygonal_path.simps(1) p1 pathstart_join polygon_pathfinish polygon_pathstart)
        ultimately show False using p1_p2_int by blast
      qed
      moreover have "x = pathstart ?l \<or> x = pathstart ?p_tl" using 7 a2 a3 by blast
      ultimately show "x = pathstart ?p_tl" by fast
    qed
    ultimately have ?case using less.hyps[of "[a, b]" p vts ?l ?p_tl vts_tl] by blast
  }
  ultimately show ?case using less 1 by linarith
qed

lemma sublist_path_image_subset:
  assumes "sublist vts1 vts2"
  assumes "length vts1 \<ge> 1"
  shows "path_image (make_polygonal_path vts1) \<subseteq> path_image (make_polygonal_path vts2)"
proof-
  let ?p1 = "make_polygonal_path vts1"
  let ?p2 = "make_polygonal_path vts2"
  let ?m = "length vts1"
  let ?n = "length vts2"
  have n_geq_m: "?n \<ge> ?m" by (simp add: assms(1) sublist_length_le)

  have ?thesis if *: "length vts1 = 1"
  proof-
    have "path_image ?p1 = {vts1!0}"
      by (metis Cons_nth_drop_Suc One_nat_def closed_segment_idem drop0 drop_eq_Nil le_numeral_extra(4) make_polygonal_path.simps(2) path_image_linepath that zero_less_one)
    moreover have "vts1!0 \<in> set vts2"
      by (metis assms(1) less_numeral_extra(1) nth_mem set_mono_sublist subsetD that)
    ultimately show ?thesis
      using vertices_on_path_image by force
  qed
  moreover have ?thesis if *: "length vts1 \<ge> 2"
  proof-
    obtain pre post where sublist: "vts2 = pre @ vts1 @ post"
      using assms(1) unfolding sublist_def by blast
    let ?i = "length pre"
    let ?j = "length vts1"
    let ?k = "?i + ?j"
    let ?x1 = "(2^?i - 1)/2^(?i)::real"
    let ?x2 = "(2^(?k-1) - 1)/(2^(?k-1))::real"
    let ?x = "(2 ^ (?i - 1) - 1) / 2 ^ (?i - 1)::real"
    have "path_image ?p1 = ?p2 ` {?x1..?x2}" if **: "length post \<ge> 1"
      using sublist * ** vts_sublist_path_image[of ?p2 vts2 ?p1 vts1 ?j ?i ?n ?m ?k ?x1 ?x2]
      by fastforce
    moreover have "path_image ?p1 = ?p2 ` {?x1..1}" if **: "length post = 0" 
    proof-
      have sublist: "vts2 = pre @ vts1" using ** sublist by blast
      moreover have "vts1 = drop ?i vts2" using sublist * by simp
      moreover have "1 \<le> ?i + 1 \<and> ?i + 1 < length vts2" using sublist * ** by simp
      ultimately show ?thesis
        using vts_split_path_image[of ?p2 vts2 _ _ ?p1 vts1 "?i + 1" ?n ?x1] add_diff_cancel_right'
        by metis
    qed
    moreover have "?p2 ` {?x1..?x2} \<subseteq> path_image ?p2 \<and> ?p2 ` {?x1..1} \<subseteq> path_image ?p2"
    proof-
      have "{?x1..?x2} \<subseteq> {0..1} \<and> {?x1..1} \<subseteq> {0..1}" by simp
      thus ?thesis unfolding path_image_def by blast
    qed
    ultimately show ?thesis by (metis less_one linorder_not_le)
  qed
  ultimately show ?thesis using assms by linarith
qed

lemma integral_on_edge_subset_integral_on_path:
  assumes "p = make_polygonal_path vts" and
          "(i::int) \<in> {0..<((length vts) - 1)}" and
          "x = vts!i" and
          "y = vts!(i+1)"
  shows "{v. integral_vec v \<and> v \<in> path_image (linepath x y)}
          \<subseteq> {v. integral_vec v \<and> v \<in> path_image p}"
  using assms edge_subset_path_image by blast

lemma sublist_pair_integral_subset_integral_on_path:
  assumes "p = make_polygonal_path vts" and
          "sublist [x, y] vts"
  shows "{v. integral_vec v \<and> v \<in> path_image (linepath x y)}
          \<subseteq> {v. integral_vec v \<and> v \<in> path_image p}"
  using assms integral_on_edge_subset_integral_on_path
proof-
  obtain pre post where vts: "vts = pre @ [x, y] @ post" using assms(2) sublist_def by blast
  let ?i = "length pre"
  have "x = vts!?i" using vts by simp
  moreover have "y = vts!(?i + 1)"
    by (metis vts add.right_neutral append_Cons nth_Cons_Suc nth_append_length nth_append_length_plus plus_1_eq_Suc)
  moreover have "?i \<in> {0..<((length vts) - 1)}" using vts by force
  ultimately show ?thesis using assms(1) integral_on_edge_subset_integral_on_path by auto
qed

lemma sublist_integral_subset_integral_on_path:
  assumes "length ell \<ge> 2"
  assumes "p = make_polygonal_path vts" and
          "sublist ell vts"
  shows "{v. integral_vec v \<and> v \<in> path_image (make_polygonal_path ell)}
          \<subseteq> {v. integral_vec v \<and> v \<in> path_image p}"
proof-
  obtain pre post where vts: "vts = pre @ ell @ post" using assms(3) sublist_def by blast
  then have len_vts: "length vts \<ge> 2"
    using assms(1) 
    by auto
  let ?i = "length pre"
  have "v \<in> path_image p" if *: "v \<in> path_image (make_polygonal_path ell)" for v
  proof - 
    have "\<exists>j::nat. v \<in> path_image (linepath (ell ! j) (ell  ! (j+1))) \<and> j+1 < length ell"
      using * polygonal_path_image_linepath_union assms(1) 
      by (meson less_diff_conv make_polygonal_path_image_property)
    then obtain j where v_in: "v \<in> path_image (linepath (ell ! j) (ell  ! (j+1)))"  "j+1 < length ell"
      by auto
    then have ell_at: "ell ! j = vts ! (j + length pre) \<and> ell ! (j+1) = vts ! (j + 1 + length pre)"
      using vts 
      by (simp add: nth_append)
    then have v_in2: "v \<in> path_image (linepath (vts ! (j + length pre)) (vts ! (j + length pre + 1)))"
      using v_in(1) by simp
    have "j + 1 + length pre < length vts"
      using ell_at v_in(2) vts by auto
    then have j_plus: "j + length pre < length vts - 1"
      by auto
    then show ?thesis using v_in2 linepaths_subset_make_polygonal_path_image[OF len_vts j_plus]  assms(1)
      assms(2) by auto
  qed
  then show ?thesis by blast
qed

section "Reversing Polygonal Path Vertex List"

lemma rev_vts_path_image:
  shows "path_image (make_polygonal_path (rev vts)) = path_image (make_polygonal_path vts)"
proof - 
  { assume "length vts \<le> 1"
    then have ?thesis
      by (smt (verit, best) One_nat_def Suc_length_conv le_SucE le_zero_eq length_0_conv rev.simps(1) rev_singleton_conv)
  } moreover
  { fix x
    assume *: "x \<in> path_image (make_polygonal_path (rev vts)) \<and> length vts \<ge> 2"
    then obtain k where k_prop: "k<length (rev vts) - 1 \<and> x \<in> path_image (linepath (rev vts ! k) (rev vts ! (k + 1)))"
      using make_polygonal_path_image_property[of "rev vts"] by auto
    have p1: "rev vts ! k = vts ! (length vts - k - 1)"
      using rev_nth 
      by (metis Suc_lessD \<open>k < length (rev vts) - 1 \<and> x \<in> path_image (linepath (rev vts ! k) (rev vts ! (k + 1)))\<close> add.commute diff_diff_left length_rev less_diff_conv plus_1_eq_Suc)
    have p2: "rev vts ! (k + 1) = vts ! (length vts - k - 2)"
      using rev_nth[of "k+1" vts] k_prop
      by force
    then have "x \<in> path_image (linepath (vts ! (length vts - k - 1)) (vts ! (length vts - k - 2)))"
      using k_prop  p1 p2 by auto
    then have "x \<in> path_image (linepath (vts ! (length vts - k - 2)) (vts ! (length vts - k - 1)))"
      using reversepath_linepath path_image_reversepath 
      by metis
    then have "x \<in> path_image (make_polygonal_path vts)"
      using linepaths_subset_make_polygonal_path_image * k_prop
      by (smt (verit, best) Nat.diff_add_assoc add.commute add_diff_cancel_left' diff_le_self length_rev less_Suc_eq less_diff_conv linorder_not_less nat_1_add_1 nat_neq_iff plus_1_eq_Suc subsetD)
  } moreover
  { fix x
    assume *: "x \<in> path_image (make_polygonal_path vts) \<and> length vts \<ge> 2"
    then obtain k where k_prop: "k<length vts - 1 \<and> x \<in> path_image (linepath (vts ! k) (vts ! (k + 1)))"
      using make_polygonal_path_image_property[of vts] by auto
    have p1: "vts ! k = (rev vts) ! (length vts - k - 1)"
      using rev_nth k_prop 
      by (metis Suc_eq_plus1 Suc_lessD diff_diff_left length_rev less_diff_conv rev_rev_ident)
    have p2: "vts ! (k + 1) = (rev vts) ! (length vts - k - 2)"
      using rev_nth[of "k+1"] 
      by (smt (verit) Suc_eq_plus1 add_2_eq_Suc' diff_diff_left k_prop length_rev less_diff_conv rev_rev_ident)
    then have "x \<in> path_image (linepath (rev vts ! (length vts - k - 2)) (rev vts ! (length vts - k - 1)))"
      using reversepath_linepath path_image_reversepath 
      by (metis k_prop p1)
    then have "x \<in> path_image (make_polygonal_path (rev vts))"
      using linepaths_subset_make_polygonal_path_image k_prop *
      by (smt (verit, best) Suc_1 Suc_diff_Suc Suc_eq_plus1 Suc_le_eq Suc_lessD bot_nat_0.not_eq_extremum diff_commute diff_diff_left diff_less length_rev less_numeral_extra(1) subsetD zero_less_diff)
  }
  ultimately show ?thesis by force
qed

lemma rev_vts_is_loop_free:
  assumes "p = make_polygonal_path vts"
  assumes "loop_free p"
  shows "loop_free (make_polygonal_path (rev vts))"
  using assms
proof(induct "length vts" arbitrary: p vts)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "Suc n \<ge> 2"
    by (metis One_nat_def Suc_length_conv constant_linepath_is_not_loop_free le_SucE le_add1 le_numeral_Suc length_greater_0_conv list.size(3) make_polygonal_path.simps(2) numeral_One plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26))
  moreover
  { assume *: "Suc n = 2"
    then obtain a b where ab: "p = linepath a b"
      using Suc.prems make_polygonal_path.simps(3)
      by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc One_nat_def Suc.hyps(2) Suc_1 diff_Suc_1 drop_0 drop_Suc length_0_conv length_tl zero_less_Suc)
    moreover then have "a \<noteq> b" using Suc.prems(2) constant_linepath_is_not_loop_free by blast
    ultimately have "loop_free (linepath b a)" by (simp add: linepath_loop_free)
    moreover have "make_polygonal_path (rev vts) = linepath b a"
      by (smt (z3) "*" Cons_nth_drop_Suc One_nat_def Suc.hyps(2) Suc.prems(1) Suc_1 Suc_diff_Suc ab butlast_snoc diff_Suc_1 drop0 hd_conv_nth hd_rev last_conv_nth length_butlast length_rev lessI linepath_1' make_polygonal_path.simps(3) nth_append_length pathstart_def pathstart_linepath pos2 rev.simps(2) rev_is_Nil_conv rev_take take_eq_Nil)
    ultimately have ?case by simp
  } moreover
  { assume *: "Suc n > 2"
    let ?vts' = "butlast vts"
    let ?p' = "make_polygonal_path ?vts'"
    let ?vts'_rev = "rev ?vts'"
    let ?p'_rev = "make_polygonal_path ?vts'_rev"

    let ?vts_rev = "rev vts"
    let ?p_rev = "make_polygonal_path ?vts_rev"

    obtain y z where yz: "y = last ?vts' \<and> z = last vts" by blast
    let ?l = "linepath y z"
    let ?l_rev = "linepath z y"
    have "loop_free ?p'"
      by (metis "*" Suc.hyps(2) Suc.prems(1) Suc.prems(2) butlast_conv_take diff_Suc_1 le_add2 less_Suc_eq_le plus_1_eq_Suc take_i_is_loop_free)
    then have loop_free_p'_rev: "loop_free ?p'_rev" using Suc.hyps by force
    moreover have "rev vts = z # ?vts'_rev"
      by (metis Suc.hyps(2) yz append_butlast_last_id length_0_conv nat.distinct(1) rev_eq_Cons_iff rev_rev_ident)
    moreover have "y = hd ?vts'_rev" using yz by (simp add: hd_rev)
    ultimately have p_rev: "?p_rev = ?l_rev +++ ?p'_rev"
      by (smt (verit, best) constant_linepath_is_not_loop_free list.sel(1) make_polygonal_path.elims make_polygonal_path.simps(4))

    have "[y, z] = drop (n-1) vts"
      using yz Suc.hyps(2)
      by (metis (no_types, opaque_lifting) "*" Cons_nth_drop_Suc Suc_1 Suc_diff_Suc Suc_lessD Suc_n_not_le_n append_butlast_last_id append_eq_conv_conj diff_Suc_1 last_conv_nth length_0_conv length_butlast less_nat_zero_code linorder_not_le nth_take)
    then have "?l = make_polygonal_path (drop (n-1) vts)"
      using make_polygonal_path.simps by metis
    moreover have "?p' = make_polygonal_path (take n vts)"
      using Suc.hyps(2) by (metis butlast_conv_take diff_Suc_1)
    ultimately have "path_image ?l \<inter> path_image ?p' \<subseteq> {pathstart ?l, pathstart ?p'}"
      using loop_free_split_int
      by (smt (verit, ccfv_SIG) Int_commute Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_1 Suc_le_mono \<open>2 \<le> Suc n\<close> insert_commute lessI)
    moreover have "path_image ?l = path_image ?l_rev" by auto
    moreover have "path_image ?p' = path_image ?p'_rev"
      using "*" Suc.hyps(2) rev_vts_path_image by force
    moreover have "pathstart ?l = pathfinish ?l_rev" by simp
    moreover have "pathstart ?p' = pathfinish ?p'_rev"
      by (metis Nil_is_rev_conv last.simps last_conv_nth last_rev list.distinct(1) list.exhaust_sel make_polygonal_path.simps(1) make_polygonal_path.simps(2) nth_Cons_0 polygon_pathfinish polygon_pathstart)
    ultimately have path_image_int:
        "path_image ?l_rev \<inter> path_image ?p'_rev \<subseteq> {pathfinish ?l_rev, pathfinish ?p'_rev}"
      by argo

    have 1: "pathfinish ?l_rev = pathstart ?p'_rev"
      by (metis make_polygonal_path_gives_path p_rev path_join_path_ends)
    { assume "pathfinish ?p'_rev = pathstart ?l_rev"
      then have ?case using simple_path_join_loop 1 p_rev path_image_int
        by (smt (verit, del_insts) Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_1 \<open>linepath y z = make_polygonal_path (drop (n - 1) vts)\<close> \<open>loop_free (make_polygonal_path (rev (butlast vts)))\<close> constant_linepath_is_not_loop_free diff_Suc_Suc drop_i_is_loop_free dual_order.eq_iff insert_commute linepath_loop_free make_polygonal_path_gives_path path_linepath pathfinish_linepath pathstart_linepath simple_path_cases simple_path_def)
    } moreover
    { assume "pathfinish ?p'_rev \<noteq> pathstart ?l_rev"
      then have "pathstart p \<noteq> pathfinish p"
        by (metis Suc.prems(1) \<open>loop_free (make_polygonal_path (butlast vts))\<close> \<open>pathstart (make_polygonal_path (butlast vts)) = pathfinish (make_polygonal_path (rev (butlast vts)))\<close> butlast_conv_take constant_linepath_is_not_loop_free last_conv_nth less_nat_zero_code make_polygonal_path.simps(1) nat_neq_iff nth_take pathstart_linepath polygon_pathfinish polygon_pathstart take_eq_Nil yz)
      then have "arc p"
        by (metis Suc.prems(1) Suc.prems(2) arc_def loop_free_cases make_polygonal_path_gives_path)
      then have "path_image ?l_rev \<inter> path_image ?p'_rev \<subseteq> {pathstart ?p'_rev}"
        using loop_free_arc_split_int
        by (metis "1" Int_commute Suc.hyps(2) Suc.prems(1) Suc.prems(2) \<open>2 \<le> Suc n\<close> \<open>linepath y z = make_polygonal_path (drop (n - 1) vts)\<close> \<open>make_polygonal_path (butlast vts) = make_polygonal_path (take n vts)\<close> \<open>path_image (linepath y z) = path_image (linepath z y)\<close> \<open>path_image (make_polygonal_path (butlast vts)) = path_image (make_polygonal_path (rev (butlast vts)))\<close> \<open>pathstart (linepath y z) = pathfinish (linepath z y)\<close> le_numeral_Suc lessI numerals(1) pred_numeral_simps(2) semiring_norm(26))
      moreover have "arc ?l_rev"
        by (metis Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_1 \<open>[y, z] = drop (n - 1) vts\<close> arc_linepath constant_linepath_is_not_loop_free diff_Suc_Suc drop_i_is_loop_free dual_order.refl make_polygonal_path.simps(3))
      moreover have "arc ?p'_rev"
      proof-
        have "?p'_rev 0 = last (butlast vts)" by (metis "1" pathfinish_linepath pathstart_def yz)
        moreover have "?p'_rev 1 = hd (butlast vts)"
          by (metis \<open>loop_free (make_polygonal_path (butlast vts))\<close> \<open>pathstart (make_polygonal_path (butlast vts)) = pathfinish (make_polygonal_path (rev (butlast vts)))\<close> constant_linepath_is_not_loop_free hd_conv_nth make_polygonal_path.simps(1) pathfinish_def polygon_pathstart)
        moreover have "last (butlast vts) \<noteq> hd (butlast vts)" using Suc.prems
          by (metis (no_types, lifting) "*" Suc.hyps(2) Suc_1 diff_is_0_eq index_Cons index_last leD length_butlast less_diff_conv less_imp_le_nat list.collapse list.size(3) loop_free_polygonal_path_vts_distinct not_one_le_zero plus_1_eq_Suc)
        ultimately have "?p'_rev 0 \<noteq> ?p'_rev 1" by simp
        thus ?thesis using loop_free_p'_rev
          by (metis arc_def loop_free_cases make_polygonal_path_gives_path pathfinish_def pathstart_def)
      qed
      ultimately have ?case
        using arc_join_eq[OF 1] arc_imp_simple_path p_rev simple_path_def by auto
    }
    ultimately have ?case by blast
  }
  ultimately show ?case by linarith
qed

lemma rev_vts_is_polygon:
  assumes "polygon_of p vts"
  shows "polygon (make_polygonal_path (rev vts))"
  using rev_vts_is_loop_free assms
  unfolding polygon_of_def polygon_def simple_path_def 
  using make_polygonal_path_gives_path
  by (metis One_nat_def closed_path_def UNIV_def length_greater_0_conv polygon_pathfinish polygon_pathstart polygonal_path_def rangeI rev.simps(1) rev_nth rev_rev_ident)

end