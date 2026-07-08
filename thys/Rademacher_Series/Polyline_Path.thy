(*
  File:     Polyline_Path.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Building a path from a list of points\<close>
theory Polyline_Path
  imports "HOL-Library.Sublist" "Path_Automation.Path_Automation"
begin

(* TODO Move *)
lemma weak_wf_pathlist_altdef:
  "weak_wf_pathlist ps \<longleftrightarrow> ps \<noteq> [] \<and> successively (\<lambda>p q. pathfinish p = pathstart q) ps"
  by (induction ps rule: weak_wf_pathlist.induct) auto

(* TODO Move *)
lemma path_image_joinpaths_list_subset:
  "ps \<noteq> [] \<Longrightarrow> path_image (joinpaths_list ps) \<subseteq> (\<Union>p\<in>set ps. path_image p)"
  by (induction ps rule: joinpaths_list.induct) (use path_image_join_subset in auto)

definition polyline_path :: "'a :: real_normed_vector list \<Rightarrow> real \<Rightarrow> 'a" where
  "polyline_path xs =
     (if length xs = 1 then linepath (hd xs) (hd xs) else joinpaths_list (map2 linepath xs (tl xs)))"

lemma pathstart_polyline_path:
  assumes "xs \<noteq> []"
  shows   "pathstart (polyline_path xs) = hd xs"
proof (cases "length xs = 1")
  case False
  hence "tl xs \<noteq> []"
    using assms by (cases xs) auto
  thus ?thesis using assms
    by (auto simp: polyline_path_def pathstart_joinpaths_list hd_map case_prod_unfold hd_zip)
qed (auto simp: polyline_path_def)

lemma pathfinish_polyline_path:
  assumes "xs \<noteq> []"
  shows   "pathfinish (polyline_path xs) = last xs"
proof (cases "length xs = 1")
  case True
  thus ?thesis
    by (cases xs) (auto simp: polyline_path_def)
next
  case False
  from assms have "length xs \<noteq> 0"
    by auto
  with False have "length xs \<ge> 2"
    by linarith    
  from False have *: "tl xs \<noteq> []"
    using assms by (cases xs) auto
  have "last (zip xs (tl xs)) = zip xs (tl xs) ! (length xs - 2)"
    using False * by (subst last_conv_nth) (auto simp: eval_nat_numeral)
  also have "snd \<dots> = xs ! (length xs - 1)"
    using \<open>length xs \<ge> 2\<close> by (subst nth_zip) (auto simp: nth_tl simp flip: Suc_diff_le)
  also have "\<dots> = last xs"
    using \<open>length xs \<ge> 2\<close> by (subst last_conv_nth) auto
  finally show ?thesis using assms False *
    by (auto simp: polyline_path_def pathfinish_joinpaths_list last_map case_prod_unfold)
qed

lemma polyline_path_welldefined:
  assumes "xs \<noteq> []"
  shows   "successively (\<lambda>p q. pathfinish p = pathstart q) (map2 linepath xs (tl xs))"
proof (cases "length xs = 1")
  case True
  thus ?thesis
    by (cases xs) auto
next
  case False
  have "length xs \<noteq> 0"
    using assms by auto
  with False have "length xs \<ge> 2"
    by linarith
  thus "successively (\<lambda>p q. pathfinish p = pathstart q) (map2 linepath xs (tl xs))"
  proof (induction xs rule: induct_list012)
    case (3 x y zs)
    have IH: 
      "successively (\<lambda>p q. pathfinish p = pathstart q) (map2 linepath (y # zs) (tl (y # zs)))"
      if "zs \<noteq> []"
      by (rule "3.IH") (use \<open>zs \<noteq> []\<close> in \<open>auto intro!: Suc_leI\<close>)
    show ?case using IH
      by (auto simp: successively_Cons hd_map hd_zip)
  qed auto
qed

lemma valid_path_polyline_path [simp, intro]: "valid_path (polyline_path xs)"
proof -
  consider "length xs = 0" | "length xs = 1" | "length xs \<ge> 2"
    by linarith
  thus ?thesis
  proof cases
    assume "length xs \<ge> 2"
    hence [simp]: "tl xs \<noteq> []" "xs \<noteq> []"
      by (cases xs; force)+
    have "valid_path (joinpaths_list (map2 linepath xs (tl xs)))"
    proof (rule valid_path_joinpaths_list)
      show "valid_path_pathlist (map2 linepath xs (tl xs))"
        unfolding valid_path_pathlist_altdef
        using \<open>length xs \<ge> 2\<close> by (simp add: list.pred_map o_def case_prod_unfold list.pred_True)
    next
      have "successively (\<lambda>p q. pathfinish p = pathstart q) (map2 linepath xs (tl xs))"
        using \<open>length xs \<ge> 2\<close> by (intro polyline_path_welldefined) auto
      thus "weak_wf_pathlist (map2 linepath xs (tl xs))"
        unfolding weak_wf_pathlist_altdef using \<open>length xs \<ge> 2\<close> by auto
    qed
    thus ?thesis
      using \<open>length xs \<ge> 2\<close> by (simp add: polyline_path_def)
  qed (auto simp: polyline_path_def)
qed

lemma path_polyline_path [simp, intro]: "path (polyline_path xs)"
  by (rule valid_path_imp_path) auto

lemma polyline_path_subset_convex:
  assumes "convex A" "set xs \<subseteq> A" and [simp]: "xs \<noteq> []"
  shows   "path_image (polyline_path xs) \<subseteq> A"
proof (cases "length xs = 1")
  case True
  thus ?thesis
    using assms by (cases xs) (auto simp: polyline_path_def)
next
  case False
  have "length xs \<noteq> 0"
    by auto
  with False have "length xs \<ge> 2"
    by linarith
  have [simp]: "tl xs \<noteq> []"
    using \<open>length xs \<ge> 2\<close> by (cases xs) auto

  have "path_image (polyline_path xs) = path_image (joinpaths_list (map2 linepath xs (tl xs)))"
    using \<open>length xs \<ge> 2\<close> unfolding polyline_path_def by simp
  also have "\<dots> \<subseteq> (\<Union>l\<in>set (map2 linepath xs (tl xs)). path_image l)"
    by (rule path_image_joinpaths_list_subset) auto
  also have "\<dots> \<subseteq> (\<Union>x\<in>set xs. \<Union>y\<in>set (tl xs). closed_segment x y)"
    using \<open>length xs \<ge> 2\<close> by (fastforce dest: set_zip_leftD set_zip_rightD)
  also have "\<dots> \<subseteq> (\<Union>x\<in>set xs. \<Union>y\<in>set xs. closed_segment x y)"
    by (cases xs) auto
  also have "\<dots> \<subseteq> A"
    by (intro UN_least closed_segment_subset) (use assms in auto)
  finally show ?thesis .
qed

lemma contour_integral_polyline_path:
  assumes "f contour_integrable_on (polyline_path ps)"
  assumes "ps \<noteq> []"
  shows   "contour_integral (polyline_path ps) f =
             (\<Sum>i<length ps-1. contour_integral (linepath (ps ! i) (ps ! Suc i)) f)"
proof (cases "length ps \<ge> 2")
  case True
  have [simp]: "ps \<noteq> []" "tl ps \<noteq> []"
    using True by (cases ps; force)+
  have "contour_integral (polyline_path ps) f =
          contour_integral (joinpaths_list (map2 linepath ps (tl ps))) f "
    unfolding polyline_path_def using True by simp
  also have "\<dots> = (\<Sum>p\<leftarrow>map2 linepath ps (tl ps). contour_integral p f)"
    using polyline_path_welldefined[of ps] assms True
    by (subst contour_integral_joinpaths_list) 
       (auto simp: valid_path_pathlist_altdef weak_wf_pathlist_altdef 
                   list.pred_set list.pred_True polyline_path_def)
  also have "\<dots> = (\<Sum>i<length ps-1. contour_integral (linepath (ps ! i) (tl ps ! i)) f)"
    by (subst sum.list_conv_set_nth) (auto simp: atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<length ps-1. contour_integral (linepath (ps ! i) (ps ! Suc i)) f)"
    by (intro sum.cong) (auto simp: nth_tl)
  finally show ?thesis .
next
  case False
  from \<open>ps \<noteq> []\<close> have "length ps \<noteq> 0"
    by auto
  hence "length ps = 1"
    using False by linarith
  thus ?thesis
    by (auto simp: polyline_path_def)
qed

end