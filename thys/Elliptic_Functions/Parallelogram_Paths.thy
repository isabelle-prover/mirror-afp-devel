subsection \<open>Parallelogram-shaped paths\<close>
theory Parallelogram_Paths
  imports "HOL-Complex_Analysis.Complex_Analysis"
begin

definition parallelogram_path :: "'a :: real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a" where
  "parallelogram_path z a b = 
     linepath z (z + a) +++ linepath (z + a) (z + a + b) +++ 
     linepath (z + a + b) (z + b) +++ linepath (z + b) z"

lemma path_parallelogram_path [intro]: "path (parallelogram_path z a b)"
  and valid_path_parallelogram_path [intro]: "valid_path (parallelogram_path z a b)"
  and pathstart_parallelogram_path [simp]: "pathstart (parallelogram_path z a b) = z"
  and pathfinish_parallelogram_path [simp]: "pathfinish (parallelogram_path z a b) = z"
  by (auto simp: parallelogram_path_def intro!: valid_path_join)

lemma parallelogram_path_altdef:
  fixes z a b :: complex
  defines "g \<equiv> (\<lambda>w. z + Re w *\<^sub>R a + Im w *\<^sub>R b)"
  shows   "parallelogram_path z a b = g \<circ> rectpath 0 (1 + \<i>)"
  by (simp add: parallelogram_path_def rectpath_def g_def Let_def o_def joinpaths_def
                fun_eq_iff linepath_def scaleR_conv_of_real algebra_simps)

lemma
  fixes f :: "complex \<Rightarrow> complex" and z \<omega>1 \<omega>2 :: complex
  defines "I \<equiv> (\<lambda>a b. contour_integral (linepath (z + a) (z + b)) f)"
  defines "P \<equiv> parallelogram_path z \<omega>1 \<omega>2"
  assumes "continuous_on (path_image P) f"
  shows contour_integral_parallelogram_path:
          "contour_integral P f =
             (I 0 \<omega>1 - I \<omega>2 (\<omega>1 + \<omega>2)) - (I 0 \<omega>2 - I \<omega>1 (\<omega>1 + \<omega>2))"
    and contour_integral_parallelogram_path':
          "contour_integral P f =
             contour_integral (linepath z (z + \<omega>1)) (\<lambda>x. f x - f (x + \<omega>2)) -
             contour_integral (linepath z (z + \<omega>2)) (\<lambda>x. f x - f (x + \<omega>1))"
proof -
  define L where "L = (\<lambda>a b. linepath (z + a) (z + b))"
  have I: "(f has_contour_integral (I a b)) (L a b)"
    if "closed_segment (z + a) (z + b) \<subseteq> path_image P" for a b
    unfolding I_def L_def
    by (intro has_contour_integral_integral contour_integrable_continuous_linepath
              continuous_on_subset[OF assms(3)] that)
  have "(f has_contour_integral
          (I 0 \<omega>1 + (I \<omega>1 (\<omega>1 + \<omega>2) + ((-I \<omega>2 (\<omega>1 + \<omega>2)) + (-I 0 \<omega>2)))))
          (L 0 \<omega>1 +++ L \<omega>1 (\<omega>1 + \<omega>2) +++ reversepath (L \<omega>2 (\<omega>1 + \<omega>2)) +++ reversepath (L 0 \<omega>2))"
    unfolding P_def parallelogram_path_def
    by (intro has_contour_integral_join valid_path_join valid_path_linepath has_contour_integral_reversepath I)
       (auto simp: parallelogram_path_def path_image_join closed_segment_commute P_def L_def add_ac)
  thus "contour_integral P f =
           (I 0 \<omega>1 - I \<omega>2 (\<omega>1 + \<omega>2)) - (I 0 \<omega>2 - I \<omega>1 (\<omega>1 + \<omega>2))"
    by (intro contour_integral_unique)
       (simp_all add: parallelogram_path_def P_def L_def algebra_simps)

  also have "I 0 \<omega>2 - I \<omega>1 (\<omega>1 + \<omega>2) = contour_integral (L 0 \<omega>2) (\<lambda>x. f x - f (x + \<omega>1))"
  proof -
    have "(f has_contour_integral I \<omega>1 (\<omega>1 + \<omega>2)) (L \<omega>1 (\<omega>1 + \<omega>2))"
      by (rule I) (auto simp: parallelogram_path_def path_image_join P_def add_ac)
    also have "L \<omega>1 (\<omega>1 + \<omega>2) = (+) \<omega>1 \<circ> L 0 \<omega>2"
      by (simp add: linepath_def L_def fun_eq_iff algebra_simps)
    finally have "((\<lambda>x. f (x + \<omega>1)) has_contour_integral I \<omega>1 (\<omega>1 + \<omega>2)) (L 0 \<omega>2)"
      unfolding has_contour_integral_translate .
    hence "((\<lambda>x. f x - f (x + \<omega>1)) has_contour_integral (I 0 \<omega>2 - I \<omega>1 (\<omega>1 + \<omega>2))) (L 0 \<omega>2)"
      by (intro has_contour_integral_diff I) 
         (auto simp: parallelogram_path_def path_image_join closed_segment_commute L_def P_def)
    thus ?thesis
      by (rule contour_integral_unique [symmetric])
  qed

  also have "I 0 \<omega>1 - I \<omega>2 (\<omega>1 + \<omega>2) = contour_integral (L 0 \<omega>1) (\<lambda>x. f x - f (x + \<omega>2))"
  proof -
    have "(f has_contour_integral I \<omega>2 (\<omega>1 + \<omega>2)) (L \<omega>2 (\<omega>1 + \<omega>2))"
      by (rule I) (auto simp: parallelogram_path_def path_image_join closed_segment_commute P_def L_def add_ac)
    also have "L \<omega>2 (\<omega>1 + \<omega>2) = (+) \<omega>2 \<circ> L 0 \<omega>1"
      by (simp add: linepath_def L_def o_def algebra_simps)
    finally have "((\<lambda>x. f (x + \<omega>2)) has_contour_integral I \<omega>2 (\<omega>1 + \<omega>2)) (L 0 \<omega>1)"
      unfolding has_contour_integral_translate .
    hence "((\<lambda>x. f x - f (x + \<omega>2)) has_contour_integral (I 0 \<omega>1 - I \<omega>2 (\<omega>1 + \<omega>2))) (L 0 \<omega>1)"
      by (intro has_contour_integral_diff I) 
         (auto simp: parallelogram_path_def path_image_join closed_segment_commute P_def)
    thus ?thesis
      by (rule contour_integral_unique [symmetric])
  qed

  finally show "contour_integral P f =
                  contour_integral (linepath z (z + \<omega>1)) (\<lambda>x. f x - f (x + \<omega>2)) -
                  contour_integral (linepath z (z + \<omega>2)) (\<lambda>x. f x - f (x + \<omega>1))"
    by (simp add: L_def add_ac)
qed

end