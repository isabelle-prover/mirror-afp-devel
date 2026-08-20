(*  Title:       Ball_Decomposition.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    Lift the paradoxical decomposition of
    \<open>S\<^sup>2\<close> to the closed unit ball \<open>B\<^sup>3\<close>.

    Step 1: \<open>B\<^sup>3 \<setminus> {0}\<close> is paradoxical, by associating
    to each sphere-piece \<open>A\<close> the radial cone
    \<open>{t x | t \<in> (0,1], x \<in> A}\<close>.

    Step 2: the final theory absorbs \<open>{0}\<close> by an off-centre isometry,
    turning the punctured-ball partition into a partition of the closed
    ball.  This theory also retains a simpler SO(3)-only finite-cover
    statement as an auxiliary result.

    This yields the paradoxical decomposition of the full closed ball.
*)

theory Ball_Decomposition
  imports Sphere_Decomposition
begin

text \<open>
  Radial cone construction: take a sphere subset and form the open
  radial cone in the ball.
\<close>

definition cone_of :: "(real^3) set \<Rightarrow> (real^3) set" where
  "cone_of S = {t *\<^sub>R x | t x. 0 < t \<and> t \<le> 1 \<and> x \<in> S}"

lemma cone_of_in_ball3:
  assumes "S \<subseteq> sphere2"
  shows "cone_of S \<subseteq> ball3"
proof
  fix y assume "y \<in> cone_of S"
  then obtain t x where y_eq: "y = t *\<^sub>R x" and t_pos: "0 < t" and t_le: "t \<le> 1"
    and x_in: "x \<in> S"
    unfolding cone_of_def by auto
  from x_in assms have x_sphere: "x \<in> sphere2" by auto
  hence x_norm: "norm x = 1" by (simp add: sphere2_def)
  have "norm y = norm (t *\<^sub>R x)" by (simp add: y_eq)
  also have "\<dots> = \<bar>t\<bar> * norm x" by simp
  also have "\<dots> = t" using t_pos x_norm by simp
  also have "\<dots> \<le> 1" using t_le .
  finally have "norm y \<le> 1" .
  thus "y \<in> ball3" by (simp add: ball3_def)
qed

lemma cone_of_in_ball3_minus_origin:
  assumes "S \<subseteq> sphere2"
  shows "cone_of S \<subseteq> ball3 - {0}"
proof
  fix y assume y_in: "y \<in> cone_of S"
  then obtain t x where y_eq: "y = t *\<^sub>R x" and t_pos: "0 < t" and t_le: "t \<le> 1"
    and x_in: "x \<in> S"
    unfolding cone_of_def by auto
  from cone_of_in_ball3[OF assms] y_in have y_ball: "y \<in> ball3"
    by blast
  from x_in assms have x_sphere: "x \<in> sphere2"
    by auto
  hence x_norm: "norm x = 1"
    by (simp add: sphere2_def)
  have "norm y = norm (t *\<^sub>R x)"
    by (simp add: y_eq)
  also have "\<dots> = t"
    using t_pos x_norm by simp
  finally have "norm y > 0"
    using t_pos by simp
  hence "y \<noteq> 0"
    by auto
  with y_ball show "y \<in> ball3 - {0}"
    by simp
qed

lemma ball3_minus_origin_eq_cone_sphere2:
  "ball3 - {0::real^3} = cone_of sphere2"
proof
  show "ball3 - {0::real^3} \<subseteq> cone_of sphere2"
  proof
    fix y assume y_in: "y \<in> ball3 - {0::real^3}"
    hence y_ball: "y \<in> ball3" and y_ne: "y \<noteq> 0"
      by auto
    define t where "t = norm y"
    define x where "x = (1 / t) *\<^sub>R y"
    have t_pos: "0 < t"
      using y_ne by (simp add: t_def)
    have t_le: "t \<le> 1"
      using y_ball by (simp add: ball3_def t_def)
    have x_sphere: "x \<in> sphere2"
    proof -
      have "norm x = norm ((1 / t) *\<^sub>R y)"
        by (simp add: x_def)
      also have "\<dots> = 1"
        using t_pos by (simp add: t_def)
      finally show ?thesis
        by (simp add: sphere2_def)
    qed
    have y_eq: "y = t *\<^sub>R x"
      using t_pos by (simp add: x_def)
    show "y \<in> cone_of sphere2"
      unfolding cone_of_def
      using y_eq t_pos t_le x_sphere by blast
  qed
  show "cone_of sphere2 \<subseteq> ball3 - {0::real^3}"
    by (rule cone_of_in_ball3_minus_origin) simp
qed

lemma cone_of_UN:
  "cone_of (\<Union>i\<in>I. S i) = (\<Union>i\<in>I. cone_of (S i))"
  unfolding cone_of_def by blast

lemma SO3_image_cone_of:
  assumes "g \<in> SO3"
  shows "g ` cone_of S = cone_of (g ` S)"
proof
  show "g ` cone_of S \<subseteq> cone_of (g ` S)"
  proof
    fix y assume "y \<in> g ` cone_of S"
    then obtain x where y_eq: "y = g x" and x_in: "x \<in> cone_of S"
      by blast
    then obtain t z where x_eq: "x = t *\<^sub>R z" and t_pos: "0 < t" and t_le: "t \<le> 1"
      and z_in: "z \<in> S"
      unfolding cone_of_def by blast
    have "y = t *\<^sub>R g z"
      using assms by (simp add: y_eq x_eq SO3_def rotation_def orthogonal_transformation_scaleR)
    thus "y \<in> cone_of (g ` S)"
      unfolding cone_of_def using t_pos t_le z_in by blast
  qed
  show "cone_of (g ` S) \<subseteq> g ` cone_of S"
  proof
    fix y assume "y \<in> cone_of (g ` S)"
    then obtain t z where y_eq: "y = t *\<^sub>R z" and t_pos: "0 < t" and t_le: "t \<le> 1"
      and z_in: "z \<in> g ` S"
      unfolding cone_of_def by blast
    then obtain x where x_in: "x \<in> S" and z_eq: "z = g x"
      by blast
    have "y = g (t *\<^sub>R x)"
      using assms by (simp add: y_eq z_eq SO3_def rotation_def orthogonal_transformation_scaleR)
    moreover have "t *\<^sub>R x \<in> cone_of S"
      unfolding cone_of_def using t_pos t_le x_in by blast
    ultimately show "y \<in> g ` cone_of S"
      by blast
  qed
qed

lemma cone_of_disjoint:
  assumes S_sub: "S \<subseteq> sphere2"
    and T_sub: "T \<subseteq> sphere2"
    and disj: "S \<inter> T = {}"
  shows "cone_of S \<inter> cone_of T = {}"
proof
  show "cone_of S \<inter> cone_of T \<subseteq> {}"
  proof
    fix y
    assume y: "y \<in> cone_of S \<inter> cone_of T"
    then obtain t x where y_tx: "y = t *\<^sub>R x" and t_pos: "0 < t"
      and xS: "x \<in> S"
      unfolding cone_of_def by blast
    from y obtain s z where y_sz: "y = s *\<^sub>R z" and s_pos: "0 < s"
      and zT: "z \<in> T"
      unfolding cone_of_def by blast
    have x_norm: "norm x = 1"
      using S_sub sphere2_def xS by auto
    have z_norm: "norm z = 1"
      using T_sub sphere2_def zT by auto
    have t_eq: "t = s"
    proof -
      have "t = norm (t *\<^sub>R x)"
        using t_pos x_norm by simp
      also have "\<dots> = norm (s *\<^sub>R z)"
        using y_tx y_sz by simp
      also have "\<dots> = s"
        using s_pos z_norm by simp
      finally show ?thesis .
    qed
    have "x = z"
      using y_tx y_sz t_eq t_pos by (simp add: scaleR_cancel_left)
    hence "x \<in> S \<inter> T"
      using xS zT by simp
    with disj show "y \<in> {}"
      by simp
  qed
  show "{} \<subseteq> cone_of S \<inter> cone_of T"
    by simp
qed

lemma cone_of_pairwise_disjoint:
  assumes disj: "pairwise_disjoint P"
    and sub: "\<forall>i < length P. P ! i \<subseteq> sphere2"
  shows "pairwise_disjoint (map cone_of P)"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length (map cone_of P)" and j: "j < length (map cone_of P)" and ij: "i \<noteq> j"
  have "P ! i \<inter> P ! j = {}"
    using disj i j ij by (simp add: pairwise_disjoint_def)
  moreover have "P ! i \<subseteq> sphere2" "P ! j \<subseteq> sphere2"
    using sub i j by auto
  ultimately show "map cone_of P ! i \<inter> map cone_of P ! j = {}"
    using i j by (simp add: cone_of_disjoint)
qed

lemma SO3_cone_images_pairwise_disjoint:
  assumes len: "length P = length g"
    and g_SO3: "set g \<subseteq> SO3"
    and P_sub: "\<forall>i < length P. P ! i \<subseteq> sphere2"
    and disj: "pairwise_disjoint (map2 (\<lambda>h A. h ` A) g P)"
  shows "pairwise_disjoint (map2 (\<lambda>h A. h ` A) g (map cone_of P))"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length (map2 (\<lambda>h A. h ` A) g (map cone_of P))"
    and j: "j < length (map2 (\<lambda>h A. h ` A) g (map cone_of P))"
    and ij: "i \<noteq> j"
  have iP: "i < length P" and jP: "j < length P"
    using i j len by auto
  have gi: "g ! i \<in> SO3" and gj: "g ! j \<in> SO3"
  proof -
    have "i < length g"
      using iP len by simp
    hence "g ! i \<in> set g"
      by (rule nth_mem)
    thus "g ! i \<in> SO3"
      using g_SO3 by blast
  next
    have "j < length g"
      using jP len by simp
    hence "g ! j \<in> set g"
      by (rule nth_mem)
    thus "g ! j \<in> SO3"
      using g_SO3 by blast
  qed
  have img_disj: "(g ! i ` (P ! i)) \<inter> (g ! j ` (P ! j)) = {}"
    using disj len iP jP ij by (simp add: pairwise_disjoint_def)
  have img_i_sub: "g ! i ` (P ! i) \<subseteq> sphere2"
    using P_sub iP rotation_preserves_sphere2[OF gi] by auto
  have img_j_sub: "g ! j ` (P ! j) \<subseteq> sphere2"
    using P_sub jP rotation_preserves_sphere2[OF gj] by auto
  have cone_disj: "cone_of (g ! i ` (P ! i)) \<inter> cone_of (g ! j ` (P ! j)) = {}"
    by (rule cone_of_disjoint[OF img_i_sub img_j_sub img_disj])
  have "map2 (\<lambda>h A. h ` A) g (map cone_of P) ! i =
      cone_of (g ! i ` (P ! i))"
    using len iP SO3_image_cone_of[OF gi, of "P ! i"] by simp
  moreover have "map2 (\<lambda>h A. h ` A) g (map cone_of P) ! j =
      cone_of (g ! j ` (P ! j))"
    using len jP SO3_image_cone_of[OF gj, of "P ! j"] by simp
  ultimately show "map2 (\<lambda>h A. h ` A) g (map cone_of P) ! i \<inter>
      map2 (\<lambda>h A. h ` A) g (map cone_of P) ! j = {}"
    using cone_disj by simp
qed

lemma zero_in_ball3 [simp]: "(0::real^3) \<in> ball3"
  by (simp add: ball3_def)

lemma indexed_image_union_append_singleton:
  fixes P :: "'a set list" and G :: "('a \<Rightarrow> 'b) list" and S :: "'a set"
    and g :: "'a \<Rightarrow> 'b"
  assumes "length P = length G"
  shows "(\<Union>i<length (P @ [S]). (G @ [g]) ! i ` ((P @ [S]) ! i)) =
    (\<Union>i<length P. G ! i ` (P ! i)) \<union> g ` S"
proof -
  have "(\<Union>i<length (P @ [S]). (G @ [g]) ! i ` ((P @ [S]) ! i)) =
      (\<Union>i<Suc (length P). (G @ [g]) ! i ` ((P @ [S]) ! i))"
    by simp
  also have "\<dots> =
      (\<Union>i<length P. (G @ [g]) ! i ` ((P @ [S]) ! i)) \<union>
      (G @ [g]) ! length P ` ((P @ [S]) ! length P)"
    by (simp add: lessThan_Suc Un_commute)
  also have "\<dots> = (\<Union>i<length P. G ! i ` (P ! i)) \<union> g ` S"
    using assms by (simp add: nth_append)
  finally show ?thesis .
qed

lemma indexed_union_append_singleton:
  fixes P :: "'a set list" and S :: "'a set"
  shows "(\<Union>i<length (P @ [S]). (P @ [S]) ! i) =
    (\<Union>i<length P. P ! i) \<union> S"
proof -
  have "(\<Union>i<length (P @ [S]). (P @ [S]) ! i) =
      (\<Union>i<Suc (length P). (P @ [S]) ! i)"
    by simp
  also have "\<dots> =
      (\<Union>i<length P. (P @ [S]) ! i) \<union> (P @ [S]) ! length P"
    by (simp add: lessThan_Suc Un_commute)
  finally show ?thesis
    by (metis sphere_indexed_union_append_singleton)
qed

text \<open>The punctured ball is paradoxical via radial cones over the sphere pieces.\<close>
theorem ball3_minus_origin_paradoxical:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3 - {0}) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> ball3 - {0}) \<and>
       ball3 - {0} = (\<Union>i<length P. P ! i) \<and>
       ball3 - {0} = (\<Union>i<length Q. Q ! i) \<and>
       ball3 - {0} = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       ball3 - {0} = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  from sphere2_paradoxical obtain P Q :: "(real^3) set list"
    and gP gQ :: "((real^3 \<Rightarrow> real^3)) list"
    where decomp:
      "length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> sphere2) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> sphere2) \<and>
       sphere2 = (\<Union>i<length P. P ! i) \<and>
       sphere2 = (\<Union>i<length Q. Q ! i) \<and>
       sphere2 = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       sphere2 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by (elim exE)
  from decomp have lenP: "length P = length gP"
    by (elim conjE)
  from decomp have lenQ: "length Q = length gQ"
    by (elim conjE)
  from decomp have gP_SO3: "set gP \<subseteq> SO3"
    by (elim conjE)
  from decomp have gQ_SO3: "set gQ \<subseteq> SO3"
    by (elim conjE)
  from decomp have P_sub_sphere: "\<forall>i < length P. P ! i \<subseteq> sphere2"
    by (elim conjE)
  from decomp have Q_sub_sphere: "\<forall>i < length Q. Q ! i \<subseteq> sphere2"
    by (elim conjE)
  from decomp have P_src_sphere: "sphere2 = (\<Union>i<length P. P ! i)"
    by (elim conjE)
  from decomp have Q_src_sphere: "sphere2 = (\<Union>i<length Q. Q ! i)"
    by (elim conjE)
  from decomp have P_cov_sphere: "sphere2 = (\<Union>i<length P. (gP ! i) ` (P ! i))"
    by (elim conjE)
  from decomp have Q_cov_sphere: "sphere2 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by (elim conjE)

  define P' where "P' = map cone_of P"
  define Q' where "Q' = map cone_of Q"
  have lenP': "length P' = length gP"
    by (simp add: P'_def lenP)
  have lenQ': "length Q' = length gQ"
    by (simp add: Q'_def lenQ)
  have P'_sub: "\<forall>i < length P'. P' ! i \<subseteq> ball3 - {0}"
    using P_sub_sphere by (simp add: P'_def cone_of_in_ball3_minus_origin)
  have Q'_sub: "\<forall>i < length Q'. Q' ! i \<subseteq> ball3 - {0}"
    using Q_sub_sphere by (simp add: Q'_def cone_of_in_ball3_minus_origin)
  have P'_src: "ball3 - {0} = (\<Union>i<length P'. P' ! i)"
  proof -
    have "(\<Union>i<length P'. P' ! i) = (\<Union>i<length P. cone_of (P ! i))"
      by (simp add: P'_def)
    also have "\<dots> = cone_of (\<Union>i<length P. P ! i)"
      by (simp add: cone_of_UN)
    also have "\<dots> = cone_of sphere2"
      using P_src_sphere by simp
    also have "\<dots> = ball3 - {0}"
      using ball3_minus_origin_eq_cone_sphere2 by simp
    finally show ?thesis by simp
  qed
  have Q'_src: "ball3 - {0} = (\<Union>i<length Q'. Q' ! i)"
  proof -
    have "(\<Union>i<length Q'. Q' ! i) = (\<Union>i<length Q. cone_of (Q ! i))"
      by (simp add: Q'_def)
    also have "\<dots> = cone_of (\<Union>i<length Q. Q ! i)"
      by (simp add: cone_of_UN)
    also have "\<dots> = cone_of sphere2"
      using Q_src_sphere by simp
    also have "\<dots> = ball3 - {0}"
      using ball3_minus_origin_eq_cone_sphere2 by simp
    finally show ?thesis by simp
  qed
  have P'_cov: "ball3 - {0} = (\<Union>i<length P'. (gP ! i) ` (P' ! i))"
  proof -
    have "(\<Union>i<length P'. (gP ! i) ` (P' ! i)) =
        (\<Union>i<length P. cone_of ((gP ! i) ` (P ! i)))"
    proof -
      have "\<And>i. i < length P \<Longrightarrow> (gP ! i) ` cone_of (P ! i) =
          cone_of ((gP ! i) ` (P ! i))"
        by (metis SO3_image_cone_of gP_SO3 lenP nth_mem subset_eq)
      thus ?thesis
        by (simp add: P'_def)
    qed
    also have "\<dots> = cone_of (\<Union>i<length P. (gP ! i) ` (P ! i))"
      by (simp add: cone_of_UN)
    also have "\<dots> = cone_of sphere2"
      using P_cov_sphere by simp
    also have "\<dots> = ball3 - {0}"
      using ball3_minus_origin_eq_cone_sphere2 by simp
    finally show ?thesis by simp
  qed
  have Q'_cov: "ball3 - {0} = (\<Union>i<length Q'. (gQ ! i) ` (Q' ! i))"
  proof -
    have "(\<Union>i<length Q'. (gQ ! i) ` (Q' ! i)) =
        (\<Union>i<length Q. cone_of ((gQ ! i) ` (Q ! i)))"
    proof -
      have "\<And>i. i < length Q \<Longrightarrow> (gQ ! i) ` cone_of (Q ! i) =
          cone_of ((gQ ! i) ` (Q ! i))"
      proof -
        fix i assume i_lt: "i < length Q"
        have "gQ ! i \<in> set gQ"
          using i_lt lenQ by (simp add: nth_mem)
        hence "gQ ! i \<in> SO3"
          using gQ_SO3 by blast
        thus "(gQ ! i) ` cone_of (Q ! i) = cone_of ((gQ ! i) ` (Q ! i))"
          by (rule SO3_image_cone_of)
      qed
      thus ?thesis
        by (simp add: Q'_def)
    qed
    also have "\<dots> = cone_of (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
      by (simp add: cone_of_UN)
    also have "\<dots> = cone_of sphere2"
      using Q_cov_sphere by simp
    also have "\<dots> = ball3 - {0}"
      using ball3_minus_origin_eq_cone_sphere2 by simp
    finally show ?thesis by simp
  qed
  show ?thesis
    apply (rule exI[of _ P'])
    apply (rule exI[of _ Q'])
    apply (rule exI[of _ gP])
    apply (rule exI[of _ gQ])
    using lenP' lenQ' gP_SO3 gQ_SO3 P'_sub Q'_sub P'_src Q'_src P'_cov Q'_cov
    by simp
qed

theorem ball3_minus_origin_paradoxical_strong:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       pairwise_disjoint (P @ Q) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q) \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3 - {0}) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> ball3 - {0}) \<and>
       ball3 - {0} = (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i) \<and>
       ball3 - {0} = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       ball3 - {0} = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  from sphere2_paradoxical_strong obtain P Q :: "(real^3) set list"
    and gP gQ :: "((real^3 \<Rightarrow> real^3)) list"
    where lenP: "length P = length gP"
      and lenQ: "length Q = length gQ"
      and gP_SO3: "set gP \<subseteq> SO3"
      and gQ_SO3: "set gQ \<subseteq> SO3"
      and source_disj: "pairwise_disjoint (P @ Q)"
      and imageP_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P)"
      and imageQ_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q)"
      and P_sub_sphere: "\<forall>i < length P. P ! i \<subseteq> sphere2"
      and Q_sub_sphere: "\<forall>i < length Q. Q ! i \<subseteq> sphere2"
      and source_cover: "sphere2 = (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)"
      and P_cov_sphere: "sphere2 = (\<Union>i<length P. (gP ! i) ` (P ! i))"
      and Q_cov_sphere: "sphere2 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by auto

  define P' where "P' = map cone_of P"
  define Q' where "Q' = map cone_of Q"
  have lenP': "length P' = length gP"
    by (simp add: P'_def lenP)
  have lenQ': "length Q' = length gQ"
    by (simp add: Q'_def lenQ)
  have P'_sub: "\<forall>i < length P'. P' ! i \<subseteq> ball3 - {0}"
    using P_sub_sphere by (simp add: P'_def cone_of_in_ball3_minus_origin)
  have Q'_sub: "\<forall>i < length Q'. Q' ! i \<subseteq> ball3 - {0}"
    using Q_sub_sphere by (simp add: Q'_def cone_of_in_ball3_minus_origin)
  have all_sub: "\<forall>i < length (P @ Q). (P @ Q) ! i \<subseteq> sphere2"
    using P_sub_sphere Q_sub_sphere by (auto simp: nth_append)
  have source_disj': "pairwise_disjoint (P' @ Q')"
    unfolding P'_def Q'_def
    using cone_of_pairwise_disjoint[OF source_disj all_sub] by simp
  have imageP_disj': "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P')"
    unfolding P'_def
    by (rule SO3_cone_images_pairwise_disjoint[OF lenP gP_SO3 P_sub_sphere imageP_disj])
  have imageQ_disj': "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q')"
    unfolding Q'_def
    by (rule SO3_cone_images_pairwise_disjoint[OF lenQ gQ_SO3 Q_sub_sphere imageQ_disj])

  have P'_src: "(\<Union>i<length P'. P' ! i) = cone_of (\<Union>i<length P. P ! i)"
  proof -
    have "(\<Union>i<length P'. P' ! i) = (\<Union>i<length P. cone_of (P ! i))"
      by (simp add: P'_def)
    also have "\<dots> = cone_of (\<Union>i<length P. P ! i)"
      by (simp add: cone_of_UN)
    finally show ?thesis .
  qed
  have Q'_src: "(\<Union>i<length Q'. Q' ! i) = cone_of (\<Union>i<length Q. Q ! i)"
    using Q'_def cone_of_UN by fastforce
  have source_cover': "ball3 - {0} = (\<Union>i<length P'. P' ! i) \<union> (\<Union>i<length Q'. Q' ! i)"
  proof -
    have "(\<Union>i<length P'. P' ! i) \<union> (\<Union>i<length Q'. Q' ! i) =
        cone_of ((\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i))"
      using P'_src Q'_src by (auto simp: cone_of_def)
    also have "\<dots> = cone_of sphere2"
      using source_cover by simp
    also have "\<dots> = ball3 - {0}"
      using ball3_minus_origin_eq_cone_sphere2 by simp
    finally show ?thesis by simp
  qed

  have P'_cov: "ball3 - {0} = (\<Union>i<length P'. (gP ! i) ` (P' ! i))"
  proof -
    have "(\<Union>i<length P'. (gP ! i) ` (P' ! i)) =
        (\<Union>i<length P. cone_of ((gP ! i) ` (P ! i)))"
    proof -
      have "\<And>i. i < length P \<Longrightarrow> (gP ! i) ` cone_of (P ! i) =
          cone_of ((gP ! i) ` (P ! i))"
      proof -
        fix i assume i_lt: "i < length P"
        have "gP ! i \<in> SO3"
          using gP_SO3 i_lt lenP by auto
        thus "(gP ! i) ` cone_of (P ! i) = cone_of ((gP ! i) ` (P ! i))"
          by (rule SO3_image_cone_of)
      qed
      thus ?thesis
        by (simp add: P'_def)
    qed
    also have "\<dots> = cone_of (\<Union>i<length P. (gP ! i) ` (P ! i))"
      by (simp add: cone_of_UN)
    also have "\<dots> = cone_of sphere2"
      using P_cov_sphere by simp
    also have "\<dots> = ball3 - {0}"
      using ball3_minus_origin_eq_cone_sphere2 by simp
    finally show ?thesis by simp
  qed
  have Q'_cov: "ball3 - {0} = (\<Union>i<length Q'. (gQ ! i) ` (Q' ! i))"
  proof -
    have "(\<Union>i<length Q'. (gQ ! i) ` (Q' ! i)) =
        (\<Union>i<length Q. cone_of ((gQ ! i) ` (Q ! i)))"
    proof -
      have "\<And>i. i < length Q \<Longrightarrow> (gQ ! i) ` cone_of (Q ! i) =
          cone_of ((gQ ! i) ` (Q ! i))"
      proof -
        fix i assume i_lt: "i < length Q"
        have "gQ ! i \<in> SO3"
          using gQ_SO3 i_lt lenQ by auto
        thus "(gQ ! i) ` cone_of (Q ! i) = cone_of ((gQ ! i) ` (Q ! i))"
          by (rule SO3_image_cone_of)
      qed
      thus ?thesis
        by (simp add: Q'_def)
    qed
    also have "\<dots> = cone_of (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
      by (simp add: cone_of_UN)
    also have "\<dots> = cone_of sphere2"
      using Q_cov_sphere by simp
    also have "\<dots> = ball3 - {0}"
      using ball3_minus_origin_eq_cone_sphere2 by simp
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (intro exI conjI)
    show "length P' = length gP"
      by (rule lenP')
    show "length Q' = length gQ"
      by (rule lenQ')
    show "set gP \<subseteq> SO3"
      by (rule gP_SO3)
    show "set gQ \<subseteq> SO3"
      by (rule gQ_SO3)
    show "pairwise_disjoint (P' @ Q')"
      by (rule source_disj')
    show "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P')"
      by (rule imageP_disj')
    show "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q')"
      by (rule imageQ_disj')
    show "\<forall>i<length P'. P' ! i \<subseteq> ball3 - {0}"
      by (rule P'_sub)
    show "\<forall>i<length Q'. Q' ! i \<subseteq> ball3 - {0}"
      by (rule Q'_sub)
    show "ball3 - {0} = (\<Union>i<length P'. P' ! i) \<union> (\<Union>i<length Q'. Q' ! i)"
      by (rule source_cover')
    show "ball3 - {0} = (\<Union>i<length P'. (gP ! i) ` (P' ! i))"
      by (rule P'_cov)
    show "ball3 - {0} = (\<Union>i<length Q'. (gQ ! i) ` (Q' ! i))"
      by (rule Q'_cov)
  qed
qed

text \<open>
  Adjoining the origin gives a useful SO(3)-only finite-cover decomposition
  of the full ball.  The partition-level absorption is completed in the final
  theory, where off-centre isometries are available.
\<close>
theorem ball3_paradoxical:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> ball3) \<and>
       ball3 = (\<Union>i<length P. P ! i) \<and>
       ball3 = (\<Union>i<length Q. Q ! i) \<and>
       ball3 = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       ball3 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  from ball3_minus_origin_paradoxical obtain P Q :: "(real^3) set list"
    and gP gQ :: "((real^3 \<Rightarrow> real^3)) list"
    where decomp:
      "length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3 - {0}) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> ball3 - {0}) \<and>
       ball3 - {0} = (\<Union>i<length P. P ! i) \<and>
       ball3 - {0} = (\<Union>i<length Q. Q ! i) \<and>
       ball3 - {0} = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       ball3 - {0} = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by (elim exE)
  from decomp have lenP: "length P = length gP"
    by (elim conjE)
  from decomp have lenQ: "length Q = length gQ"
    by (elim conjE)
  from decomp have gP_SO3: "set gP \<subseteq> SO3"
    by (elim conjE)
  from decomp have gQ_SO3: "set gQ \<subseteq> SO3"
    by (elim conjE)
  from decomp have P_sub: "\<forall>i < length P. P ! i \<subseteq> ball3 - {0}"
    by (elim conjE)
  from decomp have Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> ball3 - {0}"
    by (elim conjE)
  from decomp have P_src: "ball3 - {0} = (\<Union>i<length P. P ! i)"
    by (elim conjE)
  from decomp have Q_src: "ball3 - {0} = (\<Union>i<length Q. Q ! i)"
    by (elim conjE)
  from decomp have P_cov: "ball3 - {0} = (\<Union>i<length P. (gP ! i) ` (P ! i))"
    by (elim conjE)
  from decomp have Q_cov: "ball3 - {0} = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by (elim conjE)
  define P' where "P' = P @ [{0::real^3}]"
  define Q' where "Q' = Q @ [{0::real^3}]"
  define gP' where "gP' = gP @ [id]"
  define gQ' where "gQ' = gQ @ [id]"
  have lenP': "length P' = length gP'"
    by (simp add: P'_def gP'_def lenP)
  have lenQ': "length Q' = length gQ'"
    by (simp add: Q'_def gQ'_def lenQ)
  have P'_sub: "\<forall>i < length P'. P' ! i \<subseteq> ball3"
    using P_sub by (auto simp add: P'_def nth_append)
  have Q'_sub: "\<forall>i < length Q'. Q' ! i \<subseteq> ball3"
    using Q_sub by (auto simp add: Q'_def nth_append)
  have gP'_SO3: "set gP' \<subseteq> SO3"
    using gP_SO3 by (simp add: gP'_def id_in_SO3)
  have gQ'_SO3: "set gQ' \<subseteq> SO3"
    using gQ_SO3 by (simp add: gQ'_def id_in_SO3)
  have P'_src: "ball3 = (\<Union>i<length P'. P' ! i)"
  proof -
    have append_union:
      "(\<Union>i<length (P @ [{0::real^3}]). (P @ [{0}]) ! i) =
        (\<Union>i<length P. P ! i) \<union> {0}"
      using indexed_union_append_singleton[where P = P and S = "{0::real^3}"] .
    have "(\<Union>i<length P'. P' ! i) = (ball3 - {0}) \<union> {0}"
      unfolding P'_def
      using append_union P_src by simp
    also have "\<dots> = ball3"
      by auto
    finally show ?thesis by simp
  qed
  have Q'_src: "ball3 = (\<Union>i<length Q'. Q' ! i)"
  proof -
    have append_union:
      "(\<Union>i<length (Q @ [{0::real^3}]). (Q @ [{0}]) ! i) =
        (\<Union>i<length Q. Q ! i) \<union> {0}"
      using indexed_union_append_singleton[where P = Q and S = "{0::real^3}"] .
    have "(\<Union>i<length Q'. Q' ! i) = (ball3 - {0}) \<union> {0}"
      unfolding Q'_def
      using append_union Q_src by simp
    also have "\<dots> = ball3"
      by auto
    finally show ?thesis by simp
  qed
  have P'_cov: "ball3 = (\<Union>i<length P'. (gP' ! i) ` (P' ! i))"
  proof -
    have append_union:
      "(\<Union>i<length (P @ [{0::real^3}]). (gP @ [id]) ! i ` ((P @ [{0}]) ! i)) =
        (\<Union>i<length P. gP ! i ` (P ! i)) \<union> {0}"
      using indexed_image_union_append_singleton[
        where P = P and G = gP and S = "{0::real^3}" and g = id, OF lenP]
      by simp
    have union_eq: "(\<Union>i<length P'. (gP' ! i) ` (P' ! i)) = ball3"
    proof -
      have "(\<Union>i<length P'. (gP' ! i) ` (P' ! i)) =
          (\<Union>i<length P. gP ! i ` (P ! i)) \<union> {0}"
        unfolding P'_def gP'_def
        using append_union .
      also have "\<dots> = (ball3 - {0}) \<union> {0}"
        using P_cov by simp
      also have "\<dots> = ball3"
        by auto
      finally show ?thesis .
    qed
    thus ?thesis by simp
  qed
  have Q'_cov: "ball3 = (\<Union>i<length Q'. (gQ' ! i) ` (Q' ! i))"
  proof -
    have append_union:
      "(\<Union>i<length (Q @ [{0::real^3}]). (gQ @ [id]) ! i ` ((Q @ [{0}]) ! i)) =
        (\<Union>i<length Q. gQ ! i ` (Q ! i)) \<union> {0}"
      using indexed_image_union_append_singleton[
        where P = Q and G = gQ and S = "{0::real^3}" and g = id, OF lenQ]
      by simp
    have union_eq: "(\<Union>i<length Q'. (gQ' ! i) ` (Q' ! i)) = ball3"
    proof -
      have "(\<Union>i<length Q'. (gQ' ! i) ` (Q' ! i)) =
          (\<Union>i<length Q. gQ ! i ` (Q ! i)) \<union> {0}"
        unfolding Q'_def gQ'_def
        using append_union .
      also have "\<dots> = (ball3 - {0}) \<union> {0}"
        using Q_cov by simp
      also have "\<dots> = ball3"
        by auto
      finally show ?thesis .
    qed
    thus ?thesis by simp
  qed
  show ?thesis
    apply (rule exI[of _ P'])
    apply (rule exI[of _ Q'])
    apply (rule exI[of _ gP'])
    apply (rule exI[of _ gQ'])
    using lenP' lenQ' gP'_SO3 gQ'_SO3 P'_sub Q'_sub P'_src Q'_src P'_cov Q'_cov
    by simp
qed

end
