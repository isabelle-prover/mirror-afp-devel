theory Explicit_Fundamental_Group_Scaffold
  imports Explicit_Path_Homotopy_Scaffold Fundamental_Group_Scaffold
begin

section \<open>Explicit-topology fundamental-group quotients\<close>

text \<open>
  Building on the explicit-topology path layer, this theory forms loop classes,
  quotient carriers, and induced maps for arbitrary topological spaces. It is
  the main bridge from point-set topology to the carrier-group algebra used in
  the Seifert--van Kampen interface.
\<close>

definition loopin_class ::
  "'a topology \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) set"
where
  "loopin_class X x p = {q. q \<in> loopin_space X x \<and> homotopic_pathsin X q p}"

definition fundamental_groupin_space ::
  "'a topology \<Rightarrow> 'a \<Rightarrow> ((real \<Rightarrow> 'a) set) set"
where
  "fundamental_groupin_space X x = loopin_class X x ` loopin_space X x"

definition some_loopin ::
  "'a topology \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a)"
where
  "some_loopin X x Q = (SOME p. p \<in> loopin_space X x \<and> Q = loopin_class X x p)"

definition fundamental_groupin_one ::
  "'a topology \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set"
where
  "fundamental_groupin_one X x = loopin_class X x (\<lambda>_. x)"

definition fundamental_groupin_mult ::
  "'a topology \<Rightarrow> 'a \<Rightarrow>
    (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set"
where
  "fundamental_groupin_mult X x A B =
     loopin_class X x (joinpathin (some_loopin X x A) (some_loopin X x B))"

definition fundamental_groupin_inv ::
  "'a topology \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set"
where
  "fundamental_groupin_inv X x A = loopin_class X x (reversepathin (some_loopin X x A))"

definition loopin_image ::
  "('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'b)"
where
  "loopin_image h p = h \<circ> p"

definition fundamental_groupin_map ::
  "'a topology \<Rightarrow> 'a \<Rightarrow> 'b topology \<Rightarrow> 'b \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'b) set"
where
  "fundamental_groupin_map X x Y y h A =
     loopin_class Y y (loopin_image h (some_loopin X x A))"

lemma loopin_class_in_space:
  assumes "p \<in> loopin_space X x"
  shows "loopin_class X x p \<in> fundamental_groupin_space X x"
  using assms unfolding fundamental_groupin_space_def by blast

lemma fundamental_groupin_spaceE:
  assumes "Q \<in> fundamental_groupin_space X x"
  obtains p where "p \<in> loopin_space X x" "Q = loopin_class X x p"
  using assms unfolding fundamental_groupin_space_def by blast

lemma some_loopin_spec:
  assumes "Q \<in> fundamental_groupin_space X x"
  shows "some_loopin X x Q \<in> loopin_space X x"
    and "Q = loopin_class X x (some_loopin X x Q)"
proof -
  from assms obtain p where p: "p \<in> loopin_space X x" "Q = loopin_class X x p"
    by (rule fundamental_groupin_spaceE)
  have ex: "\<exists>p. p \<in> loopin_space X x \<and> Q = loopin_class X x p"
    using p by blast
  have "some_loopin X x Q \<in> loopin_space X x \<and> Q = loopin_class X x (some_loopin X x Q)"
    unfolding some_loopin_def by (rule someI_ex[OF ex])
  then show "some_loopin X x Q \<in> loopin_space X x"
    and "Q = loopin_class X x (some_loopin X x Q)"
    by auto
qed

lemma loopin_class_eqI:
  assumes p: "p \<in> loopin_space X x"
    and q: "q \<in> loopin_space X x"
    and pq: "homotopic_pathsin X p q"
  shows "loopin_class X x p = loopin_class X x q"
proof (auto simp: loopin_class_def)
  fix r
  assume "homotopic_pathsin X r p"
  then show "homotopic_pathsin X r q"
    using pq by (rule homotopic_pathsin_trans)
next
  fix r
  assume "homotopic_pathsin X r q"
  moreover have "homotopic_pathsin X q p"
    using pq by (rule homotopic_pathsin_sym)
  ultimately show "homotopic_pathsin X r p"
    by (rule homotopic_pathsin_trans)
qed

lemma loopin_class_eq_iff:
  assumes p: "p \<in> loopin_space X x"
    and q: "q \<in> loopin_space X x"
  shows "loopin_class X x p = loopin_class X x q \<longleftrightarrow> homotopic_pathsin X p q"
proof
  assume h: "loopin_class X x p = loopin_class X x q"
  have "p \<in> loopin_class X x p"
    using p by (auto simp: loopin_class_def elim: loopin_spaceE)
  then have "p \<in> loopin_class X x q"
    using h by simp
  then show "homotopic_pathsin X p q"
    unfolding loopin_class_def using p by auto
next
  assume pq: "homotopic_pathsin X p q"
  show "loopin_class X x p = loopin_class X x q"
    by (rule loopin_class_eqI[OF p q pq])
qed

lemma fundamental_groupin_one_in_space:
  assumes "x \<in> topspace X"
  shows "fundamental_groupin_one X x \<in> fundamental_groupin_space X x"
  unfolding fundamental_groupin_one_def
  by (rule loopin_class_in_space, rule constant_loopin_in_space, fact assms)

lemma fundamental_groupin_mult_eqI:
  assumes A_in: "A \<in> fundamental_groupin_space X x"
    and B_in: "B \<in> fundamental_groupin_space X x"
    and p: "p \<in> loopin_space X x"
    and q: "q \<in> loopin_space X x"
    and A: "A = loopin_class X x p"
    and B: "B = loopin_class X x q"
  shows "fundamental_groupin_mult X x A B = loopin_class X x (joinpathin p q)"
proof -
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have repB: "some_loopin X x B \<in> loopin_space X x" "B = loopin_class X x (some_loopin X x B)"
    using some_loopin_spec[OF B_in] by auto
  have homoA': "homotopic_pathsin X p (some_loopin X x A)"
    using repA p A by (simp add: loopin_class_eq_iff)
  have homoA: "homotopic_pathsin X (some_loopin X x A) p"
    using homoA' by (rule homotopic_pathsin_sym)
  have homoB': "homotopic_pathsin X q (some_loopin X x B)"
    using repB q B by (simp add: loopin_class_eq_iff)
  have homoB: "homotopic_pathsin X (some_loopin X x B) q"
    using homoB' by (rule homotopic_pathsin_sym)
  have join_hom:
    "homotopic_pathsin X
      (joinpathin (some_loopin X x A) (some_loopin X x B))
      (joinpathin p q)"
  proof -
    have repA_end: "some_loopin X x A 1 = x"
      using repA(1) by (auto elim: loopin_spaceE)
    have repB_start: "some_loopin X x B 0 = x"
      using repB(1) by (auto elim: loopin_spaceE)
    show ?thesis
      by (rule homotopic_pathsin_joinpathin[OF homoA homoB]) (simp add: repA_end repB_start)
  qed
  have "loopin_class X x (joinpathin (some_loopin X x A) (some_loopin X x B)) =
      loopin_class X x (joinpathin p q)"
    by (rule loopin_class_eqI[OF loopin_space_joinpathin[OF repA(1) repB(1)]
        loopin_space_joinpathin[OF p q] join_hom])
  then show ?thesis
    unfolding fundamental_groupin_mult_def .
qed

lemma fundamental_groupin_mult_in_space:
  assumes "A \<in> fundamental_groupin_space X x"
    and "B \<in> fundamental_groupin_space X x"
  shows "fundamental_groupin_mult X x A B \<in> fundamental_groupin_space X x"
proof -
  have repA: "some_loopin X x A \<in> loopin_space X x"
    using some_loopin_spec[OF assms(1)] by auto
  have repB: "some_loopin X x B \<in> loopin_space X x"
    using some_loopin_spec[OF assms(2)] by auto
  show ?thesis
    unfolding fundamental_groupin_mult_def
    using loopin_space_joinpathin[OF repA repB] by (rule loopin_class_in_space)
qed

lemma fundamental_groupin_inv_eqI:
  assumes A_in: "A \<in> fundamental_groupin_space X x"
    and p: "p \<in> loopin_space X x"
    and A: "A = loopin_class X x p"
  shows "fundamental_groupin_inv X x A = loopin_class X x (reversepathin p)"
proof -
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have homoA': "homotopic_pathsin X p (some_loopin X x A)"
    using repA p A by (simp add: loopin_class_eq_iff)
  have homoA: "homotopic_pathsin X (some_loopin X x A) p"
    using homoA' by (rule homotopic_pathsin_sym)
  have rev_hom:
    "homotopic_pathsin X (reversepathin (some_loopin X x A)) (reversepathin p)"
    using homoA by (rule homotopic_pathsin_reversepathin_D)
  have "loopin_class X x (reversepathin (some_loopin X x A)) = loopin_class X x (reversepathin p)"
    by (rule loopin_class_eqI[OF loopin_space_reversepathin[OF repA(1)]
        loopin_space_reversepathin[OF p] rev_hom])
  then show ?thesis
    unfolding fundamental_groupin_inv_def .
qed

lemma fundamental_groupin_inv_in_space:
  assumes "A \<in> fundamental_groupin_space X x"
  shows "fundamental_groupin_inv X x A \<in> fundamental_groupin_space X x"
proof -  
  have repA: "some_loopin X x A \<in> loopin_space X x"
    using some_loopin_spec[OF assms] by auto
  show ?thesis
    unfolding fundamental_groupin_inv_def
    using loopin_space_reversepathin[OF repA] by (rule loopin_class_in_space)
qed

lemma loopin_image_in_space:
  assumes p: "p \<in> loopin_space X x"
    and h: "continuous_map X Y f"
    and fx: "f x = y"
  shows "loopin_image f p \<in> loopin_space Y y"
proof -
  from p obtain p_in where p_in: "pathin X p" "p 0 = x" "p 1 = x"
    by (rule loopin_spaceE)
  have "pathin Y (loopin_image f p)"
    using p_in(1) h unfolding loopin_image_def by (rule pathin_compose)
  moreover have "loopin_image f p 0 = y" "loopin_image f p 1 = y"
    using p_in fx unfolding loopin_image_def by simp_all
  ultimately show ?thesis
    unfolding loopin_space_def by blast
qed

lemma fundamental_groupin_map_rep:
  assumes A: "A \<in> fundamental_groupin_space X x"
    and p: "p \<in> loopin_space X x"
    and rep: "A = loopin_class X x p"
    and h: "continuous_map X Y f"
    and fx: "f x = y"
  shows "fundamental_groupin_map X x Y y f A = loopin_class Y y (loopin_image f p)"
proof -
  have sp: "some_loopin X x A \<in> loopin_space X x"
    using A by (rule some_loopin_spec)
  have A': "A = loopin_class X x (some_loopin X x A)"
    using A by (rule some_loopin_spec)
  have class_eq: "loopin_class X x (some_loopin X x A) = loopin_class X x p"
    using A' rep by simp
  have hom: "homotopic_pathsin X (some_loopin X x A) p"
    using sp p class_eq by (simp add: loopin_class_eq_iff)
  have img_some: "loopin_image f (some_loopin X x A) \<in> loopin_space Y y"
    by (rule loopin_image_in_space[OF sp h fx])
  have img_p: "loopin_image f p \<in> loopin_space Y y"
    by (rule loopin_image_in_space[OF p h fx])
  have img_hom: "homotopic_pathsin Y (loopin_image f (some_loopin X x A)) (loopin_image f p)"
    using hom h unfolding loopin_image_def by (rule homotopic_pathsin_continuous_image)
  have "loopin_class Y y (loopin_image f (some_loopin X x A)) = loopin_class Y y (loopin_image f p)"
    by (rule loopin_class_eqI[OF img_some img_p img_hom])
  then show ?thesis
    unfolding fundamental_groupin_map_def by simp
qed

lemma fundamental_groupin_map_in_space:
  assumes A: "A \<in> fundamental_groupin_space X x"
    and h: "continuous_map X Y f"
    and fx: "f x = y"
  shows "fundamental_groupin_map X x Y y f A \<in> fundamental_groupin_space Y y"
proof -
  have sp: "some_loopin X x A \<in> loopin_space X x"
    using A by (rule some_loopin_spec)
  have img: "loopin_image f (some_loopin X x A) \<in> loopin_space Y y"
    by (rule loopin_image_in_space[OF sp h fx])
  show ?thesis
    unfolding fundamental_groupin_map_def by (rule loopin_class_in_space[OF img])
qed

lemma loopin_image_joinpathin [simp]:
  "loopin_image h (joinpathin p q) = joinpathin (loopin_image h p) (loopin_image h q)"
  unfolding loopin_image_def joinpathin_def by (rule ext) simp

lemma loopin_image_reversepathin [simp]:
  "loopin_image h (reversepathin p) = reversepathin (loopin_image h p)"
  unfolding loopin_image_def reversepathin_def by (rule ext) simp

lemma fundamental_groupin_map_mult:
  assumes A_in: "A \<in> fundamental_groupin_space X x"
    and B_in: "B \<in> fundamental_groupin_space X x"
    and h: "continuous_map X Y f"
    and fx: "f x = y"
  shows "fundamental_groupin_map X x Y y f (fundamental_groupin_mult X x A B) =
      fundamental_groupin_mult Y y
        (fundamental_groupin_map X x Y y f A)
        (fundamental_groupin_map X x Y y f B)"
proof -
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have repB: "some_loopin X x B \<in> loopin_space X x" "B = loopin_class X x (some_loopin X x B)"
    using some_loopin_spec[OF B_in] by auto
  have AB_in: "fundamental_groupin_mult X x A B \<in> fundamental_groupin_space X x"
    by (rule fundamental_groupin_mult_in_space[OF A_in B_in])
  have AB_eq:
    "fundamental_groupin_mult X x A B =
      loopin_class X x (joinpathin (some_loopin X x A) (some_loopin X x B))"
    by (rule fundamental_groupin_mult_eqI[OF A_in B_in repA(1) repB(1) repA(2) repB(2)])
  have map_A_in:
    "fundamental_groupin_map X x Y y f A \<in> fundamental_groupin_space Y y"
    by (rule fundamental_groupin_map_in_space[OF A_in h fx])
  have map_B_in:
    "fundamental_groupin_map X x Y y f B \<in> fundamental_groupin_space Y y"
    by (rule fundamental_groupin_map_in_space[OF B_in h fx])
  have map_A_eq:
    "fundamental_groupin_map X x Y y f A =
      loopin_class Y y (loopin_image f (some_loopin X x A))"
    by (rule fundamental_groupin_map_rep[OF A_in repA(1) repA(2) h fx])
  have map_B_eq:
    "fundamental_groupin_map X x Y y f B =
      loopin_class Y y (loopin_image f (some_loopin X x B))"
    by (rule fundamental_groupin_map_rep[OF B_in repB(1) repB(2) h fx])
  have left_eq:
    "fundamental_groupin_map X x Y y f (fundamental_groupin_mult X x A B) =
      loopin_class Y y (loopin_image f (joinpathin (some_loopin X x A) (some_loopin X x B)))"
    by (rule fundamental_groupin_map_rep[OF AB_in loopin_space_joinpathin[OF repA(1) repB(1)] AB_eq h fx])
  have map_loop_A: "loopin_image f (some_loopin X x A) \<in> loopin_space Y y"
    by (rule loopin_image_in_space[OF repA(1) h fx])
  have map_loop_B: "loopin_image f (some_loopin X x B) \<in> loopin_space Y y"
    by (rule loopin_image_in_space[OF repB(1) h fx])
  have right_eq:
    "fundamental_groupin_mult Y y
        (fundamental_groupin_map X x Y y f A)
        (fundamental_groupin_map X x Y y f B) =
      loopin_class Y y
        (joinpathin (loopin_image f (some_loopin X x A))
          (loopin_image f (some_loopin X x B)))"
    by (rule fundamental_groupin_mult_eqI[OF map_A_in map_B_in map_loop_A map_loop_B map_A_eq map_B_eq])
  then show ?thesis
    using left_eq by simp
qed

lemma fundamental_groupin_mult_one_left:
  assumes x_in: "x \<in> topspace X"
    and A_in: "A \<in> fundamental_groupin_space X x"
  shows "fundamental_groupin_mult X x (fundamental_groupin_one X x) A = A"
proof -
  have const: "(\<lambda>_. x) \<in> loopin_space X x"
    by (rule constant_loopin_in_space[OF x_in])
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have loopA: "pathin X (some_loopin X x A)" "some_loopin X x A 0 = x" "some_loopin X x A 1 = x"
    using repA(1) by (auto elim: loopin_spaceE)
  have mult_eq:
    "fundamental_groupin_mult X x (fundamental_groupin_one X x) A =
      loopin_class X x (joinpathin (\<lambda>_. x) (some_loopin X x A))"
  proof (rule fundamental_groupin_mult_eqI)
    show "fundamental_groupin_one X x \<in> fundamental_groupin_space X x"
      by (rule fundamental_groupin_one_in_space[OF x_in])
    show "A \<in> fundamental_groupin_space X x"
      by (rule A_in)
    show "(\<lambda>_. x) \<in> loopin_space X x"
      by (rule const)
    show "some_loopin X x A \<in> loopin_space X x"
      by (rule repA(1))
    show "fundamental_groupin_one X x = loopin_class X x (\<lambda>_. x)"
      by (simp add: fundamental_groupin_one_def)
    show "A = loopin_class X x (some_loopin X x A)"
      by (rule repA(2))
  qed
  have join_loop: "joinpathin (\<lambda>_. x) (some_loopin X x A) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF const repA(1)])
  have hom: "homotopic_pathsin X (joinpathin (\<lambda>_. x) (some_loopin X x A)) (some_loopin X x A)"
    using homotopic_pathsin_lid_const[OF loopA(1)] loopA(2) by simp
  have class_eq:
    "loopin_class X x (joinpathin (\<lambda>_. x) (some_loopin X x A)) = loopin_class X x (some_loopin X x A)"
    by (rule loopin_class_eqI[OF join_loop repA(1) hom])
  show ?thesis
    using mult_eq class_eq repA(2) by simp
qed

lemma fundamental_groupin_mult_one_right:
  assumes x_in: "x \<in> topspace X"
    and A_in: "A \<in> fundamental_groupin_space X x"
  shows "fundamental_groupin_mult X x A (fundamental_groupin_one X x) = A"
proof -
  have const: "(\<lambda>_. x) \<in> loopin_space X x"
    by (rule constant_loopin_in_space[OF x_in])
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have loopA: "pathin X (some_loopin X x A)" "some_loopin X x A 0 = x" "some_loopin X x A 1 = x"
    using repA(1) by (auto elim: loopin_spaceE)
  have mult_eq:
    "fundamental_groupin_mult X x A (fundamental_groupin_one X x) =
      loopin_class X x (joinpathin (some_loopin X x A) (\<lambda>_. x))"
  proof (rule fundamental_groupin_mult_eqI)
    show "A \<in> fundamental_groupin_space X x"
      by (rule A_in)
    show "fundamental_groupin_one X x \<in> fundamental_groupin_space X x"
      by (rule fundamental_groupin_one_in_space[OF x_in])
    show "some_loopin X x A \<in> loopin_space X x"
      by (rule repA(1))
    show "(\<lambda>_. x) \<in> loopin_space X x"
      by (rule const)
    show "A = loopin_class X x (some_loopin X x A)"
      by (rule repA(2))
    show "fundamental_groupin_one X x = loopin_class X x (\<lambda>_. x)"
      by (simp add: fundamental_groupin_one_def)
  qed
  have join_loop: "joinpathin (some_loopin X x A) (\<lambda>_. x) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF repA(1) const])
  have hom: "homotopic_pathsin X (joinpathin (some_loopin X x A) (\<lambda>_. x)) (some_loopin X x A)"
    using homotopic_pathsin_rid_const[OF loopA(1)] loopA(3) by simp
  have class_eq:
    "loopin_class X x (joinpathin (some_loopin X x A) (\<lambda>_. x)) = loopin_class X x (some_loopin X x A)"
    by (rule loopin_class_eqI[OF join_loop repA(1) hom])
  show ?thesis
    using mult_eq class_eq repA(2) by simp
qed

lemma fundamental_groupin_mult_assoc:
  assumes A_in: "A \<in> fundamental_groupin_space X x"
    and B_in: "B \<in> fundamental_groupin_space X x"
    and C_in: "C \<in> fundamental_groupin_space X x"
  shows "fundamental_groupin_mult X x A (fundamental_groupin_mult X x B C) =
    fundamental_groupin_mult X x (fundamental_groupin_mult X x A B) C"
proof -
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have repB: "some_loopin X x B \<in> loopin_space X x" "B = loopin_class X x (some_loopin X x B)"
    using some_loopin_spec[OF B_in] by auto
  have repC: "some_loopin X x C \<in> loopin_space X x" "C = loopin_class X x (some_loopin X x C)"
    using some_loopin_spec[OF C_in] by auto
  have loopA: "pathin X (some_loopin X x A)" "some_loopin X x A 0 = x" "some_loopin X x A 1 = x"
    using repA(1) by (auto elim: loopin_spaceE)
  have loopB: "pathin X (some_loopin X x B)" "some_loopin X x B 0 = x" "some_loopin X x B 1 = x"
    using repB(1) by (auto elim: loopin_spaceE)
  have loopC: "pathin X (some_loopin X x C)" "some_loopin X x C 0 = x" "some_loopin X x C 1 = x"
    using repC(1) by (auto elim: loopin_spaceE)
  have BC_eq:
    "fundamental_groupin_mult X x B C =
      loopin_class X x (joinpathin (some_loopin X x B) (some_loopin X x C))"
    by (rule fundamental_groupin_mult_eqI[OF B_in C_in repB(1) repC(1) repB(2) repC(2)])
  have AB_eq:
    "fundamental_groupin_mult X x A B =
      loopin_class X x (joinpathin (some_loopin X x A) (some_loopin X x B))"
    by (rule fundamental_groupin_mult_eqI[OF A_in B_in repA(1) repB(1) repA(2) repB(2)])
  have join_BC: "joinpathin (some_loopin X x B) (some_loopin X x C) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF repB(1) repC(1)])
  have join_AB: "joinpathin (some_loopin X x A) (some_loopin X x B) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF repA(1) repB(1)])
  have left_eq:
    "fundamental_groupin_mult X x A (fundamental_groupin_mult X x B C) =
      loopin_class X x
        (joinpathin (some_loopin X x A) (joinpathin (some_loopin X x B) (some_loopin X x C)))"
  proof (rule fundamental_groupin_mult_eqI)
    show "A \<in> fundamental_groupin_space X x"
      by (rule A_in)
    show "fundamental_groupin_mult X x B C \<in> fundamental_groupin_space X x"
      by (rule fundamental_groupin_mult_in_space[OF B_in C_in])
    show "some_loopin X x A \<in> loopin_space X x"
      by (rule repA(1))
    show "joinpathin (some_loopin X x B) (some_loopin X x C) \<in> loopin_space X x"
      by (rule join_BC)
    show "A = loopin_class X x (some_loopin X x A)"
      by (rule repA(2))
    show "fundamental_groupin_mult X x B C =
      loopin_class X x (joinpathin (some_loopin X x B) (some_loopin X x C))"
      by (rule BC_eq)
  qed
  have right_eq:
    "fundamental_groupin_mult X x (fundamental_groupin_mult X x A B) C =
      loopin_class X x
        (joinpathin (joinpathin (some_loopin X x A) (some_loopin X x B)) (some_loopin X x C))"
  proof (rule fundamental_groupin_mult_eqI)
    show "fundamental_groupin_mult X x A B \<in> fundamental_groupin_space X x"
      by (rule fundamental_groupin_mult_in_space[OF A_in B_in])
    show "C \<in> fundamental_groupin_space X x"
      by (rule C_in)
    show "joinpathin (some_loopin X x A) (some_loopin X x B) \<in> loopin_space X x"
      by (rule join_AB)
    show "some_loopin X x C \<in> loopin_space X x"
      by (rule repC(1))
    show "fundamental_groupin_mult X x A B =
      loopin_class X x (joinpathin (some_loopin X x A) (some_loopin X x B))"
      by (rule AB_eq)
    show "C = loopin_class X x (some_loopin X x C)"
      by (rule repC(2))
  qed
  have left_loop:
    "joinpathin (some_loopin X x A) (joinpathin (some_loopin X x B) (some_loopin X x C)) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF repA(1) join_BC])
  have right_loop:
    "joinpathin (joinpathin (some_loopin X x A) (some_loopin X x B)) (some_loopin X x C) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF join_AB repC(1)])
  have hom_assoc:
    "homotopic_pathsin X
      (joinpathin (some_loopin X x A) (joinpathin (some_loopin X x B) (some_loopin X x C)))
      (joinpathin (joinpathin (some_loopin X x A) (some_loopin X x B)) (some_loopin X x C))"
    by (rule homotopic_pathsin_assoc[OF loopA(1) loopB(1) loopC(1)]) (simp_all add: loopA loopB loopC)
  have class_eq:
    "loopin_class X x
      (joinpathin (some_loopin X x A) (joinpathin (some_loopin X x B) (some_loopin X x C))) =
      loopin_class X x
      (joinpathin (joinpathin (some_loopin X x A) (some_loopin X x B)) (some_loopin X x C))"
    by (rule loopin_class_eqI[OF left_loop right_loop hom_assoc])
  show ?thesis
    using left_eq right_eq class_eq by simp
qed

lemma fundamental_groupin_mult_inv_right:
  assumes x_in: "x \<in> topspace X"
    and A_in: "A \<in> fundamental_groupin_space X x"
  shows "fundamental_groupin_mult X x A (fundamental_groupin_inv X x A) = fundamental_groupin_one X x"
proof -
  have const: "(\<lambda>_. x) \<in> loopin_space X x"
    by (rule constant_loopin_in_space[OF x_in])
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have loopA: "pathin X (some_loopin X x A)" "some_loopin X x A 0 = x" "some_loopin X x A 1 = x"
    using repA(1) by (auto elim: loopin_spaceE)
  have inv_eq:
    "fundamental_groupin_inv X x A = loopin_class X x (reversepathin (some_loopin X x A))"
    by (rule fundamental_groupin_inv_eqI[OF A_in repA(1) repA(2)])
  have mult_eq:
    "fundamental_groupin_mult X x A (fundamental_groupin_inv X x A) =
      loopin_class X x (joinpathin (some_loopin X x A) (reversepathin (some_loopin X x A)))"
  proof (rule fundamental_groupin_mult_eqI)
    show "A \<in> fundamental_groupin_space X x"
      by (rule A_in)
    show "fundamental_groupin_inv X x A \<in> fundamental_groupin_space X x"
      by (rule fundamental_groupin_inv_in_space[OF A_in])
    show "some_loopin X x A \<in> loopin_space X x"
      by (rule repA(1))
    show "reversepathin (some_loopin X x A) \<in> loopin_space X x"
      by (rule loopin_space_reversepathin[OF repA(1)])
    show "A = loopin_class X x (some_loopin X x A)"
      by (rule repA(2))
    show "fundamental_groupin_inv X x A = loopin_class X x (reversepathin (some_loopin X x A))"
      by (rule inv_eq)
  qed
  have join_loop: "joinpathin (some_loopin X x A) (reversepathin (some_loopin X x A)) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF repA(1) loopin_space_reversepathin[OF repA(1)]])
  have hom:
    "homotopic_pathsin X
      (joinpathin (some_loopin X x A) (reversepathin (some_loopin X x A)))
      (\<lambda>_. x)"
    using homotopic_pathsin_rinv_const[OF loopA(1)] loopA(2) by simp
  have class_eq:
    "loopin_class X x (joinpathin (some_loopin X x A) (reversepathin (some_loopin X x A))) =
      loopin_class X x (\<lambda>_. x)"
    by (rule loopin_class_eqI[OF join_loop const hom])
  show ?thesis
    using mult_eq class_eq unfolding fundamental_groupin_one_def by simp
qed

lemma fundamental_groupin_mult_inv_left:
  assumes x_in: "x \<in> topspace X"
    and A_in: "A \<in> fundamental_groupin_space X x"
  shows "fundamental_groupin_mult X x (fundamental_groupin_inv X x A) A = fundamental_groupin_one X x"
proof -
  have const: "(\<lambda>_. x) \<in> loopin_space X x"
    by (rule constant_loopin_in_space[OF x_in])
  have repA: "some_loopin X x A \<in> loopin_space X x" "A = loopin_class X x (some_loopin X x A)"
    using some_loopin_spec[OF A_in] by auto
  have loopA: "pathin X (some_loopin X x A)" "some_loopin X x A 0 = x" "some_loopin X x A 1 = x"
    using repA(1) by (auto elim: loopin_spaceE)
  have inv_eq:
    "fundamental_groupin_inv X x A = loopin_class X x (reversepathin (some_loopin X x A))"
    by (rule fundamental_groupin_inv_eqI[OF A_in repA(1) repA(2)])
  have mult_eq:
    "fundamental_groupin_mult X x (fundamental_groupin_inv X x A) A =
      loopin_class X x (joinpathin (reversepathin (some_loopin X x A)) (some_loopin X x A))"
  proof (rule fundamental_groupin_mult_eqI)
    show "fundamental_groupin_inv X x A \<in> fundamental_groupin_space X x"
      by (rule fundamental_groupin_inv_in_space[OF A_in])
    show "A \<in> fundamental_groupin_space X x"
      by (rule A_in)
    show "reversepathin (some_loopin X x A) \<in> loopin_space X x"
      by (rule loopin_space_reversepathin[OF repA(1)])
    show "some_loopin X x A \<in> loopin_space X x"
      by (rule repA(1))
    show "fundamental_groupin_inv X x A = loopin_class X x (reversepathin (some_loopin X x A))"
      by (rule inv_eq)
    show "A = loopin_class X x (some_loopin X x A)"
      by (rule repA(2))
  qed
  have join_loop: "joinpathin (reversepathin (some_loopin X x A)) (some_loopin X x A) \<in> loopin_space X x"
    by (rule loopin_space_joinpathin[OF loopin_space_reversepathin[OF repA(1)] repA(1)])
  have hom:
    "homotopic_pathsin X
      (joinpathin (reversepathin (some_loopin X x A)) (some_loopin X x A))
      (\<lambda>_. x)"
    using homotopic_pathsin_linv_const[OF loopA(1)] loopA(3) by simp
  have class_eq:
    "loopin_class X x (joinpathin (reversepathin (some_loopin X x A)) (some_loopin X x A)) =
      loopin_class X x (\<lambda>_. x)"
    by (rule loopin_class_eqI[OF join_loop const hom])
  show ?thesis
    using mult_eq class_eq unfolding fundamental_groupin_one_def by simp
qed

lemma fundamental_groupin_carrier_group:
  assumes x_in: "x \<in> topspace X"
  shows "carrier_group
    (fundamental_groupin_space X x)
    (fundamental_groupin_mult X x)
    (fundamental_groupin_one X x)
    (fundamental_groupin_inv X x)"
proof
  show "fundamental_groupin_one X x \<in> fundamental_groupin_space X x"
    by (rule fundamental_groupin_one_in_space[OF x_in])
next
  fix A B
  assume "A \<in> fundamental_groupin_space X x" "B \<in> fundamental_groupin_space X x"
  then show "fundamental_groupin_mult X x A B \<in> fundamental_groupin_space X x"
    by (rule fundamental_groupin_mult_in_space)
next
  fix A
  assume "A \<in> fundamental_groupin_space X x"
  then show "fundamental_groupin_inv X x A \<in> fundamental_groupin_space X x"
    by (rule fundamental_groupin_inv_in_space)
next
  fix A B C
  assume A_in: "A \<in> fundamental_groupin_space X x"
    and B_in: "B \<in> fundamental_groupin_space X x"
    and C_in: "C \<in> fundamental_groupin_space X x"
  show
    "fundamental_groupin_mult X x (fundamental_groupin_mult X x A B) C =
      fundamental_groupin_mult X x A (fundamental_groupin_mult X x B C)"
    by (rule sym, rule fundamental_groupin_mult_assoc[OF A_in B_in C_in])
next
  fix A
  assume A_in: "A \<in> fundamental_groupin_space X x"
  show "fundamental_groupin_mult X x (fundamental_groupin_one X x) A = A"
    by (rule fundamental_groupin_mult_one_left[OF x_in A_in])
next
  fix A
  assume A_in: "A \<in> fundamental_groupin_space X x"
  show "fundamental_groupin_mult X x A (fundamental_groupin_one X x) = A"
    by (rule fundamental_groupin_mult_one_right[OF x_in A_in])
next
  fix A
  assume A_in: "A \<in> fundamental_groupin_space X x"
  show "fundamental_groupin_mult X x (fundamental_groupin_inv X x A) A = fundamental_groupin_one X x"
    by (rule fundamental_groupin_mult_inv_left[OF x_in A_in])
next
  fix A
  assume A_in: "A \<in> fundamental_groupin_space X x"
  show "fundamental_groupin_mult X x A (fundamental_groupin_inv X x A) = fundamental_groupin_one X x"
    by (rule fundamental_groupin_mult_inv_right[OF x_in A_in])
qed

lemma fundamental_groupin_map_carrier_group_hom:
  assumes x_in: "x \<in> topspace X"
    and h: "continuous_map X Y f"
    and fx: "f x = y"
  shows "carrier_group_hom
    (fundamental_groupin_space X x)
    (fundamental_groupin_mult X x)
    (fundamental_groupin_one X x)
    (fundamental_groupin_inv X x)
    (fundamental_groupin_space Y y)
    (fundamental_groupin_mult Y y)
    (fundamental_groupin_one Y y)
    (fundamental_groupin_inv Y y)
    (fundamental_groupin_map X x Y y f)"
proof -
  have y_in: "y \<in> topspace Y"
    using x_in h fx unfolding continuous_map_def by blast
  show ?thesis
  proof (rule carrier_group_hom.intro)
    show "carrier_group
      (fundamental_groupin_space X x)
      (fundamental_groupin_mult X x)
      (fundamental_groupin_one X x)
      (fundamental_groupin_inv X x)"
      by (rule fundamental_groupin_carrier_group[OF x_in])
    show "carrier_group
      (fundamental_groupin_space Y y)
      (fundamental_groupin_mult Y y)
      (fundamental_groupin_one Y y)
      (fundamental_groupin_inv Y y)"
      by (rule fundamental_groupin_carrier_group[OF y_in])
    show "carrier_group_hom_axioms
      (fundamental_groupin_space X x)
      (fundamental_groupin_mult X x)
      (fundamental_groupin_space Y y)
      (fundamental_groupin_mult Y y)
      (fundamental_groupin_map X x Y y f)"
    proof (rule carrier_group_hom_axioms.intro)
      fix A
      assume A_in: "A \<in> fundamental_groupin_space X x"
      show "fundamental_groupin_map X x Y y f A \<in> fundamental_groupin_space Y y"
        by (rule fundamental_groupin_map_in_space[OF A_in h fx])
    next
      fix A B
      assume A_in: "A \<in> fundamental_groupin_space X x"
        and B_in: "B \<in> fundamental_groupin_space X x"
      show "fundamental_groupin_map X x Y y f (fundamental_groupin_mult X x A B) =
          fundamental_groupin_mult Y y
            (fundamental_groupin_map X x Y y f A)
            (fundamental_groupin_map X x Y y f B)"
        by (rule fundamental_groupin_map_mult[OF A_in B_in h fx])
    qed
  qed
qed

lemma loopin_space_top_of_set [simp]:
  "loopin_space (top_of_set S) x = loop_space S x"
  unfolding loopin_space_def loop_space_def
  by (auto simp: pathin_canon_iff pathstart_def pathfinish_def path_image_def image_subset_iff_funcset)

lemma loopin_class_top_of_set [simp]:
  "loopin_class (top_of_set S) x p = loop_class S x p"
  unfolding loopin_class_def loop_class_def by simp

lemma fundamental_groupin_space_top_of_set [simp]:
  "fundamental_groupin_space (top_of_set S) x = fundamental_group_space S x"
  unfolding fundamental_groupin_space_def fundamental_group_space_def by simp

lemma fundamental_groupin_one_top_of_set [simp]:
  "fundamental_groupin_one (top_of_set S) x = fundamental_group_one S x"
  unfolding fundamental_groupin_one_def fundamental_group_one_def by simp

lemma loopin_image_eq_loop_image [simp]:
  "loopin_image h p = loop_image h p"
  unfolding loopin_image_def loop_image_def by simp

end
