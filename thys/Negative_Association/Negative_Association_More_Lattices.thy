section \<open>Preliminary Results on Lattices\<close>

text \<open>This entry establishes a few missing lemmas for the set-based theory of lattices from
``HOL-Algebra''. In particular, it introduces the sublocale for distributive lattices.

More crucially, a transfer theorem which can be used in conjunction with the Types-To-Sets mechanism
to be able to work with locally defined finite distributive lattices.

This is being needed for the verification of the negative association of permutation distributions
in Section~\ref{sec:permutation_distributions}.\<close>

theory Negative_Association_More_Lattices
  imports "HOL-Algebra.Lattice"
begin

text \<open>Lemma 1 Birkhoff Lattice Theory, p.8, L3\<close>
lemma (in lattice) meet_assoc_law:
  assumes "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
  using assms by (metis (full_types) eq_is_equal weak_meet_assoc)

text \<open>Lemma 1 Birkhoff Lattice Theory, p.8, L3\<close>
lemma (in lattice) join_assoc_law:
  assumes "x \<in> carrier L"  "y \<in> carrier L" "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  using assms by (metis (full_types) eq_is_equal weak_join_assoc)

text \<open>Lemma 1 Birkhoff Lattice Theory, p.8, L4\<close>
lemma (in lattice) absorbtion_law:
  assumes "x \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqinter> (x \<squnion> y) = x" "x \<squnion> (x \<sqinter> y) = x"
proof -
  have " x \<sqsubseteq> x \<squnion> y" using assms join_left by auto
  hence "x = x \<sqinter> (x \<squnion> y)" using assms by (intro iffD1[OF le_iff_join]) auto
  thus "x \<sqinter> (x \<squnion> y) = x" by simp

  have "x \<sqinter> y \<sqsubseteq> x" using assms meet_left by auto
  hence "(x \<sqinter> y) \<squnion>  x = x" using assms le_iff_meet by (intro iffD1[OF le_iff_meet]) auto
  thus  "x \<squnion> (x \<sqinter> y) = x" using join_comm by metis
qed

text \<open>Theorem 9 Birkhoff Lattice Theory, p.11\<close>
lemma (in lattice) distrib_laws_equiv:
  defines "meet_distrib \<equiv> (\<forall>x y z. {x,y,z}\<subseteq>carrier L \<longrightarrow> (x \<sqinter> (y \<squnion> z)) = (x \<sqinter> y) \<squnion> (x \<sqinter> z))"
  defines "join_distrib \<equiv> (\<forall>x y z. {x,y,z}\<subseteq>carrier L \<longrightarrow> (x \<squnion> (y \<sqinter> z)) = (x \<squnion> y) \<sqinter> (x \<squnion> z))"
  shows "meet_distrib \<longleftrightarrow> join_distrib"
proof
  assume a:"meet_distrib"
  have "(x \<squnion> y) \<sqinter> (x \<squnion> z)= x \<squnion> (y \<sqinter> z)" (is "?L = ?R") if "{x,y,z} \<subseteq> carrier L" for x y z
  proof -
    have "?L = ((x \<squnion> y) \<sqinter> x) \<squnion> ((x \<squnion> y) \<sqinter> z)" using a that unfolding meet_distrib_def by simp
    also have "\<dots> = x \<squnion> (z \<sqinter> (x \<squnion> y))" using that absorbtion_law meet_comm by (metis insert_subset)
    also have "\<dots> = x \<squnion> ((z \<sqinter> x) \<squnion> (z \<sqinter> y))" using a that unfolding meet_distrib_def by simp
    also have "\<dots> = (x \<squnion> (z \<sqinter> x)) \<squnion> (z \<sqinter> y)" using that meet_assoc_law join_assoc_law by simp
    also have "\<dots> = x \<squnion> (z \<sqinter> y)" using that absorbtion_law meet_comm by (metis insert_subset)
    also have "\<dots> = ?R" by (metis meet_comm)
    finally show ?thesis by simp
  qed
  thus "join_distrib" unfolding join_distrib_def by auto
next
  assume a:"join_distrib"
  have "(x \<sqinter> y) \<squnion> (x \<sqinter> z)= x \<sqinter> (y \<squnion> z)" (is "?L = ?R") if "{x,y,z} \<subseteq> carrier L" for x y z
  proof -
    have "?L = ((x \<sqinter> y) \<squnion> x) \<sqinter> ((x \<sqinter> y) \<squnion> z)" using a that unfolding join_distrib_def by simp
    also have "\<dots> = x \<sqinter> (z \<squnion> (x \<sqinter> y))" using that absorbtion_law join_comm by (metis insert_subset)
    also have "\<dots> = x \<sqinter> ((z \<squnion> x) \<sqinter> (z \<squnion> y))" using a that unfolding join_distrib_def by simp
    also have "\<dots> = (x \<sqinter> (z \<squnion> x)) \<sqinter> (z \<squnion> y)" using that meet_assoc_law join_assoc_law by simp
    also have "\<dots> = x \<sqinter> (z \<squnion> y)" using that absorbtion_law join_comm by (metis insert_subset)
    also have "\<dots> = ?R" by (metis join_comm)
    finally show ?thesis by simp
  qed
  thus "meet_distrib" unfolding meet_distrib_def by auto
qed

lemma (in lattice) lub_unique_set:
  assumes "is_lub L z S"
  shows "z = \<Squnion>S"
proof -
  have a:"is_lub L z' S \<Longrightarrow> z = z'" for z'
    using least_unique assms by simp
  show ?thesis
    unfolding sup_def
    by (rule someI2[where a="z"], rule assms(1), rule a)
qed

lemma (in lattice) lub_unique:
  assumes "is_lub L z {x,y}"
  shows "z = x \<squnion> y"
  using lub_unique_set[OF assms] unfolding join_def by auto

lemma (in lattice) glb_unique_set:
  assumes "is_glb L z S"
  shows "z = \<Sqinter>S"
proof -
  have a:"is_glb L z' S \<Longrightarrow> z = z'" for z'
    using greatest_unique assms(1) by simp
  show ?thesis
    unfolding meet_def inf_def
    by (rule someI2[where a="z"], rule assms(1), rule a)
qed

lemma (in lattice) glb_unique:
  assumes "is_glb L z {x,y}"
  shows "z = x \<sqinter> y"
  using glb_unique_set[OF assms] unfolding meet_def by auto

lemma (in lattice) inf_lower:
  assumes "S \<subseteq> carrier L" "s \<in> S" "finite S"
  shows "\<Sqinter>S \<sqsubseteq> s"
proof -
  have "is_glb L (\<Sqinter>S) S" using assms(2) by (intro finite_inf_greatest assms(1,3)) auto
  hence "(\<Sqinter>S) \<in> Lower L S" using greatest_mem by metis
  thus ?thesis using assms(1,2) by auto
qed

lemma (in lattice) sup_upper:
  assumes "S \<subseteq> carrier L" "s \<in> S" "finite S"
  shows "s \<sqsubseteq> \<Squnion>S"
proof -
  have "is_lub L (\<Squnion>S) S" using assms(2) by (intro finite_sup_least assms(1,3)) auto
  hence "(\<Squnion>S) \<in> Upper L S" using least_mem by metis
  thus ?thesis using assms(1,2) by auto
qed

locale distrib_lattice = lattice +
  assumes max_distrib:
    "x \<in> carrier L \<Longrightarrow> y \<in> carrier L \<Longrightarrow> z \<in> carrier L \<Longrightarrow> (x \<sqinter> (y \<squnion> z)) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
begin

lemma min_distrib:
  assumes "x \<in> carrier L" "y \<in> carrier L" "z \<in> carrier L"
  shows "(x \<squnion> (y \<sqinter> z)) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof -
  have a:"\<forall>x y z. {x, y, z} \<subseteq> carrier L \<longrightarrow> x \<sqinter> (y \<squnion> z) = x \<sqinter> y \<squnion> x \<sqinter> z" using max_distrib by auto
  show ?thesis using iffD1[OF distrib_laws_equiv a] assms by simp
qed

end

locale finite_ne_distrib_lattice = distrib_lattice +
  assumes non_empty_carrier: "carrier L \<noteq> {}"
  assumes finite_carrier: "finite (carrier L)"
begin

lemma bounded_lattice_axioms_1: "\<exists>x. least L x (carrier L)"
proof -
  have "\<Sqinter>carrier L \<in> Lower L (carrier L)"
    by (intro greatest_mem[where L="L"] finite_inf_greatest[OF finite_carrier _ non_empty_carrier])
      auto
  hence "\<forall>x \<in> carrier L. (\<Sqinter>carrier L)\<sqsubseteq>x" unfolding Lower_def by auto
  moreover have "\<Sqinter>carrier L \<in> carrier L"
    using finite_inf_closed[OF finite_carrier _ non_empty_carrier] by auto
  ultimately have "least L (\<Sqinter>carrier L) (carrier L)"
    unfolding least_def by auto

  thus ?thesis by auto
qed

lemma bounded_lattice_axioms_2: "\<exists>x. greatest L x (carrier L)"
proof -
  have "\<Squnion>carrier L \<in> Upper L (carrier L)"
    by (intro least_mem[where L="L"] finite_sup_least[OF finite_carrier _ non_empty_carrier])
      auto
  hence "\<forall>x \<in> carrier L. x \<sqsubseteq> (\<Squnion>carrier L)" unfolding Upper_def by auto
  moreover have "\<Squnion>carrier L \<in> carrier L"
    using finite_sup_closed[OF finite_carrier _ non_empty_carrier] by auto
  ultimately have "greatest L (\<Squnion>carrier L) (carrier L)"
    unfolding greatest_def by auto

  thus ?thesis by auto
qed

sublocale bounded_lattice
  using bounded_lattice_axioms_1 bounded_lattice_axioms_2
  by (unfold_locales) auto

lemma inf_empty: "\<Sqinter> {} = \<top>"
proof -
  have "is_glb L \<top> {}" using top_greatest by simp
  thus ?thesis using glb_unique_set by auto
qed

lemma inf_closed: "S \<subseteq> carrier L \<Longrightarrow>\<Sqinter>S \<in> carrier L"
  using finite_carrier inf_empty top_closed finite_inf_closed
  by (metis finite_subset)

lemma inf_insert:
  assumes "x \<in> carrier L" "S \<subseteq> carrier L"
  shows "\<Sqinter> (insert x S) = x \<sqinter> (\<Sqinter>S)"
proof -
  have fin_S: "finite S" using finite_carrier assms(2) finite_subset by metis
  have inf_S_carr: "\<Sqinter>S \<in> carrier L" using inf_closed[OF assms(2)] by force

  have "x \<sqinter> (\<Sqinter>S) \<sqsubseteq> s" if "s \<in> S" for s
  proof -
    have "\<Sqinter>S \<sqsubseteq> s" using that fin_S assms(2)
      by (metis empty_iff finite_inf_greatest greatest_Lower_below)
    moreover have "x \<sqinter> (\<Sqinter>S) \<sqsubseteq> \<Sqinter>S" using inf_S_carr assms(1) meet_right by metis
    ultimately show ?thesis using inf_S_carr meet_closed
      by (meson assms le_trans subsetD that)
  qed
  moreover have "x \<sqinter> (\<Sqinter>S) \<sqsubseteq> x" using inf_S_carr assms(1) meet_left by metis
  ultimately have "x \<sqinter> (\<Sqinter>S) \<in> Lower L (insert x S)"
    using assms(1) meet_closed inf_S_carr unfolding Lower_def by auto
  moreover have "y \<sqsubseteq> (x \<sqinter> (\<Sqinter>S))" if "y \<in> Lower L (insert x S)" for y
  proof-
    have y_carr: "y \<in> carrier L" using that assms unfolding Lower_def by auto
    have y_lb: "y \<sqsubseteq> x" using that assms unfolding Lower_def by auto

    moreover have "y \<in> Lower L S" using that unfolding Lower_def by auto
    hence "y \<sqsubseteq> \<Sqinter>S" using finite_inf_greatest[OF fin_S assms(2)]
      by (metis greatest_le inf_empty top_higher y_carr)
    ultimately show ?thesis
      using y_carr inf_S_carr assms(1) meet_le by simp
  qed
  ultimately have "is_glb L (x \<sqinter> (\<Sqinter>S)) (insert x S)" by (simp add: greatest_def)
  thus ?thesis by (intro glb_unique_set[symmetric])
qed

lemma sup_empty: "\<Squnion> {} = \<bottom>"
proof -
  have "is_lub L \<bottom> {}" using bottom_least by simp
  thus ?thesis using lub_unique_set by auto
qed

lemma sup_closed: "S \<subseteq> carrier L \<Longrightarrow>\<Squnion> S \<in> carrier L"
  using finite_carrier sup_empty bottom_closed finite_sup_closed
  by (metis finite_subset)

lemma sup_insert:
  assumes "x \<in> carrier L" "S \<subseteq> carrier L"
  shows "\<Squnion> (insert x S) = x \<squnion> (\<Squnion>S)"
proof -
  have fin_S: "finite S" using finite_carrier assms(2) finite_subset by metis
  have sup_S_carr: "\<Squnion>S \<in> carrier L" using sup_closed[OF assms(2)] by force

  have "s \<sqsubseteq> x \<squnion> (\<Squnion>S)" if "s \<in> S" for s
  proof -
    have "s \<sqsubseteq> \<Squnion>S" using that fin_S assms(2)
      by (metis empty_iff finite_sup_least least_Upper_above)
    moreover have " \<Squnion>S \<sqsubseteq> x \<squnion> (\<Squnion>S) " using sup_S_carr assms(1) join_right by metis
    ultimately show ?thesis using sup_S_carr join_closed assms
      by (meson le_trans subsetD that)
  qed
  moreover have "x \<sqsubseteq> x \<squnion> (\<Squnion>S)" using sup_S_carr assms(1) join_left by metis
  ultimately have "x \<squnion> (\<Squnion>S) \<in> Upper L (insert x S)"
    using assms(1) sup_S_carr unfolding Upper_def by auto
  moreover have "x \<squnion> (\<Squnion>S) \<sqsubseteq> y" if "y \<in> Upper L (insert x S)" for y
  proof-
    have y_carr: "y \<in> carrier L" using that assms unfolding Lower_def by auto
    have y_lb: "x \<sqsubseteq> y" using that assms by auto

    moreover have "y \<in> Upper L S" using that unfolding Upper_def by auto
    hence "\<Squnion>S \<sqsubseteq> y" using finite_sup_least[OF fin_S assms(2)]
      using least_le sup_empty bottom_lower y_carr by metis
    ultimately show ?thesis
      using y_carr sup_S_carr assms(1) join_le by simp
  qed
  ultimately have "is_lub L (x \<squnion> (\<Squnion>S)) (insert x S)" by (simp add: least_def)
  thus ?thesis by (intro lub_unique_set[symmetric])
qed

lemma inf_carrier: "\<Sqinter> (carrier L) = \<bottom>"
proof -
  have "\<Sqinter>carrier L \<in> Lower L (carrier L)"
    by (intro greatest_mem[where L="L"] finite_inf_greatest[OF finite_carrier _ non_empty_carrier])
      auto
  hence "\<forall>x \<in> carrier L. (\<Sqinter>carrier L)\<sqsubseteq>x" unfolding Lower_def by auto
  moreover have "\<Sqinter>carrier L \<in> carrier L"
    using finite_inf_closed[OF finite_carrier _ non_empty_carrier] by auto
  ultimately show ?thesis by (intro bottom_eq) auto
qed

lemma sup_carrier: "\<Squnion> (carrier L) = \<top>"
proof -
  have "\<Squnion>carrier L \<in> Upper L (carrier L)"
    by (intro least_mem[where L="L"] finite_sup_least[OF finite_carrier _ non_empty_carrier])
      auto
  hence "\<forall>x \<in> carrier L. x\<sqsubseteq> (\<Squnion>carrier L)" unfolding Upper_def by auto
  moreover have "\<Squnion>carrier L \<in> carrier L"
    using finite_sup_closed[OF finite_carrier _ non_empty_carrier] by auto
  ultimately show ?thesis by (intro top_eq) auto
qed


lemma transfer_to_type:
  assumes "finite (carrier L)" "type_definition Rep Abs (carrier L)"
  defines "inf' \<equiv> (\<lambda>M. Abs (\<Sqinter> Rep ` M))"
  defines "sup' \<equiv> (\<lambda>M. Abs (\<Squnion> Rep ` M))"
  defines "join' \<equiv> (\<lambda>x y. Abs (Rep x \<sqinter> Rep y))"
  defines "le' \<equiv> (\<lambda>x y. (Rep x \<sqsubseteq> Rep y))"
  defines "less' \<equiv> (\<lambda>x y. (Rep x \<sqsubset> Rep y))"
  defines "meet' \<equiv> (\<lambda>x y. (Abs (Rep x \<squnion> Rep y)))"
  defines "bot'\<equiv> (Abs \<bottom> :: 'c)"
  defines "top' \<equiv> Abs \<top>"
  shows "class.finite_distrib_lattice inf' sup' join' le' less' meet' bot' top'"
proof -
  interpret type_definition Rep Abs "(carrier L)"
    using assms(2) by auto

  note defs = inf'_def sup'_def join'_def le'_def less'_def meet'_def bot'_def bot'_def top'_def
  note td = Rep Rep_inverse Abs_inverse inf_closed sup_closed meet_closed join_closed Rep_range

  have class_lattice: "class.lattice join' le' less' meet'"
    unfolding defs using td
  proof (unfold_locales, goal_cases)
    case 1 thus ?case unfolding lless_eq by auto
  next
    case 2 thus ?case by (metis le_refl)
  next
    case 3 thus ?case by (metis le_trans)
  next
    case 4 thus ?case by (meson Rep_inject local.le_antisym)
  next
    case 5 thus ?case by (metis meet_left)
  next
    case 6 thus ?case by (metis meet_right)
  next
    case 7 thus ?case by (metis meet_le)
  next
    case 8 thus ?case by (metis join_left)
  next
    case 9 thus ?case by (metis join_right)
  next
    case 10 thus ?case by (metis join_le)
  qed

  have class_distrib_lattice: "class.distrib_lattice join' le' less' meet'"
    unfolding class.distrib_lattice_def eqTrueI[OF class_lattice]
    unfolding defs class.distrib_lattice_axioms_def using td
    using min_distrib by auto

  have class_finite: "class.finite TYPE('c)"
    by (unfold_locales) (metis assms(1) Abs_image finite_imageI)

  have class_finite_lattice: "class.finite_lattice inf' sup' join' le' less' meet' bot' top'"
    unfolding class.finite_lattice_def  eqTrueI[OF class_lattice] eqTrueI[OF class_finite]
    unfolding defs class.distrib_lattice_axioms_def class.finite_lattice_axioms_def using td
  proof (intro conjI TrueI, goal_cases)
    case 1 thus ?case using sup_carrier inf_empty by simp
  next
    case 2 thus ?case unfolding image_insert by (metis inf_insert image_subsetI)
  next
    case 3 thus ?case using inf_carrier sup_empty by simp
  next
    case 4 thus ?case unfolding image_insert by (metis sup_insert image_subsetI)
  next
    case 5 thus ?case using inf_carrier by simp
  next
    case 6 thus ?case using sup_carrier by simp
  qed

  show ?thesis
    using class_finite_lattice class_distrib_lattice
    unfolding class.finite_distrib_lattice_def by auto
qed

end

end
