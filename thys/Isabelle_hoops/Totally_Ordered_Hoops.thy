section\<open>Totally ordered hoops\<close>

theory Totally_Ordered_Hoops
  imports Ordinal_Sums
begin

subsection\<open>Definitions\<close>

locale totally_ordered_hoop = hoop +
  assumes total_order: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le>\<^sup>A y \<or> y \<le>\<^sup>A x "
begin

function fixed_points :: "'a \<Rightarrow> 'a set" ("F") where
  "F a = {b \<in> A-{1\<^sup>A}. a \<rightarrow>\<^sup>A b = b}" if "a \<in> A-{1\<^sup>A}"
| "F a = {1\<^sup>A}" if "a = 1\<^sup>A" 
| "F a = undefined" if "a \<notin> A"
  by auto
termination by lexicographic_order 

definition rel_F :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sim>F" 60)
  where "x \<sim>F y \<equiv> \<forall> z \<in> A. (x \<rightarrow>\<^sup>A z = z) \<longleftrightarrow> (y \<rightarrow>\<^sup>A z = z)" 

definition rel_F_canonical_map :: "'a \<Rightarrow> 'a set" ("\<pi>")
  where "\<pi> x = {b \<in> A. x \<sim>F b}"

end

subsection\<open>Properties of @{text F}\<close>

context totally_ordered_hoop 
begin

lemma F_equiv:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A"
  shows "b \<in> F a \<longleftrightarrow> (b \<in> A \<and> b \<noteq> 1\<^sup>A \<and> a \<rightarrow>\<^sup>A b = b)"
  using assms by auto

lemma F_subset:
  assumes "a \<in> A" 
  shows "F a \<subseteq> A"
proof -
  have "a = 1\<^sup>A \<or> a \<noteq> 1\<^sup>A"
    by auto
  then
  show ?thesis
    using assms by fastforce
qed 

lemma F_of_one:
  assumes "a \<in> A"
  shows "F a = {1\<^sup>A} \<longleftrightarrow> a = 1\<^sup>A"
  using F_equiv assms fixed_points.simps(2) top_closed by blast

lemma F_of_mult:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}"
  shows "F (a *\<^sup>A b) = {c \<in> A-{1\<^sup>A}. (a *\<^sup>A b) \<rightarrow>\<^sup>A c = c}"
  using assms mult_C by auto

lemma F_of_imp:
  assumes "a \<in> A" "b \<in> A" "a \<rightarrow>\<^sup>A b \<noteq> 1\<^sup>A"
  shows "F (a \<rightarrow>\<^sup>A b) = {c \<in> A-{1\<^sup>A}. (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A c = c}"
  using assms imp_closed by auto

lemma F_bound:
  assumes "a \<in> A" "b \<in> A" "a \<in> F b"
  shows "a \<le>\<^sup>A b"
proof -
  consider (1) "b \<noteq> 1\<^sup>A"
    | (2) "b = 1\<^sup>A"
    by auto
  then
  show "?thesis"
  proof(cases)
    case 1
    then
    have "b \<rightarrow>\<^sup>A a \<noteq> 1\<^sup>A"
      using assms(2,3) by simp
    then
    show ?thesis     
      using assms hoop_order_def total_order by auto
  next
    case 2
    then
    show ?thesis
      using assms(1) ord_top by auto
  qed
qed

text\<open>The following results can be found in Lemma 3.3 in \<^cite>\<open>"BUSANICHE2005"\<close>.\<close>

lemma LEMMA_3_3_1:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A" "c \<in> A" "b \<in> F a" "c \<le>\<^sup>A b"
  shows "c \<in> F a"
proof -
  from assms
  have "(a \<rightarrow>\<^sup>A c) \<le>\<^sup>A (a \<rightarrow>\<^sup>A b)"
    using DiffD1 F_equiv ord_imp_mono_B by metis
  then
  have "(a \<rightarrow>\<^sup>A c) \<le>\<^sup>A b"
    using assms(1,4,5) by simp
  then
  have "(a \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A c = ((a \<rightarrow>\<^sup>A c) *\<^sup>A ((a \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A b)) \<rightarrow>\<^sup>A c"
    using assms(1,3) hoop_order_def imp_closed by force
  also
  have "\<dots> = (b *\<^sup>A (b \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c))) \<rightarrow>\<^sup>A c"
    using assms divisibility imp_closed by simp
  also
  have "\<dots> = (b \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c)) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A c)"
    using DiffD1 assms(1-3) imp_closed swap residuation by metis
  also
  have "\<dots> = ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c)) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A c)"
    using assms(1,4) by simp
  also
  have "\<dots> = (((a \<rightarrow>\<^sup>A b) *\<^sup>A a) \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A c)"
    using assms(1,3,4) residuation by simp
  also
  have "\<dots> = (((b \<rightarrow>\<^sup>A a) *\<^sup>A b) \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A c)"
    using assms(1,2) divisibility imp_closed mult_comm by simp
  also
  have "\<dots> = (b \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A c)"
    using F_bound assms(1,4) hoop_order_def by simp
  also
  have "\<dots> = 1\<^sup>A"
    using F_bound assms hoop_order_def imp_closed by simp
  finally
  have "(a \<rightarrow>\<^sup>A c) \<le>\<^sup>A c"
    using hoop_order_def by simp
  moreover
  have "c \<le>\<^sup>A (a \<rightarrow>\<^sup>A c)"
    using assms(1,3) ord_A by simp
  ultimately
  have "a \<rightarrow>\<^sup>A c = c"
    using assms(1,3) imp_closed ord_antisymm by simp
  moreover 
  have "c \<in> A-{1\<^sup>A}"
    using assms(1,3-5) hoop_order_def imp_one_C by auto
  ultimately
  show ?thesis
    using F_equiv assms(1) by blast
qed

lemma LEMMA_3_3_2:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "F a = F b"
  shows "F a = F (a *\<^sup>A b)"
proof 
  show "F a \<subseteq> F (a *\<^sup>A b)"
  proof 
    fix c 
    assume "c \<in> F a"
    then
    have "(a *\<^sup>A b) \<rightarrow>\<^sup>A c = b \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c)"
      using DiffD1 F_subset assms(1,2) in_mono swap residuation by metis
    also
    have "\<dots> = b \<rightarrow>\<^sup>A c"
      using \<open>c \<in> F a\<close> assms(1) by auto
    also
    have "\<dots> = c"
      using \<open>c \<in> F a\<close> assms(2,3) by auto
    finally
    show "c \<in> F (a *\<^sup>A b)"
      using \<open>c \<in> F a\<close> assms(1,2) mult_C by auto
  qed
next 
  show "F (a *\<^sup>A b) \<subseteq> F a"
  proof 
    fix c
    assume "c \<in> F (a *\<^sup>A b)"
    then
    have "(a *\<^sup>A b) \<le>\<^sup>A a"
      using assms(1,2) mult_A by auto
    then
    have "(a \<rightarrow>\<^sup>A c) \<le>\<^sup>A ((a *\<^sup>A b) \<rightarrow>\<^sup>A c)"
      using DiffD1 F_subset \<open>c \<in> F (a *\<^sup>A b)\<close> assms mult_closed 
            ord_imp_anti_mono_B subsetD
      by meson
    moreover
    have "(a *\<^sup>A b) \<rightarrow>\<^sup>A c = c"
      using \<open>c \<in> F (a *\<^sup>A b)\<close> assms(1,2) mult_C by auto
    ultimately
    have "(a \<rightarrow>\<^sup>A c) \<le>\<^sup>A c"
      by simp
    moreover
    have "c \<le>\<^sup>A (a \<rightarrow>\<^sup>A c)"
      using DiffD1 F_subset \<open>c \<in> F (a *\<^sup>A b)\<close> assms(1,2) insert_Diff
            insert_subset mult_closed ord_A
      by metis
    ultimately
    show "c \<in> F a"
      using \<open>c \<in> F (a *\<^sup>A b)\<close> assms(1,2) imp_closed mult_C ord_antisymm by auto
  qed
qed

lemma LEMMA_3_3_3:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "a \<le>\<^sup>A b" 
  shows "F a \<subseteq> F b"
proof 
  fix c
  assume "c \<in> F a"
  then 
  have "(b \<rightarrow>\<^sup>A c) \<le>\<^sup>A (a \<rightarrow>\<^sup>A c)"
    using DiffD1 F_subset assms in_mono ord_imp_anti_mono_B by meson
  moreover 
  have "a \<rightarrow>\<^sup>A c = c"
    using \<open>c \<in> F a\<close> assms(1) by auto
  ultimately 
  have "(b \<rightarrow>\<^sup>A c) \<le>\<^sup>A c"
    by simp
  moreover
  have "c \<le>\<^sup>A (b \<rightarrow>\<^sup>A c)"
    using \<open>c \<in> F a\<close> assms(1,2) ord_A by force
  ultimately
  show "c \<in> F b"
    using \<open>c \<in> F a\<close> assms(1,2) imp_closed ord_antisymm by auto
qed

lemma LEMMA_3_3_4:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "a <\<^sup>A b" "F a \<noteq> F b"
  shows "a \<in> F b"
proof -
  from assms
  obtain c where "c \<in> F b \<and> c \<notin> F a"
    using LEMMA_3_3_3 hoop_order_strict_def by auto
  then
  have witness: "c \<in> A-{1\<^sup>A} \<and> b \<rightarrow>\<^sup>A c = c \<and> c <\<^sup>A (a \<rightarrow>\<^sup>A c)"
    using DiffD1 assms(1,2) hoop_order_strict_def ord_A by auto
  then
  have "(a \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A c \<in> F b"
    using DiffD1 F_equiv assms(1,2) imp_closed swap ord_D by metis
  moreover
  have "a \<le>\<^sup>A ((a \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A c)"
    using assms(1) ord_C witness by force
  ultimately
  show "a \<in> F b"
    using Diff_iff LEMMA_3_3_1 assms(1,2) imp_closed witness by metis
qed

lemma LEMMA_3_3_5:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "F a \<noteq> F b"
  shows "a *\<^sup>A b = a \<and>\<^sup>A b"
proof -
  have "a <\<^sup>A b \<or> b <\<^sup>A a"
    using DiffD1 assms hoop_order_strict_def total_order by metis
  then
  have "a \<in> F b \<or> b \<in> F a"
    using LEMMA_3_3_4 assms by metis
  then
  have "a *\<^sup>A b = (b \<rightarrow>\<^sup>A a) *\<^sup>A b \<or> a *\<^sup>A b = a *\<^sup>A (a \<rightarrow>\<^sup>A b)"
    using assms(1,2) by force
  then
  show ?thesis
    using assms(1,2) divisibility hoop_inf_def imp_closed mult_comm by auto
qed

lemma LEMMA_3_3_6:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "a <\<^sup>A b" "F a = F b"
  shows "F (b \<rightarrow>\<^sup>A a) = F b"
proof -
  have "a \<notin> F a"
    using assms(1) DiffD1 F_equiv imp_reflex by metis
  then
  have "a <\<^sup>A (b \<rightarrow>\<^sup>A a)"
    using assms(1,2,4) hoop_order_strict_def ord_A by auto
  moreover
  have "b *\<^sup>A (b \<rightarrow>\<^sup>A a) = a"
    using assms(1-3) divisibility hoop_order_def hoop_order_strict_def by simp
  moreover
  have "b \<le>\<^sup>A (b \<rightarrow>\<^sup>A a) \<or> (b \<rightarrow>\<^sup>A a) \<le>\<^sup>A b"
    using DiffD1 assms(1,2) imp_closed ord_reflex total_order by metis
  ultimately
  have "b *\<^sup>A (b \<rightarrow>\<^sup>A a) \<noteq> b \<and>\<^sup>A (b \<rightarrow>\<^sup>A a)"
    using assms(1-3) hoop_order_strict_def imp_closed inf_comm inf_order by force
  then
  show "F (b \<rightarrow>\<^sup>A a) = F b"
    using LEMMA_3_3_5 assms(1-3) imp_closed ord_D by blast
qed

subsection\<open>Properties of @{term rel_F}\<close>

subsubsection\<open>@{term rel_F} is an equivalence relation\<close>

lemma rel_F_reflex:
  assumes "a \<in> A"
  shows "a \<sim>F a"
  using rel_F_def by auto

lemma rel_F_symm: 
  assumes "a \<in> A" "b \<in> A" "a \<sim>F b"
  shows "b \<sim>F a"
  using assms rel_F_def by auto

lemma rel_F_trans:
  assumes "a \<in> A" "b \<in> A" "c \<in> A" "a \<sim>F b" "b \<sim>F c"
  shows "a \<sim>F c"
  using assms rel_F_def by auto

subsubsection\<open>Equivalent definition\<close>

lemma rel_F_equiv: 
  assumes "a \<in> A" "b \<in> A"
  shows "(a \<sim>F b) = (F a = F b)"
proof 
  assume "a \<sim>F b"
  then
  consider (1) "a \<noteq> 1\<^sup>A" "b \<noteq> 1\<^sup>A"
    | (2) "a = 1\<^sup>A" "b = 1\<^sup>A"
    using assms imp_one_C rel_F_def by fastforce
  then
  show "F a = F b"
  proof(cases)
    case 1
    then 
    show ?thesis
      using \<open>a \<sim>F b\<close> assms rel_F_def by auto
  next
    case 2
    then
    show ?thesis
      by simp
  qed
next
  assume "F a = F b"
  then
  consider (1) "a \<noteq> 1\<^sup>A" "b \<noteq> 1\<^sup>A"
    | (2) "a = 1\<^sup>A" "b = 1\<^sup>A"
    using F_of_one assms by blast
  then
  show "a \<sim>F b"
  proof(cases)
    case 1
    then
    show ?thesis
      using \<open>F a = F b\<close> assms imp_one_A imp_one_C rel_F_def by auto
  next
    case 2
    then
    show ?thesis
      using rel_F_reflex by simp
  qed
qed

subsubsection\<open>Properties of equivalence classes given by @{term rel_F}\<close>

lemma class_one: "\<pi> 1\<^sup>A = {1\<^sup>A}"
  using imp_one_C rel_F_canonical_map_def rel_F_def by auto

lemma classes_subsets:
  assumes "a \<in> A"
  shows "\<pi> a \<subseteq> A"
  using rel_F_canonical_map_def by simp

lemma classes_not_empty:
  assumes "a \<in> A"
  shows "a \<in> \<pi> a"
  using assms rel_F_canonical_map_def rel_F_reflex by simp

corollary class_not_one:
  assumes "a \<in> A-{1\<^sup>A}"
  shows "\<pi> a \<noteq> {1\<^sup>A}"
  using assms classes_not_empty by blast

lemma classes_disjoint: 
  assumes "a \<in> A" "b \<in> A" "\<pi> a \<inter> \<pi> b \<noteq> \<emptyset>"
  shows "\<pi> a = \<pi> b"
  using assms rel_F_canonical_map_def rel_F_def rel_F_trans by force

lemma classes_cover: "A = {x. \<exists> y \<in> A. x \<in> \<pi> y}"
  using classes_subsets classes_not_empty by auto

lemma classes_convex:
  assumes "a \<in> A" "b \<in> A" "c \<in> A" "d \<in> A" "b \<in> \<pi> a" "c \<in> \<pi> a" "b \<le>\<^sup>A d" "d \<le>\<^sup>A c" 
  shows "d \<in> \<pi> a"
proof -
  have eq_F: "F a = F b \<and> F a = F c"
    using assms(1,5,6) rel_F_canonical_map_def rel_F_equiv by auto
  from assms 
  consider (1) "c = 1\<^sup>A"
    | (2) "c \<noteq> 1\<^sup>A"
    by auto
  then 
  show ?thesis
  proof(cases)
    case 1 
    then
    have "b = 1\<^sup>A"
      using F_of_one eq_F assms(2) by auto
    then
    show ?thesis
      using "1" assms(2,4,5,7,8) ord_antisymm by blast
  next
    case 2
    then 
    have "b \<noteq> 1\<^sup>A \<and> c \<noteq> 1\<^sup>A \<and> d \<noteq> 1\<^sup>A"
      using eq_F assms(3,8) ord_antisymm ord_top by auto
    then
    have "F b \<subseteq> F d \<and> F d \<subseteq> F c"
      using LEMMA_3_3_3 assms(2-4,7,8) by simp
    then
    have "F a = F d"
      using eq_F by blast
    then
    have "a \<sim>F d"
      using assms(1,4) rel_F_equiv by simp
    then
    show ?thesis
      using assms(4) rel_F_canonical_map_def by simp
  qed
qed

lemma related_iff_same_class:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<sim>F b \<longleftrightarrow> \<pi> a = \<pi> b"
proof 
  assume "a \<sim>F b"
  then
  have "a = 1\<^sup>A \<longleftrightarrow> b = 1\<^sup>A"
    using assms imp_one_C imp_reflex rel_F_def by metis
  then
  have "(a = 1\<^sup>A \<and> b = 1\<^sup>A) \<or> (a \<noteq> 1\<^sup>A \<and> b \<noteq> 1\<^sup>A)"
    by auto
  then
  show "\<pi> a = \<pi> b"
    using \<open>a \<sim>F b\<close> assms rel_F_canonical_map_def rel_F_def rel_F_symm by force
next
  show "\<pi> a = \<pi> b \<Longrightarrow> a \<sim>F b"
    using assms(2) classes_not_empty rel_F_canonical_map_def by auto
qed

corollary same_F_iff_same_class:
  assumes "a \<in> A" "b \<in> A"
  shows "F a = F b \<longleftrightarrow> \<pi> a = \<pi> b"
  using assms rel_F_equiv related_iff_same_class by auto

end

subsection\<open>Irreducible hoops: definition and equivalences\<close>

text\<open>A totally ordered hoop is @{text irreducible} if it cannot be written as the ordinal sum
of two nontrivial totally ordered hoops.\<close>

locale totally_ordered_irreducible_hoop = totally_ordered_hoop +
  assumes irreducible:  "\<nexists> B C. 
    (A = B \<union> C) \<and>
    ({1\<^sup>A} = B \<inter> C) \<and>
    (\<exists> y \<in> B. y \<noteq> 1\<^sup>A) \<and>
    (\<exists> y \<in> C. y \<noteq> 1\<^sup>A) \<and>
    (hoop B (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A) \<and>
    (hoop C (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A) \<and>
    (\<forall> x \<in> B-{1\<^sup>A}. \<forall> y \<in> C. x *\<^sup>A y = x) \<and>
    (\<forall> x \<in> B-{1\<^sup>A}. \<forall> y \<in> C. x \<rightarrow>\<^sup>A y = 1\<^sup>A) \<and>
    (\<forall> x \<in> C. \<forall> y \<in> B. x \<rightarrow>\<^sup>A y = y)"

lemma irr_test: 
  assumes "totally_ordered_hoop A PA RA a"
          "\<not>totally_ordered_irreducible_hoop A PA RA a"
  shows "\<exists> B C. 
    (A = B \<union> C) \<and>
    ({a} = B \<inter> C) \<and>
    (\<exists> y \<in> B. y \<noteq> a) \<and>
    (\<exists> y \<in> C. y \<noteq> a) \<and>
    (hoop B PA RA a) \<and>
    (hoop C PA RA a) \<and> 
    (\<forall> x \<in> B-{a}. \<forall> y \<in> C. PA x y = x) \<and>
    (\<forall> x \<in> B-{a}. \<forall> y \<in> C. RA x y = a) \<and>
    (\<forall> x \<in> C. \<forall> y \<in> B. RA x y = y)" 
  using assms unfolding totally_ordered_irreducible_hoop_def
                        totally_ordered_irreducible_hoop_axioms_def
  by force

locale totally_ordered_one_fixed_hoop = totally_ordered_hoop +
  assumes one_fixed: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> y \<rightarrow>\<^sup>A x = x \<Longrightarrow> x = 1\<^sup>A \<or> y = 1\<^sup>A"

locale totally_ordered_wajsberg_hoop = totally_ordered_hoop + wajsberg_hoop

context totally_ordered_hoop
begin

text\<open>The following result can be found in \<^cite>\<open>"AGLIANO2003"\<close> (see Lemma 3.5).\<close>

lemma not_one_fixed_implies_not_irreducible:
  assumes "\<not>totally_ordered_one_fixed_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  shows "\<not>totally_ordered_irreducible_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
proof -
  have "\<exists> x y. x \<in> A \<and> y \<in> A \<and> y \<rightarrow>\<^sup>A x = x \<and> x \<noteq> 1\<^sup>A \<and> y \<noteq> 1\<^sup>A"
    using assms totally_ordered_hoop_axioms totally_ordered_one_fixed_hoop.intro
          totally_ordered_one_fixed_hoop_axioms.intro
    by meson
  then
  obtain b\<^sub>0 c\<^sub>0 where witnesses: "b\<^sub>0 \<in> A-{1\<^sup>A} \<and> c\<^sub>0 \<in> A-{1\<^sup>A} \<and> b\<^sub>0 \<rightarrow>\<^sup>A c\<^sub>0 = c\<^sub>0"
    by auto
  define B C where "B = (F b\<^sub>0) \<union> {1\<^sup>A}" and "C = A-(F b\<^sub>0)"

  have B_mult_b0: "b *\<^sup>A b\<^sub>0 = b" if "b \<in> B-{1\<^sup>A}" for b 
  proof -
    have upper_bound: "b \<le>\<^sup>A b\<^sub>0" if "b \<in> B-{1\<^sup>A}" for b
      using B_def F_bound witnesses that by force
    then
    have "b *\<^sup>A b\<^sub>0 = b\<^sub>0 *\<^sup>A b"
      using B_def witnesses mult_comm that by simp
    also
    have "\<dots> = b\<^sub>0 *\<^sup>A (b\<^sub>0 \<rightarrow>\<^sup>A b)"
      using B_def witnesses that by fastforce
    also
    have "\<dots> = b *\<^sup>A (b \<rightarrow>\<^sup>A b\<^sub>0)"
      using B_def witnesses that divisibility by auto
    also 
    have "\<dots> = b"
      using B_def hoop_order_def that upper_bound witnesses by auto
    finally
    show "b *\<^sup>A b\<^sub>0 = b"
      by auto
  qed

  have C_upper_set: "a \<in> C" if "a \<in> A" "c \<in> C" "c \<le>\<^sup>A a" for a c
  proof -
    consider (1) "a \<noteq> 1\<^sup>A"
      | (2) "a = 1\<^sup>A"
      by auto
    then
    show "a \<in> C"
    proof(cases)
      case 1
      then
      have "a \<notin> C \<Longrightarrow> a \<in> F b\<^sub>0"
        using C_def that(1) by blast
      then
      have "a \<notin> C \<Longrightarrow> c \<in> F b\<^sub>0"
        using C_def DiffD1 witnesses LEMMA_3_3_1 that by metis
      then 
      show ?thesis
        using C_def that(2) by blast
    next
      case 2
      then
      show ?thesis
        using C_def witnesses by auto
    qed
  qed

  have B_union_C: "A = B \<union> C"
    using B_def C_def witnesses one_closed by auto

  moreover

  have B_inter_C: "{1\<^sup>A} = B \<inter> C"
    using B_def C_def witnesses by force

  moreover

  have B_not_trivial: "\<exists> y \<in> B. y \<noteq> 1\<^sup>A"
  proof -
    have "c\<^sub>0 \<in> B \<and> c\<^sub>0 \<noteq> 1\<^sup>A"
      using B_def witnesses by auto
    then
    show ?thesis
      by auto
  qed

  moreover

  have C_not_trivial: "\<exists> y \<in> C. y \<noteq> 1\<^sup>A"
  proof -
    have "b\<^sub>0 \<in> C \<and> b\<^sub>0 \<noteq> 1\<^sup>A"
      using C_def witnesses by auto
    then
    show ?thesis
      by auto
  qed

  moreover

  have B_mult_closed: "a *\<^sup>A b \<in> B" if "a \<in> B" "b \<in> B" for a b
  proof -
    from that
    consider (1) "a \<in> F b\<^sub>0"
      | (2) "a = 1\<^sup>A"
      using B_def by blast
    then
    show "a *\<^sup>A b \<in> B"
    proof(cases)
      case 1
      then
      have "a \<in> A \<and> a *\<^sup>A b \<in> A \<and> (a *\<^sup>A b) \<le>\<^sup>A a"
        using B_union_C that mult_A mult_closed by blast
      then
      have "a *\<^sup>A b \<in> F b\<^sub>0"
        using "1" witnesses LEMMA_3_3_1 by metis
      then
      show ?thesis
        using B_def by simp
    next
      case 2
      then
      show ?thesis
        using B_union_C that(2) by simp
    qed
  qed

  moreover

  have B_imp_closed: "a \<rightarrow>\<^sup>A b \<in> B" if "a \<in> B" "b \<in> B" for a b
  proof -
    from that
    consider (1) "a = 1\<^sup>A \<or> b = 1\<^sup>A \<or> (a \<in> F b\<^sub>0 \<and> b \<in> F b\<^sub>0 \<and> a \<rightarrow>\<^sup>A b = 1\<^sup>A)"
      | (2) "a \<in> F b\<^sub>0" "b \<in> F b\<^sub>0" "a \<rightarrow>\<^sup>A b \<noteq> 1\<^sup>A"
      using B_def by fastforce
    then 
    show "a \<rightarrow>\<^sup>A b \<in> B"
    proof(cases)
      case 1
      then
      have "a \<rightarrow>\<^sup>A b = b \<or> a \<rightarrow>\<^sup>A b = 1\<^sup>A"
        using B_union_C that imp_one_C imp_one_top by blast
      then
      show ?thesis
        using B_inter_C that(2) by fastforce
    next
      case 2
      then
      have "a *\<^sup>A b\<^sub>0 = a"
        using B_def B_mult_b0 witnesses by auto
      then
      have "b\<^sub>0 \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A b) = (a \<rightarrow>\<^sup>A b)"
        using B_union_C witnesses that mult_comm residuation by simp
      then
      have "a \<rightarrow>\<^sup>A b \<in> F b\<^sub>0"
        using "2"(3) B_union_C F_equiv witnesses that imp_closed by auto
      then
      show ?thesis
        using B_def by auto
    qed
  qed

  moreover

  have B_hoop: "hoop B (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  proof
    show "x *\<^sup>A y \<in> B" if "x \<in> B" "y \<in> B" for x y
      using B_mult_closed that by simp
  next
    show "x \<rightarrow>\<^sup>A y \<in> B" if "x \<in> B" "y \<in> B" for x y
      using B_imp_closed that by simp
  next
    show "1\<^sup>A \<in> B"
      using B_def by simp
  next
    show "x *\<^sup>A y = y *\<^sup>A x" if "x \<in> B" "y \<in> B" for x y
      using B_union_C mult_comm that by simp
  next
    show "x *\<^sup>A (y *\<^sup>A z) = (x *\<^sup>A y) *\<^sup>A z" if "x \<in> B" "y \<in> B" "z \<in> B" for x y z
      using B_union_C mult_assoc that by simp
  next 
    show "x *\<^sup>A 1\<^sup>A = x" if "x \<in> B" for x
      using B_union_C that by simp
  next
    show "x \<rightarrow>\<^sup>A x = 1\<^sup>A" if "x \<in> B" for x
      using B_union_C that by simp
  next 
    show "x *\<^sup>A (x \<rightarrow>\<^sup>A y) = y *\<^sup>A (y \<rightarrow>\<^sup>A x)" if "x \<in> B" "y \<in> B" for x y
      using B_union_C divisibility that by simp
  next 
    show "x \<rightarrow>\<^sup>A (y \<rightarrow>\<^sup>A z) = (x *\<^sup>A y) \<rightarrow>\<^sup>A z" if "x \<in> B" "y \<in> B" "z \<in> B" for x y z
      using B_union_C residuation that by simp
  qed

  moreover

  have C_imp_B: "c \<rightarrow>\<^sup>A b = b" if "b \<in> B" "c \<in> C" for b c
  proof -
    from that
    consider (1) "b \<in> F b\<^sub>0" "c \<noteq> 1\<^sup>A"
      | (2) "b = 1\<^sup>A \<or> c = 1\<^sup>A"
      using B_def by blast
    then
    show "c \<rightarrow>\<^sup>A b = b"
    proof(cases)
      case 1
      have "b\<^sub>0 \<rightarrow>\<^sup>A ((c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b) = (c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (b\<^sub>0 \<rightarrow>\<^sup>A b)"
        using B_union_C witnesses that imp_closed swap by simp
      also
      have "\<dots> = (c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b"
        using "1"(1) witnesses by auto
      finally
      have "(c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b \<in> F b\<^sub>0" if "(c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b \<noteq> 1\<^sup>A"
        using B_union_C F_equiv witnesses \<open>b \<in> B\<close> \<open>c \<in> C\<close> that imp_closed by auto
      moreover
      have "c \<le>\<^sup>A ((c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b)"
        using B_union_C that ord_C by simp
      ultimately 
      have "(c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b = 1\<^sup>A"
        using B_def B_union_C C_def C_upper_set that(2) by blast
      moreover
      have "b \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A b) = 1\<^sup>A"
        using B_union_C that imp_A by simp
      ultimately
      show ?thesis
        using B_union_C that imp_closed ord_antisymm_equiv by blast
    next
      case 2
      then
      show ?thesis
        using B_union_C that imp_one_C imp_one_top by auto
    qed
  qed

  moreover

  have B_imp_C: "b \<rightarrow>\<^sup>A c = 1\<^sup>A" if "b \<in> B-{1\<^sup>A}" "c \<in> C" for b c
  proof -
    from that
    have "b \<le>\<^sup>A c \<or> c \<le>\<^sup>A b"
      using total_order B_union_C by blast
    moreover
    have "c \<rightarrow>\<^sup>A b = b"
      using C_imp_B that by simp
    ultimately
    show "b \<rightarrow>\<^sup>A c = 1\<^sup>A"
      using that(1) hoop_order_def by force
  qed

  moreover

  have B_mult_C: "b *\<^sup>A c = b" if "b \<in> B-{1\<^sup>A}" "c \<in> C" for b c
  proof -
    have "b = b *\<^sup>A 1\<^sup>A"
      using that(1) B_union_C by fastforce
    also
    have "\<dots> = b *\<^sup>A (b \<rightarrow>\<^sup>A c)"
      using B_imp_C that by blast
    also
    have "\<dots> = c *\<^sup>A (c \<rightarrow>\<^sup>A b)"
      using that divisibility B_union_C by simp
    also
    have "\<dots> = c *\<^sup>A b"
      using C_imp_B that by auto
    finally
    show "b *\<^sup>A c = b"
      using that mult_comm B_union_C by auto
  qed

  moreover

  have C_mult_closed: "c *\<^sup>A d \<in> C" if "c \<in> C" "d \<in> C" for c d
  proof -
    consider (1) "c \<noteq> 1\<^sup>A" "d \<noteq> 1\<^sup>A"
      | (2) "c = 1\<^sup>A \<or> d = 1\<^sup>A"
      by auto
    then
    show "c *\<^sup>A d \<in> C"
    proof(cases)
      case 1
      have "c *\<^sup>A d \<in> F b\<^sub>0" if "c *\<^sup>A d \<notin> C"
        using C_def \<open>c \<in> C\<close> \<open>d \<in> C\<close> mult_closed that by force
      then
      have "c \<rightarrow>\<^sup>A (c *\<^sup>A d) \<in> F b\<^sub>0" if "c *\<^sup>A d \<notin> C"
        using B_def C_imp_B \<open>c \<in> C\<close> that by simp
      moreover
      have "d \<le>\<^sup>A (c \<rightarrow>\<^sup>A (c *\<^sup>A d))"
        using C_def DiffD1 that ord_reflex ord_residuation residuation
              mult_closed mult_comm
        by metis
      moreover
      have "c \<rightarrow>\<^sup>A (c *\<^sup>A d) \<in> A \<and> d \<in> A"
        using C_def Diff_iff that imp_closed mult_closed by metis
      ultimately
      have "d \<in> F b\<^sub>0" if "c *\<^sup>A d \<notin> C"
        using witnesses LEMMA_3_3_1 that by blast
      then
      show ?thesis
        using C_def that(2) by blast
    next
      case 2
      then
      show ?thesis
        using B_union_C that mult_neutr mult_neutr_2 by auto
    qed
  qed

  moreover

  have C_imp_closed: "c \<rightarrow>\<^sup>A d \<in> C" if "c \<in> C" "d \<in> C" for c d
    using C_upper_set imp_closed ord_A B_union_C that by blast

  moreover

  have C_hoop: "hoop C (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  proof
    show "x *\<^sup>A y \<in> C" if "x \<in> C" "y \<in> C" for x y
      using C_mult_closed that by simp
  next
    show "x \<rightarrow>\<^sup>A y \<in> C" if "x \<in> C" "y \<in> C" for x y
      using C_imp_closed that by simp
  next
    show "1\<^sup>A \<in> C"
      using B_inter_C by auto
  next
    show "x *\<^sup>A y = y *\<^sup>A x" if "x \<in> C" "y \<in> C" for x y
      using B_union_C mult_comm that by simp
  next
    show "x *\<^sup>A (y *\<^sup>A z) = (x *\<^sup>A y) *\<^sup>A z" if "x \<in> C" "y \<in> C" "z \<in> C" for x y z
      using B_union_C mult_assoc that by simp
  next 
    show "x *\<^sup>A 1\<^sup>A = x" if "x \<in> C" for x
      using B_union_C that by simp
  next
    show "x \<rightarrow>\<^sup>A x = 1\<^sup>A" if "x \<in> C" for x
      using B_union_C that by simp
  next 
    show "x *\<^sup>A (x \<rightarrow>\<^sup>A y) = y *\<^sup>A (y \<rightarrow>\<^sup>A x)" if "x \<in> C" "y \<in> C" for x y
      using B_union_C divisibility that by simp
  next 
    show "x \<rightarrow>\<^sup>A (y \<rightarrow>\<^sup>A z) = (x *\<^sup>A y) \<rightarrow>\<^sup>A z" if "x \<in> C" "y \<in> C" "z \<in> C" for x y z
      using B_union_C residuation that by simp
  qed

  ultimately

  have "\<exists> B C. 
    (A = B \<union> C) \<and>
    ({1\<^sup>A} = B \<inter> C) \<and>
    (\<exists> y \<in> B. y \<noteq> 1\<^sup>A) \<and>
    (\<exists> y \<in> C. y \<noteq> 1\<^sup>A) \<and>
    (hoop B (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A) \<and>
    (hoop C (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A) \<and>
    (\<forall> x \<in> B-{1\<^sup>A}. \<forall> y \<in> C. x *\<^sup>A y = x) \<and>
    (\<forall> x \<in> B-{1\<^sup>A}. \<forall> y \<in> C. x \<rightarrow>\<^sup>A y = 1\<^sup>A) \<and>
    (\<forall> x \<in> C. \<forall> y \<in> B. x \<rightarrow>\<^sup>A y = y)"
    by (smt (verit)) 
  then
  show ?thesis
    using totally_ordered_irreducible_hoop.irreducible by (smt (verit))
qed

text\<open>Next result can be found in \<^cite>\<open>"BLOK2000"\<close> (see Proposition 2.2).\<close>

lemma one_fixed_implies_wajsberg:
  assumes "totally_ordered_one_fixed_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  shows "totally_ordered_wajsberg_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
proof 
  have "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b = (b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a" if "a \<in> A" "b \<in> A" "a <\<^sup>A b" for a b
  proof -
    from that
    have "(((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a) = b \<rightarrow>\<^sup>A a \<and> b \<rightarrow>\<^sup>A a \<noteq> 1\<^sup>A"
      using imp_D ord_D by simp
    then
    have "((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b = 1\<^sup>A"
      using assms that(1,2) imp_closed totally_ordered_one_fixed_hoop.one_fixed
      by metis
    moreover
    have "b \<rightarrow>\<^sup>A ((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) = 1\<^sup>A"
      using hoop_order_def that(1,2) ord_C by simp
    ultimately
    have "(b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a = b"
      using imp_closed ord_antisymm_equiv hoop_axioms that(1,2) by metis
    also
    have "\<dots> = (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b"
      using hoop_order_def hoop_order_strict_def that(2,3) imp_one_C by force
    finally
    show "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b = (b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a"
      by auto
  qed
  then
  show "(x \<rightarrow>\<^sup>A y) \<rightarrow>\<^sup>A y = (y \<rightarrow>\<^sup>A x) \<rightarrow>\<^sup>A x" if "x \<in> A" "y \<in> A" for x y 
    using total_order hoop_order_strict_def that by metis
qed

text\<open>The proof of the following result can be found in \<^cite>\<open>"AGLIANO2003"\<close> (see Theorem 3.6).\<close>

lemma not_irreducible_implies_not_wajsberg:
  assumes "\<not>totally_ordered_irreducible_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  shows "\<not>totally_ordered_wajsberg_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
proof -
  have "\<exists> B C. 
    (A = B \<union> C) \<and>
    ({1\<^sup>A} = B \<inter> C) \<and>
    (\<exists> y \<in> B. y \<noteq> 1\<^sup>A) \<and>
    (\<exists> y \<in> C. y \<noteq> 1\<^sup>A) \<and>
    (hoop B (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A) \<and>
    (hoop C (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A) \<and>
    (\<forall> x \<in> B-{1\<^sup>A}. \<forall> y \<in> C. x *\<^sup>A y = x) \<and>
    (\<forall> x \<in> B-{1\<^sup>A}. \<forall> y \<in> C. x \<rightarrow>\<^sup>A y = 1\<^sup>A) \<and>
    (\<forall> x \<in> C. \<forall> y \<in> B. x \<rightarrow>\<^sup>A y = y)"
    using irr_test[OF totally_ordered_hoop_axioms] assms by auto
  then  
  obtain B C where H:
    "(A = B \<union> C) \<and>
    ({1\<^sup>A} = B \<inter> C) \<and>
    (\<exists> y \<in> B. y \<noteq> 1\<^sup>A) \<and>
    (\<exists> y \<in> C. y \<noteq> 1\<^sup>A) \<and>
    (\<forall> x \<in> B-{1\<^sup>A}. \<forall> y \<in> C. x \<rightarrow>\<^sup>A y = 1\<^sup>A) \<and>
    (\<forall> x \<in> C. \<forall> y \<in> B. x \<rightarrow>\<^sup>A y = y)"
    by blast
  then
  obtain b c where assms: "b \<in> B-{1\<^sup>A} \<and> c \<in> C-{1\<^sup>A}"
    by auto
  then
  have "b \<rightarrow>\<^sup>A c = 1\<^sup>A"
    using H by simp
  then
  have "(b \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A c = c"
    using H assms imp_one_C by blast
  moreover
  have "(c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b = 1\<^sup>A"
    using assms H by force
  ultimately
  have "(b \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A c \<noteq> (c \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b"
    using assms by force
  moreover
  have "b \<in> A \<and> c \<in> A"
    using assms H by blast
  ultimately
  show ?thesis
    using totally_ordered_wajsberg_hoop.axioms(2) wajsberg_hoop.T by meson
qed

text\<open>Summary of all results in this subsection:\<close>

theorem one_fixed_equivalent_to_wajsberg: 
  shows "totally_ordered_one_fixed_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A \<equiv> 
         totally_ordered_wajsberg_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  using not_irreducible_implies_not_wajsberg not_one_fixed_implies_not_irreducible
        one_fixed_implies_wajsberg
  by linarith

theorem wajsberg_equivalent_to_irreducible:
  shows "totally_ordered_wajsberg_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A \<equiv>
         totally_ordered_irreducible_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  using not_irreducible_implies_not_wajsberg not_one_fixed_implies_not_irreducible
        one_fixed_implies_wajsberg
  by linarith

theorem irreducible_equivalent_to_one_fixed:
  shows "totally_ordered_irreducible_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A \<equiv>
         totally_ordered_one_fixed_hoop A (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  using one_fixed_equivalent_to_wajsberg wajsberg_equivalent_to_irreducible
  by simp

end

subsection\<open>Decomposition\<close>
                               
locale tower_of_irr_hoops = tower_of_hoops +
  assumes family_of_irr_hoops: "i \<in> I \<Longrightarrow>
                         totally_ordered_irreducible_hoop (\<bbbA>\<^sub>i) (*\<^sup>i) (\<rightarrow>\<^sup>i) 1\<^sup>S"

locale tower_of_nontrivial_irr_hoops = tower_of_irr_hoops + 
  assumes nontrivial: "i \<in> I \<Longrightarrow> \<exists> x \<in> \<bbbA>\<^sub>i. x \<noteq> 1\<^sup>S"

context totally_ordered_hoop
begin

subsubsection\<open>Definition of index set @{text "I"}\<close>

definition index_set :: "('a set) set" ("I")
  where "I = {y. (\<exists> x \<in> A. \<pi> x = y)}"

lemma indexes_subsets: 
  assumes "i \<in> I"
  shows "i \<subseteq> A"
  using index_set_def assms rel_F_canonical_map_def by auto

lemma indexes_not_empty:
  assumes "i \<in> I"
  shows "i \<noteq> \<emptyset>"
  using index_set_def assms classes_not_empty by blast

lemma indexes_disjoint:
  assumes "i \<in> I" "j \<in> I" "i \<noteq> j"
  shows "i \<inter> j = \<emptyset>"
proof -
  obtain a b where "a \<in> A \<and> b \<in> A \<and> a \<noteq> b \<and> i = \<pi> a \<and> j = \<pi> b"
    using index_set_def assms by auto
  then
  show ?thesis
    using assms(3) classes_disjoint by auto
qed

lemma indexes_cover: "A = {x. \<exists> i \<in> I. x \<in> i}"
  using classes_subsets classes_not_empty index_set_def by auto

lemma indexes_class_of_elements: 
  assumes "i \<in> I" "a \<in> A" "a \<in> i"
  shows "\<pi> a = i"
proof -
  obtain c where class_element:  "c \<in> A \<and> i = \<pi> c"
    using assms(1) index_set_def by auto
  then
  have "a \<sim>F c"
    using assms(3) rel_F_canonical_map_def rel_F_symm by auto
  then
  show ?thesis
    using assms(2) class_element related_iff_same_class by simp
qed

lemma indexes_convex:
  assumes "i \<in> I" "a \<in> i" "b \<in> i" "d \<in> A" "a \<le>\<^sup>A d" "d \<le>\<^sup>A b"
  shows "d \<in> i"
proof -
  have "a \<in> A \<and> b \<in> A \<and> d \<in> A \<and> i = \<pi> a"
    using assms(1-4) indexes_class_of_elements indexes_subsets by blast
  then
  show ?thesis
    using assms(2-6) classes_convex by auto
qed

subsubsection\<open>Definition of total partial order over @{term I}\<close>

text\<open>Since each equivalence class is convex, @{term hoop_order} induces a total order on @{term I}.\<close>

function index_order :: "('a set) \<Rightarrow> ('a set) \<Rightarrow> bool" (infix "\<le>\<^sup>I" 60) where
  "x \<le>\<^sup>I y = ((x = y) \<or> (\<forall> v \<in> x. \<forall> w \<in> y. v \<le>\<^sup>A w))" if "x \<in> I" "y \<in> I"
| "x \<le>\<^sup>I y = undefined" if "x \<notin> I \<or> y \<notin> I"
  by auto
termination by lexicographic_order

definition index_order_strict (infix "<\<^sup>I" 60)
  where "x <\<^sup>I y = (x \<le>\<^sup>I y \<and> x \<noteq> y)"

lemma index_ord_reflex: 
  assumes "i \<in> I"
  shows "i \<le>\<^sup>I i"
  using assms by simp

lemma index_ord_antisymm:
  assumes "i \<in> I" "j \<in> I" "i \<le>\<^sup>I j" "j \<le>\<^sup>I i"
  shows "i = j"
proof -
  have "i = j \<or> (\<forall> a \<in> i. \<forall> b \<in> j. a \<le>\<^sup>A b \<and> b \<le>\<^sup>A a)"
    using assms by auto
  then
  have "i = j \<or> (\<forall> a \<in> i. \<forall> b \<in> j. a = b)"
    using assms(1,2) indexes_subsets insert_Diff insert_subset ord_antisymm
    by metis
  then
  show ?thesis
    using assms(1,2) indexes_not_empty by force
qed

lemma index_ord_trans:
  assumes "i \<in> I" "j \<in> I" "k \<in> I" "i \<le>\<^sup>I j" "j \<le>\<^sup>I k" 
  shows "i \<le>\<^sup>I k"
proof -
  consider (1) "i \<noteq> j" "j \<noteq> k"
    | (2) "i = j \<or> j = k"
    by auto
  then
  show "i \<le>\<^sup>I k"
  proof(cases)
    case 1
    then
    have "(\<forall> a \<in> i. \<forall> b \<in> j. a \<le>\<^sup>A b) \<and> (\<forall> b \<in> j. \<forall> c \<in> k. b \<le>\<^sup>A c)"
      using assms by force
    moreover
    have "j \<noteq> \<emptyset>"
      using assms(2) indexes_not_empty by simp
    ultimately
    have "\<forall> a \<in> i. \<forall> c \<in> k. \<exists> b \<in> j. a \<le>\<^sup>A b \<and> b \<le>\<^sup>A c"
      using all_not_in_conv by meson
    then
    have "\<forall> a \<in> i. \<forall> c \<in> k. a \<le>\<^sup>A c"
      using assms indexes_subsets ord_trans subsetD by metis
    then
    show ?thesis
      using assms(1,3) by simp
  next
    case 2
    then
    show ?thesis
      using assms(4,5) by auto
  qed
qed

lemma index_order_total :
  assumes "i \<in> I" "j \<in> I" "\<not>(j \<le>\<^sup>I i)"
  shows "i \<le>\<^sup>I j"
proof -
  have "i \<noteq> j"
    using assms(1,3) by auto
  then
  have disjoint: "i \<inter> j = \<emptyset>"
    using assms(1,2) indexes_disjoint by simp
  moreover
  have "\<exists> x \<in> j. \<exists> y \<in> i. \<not>(x \<le>\<^sup>A y)"
    using assms index_order.simps(1) by blast
  moreover
  have subsets: "i \<subseteq> A \<and> j \<subseteq> A"
    using assms indexes_subsets by simp
  ultimately
  have "\<exists> x \<in> j. \<exists> y \<in> i. y <\<^sup>A x"
    using total_order hoop_order_strict_def insert_absorb insert_subset by metis
  then
  obtain a\<^sub>i a\<^sub>j where witnesses: "a\<^sub>i \<in> i \<and> a\<^sub>j \<in> j \<and> a\<^sub>i <\<^sup>A a\<^sub>j"
    using assms(1,2) total_order hoop_order_strict_def indexes_subsets by metis
  then
  have "a \<le>\<^sup>A b" if "a \<in> i" "b \<in> j" for a b
  proof 
    from that
    consider (1) "a\<^sub>i \<le>\<^sup>A a" "a\<^sub>j \<le>\<^sup>A b"
      | (2) "a <\<^sup>A a\<^sub>i" "b <\<^sup>A a\<^sub>j"
      | (3) "a\<^sub>i \<le>\<^sup>A a" "b <\<^sup>A a\<^sub>j"
      | (4) "a <\<^sup>A a\<^sub>i" "a\<^sub>j \<le>\<^sup>A b" 
      using total_order hoop_order_strict_def subset_eq subsets witnesses by metis
    then
    show "a \<le>\<^sup>A b"
    proof(cases)
      case 1 
      then
      have "a\<^sub>i \<le>\<^sup>A a\<^sub>j \<and> a\<^sub>j \<le>\<^sup>A b \<and> b \<le>\<^sup>A a" if "b <\<^sup>A a"
        using hoop_order_strict_def that witnesses by blast
      then
      have "a\<^sub>i \<le>\<^sup>A b \<and> b \<le>\<^sup>A a" if "b <\<^sup>A a"
        using \<open>b \<in> j\<close> in_mono ord_trans subsets that witnesses by meson
      then
      have "b \<in> i" if "b <\<^sup>A a"
        using assms(1) \<open>a \<in> i\<close> \<open>b \<in> j\<close> indexes_convex subsets that witnesses
        by blast
      then
      show "a \<le>\<^sup>A b"
        using disjoint disjoint_iff_not_equal hoop_order_strict_def subset_eq
              subsets that total_order
        by metis
    next
      case 2
      then
      have "b \<le>\<^sup>A a \<and> a \<le>\<^sup>A a\<^sub>i \<and> a\<^sub>i \<le>\<^sup>A a\<^sub>j" if "b <\<^sup>A a"
        using hoop_order_strict_def that witnesses by blast
      then
      have "b \<le>\<^sup>A a \<and> a \<le>\<^sup>A a\<^sub>j" if "b <\<^sup>A a"
        using \<open>a \<in> i\<close> ord_trans subset_eq subsets that witnesses by metis
      then
      have "a \<in> j" if "b <\<^sup>A a"
        using assms(2) \<open>a \<in> i\<close> \<open>b \<in> j\<close> indexes_convex subsets that witnesses
        by blast
      then
      show "a \<le>\<^sup>A b"
        using disjoint disjoint_iff_not_equal hoop_order_strict_def subset_eq
              subsets that total_order
        by metis
    next
      case 3 
      have "b \<le>\<^sup>A a\<^sub>i \<and> a\<^sub>i \<le>\<^sup>A a\<^sub>j" if "b \<le>\<^sup>A a\<^sub>i"
        using hoop_order_strict_def that witnesses by auto
      then
      have "a\<^sub>i \<in> j" if "b \<le>\<^sup>A a\<^sub>i"
        using assms(2) \<open>b \<in> j\<close> indexes_convex subsets that witnesses by blast
      moreover 
      have "a\<^sub>i \<notin> j"
        using disjoint witnesses by blast
      ultimately
      have "a\<^sub>i <\<^sup>A b"
        using total_order hoop_order_strict_def \<open>b \<in> j\<close> subsets witnesses by blast
      then
      have "a\<^sub>i \<le>\<^sup>A b \<and> b \<le>\<^sup>A a" if "b <\<^sup>A a"
        using hoop_order_strict_def that by auto
      then
      have "b \<in> i" if "b <\<^sup>A a"
        using assms(1) \<open>a \<in> i\<close> \<open>b \<in> j\<close> indexes_convex subsets that witnesses
        by blast
      then
      show "a \<le>\<^sup>A b"
        using disjoint disjoint_iff_not_equal hoop_order_strict_def subset_eq
              subsets that total_order
        by metis
    next
      case 4
      then
      show "a \<le>\<^sup>A b"
        using hoop_order_strict_def in_mono ord_trans subsets that witnesses
        by meson
    qed
  qed
  then
  show "i \<le>\<^sup>I j"
    using assms by simp
qed

sublocale total_poset_on "I" "(\<le>\<^sup>I)" "(<\<^sup>I)"
proof
  show "I \<noteq> \<emptyset>"
    using indexes_cover by auto
next 
  show "reflp_on I (\<le>\<^sup>I)"
    using index_ord_reflex reflp_onI by blast
next
  show "antisymp_on I (\<le>\<^sup>I)"
    using antisymp_on_def index_ord_antisymm by blast
next
  show "transp_on I (\<le>\<^sup>I)"
    using index_ord_trans transp_on_def by blast
next
  show "x <\<^sup>I y = (x \<le>\<^sup>I y \<and> x \<noteq> y)" if "x \<in> I" "y \<in> I" for x y
    using index_order_strict_def by auto
next 
  show "totalp_on I (\<le>\<^sup>I)"
    using index_order_total totalp_onI by metis
qed

subsubsection\<open>Definition of universes\<close>

definition universes :: "'a set \<Rightarrow> 'a set" ("UNI\<^sub>A")
  where "UNI\<^sub>A x = x \<union> {1\<^sup>A}"

abbreviation (uniA_i)
  uniA_i :: "['a set] \<Rightarrow> ('a set)" ("(\<bbbA>(\<^sub>_))" [61] 60)
  where "\<bbbA>\<^sub>i \<equiv> UNI\<^sub>A i"

abbreviation (uniA_pi)
  uniA_pi :: "['a] \<Rightarrow> ('a set)" ("(\<bbbA>\<^sub>\<pi> (\<^sub>_))" [61] 60)
  where "\<bbbA>\<^sub>\<pi>\<^sub>x \<equiv> UNI\<^sub>A (\<pi> x)"

abbreviation (uniA_pi_one)
  uniA_pi_one :: "'a set" ("(\<bbbA>\<^sub>\<pi>\<^sub>1\<^sub>A)" 60)
  where "\<bbbA>\<^sub>\<pi>\<^sub>1\<^sub>A \<equiv> UNI\<^sub>A (\<pi> 1\<^sup>A)"

lemma universes_subsets: 
  assumes "i \<in> I" "a \<in> \<bbbA>\<^sub>i"
  shows "a \<in> A"
  using assms universes_def indexes_subsets one_closed by fastforce

lemma universes_not_empty:
  assumes "i \<in> I"
  shows "\<bbbA>\<^sub>i \<noteq> \<emptyset>"
  using universes_def by simp

lemma universes_almost_disjoint:
  assumes "i \<in> I" "j \<in> I" "i \<noteq> j" 
  shows "(\<bbbA>\<^sub>i) \<inter> (\<bbbA>\<^sub>j) = {1\<^sup>A}"
  using assms indexes_disjoint universes_def by auto

lemma universes_cover: "A = {x. \<exists> i \<in> I. x \<in> \<bbbA>\<^sub>i}"
  using one_closed indexes_cover universes_def by auto

lemma universes_aux: 
  assumes "i \<in> I" "a \<in> i"
  shows "\<bbbA>\<^sub>i = \<pi> a \<union> {1\<^sup>A}"
  using assms universes_def universes_subsets indexes_class_of_elements by force

subsubsection\<open>Universes are subhoops of @{text "A"}\<close>

lemma universes_one_closed:
  assumes "i \<in> I"
  shows "1\<^sup>A \<in> \<bbbA>\<^sub>i"
  using universes_def by auto

lemma universes_mult_closed:
  assumes "i \<in> I" "a \<in> \<bbbA>\<^sub>i" "b \<in> \<bbbA>\<^sub>i"
  shows "a *\<^sup>A b \<in> \<bbbA>\<^sub>i"
proof -
  consider (1) "a \<noteq> 1\<^sup>A" "b \<noteq> 1\<^sup>A"
    | (2) "a = 1\<^sup>A \<or> b = 1\<^sup>A"
    by auto
  then
  show ?thesis
  proof(cases)
    case 1
    then
    have UNI_def: "\<bbbA>\<^sub>i = \<pi> a \<union> {1\<^sup>A} \<and> \<bbbA>\<^sub>i = \<pi> b \<union> {1\<^sup>A}"
      using assms universes_def universes_subsets indexes_class_of_elements
      by simp
    then
    have "\<pi> a = \<pi> b"
      using "1" assms universes_def universes_subsets indexes_class_of_elements
      by force
    then
    have "F a = F b"
      using assms universes_subsets rel_F_equiv related_iff_same_class by meson
    then
    have "F (a *\<^sup>A b) = F a"
      using "1" LEMMA_3_3_2 assms universes_subsets by blast
    then
    have "\<pi> a = \<pi> (a *\<^sup>A b)"
      using assms universes_subsets mult_closed rel_F_equiv related_iff_same_class
      by metis
    then
    show ?thesis
      using UNI_def UnI1 assms classes_not_empty universes_subsets mult_closed
      by metis
  next
    case 2
    then
    show ?thesis
      using assms universes_subsets by auto
  qed
qed

lemma universes_imp_closed:
  assumes "i \<in> I" "a \<in> \<bbbA>\<^sub>i" "b \<in> \<bbbA>\<^sub>i"
  shows "a \<rightarrow>\<^sup>A b \<in> \<bbbA>\<^sub>i"
proof -
  from assms
  consider (1) "a \<noteq> 1\<^sup>A" "b \<noteq> 1\<^sup>A" "b <\<^sup>A a"
    | (2) "a = 1\<^sup>A \<or> b = 1\<^sup>A \<or> (a \<noteq> 1\<^sup>A \<and> b \<noteq> 1\<^sup>A \<and> a \<le>\<^sup>A b)"
    using total_order universes_subsets hoop_order_strict_def by auto
  then
  show ?thesis
  proof(cases)
    case 1
    then
    have UNI_def: "\<bbbA>\<^sub>i = \<pi> a \<union> {1\<^sup>A} \<and> \<bbbA>\<^sub>i = \<pi> b \<union> {1\<^sup>A}"
      using assms universes_def universes_subsets indexes_class_of_elements
      by simp
    then
    have "\<pi> a = \<pi> b"
      using "1" assms universes_def universes_subsets indexes_class_of_elements
      by force
    then
    have "F a = F b"
      using assms universes_subsets rel_F_equiv related_iff_same_class by simp
    then
    have "F (a \<rightarrow>\<^sup>A b) = F a"
      using "1" LEMMA_3_3_6 assms universes_subsets by simp
    then
    have "\<pi> a = \<pi> (a \<rightarrow>\<^sup>A b)"
      using assms universes_subsets imp_closed same_F_iff_same_class by simp
    then
    show ?thesis
      using UNI_def UnI1 assms classes_not_empty universes_subsets imp_closed
      by metis
  next
    case 2
    then
    show ?thesis
      using assms universes_subsets universes_one_closed hoop_order_def imp_one_A
            imp_one_C
      by auto
  qed
qed

subsubsection\<open>Universes are irreducible hoops\<close>

lemma universes_one_fixed:
  assumes "i \<in> I" "a \<in> \<bbbA>\<^sub>i" "b \<in> \<bbbA>\<^sub>i" "a \<rightarrow>\<^sup>A b = b" 
  shows "a = 1\<^sup>A \<or> b = 1\<^sup>A"
proof -
  from assms
  have "\<pi> a = \<pi> b" if "a \<noteq> 1\<^sup>A" "b \<noteq> 1\<^sup>A"
    using universes_def universes_subsets indexes_class_of_elements that by force
  then
  have "F a = F b" if "a \<noteq> 1\<^sup>A" "b \<noteq> 1\<^sup>A"
    using assms(1-3) universes_subsets same_F_iff_same_class that by blast
  then
  have "b = 1\<^sup>A" if "a \<noteq> 1\<^sup>A" "b \<noteq> 1\<^sup>A"
    using F_equiv assms universes_subsets fixed_points.cases imp_reflex that by metis
  then 
  show ?thesis
    by blast
qed

corollary universes_one_fixed_hoops:
  assumes "i \<in> I"
  shows "totally_ordered_one_fixed_hoop (\<bbbA>\<^sub>i) (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
proof
  show "x *\<^sup>A y \<in> \<bbbA>\<^sub>i" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for x y
    using assms universes_mult_closed that by simp
next
  show "x \<rightarrow>\<^sup>A y \<in> \<bbbA>\<^sub>i" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for x y
    using assms universes_imp_closed that by simp
next
  show "1\<^sup>A \<in> \<bbbA>\<^sub>i"
    using assms universes_one_closed by simp
next
  show "x *\<^sup>A y = y *\<^sup>A x" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for x y
    using assms universes_subsets mult_comm that by simp
next
  show "x *\<^sup>A (y *\<^sup>A z) = (x *\<^sup>A y) *\<^sup>A z" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for x y z
    using assms universes_subsets mult_assoc that by simp
next 
  show "x *\<^sup>A 1\<^sup>A = x" if "x \<in> \<bbbA>\<^sub>i" for x
    using assms universes_subsets that by simp
next 
  show "x \<rightarrow>\<^sup>A x = 1\<^sup>A" if "x \<in> \<bbbA>\<^sub>i" for x
    using assms universes_subsets that by simp
next 
  show "x *\<^sup>A (x \<rightarrow>\<^sup>A y) = y *\<^sup>A (y \<rightarrow>\<^sup>A x)" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for x y
    using assms divisibility universes_subsets that by simp
next 
  show "x \<rightarrow>\<^sup>A (y \<rightarrow>\<^sup>A z) = (x *\<^sup>A y) \<rightarrow>\<^sup>A z" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for x y z
    using assms universes_subsets residuation that by simp
next 
  show "x \<le>\<^sup>A y \<or> y \<le>\<^sup>A x" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for x y
    using assms total_order universes_subsets that by simp
next 
  show "x = 1\<^sup>A \<or> y = 1\<^sup>A" if "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "y \<rightarrow>\<^sup>A x = x" for x y
    using assms universes_one_fixed that by blast
qed

corollary universes_irreducible_hoops:
  assumes "i \<in> I"
  shows "totally_ordered_irreducible_hoop (\<bbbA>\<^sub>i) (*\<^sup>A) (\<rightarrow>\<^sup>A) 1\<^sup>A"
  using assms universes_one_fixed_hoops totally_ordered_hoop.irreducible_equivalent_to_one_fixed
        totally_ordered_one_fixed_hoop.axioms(1)
  by metis

subsubsection\<open>Some useful results\<close>

lemma index_aux:
  assumes "i \<in> I" "j \<in> I" "i <\<^sup>I j" "a \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A}" "b \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}"
  shows "a <\<^sup>A b \<and> \<not>(a \<sim>F b)"
proof -
  have noteq: "i \<noteq> j \<and> x \<le>\<^sup>A y" if "x \<in> i" "y \<in> j" for x y
    using assms that index_order_strict_def by fastforce
  moreover 
  have ij_def: "i = \<pi> a \<and> j = \<pi> b"
    using UnE assms universes_def universes_subsets indexes_class_of_elements
    by auto
  ultimately
  have "a <\<^sup>A b"
    using assms(1,2,4,5) classes_not_empty universes_subsets hoop_order_strict_def
    by blast
  moreover
  have "i = j" if "a \<sim>F b"
    using assms(1,2,4,5) that universes_subsets ij_def related_iff_same_class by auto
  ultimately
  show ?thesis
    using assms(2,3) trichotomy by blast
qed

lemma different_indexes_mult: 
  assumes "i \<in> I" "j \<in> I" "i <\<^sup>I j" "a \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A}" "b \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}"
  shows "a *\<^sup>A b = a"
proof -
  have "a <\<^sup>A b \<and> \<not>(a \<sim>F b)"
    using assms index_aux by blast
  then
  have "a <\<^sup>A b \<and> F a \<noteq> F b"
    using DiffD1 assms(1,2,4,5) universes_subsets rel_F_equiv by meson
  then
  have "a <\<^sup>A b \<and> a *\<^sup>A b = a \<and>\<^sup>A b"
    using DiffD1 LEMMA_3_3_5 assms(1,2,4,5) universes_subsets by auto
  then
  show ?thesis
    using assms(1,2,4,5) universes_subsets hoop_order_strict_def inf_order by auto
qed

lemma different_indexes_imp_1:
  assumes "i \<in> I" "j \<in> I" "i <\<^sup>I j" "a \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A}" "b \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}"
  shows "a \<rightarrow>\<^sup>A b = 1\<^sup>A"
proof -
  have "x \<le>\<^sup>A y" if "x \<in> i" "y \<in> j" for x y
    using assms(1-3) index_order_strict_def that by fastforce
  moreover
  have "a \<in> i \<and> b \<in> j"
    using assms(4,5) assms(5) universes_def by auto
  ultimately
  show ?thesis
    using hoop_order_def by auto
qed

lemma different_indexes_imp_2 :
  assumes "i \<in> I" "j \<in> I" "i <\<^sup>I j" "a \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}" "b \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A}"
  shows "a \<rightarrow>\<^sup>A b = b"
proof -
  have "b <\<^sup>A a \<and> \<not>(b \<sim>F a)"
    using assms index_aux by blast
  then 
  have "b <\<^sup>A a \<and> F b \<noteq> F a"
    using DiffD1 assms(1,2,4,5) universes_subsets rel_F_equiv by metis
  then
  have "b \<in> F a"
    using LEMMA_3_3_4 assms(1,2,4,5) universes_subsets by simp
  then
  show ?thesis
    using assms(2,4,5) universes_subsets by fastforce
qed

subsubsection\<open>Definition of multiplications, implications and one\<close>

definition mult_map :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)" ("MUL\<^sub>A")
  where "MUL\<^sub>A x = (*\<^sup>A)"

definition imp_map :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)" ("IMP\<^sub>A")
  where "IMP\<^sub>A x = (\<rightarrow>\<^sup>A)"

definition sum_one :: "'a" ("1\<^sup>S")
  where "1\<^sup>S = 1\<^sup>A"

abbreviation (multA_i)
  multA_i :: "['a set] \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)"  ("(*(\<^sup>_))" [50] 60)
  where "*\<^sup>i \<equiv> MUL\<^sub>A i"

abbreviation (impA_i)
  impA_i:: "['a set] \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)" ("(\<rightarrow>(\<^sup>_))" [50] 60)
  where "\<rightarrow>\<^sup>i \<equiv> IMP\<^sub>A i"

abbreviation (multA_i_xy)
  multA_i_xy :: "['a, 'a set, 'a] \<Rightarrow> 'a" ("((_)/ *(\<^sup>_) / (_))" [61, 50, 61] 60)
  where "x *\<^sup>i y \<equiv> MUL\<^sub>A i x y"

abbreviation (impA_i_xy)
  impA_i_xy :: "['a, 'a set, 'a] \<Rightarrow> 'a" ("((_)/ \<rightarrow>(\<^sup>_) / (_))" [61, 50, 61] 60)
  where "x \<rightarrow>\<^sup>i y \<equiv> IMP\<^sub>A i x y"

abbreviation (ord_i_xy)
  ord_i_xy :: "['a, 'a set, 'a] \<Rightarrow> bool" ("((_)/ \<le>(\<^sup>_) / (_))" [61, 50, 61] 60)
  where "x \<le>\<^sup>i y \<equiv> hoop.hoop_order (IMP\<^sub>A i) 1\<^sup>S x y"

subsubsection\<open>Main result\<close>

text\<open>We prove the main result: a totally ordered hoop is equal 
to an ordinal sum of a tower of irreducible hoops.\<close>

sublocale A_SUM: tower_of_irr_hoops "I" "(\<le>\<^sup>I)" "(<\<^sup>I)" "UNI\<^sub>A" "MUL\<^sub>A" "IMP\<^sub>A" "1\<^sup>S" 
proof 
  show "(\<bbbA>\<^sub>i) \<inter> (\<bbbA>\<^sub>j) = {1\<^sup>S}" if "i \<in> I" "j \<in> I" "i \<noteq> j" for i j
    using universes_almost_disjoint sum_one_def that by simp
next 
  show "x *\<^sup>i y \<in> \<bbbA>\<^sub>i" if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using universes_mult_closed mult_map_def that by simp
next
  show "x \<rightarrow>\<^sup>i y \<in> \<bbbA>\<^sub>i" if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using universes_imp_closed imp_map_def that by simp
next
  show "1\<^sup>S \<in> \<bbbA>\<^sub>i" if "i \<in> I" for i
    using universes_one_closed sum_one_def that by simp
next 
  show "x *\<^sup>i y = y *\<^sup>i x" if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using universes_subsets mult_comm mult_map_def that by simp
next
  show "x *\<^sup>i (y *\<^sup>i z) = (x *\<^sup>i y) *\<^sup>i z"
    if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for i x y z
    using universes_subsets mult_assoc mult_map_def that by simp
next
  show "x *\<^sup>i 1\<^sup>S = x" if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" for i x
    using universes_subsets sum_one_def mult_map_def that by simp
next 
  show "x \<rightarrow>\<^sup>i x = 1\<^sup>S" if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" for i x
    using universes_subsets imp_map_def sum_one_def that by simp
next
  show "x *\<^sup>i (x \<rightarrow>\<^sup>i y) = y *\<^sup>i (y \<rightarrow>\<^sup>i x)"
    if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for i x y z
    using divisibility universes_subsets imp_map_def mult_map_def that by simp
next 
  show "x \<rightarrow>\<^sup>i (y \<rightarrow>\<^sup>i z) = (x *\<^sup>i y) \<rightarrow>\<^sup>i z"
    if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for i x y z
    using universes_subsets imp_map_def mult_map_def residuation that by simp
next 
  show "x \<le>\<^sup>i y \<or> y \<le>\<^sup>i x" if "i \<in> I" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using total_order universes_subsets imp_map_def sum_one_def that by simp
next
  show "\<nexists> B C.
       (\<bbbA>\<^sub>i = B \<union> C) \<and>
       ({1\<^sup>S} = B \<inter> C) \<and>
       (\<exists> y \<in> B. y \<noteq> 1\<^sup>S) \<and>
       (\<exists> y \<in> C. y \<noteq> 1\<^sup>S) \<and> 
       (hoop B (*\<^sup>i) (\<rightarrow>\<^sup>i) 1\<^sup>S) \<and>
       (hoop C (*\<^sup>i) (\<rightarrow>\<^sup>i) 1\<^sup>S) \<and>
       (\<forall> x \<in> B-{1\<^sup>S}. \<forall> y \<in> C. x *\<^sup>i y = x) \<and>
       (\<forall> x \<in> B-{1\<^sup>S}. \<forall> y \<in> C. x \<rightarrow>\<^sup>i y = 1\<^sup>S) \<and>
       (\<forall> x \<in> C. \<forall> y \<in> B. x \<rightarrow>\<^sup>i y = y)"
    if "i \<in> I" for i
    using that Un_iff universes_one_fixed_hoops imp_map_def sum_one_def
          totally_ordered_one_fixed_hoop.one_fixed
    by metis
qed

lemma same_uni [simp]: "A_SUM.sum_univ = A"
  using A_SUM.sum_univ_def universes_cover by auto 

lemma floor_is_class:
  assumes "a \<in> A-{1\<^sup>A}"
  shows "A_SUM.floor a = \<pi> a"
proof -
  have "a \<in> \<pi> a \<and> \<pi> a \<in> I"
    using index_set_def assms classes_not_empty by fastforce
  then
  show ?thesis
    using same_uni A_SUM.floor_prop A_SUM.floor_unique UnCI assms universes_aux
          sum_one_def
    by metis
qed

lemma same_mult:
  assumes "a \<in> A" "b \<in> A"
  shows "a *\<^sup>A b = A_SUM.sum_mult a b"
proof -
  from assms
  consider (1) "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "A_SUM.floor a = A_SUM.floor b"
    | (2) "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "A_SUM.floor a <\<^sup>I A_SUM.floor b"
    | (3) "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "A_SUM.floor b <\<^sup>I A_SUM.floor a"
    | (4) "a = 1\<^sup>A \<or> b = 1\<^sup>A"
    using same_uni A_SUM.floor_prop fixed_points.cases sum_one_def trichotomy
    by metis
  then
  show ?thesis
  proof(cases)
    case 1 
    then
    show ?thesis
      using A_SUM.sum_mult.simps(1) sum_one_def mult_map_def by auto
  next
    case 2
    define i j where "i = A_SUM.floor a" and "j = A_SUM.floor b"
    then
    have "i \<in> I \<and> j \<in> I \<and> a \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A} \<and> b \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}"
      using "2"(1,2) A_SUM.floor_prop sum_one_def by auto
    then
    have "a *\<^sup>A b = a"
      using "2"(3) different_indexes_mult i_def j_def by blast
    moreover
    have "A_SUM.sum_mult a b = a"
      using "2" A_SUM.sum_mult.simps(2) sum_one_def by simp
    ultimately
    show ?thesis
      by simp
  next
    case 3
    define i j where "i = A_SUM.floor a" and "j = A_SUM.floor b"
    then
    have "i \<in> I \<and> j \<in> I \<and> a \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A} \<and> b \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}"
      using "3"(1,2) A_SUM.floor_prop sum_one_def by auto
    then
    have "a *\<^sup>A b = b"
      using "3"(3) assms different_indexes_mult i_def j_def mult_comm by metis
    moreover
    have "A_SUM.sum_mult a b = b"
      using "3" A_SUM.sum_mult.simps(3) sum_one_def by simp
    ultimately
    show ?thesis
      by simp
  next
    case 4
    then
    show ?thesis
      using A_SUM.mult_neutr A_SUM.mult_neutr_2 assms sum_one_def by force
  qed
qed

lemma same_imp:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<rightarrow>\<^sup>A b = A_SUM.sum_imp a b"
proof -
  from assms
  consider (1) "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "A_SUM.floor a = A_SUM.floor b"
    | (2) "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "A_SUM.floor a <\<^sup>I A_SUM.floor b"
    | (3) "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}" "A_SUM.floor b <\<^sup>I A_SUM.floor a"
    | (4) "a = 1\<^sup>A \<or> b = 1\<^sup>A"
    using same_uni A_SUM.floor_prop fixed_points.cases sum_one_def trichotomy
    by metis
  then
  show ?thesis
  proof(cases)
    case 1 
    then
    show ?thesis
      using A_SUM.sum_imp.simps(1) imp_map_def sum_one_def by auto
  next
    case 2
    define i j where "i = A_SUM.floor a" and "j = A_SUM.floor b"
    then
    have "i \<in> I \<and> j \<in> I \<and> a \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A} \<and> b \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}"
      using "2"(1,2) A_SUM.floor_prop sum_one_def by simp
    then
    have "a \<rightarrow>\<^sup>A b = 1\<^sup>A"
      using "2"(3) different_indexes_imp_1 i_def j_def by blast
    moreover
    have "A_SUM.sum_imp a b = 1\<^sup>A"
      using "2" A_SUM.sum_imp.simps(2) sum_one_def by simp
    ultimately
    show ?thesis
      by simp
  next
    case 3
    define i j where "i = A_SUM.floor a" and "j = A_SUM.floor b"
    then
    have "i \<in> I \<and> j \<in> I \<and> a \<in> (\<bbbA>\<^sub>i)-{1\<^sup>A} \<and> b \<in> (\<bbbA>\<^sub>j)-{1\<^sup>A}"
      using "3"(1,2) A_SUM.floor_prop sum_one_def by simp
    then
    have "a \<rightarrow>\<^sup>A b = b"
      using "3"(3) different_indexes_imp_2 i_def j_def by blast
    moreover
    have "A_SUM.sum_imp a b = b"
      using "3" A_SUM.sum_imp.simps(3) sum_one_def by auto
    ultimately
    show ?thesis
      by simp
  next
    case 4
    then
    show ?thesis
      using A_SUM.imp_one_C A_SUM.imp_one_top assms imp_one_C
            imp_one_top sum_one_def
      by force
  qed
qed

lemma ordinal_sum_is_totally_ordered_hoop:
  "totally_ordered_hoop A_SUM.sum_univ A_SUM.sum_mult A_SUM.sum_imp 1\<^sup>S"
proof
  show "A_SUM.hoop_order x y \<or> A_SUM.hoop_order y x"
    if "x \<in> A_SUM.sum_univ" "y \<in> A_SUM.sum_univ" for x y
    using that A_SUM.hoop_order_def total_order hoop_order_def
          sum_one_def same_imp
    by auto
qed

theorem totally_ordered_hoop_is_equal_to_ordinal_sum_of_tower_of_irr_hoops: 
  shows eq_universe: "A = A_SUM.sum_univ"
  and eq_mult: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x *\<^sup>A y = A_SUM.sum_mult x y"
  and eq_imp: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<rightarrow>\<^sup>A y = A_SUM.sum_imp x y"
  and eq_one: "1\<^sup>A = 1\<^sup>S"
proof
  show "A \<subseteq> A_SUM.sum_univ"
    by simp
next
  show "A_SUM.sum_univ \<subseteq> A"
    by simp
next
  show "x *\<^sup>A y = A_SUM.sum_mult x y" if "x \<in> A" "y \<in> A" for x y
    using same_mult that by blast
next
  show "x \<rightarrow>\<^sup>A y = A_SUM.sum_imp x y" if "x \<in> A" "y \<in> A" for x y
    using same_imp that by blast
next 
  show "1\<^sup>A = 1\<^sup>S"
    using sum_one_def by simp
qed

subsubsection\<open>Remarks on the nontrivial case\<close>

text\<open>In the nontrivial case we have that every totally ordered hoop
can be written as the ordinal sum of a tower of nontrivial irreducible hoops. The 
proof of this fact is almost immediate. By definition, @{text "\<bbbA>\<^sub>\<pi>\<^sub>1\<^sub>A = {1\<^sup>A}"}
is the only trivial hoop in our tower. Moreover, @{text "\<bbbA>\<^sub>\<pi>\<^sub>a"} is non-trivial for every
 @{text "a \<in> A-{1\<^sup>A}"}. Given that @{text "1\<^sup>A \<in> \<bbbA>\<^sub>i"} for every @{text "i \<in> I"}
 we can simply remove @{text "\<pi> 1\<^sup>A"} from @{text "I"} and obtain the desired result.\<close>

lemma nontrivial_tower: 
  assumes "\<exists> x \<in> A. x \<noteq> 1\<^sup>A"
  shows
    "tower_of_nontrivial_irr_hoops (I-{\<pi> 1\<^sup>A}) (\<le>\<^sup>I) (<\<^sup>I) UNI\<^sub>A MUL\<^sub>A IMP\<^sub>A 1\<^sup>S"
proof
  show "I-{\<pi> 1\<^sup>A} \<noteq> \<emptyset>"
  proof -
    obtain a where "a \<in> A-{1\<^sup>A}"
      using assms by blast
    then
    have "\<pi> a \<in> I-{\<pi> 1\<^sup>A}"
      using A_SUM.floor_prop class_not_one class_one floor_is_class sum_one_def by auto
    then
    show ?thesis
      by auto
  qed
next
  show "reflp_on (I-{\<pi> 1\<^sup>A}) (\<le>\<^sup>I)"
    using Diff_subset reflex reflp_on_subset by meson
next 
  show "antisymp_on (I-{\<pi> 1\<^sup>A}) (\<le>\<^sup>I)"
    using Diff_subset antisymm antisymp_on_subset by meson
next
  show "transp_on (I-{\<pi> 1\<^sup>A}) (\<le>\<^sup>I)"
    using Diff_subset trans transp_on_subset by meson
next
  show "i <\<^sup>I j = (i \<le>\<^sup>I j \<and> i \<noteq> j)" if "i \<in> I-{\<pi> 1\<^sup>A}" "j \<in> I-{\<pi> 1\<^sup>A}" for i j
    using index_order_strict_def by simp
next
  show "totalp_on (I-{\<pi> 1\<^sup>A}) (\<le>\<^sup>I)"
    using Diff_subset total totalp_on_subset by meson
next
  show "(\<bbbA>\<^sub>i) \<inter> (\<bbbA>\<^sub>j) = {1\<^sup>S}" if "i \<in> I-{\<pi> 1\<^sup>A}" "j \<in> I-{\<pi> 1\<^sup>A}" "i \<noteq> j" for i j
    using A_SUM.almost_disjoint that by blast
next
  show "x *\<^sup>i y \<in> \<bbbA>\<^sub>i" if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using A_SUM.floor_mult_closed that by blast
next 
  show "x \<rightarrow>\<^sup>i y \<in> \<bbbA>\<^sub>i" if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using A_SUM.floor_imp_closed that by blast
next 
  show "1\<^sup>S \<in> \<bbbA>\<^sub>i" if "i \<in> I-{\<pi> 1\<^sup>A}" for i
    using universes_one_closed sum_one_def that by simp
next
  show "x *\<^sup>i y = y *\<^sup>i x" if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using universes_subsets mult_comm mult_map_def that by force
next 
  show "x *\<^sup>i (y *\<^sup>i z) = (x *\<^sup>i y) *\<^sup>i z" 
    if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for i x y z
    using universes_subsets mult_assoc mult_map_def that by force
next 
  show "x *\<^sup>i 1\<^sup>S = x" if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" for i x
    using universes_subsets sum_one_def mult_map_def that by force
next
  show "x \<rightarrow>\<^sup>i x = 1\<^sup>S" if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" for i x
    using universes_subsets imp_map_def sum_one_def that by force
next
  show "x *\<^sup>i (x \<rightarrow>\<^sup>i y) = y *\<^sup>i (y \<rightarrow>\<^sup>i x)"
    if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for i x y z
    using divisibility universes_subsets imp_map_def mult_map_def that by auto
next
  show "x \<rightarrow>\<^sup>i (y \<rightarrow>\<^sup>i z) = (x *\<^sup>i y) \<rightarrow>\<^sup>i z"
    if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" "z \<in> \<bbbA>\<^sub>i" for i x y z
    using universes_subsets imp_map_def mult_map_def residuation that by force
next
  show "x \<le>\<^sup>i y \<or> y \<le>\<^sup>i x" if "i \<in> I-{\<pi> 1\<^sup>A}" "x \<in> \<bbbA>\<^sub>i" "y \<in> \<bbbA>\<^sub>i" for i x y
    using DiffE total_order universes_subsets imp_map_def sum_one_def that by metis
next
  show "\<nexists> B C.
       (\<bbbA>\<^sub>i = B \<union> C) \<and>
       ({1\<^sup>S} = B \<inter> C) \<and>
       (\<exists> y \<in> B. y \<noteq> 1\<^sup>S) \<and>
       (\<exists> y \<in> C. y \<noteq> 1\<^sup>S) \<and> 
       (hoop B (*\<^sup>i) (\<rightarrow>\<^sup>i) 1\<^sup>S) \<and>
       (hoop C (*\<^sup>i) (\<rightarrow>\<^sup>i) 1\<^sup>S) \<and>
       (\<forall> x \<in> B-{1\<^sup>S}. \<forall> y \<in> C. x *\<^sup>i y = x) \<and>
       (\<forall> x \<in> B-{1\<^sup>S}. \<forall> y \<in> C. x \<rightarrow>\<^sup>i y = 1\<^sup>S) \<and>
       (\<forall> x \<in> C. \<forall> y \<in> B. x \<rightarrow>\<^sup>i y = y)"
    if "i \<in> I-{\<pi> 1\<^sup>A}" for i
    using that Diff_iff Un_iff universes_one_fixed imp_map_def sum_one_def by metis
next
  show "\<exists> x \<in> \<bbbA>\<^sub>i. x \<noteq> 1\<^sup>S" if "i \<in> I-{\<pi> 1\<^sup>A}" for i 
    using universes_def indexes_class_of_elements indexes_not_empty that
    by fastforce
qed

lemma ordinal_sum_of_nontrivial: 
  assumes "\<exists> x \<in> A. x \<noteq> 1\<^sup>A"
  shows "A_SUM.sum_univ = {x. \<exists> i \<in> I-{\<pi> 1\<^sup>A}. x \<in> \<bbbA>\<^sub>i}"
proof
  show "A_SUM.sum_univ \<subseteq> {x. \<exists> i \<in> I-{\<pi> 1\<^sup>A}. x \<in> \<bbbA>\<^sub>i}"
  proof 
    fix a 
    assume "a \<in> A_SUM.sum_univ"
    then
    consider (1) "a \<in> A-{1\<^sup>A}"
      | (2) "a = 1\<^sup>A"
      by auto
    then
    show "a \<in> {x. \<exists> i \<in> I-{\<pi> 1\<^sup>A}. x \<in> \<bbbA>\<^sub>i}"
    proof(cases)
      case 1 
      then
      obtain i where "i = \<pi> a"
        by simp
      then
      have "a \<in> \<bbbA>\<^sub>i \<and> i \<in> I-{\<pi> 1\<^sup>A}"
        using "1" A_SUM.floor_prop class_not_one class_one floor_is_class sum_one_def
        by auto
      then
      show ?thesis
        by blast
    next
      case 2
      obtain c where "c \<in> A-{1\<^sup>A}"
        using assms by blast
      then
      obtain i where "i = \<pi> c"
        by simp
      then
      have "a \<in> \<bbbA>\<^sub>i \<and> i \<in> I-{\<pi> 1\<^sup>A}"
        using "2" A_SUM.floor_prop \<open>c \<in> A-{1\<^sup>A}\<close> class_not_one class_one
              universes_one_closed floor_is_class sum_one_def
        by auto
      then
      show ?thesis
        by auto
    qed
  qed
next
  show "{x. \<exists> i \<in> I-{\<pi> 1\<^sup>A}. x \<in> \<bbbA>\<^sub>i} \<subseteq> A_SUM.sum_univ"
    using universes_subsets by force
qed

end

subsubsection\<open>Converse of main result\<close>

text\<open>We show that the converse of the main result also holds, that is,
the ordinal sum of a tower of irreducible hoops is a totally ordered hoop.\<close>

context tower_of_irr_hoops
begin

proposition ordinal_sum_of_tower_of_irr_hoops_is_totally_ordered_hoop:
  shows "totally_ordered_hoop S (*\<^sup>S) (\<rightarrow>\<^sup>S) 1\<^sup>S"
proof 
  show "hoop_order a b \<or> hoop_order b a" if "a \<in> S" "b \<in> S" for a b
  proof - 
    from that
    consider (1) "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "floor a = floor b"
      | (2) "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "floor a <\<^sup>I floor b \<or> floor b <\<^sup>I floor a"
      | (3) "a = 1\<^sup>S \<or> b = 1\<^sup>S"
      using floor.cases floor_prop trichotomy by metis
    then
    show "hoop_order a b \<or> hoop_order b a"
    proof(cases)
      case 1
      then
      have "a \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a \<and> b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
        using "1" floor_prop by metis
      moreover
      have "totally_ordered_hoop (\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a) (*\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a) (\<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a) 1\<^sup>S"
        using "1"(1) family_of_irr_hoops totally_ordered_irreducible_hoop.axioms(1)
              floor_prop
        by meson
      ultimately
      have "a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b = 1\<^sup>S \<or> b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a = 1\<^sup>S"
        using hoop.hoop_order_def totally_ordered_hoop.total_order
              totally_ordered_hoop_def
        by meson
      moreover
      have "a \<rightarrow>\<^sup>S b = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b \<and> b \<rightarrow>\<^sup>S a = b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a"
        using "1" by auto
      ultimately
      show ?thesis
        using hoop_order_def by force
    next
      case 2
      then
      show ?thesis
        using sum_imp.simps(2) hoop_order_def by blast
    next
      case 3
      then
      show ?thesis
        using that ord_top by auto
    qed
  qed
qed

end

end