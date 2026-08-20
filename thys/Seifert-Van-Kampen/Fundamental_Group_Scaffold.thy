theory Fundamental_Group_Scaffold
  imports "HOL-Analysis.Homotopy" Carrier_Group_Scaffold
begin

section \<open>Fundamental-group quotients\<close>

text \<open>
  This is the set-based counterpart to the explicit-topology quotient
  development. It works directly with subsets of a topological space and the
  standard HOL-Analysis path notions, which is exactly the level needed for the
  final classical theorem about open sets \<open>U\<close> and \<open>V\<close>.
\<close>

definition loop_space ::
  "'a::topological_space set => 'a => (real => 'a) set"
where
  "loop_space S x =
     {p. path p \<and> path_image p \<subseteq> S \<and> pathstart p = x \<and> pathfinish p = x}"

definition loop_class ::
  "'a::topological_space set => 'a => (real => 'a) => (real => 'a) set"
where
  "loop_class S x p = {q. q \<in> loop_space S x \<and> homotopic_paths S q p}"

definition fundamental_group_space ::
  "'a::topological_space set => 'a => ((real => 'a) set) set"
where
  "fundamental_group_space S x = loop_class S x ` loop_space S x"

definition some_loop ::
  "'a::topological_space set => 'a => (real => 'a) set => (real => 'a)"
where
  "some_loop S x Q = (SOME p. p \<in> loop_space S x \<and> Q = loop_class S x p)"

definition fundamental_group_one ::
  "'a::topological_space set => 'a => (real => 'a) set"
where
  "fundamental_group_one S x = loop_class S x (\<lambda>_. x)"

definition fundamental_group_mult ::
  "'a::topological_space set => 'a =>
    (real => 'a) set => (real => 'a) set => (real => 'a) set"
where
  "fundamental_group_mult S x A B =
     loop_class S x (some_loop S x A +++ some_loop S x B)"

definition fundamental_group_inv ::
  "'a::topological_space set => 'a =>
    (real => 'a) set => (real => 'a) set"
where
  "fundamental_group_inv S x A = loop_class S x (reversepath (some_loop S x A))"

definition loop_image ::
  "('a::topological_space => 'b::topological_space) =>
    (real => 'a) => (real => 'b)"
where
  "loop_image h p = h \<circ> p"

definition fundamental_group_map ::
  "'a::topological_space set => 'a =>
    'b::topological_space set => 'b =>
    ('a => 'b) => (real => 'a) set => (real => 'b) set"
where
  "fundamental_group_map S x T y h A =
     loop_class T y (loop_image h (some_loop S x A))"

lemma loop_spaceI:
  assumes "path p"
    and "path_image p \<subseteq> S"
    and "pathstart p = x"
    and "pathfinish p = x"
  shows "p \<in> loop_space S x"
  using assms unfolding loop_space_def by blast

lemma constant_loop_in_space:
  assumes "x \<in> S"
  shows "(\<lambda>_. x) \<in> loop_space S x"
proof (rule loop_spaceI)
  show "path (\<lambda>_. x)"
    by (simp add: path_def)
  show "path_image (\<lambda>_. x) \<subseteq> S"
    using assms by (auto simp: path_image_def)
  show "pathstart (\<lambda>_. x) = x"
    by (simp add: pathstart_def)
  show "pathfinish (\<lambda>_. x) = x"
    by (simp add: pathfinish_def)
qed

lemma loop_class_in_space:
  assumes "p \<in> loop_space S x"
  shows "loop_class S x p \<in> fundamental_group_space S x"
  using assms unfolding fundamental_group_space_def by blast

lemma fundamental_group_spaceE:
  assumes "Q \<in> fundamental_group_space S x"
  obtains p where "p \<in> loop_space S x" "Q = loop_class S x p"
  using assms unfolding fundamental_group_space_def by blast

lemma some_loop_spec:
  assumes "Q \<in> fundamental_group_space S x"
  shows "some_loop S x Q \<in> loop_space S x"
    and "Q = loop_class S x (some_loop S x Q)"
proof -
  from assms obtain p where p: "p \<in> loop_space S x" "Q = loop_class S x p"
    by (rule fundamental_group_spaceE)
  have ex: "\<exists>p. p \<in> loop_space S x \<and> Q = loop_class S x p"
    using p by blast
  have "some_loop S x Q \<in> loop_space S x \<and> Q = loop_class S x (some_loop S x Q)"
    unfolding some_loop_def by (rule someI_ex[OF ex])
  then show "some_loop S x Q \<in> loop_space S x"
    and "Q = loop_class S x (some_loop S x Q)"
    by auto
qed

lemma loop_class_eqI:
  assumes p: "p \<in> loop_space S x"
    and q: "q \<in> loop_space S x"
    and pq: "homotopic_paths S p q"
  shows "loop_class S x p = loop_class S x q"
proof (auto simp: loop_class_def)
  fix r
  assume "homotopic_paths S r p"
  then show "homotopic_paths S r q"
    using pq by (rule homotopic_paths_trans)
next
  fix r
  assume "homotopic_paths S r q"
  moreover have "homotopic_paths S q p"
    using pq by (rule homotopic_paths_sym)
  ultimately show "homotopic_paths S r p"
    by (rule homotopic_paths_trans)
qed

lemma loop_class_eq_iff:
  assumes p: "p \<in> loop_space S x"
    and q: "q \<in> loop_space S x"
  shows "loop_class S x p = loop_class S x q \<longleftrightarrow> homotopic_paths S p q"
proof
  assume h: "loop_class S x p = loop_class S x q"
  have "p \<in> loop_class S x p"
  proof -
    from p have p_props: "path p" "path_image p \<subseteq> S"
      unfolding loop_space_def by auto
    have "homotopic_paths S p p"
      using p_props by simp
    with p show ?thesis
      unfolding loop_class_def by auto
  qed
  with h show "homotopic_paths S p q"
    unfolding loop_class_def by blast
next
  assume "homotopic_paths S p q"
  then show "loop_class S x p = loop_class S x q"
    by (rule loop_class_eqI[OF p q])
qed

lemma loop_space_join:
  assumes p: "p \<in> loop_space S x"
    and q: "q \<in> loop_space S x"
  shows "p +++ q \<in> loop_space S x"
proof -
  from p have p_props:
    "path p" "path_image p \<subseteq> S" "pathstart p = x" "pathfinish p = x"
    unfolding loop_space_def by auto
  from q have q_props:
    "path q" "path_image q \<subseteq> S" "pathstart q = x" "pathfinish q = x"
    unfolding loop_space_def by auto
  show ?thesis
  proof (rule loop_spaceI)
    show "path (p +++ q)"
      using p_props q_props by simp
    show "path_image (p +++ q) \<subseteq> S"
      using p_props(2) q_props(2) by (rule subset_path_image_join)
    show "pathstart (p +++ q) = x"
      using p_props by simp
    show "pathfinish (p +++ q) = x"
      using q_props by simp
  qed
qed

lemma loop_space_reversepath:
  assumes "p \<in> loop_space S x"
  shows "reversepath p \<in> loop_space S x"
proof -
  from assms have p_props:
    "path p" "path_image p \<subseteq> S" "pathstart p = x" "pathfinish p = x"
    unfolding loop_space_def by auto
  show ?thesis
  proof (rule loop_spaceI)
    show "path (reversepath p)"
      using p_props by simp
    show "path_image (reversepath p) \<subseteq> S"
      using p_props by simp
    show "pathstart (reversepath p) = x"
      using p_props by simp
    show "pathfinish (reversepath p) = x"
      using p_props by simp
  qed
qed

lemma loop_space_continuous_image:
  assumes p: "p \<in> loop_space S x"
    and cont_h: "continuous_on S h"
    and map_h: "h \<in> S \<rightarrow> T"
    and hx: "h x = y"
  shows "loop_image h p \<in> loop_space T y"
proof -
  from p have p_props:
    "path p" "path_image p \<subseteq> S" "pathstart p = x" "pathfinish p = x"
    unfolding loop_space_def by auto
  show ?thesis
    unfolding loop_image_def
  proof (rule loop_spaceI)
    show "path (h \<circ> p)"
      using p_props(1) continuous_on_subset[OF cont_h p_props(2)]
      by (rule Path_Connected.path_continuous_image)
    show "path_image (h \<circ> p) \<subseteq> T"
      using p_props(2) map_h
      by (auto simp: path_image_def)
    show "pathstart (h \<circ> p) = y"
      using p_props(3) hx by (simp add: pathstart_compose)
    show "pathfinish (h \<circ> p) = y"
      using p_props(4) hx by (simp add: pathfinish_compose)
  qed
qed

lemma loop_image_join:
  "loop_image h (p +++ q) = loop_image h p +++ loop_image h q"
  unfolding loop_image_def
  by (rule ext) (simp add: joinpaths_def)

lemma loop_image_reversepath:
  "loop_image h (reversepath p) = reversepath (loop_image h p)"
  unfolding loop_image_def reversepath_def
  by (rule ext) simp

lemma loop_class_join_eqI:
  assumes p: "p \<in> loop_space S x"
    and p': "p' \<in> loop_space S x"
    and q: "q \<in> loop_space S x"
    and q': "q' \<in> loop_space S x"
    and pp': "homotopic_paths S p p'"
    and qq': "homotopic_paths S q q'"
  shows "loop_class S x (p +++ q) = loop_class S x (p' +++ q')"
proof (rule loop_class_eqI)
  show "p +++ q \<in> loop_space S x"
    using p q by (rule loop_space_join)
  show "p' +++ q' \<in> loop_space S x"
    using p' q' by (rule loop_space_join)
  from p have px: "pathfinish p = x"
    unfolding loop_space_def by auto
  from q have qx: "pathstart q = x"
    unfolding loop_space_def by auto
  show "homotopic_paths S (p +++ q) (p' +++ q')"
  proof (rule homotopic_paths_join)
    show "homotopic_paths S p p'"
      by (rule pp')
    show "homotopic_paths S q q'"
      by (rule qq')
    show "pathfinish p = pathstart q"
      using px qx by simp
  qed
qed

lemma loop_class_reverse_eqI:
  assumes p: "p \<in> loop_space S x"
    and q: "q \<in> loop_space S x"
    and pq: "homotopic_paths S p q"
  shows "loop_class S x (reversepath p) = loop_class S x (reversepath q)"
proof (rule loop_class_eqI)
  show "reversepath p \<in> loop_space S x"
    using p by (rule loop_space_reversepath)
  show "reversepath q \<in> loop_space S x"
    using q by (rule loop_space_reversepath)
  from pq show "homotopic_paths S (reversepath p) (reversepath q)"
    by (rule homotopic_paths_reversepath_D)
qed

lemma homotopic_paths_rid_const:
  assumes "path p"
    and "path_image p \<subseteq> S"
  shows "homotopic_paths S (p +++ (\<lambda>_. pathfinish p)) p"
proof -
  let ?f = "\<lambda>t::real. if t \<le> 1/2 then 2 *\<^sub>R t else 1"
  have contf: "continuous_on {0..1} ?f"
    unfolding split_01
    by (rule continuous_on_cases continuous_intros | auto)+
  have f01: "?f \<in> {0..1} \<rightarrow> {0..1}"
    by auto
  have "homotopic_paths S p (p +++ (\<lambda>_. pathfinish p))"
  proof (rule homotopic_paths_reparametrize[where f = ?f])
    show "path p"
      by (rule assms(1))
    show "path_image p \<subseteq> S"
      by (rule assms(2))
    show "continuous_on {0..1} ?f"
      by (rule contf)
    show "?f \<in> {0..1} \<rightarrow> {0..1}"
      by (rule f01)
    show "?f 0 = 0" "?f 1 = 1"
      by simp_all
    show "(p +++ (\<lambda>_. pathfinish p)) t = p (?f t)" if "t \<in> {0..1}" for t
      using that by (auto simp: joinpaths_def pathfinish_def)
  qed
  then show ?thesis
    by (rule homotopic_paths_sym)
qed

lemma homotopic_paths_lid_const:
  assumes "path p"
    and "path_image p \<subseteq> S"
  shows "homotopic_paths S ((\<lambda>_. pathstart p) +++ p) p"
proof -
  let ?f = "\<lambda>t::real. if t \<le> 1/2 then 0 else 2 *\<^sub>R t - 1"
  have contf: "continuous_on {0..1} ?f"
    unfolding split_01
    by (rule continuous_on_cases continuous_intros | auto)+
  have f01: "?f \<in> {0..1} \<rightarrow> {0..1}"
    by auto
  have "homotopic_paths S p ((\<lambda>_. pathstart p) +++ p)"
  proof (rule homotopic_paths_reparametrize[where f = ?f])
    show "path p"
      by (rule assms(1))
    show "path_image p \<subseteq> S"
      by (rule assms(2))
    show "continuous_on {0..1} ?f"
      by (rule contf)
    show "?f \<in> {0..1} \<rightarrow> {0..1}"
      by (rule f01)
    show "?f 0 = 0" "?f 1 = 1"
      by simp_all
    show "((\<lambda>_. pathstart p) +++ p) t = p (?f t)" if "t \<in> {0..1}" for t
      using that by (auto simp: joinpaths_def pathstart_def)
  qed
  then show ?thesis
    by (rule homotopic_paths_sym)
qed

lemma homotopic_paths_rinv_const:
  assumes "path p"
    and "path_image p \<subseteq> S"
  shows "homotopic_paths S (p +++ reversepath p) (\<lambda>_. pathstart p)"
proof -
  let ?A = "{0..1} \<times> {0..1}"
  let ?h =
    "\<lambda>y. if snd y \<le> 1/2
      then p (fst y * (2 * snd y))
      else p (fst y * (1 - (2 * snd y - 1)))"
  define H where "H = ?h"
  have p_cont: "continuous_on {0..1} p"
    using assms by (auto simp: path_def)
  have h_cont: "continuous_on ?A H"
    unfolding H_def
  proof (rule continuous_on_cases_le)
    show "continuous_on {x \<in> ?A. snd x \<le> 1/2} (\<lambda>t. p (fst t * (2 * snd t)))"
         "continuous_on {x \<in> ?A. 1/2 \<le> snd x} (\<lambda>t. p (fst t * (1 - (2 * snd t - 1))))"
      "continuous_on ?A snd"
      by (intro continuous_on_compose2 [OF p_cont] continuous_intros; auto simp: mult_le_one)+
  qed (auto simp: algebra_simps)
  have h_subset: "H \<in> ?A \<rightarrow> S"
  proof
    fix y :: "real \<times> real"
    assume y: "y \<in> ?A"
    with assms show "H y \<in> S"
      unfolding H_def
      by (force simp: path_image_def mult_le_one)
  qed
  have h0: "\<forall>x\<in>{0..1}. H (0, x) = (\<lambda>_. pathstart p) x"
    unfolding H_def by (simp add: pathstart_def)
  have h1: "\<forall>x\<in>{0..1}. H (1, x) = (p +++ reversepath p) x"
    unfolding H_def by (auto simp: joinpaths_def reversepath_def)
  have hends:
    "\<forall>t\<in>{0..1}. pathstart (H \<circ> Pair t) = pathstart (\<lambda>_. pathstart p) \<and>
      pathfinish (H \<circ> Pair t) = pathfinish (\<lambda>_. pathstart p)"
  proof
    fix t :: real
    assume "t \<in> {0..1}"
    show "pathstart (H \<circ> Pair t) = pathstart (\<lambda>_. pathstart p) \<and>
      pathfinish (H \<circ> Pair t) = pathfinish (\<lambda>_. pathstart p)"
    proof
      show "pathstart (H \<circ> Pair t) = pathstart (\<lambda>_. pathstart p)"
        unfolding H_def by (simp add: pathstart_def)
      show "pathfinish (H \<circ> Pair t) = pathfinish (\<lambda>_. pathstart p)"
        unfolding H_def by (simp add: pathstart_def pathfinish_def)
    qed
  qed
  have hom_const:
    "homotopic_paths S (\<lambda>_. pathstart p) (p +++ reversepath p)"
    apply (rule iffD2[OF homotopic_paths])
    apply (rule_tac
        x = "(\<lambda>y. if snd y \<le> 1/2
          then p (fst y * (2 * snd y))
          else p (fst y * (1 - (2 * snd y - 1))))"
        in exI)
    using h_cont h_subset h0 h1 hends
    unfolding H_def
    apply blast
    done
  show ?thesis
    using hom_const by (rule homotopic_paths_sym)
qed

lemma homotopic_paths_linv_const:
  assumes "path p"
    and "path_image p \<subseteq> S"
  shows "homotopic_paths S (reversepath p +++ p) (\<lambda>_. pathfinish p)"
  using homotopic_paths_rinv_const [of "reversepath p" S] assms
  by simp

lemma fundamental_group_one_in_space:
  assumes "x \<in> S"
  shows "fundamental_group_one S x \<in> fundamental_group_space S x"
  unfolding fundamental_group_one_def
  using constant_loop_in_space[OF assms] by (rule loop_class_in_space)

lemma fundamental_group_mult_eqI:
  assumes A_in: "A \<in> fundamental_group_space S x"
    and B_in: "B \<in> fundamental_group_space S x"
    and p: "p \<in> loop_space S x"
    and q: "q \<in> loop_space S x"
    and A: "A = loop_class S x p"
    and B: "B = loop_class S x q"
  shows "fundamental_group_mult S x A B = loop_class S x (p +++ q)"
proof -
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF A_in] by auto
  have repB: "some_loop S x B \<in> loop_space S x" "B = loop_class S x (some_loop S x B)"
    using some_loop_spec[OF B_in] by auto
  have homoA': "homotopic_paths S p (some_loop S x A)"
    using repA p A by (simp add: loop_class_eq_iff)
  have homoA: "homotopic_paths S (some_loop S x A) p"
    using homoA' by (rule homotopic_paths_sym)
  have homoB': "homotopic_paths S q (some_loop S x B)"
    using repB q B by (simp add: loop_class_eq_iff)
  have homoB: "homotopic_paths S (some_loop S x B) q"
    using homoB' by (rule homotopic_paths_sym)
  have "loop_class S x (some_loop S x A +++ some_loop S x B) = loop_class S x (p +++ q)"
    by (rule loop_class_join_eqI[OF repA(1) p repB(1) q homoA homoB])
  then show ?thesis
    unfolding fundamental_group_mult_def .
qed

lemma fundamental_group_mult_in_space:
  assumes "A \<in> fundamental_group_space S x"
    and "B \<in> fundamental_group_space S x"
  shows "fundamental_group_mult S x A B \<in> fundamental_group_space S x"
proof -
  have repA: "some_loop S x A \<in> loop_space S x"
    using some_loop_spec[OF assms(1)] by auto
  have repB: "some_loop S x B \<in> loop_space S x"
    using some_loop_spec[OF assms(2)] by auto
  show ?thesis
    unfolding fundamental_group_mult_def
    using loop_space_join[OF repA repB] by (rule loop_class_in_space)
qed

lemma fundamental_group_inv_eqI:
  assumes A_in: "A \<in> fundamental_group_space S x"
    and p: "p \<in> loop_space S x"
    and A: "A = loop_class S x p"
  shows "fundamental_group_inv S x A = loop_class S x (reversepath p)"
proof -
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF A_in] by auto
  have homoA': "homotopic_paths S p (some_loop S x A)"
    using repA p A by (simp add: loop_class_eq_iff)
  have homoA: "homotopic_paths S (some_loop S x A) p"
    using homoA' by (rule homotopic_paths_sym)
  have "loop_class S x (reversepath (some_loop S x A)) = loop_class S x (reversepath p)"
    by (rule loop_class_reverse_eqI[OF repA(1) p homoA])
  then show ?thesis
    unfolding fundamental_group_inv_def .
qed

lemma fundamental_group_inv_in_space:
  assumes "A \<in> fundamental_group_space S x"
  shows "fundamental_group_inv S x A \<in> fundamental_group_space S x"
proof -
  have repA: "some_loop S x A \<in> loop_space S x"
    using some_loop_spec[OF assms] by auto
  show ?thesis
    unfolding fundamental_group_inv_def
    using loop_space_reversepath[OF repA] by (rule loop_class_in_space)
qed

lemma fundamental_group_map_eqI:
  assumes A_in: "A \<in> fundamental_group_space S x"
    and p: "p \<in> loop_space S x"
    and A: "A = loop_class S x p"
    and cont_h: "continuous_on S h"
    and map_h: "h \<in> S \<rightarrow> T"
    and hx: "h x = y"
  shows "fundamental_group_map S x T y h A = loop_class T y (loop_image h p)"
proof -
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF A_in] by auto
  have homo':
    "homotopic_paths S p (some_loop S x A)"
    using repA(1) p repA(2) A
    by (simp add: loop_class_eq_iff)
  have homo:
    "homotopic_paths S (some_loop S x A) p"
    using homo' by (rule homotopic_paths_sym)
  have map_rep: "loop_image h (some_loop S x A) \<in> loop_space T y"
    by (rule loop_space_continuous_image[OF repA(1) cont_h map_h hx])
  have map_p: "loop_image h p \<in> loop_space T y"
    by (rule loop_space_continuous_image[OF p cont_h map_h hx])
  have map_homo:
    "homotopic_paths T (loop_image h (some_loop S x A)) (loop_image h p)"
    unfolding loop_image_def
    by (rule homotopic_paths_continuous_image[OF homo cont_h map_h])
  have
    "loop_class T y (loop_image h (some_loop S x A)) =
      loop_class T y (loop_image h p)"
    by (rule loop_class_eqI[OF map_rep map_p map_homo])
  then show ?thesis
    unfolding fundamental_group_map_def .
qed

lemma fundamental_group_map_in_space:
  assumes A_in: "A \<in> fundamental_group_space S x"
    and cont_h: "continuous_on S h"
    and map_h: "h \<in> S \<rightarrow> T"
    and hx: "h x = y"
  shows "fundamental_group_map S x T y h A \<in> fundamental_group_space T y"
proof -
  have repA: "some_loop S x A \<in> loop_space S x"
    using some_loop_spec[OF A_in] by auto
  have "loop_image h (some_loop S x A) \<in> loop_space T y"
    by (rule loop_space_continuous_image[OF repA cont_h map_h hx])
  then show ?thesis
    unfolding fundamental_group_map_def by (rule loop_class_in_space)
qed

lemma fundamental_group_map_mult:
  assumes A_in: "A \<in> fundamental_group_space S x"
    and B_in: "B \<in> fundamental_group_space S x"
    and cont_h: "continuous_on S h"
    and map_h: "h \<in> S \<rightarrow> T"
    and hx: "h x = y"
  shows
    "fundamental_group_map S x T y h (fundamental_group_mult S x A B) =
      fundamental_group_mult T y
        (fundamental_group_map S x T y h A)
        (fundamental_group_map S x T y h B)"
proof -
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF A_in] by auto
  have repB: "some_loop S x B \<in> loop_space S x" "B = loop_class S x (some_loop S x B)"
    using some_loop_spec[OF B_in] by auto
  have AB_in: "fundamental_group_mult S x A B \<in> fundamental_group_space S x"
    by (rule fundamental_group_mult_in_space[OF A_in B_in])
  have AB_eq:
    "fundamental_group_mult S x A B =
      loop_class S x (some_loop S x A +++ some_loop S x B)"
    by (rule fundamental_group_mult_eqI[OF A_in B_in repA(1) repB(1) repA(2) repB(2)])
  have map_A_in:
    "fundamental_group_map S x T y h A \<in> fundamental_group_space T y"
    by (rule fundamental_group_map_in_space[OF A_in cont_h map_h hx])
  have map_B_in:
    "fundamental_group_map S x T y h B \<in> fundamental_group_space T y"
    by (rule fundamental_group_map_in_space[OF B_in cont_h map_h hx])
  have map_A_eq:
    "fundamental_group_map S x T y h A =
      loop_class T y (loop_image h (some_loop S x A))"
    by (rule fundamental_group_map_eqI[OF A_in repA(1) repA(2) cont_h map_h hx])
  have map_B_eq:
    "fundamental_group_map S x T y h B =
      loop_class T y (loop_image h (some_loop S x B))"
    by (rule fundamental_group_map_eqI[OF B_in repB(1) repB(2) cont_h map_h hx])
  have left_eq:
    "fundamental_group_map S x T y h (fundamental_group_mult S x A B) =
      loop_class T y (loop_image h (some_loop S x A +++ some_loop S x B))"
    by (rule fundamental_group_map_eqI[OF AB_in loop_space_join[OF repA(1) repB(1)] AB_eq cont_h map_h hx])
  have map_loop_A: "loop_image h (some_loop S x A) \<in> loop_space T y"
    by (rule loop_space_continuous_image[OF repA(1) cont_h map_h hx])
  have map_loop_B: "loop_image h (some_loop S x B) \<in> loop_space T y"
    by (rule loop_space_continuous_image[OF repB(1) cont_h map_h hx])
  have right_eq:
    "fundamental_group_mult T y
        (fundamental_group_map S x T y h A)
        (fundamental_group_map S x T y h B) =
      loop_class T y
        (loop_image h (some_loop S x A) +++ loop_image h (some_loop S x B))"
    by (rule fundamental_group_mult_eqI[OF map_A_in map_B_in map_loop_A map_loop_B map_A_eq map_B_eq])
  have
    "loop_class T y (loop_image h (some_loop S x A +++ some_loop S x B)) =
      loop_class T y (loop_image h (some_loop S x A) +++ loop_image h (some_loop S x B))"
    by (rule arg_cong[where f = "loop_class T y"], simp add: loop_image_join)
  then show ?thesis
    using left_eq right_eq by simp
qed

lemma fundamental_group_map_id:
  assumes A_in: "A \<in> fundamental_group_space S x"
  shows "fundamental_group_map S x S x id A = A"
proof -
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF A_in] by auto
  have "fundamental_group_map S x S x id A =
      loop_class S x (loop_image id (some_loop S x A))"
    by (rule fundamental_group_map_eqI[OF A_in repA(1) repA(2)]) simp_all
  then show ?thesis
    using repA(2) by (simp add: loop_image_def)
qed

lemma fundamental_group_map_one:
  assumes x_in: "x \<in> S"
    and cont_h: "continuous_on S h"
    and map_h: "h \<in> S \<rightarrow> T"
    and hx: "h x = y"
  shows
    "fundamental_group_map S x T y h (fundamental_group_one S x) =
      fundamental_group_one T y"
proof -
  have one_in: "fundamental_group_one S x \<in> fundamental_group_space S x"
    by (rule fundamental_group_one_in_space[OF x_in])
  have const_in: "(\<lambda>_. x) \<in> loop_space S x"
    by (rule constant_loop_in_space[OF x_in])
  have "fundamental_group_map S x T y h (fundamental_group_one S x) =
      loop_class T y (loop_image h (\<lambda>_. x))"
    by (rule fundamental_group_map_eqI[OF one_in const_in]) (simp_all add: fundamental_group_one_def cont_h map_h hx)
  then show ?thesis
    by (simp add: fundamental_group_one_def loop_image_def hx)
qed

lemma fundamental_group_map_compose:
  assumes A_in: "A \<in> fundamental_group_space S x"
    and cont_h: "continuous_on S h"
    and map_h: "h \<in> S \<rightarrow> T"
    and hx: "h x = y"
    and cont_k: "continuous_on T k"
    and map_k: "k \<in> T \<rightarrow> U"
    and ky: "k y = z"
  shows
    "fundamental_group_map T y U z k (fundamental_group_map S x T y h A) =
      fundamental_group_map S x U z (k \<circ> h) A"
proof -
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF A_in] by auto
  have map_A_in:
    "fundamental_group_map S x T y h A \<in> fundamental_group_space T y"
    by (rule fundamental_group_map_in_space[OF A_in cont_h map_h hx])
  have map_A_eq:
    "fundamental_group_map S x T y h A =
      loop_class T y (loop_image h (some_loop S x A))"
    by (rule fundamental_group_map_eqI[OF A_in repA(1) repA(2) cont_h map_h hx])
  have left_eq:
    "fundamental_group_map T y U z k (fundamental_group_map S x T y h A) =
      loop_class U z (loop_image k (loop_image h (some_loop S x A)))"
    by (rule fundamental_group_map_eqI[OF map_A_in loop_space_continuous_image[OF repA(1) cont_h map_h hx] map_A_eq cont_k map_k ky])
  have comp_cont: "continuous_on S (k \<circ> h)"
  proof -
    have hs: "h ` S \<subseteq> T"
      using map_h by auto
    have hk: "continuous_on (h ` S) k"
      using cont_k hs by (rule continuous_on_subset)
    from cont_h hk show ?thesis
      by (rule continuous_on_compose)
  qed
  have comp_map: "(k \<circ> h) \<in> S \<rightarrow> U"
    using map_h map_k by auto
  have right_eq:
    "fundamental_group_map S x U z (k \<circ> h) A =
      loop_class U z (loop_image (k \<circ> h) (some_loop S x A))"
    by (rule fundamental_group_map_eqI[OF A_in repA(1) repA(2) comp_cont comp_map])
       (simp add: hx ky)
  have
    "loop_class U z (loop_image k (loop_image h (some_loop S x A))) =
      loop_class U z (loop_image (k \<circ> h) (some_loop S x A))"
    by (rule arg_cong[where f = "loop_class U z"]) (simp add: loop_image_def o_assoc)
  then show ?thesis
    using left_eq right_eq by simp
qed

lemma fundamental_group_mult_one_left:
  assumes "x \<in> S"
    and "A \<in> fundamental_group_space S x"
  shows "fundamental_group_mult S x (fundamental_group_one S x) A = A"
proof -
  have const: "(\<lambda>_. x) \<in> loop_space S x"
    using constant_loop_in_space[OF assms(1)] .
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF assms(2)] by auto
  have loopA:
    "path (some_loop S x A)"
    "path_image (some_loop S x A) \<subseteq> S"
    "pathstart (some_loop S x A) = x"
    "pathfinish (some_loop S x A) = x"
    using repA(1) unfolding loop_space_def by auto
  have mult_eq:
    "fundamental_group_mult S x (fundamental_group_one S x) A =
      loop_class S x ((\<lambda>_. x) +++ some_loop S x A)"
  proof (rule fundamental_group_mult_eqI)
    show "fundamental_group_one S x \<in> fundamental_group_space S x"
      by (rule fundamental_group_one_in_space[OF assms(1)])
    show "A \<in> fundamental_group_space S x"
      by (rule assms(2))
    show "(\<lambda>_. x) \<in> loop_space S x"
      by (rule const)
    show "some_loop S x A \<in> loop_space S x"
      by (rule repA(1))
    show "fundamental_group_one S x = loop_class S x (\<lambda>_. x)"
      by (simp add: fundamental_group_one_def)
    show "A = loop_class S x (some_loop S x A)"
      by (rule repA(2))
  qed
  have join_loop: "(\<lambda>_. x) +++ some_loop S x A \<in> loop_space S x"
    using const repA(1) by (rule loop_space_join)
  have hom: "homotopic_paths S ((\<lambda>_. x) +++ some_loop S x A) (some_loop S x A)"
    using homotopic_paths_lid_const[OF loopA(1) loopA(2)] loopA(3) by simp
  have class_eq:
    "loop_class S x ((\<lambda>_. x) +++ some_loop S x A) = loop_class S x (some_loop S x A)"
    by (rule loop_class_eqI[OF join_loop repA(1) hom])
  show ?thesis
    using mult_eq class_eq repA(2) by simp
qed

lemma fundamental_group_mult_one_right:
  assumes "x \<in> S"
    and "A \<in> fundamental_group_space S x"
  shows "fundamental_group_mult S x A (fundamental_group_one S x) = A"
proof -
  have const: "(\<lambda>_. x) \<in> loop_space S x"
    using constant_loop_in_space[OF assms(1)] .
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF assms(2)] by auto
  have loopA:
    "path (some_loop S x A)"
    "path_image (some_loop S x A) \<subseteq> S"
    "pathstart (some_loop S x A) = x"
    "pathfinish (some_loop S x A) = x"
    using repA(1) unfolding loop_space_def by auto
  have mult_eq:
    "fundamental_group_mult S x A (fundamental_group_one S x) =
      loop_class S x (some_loop S x A +++ (\<lambda>_. x))"
  proof (rule fundamental_group_mult_eqI)
    show "A \<in> fundamental_group_space S x"
      by (rule assms(2))
    show "fundamental_group_one S x \<in> fundamental_group_space S x"
      by (rule fundamental_group_one_in_space[OF assms(1)])
    show "some_loop S x A \<in> loop_space S x"
      by (rule repA(1))
    show "(\<lambda>_. x) \<in> loop_space S x"
      by (rule const)
    show "A = loop_class S x (some_loop S x A)"
      by (rule repA(2))
    show "fundamental_group_one S x = loop_class S x (\<lambda>_. x)"
      by (simp add: fundamental_group_one_def)
  qed
  have join_loop: "some_loop S x A +++ (\<lambda>_. x) \<in> loop_space S x"
    using repA(1) const by (rule loop_space_join)
  have hom: "homotopic_paths S (some_loop S x A +++ (\<lambda>_. x)) (some_loop S x A)"
    using homotopic_paths_rid_const[OF loopA(1) loopA(2)] loopA(4) by simp
  have class_eq:
    "loop_class S x (some_loop S x A +++ (\<lambda>_. x)) = loop_class S x (some_loop S x A)"
    by (rule loop_class_eqI[OF join_loop repA(1) hom])
  show ?thesis
    using mult_eq class_eq repA(2) by simp
qed

lemma fundamental_group_mult_assoc:
  assumes A_in: "A \<in> fundamental_group_space S x"
    and B_in: "B \<in> fundamental_group_space S x"
    and C_in: "C \<in> fundamental_group_space S x"
  shows "fundamental_group_mult S x A (fundamental_group_mult S x B C) =
    fundamental_group_mult S x (fundamental_group_mult S x A B) C"
proof -
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF A_in] by auto
  have repB: "some_loop S x B \<in> loop_space S x" "B = loop_class S x (some_loop S x B)"
    using some_loop_spec[OF B_in] by auto
  have repC: "some_loop S x C \<in> loop_space S x" "C = loop_class S x (some_loop S x C)"
    using some_loop_spec[OF C_in] by auto
  have BC_eq:
    "fundamental_group_mult S x B C =
      loop_class S x (some_loop S x B +++ some_loop S x C)"
  proof (rule fundamental_group_mult_eqI)
    show "B \<in> fundamental_group_space S x"
      by (rule B_in)
    show "C \<in> fundamental_group_space S x"
      by (rule C_in)
    show "some_loop S x B \<in> loop_space S x"
      by (rule repB(1))
    show "some_loop S x C \<in> loop_space S x"
      by (rule repC(1))
    show "B = loop_class S x (some_loop S x B)"
      by (rule repB(2))
    show "C = loop_class S x (some_loop S x C)"
      by (rule repC(2))
  qed
  have AB_eq:
    "fundamental_group_mult S x A B =
      loop_class S x (some_loop S x A +++ some_loop S x B)"
  proof (rule fundamental_group_mult_eqI)
    show "A \<in> fundamental_group_space S x"
      by (rule A_in)
    show "B \<in> fundamental_group_space S x"
      by (rule B_in)
    show "some_loop S x A \<in> loop_space S x"
      by (rule repA(1))
    show "some_loop S x B \<in> loop_space S x"
      by (rule repB(1))
    show "A = loop_class S x (some_loop S x A)"
      by (rule repA(2))
    show "B = loop_class S x (some_loop S x B)"
      by (rule repB(2))
  qed
  have join_BC: "some_loop S x B +++ some_loop S x C \<in> loop_space S x"
    using repB(1) repC(1) by (rule loop_space_join)
  have join_AB: "some_loop S x A +++ some_loop S x B \<in> loop_space S x"
    using repA(1) repB(1) by (rule loop_space_join)
  have left_eq:
    "fundamental_group_mult S x A (fundamental_group_mult S x B C) =
      loop_class S x (some_loop S x A +++ (some_loop S x B +++ some_loop S x C))"
  proof (rule fundamental_group_mult_eqI)
    show "A \<in> fundamental_group_space S x"
      by (rule A_in)
    show "fundamental_group_mult S x B C \<in> fundamental_group_space S x"
      by (rule fundamental_group_mult_in_space[OF B_in C_in])
    show "some_loop S x A \<in> loop_space S x"
      by (rule repA(1))
    show "some_loop S x B +++ some_loop S x C \<in> loop_space S x"
      by (rule join_BC)
    show "A = loop_class S x (some_loop S x A)"
      by (rule repA(2))
    show "fundamental_group_mult S x B C =
      loop_class S x (some_loop S x B +++ some_loop S x C)"
      by (rule BC_eq)
  qed
  have right_eq:
    "fundamental_group_mult S x (fundamental_group_mult S x A B) C =
      loop_class S x ((some_loop S x A +++ some_loop S x B) +++ some_loop S x C)"
  proof (rule fundamental_group_mult_eqI)
    show "fundamental_group_mult S x A B \<in> fundamental_group_space S x"
      by (rule fundamental_group_mult_in_space[OF A_in B_in])
    show "C \<in> fundamental_group_space S x"
      by (rule C_in)
    show "some_loop S x A +++ some_loop S x B \<in> loop_space S x"
      by (rule join_AB)
    show "some_loop S x C \<in> loop_space S x"
      by (rule repC(1))
    show "fundamental_group_mult S x A B =
      loop_class S x (some_loop S x A +++ some_loop S x B)"
      by (rule AB_eq)
    show "C = loop_class S x (some_loop S x C)"
      by (rule repC(2))
  qed
  have left_loop: "some_loop S x A +++ (some_loop S x B +++ some_loop S x C) \<in> loop_space S x"
    using repA(1) join_BC by (rule loop_space_join)
  have right_loop: "(some_loop S x A +++ some_loop S x B) +++ some_loop S x C \<in> loop_space S x"
    using join_AB repC(1) by (rule loop_space_join)
  have hom_assoc:
    "homotopic_paths S (some_loop S x A +++ (some_loop S x B +++ some_loop S x C))
      ((some_loop S x A +++ some_loop S x B) +++ some_loop S x C)"
    using repA(1) repB(1) repC(1)
    unfolding loop_space_def
    by (auto intro: homotopic_paths_assoc)
  have class_eq:
    "loop_class S x (some_loop S x A +++ (some_loop S x B +++ some_loop S x C)) =
      loop_class S x ((some_loop S x A +++ some_loop S x B) +++ some_loop S x C)"
    by (rule loop_class_eqI[OF left_loop right_loop hom_assoc])
  show ?thesis
    using left_eq right_eq class_eq by simp
qed

lemma fundamental_group_mult_inv_right:
  assumes "x \<in> S"
    and "A \<in> fundamental_group_space S x"
  shows "fundamental_group_mult S x A (fundamental_group_inv S x A) = fundamental_group_one S x"
proof -
  have const: "(\<lambda>_. x) \<in> loop_space S x"
    using constant_loop_in_space[OF assms(1)] .
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF assms(2)] by auto
  have loopA:
    "path (some_loop S x A)"
    "path_image (some_loop S x A) \<subseteq> S"
    "pathstart (some_loop S x A) = x"
    "pathfinish (some_loop S x A) = x"
    using repA(1) unfolding loop_space_def by auto
  have inv_eq:
    "fundamental_group_inv S x A = loop_class S x (reversepath (some_loop S x A))"
    by (rule fundamental_group_inv_eqI[OF assms(2) repA(1) repA(2)])
  have mult_eq:
    "fundamental_group_mult S x A (fundamental_group_inv S x A) =
      loop_class S x (some_loop S x A +++ reversepath (some_loop S x A))"
  proof (rule fundamental_group_mult_eqI)
    show "A \<in> fundamental_group_space S x"
      by (rule assms(2))
    show "fundamental_group_inv S x A \<in> fundamental_group_space S x"
      by (rule fundamental_group_inv_in_space[OF assms(2)])
    show "some_loop S x A \<in> loop_space S x"
      by (rule repA(1))
    show "reversepath (some_loop S x A) \<in> loop_space S x"
      by (rule loop_space_reversepath[OF repA(1)])
    show "A = loop_class S x (some_loop S x A)"
      by (rule repA(2))
    show "fundamental_group_inv S x A = loop_class S x (reversepath (some_loop S x A))"
      by (rule inv_eq)
  qed
  have join_loop: "some_loop S x A +++ reversepath (some_loop S x A) \<in> loop_space S x"
    using repA(1) loop_space_reversepath[OF repA(1)] by (rule loop_space_join)
  have hom: "homotopic_paths S (some_loop S x A +++ reversepath (some_loop S x A)) (\<lambda>_. x)"
    using homotopic_paths_rinv_const[OF loopA(1) loopA(2)] loopA(3) by simp
  have class_eq:
    "loop_class S x (some_loop S x A +++ reversepath (some_loop S x A)) = loop_class S x (\<lambda>_. x)"
    by (rule loop_class_eqI[OF join_loop const hom])
  show ?thesis
    using mult_eq class_eq unfolding fundamental_group_one_def by simp
qed

lemma fundamental_group_mult_inv_left:
  assumes "x \<in> S"
    and "A \<in> fundamental_group_space S x"
  shows "fundamental_group_mult S x (fundamental_group_inv S x A) A = fundamental_group_one S x"
proof -
  have const: "(\<lambda>_. x) \<in> loop_space S x"
    using constant_loop_in_space[OF assms(1)] .
  have repA: "some_loop S x A \<in> loop_space S x" "A = loop_class S x (some_loop S x A)"
    using some_loop_spec[OF assms(2)] by auto
  have loopA:
    "path (some_loop S x A)"
    "path_image (some_loop S x A) \<subseteq> S"
    "pathstart (some_loop S x A) = x"
    "pathfinish (some_loop S x A) = x"
    using repA(1) unfolding loop_space_def by auto
  have inv_eq:
    "fundamental_group_inv S x A = loop_class S x (reversepath (some_loop S x A))"
    by (rule fundamental_group_inv_eqI[OF assms(2) repA(1) repA(2)])
  have mult_eq:
    "fundamental_group_mult S x (fundamental_group_inv S x A) A =
      loop_class S x (reversepath (some_loop S x A) +++ some_loop S x A)"
  proof (rule fundamental_group_mult_eqI)
    show "fundamental_group_inv S x A \<in> fundamental_group_space S x"
      by (rule fundamental_group_inv_in_space[OF assms(2)])
    show "A \<in> fundamental_group_space S x"
      by (rule assms(2))
    show "reversepath (some_loop S x A) \<in> loop_space S x"
      by (rule loop_space_reversepath[OF repA(1)])
    show "some_loop S x A \<in> loop_space S x"
      by (rule repA(1))
    show "fundamental_group_inv S x A = loop_class S x (reversepath (some_loop S x A))"
      by (rule inv_eq)
    show "A = loop_class S x (some_loop S x A)"
      by (rule repA(2))
  qed
  have join_loop: "reversepath (some_loop S x A) +++ some_loop S x A \<in> loop_space S x"
    using loop_space_reversepath[OF repA(1)] repA(1) by (rule loop_space_join)
  have hom: "homotopic_paths S (reversepath (some_loop S x A) +++ some_loop S x A) (\<lambda>_. x)"
    using homotopic_paths_linv_const[OF loopA(1) loopA(2)] loopA(4) by simp
  have class_eq:
    "loop_class S x (reversepath (some_loop S x A) +++ some_loop S x A) = loop_class S x (\<lambda>_. x)"
    by (rule loop_class_eqI[OF join_loop const hom])
  show ?thesis
    using mult_eq class_eq unfolding fundamental_group_one_def by simp
qed

lemma trivial_loop_class_in_space:
  assumes "x \<in> S"
  shows "loop_class S x (\<lambda>_. x) \<in> fundamental_group_space S x"
  using constant_loop_in_space[OF assms] by (rule loop_class_in_space)

lemma fundamental_group_carrier_group:
  assumes x_in: "x \<in> S"
  shows "carrier_group
    (fundamental_group_space S x)
    (fundamental_group_mult S x)
    (fundamental_group_one S x)
    (fundamental_group_inv S x)"
proof
  show "fundamental_group_one S x \<in> fundamental_group_space S x"
    using x_in by (rule fundamental_group_one_in_space)
next
  fix A B
  assume "A \<in> fundamental_group_space S x" "B \<in> fundamental_group_space S x"
  then show "fundamental_group_mult S x A B \<in> fundamental_group_space S x"
    by (rule fundamental_group_mult_in_space)
next
  fix A
  assume "A \<in> fundamental_group_space S x"
  then show "fundamental_group_inv S x A \<in> fundamental_group_space S x"
    by (rule fundamental_group_inv_in_space)
next
  fix A B C
  assume A_in: "A \<in> fundamental_group_space S x"
    and B_in: "B \<in> fundamental_group_space S x"
    and C_in: "C \<in> fundamental_group_space S x"
  show
    "fundamental_group_mult S x (fundamental_group_mult S x A B) C =
      fundamental_group_mult S x A (fundamental_group_mult S x B C)"
    by (rule sym, rule fundamental_group_mult_assoc[OF A_in B_in C_in])
next
  fix A
  assume A_in: "A \<in> fundamental_group_space S x"
  show "fundamental_group_mult S x (fundamental_group_one S x) A = A"
    by (rule fundamental_group_mult_one_left[OF x_in A_in])
next
  fix A
  assume A_in: "A \<in> fundamental_group_space S x"
  show "fundamental_group_mult S x A (fundamental_group_one S x) = A"
    by (rule fundamental_group_mult_one_right[OF x_in A_in])
next
  fix A
  assume A_in: "A \<in> fundamental_group_space S x"
  show "fundamental_group_mult S x (fundamental_group_inv S x A) A = fundamental_group_one S x"
    by (rule fundamental_group_mult_inv_left[OF x_in A_in])
next
  fix A
  assume A_in: "A \<in> fundamental_group_space S x"
  show "fundamental_group_mult S x A (fundamental_group_inv S x A) = fundamental_group_one S x"
    by (rule fundamental_group_mult_inv_right[OF x_in A_in])
qed

lemma fundamental_group_map_carrier_group_hom:
  assumes x_in: "x \<in> S"
    and cont_h: "continuous_on S h"
    and map_h: "h \<in> S \<rightarrow> T"
    and hx: "h x = y"
  shows "carrier_group_hom
    (fundamental_group_space S x)
    (fundamental_group_mult S x)
    (fundamental_group_one S x)
    (fundamental_group_inv S x)
    (fundamental_group_space T y)
    (fundamental_group_mult T y)
    (fundamental_group_one T y)
    (fundamental_group_inv T y)
    (fundamental_group_map S x T y h)"
proof -
  have y_in: "y \<in> T"
    using x_in map_h hx by auto
  show ?thesis
  proof unfold_locales
    show "fundamental_group_one S x \<in> fundamental_group_space S x"
      by (rule fundamental_group_one_in_space[OF x_in])
  next
    fix A B
    assume A_in: "A \<in> fundamental_group_space S x"
      and B_in: "B \<in> fundamental_group_space S x"
    show "fundamental_group_mult S x A B \<in> fundamental_group_space S x"
      by (rule fundamental_group_mult_in_space[OF A_in B_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space S x"
    show "fundamental_group_inv S x A \<in> fundamental_group_space S x"
      by (rule fundamental_group_inv_in_space[OF A_in])
  next
    fix A B C
    assume A_in: "A \<in> fundamental_group_space S x"
      and B_in: "B \<in> fundamental_group_space S x"
      and C_in: "C \<in> fundamental_group_space S x"
    show "fundamental_group_mult S x (fundamental_group_mult S x A B) C =
        fundamental_group_mult S x A (fundamental_group_mult S x B C)"
      by (rule sym, rule fundamental_group_mult_assoc[OF A_in B_in C_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space S x"
    show "fundamental_group_mult S x (fundamental_group_one S x) A = A"
      by (rule fundamental_group_mult_one_left[OF x_in A_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space S x"
    show "fundamental_group_mult S x A (fundamental_group_one S x) = A"
      by (rule fundamental_group_mult_one_right[OF x_in A_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space S x"
    show "fundamental_group_mult S x (fundamental_group_inv S x A) A =
        fundamental_group_one S x"
      by (rule fundamental_group_mult_inv_left[OF x_in A_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space S x"
    show "fundamental_group_mult S x A (fundamental_group_inv S x A) =
        fundamental_group_one S x"
      by (rule fundamental_group_mult_inv_right[OF x_in A_in])
  next
    show "fundamental_group_one T y \<in> fundamental_group_space T y"
      by (rule fundamental_group_one_in_space[OF y_in])
  next
    fix A B
    assume A_in: "A \<in> fundamental_group_space T y"
      and B_in: "B \<in> fundamental_group_space T y"
    show "fundamental_group_mult T y A B \<in> fundamental_group_space T y"
      by (rule fundamental_group_mult_in_space[OF A_in B_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space T y"
    show "fundamental_group_inv T y A \<in> fundamental_group_space T y"
      by (rule fundamental_group_inv_in_space[OF A_in])
  next
    fix A B C
    assume A_in: "A \<in> fundamental_group_space T y"
      and B_in: "B \<in> fundamental_group_space T y"
      and C_in: "C \<in> fundamental_group_space T y"
    show "fundamental_group_mult T y (fundamental_group_mult T y A B) C =
        fundamental_group_mult T y A (fundamental_group_mult T y B C)"
      by (rule sym, rule fundamental_group_mult_assoc[OF A_in B_in C_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space T y"
    show "fundamental_group_mult T y (fundamental_group_one T y) A = A"
      by (rule fundamental_group_mult_one_left[OF y_in A_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space T y"
    show "fundamental_group_mult T y A (fundamental_group_one T y) = A"
      by (rule fundamental_group_mult_one_right[OF y_in A_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space T y"
    show "fundamental_group_mult T y (fundamental_group_inv T y A) A =
        fundamental_group_one T y"
      by (rule fundamental_group_mult_inv_left[OF y_in A_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space T y"
    show "fundamental_group_mult T y A (fundamental_group_inv T y A) =
        fundamental_group_one T y"
      by (rule fundamental_group_mult_inv_right[OF y_in A_in])
  next
    fix A
    assume A_in: "A \<in> fundamental_group_space S x"
    show "fundamental_group_map S x T y h A \<in> fundamental_group_space T y"
      by (rule fundamental_group_map_in_space[OF A_in cont_h map_h hx])
  next
    fix A B
    assume A_in: "A \<in> fundamental_group_space S x"
      and B_in: "B \<in> fundamental_group_space S x"
    show "fundamental_group_map S x T y h (fundamental_group_mult S x A B) =
        fundamental_group_mult T y
          (fundamental_group_map S x T y h A)
          (fundamental_group_map S x T y h B)"
      by (rule fundamental_group_map_mult[OF A_in B_in cont_h map_h hx])
  qed
qed

end
