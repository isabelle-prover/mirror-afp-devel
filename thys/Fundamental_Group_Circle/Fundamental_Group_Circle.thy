section \<open>The Fundamental Group of the Circle\<close>

theory Fundamental_Group_Circle
  imports
    "HOL-Complex_Analysis.Complex_Analysis"
    "HOL-Algebra.Group"
begin

text \<open>
  We formalise the classical result of algebraic topology that the fundamental
  group of the circle is isomorphic to the additive group of integers,
  \<open>\<pi>\<^sub>1(S\<^sup>1) \<cong> \<int>\<close>.

  The development is self-contained on top of the Isabelle distribution.  It
  models the circle as the unit sphere in the complex plane, with basepoint
  \<open>1\<close>.  Based loops are paths in the circle starting and ending at \<open>1\<close>, and the
  carrier of the fundamental group is the set of path-homotopy classes of such
  loops, with concatenation as the group operation.  The group structure is
  obtained directly from the homotopy ``groupoid'' laws in
  \<^theory>\<open>HOL-Analysis.Homotopy\<close>.

  The isomorphism with \<open>\<int>\<close> is realised by the \<^emph>\<open>degree\<close> map, which sends a
  homotopy class to the winding number of any representative loop about the
  origin.  That this is a well-defined bijective homomorphism rests on the
  classification of loops in the punctured plane up to homotopy by their
  winding number, from \<^theory>\<open>HOL-Complex_Analysis.Riemann_Mapping\<close>, together
  with a radial retraction bridging homotopies in the punctured plane and in
  the circle.

  AI assistance was used for proof engineering.  The final definitions,
  statements, and proofs are checked by Isabelle.
\<close>

subsection \<open>The circle and based loops\<close>

definition circle :: "complex set" where
  "circle = sphere 0 1"

lemma one_in_circle [simp]: "(1::complex) \<in> circle"
  by (simp add: circle_def dist_norm)

lemma zero_notin_circle [simp]: "(0::complex) \<notin> circle"
  by (simp add: circle_def)

lemma circle_subset_punctured: "circle \<subseteq> - {0}"
  by (auto simp: circle_def)

lemma norm_of_circle: "z \<in> circle \<Longrightarrow> norm z = 1"
  by (simp add: circle_def dist_norm)

text \<open>A (based) loop is a path in the circle starting and finishing at \<open>1\<close>.\<close>

definition is_loop :: "(real \<Rightarrow> complex) \<Rightarrow> bool" where
  "is_loop p \<longleftrightarrow> path p \<and> path_image p \<subseteq> circle \<and> pathstart p = 1 \<and> pathfinish p = 1"

lemma is_loop_path: "is_loop p \<Longrightarrow> path p"
  by (simp add: is_loop_def)

lemma is_loop_image: "is_loop p \<Longrightarrow> path_image p \<subseteq> circle"
  by (simp add: is_loop_def)

lemma is_loop_pathstart: "is_loop p \<Longrightarrow> pathstart p = 1"
  by (simp add: is_loop_def)

lemma is_loop_pathfinish: "is_loop p \<Longrightarrow> pathfinish p = 1"
  by (simp add: is_loop_def)

lemma is_loop_selfloop: "is_loop p \<Longrightarrow> pathfinish p = pathstart p"
  by (simp add: is_loop_def)

lemma is_loop_connect: "\<lbrakk>is_loop p; is_loop q\<rbrakk> \<Longrightarrow> pathfinish p = pathstart q"
  by (simp add: is_loop_def)

lemma is_loop_zero_notin_image: "is_loop p \<Longrightarrow> 0 \<notin> path_image p"
  using is_loop_image zero_notin_circle by blast

lemma is_loop_linepath_1 [simp]: "is_loop (linepath 1 1)"
  by (auto simp: is_loop_def path_image_linepath)

lemma is_loop_join [simp]:
  assumes "is_loop p" and "is_loop q"
  shows "is_loop (p +++ q)"
proof -
  from assms(1) have p: "path p" "path_image p \<subseteq> circle" "pathstart p = 1" "pathfinish p = 1"
    by (simp_all add: is_loop_def)
  from assms(2) have q: "path q" "path_image q \<subseteq> circle" "pathstart q = 1" "pathfinish q = 1"
    by (simp_all add: is_loop_def)
  have fs: "pathfinish p = pathstart q" using p(4) q(3) by simp
  have "path (p +++ q)" using p(1) q(1) fs by (rule path_join_imp)
  moreover have "path_image (p +++ q) \<subseteq> circle"
    using fs p(2) q(2) by (simp add: path_image_join)
  moreover have "pathstart (p +++ q) = 1" using p(3) by simp
  moreover have "pathfinish (p +++ q) = 1" using q(4) by simp
  ultimately show ?thesis by (simp add: is_loop_def)
qed

lemma is_loop_reversepath [simp]:
  assumes "is_loop p"
  shows "is_loop (reversepath p)"
  using assms by (simp add: is_loop_def)

subsection \<open>Homotopy classes of loops\<close>

definition loop_class :: "(real \<Rightarrow> complex) \<Rightarrow> (real \<Rightarrow> complex) set" where
  "loop_class p = {q. is_loop q \<and> homotopic_paths circle p q}"

definition loops_carrier :: "(real \<Rightarrow> complex) set set" where
  "loops_carrier = {loop_class p |p. is_loop p}"

definition rep :: "(real \<Rightarrow> complex) set \<Rightarrow> (real \<Rightarrow> complex)" where
  "rep A = (SOME p. is_loop p \<and> A = loop_class p)"

lemma in_loop_class: "is_loop p \<Longrightarrow> p \<in> loop_class p"
  by (simp add: loop_class_def homotopic_paths_refl is_loop_path is_loop_image)

lemma loop_class_eqI:
  assumes "is_loop p" "is_loop q" "homotopic_paths circle p q"
  shows "loop_class p = loop_class q"
proof -
  have "homotopic_paths circle p r = homotopic_paths circle q r" for r
    using assms(3)
    by (meson homotopic_paths_sym homotopic_paths_trans)
  then show ?thesis
    by (auto simp: loop_class_def)
qed

lemma loop_class_eq_iff:
  assumes "is_loop p" "is_loop q"
  shows "loop_class p = loop_class q \<longleftrightarrow> homotopic_paths circle p q"
proof
  assume "loop_class p = loop_class q"
  then have "q \<in> loop_class p"
    using in_loop_class[OF assms(2)] by simp
  then show "homotopic_paths circle p q"
    by (simp add: loop_class_def)
next
  assume "homotopic_paths circle p q"
  with assms show "loop_class p = loop_class q"
    by (rule loop_class_eqI)
qed

lemma loop_class_in_carrier [simp]: "is_loop p \<Longrightarrow> loop_class p \<in> loops_carrier"
  by (auto simp: loops_carrier_def)

lemma rep_props:
  assumes "A \<in> loops_carrier"
  shows "is_loop (rep A) \<and> loop_class (rep A) = A"
proof -
  from assms obtain p where "is_loop p \<and> A = loop_class p"
    by (auto simp: loops_carrier_def)
  then have "\<exists>p. is_loop p \<and> A = loop_class p" by blast
  then have "is_loop (rep A) \<and> A = loop_class (rep A)"
    unfolding rep_def by (rule someI_ex)
  then show ?thesis by auto
qed

lemma is_loop_rep: "A \<in> loops_carrier \<Longrightarrow> is_loop (rep A)"
  using rep_props by blast

lemma loop_class_rep: "A \<in> loops_carrier \<Longrightarrow> loop_class (rep A) = A"
  using rep_props by blast

subsection \<open>The fundamental group of the circle\<close>

definition pi1_circle :: "(real \<Rightarrow> complex) set monoid" where
  "pi1_circle =
     \<lparr> carrier = loops_carrier,
       mult = (\<lambda>A B. loop_class (rep A +++ rep B)),
       one = loop_class (linepath 1 1) \<rparr>"

lemma carrier_pi1 [simp]: "carrier pi1_circle = loops_carrier"
  by (simp add: pi1_circle_def)

lemma one_pi1 [simp]: "\<one>\<^bsub>pi1_circle\<^esub> = loop_class (linepath 1 1)"
  by (simp add: pi1_circle_def)

text \<open>Multiplication of classes is concatenation, independent of representatives.\<close>

lemma pi1_mult_class:
  assumes p: "is_loop p" and q: "is_loop q"
  shows "loop_class p \<otimes>\<^bsub>pi1_circle\<^esub> loop_class q = loop_class (p +++ q)"
proof -
  let ?rp = "rep (loop_class p)" and ?rq = "rep (loop_class q)"
  have lp: "is_loop ?rp" and cp: "loop_class ?rp = loop_class p"
    using rep_props[OF loop_class_in_carrier[OF p]] by auto
  have lq: "is_loop ?rq" and cq: "loop_class ?rq = loop_class q"
    using rep_props[OF loop_class_in_carrier[OF q]] by auto
  have hp: "homotopic_paths circle ?rp p"
    using loop_class_eq_iff[OF lp p] cp by simp
  have hq: "homotopic_paths circle ?rq q"
    using loop_class_eq_iff[OF lq q] cq by simp
  have "homotopic_paths circle (?rp +++ ?rq) (p +++ q)"
    using hp hq is_loop_connect[OF lp lq] by (intro homotopic_paths_join) simp_all
  then have "loop_class (?rp +++ ?rq) = loop_class (p +++ q)"
    by (rule loop_class_eqI[OF is_loop_join[OF lp lq] is_loop_join[OF p q]])
  then show ?thesis
    by (simp add: pi1_circle_def)
qed

lemma group_pi1_circle: "group pi1_circle"
proof (rule groupI)
  fix x y assume "x \<in> carrier pi1_circle" "y \<in> carrier pi1_circle"
  then obtain p q where "is_loop p" "x = loop_class p" "is_loop q" "y = loop_class q"
    by (auto simp: loops_carrier_def)
  then show "x \<otimes>\<^bsub>pi1_circle\<^esub> y \<in> carrier pi1_circle"
    by (simp add: pi1_mult_class)
next
  show "\<one>\<^bsub>pi1_circle\<^esub> \<in> carrier pi1_circle"
    by simp
next
  fix x y z
  assume "x \<in> carrier pi1_circle" "y \<in> carrier pi1_circle" "z \<in> carrier pi1_circle"
  then obtain p q r
    where L: "is_loop p" "is_loop q" "is_loop r"
      and X: "x = loop_class p" "y = loop_class q" "z = loop_class r"
    by (auto simp: loops_carrier_def)
  have lhs: "(x \<otimes>\<^bsub>pi1_circle\<^esub> y) \<otimes>\<^bsub>pi1_circle\<^esub> z = loop_class ((p +++ q) +++ r)"
    using L X by (simp add: pi1_mult_class)
  have rhs: "x \<otimes>\<^bsub>pi1_circle\<^esub> (y \<otimes>\<^bsub>pi1_circle\<^esub> z) = loop_class (p +++ (q +++ r))"
    using L X by (simp add: pi1_mult_class)
  have "homotopic_paths circle (p +++ (q +++ r)) ((p +++ q) +++ r)"
    using L is_loop_connect[OF L(1) L(2)] is_loop_connect[OF L(2) L(3)]
    by (intro homotopic_paths_assoc) (simp_all add: is_loop_path is_loop_image)
  then have "loop_class (p +++ (q +++ r)) = loop_class ((p +++ q) +++ r)"
    by (rule loop_class_eqI[OF is_loop_join[OF L(1) is_loop_join[OF L(2) L(3)]]
                              is_loop_join[OF is_loop_join[OF L(1) L(2)] L(3)]])
  with lhs rhs
  show "(x \<otimes>\<^bsub>pi1_circle\<^esub> y) \<otimes>\<^bsub>pi1_circle\<^esub> z = x \<otimes>\<^bsub>pi1_circle\<^esub> (y \<otimes>\<^bsub>pi1_circle\<^esub> z)"
    by simp
next
  fix x assume "x \<in> carrier pi1_circle"
  then obtain p where p: "is_loop p" and X: "x = loop_class p"
    by (auto simp: loops_carrier_def)
  have "homotopic_paths circle (linepath 1 1 +++ p) p"
    using p is_loop_pathstart[OF p]
    by (intro homotopic_paths_lid') (simp_all add: is_loop_path is_loop_image)
  then have "loop_class (linepath 1 1 +++ p) = loop_class p"
    by (rule loop_class_eqI[OF is_loop_join[OF is_loop_linepath_1 p] p])
  then show "\<one>\<^bsub>pi1_circle\<^esub> \<otimes>\<^bsub>pi1_circle\<^esub> x = x"
    using p X by (simp add: pi1_mult_class)
next
  fix x assume "x \<in> carrier pi1_circle"
  then obtain p where p: "is_loop p" and X: "x = loop_class p"
    by (auto simp: loops_carrier_def)
  have "homotopic_paths circle (reversepath p +++ p) (linepath 1 1)"
    using p homotopic_paths_linv[of p circle] is_loop_pathfinish[OF p]
    by (simp add: is_loop_path is_loop_image)
  then have "loop_class (reversepath p +++ p) = loop_class (linepath 1 1)"
    by (rule loop_class_eqI[OF is_loop_join[OF is_loop_reversepath[OF p] p] is_loop_linepath_1])
  then have "loop_class (reversepath p) \<otimes>\<^bsub>pi1_circle\<^esub> x = \<one>\<^bsub>pi1_circle\<^esub>"
    using p X by (simp add: pi1_mult_class)
  moreover have "loop_class (reversepath p) \<in> carrier pi1_circle"
    using p by simp
  ultimately
  show "\<exists>y \<in> carrier pi1_circle. y \<otimes>\<^bsub>pi1_circle\<^esub> x = \<one>\<^bsub>pi1_circle\<^esub>"
    by blast
qed

subsection \<open>The integers as a group\<close>

definition integer_group :: "int monoid" where
  "integer_group = \<lparr> carrier = UNIV, mult = (+), one = 0 \<rparr>"

lemma carrier_integer_group [simp]: "carrier integer_group = UNIV"
  by (simp add: integer_group_def)

lemma mult_integer_group [simp]: "x \<otimes>\<^bsub>integer_group\<^esub> y = x + y"
  by (simp add: integer_group_def)

lemma one_integer_group [simp]: "\<one>\<^bsub>integer_group\<^esub> = 0"
  by (simp add: integer_group_def)

lemma group_integer_group: "group integer_group"
proof (rule groupI)
  fix x assume "x \<in> carrier integer_group"
  show "\<exists>y \<in> carrier integer_group. y \<otimes>\<^bsub>integer_group\<^esub> x = \<one>\<^bsub>integer_group\<^esub>"
    by (rule bexI[of _ "- x"]) simp_all
qed simp_all

subsection \<open>The winding-number degree\<close>

definition wnd :: "(real \<Rightarrow> complex) \<Rightarrow> int" where
  "wnd p = (SOME n. winding_number p 0 = of_int n)"

lemma wnd_eq:
  assumes "is_loop p"
  shows "winding_number p 0 = of_int (wnd p)"
proof -
  have "winding_number p 0 \<in> \<int>"
    using is_loop_path[OF assms] is_loop_selfloop[OF assms] is_loop_zero_notin_image[OF assms]
    by (intro integer_winding_number) simp_all
  then have "\<exists>n. winding_number p 0 = of_int n"
    by (auto simp: Ints_def)
  then show ?thesis
    unfolding wnd_def by (rule someI_ex)
qed

lemma wnd_join:
  assumes "is_loop p" "is_loop q"
  shows "wnd (p +++ q) = wnd p + wnd q"
proof -
  have "winding_number (p +++ q) 0 = winding_number p 0 + winding_number q 0"
    using is_loop_path[OF assms(1)] is_loop_path[OF assms(2)]
      is_loop_zero_notin_image[OF assms(1)] is_loop_zero_notin_image[OF assms(2)]
      is_loop_connect[OF assms(1) assms(2)]
    by (intro winding_number_join) simp_all
  also have "\<dots> = of_int (wnd p + wnd q)"
    using assms by (simp add: wnd_eq)
  finally have "winding_number (p +++ q) 0 = of_int (wnd p + wnd q)" .
  moreover have "winding_number (p +++ q) 0 = of_int (wnd (p +++ q))"
    using assms by (simp add: wnd_eq)
  ultimately show ?thesis
    by (metis of_int_eq_iff)
qed

lemma wnd_reversepath:
  assumes "is_loop p"
  shows "wnd (reversepath p) = - wnd p"
proof -
  have "winding_number (reversepath p) 0 = - winding_number p 0"
    using assms is_loop_zero_notin_image
    by (simp add: winding_number_reversepath is_loop_path)
  also have "\<dots> = of_int (- wnd p)"
    using assms by (simp add: wnd_eq)
  finally have "winding_number (reversepath p) 0 = of_int (- wnd p)" .
  moreover have "winding_number (reversepath p) 0 = of_int (wnd (reversepath p))"
    using assms by (simp add: wnd_eq)
  ultimately show ?thesis
    by (metis of_int_eq_iff)
qed

lemma wnd_linepath_1: "wnd (linepath 1 1) = 0"
proof -
  have "winding_number (linepath 1 1) (0::complex) = 0"
    by (simp add: winding_number_trivial)
  moreover have "winding_number (linepath 1 1) (0::complex) = of_int (wnd (linepath 1 1))"
    by (simp add: wnd_eq)
  ultimately show ?thesis by simp
qed

lemma wnd_homotopic:
  assumes "is_loop p" "is_loop q" "homotopic_paths circle p q"
  shows "wnd p = wnd q"
proof -
  have "homotopic_paths (- {0}) p q"
    using assms(3) circle_subset_punctured by (rule homotopic_paths_subset)
  moreover have
    "(winding_number p 0 = winding_number q 0) = homotopic_paths (- {0}) p q"
    using is_loop_path[OF assms(1)] is_loop_path[OF assms(2)]
      is_loop_zero_notin_image[OF assms(1)] is_loop_zero_notin_image[OF assms(2)]
      is_loop_pathstart[OF assms(1)] is_loop_pathstart[OF assms(2)]
      is_loop_pathfinish[OF assms(1)] is_loop_pathfinish[OF assms(2)]
    by (intro winding_number_homotopic_paths_eq) simp_all
  ultimately have "winding_number p 0 = winding_number q 0" by simp
  then have "of_int (wnd p) = of_int (wnd q)"
    using assms by (simp add: wnd_eq)
  then show ?thesis by (metis of_int_eq_iff)
qed

definition deg :: "(real \<Rightarrow> complex) set \<Rightarrow> int" where
  "deg A = wnd (rep A)"

lemma deg_class:
  assumes "is_loop p"
  shows "deg (loop_class p) = wnd p"
proof -
  have A: "loop_class p \<in> loops_carrier"
    using assms by simp
  have lr: "is_loop (rep (loop_class p))"
    and cr: "loop_class (rep (loop_class p)) = loop_class p"
    using rep_props[OF A] by auto
  have hom: "homotopic_paths circle (rep (loop_class p)) p"
    using loop_class_eq_iff[OF lr assms] cr by simp
  have "wnd (rep (loop_class p)) = wnd p"
    by (rule wnd_homotopic[OF lr assms hom])
  then show ?thesis
    by (simp add: deg_def)
qed

subsection \<open>The degree is a homomorphism\<close>

lemma deg_mult:
  assumes "A \<in> loops_carrier" "B \<in> loops_carrier"
  shows "deg (A \<otimes>\<^bsub>pi1_circle\<^esub> B) = deg A + deg B"
proof -
  from assms obtain p q
    where p: "is_loop p" "A = loop_class p" and q: "is_loop q" "B = loop_class q"
    by (auto simp: loops_carrier_def)
  have "deg (A \<otimes>\<^bsub>pi1_circle\<^esub> B) = deg (loop_class (p +++ q))"
    using p q by (simp add: pi1_mult_class)
  also have "\<dots> = wnd (p +++ q)"
    using p q by (simp add: deg_class)
  also have "\<dots> = wnd p + wnd q"
    using p q by (simp add: wnd_join)
  also have "\<dots> = deg A + deg B"
    using p q by (simp add: deg_class)
  finally show ?thesis .
qed

lemma deg_hom: "deg \<in> hom pi1_circle integer_group"
  by (rule homI) (simp_all add: deg_mult)

subsection \<open>The degree is injective\<close>

text \<open>
  A radial retraction of the punctured plane onto the circle.  It fixes the
  circle pointwise and lets us transfer a homotopy in the punctured plane back
  into the circle.
\<close>

definition retr :: "complex \<Rightarrow> complex" where
  "retr z = z / of_real (norm z)"

lemma retr_fixes: "z \<in> circle \<Longrightarrow> retr z = z"
  by (simp add: retr_def norm_of_circle)

lemma continuous_on_retr: "continuous_on (- {0}) retr"
  unfolding retr_def by (intro continuous_intros) auto

lemma retr_into_circle: "retr \<in> (- {0}) \<rightarrow> circle"
proof
  fix z :: complex assume "z \<in> - {0}"
  then have "z \<noteq> 0" by simp
  then have "norm (retr z) = 1"
    by (simp add: retr_def norm_divide)
  then show "retr z \<in> circle"
    by (simp add: circle_def dist_norm)
qed

lemma homotopic_paths_retr_self:
  assumes "is_loop p"
  shows "homotopic_paths circle p (retr \<circ> p)"
proof (rule homotopic_paths_eq)
  show "path p" using assms by (rule is_loop_path)
  show "path_image p \<subseteq> circle" using assms by (rule is_loop_image)
  fix t :: real assume "t \<in> {0..1}"
  then have "p t \<in> path_image p"
    by (auto simp: path_image_def)
  then have "p t \<in> circle" using assms is_loop_image by blast
  then show "p t = (retr \<circ> p) t"
    by (simp add: retr_fixes)
qed

lemma deg_inj: "inj_on deg (carrier pi1_circle)"
proof (rule inj_onI)
  fix A B
  assume "A \<in> carrier pi1_circle" "B \<in> carrier pi1_circle" and eq: "deg A = deg B"
  then obtain p q
    where p: "is_loop p" "A = loop_class p" and q: "is_loop q" "B = loop_class q"
    by (auto simp: loops_carrier_def)
  from eq p q have "wnd p = wnd q"
    by (simp add: deg_class)
  then have "winding_number p 0 = winding_number q 0"
    using p q by (simp add: wnd_eq)
  moreover have
    "(winding_number p 0 = winding_number q 0) = homotopic_paths (- {0}) p q"
    using is_loop_path[OF p(1)] is_loop_path[OF q(1)]
      is_loop_zero_notin_image[OF p(1)] is_loop_zero_notin_image[OF q(1)]
      is_loop_pathstart[OF p(1)] is_loop_pathstart[OF q(1)]
      is_loop_pathfinish[OF p(1)] is_loop_pathfinish[OF q(1)]
    by (intro winding_number_homotopic_paths_eq) simp_all
  ultimately have punct: "homotopic_paths (- {0}) p q" by simp
  have "homotopic_paths circle (retr \<circ> p) (retr \<circ> q)"
    by (rule homotopic_paths_continuous_image[OF punct continuous_on_retr retr_into_circle])
  moreover have "homotopic_paths circle p (retr \<circ> p)"
    using p(1) by (rule homotopic_paths_retr_self)
  moreover have "homotopic_paths circle q (retr \<circ> q)"
    using q(1) by (rule homotopic_paths_retr_self)
  ultimately have "homotopic_paths circle p q"
    by (meson homotopic_paths_sym homotopic_paths_trans)
  then have "loop_class p = loop_class q"
    by (rule loop_class_eqI[OF p(1) q(1)])
  then show "A = B"
    using p q by simp
qed

subsection \<open>The degree is surjective\<close>

lemma is_loop_circlepath: "is_loop (circlepath 0 1)"
  by (simp add: is_loop_def circle_def)

lemma wnd_circlepath: "wnd (circlepath 0 1) = 1"
proof -
  have "winding_number (circlepath 0 1) 0 = 1"
    by (simp add: winding_number_circlepath)
  moreover have "winding_number (circlepath 0 1) 0 = of_int (wnd (circlepath 0 1))"
    using is_loop_circlepath by (simp add: wnd_eq)
  ultimately show ?thesis by simp
qed

text \<open>The \<open>n\<close>-fold concatenation of the standard circle loop.\<close>

fun cpow :: "nat \<Rightarrow> (real \<Rightarrow> complex)" where
  "cpow 0 = linepath 1 1"
| "cpow (Suc n) = circlepath 0 1 +++ cpow n"

lemma is_loop_cpow: "is_loop (cpow n)"
proof (induction n)
  case 0
  show ?case unfolding cpow.simps(1) by (rule is_loop_linepath_1)
next
  case (Suc n)
  then show ?case by (simp add: is_loop_circlepath)
qed

lemma wnd_cpow: "wnd (cpow n) = int n"
proof (induction n)
  case 0
  have "wnd (cpow 0) = 0" unfolding cpow.simps(1) by (rule wnd_linepath_1)
  then show ?case by (simp del: cpow.simps)
next
  case (Suc n)
  have "wnd (cpow (Suc n)) = wnd (circlepath 0 1) + wnd (cpow n)"
    by (simp add: wnd_join is_loop_circlepath is_loop_cpow)
  also have "\<dots> = int (Suc n)"
    by (simp add: wnd_circlepath Suc.IH)
  finally show ?case .
qed

lemma deg_surj: "deg ` carrier pi1_circle = UNIV"
proof -
  have surj: "\<exists>A \<in> carrier pi1_circle. deg A = n" for n :: int
  proof (cases "n \<ge> 0")
    case True
    have "deg (loop_class (cpow (nat n))) = int (nat n)"
      by (simp add: deg_class is_loop_cpow wnd_cpow)
    also have "\<dots> = n" using True by simp
    finally show ?thesis
      using is_loop_cpow by (metis carrier_pi1 loop_class_in_carrier)
  next
    case False
    let ?p = "reversepath (cpow (nat (- n)))"
    have loop: "is_loop ?p"
      by (simp add: is_loop_cpow)
    have "deg (loop_class ?p) = wnd ?p"
      using loop by (simp add: deg_class)
    also have "\<dots> = - int (nat (- n))"
      by (simp add: wnd_reversepath is_loop_cpow wnd_cpow)
    also have "\<dots> = n" using False by simp
    finally show ?thesis
      using loop by (metis carrier_pi1 loop_class_in_carrier)
  qed
  show ?thesis
    using surj by (metis UNIV_eq_I image_eqI)
qed

subsection \<open>The fundamental theorem\<close>

theorem pi1_circle_iso_integers: "pi1_circle \<cong> integer_group"
proof -
  have "deg \<in> iso pi1_circle integer_group"
  proof (rule isoI)
    show "deg \<in> hom pi1_circle integer_group"
      by (rule deg_hom)
    show "bij_betw deg (carrier pi1_circle) (carrier integer_group)"
      using deg_inj deg_surj by (simp add: bij_betw_def)
  qed
  then show ?thesis
    by (rule is_isoI)
qed

theorem group_hom_deg: "group_hom pi1_circle integer_group deg"
  by (simp add: group_hom_def group_hom_axioms_def
      group_pi1_circle group_integer_group deg_hom)

end
