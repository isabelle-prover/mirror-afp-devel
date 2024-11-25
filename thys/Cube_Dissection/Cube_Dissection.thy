theory Cube_Dissection
  imports Complex_Main "HOL-Library.Disjoint_Sets" "HOL-Library.Infinite_Set"
begin

text "Proof that a cube can't be dissected into a finite number of subcubes of different size
This formalization is heavily inspired by the Lean proof of the same fact,  \<^cite>\<open>leanproof\<close>.
One goal of this project, is that by restricting to cubes of dimension 3 the logic will
be easier to follow"

section "Basic definitions"
subsection "point and cube definitions"
record point = px:: real py::real pz::real
record cube = point:: point width::real
datatype axis = x | y | z
abbreviation "coordinate \<equiv> case_axis px py pz"

abbreviation is_valid :: "cube \<Rightarrow> bool" where "is_valid c \<equiv> (width c > 0)"

text "Min value of cube along given axis"
hide_const (open) min
abbreviation min :: "axis \<Rightarrow> cube \<Rightarrow> real" where "min ax c \<equiv> coordinate ax (point c)"

text "Max value (supremum) along given axis"
hide_const (open) max
abbreviation max :: "axis \<Rightarrow> cube \<Rightarrow> real" where "max ax c \<equiv> min ax c  + width c"

text "Sides of a cube. Half-open intervals, so that a dissection both is a cover, and consists of disjoint cubes"
abbreviation side :: "axis \<Rightarrow> cube \<Rightarrow> real set" where
  "side ax c \<equiv> {min ax c ..< max ax c}"

text "Sets of points generated from cubes"
definition to_set :: "cube \<Rightarrow> point set" where
  "to_set c = {p. px p \<in> side x c \<and> py p \<in> side y c \<and> pz p \<in> side z c}"
definition bot :: "cube \<Rightarrow> point set" where
  "bot c = {p. px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = min z c}"
definition top :: "cube \<Rightarrow> point set" where
  "top c = {p. px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = max z c}"

text "Moves a cube its width down (so top face to bottom face)"
definition shift_down :: "cube \<Rightarrow> cube" where 
  "shift_down c = c \<lparr> point := point c \<lparr> pz := min z c - width c  \<rparr> \<rparr>"


subsection "Calculations with sets from cubes"
text "A bunch of statements we need about how cubes can be compared by \<^term>\<open>side\<close>"
lemma top_shift_down_eq_bot: "top (shift_down c) = bot c"
  unfolding top_def bot_def shift_down_def by simp

text "Sets not empty"
lemma non_empty: "is_valid c \<Longrightarrow> to_set c \<noteq> {}"
  unfolding to_set_def by force
lemma top_non_empty: "is_valid c \<Longrightarrow> top c \<noteq> {}"
  unfolding top_def by (auto intro!: exI[of _ "point c \<lparr> pz := max z c \<rparr>"])

text "\<^term>\<open>min\<close> of a cube is in corresponding \<^term>\<open>side\<close>"
lemma min_in_side: "is_valid c \<Longrightarrow> min ax c \<in> side ax c"
  by simp

lemma min_ne_max: "is_valid c \<Longrightarrow> min ax c \<noteq> max ax c"
  by simp
lemma min_lt_max: "is_valid c \<Longrightarrow> min ax c < max ax c"
  by simp

lemma bot_subset: "bot c \<subseteq> to_set c"
  unfolding bot_def to_set_def by(auto)


subsubsection "Point membership"
text "Points in a cube's set, by looking at membership of \<^term>\<open>side\<close>"
lemma in_set_by_side: "p \<in> to_set c \<longleftrightarrow>
  px p \<in> side x c \<and> py p \<in> side y c \<and> pz p \<in> side z c"
  by(cases p, simp add: to_set_def)
lemma in_set_by_side_2: "\<lparr>px=x0, py=y0, pz=z0\<rparr> \<in> to_set c \<longleftrightarrow>
  x0 \<in> side x c \<and> y0 \<in> side y c \<and> z0 \<in> side z c"
  by(simp add: to_set_def)

lemma in_bot_by_side: "p \<in> bot c \<longleftrightarrow>
  px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = min z c"
  by(simp add: bot_def)
lemma in_bot_by_side_2: "\<lparr>px=x0, py=y0, pz=z0\<rparr> \<in> bot c \<longleftrightarrow>
  x0 \<in> side x c \<and> y0 \<in> side y c \<and> z0 = min z c"
  by(simp add: in_bot_by_side)

lemma in_top_by_side: "p \<in> top c \<longleftrightarrow>
  px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = max z c"
  by(cases p, auto simp add: top_def)
lemma in_top_by_side_2: "\<lparr>px=x0, py=y0, pz=z0\<rparr> \<in> top c \<longleftrightarrow>
  x0 \<in> side x c \<and> y0 \<in> side y c \<and> z0 = max z c"
  by(simp add: top_def)

lemma all_point_iff: "(\<forall>p. P p) \<longleftrightarrow> (\<forall>x1 y1 z1. P \<lparr>px = x1, py = y1, pz = z1\<rparr>)"
  by (metis point.cases)

text "Intersection by \<^term>\<open>side\<close>"
lemma set_intersect_by_side: "to_set c1 \<inter> to_set c2 \<noteq> {} \<longleftrightarrow>
  side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> side z c1 \<inter> side z c2 \<noteq> {}"
  unfolding set_eq_iff all_point_iff using in_set_by_side_2 by blast

lemma bot_intersect_by_side: "bot c1 \<inter> bot c2 \<noteq> {} 
  \<longleftrightarrow> side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = min z c2"
proof(intro iffI)
  assume "bot c1 \<inter> bot c2 \<noteq> {}"
  thus  "side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = min z c2" 
    using in_bot_by_side by fastforce
next
  assume "side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = min z c2" 
  thus "bot c1 \<inter> bot c2 \<noteq> {}" using in_bot_by_side_2 by blast
qed

lemma bot_top_intersect_by_side: "bot c1 \<inter> top c2 \<noteq> {} 
  \<longleftrightarrow> side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = max z c2"
proof(intro iffI)
  assume "bot c1 \<inter> top c2 \<noteq> {}"
  thus  "side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = max z c2" 
    using in_bot_by_side in_top_by_side by fastforce
next
  assume "side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = max z c2" 
  thus "bot c1 \<inter> top c2 \<noteq> {}" using in_bot_by_side_2 in_top_by_side_2 by blast
qed


subsubsection "Cubes subset of each other, by \<^term>\<open>side\<close>"
lemma set_subset_by_side: "to_set c1 \<subseteq> to_set c2 \<longleftrightarrow>
  side x c1 \<subseteq> side x c2 \<and> side y c1 \<subseteq> side y c2 \<and> side z c1 \<subseteq> side z c2"
  unfolding subset_eq Ball_def all_point_iff in_set_by_side by fastforce
lemma set_eq_by_side: "to_set c1 = to_set c2 \<longleftrightarrow>
  side x c1 = side x c2 \<and> side y c1 = side y c2 \<and> side z c1 = side z c2"
  using set_subset_by_side by fast

lemma bot_eq_by_side: "is_valid c1 \<Longrightarrow> bot c1 = bot c2 \<longleftrightarrow>
side x c1 = side x c2 \<and> side y c1 = side y c2 \<and> min z c1 = min z c2"
  unfolding bot_def set_eq_iff all_point_iff by fastforce


lemma bot_top_subset_by_side: "is_valid c1 \<Longrightarrow> bot c1 \<subseteq> top c2 \<longleftrightarrow>
side x c1 \<subseteq> side x c2 \<and> side y c1 \<subseteq> side y c2 \<and> min z c1 = max z c2"
  unfolding top_def bot_def subset_eq Ball_def all_point_iff by fastforce
lemma bot_top_eq_by_side: "is_valid c1 \<Longrightarrow> bot c1 = top c2 \<longleftrightarrow>
side x c1 = side x c2 \<and> side y c1 = side y c2 \<and> min z c1 = max z c2"
  unfolding top_def bot_def set_eq_iff Ball_def all_point_iff by fastforce

lemma width_eq_if_side_eq: "\<lbrakk>is_valid c1; side ax c1 = side ax c2\<rbrakk> \<Longrightarrow> width c1 = width c2"
  by(simp add:Ico_eq_Ico)

text "\<^term>\<open>to_set\<close> is injective"
lemma to_set_inj: 
  assumes "is_valid c1" "to_set c1 = to_set c2" 
  shows "c1 = c2"
proof -
  from assms(2) have *: "side x c1 = side x c2" "side y c1 = side y c2" "side z c1 = side z c2" 
    by(metis set_eq_by_side)+
  hence "min x c1 = min x c2" "min y c1 = min y c2" "min z c1 = min z c2"
    by(meson assms(1) Ico_eq_Ico less_add_same_cancel1)+
  hence "point c1 = point c2" by simp
  moreover from * have "width c1 = width c2" by(metis assms(1) width_eq_if_side_eq)
  ultimately show "c1 = c2" by simp
qed

text "\<^term>\<open>bot\<close> is also injective"
lemma bot_inj: assumes "is_valid c1" "bot c1 = bot c2" shows "c1 = c2"
proof -
  from assms have "width c1 = width c2" by(metis assms bot_eq_by_side width_eq_if_side_eq)
  hence "to_set c1 = to_set c2" using assms bot_eq_by_side set_eq_by_side by auto
  thus "c1 = c2" by(metis assms(1) to_set_inj)
qed


section "Cubing"
text "We in this section introduce a dissection C of the unit cube"

text "The cube we show there is no dissection of"
definition unit_cube where "unit_cube = \<lparr> point=\<lparr>px=0, py=0, pz=0\<rparr>, width=1\<rparr>"

lemma min_unit_cube_0: "min ax unit_cube = 0"
  by(metis unit_cube_def axis.exhaust axis.simps(7-9) cube.select_convs(1) point.select_convs(1-3))

lemma unit_cube_valid[simp]: "is_valid unit_cube"
  by(simp add: unit_cube_def)

text "What we want to show doesn't exist. \<^term>\<open>C\<close> is a set of cubes which satisfy:
\<^enum> All cubes are valid (width > 0)
\<^enum> All cubes a disjoint
\<^enum> The union of the cubes in \<^term>\<open>C\<close> equal \<^term>\<open>unit_cube\<close> (hence, all cubes are contained in \<^term>\<open>unit_cube\<close>)
\<^enum> All cubes in \<^term>\<open>C\<close> have different width
\<^enum> There are at least two cubes in \<^term>\<open>C\<close>
\<^enum> There are a finite number of cubes in \<^term>\<open>C\<close>"
definition is_dissection :: "cube set \<Rightarrow> bool" where
  "is_dissection C \<longleftrightarrow> 
  (\<forall> c \<in> C. is_valid c)
  \<and> disjoint (image to_set C)
  \<and> \<Union>(image to_set C) = to_set unit_cube
  \<and> inj_on width C \<comment> \<open>All cubes are of different size\<close>
  \<and> card C \<ge> 2  \<comment> \<open>At least two cubes\<close>
  \<and> finite C"

text "From now on, C is some fixed dissection of \<^term>\<open>unit_cube\<close>, and 'dissection' refers to this fact" 
context fixes C assumes dissection: "is_dissection C"
begin

subsection "Properties of \<^term>\<open>is_dissection\<close>"
lemma valid_if_dissection[simp]: "c \<in> C \<Longrightarrow> is_valid c"
  using dissection unfolding is_dissection_def by fast 

lemma side_unit_cube: 
  "side ax unit_cube = {0..<1}"
  by(metis add.commute add.right_neutral cube.select_convs(2) min_unit_cube_0 unit_cube_def)

lemma subset_unit_cube_if_dissection: "c \<in> C \<Longrightarrow> to_set c \<subseteq> to_set unit_cube"
  using dissection unfolding is_dissection_def to_set_def by fast

lemma subset_unit_cube_by_side:
  "c \<in> C \<Longrightarrow> side ax c \<subseteq> {0..<1}"
  by(metis(full_types)subset_unit_cube_if_dissection set_subset_by_side side_unit_cube axis.exhaust)

lemma eq_iff_intersect: "\<lbrakk>c1 \<in> C; c2 \<in> C\<rbrakk> \<Longrightarrow> c1 = c2 \<longleftrightarrow> to_set c1 \<inter> to_set c2 \<noteq> {}"
  using dissection unfolding is_dissection_def disjoint_def
  by (metis image_eqI inf.idem non_empty to_set_inj)

text "Whenever we have a point in \<^term>\<open>unit_cube\<close>, there exists a (unique) cube in \<^term>\<open>C\<close> containing that
point"
lemma obtain_cube: "p \<in> to_set unit_cube \<Longrightarrow> \<exists> c \<in> C. p \<in> to_set c"
  using dissection unfolding is_dissection_def by blast

text "If the top of \<^term>\<open>c\<close> doesn't touch the top of \<^term>\<open>unit_cube\<close>, then top of \<^term>\<open>c\<close> must 
be covered by bottoms of cubes in \<^term>\<open>C\<close>"
lemma top_cover_by_bot:
  assumes "c \<in> C" "max z c < 1"
  shows "top c \<subseteq> \<Union>(image bot C)"
proof(intro subsetI)
  fix p assume p_in_top: "p \<in> top c"
  from assms(1) have "side x c \<subseteq> {0..<1}" "side y c \<subseteq> {0..<1}" "side z c \<subseteq> {0..<1}" 
    using subset_unit_cube_by_side by blast+
  with assms(2) p_in_top have "px p \<in> {0..<1}" "py p \<in> {0..<1}" "pz p \<in> {0..<1}" 
    by(simp add: in_top_by_side)+
  hence "p \<in> to_set unit_cube" using in_set_by_side side_unit_cube by blast
  then obtain c' where "c' \<in> C" "p \<in> to_set c'" by(metis obtain_cube)
  moreover have "p \<notin> to_set c" using p_in_top in_top_by_side in_set_by_side by simp
  ultimately have "c' \<noteq> c" by metis
  hence "to_set c' \<inter> to_set c = {}" by(metis assms(1) \<open>c' \<in> C\<close>  eq_iff_intersect)
  have "p \<in> bot c'"
  proof(rule ccontr)
    assume "p \<notin> bot c'"
    hence "min z c' < pz p" "pz p < max z c'" using \<open>p \<in> to_set c'\<close>
      by(simp_all add: in_set_by_side in_bot_by_side)
    hence "side z c' \<inter> side z c \<noteq> {}" using \<open>p \<in> top c\<close> by(simp add: in_top_by_side)
    moreover have "side x c \<inter> side x c' \<noteq> {}" "side y c \<inter> side y c' \<noteq> {}"
      using \<open>p \<in> top c\<close> \<open>p \<in> to_set c'\<close> by(simp_all add: in_top_by_side in_set_by_side assms)
    ultimately have "to_set c' \<inter> to_set c \<noteq> {}" using set_intersect_by_side by simp
    thus "False" using \<open>to_set c' \<inter> to_set c = {}\<close> by metis
  qed
  thus "p \<in> \<Union>(image bot C)" using \<open>c' \<in> C\<close> by blast
qed


section "Hole"
text "A hole \<^term>\<open>h\<close> is a special kind of cube, where any cube whose bottom 'touches' the top of \<^term>\<open>v\<close>
must in fact have its bottom contained in the top of \<^term>\<open>v\<close>. If \<^term>\<open>h \<in> C\<close>, then this happens because 
all the other cubes surrounding \<^term>\<open>h\<close> go up taller, forming a hole on top of \<^term>\<open>v\<close>.
Note that we don't require that \<^term>\<open>h \<in> C\<close>, but this is only so we can prove that \<^term>\<open>unit_cube\<close>
shifted down by 1 is a hole - all other holes will in fact lie in \<^term>\<open>C\<close>. The concept of a hole is
inspired by the 'Valley' definition from \<^cite>\<open>leanproof\<close>"
subsection "Definitions"
definition is_hole :: "cube \<Rightarrow> bool" where
  "is_hole h \<longleftrightarrow>
    is_valid h
    \<and> top h \<subseteq> \<Union>(image bot C)
    \<and> (\<forall> c \<in> C .  bot c \<inter> top h \<noteq> {} \<longrightarrow> bot c \<subseteq> top h)
    \<comment> \<open>\<^term>\<open>v\<close> could be a cube in \<^term>\<open>C\<close> (and most often is), but any other cube must be different width.
        Also, this assumption is not actually needed (as it follows from \<^term>\<open>v\<close>, \<^term>\<open>c \<in> C\<close>), 
        but without it we have to do a special-case proof for the bottom of the \<^term>\<open>unit_cube\<close>\<close>
    \<and> (\<forall> c \<in> C . c \<noteq> h \<longrightarrow> width c \<noteq> width h)"

text "Subset of \<^term>\<open>C\<close> which are on a given hole h"
definition is_on_hole :: "cube \<Rightarrow> cube \<Rightarrow> bool" where
  "is_on_hole h c \<longleftrightarrow> bot c \<subseteq> top h"
definition filter_on_hole :: "cube \<Rightarrow> cube set" where
  "filter_on_hole h = Set.filter (is_on_hole h) C"


subsection "Properties of a hole"
text "Terminology: 
  'on hole' means cube \<^term>\<open>c\<close> with:  \<^term>\<open>bot c \<subseteq> top h\<close>. 
  'in hole' means point \<^term>\<open>p\<close> with: \<^term>\<open>p \<in> top h\<close> h"

text "\<^term>\<open>filter_on_hole h \<subseteq> C\<close>"
lemma dissection_if_on_hole[simp]: "c \<in> filter_on_hole h \<Longrightarrow> c \<in> C"
  unfolding filter_on_hole_def by simp

text "Holes, and cubes on them, are valid"
lemma valid_if_hole[simp]: "is_hole h \<Longrightarrow> is_valid h"
  by(metis is_hole_def)
lemma valid_if_on_hole[simp]: "c \<in> filter_on_hole h \<Longrightarrow> is_valid c"
  by simp

lemma on_hole_finite: "is_hole h \<Longrightarrow> finite (filter_on_hole h)"
  by (metis dissection is_dissection_def filter_on_hole_def finite_filter )

lemma on_hole_if_in_filter_on_hole: "c \<in> filter_on_hole h \<Longrightarrow> is_on_hole h c"
  unfolding filter_on_hole_def by simp

lemma on_hole_cover: assumes "is_hole h" shows "top h \<subseteq> \<Union>(image bot (filter_on_hole h))"
proof
  fix p assume "p \<in> top h"
  then obtain "c" where "c \<in> C" "p \<in> bot c" using assms unfolding is_hole_def by blast
  with \<open>p \<in> top h\<close> have "bot c \<subseteq> top h" using assms unfolding is_hole_def by blast
  hence "c \<in> filter_on_hole h"
    by (metis  \<open>c \<in> C\<close> filter_on_hole_def is_on_hole_def member_filter)
  with \<open>p \<in> bot c\<close> show "p \<in> \<Union>(image bot(filter_on_hole h))" by blast
qed

text "Whenever we have a point \<^term>\<open>p\<close> in the top of a hole \<^term>\<open>h\<close>, there exists a (unique) cube 
\<^term>\<open>c \<in> filter_on_hole h\<close>, such that \<^term>\<open>p \<in> bot c\<close>"
lemma obtain_cube_if_in_hole: "\<lbrakk>is_hole h; p \<in> top h\<rbrakk> 
  \<Longrightarrow> \<exists>c \<in> filter_on_hole h . p \<in> bot c"
  using on_hole_cover by blast

lemma on_hole_inj_on_width: "is_hole h \<Longrightarrow> inj_on width (filter_on_hole h)"
  using dissection_if_on_hole inj_on_subset dissection
    is_dissection_def subset_iff by metis


subsection "Properties of cubes on a hole"
lemma neq_hole_if_on_hole: "c \<in> filter_on_hole h \<Longrightarrow> c \<noteq> h"
  using valid_if_on_hole min_ne_max bot_top_subset_by_side is_on_hole_def 
    on_hole_if_in_filter_on_hole by blast

lemma subset_if_on_hole: "c \<in> filter_on_hole h \<Longrightarrow> bot c \<subseteq> top h"
  unfolding is_hole_def filter_on_hole_def is_on_hole_def by simp

lemma side_subset_if_on_hole: "\<lbrakk>c \<in> filter_on_hole h; ax \<in> {x,y}\<rbrakk> \<Longrightarrow> side ax c \<subseteq> side ax h"
  using bot_top_subset_by_side subset_if_on_hole by auto

lemma min_z_eq_max_z_hole_if_on_hole:
  "c \<in> filter_on_hole h \<Longrightarrow> min z c =  max z h"
  using subset_if_on_hole  by(simp add: bot_top_subset_by_side)

lemma z_eq_if_on_hole:
  "\<lbrakk>c1 \<in> filter_on_hole h; c2 \<in> filter_on_hole h\<rbrakk> \<Longrightarrow> min z c1 = min z c2"
  using min_z_eq_max_z_hole_if_on_hole by simp

text "Do not need to care about \<^term>\<open>z\<close>-coordinate"
lemma eq_iff_side_eq_if_on_hole: "\<lbrakk>c1 \<in> filter_on_hole h; c2 \<in> filter_on_hole h\<rbrakk> 
  \<Longrightarrow> c1 = c2 \<longleftrightarrow> side x c1 = side x c2 \<and> side y c1 = side y c2"
  by(meson valid_if_on_hole z_eq_if_on_hole bot_eq_by_side bot_inj)

text "Disjointness-lemmas:"
lemma eq_iff_bot_intersect_if_on_hole: 
  assumes "c1 \<in> filter_on_hole h" "c2 \<in> filter_on_hole h"
  shows "c1 = c2 \<longleftrightarrow> bot c1 \<inter> bot c2 \<noteq> {}"
proof -
  from assms have "c1 = c2 \<longleftrightarrow> to_set c1 \<inter> to_set c2 \<noteq> {}" by(simp add: eq_iff_intersect)
  moreover have "min z c1 = min z c2" by(metis assms z_eq_if_on_hole)
  hence "to_set c1 \<inter> to_set c2 \<noteq> {} \<longleftrightarrow> bot c1 \<inter> bot c2 \<noteq> {}"
    using set_intersect_by_side bot_intersect_by_side bot_subset subsetD by blast
  ultimately show "c1 = c2 \<longleftrightarrow> bot c1 \<inter> bot c2 \<noteq> {}" by blast
qed

lemma eq_iff_side_intersect_if_on_hole: 
  "\<lbrakk>c1 \<in> filter_on_hole h; c2 \<in> filter_on_hole h\<rbrakk> 
  \<Longrightarrow> c1 = c2 \<longleftrightarrow> side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {}"
  by(meson z_eq_if_on_hole eq_iff_bot_intersect_if_on_hole bot_intersect_by_side)

lemma width_on_hole_lt_width_hole: 
  assumes "is_hole h" "c \<in> filter_on_hole h" shows "width c < width h"
proof(rule ccontr)
  assume "\<not>width c < width h"
  hence "width c \<ge> width h" by simp
  moreover have "c \<noteq> h" by (metis assms(2) neq_hole_if_on_hole)
  hence "width c \<noteq> width h" using assms unfolding is_hole_def by simp
  ultimately have "width c > width h" by simp
  hence "\<not>(side x c \<subseteq> side x h)" using assms less_le_not_le by fastforce 
  hence "\<not>(bot c \<subseteq> top h)" using assms by(auto simp add: bot_top_subset_by_side)
  moreover have "bot c \<subseteq> top h" by(metis assms(2) subset_if_on_hole)
  ultimately show "False" by metis
qed

lemma strict_subset_if_on_hole: assumes "is_hole h" "c \<in> filter_on_hole h"
  shows "bot c \<subset> top h"
proof
  show "bot c \<subseteq> top h" by(metis assms(2) subset_if_on_hole)
next
  have "width c \<noteq> width h" using assms width_on_hole_lt_width_hole by fastforce
  hence "side x c \<noteq> side x h" by(metis assms(1) valid_if_hole width_eq_if_side_eq)
  thus "bot c \<noteq> top h" using assms bot_top_eq_by_side by simp
qed

lemma on_hole_non_empty: "is_hole h \<Longrightarrow> filter_on_hole h \<noteq> {}"
  using on_hole_cover
  by (metis Sup_empty image_empty subset_empty top_non_empty valid_if_hole)


section "Bottom of \<^term>\<open>unit_cube\<close> is a hole"
lemma bot_unit_cube_cover_by_bot: "bot unit_cube \<subseteq> \<Union>(image bot C)"
proof
  fix p
  assume "p \<in> bot unit_cube"
  hence "p \<in> to_set unit_cube" using bot_subset by auto
  then obtain "c" where "c \<in> C" "p \<in> to_set c" by(metis obtain_cube)
  from \<open>p \<in> bot unit_cube\<close> have "pz p = 0" by(metis min_unit_cube_0 in_bot_by_side)
  hence "min z c \<le> 0" using \<open>p \<in> to_set c\<close> by(simp add: in_set_by_side)
  moreover have "side z c \<subseteq> {0..<1}" by(metis \<open>c \<in> C\<close> subset_unit_cube_by_side)
  hence "min z c \<ge> 0" using \<open>c \<in> C\<close> by fastforce
  ultimately have "min z c = 0" by simp
  hence "p \<in> bot c" using \<open>p \<in> to_set c\<close> \<open>pz p = 0\<close> by(simp add: in_set_by_side in_bot_by_side)
  thus "p \<in> \<Union> (image bot C)" using \<open>c \<in> C\<close> by auto
qed

lemma eq_if_width_eq_if_subset:
  assumes "width c1 = width c2" "to_set c1 \<subseteq> to_set c2"
  shows "to_set c1 = to_set c2"
proof-
  from assms(2) have "side x c1 \<subseteq> side x c2" "side y c1 \<subseteq> side y c2"  "side z c1 \<subseteq> side z c2" 
    using set_subset_by_side by blast+
  hence "side x c1 = side x c2" "side y c1 = side y c2" "side z c1 = side z c2"
    using assms(1) by fastforce+
  thus "to_set c1 = to_set c2" using set_eq_by_side by blast
qed

lemma width_ne_one:
  assumes "c \<in> C"
  shows "width c \<noteq> 1"
proof(rule ccontr)
  obtain "c'" where "c' \<in> C" "c \<noteq> c'" using assms dissection 
    unfolding is_dissection_def by(auto simp add: card_le_Suc_iff numeral_eq_Suc)
  hence "to_set c' \<inter> to_set c = {}"  using assms by(metis eq_iff_intersect)
  assume "\<not> width c \<noteq> 1"
  hence "width c = 1" by blast
  moreover have "to_set c \<subseteq> to_set unit_cube" by(metis assms subset_unit_cube_if_dissection)
  ultimately have "to_set c = to_set unit_cube" using eq_if_width_eq_if_subset 
    unfolding unit_cube_def by auto
  with \<open>c' \<in> C\<close> have "to_set c' \<subseteq> to_set c" by(metis subset_unit_cube_if_dissection)
  hence "to_set c' \<inter> to_set c \<noteq> {}" using \<open>c' \<in> C\<close> by(simp add: non_empty Int_absorb2)
  moreover have "to_set c' \<inter> to_set c = {}" by(metis assms \<open>c' \<in> C\<close> \<open>c \<noteq> c'\<close> eq_iff_intersect)
  ultimately show "False" by metis
qed

text "Combines the previous lemmas, to show that the bottom of \<^term>\<open>unit_cube\<close> is a hole"
proposition hole_unit_cube: "is_hole (shift_down unit_cube)"
proof-
  let ?b = "shift_down unit_cube" \<comment> \<open>cube with \<^term>\<open>point\<close> (0,0,-1) and \<^term>\<open>width\<close> 1\<close>
  show ?thesis unfolding is_hole_def
  proof(intro conjI subsetI ballI impI)
    show "is_valid ?b" by(simp add: shift_down_def)
  next
    fix p assume "p \<in> top ?b"
    hence "p \<in> bot unit_cube"  by(simp add: top_shift_down_eq_bot)
    thus "p \<in> \<Union>(image bot C)" using bot_unit_cube_cover_by_bot by blast
  next
    fix c p assume "c \<in> C" "bot c \<inter> top ?b \<noteq> {}" "p \<in> bot c"
    with \<open>bot c \<inter> top ?b \<noteq> {}\<close> have "min z c = 0" 
      by(metis top_shift_down_eq_bot bot_intersect_by_side min_unit_cube_0)
    hence "pz p = 0" by(metis \<open>p \<in> bot c\<close> in_bot_by_side)
    moreover from \<open>p \<in> bot c\<close> have "px p \<in> {0..<1}" "py p \<in> {0..<1}" 
      using \<open>c \<in> C\<close> subset_unit_cube_by_side in_bot_by_side by blast+
    ultimately have "p \<in> bot unit_cube" by(metis min_unit_cube_0 in_bot_by_side side_unit_cube)
    thus "p \<in> top ?b" by(metis top_shift_down_eq_bot)
  next
    fix c assume "c \<in> C" "c \<noteq> ?b"
    hence "width c \<noteq> 1"  by(metis width_ne_one)
    thus "width c \<noteq> width ?b" by(simp add: unit_cube_def shift_down_def)
  qed
qed


section "Minimum cube on hole is interior"
context 
  fixes h assumes hole: "is_hole h"
begin

text "For this section, we fix a hole \<^term>\<open>h\<close>, and define \<^term>\<open>cmin\<close> to be the smallest cube 
on this hole. Theorem @{thm[source] hole} refers to this fact. The goal of this section is then to show that
\<^term>\<open>cmin\<close> itself is a hole." 

subsection "Definition: Minimum cube on \<^term>\<open>h\<close>"
text "\<^term>\<open>cmin\<close> is the smallest cube on the hole \<^term>\<open>h\<close>"
definition cmin:: "cube"
  where "cmin = (ARG_MIN width c . c \<in> filter_on_hole h)"

lemma arg_min_exist: "\<lbrakk>finite C'; C' \<noteq> {}\<rbrakk> \<Longrightarrow> (ARG_MIN width c . c \<in> C') \<in> C'"
  by(metis arg_min_on_def arg_min_if_finite(1))

text "This lemma also shows that \<^term>\<open>cmin\<close> exists"
lemma cmin_on_h: "cmin \<in> filter_on_hole h"
  unfolding cmin_def by(metis hole arg_min_exist on_hole_finite on_hole_non_empty )

lemma cmin_valid[simp]: "is_valid cmin"
  by(metis cmin_on_h valid_if_on_hole)

lemma arg_min_minimal: "\<lbrakk>finite C'; c \<in> C'\<rbrakk> \<Longrightarrow> width (ARG_MIN width c . c \<in> C') \<le> width c"
  by(metis arg_min_least arg_min_on_def empty_iff)

lemma cmin_minimal: "c \<in> filter_on_hole h \<Longrightarrow> width cmin \<le> width c"
  unfolding cmin_def by(metis hole arg_min_minimal on_hole_finite)

lemma cmin_minimal_strict:
  assumes "c \<in> filter_on_hole h" "c \<noteq> cmin"
  shows "width cmin < width c"              
proof -
  have "width cmin \<le> width c" using assms(1) by(rule cmin_minimal)
  moreover have "width cmin \<noteq> width c"
    by (metis assms on_hole_inj_on_width assms(2) cmin_on_h hole inj_on_contraD)
  ultimately show "width cmin < width c" by simp
qed

lemma cmin_max_z_neq_one: "max z cmin < 1"
proof -
  let ?On_h = "filter_on_hole h"
  have "bot cmin \<subset> top h" by(metis hole cmin_on_h strict_subset_if_on_hole)
  then obtain c where "c \<in> ?On_h" "c \<noteq> cmin" using hole obtain_cube_if_in_hole by blast 
  hence "min z cmin = min z c" by(metis cmin_on_h \<open>c \<in> ?On_h\<close> z_eq_if_on_hole)
  hence "max z cmin < max z c" by(simp add: \<open>c \<in> ?On_h\<close> \<open>c \<noteq> cmin\<close> cmin_minimal_strict)
  moreover have "side z c \<subseteq> {0..<1}" 
    by(metis \<open>c \<in> ?On_h\<close> dissection_if_on_hole  subset_unit_cube_by_side) 
  hence "max z c \<le> 1" using \<open>c \<in> ?On_h\<close> valid_if_on_hole by (simp add: less_le_not_le)
  ultimately show "max z cmin < 1" by simp
qed


subsection "Minimum cube on hole is interior"
text "All squares on the boundary of \<^term>\<open>h\<close>"
definition is_on_boundary :: "axis \<Rightarrow> cube \<Rightarrow> bool" where
  "is_on_boundary ax c \<longleftrightarrow> min ax h  = min ax c \<or> max ax h  = max ax c"

text "Shows that IF \<^term>\<open>cmin\<close> is on a boundary \<^term>\<open>ax\<close>, then we find some \<^term>\<open>ax\<close>-coordinate 
\<^term>\<open>r\<close>, which is further from the boundary than the edge of \<^term>\<open>cmin\<close>, but closer than the edge
 of any other cube sufficiently close to the boundary."
lemma cmin_on_boundary:
  assumes "is_on_boundary ax cmin"  "ax \<in> {x, y}"
  shows "\<exists>r . 
    r \<in> (side ax h - (side ax cmin)) \<and> 
    (\<forall> c \<in> filter_on_hole h .  c \<noteq> cmin \<longrightarrow> side ax cmin \<inter> side ax c \<noteq> {} \<longrightarrow> r \<in> side ax c)"
proof -
  let ?On_h = "filter_on_hole h"
  let ?c_2nd_min = "ARG_MIN width c . c \<in> (Set.remove cmin ?On_h)"
  have "bot cmin \<subset> top h" by(metis hole cmin_on_h strict_subset_if_on_hole)
  hence "Set.remove cmin ?On_h \<noteq> {}" using hole obtain_cube_if_in_hole by fastforce
  moreover have "finite (Set.remove cmin ?On_h)" 
    by (metis hole on_hole_finite remove_def finite_Diff)
  ultimately have "?c_2nd_min \<in> Set.remove cmin ?On_h" by(metis arg_min_exist)
  hence "?c_2nd_min \<in> ?On_h " and "width cmin < width ?c_2nd_min"
    by(simp, simp add: cmin_minimal_strict)
  then obtain "\<epsilon>" where "\<epsilon> > 0" "width cmin + \<epsilon> < width ?c_2nd_min" 
    by(metis field_le_epsilon less_le_not_le nle_le)
  have \<epsilon>_prop: "\<forall>c \<in> ?On_h . cmin \<noteq> c \<longrightarrow> width cmin + \<epsilon> < width c"
  proof(intro ballI impI)
    fix c assume "c \<in> ?On_h" "cmin \<noteq> c"
    hence "c \<in> Set.remove cmin ?On_h" by auto
    hence "width ?c_2nd_min \<le> width c" 
      using \<open>Set.remove cmin ?On_h \<noteq> {}\<close> \<open>finite (Set.remove cmin ?On_h) \<close> arg_min_minimal
      by blast
    thus "width cmin + \<epsilon> < width c" using \<open>width cmin + \<epsilon> < width ?c_2nd_min\<close> by simp
  qed
  then show ?thesis using assms(1) unfolding is_on_boundary_def
  proof(elim disjE)
    assume "min ax h = min ax cmin"
    let ?r = "max ax cmin + \<epsilon>" 
    show ?thesis
    proof(intro exI conjI ballI impI)
      have "?r < min ax cmin + width ?c_2nd_min" using \<open>width cmin + \<epsilon> < width ?c_2nd_min\<close> by auto
      also have "... = min ax h + width ?c_2nd_min" using \<open>min ax h = min ax cmin\<close> by simp
      finally have "?r < max ax h" 
        using \<open>?c_2nd_min \<in> ?On_h\<close> hole width_on_hole_lt_width_hole by fastforce
      moreover have "min ax cmin < max ax cmin" using assms(1) by(simp add: min_lt_max)
      hence "min ax h < ?r" using \<open>\<epsilon> > 0\<close> \<open>min ax h = min ax cmin\<close>  by linarith
      ultimately have "?r \<in> side ax h" by simp
      moreover from \<open>\<epsilon> > 0\<close> have "?r \<notin> side ax cmin" by simp
      ultimately show  "?r \<in> side ax h - side ax cmin"  by simp
    next
      fix c assume "c \<in> ?On_h" "c \<noteq> cmin" "side ax cmin \<inter> side ax c \<noteq> {}"
      from \<open>side ax cmin \<inter> side ax c \<noteq> {}\<close> have "min ax c < max ax cmin" by auto
      also have "... < ?r" using \<open>\<epsilon>>0\<close> by simp
      finally have "min ax c \<le> ?r" by simp
      moreover have "bot c \<subseteq> top h" by(metis \<open>c \<in> ?On_h\<close> subset_if_on_hole)
      hence "side ax c \<subseteq> side ax h" using \<open>c \<in> ?On_h\<close> assms(2) bot_top_subset_by_side by fastforce
      hence "min ax h \<le> min ax c" using \<open>c \<in> ?On_h\<close> by fastforce 
      hence "min ax cmin \<le> min ax c" using \<open>min ax h = min ax cmin\<close>  by simp
      hence "?r < max ax c" using \<open>c \<in> ?On_h\<close> \<open>c \<noteq> cmin\<close> \<epsilon>_prop by auto
      ultimately show "?r \<in> side ax c" by simp
    qed
  next
    assume "max ax h = max ax cmin"
    let ?r = "min ax cmin - \<epsilon>"
    show ?thesis
    proof(intro exI conjI ballI impI)
      have "min ax h = max ax h - width h" by simp
      also have "... < max ax h - width ?c_2nd_min" 
        using hole width_on_hole_lt_width_hole \<open>?c_2nd_min \<in> ?On_h\<close> by simp
      also have "... = max ax cmin - width ?c_2nd_min" using \<open>max ax h = max ax cmin\<close> by simp
      also have "... < ?r" using \<open>width cmin + \<epsilon> < width ?c_2nd_min\<close> by argo
      finally have "min ax h < ?r" by simp
      moreover have "min ax cmin < max ax cmin" using assms(1) by(simp add: min_lt_max)
      hence "?r < max ax h" using \<open>max ax h = max ax cmin\<close> \<open>\<epsilon> > 0\<close> by argo
      ultimately have "?r \<in> side ax h" by simp
      moreover have "?r \<notin> side ax cmin" using \<open>\<epsilon> > 0\<close> by simp
      ultimately show "?r \<in> side ax h - side ax cmin" by simp
    next
      fix c assume "c \<in> ?On_h" "c \<noteq> cmin" "side ax cmin \<inter> side ax c \<noteq> {}"
      have "?r < min ax cmin" using \<open>\<epsilon>>0\<close> by simp
      also have "... < max ax c" using \<open>side ax cmin \<inter> side ax c \<noteq> {}\<close> by simp
      finally have "?r < max ax c" by simp
      moreover have "bot c \<subseteq> top h" by(metis \<open>c \<in> ?On_h\<close> subset_if_on_hole)
      hence "side ax c \<subseteq> side ax h" 
        using \<open>c \<in> ?On_h\<close> assms(2) bot_top_subset_by_side by fastforce
      hence "max ax c \<le> max ax h" using \<open>c \<in> ?On_h\<close> valid_if_on_hole by fastforce
      hence "max ax c \<le> max ax cmin" using \<open> max ax h = max ax cmin\<close> by simp
      hence "min ax c\<le> ?r" using \<open>c \<in> ?On_h\<close> \<open>c \<noteq> cmin\<close> \<epsilon>_prop by auto
      ultimately show "?r \<in> side ax c" by simp
    qed
  qed
qed

text "Using the previous lemma, we show that \<^term>\<open>cmin\<close> being on the boundary leads to a 
contradiction"
lemma cmin_not_on_boundary_by_axis: 
  assumes "ax \<in> {x, y}"
  shows "\<not>is_on_boundary ax cmin "
proof(rule ccontr, unfold not_not)
  let ?On_h = "filter_on_hole h"
  assume "is_on_boundary ax cmin"
  then obtain r where "r \<in> (side ax h - side ax cmin)" and
    r_prop: "(\<forall> c \<in> ?On_h .  c \<noteq> cmin \<longrightarrow> side ax cmin \<inter> side ax c \<noteq> {} \<longrightarrow> r \<in> side ax c)"
    by(metis assms cmin_on_boundary)
  hence "r \<in> side ax h" and "r \<notin> side ax cmin" by blast+
  let ?ax2 = "if ax = x then y else x"
  let ?p1 = "if ax = x then \<lparr>px=r, py=min y cmin, pz=max z h\<rparr> else \<lparr>px=min x cmin, py=r, pz=max z h\<rparr>"
  have "side ?ax2 cmin \<subseteq> side ?ax2 h" using cmin_on_h side_subset_if_on_hole by simp
  hence "min ?ax2 cmin \<in> side ?ax2 h" using min_in_side by fastforce
  hence "?p1 \<in> top h" using \<open>r \<in> side ax h\<close> in_top_by_side assms by (simp split: if_splits)
  then obtain c1 where "?p1 \<in> bot c1" and c1_on_h: "c1 \<in> ?On_h" 
    using hole obtain_cube_if_in_hole by blast
  hence "cmin \<noteq> c1" using \<open>r \<notin> side ax cmin\<close> assms in_bot_by_side by (auto split: if_splits)
  hence "width cmin < width c1" by(metis \<open>c1 \<in> ?On_h\<close> cmin_minimal_strict)
  hence "\<not> side ?ax2 c1 \<subseteq> side ?ax2 cmin" using c1_on_h valid_if_on_hole by fastforce  
  then obtain s where "s \<in> side ?ax2 c1" "s \<notin> side ?ax2 cmin" by blast
  let ?p2="if ax = x then \<lparr>px=min x cmin, py=s, pz=max z h\<rparr> else \<lparr>px=s, py=min y cmin, pz=max z h\<rparr>"
  have "side ax cmin \<subseteq> side ax h" using assms cmin_on_h side_subset_if_on_hole by blast
  hence "min ax cmin \<in> side ax h" using min_in_side by fastforce
  moreover have "side ?ax2 c1 \<subseteq> side ?ax2 h" using \<open>c1 \<in>?On_h\<close> side_subset_if_on_hole by simp
  hence "s \<in> side ?ax2 h" using \<open>s \<in> side ?ax2 c1\<close> by blast
  ultimately have "?p2 \<in> top h" using in_top_by_side assms by (simp split: if_splits)
  then obtain c2 where  "?p2 \<in> bot c2" and c2_on_h: "c2 \<in> ?On_h" 
    using hole obtain_cube_if_in_hole by blast
  let ?p3 = "if ax = x then \<lparr>px=r, py=s, pz=max z h\<rparr> else \<lparr>px=s, py=r, pz=max z h\<rparr>"
    \<comment> \<open>We show that \<^term>\<open>?p3\<close> is in the intersection of \<^term>\<open>c1\<close> and \<^term>\<open>c2\<close>, but \<^term>\<open>p2\<close> is 
      only in \<^term>\<open>c2\<close>, contradicting disjointness\<close>
  have "?p2 \<notin> bot cmin" using \<open>s \<notin> side ?ax2 cmin\<close> in_bot_by_side by (auto split: if_splits)
  hence "cmin \<noteq> c2" using \<open>?p2 \<in> bot c2\<close> by blast
  hence "r \<in> side ax c2" using r_prop c2_on_h min_in_side \<open>?p2 \<in> bot c2\<close> in_bot_by_side assms
    by fastforce
  hence "?p3 \<in> bot c2" using \<open>?p2 \<in> bot c2\<close> in_bot_by_side assms by (simp split: if_splits)
  moreover have "?p3 \<in> bot c1" using \<open>?p1 \<in> bot c1\<close> \<open>s \<in> side ?ax2 c1\<close> in_bot_by_side by auto
  ultimately have "c1 = c2" using c1_on_h c2_on_h eq_iff_bot_intersect_if_on_hole
    by blast
  moreover from \<open>s \<notin> side ?ax2 cmin\<close> have "?p2 \<notin> to_set cmin" using in_set_by_side by auto
  hence "cmin \<noteq> c2" using eq_iff_side_eq_if_on_hole c2_on_h \<open>?p2 \<in> bot c2\<close> bot_subset 
    by blast
  hence "to_set cmin \<inter> to_set c2 = {}" using cmin_on_h c2_on_h eq_iff_intersect by simp
  hence "side ?ax2 cmin \<inter> side ?ax2 c2 = {}" using \<open>?p2 \<in> bot c2\<close> \<open>cmin \<noteq> c2\<close> 
      c2_on_h assms cmin_on_h in_bot_by_side eq_iff_side_intersect_if_on_hole by fastforce
  hence "min ?ax2 cmin \<notin> side ?ax2 c2" using cmin_valid min_in_side by blast
  hence "?p1 \<notin> bot c2" using assms in_bot_by_side by fastforce 
  hence "c1 \<noteq> c2" using \<open>?p1 \<in> bot c1\<close> by blast
  ultimately show "False" by blast
qed

text "Previous result, written as inequalities instead"
proposition cmin_not_on_boundary: 
  "min x h < min x cmin \<and> max x cmin < max x h 
        \<and> min y h < min y cmin \<and> max y cmin < max y h"
proof-
  have "side x cmin \<subseteq> side x h \<and> side y cmin \<subseteq> side y h"
    using cmin_on_h side_subset_if_on_hole by blast
  hence "min x h \<le> min x cmin \<and> max x cmin \<le> max x h \<and> 
    min y h \<le> min y cmin \<and> max y cmin \<le> max y h" using cmin_valid by auto
  thus "min x h < min x cmin \<and> max x cmin < max x h \<and>
    min y h < min y cmin \<and> max y cmin < max y h" 
    using cmin_not_on_boundary_by_axis unfolding is_on_boundary_def by force
qed


section "Minimum cube of hole induces hole on top"
text "The main result of this proof - the minimum cube on a hole is itself a hole!"
proposition hole_cmin: 
  shows "is_hole cmin"
proof-
  let ?On_cmin = "filter_on_hole cmin"
  show ?thesis unfolding is_hole_def
  proof(intro conjI ballI impI)
    show "is_valid cmin" by simp
  next 
    show "top cmin \<subseteq> \<Union>(image bot C)" 
      by(metis top_cover_by_bot cmin_max_z_neq_one cmin_on_h dissection_if_on_hole)
  next
    fix c assume "c \<in> C" "c \<noteq> cmin"
    thus "width c \<noteq> width cmin" 
      by(metis dissection dissection_if_on_hole cmin_on_h inj_onD is_dissection_def)
  next
    fix c assume "c \<in> C" "bot c \<inter> top cmin \<noteq> {}"
    hence c_valid: "is_valid c" by simp
    show "bot c \<subseteq> top cmin"
    proof(rule ccontr)
      assume "\<not> bot c \<subseteq> top cmin"
      from \<open>bot c \<inter> top cmin \<noteq> {}\<close> have "min z c = max z cmin" using bot_top_intersect_by_side 
        by blast
      with \<open>\<not> bot c \<subseteq> top cmin\<close> obtain ax where ax: "ax \<in>{x,y}" "\<not>side ax c \<subseteq> side ax cmin" 
        using bot_top_subset_by_side c_valid by (meson insert_iff)
      let ?ax2 = "if ax=x then y else x"
      have "?ax2 \<in> {x,y}" by simp
      have "min ax h < min ax cmin" "max ax cmin < max ax h" 
        using ax(1) cmin_not_on_boundary by blast+
      moreover have "side ax c \<inter> side ax cmin \<noteq> {}" 
        using \<open>bot c \<inter> top cmin \<noteq> {}\<close> ax(1) bot_top_intersect_by_side  by blast
      ultimately have "side ax c \<inter> side ax h - side ax cmin \<noteq> {}" using ax(2) by fastforce
      then obtain a where a_prop: "a \<in> side ax c \<inter> side ax h" "a \<notin> side ax cmin" by blast
      moreover from \<open>bot c \<inter> top cmin \<noteq> {}\<close> have "side ?ax2 c \<inter> side ?ax2 cmin \<noteq> {}"
        using bot_top_intersect_by_side \<open>?ax2 \<in> {x,y}\<close> by simp
      then obtain b where b_prop: "b \<in> side ?ax2 c \<inter> side ?ax2 cmin" by blast
      hence b_prop_2: "b \<in> side ?ax2 c \<inter> side ?ax2 h" 
        using \<open>?ax2 \<in> {x,y}\<close> cmin_on_h side_subset_if_on_hole by blast
      let ?x0 = "if ax=x then a else b" and ?y0 = "if ax=y then a else b"
      have xy0_props: "?x0 \<in> side x c \<inter> side x h" "?y0 \<in> side y c \<inter> side y h"
        "?x0 \<notin> side x cmin \<or> ?y0 \<notin> side y cmin"
      proof -
        show"?x0 \<in> side x c \<inter> side x h" using a_prop b_prop ax(1) \<open>?ax2 \<in> {x,y}\<close>
          using b_prop_2 by presburger
        show  "?y0 \<in> side y c \<inter> side y h" using a_prop b_prop_2 ax(1)  by fastforce
        show "?x0 \<notin> side x cmin \<or> ?y0 \<notin> side y cmin" using a_prop ax(1) by fastforce
      qed
      let ?pd = "\<lparr>px=?x0, py=?y0, pz=max z h\<rparr>"
      let ?pu = "\<lparr>px=?x0, py=?y0, pz=min z c\<rparr>"
      have "max z h = min z cmin" by(metis cmin_on_h min_z_eq_max_z_hole_if_on_hole)
      hence "?pd = \<lparr>px=?x0, py=?y0, pz=min z cmin\<rparr>" by simp
      moreover have "min z cmin < min z c" using min_lt_max \<open>min z c = max z cmin\<close> by simp
      hence "min z cmin \<notin> side z c" using in_set_by_side by simp
      ultimately have "?pd \<notin> to_set c" by(simp add: in_set_by_side)
      have "?pu \<in> bot c" using c_valid xy0_props in_bot_by_side by simp
      hence "?pu \<in> to_set c" using bot_subset by blast
      have "?pd \<notin> bot cmin" using \<open>?x0 \<notin> side x cmin \<or> ?y0 \<notin> side y cmin\<close> in_bot_by_side by auto
      have "?pd \<in> top h" using valid_if_hole xy0_props in_top_by_side by simp
      then obtain c' where "c' \<in> filter_on_hole h" "?pd \<in> bot c'" 
        using hole obtain_cube_if_in_hole by blast
      hence "c' \<noteq> cmin" using \<open>?pd \<notin> bot cmin\<close> by blast
      hence "width cmin < width c'"
        using \<open>c' \<in> filter_on_hole h\<close> cmin_minimal_strict by simp
      moreover have "min z cmin = min z c'" 
        by(metis cmin_on_h \<open>c' \<in> filter_on_hole h\<close> z_eq_if_on_hole)
      ultimately have "max z cmin < max z c'" by simp 
      hence "min z c < max z c'" by(metis \<open>min z c = max z cmin\<close>)
      hence "min z c \<in> side z c'" using \<open>min z cmin < min z c\<close> \<open>min z cmin = min z c'\<close> by auto 
      hence "?pu \<in> to_set c'" using \<open>c' \<in> filter_on_hole h\<close> \<open>?pd \<in> bot c'\<close> 
          in_bot_by_side in_set_by_side \<open>min z c = max z cmin\<close> by simp
      hence "to_set c \<inter> to_set c' \<noteq> {}" using \<open>?pu \<in> to_set c\<close> by blast
      hence "c = c'" using \<open>c' \<in> filter_on_hole h\<close>  \<open>c \<in> C\<close> eq_iff_intersect by auto
      moreover have "c \<noteq> c'" using \<open>?pd \<notin> to_set c\<close> \<open>?pd \<in> bot c'\<close> using bot_subset by blast
      ultimately show "False" by blast
    qed
  qed
qed

text "The main purpose of the previous result: From the proposition, \<^term>\<open>hole_cmin\<close> when given the
hole \<^term>\<open>h\<close> induce another hole \<^term>\<open>h'\<close> (i.e., \<^term>\<open>cmin\<close>), which is in \<^term>\<open>C\<close> and is strictly
smaller."
lemma recursive_step: "\<exists>h'. h' \<in> C \<and> is_hole h' \<and> width h' < width h"
proof-
  show ?thesis
  proof(intro exI conjI)
    show "cmin \<in> C" using cmin_on_h by force
    show "is_hole cmin" by(simp add: hole_cmin)
    show "width cmin < width h" by(simp add: hole cmin_on_h width_on_hole_lt_width_hole)
  qed
qed
text "Here we end the context in which \<^term>\<open>h\<close> is some fixed hole 
(and hence also the specific \<^term>\<open>cmin\<close>)"
end

section "The main result"
text "We combine the previous lemmas inductively as follows:
  0: Start with the bottom of \<^term>\<open>unit_cube\<close>, which we showed is a hole.
  n: For each hole, take the minimum cube on this hole, which is then a new hole, 
strictly smaller, and in \<^term>\<open>C\<close>. Hence, \<^term>\<open>C\<close> is infinite."
definition next_hole:: "cube \<Rightarrow> cube" where
  "next_hole h = (SOME h' . h' \<in> C \<and> is_hole h' \<and> width h' < width h)"

lemma next_hole_exist: "is_hole h 
  \<Longrightarrow> next_hole h \<in> C \<and> is_hole (next_hole h) \<and> width (next_hole h) < width h"
  unfolding next_hole_def  by (rule someI_ex) (rule recursive_step)

text "For following proof, we want the image of \<^term>\<open>nth_hole\<close> to be contained in \<^term>\<open>C\<close>, 
hence we start at \<^term>\<open>1\<close> (= \<^term>\<open>Suc 0\<close>). \<^term>\<open>nth_hole\<close> is a function from \<^term>\<open>\<nat>\<close> to \<^term>\<open>C\<close>"
definition nth_hole :: "nat \<Rightarrow> cube" where
  "nth_hole n = (next_hole ^^ Suc n) (shift_down unit_cube)"

text "Each cube in the image of \<^term>\<open>nth_hole\<close> is a hole"
lemma nth_hole_is_hole: "is_hole (nth_hole n)"
proof(induction n)
  case 0
  have "nth_hole 0 = next_hole (shift_down unit_cube)" by(simp add: nth_hole_def)
  moreover have "is_hole (shift_down unit_cube)" by(rule hole_unit_cube)
  ultimately show ?case by(simp add: next_hole_exist)
next
  case (Suc n)
  then show ?case by(simp add: nth_hole_def next_hole_exist)
qed

text "\<^term>\<open>uminus\<close> is \<^term>\<open>(\<lambda> x. -x)\<close>, and \<^term>\<open>strict_mono\<close> means strictly increasing 
  (not strictly monotonous, as the name might suggest)"
lemma nth_hole_strict_decreasing: "strict_mono (uminus \<circ> width \<circ> nth_hole)"
proof(rule iffD2, rule strict_mono_Suc_iff, intro allI)
  fix n
  have "is_hole (nth_hole n)" by (rule nth_hole_is_hole)
  thus "(uminus \<circ> width \<circ> nth_hole) n < (uminus \<circ> width \<circ> nth_hole) (Suc n)" 
    by(simp add: nth_hole_def next_hole_exist)
qed

text "\<^term>\<open>nth_hole\<close> is injective"
lemma nth_hole_inj : "inj nth_hole"
proof -
  have "strict_mono (uminus \<circ> width \<circ> nth_hole)" by(rule nth_hole_strict_decreasing)
  hence "inj (uminus \<circ> width \<circ> nth_hole)" by(simp add: strict_mono_imp_inj_on)
  thus "inj nth_hole" by(simp add:inj_on_imageI2)
qed

text "The image (range) of \<^term>\<open>nth_hole\<close> is contained in \<^term>\<open>C\<close>"
lemma nth_hole_in: "nth_hole n \<in> C"
proof(cases n)
  case 0
  then show ?thesis by(simp add: hole_unit_cube nth_hole_def next_hole_exist)
next
  case (Suc nat)
  then obtain m where "n = Suc m" by simp
  have "is_hole (nth_hole m)" by(simp add: nth_hole_is_hole)
  hence "next_hole (nth_hole m) \<in> C" by(simp add: next_hole_exist)
  thus "nth_hole n \<in> C"  by(simp add: nth_hole_def \<open>n = Suc m\<close>)
qed

text "Same as previous lemma, but written with a quantifier"
lemma nth_hole_in_forall: "\<forall>n . nth_hole n \<in> C"
  by(simp add: nth_hole_in)

text "The assumption made in this context (\<^term>\<open>is_dissection C\<close>) leads to \<^term>\<open>False\<close> 
(since \<^term>\<open>nth_hole\<close> generates an infinite subset of \<^term>\<open>C\<close>)"
theorem false_if_dissection: "False"
proof-
  have "inj nth_hole" by(rule nth_hole_inj)
  moreover have "\<forall>n . nth_hole n \<in> C" by(rule nth_hole_in_forall)
      \<comment> \<open>\<^term>\<open>nth_hole\<close> injective, with infinite domain \<^term>\<open>\<nat>\<close>, and image contained in \<^term>\<open>C\<close> 
  together implies that \<^term>\<open>C\<close> is infinite\<close>
  ultimately have "infinite C" by(metis finite_subset image_subset_iff range_inj_infinite)
  moreover have "finite C" using dissection unfolding is_dissection_def by metis
  ultimately show "False" by metis
qed
end \<comment> \<open>Here we end the \<^term>\<open>is_dissection C\<close> context\<close>


text "Main result (spelling out the definition of \<^term>\<open>is_dissection\<close>)."
theorem dissection_does_not_exist:
  "\<nexists> C. (\<forall> c \<in> C. is_valid c) 
  \<and> disjoint (image to_set C) 
  \<and> \<Union>(image to_set C) = to_set unit_cube 
  \<and> inj_on width C 
  \<and> card C \<ge> 2 
  \<and> finite C"
  by(metis is_dissection_def false_if_dissection)
end

