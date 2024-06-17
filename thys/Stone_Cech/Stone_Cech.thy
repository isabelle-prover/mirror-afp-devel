(*
  Author: Mike Stannett (m.stannett@sheffield.ac.uk)
  Maintainer: Mike Stannett (m.stannett@sheffield.ac.uk)
  Title:  Stone_Cech.thy
  Date:   May 2024
  Topic:  The Stone-Cech Compactification (Part 1. Definitions and Extension Property)
*)

(* The Stone-{\v{C}}ech Compactification} *)

text \<open>
  Building on parts of HOL-Analysis, we provide mathematical components for work on the 
  Stone-{\v{C}}ech compactification. The main concepts covered are: $C^*$-embedding, weak topologies 
  and compactification, focusing in particular on the Stone-{\v{C}}ech compactification of an 
  arbitrary Tychonov space $X$. Many of the proofs given here derive from those of Willard 
  (\textit{General Topology}, 1970, Addison-Wesley) and Walker (\textit{The Stone-{\v C}ech 
  Compactification}, 1974, Springer-Verlag).

  Using traditional topological proof strategies we define the evaluation and 
  projection functions for product spaces, and show that product spaces carry the weak 
  topology induced by their projections whenever those projections separate points both 
  from each other and from closed sets.

  In particular, we show that the evaluation map from 
  an arbitrary Tychonov space $X$ into $\beta{X}$ is a dense $C^*$-embedding, and then verify the 
  Stone-{\v C}ech Extension Property: any continuous map from $X$ to a compact Hausdorff space $K$ 
  extends 
  uniquely to a continuous map from $\beta{X}$ to $K$.

  \vspace{24pt}

\<close>

theory Stone_Cech
  imports "HOL.Topological_Spaces" 
          "HOL.Set" 
          "HOL-Analysis.Urysohn"

begin

text \<open> 
  Concrete definitions of finite intersections and arbitrary unions, and their
  relationship to the Analysis.Abstract\_Topology versions.
 \<close>

definition finite_intersections_of :: "'a set set \<Rightarrow> 'a set set"
  where "finite_intersections_of S = { (\<Inter> F) | F . F \<subseteq> S \<and> finite' F }"

definition arbitrary_unions_of :: "'a set set \<Rightarrow> 'a set set"
  where "arbitrary_unions_of S = { (\<Union> F) | F . F \<subseteq> S }"

lemma generator_imp_arbitrary_union:
  shows "S \<subseteq> arbitrary_unions_of S"
  unfolding arbitrary_unions_of_def by blast

lemma finite_intersections_container:
  shows "\<forall> s \<in> finite_intersections_of S . \<Union>S \<inter> s = s"
  unfolding finite_intersections_of_def by blast

lemma generator_imp_finite_intersection:
  shows "S \<subseteq> finite_intersections_of S"
  unfolding finite_intersections_of_def by blast

lemma finite_intersections_equiv:
  shows "(finite' intersection_of (\<lambda>x. x \<in> S)) U \<longleftrightarrow> U \<in> finite_intersections_of S"
  unfolding finite_intersections_of_def intersection_of_def
  by auto

lemma arbitrary_unions_equiv:
  shows "(arbitrary union_of (\<lambda> x . x \<in> S)) U \<longleftrightarrow> U \<in> arbitrary_unions_of S"
  unfolding arbitrary_unions_of_def union_of_def arbitrary_def
  by auto


text \<open> 
  Supplementary information about topological bases and the topologies they generate
\<close>

definition base_generated_on_by :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "base_generated_on_by X S = { X \<inter> s | s . s \<in> finite_intersections_of S}"

definition opens_generated_on_by :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "opens_generated_on_by X S = arbitrary_unions_of (base_generated_on_by X S)"

definition base_generated_by :: "'a set set \<Rightarrow> 'a set set"
  where "base_generated_by S = finite_intersections_of S"

definition opens_generated_by :: "'a set set \<Rightarrow> 'a set set"
  where "opens_generated_by S = arbitrary_unions_of (base_generated_by S)"

lemma generators_are_basic:
  shows "S \<subseteq> base_generated_by S"
  unfolding base_generated_by_def finite_intersections_of_def
  by blast

lemma basics_are_open:
  shows "base_generated_by S \<subseteq> opens_generated_by S"
  unfolding opens_generated_by_def arbitrary_unions_of_def
  by blast

lemma generators_are_open:
  shows   "S \<subseteq> opens_generated_by S"
  using generators_are_basic basics_are_open 
  by blast

lemma generated_topspace:
  assumes "T = topology_generated_by S"
  shows "topspace T = \<Union>S" 
  using assms by simp

lemma base_generated_by_alt:
  shows "base_generated_by S = base_generated_on_by (\<Union>S) S"
  unfolding base_generated_by_def base_generated_on_by_def
  using finite_intersections_container[of S]
  by auto

lemma opens_generated_by_alt:
  shows "opens_generated_by S = arbitrary_unions_of (finite_intersections_of S)"
  unfolding opens_generated_by_def base_generated_by_def
  by simp

lemma opens_generated_unfolded:
  shows "opens_generated_by S = {\<Union> A | A . A \<subseteq> { \<Inter> B | B . finite' B \<and> B \<subseteq> S}}"
  apply (simp add: opens_generated_by_alt)
  unfolding finite_intersections_of_def arbitrary_unions_of_def
  by blast

lemma opens_eq_generated_topology:
  shows   "openin (topology_generated_by S) U \<longleftrightarrow> U \<in> opens_generated_by S"
proof -
  have "openin (topology_generated_by S) = arbitrary union_of finite' intersection_of (\<lambda>x. x \<in> S)"
    by (metis generate_topology_on_eq istopology_generate_topology_on topology_inverse')
  also have "\<dots> = arbitrary union_of (\<lambda> U . U \<in> finite_intersections_of S)"
    using finite_intersections_equiv[of S] by presburger
  also have "\<dots> = (\<lambda> U . U \<in> arbitrary_unions_of (finite_intersections_of S))"
    using arbitrary_unions_equiv[of "finite_intersections_of S"] by presburger
  finally show ?thesis 
    using opens_generated_by_alt by auto
qed


section \<open> 
  $C^*$-embedding 
\<close>

abbreviation continuous_from_to 
    :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) set" ("cts[ _, _]") 
  where "continuous_from_to X Y \<equiv> { f . continuous_map X Y f }"

abbreviation continuous_from_to_extensional 
     :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) set" ("cts\<^sub>E[ _, _ ]")
  where "continuous_from_to_extensional X Y \<equiv> (topspace X \<rightarrow>\<^sub>E topspace Y) \<inter> cts[X,Y]"

(* Sets of continuous functions from a space X to any common space satisfying condition P *)
abbreviation continuous_maps_from_to_shared_where ::
    "'a topology \<Rightarrow> ('b topology \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) set \<Rightarrow> bool" ("cts'_on _ to'_shared  _")
  where "continuous_maps_from_to_shared_where X P 
            \<equiv> (\<lambda> fs . (\<exists> Y . P Y \<and> fs \<subseteq> cts[X,Y]))"

(* dense embeddings *)
definition dense_in :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "dense_in T A B \<equiv> T closure_of A = B"

lemma dense_in_closure:
  assumes "dense_in T A B"
  shows   "dense_in (subtopology T B) A B"
  by (metis Int_UNIV_right Int_absorb Int_commute assms closure_of_UNIV closure_of_restrict 
            closure_of_subtopology dense_in_def topspace_subtopology)
abbreviation dense_embedding :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "dense_embedding small big f  \<equiv> (embedding_map small big f) 
                                         \<and> dense_in big (f`topspace small) (topspace big)"

lemma continuous_maps_on_dense_subset:
  assumes "(cts_on X to_shared Hausdorff_space) {f,g}"
and       "dense_in X D (topspace X)"
and       "\<forall> x \<in> D . f x = g x"
shows     "\<forall> x \<in> topspace X . f x = g x"
proof -
  obtain Y where "continuous_map X Y f \<and> continuous_map X Y g \<and> Hausdorff_space Y"
    using assms(1) by auto
  thus ?thesis using assms dense_in_def forall_in_closure_of_eq by fastforce
qed

lemma continuous_map_on_dense_embedding:
  assumes "(cts_on X to_shared Hausdorff_space) {f,g}"
and       "dense_embedding D X e"
and       "\<forall> d \<in> topspace D . (f o e) d = (g o e) d"
shows     "\<forall> x \<in> topspace X . f x = g x"
  using assms continuous_maps_on_dense_subset[of f g X "e ` topspace D"]
  unfolding dense_in_def by fastforce


(* closure of range *)
definition range' :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real set"
  where "range' X f = euclideanreal closure_of (f ` topspace X)"

(* functions defining boundedness  of a C(X) function on its domain *)
abbreviation fbounded_below :: "('a \<Rightarrow> real) \<Rightarrow> 'a topology \<Rightarrow> bool"
  where "fbounded_below f X \<equiv> (\<exists> m . \<forall> y \<in> topspace X . f y \<ge> m)"

abbreviation fbounded_above :: "('a \<Rightarrow> real) \<Rightarrow> 'a topology \<Rightarrow> bool"
  where "fbounded_above f X \<equiv> (\<exists> M . \<forall> y \<in> topspace X . f y \<le> M)"

abbreviation fbounded :: "('a \<Rightarrow> real) \<Rightarrow> 'a topology \<Rightarrow> bool"
  where "fbounded f X \<equiv> (\<exists> m M . \<forall> y \<in> topspace X . m \<le> f y \<and> f y \<le> M)"

lemma fbounded_iff:
  shows "fbounded f X \<longleftrightarrow> fbounded_below f X \<and> fbounded_above f X"
  by auto

abbreviation c_of :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) set" (" C( _ ) ")
  where "C(X) \<equiv> { f . continuous_map X euclideanreal f }"

abbreviation cstar_of :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) set"  (" C*( _ ) ")
  where "C* X \<equiv> { f | f . f \<in> c_of X \<and> fbounded f X }"

definition cstar_id :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  where "cstar_id X = (\<lambda> f \<in> C* X . f)"

abbreviation c_embedding :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "c_embedding S X e \<equiv> embedding_map S X e \<and>
                            (\<forall> fS \<in> C(S) . \<exists> fX \<in> C(X) . \<forall> x \<in> topspace S . fS x  = fX (e x))"

abbreviation cstar_embedding :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "cstar_embedding S X e \<equiv> embedding_map S X e \<and>
                            (\<forall> fS \<in> C*(S) . \<exists> fX \<in> C*(X) . \<forall> x \<in> topspace S . fS x  = fX (e x))"

definition c_embedded :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> bool"
  where "c_embedded S X  \<equiv> (\<exists> e .  c_embedding S X e)"

definition cstar_embedded :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> bool"
  where "cstar_embedded S X \<equiv> (\<exists> e .  cstar_embedding S X e)"

lemma bounded_range_iff_fbounded:
  assumes "f \<in> C X"
  shows "bounded (f ` topspace X) \<longleftrightarrow> fbounded f X"
(is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume ?lhs
  then obtain x e where "\<forall> y \<in> f ` topspace X . dist x y \<le> e"
    using bounded_def[of "f ` topspace X"] by auto
  hence "\<forall> y \<in> f ` topspace X . y \<in> { (x-e) .. (x+e) }"
    using dist_real_def by auto
  thus ?rhs by auto
next
  assume ?rhs
  then obtain m M where "\<forall> y \<in> f ` topspace X . y \<in> {m..M}" by auto
  thus ?lhs using bounded_closed_interval[of m M] subsetI bounded_subset
    by meson
qed


text \<open> 
  Combinations of functions in $C(X)$ and $C^*(X)$ 
\<close>

(* building members of C(X) and C*(X) *)
abbreviation fconst :: "real \<Rightarrow> 'a  \<Rightarrow> real"
  where "fconst v \<equiv> (\<lambda> x  . v)"

definition fmin :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)"
  where "fmin f g = (\<lambda> x . min (f x) (g x))"

definition fmax :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)"
  where "fmax f g = (\<lambda> x . max (f x) (g x))"

(* truncate f above and below specified bounds *)
definition fmid :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  where "fmid f m M = fmax m (fmin f M)"

(* Used to convert a C(X) function into a C*(X) one *)
definition fbound :: "('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  where "fbound f m M = fmid f (fconst m) (fconst M)"

(* alias for continuous_map_real_min *)
lemma fmin_cts:
  assumes "(f \<in> C X) \<and> (g \<in> C X)"
  shows "fmin f g \<in> C X"
  using assms continuous_map_real_min[of X f g] fmin_def[of f g] by auto

(* alias for continuous_map_real_max *)
lemma fmax_cts:
  assumes "(f \<in> C X) \<and> (g \<in> C X)"
  shows "fmax f g \<in> C X"
  using assms continuous_map_real_max[of X f g] fmax_def[of f g] by auto

lemma fmid_cts:
  assumes "(f \<in> C X) \<and> (m \<in> C X) \<and> (M \<in> C X)"
  shows "fmid f m M \<in> C X"
  unfolding fmid_def using assms fmin_cts[of f X M] fmax_cts[of m X "(fmin f M)"] 
  by auto

lemma fconst_cts:
  shows "fconst v \<in> C X"
  by simp

lemma fbound_cts:
  assumes "f \<in> C X"
  shows "fbound f m M \<in> C X"
  unfolding fbound_def 
  using assms fmid_cts[of f X "fconst m" "fconst M"] fconst_cts[of m X] fconst_cts[of M X] 
  by auto
 

text \<open> 
  Bounded and bounding functions 
\<close>

lemma fconst_bounded:
  shows "fbounded (fconst v) X"
  by auto

lemma fmin_bounded_below:
  assumes "fbounded_below f X \<and> fbounded_below g X"
  shows "fbounded_below (fmin f g) X"
proof -
  obtain mf mg where "\<forall> y \<in> topspace X . f y \<ge> mf \<and> g y \<ge> mg" using assms by auto
  hence "\<forall> y \<in> topspace X . fmin f g y \<ge> min mf mg" unfolding fmin_def min_def by auto
  thus ?thesis by auto
qed

lemma fmax_bounded_above:
  assumes "fbounded_above f X \<and> fbounded_above g X"
  shows "fbounded_above (fmax f g) X"
proof -
  obtain mf mg where "\<forall> y \<in> topspace X . f y \<le> mf \<and> g y \<le> mg" using assms by auto
  hence "\<forall> y \<in> topspace X . fmax f g y \<le> max mf mg" unfolding fmax_def max_def by auto
  thus ?thesis by auto
qed

lemma fmid_bounded:
  assumes "fbounded m X \<and> fbounded M X"
  shows "fbounded (fmid f m M) X"
proof -
  obtain mmin mmax Mmin Mmax 
    where "\<forall> y \<in> topspace X . mmin \<le> m y \<and> m y \<le> mmax \<and> Mmin \<le> M y \<and> M y \<le> Mmax"
    using assms by blast
  hence "\<forall> y \<in> topspace X . min mmin Mmin \<le> (fmid f m M y) \<and> (fmid f m M y) \<le> max mmax Mmax"
    unfolding fmid_def fmax_def fmin_def max_def min_def by auto
  thus ?thesis by auto
qed

lemma fbound_bounded:
  shows "fbounded (fbound f m M) X"
  using fmid_bounded[of X "fconst m" "fconst M"] fconst_bounded[of X m] fconst_bounded[of X M]
  unfolding fbound_def by simp


text \<open> 
  Members of $C^*(X)$ 
\<close>

lemma fconst_cstar:
  shows "fconst v \<in> C* X"
  using fconst_cts[of v X] fconst_bounded[of X v]
  by auto

lemma fbound_cstar:
  assumes "f \<in> C X"
  shows "fbound f m M \<in> C* X"
  using assms fbound_cts[of f X m M] fbound_bounded[of X f m M]
  by auto

lemma cstar_nonempty: 
  shows "{} \<noteq> C* X"
  using fconst_cstar by blast


section \<open> 
  Weak topologies 
\<close>

definition funcset_types :: "'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c topology) \<Rightarrow> 'b set \<Rightarrow> bool"
  where "funcset_types S F T I = (\<forall> i \<in> I . F i \<in> S \<rightarrow> topspace (T i))"

lemma cstar_types:
  shows "funcset_types (topspace X) (cstar_id X) (\<lambda>f \<in> C* X . euclideanreal) (C* X)"
  unfolding funcset_types_def 
  by simp

lemma cstar_types_restricted:
  shows "funcset_types (topspace X) (cstar_id X) 
           (\<lambda>f \<in> C* X. (subtopology euclideanreal (range' X f))) (C* X)"
proof -
  have "\<forall> f \<in> C* X . f ` topspace X \<subseteq> range' X f" using range'_def[of X] 
    by (metis closedin_subtopology_refl closedin_topspace closure_of_subset 
              topspace_euclidean_subtopology)
  thus ?thesis unfolding funcset_types_def
    by (simp add: image_subset_iff cstar_id_def)
qed


(* Inverse image of f, restricted to R *)
definition inverse' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'a set"
where "inverse' f source target = { x \<in> source . f x \<in> target }"

lemma inverse'_alt:
  shows "inverse' f s t = (f -` t) \<inter> s"
  using inverse'_def[of f s t] by auto
(*
  The weak topology induced on a set S by a collection of total functions (F i) : S \<Rightarrow> (T i)
  where each (T i) is a topological space.
*)

definition open_sets_induced_by_func :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b topology \<Rightarrow> 'a set set"
  where "open_sets_induced_by_func f source T
              = { (inverse' f source V) | V . openin T V  \<and> f \<in> source \<rightarrow> topspace T}"

definition weak_generators :: "'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c topology) \<Rightarrow> 'b set \<Rightarrow> 'a set set"
  where "weak_generators source funcs tops index 
          = \<Union> { open_sets_induced_by_func (funcs i) source (tops i) |  i. i \<in> index }"

definition weak_base :: "'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c topology) \<Rightarrow> 'b set \<Rightarrow> 'a set set"
  where "weak_base source funcs tops index  = base_generated_by (weak_generators source funcs tops index)"

definition weak_opens :: "'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c topology) \<Rightarrow> 'b set \<Rightarrow> 'a set set"
  where "weak_opens source funcs tops index = opens_generated_by (weak_generators source funcs tops index)"

definition weak_topology :: "'a set  \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c topology) \<Rightarrow> 'b set \<Rightarrow> 'a topology"
  where "weak_topology source funcs tops index 
          = topology_generated_by (weak_generators source funcs tops index)"

lemma weak_topology_alt:
  shows "openin (weak_topology S F T I) U \<longleftrightarrow> U \<in> weak_opens S F T I"
  using weak_topology_def[of S F T I] weak_opens_def[of S F T I]
        opens_eq_generated_topology[of "weak_generators S F T I" U]
  by auto

lemma weak_generators_exist_for_each_point_and_axis:
  assumes "x \<in> S"
and       "funcset_types S F T I"
and       "i \<in> I"
and       "b = inverse' (F i) S (topspace (T i))"
and       "F i \<in> S  \<rightarrow> topspace (T i)"
shows     "x \<in> b \<and> b \<in> weak_generators S F T I"
proof -
  have xprops: "x \<in> {r \<in> S . F i r \<in> topspace (T i)}" 
    using assms(2) funcset_types_def[of S F T I] assms(3) assms(1)
    by blast     
  hence part1: "x \<in> b" using assms(4) inverse'_def[of "F i" S "topspace (T i)"]
    by auto

  have "openin (T i) (topspace (T i))" by simp
  hence "b \<in> open_sets_induced_by_func (F i) S (T i)"
    using open_sets_induced_by_func_def[of "F i" S "T i"] assms(4) assms(5)
          inverse'_def[of "F i" S "topspace (T i)"] xprops
    by auto    
  thus ?thesis using part1 weak_generators_def[of S F T I] assms(3) by auto
qed

lemma weak_generators_topspace:
  assumes "W = weak_topology S F T I"
  shows "topspace W = \<Union> (weak_generators S F T I)"
  using weak_topology_def[of S F T I] assms by simp

lemma weak_topology_topspace:
  assumes "W = weak_topology S F T I"
and       "funcset_types S F T I"
shows     "(I = {} \<longrightarrow> topspace W = {}) \<and> (I \<noteq> {} \<longrightarrow> topspace W = S)"
proof (cases "I = {}")
  case True
  hence "weak_generators S F T I = {}" using assms(1) weak_generators_def[of S F T I] by auto
  hence "topspace W = {}" using assms(1) weak_generators_topspace[of W S F T I] by simp
  then show ?thesis using True by simp
next
  case False
  then obtain i where iprops: "i \<in> I"  by auto
  hence "(F i) ` S \<subseteq> topspace (T i)" 
    using assms(2) unfolding funcset_types_def by auto
  hence "inverse' (F i) S (topspace (T i)) = S"
    using inverse'_def[of "F i" S "topspace (T i)"] by auto
  moreover have "openin (T i) (topspace (T i))" using weak_generators_def by simp
  ultimately have "S \<in> open_sets_induced_by_func (F i) S (T i)"
    using open_sets_induced_by_func_def[of "F i" S "T i"] assms(2) iprops unfolding funcset_types_def
    by auto
  hence "S \<in> weak_generators S F T I" 
    using weak_generators_def[of S F T I] iprops by auto
  hence "S \<subseteq> topspace W" 
    using weak_generators_topspace[of W S F T I] assms by auto

  moreover have "topspace W \<subseteq> S" 
  proof -
    have "openin W (topspace W)" by auto
    hence "topspace W \<in> opens_generated_by (weak_generators S F T I)"
      using assms(1) unfolding weak_topology_def
      using opens_eq_generated_topology[of "weak_generators S F T I" "topspace W"]
      by simp
    then obtain A where "topspace W = \<Union> A \<and> A \<subseteq> {\<Inter> B |B. finite' B \<and> B \<subseteq> weak_generators S F T I}"
      using opens_generated_unfolded[of "weak_generators S F T I"] 
      by auto
    thus ?thesis using assms(2)
      unfolding weak_generators_def open_sets_induced_by_func_def inverse'_def funcset_types_def
      by blast
  qed
  ultimately show ?thesis using False by auto
qed
 
lemma weak_opens_nhood_base:
  assumes "W = weak_topology S F T I"
and       "openin W U"
and       "x \<in> U"
shows     "\<exists> b \<in> weak_base S F T I . x \<in> b \<and> b \<subseteq> U"  
proof -
  define G where "G = weak_generators S F T I"
  hence Wprops: "U \<in> opens_generated_by G" 
    using weak_topology_def[ of S F T I] opens_eq_generated_topology[of G] assms(1) assms(2) 
    by presburger
  then obtain B where Bprops: "B \<subseteq> base_generated_by G \<and> U = \<Union>B"
    unfolding opens_generated_by_def arbitrary_unions_of_def by auto
  then obtain b where "b \<in> base_generated_by G \<and> x \<in> b"
    using assms(3) by blast
  thus ?thesis using G_def weak_base_def[of S F T I]
    by (metis Union_iff Bprops assms(3) subset_eq)
qed

lemma opens_generate_opens:
assumes "\<forall> b \<in> S . openin T b"
shows   "\<forall> U \<in> opens_generated_by S . openin T U"
by (metis assms generate_topology_on_coarsest istopology_openin openin_topology_generated_by 
          opens_eq_generated_topology)

lemma weak_topology_is_weakest:
  assumes "W = weak_topology S F T I"
and       "funcset_types S F T I"
and       "topspace X = topspace W"
and       "\<forall> i \<in> I . continuous_map X (T i) (F i)"
and       "openin W U"
shows     "openin X U"
proof - 
  { fix b assume bprops: "b \<in> weak_generators S F T I"
    then obtain i where iprops: "i \<in> I \<and> b \<in> open_sets_induced_by_func (F i) S (T i)"
      using weak_generators_def[of S F T I] by auto
    hence Sprops: "S = topspace X"
      using assms(1) assms(2) weak_topology_topspace[of W S F T I]
      unfolding funcset_types_def assms(3) 
      by auto
    obtain V where Vprops: "openin (T i) V \<and> b = inverse' (F i) S V"
      using iprops open_sets_induced_by_func_def[of "F i" S "T i"] by auto
    have cts: "continuous_map X (T i) (F i)" using iprops assms(4) by auto
    hence "\<forall>U. openin (T i) U \<longrightarrow> openin X {x \<in> topspace X. F i x \<in> U}" 
      unfolding continuous_map_def by simp
    hence "openin X {x \<in> topspace X. F i x \<in> V}" using Vprops by auto
    hence "openin X b" using Vprops Sprops unfolding inverse'_def by auto
  }
  hence "\<forall> b \<in> weak_generators S F T I . openin X b" by auto
  hence "\<forall> c \<in> weak_opens S F T I . openin X c"
    using assms(5) weak_opens_def[of S F T I] opens_generate_opens[of "weak_generators S F T I" X]
    by auto
  moreover have "U \<in> weak_opens S F T I" 
    using assms(1) weak_topology_def[of S F T I]  weak_opens_def[of S F T I]
          opens_eq_generated_topology[of "weak_generators S F T I" U] assms(5)
    by auto
  ultimately show ?thesis by auto
qed

lemma weak_generators_continuous:
  assumes "W = weak_topology S F T I"
and       "funcset_types S F T I"
and       "i \<in> I"
shows     "continuous_map W (T i) (F i)"
proof -
  have "S = topspace W" using assms(1) assms(2) assms(3) weak_topology_topspace[of W S F T I]
    unfolding funcset_types_def by auto
  hence "F i \<in> topspace W \<rightarrow> topspace (T i)"
    using assms funcset_types_def[of S F T I] by auto
  moreover have "\<forall> V . openin (T i) V \<longrightarrow> openin W {x \<in> topspace W. (F i) x \<in> V}"
  proof -
    { fix V assume Vprops: "openin (T i) V"
      { assume hyp: "inverse' (F i) (topspace W) V \<noteq> {}"
        have "{x \<in> topspace W. (F i) x \<in> V} = inverse' (F i) (topspace W) V" 
          using inverse'_def[of "F i" "topspace W" V] by simp
        moreover have  "(inverse' (F i) (topspace W) V) \<in> open_sets_induced_by_func (F i) S (T i)"
          using Vprops assms weak_topology_topspace[of W S F T I] hyp
          unfolding open_sets_induced_by_func_def funcset_types_def
          by fastforce
        ultimately have "{x \<in> topspace W. (F i) x \<in> V} \<in> weak_generators S F T I"
          using weak_generators_def[of S F T I] assms(3) by auto
        hence "openin W {x \<in> topspace W. (F i) x \<in> V}"
          using assms(1) weak_topology_def[of S F T I] 
                generators_are_open[of "weak_generators S F T I"] 
                opens_eq_generated_topology[of "weak_generators S F T I" "{x \<in> topspace W. (F i) x \<in> V}"]
          by auto
      }
      hence "inverse' (F i) (topspace W) V \<noteq> {} \<longrightarrow> openin W {x \<in> topspace W. (F i) x \<in> V}"
        by auto
      moreover have "inverse' (F i) (topspace W) V = {} \<longrightarrow> openin W {x \<in> topspace W. (F i) x \<in> V}"
        by (metis openin_empty inverse'_def)
      ultimately have "openin W {x \<in> topspace W. (F i) x \<in> V}" by auto
    }
    thus ?thesis by auto
  qed
  ultimately show ?thesis using continuous_map_def by blast
qed

lemma funcset_types_on_empty:
  shows "funcset_types {} F T I"
  unfolding funcset_types_def by simp

lemma weak_topology_on_empty:
  assumes "W = weak_topology {} F T I"
  shows   "\<forall> U . openin W U \<longleftrightarrow> U = {}"
proof -
  have "topspace W = {}" 
    using assms(1) weak_topology_topspace[of W "{}" F T I] funcset_types_on_empty[of F T I] 
    by blast
  thus ?thesis by simp
qed




subsection \<open> 
  Tychonov spaces carry the weak topology induced by $C^*(X)$ 
\<close>

abbreviation tych_space :: "'a topology \<Rightarrow> bool"
  where "tych_space X \<equiv> t1_space X \<and> completely_regular_space X"

abbreviation compact_Hausdorff :: "'a topology \<Rightarrow> bool"
  where "compact_Hausdorff X \<equiv> compact_space X \<and> Hausdorff_space X"

lemma compact_Hausdorff_imp_tych:
  assumes "compact_Hausdorff K"
  shows   "tych_space K"
  by (simp add: Hausdorff_imp_t1_space assms compact_Hausdorff_or_regular_imp_normal_space 
                normal_imp_completely_regular_space_A)

lemma tych_space_imp_Hausdorff:
  assumes "tych_space X"
  shows "Hausdorff_space X"
proof -
  have "Hausdorff_space euclideanreal" by auto
  moreover have "(0::real) \<noteq> (1::real)" by simp
  moreover have "(0::real) \<in> topspace euclideanreal \<and> (1::real) \<in> topspace euclideanreal" by simp
  ultimately have "\<exists> U V . openin euclideanreal U \<and> openin euclideanreal V \<and> (0::real) \<in> U \<and> (1::real) \<in> V \<and> disjnt U V"
    using Hausdorff_space_def[of euclideanreal] by blast
  then obtain U V 
    where UVprops: "openin euclideanreal U \<and> openin euclideanreal V \<and> (0::real) \<in> U \<and> (1::real) \<in> V \<and> disjnt U V"
    by auto

  { fix x y assume xyprops: "x \<in> topspace X \<and> y \<in> topspace X \<and> x \<noteq> y"
    hence "closedin X {y} \<and> x \<in> topspace X - {y}" 
      using assms(1) by (simp add: t1_space_closedin_finite)
    then obtain f 
      where fprops: "continuous_map X (top_of_set {0..1}) f \<and> f x = (0::real) \<and> f y \<in> {1::real}"
      using assms(1) completely_regular_space_def[of X] by blast
    hence freal: "continuous_map X euclideanreal f \<and> f x = 0 \<and> f y = 1" 
      using continuous_map_into_fulltopology by auto

    define U' where "U' = { v \<in> topspace X . f v \<in> U }"
    define V' where "V' = { v \<in> topspace X . f v \<in> V }"
    have "openin X U' \<and> openin X V'" 
      using U'_def V'_def UVprops freal continuous_map_def[of X euclideanreal f] 
      by auto
    moreover have "U' \<inter> V' = {}" using UVprops U'_def V'_def disjnt_def[of U V] by auto
    moreover have "x \<in> U' \<and> y \<in> V'" using UVprops U'_def V'_def fprops xyprops by auto
    ultimately have "\<exists> U' V' . openin X U' \<and> openin X V' \<and> x \<in> U' \<and> y \<in> V' \<and> disjnt U' V' "
      using disjnt_def[of U' V'] by auto
  }
  hence "\<forall> x y . x \<in> topspace X \<and> y \<in> topspace X \<and> x \<noteq> y 
              \<longrightarrow> (\<exists> U' V' . openin X U' \<and> openin X V' \<and> x \<in> U' \<and> y \<in> V' \<and> disjnt U' V' )"
    by auto
  thus ?thesis using Hausdorff_space_def[of X] by blast
qed

(* can restrict to the range-closures of the functions *)
lemma cstar_range_restricted:
  assumes "f \<in> C* X"
  and     "U \<subseteq> topspace euclideanreal"
shows     "inverse' f (topspace X) U = inverse' f (topspace X) (U \<inter> range' X f)"
proof -
  define U' where "U' = U \<inter> range' X f"
  hence "inverse' f (topspace X) U' \<subseteq> inverse' f (topspace X) U"
    unfolding inverse'_def U'_def by auto
  moreover have "inverse' f (topspace X) U \<subseteq> inverse' f (topspace X) U'"
  proof -
    { fix x assume hyp: "x \<in> inverse' f (topspace X) U"
      hence "f x \<in> U \<inter> (f ` topspace X)" unfolding inverse'_def by auto
      hence "f x \<in> U \<inter> range' X f" 
        unfolding range'_def
        by (metis Int_iff closure_of_subset_Int inf.orderE inf_top_left topspace_euclidean)
      hence "x \<in> inverse' f (topspace X) U'" 
        unfolding inverse'_def
        using U'_def hyp inverse'_alt by fastforce
    }
    thus ?thesis 
      by (simp add: subsetI)
  qed
  ultimately show ?thesis using U'_def by simp
qed

lemma weak_restricted_topology_eq_weak:
shows   "weak_topology (topspace X) (cstar_id X) (\<lambda> f \<in> C* X . euclideanreal) (C* X) 
       = weak_topology (topspace X) (cstar_id X) (\<lambda> f \<in> C* X . subtopology euclideanreal (range' X f)) (C* X)"
proof -
  define T  where "T  = (\<lambda> f \<in> C* X . euclideanreal)"
  define T' where "T' = (\<lambda> f \<in> C* X . subtopology euclideanreal (range' X f))"
  define W  where "W  = weak_topology (topspace X) (cstar_id X) T (C* X)"
  define W' where "W' = weak_topology (topspace X) (cstar_id X) T' (C* X)"

  have "\<forall> f \<in> C* X . f \<in> topspace X \<rightarrow> topspace (T f)"
    using T_def unfolding continuous_map_def T_def by auto

  have generators: "weak_generators (topspace X) (cstar_id X) T (C* X) 
                = weak_generators (topspace X) (cstar_id X) T' (C* X)"
  proof -
    (* T \<longrightarrow> T' *)
    have "weak_generators (topspace X) (cstar_id X) T (C* X) 
                \<subseteq> weak_generators (topspace X) (cstar_id X) T' (C* X)"
    proof -
      have "weak_generators (topspace X) (cstar_id X) T (C* X) 
                \<subseteq> weak_generators (topspace X) (cstar_id X) T' (C* X)"
      proof -
        { fix U assume Uprops: "U \<in> weak_generators (topspace X) (cstar_id X) T (C* X)"
          then obtain f where fprops: "f \<in> (C* X) \<and> U \<in> open_sets_induced_by_func f (topspace X) (T f)"
            unfolding weak_generators_def using cstar_id_def[of X]
            by (smt (verit) Union_iff mem_Collect_eq restrict_apply')
          then obtain V where Vprops: "U = inverse' f (topspace X) V \<and> openin (T f) V"
            unfolding open_sets_induced_by_func_def by blast
          hence "U = inverse' f (topspace X) V" by auto
          hence rtp1: "U \<subseteq> topspace X" unfolding inverse'_def by auto

          have rtp2: "openin (T' f) (V \<inter> range' X f)"
          proof -
            have "openin euclideanreal V" using fprops Vprops T_def by auto
            hence "openin (subtopology euclideanreal (range' X f)) (V \<inter> range' X f)"
              by (simp add: openin_subtopology_Int) 
            thus ?thesis using fprops T'_def by auto
          qed

          have rtp3: "f \<in> topspace X \<rightarrow> topspace (T' f)"
          proof -
            have "f ` topspace X \<subseteq> topspace euclideanreal" using fprops by auto
            hence "f ` topspace X \<subseteq> range' X f" unfolding range'_def
              by (meson closure_of_subset)
            thus ?thesis using T'_def fprops by auto
          qed

          hence rtp4: "U = inverse' f (topspace X) (V \<inter> range' X f)"
          proof -
            have "inverse' f (topspace X) (V \<inter> range' X f) \<subseteq> U"
              using Vprops fprops unfolding inverse'_def by auto
            moreover have "U  \<subseteq> inverse' f (topspace X) (V \<inter> range' X f)"
            proof -
              { fix u assume uprops: "u \<in> U"
                hence "f u \<in> V" using Vprops unfolding inverse'_def by auto
                moreover have "f u \<in> range' X f" using uprops rtp1 unfolding range'_def                   
                  by (metis closure_of_subset_Int imageI inf_top_left subset_iff topspace_euclidean)
                ultimately have "u \<in> inverse' f (topspace X) (V \<inter> range' X f)"
                  unfolding inverse'_def range'_def using rtp1 uprops by force
              }
              thus ?thesis by auto
            qed
            ultimately show ?thesis by auto
          qed
          (* ... and hence ... *)
          have "U \<in> open_sets_induced_by_func f (topspace X) (T' f)"
            using rtp1 rtp2 rtp3 rtp4 unfolding open_sets_induced_by_func_def 
            by blast
          hence "U \<in> weak_generators (topspace X) (cstar_id X) T' (C* X)"
            using fprops weak_generators_def[of "(topspace X)" "(cstar_id X)" T' "(C* X)"] cstar_id_def[of X]
            by (smt (verit, best) Sup_upper in_mono mem_Collect_eq restrict_apply')
        }
        thus ?thesis by auto
      qed
      thus ?thesis by auto
    qed
    (* T' \<longrightarrow> T *)
    moreover have "weak_generators (topspace X) (cstar_id X) T' (C* X) 
              \<subseteq> weak_generators (topspace X) (cstar_id X) T (C* X)"
    proof -
      { fix U assume Uprops: "U \<in> weak_generators (topspace X) (cstar_id X) T' (C* X)"
        then obtain f where fprops: "f \<in> (C* X) \<and> U \<in> open_sets_induced_by_func f (topspace X) (T' f)"
          unfolding weak_generators_def using cstar_id_def[of X]
          by (smt (verit) Union_iff mem_Collect_eq restrict_apply')
        (* Vprops:  U = f\<^sup>-\<^sup>1(V) with V open in T' *)
        then obtain V where Vprops: "U = inverse' f (topspace X) V \<and> openin (T' f) V"
          unfolding open_sets_induced_by_func_def by blast
        (* Vbigprops: V = Vbig \<inter> T'   with Vbig open in T *)
        have "T' f = subtopology (T f) (topspace (T' f))" 
          using T_def T'_def fprops unfolding range'_def by auto
        moreover have "openin (T' f) V" using Vprops by simp
        ultimately obtain Vbig where Vbigprops: "openin (T f) Vbig \<and> V = Vbig \<inter> (topspace (T' f))"
          using openin_subtopology[of "T f" "topspace (T' f)"]
          by auto
        (* Vrestrict: Vbig \<inter> T' = Vbig \<inter> range *)
        have Vrestrict: "Vbig \<inter> topspace (T' f) = Vbig \<inter> range' X f" 
          using T'_def fprops by auto
        (* Vrange: f\<^sup>-\<^sup>1(Vbig \<inter> range) = f\<^sup>-\<^sup>1(Vbig) *)
        have Vrange: "inverse' f (topspace X) (Vbig \<inter> range' X f) = inverse' f (topspace X) Vbig"
        proof -
          { fix x assume "x \<in> inverse' f (topspace X) Vbig"
            hence "x \<in> topspace X \<and> f x \<in> Vbig \<inter> range' X f"
              using range'_def[of X f] 
              by (metis Int_iff closure_of_subset image_subset_iff inverse'_alt subset_UNIV 
                  topspace_euclidean vimage_eq)
            hence "x \<in> inverse' f (topspace X) (Vbig \<inter> range' X f)" unfolding inverse'_def by auto
          }
          hence "inverse' f (topspace X) Vbig \<subseteq> inverse' f (topspace X) (Vbig \<inter> range' X f)" by auto
          thus ?thesis unfolding inverse'_def by auto
        qed
        hence "U = inverse' f (topspace X) Vbig \<and> openin (T f) Vbig"
          by (simp add: Vbigprops Vprops Vrestrict)
        moreover have fcstar: "f \<in> C* X" using fprops by simp
        ultimately have "U \<in> open_sets_induced_by_func f (topspace X) (T f)"
          using open_sets_induced_by_func_def[of f "topspace X" euclideanreal] T_def
          by auto
        hence "U \<in> open_sets_induced_by_func (cstar_id X f) (topspace X) (T f) \<and> f \<in>  C* X"
          using fcstar cstar_id_def[of X] by auto
        hence "U \<in> weak_generators (topspace X) (cstar_id X) T  (C* X)"
          using fcstar unfolding weak_generators_def by auto
      }
      thus ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
  thus ?thesis by (simp add: T_def T'_def weak_topology_def cstar_id_def)
qed


subsection \<open> 
  A topology is a weak topology if it admits a continuous function set that separates
  points from closed sets 
\<close>

definition funcset_separates_points :: "'a topology \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> bool"
  where "funcset_separates_points X F I
            = (\<forall> x \<in> topspace X . \<forall> y \<in> topspace X . x \<noteq> y \<longrightarrow> (\<exists> i \<in> I . F i x \<noteq> F i y))"

definition funcset_separates_points_from_closed_sets ::
    "'a topology \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c topology) \<Rightarrow> 'b set \<Rightarrow> bool"
  where "funcset_separates_points_from_closed_sets X F T I
            = (\<forall> x . \<forall> A . closedin X A \<and> x \<in> (topspace X - A) 
                        \<longrightarrow> (\<exists> i \<in> I . F i x  \<notin> (T i) closure_of (F i ` A)))"

lemma funcset_separates_points_from_closed_sets_imp_weak:
  assumes "funcset_separates_points_from_closed_sets X F T I"
and       "\<forall> i \<in> I . continuous_map X (T i) (F i)"
and       "W = weak_topology (topspace X) F T I"
and       "funcset_types (topspace X) F T I"
  shows   "X = W"
proof -
  { fix U assume Uhyp: "openin X U"
    { fix x assume xhyp: "x \<in> U"
      define A where "A = (topspace X) - U"
      have xinX: "x \<in> topspace X" using Uhyp xhyp openin_subset by auto
      moreover have Aprops: "closedin X A \<and> x \<notin> A" using Uhyp xhyp A_def by auto
      ultimately obtain i where iprops: "i \<in> I \<and> F i x  \<notin> (T i) closure_of (F i ` A)"
        using assms(1) funcset_separates_points_from_closed_sets_def[of X F T I] by auto
  
      define V where "V = topspace (T i) - (T i) closure_of (F i ` A)"
      define R where "R = { p \<in> (topspace X) . F i p \<in> V }"
        have Vopen: "openin (T i) V \<and> F i x \<in> V" using iprops xinX V_def
        by (metis DiffI Int_iff assms(2) closedin_closure_of continuous_map_preimage_topspace 
                  openin_diff openin_topspace vimage_eq)
      hence "x \<in> R" using R_def assms(2) xinX by simp
      moreover have "R \<subseteq> U" 
      proof -
        have "F i ` R \<subseteq> V" using R_def by auto
        hence "F i ` R \<inter> (T i) closure_of (F i ` A) = {}" using V_def by auto
        moreover have "F i ` A \<subseteq> (T i) closure_of (F i ` A)" 
          by (metis Aprops assms(2) closure_of_eq continuous_map_subset_aux1 iprops)
        ultimately have "F i ` R \<inter> (F i `A) = {}" by auto
        hence "R \<inter> A = {}" by auto
        thus ?thesis using A_def R_def by auto
      qed
      moreover have "openin W R" 
      proof -
        have "R = inverse' (F i) (topspace X) V" 
          by (simp add: R_def inverse'_def)
        hence "R \<in> open_sets_induced_by_func (F i) (topspace X) (T i)"
          using open_sets_induced_by_func_def[of "F i" "topspace X" "T i"] Vopen
                assms(2) continuous_map_funspace iprops by fastforce
        hence "R \<in> weak_generators (topspace X) F T I"
          using weak_generators_def[of "topspace X" F T I] iprops by auto
        thus ?thesis using generators_are_open[of "weak_generators (topspace X) F T I"]
          opens_eq_generated_topology[of "weak_generators (topspace X) F T I" R] assms(3)
          by (simp add: topology_generated_by_Basis weak_topology_def)
      qed
      ultimately have "x \<in> R \<and> R \<subseteq> U \<and> openin W R" by auto
      hence "\<exists> R . x \<in> R \<and> R \<subseteq> U \<and> openin W R" by auto
    }
    hence "\<forall> x . x \<in> U \<longrightarrow> (\<exists> R . x \<in> R \<and> R \<subseteq> U \<and> openin W R)"
      by auto
    hence "openin W U" by (meson openin_subopen)
  }
  hence XimpW: "\<forall> U . openin X U \<longrightarrow> openin W U" by auto

  moreover have "\<forall> U . openin W U \<longrightarrow> openin X U"
  proof -
    have "topspace X = topspace W" 
      using assms(3) assms(4) weak_topology_topspace[of W "topspace X" F T I]
      by (metis XimpW openin_topspace openin_topspace_empty subtopology_eq_discrete_topology_empty)
    thus ?thesis
      using assms(3) assms(4) assms(2) weak_topology_is_weakest[of W "topspace X" F T I X] 
      by blast
  qed
  ultimately show ?thesis by (meson topology_eq)
qed


text \<open> 
  The canonical functions on a product space: evaluation and projection 
\<close>

definition evaluation_map :: "'a topology \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  where "evaluation_map X F I  = (\<lambda> x \<in> topspace X . (\<lambda> i \<in> I . F i x))"

definition product_projection :: "('a \<Rightarrow> 'b topology) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "product_projection T I = (\<lambda> i \<in> I . (\<lambda> p \<in> topspace (product_topology T I) . p i))"

lemma product_projection:
  shows "\<forall> i \<in> I . \<forall> p \<in> topspace (product_topology T I) . product_projection T I i p = p i"
  using product_projection_def[of T I] by simp

(* evaluation and projection are complementary *)
lemma evaluation_then_projection:
assumes "\<forall> i \<in> I . F i \<in> topspace X \<rightarrow> topspace (T i)"
  shows "\<forall> i \<in> I . \<forall> x \<in> topspace X . ((product_projection T I i) o (evaluation_map X F I)) x = F i x" 
proof -
  { fix i assume iprops: "i \<in> I"
    { fix x assume xprops: "x \<in> topspace X"
      have Fix: "(\<lambda> i \<in> I . F i x) \<in> topspace (product_topology T I)" using xprops assms(1) by auto
      have "((product_projection T I i) o (evaluation_map X F I)) x
                = (product_projection T I i) ((\<lambda> x \<in> topspace X . (\<lambda> i \<in> I . F i x)) x)"
        unfolding evaluation_map_def by auto
      moreover have "\<dots> = (product_projection T I i) (\<lambda> i \<in> I . F i x)" using xprops by simp
      moreover have "\<dots> = (\<lambda> p \<in> topspace (product_topology T I) . p i)  (\<lambda> i \<in> I . F i x)"
        unfolding product_projection_def using iprops by auto
      moreover have "\<dots> = F i x" using Fix iprops by simp
      ultimately have "((product_projection T I i) o (evaluation_map X F I)) x = F i x" by auto
    }
    hence "\<forall> x \<in> topspace X . ((product_projection T I i) o (evaluation_map X F I)) x = F i x" 
      by auto
  }
  thus ?thesis by auto
qed


subsection \<open> 
  A product topology is the weak topology induced by its projections if the projections
  separate points from closed sets. 
\<close>

lemma projections_continuous:
  assumes "P = product_topology T I"
and       "F = (\<lambda> i \<in> I .  product_projection T I i)"
shows     "\<forall>i\<in>I. continuous_map P (T i) (F i)" 
    using assms(1) assms(2) product_projection_def[of T I]
    by fastforce

lemma product_topology_eq_weak_topology:
  assumes "P = product_topology T I"
and       "F = (\<lambda> i \<in> I .  product_projection T I i)"
and       "W = weak_topology (topspace P) F T I"
and       "funcset_types (topspace P) F T I"
and       "funcset_separates_points_from_closed_sets P F T I"
shows     "P = W"
using assms product_projection_def[of T I] projections_continuous
      funcset_separates_points_from_closed_sets_imp_weak[of P F T I W]
    by simp


text \<open> 
  Reducing the domain and minimising the range of continuous functions,
  and related results concerning weak topologies.
\<close>

lemma continuous_map_reduced:
  assumes "continuous_map X Y f"
  shows   "continuous_map (subtopology X S) (subtopology Y (f`S)) (restrict f S)"
  using assms continuous_map_from_subtopology continuous_map_in_subtopology by fastforce

lemma inj_on_imp:
  assumes "inj_on f S"
  shows "\<forall> y . (y \<in> f ` S) \<longleftrightarrow> (\<exists> x \<in> S . y = f x)"
by (simp add: image_iff)

lemma injection_on_intersection:
  assumes "inj_on f S"
and       "B \<noteq> {}"
and       "\<forall> b \<in> B . b \<subseteq> S"
  shows   "f ` (\<Inter>B) = \<Inter>{ f ` b | b . b \<in> B }"
(is "?lhs = ?rhs")
proof -
  have "?lhs \<subseteq> ?rhs" by auto
  moreover have "?rhs \<subseteq> ?lhs"
  proof -
    { fix y assume rhs: "y \<in> ?rhs"
      then obtain b where bprops: "y \<in> f ` b \<and> b \<in> B" 
        by (smt (verit, del_insts) Inter_iff assms(2) ex_in_conv mem_Collect_eq)
      then obtain x where xprops: "x \<in> b \<and> b \<in> B \<and> y = f x" by auto

      (* since y is in all b's ... *)
      have  "\<forall> b \<in> B . y \<in> f ` b" using rhs by auto
      hence "\<forall> b \<in> B . f x \<in> f ` b" using xprops by auto
      hence "\<forall> b \<in> B . x \<in> b" using assms(1)
        by (meson assms(3) in_mono inj_on_image_mem_iff xprops)
      hence "x \<in> \<Inter>B" by auto
      hence "y \<in> ?lhs" using xprops by auto
    }
    thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed


subsection \<open> 
  Evaluation is an embedding for weak topologies 
\<close>

lemma evaluation_is_embedding:
  assumes "X = weak_topology (topspace X) F T I"
and       "P = product_topology T I"
and       "funcset_types (topspace X) F T I"
and       "funcset_separates_points X F I"
shows     "embedding_map X P (evaluation_map X F I)"
proof -
  define ev   where "ev   = evaluation_map X F I"
  define proj where "proj = product_projection T I"
  define R    where "R    = ev ` topspace X"
  define Rtop where "Rtop = subtopology P R"

(* ev is injective *)
  have injective: "inj_on ev (topspace X)"
  proof -
    have sigs: "\<forall> i \<in> I . F i \<in> (topspace X) \<rightarrow> (topspace (T i))"
      using assms(3) funcset_types_def[of "topspace X" F T I]
      by blast

    { fix x y assume xyprops: "x \<in> topspace X \<and> y \<in> topspace X"
      { assume hyp: "x \<noteq> y"
        then obtain i where iprops: "i \<in> I \<and> F i x \<noteq> F i y"
          using assms(4) funcset_separates_points_def[of X F I] hyp xyprops
          by blast
        hence "(proj i) (ev x) \<noteq> (proj i) (ev y)"
          using evaluation_then_projection[of I F X T] proj_def ev_def
          by (simp add: sigs xyprops)          
        hence "ev x \<noteq> ev y" by auto
      }
      hence "ev x = ev y \<longrightarrow> x = y" by auto
    }
    thus ?thesis using inj_on_def by blast
  qed
(* ev is continuous *)
  moreover have ev_cts: "continuous_map X Rtop ev"
  proof -
    have main: "\<forall> i \<in> I . \<forall> x \<in> topspace X . (proj i o ev) x = F i x" 
      using proj_def ev_def product_projection_def[of T I] evaluation_then_projection[of I F X T]
            evaluation_map_def[of X F I]
      by (metis assms(1) assms(3) continuous_map_funspace weak_generators_continuous)
    moreover have "\<forall> i \<in> I . continuous_map X (T i) (F i)" 
      using weak_generators_continuous[of X "topspace X" F T I] assms by auto
    moreover have "\<forall> i \<in> I . \<forall> x \<in> topspace X . F i x = ev x i"
      using product_projection_def[of T I] main ev_def
      by (simp add: evaluation_map_def[of X F I])
    moreover have "ev ` topspace X \<subseteq> extensional I"
      using ev_def extensional_def assms evaluation_map_def[of X F I]
      by fastforce
    ultimately have "continuous_map X P ev" 
      using assms proj_def ev_def Rtop_def continuous_map_componentwise[of X T I ev]
            continuous_map_eq by fastforce
    thus ?thesis
      using Rtop_def R_def continuous_map_in_subtopology by blast
  qed
(* ev is open *)
  moreover have "open_map X Rtop ev"
  proof -
    have open_map_on_gens: "\<forall> U \<in> weak_generators (topspace X) F T I . openin Rtop (ev ` U)"
    proof -
      { define Rs where "Rs = (\<lambda> i \<in> I . (F i ` topspace X))"
        define Rtops where "Rtops = (\<lambda> i \<in> I . subtopology (T i) (Rs i))"

        fix U assume "U \<in> weak_generators (topspace X) F T I"
        then obtain i where iprops: "i \<in> I \<and> U \<in> open_sets_induced_by_func (F i) (topspace X) (T i)"
          using assms weak_generators_def[of "topspace X" F T I] by auto
        then obtain V 
          where Vprops: "openin (T i) V \<and> U = inverse' (F i) (topspace X) V"
          using open_sets_induced_by_func_def[of "F i" "topspace X" "T i"]
          by blast
        hence Uprops: "openin (T i) V \<and> U = { x \<in> topspace X . F i x \<in> V }"
          using inverse'_def[of "F i" "topspace X" V] by auto
        moreover have "\<forall> x \<in> topspace X . F i x = ((proj i) o ev) x"
          using evaluation_then_projection[of I F X T] assms(3) 
                funcset_types_def[of "topspace X" F T I] iprops
                proj_def ev_def
          by auto
        hence "U = { x \<in> topspace X . ((proj i) o ev) x \<in> V }" using Uprops by auto
        hence "ev ` U = { y \<in> R . (proj i) y \<in> V }" using R_def by auto
        moreover have "{ y \<in> R . (proj i) y \<in> V } = R \<inter> ((proj i) -` V )"
          by auto
        moreover have "continuous_map P (T i) (proj i)" 
          using continuous_map_product_projection[of i I T] iprops proj_def
                product_projection_def[of T I] assms(2)  by auto
        ultimately have summary: "openin (T i) V \<and> continuous_map P (T i) (proj i) 
                        \<and> (ev ` U) = R \<inter> ((proj i) -` V )"  by auto
        hence "\<forall>U. openin (T i) U \<longrightarrow> openin P {x \<in> topspace P. proj i x \<in> U}"
          using continuous_map_def[of P "T i" "proj i"] by auto
        hence "openin P ((proj i -` V) \<inter> topspace P)"
          using summary by blast
        moreover have "R \<subseteq> topspace P" 
          using R_def ev_def evaluation_map_def[of X F I] assms(3) 
                funcset_types_def[of "topspace X" F T I]
          by (metis Rtop_def ev_cts continuous_map_image_subset_topspace 
              continuous_map_into_fulltopology)
        ultimately have "openin Rtop ((proj i -` V) \<inter> R)"
          using Rtop_def
          by (metis inf.absorb_iff2 inf_assoc openin_subtopology)
        hence "openin Rtop (ev ` U)" using summary 
          by (simp add: inf_commute)
      }
      thus ?thesis by auto
    qed

    have open_map_on_basics: "\<forall> U \<in> weak_base (topspace X) F T I . openin Rtop (ev ` U)"
    proof -
      have Ugens: "\<Union> (weak_generators (topspace X) F T I) = topspace X"
        using assms(1) weak_generators_topspace by blast

      { fix U assume bprops: "U \<in> weak_base (topspace X) F T I"
        hence "U  \<in> finite_intersections_of (weak_generators (topspace X) F T I)"
          by (simp add: base_generated_by_def weak_base_def)
        then obtain b where bprops: "b \<subseteq> weak_generators (topspace X) F T I \<and> finite' b \<and> U = \<Inter>b"
          unfolding finite_intersections_of_def
          by auto
        hence "finite' b \<and> (\<forall> g \<in> b . openin Rtop (ev ` g))" using open_map_on_gens by auto
        hence "openin Rtop (\<Inter> { (ev ` g) | g . g \<in> b })" by auto
        hence "openin Rtop (ev ` \<Inter>b)" 
          using injection_on_intersection[of ev "topspace X" b] bprops 
          by (metis (no_types, lifting) Ugens Union_upper in_mono injective)
        hence "openin Rtop (ev ` U)" using bprops by metis
      }
      thus ?thesis by auto
    qed
    hence open_map_on_opens: "\<forall> U \<in> weak_opens (topspace X) F T I . openin Rtop (ev ` U)"
      by (smt (verit, ccfv_SIG) image_iff image_mono openin_subopen weak_opens_nhood_base 
          weak_topology_alt)
    thus ?thesis 
      using opens_eq_generated_topology[of "weak_generators (topspace X) F T I"] assms(1)
      unfolding weak_topology_def using open_map_def[of X Rtop]
      by (simp add: weak_opens_def)
  qed
(* so ev is a homeomorphism X \<longleftrightarrow> Rtop *)
  ultimately have "homeomorphic_map X Rtop ev"
    by (metis R_def Rtop_def bijective_open_imp_homeomorphic_map continuous_map_image_subset_topspace 
        continuous_map_into_fulltopology topspace_subtopology_subset)
  thus ?thesis using embedding_map_def[of X P ev] ev_def R_def Rtop_def
    by auto
qed
(* end of proof that ev is an embedding *)


section \<open> 
  Compactification
\<close>

subsection \<open> Definition \<close>

lemma embedding_map_id: 
  assumes "S \<subseteq> topspace X"
  shows   "embedding_map (subtopology X S) X id" 
  using assms embedding_map_def topspace_subtopology_subset 
  by fastforce

(* X is densely embedded in compactification K via a known evaluation *)
definition compactification_via :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a topology \<Rightarrow> 'b topology \<Rightarrow> bool"
  where "compactification_via f X K \<equiv> compact_space K \<and> dense_embedding X K f"

(* X is densely embedded in compactification K via an unknown evaluation *)
definition compactification :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> bool"
  where "compactification X K  = (\<exists> f . compactification_via f X K)"

lemma compactification_compactification_via:
  assumes "compactification_via f X K"
  shows   "compactification X K"
  using assms unfolding compactification_def by fastforce



subsection \<open> 
  Example: The Alexandroff compactification of a non-compact locally-compact Hausdorff space 
\<close>

lemma Alexandroff_is_compactification_via_Some: 
  assumes "\<not> compact_space X \<and>  Hausdorff_space X \<and> locally_compact_space X"
  shows "compactification_via Some X (Alexandroff_compactification X)"
  using assms compact_space_Alexandroff_compactification
              embedding_map_Some
              Alexandroff_compactification_dense
              compactification_via_def
  by (metis dense_in_def)


subsection \<open> 
  Example: The closure of a subset of a compact space 
\<close>

lemma compact_closure_is_compactification:
  assumes "compact_space K"
and       "S \<subseteq> topspace K"
shows     "compactification_via id (subtopology K S)  (subtopology K (K closure_of S))"
proof -
  define big where "big = subtopology K (K closure_of S)"
  define small where "small = subtopology K S"
  have "dense_in big (id ` topspace small) (topspace big)"
    by (metis dense_in_def big_def small_def assms(2) closedin_topspace closure_of_minimal 
              closure_of_subset closure_of_subtopology_open id_def image_id inf.orderE 
              openin_imp_subset openin_subtopology_refl topspace_subtopology_subset)
  moreover have "embedding_map small big id"
    by (metis assms(2) big_def closure_of_subset_Int embedding_map_in_subtopology id_apply 
              embedding_map_id image_id small_def topspace_subtopology)
  ultimately have "dense_embedding small big id" by blast
  moreover have "compact_space big"
    by (simp add: big_def assms(1) closedin_compact_space compact_space_subtopology)
  ultimately show ?thesis 
    unfolding compactification_via_def using small_def big_def by blast
qed


subsection \<open> 
  Example: A compact space is a compactification of itself 
\<close>

lemma compactification_of_compact:
  assumes "compact_space K"
  shows   "compactification_via id K K"
  using compact_closure_is_compactification[of K "topspace K"]
  by (simp add: assms)


subsection \<open> 
  Example: A closed non-trivial real interval is a compactification of its interior 
\<close>

lemma closed_interval_interior:
  shows "{a::real <..< b} = interior {a..b}"
  by auto

lemma open_interval_closure:
  shows "(a < (b::real)) \<longrightarrow> {a .. b} = closure {a <..< b}" 
    using closure_greaterThanLessThan[of a b] by simp

lemma closed_interval_compactification:
  assumes "(a::real) < b"
and       "open_interval = subtopology euclideanreal {a<..<b}"
and       "closed_interval = subtopology euclideanreal {a..b}"
  shows "compactification open_interval closed_interval"
proof -
  have "compact_space closed_interval" using assms(3)
    using compact_space_subtopology compactin_euclidean_iff by blast
  moreover have "Hausdorff_space closed_interval"
    by (simp add: Hausdorff_space_subtopology assms(3))
  moreover have "{a<..<b} \<subseteq> topspace closed_interval"
    by (simp add: assms(3) greaterThanLessThan_subseteq_atLeastAtMost_iff)
  ultimately have "compactification_via id open_interval closed_interval"
    using compact_closure_is_compactification[of closed_interval "{a<..<b}"]
          open_interval_closure[of a b]
    by (metis assms closedin_self closedin_subtopology_refl closure_of_subtopology 
              euclidean_closure_of subtopology_subtopology subtopology_topspace 
              topspace_subtopology_subset)
  thus ?thesis using
          compactification_compactification_via[of id open_interval closed_interval]
    by auto
qed


section \<open> The Stone-{\v C}ech compactification of a Tychonov space \<close>


(* smallest closed interval containing the range of a bounded function *)
lemma compact_range':
  assumes "f \<in> C* X"
  shows   "compact (range' X f)"
proof -
  obtain m M where mM: "\<forall> y \<in> topspace X . f y \<in> {m..M}" using assms by auto
  hence "f ` topspace X \<subseteq> {m..M}" by auto
  hence "range' X f \<subseteq> euclideanreal closure_of {m..M}" 
    unfolding range'_def by (meson closure_of_mono)
  moreover have "compact {m..M}" by auto
  ultimately show ?thesis
    by (metis closed_Int_compact closed_atLeastAtMost closed_closedin closedin_closure_of 
              closure_of_closedin inf.order_iff range'_def)
qed

lemma c_range_nonempty:
  assumes "f \<in> C(X)"
and       "topspace X \<noteq> {}"
shows   "range' X f \<noteq> {}"
proof -
  have "f ` topspace X \<noteq> {}" using assms by blast
  thus ?thesis unfolding range'_def by simp
qed

lemma cstar_range_nonempty:
  assumes "f \<in> C* X"
and       "topspace X \<noteq> {}"
shows     "range' X f \<noteq> {}"
  using assms c_range_nonempty[of f X]
  by auto

(* C*(X) separates points from closed subsets in a tych_space *)
lemma cstar_separates_tych_space:
  assumes "tych_space X"
  shows "funcset_separates_points_from_closed_sets X (cstar_id X) (\<lambda>f \<in> C* X. euclideanreal) (C* X)
         \<and> funcset_separates_points X (cstar_id X) (C* X)"
proof -
  { fix x S assume "closedin X S \<and> x \<in> topspace X - S"
    then obtain f 
      where fprops: "continuous_map X (top_of_set {0..(1::real)}) f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
      using assms completely_regular_space_def[of X] 
      by presburger
    hence "f \<in> C X" 
      using continuous_map_into_fulltopology[of X euclideanreal "{0..(1::real)}" f]
      by auto
    moreover have "fbounded f X"
    proof -
      have "\<forall> x \<in> topspace X . 0 \<le> f x \<and> f x \<le> 1" using fprops 
        by (simp add: continuous_map_in_subtopology image_subset_iff)
      thus ?thesis by auto
    qed
    ultimately have f_in_cstar: "f \<in> (C* X)" by auto

    moreover have f_separates: "f x \<notin> (euclideanreal closure_of (f ` S))"
    proof -
      have "closedin euclideanreal (f ` S)"
        by (metis closed_closedin closed_empty closed_singleton fprops subset_singletonD)
      moreover have "f x \<notin> f ` S" using fprops by auto
      thus ?thesis using calculation by auto
    qed
    ultimately have "\<exists> f \<in> C* X . f x \<notin> euclideanreal closure_of (f ` S)" by auto
  }
  hence rtp1: "funcset_separates_points_from_closed_sets X (cstar_id X) (\<lambda>f \<in> C* X. euclideanreal) (C* X)"
    using cstar_id_def[of X] unfolding funcset_separates_points_from_closed_sets_def by auto

  moreover have "funcset_separates_points X (cstar_id X) (C* X)" 
  proof -
    { fix x y assume "{x,y} \<subseteq> topspace X \<and> x \<noteq> y"
      hence "closedin X {y} \<and> x \<in> topspace X - {y}" 
        using assms by (simp add: t1_space_closedin_finite)
      hence "\<exists>f \<in> C* X  . cstar_id X f x \<notin> (\<lambda>f\<in> C* X  . euclideanreal) f closure_of cstar_id X f ` {y}" 
        using funcset_separates_points_from_closed_sets_def[of X "cstar_id X" "\<lambda> f \<in> C* X . euclideanreal" "C* X"]
              rtp1 by presburger
      hence "\<exists> f \<in> C* X . f x \<noteq> f y"  
        using cstar_id_def[of X] t1_space_closedin_finite[of euclideanreal] by auto
    }
    thus ?thesis using cstar_id_def[of X] unfolding funcset_separates_points_def by auto
  qed
  ultimately show ?thesis by auto
qed


text \<open> 
  The product topology induced by $C^*(X)$ on a Tychonov space.
\<close>

(* scT identifies the compact component of product_topology associated with each f in C*(X) *)
definition scT :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real topology"
  where "scT X = (\<lambda> f \<in> C* X . subtopology euclideanreal (range' X f))"

(* sometimes we want the whole of euclideanreal, not just the range' *)
definition scT_full :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real topology"
  where "scT_full X = (\<lambda> f \<in> C* X . euclideanreal)"

(* the product_topology cube containing \<beta>X *)
definition scProduct :: "'a topology \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) topology"
  where "scProduct X = product_topology (scT X) (C* X)"

(* the projection operator for scProduct *)
definition scProject :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> real"
  where "scProject X = product_projection (scT X) (C* X)"

(* the evaluation operator for scProduct (called scEmbed, as we'll see below that it's an embedding *)
definition scEmbed :: "'a topology \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where "scEmbed X = evaluation_map X (cstar_id X) (C* X)"

lemma scT_images_compact_Hausdorff:
  shows "\<forall> f \<in> C* X . compact_Hausdorff (scT X f)"
proof -
  have T: "\<forall> f \<in> C* X . scT X f = subtopology euclideanreal (range' X f)"
    unfolding scT_def by simp
  thus ?thesis using range'_def[of X f]
    by (simp add: Hausdorff_space_subtopology compact_range' compact_space_subtopology)
qed

lemma scT_images_bounded:
  shows "\<forall> f \<in> C* X . bounded (topspace (scT X f))"
  using scT_images_compact_Hausdorff[of X] scT_def[of X]
  by (simp add: compact_imp_bounded compact_range')

lemma scProduct_compact_Hausdorff:
  shows "compact_Hausdorff (scProduct X)"
  unfolding scProduct_def using scT_images_compact_Hausdorff[of X]
  using compact_space_product_topology 
  by (metis (no_types, lifting) compact_Hausdorff_imp_regular_space regular_space_product_topology 
            regular_t0_eq_Hausdorff_space t0_space_product_topology)


text \<open> 
  The Stone-{\v C}ech compactification of a Tychonov space and its extension properties 
\<close>

lemma tych_space_weak:
  assumes "tych_space X"
shows     "X = weak_topology (topspace X) (cstar_id X) (scT X) (C* X)"
proof (cases "topspace X = {}")
  case True 
  then show ?thesis 
    using weak_topology_on_empty[of "weak_topology (topspace X) (cstar_id X) (scT X) (C* X)"]
          topology_eq by fastforce
next
  case False 
  define W where "W = weak_topology (topspace X) (cstar_id X) (scT X) (C* X)"
    
  hence "topspace W = topspace X"
    using cstar_types_restricted[of X] scT_def[of X] W_def cstar_nonempty[of X]
          weak_topology_topspace[of W "topspace X" "cstar_id X" "scT X" "C* X"]
    by auto
  moreover have "\<forall>f\<in> C* X  . continuous_map X (scT X f) f"
    unfolding scT_def range'_def
    by (metis (mono_tags, lifting) closure_of_subset continuous_map_image_subset_topspace 
              continuous_map_in_subtopology mem_Collect_eq restrict_apply')
  ultimately have  "\<forall> U . openin W U \<longrightarrow> openin X U" 
    using W_def cstar_types_restricted[of X] scT_def[of X] cstar_id_def[of X]
          weak_topology_is_weakest[of W "(topspace X)" "(cstar_id X)" "(scT X)"  "C* X" X]
    by (smt (verit, ccfv_threshold) restrict_apply')
   
  moreover have "\<forall> U . openin X U \<longrightarrow> openin W U" 
  proof -
    { fix U assume props: "openin X U"
      { fix x assume xprops: "x \<in> U"
        hence x_in_X: "x \<in> topspace X" 
          using openin_subset props by fastforce
  
        define S where "S = topspace X - U"
        hence props': "x \<in> topspace X - S \<and> closedin X S" 
          using props openin_closedin_eq xprops  by fastforce
        then obtain f where fprops: "continuous_map X (top_of_set {0..1::real}) f \<and> f x = 0 \<and> f ` S \<subseteq> {1}" 
          using assms(1) completely_regular_space_def[of X]
          by meson
        then obtain ffull 
          where ffullprops: "(ffull \<in> C X) \<and> ffull x = (0::real) \<and> ffull ` S \<subseteq> {1}"
          using continuous_map_into_fulltopology 
          by (metis mem_Collect_eq)
        
        define F where "F = fbound ffull 0 1"
        hence Fcstar: "F \<in> C* X" using ffullprops fbound_cstar[of ffull X 0 1] by auto
        hence Ftype: "F \<in> topspace X \<rightarrow> topspace euclideanreal"
          unfolding continuous_map_def by auto
  
        define I where "I = {(-1) <..< 1::real}"
        hence Iprops: "openin euclideanreal I" 
          by (simp add: openin_delete)
  
        define V where "V = inverse' F (topspace X) I"
  
        have crprops: "F x = 0 \<and> F ` S \<subseteq> {1}"
          using ffullprops F_def 
          unfolding fbound_def fmid_def fmin_def fmax_def min_def max_def
          by auto
  
        hence "V \<subseteq> U" 
        proof -
          { fix v assume "v \<in> V"
            hence "v \<in> topspace X \<and> F v \<in> I" unfolding inverse'_def V_def by auto
            hence "v \<in> U" using S_def crprops I_def by auto
          }
          thus ?thesis by auto
        qed
        moreover have "x \<in> V" 
          using crprops I_def x_in_X unfolding inverse'_def V_def by auto  
        moreover have "openin W V" (* sledgehammer needs step-by-step guidance *)
        proof -
          have "V \<in> open_sets_induced_by_func F (topspace X) euclideanreal"
            unfolding open_sets_induced_by_func_def using Ftype V_def Iprops
            by blast
          moreover have "open_sets_induced_by_func F (topspace X) euclideanreal \<subseteq>
                         weak_generators (topspace X) (cstar_id X) (scT_full X) (C* X)"
            using weak_generators_def[of "topspace X" "(cstar_id X)" "scT_full X" "C* X"] 
                  scT_full_def[of X] cstar_id_def[of X] Fcstar 
            by (smt (verit, ccfv_SIG) Sup_upper mem_Collect_eq restrict_apply')
          ultimately have "V \<in> weak_generators (topspace X) (cstar_id X) (scT_full X) (C* X)"
            by auto
          hence "openin (topology_generated_by (weak_generators (topspace X) (cstar_id X) (scT_full X) (C* X))) V"
            using generators_are_open[of "weak_generators (topspace X) (cstar_id X) (scT_full X) (C* X)"]
                  topology_generated_by_Basis by blast
          thus ?thesis 
            using W_def weak_restricted_topology_eq_weak[of X]
            unfolding scT_def scT_full_def weak_topology_def
            by simp
        qed
        ultimately have "x \<in> V \<and> V \<subseteq> U \<and> openin W V" by auto
        hence "\<exists> V . x \<in> V \<and> V \<subseteq> U \<and> openin W V" by auto
      }
      hence "\<forall> x \<in> U . \<exists> V . x \<in> V \<and> V \<subseteq> U \<and> openin W V" by blast
      hence "openin W U" by (meson openin_subopen)
    }
    thus ?thesis by auto
  qed
  ultimately have "\<forall> U . openin X U \<longleftrightarrow> openin W U" by auto
  hence "X = W" by (simp add: topology_eq)
  thus ?thesis using W_def by simp
qed


subsection \<open> 
  Definition of $\beta{X}$ 
\<close>

definition scEmbeddedCopy :: "'a topology \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) set"
  where "scEmbeddedCopy X = scEmbed X ` topspace X"

definition scCompactification :: "'a topology \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) topology" ("\<beta> _")
  where "scCompactification X 
            = subtopology (scProduct X) ((scProduct X) closure_of (scEmbeddedCopy X))"

lemma sc_topspace:
  shows "topspace (\<beta> X) = (scProduct X) closure_of (scEmbeddedCopy X)"
  using scCompactification_def[of X] closure_of_subset_topspace by force

lemma scProject': 
  shows "\<forall> f \<in> C* X . \<forall> p \<in> topspace (\<beta> X) . scProject X f p = p f"
proof -
  have "topspace (\<beta> X) \<subseteq> topspace (scProduct X)" unfolding scCompactification_def by auto
  thus ?thesis 
    unfolding scProject_def product_projection_def scProduct_def
    by auto
qed
    
        
text \<open> 
  Evaluation densely embeds Tychonov $X$ in $\beta{X}$ 
\<close>

lemma dense_embedding_scEmbed:
  assumes "tych_space X"
  shows   "dense_embedding X (\<beta> X) (scEmbed X)"
proof -
  define W where "W = weak_topology (topspace X) (cstar_id X) (\<lambda>f \<in> C* X. euclideanreal) (C* X)"
  hence "X = W" using assms tych_space_weak[of X]
    by (metis (mono_tags, lifting) scT_def weak_restricted_topology_eq_weak)

  hence Xweak: "X = weak_topology (topspace X) (cstar_id X) (scT X) (C* X)"
    using scT_def[of X] W_def cstar_id_def[of X]
          weak_restricted_topology_eq_weak[where X ="X"] by auto
  moreover have "scProduct X = product_topology (scT X) (C* X)" using scProduct_def[of X] by auto
  moreover have "funcset_types (topspace X) (cstar_id X) (scT X) (C* X)"
    unfolding scT_def using cstar_types_restricted[of X] by auto
  moreover have "funcset_separates_points X (cstar_id X) (C* X)"
    using cstar_separates_tych_space[of X] assms(1) by auto
  moreover have "(C* X) \<noteq> {}" using cstar_nonempty by auto
  ultimately have "embedding_map X (scProduct X) (scEmbed X)"
    using evaluation_is_embedding[of X "cstar_id X" "scT X" "C* X" "scProduct X"]
    unfolding scProduct_def scEmbed_def
    by auto
  hence embeds: "embedding_map X (\<beta> X) (scEmbed X)"
    unfolding scCompactification_def 
    by (metis closure_of_subset embedding_map_in_subtopology scEmbeddedCopy_def subtopology_topspace)
  moreover have "dense_in (\<beta> X) (scEmbed X ` topspace X) (topspace (\<beta> X))"
    unfolding dense_in_def using scCompactification_def[of X] scEmbeddedCopy_def[of X]
    by (metis Int_absorb1 closure_of_subset closure_of_subset_topspace closure_of_subtopology 
              embedding_map_in_subtopology embeds set_eq_subset subtopology_topspace 
              topspace_subtopology_subset)
  ultimately show ?thesis by auto
qed


subsection \<open> 
  $\beta{X}$ is a compactification of $X$ 
\<close>

lemma scCompactification_compact_Hausdorff:
  assumes "tych_space X"
  shows   "compact_Hausdorff (\<beta> X)"
  using scCompactification_def[of X] scProduct_compact_Hausdorff[of X]
  by (simp add: Hausdorff_space_subtopology closedin_compact_space compact_space_subtopology)

lemma scCompactification_is_compactification_via_scEmbed:
  assumes "tych_space X"
  shows "compactification_via (scEmbed X) X (\<beta> X)"
  using compactification_via_def[of "scEmbed X" X "\<beta> X"]
        scCompactification_compact_Hausdorff[of X]
        dense_embedding_scEmbed[of X] assms 
  by auto

lemma scCompactification_is_compactification:
  assumes "tych_space X"
  shows   "compactification X (\<beta> X)"
  using assms compactification_compactification_via
              scCompactification_is_compactification_via_scEmbed
  by blast

lemma scEvaluation_range: 
  assumes "x \<in> topspace X"
and       "tych_space X"
shows     "(\<lambda> f \<in> C* X . f x) \<in> topspace (product_topology (scT X)  C* X)"
proof -
  have "funcset_types (topspace X) (cstar_id X) (\<lambda>f\<in> C* X  . top_of_set (range' X f))  C* X"
    using cstar_types_restricted[of X] by auto
  hence "\<forall>f\<in> C* X  . f   \<in> topspace X \<rightarrow> topspace (scT X f)"
    unfolding funcset_types_def scT_def cstar_id_def[of X] by auto
  thus ?thesis using topspace_product_topology[of "scT X" "C* X"] assms(1) by auto
qed

lemma scEmbed_then_project:
  assumes "f \<in> C* X"
and       "x \<in> topspace X"
and       "tych_space X"
shows     "scProject X f (scEmbed X x) = f x"
proof -
  have fequiv: "\<forall> y \<in> topspace X . (\<lambda> g \<in> C* X . (cstar_id X) g y) = (\<lambda> g \<in> C* X . g y)" 
  proof -
    { fix y assume yprops: "y \<in> topspace X"
      hence "\<forall> g \<in> C* X .  (cstar_id X) g y = g y" unfolding cstar_id_def by auto
      hence "(\<lambda> g \<in> C* X . (cstar_id X) g y) = (\<lambda> g \<in> C* X . g y)" 
        by (meson restrict_ext)
    }
    thus ?thesis by auto
  qed
  
  have "scProject X f (scEmbed X x) = scProject X f (evaluation_map X (cstar_id X) (C* X) x)"
    unfolding scEmbed_def by auto
  also have "\<dots> = scProject X f (\<lambda>g\<in> C* X  . g x)"
    unfolding evaluation_map_def using assms(2) fequiv by auto
  also have "\<dots> = (\<lambda>g\<in> C* X. \<lambda>p\<in>topspace (product_topology (scT X) (C* X)). p g)  f (\<lambda>g\<in> C* X . g x)"
    unfolding  product_projection_def scProject_def by auto
  also have "\<dots> = (\<lambda>p\<in>topspace (product_topology (scT X) (C* X)). p f)  (\<lambda>g\<in> C* X . g x)"
    using assms(1) by auto 
  also have "\<dots> =  f x" using scEvaluation_range[of x X] assms by auto
  ultimately show ?thesis by auto
qed


subsection \<open> 
  Evaluation is a $C^*$-embedding of $X$ into $\beta{X}$ 
\<close>

definition scExtend :: "'a topology \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> real"
  where "scExtend X = (\<lambda> f \<in> C* X . restrict (scProject X f) (topspace (\<beta> X)))"

(* (scExtend X) extends functions in C*(X) to functions on topspace (\<beta> X) *)
proposition scExtend_extends:
  assumes "tych_space X"
  shows   "\<forall> f \<in> C* X . \<forall> x \<in> topspace X . f x = (scExtend X f) (scEmbed X x)"
proof -
  { fix f assume fprops: "f \<in> C* X"
    have "\<forall> x \<in> topspace X . (scProject X f) (scEmbed X x) = (scExtend  X f) (scEmbed X x) "
    proof - 
      { fix x assume xprops: "x \<in> topspace X"
        define p where pprops: "p = scEmbed X x"

        hence "scExtend X f p = (restrict (scProject X f) (topspace \<beta> X)) p" 
          using xprops fprops unfolding scExtend_def by auto
        moreover have "p \<in> topspace \<beta> X"
          using assms(1) pprops dense_embedding_scEmbed[of X]
                scCompactification_def[of X] scEmbeddedCopy_def[of X]
          by (metis (no_types, lifting) embedding_map_in_subtopology image_eqI
                    in_mono subtopology_topspace xprops)
        ultimately have "scExtend X f p =  scProject X f p" 
          using pprops scEmbeddedCopy_def[of X] scEmbed_def[of X] evaluation_map_def by auto 
      }
      thus ?thesis by auto
    qed
    hence "\<forall> x \<in> topspace X . f x = (scExtend X f) (scEmbed X x)"  
      using scEmbed_then_project[of f X] assms(1) fprops by auto
  }
  thus ?thesis by auto
qed

lemma scExtend_extends_cstar:
  assumes "tych_space X"   
  shows   "\<forall> f \<in> C* X . (\<forall> x \<in> topspace X . f x = (scExtend X f) (scEmbed X x)) \<and> scExtend X f \<in> C* (\<beta> X)"
proof -
  define e where "e = scExtend X"
  { fix f assume fprops: "f \<in> C* X"
    hence  "continuous_map (scProduct X) (scT X f) (scProject X f)"
      using scProduct_def[of X] scProject_def[of X] 
            projections_continuous[of "scProduct X" "scT X" "C* X" "scProject X"]
            product_projection_def[of "scT X" "C* X"] 
      by (metis (no_types, lifting) restrict_extensional extensional_restrict)
    hence "continuous_map (\<beta> X) (scT X f) (scProject X f)"
      by (simp add: continuous_map_from_subtopology scCompactification_def)
    hence c_embedded_f: "continuous_map (\<beta> X) (scT X f) (scExtend X f)"
      using scExtend_def[of X] fprops by force
    moreover have fbounded_f:"fbounded (scExtend X f) (\<beta> X)"
    proof -
      obtain m M where "f ` topspace X \<subseteq> {m..M}" using fprops by force
      hence extend_on_embedded: "e f ` (scEmbeddedCopy X) \<subseteq> {m..M}"
        using scExtend_extends[of X] e_def
        by (smt (verit, ccfv_SIG) fprops assms(1) image_cong image_image scEmbeddedCopy_def)
      hence "e f ` (topspace (\<beta> X)) \<subseteq> {m..M}"
      proof -
        { fix p assume pprops: "p \<in> e f ` (topspace (\<beta> X))"
          then obtain v where vprops: "v \<in> topspace (\<beta> X) \<and> p = e f v" by auto
          { fix U assume Uprops: "openin (scT X f) U \<and> p \<in> U"
            define V where "V = inverse' (e f) (topspace (\<beta> X)) U"
            hence "openin (\<beta> X) V"
              using c_embedded_f Uprops e_def unfolding continuous_map_def inverse'_def
              by auto
            moreover have "topspace (\<beta> X) = (\<beta> X) closure_of scEmbeddedCopy X"
              using scCompactification_def[of X] closure_of_subset_topspace[of "\<beta> X" "scEmbeddedCopy X"]  
                    dense_embedding_scEmbed[of X] scEmbeddedCopy_def[of X]
              by (metis assms closure_of_subtopology_open embedding_map_in_subtopology 
                        subtopology_topspace topspace_subtopology)
            moreover have "v \<in> V \<and> v \<in> topspace (\<beta> X)" 
              using vprops V_def Uprops unfolding inverse'_def by auto
            ultimately obtain x where xprops: "x \<in> scEmbeddedCopy X \<and> x \<in> V"
              using in_closure_of[of v "\<beta> X" "scEmbeddedCopy X"]
              by presburger
            define w where "w = e f x"
            hence "w \<in> {m..M}" using extend_on_embedded xprops by blast
            moreover have "w \<in> U" using w_def xprops vprops V_def
              by (simp add: inverse'_alt)
            ultimately have "\<exists> w. w \<in> U \<inter> {m..M}" by auto
          }
          hence "\<forall> U . openin (scT X f) U \<and> p \<in> U \<longrightarrow> (\<exists> w. w \<in> U \<inter> {m..M})" by auto
          moreover have "p \<in> topspace (scT X f)" 
            by (metis e_def Int_iff vprops c_embedded_f continuous_map_preimage_topspace vimageE)
          ultimately have "p \<in> (scT X f) closure_of {m..M}"
            using in_closure_of[of p "scT X f" "{m..M}"]
            by auto
          hence "p \<in> euclideanreal closure_of {m..M}"
            using scT_def[of X] range'_def[of X f] 
            by (metis (no_types, lifting) closure_of_subtopology_subset fprops restrict_apply' subsetD)
          hence "p \<in> {m..M}" by auto
        }
        thus ?thesis by auto
      qed
      thus ?thesis by (metis e_def atLeastAtMost_iff image_subset_iff)
    qed
    ultimately have "scExtend X f \<in> C* (\<beta> X)" 
      using scT_def[of X] continuous_map_into_fulltopology fprops by auto
  }
  hence "\<forall> f \<in> C* X . scExtend X f \<in> C* (\<beta> X)" by auto
  thus ?thesis using assms scExtend_extends by blast
qed

lemma cstar_embedding_scEmbed:
  assumes "tych_space X"
  shows   "cstar_embedding X (\<beta> X) (scEmbed X)"
  using assms scExtend_extends_cstar[of X] dense_embedding_scEmbed[of X] 
  by meson


text \<open> 
  A compact Hausdorff space is its own Stone-Cech compactification 
\<close>

lemma scCompactification_of_compact_Hausdorff:
assumes "compact_Hausdorff X"
shows   "homeomorphic_map X (\<beta> X) (scEmbed X)"
proof -
  have dense: "dense_embedding X (\<beta> X) (scEmbed X)"
    by (simp add: assms compact_Hausdorff_imp_tych dense_embedding_scEmbed)
  moreover have closed: "closed_map X (\<beta> X) (scEmbed X)"
    by (meson T1_Spaces.continuous_imp_closed_map assms compact_Hausdorff_imp_tych 
              continuous_map_in_subtopology embedding_map_def dense
              homeomorphic_eq_everything_map scCompactification_compact_Hausdorff)
  moreover have "open_map X (\<beta> X) (scEmbed X)"
    by (metis closed closure_of_subset_eq dense_in_def embedding_imp_closed_map_eq 
              embedding_map_def homeomorphic_imp_open_map local.dense subtopology_superset)
  thus ?thesis
    by (metis closed closure_of_subset_eq dense_in_def embedding_imp_closed_map_eq 
              embedding_map_def local.dense subtopology_superset)
qed


subsection \<open> 
  The Stone-{\v C}ech Extension Property: 
  Any continuous map from $X$ to a compact Hausdorff space $K$ extends uniquely to a continuous map 
  from $\beta{X}$ to $K$. 
\<close>

(* a simple, but key, lemma *)
proposition gof_cstar:
  assumes "compact_Hausdorff K"
and       "continuous_map X K f"
shows     "\<forall> g \<in> C* K .  (g o f) \<in> C* X"
proof -
  have tych_K: "tych_space K" 
    using  assms(1) compact_Hausdorff_imp_tych by auto

  { fix g assume gprops: "g \<in> C* K"
    have "continuous_map K (scT K g) g"
      using scT_def[of K] range'_def[of K g] cstar_types_restricted[of K] assms(2)
            gprops weak_generators_continuous[of K "topspace K" "cstar_id K" "(scT K)" "(C* K)" g]
      by (metis (mono_tags, lifting) closure_of_topspace continuous_map_image_closure_subset 
                 continuous_map_in_subtopology mem_Collect_eq restrict_apply')     
    hence cts_scT: "continuous_map X (scT K g) (g o f)" 
      using assms by (simp add: continuous_map_compose)
    hence gofprops: "(g o f) \<in> (C X)"
      using scT_def[of K] range'_def[of K] 
      by (metis (mono_tags, lifting) continuous_map_in_subtopology gprops mem_Collect_eq restrict_apply')
    moreover have "fbounded (g o f) X"
    proof -
      have "compact (g ` topspace K)" using assms(1) gprops 
        using compact_space_def compactin_euclidean_iff image_compactin by blast
      hence "bounded (g ` topspace K)" 
        by (simp add: compact_imp_bounded)
      moreover have "(g o f) ` topspace X \<subseteq> g ` topspace K" 
        by (metis assms(2) continuous_map_image_subset_topspace image_comp image_mono)
      ultimately have "bounded ((g o f) ` topspace X)"
        by (metis bounded_subset)
      thus ?thesis using bounded_range_iff_fbounded[of "g o f" X] gofprops by auto
    qed
    ultimately have "(g o f) \<in> C* X" by auto
  }
  thus ?thesis by auto
qed

proposition scEmbed_range:
  assumes "tych_space X"
and       "x \<in> topspace X"
shows     "scEmbed X x \<in> topspace (\<beta> X)"
  using assms(1) assms(2) dense_embedding_scEmbed embedding_map_in_subtopology by fastforce

proposition scEmbed_range':
  assumes "tych_space X"
and       "x \<in> topspace X"
shows     "scEmbed X x \<in> topspace (scProduct X)"
  using assms(1) assms(2) scEmbed_range[of X] 
  by (simp add: scCompactification_def)

proposition scProjection:
  shows "\<forall> f \<in> C* X. \<forall> p \<in> topspace (scProduct X) . scProject X f p = p f"
  using scProject_def[of X] scProduct_def[of X] product_projection[of "C* X" "scT X"]
  by simp

proposition scProjections_continuous:
  shows "\<forall> f \<in> C* X . continuous_map (scProduct X) (scT X f) (scProject X f)"
proof -
  have "\<forall> f \<in> C* X . continuous_map (scProduct X) (scT X f) (scProject X f)"
    using scProduct_def[of X] scProject_def[of X] 
    by (metis (mono_tags, lifting) projections_continuous restrict_apply')
  thus ?thesis using scCompactification_def[of X] by simp
qed

proposition continuous_embedding_inverse:
  assumes "embedding_map X Y e"
  shows "\<exists> e' . continuous_map (subtopology Y (e ` topspace X)) X e' \<and> (\<forall> x \<in> topspace X . e' (e x) = x)"
  by (meson assms embedding_map_def homeomorphic_map_maps homeomorphic_maps_def)


(* The Stone-Cech Extension Property - Proof adapted from Willard 19.5 *)
(* Every continuous map from X to K extends uniquely to \<beta> X *)

lemma scExtension_exists:
  assumes "tych_space X"
and       "compact_Hausdorff K"
shows     "\<forall> f \<in> cts[X,K] . \<exists> F \<in> cts[\<beta> X, K] . (\<forall> x \<in> topspace X . F (scEmbed X x) = f x)"
proof-
  { fix f assume fprops: "f \<in> cts[X,K]"

    (* start with some basic facts that are already known to be useful in other proofs  *)
    have tych_K: "tych_space K" using assms(2) compact_Hausdorff_imp_tych[of K] by simp
  
    define Xspace where "Xspace = topspace (scProduct X)"
    define Kspace where "Kspace = topspace (scProduct K)" 
    (* Now define a map H : scProduct X \<Rightarrow> scProduct K *)
    define H where "H = (\<lambda> p \<in> Xspace . \<lambda> g \<in> C* K . scProject X (g o f) p)"

    have H_of_scEmbed: "\<forall> x \<in> topspace X . H (scEmbed X x) = scEmbed K (f x)"
    proof -
      { fix x assume xprops: "x \<in> topspace X"
        hence "H (scEmbed X x) =  (\<lambda> p \<in> Xspace . \<lambda> g \<in> C* K . scProject X (g o f) p) (scEmbed X x)" 
          using H_def by auto
        moreover have "(scEmbed X x) \<in> Xspace" 
          using Xspace_def assms(1) scEmbed_range'[of X x] xprops by auto
        ultimately have "H (scEmbed X x)  = (\<lambda> g \<in> C* K . scProject X (g o f) (scEmbed X x)) "
          by auto
        also have "\<dots> = (\<lambda> g \<in> C* K . (g o f) x)" 
          using assms(2) gof_cstar[of K X f] xprops fprops assms(1)
                scEmbed_then_project[where x="x" and X="X"]
          by (metis (no_types, lifting) mem_Collect_eq restrict_ext)
        also have "\<dots>  = (\<lambda> g \<in> C* K . g (f x))" by auto
        finally have "H (scEmbed X x) = scEmbed K (f x)" 
          using scEmbed_def[of K] cstar_id_def[of K] evaluation_map_def[of K "cstar_id K" "C* K"]
          by (smt (verit) continuous_map_image_subset_topspace fprops xprops image_subset_iff 
                  mem_Collect_eq restrict_apply' restrict_ext xprops)
      }
      thus ?thesis by auto
    qed
    hence H_on_embedded: "H ` scEmbeddedCopy X \<subseteq> scEmbeddedCopy K"
    proof -
      { fix p assume "p \<in> H ` scEmbeddedCopy X"
        then obtain q where qprops: "q \<in> scEmbeddedCopy X \<and> p = H q" by auto
        then obtain x where xprops: "x \<in> topspace  X \<and> q = scEmbed X x" 
          using scEmbeddedCopy_def[of X] by auto
        hence "p = scEmbed K (f x)" using qprops H_of_scEmbed by auto
        hence "p \<in> scEmbeddedCopy K" 
          using scEmbeddedCopy_def[of K] xprops qprops fprops 
          by (metis continuous_map_image_subset_topspace image_eqI in_mono mem_Collect_eq)
      }
      thus ?thesis by auto
    qed
      (* We'll be using:
      continuous_map_coordinatewise_then_product[of "C* K" "scProduct X" "scT K" "H"]:
          \<forall> g \<in> C* K .  continuous_map (scProduct X) (scT K g) (\<lambda>x. H x g)) \<Longrightarrow>
                        continuous_map (scProduct X) (product_topology (scT K) (C* K)) H
       *)
    (* Show that each projection of H is continuous *)
    have components_cts: "\<forall> g \<in> C* K .  continuous_map (scProduct X) (scT K g) (\<lambda>x \<in> Xspace . H x g)"
    proof -
      { fix g assume gprops: "g \<in> C* K"
        (* range described using X *)
        have "continuous_map (scProduct X) (scT X (g o f)) ( \<lambda> x \<in> Xspace . H x g)" 
        proof -
          have "\<forall>f\<in> C* X . continuous_map (scProduct X) (scT X f) (scProject X f)"
            using scProjections_continuous[of X] by simp
          hence "continuous_map (scProduct X) (scT X (g o f)) (scProject X (g o f))"
            using assms(2) fprops gprops gof_cstar[of K X f] by auto
          moreover have "\<forall>x \<in> Xspace. H x g = (scProject X (g o f)) x"
            using gprops  H_def Xspace_def
            by auto
          ultimately show ?thesis
            using Xspace_def continuous_map_eq by fastforce
        qed
        (* need to convert to range using K *)
        moreover have "scT X (g o f) = subtopology (scT K g) (range' X (g o f))"
        proof -
          have "(g o f) ` topspace X \<subseteq> g ` topspace K" 
              using gprops fprops unfolding continuous_map_def by auto
          hence "range' X (g o f) \<subseteq> range' K g" 
            unfolding range'_def by (meson closure_of_mono)
          hence "top_of_set (range' X (g o f)) 
                          = subtopology (top_of_set (range' K g)) (range' X (g o f))"
            by (simp add: inf.absorb_iff2 subtopology_subtopology)
          hence "scT X (g o f) = subtopology (scT K g) (range' X (g o f))"
            using scT_def[of X] scT_def[of K] gprops assms(2) gof_cstar[of K X f] fprops by auto
          thus ?thesis by auto
        qed
        ultimately have "continuous_map (scProduct X) (scT K g) ( \<lambda> x \<in> Xspace . H x g)"
          using continuous_map_in_subtopology by auto
      }
      thus ?thesis by auto
    qed
    (* and hence H is continuous *)
    hence Hcts: "continuous_map (scProduct X) (scProduct K) H"
      using continuous_map_coordinatewise_then_product[of "C* K" "scProduct X" "scT K" "H"]
            scProduct_def[of X] scProduct_def[of K] H_def Xspace_def
      by (smt (verit, del_insts) continuous_map_eq restrict_apply)
    (* the image of \<beta>X under H is inside scEmbeddedCopy K  *)
    have H_on_beta: "H ` topspace (\<beta> X) \<subseteq> scEmbeddedCopy K"
    proof -
      have "H ` scEmbeddedCopy X \<subseteq> scEmbeddedCopy K" using H_on_embedded by auto
      hence "H ` topspace (\<beta> X) \<subseteq> scProduct K closure_of scEmbeddedCopy K"
        using scCompactification_def[of X] Hcts closure_of_mono 
             continuous_map_eq_image_closure_subset by fastforce
      thus ?thesis using scEmbeddedCopy_def
        by (metis assms(2) closure_of_subset_topspace homeomorphic_imp_surjective_map 
                  scCompactification_def scCompactification_of_compact_Hausdorff topspace_subtopology_subset)
    qed
    (* now obtain an inverse for scEmbed K *)
    have embeds: "dense_embedding K (\<beta> K) (scEmbed K)" using dense_embedding_scEmbed[of K] tych_K by auto
    have closed: "closedin (scProduct K) (scEmbeddedCopy K)"
      using assms(2) scEmbeddedCopy_def[of X] scCompactification_def[of K]      
            scCompactification_compact_Hausdorff[of K] 
      by (metis closure_of_eq closure_of_subset_topspace closure_of_topspace dense_in_def embeds 
                homeomorphic_map_closure_of scCompactification_of_compact_Hausdorff scEmbeddedCopy_def 
                topspace_subtopology_subset)
    hence onto: "scEmbeddedCopy K = topspace (\<beta> K)" 
      using scCompactification_def[of K]
      by (metis closure_of_closedin closure_of_subset_topspace topspace_subtopology_subset)
    then obtain e' 
      where e'props: "continuous_map (\<beta> K) K e' 
                  \<and> (\<forall> x \<in> topspace K . e' (scEmbed K x) = x)"
         by (metis continuous_embedding_inverse embeds scEmbeddedCopy_def subtopology_topspace)
    (* ... and use it to define F. Then verify its properties *)
    define F where "F = e' o (\<lambda> p \<in> topspace (\<beta> X) . restrict H (topspace \<beta> X) p)"
    (* F is continuous *)
    have Fcts: "F \<in> cts[ \<beta> X, K ]"
    proof -
      have "(\<lambda> p \<in> topspace (\<beta> X) . restrict H (topspace \<beta> X) p) \<in> cts[\<beta> X, scProduct K]" 
        using Hcts Xspace_def continuous_map_from_subtopology scCompactification_def
        by (metis closedin_subset closedin_topspace mem_Collect_eq restrict_continuous_map)
      moreover have "H ` (topspace \<beta> X) \<subseteq> topspace (\<beta> K)"
        using Xspace_def H_on_beta Xspace_def scCompactification_def[of K] onto by blast
      ultimately have "(\<lambda> p \<in> topspace (\<beta> X) . restrict H (topspace \<beta> X) p) \<in> cts[\<beta> X, \<beta> K]"
        using scCompactification_def[of K]
        by (metis closed closure_of_closedin continuous_map_in_subtopology image_restrict_eq mem_Collect_eq onto)
      moreover have "e' \<in> cts[ \<beta> K, K ]" using e'props by simp
      ultimately show ?thesis
        using F_def continuous_map_compose[of "\<beta> X" "\<beta> K" "(\<lambda> p \<in> topspace (\<beta> X) . restrict H (topspace \<beta> X) p)"]
        by auto
    qed
    (* F extends f *)
    moreover have Fextends: "\<forall> x \<in> topspace X . (F o scEmbed X) x = f x"
    proof -
      { fix x assume xprops: "x \<in> topspace X"
        have "(F o scEmbed X) x = F (scEmbed X x)" by auto
        moreover have "scEmbed X x \<in> topspace (\<beta> X)" 
          using assms(1) scEmbed_range[of X x] xprops by auto
        ultimately have "(F o scEmbed X) x 
              = (e' o (\<lambda> p \<in> topspace (\<beta> X) . restrict H (topspace \<beta> X) p)) (scEmbed X x)" 
          using F_def by simp
        also have "\<dots> = (e' o (\<lambda> p \<in> topspace (\<beta> X) . H p)) (scEmbed X x)" by auto
        finally have step1: "(F o scEmbed X) x = e' ((\<lambda> p \<in> topspace (\<beta> X) . H p) (scEmbed X x))" by auto
        have "(\<lambda> p \<in> topspace (\<beta> X) . H p) (scEmbed X x) = H (scEmbed X x)"
          using scEmbed_range[of X x] assms(1) xprops by auto
        also have "\<dots> = scEmbed K (f x)" using H_of_scEmbed  xprops by auto
        finally have step2: "(\<lambda> p \<in> topspace (\<beta> X) . H p) (scEmbed X x) = scEmbed K (f x)"
          by auto        
        have "(F o scEmbed X) x = e' ((\<lambda> p \<in> topspace (\<beta> X) . H p) (scEmbed X x))"
          using step1 by simp
        also have "\<dots> = e' (scEmbed K (f x))" using step2 by auto
        finally have "(F o scEmbed X) x = f x" 
          using e'props tych_K scEmbed_range[of K "f x"] xprops fprops
          by (metis continuous_map_image_subset_topspace image_subset_iff mem_Collect_eq)
      }
      thus ?thesis by auto
    qed
    (* So F is the extension we want *)
    ultimately have "F \<in> cts[\<beta> X, K] \<and> (\<forall> x \<in> topspace X . F (scEmbed X x) = f x)"
      by auto
    hence "\<exists> F \<in> cts[\<beta> X, K] . (\<forall> x \<in> topspace X . F (scEmbed X x) = f x)" by auto
  }
  thus ?thesis by auto
qed

lemma scExtension_unique:
  assumes "F \<in> cts[\<beta> X, K] \<and> (\<forall> x \<in> topspace X . F (scEmbed X x) = f x)"
and       "compact_Hausdorff K"
shows     "(\<forall> G . G \<in> cts[\<beta> X, K] \<and> (\<forall> x \<in> topspace X . G (scEmbed X x) = f x) 
                      \<longrightarrow> (\<forall> p \<in> topspace (\<beta> X) . F p = G p))"
proof -
  { fix G assume Gprops: "G \<in> cts[\<beta> X, K] \<and> (\<forall> x \<in> topspace X . G (scEmbed X x) = f x)"
    have "\<forall> p \<in> scEmbeddedCopy X . F p = G p"         
    proof -
      { fix p assume pprops: "p \<in> scEmbeddedCopy X"
        then obtain x where xprops: "x \<in> topspace X \<and> p = scEmbed X x"
          using scEmbeddedCopy_def[of X] by auto
        hence "F p = G p" using assms Gprops by auto
      }
      thus ?thesis by auto
    qed
    moreover have "dense_in (\<beta> X) (scEmbeddedCopy X) (topspace (\<beta> X))"
        by (metis closure_of_subset_topspace dense_in_closure dense_in_def scCompactification_def 
                  topspace_subtopology_subset)
    moreover have "(cts_on \<beta> X to_shared Hausdorff_space) {F,G}"
    proof -
      have "Hausdorff_space K" using assms(2) by auto
      moreover have "\<forall> g \<in> {F,G} . g \<in> cts[\<beta> X, K]"
        using assms Gprops by auto
      ultimately have "\<exists> K . Hausdorff_space K \<and> {F,G} \<subseteq> cts[\<beta> X,K]" by auto
      thus ?thesis by auto
    qed
    ultimately have "(\<forall> p \<in> topspace (\<beta> X) . F p = G p)"
      using continuous_maps_on_dense_subset[of F G "\<beta> X" "scEmbeddedCopy X"]
      by auto
  }
  thus ?thesis by auto
qed

lemma scExtension_property:
  assumes "tych_space X"
and       "compact_Hausdorff K"
shows     "\<forall> f \<in> cts[X,K] . \<exists>! F \<in> cts\<^sub>E[\<beta> X, K] . (\<forall> x \<in> topspace X . F (scEmbed X x) = f x)"
proof -
  { fix f assume fprops: "f \<in> cts[X,K]"
    define P where "P = (\<lambda>g . g \<in> cts\<^sub>E[\<beta> X, K] \<and> (\<forall> x \<in> topspace X . g (scEmbed X x) = f x))"
    then obtain F where Fprops: "F \<in> cts[\<beta> X, K] \<and> (\<forall> x \<in> topspace X . F (scEmbed X x) = f x)"
      using scExtension_exists[of X K] assms fprops by auto 
    define F' where "F' = restrict F (topspace \<beta> X)"
    (* show that F' satisfies P *)
    have "F \<in> (topspace \<beta> X) \<rightarrow> topspace K" using Fprops continuous_map_def[of "\<beta> X" K F] by auto
    hence F'ext: "F' \<in> (topspace \<beta> X) \<rightarrow>\<^sub>E topspace K" 
      using F'_def restrict_def[of F "topspace \<beta> X"] extensional_def[of "topspace \<beta> X"]
      by auto
    moreover have F'cts: "F' \<in> cts[ \<beta> X, K ]" 
    proof -
      have "F' \<in> (topspace \<beta> X) \<rightarrow> topspace K" using F'ext by auto
      moreover have "\<forall> U . {x \<in> topspace \<beta> X. F x \<in> U} = {x \<in> topspace \<beta> X. F' x \<in> U}"
        using F'_def by auto
      ultimately show ?thesis using Fprops unfolding continuous_map_def by auto
    qed
    ultimately have "F' \<in> cts\<^sub>E[ \<beta> X, K ]" by auto
    moreover have F'embed: "(\<forall> x \<in> topspace X . F' (scEmbed X x) = f x)"
    proof -
      have "\<forall> x \<in> topspace X . scEmbed X x \<in> topspace \<beta> X"
        using assms(1) scEmbed_range[of X] by blast
      thus ?thesis using F'_def Fprops by fastforce
    qed
    ultimately have "P F'" using P_def by auto
    (* now show that nothing else satisfies P *)
    moreover have "\<forall> G . P G \<longrightarrow> G = F'"
    proof - 
      { fix G assume Gprops: "P G"
        { fix p
          have "F' p = G p"
          proof (cases "p \<in> topspace \<beta> X")
            case True
            hence "F' \<in> cts[ \<beta> X, K] \<and> (\<forall>x\<in>topspace X. F' (scEmbed X x) = f x)"
              using F'cts F'embed by auto
            moreover have "G \<in> cts[ \<beta> X, K] \<and> (\<forall>x\<in>topspace X. G (scEmbed X x) = f x)"
              using Gprops P_def by auto
            ultimately show ?thesis
              using assms(2) scExtension_unique[of F' X K f] "True" by blast
          next
            case False
            hence "F' p = undefined" using F'_def by auto
            moreover have "G p = undefined" 
              using Gprops P_def extensional_def[of "topspace \<beta> X"] "False" by auto
            ultimately show ?thesis by auto
          qed
        }
        hence "\<forall> p . F' p = G p" by auto
      }
      thus ?thesis by auto
    qed
    ultimately have "\<exists>! F' . P F'" by blast
    hence "\<exists>! F \<in> cts\<^sub>E[\<beta> X, K] . (\<forall> x \<in> topspace X . F (scEmbed X x) = f x)"
      using P_def by auto
  }
  thus ?thesis by auto
qed
(* Concludes the proof of the Stone-Cech Extension Property *)       

end
