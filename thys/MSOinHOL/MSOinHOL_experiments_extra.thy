theory MSOinHOL_experiments_extra
  imports
    MSOinHOL_deep
    MSOinHOL_shallow
    MSOinHOL_shallow_minimal
begin

text \<open>Additional MSO landmarks complementing the experiments in
  @{text MSOinHOL_experiments_classic}: 3-colorability, vertex cover,
  transitivity, symmetry and triangle existence, each replicated across
  the deep, maximal-shallow and minimal-shallow embeddings.\<close>

abbreviation "(x::V) \<equiv> 1"
abbreviation "(y::V) \<equiv> 2"
abbreviation "(z::V) \<equiv> 3"
abbreviation "(u::V) \<equiv> 4"
abbreviation "(v::V) \<equiv> 5"
abbreviation "(X::V2) \<equiv> 1"
abbreviation "(Y::V2) \<equiv> 2"
abbreviation "(Z::V2) \<equiv> 3"

consts P :: R

subsubsection \<open>Deep embedding (under @{text "\<Turnstile>\<^sup>d'"})\<close>

text \<open>3-colorability (Thomas 1997): refuted on @{text \<open>K\<^sub>4\<close>}
  (the complete graph on four vertices, which needs four colors).
  Generalisation of @{text two_colorability_not_valid_d}.\<close>

lemma three_colorability_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2X. \<exists>\<^sup>d\<^sub>2Y. \<exists>\<^sup>d\<^sub>2Z. ((\<forall>\<^sup>du. (X\<^sup>d(u) \<or>\<^sup>d Y\<^sup>d(u) \<or>\<^sup>d Z\<^sup>d(u))) \<and>\<^sup>d (\<forall>\<^sup>du. \<forall>\<^sup>dv. (P\<^sup>d(u,v) \<supset>\<^sup>d ((\<not>\<^sup>d (X\<^sup>d(u) \<and>\<^sup>d X\<^sup>d(v))) \<and>\<^sup>d (\<not>\<^sup>d (Y\<^sup>d(u) \<and>\<^sup>d Y\<^sup>d(v))) \<and>\<^sup>d (\<not>\<^sup>d (Z\<^sup>d(u) \<and>\<^sup>d Z\<^sup>d(v))))))))"
  unfolding DefD apply simp nitpick oops

text \<open>Vertex cover existence: the predicate @{text Univ} is a witness, so
  the schema is universally valid.\<close>

lemma vertex_cover_valid_d:
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2X. \<forall>\<^sup>du. \<forall>\<^sup>dv. (P\<^sup>d(u,v) \<supset>\<^sup>d (X\<^sup>d(u) \<or>\<^sup>d X\<^sup>d(v))))"
  unfolding DefD
  apply (intro allI, simp add: SetMod_def EnvMod_def)
  by (rule exI[of _ "Univ"]) (auto simp: SetMod_def EnvMod_def)

text \<open>Transitivity of @{text P}: not universally valid; refuted by any
  3-path @{text \<open>a \<rightarrow> b \<rightarrow> c\<close>} without the closing edge @{text \<open>a \<rightarrow> c\<close>}.\<close>

lemma transitivity_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>dx. \<forall>\<^sup>dy. \<forall>\<^sup>dz. (P\<^sup>d(x,y) \<supset>\<^sup>d (P\<^sup>d(y,z) \<supset>\<^sup>d P\<^sup>d(x,z))))"
  unfolding DefD apply simp nitpick oops

text \<open>Symmetric extension: stating @{text P} is symmetric is also not
  universally valid; refuted by any directed edge without its converse.\<close>

lemma symmetry_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>dx. \<forall>\<^sup>dy. (P\<^sup>d(x,y) \<supset>\<^sup>d P\<^sup>d(y,x)))"
  unfolding DefD apply simp nitpick oops

text \<open>Existence of a triangle: not universally valid; refuted on any
  triangle-free graph (e.g. the empty graph).\<close>

lemma triangle_exists_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>dx. \<exists>\<^sup>dy. \<exists>\<^sup>dz. (P\<^sup>d(x,y) \<and>\<^sup>d P\<^sup>d(y,z) \<and>\<^sup>d P\<^sup>d(x,z)))"
  unfolding DefD apply simp nitpick oops

text \<open>Existence of an edge: refuted on the empty graph.\<close>

lemma has_edge_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>dx. \<exists>\<^sup>dy. P\<^sup>d(x,y))"
  unfolding DefD apply simp nitpick oops

text \<open>Loop-freeness: stating @{text P} has no self-loops is refuted by any
  graph with a fixed point.\<close>

lemma loop_free_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>dx. \<not>\<^sup>d P\<^sup>d(x,x))"
  unfolding DefD apply simp nitpick oops

subsubsection \<open>Maximal-shallow embedding (under @{text "\<Turnstile>\<^sup>s'"})\<close>

lemma three_colorability_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<exists>\<^sup>s\<^sub>2X. \<exists>\<^sup>s\<^sub>2Y. \<exists>\<^sup>s\<^sub>2Z. ((\<forall>\<^sup>su. (X\<^sup>s(u) \<or>\<^sup>s Y\<^sup>s(u) \<or>\<^sup>s Z\<^sup>s(u))) \<and>\<^sup>s (\<forall>\<^sup>su. \<forall>\<^sup>sv. (P\<^sup>s(u,v) \<supset>\<^sup>s ((\<not>\<^sup>s (X\<^sup>s(u) \<and>\<^sup>s X\<^sup>s(v))) \<and>\<^sup>s (\<not>\<^sup>s (Y\<^sup>s(u) \<and>\<^sup>s Y\<^sup>s(v))) \<and>\<^sup>s (\<not>\<^sup>s (Z\<^sup>s(u) \<and>\<^sup>s Z\<^sup>s(v))))))))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

lemma vertex_cover_valid_s:
  "\<Turnstile>\<^sup>s' (\<exists>\<^sup>s\<^sub>2X. \<forall>\<^sup>su. \<forall>\<^sup>sv. (P\<^sup>s(u,v) \<supset>\<^sup>s (X\<^sup>s(u) \<or>\<^sup>s X\<^sup>s(v))))"
  unfolding DefS
  apply (intro allI, simp)
  by (rule exI[of _ "Univ"]) auto

lemma transitivity_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>sx. \<forall>\<^sup>sy. \<forall>\<^sup>sz. (P\<^sup>s(x,y) \<supset>\<^sup>s (P\<^sup>s(y,z) \<supset>\<^sup>s P\<^sup>s(x,z))))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

lemma symmetry_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>sx. \<forall>\<^sup>sy. (P\<^sup>s(x,y) \<supset>\<^sup>s P\<^sup>s(y,x)))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

lemma triangle_exists_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<exists>\<^sup>sx. \<exists>\<^sup>sy. \<exists>\<^sup>sz. (P\<^sup>s(x,y) \<and>\<^sup>s P\<^sup>s(y,z) \<and>\<^sup>s P\<^sup>s(x,z)))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

lemma has_edge_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<exists>\<^sup>sx. \<exists>\<^sup>sy. P\<^sup>s(x,y))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

lemma loop_free_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>sx. \<not>\<^sup>s P\<^sup>s(x,x))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

subsubsection \<open>Minimal-shallow embedding (under @{text "\<Turnstile>\<^sup>m"})\<close>

text \<open>In the minimal embedding the second-order existential ranges over
  the (countable) assignment range, so even formulae that hold under the
  full second-order domain (such as vertex cover) need not hold here.
  @{text nitpick} can certify a POTENTIAL countermodel only.\<close>

lemma three_colorability_not_valid_m:
  "\<Turnstile>\<^sup>m (\<exists>\<^sup>m\<^sub>2X. \<exists>\<^sup>m\<^sub>2Y. \<exists>\<^sup>m\<^sub>2Z. ((\<forall>\<^sup>mu. (X\<^sup>m(u) \<or>\<^sup>m Y\<^sup>m(u) \<or>\<^sup>m Z\<^sup>m(u))) \<and>\<^sup>m (\<forall>\<^sup>mu. \<forall>\<^sup>mv. (P\<^sup>m(u,v) \<supset>\<^sup>m ((\<not>\<^sup>m (X\<^sup>m(u) \<and>\<^sup>m X\<^sup>m(v))) \<and>\<^sup>m (\<not>\<^sup>m (Y\<^sup>m(u) \<and>\<^sup>m Y\<^sup>m(v))) \<and>\<^sup>m (\<not>\<^sup>m (Z\<^sup>m(u) \<and>\<^sup>m Z\<^sup>m(v))))))))"
  unfolding DefM nitpick[expect=potential] oops

lemma vertex_cover_not_valid_m:
  "\<Turnstile>\<^sup>m (\<exists>\<^sup>m\<^sub>2X. \<forall>\<^sup>mu. \<forall>\<^sup>mv. (P\<^sup>m(u,v) \<supset>\<^sup>m (X\<^sup>m(u) \<or>\<^sup>m X\<^sup>m(v))))"
  unfolding DefM oops

text \<open>Explicit refutability of the vertex-cover schema in the minimal
  embedding: with @{text II} interpreting @{text P} as the complete
  relation and @{text GG} mapping every symbol to the empty set, no
  symbol-indexed @{text X} can cover any edge.\<close>

lemma vertex_cover_refutable_m:
  "\<exists>(II'::\<I>) (gg'::\<E>) (GG'::\<G>).
     \<not> (\<exists>X. \<forall>u. \<forall>v. II' P (gg' u) (gg' v) \<longrightarrow> (GG' X) (gg' u) \<or> (GG' X) (gg' v))"
  by (rule exI[of _ "\<lambda>r a b. True"],
      rule exI[of _ "\<lambda>_. undefined"],
      rule exI[of _ "\<lambda>Z d. False"]) simp

lemma transitivity_not_valid_m:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>mx. \<forall>\<^sup>my. \<forall>\<^sup>mz. (P\<^sup>m(x,y) \<supset>\<^sup>m (P\<^sup>m(y,z) \<supset>\<^sup>m P\<^sup>m(x,z))))"
  unfolding DefM nitpick oops

lemma symmetry_not_valid_m:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>mx. \<forall>\<^sup>my. (P\<^sup>m(x,y) \<supset>\<^sup>m P\<^sup>m(y,x)))"
  unfolding DefM nitpick oops

lemma triangle_exists_not_valid_m:
  "\<Turnstile>\<^sup>m (\<exists>\<^sup>mx. \<exists>\<^sup>my. \<exists>\<^sup>mz. (P\<^sup>m(x,y) \<and>\<^sup>m P\<^sup>m(y,z) \<and>\<^sup>m P\<^sup>m(x,z)))"
  unfolding DefM oops

text \<open>Explicit refutability: with @{text II} interpreting @{text P} as
  the empty relation no triangle can exist.\<close>

lemma triangle_exists_refutable_m:
  "\<exists>(II'::\<I>) (gg'::\<E>).
     \<not> (\<exists>x. \<exists>y. \<exists>z. II' P (gg' x) (gg' y) \<and> II' P (gg' y) (gg' z) \<and> II' P (gg' x) (gg' z))"
  by (rule exI[of _ "\<lambda>r a b. False"], rule exI[of _ "\<lambda>_. undefined"]) simp

lemma has_edge_not_valid_m:
  "\<Turnstile>\<^sup>m (\<exists>\<^sup>mx. \<exists>\<^sup>my. P\<^sup>m(x,y))"
  unfolding DefM nitpick oops

lemma loop_free_not_valid_m:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>mx. \<not>\<^sup>m P\<^sup>m(x,x))"
  unfolding DefM nitpick oops

end
