theory Multitape_Enum_Type
  imports "HOL-Library.Cardinality"
begin

section \<open>An enumerable type of any size\<close>

text \<open>A statement proved for every \<^class>\<open>enum\<close> type with at least \<open>K\<close>
  elements, and mentioning that type nowhere else, holds outright: the type
  can be taken to be a local copy of \<open>{0..<K}\<close>.  The linear speedup theorem
  is parametric in the type of its compression alphabet, with a lower bound on
  its size that depends on the machine being sped up, and HOL has no way to
  pick a type by value inside a proof.

  The pattern is \<open>unoverload_type\<close> from \<open>HOL-Types_To_Sets\<close>, which turns the
  class into an explicit premise on its operations, now variables, followed
  by a local type definition whose operations are read off the bijection with
  \<open>{0..<K}\<close>.  Because the statement does not mention the type, no transfer
  rules are needed.  This theory supplies the one fact about the local type
  that the library lacks, that it is an instance of \<^class>\<open>enum\<close>; its
  size is \<open>type_definition.card\<close>, from \<open>HOL-Library.Cardinality\<close>.  The
  theory that applies the pattern imports \<open>Types_To_Sets\<close> itself, so this
  entry keeps its dependency on \<open>HOL-Library\<close> alone.

  The lemma is proved in plain HOL, for any type that happens to be in
  bijection with \<open>{0..<K}\<close>.  The pattern that applies it goes beyond plain
  HOL: \<open>unoverload_type\<close> uses the Unoverloading rule and
  \<open>cancel_type_definition\<close> the Local Typedef rule, which
  \<open>HOL-Types_To_Sets\<close> adds to the logic as oracles.  A theorem obtained by
  the pattern depends on both, and Isabelle records them in its
  derivation.\<close>

lemma enum_on_typedef:
  assumes t: "type_definition (rep :: 'b \<Rightarrow> nat) ab {0..<K}"
  shows "class.enum (map ab [0..<K]) (\<lambda>P. list_all P (map ab [0..<K]))
           (\<lambda>P. list_ex P (map ab [0..<K]))"
proof -
  have univ: "(UNIV :: 'b set) = set (map ab [0..<K])"
    using type_definition.Abs_image [OF t] by simp
  have dist: "distinct (map ab [0..<K])"
  proof -
    have "inj_on ab {0..<K}"
      by (rule inj_onI) (metis type_definition.Abs_inverse [OF t])
    then show ?thesis by (simp add: distinct_map)
  qed
  show ?thesis
    unfolding class.enum_def
    using univ dist by (auto simp: list_all_iff list_ex_iff)
qed

end
