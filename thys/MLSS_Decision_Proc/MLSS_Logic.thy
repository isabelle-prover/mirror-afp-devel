theory MLSS_Logic
  imports Main
begin

section \<open>Propositional formulae\<close>
text \<open>
  This theory contains syntax and semantics of propositional formulae.
\<close>

datatype (atoms: 'a) fm =
  is_Atom: Atom 'a | And "'a fm" "'a fm" | Or "'a fm" "'a fm" |
  Neg "'a fm"

fun "interp" :: "('model \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'model \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "interp I\<^sub>a M (Atom a) = I\<^sub>a M a" |
  "interp I\<^sub>a M (And \<phi>\<^sub>1 \<phi>\<^sub>2) = (interp I\<^sub>a M \<phi>\<^sub>1 \<and> interp I\<^sub>a M \<phi>\<^sub>2)" |
  "interp I\<^sub>a M (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = (interp I\<^sub>a M \<phi>\<^sub>1 \<or> interp I\<^sub>a M \<phi>\<^sub>2)" |
  "interp I\<^sub>a M (Neg \<phi>) = (\<not> interp I\<^sub>a M \<phi>)"

locale ATOM =
  fixes I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool"
begin

abbreviation I where "I \<equiv> interp I\<^sub>a"

end

definition "Atoms A \<equiv> {a |a. Atom a \<in> A}"

lemma Atoms_Un[simp]: "Atoms (A \<union> B) = Atoms A \<union> Atoms B"
  unfolding Atoms_def by auto

lemma Atoms_mono: "A \<subseteq> B \<Longrightarrow> Atoms A \<subseteq> Atoms B"
  unfolding Atoms_def by auto

end