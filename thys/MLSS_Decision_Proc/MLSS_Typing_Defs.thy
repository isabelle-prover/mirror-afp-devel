theory MLSS_Typing_Defs
  imports MLSS_Semantics "HOL-Library.Adhoc_Overloading"
begin

section \<open>Typing Rules\<close>
text \<open>
  We define the typing rules for set terms and atoms, as well as
  for formulae
\<close>

inductive types_pset_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a pset_term \<Rightarrow> nat \<Rightarrow> bool" ("_ \<turnstile> _ : _" [46, 46, 46] 46) where
  "v \<turnstile> \<emptyset> n : Suc n"
| "v \<turnstile> Var x : v x"
| "v \<turnstile> t : l \<Longrightarrow> v \<turnstile> Single t : Suc l"
| "v \<turnstile> s : l \<Longrightarrow> v \<turnstile> t : l \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> v \<turnstile> s \<squnion>\<^sub>s t : l"
| "v \<turnstile> s : l \<Longrightarrow> v \<turnstile> t : l \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> v \<turnstile> s \<sqinter>\<^sub>s t : l"
| "v \<turnstile> s : l \<Longrightarrow> v \<turnstile> t : l \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> v \<turnstile> s -\<^sub>s t : l"

text \<open>Activate this bundle to avoid ambiguity between
      \<^const>\<open>Set.member\<close> and \<^const>\<open>types_pset_term\<close>.\<close>
bundle Set_member_no_ascii_notation
begin
no_notation Set.member ("(_/ : _)" [51, 51] 50)
end

inductive_cases types_pset_term_cases:
  "v \<turnstile> \<emptyset> n : l" "v \<turnstile> Var x : l" "v \<turnstile> Single t : l"
  "v \<turnstile> s \<squnion>\<^sub>s t : l" "v \<turnstile> s \<sqinter>\<^sub>s t : l" "v \<turnstile> s -\<^sub>s t : l"

lemma types_pset_term_intros':
  "l = Suc n \<Longrightarrow> v \<turnstile> \<emptyset> n : l"
  "l = v x \<Longrightarrow> v \<turnstile> Var x : l"
  "l \<noteq> 0 \<Longrightarrow> v \<turnstile> t : nat.pred l \<Longrightarrow> v \<turnstile> Single t : l"
  by (auto simp add: types_pset_term.intros(1,2,3) pred_def split: nat.splits)

definition type_of_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a pset_term \<Rightarrow> nat" where
  "type_of_term v t \<equiv> THE l. v \<turnstile> t : l"

inductive types_pset_atom :: "('a \<Rightarrow> nat) \<Rightarrow> 'a pset_atom \<Rightarrow> bool" where
  "\<lbrakk> v \<turnstile> s : l; v \<turnstile> t : l \<rbrakk> \<Longrightarrow> types_pset_atom v (s =\<^sub>s t)"
| "\<lbrakk> v \<turnstile> s : l; v \<turnstile> t : Suc l\<rbrakk> \<Longrightarrow> types_pset_atom v (s \<in>\<^sub>s t)"

definition types_pset_fm :: "('a \<Rightarrow> nat) \<Rightarrow> 'a pset_fm \<Rightarrow> bool" where
  "types_pset_fm v \<phi> \<equiv> (\<forall>a \<in> atoms \<phi>. types_pset_atom v a)"

consts types :: "('a \<Rightarrow> nat) \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<turnstile>" 45)
adhoc_overloading types types_pset_atom types_pset_fm

inductive_cases types_pset_atom_Member_cases:
  "v \<turnstile> s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2" "v \<turnstile> s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2" "v \<turnstile> s \<in>\<^sub>s t1 -\<^sub>s t2" "v \<turnstile> s \<in>\<^sub>s Single t"

context includes Set_member_no_ascii_notation
begin
abbreviation "urelem' v (\<phi> :: 'a pset_fm) t \<equiv> v \<turnstile> \<phi> \<and> v \<turnstile> t : 0"
end

definition urelem :: "'a pset_fm \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "urelem \<phi> t \<equiv> (\<exists>v. urelem' v \<phi> t)"

end