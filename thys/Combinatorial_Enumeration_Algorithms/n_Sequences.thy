section "N-Sequences"

theory n_Sequences
  imports
    "HOL.List"
    Common_Lemmas
begin

subsection"Definition"

definition n_sequences :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "n_sequences A n = {xs. set xs \<subseteq> A \<and> length xs = n}"

text"Cardinality: \<open>card A ^ n\<close>"
text"Example: \<open>n_sequences {0, 1} 2 = {[0,0], [0,1], [1,0], [1,1]}\<close>"

subsection"Algorithm"
                            
fun n_sequence_enum :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "n_sequence_enum xs 0 = [[]]"
| "n_sequence_enum xs (Suc n) = [x#r . x \<leftarrow> xs, r \<leftarrow> n_sequence_enum xs n]"


text "An enumeration of n-sequences already exists: \<open>n_lists\<close>. This part of this AFP entry is mostly
to establish the patterns used in the more complex combinatorial objects."

lemma "set (n_sequence_enum xs n) = set (List.n_lists n xs)"
  by(induct n) auto

thm set_n_lists

subsection"Verification"

subsubsection"Correctness"

theorem n_sequence_enum_correct: 
  "set (n_sequence_enum xs n) = n_sequences (set xs) n"
proof standard
  show "set (n_sequence_enum xs n) \<subseteq> n_sequences (set xs) n"
    unfolding n_sequences_def by (induct n) auto+
next
  show "n_sequences (set xs) n \<subseteq> set (n_sequence_enum xs n)"
  proof(induct n)
    case 0
    then show ?case
      unfolding n_sequences_def by auto
  next
    case (Suc n)
    
    have "\<lbrakk>n_sequences (set xs) n \<subseteq> set (n_sequence_enum xs n); set x \<subseteq> set xs; length x = Suc n\<rbrakk>
      \<Longrightarrow> \<exists>xa\<in>set xs. x \<in> (#) xa ` set (n_sequence_enum xs n)" for x
      unfolding n_sequences_def by (cases x) auto
      
    from this Suc show ?case
      unfolding n_sequences_def by auto
  qed
qed

subsubsection"Distinctness"

theorem n_sequence_enum_distinct: 
  "distinct xs \<Longrightarrow> distinct (n_sequence_enum xs n)"
  by (induct n) (auto simp: Cons_distinct_concat_map)

subsubsection"Cardinality"

lemma n_sequence_enum_length: 
  "length (n_sequence_enum xs n) = (length xs) ^ n "
  by(induct n arbitrary: xs) (auto simp: length_concat_map) 

text"of course \<open>card_lists_length_eq\<close> can directly proof it
but we want to derive it from \<open>n_sequence_enum_length\<close>"
thm card_lists_length_eq

theorem n_sequences_card:
  assumes "finite A"
  shows "card (n_sequences A n) = card A ^ n"
proof -
  obtain xs where set: "set xs = A" and dis: "distinct xs"
    using assms finite_distinct_list by auto
  have "length (n_sequence_enum xs n) = (length xs) ^ n"
    using n_sequence_enum_distinct n_sequence_enum_length by auto
  then have "card (set (n_sequence_enum xs n)) = card (set xs) ^ n"
    by (simp add: dis distinct_card n_sequence_enum_distinct)
  then have "card (n_sequences (set xs) n) = card (set xs) ^ n"
    by (simp add: n_sequence_enum_correct)
  then show "card (n_sequences A n) = card A ^ n"
    using set by simp
qed

end
