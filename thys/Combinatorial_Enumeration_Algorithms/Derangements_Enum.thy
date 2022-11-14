section"Derangements"
theory Derangements_Enum
  imports
    "HOL-Combinatorics.Multiset_Permutations"
    "Common_Lemmas"
   (* "Derangements.Derangements" *)
begin

subsection"Definition"

fun no_overlap :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "no_overlap _ [] = True"
| "no_overlap [] _ = True"
| "no_overlap (x#xs) (y#ys) = (x \<noteq> y \<and> no_overlap xs ys)"

lemma no_overlap_nth: "length xs = length ys \<Longrightarrow> i < length xs \<Longrightarrow> no_overlap xs ys \<Longrightarrow> xs ! i \<noteq> ys ! i" 
  by(induct xs ys arbitrary: i rule: list_induct2) (auto simp: less_Suc_eq_0_disj)

lemma nth_no_overlap: "length xs = length ys \<Longrightarrow> \<forall> i < length xs. xs ! i \<noteq> ys ! i \<Longrightarrow> no_overlap xs ys"
proof (induct xs ys rule: list_induct2)
  case (Cons x xs y ys)
  then show ?case using Suc_less_eq nth_Cons_Suc by fastforce
qed simp 
  
definition derangements :: "'a list \<Rightarrow> 'a list set" where
  "derangements xs = {ys. distinct ys \<and> length xs = length ys \<and> set xs = set ys \<and> no_overlap xs ys }"
text "A derangement of a list is a permutation where every element changes its position,
  assuming all elements are distinguishable."
text \<open>An alternative definition exists in \<open>Derangements.Derangements\<close> \cite{AFPderan}.\<close>
text "Cardinality: \<open>count_derangements (length xs)\<close> (from \<open>Derangements.Derangements\<close>)"
text "Example: \<open>derangements [0,1,2] = {[1,2,0], [2,0,1]}\<close>"

subsection"Algorithm"
fun derangement_enum_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "derangement_enum_aux [] ys = [[]]"
| "derangement_enum_aux (x#xs) ys = [y#r . y \<leftarrow> ys, r \<leftarrow> derangement_enum_aux xs (remove1 y ys), y \<noteq> x]"

fun derangement_enum :: "'a list  \<Rightarrow> 'a list list" where
 "derangement_enum xs = derangement_enum_aux xs xs"

subsection"Verification"

subsubsection"Correctness"

lemma derangement_enum_aux_elem_length: "zs \<in> set (derangement_enum_aux xs ys) \<Longrightarrow> length xs = length zs"
  by(induct xs arbitrary: ys zs) auto

lemma derangement_enum_aux_not_in: "y \<notin> set ys \<Longrightarrow> zs \<in> set (derangement_enum_aux xs ys) \<Longrightarrow> y \<notin> set zs"
proof(induct xs arbitrary: ys zs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain z zs2 where ob: "zs = z#zs2"
    by auto
  have "zs2 \<in> set (derangement_enum_aux xs (remove1 z ys)) \<Longrightarrow> y \<notin> set zs2"
    using Cons notin_set_remove1 by fast
  then show ?case using Cons ob
    by auto
qed

lemma derangement_enum_aux_in: "y \<in> set zs \<Longrightarrow> zs \<in> set (derangement_enum_aux xs ys) \<Longrightarrow> y \<in> set ys"
  using derangement_enum_aux_not_in by fast
  
lemma derangement_enum_aux_distinct_elem: "distinct ys \<Longrightarrow> zs \<in> set (derangement_enum_aux xs ys) \<Longrightarrow> distinct zs"
proof(induct xs arbitrary: ys zs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain z zs2 where ob: "zs = z#zs2"
    using Cons by auto
  then have ev: "zs2 \<in> set (derangement_enum_aux xs (remove1 z ys))"
    using Cons ob by auto

  have "distinct zs2"
    using ev Cons distinct_remove1 by fast
  moreover have "z \<notin> set zs2"
    using ev Cons(2) derangement_enum_aux_in by fastforce
  ultimately show ?case using ob by simp
qed

lemma derangement_enum_aux_no_overlap: "zs \<in> set (derangement_enum_aux xs ys) \<Longrightarrow> no_overlap xs zs"
  by(induct xs arbitrary: zs ys) auto

lemma derangement_enum_aux_set:
  "length xs = length ys \<Longrightarrow> zs \<in> set (derangement_enum_aux xs ys) \<Longrightarrow> set zs = set ys"
proof(induct xs ys arbitrary: zs rule: derangement_enum_aux.induct)
  case (1 ys)
  then show ?case by simp
next
  case (2 x xs ys)
  obtain z zs2 where ob: "zs = z#zs2"
    using 2 by auto
  have ev1: "zs2 \<in> set (derangement_enum_aux xs (remove1 z ys))"
    using 2 ob  by simp
  have ev2:"z \<in> set ys"
    using 2 ob by simp

  have "length xs = length (remove1 z ys)"
    using ev2 Suc_length_remove1 "2.prems"(1) by force
  then have "set zs2 = set (remove1 z ys)"
    using "2.hyps"[of z zs2] ev1 ev2  by simp

  then show ?case
    using ob notin_set_remove1 ev2 in_set_remove1 by fastforce
qed

lemma derangement_enum_correct_aux1:
  "\<lbrakk>distinct zs;length ys = length zs; length ys = length xs; set ys = set zs; no_overlap xs zs\<rbrakk>
   \<Longrightarrow> zs \<in> set (derangement_enum_aux xs ys)"
proof(induct xs arbitrary: zs ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain z zs2 where ob: "zs = z#zs2"
    using Cons length_0_conv neq_Nil_conv by metis

  have e1: "z \<noteq> x"
    using Cons.prems(5) ob  by auto

  have "distinct zs2"
    using Cons.prems(1) ob by auto 
  moreover have "length (remove1 z ys) = length zs2" using Cons.prems ob
    by (simp add: length_remove1) 
  moreover have "length (remove1 z ys) = length xs"
    by (simp add: Cons.prems(3) Cons.prems(4) length_remove1 ob) 
  moreover have "set (remove1 z ys) = set zs2"
    using Cons ob by (metis distinct_card distinct_remdups length_remdups_eq remove1.simps(2) set_remdups set_remove1_eq)
  moreover have "no_overlap xs zs2"
    using Cons.prems(5) ob by fastforce 

  ultimately have "zs2 \<in> set (derangement_enum_aux xs (remove1 z ys))"
    using Cons.hyps[of zs2 "(remove1 z ys)"] by simp
  then show ?case
    using ob e1 Cons by simp 
qed

theorem derangement_enum_correct: "distinct xs \<Longrightarrow> derangements xs = set (derangement_enum xs)"
proof(standard)
  show "distinct xs \<Longrightarrow> derangements xs \<subseteq> set (derangement_enum xs)"
    unfolding derangements_def using derangement_enum_correct_aux1 by auto 
next
  show "distinct xs \<Longrightarrow> set (derangement_enum xs) \<subseteq> derangements xs"
    unfolding derangements_def
    using derangement_enum_aux_set derangement_enum_aux_distinct_elem derangement_enum_aux_elem_length derangement_enum_aux_no_overlap
    by auto
qed

subsubsection"Distinctness"

lemma derangement_enum_aux_distinct: "distinct ys \<Longrightarrow> distinct (derangement_enum_aux xs ys)"
proof(induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    using inj2_distinct_concat_map_function_filter[of
        "Cons"
         ys
         "\<lambda>y. derangement_enum_aux xs (remove1 y ys)"
        "\<lambda>y. y \<noteq> x"
      ]
    using Cons Cons_inj2
    by (simp)
qed

theorem derangement_enum_distinct: "distinct xs \<Longrightarrow> distinct (derangement_enum xs)"
  using derangement_enum_aux_distinct by auto

(*
subsubsection"Cardinality"
should be provable with Derangements.Derangements
*)

end
