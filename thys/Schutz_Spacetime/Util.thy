(*  Title:      Schutz_Spacetime/Util.thy
    Authors:    Richard Schmoetten, Jake Palmer and Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)
theory Util
imports Main

begin

text \<open>Some "utility" proofs -- little proofs that come in handy every now and then.\<close>

text \<open>
  We need this in order to obtain a natural number which can be passed to the ordering function,
  distinct from two others, in the case of a finite set of events with cardinality a least 3.
\<close>

lemma is_free_nat:
  assumes "(m::nat) < n"
      and "n < c"
      and "c \<ge> 3"
  shows "\<exists>k::nat. k < m \<or> (m < k \<and> k < n) \<or> (n < k \<and> k < c)"
using assms by presburger

text \<open>Helpful proofs on sets.\<close>

lemma set_le_two [simp]: "card {a, b} \<le> 2"
  by (simp add: card_insert_if)

lemma set_le_three [simp]: "card {a, b, c} \<le> 3"
  by (simp add: card_insert_if)

lemma card_subset: "\<lbrakk>card Y = n; Y \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> n \<or> infinite X"
  using card_mono by blast

lemma card_subset_finite: "\<lbrakk>finite X; card Y = n; Y \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> n"
  using card_subset by auto

lemma three_subset: "\<lbrakk>x \<noteq> y; x \<noteq> z; y \<noteq> z; {x,y,z} \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> 3 \<or> infinite X"
  apply (case_tac "finite X")
  apply (auto simp : card_mono)
  apply (erule_tac Y = "{x,y,z}" in card_subset_finite)
  by auto

lemma three_in_set3:
  assumes "card X \<ge> 3"
  obtains x y z where "x\<in>X" and "y\<in>X" and "z\<in>X" and "x\<noteq>y" and "x\<noteq>z" and "y\<noteq>z"
  using assms by (auto simp add: card_le_Suc_iff numeral_3_eq_3)

lemma card_Collect_nat:
  assumes "(j::nat)>i"
  shows "card {i..j} = j-i+1"
  using card_atLeastAtMost
  using Suc_diff_le assms le_eq_less_or_eq by presburger

lemma inf_3_elms: assumes "infinite X" shows "(\<exists>x\<in>X. \<exists>y\<in>X. \<exists>z\<in>X. x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z)"
proof -
  obtain x y where 1: "x\<in>X" "y\<in>X" "y\<noteq>x"
    by (metis assms finite.emptyI finite.insertI rev_finite_subset singleton_iff subsetI)
  have "infinite (X-{x,y})"
    using infinite_remove by (simp add: assms)
  then obtain z where 2: "z\<in>X" "x\<noteq>z" "z\<noteq>y"
    using infinite_imp_nonempty by (metis Diff_eq_empty_iff insertCI subset_eq)
  show ?thesis using 1 2 by blast
qed

lemma card_3_dist: "card {x,y,z} = 3 \<longleftrightarrow> x\<noteq>y \<and> x\<noteq>z \<and> y\<noteq>z"
  by (simp add: eval_nat_numeral card_insert_if)

lemma card_3_eq:
  "card X = 3 \<longleftrightarrow> (\<exists>x y z. X={x,y,z} \<and> x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z)"
  (is "card X = 3 \<longleftrightarrow> ?card3 X")
proof
  assume asm: "card X = 3" hence "card X \<ge> 3" by simp
  then obtain x y z where "x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z" "{x,y,z} \<subseteq> X"
    apply (simp add: eval_nat_numeral)
    by (auto simp add: card_le_Suc_iff)
  thus "?card3 X"
    using Finite_Set.card_subset_eq \<open>card X = 3\<close>
    apply (simp add: eval_nat_numeral)
    by (smt (verit, ccfv_threshold) \<open>{x, y, z} \<subseteq> X\<close> card.empty card.infinite card_insert_if
      card_subset_eq empty_iff finite.emptyI insertE nat.distinct(1))
next
  show "?card3 X \<Longrightarrow> card X = 3"
    by (smt (z3) card.empty card.insert eval_nat_numeral(2) finite.intros(1) finite_insert insertE
      insert_absorb insert_not_empty numeral_3_eq_3 semiring_norm(26,27))
qed


lemma card_3_eq':
    "\<lbrakk>card X = 3; card {a,b,c} = 3; {a,b,c} \<subseteq>X\<rbrakk> \<Longrightarrow> X = {a,b,c}"
    "\<lbrakk>card X = 3; a \<in> X; b \<in> X; c \<in> X; a \<noteq> b; a \<noteq> c; b \<noteq> c\<rbrakk> \<Longrightarrow> X = {a,b,c}"
proof -
  show "\<lbrakk>card X = 3; card {a,b,c} = 3; {a,b,c} \<subseteq>X\<rbrakk> \<Longrightarrow> X = {a,b,c}"
    by (metis card.infinite card_subset_eq zero_neq_numeral)
  thus "\<lbrakk>card X = 3; a \<in> X; b \<in> X; c \<in> X; a \<noteq> b; a \<noteq> c; b \<noteq> c\<rbrakk> \<Longrightarrow> X = {a,b,c}"
    by (meson card_3_dist empty_subsetI insert_subset)
qed

lemma card_4_eq:
  "card X = 4 \<longleftrightarrow> (\<exists>S\<^sub>1. \<exists>S\<^sub>2. \<exists>S\<^sub>3. \<exists>S\<^sub>4. X = {S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4} \<and>
    S\<^sub>1 \<noteq> S\<^sub>2 \<and> S\<^sub>1 \<noteq> S\<^sub>3 \<and> S\<^sub>1 \<noteq> S\<^sub>4 \<and> S\<^sub>2 \<noteq> S\<^sub>3 \<and> S\<^sub>2 \<noteq> S\<^sub>4 \<and> S\<^sub>3 \<noteq> S\<^sub>4)"
  (is "card X = 4 \<longleftrightarrow> ?card4 X")
proof
  assume "card X = 4"
  hence "card X \<ge> 4" by auto
  then obtain S\<^sub>1 S\<^sub>2 S\<^sub>3 S\<^sub>4 where
    0: "S\<^sub>1\<in>X \<and> S\<^sub>2\<in>X \<and> S\<^sub>3\<in>X \<and> S\<^sub>4\<in>X" and
    1: "S\<^sub>1 \<noteq> S\<^sub>2 \<and> S\<^sub>1 \<noteq> S\<^sub>3 \<and> S\<^sub>1 \<noteq> S\<^sub>4 \<and> S\<^sub>2 \<noteq> S\<^sub>3 \<and> S\<^sub>2 \<noteq> S\<^sub>4 \<and> S\<^sub>3 \<noteq> S\<^sub>4"
    apply (simp add: eval_nat_numeral)
    by (auto simp add: card_le_Suc_iff)
  then have 2: "{S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4} \<subseteq> X" "card {S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4} = 4" by auto
  have "X = {S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4}"
    using Finite_Set.card_subset_eq \<open>card X = 4\<close>
    apply (simp add: eval_nat_numeral)
    by (smt (z3) \<open>card X = 4\<close> 2 card.infinite card_subset_eq nat.distinct(1))
  thus "?card4 X" using 1 by blast
next
  show "?card4 X \<Longrightarrow> card X = 4"
    by (smt (z3) card.empty card.insert eval_nat_numeral(2) finite.intros(1) finite_insert insertE
      insert_absorb insert_not_empty numeral_3_eq_3 semiring_norm(26,27))
qed


text \<open>These lemmas make life easier with some of the ordering proofs.\<close>

lemma less_3_cases: "n < 3 \<Longrightarrow> n = 0 \<or> n = Suc 0 \<or> n = Suc (Suc 0)"
  by auto

end