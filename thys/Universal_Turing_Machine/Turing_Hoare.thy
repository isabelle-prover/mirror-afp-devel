(* Title: thys/Turing_Hoare.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Modifications, comments by Franz Regensburger (FABR) 02/2022
 *)

section \<open>Hoare Rules for Turing Machines\<close>

theory Turing_Hoare
  imports Numerals
begin


subsection \<open>Hoare\_halt and Hoare\_unhalt for total correctness\<close>

subsubsection \<open>Definition for Hoare\_halt and Hoare\_unhalt conditions\<close>

type_synonym assert = "tape \<Rightarrow> bool"

definition 
  assert_imp :: "assert \<Rightarrow> assert \<Rightarrow> bool" ("_ \<mapsto> _" [0, 0] 100)
  where
    "P \<mapsto> Q \<equiv> \<forall>l r. P (l, r) \<longrightarrow> Q (l, r)"

lemma refl_assert[intro, simp]:
  "P \<mapsto> P"
  unfolding assert_imp_def by simp

(* Purpose of the function holds_for:
 * We do not need to apply the selector snd on a configuration c if
 * we just like to apply a predicate to the tape component of the configuration.
 * 
 * We may write 
 *   Q holds_for c
 *  instead of
 *   Q (snd c)
 *)

fun 
  holds_for :: "(tape \<Rightarrow> bool) \<Rightarrow> config \<Rightarrow> bool" ("_ holds'_for _" [100, 99] 100)
  where
    "P holds_for (s, l, r) = P (l, r)"  

lemma is_final_holds[simp]:
  assumes "is_final c"
  shows "Q holds_for (steps c p n) = Q holds_for c"
  using assms 
  by(induct n;cases c,auto)

(* Hoare notation and rules for total correctness *)

(* halting case:
   If the pre-condition P holds for a tape
   then the program p eventually reaches the final state 0 and
   the post-condition holds for (the tape of) the final configuration.
 *)

definition
  Hoare_halt :: "assert \<Rightarrow> tprog0 \<Rightarrow> assert \<Rightarrow> bool" ("(\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
    "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace> \<equiv> (\<forall>tap. P tap \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) p n) \<and> Q holds_for (steps0 (1, tap) p n) ))"

(* not halting case:
   If the pre-condition P holds for a tape
   then the program p never reaches the final state 0. 
 *)
definition
  Hoare_unhalt :: "assert \<Rightarrow> tprog0 \<Rightarrow> bool" ("(\<lbrace>(1_)\<rbrace>/ (_)) \<up>" 50)
  where
    "\<lbrace>P\<rbrace> p \<up> \<equiv> \<forall>tap. P tap \<longrightarrow> (\<forall> n . \<not>(is_final (steps0 (1, tap) p n)))"

lemma Hoare_haltI:
  assumes "\<And>l r. P (l, r) \<Longrightarrow> \<exists>n. is_final (steps0 (1, (l, r)) p n) \<and> Q holds_for (steps0 (1, (l, r)) p n)"
  shows "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>"
  unfolding Hoare_halt_def 
  using assms by auto

lemma Hoare_haltE:
  assumes "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>"
  and "P (l, r)"
shows "\<exists>n. is_final (steps0 (1, (l, r)) p n) \<and> Q holds_for (steps0 (1, (l, r)) p n)"
  using assms by (auto simp add: Hoare_halt_def)

lemma Hoare_unhaltI:
  assumes "\<And>l r n. P (l, r) \<Longrightarrow> \<not> is_final (steps0 (1, (l, r)) p n)"
  shows "\<lbrace>P\<rbrace> p \<up>"
  unfolding Hoare_unhalt_def 
  using assms 
by auto

lemma Hoare_unhaltE:
  assumes "\<lbrace>P\<rbrace> p \<up>"
  and  "P tap"
shows "\<not> (is_final (steps0 (1, tap) p n))"
proof
  assume major: "is_final (steps0 (1, tap) p n)"
  from assms(1) have "\<forall>tap. P tap \<longrightarrow> (\<forall> n . \<not> (is_final (steps0 (1, tap) p n)))"
    by (auto simp add: Hoare_unhalt_def)
  with assms(2) have "(\<forall> n . \<not> (is_final (steps0 (1, tap) p n)))" by blast
  with major show "False" by auto
qed

(* Some alternative introduction and elimination rules without intermediate concept holds_for *)
(* Added by FABR *)

lemma Hoare_halt_iff:
 "\<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>
   \<longleftrightarrow> 
  (\<forall>l1 r1. P (l1,r1) \<longrightarrow> (\<exists>stp l0 r0.  steps0 (1, l1,r1) tm stp = (0,l0,r0) \<and> Q (l0,r0)))"
  unfolding Hoare_halt_def
proof
  show " \<forall>tap. P tap \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n)
         \<Longrightarrow> \<forall>l1 r1. P (l1, r1) \<longrightarrow> (\<exists>stp l0 r0. steps0 (1, l1, r1) tm stp = (0, l0, r0) \<and> Q (l0, r0))"
    by (metis holds_for.elims(2) is_final.simps)
next
  show "\<forall>l1 r1. P (l1, r1) \<longrightarrow> (\<exists>stp l0 r0. steps0 (1, l1, r1) tm stp = (0, l0, r0) \<and> Q (l0, r0))
         \<Longrightarrow> \<forall>tap. P tap \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n)"
    by (metis before_final holds_for.simps is_finalI old.prod.exhaust)
qed

(* Use like this:

    thm Hoare_halt_iff[THEN iffD1]
    
    \<lbrace>?P1\<rbrace> ?tm1 \<lbrace>?Q1\<rbrace>
     \<Longrightarrow> \<forall>l1 r1. ?P1 (l1, r1) \<longrightarrow> (\<exists>stp l0 r0. steps0 (1, l1, r1) ?tm1 stp = (0, l0, r0) \<and> ?Q1 (l0, r0))
    
    thm Hoare_halt_iff[THEN iffD2]
    
    \<forall>l1 r1. ?P1 (l1, r1) \<longrightarrow> (\<exists>stp l0 r0. steps0 (1, l1, r1) ?tm1 stp = (0, l0, r0) \<and> ?Q1 (l0, r0))
     \<Longrightarrow> \<lbrace>?P1\<rbrace> ?tm1 \<lbrace>?Q1\<rbrace>

 *)

lemma Hoare_halt_I0:
assumes "\<And>l1 r1. P(l1, r1) \<Longrightarrow> steps0 (1, l1, r1) tm stp = (0, l0, r0) \<and> Q (l0, r0)"
shows "\<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>"
  using assms Hoare_halt_iff[THEN iffD2]
  by blast

lemma Hoare_halt_E0:
  assumes major: "\<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>"
and "P(l1, r1)"
shows "\<exists>stp l0 r0. steps0 (1, l1, r1) tm stp = (0, l0, r0) \<and> Q(l0, r0)"
  using assms Hoare_halt_iff[THEN iffD1]
  by (auto simp add: Hoare_halt_def)

(* Despite their triviality, the following lemmas explain our general approach in proving total correctness *)

lemma partial_correctness_and_halts_imp_total_correctness': (* mind the parenthesis arround the premise *)
  assumes partial_corr: "(\<exists>stp l1 r1. P (l1, r1) \<and>  is_final (steps0 (1, l1,r1) tm stp)) \<longrightarrow> \<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>"
  and halts: "(\<exists>stp l1 r1. P (l1, r1) \<and>  is_final (steps0 (1, l1,r1) tm stp))"
shows "\<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>"
  using halts partial_corr by blast

(* is the same as *)

lemma partial_correctness_and_halts_imp_total_correctness:
  assumes partial_corr: "\<forall>l1 r1 stp. P (l1, r1) \<and> is_final (steps0 (1, l1,r1) tm stp) \<longrightarrow> \<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>"
  and halts: "(\<exists>stp l1 r1. P (l1, r1) \<and>  is_final (steps0 (1, l1,r1) tm stp))"
shows "\<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>"
  using halts partial_corr by blast

(* because of simple predicate logic *)

lemma "( (\<exists>stp l1 r1. P (l1, r1) \<and>  is_final (steps0 (1, l1,r1) tm stp)) \<longrightarrow> \<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace> )
       \<longleftrightarrow>
       (  \<forall>stp l1 r1. (P (l1, r1) \<and> is_final (steps0 (1, l1,r1) tm stp)  \<longrightarrow> \<lbrace>P\<rbrace> tm \<lbrace>Q\<rbrace>)  )"
  by blast

(* --- *)

lemma Hoare_consequence:
  assumes "P' \<mapsto> P" "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>" "Q \<mapsto> Q'"
  shows "\<lbrace>P'\<rbrace> p \<lbrace>Q'\<rbrace>"
  using assms
  unfolding Hoare_halt_def assert_imp_def
  by (metis holds_for.simps surj_pair)

subsubsection \<open>Relation between Hoare\_halt and Hoare\_unhalt\<close>

lemma Hoare_halt_impl_not_Hoare_unhalt:
  assumes "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>" and "P tap"
  shows "\<not>(\<lbrace>P\<rbrace> p \<up>)"
proof
  assume "\<lbrace>P\<rbrace> p \<up>"
  then have "\<forall>tap. P tap \<longrightarrow> (\<forall> n . \<not> (is_final (steps0 (1, tap) p n)))"
    by (auto simp add: Hoare_unhalt_def)
  with \<open>P tap\<close> have L1: "(\<forall> n . \<not> (is_final (steps0 (1, tap) p n)))" by blast
  from assms have "(\<forall>tap. P tap \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) p n) \<and> Q holds_for (steps0 (1, tap) p n) ))"
    by (auto simp add: Hoare_halt_def)
  with \<open>P tap\<close> have "(\<exists>n. is_final (steps0 (1, tap) p n) \<and> Q holds_for (steps0 (1, tap) p n) )"
    by blast
  then obtain n where w_n: "is_final (steps0 (1, tap) p n) \<and> Q holds_for (steps0 (1, tap) p n)" by blast
  then have "is_final (steps0 (1, tap) p n)" by auto
  with L1 show False by auto
qed

lemma Hoare_unhalt_impl_not_Hoare_halt:
  assumes "\<lbrace>P\<rbrace> p \<up>" and "P tap"
  shows "\<not>(\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>)"
proof 
  assume "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>"
  then have
    "(\<forall>tap. P tap \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) p n) \<and> Q holds_for (steps0 (1, tap) p n) ))"
    by (auto simp add: Hoare_halt_def)
  with \<open>P tap\<close> have "(\<exists>n. is_final (steps0 (1, tap) p n) \<and> Q holds_for (steps0 (1, tap) p n) )"
    by blast
  then obtain n where w_n: "is_final (steps0 (1, tap) p n) \<and> Q holds_for (steps0 (1, tap) p n)" by blast
  then have L1: "is_final (steps0 (1, tap) p n)" by auto
  from assms have "\<forall>tap. P tap \<longrightarrow> (\<forall> n . \<not> (is_final (steps0 (1, tap) p n)))"
    by (auto simp add: Hoare_unhalt_def)
  with \<open>P tap\<close> have "\<not> (is_final (steps0 (1, tap) p n))" by blast
  with L1 show False by auto
qed

subsubsection \<open>Hoare\_halt and Hoare\_unhalt for composed Turing Machines\<close>

(*
    Note: "composable_tm (A, 0)" means: A is a composable Turing program

    \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>   \<lbrace>Q\<rbrace> B \<lbrace>S\<rbrace>   (A is composable)
    ----------------------------------------
               \<lbrace>P\<rbrace> A |+| B \<lbrace>S\<rbrace>
*)

lemma Hoare_plus_halt [case_names A_halt B_halt A_composable]: 
  assumes A_halt : "\<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>"
    and B_halt : "\<lbrace>Q\<rbrace> B \<lbrace>S\<rbrace>"
    and A_composable : "composable_tm (A, 0)"
  shows "\<lbrace>P\<rbrace> A |+| B \<lbrace>S\<rbrace>"
proof(rule Hoare_haltI)
  fix l r
  assume h: "P (l, r)"
  then obtain n1 l' r' 
    where "is_final (steps0 (1, l, r) A n1)"  
      and a1: "Q holds_for (steps0 (1, l, r) A n1)"
      and a2: "steps0 (1, l, r) A n1 = (0, l', r')"
    using A_halt unfolding Hoare_halt_def
    by (metis is_final_eq surj_pair) 
  then obtain n2 
    where "steps0 (1, l, r) (A |+| B) n2 = (Suc (length A div 2), l', r')"
    using A_composable by (rule_tac seq_tm_next) 
  moreover
  from a1 a2 have "Q (l', r')" by (simp)
  then obtain n3 l'' r''
    where "is_final (steps0 (1, l', r') B n3)" 
      and b1: "S holds_for (steps0 (1, l', r') B n3)"
      and b2: "steps0 (1, l', r') B n3 = (0, l'', r'')"
    using B_halt unfolding Hoare_halt_def 
    by (metis is_final_eq surj_pair) 
  then have "steps0 (Suc (length A div 2), l', r')  (A |+| B) n3 = (0, l'', r'')"
    using A_composable by (rule_tac seq_tm_final) 
  ultimately show 
    "\<exists>n. is_final (steps0 (1, l, r) (A |+| B) n) \<and> S holds_for (steps0 (1, l, r) (A |+| B) n)"
    using b1 b2 by (rule_tac x = "n2 + n3" in exI) (simp)
qed

(*
    \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>   \<lbrace>Q\<rbrace> B loops   (A is composable)
    ------------------------------------------
              \<lbrace>P\<rbrace> A |+| B  loops
*)

lemma Hoare_plus_unhalt [case_names A_halt B_unhalt A_composable]:
  assumes A_halt: "\<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>"
    and B_uhalt: "\<lbrace>Q\<rbrace> B \<up>"
    and A_composable : "composable_tm (A, 0)"
  shows "\<lbrace>P\<rbrace> (A |+| B) \<up>"
proof(rule_tac Hoare_unhaltI)
  fix n l r 
  assume h: "P (l, r)"
  then obtain n1 l' r'
    where a: "is_final (steps0 (1, l, r) A n1)" 
      and b: "Q holds_for (steps0 (1, l, r) A n1)"
      and c: "steps0 (1, l, r) A n1 = (0, l', r')"
    using A_halt unfolding Hoare_halt_def 
    by (metis is_final_eq surj_pair) 
  then obtain n2 where eq: "steps0 (1, l, r) (A |+| B) n2 = (Suc (length A div 2), l', r')"
    using A_composable by (rule_tac seq_tm_next)
  then show "\<not> is_final (steps0 (1, l, r) (A |+| B) n)"
  proof(cases "n2 \<le> n")
    case True
    from b c have "Q (l', r')" by simp
    then have "\<forall> n. \<not> is_final (steps0 (1, l', r') B n)  "
      using B_uhalt unfolding Hoare_unhalt_def by simp
    then have "\<not> is_final (steps0 (1, l', r') B (n - n2))" by auto
    then obtain s'' l'' r'' 
      where "steps0 (1, l', r') B (n - n2) = (s'', l'', r'')" 
        and "\<not> is_final (s'', l'', r'')" by (metis surj_pair)
    then have "steps0 (Suc (length A div 2), l', r') (A |+| B) (n - n2) = (s''+ length A div 2, l'', r'')"
      using A_composable by (auto dest: seq_tm_second simp del: composable_tm.simps)
    then have "\<not> is_final (steps0 (1, l, r) (A |+| B) (n2 + (n  - n2)))"
      using A_composable by (simp only: steps_add eq) simp
    then show "\<not> is_final (steps0 (1, l, r) (A |+| B) n)" 
      using \<open>n2 \<le> n\<close> by simp
  next 
    case False
    then obtain n3 where "n = n2 - n3"
      using diff_le_self le_imp_diff_is_add nat_le_linear
        add.commute by metis
    moreover
    with eq show "\<not> is_final (steps0 (1, l, r) (A |+| B) n)"
      by (simp add: not_is_final[where ?n1.0="n2"])
  qed
qed

subsection \<open>Trailing Blanks on the left tape do not matter for Hoare\_halt\<close>

text \<open>The following theorems have major impact on the definition of Turing Computability.\<close>

lemma Hoare_halt_add_Bks_left_tape_L1:
  assumes "\<lbrace> \<lambda>tap. tap = ([], r)\<rbrace> p \<lbrace> (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k,  CR @ Bk \<up> l)) \<rbrace>"
  shows   "\<forall>z. \<exists>stp k l. (steps0 (1, Bk\<up>z,r) p stp) = (0, Bk \<up> k, CR @ Bk \<up> l)"
proof -
  from assms
  have "\<exists>stp. is_final (steps0 (1, [], r) p stp) \<and> (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, CR @ Bk \<up> l)) holds_for steps0 (1, [], r) p stp"
    using Hoare_haltE[OF assms] by auto
  then obtain stp where
    w: "is_final (steps0 (1, [], r) p stp) \<and> (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, CR @ Bk \<up> l)) holds_for steps0 (1, [], r) p stp" by blast
  then have  "\<exists>k  l. snd(steps0 (1, [], r) p stp) = (Bk \<up> k, CR @ Bk \<up> l)"
  proof (cases " steps0 (1, [], r) p stp")
    case (fields s' l' r')
    then have "steps0 (1, [], r) p stp = (s', l', r')" .
    then show ?thesis
      using w holds_for.simps snd_conv by auto
  qed
  moreover from w have "fst (steps0 (1, [], r) p stp) = 0"
    by (metis is_final_eq surjective_pairing)
  ultimately have "\<exists>stp k l. steps0 (1, [], r) p stp = (0, Bk \<up> k, CR @ Bk \<up> l)"
    by (metis surjective_pairing)
  then have "\<forall>z. \<exists>stp k l. (steps0 (1, (Bk\<up>z, r)) p stp) = (0, Bk \<up> k, CR @ Bk \<up> l)"
    using steps_left_tape_Nil_imp_All 
    by blast
  then show ?thesis
    by blast
qed

lemma Hoare_halt_add_Bks_left_tape_L2:
  assumes "\<forall>z. \<exists>stp k l. (steps0 (1, Bk\<up>z,r) p stp) = (0, Bk \<up> k, CR @ Bk \<up> l)"
  shows "\<lbrace>(\<lambda>tap. \<exists>z. tap = (Bk\<up>z, r))\<rbrace> p \<lbrace> (\<lambda>tap. (\<exists>k l. tap = (Bk \<up> k,  CR @ Bk \<up> l))) \<rbrace>"
  unfolding Hoare_halt_def
proof 
  fix tap
  show "(\<exists>z. tap = (Bk \<up> z, r)) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) p n) \<and>
                                   (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, CR @ Bk \<up> l)) holds_for steps0 (1, tap) p n)"
  proof
    assume A: "\<exists>z. tap = (Bk \<up> z, r)"
    from assms have B: "\<And>z. \<exists>stp k l. steps0 (1, Bk \<up> z, r) p stp = (0, Bk \<up> k, CR @ Bk \<up> l)" by blast
    from A obtain z2 where w_z: "tap = (Bk \<up> z2, r)" by blast
    from B obtain stp k l where w: "(steps0 (1, (Bk\<up>z2, r)) p stp) = (0, Bk \<up> k, CR @ Bk \<up> l)"
      by blast

    show "\<exists>n. is_final (steps0 (1, tap) p n) \<and> (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, CR @ Bk \<up> l)) holds_for steps0 (1, tap) p n"
    proof
      show "is_final (steps0 (1, tap) p stp) \<and> (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, CR @ Bk \<up> l)) holds_for steps0 (1, tap) p stp"
      proof
        from w and w_z       
        show "is_final (steps0 (1, tap) p stp)" by (auto simp add: is_final_eq)
      next
        from w and w_z show "(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, CR @ Bk \<up> l)) holds_for steps0 (1, tap) p stp"
          by auto
      qed
    qed
  qed
qed

theorem Hoare_halt_add_Bks_left_tape:
  "\<lbrace>(\<lambda>tap.     tap = ([]  , r))\<rbrace> p \<lbrace> (\<lambda>tap. (\<exists>k l. tap = (Bk \<up> k,  CR @ Bk \<up> l))) \<rbrace>
  \<Longrightarrow>
   \<forall>z.  \<lbrace>(\<lambda>tap. tap = (Bk\<up>z, r))\<rbrace> p \<lbrace> (\<lambda>tap. (\<exists>k l. tap = (Bk \<up> k,  CR @ Bk \<up> l))) \<rbrace>"
  using Hoare_halt_add_Bks_left_tape_L1 Hoare_halt_add_Bks_left_tape_L2
  by (simp add: Hoare_haltI  Hoare_halt_def Pair_inject old.prod.exhaust )

theorem Hoare_halt_del_Bks_left_tape:
  "\<lbrace>(\<lambda>tap. \<exists>z. tap = (Bk\<up>z, r))\<rbrace> p \<lbrace> (\<lambda>tap. (\<exists>k l. tap = (Bk \<up> k,  CR @ Bk \<up> l))) \<rbrace>
  \<Longrightarrow>
   \<lbrace>(\<lambda>tap.     tap = ([]  , r))\<rbrace> p \<lbrace> (\<lambda>tap. (\<exists>k l. tap = (Bk \<up> k,  CR @ Bk \<up> l))) \<rbrace>"
  unfolding Hoare_halt_def
  by auto

(* Hoare unhalt *)

lemma is_final_del_Bks: "is_final (steps0 (s, Bk \<up> k, r) tm stp) \<Longrightarrow> is_final (steps0 (s, [], r) tm stp)"
proof (cases k)
  assume "is_final (steps0 (s, Bk \<up> k, r) tm stp)"
    and "k=0"
  case 0
  then show ?thesis
    using \<open>is_final (steps0 (s, Bk \<up> k, r) tm stp)\<close> replicate_0 by auto
next
  fix nat
  assume A: "is_final (steps0 (s, Bk \<up> k, r) tm stp)" and "k = Suc nat"
  then have B: "0 <k" by auto
  have "\<exists> l' r'. (steps0 (s, Bk \<up> k, r) tm stp) = (0, l', r')"
  proof (cases "steps0 (s, Bk \<up> k, r) tm stp")
    case (fields a b c)
    then show ?thesis
      using A is_final_eq by auto
  qed
  then obtain l' r' where w: "steps0 (s, Bk \<up> k, r) tm stp = (0, l', r')" by blast
  then have "steps0 (s, []@Bk \<up> k, r) tm stp = (0, l', r')" by auto

  with B have "\<exists>zb CL'. l' = CL'@Bk\<up>zb  \<and> steps0 (s,[], r) tm stp = (0,CL',r')"
    using steps_left_tape_ShrinkBkCtx_arbitrary_CL
    by auto
  then obtain zb CL' where "l' = CL'@Bk\<up>zb  \<and> steps0 (s,[], r) tm stp = (0,CL',r')" by blast
  then show ?thesis by auto
qed

lemma Hoare_unhalt_add_Bks_left_tape_L1:
  assumes "\<lbrace>\<lambda>tap. tap = ([], r)\<rbrace> p \<up>"
  shows "\<forall>z. \<lbrace>\<lambda>tap. tap = (Bk \<up> z, r)\<rbrace> p \<up>"
proof -
  from assms have "\<And>stp. \<not> is_final (steps0 (1, [], r) p stp)"
    using Hoare_unhaltE[OF assms] by auto
  then have "\<And>stp z. \<not> is_final (steps0 (1, Bk \<up> z, r) p stp)"
    using is_final_del_Bks
    by blast
  then show ?thesis
    by (simp add: Hoare_unhaltI Hoare_unhalt_def)
qed

subsection \<open>Halt lemmas with respect to function mk\_composable0\<close>

theorem Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list: "\<lbrace>\<lambda>tap. tap = ([], cl)\<rbrace> tm \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], cl)\<rbrace> mk_composable0 tm \<lbrace>Q\<rbrace>" 
  unfolding Hoare_halt_def
proof -
  assume A: "\<forall>tap. (tap = ([], cl)) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n)"
  show "\<forall>tap. (tap = ([], cl)) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n)"
  proof
    fix tap
    show "(tap = ([], cl)) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n)"
    proof
      assume "tap = ([], cl)"
      with A have "(\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n)"
        by auto
      then obtain n where w_n: "is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n"
        by blast

      with \<open>tap = ([], cl)\<close> have w_n': "is_final (steps0 (1, [], cl) tm n) \<and> Q holds_for steps0 (1, [], cl) tm n" by auto

      have "\<exists>n. is_final (steps0 (1, [], cl) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, [], cl) (mk_composable0 tm) n"

      proof (cases "\<forall>stp. steps0 (1,[],cl) (mk_composable0 tm) stp = steps0 (1,[], cl) tm stp")
        case True
        with w_n' have "is_final (steps0 (1, [], cl) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, [], cl) (mk_composable0 tm) n" by auto
        then show ?thesis by auto
      next
        case False
        then have "\<exists>stp. steps0 (1, [], cl) (mk_composable0 tm) stp \<noteq> steps0 (1, [], cl) tm stp" by blast
        then obtain stp where w_stp: "steps0 (1, [], cl) (mk_composable0 tm) stp \<noteq> steps0 (1, [], cl) tm stp" by blast

        show "\<exists>m. is_final (steps0 (1, [], cl) (mk_composable0 tm) m) \<and> Q holds_for steps0 (1, [], cl) (mk_composable0 tm) m"
        proof -
          from w_stp have F0: "0 < stp \<and>
                           (\<exists>fl fr.
                                   snd (steps0 (1, [], cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, [], cl) (mk_composable0 tm) i = steps0 (1, [], cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, [], cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, [], cl) (mk_composable0 tm) j =(0, fl, fr)))"
            by (rule mk_composable0_tm_at_most_one_diff')

          from F0 have "0 < stp" by auto

          from F0 obtain fl fr where w_fl_fr: "snd (steps0 (1, [], cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, [], cl) (mk_composable0 tm) i = steps0 (1, [], cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, [], cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, [], cl) (mk_composable0 tm) j =(0, fl, fr))" by blast


          have "steps0 (1, [], cl) tm (stp+1) = steps0 (1, [], cl) tm  n"
          proof (cases "steps0 (1, [], cl) tm n")
            case (fields fsn fln frn)
            then have "steps0 (1, [], cl) tm n = (fsn, fln, frn)" .
            with w_n' have "is_final (fsn, fln, frn)" by auto
            with is_final_eq have "fsn=0" by auto
            with \<open>steps0 (1, [], cl) tm n = (fsn, fln, frn)\<close>  have "steps0 (1, [], cl) tm n = (0, fln, frn)" by auto

            show "steps0 (1, [], cl) tm (stp + 1) = steps0 (1, [], cl) tm n"
            proof (cases "n \<le> stp+1")
              case True
              then have "n \<le> stp + 1" .
              show ?thesis
              proof -
                from \<open>steps0 (1, [], cl) tm n = (0, fln, frn)\<close> and \<open>n \<le> stp + 1\<close> have "steps0 (1, [], cl) tm (stp+1) = (0, fln, frn)"
                  by (rule stable_config_after_final_ge_2')
                with \<open>fsn=0\<close> and \<open>steps0 (1, [], cl) tm n = (fsn, fln, frn)\<close> show ?thesis by auto
              qed
            next
              case False
              then have "stp + 1 \<le> n" by arith
              show ?thesis
              proof -
                from w_fl_fr have "steps0 (1, [], cl) tm (stp+1) = (0, fl, fr)" by auto
                have "steps0 (1, [], cl) tm n = (0, fl, fr)"
                proof (rule stable_config_after_final_ge_2')
                  from \<open>steps0 (1, [], cl) tm (stp+1) = (0, fl, fr)\<close> show "steps0 (1, [], cl) tm (stp+1) = (0, fl, fr)" by auto
                next
                  from \<open>stp + 1 \<le> n\<close> show "stp + 1 \<le> n" .
                qed
                with \<open>steps0 (1, [], cl) tm (stp+1) = (0, fl, fr)\<close> show ?thesis by auto
              qed
            qed
          qed

          with w_n' have "is_final(steps0 (1, [], cl) tm (stp+1)) \<and> Q holds_for steps0 (1, [], cl) tm (stp+1)" by auto
          moreover from w_fl_fr have "steps0 (1, [], cl) tm (stp+1) = steps0 (1, [], cl) (mk_composable0 tm) (stp+1)" by auto
          ultimately have "is_final(steps0 (1, [], cl) (mk_composable0 tm) (stp+1)) \<and> Q holds_for steps0 (1, [], cl) (mk_composable0 tm) (stp+1)" by auto
          then show ?thesis by blast
        qed
      qed
      with \<open>tap = ([], cl)\<close> show "\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n" by auto
    qed
  qed
qed

theorem Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list_rev: "\<lbrace>\<lambda>tap. tap = ([], cl)\<rbrace> mk_composable0 tm \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], cl)\<rbrace> tm \<lbrace>Q\<rbrace>" 
  unfolding Hoare_halt_def
proof -
  assume A: "\<forall>tap. tap = ([], cl) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n)"
  show "\<forall>tap. tap = ([], cl) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n)"
  proof
    fix tap
    show "(tap = ([], cl) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n))"
    proof
      assume "tap = ([], cl)"
      with A have "(\<exists>n. is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n)"
        by auto
      then obtain n where w_n: "is_final (steps0 (1, tap) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, tap) (mk_composable0 tm) n"
        by blast

      with \<open>tap = ([], cl)\<close> have w_n': "is_final (steps0 (1, [], cl) (mk_composable0 tm) n) \<and> Q holds_for steps0 (1, [], cl) (mk_composable0 tm) n" by auto

      have "\<exists>n. is_final (steps0 (1, [], cl) tm n) \<and> Q holds_for steps0 (1, [], cl) tm n"

      proof (cases "\<forall>stp. steps0 (1,[],cl) (mk_composable0 tm) stp = steps0 (1,[], cl) tm stp")
        case True
        with w_n' have "is_final (steps0 (1, [], cl)  tm n) \<and> Q holds_for steps0 (1, [], cl)  tm n" by auto
        then show ?thesis by auto
      next
        case False
        then have "\<exists>stp. steps0 (1, [], cl) (mk_composable0 tm) stp \<noteq> steps0 (1, [], cl) tm stp" by blast
        then obtain stp where w_stp: "steps0 (1, [], cl) (mk_composable0 tm) stp \<noteq> steps0 (1, [], cl) tm stp" by blast

        show "\<exists>m. is_final (steps0 (1, [], cl) tm m) \<and> Q holds_for steps0 (1, [], cl) tm m"
        proof -
          from w_stp have F0: "0 < stp \<and>
                           (\<exists>fl fr.
                                   snd (steps0 (1, [], cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, [], cl) (mk_composable0 tm) i = steps0 (1, [], cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, [], cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, [], cl) (mk_composable0 tm) j =(0, fl, fr)))"
            by (rule mk_composable0_tm_at_most_one_diff')

          from F0 have "0 < stp" by auto

          from F0 obtain fl fr where w_fl_fr: "snd (steps0 (1, [], cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, [], cl) (mk_composable0 tm) i = steps0 (1, [], cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, [], cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, [], cl) (mk_composable0 tm) j =(0, fl, fr))" by blast


          have "steps0 (1, [], cl) (mk_composable0 tm) (stp+1) = steps0 (1, [], cl) (mk_composable0 tm)  n"
            by (metis One_nat_def add_Suc_right is_final.elims(2) less_add_one nat_le_linear stable_config_after_final_ge w_fl_fr w_n')
          with w_n' have "is_final(steps0 (1, [], cl) (mk_composable0 tm) (stp+1)) \<and> Q holds_for steps0 (1, [], cl) (mk_composable0 tm) (stp+1)" by auto
          moreover from w_fl_fr have "steps0 (1, [], cl) tm (stp+1) = steps0 (1, [], cl) (mk_composable0 tm) (stp+1)" by auto
          ultimately have "is_final(steps0 (1, [], cl)  tm (stp+1)) \<and> Q holds_for steps0 (1, [], cl) tm (stp+1)" by auto
          then show ?thesis by blast
        qed
      qed
      with \<open>tap = ([], cl)\<close> show "\<exists>n. is_final (steps0 (1, tap) tm n) \<and> Q holds_for steps0 (1, tap) tm n" by auto
    qed
  qed
qed

lemma Hoare_unhalt_tm_impl_Hoare_unhalt_mk_composable0_cell_list: "(\<lbrace>\<lambda>tap. tap = ([], cl )\<rbrace> tm \<up>) \<Longrightarrow> (\<lbrace>\<lambda>tap. tap = ([], cl) \<rbrace> (mk_composable0 tm) \<up>)" 
  unfolding Hoare_unhalt_def
proof -
  assume A: " \<forall>tap. (tap = ([], cl)) \<longrightarrow> (\<forall>n. \<not> is_final (steps0 (1, tap) tm n))"
  show  "\<forall>tap. (tap = ([], cl)) \<longrightarrow> (\<forall>n. \<not> is_final (steps0 (1, tap) (mk_composable0 tm) n))"
  proof
    fix tap
    show "(tap = ([], cl)) \<longrightarrow> (\<forall>n. \<not> is_final (steps0 (1, tap) (mk_composable0 tm) n))"
    proof
      assume "tap = ([], cl)"
      with A have B: "\<forall>n. \<not> is_final (steps0 (1, tap) tm n)" by auto

      show "\<forall>n. \<not> is_final (steps0 (1, tap) (mk_composable0 tm) n)"
      proof (cases "\<forall>stp. steps0 (1,[], cl) (mk_composable0 tm) stp = steps0 (1,[], cl) tm stp")
        case True
        then have "\<forall>stp. steps0 (1, [], cl) (mk_composable0 tm) stp = steps0 (1, [], cl) tm stp" .
        show ?thesis
        proof
          fix n

          from \<open>\<forall>stp. steps0 (1, [], cl) (mk_composable0 tm) stp = steps0 (1, [], cl) tm stp\<close>
          have "steps0 (1, [], cl) (mk_composable0 tm) n = steps0 (1, [], cl) tm n" by auto
          moreover from B and \<open>tap = ([], cl)\<close> have "\<not> is_final (steps0 (1, [], cl) tm n)" by auto
          ultimately have "\<not> is_final (steps0 (1, [], cl)  (mk_composable0 tm) n)" by auto
          with  \<open>tap = ([], cl)\<close> show "\<not> is_final (steps0 (1, tap)  (mk_composable0 tm) n)" by auto
        qed
      next
        case False
        then have "\<not> (\<forall>stp. steps0 (1, [], cl) (mk_composable0 tm) stp = steps0 (1, [], cl) tm stp)" .
        then have "\<exists>stp. steps0 (1, [], cl) (mk_composable0 tm) stp \<noteq> steps0 (1, [], cl) tm stp" by blast
        then obtain stp where w_stp: "steps0 (1, [], cl) (mk_composable0 tm) stp \<noteq> steps0 (1, [], cl) tm stp" by blast

        show "\<forall>n. \<not> is_final (steps0 (1, tap) (mk_composable0 tm) n)"
        proof -
          from w_stp have F0: "0 < stp \<and>
                           (\<exists>fl fr.
                                   snd (steps0 (1, [], cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, [], cl) (mk_composable0 tm) i = steps0 (1, [], cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, [], cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, [], cl) (mk_composable0 tm) j =(0, fl, fr)))"
            by (rule mk_composable0_tm_at_most_one_diff')
          then have "(\<exists>fl fr.
                                   snd (steps0 (1, [], cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, [], cl) (mk_composable0 tm) i = steps0 (1, [], cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, [], cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, [], cl) (mk_composable0 tm) j =(0, fl, fr)))" by auto
          then obtain fl fr where w_fl_fr: "snd (steps0 (1, [], cl) tm stp) = (fl, fr) \<and>
                                   (\<forall>i < stp. steps0 (1, [], cl) (mk_composable0 tm) i = steps0 (1, [], cl) tm i) \<and>
                                   (\<forall>j > stp. steps0 (1, [], cl) tm (j) = (0, fl, fr) \<and> 
                                              steps0 (1, [], cl) (mk_composable0 tm) j =(0, fl, fr))" by blast
          then have "steps0 (1, [], cl) tm (stp+1) = (0, fl, fr)" by auto
          then have "is_final (steps0 (1, [], cl) tm (stp+1))" by auto
          with \<open>tap = ([], cl)\<close> have "is_final (steps0 (1, tap) tm (stp+1))" by auto
          moreover from B have "\<not> is_final (steps0 (1, tap) tm (stp+1))" by blast
          ultimately have False by auto
          then show ?thesis by auto
        qed
      qed
    qed
  qed
qed

(* --- trivial specializations for cells generated from lists of natural numbers or pairs of such cell lists --- *)

corollary Hoare_halt_tm_impl_Hoare_halt_mk_composable0: "\<lbrace>\<lambda>tap. tap = ([]::cell list, <nl>)\<rbrace> tm \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 tm \<lbrace>Q\<rbrace>"
  using Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list by auto

corollary Hoare_unhalt_tm_impl_Hoare_unhalt_mk_composable0: "(\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm \<up>) \<Longrightarrow> (\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> (mk_composable0 tm) \<up>)"
  using Hoare_unhalt_tm_impl_Hoare_unhalt_mk_composable0_cell_list by auto

(* --- *)

corollary Hoare_halt_tm_impl_Hoare_halt_mk_composable0_pair:
  "\<lbrace>\<lambda>tap. tap = ([], <(nl1,nl2)>)\<rbrace> tm \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <(nl1,nl2)>)\<rbrace> mk_composable0 tm \<lbrace>Q\<rbrace>"
  using Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list by auto

corollary Hoare_unhalt_tm_impl_Hoare_unhalt_mk_composable0_pair: "(\<lbrace>\<lambda>tap. tap = ([], <(nl1, nl2)>)\<rbrace> tm \<up>) \<Longrightarrow> (\<lbrace>\<lambda>tap. tap = ([], <(nl1,nl2)>)\<rbrace> (mk_composable0 tm) \<up>)"
  using Hoare_unhalt_tm_impl_Hoare_unhalt_mk_composable0_cell_list by auto


section \<open>The Halt Lemma: no infinite descend\<close>

lemma halt_lemma: 
  "\<lbrakk>wf LE; \<forall>n. (\<not> P (f n) \<longrightarrow> (f (Suc n), (f n)) \<in> LE)\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  by (metis wf_iff_no_infinite_down_chain)

end
