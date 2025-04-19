(* IsaGeoCoq - Tarski_Neutral_Archimedes

Port part of GeoCoq 3.4.0 (https://geocoq.github.io/GeoCoq/) in Isabelle/Hol 

Copyright (C) 2021-2025  Roland Coghetto roland.coghetto (at) cafr-msa2p.be

License: LGPL

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*)

theory Tarski_Neutral_Archimedes

imports 
  Tarski_Neutral

begin

section "Continuity Axioms"

context Tarski_neutral_dimensionless

begin

subsection "Definitions"

definition greenberg_s_axiom ::
  "bool"
  ("GreenBergsAxiom")
  where
    "greenberg_s_axiom \<equiv> \<forall> P Q R A B C. 
\<not> Col A B C \<and> Acute A B C \<and> Q \<noteq> R \<and> Per P Q R \<longrightarrow>
(\<exists> S. P S Q LtA A B C \<and> Q Out S R)"

definition aristotle_s_axiom ::
  "bool"
  ("AristotleAxiom") where
  "aristotle_s_axiom \<equiv> \<forall> P Q A B C.
\<not> Col A B C \<and> Acute A B C \<longrightarrow>
(\<exists> X Y. B Out A X \<and> B Out C Y \<and> Per B X Y \<and> P Q Lt X Y)"

definition Axiom1:: "bool" where "Axiom1 \<equiv> \<forall> A B C D. 
(\<exists> I. Col I A B \<and> Col I C D) \<or> \<not>  (\<exists> I. Col I A B \<and> Col I C D)"

definition PreGrad :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "PreGrad A B C D \<equiv> (A \<noteq> B \<and> Bet A B C \<and> Bet A C D \<and> Cong A B C D)"

fun Sym :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "Sym A B C = (if (A \<noteq> B \<and> Bet A B C) then
      (SOME x::'p. PreGrad A B C x)
         else
       A)"

fun Gradn :: "['p,'p] \<Rightarrow> nat \<Rightarrow>'p"where
  "Gradn A B n = (if (A = B) then 
                    A
                      else 
                    (if (n = 0) then 
                       A 
                         else 
                     (if (n = 1) then 
                        B 
                          else 
                        (Sym A B (Gradn A B (n-1))))))"

definition Grad :: "['p,'p,'p] \<Rightarrow> bool" where
  "Grad A B C \<equiv> \<exists> n. (n \<noteq> 0) \<and> (C = Gradn A B n)"

inductive GradI :: "['p,'p,'p] \<Rightarrow> bool" for A B
  where
    gradi_init : "GradI A B B" 
  | gradi_stab : "GradI A B C'" if 
    "GradI A B C" 
    and "Bet A C C'" 
    and "Cong A B C C'" 

definition Reach :: "['p,'p,'p,'p] \<Rightarrow> bool" where
  "Reach A B C D \<equiv> \<exists> B'. Grad A B B' \<and> C D Le A B'"

definition archimedes_axiom ::
  "bool"
  ("ArchimedesAxiom") where
  "archimedes_axiom \<equiv> \<forall> A B C D::'p. 
A \<noteq> B \<longrightarrow> Reach A B C D"

inductive GradA :: "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" for A B C
  where
    grada_init : "GradA A B C D E F" if 
    "A B C CongA D E F" 
  | grada_stab : "GradA A B C G H I" if 
    "GradA A B C D E F" 
    and "SAMS D E F A B C" 
    and "D E F A B C SumA G H I" 

inductive GradAExp :: "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" for A B C 
  where
    gradaexp_init : "GradAExp A B C D E F" if 
    "A B C CongA D E F" 
  | gradaexp_stab : "GradAExp A B C G H I" if 
    "GradAExp A B C D E F" 
    and "SAMS D E F D E F" 
    and "D E F D E F SumA G H I" 

definition Grad2 :: "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" where
  "Grad2 A B C D E F \<equiv> \<exists> n. (n \<noteq> 0) \<and> (C = Gradn A B n) \<and> (F = Gradn D E n)"

fun SymR :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "SymR A B = (SOME x::'p. B Midpoint A x)"

fun GradExpn :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p" where
  "(GradExpn A B n) = (if (A = B) then 
                         A 
                           else
                         (if (n = 0) then 
                            A
                              else
                            (if (n = 1) then 
                               B
                                 else 
                               (SymR A (GradExpn A B (n-1))))))"

definition GradExp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "GradExp A B C \<equiv>  \<exists> n. (n \<noteq> 0) \<and> C = GradExpn A B n"

definition GradExp2 :: "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" where
  "GradExp2 A B C D E F \<equiv> \<exists> n. (n \<noteq> 0) \<and> (C = GradExpn A B n) \<and> (F = GradExpn D E n)"

fun MidR :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "MidR A B = (SOME x. x Midpoint A B)"

fun GradExpInvn :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p" where
  "(GradExpInvn A B n) = (if (A = B) then 
                            A 
                              else
                            (if (n = 0) then 
                               B
                                 else
                               (if (n = 1) then 
                                  (MidR A B)
                                    else 
                                  (MidR A (GradExpInvn A B (n-1))))))"

definition GradExpInv :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "GradExpInv A B C \<equiv>  \<exists> n. B = GradExpInvn A C n"

subsection "Propositions"

lemma PreGrad_lem1:
  assumes "A \<noteq> B" and 
    "Bet A B C"
  shows "\<exists> x. PreGrad A B C x"
  by (meson PreGrad_def assms(1) assms(2) not_cong_3412 segment_construction) 

lemma PreGrad_uniq:
  assumes "PreGrad A B C x" and
    "PreGrad A B C y"
  shows "x = y"
  by (metis (no_types, lifting) PreGrad_def assms(1) assms(2) 
      bet_neq12__neq between_cong_3 cong_inner_transitivity)

lemma Diff_Mid__PreGrad:
  assumes "A \<noteq> B" and
    "B Midpoint A C"
  shows "PreGrad A B B C"
  by (simp add: PreGrad_def assms(1) assms(2) between_trivial midpoint_bet midpoint_cong)

lemma Diff_Mid_Mid_PreGrad:
  assumes "A \<noteq> B" and
    "B Midpoint A C" and
    "C Midpoint B D" 
  shows "PreGrad A B C D"
proof -
  have "Bet A B C" 
    using Midpoint_def assms(2) by presburger
  moreover have "Bet A C D" 
    using Midpoint_def assms(3) calculation is_midpoint_id outer_transitivity_between2 by blast
  moreover have "Cong A B C D" 
    using assms(2) assms(3) cong_transitivity midpoint_cong by blast
  ultimately show ?thesis 
    by (simp add: assms(1) PreGrad_def)
qed

lemma Sym_Diff__Diff:
  assumes "Sym A B C = D" and 
    "A \<noteq> D"
  shows "A \<noteq> B"
  using assms(1) assms(2) by force 

lemma Sym_Refl:
  "Sym A A A = A"
  by simp

lemma Diff_Mid__Sym:
  assumes "A \<noteq> B" and
    "B Midpoint A C"
  shows "Sym A B B = C" 
  using someI_ex by (metis Diff_Mid__PreGrad Sym.elims PreGrad_uniq 
      assms(1) assms(2) between_trivial) 

lemma Mid_Mid__Sym:
  assumes "A \<noteq> B" and
    "B Midpoint A C" and
    "C Midpoint B D"
  shows "Sym A B C = D" 
proof -
  have "PreGrad A B C D"
    by (simp add: Diff_Mid_Mid_PreGrad assms(1) assms(2) assms(3))
  thus ?thesis 
    using someI_ex assms(1) 
    by (metis PreGrad_uniq Sym.elims assms(2) midpoint_bet) 
qed

lemma Sym_Bet__Bet_Bet:
  assumes "Sym A B C = D" and 
    "A \<noteq> B" and 
    "Bet A B C" 
  shows "Bet A B D \<and> Bet A C D"
proof -
  have "(SOME x::'p. PreGrad A B C x) = D"
    using assms(1) assms(2) assms(3) by auto
  hence "PreGrad A B C D"
    by (metis PreGrad_lem1 assms(2) assms(3) someI2) 
  thus ?thesis
    by (meson PreGrad_def between_exchange4) 
qed

lemma Sym_Bet__Cong:
  assumes "Sym A B C = D" and 
    "A \<noteq> B" and 
    "Bet A B C" 
  shows "Cong A B C D"
proof -
  have "(SOME x::'p. PreGrad A B C x) = D"
    using assms(1) assms(2) assms(3) by auto
  hence "PreGrad A B C D"
    by (metis PreGrad_lem1 assms(2) assms(3) someI2) 
  thus ?thesis
    by (meson PreGrad_def between_exchange4) 
qed

lemma LemSym_aux:
  assumes "A \<noteq> B" and 
    "Bet A B C" and
    "Bet A C D" and
    "Cong A B C D"
  shows "Sym A B C = D"
proof -
  have "PreGrad A B C D"
    using PreGrad_def assms(1) assms(2) assms(3) assms(4) by blast
  thus ?thesis
    by (metis PreGrad_def PreGrad_uniq Sym_Bet__Bet_Bet Sym_Bet__Cong)
qed

lemma Lem_Gradn_id_n:
  "Gradn A A n = A" 
  by simp

lemma Lem_Gradn_0:
  "Gradn A B 0 = A" 
  by simp

lemma Lem_Gradn_1:
  "Gradn A B 1 = B" 
  by simp

lemma Diff__Gradn_Sym:
  assumes "A \<noteq> B" and
    "n > 1"
  shows "Gradn A B n = Sym A B (Gradn A B (n-1))" 
proof -
  have "\<not> (n = 0 \<and> n = 1)"
    by auto
  thus ?thesis 
    using assms(1) assms(2) by simp
qed

lemma Diff__Bet_Gradn_Suc:
  assumes "A \<noteq> B"
  shows "Bet A B (Gradn A B (Suc n))"
proof (induction n)
  case 0
  hence "Gradn A B (Suc 0) = B" 
    using assms(1) by simp
  thus ?case
    by (simp add: between_trivial) 
next
  case (Suc n)
  {
    assume 1: "Bet A B (Gradn A B (Suc n))"
    have "Gradn A B (Suc (Suc n)) = Sym A B (Gradn A B (Suc n))"
      by simp
    hence "Bet A B (Gradn A B (Suc (Suc n))) \<and> 
    Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))"
      using 1 Sym_Bet__Bet_Bet assms by presburger 
    hence "Bet A B (Gradn A B (Suc (Suc n)))"
      by simp
  }
  thus ?case
    using Suc.IH by blast 
qed

lemma Diff_Le_Gradn_Suc:
  assumes "A \<noteq> B"
  shows "A B Le A (Gradn A B (Suc n))"
  by (meson Diff__Bet_Gradn_Suc assms bet__le1213)

lemma Diff__Bet_Gradn:
  assumes "A \<noteq> B" and
    "n \<noteq> 0"
  shows "Bet A B (Gradn A B n)" 
  using assms(1) assms(2) Diff__Bet_Gradn_Suc not0_implies_Suc by blast

lemma Diff_Le_Gradn_n:
  assumes "A \<noteq> B" and
    "n \<noteq> 0"
  shows "A B Le A (Gradn A B n)"
  by (meson Diff__Bet_Gradn assms(1) assms(2) l5_12_a)

lemma Diff_Bet_Gradn_Suc_Gradn_Suc2:
  assumes "A \<noteq> B"
  shows "Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))"
proof (induction n)
  case 0
  hence 1: "Gradn A B (Suc 0) = B" 
    using assms(1) by simp
  from assms(1) 
  have "(Gradn A B (Suc (Suc 0))) = (Sym A B (Gradn A B (Suc 0)))" 
    by simp
  thus ?case
    by (metis "1" Diff__Bet_Gradn_Suc assms) 
next
  case (Suc n)
  {
    assume 1: "Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))"
    have "Gradn A B (Suc (Suc n)) = Sym A B (Gradn A B (Suc n))"
      by simp
    hence "Bet A B (Gradn A B (Suc (Suc n)))"
      using Diff__Bet_Gradn_Suc assms by blast 
    have "Gradn A B (Suc(Suc (Suc n))) = Sym A B (Gradn A B (Suc(Suc n)))"
      by simp
    hence "PreGrad A B (Gradn A B (Suc(Suc n))) (Gradn A B (Suc(Suc (Suc n))))"
      using PreGrad_def Sym_Bet__Bet_Bet Sym_Bet__Cong 
        \<open>Bet A B (Gradn A B (Suc (Suc n)))\<close> assms by presburger
    hence "Bet A B (Gradn A B (Suc(Suc (Suc n)))) \<and> 
    Bet A (Gradn A B (Suc(Suc n))) (Gradn A B (Suc(Suc (Suc n))))"
      by (metis Diff__Bet_Gradn_Suc Sym_Bet__Bet_Bet 
          \<open>Gradn A B (Suc (Suc (Suc n))) = Sym A B (Gradn A B (Suc (Suc n)))\<close> assms)     
    hence "Bet A (Gradn A B (Suc(Suc n))) (Gradn A B (Suc(Suc (Suc n))))"
      by blast
  }
  thus ?case
    using Suc.IH by blast
qed

lemma Diff__Bet_Gradn_Gradn_SucA:
  assumes "A \<noteq> B"
  shows "A (Gradn A B (Suc n)) Le A (Gradn A B (Suc (Suc n)))"
  by (meson Diff_Bet_Gradn_Suc_Gradn_Suc2 assms bet__le1213)

lemma Diff__Bet_Gradn_Gradn_Suc:
  assumes "A \<noteq> B"
  shows "Bet A (Gradn A B n) (Gradn A B (Suc n))"
proof (induction n)
  case 0
  hence "Gradn A B 0 = A" by simp
  thus ?case
    using between_trivial2 by presburger  
next
  case (Suc n)
  {
    assume 1: "Bet A (Gradn A B n) (Gradn A B (Suc n))"
    have "Gradn A B (Suc (Suc n)) = Sym A B (Gradn A B (Suc n))"
      by simp
    hence "Bet A B (Gradn A B (Suc (Suc n))) \<and> 
    Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))"
      using 1 Sym_Bet__Bet_Bet assms Diff__Bet_Gradn_Suc by presburger 
    hence "Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))"
      by blast
  }
  thus ?case
    using Suc.IH by simp
qed

lemma Bet_Gradn_Gradn_Suc: 
  shows "Bet A (Gradn A B n) (Gradn A B (Suc n))"
  by (metis Lem_Gradn_id_n Diff__Bet_Gradn_Gradn_Suc not_bet_distincts)

lemma Gradn_Le_Gradn_Suc: 
  shows "A (Gradn A B n) Le A (Gradn A B (Suc n))"
  using Bet_Gradn_Gradn_Suc bet__le1213 by blast

lemma Bet_Gradn_Suc_Gradn_Suc2:
  shows "Bet B (Gradn A B (Suc n)) (Gradn A B (Suc(Suc n)))"
  by (metis Bet_Gradn_Gradn_Suc Diff__Bet_Gradn_Suc between_exchange3) 

lemma Gradn_Suc_Le_Gradn_Suc2:
  shows "B (Gradn A B (Suc n)) Le B (Gradn A B (Suc(Suc n)))"
  using Bet_Gradn_Suc_Gradn_Suc2 bet__le1213 by blast

lemma Diff_Le__Bet_Gradn_Plus:
  assumes "A \<noteq> B" and
    "n \<le> m"
  shows "Bet A (Gradn A B n) (Gradn A B (k + n))"
proof (induction k)
  case 0
  thus ?case
    using between_trivial by auto
next
  case (Suc k)
  {
    assume "Bet A (Gradn A B n) (Gradn A B (k + n))" 
    have "Bet A (Gradn A B (k + n)) (Gradn A B (Suc (k + n)))"
      using Diff__Bet_Gradn_Gradn_Suc assms(1) by presburger 
    hence "Bet A (Gradn A B n) (Gradn A B ((Suc k) + n))"
      by (metis \<open>Bet A (Gradn A B n) (Gradn A B (k + n))\<close> 
          add_Suc between_exchange4) 
  }
  thus ?case
    using Suc.IH by blast 
qed

lemma  Diff_Le_Gradn_Plus:
  assumes "A \<noteq> B" and
    "n \<le> m"
  shows "A (Gradn A B n) Le A (Gradn A B (k + n))"
  by (meson Diff_Le__Bet_Gradn_Plus assms(1) assms(2) l5_12_a)

lemma Diff_Le_Bet__Gradn_Gradn:
  assumes "A \<noteq> B" and
    "n \<le> m"
  shows "Bet A (Gradn A B n) (Gradn A B m)"
proof (cases "n = 0")
  case True
  thus ?thesis
    using Lem_Gradn_0 between_trivial2 by presburger 
next
  case False
  hence 1: "n \<noteq> 0" 
    by auto
  show "Bet A (Gradn A B n) (Gradn A B m)"
  proof (cases "n = m")
    case True
    thus ?thesis 
      using between_trivial by presburger
  next
    case False
    hence "n < m"
      using assms(2) le_neq_implies_less by blast
    then obtain k where "m = k + n"
      using add.commute assms(2) le_Suc_ex by blast 
    have "Bet A (Gradn A B n) (Gradn A B (k + n))"
      using Diff_Le__Bet_Gradn_Plus assms(1) by blast 
    thus ?thesis
      using \<open>m = k + n\<close> by blast 
  qed
qed

lemma Diff_Le_Gradn:
  assumes "A \<noteq> B" and
    "n \<le> m"
  shows "A (Gradn A B n) Le A (Gradn A B m)"
  by (metis Diff_Le_Bet__Gradn_Gradn bet__le1213 assms(1) assms(2))

lemma Diff__Cong_Gradn_Suc_Gradn_Suc2:
  assumes "A \<noteq> B"
  shows "Cong A B (Gradn A B (Suc n)) (Gradn A B  (Suc (Suc n)))"
proof (induction n)
  case 0
  hence 1: "Gradn A B (Suc 0) = B" 
    using assms(1) by simp
  from assms(1) 
  have "(Gradn A B (Suc (Suc 0))) = (Sym A B (Gradn A B (Suc 0)))" by simp
  hence "(Gradn A B (Suc (Suc 0))) = (Sym A B B)"
    using "1" by presburger 
  obtain C where "B Midpoint A C"
    using symmetric_point_construction by blast
  hence "C = Sym A B B"
    using Diff_Mid__Sym assms by blast
  hence "(Gradn A B (Suc (Suc 0))) = C"
    using "1" \<open>Gradn A B (Suc (Suc 0)) = Sym A B (Gradn A B (Suc 0))\<close> by presburger 
  have "Cong A B (Gradn A B (Suc 0)) (Gradn A B  (Suc (Suc 0)))"
    using "1" \<open>B Midpoint A C\<close> \<open>Gradn A B (Suc (Suc 0)) = C\<close> midpoint_cong 
    by presburger 
  thus ?case
    by blast 
next
  case (Suc n)
  {
    assume "Cong A B (Gradn A B (Suc n)) (Gradn A B  (Suc (Suc n)))"
    have 1: "Gradn A B (Suc(Suc (Suc n))) = Sym A B (Gradn A B (Suc(Suc n)))"
      by simp
    have "Bet A B (Gradn A B (Suc (Suc n)))"
      using Diff__Bet_Gradn_Suc assms by blast
    hence "PreGrad A B (Gradn A B (Suc(Suc n))) (Gradn A B (Suc(Suc (Suc n))))"
      using 1 assms 
      by (metis PreGrad_def Sym_Bet__Cong Diff_Bet_Gradn_Suc_Gradn_Suc2) 
    hence "Cong A B (Gradn A B (Suc (Suc n))) (Gradn A B  (Suc(Suc (Suc n))))"
      using "1" Sym_Bet__Cong \<open>Bet A B (Gradn A B (Suc (Suc n)))\<close> assms 
      by presburger
  }
  thus ?case
    using Suc.IH by blast 
qed

lemma Cong_Gradn_Suc_Gradn_Suc2:
  shows "Cong A B (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))"
  using Diff__Cong_Gradn_Suc_Gradn_Suc2 cong_reflexivity by auto 

lemma Cong_Gradn_Gradn_Suc:
  shows "Cong a b (Gradn a b n) (Gradn a b (Suc n))"
proof (cases "a = b")
  case True
  thus ?thesis
    by (simp add: cong_trivial_identity)
next
  case False
  have 1: "Gradn a b 0 = a"
    by auto
  have 2: "(Gradn a b (Suc 0)) = b"
    by auto
  {
    assume 3: "n = 0"
    hence "Cong a b a b \<and> (Suc n = 1)"
      by (simp add: cong_reflexivity) 
    hence "Cong a b (Gradn a b n) (Gradn a b (Suc n))" 
      using 1 2 3 by presburger
  }
  moreover
  {
    assume "n \<noteq> 0"
    hence "Cong a b (Gradn a b n) (Gradn a b (Suc n))"
      by (metis False Diff__Cong_Gradn_Suc_Gradn_Suc2 old.nat.exhaust) 
  }
  ultimately
  show ?thesis
    by blast
qed

lemma Diff_Bet_Bet_Cong_Gradn_Suc: 
  assumes "A \<noteq> B" and 
    "Bet A B C" and
    "Bet A (Gradn A B n) C" and
    "Cong A B (Gradn A B n) C"
  shows "C = (Gradn A B (Suc n))"
proof (cases "n = 0")
  case True
  thus ?thesis
    by (metis Lem_Gradn_0 Diff__Bet_Gradn_Suc Cong_Gradn_Gradn_Suc 
        assms(1) assms(2) assms(4) between_cong)  
next
  case False
  hence "Bet A B (Gradn A B n)"
    using Diff__Bet_Gradn assms(1) by blast 
  thus ?thesis
    by (metis LemSym_aux Diff__Bet_Gradn_Gradn_Suc Cong_Gradn_Gradn_Suc 
        assms(1) assms(3) assms(4)) 
qed

lemma grad_rec_0_1:
  shows "Cong a b (Gradn a b 0) (Gradn a b 1)"
  by (simp add: cong_reflexivity)

lemma grad_rec_1_2:
  shows "Cong a b (Gradn a b 1) (Gradn a b 2)"
  by (metis Cong_Gradn_Gradn_Suc Suc_1)

lemma grad_rec_2_3:
  shows "Cong a b (Gradn a b 2) (Gradn a b 3)"
proof (cases "a = b")
  case True
  thus ?thesis 
    using Lem_Gradn_id_n cong_reflexivity by presburger 
next
  case False
  thus ?thesis 
    using Diff__Cong_Gradn_Suc_Gradn_Suc2 numeral_2_eq_2 numeral_3_eq_3 
    by presburger 
qed

lemma grad_rec_a_a:
  shows "(Gradn a a n) = a" 
  by simp

lemma Gradn_uniq_aux_1:
  assumes "A \<noteq> B" 
  shows "Gradn A B n \<noteq> Gradn A B (Suc n)" 
proof -
  have "Gradn A B 0 \<noteq> Gradn A B (Suc 0)"
    by (simp add: assms)   
  moreover
  have "n > 0 \<longrightarrow> (Gradn A B n \<noteq> Gradn A B (Suc n))"
    by (metis Diff__Cong_Gradn_Suc_Gradn_Suc2 assms cong_diff_2 gr0_implies_Suc)  
  ultimately
  show ?thesis
    by blast 
qed

lemma Gradn_uniq_aux_1_aa:
  assumes "A \<noteq> B" 
  shows "Gradn A B (k + n) \<noteq> Gradn A B (k + (Suc n))"
proof (induction k)
  case 0
  show "Gradn A B (0 + n) \<noteq> Gradn A B (0 + (Suc n))"
    using Gradn_uniq_aux_1 assms plus_nat.add_0 by presburger 
next
  case (Suc k)
  show "Gradn A B (Suc k + n) \<noteq> Gradn A B (Suc k + (Suc n))"
    using Gradn_uniq_aux_1 add_Suc_right assms by presburger 
qed

lemma Gradn_uniq_aux_1_bb:
  assumes "A \<noteq> B" 
  shows "Gradn A B (k + n) \<noteq> Gradn A B (k + (Suc (Suc n)))"
proof (induction k)
  case 0
  show "Gradn A B (0 + n) \<noteq> Gradn A B (0 + (Suc(Suc n)))"
    by (metis Gradn_uniq_aux_1 Diff__Bet_Gradn_Gradn_Suc add.left_neutral 
        assms between_equality_2)
next
  case (Suc k)
  show "Gradn A B ((Suc k) + n) \<noteq> Gradn A B ((Suc k) + (Suc(Suc n)))"
    by (metis Gradn_uniq_aux_1_aa Diff_Bet_Gradn_Suc_Gradn_Suc2 add_Suc 
        add_Suc_shift assms between_equality_2) 
qed

lemma Gradn_aux_1_0:
  assumes  "A \<noteq> B" 
  shows "Gradn A B (Suc n) \<noteq> A"
  by (metis Diff__Bet_Gradn_Suc assms bet_neq32__neq)

lemma Gradn_aux_1_1:
  assumes  "A \<noteq> B" and
    "n \<noteq> 0"
  shows "Gradn A B (Suc n) \<noteq> B"
proof -
  obtain m where "n = Suc m"
    using assms(2) not0_implies_Suc by blast
  have "Gradn A B (Suc(Suc m)) \<noteq> B"
  proof (induction m)
    show "Gradn A B (Suc(Suc 0)) \<noteq> B"
      by (metis Gradn_uniq_aux_1 Diff__Bet_Gradn_Suc 
          Diff_Bet_Gradn_Suc_Gradn_Suc2 assms(1) between_equality_2) 
  next
    fix m
    assume "Gradn A B (Suc(Suc m)) \<noteq> B"
    thus "Gradn A B (Suc(Suc(Suc m))) \<noteq> B"
      by (metis Diff__Bet_Gradn_Suc Diff_Bet_Gradn_Suc_Gradn_Suc2 
          assms(1) between_equality_2) 
  qed
  thus ?thesis
    by (simp add: \<open>n = Suc m\<close>) 
qed

lemma Gradn_aux_1_1_bis:
  assumes  "A \<noteq> B" and
    "n \<noteq> 1"
  shows "Gradn A B n \<noteq> B"
proof (cases "n = 0")
  case True
  thus ?thesis
    using Lem_Gradn_0 assms(1) by presburger
next
  case False 
  then obtain m where "n = Suc m"
    using not0_implies_Suc by presburger 
  hence "m \<noteq> 0"
    using assms(2) by force 
  thus ?thesis 
    using Gradn_aux_1_1 assms(1) \<open>n = Suc m\<close> by blast 
qed

lemma Gradn_aux_1_2:
  assumes  "A \<noteq> B" and
    "Gradn A B n = A"
  shows "n = 0" 
proof -
  {
    assume "n \<noteq> 0"
    then obtain m where "n = Suc m" 
      using not0_implies_Suc by presburger
    hence "Gradn A B n \<noteq> A"
      using Gradn_aux_1_0 assms(1) by blast 
    hence "False"
      using Gradn_aux_1_0 assms(1) assms(2) by blast
  }
  thus ?thesis by blast
qed

lemma Gradn_aux_1_3:
  assumes  "A \<noteq> B" and
    "Gradn A B n = B"
  shows "n = 1"
  using Gradn_aux_1_1_bis assms(1) assms(2) by blast

lemma Gradn_uniq_aux_2_a:
  assumes "A \<noteq> B" and
    "n \<noteq> 0"
  shows "Gradn A B 0 \<noteq> Gradn A B n"
  by (metis Gradn_aux_1_2 Lem_Gradn_0 assms(1) assms(2)) 

lemma Gradn_uniq_aux_2:
  assumes "A \<noteq> B" and
    "n < m"
  shows "Gradn A B n \<noteq> Gradn A B m" 
proof -
  obtain k where "m = (Suc k) + n"
    by (metis Suc_diff_Suc add.commute add_diff_cancel_left' 
        assms(2) less_imp_add_positive)
  have "Gradn A B n \<noteq> Gradn A B ((Suc k) + n)"
  proof (induction k)
    case 0
    have "0 + n = n" 
      by simp
    thus "Gradn A B n \<noteq> Gradn A B ((Suc 0) + n)" 
      using Gradn_uniq_aux_1_aa assms(1) by (metis add.commute) 
  next
    case (Suc k)
    hence "Gradn A B n \<noteq> Gradn A B ((Suc k) + n)" 
      by blast
    have "Suc ((Suc k) + n) = Suc(Suc(k)) + n"
      by simp
    {
      assume "Gradn A B n = Gradn A B ((Suc (Suc k)) + n)" 
      have "Gradn A B n = Gradn A B ((Suc k) + n)" 
      proof (cases "n = 0")
        case True
        thus ?thesis
          by (metis Gradn_aux_1_2 Lem_Gradn_0 
              \<open>Gradn A B n = Gradn A B (Suc (Suc k) + n)\<close> add_cancel_left_right 
              assms(1) nat_neq_iff zero_less_Suc) 
      next
        case False
        have "(Suc k) + n = Suc(k + n)" 
          by simp
        hence "Bet A B (Gradn A B ((Suc k)+n))" 
          using assms(1) Diff__Bet_Gradn_Suc by presburger
        hence "Bet A B (Gradn A B n)" 
          using assms(1) Diff__Bet_Gradn_Suc 
            \<open>Gradn A B n = Gradn A B (Suc (Suc k) + n)\<close> add_Suc by presburger 
        have "Bet A (Gradn A B ((Suc k)+n)) (Gradn A B (Suc((Suc k) +n)))"
          using Diff__Bet_Gradn_Gradn_Suc assms(1) by blast
        hence "Bet A (Gradn A B ((Suc k)+n)) (Gradn A B n)" 
          using \<open>Gradn A B n = Gradn A B ((Suc (Suc k)) + n)\<close> 
            \<open>Suc ((Suc k) + n) = Suc(Suc(k)) + n\<close> by simp
        moreover
        have "Bet A (Gradn A B n) (Gradn A B ((Suc k) + n))"
          using Diff_Le__Bet_Gradn_Plus assms(1) by blast 
        ultimately
        show ?thesis
          using between_equality_2 by blast 
      qed
      hence False
        using Suc.IH by blast 
    }
    thus "Gradn A B n \<noteq> Gradn A B ((Suc (Suc k)) + n)" 
      by blast
  qed
  thus ?thesis
    using \<open>m = Suc k + n\<close> by blast 
qed

lemma Gradn_uniq:
  assumes "A \<noteq> B" and
    "Gradn A B n = Gradn A B m"
  shows "n = m" 
proof -
  {
    assume "n \<noteq> m"
    {
      assume "n < m"
      hence "False"
        using Gradn_uniq_aux_2 assms(1) assms(2) by blast 
    }
    moreover
    {
      assume "m < n"
      hence "False"
        by (metis Gradn_uniq_aux_2 assms(1) assms(2))
    }
    ultimately
    have "False"
      using \<open>n \<noteq> m\<close> nat_neq_iff by blast 
  }
  thus ?thesis by blast
qed

lemma Gradn_le_suc_1:
  shows "A (Gradn A B n) Le A (Gradn A B (Suc n))"
  using Bet_Gradn_Gradn_Suc l5_12_a by presburger

lemma Gradn_le_1:
  assumes "m \<le> n"
  shows "A (Gradn A B m) Le A (Gradn A B (Suc n))"
  by (metis Bet_Gradn_Gradn_Suc Lem_Gradn_id_n Diff_Le_Bet__Gradn_Gradn 
      assms bet__le1213 le_Suc_eq)

lemma Gradn_le_suc_2:
  shows "B (Gradn A B (Suc n)) Le B (Gradn A B (Suc(Suc n)))"
  by (metis Bet_Gradn_Gradn_Suc Diff__Bet_Gradn_Suc bet__le1213 
      between_exchange3)

lemma grad_equiv_coq_1:
  shows "Grad A B B"
proof -
  have "(Gradn A B (Suc 0)) = B"
    by auto
  thus ?thesis
    by (metis Grad_def n_not_Suc_n)
qed

lemma grad_aab__ab:
  assumes "Grad A A B" 
  shows "A = B" 
proof -
  obtain n where "B = Gradn A A n"
    using Grad_def assms by blast
  thus ?thesis
    by simp 
qed

lemma grad_stab:
  assumes "Grad A B C" and
    "Bet A C C'" and
    "Cong A B C C'"
  shows "Grad A B C'"
proof (cases "A = B")
  case True
  thus ?thesis
    using assms(1) assms(3) cong_reverse_identity by blast 
next
  case False
  obtain n where "n \<noteq> 0 \<and> C = Gradn A B n"
    using Grad_def assms(1) by presburger
  hence "Bet A B (Gradn A B n)"
    using False Diff__Bet_Gradn by blast
  hence "Bet A B C"
    using \<open>n \<noteq> 0 \<and> C = Gradn A B n\<close> by blast 
  hence "C' = Gradn A B (Suc n)"
    using False Diff_Bet_Bet_Cong_Gradn_Suc \<open>n \<noteq> 0 \<and> C = Gradn A B n\<close> 
      assms(2) assms(3) between_exchange4 by blast
  thus ?thesis  
    using Grad_def by blast
qed

lemma grad__bet:
  assumes "Grad A B C"
  shows "Bet A B C"
proof (cases "A = B")
  case True
  thus ?thesis
    by (simp add: between_trivial2)
next
  case False
  obtain n where "n \<noteq> 0 \<and> C = Gradn A B n"
    using Grad_def assms(1) by presburger
  hence "Bet A B (Gradn A B n)"
    using False Diff__Bet_Gradn by blast
  thus ?thesis
    using \<open>n \<noteq> 0 \<and> C = Gradn A B n\<close> by blast 
qed

lemma grad__col:
  assumes "Grad A B C"
  shows "Col A B C"
  by (simp add: assms bet_col grad__bet) 

lemma grad_neq__neq13:
  assumes "Grad A B C" and
    "A \<noteq> B"
  shows "A \<noteq> C"
  using assms(1) assms(2) between_identity grad__bet by blast

lemma grad_neq__neq12:
  assumes "Grad A B C" and
    "A \<noteq> C"
  shows "A \<noteq> B"
  using Grad_def assms(1) assms(2) grad_rec_a_a by force 

lemma grad112__eq:
  assumes "Grad A A B"
  shows "A = B"
  by (meson assms grad_neq__neq12) 

lemma grad121__eq:
  assumes "Grad A B A"
  shows "A = B"
  using assms grad_neq__neq13 by blast

lemma grad__le: 
  assumes "Grad A B C"
  shows "A B Le A C"
  using assms bet__le1213 grad__bet by blast

lemma grad2_init:
  shows "Grad2 A B B C D D"
proof -
  have "(B = Gradn A B (Suc 0)) \<and> (D = Gradn C D (Suc 0))"
    using One_nat_def Lem_Gradn_1 by presburger 
  thus ?thesis
    using Grad2_def by blast
qed

lemma Grad2_stab:
  assumes "Grad2 A B C D E F" and
    "Bet A C C'" and
    "Cong A B C C'" and
    "Bet D F F'" and
    "Cong D E F F'"
  shows "Grad2 A B C' D E F'"
proof -
  obtain n where "(n \<noteq> 0) \<and> (C = Gradn A B n) \<and> (F = Gradn D E n)"
    using Grad2_def assms(1) by presburger
  have "C' = Gradn A B (Suc n)"
    by (metis Diff_Bet_Bet_Cong_Gradn_Suc Lem_Gradn_id_n Diff__Bet_Gradn
        \<open>n \<noteq> 0 \<and> C = Gradn A B n \<and> F = Gradn D E n\<close> assms(2) assms(3) 
        between_exchange4 cong_reverse_identity)
  moreover
  have "F' = Gradn D E (Suc n)"
    by (metis Diff_Bet_Bet_Cong_Gradn_Suc Lem_Gradn_id_n Diff__Bet_Gradn
        \<open>n \<noteq> 0 \<and> C = Gradn A B n \<and> F = Gradn D E n\<close> assms(4) assms(5) 
        between_exchange4 cong_reverse_identity)
  ultimately
  show ?thesis
    using Grad2_def by blast
qed

lemma bet_cong2_grad__grad2_aux_1:
  assumes "C = (Gradn A B 0)" and
    "Bet D E F" and
    "Cong A B D E" and
    "Cong B C E F"
  shows "F = Gradn D E 2"
proof -
  have "(Gradn A B 0) = A"
    using Lem_Gradn_0 by blast
  hence "A = C" 
    using assms(1) by auto
  hence "Cong D E E F"
    using assms(3) assms(4) cong_transitivity not_cong_4312 by blast
  thus ?thesis
    by (metis Diff_Bet_Bet_Cong_Gradn_Suc Lem_Gradn_1 Suc_1 
        assms(2) cong_diff_3 grad_rec_1_2)
qed

lemma bet_cong2_grad__grad2_aux_2:
  assumes "Bet D E F" and
    "Cong A B D E" and
    "Cong B (Gradn A B (Suc n)) E F"
  shows "F = Gradn D E (Suc n)"
proof -
  have "\<forall> A B D E F. (Bet D E F \<and> Cong A B D E \<and> 
  Cong B (Gradn A B (Suc n)) E F \<longrightarrow> F = Gradn D E (Suc n))"
  proof (induction n)
    case 0
    { 
      fix A B C D E F
      assume 1: "Bet D E F \<and> Cong A B D E \<and> Cong B (Gradn A B (Suc 0)) E F"
      hence "Gradn A B (Suc 0) = B"
        using One_nat_def Lem_Gradn_1 by presburger
      hence "E = F"
        by (metis "1" cong_diff_4)
      hence "F = Gradn D E (Suc 0)"
        by simp 
    }
    thus ?case
      by blast
  next
    case (Suc n)
    {
      assume 2: "\<forall> A B D E F. (Bet D E F \<and> Cong A B D E \<and> 
    Cong B (Gradn A B (Suc n)) E F) \<longrightarrow> F = Gradn D E (Suc n)"
      {
        fix A B D E F
        assume "Bet D E F" and 
          "Cong A B D E" and 
          "Cong B (Gradn A B (Suc (Suc n))) E F"
        have "Cong A B (Gradn A B (Suc n)) (Gradn A B (Suc(Suc n)))"
          using Cong_Gradn_Suc_Gradn_Suc2 by auto
        have "Bet A (Gradn A B (Suc n)) (Gradn A B (Suc(Suc n)))"
          using Bet_Gradn_Gradn_Suc by auto
        have "F = Gradn D E (Suc (Suc n))" 
        proof (cases "A = B")
          case True
          thus ?thesis 
            by (metis \<open>Cong A B D E\<close> \<open>Cong B (Gradn A B (Suc (Suc n))) E F\<close> 
                cong_reverse_identity grad_rec_a_a)
        next
          case False
          have "D \<noteq> E"
            using False \<open>Cong A B D E\<close> cong_diff by blast 
          obtain F' where "Bet D E F'" and "Cong E F' B (Gradn A B (Suc n))"
            using segment_construction by fastforce
          have "Cong B (Gradn A B (Suc n)) E F'"
            using \<open>Cong E F' B (Gradn A B (Suc n))\<close> not_cong_3412 by blast 
          hence "F' = Gradn D E (Suc n)"
            using \<open>Bet D E F'\<close> \<open>Cong A B D E\<close> "2" by blast
          thus ?thesis 
          proof (cases "E = F'")
            case True
            thus ?thesis 
              by (metis Diff_Bet_Bet_Cong_Gradn_Suc
                  \<open>Cong A B (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))\<close> \<open>D \<noteq> E\<close> 
                  \<open>F' = Gradn D E (Suc n)\<close> cong_inner_transitivity 
                  cong_reverse_identity \<open>Bet D E F\<close> \<open>Cong A B D E\<close> 
                  \<open>Cong B (Gradn A B (Suc (Suc n))) E F\<close> 
                  \<open>Cong E F' B (Gradn A B (Suc n))\<close>)
          next
            case False
            have "F = Sym D E (Gradn D E ((Suc(Suc n))-1))" 
            proof -
              have "Bet D E (Gradn D E ((Suc(Suc n))-1))"
                using \<open>Bet D E F'\<close> \<open>F' = Gradn D E (Suc n)\<close> by auto 
              moreover
              have "PreGrad D E (Gradn D E ((Suc(Suc n))-1)) F" 
              proof -
                have "Bet D E (Gradn D E (Suc n))"
                  using Diff__Bet_Gradn_Suc \<open>D \<noteq> E\<close> by blast 
                hence "Bet D E (Gradn D E ((Suc(Suc n))-1))"
                  by fastforce 
                moreover
                have "Bet D (Gradn D E (Suc n)) F" 
                proof -
                  have "Bet B (Gradn A B (Suc n)) (Gradn A B (Suc(Suc n)))"
                    by (metis Diff__Bet_Gradn_Suc 
                        \<open>Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))\<close> 
                        between_exchange3) 
                  moreover
                  have "Cong B (Gradn A B (Suc n)) E (Gradn D E (Suc n))"
                    using \<open>Cong B (Gradn A B (Suc n)) E F'\<close> 
                      \<open>F' = Gradn D E (Suc n)\<close> by blast 
                  moreover
                  have "Cong B (Gradn A B (Suc(Suc n))) E (Gradn D E (Suc(Suc n)))"
                  proof -
                    have "Bet A B (Gradn A B (Suc n))" 
                      using Diff__Bet_Gradn_Suc not_bet_distincts by blast
                    moreover
                    have "Cong D E (Gradn D E (Suc n)) (Gradn D E (Suc (Suc n)))" 
                      using Cong_Gradn_Suc_Gradn_Suc2 by auto
                    moreover
                    have "Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))" 
                      using Bet_Gradn_Gradn_Suc by blast 
                    moreover
                    have "Cong D E (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))"                      
                      using \<open>Cong A B (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))\<close> 
                        \<open>Cong A B D E\<close> cong_inner_transitivity by blast
                    moreover
                    have "Bet D (Gradn D E (Suc n)) (Gradn D E (Suc (Suc n)))" 
                      using Bet_Gradn_Gradn_Suc by blast
                    thus ?thesis
                      using l2_11_b between_exchange3 calculation(2) cong_inner_transitivity 
                      by (meson \<open>Bet B (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))\<close> 
                          \<open>Cong B (Gradn A B (Suc n)) E (Gradn D E (Suc n))\<close> 
                          \<open>Bet D E (Gradn D E (Suc n))\<close>
                          calculation(3) calculation(4))
                  qed
                  moreover
                  have "E Out (Gradn D E (Suc(Suc n))) (Gradn D E (Suc n))"
                    by (metis False Diff__Bet_Gradn_Gradn_Suc 
                        \<open>Bet D E (Gradn D E (Suc n))\<close> 
                        \<open>D \<noteq> E\<close> \<open>F' = Gradn D E (Suc n)\<close> 
                        bet_out between_exchange3 l6_6) 
                  ultimately
                  show ?thesis
                    using Bet_Gradn_Gradn_Suc Diff__Bet_Gradn_Suc \<open>D \<noteq> E\<close> 
                      construction_uniqueness not_cong_3412 
                    by (metis \<open>Bet D E F\<close> \<open>Cong B (Gradn A B (Suc (Suc n))) E F\<close>)
                qed
                hence "Bet D (Gradn D E ((Suc(Suc n))-1)) F"
                  by simp 
                moreover
                have "Cong (Gradn A B (Suc n)) (Gradn A B(Suc(Suc n))) (Gradn D E (Suc n)) F"
                proof -
                  let ?A = "A"
                  let ?B = "Gradn A B (Suc n)"
                  let ?C = "Gradn A B (Suc (Suc n))"
                  let ?A' = "D"
                  let ?B' = "Gradn D E (Suc n)"
                  let ?C' = "F"
                  have "Bet ?A ?B ?C" 
                    using \<open>Bet A (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))\<close> by auto
                  moreover have "Bet ?A' ?B' ?C'" 
                    using \<open>Bet D (Gradn D E (Suc n)) F\<close> by auto
                  moreover have "Cong ?A ?B ?A' ?B'" 
                    by (metis Diff__Bet_Gradn_Suc cong_reverse_identity
                        \<open>Cong A B D E\<close> \<open>Cong E F' B (Gradn A B (Suc n))\<close> 
                        \<open>F' = Gradn D E (Suc n)\<close> l2_11_b not_cong_3412)
                  moreover have "Cong ?A ?C ?A' ?C'" 
                    by (metis Diff__Bet_Gradn_Suc cong_reverse_identity 
                        \<open>Bet D E F\<close> \<open>Cong A B D E\<close> 
                        \<open>Cong B (Gradn A B (Suc (Suc n))) E F\<close> l2_11_b)
                  ultimately show ?thesis 
                    using l4_3_1 by blast
                qed
                hence "Cong A B (Gradn D E (Suc n)) F"
                  using \<open>Cong A B (Gradn A B (Suc n)) (Gradn A B (Suc (Suc n)))\<close> 
                    cong_transitivity by blast 
                hence "Cong D E (Gradn D E (Suc n)) F" 
                  using \<open>Cong A B D E\<close> cong_inner_transitivity by blast
                hence "Cong D E (Gradn D E ((Suc(Suc n))-1)) F" 
                  by simp
                ultimately
                show ?thesis
                  using \<open>D \<noteq> E\<close> PreGrad_def by blast 
              qed
              ultimately
              show ?thesis
                by (metis PreGrad_def LemSym_aux) 
            qed
            hence "F = Gradn D E (Suc (Suc n))"
              by simp 
            thus ?thesis by blast
          qed
        qed
      }
      hence "\<forall> A B D E F. (Bet D E F \<and> Cong A B D E \<and> 
    Cong B (Gradn A B (Suc(Suc n))) E F) \<longrightarrow> F = Gradn D E (Suc(Suc n))" 
        by blast
    }
    thus ?case
      using Suc.IH by fastforce 
  qed
  thus ?thesis
    using assms(1) assms(2) assms(3) by blast 
qed

lemma bet_cong2_grad__grad2_aux:
  assumes "n \<noteq> 0" and
    "C = (Gradn A B n)" and
    "Bet D E F" and
    "Cong A B D E" and
    "Cong B C E F"
  shows "F = Gradn D E n"
proof -
  obtain k where "n = Suc k"
    using assms(1) not0_implies_Suc by blast
  thus ?thesis
    using assms(5) assms(2) assms (3) assms(4) bet_cong2_grad__grad2_aux_2 by blast
qed

lemma bet_cong2_grad__grad2:
  assumes "Grad A B C" and
    "Bet D E F" and
    "Cong A B D E" and
    "Cong B C E F"
  shows "Grad2 A B C D E F" 
proof (cases "A = B")
  case True
  thus ?thesis 
    by (metis assms(1) assms(4) cong_diff_4 grad2_init grad_neq__neq12)
next
  case False
  hence "D \<noteq> E"
    using assms(3) cong_diff by blast
  obtain n where "n \<noteq> 0 \<and> C = (Gradn A B n)"
    using Grad_def assms(1) by presburger 
  have "F = Gradn D E n" 
    using bet_cong2_grad__grad2_aux \<open>n \<noteq> 0 \<and> C = Gradn A B n\<close> 
      assms(2) assms(3) assms(4) by blast 
  thus ?thesis 
    using \<open>n \<noteq> 0 \<and> C = (Gradn A B n)\<close> Grad2_def by blast 
qed

lemma grad2__grad123: 
  assumes "Grad2 A B C D E F"
  shows "Grad A B C" 
proof -
  obtain n where "(n \<noteq> 0) \<and> (C = Gradn A B n) \<and> (F = Gradn D E n)"
    using Grad2_def assms by presburger
  thus ?thesis
    using Grad_def by blast 
qed

lemma grad2__grad456:
  assumes "Grad2 A B C D E F"
  shows "Grad D E F" 
proof -
  obtain n where "(n \<noteq> 0) \<and> (C = Gradn A B n) \<and> (F = Gradn D E n)"
    using Grad2_def assms by presburger
  thus ?thesis
    using Grad_def by blast 
qed

lemma grad_sum_aux_R1: 
  assumes 
    "A C Le A D" and
    "Cong A D A E" and
    "Cong A C A E'" and 
    "A Out E E'"
  shows "Bet A E' E"
  by (meson Out_cases l5_6 assms(2) assms(3) assms(4) assms(1) l6_13_1) 

lemma grad_sum_aux_0: 
  assumes "A \<noteq> B" and
    "D = Gradn A B (Suc(Suc n))" and
    "Cong A D A E" and
    "C = Gradn A B (Suc n)" and
    "Cong A C A E'" and 
    "A Out E E'"
  shows "Bet A E' E" 
proof -
  {
    assume "Bet A E E'"
    have False
      by (metis Gradn_aux_1_0 Gradn_uniq_aux_1 
          Diff__Bet_Gradn_Gradn_Suc \<open>Bet A E E'\<close> 
          assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
          between_cong_2 between_equality_2 cong_preserves_bet 
          cong_transitivity l5_1 l6_6 not_cong_3412)
  }
  thus ?thesis
    using Out_def assms(6) by auto 
qed


lemma grad_sum_aux_1:
  assumes "A \<noteq> B" and
    "D = Gradn A B (Suc(Suc n))" and
    "Bet A C E" and
    "Cong A D C E" and
    "F = Gradn A B (Suc n)" and
    "Bet A C E'" and 
    "Cong A F C E'" and 
    "C \<noteq> A" 
  shows "Bet A E' E" 
proof -
  have "A \<noteq> B \<and> D = Gradn A B (Suc(Suc n)) \<and>
  Bet A C E \<and> Cong A D C E \<and>
  F = Gradn A B (Suc n) \<and>
  Bet A C E' \<and> Cong A F C E' \<and> A \<noteq> C \<longrightarrow>
  Bet A E' E"
  proof (induction n)
    case 0
    {
      fix A B C D E F
      assume "A \<noteq> B" and
        "D = Gradn A B (Suc(Suc 0))" and
        "Bet A C E" and
        "Cong A D C E" and
        "F = Gradn A B (Suc 0)" and
        "Bet A C E'" and
        "Cong A F C E'" and
        "A \<noteq> C"
      have "F = B"
        by (simp add: \<open>F = Gradn A B (Suc 0)\<close>)
      have "Bet C E' E" 
      proof -
        have "C Out E' E" 
        proof -
          {
            assume "C = E'"
            hence "A = F"
              using \<open>Cong A F C E'\<close> cong_identity by blast 
            hence False
              using \<open>A \<noteq> B\<close> \<open>F = B\<close> by fastforce
          }
          hence "C \<noteq> E'"
            by  blast
          moreover
          {
            assume "C = E"
            hence "A = D"
              using \<open>Cong A D C E\<close> cong_identity by blast 
            hence False
              by (metis Gradn_aux_1_0 \<open>A \<noteq> B\<close> \<open>D = Gradn A B (Suc (Suc 0))\<close>) 
          }
          hence "C \<noteq> E" 
            by blast
          moreover
          have "Bet E' C A" 
            using \<open>Bet A C E'\<close> Bet_cases by blast
          moreover
          have "Bet E C A"
            using Bet_cases \<open>Bet A C E\<close> by blast 
          ultimately
          show ?thesis
            using \<open>A \<noteq> C\<close> l6_2 by metis 
        qed
        moreover
        have "A F Le A D" 
          using \<open>F = Gradn A B (Suc 0)\<close> \<open>D = Gradn A B (Suc(Suc 0))\<close> 
            Gradn_le_suc_1 by blast 
        hence "C E' Le C E" 
          using l5_6 \<open>Cong A D C E\<close> \<open>Cong A F C E'\<close> by blast 
        ultimately
        show ?thesis 
          using l6_13_1 by blast
      qed
      hence "Bet A E' E"
        by (meson \<open>Bet A C E\<close> between_exchange2) 
    }
    thus ?case 
      by force
  next
    case (Suc n)
    {
      assume 1: "A \<noteq> B \<and> D = Gradn A B (Suc(Suc n)) \<and>
    Bet A C E \<and> Cong A D C E \<and>
    F = Gradn A B (Suc n) \<and>
    Bet A C E' \<and> Cong A F C E' \<and> A \<noteq> C \<longrightarrow>
    Bet A E' E" 
      {
        assume "A \<noteq> B" and
          "D = Gradn A B (Suc(Suc(Suc n)))" and
          "Bet A C E" and
          "Cong A D C E" and
          "F = Gradn A B (Suc(Suc n))" and
          "Bet A C E'"
          "Cong A F C E'" and
          "A \<noteq> C"
        obtain F' where "F' = Gradn A B (Suc n)"
          by auto
        obtain E'' where "Bet A C E'' \<and> Cong A F' C E''"
          by (meson Cong_cases segment_construction)
        have "Bet A E'' E'"
        proof -
          have "A \<noteq> B"
            by (simp add: assms(1)) 
          moreover
          have "F = Gradn A B (Suc(Suc n))"
            by (simp add: \<open>F = Gradn A B (Suc (Suc n))\<close>) 
          moreover
          have "Bet A C E'"
            by (simp add: assms(6)) 
          moreover
          have "Cong A F C E'"
            by (simp add: assms(7)) 
          moreover
          have "F' = Gradn A B (Suc n)"
            by (simp add: \<open>F' = Gradn A B (Suc n)\<close>) 
          moreover
          have "Bet A C E''"
            by (simp add: \<open>Bet A C E'' \<and> Cong A F' C E''\<close>) 
          moreover
          have "Cong A F' C E''"
            by (simp add: \<open>Bet A C E'' \<and> Cong A F' C E''\<close>)
          moreover
          have "A \<noteq> C"
            using assms(8) by auto
          ultimately
          show ?thesis 
          proof -
            {
              assume "Bet C E'' E'"
              hence ?thesis 
                using assms(6) between_exchange2 by blast
            }
            moreover
            {
              assume "Bet C E' E''"
              hence ?thesis
                by (metis Diff__Bet_Gradn_Gradn_Suc Gradn_aux_1_0 
                    bet2__out cong_identity_inv cong_preserves_bet 
                    \<open>Bet A C E'' \<and> Cong A F' C E''\<close> \<open>F = Gradn A B (Suc (Suc n))\<close> 
                    \<open>F' = Gradn A B (Suc n)\<close> assms(1) assms(7) 
                    calculation not_bet_distincts)
            }
            ultimately show ?thesis 
              by (metis \<open>Bet A C E''\<close> assms(6) assms(8) l5_2)
          qed
        qed
        have "C E'' Le C E'"
          using \<open>Bet A C E'' \<and> Cong A F' C E''\<close> \<open>Bet A E'' E'\<close> 
            bet__le1213 between_exchange3 by blast 
        have "A (Gradn A B (Suc (Suc n))) Le A (Gradn A B (Suc (Suc (Suc n))))"
          using Gradn_Le_Gradn_Suc by blast 
        hence "A F Le A D"
          using \<open>F = Gradn A B (Suc (Suc n))\<close> 
            \<open>D = Gradn A B (Suc(Suc(Suc n)))\<close> by blast
        hence "C E' Le C E"
          using assms(4) assms(7) l5_6 by blast 
        have "Bet A E' E"
        proof -
          {
            assume "Bet A E E'"
            hence "A E Le A E'"
              using bet__le1213 by auto
            hence "C E Le C E'"
              using \<open>Bet A E E'\<close> assms(3) bet__le1213 between_exchange3 by blast
            hence "Cong C E C E'"
              by (simp add: \<open>C E' Le C E\<close> le_anti_symmetry)
            hence "Cong A D A F"
              by (meson assms(4) assms(7) cong_transitivity not_cong_3412) 
            hence False
              by (metis Gradn_uniq_aux_1 Diff__Bet_Gradn_Gradn_Suc 
                  \<open>D = Gradn A B (Suc (Suc (Suc n)))\<close> 
                  \<open>F = Gradn A B (Suc (Suc n))\<close> 
                  assms(1) between_cong not_cong_3412) 
          }
          thus ?thesis
            by (metis assms(3) assms(6) assms(8) l5_1) 
        qed
      }
    }
    thus ?case    
      using Suc.IH by fastforce 
  qed
  thus ?thesis
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
      assms(7) assms(8) by blast 
qed

lemma grad_sum_aux_1A:
  assumes "A \<noteq> B" and
    "C = Gradn A B (Suc (Suc 0))"
  shows "B Midpoint A C" 
proof -
  have "C =  (Sym A B (Gradn A B (Suc 0)))"
    by (simp add: assms(2))
  have "... = (Sym A B B)"
    by (simp add: assms(1)) 
  hence "(SOME x::'p. PreGrad A B B x) = C"
    using assms(1) by (metis Gradn_aux_1_0 Sym.simps 
        \<open>C = Sym A B (Gradn A B (Suc 0))\<close> assms(2)) 
  hence "PreGrad A B B C"
    by (metis PreGrad_def Sym_Bet__Bet_Bet Sym_Bet__Cong 
        Sym.elims assms(1) not_bet_distincts)
  thus ?thesis
    by (simp add: Midpoint_def PreGrad_def)
qed

lemma grad_sum_aux_2:
  assumes "A \<noteq> B" and
    "D = Gradn A B (Suc(Suc n))" and
    "Bet A C E" and
    "Cong A D C E" and
    "F = Gradn A B (Suc n)" and
    "Bet A C E'" and 
    "Cong A F C E'" and 
    "C \<noteq> A"
  shows "Cong A B E' E" 
proof -
  have "A \<noteq> B \<and> D = Gradn A B (Suc(Suc n)) \<and> Bet A C E \<and> Cong A D C E \<and>
  F = Gradn A B (Suc n) \<and> Bet A C E' \<and> Cong A F C E' \<and> A \<noteq> C \<longrightarrow>
  Cong  A B E' E"
  proof (induction n)
    case 0
    {
      fix A B C D E F
      assume "A \<noteq> B" and
        "D = Gradn A B (Suc(Suc 0))" and
        "Bet A C E" and
        "Cong A D C E" and
        "F = Gradn A B (Suc 0)" and
        "Bet A C E'" and
        "Cong A F C E'" and
        "A \<noteq> C"
      have "B Midpoint A D" 
        using grad_sum_aux_1A \<open>A \<noteq> B\<close> \<open>D = Gradn A B (Suc (Suc 0))\<close> by blast 
      hence "Bet A B D \<and> Cong A B B D"
        using Midpoint_def by blast
      have "B = F"
        using One_nat_def Lem_Gradn_1 \<open>F = Gradn A B (Suc 0)\<close> by presburger 
      hence "Cong A B C E'"
        by (simp add: \<open>Cong A F C E'\<close>) 
      have "Cong B D C E'"
        using \<open>B = F\<close> \<open>Bet A B D \<and> Cong A B B D\<close> \<open>Cong A B C E'\<close> 
          cong_inner_transitivity by blast 
      have "Cong B D E' E" 
        using cong_commutativity cong_diff_2 Tarski_neutral_dimensionless_axioms 
          \<open>A \<noteq> B\<close> \<open>A \<noteq> C\<close> \<open>B = F\<close> \<open>Bet A B D \<and> Cong A B B D\<close> \<open>Bet A C E'\<close> 
          \<open>Bet A C E\<close> \<open>Cong A D C E\<close> \<open>Cong A F C E'\<close> bet_out between_symmetry 
          l6_2 out_cong_cong by metis
      hence "Cong C E' E' E"
        using \<open>Cong B D C E'\<close> cong_inner_transitivity by blast 
      hence "Cong A B E' E"
        using \<open>B = F\<close> \<open>Cong A F C E'\<close> cong_transitivity by blast 
    }
    thus ?case
      by blast 
  next
    case (Suc n)
    have "Cong A B E' E" 
    proof -
      have "Bet A F D" 
        using Diff__Bet_Gradn_Gradn_Suc assms(1) assms(2) assms(5) by blast
      have "Cong A B F D" 
        using  Diff__Cong_Gradn_Suc_Gradn_Suc2 assms(1) assms(2) 
          assms(5) by blast
      have "Bet A E' E" 
        using grad_sum_aux_1 assms(1) assms(2) assms(3) assms(4) 
          assms(5) assms(6) assms(7) assms(8) by blast
      {
        assume "Bet C E E'"
        hence "Cong A B E' E" 
          by (metis \<open>Bet A E' E\<close> \<open>Bet A F D\<close> \<open>Cong A B F D\<close> 
              assms(1) assms(4) assms(6) assms(7) between_cong between_equality_2 
              between_exchange3 cong_diff cong_transitivity not_cong_3412) 
      }
      moreover
      {
        assume "Bet C E' E"
        hence "Cong A B E' E"  
          using \<open>Bet A F D\<close> \<open>Cong A B F D\<close> assms(4) assms(7) 
            cong_transitivity l4_3_1 by blast
      }
      ultimately show ?thesis 
        by (metis assms(3) assms(6) assms(8) l5_2)
    qed
    thus ?case 
      by blast
  qed
  thus ?thesis 
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) by blast
qed

lemma grad_sum_aux:
  assumes "A \<noteq> B" and
    "C = Gradn A B (Suc n)" and
    "D = Gradn A B (Suc m)" and
    "Bet A C E" and
    "Cong A D C E"
  shows "E = Gradn A B ((Suc n) + (Suc m))" 
proof -
  have "\<forall> A B C D E. (A \<noteq> B \<and> C = Gradn A B (Suc n) \<and> 
  D = Gradn A B (Suc m) \<and> Bet A C E \<and> Cong A D C E) \<longrightarrow>
  E = Gradn A B ((Suc n) + (Suc m))"
  proof (induction m)
    case 0
    {
      fix A B C D E
      assume "A \<noteq> B" and
        "C = Gradn A B (Suc n)" and
        "D = Gradn A B (Suc 0)" and  
        "Bet A C E" and
        "Cong A D C E"
      have "E = Gradn A B ((Suc n) + (Suc 0))"
        by (metis Nat.add_0_right Diff_Bet_Bet_Cong_Gradn_Suc 
            Lem_Gradn_0 Diff__Bet_Gradn_Suc Cong_Gradn_Gradn_Suc 
            cong_transitivity \<open>A \<noteq> B\<close> \<open>Bet A C E\<close> \<open>C = Gradn A B (Suc n)\<close> 
            \<open>Cong A D C E\<close> \<open>D = Gradn A B (Suc 0)\<close> add_Suc_shift between_exchange4)
    }
    thus ?case
      by force 
  next
    case (Suc m)
    {
      assume 1: "\<forall> A B C D E. (A \<noteq> B \<and> C = Gradn A B (Suc n) \<and> 
    D = Gradn A B (Suc m) \<and> Bet A C E \<and> Cong A D C E) \<longrightarrow>
    E = Gradn A B ((Suc n) + (Suc m))"
      {
        fix A B C D E
        assume "A \<noteq> B" and
          "C = Gradn A B (Suc n)" and
          "D = Gradn A B (Suc(Suc m))" and
          "Bet A C E" and
          "Cong A D C E"
        obtain F where 2: "F = Gradn A B (Suc m)"
          by simp
        obtain E' where 3: "Bet A C E' \<and> Cong A F C E'"
          by (meson cong_4312 segment_construction)
        hence 4: "E' = Gradn A B ((Suc n) + (Suc m))"
          using 1 2 \<open>A \<noteq> B\<close> \<open>C = Gradn A B (Suc n)\<close> by blast
        have 5: "Bet A B E" 
        proof -
          have "Grad A B C" 
            using Grad_def \<open>C = Gradn A B (Suc n)\<close> by blast 
          hence "Bet A B C"
            using grad__bet by blast 
          thus ?thesis
            using \<open>Bet A C E\<close> between_exchange4 by blast 
        qed
        have 6: "Bet A E' E" 
          using grad_sum_aux_1 \<open>A \<noteq> B\<close> \<open>D = Gradn A B (Suc(Suc m))\<close> 
            \<open>Bet A C E\<close> \<open>Cong A D C E\<close> 2 3 Gradn_aux_1_0 
            \<open>C = Gradn A B (Suc n)\<close> by blast 
        have "Cong A B E' E"
          using grad_sum_aux_2 "2" "3" Gradn_aux_1_0 \<open>A \<noteq> B\<close> 
            \<open>Bet A C E\<close> \<open>C = Gradn A B (Suc n)\<close> \<open>Cong A D C E\<close> 
            \<open>D = Gradn A B (Suc (Suc m))\<close> by blast
        hence "E = Gradn A B (Suc(Suc n) + (Suc m))" 
          using Diff_Bet_Bet_Cong_Gradn_Suc 3 4 5 6
          by (metis \<open>A \<noteq> B\<close> add_Suc_right add_Suc_shift) 
        hence "E = Gradn A B ((Suc n) + (Suc(Suc m)))"
          by simp 
      }
      hence "\<forall> A B C D E. (A \<noteq> B \<and> C = Gradn A B (Suc n) \<and> 
    D = Gradn A B (Suc(Suc m)) \<and> Bet A C E \<and> Cong A D C E) \<longrightarrow>
    E = Gradn A B ((Suc n) + (Suc(Suc m)))" by blast
    }
    thus ?case
      using Suc.IH by fastforce 
  qed
  thus ?thesis
    using assms(1) assms(2) assms(3) assms(4) assms(5) by blast 
qed

lemma grad_sum:
  assumes "Grad A B C" and
    "Grad A B D" and
    "Bet A C E" and
    "Cong A D C E"
  shows "Grad A B E"
proof (cases "A = B")
  case True
  thus ?thesis
    using assms(1) assms(2) assms(3) assms(4) grad112__eq grad_stab by blast 
next
  case False
  obtain n where 1: "(n \<noteq> 0) \<and> (C = Gradn A B n)"
    using Grad_def assms(1) by presburger 
  obtain m where 2: "(m \<noteq> 0) \<and> (D = Gradn A B m)"
    using Grad_def assms(2) by presburger 
  obtain k l where "n = Suc k \<and> m = Suc l" 
    using 1 2 not0_implies_Suc by presburger 
  hence "E = Gradn A B (n + m)" 
    using False 1 2 grad_sum_aux assms(3) assms(4) by blast 
  thus ?thesis
    by (meson Grad_def \<open>n \<noteq> 0 \<and> C = Gradn A B n\<close> add_is_0) 
qed

lemma SymR_ex:
  assumes "B Midpoint A C"
  shows "C = SymR A B"
proof -
  have "\<exists> x. B Midpoint A x" 
    using assms(1) by blast
  thus ?thesis
    using assms(1) someI_ex
    by (metis SymR_uniq_aux SymR.elims) 
qed

lemma SymR__midp:
  assumes "C = SymR A B"
  shows "B Midpoint A C"
  using SymR_ex assms symmetric_point_construction by blast

lemma SymR_uniq:
  assumes "C = SymR A B" and
    "D = SymR A B" 
  shows "C = D"
  by (simp add: assms(1) assms(2))

lemma GradExpn_1:
  shows "GradExpn A A n = A" 
  by simp

lemma GradExpn_2:
  shows "Bet A B (GradExpn A B (Suc n))"
proof (cases "A = B")
  case True
  thus ?thesis
    using between_trivial2 by blast
next
  case False
  show "Bet A B (GradExpn A B (Suc n))" 
  proof(induction n)
    case 0
    have "(GradExpn A B 1) = B" 
      using False by simp
    thus "Bet A B (GradExpn A B (Suc 0))"
      by (metis One_nat_def not_bet_distincts) 
  next
    case (Suc n)
    {
      assume "Bet A B (GradExpn A B (Suc n))"
      have "(Suc (Suc n)) \<noteq> 0 \<and> (Suc (Suc n)) \<noteq> 1" 
        by presburger
      hence "GradExpn A B (Suc(Suc n)) = SymR A (GradExpn A B (Suc n))" 
        using False by simp             
      obtain C where "(GradExpn A B (Suc n)) Midpoint A C"
        using symmetric_point_construction by blast
      hence "Bet A (GradExpn A B (Suc n)) C" 
        using Midpoint_def by blast
      have "C = GradExpn A B (Suc(Suc n))"
        using SymR_ex 
          \<open>GradExpn A B (Suc (Suc n)) = SymR A (GradExpn A B (Suc n))\<close> 
          \<open>GradExpn A B (Suc n) Midpoint A C\<close> by presburger 
      hence "Bet A B (GradExpn A B (Suc(Suc n)))"
        using \<open>Bet A (GradExpn A B (Suc n)) C\<close> 
          \<open>Bet A B (GradExpn A B (Suc n))\<close> between_exchange4 by blast
    }
    thus ?case 
      using Suc.IH by blast 
  qed
qed

lemma GradExpn_3:
  shows "Bet A (GradExpn A B (Suc n)) (GradExpn A B (Suc(Suc n)))"
proof (cases "A = B")
  case True
  thus ?thesis
    using between_trivial2 by force
next
  case False
  show "Bet A (GradExpn A B (Suc n)) (GradExpn A B (Suc(Suc n)))" 
  proof(induction n)
    case 0
    have "(GradExpn A B 1) = B" 
      using False by simp
    thus "Bet A (GradExpn A B (Suc 0)) (GradExpn A B (Suc(Suc 0)))"
      using GradExpn_2 One_nat_def by presburger
  next
    case (Suc n)
    {
      assume "Bet A (GradExpn A B (Suc n)) (GradExpn A B (Suc(Suc n)))"
      have "(Suc(Suc (Suc n))) \<noteq> 0 \<and> (Suc(Suc (Suc n))) \<noteq> 1" 
        by presburger
      hence "GradExpn A B (Suc(Suc(Suc n))) = SymR A (GradExpn A B (Suc(Suc n)))" 
        using False by simp             
      obtain C where "(GradExpn A B (Suc(Suc n))) Midpoint A C"
        using symmetric_point_construction by blast
      hence "Bet A (GradExpn A B (Suc(Suc n))) C" 
        using Midpoint_def by blast
      have "C = GradExpn A B (Suc(Suc(Suc n)))"
        using SymR_ex 
          \<open>GradExpn A B (Suc(Suc (Suc n))) = SymR A (GradExpn A B (Suc(Suc n)))\<close> 
          \<open>GradExpn A B (Suc(Suc n)) Midpoint A C\<close> by presburger 
      hence "Bet A (GradExpn A B (Suc (Suc(n)))) (GradExpn A B (Suc(Suc(Suc n))))"
        using \<open>Bet A (GradExpn A B (Suc (Suc n))) C\<close> by blast 
    }
    thus ?case 
      using Suc.IH by blast 
  qed
qed

lemma GradExpn_4:
  shows "Cong A (GradExpn A B (Suc n)) (GradExpn A B (Suc n)) (GradExpn A B (Suc(Suc n)))"
proof (cases "A = B")
  case True
  thus ?thesis
    using GradExpn_1 cong_trivial_identity by presburger
next
  case False
  show "Cong A (GradExpn A B (Suc n)) (GradExpn A B (Suc n)) (GradExpn A B (Suc(Suc n)))"
  proof (induction n)
    case 0
    have "GradExpn A B (Suc 0) = B"
      using False by simp
    show "Cong A (GradExpn A B (Suc 0)) (GradExpn A B (Suc 0)) (GradExpn A B (Suc(Suc 0)))" 
    proof -
      have "(Suc(Suc 0)) \<noteq> 0 \<and> (Suc(Suc 0)) \<noteq> 1" 
        by presburger
      hence "GradExpn A B (Suc(Suc 0)) = SymR A (GradExpn A B (Suc 0))" 
        using False by simp             
      obtain C where "(GradExpn A B (Suc 0)) Midpoint A C"
        using symmetric_point_construction by blast
      hence "Cong A (GradExpn A B (Suc 0)) (GradExpn A B (Suc 0)) C" 
        using Midpoint_def by blast
      have "C = GradExpn A B (Suc(Suc 0))"
        using SymR_ex \<open>GradExpn A B (Suc (Suc 0)) = SymR A (GradExpn A B (Suc 0))\<close> 
          \<open>GradExpn A B (Suc 0) Midpoint A C\<close> by presburger 
      thus ?thesis
        using \<open>Cong A (GradExpn A B (Suc 0)) (GradExpn A B (Suc 0)) C\<close> by blast 
    qed
  next
    case (Suc n)
    {
      assume "Cong A (GradExpn A B (Suc n)) (GradExpn A B (Suc n)) (GradExpn A B (Suc(Suc n)))"
      have "(Suc(Suc(Suc n))) \<noteq> 0 \<and> (Suc(Suc(Suc n))) \<noteq> 1" 
        by presburger
      hence "GradExpn A B (Suc(Suc(Suc n))) = SymR A (GradExpn A B (Suc(Suc n)))" 
        using False by simp             
      obtain C where "(GradExpn A B (Suc(Suc n))) Midpoint A C"
        using symmetric_point_construction by blast
      hence "Cong A (GradExpn A B (Suc(Suc n))) (GradExpn A B (Suc(Suc n))) C" 
        using Midpoint_def by blast
      have "C = GradExpn A B (Suc(Suc(Suc n)))"
        using SymR_ex 
          \<open>GradExpn A B (Suc(Suc (Suc n))) = SymR A (GradExpn A B (Suc(Suc n)))\<close> 
          \<open>GradExpn A B (Suc(Suc n)) Midpoint A C\<close> by presburger 
      hence "Cong A (GradExpn A B (Suc(Suc n)))
    (GradExpn A B (Suc(Suc n))) (GradExpn A B (Suc(Suc(Suc n))))"
        using \<open>Cong A (GradExpn A B (Suc (Suc n))) (GradExpn A B (Suc (Suc n))) C\<close> 
        by fastforce 
    }
    thus ?case
      using Suc.IH by blast
  qed
qed

lemma gradexp_init:
  shows "GradExp A B B"
proof -
  have "B = GradExpn A B (Suc 0)"
    by auto
  thus ?thesis
    using GradExp_def by blast
qed

lemma gradexp_stab_aux_0:
  assumes "C = GradExpn A B 0" and
    "Bet A C C'" and
    "Cong A C C C'"
  shows "C' = GradExpn A B 0" 
proof -
  obtain m where "m = Suc 0"
    by simp 
  show ?thesis
  proof (cases "A = B")
    case True
    thus ?thesis
      by (metis GradExpn_1 assms(1) assms(3) cong_reverse_identity)
  next
    case False
    hence "A \<noteq> B" 
      by auto
    show ?thesis
    proof -
      have "C = A" 
        using assms(1) by simp
      hence "C = C'"
        using assms(3) cong_reverse_identity by blast 
      thus ?thesis
        using assms(1) by fastforce 
    qed
  qed
qed

lemma gradexp_stab_aux_n:
  assumes "C = GradExpn A B (Suc n)" and
    "Bet A C C'" and
    "Cong A C C C'"
  shows "C' = GradExpn A B (Suc(Suc n))" 
proof -
  obtain m where "m = Suc(Suc n)"
    by simp 
  hence "m - 1 = Suc n" 
    by simp
  show ?thesis
  proof (cases "A = B")
    case True
    thus ?thesis
      by (metis GradExpn_1 assms(1) assms(3) cong_reverse_identity)
  next
    case False
    hence "A \<noteq> B" 
      by auto
    show ?thesis
    proof -
      have "C Midpoint A C'"
        using assms(2) assms(3) midpoint_def by auto 
      hence "C' = SymR A C"
        using SymR_ex by blast
      hence "C' = SymR A (GradExpn A B (m - 1))"
        using \<open>m - 1 = Suc n\<close> assms(1) by presburger 
      hence "C' = GradExpn A B m"
        by (simp add: False \<open>m = Suc (Suc n)\<close>) 
      thus ?thesis
        using \<open>m = Suc (Suc n)\<close> by blast
    qed
  qed
qed

lemma gradexp_stab:
  assumes "GradExp A B C" and
    "Bet A C C'" and
    "Cong A C C C'"
  shows "GradExp A B C'" 
proof -
  obtain n where "C = GradExpn A B n"
    using GradExp_def assms(1) by blast 
  show ?thesis 
  proof (cases "n = 0")
    case True
    thus ?thesis
      using \<open>C = GradExpn A B n\<close> assms(1) assms(2) assms(3) 
        gradexp_stab_aux_0 by blast 
  next
    case False
    then obtain m where "Suc m = n"
      using not0_implies_Suc by auto
    hence "C = GradExpn A B (Suc m)"
      by (simp add: \<open>C = GradExpn A B n\<close>)
    hence "C' = GradExpn A B (Suc(Suc m))"
      using assms(2) assms(3) gradexp_stab_aux_n by blast 
    moreover
    have "(Suc (Suc m)) \<noteq> 0"
      by simp 
    ultimately
    show ?thesis
      using GradExp_def by blast 
  qed
qed

lemma gradexp__grad_aux_1: 
  shows "\<forall> C. (C = (GradExpn A A (Suc n)) \<longrightarrow> Grad A A C)"
  by (simp add: grad_equiv_coq_1)

lemma gradexp__grad_aux: 
  assumes "A \<noteq> B"
  shows "\<forall> C. (C = (GradExpn A B (Suc n)) \<longrightarrow> Grad A B C)" 
proof (induction n)
  case 0
  {
    fix C
    assume "C = (GradExpn A B (Suc 0))"
    hence "C = B"
      by force 
    hence "Grad A B C"
      using grad_equiv_coq_1 by auto 
  }
  hence "(\<forall> C. (C = (GradExpn A B (Suc 0))) \<longrightarrow> Grad A B C)" 
    by blast
  thus ?case
    by blast 
next
  case (Suc n)
  {
    assume 1: "\<forall> C. (C = (GradExpn A B (Suc n)) \<longrightarrow> Grad A B C)"
    {
      fix C'
      assume "C' = (GradExpn A B ((Suc n) + 1))"
      have "A \<noteq> B \<and> ((Suc n) + 1) \<noteq> 0 \<and> ((Suc n)+1) \<noteq> 1"
        using assms by auto 
      then
      have "C' = (SymR A (GradExpn A B (Suc n)))"
        by (simp add: \<open>C' = GradExpn A B ((Suc n)+1)\<close>) 
      hence "Grad A B (GradExpn A B (Suc n))"
        using "1" by blast 
      have "Grad A B C'" 
      proof -
        have "Grad A B (GradExpn A B (Suc n))"
          using \<open>Grad A B (GradExpn A B (Suc n))\<close> by blast 
        moreover
        have "Bet A (GradExpn A B (Suc n)) (GradExpn A B (Suc(Suc n)))" 
          using GradExpn_3 by blast 
        moreover
        have "Cong A (GradExpn A B (Suc n)) (GradExpn A B (Suc n)) C'"
          using GradExpn_4 \<open>C' = GradExpn A B (Suc n + 1)\<close> by force 
        ultimately
        show ?thesis
          using grad_sum by (metis Suc_eq_plus1 \<open>C' = GradExpn A B (Suc n + 1)\<close>) 
      qed
    }
    hence "\<forall> C. (C = (GradExpn A B ((Suc n) + 1)) \<longrightarrow> Grad A B C)"
      by blast
  }
  thus ?case
    using Suc.IH Suc_eq_plus1 by metis 
qed

lemma gradexp__grad: 
  assumes "GradExp A B C"
  shows "Grad A B C" 
proof -
  obtain n where "n \<noteq> 0 \<and> C = GradExpn A B n"
    using GradExp_def assms by blast
  hence "n \<noteq> 0" 
    by blast
  then obtain m where "n = Suc m"
    using not0_implies_Suc by presburger 
  thus ?thesis
    by (simp add: \<open>n \<noteq> 0 \<and> C = GradExpn A B n\<close> gradexp__grad_aux 
        gradexp__grad_aux_1)
qed

lemma gradexp_le__reach:
  assumes "GradExp A B B'" and
    "C D Le A B'"
  shows "Reach A B C D"
  using Reach_def assms(1) assms(2) gradexp__grad by blast 

lemma grad__ex_gradexp_le_aux_0:
  assumes "A = B"
  shows "\<exists> D. GradExp A B D \<and> A (Gradn A B n) Le A D" 
proof (induction n)
  case 0
  have "Gradn A B 0 = A"
    by auto
  moreover
  have "GradExp A B B"
    by (simp add: gradexp_init)
  moreover
  have "A A Le A B"
    by (simp add: le_trivial) 
  ultimately
  show "\<exists> D. GradExp A B D \<and> A (Gradn A B 0) Le A D"
    by auto 
next
  case (Suc n)
  {
    assume "\<exists> D. GradExp A B D \<and> A (Gradn A B n) Le A D" 
    then obtain D where "GradExp A B D \<and> A (Gradn A B n) Le A D" 
      by blast
    let ?n = "Gradn A B n"
    let ?sucn = "Gradn A B (Suc n)"
    have "?n = ?sucn"
      using assms by force 
    hence "\<exists> D. GradExp A B D \<and> A (Gradn A B (Suc n)) Le A D"
      using \<open>\<exists>D. GradExp A B D \<and> A (Gradn A B n) Le A D\<close> by presburger 
  }
  thus ?case   
    using Suc.IH by blast 
qed

lemma grad__ex_gradexp_le_aux_1:
  assumes "A \<noteq> B"
  shows "\<exists> D. GradExp A B D \<and> A (Gradn A B n) Le A D" 
proof (induction n)
  case 0
  have "Gradn A B 0 = A"
    by auto
  moreover
  have "GradExp A B B"
    by (simp add: gradexp_init)
  moreover
  have "A A Le A B"
    by (simp add: le_trivial) 
  ultimately
  show "\<exists> D. GradExp A B D \<and> A (Gradn A B 0) Le A D"
    by auto 
next
  case (Suc n)
  {
    assume "\<exists> D. GradExp A B D \<and> A (Gradn A B n) Le A D" 
    then obtain D where "GradExp A B D \<and> A (Gradn A B n) Le A D" 
      by blast
    obtain D' where "Bet A D D' \<and> Cong D D' A D"
      using segment_construction by blast
    have "(Gradn A B n) (Gradn A B (Suc n)) Le D D'"
      by (meson Cong_Gradn_Gradn_Suc \<open>Bet A D D' \<and> Cong D D' A D\<close> 
          \<open>GradExp A B D \<and> A (Gradn A B n) Le A D\<close> grad__le gradexp__grad 
          l5_6 le_right_comm not_cong_4312) 
    hence "GradExp A B D' \<and> A (Gradn A B (Suc n)) Le A D'"
      by (meson Diff__Bet_Gradn_Gradn_Suc \<open>Bet A D D' \<and> Cong D D' A D\<close>
          \<open>GradExp A B D \<and> A (Gradn A B n) Le A D\<close> assms bet2_le2__le1346 
          gradexp_stab not_cong_3412) 
    hence "\<exists> D. GradExp A B D \<and> A (Gradn A B (Suc n)) Le A D" 
      by blast
  }
  thus ?case   
    using Suc.IH by blast 
qed

lemma grad__ex_gradexp_le_aux:
  shows "\<exists> D. GradExp A B D \<and> A (Gradn A B n) Le A D" 
  using grad__ex_gradexp_le_aux_0 grad__ex_gradexp_le_aux_1 by blast

lemma grad__ex_gradexp_le:
  assumes "Grad A B C"
  shows "\<exists> D. GradExp A B D \<and> A C Le A D" 
  using grad__ex_gradexp_le_aux Grad_def assms by auto 

lemma reach__ex_gradexp_le: 
  assumes "Reach A B C D"
  shows "\<exists> B'. GradExp A B B' \<and> C D Le A B'"
  by (meson Reach_def le_transitivity assms grad__ex_gradexp_le)

lemma gradexp2_init:
  shows "GradExp2 A B B C D D" 
proof -
  have "B = GradExpn A B (Suc 0)"
    by auto
  moreover
  have "D = GradExpn C D (Suc 0)"
    by auto
  ultimately
  show ?thesis
    using GradExp2_def by blast
qed

lemma GradExp2_stab:
  assumes "GradExp2 A B C D E F" and
    "Bet A C C'" and
    "Cong A C C C'" and
    "Bet D F F'" and
    "Cong D F F F'"
  shows "GradExp2 A B C' D E F'"
proof -
  obtain n where "(n \<noteq> 0) \<and> (C = GradExpn A B n) \<and> (F = GradExpn D E n)"
    using GradExp2_def assms(1) by presburger
  hence "n \<noteq> 0" 
    by blast
  then obtain m where "Suc m = n"
    using not0_implies_Suc by auto
  hence "C = GradExpn A B (Suc m)"
    using \<open>n \<noteq> 0 \<and> C = GradExpn A B n \<and> F = GradExpn D E n\<close> by blast 
  hence "C' = GradExpn A B (Suc (Suc m))"
    using assms(2) assms(3) gradexp_stab_aux_n by blast 
  moreover
  have "F = GradExpn D E (Suc m)"
    using \<open>Suc m = n\<close> \<open>n \<noteq> 0 \<and> C = GradExpn A B n \<and> F = GradExpn D E n\<close> by blast
  hence "F' = GradExpn D E (Suc (Suc m))"
    using assms(4) assms(5) gradexp_stab_aux_n by blast 
  moreover
  have "Suc (Suc m) \<noteq> 0" 
    by simp
  ultimately
  show ?thesis
    using GradExp2_def by blast 
qed

lemma gradexp2__gradexp123:
  assumes "GradExp2 A B C D E F"
  shows "GradExp A B C"
proof -
  obtain n where "n \<noteq> 0 \<and> (C = GradExpn A B n) \<and> (F = GradExpn D E n)"
    using assms(1) GradExp2_def by blast
  thus ?thesis using GradExp_def by blast
qed

lemma gradexp2__gradexp456:
  assumes "GradExp2 A B C D E F"
  shows "GradExp D E F"
proof -
  obtain n where "n \<noteq> 0 \<and> (C = GradExpn A B n) \<and> (F = GradExpn D E n)"
    using assms(1) GradExp2_def by blast
  thus ?thesis using GradExp_def by blast
qed

lemma MidR_uniq:
  assumes "C = MidR A B" and
    "D = MidR A B" 
  shows "C = D"
  by (simp add: assms(1) assms(2))

lemma MidR_ex_0:
  shows "(MidR A B) Midpoint A B" 
proof -
  have "MidR A B = (SOME x. x Midpoint A B)" 
    by simp
  thus ?thesis 
    using someI_ex by (metis midpoint_existence) 
qed

lemma MidR_ex_1:
  assumes "C = (MidR A B)" 
  shows "C Midpoint A B" 
  using assms MidR_ex_0 by blast

lemma MidR_ex_aux:
  assumes "C Midpoint A B"
  shows "C = (SOME x. x Midpoint A B)" 
  by (metis assms MidR_uniq_aux someI)   

lemma MidR_ex:
  assumes "C Midpoint A B"
  shows "C = (MidR A B)"
  using MidR_ex_0 MidR_uniq_aux assms by blast 

lemma gradexpinv_init_aux:
  shows "B = GradExpInvn A B 0"
  by simp

lemma gradexpinv_init:
  shows "GradExpInv A B B"
  using gradexpinv_init_aux using GradExpInv_def by blast 

lemma gradexpinv_stab_aux_0:
  assumes "B = GradExpInvn A C 0" and
    "Bet A B' B" and
    "Cong A B' B' B"
  shows "B' = GradExpInvn A C (Suc 0)" 
proof -
  have "B = C" 
    using assms(1) by simp
  have "B' Midpoint A B"
    by (simp add: assms(2) assms(3) midpoint_def) 
  hence "B' = MidR A B"
    using MidR_ex by blast
  show ?thesis
  proof (cases "A = C")
    case True
    hence "B' = B"
      using \<open>B = C\<close> assms(2) bet_neq12__neq by blast 
    moreover
    have "A = GradExpInvn A C (Suc 0)" 
      using True by simp
    ultimately
    show ?thesis
      using True \<open>B = C\<close> by force
  next
    case False
    hence "MidR A C = GradExpInvn A C (Suc 0)" 
      by simp
    thus ?thesis
      using \<open>B = C\<close> \<open>B' = MidR A B\<close> by blast 
  qed
qed

lemma gradexpinv_stab_aux_n:
  assumes "Bet A B' B" and
    "Cong A B' B' B" and
    "B = GradExpInvn A C (Suc n)"
  shows "B' = GradExpInvn A C (Suc (Suc n))" 
proof -
  have "Suc (Suc n) \<noteq> 0" by simp
  moreover
  have "Suc (Suc n) \<noteq> 1" by simp
  moreover
  have "B' Midpoint A B"
    using Midpoint_def assms(1) assms(2) by blast 
  hence "B' = MidR A (GradExpInvn A C (Suc n))"
    using MidR_ex assms(3) by blast 
  ultimately
  show ?thesis
    by (metis GradExpInvn.simps One_nat_def assms(1) assms(3) 
        diff_Suc_Suc l8_20_1_R1 l8_6 minus_nat.diff_0)  
qed

lemma gradexpinv_stab:
  assumes "Bet A B' B" and
    "Cong A B' B' B" and
    "GradExpInv A B C"
  shows "GradExpInv A B' C" 
proof -
  have "GradExpInv A B C"
    using GradExpInv_def assms(3) by auto
  then obtain n where "B = GradExpInvn A C n"
    using GradExpInv_def by blast
  have "B' = GradExpInvn A C (Suc n)" 
  proof (cases "n = 0")
    case True
    show ?thesis
      using True \<open>B = GradExpInvn A C n\<close> assms(1) assms(2) 
        gradexpinv_stab_aux_0 by blast 
  next
    case False
    then obtain k where "Suc k = n"
      using not0_implies_Suc by auto 
    hence "B = GradExpInvn A C (Suc k)" 
      using \<open>B = GradExpInvn A C n\<close> by blast
    hence "B' = GradExpInvn A C (Suc (Suc k))" 
      using gradexpinv_stab_aux_n assms(1) assms(2) by blast
    show ?thesis
      using \<open>B' = GradExpInvn A C (Suc (Suc k))\<close> \<open>Suc k = n\<close> by blast 
  qed
  moreover
  have "Suc n \<noteq> 0"
    by simp 
  ultimately
  show ?thesis 
    using GradExpInv_def by blast
qed

lemma gradexp__gradexpinv_aux_1_0:
  assumes "C = GradExpn A B (Suc 0)"
  shows "B = GradExpInvn A C 0" 
proof (cases "A = B")
  case True
  hence "C = A"
    by (simp add: assms)
  thus ?thesis
    by (simp add: True)
next
  case False
  hence "C = B" 
    using assms by simp
  thus ?thesis 
    using False by simp
qed

lemma SymR_MidR:
  assumes "A = SymR B C"
  shows "C = MidR A B"
proof -
  have "C Midpoint B A" 
    using assms SymR_ex symmetric_point_construction by blast 
  thus ?thesis
    using MidR_ex_0 l7_17_bis by auto 
qed

lemma MidR_comm:
  assumes "C = MidR A B"
  shows "C = MidR B A"
proof -
  have "C Midpoint B A"
    using MidR_ex_0 assms l7_2 by blast
  thus ?thesis
    by (meson MidR_ex \<open>C Midpoint B A\<close>) 
qed

lemma MidR_SymR:
  assumes "C = MidR A B"
  shows "A = SymR B C" 
proof -
  have "C Midpoint B A"
    using MidR_ex_0 assms l7_2 by blast
  thus ?thesis
    using SymR_ex by auto 
qed

lemma MidR_AA:
  shows "A = MidR A A" 
  using l7_3_2 MidR_ex by blast 

lemma MidR_AB:
  assumes "A = MidR A B"
  shows "A = B"
  by (metis MidR_AA MidR_SymR MidR_comm assms) 

lemma gradexp__gradexpinv_aux_1_n_aa:
  shows "GradExpInvn A' (MidR A' C') n = GradExpInvn A' C' (Suc n)" 
proof (cases "A' = C'")
  case True
  hence "A' = MidR A' C'" 
    using l7_3_2 MidR_ex by blast 
  hence "GradExpInvn A' (MidR A' C') n = A'"
    by simp
  moreover
  have "GradExpInvn A' C' (Suc n) = A'"
    using True by simp
  ultimately
  show ?thesis 
    by simp
next
  case False
  have "GradExpInvn A' (MidR A' C') n = GradExpInvn A' C' (Suc n)" 
  proof (induction n)
    case 0
    hence "A' \<noteq> MidR A' C'"
      using False MidR_AB by blast 
    hence "GradExpInvn A' (MidR A' C') 0 = (MidR A' C')"
      by simp 
    moreover
    have "GradExpInvn A' C' 0 = C'"
      using gradexpinv_init_aux by presburger 
    hence "GradExpInvn A' C' (Suc 0) = (MidR A' C')" 
      using False by simp
    ultimately
    have "GradExpInvn A' (MidR A' C') 0 = GradExpInvn A' C' (Suc 0)" 
      by simp
    thus ?case 
      by blast
  next
    case (Suc n)
    {
      assume "GradExpInvn A' (MidR A' C') n = GradExpInvn A' C' (Suc n)" 
      have "GradExpInvn A' (MidR A' C') (Suc n) 
    = (MidR A' (GradExpInvn A' (MidR A' C') ((Suc n)-1)))"
        by (metis GradExpInvn.simps MidR_AB Suc_neq_Zero diff_self_eq_0)
      have "\<dots> = MidR A' (GradExpInvn A' (MidR A' C') n)" 
        by simp
      have "\<dots> = MidR A' (GradExpInvn A' C' (Suc n))"
        using Suc.IH by presburger 
      have "\<dots> = MidR A' (GradExpInvn A' C' ((Suc(Suc n))-1))"
        using diff_Suc_1 by presburger 
      have "\<dots> = GradExpInvn A' C' (Suc(Suc n))"
        using False by auto 
      hence "GradExpInvn A' (MidR A' C') (Suc n) = GradExpInvn A' C' (Suc(Suc n))"
        using \<open>GradExpInvn A' (MidR A' C') (Suc n) 
      = MidR A' (GradExpInvn A' (MidR A' C') (Suc n - 1))\<close> 
          \<open>MidR A' (GradExpInvn A' (MidR A' C') (Suc n - 1)) 
      = MidR A' (GradExpInvn A' (MidR A' C') n)\<close> 
          \<open>MidR A' (GradExpInvn A' (MidR A' C') n) 
      = MidR A' (GradExpInvn A' C' (Suc n))\<close> 
          \<open>MidR A' (GradExpInvn A' C' (Suc n)) 
      = MidR A' (GradExpInvn A' C' (Suc (Suc n) - 1))\<close> 
        by presburger      
    }
    thus ?case
      using Suc.IH by blast 
  qed
  thus ?thesis by blast
qed

lemma gradexp__gradexpinv_aux_1_n_a:
  assumes "\<forall> A B C. (C = GradExpn A B (Suc n)) \<longrightarrow> B = GradExpInvn A C n"
  shows "\<forall> A' B' C'. (C' = GradExpn A' B' (Suc(Suc n))) \<longrightarrow> B' = GradExpInvn A' C' (Suc n)"
proof -
  {
    fix A' B' C'
    assume "C' = GradExpn A' B' (Suc(Suc n))"
    have "B' = GradExpInvn A' C' (Suc n)"
    proof (cases "A' = B'")
      case True
      {
        hence "C' = A'" 
          using True by (simp add: \<open>C' = GradExpn A' B' (Suc (Suc n))\<close>) 
        hence "A' = GradExpInvn A' C' (Suc n)"
          by simp
        hence "B' = GradExpInvn A' C' (Suc n)" 
          using True by simp
      }
      thus ?thesis
        using \<open>C' = GradExpn A' B' (Suc (Suc n))\<close> by blast 
    next
      case False
      {
        have "Suc (Suc n) \<noteq> 0" 
          by simp
        moreover
        have "Suc (Suc n) \<noteq> 1" 
          by simp
        moreover
        have "C' = SymR A' (GradExpn A' B' ((Suc (Suc n))-1))"
          by (simp add: False \<open>C' = GradExpn A' B' (Suc (Suc n))\<close>)
        have "(Suc (Suc n))-1 = Suc n" 
          by simp
        let ?ssn1 = "(Suc (Suc n))-1"
        let ?B1 = "GradExpn A' B' ?ssn1"
        have "?B1 = (GradExpn A' B' (Suc n))"
          by simp 
        hence "B' = (GradExpInvn A' ?B1 n)" 
          using assms by blast
        have "C' = SymR A' ?B1"
          using \<open>C' = SymR A' (GradExpn A' B' (Suc (Suc n) - 1))\<close> by blast 
        {
          assume "n = 0"
          hence "B' = ?B1"
            by force 
        }
        {
          assume "n = 1"
          hence "B' = MidR A' ?B1"
            by (metis False GradExpInvn.simps One_nat_def 
                \<open>B' = GradExpInvn A' (GradExpn A' B' (Suc (Suc n) - 1)) n\<close> 
                \<open>GradExpn A' B' (Suc (Suc n) - 1) = GradExpn A' B' (Suc n)\<close> 
                n_not_Suc_n) 
        }
        {
          assume "n \<noteq> 0 \<and> n \<noteq> 1"
          hence "B' = MidR A' (GradExpInvn A' ?B1 (n-1))"
            by (metis False GradExpInvn.simps 
                \<open>B' = GradExpInvn A' (GradExpn A' B' (Suc (Suc n) - 1)) n\<close>) 
        }
        {
          assume "Suc n = 1"
          hence "n = 0" 
            by simp
          have "C' = SymR A' ?B1"
            using \<open>C' = SymR A' (GradExpn A' B' (Suc (Suc n) - 1))\<close> by blast 
          hence "?B1 = MidR C' A'"
            using SymR_MidR by blast 
          hence "?B1 = MidR A' C'"
            using MidR_comm by blast 
          hence "B' = MidR A' C'"
            using \<open>n = 0 \<Longrightarrow> B' = GradExpn A' B' (Suc (Suc n) - 1)\<close> \<open>n = 0\<close> 
            by force 
        }
        moreover
        {
          assume "Suc n \<noteq> 1"
          hence "B' = MidR A' (GradExpInvn A' ?B1 (n-1))"
            by (metis One_nat_def 
                \<open>n = 1 \<Longrightarrow> B' = MidR A' (GradExpn A' B' (Suc (Suc n) - 1))\<close> 
                \<open>n \<noteq> 0 \<and> n \<noteq> 1 \<Longrightarrow> B' 
            = MidR A' (GradExpInvn A' (GradExpn A' B' (Suc (Suc n) - 1)) (n - 1))\<close> 
                diff_Suc_1 gradexpinv_init_aux) 
          obtain k where "Suc k = n"
            using \<open>Suc n \<noteq> 1\<close> not0_implies_Suc by auto 
          have "C' = SymR A' ?B1"
            using \<open>C' = SymR A' (GradExpn A' B' (Suc (Suc n) - 1))\<close> by blast 
          hence "?B1 = MidR A' C'"
            using MidR_comm SymR_MidR by presburger 
          hence "GradExpInvn A' ?B1 k = (GradExpInvn A' C' (Suc k))" 
            using gradexp__gradexpinv_aux_1_n_aa by presburger 
          hence "GradExpInvn A' ?B1 (n-1) = (GradExpInvn A' C' n)"
            using \<open>Suc k = n\<close> by force 
          hence "B' = MidR A' (GradExpInvn A' C' n)"
            using \<open>B' = MidR A' (GradExpInvn A' (GradExpn A' B' (Suc (Suc n) - 1)) (n - 1))\<close> 
            by presburger 
          hence "B' = MidR A' (GradExpInvn A' C' ((Suc n)-1))"
            using diff_Suc_1 by presburger 
        }
        ultimately
        have "B' = GradExpInvn A' C' (Suc n)"
          by (metis GradExpInvn.elims GradExpn_2 Suc_neq_Zero 
              \<open>C' = GradExpn A' B' (Suc (Suc n))\<close> bet_neq12__neq) 
      }
      hence "(C' = GradExpn A' B' (Suc(Suc n))) \<longrightarrow> B' = GradExpInvn A' C' (Suc n)" by blast
      thus ?thesis
        using \<open>C' = GradExpn A' B' (Suc (Suc n))\<close> by blast 
    qed
  }
  thus ?thesis by blast
qed

lemma gradexp__gradexpinv_aux_1_b:
  shows "\<forall> A B C. C = GradExpn A B (Suc n) \<longrightarrow> B = GradExpInvn A C n" 
proof (induction n)
  case 0
  have "\<forall> A B C. C = GradExpn A B (Suc 0) \<longrightarrow> B = GradExpInvn A C 0"
    by (meson gradexp__gradexpinv_aux_1_0) 
  thus ?case by blast
next
  case (Suc n)
  {
    assume  "\<forall> A B C. C = GradExpn A B (Suc n) \<longrightarrow> B = GradExpInvn A C n" 
    {
      fix A B C
      assume "C = GradExpn A B (Suc(Suc n))" 
      have "B = GradExpInvn A C (Suc n)"
        using \<open>C = GradExpn A B (Suc (Suc n))\<close> 
          \<open>\<forall>A B C. C = GradExpn A B (Suc n) \<longrightarrow> B = GradExpInvn A C n\<close> 
          gradexp__gradexpinv_aux_1_n_a by presburger 
    }
    hence "\<forall> A B C. C = GradExpn A B (Suc(Suc n)) \<longrightarrow> B = GradExpInvn A C (Suc n)" 
      by blast
  }
  thus ?case
    using Suc.IH by fastforce 
qed

lemma gradexp__gradexpinv_aux_1:
  assumes "C = GradExpn A B (Suc n)"
  shows "B = GradExpInvn A C n"
  using assms gradexp__gradexpinv_aux_1_b by blast 

lemma gradexp__gradexpinv_aux:
  assumes "GradExp A B C"
  shows "GradExpInv A B C" 
proof -
  obtain n where "n \<noteq> 0 \<and> C = GradExpn A B n" 
    using assms GradExp_def by blast
  hence "n \<noteq> 0"
    by blast
  then obtain m where "n = Suc m"
    using not0_implies_Suc by presburger 
  hence "B = GradExpInvn A C m" 
    using gradexp__gradexpinv_aux_1
    using \<open>n \<noteq> 0 \<and> C = GradExpn A B n\<close> by blast 
  thus ?thesis
    using GradExpInv_def \<open>n \<noteq> 0 \<and> C = GradExpn A B n\<close> by blast 
qed

lemma gradexpinv__gradexp_aux_1_a_0: 
  assumes "B' = MidR A' (GradExpInvn A' C' (Suc 0))"
  shows "C' = SymR A' (GradExpn A' B' (Suc(Suc 0)))" 
proof (cases "A' = C'")
  case True
  hence "B' = MidR A' C'"
    by (simp add: assms) 
  thus ?thesis
    by (metis GradExpn_1 MidR_AA MidR_SymR True)
next
  case False
  thus ?thesis
    by (metis GradExpn_2 GradExpn_4 Mid_cases SymR_MidR 
        assms gradexp__gradexpinv_aux_1_0 gradexp__gradexpinv_aux_1_n_aa 
        gradexpinv_init_aux gradexpinv_stab_aux_0 l7_9 
        midpoint_def midpoint_existence) 
qed

lemma sym_mid:
  shows "SymR A (MidR A B) = B"
  by (metis MidR_SymR MidR_comm)

lemma gradexpn_suc_suc:
  shows "GradExpn A B (Suc n) = GradExpn A (MidR A B) (Suc(Suc n))" 
proof (cases "A = B")
  case True 
  thus ?thesis
    using GradExpn_1 MidR_AA by presburger 
next
  case False
  hence "A \<noteq> B" 
    by simp
  have  "GradExpn A B (Suc n) = GradExpn A (MidR A B) (Suc(Suc n))" 
  proof (induction n)
    case 0
    have "GradExpn A (MidR A B) (Suc(Suc 0)) 
  = SymR A (GradExpn A (MidR A B) ((Suc(Suc 0))-1))"
      using False MidR_AB 
      by (metis diff_Suc_1 gradexp__gradexpinv_aux_1_b 
          gradexp__gradexpinv_aux_1_n_aa gradexpinv_init_aux sym_mid)
    hence "\<dots> = SymR A (GradExpn A (MidR A B) (Suc 0))"
      using diff_Suc_1 by presburger
    hence "\<dots> = SymR A (MidR A B)"
      by simp
    hence "\<dots> = B"
      using sym_mid by blast
    hence "GradExpn A B (Suc 0) = GradExpn A (MidR A B) (Suc (Suc 0))"
      by (metis gradexp__gradexpinv_aux_1 gradexp__gradexpinv_aux_1_n_aa 
          gradexpinv__gradexp_aux_1_a_0 gradexpinv_init_aux) 
    thus ?case
      by blast 
  next
    case (Suc n)
    {
      assume "\<forall> A' B'. GradExpn A' B' (Suc n) = GradExpn A' (MidR A' B') (Suc(Suc n))"
      {
        fix A B
        have "GradExpn A (MidR A B) (Suc(Suc(Suc n))) 
                  = SymR A (GradExpn A (MidR A B) (Suc(Suc(Suc n))-1))"
          using MidR_AA MidR_SymR by fastforce
        hence "\<dots> = GradExpn A B (Suc(Suc n))"
          by (metis GradExpn_3 GradExpn_4 
              \<open>\<forall>A' B'. GradExpn A' B' (Suc n) = GradExpn A' (MidR A' B') (Suc (Suc n))\<close> 
              gradexp_stab_aux_n) 
        hence "GradExpn A B (Suc(Suc n)) = GradExpn A (MidR A B) (Suc(Suc(Suc n)))"
          using \<open>GradExpn A (MidR A B) (Suc (Suc (Suc n))) 
                    = SymR A (GradExpn A (MidR A B) (Suc (Suc (Suc n)) - 1))\<close> 
          by presburger 
      }
      hence "\<forall> A B. GradExpn A B (Suc(Suc n)) = GradExpn A (MidR A B) (Suc(Suc(Suc n)))"
        by blast
    }
    thus ?case
      using GradExpn_3 GradExpn_4 Suc.IH gradexp_stab_aux_n by blast 
  qed
  thus ?thesis by blast
qed

lemma gradexpinv__gradexp_aux_1_a_n: 
  assumes "\<forall> A B C. (B = MidR A (GradExpInvn A C (Suc n))) \<longrightarrow> 
  C = SymR A (GradExpn A B (Suc(Suc n)))" 
  shows "B' = MidR A' (GradExpInvn A' C' (Suc(Suc n))) \<longrightarrow> 
  C' = SymR A' (GradExpn A' B' (Suc(Suc(Suc n))))" 
proof (cases "A' = C'")
  case True
  thus ?thesis
    by (metis GradExpn_1 MidR_AA MidR_SymR gradexp__gradexpinv_aux_1) 
next
  case False
  {
    assume "B' = MidR A' (GradExpInvn A' C' (Suc(Suc n)))"
    hence "\<dots> =  MidR A' (MidR A' (GradExpInvn A' C' (Suc(Suc n)-1)))"
      using False by force
    hence "\<dots> = MidR A' (MidR A' (GradExpInvn A' C' (Suc n)))"
      by simp
    let ?B1 = "(MidR A' (GradExpInvn A' C' (Suc n)))"
    have "C' = SymR A' (GradExpn A' ?B1 (Suc(Suc n)))" 
      using assms by blast
    have "GradExpn A' ?B1 (Suc(Suc n)) = GradExpn A' (MidR A' ?B1) (Suc(Suc(Suc n)))" 
      using gradexpn_suc_suc by blast 
    hence "C' = SymR A' (GradExpn A' B' (Suc(Suc(Suc n))))"
      by (metis MidR_comm SymR_MidR \<open>B' = MidR A' (GradExpInvn A' C' (Suc (Suc n)))\<close> 
          \<open>C' = SymR A' (GradExpn A' (MidR A' (GradExpInvn A' C' (Suc n))) (Suc (Suc n)))\<close> 
          gradexp__gradexpinv_aux_1 gradexp__gradexpinv_aux_1_n_aa)
  }
  thus ?thesis 
    by blast
qed

lemma gradexpinv__gradexp_aux_1_a:
  shows "\<forall> A B C. B = MidR A (GradExpInvn A C (Suc n)) \<longrightarrow> 
  C = SymR A (GradExpn A B (Suc(Suc n)))" 
proof (induction n)
  case 0
  thus ?case
    using gradexpinv__gradexp_aux_1_a_0 by blast
next
  case (Suc n)
  thus ?case
    using gradexpinv__gradexp_aux_1_a_n by blast
qed

lemma gradexpinv__gradexp_aux_1_n:
  assumes "B = GradExpInvn A C n \<longrightarrow> C = GradExpn A B (Suc n)" 
  shows "B' = GradExpInvn A' C' (Suc n)\<longrightarrow>C' = GradExpn A' B' (Suc(Suc n))"
proof (cases "A' = C'")
  case True
  thus ?thesis 
    by force
next
  case False
  hence "A' \<noteq> C'" 
    by blast
  {
    assume "B' = GradExpInvn A' C' (Suc n)" 
    have "C' = GradExpn A' B' (Suc(Suc n))"
    proof (cases "Suc n = 1")
      case True
      hence "B' = GradExpInvn A' C' 1" 
        using \<open>B' = GradExpInvn A' C' (Suc n)\<close> by simp 
      hence "B' = MidR A' C'" 
        using \<open>A' \<noteq> C'\<close> by simp
      hence "C' = SymR A' B'"
        by (metis MidR_SymR MidR_comm)
      have "A' \<noteq> B'"
        using False MidR_AB \<open>B' = MidR A' C'\<close> by blast 
      have "Suc(Suc n) \<noteq> 0 \<and> Suc (Suc n) \<noteq> 1" 
        by simp
      hence "GradExpn A' B' (Suc(Suc n)) =  SymR A' (GradExpn A' B' (Suc(Suc n)-1))"
        by (simp add: \<open>A' \<noteq> B'\<close>) 
      hence "\<dots> = SymR A' B'"
        by (simp add: True) 
      thus ?thesis
        using \<open>C' = SymR A' B'\<close> 
          \<open>GradExpn A' B' (Suc (Suc n)) = SymR A' (GradExpn A' B' (Suc (Suc n) - 1))\<close> 
        by presburger 
    next
      case False
      hence "B' = (MidR A' (GradExpInvn A' C' ((Suc n)-1)))"
        using \<open>B' = GradExpInvn A' C' (Suc n)\<close> 
        by (simp add: \<open>A' \<noteq> C'\<close>) 
      hence "C' = SymR A' (GradExpn A' B' ((Suc(Suc n)-1)))" 
        using gradexpinv__gradexp_aux_1_a 
        by (metis GradExpn.simps One_nat_def \<open>A' \<noteq> C'\<close> 
            \<open>B' = GradExpInvn A' C' (Suc n)\<close> gradexp__gradexpinv_aux_1 
            nat.distinct(1) nat.inject) 
      hence "\<dots> = GradExpn A' B' (Suc(Suc n))"
        by (metis GradExpn.simps GradExpn_1 MidR_AB MidR_SymR 
            One_nat_def \<open>B' = MidR A' (GradExpInvn A' C' (Suc n - 1))\<close> 
            nat.distinct(1) nat.inject) 
      thus ?thesis
        using \<open>C' = SymR A' (GradExpn A' B' (Suc (Suc n) - 1))\<close> by blast 
    qed
  }
  thus ?thesis 
    by blast
qed

lemma gradexpinv__gradexp_aux_1:
  shows "B = GradExpInvn A C n \<longrightarrow> C = GradExpn A B (Suc n)" 
proof (induction n)
  case 0
  thus ?case by force
next
  case (Suc n)
  thus ?case 
    using gradexpinv__gradexp_aux_1_n by blast
qed

lemma gradexpinv__gradexp_aux:
  assumes "GradExpInv A B C"
  shows "GradExp A B C" 
proof -
  obtain n where "B = GradExpInvn A C n"
    using GradExpInv_def assms by blast
  hence "C = GradExpn A B (Suc n)" 
    using gradexpinv__gradexp_aux_1 by blast
  thus ?thesis
    using GradExp_def by blast 
qed

lemma gradexp__gradexpinv: 
  shows "GradExp A B C \<longleftrightarrow> GradExpInv A B C"
  using gradexp__gradexpinv_aux gradexpinv__gradexp_aux by blast 


lemma reach__ex_gradexp_lt_aux:
  shows "\<forall> A B C P Q R. ((A \<noteq> B \<and> A B Le P R \<and> R = GradExpn P Q (Suc n)) \<longrightarrow> 
  (\<exists> C. GradExp A C B \<and> A C Lt P Q))" 
proof (induction n)
  case 0
  {
    fix A B C P Q R
    assume 1: "A \<noteq> B" and 2:"A B Le P R" and 3: "R = GradExpn P Q (Suc 0)"
    obtain C where "Bet A C B \<and> Cong A C C B"
      by (meson midpoint_bet midpoint_cong midpoint_existence)
    have "P \<noteq> Q"
      using "1" "2" "3" le_zero by force 
    have "R = Q"
      by (simp add: "3") 
    have "GradExpInv A C B" 
    proof -
      have "GradExpInv A B B"
        using gradexpinv_init by blast
      thus ?thesis
        using \<open>Bet A C B \<and> Cong A C C B\<close> gradexpinv_stab by blast 
    qed
    hence "GradExp A C B"
      by (simp add: gradexpinv__gradexp_aux) 
    moreover
    have "A C Lt P Q" 
    proof -
      have "A C Lt A B"
        by (simp add: "1" \<open>Bet A C B \<and> Cong A C C B\<close> mid__lt midpoint_def) 
      moreover
      have "A B Le P Q"
        using "2" \<open>R = Q\<close> by auto
      ultimately
      show ?thesis
        using le3456_lt__lt by blast
    qed
    ultimately
    have "\<exists> C. GradExp A C B \<and> A C Lt P Q"
      by blast 
  }
  thus ?case by blast
next
  case (Suc n)
  {
    assume H1: "\<forall> A' B' C' P' Q' R'. 
    (A' \<noteq> B' \<and> A' B' Le P' R' \<and> R' = GradExpn P' Q' (Suc n) 
    \<longrightarrow> (\<exists> C'. GradExp A' C' B' \<and> A' C' Lt P' Q'))" 
    {
      fix A B C P Q R
      assume 1: "A \<noteq> B" and 
        2:"A B Le P R" and 
        3: "R = GradExpn P Q (Suc (Suc n))"
      obtain M where "M Midpoint A B"
        using midpoint_existence by blast
      have "P \<noteq> R"
        using "1" "2" le_diff by blast 
      have "M \<noteq> A"
        using "1" \<open>M Midpoint A B\<close> bet_cong_eq between_trivial2 
          midpoint_cong by blast 
      have "M \<noteq> B"
        using "1" \<open>M Midpoint A B\<close> cong_identity midpoint_cong by blast 
      have "A M Le P R"
        using "1" "2" \<open>M Midpoint A B\<close> le3456_lt__lt lt__le mid__lt by blast 
      have "R = SymR P (GradExpn P Q ((Suc(Suc n))-1))"
        using "3" \<open>P \<noteq> R\<close> by auto
      hence "\<dots> = SymR P (GradExpn P Q (Suc n))"
        using diff_Suc_1 by presburger 
      let ?R' = "GradExpn P Q (Suc n)"
      have "\<exists> C. (GradExp A C M \<and> A C Lt P Q)"
      proof -
        have "A M Le P ?R'"
          using "2" "3" GradExpn_3 GradExpn_4 \<open>M Midpoint A B\<close> 
            le_mid2__le12 midpoint_def by blast 
        moreover
        have "M \<noteq> A" 
          using \<open>M \<noteq> A\<close> by force
        moreover
        have "?R' = GradExpn P Q (Suc n)" 
          by simp
        ultimately
        show ?thesis 
          using H1 by force 
      qed
      then obtain C where "GradExp A C M \<and> A C Lt P Q" 
        by auto
      hence "\<exists> C. GradExp A C B \<and> A C Lt P Q"
        using \<open>M Midpoint A B\<close> gradexp_stab midpoint_bet 
          midpoint_cong by blast 
    }
    hence "\<forall> A B C P Q R. 
    A \<noteq> B \<and> A B Le P R \<and> R = GradExpn P Q (Suc (Suc n)) 
    \<longrightarrow> (\<exists> C. GradExp A C B \<and> A C Lt P Q)" 
      by blast
  }
  thus ?case
    using Suc.IH by presburger
qed

lemma reach__grad_min_1:
  assumes "A \<noteq> B" and
    "Bet A B C"  and
    "A C Le A (Gradn A B (Suc 0))" 
  shows "\<exists> D E. (Bet A D C \<and> Grad A B D \<and> E \<noteq> C \<and> Bet A C E \<and> Bet A D E \<and> Cong A B D E)" 
proof (cases "C = (Gradn A B (Suc 0))")
  case True
  let ?f = "Gradn A B (Suc (Suc 0))"
  have "Grad A B B"
    by (simp add: grad_equiv_coq_1) 
  moreover
  have "?f \<noteq> C"
    by (metis Gradn_uniq_aux_1 True assms(1)) 
  moreover
  have "Bet A C ?f"
    using Bet_Gradn_Gradn_Suc True by blast 
  moreover
  have "Bet A B ?f"
    by (meson Diff__Bet_Gradn_Suc assms(1)) 
  moreover
  have "Cong A B B ?f"
    by (metis Lem_Gradn_0 Cong_Gradn_Gradn_Suc True assms(2) between_cong) 
  ultimately
  show ?thesis
    using assms(2) by blast
next
  case False
  let ?e = "Gradn A B (Suc 0)"
  have "Grad A B B"
    by (simp add: grad_equiv_coq_1) 
  moreover
  have "?e \<noteq> C"
    using False by auto 
  moreover
  have "Bet A C ?e"
    by (meson Gradn_aux_1_0 Diff__Bet_Gradn_Suc assms(1) 
        assms(2) assms(3) bet_out l5_1 l6_13_1 l6_6) 
  moreover
  have "Bet A B ?e"
    using Diff__Bet_Gradn_Suc not_bet_distincts by blast 
  moreover
  have "Cong A B B ?e"
    by (metis (full_types) False Lem_Gradn_0 Cong_Gradn_Gradn_Suc 
        assms(2) bet_neq23__neq between_cong_2 between_exchange3 
        calculation(3) calculation(4) l5_1)
  ultimately
  show ?thesis
    using assms(2) by blast
qed

lemma reach__grad_min_n:
  assumes "A \<noteq> B" and 
    "Bet A B C" and 
    "A C Le A (Gradn A B (Suc n)) \<longrightarrow> 
  (\<exists> D E. (Bet A D C \<and> Grad A B D \<and> E \<noteq> C \<and> Bet A C E \<and> Bet A D E \<and> Cong A B D E))"
  shows "A C Le A (Gradn A B (Suc(Suc n))) \<longrightarrow> 
  (\<exists> D E. (Bet A D C \<and> Grad A B D \<and> E \<noteq> C \<and> Bet A C E \<and> Bet A D E \<and> Cong A B D E))"
proof -
  {
    assume
      H1: "A C Le A (Gradn A B (Suc(Suc n)))"
    have  "\<exists> D E. (Bet A D C \<and> Grad A B D \<and> E \<noteq> C \<and> Bet A C E \<and> Bet A D E \<and> Cong A B D E)" 
    proof (cases "A C Le A (Gradn A B (Suc n))")
      case True
      hence "A C Le A (Gradn A B (Suc n))"
        by blast
      then obtain D E where 
        "Bet A D C \<and> Grad A B D \<and> E \<noteq> C \<and> Bet A C E \<and> Bet A D E \<and> Cong A B D E" 
        using assms(1) assms(3) by blast 
      thus ?thesis 
        by blast
    next
      case False
      hence "A (Gradn A B (Suc n)) Lt A C"
        by (meson nlt__le)
      let ?f = "Gradn A B (Suc (Suc n))"
      show ?thesis 
      proof (cases "C = ?f")
        case True
        let ?e = "Gradn A B (Suc (Suc (Suc n)))"
        show ?thesis 
        proof -
          have "Bet A C C"
            using not_bet_distincts by auto 
          moreover
          have "C = Gradn A B (Suc (Suc n))"
            using True by auto 
          hence "Grad A B C"
            using Grad_def by blast 
          moreover
          have "?e \<noteq> C"
            by (metis Gradn_uniq_aux_1 True assms(1)) 
          moreover
          have "Bet A C ?e"
            using Bet_Gradn_Gradn_Suc True by blast 
          moreover
          have "Bet A B ?e"
            using Diff__Bet_Gradn_Suc not_bet_distincts by blast 
          moreover
          have "Cong A B C ?e"
            using Cong_Gradn_Gradn_Suc True by blast
          ultimately
          show ?thesis
            using assms(2) by blast
        qed
      next
        case False 
        hence " A C Le A ?f"
          using H1 by blast
        show ?thesis
        proof -
          let ?d = "Gradn A B (Suc n)"
          let ?e = "Gradn A B (Suc(Suc n))"
          have "Bet A ?d C"
            by (meson Diff__Bet_Gradn_Suc 
                \<open>A (Gradn A B (Suc n)) Lt A C\<close> assms(1) assms(2)
                l5_1 l5_12_a lt__nle) 
          moreover
          have "Grad A B ?d"
            using Grad_def by blast 
          moreover
          have "?e \<noteq> C"
            using False by auto
          moreover
          have "Bet A C ?e"
            by (metis H1 Bet_Gradn_Gradn_Suc assms(1) bet__lt1213 
                calculation(1) calculation(2) grad_neq__neq13 l5_1 lt__nle)
          moreover
          have "Bet A B ?e"
            using Diff__Bet_Gradn_Suc not_bet_distincts by blast 
          moreover
          have "Cong A B ?d ?e"
            using Cong_Gradn_Gradn_Suc by blast
          ultimately
          show ?thesis
            using between_exchange4 by blast
        qed
      qed
    qed
  }
  thus ?thesis
    by blast 
qed

lemma reach__grad_min_aux:
  assumes "A \<noteq> B" and
    "Bet A B C"
  shows "(Grad A B (Gradn A B (Suc n)) \<and> A C Le A (Gradn A B (Suc n))) 
  \<longrightarrow> (\<exists> D E. (Bet A D C \<and> Grad A B D \<and> E \<noteq> C \<and> Bet A C E \<and> Bet A D E \<and> Cong A B D E))"
proof (induction n)
  case 0
  show ?case   
    using assms(1) assms(2) reach__grad_min_1 by blast
next
  case (Suc n)
  have "Grad A B (Gradn A B (Suc n)) \<and> Grad A B (Gradn A B (Suc (Suc n)))"
    using Grad_def by blast
  thus ?case 
    using assms(1) assms(2) reach__grad_min_n Suc.IH by blast
qed

(** D is the last graduation of AB before or equal to C, and E the first graduation after C *)
lemma reach__grad_min:
  assumes "A \<noteq> B" and
    "Bet A B C" and
    "Reach A B A C"
  shows "\<exists> D E. (Bet A D C \<and> Grad A B D \<and> E \<noteq> C \<and> Bet A C E \<and> Bet A D E \<and> Cong A B D E)" 
proof -
  obtain D where "Grad A B D \<and> A C Le A D"
    by (meson assms(3) gradexp__grad reach__ex_gradexp_le)
  hence "A C Le A D" 
    by blast
  have "A Out C D" 
  proof -
    have "A Out C B"
      using assms(1) assms(2) bet_out l6_6 by presburger 
    moreover
    have "Grad A B D"
      by (simp add: \<open>Grad A B D \<and> A C Le A D\<close>)
    hence "Bet A B D"
      by (simp add: grad__bet) 
    hence "A Out B D"
      using assms(1) bet_out by force 
    ultimately
    show ?thesis
      using l6_7 by blast
  qed
  hence "Bet A C D" 
    using l6_13_1 by (simp add: \<open>A C Le A D\<close>) 
  have "Grad A B D"
    by (simp add: \<open>Grad A B D \<and> A C Le A D\<close>)
  then obtain n where "(n \<noteq> 0) \<and> (D = Gradn A B n)"
    using Grad_def by blast
  hence "n \<noteq> 0" 
    by simp
  then obtain m where "Suc m = n"
    by (metis not0_implies_Suc) 
  hence "D = Gradn A B (Suc m)"
    by (simp add: \<open>n \<noteq> 0 \<and> D = Gradn A B n\<close>) 
  show ?thesis 
    by (metis \<open>Grad A B D \<and> A C Le A D\<close> 
        \<open>Suc m = n\<close> \<open>n \<noteq> 0 \<and> D = Gradn A B n\<close> 
        assms(1) assms(2) reach__grad_min_aux) 
qed

lemma reach__ex_gradexp_lt:
  assumes "A \<noteq> B" and
    "Reach P Q A B"
  shows "\<exists> C. GradExp A C B \<and> A C Lt P Q"
proof -
  obtain R where "GradExp P Q R \<and> A B Le P R"
    using assms(2) reach__ex_gradexp_le by blast
  then obtain n where "n \<noteq> 0 \<and> R = GradExpn P Q n"
    using GradExp_def by blast 
  hence "n \<noteq> 0" 
    by blast
  then obtain m where "Suc m = n"
    using not0_implies_Suc by blast
  hence "R = GradExpn P Q (Suc m)"
    by (simp add: \<open>n \<noteq> 0 \<and> R = GradExpn P Q n\<close>) 
  {
    fix B 
    assume "A \<noteq> B" and "A B Le P R" 
    hence "\<exists> C. (GradExp A C B \<and> A C Lt P Q)"
      using \<open>R = GradExpn P Q (Suc m)\<close> reach__ex_gradexp_lt_aux by force
  }
  thus ?thesis
    by (simp add: \<open>GradExp P Q R \<and> A B Le P R\<close> assms(1)) 
qed

(** This development is inspired by The Foundations of Geometry and 
  the Non-Euclidean Plane, by George E Martin, chapter 22 *)

lemma t22_18_aux_0:
  assumes "Bet A0 D1 A1" and
    "Cong E0 E1 A1 D1" and
    "D = Gradn A0 D1 (Suc 0)"
  shows "\<exists> A E. (Grad2 A0 A1 A E0 E1 E \<and> Cong E0 E A D \<and> Bet A0 D A)" 
proof -
  have "D = D1" 
    by (simp add: assms(3))  
  thus ?thesis 
    using assms(1) assms(2) grad2_init by blast
qed

lemma t22_18_aux_n:
  assumes "\<forall> A0 D1 A1 E0 E1 D. 
  (Bet A0 D1 A1 \<and> Cong E0 E1 A1 D1 \<and> D = Gradn A0 D1 (Suc n)) \<longrightarrow>
  (\<exists> A E. (Grad2 A0 A1 A E0 E1 E \<and> Cong E0 E A D \<and> Bet A0 D A))" 
  shows "\<forall> A0 D1 A1 E0 E1 D. 
  (Bet A0 D1 A1 \<and> Cong E0 E1 A1 D1 \<and> D = Gradn A0 D1 (Suc(Suc n))) \<longrightarrow>
  (\<exists> A E. (Grad2 A0 A1 A E0 E1 E \<and> Cong E0 E A D \<and> Bet A0 D A))" 
proof -
  have "\<forall> A0 D1 A1 E0 E1 D. (Bet A0 D1 A1 \<and> Cong E0 E1 A1 D1 \<and>
  D = Gradn A0 D1 (Suc n)) \<longrightarrow>
  (\<exists> A E. (Grad2 A0 A1 A E0 E1 E \<and> Cong E0 E A D \<and> Bet A0 D A))" 
    using assms by blast
  {
    fix A0 D1 A1 E0 E1 D
    assume 1: "Bet A0 D1 A1" and
      2: "Cong E0 E1 A1 D1" and
      "D = Gradn A0 D1 (Suc(Suc n))"
    let ?C = "Gradn A0 D1 (Suc n)"
    obtain A E where "Grad2 A0 A1 A E0 E1 E" and "Cong E0 E A ?C" and "Bet A0 ?C A" 
      using 1 2 assms by blast
    obtain A' where "Bet A0 A A'" and "Cong A A' A0 A1" 
      using segment_construction by blast
    obtain E' where "Bet E0 E E'" and "Cong E E' E0 E1"
      using segment_construction by blast
    have "Grad2 A0 A1 A' E0 E1 E'" 
      using Grad2_stab \<open>Bet A0 A A'\<close> \<open>Bet E0 E E'\<close> \<open>Cong A A' A0 A1\<close> 
        \<open>Cong E E' E0 E1\<close> \<open>Grad2 A0 A1 A E0 E1 E\<close> cong_symmetry by blast
    moreover
    have "E0 E1 Le A A'" 
      by (meson "1" "2" \<open>Cong A A' A0 A1\<close> bet__le2313 l5_6 
          le_left_comm not_cong_3412)
    obtain D' where "Bet A D' A'" and "Cong E0 E1 A D'"
      using Le_def \<open>E0 E1 Le A A'\<close> by blast
    have "Cong E0 E' A' D" 
    proof -
      have "Cong E0 E' ?C D'" 
      proof -
        have "Bet ?C A D'" 
          by (metis between_exchange3 \<open>Bet A D' A'\<close> 
              \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> \<open>Bet A0 A A'\<close> 
              between_inner_transitivity)
        moreover
        have "Cong E0 E ?C A" 
          using \<open>Cong E0 E A (Gradn A0 D1 (Suc n))\<close> not_cong_1243 by blast
        moreover
        have "Cong E E' A D'" 
          by (metis cong_transitivity \<open>Cong E E' E0 E1\<close> \<open>Cong E0 E1 A D'\<close>)
        ultimately
        show ?thesis 
          using \<open>Bet E0 E E'\<close> l2_11 by blast
      qed
      moreover
      have "Cong ?C D' A' D" 
      proof -
        have "Bet ?C D' A'" 
          by (metis between_exchange3 \<open>Bet A D' A'\<close> 
              \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> \<open>Bet A0 A A'\<close> between_exchange2)
        moreover
        have "Bet A' D ?C" 
        proof -
          have "Grad A0 A1 A" 
            using \<open>Grad2 A0 A1 A E0 E1 E\<close> grad2__grad123 by blast
          hence "Bet A0 A1 A" 
            by (simp add: grad__bet)
          have "Bet A0 D1 ?C" 
            using Diff__Bet_Gradn_Suc not_bet_distincts by blast
          show ?thesis 
          proof (cases "A0 = ?C")
            case True
            thus ?thesis 
              by (metis Gradn_aux_1_0 Lem_Gradn_id_n 
                  \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> not_bet_distincts)
          next
            case False
            hence "A0 \<noteq> ?C" 
              by blast
            show ?thesis 
            proof (cases "D = ?C")
              case True
              thus ?thesis 
                using not_bet_distincts by blast
            next
              case False
              hence "D \<noteq> ?C"
                by blast
              show ?thesis 
              proof (cases "A' = ?C")
                case True
                thus ?thesis 
                  by (metis "1" Lem_Gradn_id_n cong_diff_3 
                      \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> \<open>Bet A0 A A'\<close> 
                      \<open>Cong A A' A0 A1\<close> \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> 
                      between_equality_2 between_identity)
              next
                case False
                hence "A' \<noteq> ?C" 
                  by blast
                have "?C Out D A'" 
                proof -
                  have "D \<noteq> ?C"
                    using \<open>D \<noteq> Gradn A0 D1 (Suc n)\<close> by auto
                  moreover
                  have "A' \<noteq> ?C" 
                    using False by blast
                  moreover
                  have "A0 \<noteq> ?C" 
                    using \<open>A0 \<noteq> Gradn A0 D1 (Suc n)\<close> by auto
                  moreover
                  have "Bet D ?C A0" 
                    using Bet_Gradn_Gradn_Suc 
                      \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> between_symmetry by blast
                  ultimately
                  show ?thesis 
                    by (meson \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> \<open>Bet A0 A A'\<close> 
                        between_exchange4 between_symmetry l6_3_2)
                qed
                moreover
                have "?C D Le ?C A'" 
                proof -
                  have "?C D Le A A'" 
                    by (metis "1" Cong_Gradn_Gradn_Suc cong_symmetry 
                        \<open>Cong A A' A0 A1\<close> \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> 
                        bet__le1213 l5_6)
                  moreover
                  have "A A' Le ?C A'" 
                    by (metis between_exchange3 
                        \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> 
                        \<open>Bet A0 A A'\<close> bet__le2313)
                  ultimately
                  show ?thesis 
                    using le_transitivity by blast
                qed
                ultimately
                show ?thesis
                  using between_symmetry l6_13_1 by blast
              qed
            qed
          qed
        qed
        moreover
        have "Cong ?C A' A' ?C" 
          by (simp add: cong_pseudo_reflexivity)
        moreover
        have "Cong D' A' D ?C" 
        proof -
          have "Cong A0 D1 (Gradn A0 D1 (Suc n)) (Gradn A0 D1 (Suc (Suc n)))" 
            using Cong_Gradn_Gradn_Suc by blast
          hence "Cong A0 D1 ?C D" 
            using \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> by blast
          hence "Cong A0 D1 D ?C" 
            using not_cong_1243 by blast
          have "Bet A1 D1 A0" 
            by (simp add: "1" between_symmetry)
          have "Cong A1 D1 A D'" 
            using "2" \<open>Cong E0 E1 A D'\<close> cong_inner_transitivity 
            by blast
          have "Cong A0 A1 A A'" 
            using \<open>Cong A A' A0 A1\<close> cong_symmetry by presburger
          hence "Cong A0 D1 D' A'" 
            using  \<open>Bet A D' A'\<close> \<open>Bet A1 D1 A0\<close> \<open>Cong A1 D1 A D'\<close> 
              l4_3_1 not_cong_2134 by blast
          thus ?thesis 
            using \<open>Cong A0 D1 D (Gradn A0 D1 (Suc n))\<close> 
              cong_inner_transitivity by blast
        qed
        ultimately
        show ?thesis 
          using l4_3 by blast
      qed
      ultimately
      show ?thesis 
        using Cong_cases cong_inner_transitivity by blast
    qed
    moreover
    have "Bet A0 D A'" 
    proof -
      have "Bet A0 ?C A'" 
        using \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> \<open>Bet A0 A A'\<close> 
          between_exchange4 by blast
      have "Bet ?C D A'" 
      proof -
        have "Grad A0 A1 A" 
          using \<open>Grad2 A0 A1 A E0 E1 E\<close> grad2__grad123 by blast
        hence "Bet A0 A1 A" 
          by (simp add: grad__bet)
        have "Bet A0 D1 ?C" 
          using Diff__Bet_Gradn_Suc not_bet_distincts by blast
        show ?thesis 
        proof (cases "A0 = ?C")
          case True
          thus ?thesis 
            by (metis Gradn_aux_1_0 Lem_Gradn_id_n 
                \<open>Bet A0 (Gradn A0 D1 (Suc n)) A'\<close> 
                \<open>D = Gradn A0 D1 (Suc (Suc n))\<close>)
        next
          case False
          hence "A0 \<noteq> ?C" 
            by blast
          show ?thesis 
          proof (cases "D = ?C")
            case True
            thus ?thesis 
              using between_trivial2 by auto
          next
            case False
            hence "D \<noteq> ?C"
              by blast
            show ?thesis 
            proof (cases "A' = ?C")
              case True
              thus ?thesis 
                by (metis "1" Lem_Gradn_id_n cong_diff_3
                    \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> \<open>Bet A0 A A'\<close> 
                    \<open>Cong A A' A0 A1\<close> \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> 
                    between_equality_2 between_identity)
            next
              case False
              hence "A' \<noteq> ?C" 
                by blast
              have "?C Out D A'" 
              proof -
                have "D \<noteq> ?C"
                  using \<open>D \<noteq> Gradn A0 D1 (Suc n)\<close> by auto
                moreover
                have "A' \<noteq> ?C" 
                  using False by blast
                moreover
                have "A0 \<noteq> ?C" 
                  using \<open>A0 \<noteq> Gradn A0 D1 (Suc n)\<close> by auto
                moreover
                have "Bet D ?C A0" 
                  using Bet_Gradn_Gradn_Suc 
                    \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> 
                    between_symmetry by blast
                ultimately
                show ?thesis 
                  by (meson \<open>Bet A0 (Gradn A0 D1 (Suc n)) A'\<close>
                      between_symmetry l6_3_2)
              qed
              moreover
              have "?C D Le ?C A'" 
              proof -
                have "?C D Le A A'" 
                  by (metis "1" Cong_Gradn_Gradn_Suc cong_symmetry
                      \<open>Cong A A' A0 A1\<close> \<open>D = Gradn A0 D1 (Suc (Suc n))\<close> 
                      bet__le1213 l5_6)
                moreover
                have "A A' Le ?C A'" 
                  by (metis between_exchange3 \<open>Bet A0 (Gradn A0 D1 (Suc n)) A\<close> 
                      \<open>Bet A0 A A'\<close> bet__le2313)
                ultimately
                show ?thesis 
                  using le_transitivity by blast
              qed
              ultimately
              show ?thesis 
                using l6_13_1 by blast
            qed
          qed
        qed
      qed
      thus ?thesis
        using \<open>Bet A0 (Gradn A0 D1 (Suc n)) A'\<close> between_exchange2 by blast
    qed
    ultimately
    have "\<exists> A E. (Grad2 A0 A1 A E0 E1 E \<and> Cong E0 E A D \<and> Bet A0 D A)" 
      by blast
  }
  thus ?thesis by blast
qed

lemma t22_18_aux0:
  shows "\<forall> A0 D1 A1 E0 E1 D. 
  (Bet A0 D1 A1 \<and> Cong E0 E1 A1 D1 \<and> D = Gradn A0 D1 (Suc n)) \<longrightarrow>
  (\<exists> A E. (Grad2 A0 A1 A E0 E1 E \<and> Cong E0 E A D \<and> Bet A0 D A))" 
proof (induction n)
  case 0
  show ?case 
    using t22_18_aux_0 by auto
next
  case (Suc n)
  show ?case
    using t22_18_aux_n Suc.IH by blast
qed

(** For every m, there exists n such that A0Dm = A0An - E0En = n(A0A1 - E0E1) (m=n) *)
lemma t22_18_aux1:
  assumes "Bet A0 D1 A1" and
    "Cong E0 E1 A1 D1" and
    "Grad A0 D1 D"
  shows "\<exists> A E. (Grad2 A0 A1 A E0 E1 E \<and> Cong E0 E A D \<and> Bet A0 D A)"
proof -
  obtain n  where "n \<noteq> 0" and "D = Gradn A0 D1 n" 
    using Grad_def assms(3) by blast
  hence "n \<noteq> 0" 
    by blast
  then obtain m where "n = Suc m" 
    using not0_implies_Suc by presburger
  hence "D = Gradn A0 D1 (Suc m)" 
    by (simp add: \<open>D = Gradn A0 D1 n\<close>)
  thus ?thesis 
    using assms(1) assms(2) t22_18_aux0 by blast  
qed

lemma t22_18_aux2_0:
  assumes "Saccheri A0 B0 B1 A1" and
    "A = Gradn A0 A1 (Suc 0)" and
    "E = Gradn B0 B1 (Suc 0)" and
    "Saccheri A0 B0 B A"
  shows "B0 B Le B0 E" 
proof -
  have "Per B0 A0 A1" 
    using Saccheri_def assms(1) by blast
  have "Per A0 A1 B1" 
    using Saccheri_def assms(1) by blast
  have "Cong A0 B0 B1 A1" 
    using Saccheri_def assms(1) by blast
  have "A0 A1 OS B0 B1"   
    using Saccheri_def assms(1) by blast
  have "Per B0 A0 A"
    using Saccheri_def assms(4) by blast
  have "Per A0 A B"
    using Saccheri_def assms(4) by blast
  have "A0 A OS B0 B"
    using Saccheri_def assms(4) by blast
  have "Cong A0 B0 B A"
    using Saccheri_def assms(4) by blast
  have "A = A1"
    by (simp add: assms(2))
  have "E = B1"
    by (simp add: assms(3))
  have "Saccheri A0 B0 B A1" 
    using \<open>A = A1\<close> assms(4) by auto
  hence "Cong A0 B0 B A1"
    using Saccheri_def by blast
  hence "B = B1" 
  proof-
    have "A0 \<noteq> A1" 
      using \<open>A0 A1 OS B0 B1\<close> os_distincts by blast
    have "A1 Out B B1" 
    proof -
      have "Col A1 B B1" 
      proof -
        have "Coplanar A0 B B1 A1" 
        proof -
          have "\<not> Col B0 A0 A1" 
            by (meson \<open>A0 A1 OS B0 B1\<close> col123__nos not_col_permutation_2)
          moreover
          have "Coplanar B0 A0 A1 B" 
            using \<open>A = A1\<close> assms(4) coplanar_perm_7 sac__coplanar by blast
          moreover
          have "Coplanar B0 A0 A1 B1" 
            by (meson \<open>A0 A1 OS B0 B1\<close> ncoplanar_perm_8 os__coplanar)
          ultimately
          show ?thesis 
            by (meson coplanar_pseudo_trans ncop_distincts)
        qed
        moreover
        have "A0 \<noteq> A1" 
          using \<open>A0 \<noteq> A1\<close> by auto
        moreover
        have "Per B A1 A0" 
          using \<open>A = A1\<close> \<open>Per A0 A B\<close> l8_2 by blast
        moreover
        have "Per B1 A1 A0" 
          using Per_cases \<open>Per A0 A1 B1\<close> by blast
        ultimately
        show ?thesis 
          using col_permutation_2 cop_per2__col by blast
      qed
      moreover
      have "A1 A0 OS B B1" 
      proof -
        have "A1 A0 OS B B0" 
          using Saccheri_def \<open>A = A1\<close> assms(4) invert_one_side 
            one_side_symmetry by blast
        moreover
        have "A1 A0 OS B0 B1" 
          by (simp add: \<open>A0 A1 OS B0 B1\<close> invert_one_side)
        ultimately
        show ?thesis 
          using one_side_transitivity by blast
      qed
      ultimately
      show ?thesis 
        using col_one_side_out by auto
    qed
    moreover
    have "Cong A1 B A0 B0" 
      using Cong_cases \<open>Cong A0 B0 B A1\<close> by blast
    moreover
    have "A1 Out B1 B1" 
      using calculation(1) out_diff2 out_trivial by auto
    moreover
    have "Cong A1 B1 A0 B0" 
      using \<open>Cong A0 B0 B1 A1\<close> not_cong_3421 by blast
    ultimately
    show ?thesis 
      using l6_11_uniqueness by blast
  qed
  thus ?thesis 
    using \<open>E = B1\<close> local.le_cases by blast
qed

lemma t22_18_aux2_Sucn:
  assumes "\<forall> A A0 A1 B B0 B1 E.
  Saccheri A0 B0 B1 A1 \<and> A = Gradn A0 A1 (Suc n) \<and>
  E = Gradn B0 B1 (Suc n) \<and> Saccheri A0 B0 B A \<longrightarrow> B0 B Le B0 E" 
  shows "\<forall> A A0 A1 B B0 B1 E.
  Saccheri A0 B0 B1 A1 \<and> A = Gradn A0 A1 (Suc(Suc n)) \<and>
  E = Gradn B0 B1 (Suc(Suc n)) \<and> Saccheri A0 B0 B A \<longrightarrow> B0 B Le B0 E" 
proof -
  {
    fix A A0 A1 B B0 B1 E
    assume "Saccheri A0 B0 B1 A1" and
      "A = Gradn A0 A1 (Suc(Suc n))" and
      "E = Gradn B0 B1 (Suc(Suc n))" and
      "Saccheri A0 B0 B A"
    have "A0 \<noteq> B0" 
      using \<open>Saccheri A0 B0 B1 A1\<close> sac_distincts by blast
    let ?A = "Gradn A0 A1 (Suc n)"
    let ?E = "Gradn B0 B1 (Suc n)"
    have "Saccheri A0 B0 B ?A \<longrightarrow> B0 B Le B0 ?E"
      using \<open>Saccheri A0 B0 B1 A1\<close> assms by blast
    {
      assume "A0 = ?A"
      have "Bet A0 A1 ?A" 
        using Diff__Bet_Gradn_Suc not_bet_distincts by blast
      hence "A1 = A0" 
        by (metis \<open>A0 = Gradn A0 A1 (Suc n)\<close> bet_neq32__neq)
      hence False 
        using sac_distincts \<open>Saccheri A0 B0 B1 A1\<close> by blast
    }
    hence "A0 \<noteq> ?A" 
      by blast
    have "\<exists> B. Saccheri A0 B0 B ?A" 
    proof -
      have "Grad A0 A1 ?A" 
        using Grad_def by blast
      hence "Bet A0 A1 ?A" 
        by (simp add: grad__bet)
      have "\<exists> P. A0 A1 Perp P ?A \<and> A0 A1 OS B0 P"
      proof -
        have "Grad A0 A1 ?A" 
          using Grad_def by blast
        hence "Bet A0 A1 ?A" 
          by (simp add: grad__bet)
        hence "Col A0 A1 ?A" 
          using Col_def by blast
        moreover
        have "\<not> Col A0 A1 B0" 
          by (meson \<open>Saccheri A0 B0 B1 A1\<close> Col_cases col_trivial_3 
              l8_16_1 sac__perp1214)
        ultimately
        show ?thesis 
          using l10_15 by blast
      qed
      then obtain P where "A0 A1 Perp P ?A" and "A0 A1 OS B0 P" 
        by blast
      hence "P \<noteq> ?A" 
        using perp_not_eq_2 by blast
      hence "\<exists> B. ?A Out B P \<and> Cong ?A B A0 B0" 
        using l6_11_existence \<open>A0 \<noteq> B0\<close> by simp
      then obtain B' where "?A Out B' P" and "Cong ?A B' A0 B0"
        by blast
      have "Saccheri A0 B0 B' ?A" 
      proof -
        have "Per B0 A0 ?A" 
        proof -
          have "Per B0 A0 A1" 
            by (meson perp_per_2 \<open>Saccheri A0 B0 B1 A1\<close> sac__perp1214)
          moreover
          have "Col A0 A1 ?A" 
            using Col_def \<open>Bet A0 A1 (Gradn A0 A1 (Suc n))\<close> by blast
          ultimately
          show ?thesis 
            using \<open>Saccheri A0 B0 B1 A1\<close> per_col sac_distincts by blast
        qed
        moreover
        have "Per A0 ?A B'"
        proof -
          have "?A A0 Perp ?A P" 
            using Perp_cases \<open>A0 A1 Perp P (Gradn A0 A1 (Suc n))\<close>
              \<open>A0 \<noteq> Gradn A0 A1 (Suc n)\<close> \<open>Bet A0 A1 (Gradn A0 A1 (Suc n))\<close>
              bet_col perp_col1 by blast
          moreover
          have "Col ?A P B'" 
            using \<open>Gradn A0 A1 (Suc n) Out B' P\<close> col_permutation_5 out_col by blast
          ultimately
          show ?thesis 
            by (meson Perp_cases col_trivial_3 l8_16_1)
        qed
        moreover
        have "Col A0 A1 ?A" 
          using Col_def \<open>Bet A0 A1 (Gradn A0 A1 (Suc n))\<close> by blast
        hence "A0 ?A OS B0 P" 
          using \<open>A0 A1 OS B0 P\<close> \<open>A0 \<noteq> Gradn A0 A1 (Suc n)\<close> 
            col_one_side by blast
        hence "?A A0 OS B0 P" 
          using invert_one_side by blast
        hence "?A A0 OS B0 B'" 
          using \<open>Gradn A0 A1 (Suc n) Out B' P\<close> l6_6
            out_out_one_side by blast
        hence "A0 ?A OS B0 B'" 
          using invert_one_side by blast
        ultimately
        show ?thesis 
          using Saccheri_def \<open>Cong (Gradn A0 A1 (Suc n)) B' A0 B0\<close>
            not_cong_4312 by blast
      qed
      thus ?thesis 
        by blast
    qed
    then obtain B' where "Saccheri A0 B0 B' ?A" 
      by blast
    hence "B0 B' Le B0 ?E" 
      using \<open>Saccheri A0 B0 B1 A1\<close> assms by blast
    have "Per B0 A0 ?A"
      using \<open>Saccheri A0 B0 B' ?A\<close> Saccheri_def by blast
    have "Per A0 ?A B'"
      using \<open>Saccheri A0 B0 B' ?A\<close> Saccheri_def by blast
    have "Cong A0 B0 B' ?A"
      using \<open>Saccheri A0 B0 B' ?A\<close> Saccheri_def by blast
    have "A0 ?A OS B0 B'"
      using \<open>Saccheri A0 B0 B' ?A\<close> Saccheri_def by blast
    obtain C where "Bet B0 B' C" and "Cong B' C ?E E" 
      using segment_construction by blast
    have "Cong B0 B1 B' B" 
    proof -
      have "Saccheri A0 B0 B1 A1" 
        by (simp add: \<open>Saccheri A0 B0 B1 A1\<close>)
      moreover
      have "Saccheri ?A B' B A" 
      proof -
        have "Saccheri A0 B0 B' ?A" 
          using \<open>Saccheri A0 B0 B' (Gradn A0 A1 (Suc n))\<close> by auto
        moreover
        have "?A \<noteq> A" 
          by (metis Gradn_uniq_aux_1 \<open>A = Gradn A0 A1 (Suc (Suc n))\<close> 
              \<open>A0 \<noteq> Gradn A0 A1 (Suc n)\<close> grad_rec_a_a)
        moreover
        have "Coplanar A0 B0 ?A A" 
          by (metis Bet_Gradn_Gradn_Suc ncop__ncols 
              \<open>A = Gradn A0 A1 (Suc (Suc n))\<close> bet_col)
        ultimately
        show ?thesis 
          by (meson cop_sac2__sac \<open>Saccheri A0 B0 B A\<close>)
      qed
      moreover
      have "Cong A0 B0 ?A B'" 
        using \<open>Cong A0 B0 B' (Gradn A0 A1 (Suc n))\<close> 
          cong_right_commutativity by blast
      moreover
      have "Cong A0 A1 ?A A" 
        using Cong_Gradn_Gradn_Suc \<open>A = Gradn A0 A1 (Suc (Suc n))\<close> by blast
      ultimately
      show ?thesis 
        using cong2_sac2__cong by blast
    qed
    have "Cong B B' B' C" 
    proof -
      have "Cong B B' ?E E" 
        using Cong_Gradn_Gradn_Suc 
          \<open>Cong B0 B1 B' B\<close> \<open>E = Gradn B0 B1 (Suc (Suc n))\<close> 
          cong_transitivity not_cong_3421 by blast
      moreover
      have "Cong ?E E B' C" 
        using \<open>Cong B' C (Gradn B0 B1 (Suc n)) E\<close> 
          cong_inner_transitivity cong_reflexivity by blast
      ultimately
      show ?thesis 
        by (meson cong_transitivity)
    qed
    hence "B0 B Le B0 C"
      by (meson  \<open>Bet B0 B' C\<close> Cong_cases cong_reflexivity 
          triangle_inequality_2)
    moreover
    have "B0 C Le B0 E" 
    proof -
      have "Bet B0 B' C" 
        by (simp add: \<open>Bet B0 B' C\<close>)
      moreover
      have "Bet B0 ?E E" 
        using Bet_Gradn_Gradn_Suc \<open>E = Gradn B0 B1 (Suc (Suc n))\<close> by blast
      moreover
      have "B0 B' Le B0 ?E" 
        using \<open>B0 B' Le B0 (Gradn B0 B1 (Suc n))\<close> by auto
      moreover
      have "B' C Le ?E E" 
        using \<open>Cong B' C (Gradn B0 B1 (Suc n)) E\<close> cong__le by blast
      ultimately
      show ?thesis 
        using \<open>Cong B' C (Gradn B0 B1 (Suc n)) E\<close> 
          bet2_le2__le1346 cong__le by blast
    qed
    ultimately
    have "B0 B Le B0 E"
      using le_transitivity by blast
  }
  thus ?thesis 
    by blast
qed

lemma t22_18_aux2_n:
  shows "\<forall> A A0 A1 B B0 B1 E.
  Saccheri A0 B0 B1 A1 \<and> A = Gradn A0 A1 (Suc n) \<and>
  E = Gradn B0 B1 (Suc n) \<and> Saccheri A0 B0 B A 
  \<longrightarrow> B0 B Le B0 E" 
proof (induction n)
  case 0
  show ?case
    using t22_18_aux2_0 by blast
next
  case (Suc n)
  show ?case
    using t22_18_aux2_Sucn Suc.IH by blast
qed

(** For every n, B0Bn is lower than or equal to n times B0B1 *)
lemma t22_18_aux2:
  assumes "Saccheri A0 B0 B1 A1" and
    "Grad2 A0 A1 A B0 B1 E" and
    "Saccheri A0 B0 B A"
  shows "B0 B Le B0 E" 
proof -
  obtain n where "n \<noteq> 0" and "A = Gradn A0 A1 n" and 
    "E = Gradn B0 B1 n" 
    using Grad2_def assms(2) by blast
  obtain m where "n = Suc m" 
    using \<open>n \<noteq> 0\<close> not0_implies_Suc by blast
  hence "A = Gradn A0 A1 (Suc m) \<and> E = Gradn B0 B1 (Suc m)" 
    using \<open>A = Gradn A0 A1 n\<close> \<open>E = Gradn B0 B1 n\<close> by blast
  show ?thesis 
    using t22_18_aux2_n 
      \<open>A = Gradn A0 A1 (Suc m) \<and> E = Gradn B0 B1 (Suc m)\<close> 
      assms(1) assms(3) by blast
qed

lemma t22_18:
  assumes "archimedes_axiom"
  shows "\<forall> A0 B0 B1 A1. Saccheri A0 B0 B1 A1 \<longrightarrow> \<not> (B0 B1 Lt A1 A0)"
proof -
  {
    fix A0 B0 B1 A1
    assume "Saccheri A0 B0 B1 A1"
    assume "B0 B1 Lt A1 A0"
    hence "B0 B1 Le A1 A0"
      using cong__nlt lt__le by blast
    then obtain D1 where "Bet A1 D1 A0" and "Cong B0 B1 A1 D1" 
      using Le_def by blast
    obtain C0 where "Bet A0 D1 C0" and "Cong D1 C0 A0 B0" 
      using segment_construction by fastforce
    obtain C where "Bet A0 C0 C" and "Cong C0 C A0 B0" 
      using segment_construction by fastforce
    {
      fix D
      assume "Grad A0 D1 D"
      have "A0 D Lt A0 C" 
      proof (cases "A0 = D1")
        case True
        thus ?thesis 
          using \<open>B0 B1 Lt A1 A0\<close> \<open>Cong B0 B1 A1 D1\<close> cong__nlt by blast
      next 
        case False
        obtain A E where "Grad2 A0 A1 A B0 B1 E \<and> Cong B0 E A D \<and> Bet A0 D A" 
          using t22_18_aux1 Bet_cases \<open>Bet A1 D1 A0\<close> 
            \<open>Cong B0 B1 A1 D1\<close> \<open>Grad A0 D1 D\<close> by blast
        have "Grad2 A0 A1 A B0 B1 E" 
          using \<open>Grad2 A0 A1 A B0 B1 E \<and> Cong B0 E A D \<and> Bet A0 D A\<close> by blast
        hence "Grad A0 A1 A" 
          using grad2__grad123 by blast
        hence "Bet A0 A1 A" 
          by (simp add: grad__bet)
        have "Cong B0 E A D" 
          using \<open>Grad2 A0 A1 A B0 B1 E \<and> Cong B0 E A D \<and> Bet A0 D A\<close> by blast
        have "Bet A0 D A" 
          using \<open>Grad2 A0 A1 A B0 B1 E \<and> Cong B0 E A D \<and> Bet A0 D A\<close> by blast
        have "\<exists> P. A0 A1 Perp A P \<and> A0 A1 OS B0 P"
        proof -
          have "Col A0 A1 A" 
            by (simp add: Col_def \<open>Bet A0 A1 A\<close>)
          moreover
          have "A0 A1 ParStrict B0 B1" 
            by (simp add: \<open>Saccheri A0 B0 B1 A1\<close> sac__pars1423)
          hence "\<not> Col A0 A1 B0"
            using par_strict_not_col_1 by blast
          ultimately
          show ?thesis 
            using Perp_cases l10_15 by blast
        qed
        then obtain P where "A0 A1 Perp A P" and "A0 A1 OS B0 P"
          by blast
        have "P \<noteq> A" 
          using \<open>A0 A1 Perp A P\<close> perp_not_eq_2 by blast
        have "A0 \<noteq> B0" 
          using \<open>A0 A1 OS B0 P\<close> os_distincts by blast
        then obtain B where "A Out B P" and "Cong A B A0 B0"
          using l6_11_existence \<open>P \<noteq> A\<close> by blast
        have "Saccheri A0 B0 B A" 
        proof -
          have "Per B0 A0 A" 
          proof -
            have "A0 \<noteq> A1" 
              using \<open>A0 A1 OS B0 P\<close> os_distincts by blast
            moreover
            have "Per B0 A0 A1" 
              by (meson perp_per_2 \<open>Saccheri A0 B0 B1 A1\<close> sac__perp1214)
            moreover
            have "Col A0 A1 A" 
              by (simp add: Col_def \<open>Bet A0 A1 A\<close>)
            ultimately
            show ?thesis 
              using per_col by blast
          qed
          moreover
          have "Per A0 A B"
          proof -
            have "A \<noteq> B" 
              using \<open>A Out B P\<close> out_distinct by blast
            moreover
            have "A A0 Perp A P" 
            proof -
              have "A0 \<noteq> A" 
                using False \<open>Bet A0 D A\<close> \<open>Grad A0 D1 D\<close> 
                  bet_neq32__neq grad_neq__neq13 by blast
              moreover
              have "A0 A1 Perp P A" 
                using Perp_cases \<open>A0 A1 Perp A P\<close> by blast
              moreover
              have "Col A0 A1 A" 
                by (simp add: Col_def \<open>Bet A0 A1 A\<close>)
              ultimately
              show ?thesis 
                using \<open>A0 A1 Perp A P\<close> col_trivial_3 perp_col2 
                by presburger
            qed
            moreover
            have "Col A P B" 
              by (simp add: \<open>A Out B P\<close> l6_6 out_col)
            ultimately
            show ?thesis 
              by (meson perp_per_2 perp_col1)
          qed
          moreover
          have "Cong A0 B0 B A" 
            using \<open>Cong A B A0 B0\<close> not_cong_4312 by blast
          moreover
          have "A A0 OS B0 B"
          proof -
            have "A A0 OS B0 P" 
              using \<open>A0 A1 OS B0 P\<close> \<open>Bet A0 A1 A\<close> bet_col 
                bet_neq32__neq col_one_side invert_one_side by blast
            moreover
            have "A Out P B" 
              using Out_cases \<open>A Out B P\<close> by blast
            ultimately
            show ?thesis 
              using out_out_one_side by blast
          qed
          hence "A0 A OS B0 B" 
            using invert_one_side by blast
          ultimately
          show ?thesis 
            using Saccheri_def by blast
        qed
        have "B0 B Le B0 E"
          using \<open>Saccheri A0 B0 B1 A1\<close> \<open>Grad2 A0 A1 A B0 B1 E\<close> 
            \<open>Saccheri A0 B0 B A\<close> t22_18_aux2 by blast
        have "B0 E Le A A0" 
          using Le_def \<open>Bet A0 D A\<close> \<open>Cong B0 E A D\<close> 
            between_symmetry by blast
        hence "B0 B Le A A0" 
          using le_transitivity \<open>B0 B Le B0 E\<close> by blast
        then obtain Q where "Bet A Q A0" and "Cong B0 B A Q" 
          using Le_def by blast
        have "A0 D Le A0 Q" 
        proof -
          have "Bet A0 Q A" 
            using Bet_cases \<open>Bet A Q A0\<close> by blast
          moreover
          have "Q A Le D A" 
          proof -
            have "Cong B0 B Q A" 
              using Cong_cases \<open>Cong B0 B A Q\<close> by blast
            moreover
            have "Cong B0 E D A" 
              using Cong_cases \<open>Cong B0 E A D\<close> by blast
            ultimately
            show ?thesis 
              using \<open>B0 B Le B0 E\<close> l5_6 by blast
          qed
          moreover
          have "A0 A Le A0 A" 
            using between_trivial2 l5_12_a by auto
          ultimately
          show ?thesis 
            using \<open>Bet A0 D A\<close> bet2_le2__le1245 by blast
        qed
        moreover
        have "A \<noteq> A0" 
          using False \<open>Bet A0 D A\<close> \<open>Grad A0 D1 D\<close> between_identity 
            grad_neq__neq13 by blast
        then obtain B0' where "A0 Out B0' A \<and> Cong A0 B0' A0 B0"
          using \<open>A0 \<noteq> B0\<close> l6_11_existence by presburger
        have "A0 Out B0' A"
          using \<open>A0 Out B0' A \<and> Cong A0 B0' A0 B0\<close> by blast
        have "Cong A0 B0' A0 B0"
          using \<open>A0 Out B0' A \<and> Cong A0 B0' A0 B0\<close> by blast
        obtain B' where "Bet A0 B0' B'" and "Cong B0' B' B0 B" 
          using segment_construction by blast
        obtain A' where "Bet B0' B' A'" and "Cong B' A' B A" 
          using segment_construction by blast
        have "A0 A Le A0 A'" 
        proof -
          obtain B'' where "Bet A0 B0' B''" and "Cong B0' B'' B0 A"
            using segment_construction by blast
          have "A0 A Le A0 B''" 
            by (meson \<open>Bet A0 B0' B''\<close> \<open>Cong A0 B0' A0 B0\<close> 
                \<open>Cong B0' B'' B0 A\<close> cong__le3412 l2_11_b lt__le not_cong_3412 
                triangle_strict_inequality_2)
          moreover
          have "A0 B'' Le A0 A'" 
          proof -
            have "B0' \<noteq> B'" 
              using sac_distincts 
              using \<open>Cong B0' B' B0 B\<close> \<open>Saccheri A0 B0 B A\<close> 
                cong_reverse_identity by blast
            hence "Bet A0 B0' A'" 
              using  \<open>Bet B0' B' A'\<close> \<open>Bet A0 B0' B'\<close> outer_transitivity_between 
              by blast 
            moreover
            have "A0 B0' Le A0 B0'" 
              using local.le_cases by auto 
            moreover
            have "B0' B'' Le B0' A'" 
            proof -
              have "B0 A Le B0' A'" 
              proof -
                have "Cong B0 B B0' B'" 
                  using \<open>Cong B0' B' B0 B\<close> not_cong_3412 by blast
                moreover
                have "Cong B A B' A'" 
                  using \<open>Cong B' A' B A\<close> cong_symmetry by presburger
                ultimately
                show ?thesis 
                  using \<open>Bet B0' B' A'\<close> triangle_inequality_2 by blast
              qed
              moreover
              have "Cong B0 A B0' B''" 
                using \<open>Cong B0' B'' B0 A\<close> cong_symmetry by blast
              moreover
              have "Cong B0' A' B0' A'" 
                by (simp add: cong_reflexivity)
              ultimately
              show ?thesis 
                using l5_6 by blast
            qed
            ultimately
            show ?thesis 
              using \<open>Bet A0 B0' B''\<close> bet2_le2__le1346 by blast
          qed
          ultimately
          show ?thesis 
            using le_transitivity by blast
        qed
        have "B0 B Le A' B0'" 
        proof -
          have "B0' B' Le B0' A'" 
            by (simp add: \<open>Bet B0' B' A'\<close> l5_12_a)
          moreover
          have "Cong B0' A' A' B0'" 
            by (simp add: cong_pseudo_reflexivity)
          ultimately
          show ?thesis 
            using \<open>Cong B0' B' B0 B\<close> l5_6 by blast
        qed
        obtain Q' where "Bet A' Q' B0'" and "Cong B0 B A' Q'" 
          using Le_def \<open>B0 B Le A' B0'\<close> by blast
        have "B0' \<noteq> B'" 
          using sac_distincts \<open>Cong B0' B' B0 B\<close> \<open>Saccheri A0 B0 B A\<close> 
            cong_reverse_identity by blast
        hence "Bet A0 B0' A'"
          using  \<open>Bet A0 B0' B'\<close> \<open>Bet B0' B' A'\<close> 
            outer_transitivity_between by blast
        have "A0 Q Lt A0 C" 
        proof -
          have "A0 Q Le A0 Q'" 
          proof -
            have "Bet A0 Q' A'" 
              using \<open>Bet A' Q' B0'\<close> \<open>Bet A0 B0' A'\<close> bet3__bet 
                between_trivial by blast
            moreover
            have "Bet A0 Q A" 
              using Bet_cases \<open>Bet A Q A0\<close> by auto
            moreover
            have "Q' A' Le Q A" 
              by (meson le_reflexivity \<open>Cong B0 B A Q\<close> 
                  \<open>Cong B0 B A' Q'\<close> l5_6 le_comm)
            ultimately
            show ?thesis 
              using \<open>A0 A Le A0 A'\<close> bet2_le2__le1245 by blast
          qed
          moreover
          have "A0 Q' Lt A0 C" 
          proof -
            have "Bet A0 D1 C" 
              using \<open>Bet A0 C0 C\<close> \<open>Bet A0 D1 C0\<close> between_exchange4 by blast
            hence "D1 C Lt A0 C" 
              by (simp add: False bet__lt2313)
            moreover
            have "Cong D1 C A0 Q'" 
            proof -
              have "Bet D1 C0 C"
                using \<open>Bet A0 C0 C\<close> \<open>Bet A0 D1 C0\<close> between_exchange3 by blast
              moreover
              have "Bet A0 B0' Q'" 
                using \<open>Bet A' Q' B0'\<close> \<open>Bet A0 B0' A'\<close> between_exchange3 
                  between_symmetry by blast
              moreover
              have "Cong D1 C0 A0 B0'" 
                by (metis Cong_cases \<open>Cong A0 B0' A0 B0\<close> 
                    \<open>Cong D1 C0 A0 B0\<close> cong_inner_transitivity)
              moreover
              have "Cong B0' Q' A B" 
              proof -
                have "Cong B0' B' A' Q'" 
                  using \<open>Cong B0 B A' Q'\<close> \<open>Cong B0' B' B0 B\<close> 
                    cong_transitivity by blast
                have "Cong B0' Q' A' B'" 
                proof (cases "Bet B0' Q' B'")
                  case True
                  hence "Bet A' B' Q'" 
                    using Bet_perm \<open>Bet B0' B' A'\<close> between_exchange3 by blast
                  moreover
                  have "Cong Q' B' B' Q'" 
                    by (simp add: cong_pseudo_reflexivity)
                  ultimately
                  show ?thesis 
                    using \<open>Cong B0' B' A' Q'\<close> True l4_3 by blast
                next
                  case False
                  hence "Q' \<noteq> B0'" 
                    using between_trivial2 by blast
                  hence "A' \<noteq> B0'" 
                    using \<open>Bet A' Q' B0'\<close> between_identity by blast
                  have "B0' Out B' Q'" 
                  proof -
                    have "B0' Out B' A'" 
                      using \<open>B0' \<noteq> B'\<close> \<open>Bet B0' B' A'\<close> bet_out by force
                    moreover
                    have "B0' Out A' Q'" 
                      by (simp add: \<open>Bet A' Q' B0'\<close> \<open>Q' \<noteq> B0'\<close> bet_out_1 l6_6)
                    ultimately
                    show ?thesis 
                      using l6_7 by blast
                  qed
                  hence "Bet B0' B' Q'" 
                    using False Out_def by blast
                  moreover
                  have "Bet A' Q' B'" 
                    using \<open>Bet A' Q' B0'\<close> between_exchange3 
                      between_symmetry calculation by blast
                  moreover
                  have "Cong B' Q' Q' B'"
                    by (simp add: cong_pseudo_reflexivity)
                  ultimately
                  show ?thesis 
                    using \<open>Cong B0' B' A' Q'\<close> l2_11_b by blast
                qed
                moreover
                have "Cong A' B' A B" 
                  using \<open>Cong B' A' B A\<close> not_cong_2143 by blast
                ultimately
                show ?thesis 
                  using cong_transitivity by blast
              qed
              hence "Cong B0' Q' A0 B0" 
                using  \<open>Cong A B A0 B0\<close> cong_transitivity by blast
              hence "Cong C0 C B0' Q'" 
                using cong_inner_transitivity \<open>Cong C0 C A0 B0\<close> cong_symmetry by blast
              ultimately
              show ?thesis 
                using l2_11_b by blast
            qed
            moreover
            have "Cong A0 C A0 C" 
              by (simp add: cong_reflexivity)
            ultimately
            show ?thesis 
              using cong2_lt__lt by blast
          qed
          ultimately
          show ?thesis 
            by (meson le1234_lt__lt)
        qed
        ultimately
        show ?thesis 
          using le1234_lt__lt by blast
      qed
    }
    hence "\<forall> D. Grad A0 D1 D \<longrightarrow> A0 D Lt A0 C" 
      by blast
    have "\<not> Cong B0 B1 A1 A0"
      using \<open>B0 B1 Lt A1 A0\<close> cong__nlt lt__le by blast
    have"A0 \<noteq> D1 \<longrightarrow> Reach A0 D1 A0 C" 
      using archimedes_axiom_def assms by blast
    then obtain D where "Grad A0 D1 D \<and> A0 C Le A0 D" 
      using Reach_def \<open>Cong B0 B1 A1 D1\<close> \<open>\<not> Cong B0 B1 A1 A0\<close> by blast
    hence "A0 D Lt A0 C" 
      by (simp add: \<open>\<forall>D. Grad A0 D1 D \<longrightarrow> A0 D Lt A0 C\<close>)
    moreover
    have "A0 C Lt A0 C" 
      using \<open>Grad A0 D1 D \<and> A0 C Le A0 D\<close> calculation lt__nle by blast  
    ultimately
    have False 
      using nlt by auto
  }
  thus ?thesis 
    by blast
qed

lemma t22_19:
  assumes "archimedes_axiom" 
  shows "\<forall> A B C D. Saccheri A B C D \<longrightarrow> \<not> Obtuse A B C" 
proof -
  {
    fix A B C D
    assume "Saccheri A B C D"
    hence "\<not> C B Lt A D" 
      using assms lt_comm t22_18 by blast
    moreover
    assume "Obtuse A B C"
    hence "C B Lt A D" 
      using \<open>Saccheri A B C D\<close> lt_left_comm lt_sac__obtuse_aux2 by blast
    ultimately
    have False 
      by blast
  }
  thus ?thesis 
    by blast
qed

lemma archi__obtuse_case_elimination:
  assumes "archimedes_axiom"
  shows "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" 
proof -
  have "\<not> (\<forall> A B C D. Saccheri A B C D \<longrightarrow> Obtuse A B C)"
    using assms ex_saccheri t22_19 by blast
  thus ?thesis 
    using hypothesis_of_obtuse_saccheri_quadrilaterals_def by blast
qed

lemma t22_23_aux:
  assumes "\<not> Col A M N" and
    "Per B C A" and
    "A \<noteq> C" and
    "M Midpoint A B" and
    "Per M N A" and
    "Col A C N" and
    "M Midpoint N L"
  shows "Bet A N C \<and> Lambert N L B C \<and> Cong B L A N"
proof -
  have "A \<noteq> M" 
    using assms(1) col_trivial_1 by blast
  have "N \<noteq> M" 
    using assms(1) col_trivial_2 by blast
  have "A \<noteq> N" 
    using assms(1) col_trivial_3 by blast
  have "L \<noteq> N" 
    using \<open>N \<noteq> M\<close> assms(7) l7_3 by blast
  have "A \<noteq> B" 
    using \<open>A \<noteq> M\<close> assms(4) l7_3 by blast
  hence "B \<noteq> M" 
    using assms(4) is_midpoint_id_2 by blast
  have "Bet A N C" 
  proof -
    have "Bet A M B" 
      by (simp add: assms(4) midpoint_bet)
    moreover
    have "Col A N C" 
      using assms(6) not_col_permutation_5 by blast
    moreover
    have "Per A N M" 
      by (simp add: assms(5) l8_2)
    moreover
    have "Per A C B" 
      by (simp add: assms(2) l8_2)
    ultimately
    show ?thesis 
      by (metis per23_preserves_bet \<open>A \<noteq> N\<close> assms(3))
  qed
  moreover
  have "A M N CongA B M L" 
    using \<open>A \<noteq> M\<close> \<open>N \<noteq> M\<close> assms(4) assms(7) l7_3_2 
      symmetry_preserves_conga by blast
  hence "Cong A N B L \<and> M A N CongA M B L \<and> M N A CongA M L B" 
    using per23_preserves_bet Cong_cases l11_49 \<open>A \<noteq> N\<close> assms(4) 
      assms(7) midpoint_cong by meson
  have "Lambert N L B C" 
  proof -
    {
      assume "C = N"
      have "M = B"
      proof -
        have "\<not> Col A M N"
          by (simp add: assms(1))
        moreover
        have "N \<noteq> M" 
          by (simp add: \<open>N \<noteq> M\<close>)
        moreover
        have "Col A M M" 
          using not_col_distincts by blast
        moreover
        have "Bet A M B" 
          by (simp add: assms(4) midpoint_bet)
        hence "Col A M B" 
          by (simp add: Col_def)
        moreover
        have "Col N M M" 
          by (simp add: col_trivial_2)
        moreover
        have "Coplanar A B M N" 
          by (meson \<open>A \<noteq> M\<close> calculation(3) calculation(4) 
              col__coplanar col_transitivity_1)
        hence "Col N M B" 
          using \<open>C = N\<close> \<open>A \<noteq> N\<close> assms(2) assms(5) col_permutation_3 
            cop_per2__col by blast
        moreover
        show ?thesis 
          using calculation(1) calculation(4) calculation(6) l6_16_1 by blast
      qed
      hence False 
        using \<open>B \<noteq> M\<close> by auto
    }
    hence "C \<noteq> N" 
      by blast
    moreover  
    have "L \<noteq> B"  
      using \<open>A \<noteq> N\<close> \<open>Cong A N B L \<and> M A N CongA M B L \<and> M N A CongA M L B\<close> 
        cong_diff by blast
    moreover
    have "B \<noteq> C"  
      using \<open>A \<noteq> B\<close> assms(1) assms(4) assms(6) col_permutation_1 
        l6_16_1 midpoint_col by blast
    moreover
    have "N \<noteq> L" 
      using \<open>L \<noteq> N\<close> by auto
    moreover
    have "Per L N C"  
      by (metis per_col \<open>A \<noteq> N\<close> \<open>N \<noteq> M\<close> assms(5) assms(6) assms(7) 
          col_per2__per l8_20_1_R1 midpoint_col not_col_permutation_1)
    moreover
    have "Per N C B"  
      by (metis per_col assms(2) assms(3) assms(6) col_permutation_4 l8_2)
    moreover
    have "Per N L B"  
    proof -
      have "Per M N A" 
        by (simp add: assms(5))
      moreover
      have "M N A CongA N L B" 
      proof -
        have "M N A CongA M L B" 
          by (simp add: \<open>Cong A N B L \<and> M A N CongA M B L \<and> M N A CongA M L B\<close>)
        moreover
        have "N Out M M" 
          using \<open>N \<noteq> M\<close> out_trivial by auto
        moreover
        have "N Out A A" 
          using \<open>A \<noteq> N\<close> \<open>Bet A N C\<close> \<open>C \<noteq> N\<close> l6_3_2 by blast
        moreover
        have "M \<noteq> L" 
          using \<open>N \<noteq> L\<close> assms(7) is_midpoint_id_2 by blast
        have "Bet L M N" 
          using assms(7) Bet_perm Midpoint_def by blast
        hence "L Out N M" 
          by (simp add: Out_def \<open>M \<noteq> L\<close> \<open>N \<noteq> L\<close>)
        moreover
        have "L Out B B" 
          using \<open>L \<noteq> B\<close> out_trivial by auto
        ultimately
        show ?thesis 
          using l11_10 by blast
      qed
      ultimately
      show ?thesis 
        using l11_17 by blast
    qed
    moreover
    have "Coplanar N L B C" 
    proof -
      have "Coplanar B C N M" 
      proof -
        have "Coplanar C N A B" 
          by (simp add: \<open>Bet A N C\<close> bet__coplanar between_symmetry)
        moreover
        have "Bet A M B" 
          by (simp add: assms(4) midpoint_bet)
        hence "Col B A M" 
          using Col_def by auto
        ultimately
        show ?thesis 
          using \<open>A \<noteq> B\<close> col_cop__cop coplanar_perm_14 
            coplanar_perm_7 by blast
      qed
      moreover
      have "Bet N M L" 
        using assms(7) midpoint_bet by blast
      hence "Col N M L" 
        by (simp add: Col_def)
      ultimately
      show ?thesis 
        using \<open>N \<noteq> M\<close> col_cop__cop ncoplanar_perm_16 by blast
    qed
    ultimately
    show ?thesis 
      using Lambert_def by blast
  qed
  moreover
  have "Cong A N B L"
    using \<open>Cong A N B L \<and> M A N CongA M B L \<and> M N A CongA M L B\<close> by blast
  hence "Cong B L A N" 
    by (simp add: cong_symmetry)
  ultimately
  show ?thesis 
    by simp
qed

lemma t22_23:
  assumes "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals"
  shows "\<forall> A B C M N L.
  \<not> Col A M N \<and> Per B C A \<and> A \<noteq> C \<and> M Midpoint A B \<and>
  Per M N A \<and> Col A C N \<and> M Midpoint N L \<longrightarrow>
  (Bet A N C \<and> N C Le A N \<and> L N Le B C)"
proof -
  {
    fix A B C M N L
    assume "\<not> Col A M N" and 
      "Per B C A" and
      "A \<noteq> C" and
      "M Midpoint A B" and
      "Per M N A" and
      "Col A C N" and
      "M Midpoint N L" 
    hence "Bet A N C \<and> Lambert N L B C \<and> Cong B L A N" 
      using t22_23_aux by blast
    have "Bet A N C" 
      using \<open>Bet A N C \<and> Lambert N L B C \<and> Cong B L A N\<close> by blast
    moreover
    have "Lambert N L B C" 
      using \<open>Bet A N C \<and> Lambert N L B C \<and> Cong B L A N\<close> by blast
    have "Cong B L A N" 
      using \<open>Bet A N C \<and> Lambert N L B C \<and> Cong B L A N\<close> by blast
    have "\<not> Obtuse L B C" 
      using \<open>Bet A N C \<and> Lambert N L B C \<and> Cong B L A N\<close> assms 
        lam_obtuse__oah_1 by blast
    have "N L OS B C"
      using \<open>Lambert N L B C\<close> by (simp add: lam__os)
    have "Lambert N C B L" 
      by (simp add: lam_perm  \<open>Lambert N L B C\<close>)
    hence "N C OS B L"
      by (simp add: lam__os)
    have "N C Le A N \<and> L N Le B C" 
    proof (cases "Acute L B C")
      case True
      have "N C Lt A N" 
      proof -
        have "N C Lt B L" 
          by (simp add: acute_lam__lt True 
              \<open>Bet A N C \<and> Lambert N L B C \<and> Cong B L A N\<close> lt_right_comm)
        moreover
        have "Cong N C N C" 
          by (simp add: cong_reflexivity)
        moreover
        have "Cong B L A N" 
          by (simp add: \<open>Cong B L A N\<close>)
        ultimately
        show ?thesis 
          using cong2_lt__lt by blast
      qed
      moreover
      have "N L Lt B C" 
      proof -
        have "Per L N C" 
          by (metis Col_def \<open>Bet A N C\<close> \<open>M Midpoint N L\<close> 
              \<open>Per M N A\<close> \<open>\<not> Col A M N\<close> between_trivial col_per2__per 
              l8_2 l8_5 midpoint_col)
        moreover
        have "Per N C B" 
          by (metis \<open>A \<noteq> C\<close> \<open>Col A C N\<close> \<open>Per B C A\<close>
              col_permutation_4 l8_2 per_col)
        moreover
        have "N C OS L B" 
          by (simp add: \<open>N C OS B L\<close> one_side_symmetry)
        moreover
        have "L B C LtA N L B"
        proof -
          have "Acute L B C" 
            by (simp add: True)
          moreover
          have "Per N L B"
            using \<open>Lambert N L B C\<close> Lambert_def by blast 
          ultimately
          show ?thesis 
            by (metis \<open>Bet A N C \<and> Lambert N L B C \<and> Cong B L A N\<close> 
                acute_per__lta lam__os os_distincts)
        qed
        ultimately
        show ?thesis 
          by (simp add: lta_os_per2__lt)
      qed
      hence "L N Lt B C" 
        by (meson lt_left_comm)
      ultimately
      show ?thesis 
        by (simp add: lt__le)
    next
      case False
      hence "Per L B C" 
        by (metis \<open>N C OS B L\<close> \<open>N L OS B C\<close> \<open>\<not> Obtuse L B C\<close> 
            angle_partition os_distincts)
      have "Cong N C B L" 
        using \<open>Lambert N L B C\<close> \<open>Per L B C\<close> cong_right_commutativity 
          lam_per__cong by blast
      hence "Cong N C A N"
        using \<open>Cong B L A N\<close> cong_transitivity by blast
      moreover
      have "Cong L N B C" 
        using \<open>Lambert N C B L\<close> \<open>Per L B C\<close> cong_commutativity 
          l8_2 lam_per__cong by blast
      ultimately
      show ?thesis 
        by (simp add: cong__le)
    qed
    ultimately
    have "Bet A N C \<and> N C Le A N \<and> L N Le B C" 
      by blast
  }
  thus ?thesis 
    by blast
qed

lemma t22_24_aux_0_a:
  assumes (*"\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" and*)
    "\<not> Col A B0 C0" and 
    "A C0 Perp B0 C0" and
    "B = GradExpn A B0 (Suc 0)" and
    "E = GradExpn B0 C0 (Suc 0)" and
    "A C0 Perp B C" and
    "Col A C0 C"
  shows "B0 E Le B C" 
proof -
  have "A \<noteq> B0" 
    using assms(1) col_trivial_1 by auto
  hence "B = B0"
    using assms(3) by simp
  have "B0 \<noteq> C0" 
    using assms(1) col_trivial_2 by fastforce
  hence "C0 = E"
    using assms(4) by simp
  thus ?thesis 
    using \<open>B = B0\<close> assms(2) assms(6) assms(5) col_trivial_2 
      l8_18_uniqueness le_reflexivity by blast
qed

lemma t22_24_aux_0:
  (* assumes "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals"*)
  shows "\<forall> A B0 C0 B C E.
  \<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and> 
  (B = GradExpn A B0 (Suc 0)) \<and> (E = GradExpn B0 C0 (Suc 0)) \<and> 
  A C0 Perp B C \<and> Col A C0 C \<longrightarrow>
  B0 E Le B C"
  using t22_24_aux_0_a by blast

lemma t22_24_aux_suc:
  assumes "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" and
    "\<forall> A B0 C0 B C E.
  \<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and>
  (B = GradExpn A B0 (Suc n)) \<and> (E = GradExpn B0 C0 (Suc n)) \<and> 
  A C0 Perp B C \<and> Col A C0 C \<longrightarrow>
  B0 E Le B C" 
  shows
    "\<forall> A B0 C0 B C E.
  \<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and>
  (B = GradExpn A B0 (Suc(Suc n))) \<and> (E = GradExpn B0 C0 (Suc(Suc n))) \<and> 
  A C0 Perp B C \<and> Col A C0 C \<longrightarrow>
  B0 E Le B C" 
proof -
  {
    fix A B0 C0 B' C' E'
    assume "\<not> Col A B0 C0" and 
      "A C0 Perp B0 C0" and
      "B' = GradExpn A B0 (Suc(Suc n))" and
      "E' = GradExpn B0 C0 (Suc(Suc n))" and
      "A C0 Perp B' C'" and
      "Col A C0 C'"
    let ?B = "GradExpn A B0 (Suc n)"
    have "Cong A ?B ?B B'" 
      using GradExpn_4 \<open>B' = GradExpn A B0 (Suc (Suc n))\<close> by presburger
    have "Bet A ?B B'" 
      using GradExpn_3 \<open>B' = GradExpn A B0 (Suc (Suc n))\<close> by blast
    have "Bet A B0 ?B" 
      using GradExpn_2 by auto
    let ?E = "GradExpn B0 C0 (Suc n)"
    have "Cong B0 ?E ?E E'" 
      using GradExpn_4 \<open>E' = GradExpn B0 C0 (Suc (Suc n))\<close> by presburger
    have "Bet B0 ?E E'" 
      using GradExpn_3 \<open>E' = GradExpn B0 C0 (Suc (Suc n))\<close> by blast
    have "\<not> Col A C0 ?B" 
      by (metis \<open>Bet A B0 (GradExpn A B0 (Suc n))\<close> \<open>\<not> Col A B0 C0\<close> 
          bet_col bet_neq12__neq colx not_col_distincts not_col_permutation_5)
    then obtain C where "Col A C0 C" and "A C0 Perp ?B C" 
      using l8_18_existence by blast
    have "B0 ?E Le ?B C" 
      using \<open>A C0 Perp B0 C0\<close> \<open>A C0 Perp (GradExpn A B0 (Suc n)) C\<close> 
        \<open>Col A C0 C\<close> \<open>\<not> Col A B0 C0\<close> assms(2) by blast
    obtain D where "?B Midpoint C D" 
      using symmetric_point_construction by blast
    have "B0 E' Le D C" 
    proof -
      have "Bet B0 ?E E'" 
        using \<open>Bet B0 (GradExpn B0 C0 (Suc n)) E'\<close> by blast
      moreover
      have "Bet D ?B C" 
        by (metis midpoint_bet  \<open>GradExpn A B0 (Suc n) Midpoint C D\<close> 
            between_symmetry)
      moreover
      have "B0 ?E Le D ?B" 
        by (meson \<open>B0 (GradExpn B0 C0 (Suc n)) Le (GradExpn A B0 (Suc n)) C\<close> 
            \<open>GradExpn A B0 (Suc n) Midpoint C D\<close> cong_pseudo_reflexivity 
            l5_6 le_right_comm midpoint_cong)
      moreover
      have "?E E' Le ?B C" 
        by (meson \<open>Cong B0 (GradExpn B0 C0 (Suc n)) (GradExpn B0 C0 (Suc n)) E'\<close> 
            \<open>GradExpn A B0 (Suc n) Midpoint C D\<close> calculation(3) 
            l5_6 l7_2 midpoint_cong)
      ultimately
      show ?thesis 
        using bet2_le2__le1346 by blast
    qed
    moreover
    {
      assume "A = C"
      have "A = C0" 
      proof -
        have "\<not> Col A C0 B0" 
          using \<open>\<not> Col A B0 C0\<close> col_permutation_5 by blast
        moreover
        have "Col A C0 A" 
          using col_trivial_3 by blast
        moreover
        have "A C0 Perp B0 A" 
        proof -
          have "A C0 Perp A ?B" 
            using \<open>A = C\<close> \<open>A C0 Perp (GradExpn A B0 (Suc n)) C\<close>
              perp_right_comm by blast
          moreover
          have "Col A ?B B0" 
            using \<open>Bet A B0 (GradExpn A B0 (Suc n))\<close> bet_col 
              not_col_permutation_5 by blast
          ultimately
          show ?thesis 
            using \<open>\<not> Col A C0 B0\<close> not_col_distincts perp_col2_bis by blast
        qed
        moreover
        have "Col A C0 C0" 
          by (simp add: col_trivial_2)
        ultimately
        show ?thesis 
          using \<open>A C0 Perp B0 C0\<close> l8_18_uniqueness by blast
      qed
      hence False 
        using \<open>\<not> Col A B0 C0\<close> col_trivial_3 by blast
    }
    hence "A \<noteq> C" 
      by auto
    {
      assume "A = C'"
      have "A = C0" 
      proof -
        have "\<not> Col A C0 B0" 
          using \<open>\<not> Col A B0 C0\<close> col_permutation_5 by blast
        moreover
        have "Col A C0 A" 
          using col_trivial_3 by blast
        moreover
        have "A C0 Perp B0 A" 
        proof -
          have "A C0 Perp A B'" 
            using \<open>A = C'\<close> \<open>A C0 Perp B' C'\<close> perp_right_comm by blast
          moreover
          have "Bet A B0 B'" 
            using \<open>B' = GradExpn A B0 (Suc(Suc n))\<close> GradExpn_2 by blast
          hence "Col A B' B0" 
            by (simp add: bet_col col_permutation_5)
          ultimately
          show ?thesis 
            using \<open>\<not> Col A C0 B0\<close> not_col_distincts perp_col2_bis by blast
        qed
        moreover
        have "Col A C0 C0" 
          by (simp add: col_trivial_2)
        ultimately
        show ?thesis 
          using \<open>A C0 Perp B0 C0\<close> l8_18_uniqueness by blast
      qed
      hence False 
        using \<open>\<not> Col A B0 C0\<close> col_trivial_3 by blast
    }
    hence "A \<noteq> C'"
      by blast
    have "Per A C ?B"  
      using \<open>Col A C0 C\<close> \<open>A C0 Perp (GradExpn A B0 (Suc n)) C\<close> 
        col_trivial_3 l8_16_1 l8_2 by blast
    have "D C Le B' C'"
    proof -
      have "\<not> Col A ?B C" 
        using NCol_perm \<open>A \<noteq> C\<close> \<open>Col A C0 C\<close> \<open>\<not> Col A C0 (GradExpn A B0 (Suc n))\<close> 
          col_transitivity_1 by blast
      moreover
      have "C' B' Perp A C0" 
        using Perp_perm \<open>A C0 Perp B' C'\<close> by blast
      hence "C' B' Perp A C'"
        using \<open>A \<noteq> C'\<close> \<open>Col A C0 C'\<close> perp_col1 by blast
      hence "B' C' Perp C' A" 
        using Perp_cases by blast
      hence "Per B' C' A" 
        using \<open>C' B' Perp A C'\<close> perp_per_1 by blast
      moreover
      have "?B Midpoint A B'" 
        using \<open>Bet A (GradExpn A B0 (Suc n)) B'\<close> 
          \<open>Cong A (GradExpn A B0 (Suc n)) (GradExpn A B0 (Suc n)) B'\<close> 
          midpoint_def by blast
      moreover
      have "Col A C' C" 
        by (metis \<open>Col A C0 C'\<close> \<open>Col A C0 C\<close> \<open>\<not> Col A B0 C0\<close> 
            col_transitivity_1 not_col_distincts)
      ultimately
      show ?thesis using t22_23 
        using \<open>A \<noteq> C'\<close> \<open>GradExpn A B0 (Suc n) Midpoint C D\<close> 
          \<open>Per A C (GradExpn A B0 (Suc n))\<close> assms(1) l8_2 by blast
    qed
    ultimately
    have "B0 E' Le B' C'" 
      using le_transitivity by blast
  }
  thus ?thesis 
    by blast
qed

lemma t22_24_aux_n:
  assumes "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals"
  shows "\<forall> A B0 C0 B C E.
  (\<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and> 
  (B = GradExpn A B0 (Suc n)) \<and> (E = GradExpn B0 C0 (Suc n)) \<and> 
  A C0 Perp B C \<and> Col A C0 C) \<longrightarrow>
  B0 E Le B C" 
proof (induction n)
  case 0
  thus ?case 
    using t22_24_aux_0 by fastforce
next
  case (Suc n)
  thus ?case 
    using assms t22_24_aux_suc by presburger
qed

(** For every n, 2^n times B0C0 is lower than or equal to BnCn *)
(** B0 is introduced twice for the induction tactic to work properly *)
lemma t22_24_aux:
  assumes "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals"
  shows "\<forall> A B0 B00 C0 B C E.
  \<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and> B0 = B00 \<and>
  GradExp2 A B0 B B00 C0 E \<and> A C0 Perp B C \<and> Col A C0 C \<longrightarrow>
  B0 E Le B C"
proof -
  {
    fix A B0 B00 C0 B C E
    assume " \<not> Col A B0 C0" and
      "A C0 Perp B0 C0" and
      "B0 = B00" and
      "GradExp2 A B0 B B00 C0 E" and
      "A C0 Perp B C" and
      "Col A C0 C"
    obtain n where "n \<noteq> 0 \<and> (B = GradExpn A B0 n) \<and> (E = GradExpn B00 C0 n)" 
      using GradExp2_def \<open>GradExp2 A B0 B B00 C0 E\<close> by presburger
    hence "n \<noteq> 0" 
      by blast
    then obtain m where "n = Suc m" 
      using not0_implies_Suc by blast
    have "B = GradExpn A B0 (Suc m)" 
      by (simp add: \<open>n = Suc m\<close> \<open>n \<noteq> 0 \<and> B = GradExpn A B0 n \<and> E = GradExpn B00 C0 n\<close>)
    moreover
    have "E = GradExpn B0 C0 (Suc m)" 
      by (simp add:  \<open>B0 = B00\<close> \<open>n = Suc m\<close> 
          \<open>n \<noteq> 0 \<and> B = GradExpn A B0 n \<and> E = GradExpn B00 C0 n\<close>)
    ultimately
    have "B0 E Le B C" 
      using \<open>A C0 Perp B C\<close> \<open>A C0 Perp B0 C0\<close> \<open>Col A C0 C\<close> 
        \<open>\<not> Col A B0 C0\<close> assms t22_24_aux_n by blast
  }
  thus ?thesis by blast
qed

lemma t22_24_aux1_0:
  shows"\<forall> A B0 C0 E. 
  (\<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and>
  E = GradExpn B0 C0 (Suc 0)) \<longrightarrow>
  (\<exists> B C. GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C)"
proof -
  {
    fix A B0 C0 E
    assume "\<not> Col A B0 C0" and
      "A C0 Perp B0 C0" and
      "E = GradExpn B0 C0 (Suc 0)"
    have "B0 \<noteq> C0" 
      using \<open>\<not> Col A B0 C0\<close> not_col_distincts by blast
    hence "E = C0" 
      using \<open>E = GradExpn B0 C0 (Suc 0)\<close> by simp
    have "A \<noteq> B0" 
      using \<open>\<not> Col A B0 C0\<close> col_trivial_1 by blast
    hence "B0 = GradExpn A B0 (Suc 0)" 
      by simp
    have "GradExp2 A B0 B0 B0 C0 E" 
      using \<open>E = C0\<close> gradexp2_init by auto
    moreover
    have "Col A C0 C0" 
      by (simp add: col_trivial_2)
    ultimately
    have "\<exists> B C. GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C" 
      using \<open>A C0 Perp B0 C0\<close> by blast
  }
  thus ?thesis 
    by blast
qed

lemma t22_24_aux1_suc:
  assumes "\<forall> A B0 C0 E. 
  (\<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and>
  E = GradExpn B0 C0 (Suc(n))) \<longrightarrow>
  (\<exists> B C. GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C)"
  shows "\<forall> A B0 C0 E. 
  (\<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and> 
  E = GradExpn B0 C0 (Suc(Suc(n)))) \<longrightarrow>
  (\<exists> B C. GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C)" 
proof -
  {
    fix A B0 C0 E'
    assume "\<not> Col A B0 C0" and
      "A C0 Perp B0 C0" and
      "E' = GradExpn B0 C0 (Suc(Suc(n)))"
    let ?E = "GradExpn B0 C0 (Suc n)"
    have "Bet B0 ?E E'" 
      using GradExpn_3 \<open>E' = GradExpn B0 C0 (Suc (Suc n))\<close> by blast
    have "Cong B0 ?E ?E E'" 
      using GradExpn_4 \<open>E' = GradExpn B0 C0 (Suc (Suc n))\<close> by blast
    obtain B C where "GradExp2 A B0 B B0 C0 ?E \<and> A C0 Perp B C \<and> Col A C0 C" 
      using \<open>A C0 Perp B0 C0\<close> \<open>\<not> Col A B0 C0\<close> assms by presburger
    have "GradExp2 A B0 B B0 C0 ?E" 
      using \<open>GradExp2 A B0 B B0 C0 ?E \<and> A C0 Perp B C \<and> Col A C0 C\<close> by blast
    hence "GradExp A B0 B" 
      by (simp add: gradexp2__gradexp123)
    hence "Grad A B0 B" 
      by (simp add: gradexp__grad)
    hence "Bet A B0 B" 
      by (simp add: grad__bet)
    have "A C0 Perp B C" 
      using \<open>GradExp2 A B0 B B0 C0 ?E \<and> A C0 Perp B C \<and> Col A C0 C\<close> by blast
    have "Col A C0 C" 
      using \<open>GradExp2 A B0 B B0 C0 ?E \<and> A C0 Perp B C \<and> Col A C0 C\<close> by blast
    obtain B' where "Bet A B B' \<and> Cong B B' A B" 
      using segment_construction by presburger
    have "Bet A B B'" 
      using \<open>Bet A B B' \<and> Cong B B' A B\<close> by blast
    have "Cong B B' A B" 
      using \<open>Bet A B B' \<and> Cong B B' A B\<close> by blast
    have "\<not> Col A C0 B'" 
      by (metis \<open>Bet A B0 B\<close> \<open>Bet A B B'\<close> \<open>\<not> Col A B0 C0\<close> 
          bet_col bet_neq12__neq col_trivial_3 colx not_col_permutation_5)
    then obtain C' where "Col A C0 C' \<and> A C0 Perp B' C'" 
      using l8_18_existence by blast
    moreover
    have "GradExp2 A B0 B' B0 C0 E'" 
    proof -
      have "GradExp2 A B0 B B0 C0 ?E" 
        using \<open>GradExp2 A B0 B B0 C0 (GradExpn B0 C0 (Suc n))\<close> by blast
      moreover
      have "Bet A B B'" 
        by (simp add: \<open>Bet A B B' \<and> Cong B B' A B\<close>)
      moreover
      have "Cong A B B B'" 
        using Cong_cases \<open>Cong B B' A B\<close> by blast
      moreover
      have "Bet B0 ?E E'" 
        using \<open>Bet B0 (GradExpn B0 C0 (Suc n)) E'\<close> by auto
      moreover
      have "Cong B0 ?E ?E E'" 
        using \<open>Cong B0 (GradExpn B0 C0 (Suc n)) (GradExpn B0 C0 (Suc n)) E'\<close> 
        by auto
      ultimately
      show ?thesis 
        using GradExp2_stab by blast
    qed
    ultimately
    have "\<exists> B C. GradExp2 A B0 B B0 C0 E' \<and> A C0 Perp B C \<and> Col A C0 C" 
      by blast
  }
  thus ?thesis 
    by blast
qed

lemma t22_24_aux1_n:
  shows "\<forall> A B0 C0 E. 
  (\<not> Col A B0 C0 \<and> A C0 Perp B0 C0 \<and>
  E = GradExpn B0 C0 (Suc(n))) \<longrightarrow>
  (\<exists> B C. GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C)"
proof (induction n)
  case 0
  thus ?case using t22_24_aux1_0 by blast
next
  case (Suc n)
  thus ?case using t22_24_aux1_suc by presburger
qed

(** For every n, it is possible to get Bn and Cn *)
lemma t22_24_aux1:
  assumes "\<not> Col A B0 C0" and
    "A C0 Perp B0 C0" and
    "GradExp B0 C0 E"
  shows "\<exists> B C. GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C" 
proof -
  obtain n where "n \<noteq> 0 \<and> E = GradExpn B0 C0 n" 
    using GradExp_def assms(3) by presburger
  hence "n \<noteq> 0"
    by simp
  then obtain m where "n = Suc m" 
    using not0_implies_Suc by presburger
  thus ?thesis 
    using t22_24_aux1_n assms(1) assms(2) \<open>n \<noteq> 0 \<and> E = GradExpn B0 C0 n\<close> by blast
qed

lemma t22_24:
  assumes "archimedes_axiom"
  shows "aristotle_s_axiom"
proof -
  {
    fix P Q D A B0
    assume "\<not> Col D A B0" and
      "Acute D A B0"
    obtain C0 where "Col A D C0" and "A D Perp B0 C0" 
      using Col_cases \<open>\<not> Col D A B0\<close> l8_18_existence by blast
    hence "A \<noteq> C0" 
      using \<open>Acute D A B0\<close> acute_col_perp__out acute_sym 
        col_trivial_3 l6_3_1 by blast
    {
      assume "Col A B0 C0"
      hence "Col C0 A B0" 
        using Col_cases by blast
      hence "Col D A B0" 
        by (metis \<open>A D Perp B0 C0\<close> \<open>Acute D A B0\<close> 
            acute_col_perp__out acute_sym col_trivial_3 l6_3_1 
            not_col_permutation_1 perp_col1)
      hence False 
        using \<open>\<not> Col D A B0\<close> by blast
    }
    hence "\<not> Col A B0 C0" 
      by blast
    have "A C0 Perp B0 C0" 
      using \<open>Col A D C0\<close> \<open>A \<noteq> C0\<close> \<open>A D Perp B0 C0\<close> perp_col by blast
    have "\<exists> X Y. A Out D X \<and> A Out B0 Y \<and> Per A X Y \<and> P Q Lt X Y" 
    proof (cases "P = Q")
      case True
      have "Acute B0 A D" 
        by (simp add: \<open>Acute D A B0\<close> acute_sym)
      hence "A Out D C0" 
        using \<open>Col A D C0\<close> \<open>A D Perp B0 C0\<close> 
          acute_col_perp__out l6_6 by blast
      moreover
      have "A Out B0 B0" 
        by (metis \<open>\<not> Col D A B0\<close> col_trivial_2 out_trivial)
      moreover
      have "Per A C0 B0" 
        by (simp add: \<open>A C0 Perp B0 C0\<close> perp_comm perp_per_2)
      moreover
      have "\<not> Cong P P C0 B0" 
        using \<open>A C0 Perp B0 C0\<close> cong_reverse_identity 
          perp_not_eq_2 by blast
      hence "P P Lt C0 B0" 
        by (metis cong_trivial_identity lt1123)
      ultimately
      show ?thesis
        using True by blast
    next
      case False
      obtain Q' where "Bet P Q Q'" and "Cong Q Q' P Q" 
        using segment_construction by blast
      have "B0 \<noteq> C0" 
        using \<open>\<not> Col A B0 C0\<close> col_trivial_2 by blast
      hence "Reach B0 C0 P Q'" 
        using archimedes_axiom_def assms by blast
      then obtain E where "GradExp B0 C0 E" and "P Q' Le B0 E" 
        using reach__ex_gradexp_le by blast
      obtain B C where "GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C" 
        using \<open>A C0 Perp B0 C0\<close> \<open>GradExp B0 C0 E\<close> \<open>\<not> Col A B0 C0\<close> 
          t22_24_aux1 by blast
      have "GradExp2 A B0 B B0 C0 E" 
        using \<open>GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C\<close> by blast
      hence "Grad A B0 B" 
        using gradexp2__gradexp123 gradexp__grad by blast
      hence "Bet A B0 B" 
        by (simp add: grad__bet)
      have "A C0 Perp B C" 
        using \<open>GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C\<close> by blast
      have "Col A C0 C" 
        using \<open>GradExp2 A B0 B B0 C0 E \<and> A C0 Perp B C \<and> Col A C0 C\<close> by blast
      have "A Out B0 B" 
        by (metis \<open>Bet A B0 B\<close> \<open>\<not> Col D A B0\<close> bet_out col_trivial_2)
      have "Acute D A B" 
        by (metis \<open>Acute D A B0\<close> \<open>Bet A B0 B\<close> \<open>\<not> Col D A B0\<close> 
            acute_col__out acute_out2__acute acute_trivial bet2__out 
            bet_neq21__neq l5_1 not_col_distincts)
      {
        assume "A = C"
        have "Per D A B" 
        proof -
          have "A C0 Perp B A" 
            using \<open>A = C\<close> \<open>A C0 Perp B C\<close> by auto
          moreover
          have "Col A C0 D" 
            using Col_cases \<open>Col A D C0\<close> by blast
          ultimately
          show ?thesis 
            by (meson col_trivial_3 l8_16_1 l8_2)
        qed
        hence False 
          using \<open>Acute D A B\<close> acute_not_per by auto
      }
      hence "A \<noteq> C" 
        by blast
      have "A Out D C" 
      proof -
        have "Acute B A D" 
          by (simp add: \<open>Acute D A B\<close> acute_sym)
        moreover
        have "Col A D C" 
          using \<open>A \<noteq> C0\<close> \<open>Col A C0 C\<close> \<open>Col A D C0\<close> col_trivial_3 
            colx by blast
        moreover
        have "A D Perp B C" 
          by (metis \<open>A C0 Perp B C\<close> \<open>Col A D C0\<close> \<open>\<not> Col D A B0\<close> 
              col_trivial_3 not_col_permutation_5 perp_col)
        ultimately
        show ?thesis 
          using acute_col_perp__out l6_6 by blast
      qed
      moreover
      have "A Out B0 B" 
        by (simp add: \<open>A Out B0 B\<close>)
      moreover
      have "Per A C B" 
        using \<open>A C0 Perp B C\<close> \<open>Col A C0 C\<close> col_trivial_3 
          l8_16_1 l8_2 by blast
      moreover
      have "P Q Lt C B" 
      proof -
        have "P Q Lt P Q'" 
          by (metis False bet__lt1213 cong_diff_3 
              \<open>Bet P Q Q'\<close> \<open>Cong Q Q' P Q\<close>)
        moreover
        have "B0 E Le B C" 
        proof -
          have "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" 
            by (simp add: archi__obtuse_case_elimination assms)
          moreover
          have "\<not> Col A B0 C0" 
            by (simp add: \<open>\<not> Col A B0 C0\<close>)
          moreover
          have "A C0 Perp B0 C0" 
            by (simp add: \<open>A C0 Perp B0 C0\<close>)
          moreover
          have "GradExp2 A B0 B B0 C0 E" 
            by (simp add: \<open>GradExp2 A B0 B B0 C0 E\<close>)
          moreover
          have "A C0 Perp B C" 
            by (simp add: \<open>A C0 Perp B C\<close>)
          moreover
          have "Col A C0 C" 
            using \<open>Col A C0 C\<close> by auto
          ultimately
          show ?thesis 
            using t22_24_aux by blast
        qed
        hence "B0 E Le C B" 
          by (simp add: le_right_comm)
        hence "P Q' Le C B" 
          using \<open>P Q' Le B0 E\<close> le_transitivity by blast
        ultimately
        show ?thesis 
          using le3456_lt__lt by blast
      qed
      ultimately
      show ?thesis 
        by blast
    qed
  }
  thus ?thesis
    by (simp add: aristotle_s_axiom_def)
qed

subsection "Equivalence Grad / GradI (inductive)"

lemma Grad1__GradI:
  shows "GradI A B (Gradn A B 1)"
proof -
  have "B = Gradn A B 1" 
    by force
  thus ?thesis 
    using gradi_init by auto
qed

lemma Gradn__GradI:
  shows "GradI A B (Gradn A B (Suc n))" 
proof (induction n)
  show "GradI A B (Gradn A B (Suc 0))" 
    by (simp add: gradi_init)
  {
    fix n
    assume "GradI A B (Gradn A B (Suc n))"
    have "GradI A B (Gradn A B (Suc (Suc n)))" 
    proof(rule GradI.induct [where ?A ="A" and ?B="B"])
      show "GradI A B (Gradn A B (Suc (Suc n)))" 
        using Bet_Gradn_Gradn_Suc Cong_Gradn_Gradn_Suc GradI.simps 
          \<open>GradI A B (Gradn A B (Suc n))\<close> by blast
      show "GradI A B B" 
        by (simp add: gradi_init)
      show "\<And>C C'. GradI A B C \<Longrightarrow> GradI A B C \<Longrightarrow> Bet A C C' \<Longrightarrow> Cong A B C C' \<Longrightarrow> GradI A B C'" 
        using gradi_stab by blast
    qed
  }
  thus "\<And>n. GradI A B (Gradn A B (Suc n)) \<Longrightarrow> GradI A B (Gradn A B (Suc (Suc n)))" 
    by blast
qed

lemma Grad__GradI:
  assumes "Grad A B C"
  shows "GradI A B C" 
proof (cases "B = C")
  case True
  thus ?thesis 
    by (simp add: gradi_init)
next
  case False
  obtain n where "n \<noteq> 0" and "C = Gradn A B n" 
    using Grad_def assms by blast
  then obtain m where "n = Suc m" 
    using not0_implies_Suc by blast
  hence "C = Gradn A B (Suc m)"
    using \<open>C = Gradn A B n\<close> by blast
  thus ?thesis 
    using Gradn__GradI by blast
qed

lemma GradIAAB__not:
  assumes "GradI A A B" 
  shows "A = B"
proof (rule GradI.induct [OF assms])
  show "A = A" 
    by blast
  show "\<And>C C'. GradI A A C \<Longrightarrow> A = C \<Longrightarrow> Bet A C C' \<Longrightarrow> Cong A A C C' \<Longrightarrow> A = C'"
    using between_cong by presburger
qed

lemma GradI__Grad:
  assumes "GradI A B C"
  shows "Grad A B C" 
proof (cases "A = B")
  case True
  hence "A = C" 
    using GradIAAB__not assms by blast
  thus ?thesis 
    using True grad_equiv_coq_1 by blast
next
  case False
  show ?thesis 
  proof (rule GradI.induct [where ?A="A" and ?B="B"])
    show "GradI A B C" 
      by (simp add: assms)
    show "Grad A B B" 
      by (simp add: grad_equiv_coq_1)
    show "\<And>C C'. GradI A B C \<Longrightarrow> Grad A B C \<Longrightarrow> Bet A C C' \<Longrightarrow> Cong A B C C' \<Longrightarrow> Grad A B C'" 
      using grad_stab by blast
  qed
qed

theorem Grad_GradI:
  shows "Grad A B C \<longleftrightarrow> GradI A B C" 
  using GradI__Grad Grad__GradI by blast

subsection "GradA"

lemma grada_distincts:
  assumes "GradA A B C D E F" 
  shows "A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E"
proof(induction rule: GradA.induct [OF assms(1)])
  show "\<And>D E F. A B C CongA D E F \<Longrightarrow> A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E" 
    by (simp add: CongA_def)
  show "\<And>D E F G H I.
       GradA A B C D E F \<Longrightarrow>
       A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E \<Longrightarrow>
       SAMS D E F A B C \<Longrightarrow>
       D E F A B C SumA G H I \<Longrightarrow> A \<noteq> B \<and> C \<noteq> B \<and> G \<noteq> H \<and> I \<noteq> H" 
    using suma_distincts by blast
qed

lemma grada_ABC:
  assumes "A \<noteq> B" and
    "B \<noteq> C"
  shows "GradA A B C A B C" 
proof -
  have "A B C CongA A B C" 
    using assms(1) assms(2) conga_refl by force
  thus ?thesis 
    using grada_init 
    by force
qed

lemma gradaexp_distincts:
  assumes "GradAExp A B C D E F" 
  shows "A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E"
proof(induction rule: GradAExp.induct [OF assms(1)])
  show "\<And>D E F. A B C CongA D E F \<Longrightarrow> A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E" 
    by (simp add: CongA_def)
  show "\<And>D E F G H I.
       GradAExp A B C D E F \<Longrightarrow>
       A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E \<Longrightarrow>
       SAMS D E F D E F \<Longrightarrow> D E F D E F SumA G H I \<Longrightarrow> A \<noteq> B \<and> C \<noteq> B \<and> G \<noteq> H \<and> I \<noteq> H"
    using suma_distincts by blast
qed

lemma gradaexp_ABC:
  assumes "A \<noteq> B" and
    "B \<noteq> C"
  shows "GradAExp A B C A B C" 
proof -
  have "A B C CongA A B C" 
    using assms(1) assms(2) conga_refl by force
  thus ?thesis 
    using gradaexp_init 
    by force
qed

lemma conga2_grada__grada_aux1: 
  assumes "GradA A B C D E F" and
    "A B C CongA A' B' C'" 
  shows "GradA A' B' C' D E F" 
proof (induction rule: GradA.cases [OF assms(1)])
  { 
    assume "A B C CongA D E F"
    hence "GradA A' B' C' D E F" 
      using grada_init 
      by (meson assms(2) not_conga not_conga_sym)
  }
  thus "\<And>Da Ea Fa.
       D = Da \<Longrightarrow>
       E = Ea \<Longrightarrow> F = Fa \<Longrightarrow> A B C CongA Da Ea Fa \<Longrightarrow> GradA A' B' C' D E F" 
    by blast
  {
    fix Da Ea Fa
    assume 1: "GradA A B C Da Ea Fa" and
      2: "SAMS Da Ea Fa A B C" and
      3: "Da Ea Fa A B C SumA D E F" 
    have "GradA A' B' C' D E F" 
    proof (rule grada_stab)
      let ?D = "Da"
      let ?E = "Ea"
      let ?F = "Fa"
      show "GradA A' B' C' ?D ?E ?F" 
      proof (rule GradA.inducts)
        show "GradA A B C Da Ea Fa" 
          by (simp add: "1")
        show "\<And>D E F. A B C CongA D E F \<Longrightarrow> GradA A' B' C' D E F" 
          by (meson conga_trans not_conga_sym assms(2) grada_init)
        {
          fix D E F G H I
          assume "GradA A B C D E F" and
            A:  "GradA A' B' C' D E F" and
            B:  "SAMS D E F A B C" and
            C:  "D E F A B C SumA G H I"
          have "GradA A' B' C' G H I"  
          proof (rule grada_stab)
            show "GradA A' B' C' D E F" 
              by (simp add: A)
            show "SAMS D E F A' B' C'" using B 
              by (meson C conga2_sams__sams assms(2) sams2_suma2__conga123)
            show "D E F A' B' C' SumA G H I" using C 
              by (meson B conga3_suma__suma sams2_suma2__conga123 suma2__conga assms(2))
          qed
        }
        thus "\<And>D E F G H I.
       GradA A B C D E F \<Longrightarrow>
       GradA A' B' C' D E F \<Longrightarrow>
       SAMS D E F A B C \<Longrightarrow>
       D E F A B C SumA G H I \<Longrightarrow> GradA A' B' C' G H I" 
          by blast
      qed
      show "SAMS ?D ?E ?F A' B' C'" using 2 
        by (meson "3" sams2_suma2__conga123 assms(2) conga2_sams__sams)
      show "?D ?E ?F A' B' C' SumA D E F" using 3 
        by (meson "2" sams2_suma2__conga123 assms(2) conga3_suma__suma suma2__conga)
    qed
  }
  thus "\<And>Da Ea Fa G H I.
       D = G \<Longrightarrow>
       E = H \<Longrightarrow>
       F = I \<Longrightarrow>
       GradA A B C Da Ea Fa \<Longrightarrow>
       SAMS Da Ea Fa A B C \<Longrightarrow>
       Da Ea Fa A B C SumA G H I \<Longrightarrow> GradA A' B' C' D E F " 
    by blast
qed

lemma conga2_grada__grada_aux2: 
  assumes "GradA A B C D E F" and
    "D E F CongA D' E' F'" 
  shows "GradA A B C D' E' F'" 
proof (induction rule: GradA.cases [OF assms(1)])
  {
    assume "A B C CongA D E F"
    hence "A B C CongA D' E' F'" 
      by (metis conga_trans assms(2))
    hence "GradA A B C D' E' F'" 
      by (simp add: grada_init)
  }
  thus "\<And>Da Ea Fa.
       D = Da \<Longrightarrow>
       E = Ea \<Longrightarrow> F = Fa \<Longrightarrow> A B C CongA Da Ea Fa \<Longrightarrow> GradA A B C D' E' F'" 
    by blast
  {
    fix Da Ea Fa
    assume 1: "GradA A B C Da Ea Fa" and
      2: "SAMS Da Ea Fa A B C" and
      3: "Da Ea Fa A B C SumA D E F"
    have  "GradA A B C D' E' F'" 
    proof (rule grada_stab)
      show "GradA A B C Da Ea Fa" 
        by (simp add: "1")
      show "SAMS Da Ea Fa A B C" 
        by (simp add: "2")
      show "Da Ea Fa A B C SumA D' E' F'" 
        by (meson "2" "3" sams2_suma2__conga123 assms(2) 
            conga3_suma__suma sams2_suma2__conga456)
    qed
  }
  thus "\<And>Da Ea Fa G H I.
       D = G \<Longrightarrow>
       E = H \<Longrightarrow>
       F = I \<Longrightarrow>
       GradA A B C Da Ea Fa \<Longrightarrow>
       SAMS Da Ea Fa A B C \<Longrightarrow>
       Da Ea Fa A B C SumA G H I \<Longrightarrow> GradA A B C D' E' F'" 
    by blast
qed

lemma conga2_grada__grada: 
  assumes "GradA A B C D E F" and
    "A B C CongA A' B' C'" and
    "D E F CongA D' E' F'"
  shows "GradA A' B' C' D' E' F'" 
  using assms(1) assms(2) assms(3) 
    conga2_grada__grada_aux1 conga2_grada__grada_aux2 by blast

lemma grada__lea:
  assumes "GradA A B C D E F"
  shows "A B C LeA D E F" 
proof (induction rule: GradA.cases [OF assms(1)])
  case (1 D E F)
  then show ?case 
    by (simp add: conga__lea)
next
  case (2 D E F G H I)
  thus ?case 
    by (metis sams_suma__lea456789)
qed

lemma grada_out__out:
  assumes "E Out D F" and 
    "GradA A B C D E F" 
  shows "B Out A C" 
proof (induction rule: GradA.cases [OF assms(2)])
  case (1 D E F)
  then show ?case 
    by (metis not_conga_sym assms(1) l11_21_a)
next
  case (2 D E F G H I)
  then show ?case 
    by (metis sams_suma__lea456789 assms(1) out_lea__out)
qed

lemma grada2_sams_suma__grada_aux:
  shows "\<forall> A B C D E F G H I K L M. 
              GradA A B C D E F \<and> GradA A B C G H I \<and> 
              SAMS D E F G H I \<and> D E F G H I SumA K L M \<longrightarrow> GradA A B C K L M"
proof -
  {
    fix A B C D E F G' H' I' K L M
    assume K1: "GradA A B C D E F" and
      K2: "GradA A B C G' H' I'" 
    have "\<forall> K L M. (SAMS D E F G' H' I' \<and> D E F G' H' I' SumA K L M) \<longrightarrow> GradA A B C K L M" 
    proof(induction rule: GradA.induct [OF K2])
      {
        fix Da Ea Fa
        assume "A B C CongA Da Ea Fa"
        {
          fix K L M
          assume "SAMS D E F Da Ea Fa" and "D E F Da Ea Fa SumA K L M"
          have "SAMS D E F A B C" 
            by (meson conga2_sams__sams not_conga_sym sams2_suma2__conga123 
                \<open>A B C CongA Da Ea Fa\<close> \<open>D E F Da Ea Fa SumA K L M\<close> \<open>SAMS D E F Da Ea Fa\<close>)
          moreover have "D E F A B C SumA K L M" 
            by (meson conga3_suma__suma not_conga_sym sams2_suma2__conga123 
                \<open>A B C CongA Da Ea Fa\<close> \<open>D E F Da Ea Fa SumA K L M\<close> \<open>SAMS D E F Da Ea Fa\<close> 
                suma2__conga)
          ultimately have "GradA A B C K L M" 
            using K1 grada_stab by blast
        }
        hence "\<forall>K L M. (SAMS D E F Da Ea Fa \<and> D E F Da Ea Fa SumA K L M) \<longrightarrow> GradA A B C K L M" 
          by blast
      }
      thus "\<And>Da Ea Fa.
       A B C CongA Da Ea Fa \<Longrightarrow>
       \<forall>K L M. (SAMS D E F Da Ea Fa \<and> D E F Da Ea Fa SumA K L M) \<longrightarrow> GradA A B C K L M" 
        by blast
      {
        fix G H I 
        {
          fix Da Ea Fa
          assume "GradA A B C Da Ea Fa" and
            "SAMS Da Ea Fa A B C" and
            "Da Ea Fa A B C SumA G H I" and
            P1: "\<forall>K L M. SAMS D E F Da Ea Fa \<and> D E F Da Ea Fa SumA K L M \<longrightarrow> GradA A B C K L M"
          {
            fix K0 L0 M0
            assume "SAMS D E F G H I" and
              "D E F G H I SumA K0 L0 M0"
            have "Da \<noteq> Ea" 
              using \<open>SAMS Da Ea Fa A B C\<close> sams_distincts by auto
            have "Fa \<noteq> Ea" 
              using \<open>GradA A B C Da Ea Fa\<close> grada_distincts by blast
            have "D \<noteq> E" 
              using \<open>SAMS D E F G H I\<close> sams_distincts by blast
            have "E \<noteq> F" 
              using \<open>SAMS D E F G H I\<close> sams_distincts by blast
            obtain K L M where "D E F Da Ea Fa SumA K L M" 
              using ex_suma \<open>D \<noteq> E\<close> \<open>Da \<noteq> Ea\<close> \<open>E \<noteq> F\<close> \<open>Fa \<noteq> Ea\<close> by presburger
            have "SAMS D E F Da Ea Fa" 
            proof (rule sams_lea2__sams [where ?A'="D" and ?B'="E" and ?C'="F" and
                  ?D'="G" and ?E'="H" and ?F'="I"]) 
              show "SAMS D E F G H I" 
                using \<open>SAMS D E F G H I\<close> by blast
              show "D E F LeA D E F" 
                using \<open>D \<noteq> E\<close> \<open>E \<noteq> F\<close> lea_refl by force
              show "Da Ea Fa LeA G H I"
              proof (rule sams_suma__lea123789 [where ?D="A" and ?E="B" and ?F="C"])
                show "Da Ea Fa A B C SumA G H I" 
                  using \<open>Da Ea Fa A B C SumA G H I\<close> by blast
                show "SAMS Da Ea Fa A B C"
                  by (simp add: \<open>SAMS Da Ea Fa A B C\<close>)
              qed
            qed
            have "GradA A B C K0 L0 M0" 
            proof (rule grada_stab [where ?D = "K" and ?E = "L" and ?F = "M"])
              show "GradA A B C K L M" 
                using P1 \<open>D E F Da Ea Fa SumA K L M\<close> \<open>SAMS D E F Da Ea Fa\<close> by blast
              show "SAMS K L M A B C" 
                using sams_assoc_2 [where ?A="D" and ?B="E" and ?C="F" and
                    ?D="Da" and ?E="Ea" and ?F="Fa" and ?D'="G" and ?E'="H" and ?F'="I"] 
                using \<open>D E F Da Ea Fa SumA K L M\<close> \<open>Da Ea Fa A B C SumA G H I\<close> 
                  \<open>SAMS D E F Da Ea Fa\<close> \<open>SAMS D E F G H I\<close> \<open>SAMS Da Ea Fa A B C\<close> by blast
              show "K L M A B C SumA K0 L0 M0" 
                by (meson suma_assoc_2 \<open>D E F Da Ea Fa SumA K L M\<close> 
                    \<open>D E F G H I SumA K0 L0 M0\<close> \<open>Da Ea Fa A B C SumA G H I\<close> \<open>SAMS D E F Da Ea Fa\<close> 
                    \<open>SAMS Da Ea Fa A B C\<close>)
            qed
          }
          hence "\<forall>K L M. SAMS D E F G H I \<and> D E F G H I SumA K L M \<longrightarrow> GradA A B C K L M" 
            by blast
        }
        hence "\<And> Da Ea Fa. GradA A B C Da Ea Fa \<and> SAMS Da Ea Fa A B C \<and>
                            Da Ea Fa A B C SumA G H I \<and>
     (\<forall>K L M. SAMS D E F Da Ea Fa \<and> D E F Da Ea Fa SumA K L M \<longrightarrow> GradA A B C K L M) \<longrightarrow>
     (\<forall>K L M. SAMS D E F G H I \<and> D E F G H I SumA K L M \<longrightarrow> GradA A B C K L M)" 
          by blast
      }
     thus "\<And>Da Ea Fa G H I.
       GradA A B C Da Ea Fa \<Longrightarrow>
       (\<forall>K L M. SAMS D E F Da Ea Fa \<and> D E F Da Ea Fa SumA K L M \<longrightarrow> GradA A B C K L M) \<Longrightarrow>
       SAMS Da Ea Fa A B C \<Longrightarrow>
       Da Ea Fa A B C SumA G H I \<Longrightarrow>
       (\<forall>K L M. SAMS D E F G H I \<and> D E F G H I SumA K L M \<longrightarrow> GradA A B C K L M)" 
        by blast
    qed
  }
  thus ?thesis by blast
qed

lemma grada2_sams_suma__grada:
  assumes "GradA A B C D E F" and
    "GradA A B C G H I" and
    "SAMS D E F G H I" and 
    "D E F G H I SumA K L M"
  shows "GradA A B C K L M" 
  using assms(1) assms(2) assms(3) assms(4) grada2_sams_suma__grada_aux by blast

lemma gradaexp__grada:
  assumes "GradAExp A B C D E F"
  shows "GradA A B C D E F" 
proof (rule GradAExp.induct [OF assms])
  show "\<And>D E F. A B C CongA D E F \<Longrightarrow> GradA A B C D E F" 
    by (simp add: grada_init)
  show " \<And>D E F G H I.
       GradAExp A B C D E F \<Longrightarrow>
       GradA A B C D E F \<Longrightarrow> SAMS D E F D E F \<Longrightarrow> D E F D E F SumA G H I \<Longrightarrow> GradA A B C G H I" 
    using grada2_sams_suma__grada_aux by blast
qed

lemma acute_archi_aux:
  assumes "Per PO A B" and
    "PO \<noteq> A" and
    "B \<noteq> A" and
    "C \<noteq> D" and
    "D \<noteq> E" and
    "Bet A C D" and
    "Bet C D E" and
    "Bet D E B" and
    "C PO D CongA D PO E"
  shows "C D Lt D E"
proof -
  have "D \<noteq> A" 
    using assms(4) assms(6) between_identity by blast
  have "C \<noteq> PO" 
    using assms(9) conga_diff1 by auto
  have "D \<noteq> PO" 
    using assms(9) conga_diff45 by blast
  have "\<not> Col PO A B" 
    by (metis assms(1) assms(2) assms(3) l8_8 not_col_permutation_2 per_col)
  hence "\<not> Col PO A D" 
    by (metis Col_def \<open>D \<noteq> A\<close> assms(4) assms(5) assms(6) assms(7) assms(8) l6_16_1)
  have "\<not> Col PO D E" 
    by (metis Col_def \<open>\<not> Col PO A D\<close> assms(4) assms(5) assms(6) assms(7) l6_16_1)
  then obtain P where "A D PO CongA PO D P" and "PO D OS P E" 
    using \<open>\<not> Col PO A D\<close> angle_construction_1 not_col_permutation_1 by blast
  have "Acute A D PO" 
    by (metis \<open>D \<noteq> A\<close> assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) 
        assms(8) bet_col1 between_trivial l11_43 outer_transitivity_between per_col)
  hence "Acute A D PO \<longleftrightarrow> A D PO LtA E D PO" 
    by (metis acute_chara_1 assms(4) assms(5) assms(6) assms(7) outer_transitivity_between2)
  have "A D PO LeA E D PO" 
    by (metis lta__lea outer_transitivity_between2 \<open>Acute A D PO\<close> acute_chara_1 
        assms(4) assms(5) assms(6) assms(7))
  hence "PO D P LeA PO D E" 
    by (meson lea_right_comm lea_trans \<open>A D PO CongA PO D P\<close> conga__lea456123)
  hence "P InAngle PO D E" 
    using \<open>PO D OS P E\<close> lea_in_angle one_side_symmetry by presburger
  have "P \<noteq> D" 
    using \<open>PO D OS P E\<close> os_distincts by blast
  obtain F where "Bet PO F E" and "D Out F P" 
    using InAngle_def \<open>P InAngle PO D E\<close> \<open>\<not> Col PO D E\<close> bet_col by auto
  have "A D PO CongA PO D F" 
    by (metis out2__conga \<open>A D PO CongA PO D P\<close> \<open>D Out F P\<close> \<open>D \<noteq> PO\<close> 
        bet_out_1 conga_trans not_bet_distincts)
  have "D Out A C" 
    by (simp add: assms(4) assms(6) bet_out_1 l6_6)
  have "D Out PO PO" 
    using \<open>D \<noteq> PO\<close> out_trivial by auto
  have "PO D C CongA A D PO"
    by (simp add: out2__conga \<open>D Out A C\<close> \<open>D Out PO PO\<close> conga_left_comm)
  have "\<not> Col PO D F" 
    using \<open>D Out F P\<close> \<open>D Out PO PO\<close> \<open>PO D OS P E\<close> col_out2_col col_trivial_3 l9_19 by blast
  have "PO \<noteq> F" 
    using \<open>\<not> Col PO D F\<close> col_trivial_3 by auto
  have "\<not> Col PO D C" 
    using \<open>\<not> Col PO A D\<close> assms(4) assms(6) bet_col col2__eq col_permutation_5 by blast
  have "PO Out D D" 
    by (simp add: \<open>D \<noteq> PO\<close> out_trivial)
  have "PO Out C C" 
    by (simp add: \<open>C \<noteq> PO\<close> out_trivial)
  have "PO Out F E" 
    using \<open>Bet PO F E\<close> \<open>PO \<noteq> F\<close> bet_out by auto
  hence "D PO C CongA D PO F" 
    using l11_10 \<open>PO Out C C\<close> \<open>PO Out D D\<close> assms(9) conga_left_comm by blast
  have "PO D C CongA PO D F" 
    by (meson conga_trans \<open>A D PO CongA PO D F\<close> \<open>PO D C CongA A D PO\<close>)
  have "Cong PO D PO D" 
    by (simp add: cong_reflexivity)
  have "Cong PO C PO F \<and> Cong D C D F \<and> PO C D CongA PO F D" 
    using l11_50_1 \<open>Cong PO D PO D\<close> \<open>D PO C CongA D PO F\<close> \<open>PO D C CongA PO D F\<close>
      \<open>\<not> Col PO D C\<close> by blast
  hence "Cong D F C D" 
    using not_cong_4312 by blast
  moreover
  {
    assume "Col E D F"
    {
      assume "E = F"
      have "D \<noteq> C" 
        using assms(4) by auto
      moreover have "Per PO D C" 
        using \<open>E = F\<close> \<open>PO D C CongA PO D F\<close> assms(7) l11_18_2 by auto
      moreover have "Col D C A" 
        using \<open>D Out A C\<close> not_col_permutation_5 out_col by blast
      ultimately have "Per A D PO" 
        by (meson l11_17 \<open>PO D C CongA A D PO\<close>)
      hence False 
        using acute_not_per \<open>Acute A D PO\<close> by blast
    }
    moreover
    {
      assume "E \<noteq> F" 
      hence False
        by (metis col_permutation_1 \<open>Bet PO F E\<close> \<open>Col E D F\<close> \<open>\<not> Col PO D F\<close> bet_col col2__eq)
    }
    ultimately have False 
      by blast
  }
  hence "\<not> Col E D F" 
    by blast
  have "E \<noteq> F" 
    using \<open>\<not> Col E D F\<close> not_col_distincts by blast
  have "D E F LtA D F E" 
  proof (rule lta_trans [where ?A1.0 = "F" and ?B1.0 = "D" and ?C1.0 = "PO"])
    have "D PO E LtA PO D C \<and> D E PO LtA PO D C" 
      by (metis l11_41 not_col_permutation_1 one_side_not_col124 
          \<open>\<And>thesis. (\<And>P. \<lbrakk>A D PO CongA PO D P; PO D OS P E\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
          assms(4) assms(7) between_symmetry)
    show "D E F LtA F D PO" 
    proof -
      have "D E PO CongA D E F" 
        by (metis bet_out_1 out2__conga \<open>Bet PO F E\<close> \<open>E \<noteq> F\<close> assms(5) out_trivial)
      moreover have "PO D C CongA F D PO" 
        by (simp add: \<open>PO D C CongA PO D F\<close> conga_right_comm)
      ultimately show ?thesis
        by (simp add: conga_preserves_lta \<open>D PO E LtA PO D C \<and> D E PO LtA PO D C\<close>)
    qed
    show "F D PO LtA D F E"     
      by (metis bet_col col_lta__bet l11_41_aux not_col_permutation_2 
          \<open>Bet PO F E\<close> \<open>D PO E LtA PO D C \<and> D E PO LtA PO D C\<close> \<open>E \<noteq> F\<close> \<open>PO D C CongA A D PO\<close> 
          \<open>PO D C CongA PO D F\<close> 
          \<open>\<And>thesis. (\<And>P. \<lbrakk>A D PO CongA PO D P; PO D OS P E\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
          bet_conga__bet col123__nos ncol_conga_ncol)
  qed
  hence "D F Lt D E" 
    using l11_44_2_b by blast
  ultimately show ?thesis 
    using cong2_lt__lt 
    using cong_reflexivity by blast
qed

lemma acute_archi_aux1:
  assumes "Per PO A0 B" and
    "B \<noteq> A0" and
    "Bet A0 A1 B" and
    "GradA A0 PO A1 P Q R" and
    "A0 \<noteq> A1" 
  shows "A0 PO B LeA P Q R \<or> (\<exists> A. Bet A0 A1 A \<and> Bet A0 A B \<and> P Q R CongA A0 PO A)" 
proof -
  have "A0 \<noteq> PO" 
    using assms(4) grada_distincts by auto
  have "A1 \<noteq> PO"  
    using assms(4) grada_distincts by auto
  have "P \<noteq> Q" 
    using assms(4) grada_distincts by auto
  have "R \<noteq> Q" 
    using assms(4) grada_distincts by auto
  have "\<not> Col PO A0 B" 
    by (metis per_not_col \<open>A0 \<noteq> PO\<close> assms(1) assms(2))
  have "PO \<noteq> B" 
    using assms(1) assms(2) per_distinct_1 by blast
  {
    assume "P Q R LeA A0 PO B"
    {
      assume "Col P Q R" 
      {
        assume "Q Out P R"
        hence "PO Out A0 A1"
          using grada_out__out [where ?D = "P" and ?E = "Q" and ?F = "R"] assms(4) by blast
        hence False 
          using \<open>\<not> Col PO A0 B\<close> assms(3) assms(4) assms(5) bet_col col_trivial_2 
            colx out_col by blast
      }
      hence "\<not> Q Out P R" 
        by blast
      hence "Bet P Q R" 
        using \<open>Col P Q R\<close> not_out_bet by blast
      hence "Bet A0 PO B" 
        using \<open>P Q R LeA A0 PO B\<close> bet_lea__bet [where ?A = "P" and ?B = "Q" and ?C = "R"]
        by blast
      hence False 
        using \<open>\<not> Col PO A0 B\<close> bet_col not_col_permutation_4 by blast
    }
    hence "\<not> Col P Q R" 
      by blast
    then obtain C where "P Q R CongA A0 PO C" and "A0 PO OS C B" 
      by (metis NCol_cases \<open>\<not> Col PO A0 B\<close> angle_construction_1)
    have "C InAngle A0 PO B" 
    proof (rule lea_in_angle)
      have "A0 PO B CongA A0 PO B" 
        using \<open>A0 \<noteq> PO\<close> \<open>PO \<noteq> B\<close> conga_refl by auto
      thus "A0 PO C LeA A0 PO B" 
        using l11_30 [where ?A="P" and ?B="Q" and ?C="R" and ?D="A0" and ?E="PO" and ?F="B"]
          \<open>P Q R LeA A0 PO B\<close> \<open>P Q R CongA A0 PO C\<close> by blast
      show "A0 PO OS B C" 
        by (simp add: \<open>A0 PO OS C B\<close> one_side_symmetry)
    qed
    have "C \<noteq> PO" 
      using \<open>A0 PO OS C B\<close> os_distincts by blast
    obtain A where "Bet A0 A B" and "A = PO \<or> PO Out A C" 
      using InAngle_def \<open>C InAngle A0 PO B\<close> by blast
    hence "PO Out A C" 
      using Bet_cases Col_def \<open>\<not> Col PO A0 B\<close> by blast
    have "P Q R CongA A0 PO A" 
    proof (rule l11_10 [where ?A ="P" and ?C="R" and ?D="A0" and ?F="C"],
        insert \<open>P Q R CongA A0 PO C\<close> \<open>PO Out A C\<close>) 
      show "Q Out P P" 
        by (simp add: \<open>P \<noteq> Q\<close> out_trivial)
      show "Q Out R R" 
        using \<open>R \<noteq> Q\<close> out_trivial by auto
      show "PO Out A0 A0" 
        by (simp add: \<open>A0 \<noteq> PO\<close> out_trivial)
    qed
    have "Bet A0 A1 A" 
    proof (cases "A0 = A1")
      case True
      thus ?thesis
        using assms(5) by auto
    next
      case False
      hence "\<not> Col A0 PO A" 
        by (metis Col_perm \<open>A0 PO OS C B\<close> \<open>PO Out A C\<close> l6_16_1 
            one_side_not_col123 out_col out_distinct)
      have "A1 InAngle A0 PO A" 
      proof (rule lea_in_angle)
        show "A0 PO A1 LeA A0 PO A"
        proof (rule l11_30 [where ?A="A0" and ?B="PO" and ?C="A1" and ?D="P" and ?E="Q" and ?F="R"])
          show "A0 PO A1 LeA P Q R" 
            by (simp add: assms(4) grada__lea)
          show "A0 PO A1 CongA A0 PO A1" 
            by (simp add: \<open>A0 \<noteq> PO\<close> \<open>A1 \<noteq> PO\<close> conga_refl)
          show "P Q R CongA A0 PO A"
            by (simp add: \<open>P Q R CongA A0 PO A\<close>)
        qed
        show "A0 PO OS A A1"
          using False \<open>Bet A0 A B\<close> \<open>\<not> Col A0 PO A\<close> assms(3) bet2__out 
            not_col_distincts out_one_side by presburger
      qed
      obtain X where "Bet A0 X A" and "X = PO \<or> PO Out X A1" 
        using InAngle_def \<open>A1 InAngle A0 PO A\<close> by blast
      hence "PO Out X A1" 
        using \<open>\<not> Col A0 PO A\<close> bet_col by blast
      have "X = A1 \<longrightarrow> Bet A0 A1 A" 
        using \<open>Bet A0 X A\<close> by blast
      moreover
      have "X \<noteq> A1 \<longrightarrow> Bet A0 A1 A" 
        by (meson \<open>Bet A0 A B\<close> \<open>Bet A0 X A\<close> \<open>PO Out X A1\<close> \<open>\<not> Col A0 PO A\<close> 
            assms(3) bet_col bet_col1 col_permutation_2 colx out_col)
      ultimately
      show ?thesis 
        by blast
    qed
    moreover have "Bet A0 A B" 
      by (simp add: \<open>Bet A0 A B\<close>)
    ultimately have  "A0 PO B LeA P Q R \<or> (\<exists> A. Bet A0 A1 A \<and> Bet A0 A B \<and> P Q R CongA A0 PO A)" 
      using \<open>P Q R CongA A0 PO A\<close> by blast
  }
  thus ?thesis 
    by (metis \<open>A0 \<noteq> PO\<close> \<open>P \<noteq> Q\<close> \<open>PO \<noteq> B\<close> \<open>R \<noteq> Q\<close> lea_total)
qed


lemma acute_archi_aux2_1_a:
  assumes "Per PO A0 B" and
    "PO \<noteq> A0" and
    "B \<noteq> A0" and
    "Bet A0 A1 B" and
    "A0 \<noteq> A1" and "\<not> Col PO A0 B" and "\<not> Col A0 PO A1" and "PO \<noteq> A1" and "PO \<noteq> B"
  shows "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
                  (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 A1 Le A0 A' \<and>
                  (\<exists> A. Bet A0 A A' \<and> A0 PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
proof -
  let ?P = "A0"
  let ?Q = "PO"
  let ?R = "A1"
  have "(GradA A0 PO A1 ?P ?Q ?R \<and> (A0 PO B LeA ?P ?Q ?R \<or>
                  (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> ?P ?Q ?R CongA A0 PO A' \<and> A0 A1 Le A0 A' \<and>
                  (\<exists> A. Bet A0 A A' \<and> A0 PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
    by (metis assms(2) assms(4) assms(8) bet__le1213 conga_refl grada_init not_bet_distincts)
  thus ?thesis by blast
qed

lemma acute_archi_aux2_1:
  assumes "Per PO A B" and
    "PO \<noteq> A" and
    "B \<noteq> A" and
    "Bet A B0 B" and
    "A \<noteq> B0" and "\<not> Col PO A B" and "\<not> Col A PO B0" and "PO \<noteq> B0" and "PO \<noteq> B"
  shows "\<exists> P Q R. (GradA A PO B0 P Q R \<and> (A PO B LeA P Q R \<or>
                  (\<exists> A'. Bet A B0 A' \<and> Bet A A' B \<and> P Q R CongA A PO A' \<and> A B0 Le A A' \<and>
                  (\<exists> A0. Bet A A0 A' \<and> A0 PO A' CongA A PO B0 \<and> A B0 Le A0 A'))))" 
proof -
  let ?A0 = "A"
  let ?A1 = "B0"
  have "\<exists> P Q R. (GradA ?A0 PO ?A1 P Q R \<and> (?A0 PO B LeA P Q R \<or>
                  (\<exists> A'. Bet ?A0 ?A1 A' \<and> Bet ?A0 A' B \<and> P Q R CongA ?A0 PO A' \<and> 
                         ?A0 ?A1 Le ?A0 A' \<and>
                  (\<exists> A. Bet ?A0 A A' \<and> ?A0 PO A' CongA ?A0 PO ?A1 \<and> ?A0 ?A1 Le A A'))))" 
    using acute_archi_aux2_1_a assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) 
      assms(8) assms(9) by blast
  thus ?thesis 
    by (metis not_bet_distincts)
qed

lemma acute_archi_aux2_2:
  assumes "Per PO A0 B" and
    "PO \<noteq> A0" and
    "B \<noteq> A0" and
    "Bet A0 A1 B" and
    "A0 \<noteq> A1" and
    "Grad A0 A1 C" and
    "Bet A0 C C'" and
    "Cong A0 A1 C C'" and
    "\<not> Col PO A0 B" and
    "\<not> Col A0 PO A1" and
    "PO \<noteq> A1" and
    "PO \<noteq> B" and
    "Per PO A0 B \<and> PO \<noteq> A0 \<and>
       B \<noteq> A0 \<and> Bet A0 A1 B \<and>
       A0 \<noteq> A1 \<and>
       \<not> Col PO A0 B \<and>
       \<not> Col A0 PO A1 \<and>
       PO \<noteq> A1 \<longrightarrow> (\<exists> P Q R.
         (GradA A0 PO A1 P Q R \<and>
         (A0 PO B LeA P Q R \<or>
          (\<exists> A'.
             Bet A0 A1 A' \<and>
             Bet A0 A' B \<and>
             P Q R CongA A0 PO A' \<and>
             A0 C Le A0 A' \<and> (\<exists> A. ( Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))))"
  shows "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> 
(A0 PO B LeA P Q R \<or>
(\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C' Le A0 A' \<and>
                     (\<exists> A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
proof -
  have "\<exists> P Q R.
         (GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
          (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and>
             A0 C Le A0 A' \<and> (\<exists> A. ( Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A')))))"
    using assms(13) assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) 
      assms(5) assms(9) by blast
  then obtain P Q R where "GradA A0 PO A1 P Q R" and
    P2:  "A0 PO B LeA P Q R \<or>
          (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C Le A0 A' \<and> 
             (\<exists> A. ( Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A')))"
    by blast
  {
    assume "A0 PO B LeA P Q R" 
    hence "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
               (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C' Le A0 A' \<and>
                     (\<exists> A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
      using \<open>GradA A0 PO A1 P Q R\<close> by blast
  }
  moreover
  {
    assume "\<not> A0 PO B LeA P Q R" 
    assume "\<exists> A'.
             Bet A0 A1 A' \<and>
             Bet A0 A' B \<and>
             P Q R CongA A0 PO A' \<and>
             A0 C Le A0 A' \<and> (\<exists> A. ( Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))"
    then obtain A' where "Bet A0 A1 A'" and
      "Bet A0 A' B" and
      "P Q R CongA A0 PO A'" and
      "A0 C Le A0 A'" and 
      P3: "(\<exists> A. ( Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))"
      by blast
    then obtain A where "Bet A0 A A'" and "A PO A' CongA A0 PO A1" and "A0 A1 Le A A'"
      by blast
    have "SAMS P Q R A0 PO A1" 
    proof (rule sams_lea2__sams [where ?A'="A0" and ?B'="PO" and ?C'="B" and 
          ?D'="A0" and ?E'="PO" and ?F'="B"])
      show "SAMS A0 PO B A0 PO B" 
        by (metis acute_chara_1 lea_right_comm lta__lea assms(1) assms(2) assms(3) l11_43 
            point_construction_different sams_chara)
      show "P Q R LeA A0 PO B"
      proof (rule l11_30 [where ?A="A0" and ?B="PO" and ?C="A'" and 
            ?D="A0" and ?E="PO" and ?F="B"])
        have "A' InAngle A0 PO B" 
          by (metis InAngle_def Out_def \<open>A PO A' CongA A0 PO A1\<close> 
              \<open>Bet A0 A' B\<close> assms(12) assms(2) between_trivial conga_diff2)
        thus "A0 PO A' LeA A0 PO B" 
          using inangle__lea by force
        show "A0 PO A' CongA P Q R" 
          using \<open>P Q R CongA A0 PO A'\<close> conga_sym_equiv by auto
        show "A0 PO B CongA A0 PO B" 
          using assms(12) assms(2) conga_refl by force
      qed
      have "A1 InAngle A0 PO B" 
        using InAngle_def assms(11) assms(12) assms(2) assms(4) out_trivial by auto
      thus "A0 PO A1 LeA A0 PO B" 
        by (simp add: inangle__lea)
    qed
    have "A0 \<noteq> A'" 
      using \<open>Bet A0 A1 A'\<close> assms(5) between_identity by blast
    have "A \<noteq> A'" 
      using Le_def \<open>A0 A1 Le A A'\<close> assms(5) between_identity cong_identity_inv by blast
    have "PO \<noteq> A" 
      using \<open>A PO A' CongA A0 PO A1\<close> conga_diff1 by blast
    have "P \<noteq> Q" 
      using \<open>P Q R CongA A0 PO A'\<close> conga_diff1 by blast
    have "PO \<noteq> A'" 
      using P3 conga_diff2 by blast
    have "Q \<noteq> R" 
      using \<open>P Q R CongA A0 PO A'\<close> conga_diff2 by blast
    then obtain P' Q' R' where "P Q R A0 PO A1 SumA P' Q' R'" 
      using ex_suma \<open>P \<noteq> Q\<close> assms(11) assms(2) by fastforce
    have "GradA A0 PO A1 P' Q' R'" 
      using grada_stab [where ?D="P" and ?E="Q" and ?F="R"]
        \<open>GradA A0 PO A1 P Q R\<close> \<open>SAMS P Q R A0 PO A1\<close> \<open>P Q R A0 PO A1 SumA P' Q' R'\<close> by blast
    moreover
    have "A0 PO B LeA P' Q' R' \<or> (\<exists> A. Bet A0 A1 A \<and> Bet A0 A B \<and> P' Q' R' CongA A0 PO A)"
      using acute_archi_aux1 assms(1) assms(3) assms(4) assms(5) calculation by blast 
    moreover
    {
      assume "A0 PO B LeA P' Q' R'"
      hence "GradA A0 PO A1 P' Q' R'" 
        using calculation by auto
      hence "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> 
(A0 PO B LeA P Q R \<or>
(\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C' Le A0 A' \<and>
                     (\<exists> A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
        using \<open>A0 PO B LeA P' Q' R'\<close> by blast
    }
    moreover
    {
      assume "\<exists> A. Bet A0 A1 A \<and> Bet A0 A B \<and> P' Q' R' CongA A0 PO A"
      then obtain A'' where "Bet A0 A1 A''" and "Bet A0 A'' B" and "P' Q' R' CongA A0 PO A''" 
        by blast
      have "\<not> Col A PO A'" 
        by (meson \<open>A \<noteq> A'\<close> \<open>Bet A0 A A'\<close> \<open>Bet A0 A' B\<close> \<open>Bet A0 A1 A'\<close> assms(10) assms(4) 
            bet_col1 colx not_col_permutation_5)
      have "\<not> Col A0 PO A'" 
        by (meson \<open>A0 \<noteq> A'\<close> \<open>Bet A0 A' B\<close> assms(10) assms(4) bet_col1 col_trivial_3 colx)
      {
        assume "Col A' PO A''" 
        have "A' \<noteq> A'' \<longrightarrow> False" 
          by (meson \<open>Bet A0 A1 A''\<close> \<open>Bet A0 A1 A'\<close> \<open>Col A' PO A''\<close> assms(10) 
              bet_col col_permutation_5 colx)
        moreover
        {
          assume "A' = A''"
          have "A0 PO A' A0 PO A1 SumA A0 PO A'" 
            using conga3_suma__suma [where ?A="P" and ?B="Q" and ?C="R" and
                ?D="A0" and ?E="PO" and ?F="A1" and ?G="P'" and ?H="Q'" and ?I="R'"]
            using \<open>A' = A''\<close> \<open>P Q R A0 PO A1 SumA P' Q' R'\<close> \<open>P Q R CongA A0 PO A'\<close> 
              \<open>P' Q' R' CongA A0 PO A''\<close> assms(11) assms(2) conga_refl by force
          have "\<not> Col A0 PO A''" 
            using \<open>A' = A''\<close> \<open>\<not> Col A0 PO A'\<close> by auto
          have "Bet A0 A' A''" 
            by (simp add: \<open>A' = A''\<close> between_trivial)
          have "SAMS A0 PO A' A0 PO A1" 
            using conga2_sams__sams [where ?A="P" and ?B="Q" and ?C="R" and
                ?D="A0" and ?E="PO" and ?F="A1"] 
            using \<open>P Q R CongA A0 PO A'\<close> \<open>SAMS P Q R A0 PO A1\<close> assms(11) assms(2) 
              conga_refl by presburger
          hence "Col A0 PO A1"
            using sams_suma__out546
            by (meson not_col_permutation_4 \<open>A0 PO A' A0 PO A1 SumA A0 PO A'\<close> out_col)
          hence False 
            using assms(10) by blast
        }
        ultimately have False 
          by blast
      }
      hence "\<not> Col A' PO A''" 
        by blast
      have "\<not> Col A0 PO A''" 
        by (metis \<open>Bet A0 A'' B\<close> \<open>Bet A0 A1 A''\<close> assms(10) assms(4) bet_col1 
            between_identity colx not_col_distincts)
      have "Bet A0 A' A''" 
      proof (rule col_two_sides_bet [where ?B="PO"])
        show "Col A' A0 A''" 
          using \<open>Bet A0 A' B\<close> \<open>Bet A0 A'' B\<close> bet_col1 not_col_permutation_1 by blast
        have "A' InAngle A0 PO A''" 
        proof (rule lea_in_angle)
          show "A0 PO A' LeA A0 PO A''" 
            using l11_30 [where ?A="P" and ?B="Q" and ?C="R" and
                ?D="P'" and ?E="Q'" and ?F="R'"] 
            by (meson sams_suma__lea123789 \<open>P Q R A0 PO A1 SumA P' Q' R'\<close> 
                \<open>P Q R CongA A0 PO A'\<close> \<open>P' Q' R' CongA A0 PO A''\<close> \<open>SAMS P Q R A0 PO A1\<close>)
          show "A0 PO OS A'' A'" 
            by (metis \<open>A0 \<noteq> A'\<close> \<open>Bet A0 A' B\<close> \<open>Bet A0 A'' B\<close> \<open>Bet A0 A1 A''\<close> 
                \<open>\<not> Col A0 PO A'\<close> assms(5) bet2__out between_identity out_one_side)
        qed
        thus "A' PO TS A0 A''" 
          by (simp add: \<open>\<not> Col A' PO A''\<close> \<open>\<not> Col A0 PO A'\<close> in_angle_two_sides 
              not_col_permutation_1 not_col_permutation_4)
      qed
      have "A PO A' CongA A' PO A''" 
      proof (rule conga_trans [where ?A'="A0" and ?B'="PO" and ?C'="A1"])
        have "PO \<noteq> A''" 
          using \<open>\<not> Col A' PO A''\<close> not_col_distincts by blast
        have "A' \<noteq> A''" 
          using \<open>\<not> Col A' PO A''\<close> not_col_distincts by blast
        have "\<not> PO A' OS A0 A''" 
          using \<open>Bet A0 A' A''\<close> col_trivial_3 one_side_chara by force
        show "A PO A' CongA A0 PO A1" 
          by (simp add: \<open>A PO A' CongA A0 PO A1\<close>)
        show "A0 PO A1 CongA A' PO A''" 
        proof (rule sams2_suma2__conga456 [where ?A="P" and ?B="Q" and ?C="R" 
              and ?G="P'" and ?H="Q'" and ?I="R'"])
          show "SAMS P Q R A0 PO A1" 
            using \<open>SAMS P Q R A0 PO A1\<close> by auto
          show "SAMS P Q R A' PO A''" 
          proof (rule conga2_sams__sams [where ?A="A0" and ?B="PO" and ?C="A'" and 
                ?D="A'" and ?E="PO" and ?F="A''"])
            show "A0 PO A' CongA P Q R" 
              using \<open>P Q R CongA A0 PO A'\<close> conga_sym_equiv by blast
            show "A' PO A'' CongA A' PO A''" 
              using \<open>PO \<noteq> A''\<close> \<open>PO \<noteq> A'\<close> conga_refl by auto
            show "SAMS A0 PO A' A' PO A''" 
              by (metis Col_cases bet_out bet_out_1 os2__sams out_one_side 
                  \<open>A' \<noteq> A''\<close> \<open>A0 \<noteq> A'\<close> \<open>Bet A0 A' A''\<close> \<open>\<not> Col A0 PO A''\<close>)
          qed
          show "P Q R A0 PO A1 SumA P' Q' R'" 
            by (simp add: \<open>P Q R A0 PO A1 SumA P' Q' R'\<close>)
          show "P Q R A' PO A'' SumA P' Q' R'"
          proof (rule conga3_suma__suma [where ?A="A0" and ?B="PO" and ?C="A'" and
                ?D="A'" and ?E="PO" and ?F="A''" and ?G="A0" and ?H="PO" and ?I="A''"])
            show "A0 PO A' A' PO A'' SumA A0 PO A''" 
            proof -
              have "A' PO A'' CongA A' PO A''"                 
                using \<open>PO \<noteq> A''\<close> \<open>PO \<noteq> A'\<close> conga_refl by auto
              moreover have "\<not> PO A' OS A0 A''"                   
                using \<open>\<not> PO A' OS A0 A''\<close> by auto
              moreover have "Coplanar A0 PO A' A''"                   
                using \<open>Bet A0 A' A''\<close> bet_col ncop__ncols by blast
              moreover have "A0 PO A'' CongA A0 PO A''"       
                using \<open>PO \<noteq> A''\<close> assms(2) conga_refl by auto
              ultimately show ?thesis
                using SumA_def by blast
            qed
            show "A0 PO A' CongA P Q R" 
              using \<open>P Q R CongA A0 PO A'\<close> conga_sym_equiv by auto
            show "A' PO A'' CongA A' PO A''" 
              using \<open>PO \<noteq> A''\<close> \<open>PO \<noteq> A'\<close> conga_refl by auto
            show "A0 PO A'' CongA P' Q' R'"
              using \<open>P' Q' R' CongA A0 PO A''\<close> conga_sym_equiv by auto
          qed
        qed
      qed
      have "A A' Lt A' A''" 
        using acute_archi_aux [where ?PO="PO" and ?A="A0" and ?B="B"] 
        by (metis ncol_conga_ncol not_col_distincts not_conga_sym 
            \<open>A PO A' CongA A' PO A''\<close> \<open>A PO A' CongA A0 PO A1\<close> \<open>Bet A0 A A'\<close>
            \<open>Bet A0 A' A''\<close> \<open>Bet A0 A'' B\<close> assms(1) assms(10) assms(3) between_exchange3)
      hence "A A' Le A' A''" 
        using Lt_def by blast
      hence "A0 A1 Le A' A''" 
        by (meson le_transitivity \<open>A0 A1 Le A A'\<close>)
      have "Bet A0 A1 A''" 
        by (simp add: \<open>Bet A0 A1 A''\<close>)
      moreover have "Bet A0 A'' B" 
        by (simp add: \<open>Bet A0 A'' B\<close>)
      moreover have "P' Q' R' CongA A0 PO A''" 
        by (simp add: \<open>P' Q' R' CongA A0 PO A''\<close>)
      moreover have "A0 C' Le A0 A''" 
        by (meson bet2_le2__le1346 \<open>A0 A1 Le A' A''\<close> \<open>A0 C Le A0 A'\<close>
            \<open>Bet A0 A' A''\<close> assms(7) assms(8) cong_reflexivity l5_6)
      moreover
      have "\<exists> A. Bet A0 A A'' \<and> A PO A'' CongA A0 PO A1 \<and> A0 A1 Le A A''" 
      proof -
        have "Bet A0 A' A''" 
          using \<open>Bet A0 A' A''\<close> by fastforce
        moreover have "A' PO A'' CongA A0 PO A1" 
          by (meson not_conga not_conga_sym \<open>A PO A' CongA A' PO A''\<close> 
              \<open>A PO A' CongA A0 PO A1\<close>)
        moreover have "A0 A1 Le A' A''" 
          using \<open>A0 A1 Le A' A''\<close> by auto
        ultimately show ?thesis by blast
      qed
      ultimately
      have "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or> 
                  (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C' Le A0 A' \<and>
                     (\<exists> A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
        using \<open>GradA A0 PO A1 P' Q' R'\<close> by blast
    }
    ultimately
    have "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or> 
                  (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C' Le A0 A' \<and>
                     (\<exists> A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
      using \<open>GradA A0 PO A1 P Q R\<close> by blast
  }
  ultimately
  show ?thesis 
    using P2 by blast
qed

lemma acute_archi_aux2:
  assumes "Per PO A0 B" and
    "PO \<noteq> A0" and
    "B \<noteq> A0" and
    "Bet A0 A1 B" and
    "A0 \<noteq> A1" and
    "Grad A0 A1 C"
  shows "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
                  (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C Le A0 A' \<and>
                  (\<exists> A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
proof -
  have "\<not> Col PO A0 B" 
    by (metis assms(1) assms(2) assms(3) col_permutation_1 l8_8 per_col)
  have "\<not> Col A0 PO A1" 
    by (metis \<open>\<not> Col PO A0 B\<close> assms(4) assms(5) bet_col col_trivial_3 colx not_col_permutation_2)
  have "PO \<noteq> A1" 
    using \<open>\<not> Col A0 PO A1\<close> assms(4) bet_col1 by blast
  have "PO \<noteq> B" 
    using assms(1) assms(3) per_distinct_1 by auto
  have "GradI A0 A1 C" 
    by (simp add: Grad__GradI assms(6))
  let ?th = "\<exists> P Q R. (GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
                  (\<exists> A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and> A0 C Le A0 A' \<and>
                  (\<exists> A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
  have ?th
  proof (rule GradI.induct [where ?A="A0" and ?B="A1" and ?x="C"])
    show "GradI A0 A1 C" 
      using \<open>GradI A0 A1 C\<close> by blast
    show "\<exists>P Q R.
       GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
        (\<exists>A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and>
              A0 A1 Le A0 A' \<and> (\<exists>A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A')))" 
      by (metis bet_col assms(1) assms(2) assms(3) assms(4) assms(5) cong2_per2__cong_conga2 
          cong_reflexivity grada_init le_reflexivity not_bet_distincts
          not_col_permutation_5 per_col)
    {
      fix C0 C'
      assume H1: "GradI A0 A1 C0" and
        H2: "\<exists>P Q R. GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
         (\<exists>A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and>
           A0 C0 Le A0 A' \<and> (\<exists>A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A')))" and
        H3: "Bet A0 C0 C'" and
        H4: "Cong A0 A1 C0 C'" 
      have "\<exists>P Q R. GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
           (\<exists>A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and>
                 A0 C' Le A0 A' \<and> (\<exists>A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A')))"
      proof (rule acute_archi_aux2_2 [where ?C="C0"])
        show "Per PO A0 B"
          using assms(1) by auto
        show "PO \<noteq> A0" 
          by (simp add: assms(2))
        show "B \<noteq> A0" 
          by (simp add: assms(3))
        show "Bet A0 A1 B" 
          by (simp add: assms(4))
        show "A0 \<noteq> A1"
          by (simp add: assms(5))
        show "Grad A0 A1 C0" 
          by (simp add: Grad_GradI H1)
        show "Bet A0 C0 C'" 
          using H3 by auto
        show "Cong A0 A1 C0 C'" 
          using H4 by auto
        show "\<not> Col PO A0 B" 
          using \<open>\<not> Col PO A0 B\<close> by auto
        show "\<not> Col A0 PO A1" 
          by (simp add: \<open>\<not> Col A0 PO A1\<close>)
        show "PO \<noteq> A1" 
          by (simp add: \<open>PO \<noteq> A1\<close>)
        show "PO \<noteq> B" 
          using \<open>PO \<noteq> B\<close> by auto
        show "Per PO A0 B \<and> PO \<noteq> A0 \<and> B \<noteq> A0 \<and> Bet A0 A1 B \<and> A0 \<noteq> A1 \<and> 
               \<not> Col PO A0 B \<and> \<not> Col A0 PO A1 \<and> PO \<noteq> A1 \<longrightarrow>
               (\<exists>P Q R. GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
                  (\<exists>A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and>
               A0 C0 Le A0 A' \<and> (\<exists>A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))))" 
          using H2 by blast
      qed
    }
    thus "\<And>C C'.
       GradI A0 A1 C \<Longrightarrow>
       \<exists>P Q R. GradA A0 PO A1 P Q R \<and> (A0 PO B LeA P Q R \<or>
           (\<exists>A'. Bet A0 A1 A' \<and> Bet A0 A' B \<and> P Q R CongA A0 PO A' \<and>
                 A0 C Le A0 A' \<and> (\<exists>A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A'))) \<Longrightarrow>
       Bet A0 C C' \<Longrightarrow>
       Cong A0 A1 C C' \<Longrightarrow>
       \<exists>P Q R.
          GradA A0 PO A1 P Q R \<and>
          (A0 PO B LeA P Q R \<or>
           (\<exists>A'. Bet A0 A1 A' \<and>
                 Bet A0 A' B \<and>
                 P Q R CongA A0 PO A' \<and>
                 A0 C' Le A0 A' \<and> (\<exists>A. Bet A0 A A' \<and> A PO A' CongA A0 PO A1 \<and> A0 A1 Le A A')))" 
      by blast
  qed
  thus ?thesis by blast
qed

lemma archi_in_acute_angles:
  assumes "archimedes_axiom" 
  shows "\<forall> A B C D E F. \<not> Col A B C \<and> Acute D E F 
                        \<longrightarrow> (\<exists> P Q R. GradA A B C P Q R \<and> D E F LeA P Q R)" 
proof -
  {
    fix A B C D E F
    assume "\<not> Col A B C" and
      "Acute D E F"
    have "A \<noteq> B"  
      using \<open>\<not> Col A B C\<close> col_trivial_1 by fastforce
    have "C \<noteq> B" 
      using \<open>\<not> Col A B C\<close> col_trivial_2 by force
    have "E \<noteq> D" 
      using \<open>Acute D E F\<close> acute_distincts by blast
    have "E \<noteq> F" 
      using \<open>Acute D E F\<close> acute_distincts by blast
    have "\<exists> P Q R. GradA A B C P Q R \<and> D E F LeA P Q R" 
    proof (cases "Col D E F")
      case True
      thus ?thesis 
        by (metis Col_def Out_cases bet_out bet_out_1 l11_31_1  \<open>A \<noteq> B\<close> 
            \<open>Acute D E F\<close> \<open>C \<noteq> B\<close> \<open>E \<noteq> D\<close> \<open>E \<noteq> F\<close> acute_not_bet grada_ABC)
    next
      case False
      {
        assume "D E F LeA A B C"
        hence "\<exists> P Q R. GradA A B C P Q R \<and> D E F LeA P Q R" 
          by (metis \<open>A \<noteq> B\<close> \<open>C \<noteq> B\<close> grada_ABC)
      }
      moreover
      {
        assume "A B C LeA D E F"
        obtain D0 where "Col D E D0" and "D E Perp F D0" 
          using False l8_18_existence by blast
        have "E Out D0 D" 
        proof (rule acute_col_perp__out [where ?A="F"])
          show "Acute F E D"             
            using \<open>Acute D E F\<close> acute_sym by blast
          show "Col E D D0" 
            using \<open>Col D E D0\<close> not_col_permutation_4 by blast
          show "E D Perp F D0" 
            using \<open>D E Perp F D0\<close> perp_left_comm by blast
        qed
        have "D0 \<noteq> F" 
          using \<open>D E Perp F D0\<close> perp_not_eq_2 by blast
        have "D0 \<noteq> E" 
          using \<open>E Out D0 D\<close> out_diff1 by auto
        have "D E F CongA D0 E F" 
          by (metis acute_col_perp__out acute_sym out2__conga out_trivial
              perp_left_comm \<open>Acute D E F\<close> \<open>Col D E D0\<close> \<open>D E Perp F D0\<close> \<open>E \<noteq> F\<close> 
              not_col_permutation_4)
        have "Acute D0 E F" 
          by (meson acute_conga__acute \<open>Acute D E F\<close> \<open>D E F CongA D0 E F\<close>)
        have "A B C LeA D0 E F" 
          by (meson conga__lea lea_trans \<open>A B C LeA D E F\<close> \<open>D E F CongA D0 E F\<close>)
        have "\<not> Col D E F" 
          by (simp add: False)
        have "Per E D0 F" 
          by (meson Per_cases l8_16_1 \<open>Col D E D0\<close> \<open>D E Perp F D0\<close> col_trivial_2)
        obtain D1' where "A B C CongA D0 E D1'" and "D0 E OS D1' F" 
          by (metis Col_cases False angle_construction_1 \<open>Col D E D0\<close> 
              \<open>D0 \<noteq> E\<close> \<open>\<not> Col A B C\<close> col2__eq)
        have "D0 E F CongA D0 E F" 
          using \<open>D0 \<noteq> E\<close> \<open>E \<noteq> F\<close> conga_refl by auto
        hence "D0 E D1' LeA D0 E F" 
          using l11_30 [where ?A="A" and ?B="B" and ?C="C" and ?D="D0" and ?E="E" and ?F="F"]
            \<open>A B C LeA D0 E F\<close> \<open>A B C CongA D0 E D1'\<close> by blast
        have "D0 E OS F D1'" 
          by (simp add: \<open>D0 E OS D1' F\<close> one_side_symmetry)
        hence "D1' InAngle D0 E F" 
          using lea_in_angle \<open>D0 E D1' LeA D0 E F\<close> by blast
        then obtain D1 where "Bet D0 D1 F" and "D1 = E \<or> E Out D1 D1'" 
          using InAngle_def by force
        have "D1 = E \<longrightarrow> (\<exists> P Q R. GradA A B C P Q R \<and> D E F LeA P Q R)" 
          using \<open>Acute D0 E F\<close> \<open>Bet D0 D1 F\<close> acute_not_bet by blast
        moreover
        {
          assume "E Out D1 D1'"
          have "A B C CongA D0 E D1"
          proof (rule l11_10 [where ?A="A" and ?C="C" and ?D="D0" and ?F="D1'"], 
              insert \<open>A B C CongA D0 E D1'\<close> \<open>E Out D1 D1'\<close>)
            show "B Out A A" 
              using \<open>A \<noteq> B\<close> out_trivial by auto
            show "B Out C C" 
              by (simp add: \<open>C \<noteq> B\<close> out_trivial)
            show "E Out D0 D0" 
              by (simp add: \<open>D0 \<noteq> E\<close> out_trivial)
          qed
          have "\<not> Col D0 E D1'" 
            using \<open>D0 E OS D1' F\<close> col123__nos by force
          have "D0 \<noteq> D1" 
            using Col_cases \<open>E Out D1 D1'\<close> \<open>\<not> Col D0 E D1'\<close> out_col by blast
          obtain F' where "Bet D0 F F'" and "Cong F F' D0 F" 
            using segment_construction by blast
          obtain G where "Grad D0 D1 G" and "D0 F' Le D0 G" 
            using Reach_def \<open>D0 \<noteq> D1\<close> archimedes_axiom_def assms by blast
          have "GradI D0 D1 G" 
            by (simp add: Grad__GradI \<open>Grad D0 D1 G\<close>)
          have "\<exists> P Q R. (GradA D0 E D1 P Q R \<and> (D0 E F LeA P Q R \<or>
            (\<exists> A'. Bet D0 D1 A' \<and> Bet D0 A' F \<and> P Q R CongA D0 E A' \<and>
              D0 G Le D0 A' \<and> (\<exists> A. Bet D0 A A' \<and> A E A' CongA D0 E D1 \<and> D0 D1 Le A A'))))" 
            using acute_archi_aux2 \<open>Bet D0 D1 F\<close> \<open>D0 \<noteq> D1\<close> \<open>D0 \<noteq> E\<close> \<open>D0 \<noteq> F\<close> 
              \<open>Grad D0 D1 G\<close> \<open>Per E D0 F\<close> by blast
          then obtain P Q R where
            "GradA D0 E D1 P Q R" and
            "D0 E F LeA P Q R \<or> (\<exists> A'. Bet D0 D1 A' \<and> Bet D0 A' F \<and>
                 P Q R CongA D0 E A' \<and> D0 G Le D0 A' \<and> 
                 (\<exists> A. Bet D0 A A' \<and> A E A' CongA D0 E D1 \<and> D0 D1 Le A A'))" by blast
          have "D0 \<noteq> E"  
            using grada_distincts [where ?A="D0" and ?B="E" and ?C="D1" and 
                ?D="P" and ?E="Q" and ?F="R"] \<open>GradA D0 E D1 P Q R\<close> by blast
          have "D1 \<noteq> E" 
            using grada_distincts [where ?A="D0" and ?B="E" and ?C="D1" and 
                ?D="P" and ?E="Q" and ?F="R"] \<open>GradA D0 E D1 P Q R\<close> by blast
          have "P \<noteq> Q"
            using grada_distincts [where ?A="D0" and ?B="E" and ?C="D1" and 
                ?D="P" and ?E="Q" and ?F="R"] \<open>GradA D0 E D1 P Q R\<close> by blast
          have "R \<noteq> Q" 
            using grada_distincts [where ?A="D0" and ?B="E" and ?C="D1" and 
                ?D="P" and ?E="Q" and ?F="R"] \<open>GradA D0 E D1 P Q R\<close> by blast
          have "GradA A B C P Q R"
          proof (rule conga2_grada__grada [where ?A="D0" and ?B="E" and ?C="D1" 
                and ?D="P" and ?E="Q" and ?F="R"], insert \<open>GradA D0 E D1 P Q R\<close>)
            show "D0 E D1 CongA A B C" 
              using \<open>A B C CongA D0 E D1\<close> conga_sym_equiv by auto
            show "P Q R CongA P Q R" 
              by (simp add: \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> conga_refl)
          qed
          moreover 
          have "D E F LeA P Q R" 
          proof -
            {
              assume "D0 E F LeA P Q R"
              have "D E F LeA P Q R" 
              proof (rule l11_30 [where ?A="D0" and ?B="E" and ?C="F" and 
                    ?D="P" and ?E="Q" and ?F="R"])
                show "D0 E F LeA P Q R" 
                  by (simp add: \<open>D0 E F LeA P Q R\<close>)
                show "D0 E F CongA D E F" 
                  using \<open>D E F CongA D0 E F\<close> conga_sym_equiv by auto
                show "P Q R CongA P Q R" 
                  using \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> conga_refl by auto
              qed
            }
            moreover
            {
              assume "\<exists> A'. Bet D0 D1 A' \<and> Bet D0 A' F \<and> P Q R CongA D0 E A' \<and>
                D0 G Le D0 A' \<and> (\<exists> A. Bet D0 A A' \<and> A E A' CongA D0 E D1 \<and> D0 D1 Le A A')"
              then obtain A' where "Bet D0 D1 A'" and "Bet D0 A' F" and
                "P Q R CongA D0 E A'" and "D0 G Le D0 A'" and 
                "\<exists> A. Bet D0 A A' \<and> A E A' CongA D0 E D1 \<and> D0 D1 Le A A'"
                by blast
              have "D0 A' Le D0 F"         
                by (simp add: \<open>Bet D0 A' F\<close> bet__le1213)
              hence "D0 G Le D0 F"
                using \<open>D0 G Le D0 A'\<close> le_transitivity by blast
              moreover have "D0 F Lt D0 F'" 
                using \<open>Bet D0 F F'\<close> \<open>Cong F F' D0 F\<close> \<open>D0 \<noteq> F\<close> 
                  bet__lt1213 cong_diff_3 by presburger
              ultimately have "D0 G Lt D0 F'" 
                using le1234_lt__lt by blast
              hence False 
                using \<open>D0 F' Le D0 G\<close> le__nlt by auto
              hence "D E F LeA P Q R" 
                by blast
            }
            ultimately show ?thesis 
              using \<open>D0 E F LeA P Q R \<or> (\<exists>A'. Bet D0 D1 A' \<and> Bet D0 A' F \<and> 
                P Q R CongA D0 E A' \<and> D0 G Le D0 A' \<and> 
                (\<exists>A. Bet D0 A A' \<and> A E A' CongA D0 E D1 \<and> D0 D1 Le A A'))\<close> by blast
          qed
          ultimately have "\<exists> P Q R. GradA A B C P Q R \<and> D E F LeA P Q R" 
            by blast
        }
        ultimately have "\<exists> P Q R. GradA A B C P Q R \<and> D E F LeA P Q R" 
          using \<open>D1 = E \<or> E Out D1 D1'\<close> by blast
      }
      ultimately show ?thesis using lea_total 
        by (metis \<open>A \<noteq> B\<close> \<open>C \<noteq> B\<close> \<open>E \<noteq> D\<close> \<open>E \<noteq> F\<close>)
    qed
  }
  thus ?thesis 
    by blast
qed

lemma angles_archi_aux:
  assumes "GradA A B C D E F" and 
    "GradA A B C G H I" and
    "\<not> SAMS D E F G H I" 
  shows "\<exists> P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C" 
proof -
  have "\<not> SAMS D E F G H I \<longrightarrow> (\<exists> P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C)" 
  proof (rule GradA.induct [OF assms(2)])
    show "\<And>Da Ea Fa.
       A B C CongA Da Ea Fa \<Longrightarrow> \<not> SAMS D E F Da Ea Fa \<longrightarrow> 
                                (\<exists>P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C)" 
      by (metis Tarski_neutral_dimensionless.conga_refl Tarski_neutral_dimensionless_axioms 
          assms(1) conga2_sams__sams grada_distincts)
    {
      fix Da Ea Fa G H I
      assume "GradA A B C Da Ea Fa" and
        "\<not> SAMS D E F Da Ea Fa \<longrightarrow> (\<exists> P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C)" and
        "SAMS Da Ea Fa A B C" and
        "Da Ea Fa A B C SumA G H I"
      {
        assume "\<not> SAMS D E F G H I"
        {
          assume "SAMS D E F Da Ea Fa"
          have "E \<noteq> D" 
            using \<open>SAMS D E F Da Ea Fa\<close> sams_distincts by blast
          have "E \<noteq> F" 
            using \<open>SAMS D E F Da Ea Fa\<close> sams_distincts by blast
          have "Ea \<noteq> Da" 
            using \<open>SAMS D E F Da Ea Fa\<close> sams_distincts by blast
          have "Ea \<noteq> Fa" 
            using \<open>SAMS D E F Da Ea Fa\<close> sams_distincts by blast
          obtain P Q R where "D E F Da Ea Fa SumA P Q R"
            using ex_suma \<open>E \<noteq> D\<close> \<open>E \<noteq> F\<close> \<open>Ea \<noteq> Da\<close> \<open>Ea \<noteq> Fa\<close> by presburger
          have "GradA A B C P Q R" 
            using grada2_sams_suma__grada [where ?D="D" and ?E="E" and ?F="F" and
                ?G="Da" and ?H="Ea" and ?I="Fa"]
              assms(1) \<open>GradA A B C Da Ea Fa\<close> \<open>SAMS D E F Da Ea Fa\<close> \<open>D E F Da Ea Fa SumA P Q R\<close>
            by blast
          moreover 
          {
            assume "SAMS P Q R A B C"
            have "SAMS D E F G H I"
              using \<open>SAMS D E F Da Ea Fa\<close> \<open>SAMS Da Ea Fa A B C\<close> \<open>D E F Da Ea Fa SumA P Q R\<close>
                \<open>Da Ea Fa A B C SumA G H I\<close> \<open>SAMS P Q R A B C\<close> sams_assoc_1 by blast
            hence False 
              using \<open>\<not> SAMS D E F G H I\<close> by blast
          }
          ultimately have "\<exists>P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C" 
            by blast
        }
        hence "\<exists>P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C" 
          using \<open>\<not> SAMS D E F Da Ea Fa \<longrightarrow> (\<exists>P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C)\<close> 
          by blast
      }
      hence "\<not> SAMS D E F G H I \<longrightarrow> (\<exists>P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C)" 
        by blast
    }
    thus "\<And>Da Ea Fa G H I.
       GradA A B C Da Ea Fa \<Longrightarrow>
       \<not> SAMS D E F Da Ea Fa \<longrightarrow> (\<exists>P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C) \<Longrightarrow>
       SAMS Da Ea Fa A B C \<Longrightarrow> Da Ea Fa A B C SumA G H I \<Longrightarrow> 
       \<not> SAMS D E F G H I \<longrightarrow> (\<exists>P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C)" 
      by blast
  qed
  thus ?thesis 
    using assms(3) by blast
qed

lemma angles_archi_aux1:
  assumes "archimedes_axiom"
  shows "\<forall> A B C D E F.
\<not> Col A B C \<and> \<not> Bet D E F \<longrightarrow>
(\<exists> P Q R. GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C))" 
proof -
  {
    fix A B C D E F
    assume "\<not> Col A B C" and
      "\<not> Bet D E F"
    have "D \<noteq> E" 
      using \<open>\<not> Bet D E F\<close> between_trivial2 by auto
    have "F \<noteq> E" 
      using \<open>\<not> Bet D E F\<close> not_bet_distincts by blast
    obtain F1 where "F1 InAngle D E F" and "F1 E D CongA F1 E F" 
      using angle_bisector \<open>D \<noteq> E\<close> \<open>F \<noteq> E\<close> by blast
    have "F1 \<noteq> E" 
      using \<open>F1 E D CongA F1 E F\<close> conga_distinct by auto
    have "\<not> E F1 OS D F"
    proof (cases "Col D E F1")
      case True
      thus ?thesis
        using NCol_perm col123__nos by blast
    next
      case False
      thus ?thesis
        by (meson \<open>F1 InAngle D E F\<close> col124__nos col_permutation_4 col_permutation_5 
            in_angle_two_sides invert_one_side l9_9)
    qed
    have "D E F1 D E F1 SumA D E F" 
      by (meson conga_refl \<open>D \<noteq> E\<close> \<open>F \<noteq> E\<close> \<open>F1 E D CongA F1 E F\<close> 
          \<open>F1 InAngle D E F\<close> \<open>F1 \<noteq> E\<close> conga3_suma__suma 
          conga_left_comm inangle__suma not_conga_sym)
    have "SAMS D E F1 D E F1" 
    proof -
      {
        assume "Bet D E F1" 
        hence False 
          using bet_in_angle_bet \<open>F1 InAngle D E F\<close> \<open>\<not> Bet D E F\<close> by blast
      }
      hence "E Out D F1 \<or> \<not> Bet D E F1" 
        by blast
      moreover 
      have "\<exists> J. F1 E J CongA D E F1 \<and> \<not> E F1 OS D J \<and> \<not> D E TS F1 J \<and> Coplanar D E F1 J" 
      proof -
        have "F1 E F CongA D E F1" 
          using \<open>F1 E D CongA F1 E F\<close> conga_left_comm conga_sym_equiv by blast
        moreover have "\<not> E F1 OS D F" 
          by (simp add: \<open>\<not> E F1 OS D F\<close>)
        moreover have "\<not> D E TS F1 F" 
        proof (cases "Col D E F1")
          case True
          thus ?thesis 
            using TS_def col_permutation_2 by blast
        next
          case False
          thus ?thesis
            by (metis Col_cases TS_def \<open>F1 InAngle D E F\<close> in_angle_one_side l9_9)
        qed
        moreover have "Coplanar D E F1 F" 
          by (meson inangle__coplanar \<open>F1 InAngle D E F\<close> coplanar_perm_8)
        ultimately show ?thesis 
          by blast
      qed
      ultimately show ?thesis 
        using SAMS_def \<open>D \<noteq> E\<close> by auto
    qed
    hence "Acute D E F1" 
      by (metis nbet_sams_suma__acute \<open>D E F1 D E F1 SumA D E F\<close> \<open>\<not> Bet D E F\<close>)
    then obtain P1 Q1 R1 where "GradA A B C P1 Q1 R1" and "D E F1 LeA P1 Q1 R1"  
      using archi_in_acute_angles \<open>\<not> Col A B C\<close> assms by blast
    have "P1 \<noteq> Q1"
      using \<open>GradA A B C P1 Q1 R1\<close> grada_distincts by blast
    have "Q1 \<noteq> R1" 
      using \<open>GradA A B C P1 Q1 R1\<close> grada_distincts by blast
    {
      assume "SAMS P1 Q1 R1 P1 Q1 R1"
      obtain P Q R where "P1 Q1 R1 P1 Q1 R1 SumA P Q R" 
        using ex_suma \<open>P1 \<noteq> Q1\<close> \<open>Q1 \<noteq> R1\<close> by presburger
      have "GradA A B C P Q R" 
        using grada2_sams_suma__grada [where ?D="P1" and ?E="Q1" and ?F="R1" and 
            ?G="P1" and ?H="Q1" and ?I="R1"] \<open>GradA A B C P1 Q1 R1\<close> \<open>GradA A B C P1 Q1 R1\<close> 
          \<open>SAMS P1 Q1 R1 P1 Q1 R1\<close> \<open>P1 Q1 R1 P1 Q1 R1 SumA P Q R\<close> by blast
      moreover have "D E F LeA P Q R" 
        using sams_lea2_suma2__lea [where ?A="D" and ?B="E" and ?C="F1" and 
            ?D="D" and ?E="E" and ?F="F1" and
            ?A'="P1" and ?B'="Q1" and ?C'="R1" and ?D'="P1" and ?E'="Q1" and ?F'="R1"]
          \<open>D E F1 LeA P1 Q1 R1\<close> \<open>SAMS P1 Q1 R1 P1 Q1 R1\<close> \<open>D E F1 D E F1 SumA D E F\<close>
          \<open>P1 Q1 R1 P1 Q1 R1 SumA P Q R\<close> by blast
      ultimately have "\<exists> P Q R. GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C)" 
        by blast
    }
    moreover
    {
      assume "\<not> SAMS P1 Q1 R1 P1 Q1 R1"
      hence "\<exists> P Q R. GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C)" 
        using angles_archi_aux \<open>GradA A B C P1 Q1 R1\<close> calculation by blast
    }
    ultimately have "\<exists> P Q R. GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C)" 
      by blast
  }
  thus ?thesis
    by blast
qed

(** Inspired by Hartshorne's demonstration of Lemma 35.1 in Geometry Euclid and Beyond *)
lemma archi_in_angles:
  assumes "archimedes_axiom" 
  shows "\<forall> A B C. \<forall> D ::'p. \<forall> E ::'p. \<forall> F ::'p. (\<not> Col A B C \<and> D \<noteq> E \<and> F \<noteq> E) \<longrightarrow>
    (\<exists> P Q R. GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C))" 
proof -
  {
    fix A B C 
    fix D::'p
    fix E::'p
    fix F::'p
    assume "\<not> Col A B C" and 
      "D \<noteq> E" and 
      "F \<noteq> E"
    have "\<exists> P Q R. (GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C))" 
    proof (cases "Bet D E F")
      case True
      obtain A0 where "Bet A B A0" and "Cong B A0 A B" 
        using segment_construction by blast
      have "A \<noteq> B" 
        using \<open>\<not> Col A B C\<close> not_col_distincts by blast
      have "C \<noteq> B" 
        using \<open>\<not> Col A B C\<close> col_trivial_2 by auto
      have "B \<noteq> A0" 
        using \<open>A \<noteq> B\<close> \<open>Cong B A0 A B\<close> cong_reverse_identity by blast
      have "\<not> Col A0 B C" 
        by (meson \<open>B \<noteq> A0\<close> \<open>Bet A B A0\<close> \<open>\<not> Col A B C\<close> bet_col col2__eq col_permutation_3)
      obtain P1 Q1 R1 where "GradA A B C P1 Q1 R1" and 
        "C B A0 LeA P1 Q1 R1 \<or> \<not> SAMS P1 Q1 R1 A B C" 
        using angles_archi_aux1 
        by (metis Col_def \<open>\<not> Col A B C\<close> \<open>\<not> Col A0 B C\<close> assms between_symmetry)
      {
        assume "SAMS P1 Q1 R1 A B C"
        hence "C B A0 LeA P1 Q1 R1" 
          using \<open>C B A0 LeA P1 Q1 R1 \<or> \<not> SAMS P1 Q1 R1 A B C\<close> by auto
        have "P1 \<noteq> Q1" 
          using \<open>SAMS P1 Q1 R1 A B C\<close> 
          by (simp add: sams_distincts)
        have "R1 \<noteq> Q1" 
          using \<open>C B A0 LeA P1 Q1 R1\<close> lea_distincts by blast
        obtain P Q R where "P1 Q1 R1 A B C SumA P Q R" 
          using ex_suma \<open>A \<noteq> B\<close> \<open>C \<noteq> B\<close> \<open>P1 \<noteq> Q1\<close> \<open>R1 \<noteq> Q1\<close> by presburger
        have "GradA A B C P Q R"
          using grada_stab [where ?D="P1" and ?E="Q1" and ?F="R1"]
            \<open>GradA A B C P1 Q1 R1\<close> \<open>SAMS P1 Q1 R1 A B C\<close> \<open>P1 Q1 R1 A B C SumA P Q R\<close> by auto
        moreover 
        have "P \<noteq> Q" 
          using calculation grada_distincts by blast
        have "R \<noteq> Q" 
          using calculation grada_distincts by blast
        have "A B A0 LeA P Q R"
        proof (rule sams_lea2_suma2__lea [where 
              ?A="A0" and ?B="B" and ?C="C" and ?D="A" and ?E="B" and ?F="C" 
              and ?A'="P1" and ?B'="Q1" and ?C'="R1" and ?D'="A" and ?E'="B" and ?F'="C"])
          show "A0 B C LeA P1 Q1 R1" 
            using \<open>C B A0 LeA P1 Q1 R1\<close> lea_left_comm by blast
          show "A B C LeA A B C" 
            using \<open>A \<noteq> B\<close> \<open>C \<noteq> B\<close> lea_refl by force
          show "SAMS P1 Q1 R1 A B C" 
            using \<open>SAMS P1 Q1 R1 A B C\<close> by auto
          show "A0 B C A B C SumA A B A0" 
            by (metis Bet_cases \<open>A \<noteq> B\<close> \<open>B \<noteq> A0\<close> \<open>Bet A B A0\<close> \<open>C \<noteq> B\<close> 
                bet__suma suma_middle_comm suma_right_comm)
          show "P1 Q1 R1 A B C SumA P Q R" 
            using \<open>P1 Q1 R1 A B C SumA P Q R\<close> by auto
        qed
        hence "Bet P Q R" 
          using \<open>Bet A B A0\<close> bet_lea__bet by blast
        hence "D E F LeA P Q R" 
          using l11_31_2 \<open>D \<noteq> E\<close> \<open>F \<noteq> E\<close> \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> by blast
        ultimately have "\<exists> P Q R. (GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C))" 
          by blast
      }
      moreover
      {
        assume "\<not> SAMS P1 Q1 R1 A B C"
        hence "\<exists> P Q R. (GradA A B C P Q R \<and> (D E F LeA P Q R \<or> \<not> SAMS P Q R A B C))" 
          using \<open>GradA A B C P1 Q1 R1\<close> by blast
      }
      ultimately show ?thesis 
        by blast
    next
      case False
      thus ?thesis 
        using \<open>\<not> Col A B C\<close> angles_archi_aux1 assms by blast
    qed
  }
  thus ?thesis
    by blast
qed

(** If Archimedes' postulate holds, every nondegenerate angle can be 
    repeated until exceeding 180\<degree> *)
lemma archi__grada_destruction:
  assumes "archimedes_axiom" 
  shows "\<forall> A B C. \<not> Col A B C \<longrightarrow>
(\<exists> P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C)" 
proof -
  {
    fix A B C
    assume "\<not> Col A B C"
    obtain A0 where "Bet A B A0" and "Cong B A0 A B" 
      using segment_construction by blast
    have "A \<noteq> B" 
      using \<open>\<not> Col A B C\<close> col_trivial_1 by blast
    have "B \<noteq> A0" 
      using \<open>A \<noteq> B\<close> \<open>Cong B A0 A B\<close> cong_reverse_identity by blast
    obtain P Q R where "GradA A B C P Q R" and "A B A0 LeA P Q R \<or> \<not> SAMS P Q R A B C"
      using archi_in_angles \<open>A \<noteq> B\<close> \<open>B \<noteq> A0\<close> \<open>\<not> Col A B C\<close> assms by metis
    {
      assume "A B A0 LeA P Q R"
      assume "SAMS P Q R A B C"
      hence "B Out A C \<or> \<not> Bet P Q R"
        using SAMS_def by blast
      have "B Out A C \<longrightarrow> False" 
        using Col_cases \<open>\<not> Col A B C\<close> out_col by blast
      moreover
      {
        assume "\<not> Bet P Q R"
        have "Bet A B A0" 
          by (simp add: \<open>Bet A B A0\<close>)
        hence False 
          using bet_lea__bet \<open>A B A0 LeA P Q R\<close> \<open>B Out A C \<or> \<not> Bet P Q R\<close> calculation by blast
      }
      hence "\<not> Bet P Q R \<longrightarrow> False" 
        by blast
      ultimately have False 
        using \<open>B Out A C \<or> \<not> Bet P Q R\<close> by fastforce
    }
    hence "A B A0 LeA P Q R \<longrightarrow> \<not> SAMS P Q R A B C" 
      by blast
    hence "\<not> SAMS P Q R A B C" 
      using \<open>A B A0 LeA P Q R \<or> \<not> SAMS P Q R A B C\<close> by blast
    hence "\<exists> P Q R. GradA A B C P Q R \<and> \<not> SAMS P Q R A B C" 
      using \<open>GradA A B C P Q R\<close> by blast
  }
  thus ?thesis 
    by blast
qed

lemma gradaexp_destruction_aux:
  assumes "GradA A B C P Q R"
  shows "\<exists> S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> P Q R LeA S T U)" 
proof (rule GradA.induct [OF assms(1)])
  show "\<And>D E F. A B C CongA D E F \<Longrightarrow> 
           \<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> D E F LeA S T U)" 
    by (metis conga__lea456123 conga_diff1 conga_diff2 gradaexp_ABC)
  {
    fix D E F G H I
    assume "GradA A B C D E F" and
      "\<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> D E F LeA S T U)" and
      "SAMS D E F A B C" and
      "D E F A B C SumA G H I"
    then obtain P Q R where "GradAExp A B C P Q R" and "Obtuse P Q R \<or> D E F LeA P Q R" 
      by blast
    have "P \<noteq> Q" 
      using \<open>GradAExp A B C P Q R\<close> gradaexp_distincts by blast
    have "R \<noteq> Q" 
      using \<open>GradAExp A B C P Q R\<close> gradaexp_distincts by blast
    {
      assume "SAMS P Q R P Q R"
      {
        assume "Obtuse P Q R" 
        hence "\<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> G H I LeA S T U)" 
          using \<open>GradAExp A B C P Q R\<close> by blast
      }
      moreover
      {
        assume  "D E F LeA P Q R" 
        obtain S T U where "P Q R P Q R SumA S T U" 
          using ex_suma \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> by presburger
        have "GradAExp A B C S T U"
        proof (rule gradaexp_stab [where ?D="P" and ?E="Q" and ?F="R"])
          show "GradAExp A B C P Q R" 
            by (simp add: \<open>GradAExp A B C P Q R\<close>)
          show "SAMS P Q R P Q R" 
            by (simp add: \<open>SAMS P Q R P Q R\<close>)
          show "P Q R P Q R SumA S T U"
            using \<open>P Q R P Q R SumA S T U\<close> by auto
        qed
        moreover
        have "GradA A B C P Q R" 
          using \<open>GradAExp A B C P Q R\<close> gradaexp__grada by auto
        hence "G H I LeA S T U" 
          by (meson \<open>D E F A B C SumA G H I\<close> \<open>D E F LeA P Q R\<close> \<open>P Q R P Q R SumA S T U\<close>
              \<open>SAMS P Q R P Q R\<close> grada__lea sams_lea2_suma2__lea)
        ultimately have "\<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> G H I LeA S T U)" 
          by blast
      }
      ultimately have "\<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> G H I LeA S T U)" 
        using \<open>Obtuse P Q R \<or> D E F LeA P Q R\<close> by blast
    }
    moreover
    {
      assume "\<not> SAMS P Q R P Q R"
      hence "Obtuse P Q R" 
        using \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> nsams__obtuse by auto
      hence "\<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> G H I LeA S T U)" 
        using \<open>GradAExp A B C P Q R\<close> by blast
    }
    ultimately have "\<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> G H I LeA S T U)" 
      by blast
  }
  thus "\<And>D E F G H I.
       GradA A B C D E F \<Longrightarrow>
       \<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> D E F LeA S T U) \<Longrightarrow>
       SAMS D E F A B C \<Longrightarrow>
       D E F A B C SumA G H I \<Longrightarrow> \<exists>S T U. GradAExp A B C S T U \<and> (Obtuse S T U \<or> G H I LeA S T U)" 
    by blast
qed

(** If Archimedes' postulate holds, every nondegenerate angle can be doubled until exceeding 90\<degree> *)
lemma archi__gradaexp_destruction:
  assumes "archimedes_axiom"
  shows "\<forall> A B C. \<not> Col A B C \<longrightarrow> (\<exists> P Q R. GradAExp A B C P Q R \<and> Obtuse P Q R)" 
proof -
  {
    fix A B C
    assume "\<not> Col A B C"
    obtain D E F where "GradA A B C D E F" and "\<not> SAMS D E F A B C" 
      using archi__grada_destruction \<open>\<not> Col A B C\<close> assms by blast
    obtain P Q R where "GradAExp A B C P Q R" and "Obtuse P Q R \<or> D E F LeA P Q R" 
      using \<open>GradA A B C D E F\<close> gradaexp_destruction_aux by blast
    have "P \<noteq> Q" 
      using \<open>GradAExp A B C P Q R\<close> gradaexp_distincts by blast
    have "R \<noteq> Q" 
      using \<open>GradAExp A B C P Q R\<close> gradaexp_distincts by blast
    {
      assume "D E F LeA P Q R" 
      {
        assume "SAMS P Q R P Q R" 
        have "A B C LeA P Q R" 
          using \<open>GradAExp A B C P Q R\<close> grada__lea gradaexp__grada by blast
        hence "SAMS D E F A B C" 
          using sams_lea2__sams [where ?A'="P" and ?B'="Q" and ?C'="R" and 
              ?D'="P" and ?E'="Q" and ?F'="R"]
            \<open>SAMS P Q R P Q R\<close> \<open>D E F LeA P Q R\<close> by blast
        hence False 
          using \<open>\<not> SAMS D E F A B C\<close> by blast
      }
      hence "\<not> SAMS P Q R P Q R" 
        by blast
      hence "Obtuse P Q R" 
        using \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> nsams__obtuse by auto
    }
    hence "\<exists> P Q R. GradAExp A B C P Q R \<and> Obtuse P Q R" 
      using \<open>GradAExp A B C P Q R\<close> \<open>Obtuse P Q R \<or> D E F LeA P Q R\<close> by blast
  }
  thus ?thesis
    by blast
qed

end
end
