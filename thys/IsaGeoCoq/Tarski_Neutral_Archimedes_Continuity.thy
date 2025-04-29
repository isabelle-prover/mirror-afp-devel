(* IsaGeoCoq - Tarski_Neutral_Archimedes_Continuity.thy

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

theory Tarski_Neutral_Archimedes_Continuity

imports
  Tarski_Neutral_Archimedes
  Tarski_Neutral_Continuity
begin

context Tarski_neutral_dimensionless

begin

section "Archimedes continuity"

subsection "Definitions"

definition AlphaTmp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where
    "AlphaTmp A B \<equiv> \<lambda> X. X = A \<or> (A Out B X \<and> Reach A B A X)"

definition BetaTmp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  where
    "BetaTmp A B \<equiv> \<lambda> X. A Out B X \<and> \<not> Reach A B A X" 

definition NestedBis ::  "(nat \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'p \<Rightarrow> bool)=>bool"
  where
    "NestedBis A B \<equiv> 
(\<forall> n. \<exists> An Bn. A n An \<and> B n Bn) \<and>
(\<forall> n An An'. A n An \<and> A n An' \<longrightarrow> An = An') \<and>
(\<forall> n Bn Bn'. B n Bn \<and> B n Bn' \<longrightarrow> Bn = Bn') \<and>
(\<forall> n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn \<longrightarrow>
Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)"

definition CantorVariant :: bool
  where
    "CantorVariant \<equiv> \<forall> A B. NestedBis A B \<longrightarrow>
 (\<exists> X. \<forall> n An Bn. A n An \<and> B n Bn \<longrightarrow> Bet An X Bn)"

definition inj:: "('p \<Rightarrow> 'p) \<Rightarrow> bool"
  where
    "inj f \<equiv> \<forall> A B::'p. f A = f B \<longrightarrow> A = B" 

definition pres_bet:: "('p\<Rightarrow>'p) \<Rightarrow>bool"
  where 
    "pres_bet f \<equiv> \<forall> A B C. Bet A B C \<longrightarrow> Bet (f A) (f B) (f C)"

definition pres_cong :: "('p\<Rightarrow>'p) \<Rightarrow>bool"
  where
    "pres_cong f \<equiv> \<forall> A B C D. Cong A B C D \<longrightarrow> Cong (f A) (f B) (f C) (f D)"

definition extension:: "('p\<Rightarrow>'p) \<Rightarrow> bool"
  where
    "extension f \<equiv> inj f \<and> pres_bet f \<and> pres_cong f"
    (*
Definition completeness_for_planes := forall (Tm: Tarski_neutral_dimensionless)
  (Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm)
  (M : Tarski_2D Tm2)
  (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  extension f ->
  forall A, exists B, f B = A.

Definition completeness_for_3d_spaces := forall (Tm: Tarski_neutral_dimensionless)
  (Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm)
  (M : Tarski_3D Tm2)
  (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  extension f ->
  forall A, exists B, f B = A.
*)

definition inj_line :: "('p\<Rightarrow>'p)\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool"
  where
    "inj_line f P Q \<equiv> \<forall> A B. Col P Q A \<and> Col P Q B \<and> f A = f B \<longrightarrow> A = B"

definition pres_bet_line :: "('p\<Rightarrow>'p)\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool"
  where
    "pres_bet_line f P Q \<equiv> 
\<forall> A B C. Col P Q A \<and> Col P Q B \<and> Col P Q C \<and> Bet A B C 
\<longrightarrow> 
Bet (f A)(f B)(f C)"

definition pres_cong_line :: "('p\<Rightarrow>'p)\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool"
  where
    "pres_cong_line f P Q \<equiv> 
\<forall> A B C D. Col P Q A \<and> Col P Q B \<and> Col P Q C \<and> Col P Q D \<and> Cong A B C D 
\<longrightarrow> 
Cong (f A) (f B) (f C) (f D)"

definition line_extension :: "('p\<Rightarrow>'p)\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool"
  where
    "line_extension f P Q \<equiv> P \<noteq> Q \<and> inj_line f P Q \<and> pres_bet_line f P Q \<and> pres_cong_line f P Q"

(** Rmq: ici Tm = Tm2 **)
definition line_completeness :: bool
  where
    "line_completeness \<equiv> archimedes_axiom \<and> 
(\<forall> f. \<forall> P Q. line_extension f P Q 
\<longrightarrow>
(\<forall> A. Col (f P) (f Q) A \<longrightarrow> (\<exists> B. Col P Q B \<and> f B = A)))"

subsection "Propositions"

lemma archimedes_aux :
  assumes "\<forall> A B C. A Out B C \<longrightarrow> Reach A B A C" 
  shows "ArchimedesAxiom" 
proof -
  {
    fix A B C D :: 'p
    assume "A \<noteq> B" 
    have "Reach A B C D" 
    proof (cases "C = D")
      case True
      have "Grad A B B" 
        by (simp add: grad_equiv_coq_1)
      moreover have "C D Le A B" 
        by (simp add: True le_trivial)
      ultimately show ?thesis 
        using Reach_def by blast
    next
      case False
      hence "C \<noteq> D" 
        by simp
      obtain E where "A Out B E" and "Cong A E C D" 
        using False \<open>A \<noteq> B\<close> segment_construction_3 by blast
      obtain B' where "Grad A B B'" and "A E Le A B'" 
        using assms(1) Reach_def \<open>A Out B E\<close> by blast
      moreover have "C D Le A B'" 
        using \<open>Cong A E C D\<close> calculation(2) cong__le3412 le_transitivity by blast 
      ultimately show ?thesis 
        using Reach_def by blast
    qed
  }
  thus ?thesis 
    using archimedes_axiom_def by blast
qed

lemma dedekind_variant__archimedes: 
  assumes "DedekindVariant" 
  shows "archimedes_axiom" 
proof -
  {
    fix A B C
    assume "A Out B C"
    {
      assume "\<not> Reach A B A C"
      have "\<exists> X. \<forall> P Q. (P = A \<or> (A Out B P \<and> Reach A B A P)) \<and> 
                        (A Out B Q \<and> \<not> Reach A B A Q) \<longrightarrow> Bet P X Q" 
      proof -
        let ?Alpha = "(AlphaTmp A B)"
        let ?Beta = "(BetaTmp A B)"
        have "\<forall> Alpha Beta. \<forall> A C. (Alpha A \<and> Beta C \<and> 
                (\<forall> P. A Out P C \<longrightarrow> (Alpha P \<or> Beta P)) \<and> (\<forall> X Y. (Alpha X \<and> Beta Y) 
                \<longrightarrow> (Bet A X Y \<and> X \<noteq> Y))) \<longrightarrow> (\<exists> B'. \<forall> X Y. (Alpha X \<and> Beta Y) 
                       \<longrightarrow> Bet X B' Y)"
          using assms DedekindVariant_def by auto
        hence 2: "\<forall> A C. (?Alpha A \<and> ?Beta C \<and> (\<forall> P. A Out P C \<longrightarrow> (?Alpha P \<or> ?Beta P)) \<and> 
                   (\<forall> X Y. (?Alpha X \<and> ?Beta Y) \<longrightarrow> (Bet A X Y \<and> X \<noteq> Y))) 
                   \<longrightarrow> (\<exists> B'. \<forall> X Y. (?Alpha X \<and> ?Beta Y) \<longrightarrow> Bet X B' Y)"
          by simp
        have "?Alpha A" 
          by (simp add: AlphaTmp_def)
        moreover have "?Beta C" 
          by (simp add: BetaTmp_def \<open>A Out B C\<close> \<open>\<not> Reach A B A C\<close>)
        moreover have "\<forall> P. A Out P C \<longrightarrow> (?Alpha P \<or> ?Beta P)" 
          by (meson AlphaTmp_def BetaTmp_def \<open>A Out B C\<close> l6_6 l6_7)
        moreover {
          fix P Q
          assume "?Alpha P" and "?Beta Q" 
          hence "P = A \<or> (A Out B P \<and> Reach A B A P)" 
            using AlphaTmp_def by metis
          have "A Out B Q \<and> \<not> Reach A B A Q"
            using BetaTmp_def \<open>BetaTmp A B Q\<close> by auto
          hence "A Out B Q"
            by simp
          have "\<not> Reach A B A Q"
            using \<open>A Out B Q \<and> \<not> Reach A B A Q\<close> by auto
          have "Bet A P Q \<and> P \<noteq> Q" 
          proof -
            have "P = A \<longrightarrow> ?thesis" 
              using Out_def \<open>A Out B Q \<and> \<not> Reach A B A Q\<close> between_trivial2 by auto
            moreover {
              assume  "A Out B P" and "Reach A B A P"
              have "A Out P Q" 
                using Out_cases \<open>A Out B P\<close> \<open>A Out B Q\<close> l6_7 by blast
              hence "Bet A P Q \<or> Bet A Q P" 
                by (simp add: Out_def)
              moreover {
                assume "Bet A Q P"
                obtain B' where "Grad A B B'" and "A P Le A B'" 
                  using Reach_def \<open>Reach A B A P\<close> by blast
                hence "A Q Le A B'" 
                  using \<open>Bet A Q P\<close> l5_12_a le_transitivity by blast
                hence "Reach A B A Q" 
                  using Reach_def \<open>Grad A B B'\<close> by blast
                hence False 
                  by (simp add: \<open>\<not> Reach A B A Q\<close>)
                hence "Bet A P Q" 
                  by blast
              }
              ultimately have "Bet A P Q" 
                by blast
              moreover have "P \<noteq> Q" 
                using \<open>Reach A B A P\<close> \<open>\<not> Reach A B A Q\<close> by auto
              ultimately have "Bet A P Q \<and> P \<noteq> Q" 
                by simp
            }
            ultimately show ?thesis 
              using \<open>P = A \<or> A Out B P \<and> Reach A B A P\<close> by fastforce
          qed
        }
        hence "\<exists> B'. \<forall> X Y. (?Alpha X \<and> ?Beta Y) \<longrightarrow> Bet X B' Y" 
          using 2 calculation(1) calculation(2) calculation(3) by blast
        thus ?thesis 
          using AlphaTmp_def BetaTmp_def by simp
      qed
      then obtain X where "\<forall> P Q. (P = A \<or> (A Out B P \<and> Reach A B A P)) \<and> 
                                  (A Out B Q \<and> \<not> Reach A B A Q) \<longrightarrow> Bet P X Q" 
        by blast
      have "A \<noteq> B" 
        using \<open>A Out B C\<close> out_diff1 by blast
      have "C \<noteq> A" 
        using Out_def \<open>A Out B C\<close> by presburger
      have "Grad A B B" 
        by (simp add: grad_equiv_coq_1)
      have "B = A \<or> A Out B B \<and> Reach A B A B"           
        using Reach_def bet__le2313 between_trivial2 grad_equiv_coq_1 out_trivial by blast
      hence "Bet B X C" 
        by (simp add: \<open>A Out B C\<close> \<open>\<not> Reach A B A C\<close> 
            \<open>\<forall>P Q. (P = A \<or> A Out B P \<and> Reach A B A P) \<and> A Out B Q \<and> \<not> Reach A B A Q 
                   \<longrightarrow> Bet P X Q\<close>)
      have "A Out B X" 
        using \<open>A Out B C\<close> \<open>Bet B X C\<close> out_bet_out_1 by blast
      have "Bet A B C \<or> Bet A C B" 
        using Out_def \<open>A Out B C\<close> by auto
      {
        assume "Bet A C B"
        have "A C Le A B" 
          by (simp add: \<open>Bet A C B\<close> bet__le1213)
        hence "Reach A B A C" 
          using Reach_def \<open>Grad A B B\<close> by blast
        hence False 
          using \<open>\<not> Reach A B A C\<close> by auto
      }
      hence "Bet A B C" 
        using \<open>Bet A B C \<or> Bet A C B\<close> by blast
      {
        assume "Reach A B A X" 
        then obtain X1 where "X Out C X1" and "Cong X X1 A B" 
          by (metis \<open>A \<noteq> B\<close> \<open>\<not> Reach A B A C\<close> segment_construction_3)
        have "Bet A X X1" 
          by (meson Bet_cases \<open>Bet A B C\<close> \<open>Bet B X C\<close> \<open>X Out C X1\<close> 
              bet_out__bet between_exchange4)
        have "X Out X1 C" 
          using Out_cases \<open>X Out C X1\<close> by blast
        moreover have "Bet X1 X C" 
        proof -
          have "A Out B X1" 
            by (metis \<open>A \<noteq> B\<close> \<open>Bet A B C\<close> \<open>Bet A X X1\<close> \<open>Bet B X C\<close> bet_out 
                between_exchange4 between_inner_transitivity)
          moreover 
          obtain B' where "Grad A B B'" and "A X Le A B'" 
            using Reach_def \<open>Reach A B A X\<close> by blast
          obtain B1' where "Bet A B' B1'" and "Cong B' B1' A B" 
            using segment_construction by blast
          hence "Grad A B B1'" 
            using \<open>Grad A B B'\<close> \<open>Grad A B B\<close> cong_symmetry grad_sum by blast
          moreover have "X X1 Le B' B1'" 
            by (meson \<open>Cong B' B1' A B\<close> \<open>Cong X X1 A B\<close> cong__le3412 
                cong_reflexivity cong_symmetry l5_6)
          hence "A X1 Le A B1'" 
            using \<open>A X Le A B'\<close> \<open>Bet A B' B1'\<close> \<open>Bet A X X1\<close> bet2_le2__le1346 by force
          ultimately have "Reach A B A X1" 
            using Reach_def by blast
          show ?thesis 
            using \<open>A Out B C\<close> \<open>\<not> Reach A B A C\<close> \<open>A Out B X1\<close> \<open>Reach A B A X1\<close>
              \<open>\<forall>P Q. (P = A \<or> A Out B P \<and> Reach A B A P) \<and> A Out B Q \<and> \<not> Reach A B A Q 
                     \<longrightarrow> Bet P X Q\<close> by blast
        qed
        ultimately have "Bet X1 X C \<and> X Out X1 C" 
          by simp
        hence False 
          using not_bet_and_out by blast
      }
      moreover 
      {
        assume "\<not> Reach A B A X" 
        have "X \<noteq> B" 
          using \<open>A \<noteq> B\<close> \<open>B = A \<or> A Out B B \<and> Reach A B A B\<close> calculation by blast
        have "X A Le A B \<longrightarrow> False"             
          by (meson \<open>Bet A B C\<close> \<open>Bet B X C\<close> \<open>X \<noteq> B\<close> bet_le_eq between_exchange3 
              between_symmetry le_right_comm)
        moreover 
        {
          assume "A B Le X A" 
          have "Bet A B X" 
            using \<open>Bet A B C\<close> \<open>Bet B X C\<close> between_inner_transitivity by blast
          obtain X0 where "Bet X X0 A" and "Cong A B X X0"
            using Le_def \<open>A B Le X A\<close> by blast
          {
            assume "\<not> Reach A B A X0"
            have "X Out X0 B" 
              by (metis \<open>A \<noteq> B\<close> \<open>Bet A B X\<close> \<open>Bet X X0 A\<close> \<open>Cong A B X X0\<close> \<open>X \<noteq> B\<close> 
                  bet_out bet_out_1 cong_reverse_identity l6_6 l6_7 not_cong_3421)
            hence False
              by (metis \<open>A \<noteq> B\<close> \<open>Bet A B X\<close> \<open>Bet X X0 A\<close> \<open>Cong A B X X0\<close> \<open>X Out X0 B\<close> 
                  \<open>\<forall>P Q. (P = A \<or> A Out B P \<and> Reach A B A P) \<and> A Out B Q \<and> \<not> Reach A B A Q 
                         \<longrightarrow> Bet P X Q\<close> 
                  \<open>\<not> Reach A B A X0\<close> bet2__out bet_cong_eq between_symmetry between_trivial2 
                  not_bet_and_out not_cong_1243)
          }
          hence "Reach A B A X0" 
            by blast
          moreover 
          {
            assume "Reach A B A X0"
            obtain B' where "Grad A B B'" and "A X0 Le A B'" 
              using Reach_def calculation by blast
            obtain B1' where "Bet A B' B1'" and "Cong B' B1' A B" 
              using segment_construction by blast
            have "Grad A B B1'" 
              using Cong_cases \<open>Bet A B' B1'\<close> \<open>Cong B' B1' A B\<close> \<open>Grad A B B'\<close> 
                grad_stab by blast
            moreover have "X0 X Le B' B1'" 
              by (meson \<open>Cong A B X X0\<close> \<open>Cong B' B1' A B\<close> cong_pseudo_reflexivity 
                  cong_transitivity l5_6 le_reflexivity)
            hence "A X Le A B1'" 
              using \<open>A X0 Le A B'\<close> \<open>Bet A B' B1'\<close> \<open>Bet X X0 A\<close> bet2_le2__le1346 
                between_symmetry by blast
            ultimately have "Reach A B A X" 
              using Reach_def by blast
            hence False 
              by (simp add: \<open>\<not> Reach A B A X\<close>)
          }
          ultimately have False 
            by blast
        }
        ultimately have False
          using local.le_cases by blast
      }
      ultimately have False 
        by blast
    } 
    hence "Reach A B A C" 
      by blast
  }
  thus ?thesis
    using archimedes_aux by blast
qed

lemma dedekind__archimedes:
  assumes "DedekindsAxiom" 
  shows "archimedes_axiom" 
  using assms dedekind_equiv dedekind_variant__archimedes by blast

lemma nested_bis__nested:
  assumes "NestedBis A B" 
  shows "Nested A B" 
  using NestedBis_def Nested_def assms by presburger

lemma cantor__cantor_variant_1:
  assumes "CantorsAxiom" 
  shows "CantorVariant" 
  using CantorVariant_def CantorsAxiom_def assms nested_bis__nested by blast

lemma cantor__cantor_variant_2:
  assumes "CantorVariant"
  shows "CantorsAxiom" 
proof -
  { 
    fix A B
    assume "Nested A B" 
    then obtain fA::"nat\<Rightarrow>'p" where "\<forall> x. A x (fA x)"
      by (metis nested__ex_right nested_sym) 
    obtain fB::"nat\<Rightarrow>'p" where "\<forall> x. B x (fB x)"
      using \<open>Nested A B\<close> nested__ex_right nested_sym by metis
    let ?f1 = "\<lambda> n::nat. \<lambda> An::'p. An = fA n"
    let ?f2 = "\<lambda> n::nat. \<lambda> Bn::'p. Bn = fB n"
    have "(\<forall> n. (\<exists> An Bn. A n An \<and> B n Bn)) \<and> (\<forall> n An Am Bm Bn.
                    (A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn) 
                    \<longrightarrow> (Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm))"
      using \<open>Nested A B\<close> Nested_def by auto
    have "NestedBis ?f1 ?f2" 
    proof -
      have "(\<forall> n. \<exists> An Bn. ?f1 n An \<and> ?f2 n Bn)" 
        by simp
      moreover have "(\<forall> n An An'. ?f1 n An \<and> ?f1 n An' \<longrightarrow> An = An')" 
        by simp
      moreover have "(\<forall> n Bn Bn'. ?f2 n Bn \<and> ?f2 n Bn' \<longrightarrow> Bn = Bn')" 
        by simp
      moreover have "(\<forall> n An Am Bm Bn. ?f1 n An \<and> ?f1 (Suc n) Am \<and>  
                           ?f2 (Suc n) Bm \<and> ?f2 n Bn \<longrightarrow> 
                      Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)"
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
                    (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                     \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> 
          \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      ultimately show ?thesis 
        using NestedBis_def by presburger
    qed
    hence "\<exists> X. \<forall> n An Bn. An = fA n \<and> Bn = fB n  \<longrightarrow> Bet An X Bn"
      using assms(1) CantorVariant_def by blast
    then obtain X where "\<forall> n An Bn. An = fA n \<and> Bn = fB n  \<longrightarrow> Bet An X Bn"
      by blast
    {
      fix n An Bn
      assume "A n An" and "B n Bn"
      have "Bet An (fA (Suc n)) (fB (Suc n))" 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
                (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                 \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> 
          \<open>A n An\<close> \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      moreover have "Bet (fA (Suc n)) (fB (Suc n)) Bn" 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
               (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
               \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> \<open>B n Bn\<close> 
          \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      moreover have "fA (Suc n) \<noteq> fB (Suc n)" 
        using \<open>(\<forall>n. \<exists>An Bn. A n An \<and> B n Bn) \<and> 
                (\<forall>n An Am Bm Bn. A n An \<and> A (Suc n) Am \<and> B (Suc n) Bm \<and> B n Bn 
                  \<longrightarrow> Bet An Am Bm \<and> Bet Am Bm Bn \<and> Am \<noteq> Bm)\<close> 
          \<open>\<forall>x. A x (fA x)\<close> \<open>\<forall>x. B x (fB x)\<close> by blast
      moreover have "Bet (fA (Suc n)) X (fB (Suc n))" 
        by (simp add: \<open>\<forall>n An Bn. An = fA n \<and> Bn = fB n \<longrightarrow> Bet An X Bn\<close>)
      ultimately have "Bet An X Bn" 
        by (meson bet3__bet between_exchange4 outer_transitivity_between2)
    }
    hence "\<exists> X. \<forall> n An Bn. (A n An \<and> B n Bn) \<longrightarrow> Bet An X Bn" 
      by blast
  }
  thus ?thesis 
    using CantorsAxiom_def by blast
qed

lemma cantor__cantor_variant:
  shows "CantorsAxiom \<longleftrightarrow> CantorVariant" 
  using cantor__cantor_variant_1 cantor__cantor_variant_2 by blast

lemma inj_line_symmetry:
  assumes "inj_line f P Q"
  shows "inj_line f Q P" 
  by (metis NCol_cases assms inj_line_def)

lemma pres_bet_line_symmetry:
  assumes "pres_bet_line f P Q"
  shows "pres_bet_line f Q P"
  by (metis assms not_col_permutation_4 pres_bet_line_def)

lemma pres_cong_line_symmetry:
  assumes "pres_cong_line f P Q"
  shows "pres_cong_line f Q P" 
proof -
  { 
    fix A B C D
    assume "Col Q P A" and "Col Q P B" and "Col Q P C" and
      "Col Q P D" and "Cong A B C D"
    have "Col P Q A" 
      using NCol_cases \<open>Col Q P A\<close> by blast
    moreover have "Col P Q B" 
      using \<open>Col Q P B\<close> col_permutation_4 by blast
    moreover have "Col P Q C" 
      using NCol_cases \<open>Col Q P C\<close> by blast
    moreover have "Col P Q D" 
      using Col_cases \<open>Col Q P D\<close> by auto
    ultimately have "Cong (f A) (f B) (f C) (f D)" 
      using \<open>Cong A B C D\<close> assms pres_cong_line_def by blast
  }
  thus ?thesis 
    using assms not_col_permutation_4 pres_cong_line_def by blast
qed

lemma line_extension_symmetry:
  assumes "line_extension f P Q"
  shows "line_extension f Q P"
proof -
  have "Q \<noteq> P" 
    using assms line_extension_def by auto
  moreover have "inj_line f Q P" 
    using assms inj_line_symmetry line_extension_def by blast
  moreover have "pres_bet_line f Q P" 
    by (meson assms line_extension_def pres_bet_line_symmetry)
  moreover have "pres_cong_line f Q P" 
    by (meson assms line_extension_def pres_cong_line_symmetry)
  ultimately show ?thesis
    using line_extension_def by blast
qed

lemma inj_line_stability:
  assumes "Col P Q R" and
    "P \<noteq> R" and
    "inj_line f P Q"
  shows "inj_line f P R" 
proof -
  {
    fix A B
    assume "Col P R A" and "Col P R B" and "f A = f B"
    moreover have "Col P Q A" 
      by (meson assms(1) assms(2) calculation(1) colx not_col_distincts)
    moreover have "Col P Q B" 
      using assms(1) assms(2) calculation(2) col_trivial_3 colx by blast
    ultimately have "A = B" 
      using assms(3) inj_line_def by blast
  }
  thus ?thesis 
    using inj_line_def by force
qed

lemma pres_bet_line_stability:
  assumes "Col P Q R" and
    "P \<noteq> R" and
    "pres_bet_line f P Q"
  shows "pres_bet_line f P R" 
proof -
  {
    fix A B C
    assume "Col P R A" and "Col P R B" and "Col P R C" and "Bet A B C"
    have "Col P Q A" 
      using \<open>Col P R A\<close> assms(1) assms(2) col_trivial_3 colx by blast
    moreover have "Col P Q B" 
      using \<open>Col P R B\<close> assms(1) assms(2) col_trivial_3 colx by blast
    moreover have "Col P Q C" 
      using \<open>Col P R C\<close> assms(1) assms(2) col_trivial_3 colx by blast
    ultimately have "Bet (f A)(f B)(f C)" 
      using \<open>Bet A B C\<close> assms(3) pres_bet_line_def by blast
  }
  thus ?thesis 
    using pres_bet_line_def by force
qed

lemma pres_cong_line_stability:
  assumes "Col P Q R" and
    "P \<noteq> R" and
    "pres_cong_line f P Q"
  shows "pres_cong_line f P R" 
proof -
  {
    fix A B C D
    assume "Col P R A" and "Col P R B" and "Col P R C" and "Col P R D" and "Cong A B C D"
    have "Col P Q A" 
      using \<open>Col P R A\<close> assms(1) assms(2) col_trivial_3 colx by blast
    moreover have "Col P Q B" 
      using \<open>Col P R B\<close> assms(1) assms(2) col_trivial_3 colx by blast
    moreover have "Col P Q C" 
      by (meson \<open>Col P R C\<close> assms(1) assms(2) colx not_col_distincts)
    moreover have "Col P Q D" 
      by (meson \<open>Col P R D\<close> assms(1) assms(2) colx not_col_distincts)
    ultimately have "Cong (f A) (f B) (f C) (f D)" 
      using \<open>Cong A B C D\<close> assms(3) pres_cong_line_def by blast
  }
  thus ?thesis 
    using pres_cong_line_def by force
qed

lemma line_extension_stability:
  assumes "Col P Q R" and
    "P \<noteq> R" and
    "line_extension f P Q"
  shows "line_extension f P R" 
  using assms(1) assms(2) assms(3) inj_line_stability line_extension_def 
    pres_bet_line_stability pres_cong_line_stability by auto

lemma line_extension_reverse_bet:
  assumes "line_extension f P Q" and
    "Col P Q A" and
    "Col P Q B" and
    "Col P Q C" and
    "Bet (f A) (f B) (f C)"
  shows "Bet A B C" 
proof -
  have "pres_bet_line f P Q" 
    using assms(1) line_extension_def by auto
  have "inj_line f P Q" 
    using assms(1) line_extension_def by auto
  have "Col A B C" 
    using assms(1) assms(2) assms(3) assms(4) col3 line_extension_def by blast
  hence "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    by (simp add: Col_def)
  moreover {
    assume "Bet B C A"
    hence "f B = f C" 
      by (meson assms(1) assms(2) assms(3) assms(4) assms(5) between_equality_2 
          between_symmetry line_extension_def pres_bet_line_def)
    hence "B = C" 
      using assms(3) assms(4) inj_line_def \<open>inj_line f P Q\<close> by blast
    hence "Bet A B C" 
      by (simp add: between_trivial)
  }
  moreover {
    assume  "Bet C A B" 
    hence "f A = f B" 
      using \<open>pres_bet_line f P Q\<close> assms(2) assms(3) assms(4) assms(5) 
        between_equality between_symmetry pres_bet_line_def by blast
    hence "A = B" 
      using \<open>inj_line f P Q\<close> assms(2) assms(3) inj_line_def by blast
    hence "Bet A B C" 
      by (simp add: between_trivial2)
  }
  ultimately show ?thesis 
    by blast
qed

lemma pres_bet_line__col:
  assumes "P \<noteq> Q" and 
    "pres_bet_line f P Q" and
    "Col P Q A" and
    "Col P Q B" and
    "Col P Q C" 
  shows "Col (f A) (f B) (f C)"
proof -
  have "Col A B C"
    using col3 [where ?X="P" and ?Y="Q"] assms(1) assms(3) assms(4) assms(5) by blast
  thus ?thesis 
    by (meson Col_def assms(2) assms(3) assms(4) assms(5) pres_bet_line_def)
qed

lemma col2_diff_inj_line__diff:
  assumes "inj_line f P Q" and
    "Col P Q A" and
    "Col P Q B" and
    "A \<noteq> B"
  shows "f A \<noteq> f B" 
  using assms(1) assms(2) assms(3) assms(4) inj_line_def by blast

lemma extension__line_extension:
  assumes "P \<noteq> Q" and
    "extension f"
  shows "line_extension f P Q"
proof -
  have "inj f"
    using assms(2) extension_def by auto
  have "pres_bet f" 
    using assms(2) extension_def by auto
  have "pres_cong f"
    using assms(2) extension_def by auto
  moreover have "inj_line f P Q" 
    using \<open>local.inj f\<close> inj_line_def local.inj_def by blast
  moreover have "pres_bet_line f P Q"   
    using \<open>pres_bet f\<close> pres_bet_def pres_bet_line_def by auto
  moreover have "pres_cong_line f P Q"
    using \<open>pres_cong f\<close> pres_cong_def pres_cong_line_def by auto
  ultimately show ?thesis
    using line_extension_def assms(1) by blast
qed

lemma extension_reverse_bet:
  assumes "extension f" and
    "Bet (f A) (f B) (f C)" 
  shows "Bet A B C" 
proof (cases "(f A) = (f B)")
  case True
  have "inj f"
    using assms(1) extension_def by auto
  hence "A = B" 
    using True local.inj_def by blast
  then show ?thesis 
    by (simp add: between_trivial2)
next
  case False
  hence "(f A) \<noteq> (f B)" 
    by blast
  have "inj f"
    using assms(1) extension_def by auto
  obtain D where "Bet A B D" and "Cong B D B C" 
    using segment_construction by fastforce
  have "(f C) = (f D)"
  proof (rule between_cong_3 [where ?A="(f A)" and ?B="(f B)"])
    show "f A \<noteq> f B" 
      by (simp add: False)
    show "Bet (f A) (f B) (f C)"
      by (simp add: assms(2))
    show "Bet (f A) (f B) (f D)"
      using \<open>Bet A B D\<close> assms(1) extension_def pres_bet_def by blast
    show "Cong (f B) (f C) (f B) (f D)"
      using \<open>Cong B D B C\<close> assms(1) extension_def not_cong_3412 pres_cong_def by blast
  qed
  hence "C = D"
    using \<open>local.inj f\<close> local.inj_def by blast
  then show ?thesis 
    by (simp add: \<open>Bet A B D\<close>)
qed

lemma extension_reverse_col:
  assumes "extension f" and
    "Col (f A) (f B) (f C)"
  shows "Col A B C" 
proof -
  have "Bet (f A) (f B) (f C) \<longrightarrow> Bet A B C" 
    using assms(1) extension_reverse_bet by blast
  moreover have "Bet (f B) (f C) (f A) \<longrightarrow> Bet B C A" 
    using assms(1) extension_reverse_bet by blast
  moreover have "Bet (f C) (f A) (f B) \<longrightarrow> Bet C A B" 
    using assms(1) extension_reverse_bet by blast
  ultimately show ?thesis 
    using Col_def assms(1) assms(2) extension_reverse_bet by blast
qed

(** The following section is inspired by Theorem 32 of Hilbert's Foundations of Geometry 
    (10th edition).
    It deduces completeness of a 2 or 3-dimensional space from completeness of lines.
    The original proof is due to Paul Bernays. *)

lemma line_completeness_aux: 
  assumes "line_completeness" and
    "archimedes_axiom" and
    "extension f" and
    "\<not> Col P Q R" and
    "Coplanar (f P) (f Q) (f R) A"
  shows "\<exists> B. Coplanar P Q R B \<and> f B = A"
proof -
  have "archimedes_axiom"
    using assms(1) line_completeness_def by blast
  have "\<forall> f. \<forall> P Q. line_extension f P Q \<longrightarrow>
(\<forall> A. Col (f P) (f Q) A \<longrightarrow> (\<exists> B. Col P Q B \<and> f B = A))" 
    using assms(1) line_completeness_def by blast
  {
    fix X Y ::'p
    assume "X \<noteq> Y"
    hence "line_extension f X Y" 
      by (simp add: assms(3) extension__line_extension)
  }
  obtain S where "S Midpoint P Q" 
    using MidR_uniq_aux by blast
  show "\<exists> B. Coplanar P Q R B \<and> f B = A"
  proof (cases "Col (f R) (f S) A")
    case True
    {
      assume "R = S"
      hence "Col P Q R" 
        using \<open>S Midpoint P Q\<close> col_permutation_1 midpoint_col by blast
      hence False 
        by (simp add: assms(4))
    }
    hence "R \<noteq> S" 
      by blast
    hence "\<exists> B. Col R S B \<and> (f B) = A" 
      using assms(1) line_completeness_def True \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> 
      by presburger
    then obtain B where "Col R S B" and "(f B) = A"
      by blast
    moreover
    hence "Coplanar P Q R B" 
      using Coplanar_def Midpoint_def \<open>S Midpoint P Q\<close> bet_col1 between_exchange2 
        between_symmetry not_col_permutation_5 point_construction_different by meson
    ultimately show ?thesis
      by blast
  next
    case False
    hence "\<not> Col (f R) (f S) A"
      by simp
    show ?thesis 
    proof (cases "Col (f P) (f Q) A")
      case True
      have "\<exists> B. Col P Q B \<and> (f B) = A" 
        using assms(1) line_completeness_def by (metis True 
            \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> assms(4) col_permutation_2 col_trivial_3)
      then obtain B0 where "Col P Q B0" and "f B0 = A" 
        by blast
      hence "Coplanar P Q R B0" 
        using ncop__ncols by blast
      thus ?thesis 
        using \<open>f B0 = A\<close> by blast
    next
      case False
      hence "\<not> Col (f P) (f Q) A"
        by simp
      hence "\<exists> X. Col A (f S) X \<and> (BetS (f P) X (f R) \<or> BetS (f Q) X (f R))" 
      proof -
        have "Coplanar (f P) (f Q) (f R) A" 
          by (simp add: assms(5))
        moreover have "\<not> Col (f R) (f S) A" 
          by (simp add: \<open>\<not> Col (f R) (f S) A\<close>)
        moreover have "\<not> Col (f P) (f Q) A" 
          by (simp add: False)
        moreover have "BetS (f P) (f S)(f Q)" 
          by (metis BetS_def False Midpoint_def \<open>S Midpoint P Q\<close> assms(3) col_trivial_3 
              extension_def local.inj_def midpoint_distinct_1 not_col_permutation_5 pres_bet_def)
        ultimately show ?thesis
          by (simp add: hilbert_s_version_of_pasch)
      qed
      then obtain X where "Col A (f S) X" and "BetS (f P) X (f R) \<or> BetS (f Q) X (f R)"
        by blast
      have "\<exists> Y. Coplanar P Q R Y \<and> (f Y) = X" 
      proof -
        {
          assume "BetS (f P) X (f R)"
          hence "\<exists> Y. Col P R Y \<and> (f Y) = X"
            using assms(1) line_completeness_def by (metis BetSEq Col_def 
                \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> between_symmetry)
          hence "\<exists> Y. Coplanar P Q R Y \<and> (f Y) = X"
            using ncop__ncols by blast
        }
        moreover {
          assume "BetS (f Q) X (f R)"
          hence "\<exists> Y. Col Q R Y \<and> (f Y) = X" 
            using assms(1) line_completeness_def by (metis BetSEq Col_def 
                \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> between_symmetry)
          hence "\<exists> Y. Coplanar P Q R Y \<and> (f Y) = X" 
            using ncop__ncols by blast
        }
        ultimately show ?thesis 
          using \<open>BetS (f P) X (f R) \<or> BetS (f Q) X (f R)\<close> by blast
      qed
      then obtain Y where "Coplanar P Q R Y" and "(f Y) = X" 
        by blast
      {
        assume "S = Y"
        have "Bet P S Q" 
          using Midpoint_def \<open>S Midpoint P Q\<close> by auto
        hence "Bet (f P) (f S) (f Q)" 
          using assms(3) extension_def pres_bet_def by blast
        have "BetS (f P) (f S) (f R) \<or> BetS (f Q) (f S) (f R)" 
          by (simp add: \<open>BetS (f P) X (f R) \<or> BetS (f Q) X (f R)\<close> \<open>S = Y\<close> \<open>f Y = X\<close>)
        moreover
        have "BetS (f P) (f S) (f R) \<longrightarrow> Col (f P) (f Q) (f R)" 
          using BetSEq Col_def \<open>Bet (f P) (f S) (f Q)\<close> between_symmetry l5_1 by blast
        moreover {
          assume "BetS (f Q) (f S) (f R)" 
          have "f S \<noteq> f Q" 
            by (metis BetSEq \<open>BetS (f Q) (f S) (f R)\<close>)
          moreover have "Col (f S) (f Q) (f P)" 
            by (simp add: Col_def \<open>Bet (f P) (f S) (f Q)\<close>)
          moreover have "Col (f S) (f Q) (f R)" 
            using BetSEq Bet_cases Col_def \<open>BetS (f Q) (f S) (f R)\<close> by blast
          ultimately have "Col (f P) (f Q) (f R)" 
            using col3 col_trivial_2 by blast
        }
        ultimately have "Col (f P) (f Q) (f R)" 
          by blast
        hence "Col P Q R"
          using assms(3) extension_reverse_col by blast
        hence False 
          by (simp add: assms(4))
      }
      hence "S \<noteq> Y" 
        by blast
      obtain B where "Col S Y B" and "(f B) = A" 
        using assms(1) line_completeness_def Col_cases \<open>Col A (f S) X\<close> \<open>S = Y \<Longrightarrow> False\<close> 
          \<open>\<And>Y X. X \<noteq> Y \<Longrightarrow> line_extension f X Y\<close> \<open>f Y = X\<close> by blast
      have "Coplanar P Q R S" 
        using Col_def Midpoint_def \<open>S Midpoint P Q\<close> between_symmetry ncop__ncols by blast
      hence "Coplanar P Q R B" 
        using col_cop2__cop [where ?U = "S" and ?V = "Y"] \<open>Col S Y B\<close> \<open>Coplanar P Q R Y\<close> 
          \<open>S \<noteq> Y\<close> by blast
      thus ?thesis 
        using \<open>f B = A\<close> by blast
    qed
  qed
qed

(*lemma line_completeness__completeness_for_planes:
  assumes "line_completeness" 
  shows "completeness_for_planes" 
*)

  (**    All these properties are known to be equivalent in an arbitrary Hilbert plane (Tarski_2D)
  as shown by Strommer, but we don't have formalized the proof yet.

  We have the following proofs:
  - five equivalent variants of the circle-circle continuity axiom;
  - three equivalent variants of the line-circle continuity axiom;
  - the implication from the circle-circle continuity axiom to the line-circle continuity axiom.

  Since we have proved the circle-circle continuity axiom to follow 
  from Tarski's axiom of continuity,
  all these properties do.
*)

lemma segment_circle__one_point_line_circle_R1:
  assumes "SegmentCircle" 
  shows "OnePointLineCircle" 
proof -
  {
    fix A B U V P
    assume "Col U V P" and "U \<noteq> V" and "Bet A P B" 
    have "\<exists> Z. Col U V Z \<and> Z OnCircle A B" 
    proof (cases "A = B")
      case True
      thus ?thesis 
        using \<open>Bet A P B\<close> \<open>Col U V P\<close> between_identity onc212 by blast
    next
      case False
      hence "A \<noteq> B" 
        by simp
      have "P InCircle A B" 
        by (simp add: InCircle_def \<open>Bet A P B\<close> bet__le1213)
      obtain W where "U \<noteq> W" and "V \<noteq> W" and "P \<noteq> W" and "Col U V W" 
        using \<open>Col U V P\<close> diff_col_ex3 by blast
      show ?thesis 
      proof (cases "A = P")
        case True
        obtain Q where "Bet W A Q" and "Cong A Q A B" 
          using segment_construction by blast
        hence "Q OutCircle A B" 
          using OnCircle_def onc__outc by blast
        then obtain Z where "Bet A Z Q" and "Z OnCircle A B" 
          using segment_circle_def True \<open>P InCircle A B\<close> assms by blast
        have "Col U V Z"
          by (metis Col_def OnCircle_def True \<open>Bet A Z Q\<close> \<open>Bet W A Q\<close> 
              \<open>Col U V P\<close> \<open>Col U V W\<close> \<open>Cong A Q A B\<close> \<open>P \<noteq> W\<close> \<open>Z OnCircle A B\<close> 
              bet_cong_eq between_symmetry between_trivial col_transitivity_1) 
        thus ?thesis 
          using \<open>Z OnCircle A B\<close> by blast
      next
        case False
        hence "A \<noteq> P" 
          by simp
        obtain Q0 where "Bet W P Q0" and "Cong P Q0 P A" 
          using segment_construction by blast
        obtain Q where "Bet P Q0 Q" and "Cong Q0 Q A B" 
          using segment_construction by blast
        have "P Out Q Q0" 
          by (metis False \<open>Bet P Q0 Q\<close> \<open>Cong P Q0 P A\<close> bet_out cong_reverse_identity l6_6)
        hence "Q Q0 Le Q A" 
          using \<open>Cong P Q0 P A\<close> not_cong_3412 triangle_reverse_inequality by blast
        hence "Q OutCircle A B" 
          using l5_6 by (meson OutCircle_def \<open>Cong Q0 Q A B\<close> 
              cong_pseudo_reflexivity not_cong_4312)
        then obtain Z where "Bet P Z Q" and "Z OnCircle A B" 
          using segment_circle_def \<open>P InCircle A B\<close> assms by blast
        hence "Col U V Z" 
          by (metis Col_def Out_def \<open>Bet W P Q0\<close> \<open>Col U V P\<close> 
              \<open>Col U V W\<close> \<open>P Out Q Q0\<close> \<open>P \<noteq> W\<close> colx)
        then show ?thesis 
          using \<open>Z OnCircle A B\<close> by blast
      qed 
    qed
  }
  thus ?thesis 
    using one_point_line_circle_def by blast
qed

lemma segment_circle__one_point_line_circle_R2:
  assumes "OnePointLineCircle" 
  shows "SegmentCircle" 
proof -
  {
    fix A B P Q
    assume "P InCircle A B" and
      "Q OutCircle A B" 
    have "\<exists> Z. Bet P Z Q \<and> Z OnCircle A B" 
    proof (cases "A = B")
      case True
      thus ?thesis 
        using \<open>P InCircle A B\<close> between_trivial2 inc_eq onc212 by blast
    next
      case False
      hence "A \<noteq> B" 
        by simp
      show ?thesis
      proof (cases "P = Q")
        case True
        then show ?thesis 
          using \<open>P InCircle A B\<close> \<open>Q OutCircle A B\<close> inc_outc__onc not_bet_distincts by blast
      next
        case False
        hence "P \<noteq> Q"
          by simp
        show ?thesis 
        proof (cases "Cong A B A Q")
          case True
          then show ?thesis 
            by (meson OnCircle_def not_bet_distincts onc_sym)
        next
          case False
          hence "\<not> Cong A B A Q"
            by simp
          then obtain B' where "Cong A B A B'" and "Bet A P B'"
            using OnCircle_def \<open>P InCircle A B\<close> inc__radius onc_sym by blast
          obtain Z1 where "Col P Q Z1" and "Z1 OnCircle A B'" 
            using assms one_point_line_circle_def 
            by (meson \<open>Bet A P B'\<close> \<open>P \<noteq> Q\<close> not_col_distincts)
          have "Z1 OnCircle A B" 
            using EqC_def \<open>Cong A B A B'\<close> \<open>Z1 OnCircle A B'\<close> eqc_chara_2 by presburger
          have "Bet P Z1 Q \<longrightarrow> ?thesis" 
            using \<open>Z1 OnCircle A B\<close> by auto
          moreover 
          {
            assume "Z1 Out P Q" 
            obtain Z2 where "Z2 OnCircle A B" and "Bet Z1 P Z2" 
              using \<open>P InCircle A B\<close> \<open>Z1 OnCircle A B\<close> chord_completion by blast
            have "Bet Z1 Z2 Q" 
            proof -
              have "Z1 Out Z2 Q" 
                by (metis Out_def \<open>Bet Z1 P Z2\<close> \<open>Z1 Out P Q\<close> bet_neq12__neq l6_7)
              moreover have "Q Out Z1 Z2" 
              proof (rule col_inc2_outcs__out [where ?A="A" and ?B="B"])
                show "Z1 InCircle A B" 
                  by (simp add: \<open>Z1 OnCircle A B\<close> onc__inc) 
                show "Z2 InCircle A B" 
                  using \<open>Z2 OnCircle A B\<close> onc__inc by auto 
                show "Col Z1 Z2 Q" 
                  by (simp add: calculation out_col)
                show "Q OutCircleS A B" 
                  using False OnCircle_def \<open>Q OutCircle A B\<close> circle_cases 
                    not_cong_3412 outc__nincs_1 by blast
              qed
              ultimately show ?thesis 
                using out2__bet by blast
            qed
            hence "Bet P Z2 Q" 
              using \<open>Bet Z1 P Z2\<close> between_exchange3 by blast
            hence ?thesis 
              using \<open>Z2 OnCircle A B\<close> by blast
          }
          moreover have "\<not> Col P Z1 Q \<longrightarrow> ?thesis" 
            using Col_perm \<open>Col P Q Z1\<close> by blast
          ultimately
          show ?thesis 
            using l6_4_2 by blast
        qed
      qed
    qed
  }
  thus ?thesis 
    by (simp add: segment_circle_def)
qed

lemma segment_circle__one_point_line_circle:
  shows "SegmentCircle \<longleftrightarrow> OnePointLineCircle" 
  using segment_circle__one_point_line_circle_R1 
    segment_circle__one_point_line_circle_R2 by blast

lemma one_point_line_circle__two_points_line_circle_R1 :
  assumes "one_point_line_circle" 
  shows "two_points_line_circle"
proof -
  {
    fix A B U V P
    assume "Col U V P" and "U \<noteq> V" and "Bet A P B"
    have "\<exists> Z1 Z2. Col U V Z1 \<and> Z1 OnCircle A B \<and>
                Col U V Z2 \<and> Z2 OnCircle A B \<and>
                Bet Z1 P Z2 \<and> (P \<noteq> B \<longrightarrow> Z1 \<noteq> Z2)" 
    proof (cases "P = B")
      case True
      then show ?thesis 
        using \<open>Col U V P\<close> between_trivial2 onc212 by blast
    next
      case False
      hence "P \<noteq> B" 
        by simp
      obtain Z1 where "Col U V Z1" and "Z1 OnCircle A B" 
        using \<open>Bet A P B\<close> \<open>Col U V P\<close> \<open>U \<noteq> V\<close> assms one_point_line_circle_def by blast
      have "P InCircle A B" 
        using \<open>Bet A P B\<close> bet_inc2__inc inc112 onc212 onc__inc by blast
      then obtain Z2 where "Z2 OnCircle A B" and "Bet Z1 P Z2" 
        using chord_completion \<open>Z1 OnCircle A B\<close> by blast
      have "Z1 \<noteq> P" 
        using False \<open>Bet A P B\<close> \<open>Z1 OnCircle A B\<close> between_cong onc212 onc2__cong by blast
      thus ?thesis 
        by (metis \<open>Col U V P\<close> \<open>Col U V Z1\<close> \<open>Z1 OnCircle A B\<close> 
            \<open>\<And>thesis. (\<And>Z2. \<lbrakk>Z2 OnCircle A B ; Bet Z1 P Z2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
            bet_col between_equality colx outer_transitivity_between point_construction_different)
    qed
  }
  thus ?thesis 
    using two_points_line_circle_def by blast
qed

lemma one_point_line_circle__two_points_line_circle_R2 :
  assumes "two_points_line_circle"
  shows "one_point_line_circle" 
  using assms two_points_line_circle_def one_point_line_circle_def by blast

lemma one_point_line_circle__two_points_line_circle :
  shows "one_point_line_circle \<longleftrightarrow> two_points_line_circle" 
  using one_point_line_circle__two_points_line_circle_R1 
    one_point_line_circle__two_points_line_circle_R2 by blast

lemma circle_circle_bis__circle_circle_axiom_R1: 
  assumes "circle_circle_bis" 
  shows "circle_circle_axiom" 
proof -
  {
    fix A B C D B' D'
    assume "Cong A B' A B" and "Cong C D' C D" and
      "Bet A D' B" and "Bet C B' D"
    have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D"
    proof -
      have "D' OnCircle C D" 
        by (simp add: OnCircle_def \<open>Cong C D' C D\<close>)
      moreover have "D' InCircle A B" 
        using \<open>Bet A D' B\<close> bet_inc2__inc inc112 inc__outc incs__inc outc__nincs by blast
      moreover have "B' OnCircle A B" 
        by (simp add: OnCircle_def \<open>Cong A B' A B\<close>)
      moreover have "B' InCircle C D" 
        using \<open>Bet C B' D\<close> bet_inc2__inc inc112 onc212 onc__inc by blast
      ultimately show ?thesis
        using assms circle_circle_bis_def by blast
    qed
    hence "\<exists> Z. Cong A Z A B \<and> Cong C Z C D" 
      using OnCircle_def by blast
  }
  thus ?thesis 
    using circle_circle_axiom_def by blast
qed

lemma circle_circle_bis__circle_circle_axiom_R2:
  assumes "circle_circle_axiom" 
  shows "circle_circle_bis" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "P InCircle A B" and "Q OnCircle A B" and "Q InCircle C D"
    hence "A P Le A Q" 
      using InCircle_def OnCircle_def cong_reflexivity l5_6 onc_sym by blast
    then obtain Q' where "Bet A P Q'" and "Cong A Q' A Q" 
      using l5_5_1 by blast
    have "C Q Le C P" 
      using InCircle_def OnCircle_def \<open>P OnCircle C D\<close> \<open>Q InCircle C D\<close> 
        cong__le3412 le_transitivity by blast
    then obtain P' where "Bet C Q P'" and "Cong C P' C P" 
      using l5_5_1 by blast
    have "Cong A Q A Q'" 
      using \<open>Cong A Q' A Q\<close> not_cong_3412 by blast
    moreover have "Cong C P C P'" 
      by (simp add: \<open>Cong C P' C P\<close> cong_symmetry)
    ultimately obtain Z where "Cong A Z A Q'" and "Cong C Z C P'" 
      using \<open>Bet A P Q'\<close> \<open>Bet C Q P'\<close> assms circle_circle_axiom_def by blast
    have "Z OnCircle A B" 
      using OnCircle_def \<open>Cong A Q' A Q\<close> \<open>Cong A Z A Q'\<close> 
        \<open>Q OnCircle A B\<close> cong_transitivity by blast
    moreover have "Z OnCircle C D" 
      using OnCircle_def \<open>Cong C P' C P\<close> \<open>Cong C Z C P'\<close> 
        \<open>P OnCircle C D\<close> cong_transitivity by blast
    ultimately have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
      by blast
  }
  thus ?thesis 
    using circle_circle_bis_def by blast
qed

lemma circle_circle_bis__circle_circle_axiom:
  shows "circle_circle_bis \<longleftrightarrow> circle_circle_axiom" 
  using circle_circle_bis__circle_circle_axiom_R1 
    circle_circle_bis__circle_circle_axiom_R2 by blast

lemma circle_circle__circle_circle_bis:
  assumes "circle_circle"
  shows "circle_circle_bis" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "P InCircle A B" and "Q OnCircle A B" and "Q InCircle C D"
    have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
    proof (cases "P = Q")
      case True
      thus ?thesis 
        using \<open>P OnCircle C D\<close> \<open>Q OnCircle A B\<close> by blast
    next
      case False
      hence "P \<noteq> Q"
        by simp
      obtain P' where "P' OnCircle C D" and "Bet P Q P'" 
        using \<open>P OnCircle C D\<close> \<open>Q InCircle C D\<close> chord_completion by blast
      obtain Q' where "Q' OnCircle A B" and "Bet Q P Q'" 
        using \<open>P InCircle A B\<close> \<open>Q OnCircle A B\<close> chord_completion by blast
      have "P' OutCircle A B" 
        by (metis False \<open>Bet P Q P'\<close> \<open>P InCircle A B\<close> \<open>Q OnCircle A B\<close> 
            bet_inc2__incs incs__inc onc__outc outc__nincs) 
      thus ?thesis 
        using \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> \<open>P' OnCircle C D\<close> 
          assms circle_circle_def by blast
    qed
  }
  thus ?thesis 
    using circle_circle_bis_def by blast
qed

lemma circle_circle_bis__one_point_line_circle_aux:
  assumes "circle_circle_bis" and
    "Col U V P" and "U \<noteq> V" and "Bet A P B" and "\<not> Per A U V"
  shows "\<exists> Z. Col U V Z \<and> Z OnCircle A B" 
proof (cases "Col U V B")
  case True
  thus ?thesis 
    using onc212 by blast
next
  case False
  hence "\<not> Col U V B" 
    by simp
  show ?thesis 
  proof (cases "A = P")
    case True
    obtain W where "U \<noteq> W" and "V \<noteq> W" and "A \<noteq> W" and "Col U V W" 
      using assms(2) diff_col_ex3 by blast
    obtain Z where "Bet W A Z" and "Cong A Z A B" 
      using segment_construction by blast
    hence "Col U V Z" 
      by (metis True \<open>A \<noteq> W\<close> \<open>Col U V W\<close> assms(2) bet_col col3 not_col_distincts)
    moreover have "Z OnCircle A B" 
      by (simp add: OnCircle_def \<open>Cong A Z A B\<close>)
    ultimately show ?thesis 
      by blast
  next
    case False
    hence "A \<noteq> P" 
      by simp
    obtain C where "A C Reflect U V" 
      using l10_6_existence by blast
    obtain D where "B D Reflect U V" 
      using l10_6_existence by blast
    hence "Bet C P D" 
      using \<open>A C Reflect U V\<close> assms(4) assms(2) assms(3) image_gen_preserves_bet 
        l10_6_existence local.image_id by blast
    have "Cong B P D P" 
      using \<open>B D Reflect U V\<close> assms(3) assms(2) is_image_col_cong by blast
    have "Cong P D P B" 
      using Cong_cases \<open>Cong B P D P\<close> by blast
    hence "D InCircle A B" 
      using triangle_inequality InCircle_def assms(4) by blast 
    have "Cong P B P D" 
      using \<open>Cong B P D P\<close> not_cong_2143 by blast
    hence "B InCircle A B" 
      by (simp add: onc212 onc__inc)
    have "B InCircle C D" 
      using InCircle_def \<open>Bet C P D\<close> \<open>Cong P B P D\<close> triangle_inequality by blast
    then obtain Z0 where "Z0 OnCircle A B" and "Z0 OnCircle C D" 
      using assms(1) circle_circle_bis_def \<open>D InCircle A B\<close> onc212 by blast
    then obtain Z where "Z OnCircle A B" and "Z OnCircle C D" and "Coplanar A C U Z" 
      using circle_circle_cop by blast
    have "Col U V Z" 
    proof -
      {
        assume "A = C" 
        hence "A A Reflect U V" 
          using \<open>A C Reflect U V\<close> by auto
        hence "Col A U V" 
          by (simp add: l10_8)
        hence False 
          by (metis False \<open>\<not> Col U V B\<close> assms(2) assms(3) assms(4) bet_col 
              col_permutation_1 col_transitivity_1)
      }
      moreover have "Cong A B C D" 
        by (meson \<open>B D Reflect U V\<close> \<open>A C Reflect U V\<close> l10_10 not_cong_3412)
      hence "Cong A B C Z" 
        using OnCircle_def \<open>Z OnCircle C D\<close> cong_symmetry cong_transitivity by blast
      hence "Cong A Z C Z" 
        using OnCircle_def \<open>Z OnCircle A B\<close> cong_inner_transitivity onc_sym by blast
      moreover 
      { 
        assume "Col C U A" 
        have "A = C \<longrightarrow> False" 
          using calculation(1) by blast
        moreover 
        {
          assume "A \<noteq> C" 
          have "A C ReflectL U V" 
            using assms(3) \<open>A C Reflect U V\<close> is_image_is_image_spec by blast
          hence "U ReflectLAt A C U V" 
            by (meson \<open>A \<noteq> C\<close> \<open>Col C U A\<close> image_image_in not_col_distincts 
                not_col_permutation_3)
          hence "U V Perp C A \<or> C = A" 
            using ReflectLAt_def by blast
          hence "U V Perp C A" 
            using \<open>A \<noteq> C\<close> by blast
          hence "False" 
          proof (cases "A = U")
            case True
            then show ?thesis 
              using False \<open>\<not> Col U V B\<close> assms(2) assms(4) bet_col colx 
                not_col_distincts by blast
          next
            case False
            have "U A Perp U V" 
              by (metis False Perp_cases \<open>A \<noteq> C\<close> \<open>Col C U A\<close> \<open>U V Perp C A \<or> C = A\<close>
                  not_col_permutation_1 perp_col1)
            thus ?thesis 
              using assms(5) perp_per_2 by auto
          qed
        }
        ultimately have False 
          by blast
      }
      hence "\<not> Col C U A"
        by blast
      have "Coplanar C U A V" 
        using \<open>A C Reflect U V\<close> coplanar_perm_8 reflect__coplanar by blast
      have "Coplanar C U A Z" 
        by (simp add: \<open>Coplanar A C U Z\<close> coplanar_perm_8)
      hence "Coplanar U A V Z" 
        using \<open>Coplanar C U A V\<close> \<open>\<not> Col C U A\<close> coplanar_trans_1 by blast
      hence "Coplanar U V A Z" 
        using ncoplanar_perm_2 by blast
      ultimately show ?thesis 
        using \<open>A C Reflect U V\<close> cong_cop_image__col by blast
    qed
    thus ?thesis 
      using \<open>Z OnCircle A B\<close> by blast
  qed
qed

lemma circle_circle_bis__one_point_line_circle:
  assumes "circle_circle_bis" 
  shows "one_point_line_circle" 
proof -
  {
    fix A B U V P
    assume "Col U V P" and "U \<noteq> V" and "Bet A P B"
    have "\<exists> Z. Col U V Z \<and> Z OnCircle A B" 
    proof (cases "Per A U V")
      case True
      hence "\<not> Per A V U" 
        using \<open>U \<noteq> V\<close> l8_7 by blast
      then obtain Z where "Col V U Z \<and> Z OnCircle A B" 
        using Col_cases \<open>Bet A P B\<close> \<open>Col U V P\<close> \<open>U \<noteq> V\<close> 
          circle_circle_bis__one_point_line_circle_aux assms(1) by blast
      thus ?thesis 
        using Col_cases by blast
    next
      case False
      thus ?thesis 
        using \<open>Bet A P B\<close> \<open>Col U V P\<close> \<open>U \<noteq> V\<close> assms(1)
          circle_circle_bis__one_point_line_circle_aux by auto
    qed
  }
  thus ?thesis 
    using one_point_line_circle_def by blast
qed

lemma circle_circle__circle_circle_two_R1 :
  assumes "circle_circle" 
  shows "circle_circle_two" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and
      "P InCircle A B" and "Q OutCircle A B"
    have "\<exists> Z1 Z2. Z1 OnCircle A B \<and> Z1 OnCircle C D \<and>
    Z2 OnCircle A B \<and> Z2 OnCircle  C D \<and>
    ((P InCircleS A B \<and> Q OutCircleS A B)\<longrightarrow>Z1 \<noteq> Z2)" 
    proof (cases "A = C")
      case True
      have "Cong A B A D" 
      proof -
        have "A B Le A D" 
        proof -
          have "A B Le A Q" 
            using OutCircle_def \<open>Q OutCircle A B\<close> by blast
          moreover have "Cong A B A B" 
            by (simp add: cong_reflexivity)
          moreover have "Cong A Q A D" 
            using OnCircle_def True \<open>Q OnCircle C D\<close> by blast
          ultimately show ?thesis 
            using l5_6 by blast
        qed
        moreover have "A D Le A B" 
        proof -
          have "A P Le A B" 
            using InCircle_def \<open>P InCircle A B\<close> by blast
          moreover have "Cong A P A D" 
            using OnCircle_def True \<open>P OnCircle C D\<close> by auto
          moreover have "Cong A B A B" 
            by (simp add: cong_reflexivity)
          ultimately show ?thesis 
            using l5_6 by blast
        qed
        ultimately show ?thesis 
          using le_anti_symmetry by blast
      qed
      have "P OnCircle A B" 
        using EqC_def True \<open>Cong A B A D\<close> \<open>P OnCircle C D\<close> eqc_chara_2 by presburger
      moreover have "P OnCircle C D" 
        using \<open>P OnCircle C D\<close> by auto
      moreover have "(P InCircleS A B \<and> Q OutCircleS A B)\<longrightarrow>P \<noteq> P" 
        using calculation(1) onc__outc outc__nincs by blast
      ultimately show ?thesis 
        by blast
    next
      case False
      obtain Z1 where "Z1 OnCircle A B" and "Z1 OnCircle C D" 
        using \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> \<open>Q OnCircle C D\<close> \<open>Q OutCircle A B\<close> 
          assms circle_circle_def by blast
      obtain Z2 where "Z1 Z2 Reflect A C" 
        using l10_6_existence by fastforce
      have "Cong Z1 C Z2 C" 
        by (metis False \<open>Z1 Z2 Reflect A C\<close> image_triv is_image_col_cong is_image_rev l10_8)
      have "Cong Z1 A Z2 A" 
      proof (rule is_image_col_cong [where ?A="A" and ?B="C"])
        show "A \<noteq> C" 
          by (simp add: False)
        show "Z1 Z2 Reflect A C" 
          by (simp add: \<open>Z1 Z2 Reflect A C\<close>)
        show "Col A C A" 
          by (simp add: col_trivial_3)
      qed
      have "Z2 OnCircle A B" 
        by (meson OnCircle_def \<open>Cong Z1 A Z2 A\<close> \<open>Z1 OnCircle A B\<close> 
            cong_transitivity not_cong_4321)
      moreover have "Z2 OnCircle  C D" 
        by (meson OnCircle_def \<open>Cong Z1 C Z2 C\<close> \<open>Z1 OnCircle C D\<close> 
            cong_transitivity not_cong_4321)
      moreover 
      {
        assume "P InCircleS A B" and "Q OutCircleS A B"
        assume "Z1 = Z2"
        {
          assume "Bet A C Z1" 
          have "Cong C Q C Z1" 
            using \<open>Q OnCircle C D\<close> \<open>Z1 OnCircle C D\<close> onc2__cong by blast
          hence "A Q Le A Z1" 
            using \<open>Bet A C Z1\<close> triangle_inequality by auto
          hence "A Q Le A B" 
            using InCircle_def \<open>Z1 OnCircle A B\<close> le_transitivity onc__inc by blast
          hence False 
            using InCircle_def \<open>Q OutCircleS A B\<close> outcs__ninc_1 by blast
        }
        moreover 
        {
          assume "C Out A Z1"
          have "Cong C P C Z1" 
            using \<open>P OnCircle C D\<close> \<open>Z1 OnCircle C D\<close> onc2__cong by force
          hence "A Z1 Le A P" 
            using \<open>C Out A Z1\<close> triangle_reverse_inequality by blast
          hence "A B Le A P" 
            using OutCircle_def \<open>Z1 OnCircle A B\<close> le_transitivity onc__outc by blast
          hence False 
            using InCircle_def \<open>P InCircleS A B\<close> inc__outc outc__nincs_1 by blast
        }
        moreover 
        { 
          assume "\<not> Col A C Z1"
          have "Col Z1 A C" 
            using l10_8 \<open>Z1 = Z2\<close> \<open>Z1 Z2 Reflect A C\<close> by blast
          hence False 
            using NCol_perm \<open>\<not> Col A C Z1\<close> by blast
        }
        ultimately have False 
          using not_bet_out by blast 
      }
      ultimately show ?thesis 
        using \<open>Z1 OnCircle A B\<close> \<open>Z1 OnCircle C D\<close> by blast
    qed
  }
  thus ?thesis 
    using circle_circle_two_def by blast
qed

lemma circle_circle__circle_circle_two_R2 :
  assumes "circle_circle_two"
  shows "circle_circle" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and 
      "P InCircle A B" and "Q OutCircle A B"
    then obtain Z1 Z2 where "Z1 OnCircle A B \<and> Z1 OnCircle C D \<and>
    Z2 OnCircle A B \<and> Z2 OnCircle  C D \<and>
    ((P InCircleS A B \<and> Q OutCircleS A B) \<longrightarrow> Z1 \<noteq> Z2)" 
      using assms circle_circle_two_def by blast
    have "Z1 OnCircle A B" 
      by (simp add: \<open>Z1 OnCircle A B \<and> Z1 OnCircle C D \<and> Z2 OnCircle A B \<and> 
                     Z2 OnCircle C D \<and> (P InCircleS A B \<and> Q OutCircleS A B \<longrightarrow> Z1 \<noteq> Z2)\<close>)
    moreover have "Z1 OnCircle C D" 
      by (simp add: \<open>Z1 OnCircle A B \<and> Z1 OnCircle C D \<and> Z2 OnCircle A B \<and> 
                     Z2 OnCircle C D \<and> (P InCircleS A B \<and> Q OutCircleS A B \<longrightarrow> Z1 \<noteq> Z2)\<close>)
    ultimately have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
      by blast
  }
  thus ?thesis 
    using circle_circle_def by blast
qed

lemma circle_circle__circle_circle_two :
  shows "circle_circle \<longleftrightarrow> circle_circle_two" 
  using circle_circle__circle_circle_two_R1 circle_circle__circle_circle_two_R2 by blast

lemma euclid_22_aux:
  assumes "A B C D SumS E' F'" and
    "C D E F SumS A' B'" and
    "E F Le E' F'" and
    "A B Le A' B'" and
    "A Out B C1" and
    "Cong A C1 C D" and
    "Bet B A C2" and
    "Cong A C2 C D" and
    "B Out A E1" and
    "Cong B E1 E F"
  shows "Bet C1 E1 C2" 
proof -
  have "Bet C1 A C2" 
    using assms(5) assms(7) bet_out__bet by blast
  have "Col C1 E1 C2" 
    by (metis Out_def assms(5) assms(7) assms(9) bet_col col3 not_col_permutation_4 out_col)
  moreover 
  {
    assume "E1 Out C1 C2" 
    {
      assume "Bet E1 C1 C2" 
      have "Bet A C1 E1" 
        using \<open>Bet C1 A C2\<close> \<open>Bet E1 C1 C2\<close> between_inner_transitivity 
          between_symmetry by blast
      have "Bet A E1 B" 
        by (meson Out_def \<open>Bet A C1 E1\<close> assms(5) assms(9) between_inner_transitivity 
            between_symmetry not_bet_and_out)
      have "A' B' Lt A B" 
      proof -
        have "C D Lt A E1" 
          by (metis Out_def \<open>Bet A C1 E1\<close> \<open>E1 Out C1 C2\<close> assms(6) bet__lt1213 
              cong2_lt__lt cong_reflexivity)
        moreover have "E F Le E1 B" 
          using Cong_cases assms(10) cong__le3412 by blast
        moreover have "C D E F SumS A' B'" 
          by (simp add: assms(2))
        moreover have "A E1 E1 B SumS A B" 
          by (simp add: \<open>Bet A E1 B\<close> bet__sums)
        ultimately show ?thesis 
          using le_lt12_sums2__lt by blast
      qed
      hence False 
        using assms(4) lt__nle by force
    }
    moreover {
      assume "Bet E1 C2 C1"
      hence "Bet A C2 E1" 
        using Bet_cases \<open>Bet C1 A C2\<close> between_exchange3 by blast
      hence "Bet B C2 E1" 
        by (metis \<open>Bet E1 C2 C1\<close> assms(6) assms(7) assms(8) calculation cong_diff_4 
            cong_identity outer_transitivity_between2)
      have "B C2 Lt B E1" 
        using Out_def \<open>Bet B C2 E1\<close> \<open>E1 Out C1 C2\<close> bet__lt1213 by auto
      moreover have "Cong B C2 E' F'" 
        using SumS_def assms(1) assms(7) assms(8) cong_pseudo_reflexivity 
          cong_reflexivity sums2__cong56 by blast
      ultimately have "E' F' Lt E F" 
        using assms(10) cong2_lt__lt by blast
      hence False 
        by (simp add: assms(3) le__nlt)
    }
    ultimately have False 
      using Out_def \<open>E1 Out C1 C2\<close> by presburger
  }
  ultimately show ?thesis 
    using not_out_bet by blast
qed

lemma circle_circle_bis__euclid_22:
  assumes "circle_circle_bis"
  shows "euclid_s_prop_1_22"
proof -
  {
    fix A B C D E F A' B' C' D' E' F'
    assume "A B C D SumS E' F'" and "A B E F SumS C' D'" and "C D E F SumS A' B'" and
      "E F Le E' F'" and "C D Le C' D'" and "A B Le A' B'"
    have "\<exists> R. Cong A B A B \<and> Cong A R C D \<and> Cong B R E F" 
    proof (cases "A = B")
      case True
      obtain P where "Cong A P C D" 
        using segment_construction_0 by blast
      have "C D Le E F" 
        using True \<open>A B E F SumS C' D'\<close> \<open>C D Le C' D'\<close> cong_reflexivity l5_6
          not_cong_3412 sums__cong2345 by blast
      moreover have "E F Le C D" 
        using True \<open>A B C D SumS E' F'\<close> \<open>E F Le E' F'\<close> cong_reflexivity l5_6 
          not_cong_3412 sums__cong2345 by blast
      ultimately have "Cong C D E F" 
        using le_anti_symmetry by auto
      hence "Cong A P E F" 
        using \<open>Cong A P C D\<close> cong_transitivity by blast
      hence "Cong B P E F" 
        using True by auto
      thus ?thesis 
        using True \<open>Cong A P C D\<close> cong_pseudo_reflexivity by blast
    next
      case False
      hence "A \<noteq> B" 
        by simp
      show ?thesis
      proof (cases "C = D")
        case True
        have "B A Le E F" 
          using True \<open>A B Le A' B'\<close> \<open>C D E F SumS A' B'\<close> cong_pseudo_reflexivity
            l5_6 not_cong_3412 sums__cong2345 by blast
        moreover have "E F Le B A" 
          using True \<open>A B C D SumS E' F'\<close> \<open>E F Le E' F'\<close> cong_reflexivity
            l5_6 not_cong_4312 sums__cong1245 by blast
        ultimately have "Cong B A E F" 
          using le_anti_symmetry by auto
        thus ?thesis 
          using True cong_reflexivity cong_trivial_identity by blast
      next
        case False
        hence "C \<noteq> D" 
          by simp
        show ?thesis 
        proof (cases "E = F")
          case True
          thus ?thesis 
            by (metis \<open>A B C D SumS E' F'\<close> \<open>A B E F SumS C' D'\<close> \<open>A B Le A' B'\<close> 
                \<open>C D E F SumS A' B'\<close> \<open>C D Le C' D'\<close> cong_reflexivity le2_sums2__cong34 
                le2_sums2__le12 le_trivial sums123312 sums_sym)
        next
          case False
          hence "E \<noteq> F" 
            by simp
          obtain C1 where "A Out B C1" and "Cong A C1 C D" 
            using segment_construction_3 \<open>A \<noteq> B\<close> \<open>C \<noteq> D\<close> by force
          obtain E1 where "B Out A E1" and "Cong B E1 E F" 
            using segment_construction_3 \<open>A \<noteq> B\<close> \<open>E \<noteq> F\<close> by metis
          obtain C2 where "Bet B A C2" and "Cong A C2 C D" 
            using segment_construction by blast
          obtain E2 where "Bet A B E2" and "Cong B E2 E F"   
            using segment_construction by blast
          have "Bet C1 E1 C2" using euclid_22_aux [where ?A="A" and ?B="B" and 
                ?C="C" and ?D="D" and ?E="E" and ?F="F" and
                ?A'="A'" and ?B'="B'" and ?E'="E'" and ?F'="F'"]   
            using \<open>A B C D SumS E' F'\<close> \<open>A B Le A' B'\<close> \<open>A Out B C1\<close> \<open>B Out A E1\<close> 
              \<open>Bet B A C2\<close> \<open>C D E F SumS A' B'\<close> \<open>Cong A C1 C D\<close> \<open>Cong A C2 C D\<close> 
              \<open>Cong B E1 E F\<close> \<open>E F Le E' F'\<close> by blast
          have "Bet E1 C1 E2"  using euclid_22_aux [where ?A="B" and ?B="A" and 
                ?C="E" and ?D="F" and ?E="C" and ?F="D" and
                ?A'="B'" and ?B'="A'" and ?E'="C'" and ?F'="D'" and ?C1.0="C1" 
                and ?C2.0="E2" and ?E1.0="C1"] 
            by (meson \<open>A B E F SumS C' D'\<close> \<open>A B Le A' B'\<close> \<open>A Out B C1\<close> \<open>B Out A E1\<close> 
                \<open>Bet A B E2\<close> \<open>C D E F SumS A' B'\<close> \<open>C D Le C' D'\<close> \<open>Cong A C1 C D\<close> \<open>Cong B E1 E F\<close> 
                \<open>Cong B E2 E F\<close> euclid_22_aux le_left_comm sums_left_comm sums_sym)
          have "E1 OnCircle B E1"
            by (simp add: onc212)
          moreover have "C1 OnCircle A C1"  
            by (simp add: onc212)
          moreover have "E1 InCircle A C1" 
          proof (rule bet_inc2__inc [where ?U="C1" and ?V="C2"])
            show "C1 InCircle A C1" 
              by (simp add: onc212 onc__inc)
            show "C2 InCircle A C1" 
              by (meson InCircle_def \<open>Cong A C1 C D\<close> \<open>Cong A C2 C D\<close> cong__le 
                  cong_inner_transitivity not_cong_3421)
            show "Bet C1 E1 C2" 
              using \<open>Bet C1 E1 C2\<close> by auto
          qed
          moreover have "C1  InCircle B E1" 
          proof (rule bet_inc2__inc [where ?U="E1" and ?V="E2"])
            show "E1 InCircle B E1" 
              by (simp add: onc212 onc__inc)
            show "E2 InCircle B E1" 
              by (meson InCircle_def \<open>Cong B E1 E F\<close> \<open>Cong B E2 E F\<close> cong__le3412 
                  cong_inner_transitivity not_cong_4321)
            show "Bet E1 C1 E2" 
              using \<open>Bet E1 C1 E2\<close> by auto
          qed
          ultimately obtain Z where "Z OnCircle A C1" and "Z OnCircle B E1" 
            using assms(1) circle_circle_bis_def by blast
          then show ?thesis 
            by (meson OnCircle_def \<open>Cong A C1 C D\<close> \<open>Cong B E1 E F\<close> 
                cong_reflexivity cong_transitivity)
        qed
      qed
    qed
    hence "\<exists> P Q R. (Cong P Q A B \<and> Cong P R C D \<and> Cong Q R E F)" 
      by blast
  }
  thus ?thesis
    using euclid_s_prop_1_22_def by blast
qed

lemma triangle_inequality1:
  assumes "A B B C SumS D E"
  shows "A C Le D E"
proof -
  obtain D' where "Bet A B D'" and "Cong B D' B C" 
    using segment_construction by blast
  have "A C Le A D'" 
    using \<open>Bet A B D'\<close> \<open>Cong B D' B C\<close> cong_symmetry triangle_inequality by blast
  moreover have "Cong A D' D E" 
    using SumS_def \<open>Bet A B D'\<close> \<open>Cong B D' B C\<close> assms cong_reflexivity sums2__cong56 by blast
  ultimately show ?thesis 
    using cong__le le_transitivity by blast
qed

lemma euclid_22__circle_circle:
  assumes "euclid_s_prop_1_22"
  shows "circle_circle" 
proof -
  {
    fix A B C D P Q
    assume "P OnCircle C D" and "Q OnCircle C D" and "P InCircle A B" and "Q OutCircle A B"
    have "\<exists> X Y Z. Cong X Y A C \<and> Cong X Z A B \<and> Cong Y Z C D" 
    proof -
      obtain L1 R1 where "A B C D SumS L1 R1" 
        using ex_sums by blast
      obtain L2 R2 where "A C C D SumS L2 R2" 
        using ex_sums by blast
      obtain L3 R3 where "A C A B SumS L3 R3" 
        using ex_sums by blast
      have "C D Le L3 R3"
      proof - 
        obtain R S where "C A A P SumS R S"
          using ex_sums by blast
        have "C D Le R S" 
          by (metis Cong_cases OnCircle_def \<open>C A A P SumS R S\<close> \<open>P OnCircle C D\<close> 
              cong__le le_transitivity triangle_inequality1)
        moreover have "R S Le L3 R3"
          using le2_sums2__le [where ?A="C" and ?B="A" and ?C="A" and ?D="P" and 
              ?A'="A" and ?B'="C" and ?C'="A" and ?D'="B"] InCircle_def \<open>A C A B SumS L3 R3\<close> 
            \<open>C A A P SumS R S\<close> \<open>P InCircle A B\<close> le1221 by blast
        ultimately show ?thesis 
          using le_transitivity by blast
      qed
      moreover have "A C C Q SumS L2 R2" 
        by (meson OnCircle_def \<open>A C C D SumS L2 R2\<close> \<open>Q OnCircle C D\<close> 
            cong3_sums__sums cong_reflexivity onc_sym)
      hence "A Q Le L2 R2" 
        using triangle_inequality1 by auto
      hence "A B Le L2 R2" 
        using OutCircle_def \<open>Q OutCircle A B\<close> le_transitivity by blast
      moreover have "A C Le L1 R1" 
      proof -
        obtain R S where "A P P C SumS R S"
          using ex_sums by blast
        have "A C Le R S" 
          using \<open>A P P C SumS R S\<close> triangle_inequality1 by auto
        moreover have "R S Le L1 R1" 
          using le2_sums2__le [where ?A="A" and ?B="P" and ?C="P" and ?D="C" and 
              ?A'="A" and ?B'="B" and ?C'="C" and ?D'="D"] by (meson InCircle_def OnCircle_def 
              \<open>A B C D SumS L1 R1\<close> \<open>A P P C SumS R S\<close> \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> 
              cong__le not_cong_3421 onc_sym)
        ultimately show ?thesis 
          using le_transitivity by blast
      qed
      ultimately show ?thesis 
        using \<open>A B C D SumS L1 R1\<close> \<open>A C A B SumS L3 R3\<close> \<open>A C C D SumS L2 R2\<close> assms 
          euclid_s_prop_1_22_def by blast
    qed
    then obtain X Y Z where "Cong X Y A C" and "Cong X Z A B" and "Cong Y Z C D" 
      by blast
    have "\<exists> Z. Z OnCircle A B \<and> Z OnCircle C D" 
    proof (cases "A = C")
      case True
      then show ?thesis 
        using OnCircle_def \<open>\<exists>X Y Z. Cong X Y A C \<and> Cong X Z A B \<and> Cong Y Z C D\<close> 
          cong_identity cong_inner_transitivity by blast
    next
      case False
      hence "A \<noteq> C"
        by blast
      show ?thesis 
      proof (cases "A = B")
        case True
        then show ?thesis 
          using \<open>P InCircle A B\<close> \<open>P OnCircle C D\<close> inc__outc_1 inc_eq 
            inc_outc__onc by blast
      next
        case False
        hence "A \<noteq>B" 
          by simp
        have "X \<noteq> Z" 
          using False \<open>Cong X Z A B\<close> cong_reverse_identity by force
        have "X \<noteq> Y" 
          using \<open>A \<noteq> C\<close> \<open>Cong X Y A C\<close> cong_diff_3 by blast
        have "\<exists> Z0. Y X Z CongA C A Z0 \<and> Cong X Z A Z0"
        proof -
          obtain Z' where "Y X Z CongA C A Z'" 
            using \<open>A \<noteq> C\<close> \<open>X \<noteq> Y\<close> \<open>X \<noteq> Z\<close> angle_construction_3 by presburger
          obtain Z0 where "A Out Z' Z0" and "Cong A Z0 X Z" 
            by (metis \<open>X \<noteq> Z\<close> \<open>Y X Z CongA C A Z'\<close> conga_diff56 segment_construction_3)
          have "Y X Z CongA C A Z0" 
            by (metis \<open>A Out Z' Z0\<close> \<open>A \<noteq> C\<close> \<open>Y X Z CongA C A Z'\<close> not_conga 
                not_conga_sym out2__conga out_trivial)
          thus ?thesis 
            using \<open>Cong A Z0 X Z\<close> cong_symmetry by blast
        qed
        then obtain Z0 where "Y X Z CongA C A Z0" and "Cong X Z A Z0" 
          by blast
        then show ?thesis 
          by (meson OnCircle_def \<open>Cong X Y A C\<close> \<open>Cong X Z A B\<close> \<open>Cong Y Z C D\<close> 
              cong_inner_transitivity l11_49)
      qed
    qed
  }
  thus ?thesis 
    using circle_circle_def by blast
qed

theorem equivalent_variants_of_circle_circle:
  shows "(circle_circle \<longleftrightarrow> circle_circle_two) \<and>
    (circle_circle_two \<longleftrightarrow> circle_circle_bis) \<and>
    (circle_circle_bis \<longleftrightarrow> circle_circle_axiom)\<and>
    (circle_circle_axiom \<longleftrightarrow> euclid_s_prop_1_22)" 
proof -
  have "circle_circle \<longleftrightarrow> circle_circle_two" 
    using circle_circle__circle_circle_two by blast
  moreover have "circle_circle_two \<longleftrightarrow> circle_circle_bis" 
    using circle_circle__circle_circle_bis circle_circle__circle_circle_two 
      circle_circle_bis__euclid_22 euclid_22__circle_circle by blast
  moreover have "circle_circle_bis \<longleftrightarrow> circle_circle_axiom" 
    by (simp add: circle_circle_bis__circle_circle_axiom)
  moreover have "circle_circle_axiom \<longleftrightarrow> euclid_s_prop_1_22" 
    using circle_circle__circle_circle_bis circle_circle_bis__circle_circle_axiom 
      circle_circle_bis__euclid_22 euclid_22__circle_circle by blast
  ultimately show ?thesis 
    by blast
qed

theorem equivalent_variants_of_line_circle:
  shows "(segment_circle \<longleftrightarrow> one_point_line_circle) \<and> 
         (one_point_line_circle \<longleftrightarrow> two_points_line_circle)"
proof -
  have "segment_circle \<longrightarrow> one_point_line_circle" 
    by (simp add: segment_circle__one_point_line_circle)
  moreover have "one_point_line_circle \<longrightarrow> two_points_line_circle" 
    by (simp add: one_point_line_circle__two_points_line_circle)
  moreover have "two_points_line_circle \<longrightarrow> segment_circle" 
    by (simp add: one_point_line_circle__two_points_line_circle_R2 
        segment_circle__one_point_line_circle_R2)
  ultimately show ?thesis 
    by blast
qed

end
end

