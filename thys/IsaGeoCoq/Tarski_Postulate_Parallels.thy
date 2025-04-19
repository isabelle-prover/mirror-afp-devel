(* IsaGeoCoq - Tarski_Postulate_Parallels

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

theory Tarski_Postulate_Parallels

imports
  Tarski_Neutral

begin

context Tarski_neutral_dimensionless

begin

section "Parallel's definition Postulate"

definition tarski_s_parallel_postulate ::
  "bool"
  ("TarskiSParallelPostulate")
  where
    "tarski_s_parallel_postulate \<equiv> 

     \<forall> A B C D T.
     Bet A D T \<and> Bet B D C \<and> A \<noteq> D 
\<longrightarrow>
     (\<exists> X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y)"

definition euclid_5 ::
  "bool" ("Euclid5")
  where
    "euclid_5 \<equiv> 

     \<forall> P Q R S T U.
     BetS P T Q \<and> BetS R T S \<and> BetS Q U R \<and> \<not> Col P Q S \<and> Cong P T Q T \<and> Cong R T S T
\<longrightarrow>
     (\<exists> I. BetS S Q I \<and> BetS P U I)"

definition euclid_s_parallel_postulate ::
  "bool" ("EuclidSParallelPostulate")
  where
    "euclid_s_parallel_postulate \<equiv> 

     \<forall> A B C D P Q R.
     B C OS A D \<and> SAMS A B C B C D \<and> A B C B C D SumA P Q R \<and> \<not> Bet P Q R 
\<longrightarrow>
     (\<exists> Y. B Out A Y \<and> C Out D Y)"

definition playfair_s_postulate ::
  "bool"
  ("PlayfairSPostulate")
  where
    "playfair_s_postulate \<equiv> 

     \<forall> A1 A2 B1 B2 C1 C2 P.
     A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 
\<longrightarrow>
     Col C1 B1 B2 \<and> Col C2 B1 B2"

section "Some postulates of the parallels"

lemma euclid_5__original_euclid:
  assumes "Euclid5"
  shows "EuclidSParallelPostulate"
proof -
  {
    fix A B C D P Q R
    assume P1: "B C OS A D \<and> SAMS A B C B C D \<and> A B C B C D SumA P Q R \<and> \<not> Bet P Q R"
    obtain M where P2: "M Midpoint B C"
      using midpoint_existence by auto
    obtain D' where P3: "C Midpoint D D'"
      using symmetric_point_construction by auto
    obtain E where P4: "M Midpoint D' E"
      using symmetric_point_construction by auto
    have P5: "A \<noteq> B"
      using P1 os_distincts by blast
    have P6: "B \<noteq> C"
      using P1 os_distincts by blast
    have P7: "C \<noteq> D"
      using P1 os_distincts by blast
    have P10: "M \<noteq> B"
      using P2 P6 is_midpoint_id by auto
    have P11: "M \<noteq> C"
      using P2 P6 is_midpoint_id_2 by auto
    have P13: "C \<noteq> D'"
      using P3 P7 is_midpoint_id_2 by blast
    have P16: "\<not> Col B C A"
      using one_side_not_col123 P1 by blast
    have "B C OS D A"
      using P1 one_side_symmetry by blast
    then have P17: "\<not> Col B C D"
      using one_side_not_col123 P1 by blast
    then have P18: "\<not> Col M C D"
      using P2 Col_perm P11 col_transitivity_2 midpoint_col by blast
    then have P19: "\<not> Col M C D'"
      by (metis P13  P3 Col_perm col_transitivity_2 midpoint_col)
    then have P20: "\<not> Col D' C B"
      by (metis Col_perm P13 P17 P3 col_transitivity_2 midpoint_col)
    then have P21: "\<not> Col M C E"
      by (metis P19 P4 bet_col col2__eq col_permutation_4 midpoint_bet midpoint_distinct_2)
    have P22: "M C D' CongA M B E \<and> M D' C CongA M E B" using P13 l11_49
      by (metis Cong_cases P19 P2 P4 l11_51 l7_13_R1 l7_2 midpoint_cong not_col_distincts)
    have P23: "Cong C D' B E"
      using P11 P2 P4 l7_13_R1 l7_2 by blast
    have P27: "C B TS D D'"
      by (simp add: P13 P17 P3 bet__ts midpoint_bet not_col_permutation_4)
    have P28: "A InAngle C B E"
    proof -
      have "C B A LeA C B E"
      proof -
        have "A B C LeA B C D'"
        proof -
          have "Bet D C D'"
            by (simp add: P3 midpoint_bet)
          then show ?thesis using P1 P7 P13 sams_chara
            by (metis sams_left_comm sams_sym)
        qed
        moreover have "A B C CongA C B A"
          using P5 P6 conga_pseudo_refl by auto
        moreover have "B C D' CongA C B E"
          by (metis CongA_def Mid_cases P2 P22 P4 P6 symmetry_preserves_conga)
        ultimately show ?thesis
          using l11_30 by blast
      qed
      moreover have "C B OS E A"
      proof -
        have "C B TS E D'"
          using P2 P20 P4 l7_2 l9_2 mid_two_sides not_col_permutation_1 by blast
        moreover have "C B TS A D'"
          using P27 \<open>B C OS D A\<close> invert_two_sides l9_8_2 by blast
        ultimately show ?thesis
          using OS_def by blast
      qed
      ultimately show ?thesis
        using lea_in_angle by simp
    qed
    obtain A' where P30: "Bet C A' E \<and> (A' = B \<or> B Out A' A)" using P28 InAngle_def by auto
    {
      assume "A' = B"
      then have "Col D' C B"
        by (metis Col_def P2 P21 P30 P6 col_transitivity_1 midpoint_col)
      then have "False"
        by (simp add: P20)
      then have "\<exists> Y. B Out A Y \<and> C Out D Y" by auto
    }
    {
      assume P31: "B Out A' A"
      have "\<exists> I. BetS D' C I \<and> BetS B A' I"
      proof -
        have P32: "BetS B M C"
          using BetS_def Midpoint_def P10 P11 P2 by auto
        moreover have "BetS E M D'"
          using BetS_def Bet_cases P19 P21 P4 midpoint_bet not_col_distincts by fastforce
        moreover have "BetS C A' E"
        proof -
          have P32A: "C \<noteq> A'"
            using P16 P31 out_col by auto
          {
            assume "A' = E"
            then have P33: "B Out A E"
              using P31 l6_6 by blast
            then have "A B C B C D SumA D' C D"
            proof -
              have "D' C B CongA A B C"
              proof -
                have "D' C M CongA E B M"
                  by (simp add: P22 conga_comm)
                moreover have "C Out D' D'"
                  using P13 out_trivial by auto
                moreover have "C Out B M"
                  using BetSEq Out_cases P32 bet_out_1 by blast
                moreover have "B Out A E"
                  using P33 by auto
                moreover have "B Out C M"
                  using BetSEq Out_def P32 by blast
                ultimately show ?thesis
                  using l11_10 by blast
              qed
              moreover have "D' C B B C D SumA D' C D"
                by (simp add: P27 l9_2 ts__suma_1)
              moreover have "B C D CongA B C D"
                using P6 P7 conga_refl by auto
              moreover have "D' C D CongA D' C D"
                using P13 P7 conga_refl by presburger
              ultimately show ?thesis
                using conga3_suma__suma by blast
            qed
            then have "D' C D CongA P Q R"
              using P1 suma2__conga by auto
            then have "Bet P Q R"
              using Bet_cases P3 bet_conga__bet midpoint_bet by blast
            then have "False" using P1 by simp
          }
          then have "A' \<noteq> E" by auto
          then show ?thesis
            by (simp add: BetS_def P30 P32A)
        qed
        moreover have "\<not> Col B C D'"
          by (simp add: P20 not_col_permutation_3)
        moreover have "Cong B M C M"
          using Midpoint_def P2 not_cong_1243 by blast
        moreover have "Cong E M D' M"
          using Cong_perm Midpoint_def P4 by blast
        ultimately show ?thesis
          using euclid_5_def assms by blast
      qed
      then obtain Y where P34: "Bet D' C Y \<and> BetS B A' Y" using BetSEq by blast
      then have "\<exists> Y. B Out A Y \<and> C Out D Y"
      proof -
        have P35: "B Out A Y"
          by (metis BetSEq Out_def P31 P34 l6_7)
        moreover have "C Out D Y"
        proof -
          have "D \<noteq> C"
            using P7 by auto
          moreover have "Y \<noteq> C"
            using P16 P35 l6_6 out_col by blast
          moreover have "D' \<noteq> C"
            using P13 by auto
          moreover have "Bet D C D'"
            by (simp add: P3 midpoint_bet)
          moreover have "Bet Y C D'"
            by (simp add: Bet_perm P34)
          ultimately show ?thesis
            using l6_2 by blast
        qed
        ultimately show ?thesis by auto
      qed
    }
    then have "\<exists> Y. B Out A Y \<and> C Out D Y"
      using P30 \<open>A' = B \<Longrightarrow> \<exists>Y. B Out A Y \<and> C Out D Y\<close> by blast
  }
  then show ?thesis using euclid_s_parallel_postulate_def  by blast
qed

lemma tarski_s_euclid_implies_euclid_5:
  assumes "TarskiSParallelPostulate"
  shows "Euclid5"
proof -
  {
    fix P Q R S T U
    assume
      P1: "BetS P T Q \<and> BetS R T S \<and> BetS Q U R \<and> \<not> Col P Q S \<and> Cong P T Q T \<and> Cong R T S T"
    have P1A: "BetS P T Q" using P1 by simp
    have P1B: "BetS R T S" using P1 by simp
    have P1C: "BetS Q U R" using P1 by simp
    have P1D: "\<not> Col P Q S" using P1 by simp
    have P1E: "Cong P T Q T" using P1 by simp
    have P1F: "Cong R T S T" using P1 by simp
    obtain V where P2: "P Midpoint R V"
      using symmetric_point_construction by auto
    have P3: "Bet V P R"
      using Mid_cases P2 midpoint_bet by blast
    then obtain W where P4: "Bet P W Q \<and> Bet U W V" using inner_pasch
      using BetSEq P1C by blast
    {
      assume "P = W"
      have "P \<noteq> V"
        by (metis BetSEq Bet_perm Col_def Cong_perm Midpoint_def P1A P1B P1D P1E P1F P2 between_trivial is_midpoint_id_2 l7_9)
      have "Col P Q S"
      proof -
        have f1: "Col V P R"
          by (meson Col_def P3)
        have f2: "Col U R Q"
          by (simp add: BetSEq Col_def P1)
        have f3: "Bet P T Q"
          using BetSEq P1 by fastforce
        have f4: "R = P \<or> Col V P U"
          by (metis (no_types) Col_def P4 \<open>P = W\<close> \<open>P \<noteq> V\<close> l6_16_1)
        have f5: "Col Q P T"
          using f3 by (meson Col_def)
        have f6: "Col T Q P"
          using f3 by (meson Col_def)
        have f7: "Col P T Q"
          using f3 by (meson Col_def)
        have f8: "Col P Q P"
          using Col_def P4 \<open>P = W\<close> by blast
        have "Col R T S"
          by (meson BetSEq Col_def P1)
        then have "T = P \<or> Q = P"
          using f8 f7 f6 f5 f4 f2 f1 by (metis (no_types) BetSEq P1 \<open>P \<noteq> V\<close> colx l6_16_1)
        then show ?thesis
          by (metis BetSEq P1)
      qed
      then have "False"
        by (simp add: P1D)
    }
    then have P5: "P \<noteq> W" by auto
    have "Bet V W U"
      using Bet_cases P4 by auto
    then obtain X Y where P7: "Bet P V X \<and> Bet P U Y \<and> Bet X Q Y"
      using assms(1) P1 P4 P5 tarski_s_parallel_postulate_def by blast
    have "Q S Par P R"
    proof -
      have "Q \<noteq> S"
        using P1D col_trivial_2 by auto
      moreover have "T Midpoint Q P"
        using BetSEq P1A P1E l7_2 midpoint_def not_cong_1243 by blast
      moreover have "T Midpoint S R"
        using BetSEq P1B P1F l7_2 midpoint_def not_cong_1243 by blast
      ultimately show ?thesis
        using l12_17 by auto
    qed
    then have P9: "Q S ParStrict P R"
      using P1D Par_def par_strict_symmetry par_symmetry by blast
    have P10: "Q S TS P Y"
    proof -
      have P10A: "P \<noteq> R"
        using P9 par_strict_distinct by auto
      then have P11: "P \<noteq> X"
        by (metis P2 P7 bet_neq12__neq midpoint_not_midpoint)
      have P12: "\<not> Col X Q S"
      proof -
        have "Q S ParStrict P R"
          by (simp add: P9)
        then have "Col P R X"
          by (metis P2 P3 P7 bet_col between_symmetry midpoint_not_midpoint not_col_permutation_4 outer_transitivity_between)
        then have "P X ParStrict Q S"
          using P9 Par_strict_perm P11 par_strict_col_par_strict by blast
        then show ?thesis
          using par_strict_not_col_2 by auto
      qed
      {
        assume W1: "Col Y Q S"
        have W2: "Q = Y"
          by (metis P12 P7 W1 bet_col bet_col1 colx)
        then have "\<not> Col Q P R"
          using P9 W1 par_not_col by auto
        then have W3: "Q = U"
          by (smt BetS_def Col_def P1C P7 W2 col_transitivity_2)
        then have "False"
          using BetS_def P1C by auto
      }
      then have "\<not> Col Y Q S" by auto
      then have "Q S TS X Y"
        by (metis P7 P12 bet__ts not_col_distincts not_col_permutation_1)
      moreover have "Q S OS X P"
      proof -
        have "P \<noteq> V"
          using P10A P2 is_midpoint_id_2 by blast
        then have "Q S ParStrict P X"
          by (meson Bet_perm P3 P7 P9 P11 bet_col not_col_permutation_4 par_strict_col_par_strict)
        then have "Q S ParStrict X P"
          by (simp add: par_strict_right_comm)
        then show ?thesis
          by (simp add: l12_6)
      qed
      ultimately show ?thesis
        using l9_8_2 by auto
    qed
    then obtain I where W4: "Col I Q S \<and> Bet P I Y"
      using TS_def by blast
    have "\<exists> I. (BetS S Q I \<and> BetS P U I)"
    proof -
      have "BetS P U I"
      proof -
        have "P \<noteq> Y"
          using P10 not_two_sides_id by auto
        have W4A: "Bet P U I"
        proof -
          have W5: "Col P U I"
            using P7 W4 bet_col1 by auto
          {
            assume W6: "Bet U I P"
            have W7: "Q S OS P U"
            proof -
              have "Q S OS R U"
              proof -
                have "\<not> Col Q S R"
                  using P9 par_strict_not_col_4 by auto
                moreover have "Q Out R U"
                  using BetSEq Out_def P1C by blast
                ultimately show ?thesis
                  by (simp add: out_one_side)
              qed
              moreover have "Q S OS P R"
                by (simp add: P9 l12_6)
              ultimately show ?thesis
                using one_side_transitivity by blast
            qed
            have W8: "I Out P U \<or> \<not> Col Q S P"
              by (simp add: P1D not_col_permutation_1)
            have "False"
            proof -
              have "I Out U P"
                using W4 W6 W7 between_symmetry one_side_chara by blast
              then show ?thesis
                using W6 not_bet_and_out by blast
            qed
          }
          {
            assume V1: "Bet I P U"
            have "P R OS I U"
            proof -
              have "P R OS I Q"
              proof -
                {
                  assume "Q = I"
                  then have "Col P Q S"
                    by (metis BetSEq Col_def P1C P7 P9 V1 W4 between_equality outer_transitivity_between par_not_col)
                  then have "False"
                    using P1D by blast
                }
                then have "Q \<noteq> I" by blast
                moreover have "P R ParStrict Q S"
                  using P9 par_strict_symmetry by blast
                moreover have "Col Q S I"
                  using Col_cases W4 by blast
                ultimately show ?thesis
                  using one_side_symmetry par_strict_all_one_side by blast
              qed
              moreover have "P R OS Q U"
              proof -
                have "Q S ParStrict P R"
                  using P9 by blast
                have "R Out Q U \<and> \<not> Col P R Q"
                  by (metis BetSEq Bet_cases Out_def P1C calculation col124__nos)
                then show ?thesis
                  by (metis P7 V1 W4 \<open>Bet U I P \<Longrightarrow> False\<close> between_equality col_permutation_2 not_bet_distincts out_col outer_transitivity_between)
              qed
              ultimately show ?thesis
                using one_side_transitivity by blast
            qed
            then have V2: "P Out I U"
              using P7 W4 bet2__out os_distincts by blast
            then have "Col P I U"
              using V1 not_bet_and_out by blast
            then have "False"
              using V1 V2 not_bet_and_out by blast
          }
          then moreover have "\<not> (Bet U I P \<or> Bet I P U)"
            using \<open>Bet U I P \<Longrightarrow> False\<close> by auto
          ultimately show ?thesis
            using Col_def W5 by blast
        qed
        {
          assume "P = U"
          then have "Col P R Q"
            using BetSEq Col_def P1C by blast
          then have "False"
            using P9 par_strict_not_col_3 by blast
        }
        then have V6: "P \<noteq> U" by auto
        {
          assume "U = I"
          have "Q = U"
          proof -
            have f1: "BetS Q I R"
              using P1C \<open>U = I\<close> by blast
            then have f2: "Col Q I R"
              using BetSEq Col_def by blast
            have f3: "Col I R Q"
              using f1 by (simp add: BetSEq Col_def)
            { assume "R \<noteq> Q"
              moreover
              { assume "(R \<noteq> Q \<and> R \<noteq> I) \<and> \<not> Col I Q R"
                moreover
                { assume "\<exists>p. (R \<noteq> Q \<and> \<not> Col I p I) \<and> Col Q I p"
                  then have "I = Q"
                    using f1 by (metis (no_types) BetSEq Col_def col_transitivity_2) }
                ultimately have "(\<exists>p pa. ((pa \<noteq> I \<and> \<not> Col pa p R) \<and> Col Q I pa) \<and> Col I pa p) \<or> I = Q"
                  using f3 f2 by (metis (no_types) col_transitivity_2) }
              ultimately have "(\<exists>p pa. ((pa \<noteq> I \<and> \<not> Col pa p R) \<and> Col Q I pa) \<and> Col I pa p) \<or> I = Q"
                using f1 by (metis (no_types) BetSEq P9 W4 col_transitivity_2 par_strict_not_col_4) }
            then show ?thesis
              using f2 by (metis P9 W4 \<open>U = I\<close> col_transitivity_2 par_strict_not_col_4)
          qed
          then have "False"
            using BetSEq P1C by blast
        }
        then have "U \<noteq> I" by auto
        then show ?thesis
          by (simp add: W4A V6 BetS_def)
      qed
      moreover have "BetS S Q I"
      proof -
        have "Q R TS S I"
        proof -
          have "Q R TS P I"
          proof -
            have "\<not> Col P Q R"
              using P9 col_permutation_5 par_strict_not_col_3 by blast
            moreover have "\<not> Col I Q R"
            proof -
              {
                assume "Col I Q R"
                then have "Col Q S R"
                proof -
                  have f1: "\<forall>p pa pb. Col p pa pb \<or> \<not> BetS pb p pa"
                    by (meson BetSEq Col_def)
                  then have f2: "Col U I P"
                    using \<open>BetS P U I\<close> by blast
                  have f3: "Col I P U"
                    by (simp add: BetSEq Col_def \<open>BetS P U I\<close>)
                  have f4: "\<forall>p. (U = Q \<or> Col Q p R) \<or> \<not> Col Q U p"
                    by (metis BetSEq Col_def P1C col_transitivity_1)
                  { assume "P \<noteq> Q"
                    moreover
                    { assume "(P \<noteq> Q \<and> U \<noteq> Q) \<and> Col Q P Q"
                      then have "(P \<noteq> Q \<and> U \<noteq> Q) \<and> \<not> Col Q P R"
                        using Col_cases \<open>\<not> Col P Q R\<close> by blast
                      moreover
                      { assume "\<exists>p. ((U \<noteq> Q \<and> P \<noteq> Q) \<and> \<not> Col Q p P) \<and> Col Q P p"
                        then have "U \<noteq> Q \<and> \<not> Col Q P P"
                          by (metis col_transitivity_1)
                        then have "\<not> Col U Q P"
                          using col_transitivity_2 by blast }
                      ultimately have "\<not> Col U Q P \<or> I \<noteq> Q"
                        using f4 f3 by blast }
                    ultimately have "I \<noteq> Q"
                      using f2 f1 by (metis BetSEq P1C col_transitivity_1 col_transitivity_2) }
                  then have "I \<noteq> Q"
                    using BetSEq \<open>BetS P U I\<close> by blast
                  then show ?thesis
                    by (simp add: W4 \<open>Col I Q R\<close> col_transitivity_2)
                qed
                then have "False"
                  using P9 par_strict_not_col_4 by blast
              }
              then show ?thesis by blast
            qed
            moreover have "Col U Q R"
              using BetSEq Bet_cases Col_def P1C by blast
            moreover have "Bet P U I"
              by (simp add: BetSEq \<open>BetS P U I\<close>)
            ultimately show ?thesis
              using TS_def by blast
          qed
          moreover have "Q R OS P S"
          proof -
            have "Q R Par P S"
            proof -
              have "Q \<noteq> R"
                using BetSEq P1 by blast
              moreover have "T Midpoint Q P"
                using BetSEq Bet_cases P1A P1E cong_3421 midpoint_def by blast
              moreover have "T Midpoint R S"
                using BetSEq P1B P1F midpoint_def not_cong_1243 by blast
              ultimately show ?thesis
                using l12_17 by blast
            qed
            then have "Q R ParStrict P S"
              by (simp add: P1D Par_def not_col_permutation_4)
            then show ?thesis
              using l12_6 by blast
          qed
          ultimately show ?thesis
            using l9_8_2 by blast
        qed
        then show ?thesis
          by (metis BetS_def W4 col_two_sides_bet not_col_permutation_2 ts_distincts)
      qed
      ultimately show ?thesis
        by auto
    qed
  }
  then show ?thesis using euclid_5_def by blast
qed

lemma tarski_s_implies_euclid_s_parallel_postulate:
  assumes "TarskiSParallelPostulate"
  shows "EuclidSParallelPostulate"
  by (simp add: assms euclid_5__original_euclid tarski_s_euclid_implies_euclid_5)

theorem tarski_s_euclid_implies_playfair_s_postulate:
  assumes "TarskiSParallelPostulate"
  shows "PlayfairSPostulate"
proof -
  {
    fix A1 A2 B1 B2 P C1 C2
    assume P1: "\<not> Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2"
    have P1A: "\<not> Col P A1 A2"
      by (simp add: P1)
    have P2: "A1 A2 Par B1 B2"
      by (simp add: P1)
    have P3: "Col P B1 B2"
      by (simp add: P1)
    have P4: "A1 A2 Par C1 C2"
      by (simp add: P1)
    have P5: "Col P C1 C2"
      by (simp add: P1)
    have P6: "A1 A2 ParStrict B1 B2"
    proof -
      have "A1 A2 Par B1 B2"
        by (simp add: P1)
      moreover have "Col B1 B2 P"
        using P3 not_col_permutation_2 by blast
      moreover have "\<not> Col A1 A2 P"
        by (simp add: P1A not_col_permutation_1)
      ultimately show ?thesis
        using par_not_col_strict by auto
    qed
    have P7: "A1 A2 ParStrict C1 C2"
    proof -
      have "A1 A2 Par C1 C2"
        by (simp add: P1)
      moreover have "Col C1 C2 P"
        using Col_cases P1 by blast
      moreover have "\<not> Col A1 A2 P"
        by (simp add: P1A not_col_permutation_1)
      ultimately show ?thesis
        using par_not_col_strict by auto
    qed
    {
      assume "\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2"
      have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'"
      proof -
        have T2: "Coplanar A1 A2 P A1"
          using ncop_distincts by auto
        have T3: "Coplanar A1 A2 B1 B2"
          by (simp add: P1 par__coplanar)
        have T4: "Coplanar A1 A2 C1 C2"
          by (simp add: P7 pars__coplanar)
        have T5: "Coplanar A1 A2 P B1"
          using P1 col_trivial_2 ncop_distincts par__coplanar par_col2_par_bis by blast
        then have T6: "Coplanar A1 A2 P B2"
          using P3 T3 col_cop__cop by blast
        have T7: "Coplanar A1 A2 P C1"
          using P1 T4 col_cop__cop coplanar_perm_1 not_col_permutation_2 par_distincts by blast
        then have T8: "Coplanar A1 A2 P C2"
          using P5 T4 col_cop__cop by blast
        {
          assume "\<not> Col C1 B1 B2"
          moreover have "C1 \<noteq> C2"
            using P1 par_neq2 by auto
          moreover have "Col B1 B2 P"
            using P1 not_col_permutation_2 by blast
          moreover have "Col C1 C2 P"
            using Col_cases P5 by auto
          moreover have "\<not> Col B1 B2 C1"
            using Col_cases calculation(1) by auto
          moreover have "\<not> Col B1 B2 A1"
            using P6 par_strict_not_col_3 by auto
          moreover have "Coplanar B1 B2 C1 A1"
            using Col_cases P1A T5 T2 T6 T7 coplanar_pseudo_trans by blast
          ultimately have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'"
            using cop_not_par_other_side by blast
        }
        {
          assume "\<not> Col C2 B1 B2"
          moreover have "C2 \<noteq> C1"
            using P1 par_neq2 by blast
          moreover have "Col B1 B2 P"
            using Col_cases P3 by auto
          moreover have "Col C2 C1 P"
            using Col_cases P5 by auto
          moreover have "\<not> Col B1 B2 C2"
            by (simp add: calculation(1) not_col_permutation_1)
          moreover have "\<not> Col B1 B2 A1"
            using P6 par_strict_not_col_3 by auto
          moreover have "Coplanar B1 B2 C2 A1"
            using Col_cases P1A T2 T5 T6 T8 coplanar_pseudo_trans by blast
          ultimately have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'" using cop_not_par_other_side
            by (meson not_col_permutation_4)
        }
        then show ?thesis
          using \<open>\<not> Col C1 B1 B2 \<Longrightarrow> \<exists>C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'\<close> \<open>\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2\<close> by blast
      qed
      then obtain C' where W1: "Col C1 C2 C' \<and> B1 B2 TS A1 C'" by auto
      then have W2: "\<not> Col A1 B1 B2"
        using TS_def by blast
      obtain B where W3: "Col B B1 B2 \<and> Bet A1 B C'"
        using TS_def W1 by blast
      obtain C where W4: "P Midpoint C' C"
        using symmetric_point_construction by blast
      then have W4A: "Bet A1 B C' \<and> Bet C P C'"
        using Mid_cases W3 midpoint_bet by blast
      then obtain D where W5: "Bet B D C \<and> Bet P D A1" using inner_pasch by blast
      have W6: "C' \<noteq> P"
        using P3 TS_def W1 by blast
      then have "A1 A2 Par C' P"
        by (meson P1 W1 not_col_permutation_2 par_col2_par)
      have W9: "A1 A2 ParStrict C' P"
        using Col_cases P5 P7 W1 W6 par_strict_col2_par_strict by blast
      then have W10: "B \<noteq> P"
        by (metis W6 W4A bet_out_1 out_col par_strict_not_col_3)
      have W11: "P \<noteq> C"
        using W6 W4 is_midpoint_id_2 by blast
      {
        assume "P = D"
        then have "False"
          by (metis Col_def P3 W1 W3 W4A W5 W10 W11 col_trivial_2 colx l9_18_R1)
      }
      then have "P \<noteq> D" by auto
      then obtain X Y where W12: "Bet P B X \<and> Bet P C Y \<and> Bet X A1 Y"
        using W5 assms tarski_s_parallel_postulate_def by blast
      then have "P \<noteq> X"
        using W10 bet_neq12__neq by auto
      then have "A1 A2 ParStrict P X"
        by (metis Col_cases P3 P6 W10 W12 W3 bet_col colx par_strict_col2_par_strict)
      then have W15: "A1 A2 OS P X"
        by (simp add: l12_6)
      have "P \<noteq> Y"
        using W11 W12 between_identity by blast
      then have "A1 A2 ParStrict P Y"
        by (metis Col_def W11 W12 W4A W9 col_trivial_2 par_strict_col2_par_strict)
      then have W16: "A1 A2 OS P Y"
        using l12_6 by auto
      have "Col A1 X Y"
        by (simp add: W12 bet_col col_permutation_4)
      then have "A1 Out X Y" using col_one_side_out W15 W16
        using one_side_symmetry one_side_transitivity by blast
      then have "False"
        using W12 not_bet_and_out by blast
    }
    then have "Col C1 B1 B2 \<and> Col C2 B1 B2"
      by auto
  }
  {
    fix A1 A2 B1 B2 P C1 C2
    assume P1: "Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2"
    have "Col C1 B1 B2"
      by (smt P1 l9_10 not_col_permutation_3 not_strict_par2 par_col2_par par_comm par_id_5 par_symmetry ts_distincts)
    moreover have "Col C2 B1 B2"
      by (smt P1 l9_10 not_col_permutation_3 not_strict_par2 par_col2_par par_id_5 par_left_comm par_symmetry ts_distincts)
    ultimately have "Col C1 B1 B2 \<and> Col C2 B1 B2" by auto
  }
  then show ?thesis
    using playfair_s_postulate_def
    by (metis \<open>\<And>P C2 C1 B2 B1 A2 A1. \<not> Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<Longrightarrow> Col C1 B1 B2 \<and> Col C2 B1 B2\<close>)
qed

end
end
