(* IsaGeoCoq - Highschool_Neutral.thy

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


theory Highschool_Neutral

imports 
  Tarski_Neutral
begin

section "Highschool Neutral"

context Tarski_neutral_dimensionless

begin

subsection "Definitions"

subsection "Propositions"

(** Existence of the interior bisector of an angle. *)

lemma bisector_existence:
  assumes "A \<noteq> B" and "B \<noteq> C"
  shows "\<exists> E. E InAngle A B C \<and> A B E CongA E B C"
proof (cases "Col A B C")
  case True
  thus ?thesis 
  proof (cases "B Out A C")
    case True
    have "C InAngle A B C" 
      using assms(1) assms(2) inangle3123 by presburger
    moreover
    have "A B C CongA C B C" 
      by (metis between_trivial2 True l11_21_b out2_bet_out)
    ultimately
    show ?thesis 
      by blast
  next
    case False
    hence "Bet A B C" 
      using True l6_4_2 by blast
    have "A \<noteq> C" 
      using False assms(1) out_trivial by blast
    then obtain E where "B E Perp A C" 
      using perp_exists by blast
    have "E InAngle A B C" 
      by (metis \<open>B E Perp A C\<close> \<open>Bet A B C\<close> assms(1) assms(2) in_angle_line perp_not_eq_1)
    moreover
    have "A B E CongA E B C" 
      by (metis True \<open>B E Perp A C\<close> assms(1) assms(2) col_permutation_5 
          l11_16 l8_2 not_col_permutation_4 per_col perp_col1 perp_not_eq_1 perp_per_1)
    ultimately
    show ?thesis 
      by blast
  qed
next
  case False
  hence "\<not> Col A B C" 
    by simp
  obtain C' where "Bet B A C'" and "Cong A C' B C" 
    using segment_construction by blast
  obtain A' where "Bet B C A'" and "Cong C A' B A" 
    using segment_construction by blast
  obtain I where "I Midpoint A' C'" 
    using midpoint_existence by blast
  hence "I \<noteq> B" 
    by (metis False bet_col midpoint_bet \<open>Bet B A C'\<close> \<open>Bet B C A'\<close>
        between_inner_transitivity between_symmetry)
  have "Cong B C' A' B" 
    by (meson Bet_cases \<open>Bet B A C'\<close> \<open>Cong A C' B C\<close> \<open>Bet B C A'\<close> \<open>Cong C A' B A\<close> 
        l2_11_b not_cong_2134 not_cong_3421)
  hence "A' C' B CongA C' A' B" 
    by (metis False \<open>Bet B A C'\<close> \<open>Bet B C A'\<close> assms(1) assms(2) bet_col1 
        bet_neq12__neq cong_3421 cong_reflexivity l11_51 not_col_permutation_4 not_cong_2134)
  have "C' I B CongA A' I B \<and> C' B I CongA A' B I" 
  proof -
    have "Cong I B I B" 
      by (simp add: cong_reflexivity) 
    hence "(I \<noteq> B \<longrightarrow> (C' I B CongA A' I B \<and> C' B I CongA A' B I))" 
      by (metis Cong_cases conga_distinct l11_51 Tarski_neutral_dimensionless.midpoint_cong 
          Tarski_neutral_dimensionless_axioms \<open>A' C' B CongA C' A' B\<close> 
          \<open>Cong B C' A' B\<close> \<open>I Midpoint A' C'\<close>)
    thus ?thesis
      using \<open>I \<noteq> B\<close> by blast
  qed
  have "I InAngle A B C" 
  proof -
    have "A \<noteq> B" 
      by (simp add: assms(1))
    moreover
    have "C \<noteq> B" 
      using assms(2) by blast
    moreover  
    have "I \<noteq> B" 
      by (simp add: \<open>I \<noteq> B\<close>)
    moreover
    have "\<exists> X. Bet A X C \<and> (X = B \<or> B Out X I)" 
    proof -
      have "Bet A' I C'" 
        by (simp add: \<open>I Midpoint A' C'\<close> midpoint_bet)
      hence "\<exists> x1. (Bet I x1 B \<and> Bet A x1 A')"
        using \<open>Bet B A C'\<close> inner_pasch by blast
      then obtain x1 where "Bet I x1 B" and "Bet A x1 A'"
        by blast
      then obtain x2 where  "Bet x1 x2 B" and "Bet C x2 A"
        using \<open>Bet B C A'\<close> inner_pasch by blast
      hence "Bet A x2 C" 
        using Bet_cases by blast
      moreover
      have "x2 = B \<or> B Out x2 I" 
        by (meson \<open>Bet I x1 B\<close> \<open>Bet x1 x2 B\<close> bet_out_1 between_exchange2)
      ultimately
      show ?thesis 
        by blast
    qed
    ultimately
    show ?thesis 
      by (simp add: InAngle_def)
  qed
  moreover
  have "A B I CongA I B C" 
  proof -
    have "C' B I CongA A' B I" 
      using \<open>C' I B CongA A' I B \<and> C' B I CongA A' B I\<close> by blast
    thus ?thesis 
      using assms(1) assms(2) bet_out conga_right_comm l11_10 out_trivial 
      using \<open>Bet B A C'\<close> \<open>Bet B C A'\<close> \<open>I \<noteq> B\<close> by presburger
  qed
  ultimately
  show ?thesis 
    by blast
qed

lemma not_col_bfoot_not_equality:
  assumes "\<not> Col A B C" and
    "Coplanar A B C I" and
    "Col A B H1" and
    (*"Col B C H2" and*)
    "A B I CongA I B C" and
    "A B Perp I H1" and
    "B C Perp I H2" 
  shows "H1 \<noteq> B \<and> H2 \<noteq> B" 
proof -
  {
    assume "H1 = B"
    hence "Per A B I" 
      using assms(5) perp_left_comm perp_per_1 by blast
    have "Col A C B" 
    proof -
      have "Coplanar I A C B" 
        using assms(2) ncoplanar_perm_11 by blast
      moreover
      have "I \<noteq> B" 
        using \<open>H1 = B\<close> assms(5) perp_distinct by blast
      moreover
      have "Per I B C" 
        using \<open>Per A B I\<close> assms(4) l11_17 by blast
      hence "Per C B I" 
        by (simp add: l8_2)
      ultimately
      show ?thesis 
        using \<open>Per A B I\<close> cop_per2__col by blast
    qed
    hence False 
      using assms(1) col_permutation_5 by blast
  }
  moreover
  {
    assume "H2 = B"
    hence "Per C B I" 
      using assms(6) perp_per_1 by blast
    hence "Per I B C" 
      using l8_2 by blast
    have "Col A C B" 
    proof -
      have "Coplanar I A C B" 
        by (simp add: assms(2) coplanar_perm_19)
      moreover
      have "I \<noteq> B" 
        using \<open>H2 = B\<close> assms(6) perp_distinct by presburger
      moreover
      have "Per A B I" 
        by (meson \<open>Per I B C\<close> assms(4) l11_17 not_conga_sym)
      ultimately
      show ?thesis 
        using \<open>Per C B I\<close> cop_per2__col by blast
    qed
    hence False 
      using assms(1) col_permutation_5 by blast
  }
  ultimately show ?thesis by blast
qed

lemma bisector_foot_out_out:
  assumes "\<not> Col A B C" and
    "Coplanar A B C I" and
    "Col B C H2" and
    "A B I CongA I B C" and
    "A B Perp I H1" and
    "B C Perp I H2" and
    "B Out H1 A"
  shows "B Out H2 C" 
proof -
  have "Col A B H1" 
    using assms(7) col_permutation_2 out_col by blast
  hence "H1 \<noteq> B \<and> H2 \<noteq> B" 
    using not_col_bfoot_not_equality assms(1) assms(2) assms(4) assms(5) assms(6) by blast
  hence "Acute H1 B I" 
    by (metis l8_16_1 \<open>Col A B H1\<close> assms(5) col_trivial_2 l11_43) 
  have "H1 B I CongA I B C" 
    by (metis CongA_def Out_def assms(4) assms(7) not_bet_distincts not_conga out2__conga)
  hence "Acute I B C" 
    using \<open>Acute H1 B I\<close> acute_conga__acute by blast
  thus ?thesis 
    by (meson acute_col_perp__out assms(3) assms(6))
qed

lemma not_col_efoot_not_equality:
  assumes "\<not> Col A B C" and
    "Coplanar A B C I" and
    "Col A B H1" and
    "Col B C H2" and
    "Cong I H1 I H2" and
    "A B Perp I H1" and
    "B C Perp I H2"
  shows "H1 \<noteq> B \<and> H2 \<noteq> B" 
proof -
  {
    assume "H1 = B"
    hence "H2 \<noteq> B" 
      using assms(1) assms(2) assms(6) assms(7) col_permutation_2 cop_perp2__col 
        coplanar_perm_11 perp_comm perp_right_comm by blast
    hence False 
      by (metis Cong_cases Perp_cases \<open>H1 = B\<close> acute_not_per assms(4) assms(5) 
          assms(7) cong__acute perp_col1 perp_distinct perp_per_1)
  }
  moreover
  {
    assume "H2 = B"
    have "B H1 Perp I H1" 
      using \<open>H1 = B \<Longrightarrow> False\<close> assms(3) assms(6) col_trivial_2 perp_col2 by presburger
    hence "Per B H1 I" 
      using Perp_cases perp_per_1 by blast
    have "B H1 I CongA H1 B I" 
      by (metis Cong_cases \<open>H1 = B \<Longrightarrow> False\<close> \<open>H2 = B\<close> assms(5) 
          cong_identity_inv cong_reflexivity l11_51)
    hence "Per H1 B I" 
      using \<open>Per B H1 I\<close> l11_17 by blast
    hence False 
      using \<open>H1 = B \<Longrightarrow> False\<close> \<open>Per B H1 I\<close> l8_2 l8_7 by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma equality_foot_out_out:
  assumes "\<not> Col A B C" and
    "I InAngle A B C" and
    "Col B C H2" and
    "Cong I H1 I H2" and
    "A B Perp I H1" and
    "B C Perp I H2" and
    "B Out H1 A"
  shows "B Out H2 C" 
proof -
  have "H1 \<noteq> B \<and> H2 \<noteq> B" 
    by (metis Col_cases cong__acute acute_not_per assms(4) assms(5) assms(7) 
        col_trivial_2 l8_16_1 out_col out_diff1)
  have "Cong H1 B H2 B \<and> H1 B I CongA H2 B I \<and> H1 I B CongA H2 I B"
  proof -
    have "B H1 I CongA B H2 I" 
      by (metis Col_cases l11_16 \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(3) assms(5) 
          assms(6) assms(7) col_trivial_2 conga_comm l8_16_1 out_col)
    moreover
    have "Per B H1 I" 
      by (metis Col_cases l8_16_1 l8_2 assms(5) assms(7) col_trivial_2 out_col)
    hence "H1 I Le B I" 
      using l11_46 by (metis perp_distinct \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(5) lt__le)
    ultimately
    show ?thesis 
      using assms(4) cong_reflexivity l11_52 not_cong_2143 by blast
  qed
  have "I B TS A C" 
    by (metis col_permutation_2 col_permutation_5 out_col perp_not_col2 
        assms(2) assms(3) assms(5) assms(6) assms(7) in_angle_two_sides)
  have "B Out H1 H2 \<or> I B TS H1 H2" 
  proof -
    have "Coplanar I B H1 H2" 
    proof -
      have "\<not> Col A I B" 
        using TS_def \<open>I B TS A C\<close> by blast
      moreover
      have "Coplanar A I B H1" 
        using assms(5) coplanar_perm_2 perp__coplanar by blast
      moreover
      have "Coplanar A I B H2" 
        by (metis not_col_distincts assms(1) assms(2) assms(3) col_cop__cop 
            coplanar_perm_6 inangle__coplanar)
      ultimately
      show ?thesis 
        using coplanar_trans_1 by blast
    qed
    moreover
    have "I B H1 CongA I B H2" 
      by (simp add: \<open>Cong H1 B H2 B \<and> H1 B I CongA H2 B I \<and> H1 I B CongA H2 I B\<close> conga_comm)
    ultimately
    show ?thesis 
      using conga_cop__or_out_ts by blast
  qed
  moreover
  {
    assume "B Out H1 H2"
    hence False
      by (metis Col_cases \<open>B Out H1 H2\<close> assms(1) assms(3) assms(7) 
          col_trivial_3 l9_19 out_diff2 out_one_side)
  }
  moreover
  {
    assume "I B TS H1 H2"
    have "I B TS A H2" 
      by (meson not_col_distincts \<open>I B TS H1 H2\<close> assms(7) l9_5)
    hence "I B OS H2 C" 
      using OS_def \<open>I B TS A C\<close> l9_2 by blast
    hence "B I OS H2 C" 
      using invert_one_side by blast
    moreover
    have "Col B H2 C" 
      using Col_cases assms(3) by blast
    ultimately
    have "B Out H2 C" 
      using col_one_side_out by force
  }
  ultimately show ?thesis by blast
qed

(** The points on the bisector of an angle are at equal distances of the two sides. *)

lemma bisector_perp_equality:
  assumes "Coplanar A B C I" and
    "Col B H1 A" and
    "Col B C H2" and
    "A B Perp I H1" and
    "B C Perp I H2" and
    "A B I CongA I B C"
  shows "Cong I H1 I H2" 
proof (cases "Col A B C")
  case True
  hence "A B Perp I H2" 
    by (metis assms(4) assms(5) col_trivial_3 not_col_permutation_2 perp_col2 perp_not_eq_1)
  have "H1 = H2" 
    by (metis col_trivial_2 True \<open>A B Perp I H2\<close> assms(2) assms(3) 
        assms(4) assms(5) colx l8_18_uniqueness not_col_permutation_1 perp_not_eq_1)
  thus ?thesis 
    by (simp add: cong_reflexivity)
next
  case False
  hence "\<not> Col A B C"
    by blast
  have "Col A B H1" 
    using Col_cases assms(2) by blast
  have "Col B C H2" 
    by (simp add: assms(3))
  hence "H1 \<noteq> B \<and> H2 \<noteq> B" 
    using False \<open>Col A B H1\<close> assms(1) assms(4) assms(5) assms(6) 
      not_col_bfoot_not_equality by blast
  show ?thesis 
  proof (cases "B Out H1 A")
    case True
    hence "B Out H2 C" 
      using False assms(1) assms(3) assms(4) assms(5) assms(6) 
        bisector_foot_out_out by blast
    have "\<not> Col I B H1" 
      by (metis \<open>Col A B H1\<close> \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(4) l6_16_1 perp_not_col2)
    moreover
    have "B H1 I CongA B H2 I" 
    proof -
      have "Per B H1 I" 
        using \<open>Col A B H1\<close> assms(4) col_trivial_2 l8_16_1 l8_2 by blast
      moreover
      have "Per B H2 I" 
        by (meson l8_2 assms(3) assms(5) col_trivial_3 l8_16_1)
      ultimately
      show ?thesis 
        by (metis Col_cases Perp_cases \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(4) assms(5) 
            col_trivial_2 l11_16 l8_16_1)
    qed
    moreover
    have "H1 B I CongA H2 B I" 
    proof -
      have "B Out H1 A" 
        by (simp add: True)
      moreover
      have "B Out H2 C" 
        using \<open>B Out H2 C\<close> by auto
      moreover
      have "A B I CongA I B C" 
        by (simp add: assms(6))
      have "B Out I I" 
        by (metis \<open>\<not> Col I B H1\<close> bet_out_1 not_bet_distincts not_col_distincts)
      ultimately
      show ?thesis 
        by (meson conga_left_comm l11_10 assms(6) conga_comm)
    qed
    hence "I B H1 CongA I B H2" 
      using conga_comm by blast
    moreover
    have "Cong I B I B" 
      by (simp add: cong_reflexivity)
    ultimately
    show ?thesis 
      using l11_50_2 by blast
  next
    case False
    obtain A' where "B Midpoint A A'" 
      using symmetric_point_construction by presburger
    hence "Bet A B A'" 
      by (simp add: midpoint_bet)
    hence "B Out H1 A'" 
      by (metis False Out_def midpoint_distinct_1 
          Tarski_neutral_dimensionless.perp_distinct 
          Tarski_neutral_dimensionless_axioms \<open>B Midpoint A A'\<close> 
          \<open>Col A B H1\<close> \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(4) bet_out_1 fourth_point)
    obtain C' where "B Midpoint C C'"
      using symmetric_point_construction by presburger
    hence "Bet C B C'" 
      using midpoint_bet by blast
    have "B Out H2 C'" 
    proof -
      {
        assume "Col A' B C'"
        hence "Col A B C" 
          by (metis Out_def midpoint_distinct_1 \<open>B Midpoint C C'\<close> \<open>B Out H1 A'\<close> 
              \<open>Bet A B A'\<close> \<open>Bet C B C'\<close> bet_col col2__eq col_trivial_2)
        hence False 
          using \<open>\<not> Col A B C\<close> by auto
      }
      hence "\<not> Col A' B C'" 
        by blast
      moreover
      have "Coplanar A' B C' I" 
      proof -
        have "Coplanar A B C A'" 
          by (simp add: \<open>Bet A B A'\<close> bet__coplanar coplanar_perm_1)
        moreover
        have "Coplanar A B C B" 
          using ncop_distincts by blast
        moreover
        have "Coplanar A B C C'" 
          by (metis Bet_cases Col_def \<open>Bet C B C'\<close> ncop__ncols)
        ultimately
        show ?thesis 
          by (meson \<open>\<not> Col A B C\<close> assms(1) coplanar_pseudo_trans)
      qed
      moreover
      have "Col B C' H2" 
        by (metis Col_def \<open>Bet C B C'\<close> \<open>\<not> Col A B C\<close> assms(3) col_transitivity_1 col_trivial_2)
      moreover  
      have "A' B I CongA I B C'" 
        by (metis conga_right_comm \<open>Bet A B A'\<close> \<open>Bet C B C'\<close> assms(6) 
            calculation(1) l11_13 not_col_distincts)
      moreover
      have "A' B Perp I H1" 
        by (metis \<open>Bet A B A'\<close> assms(4) bet_col calculation(1) not_col_distincts perp_col2)
      moreover
      have "B C' Perp I H2" 
        by (metis Col_cases Col_def \<open>Bet C B C'\<close> assms(5) calculation(1) 
            not_col_distincts perp_col)
      ultimately
      show ?thesis 
        using \<open>B Out H1 A'\<close> bisector_foot_out_out by blast
    qed
    have "\<not> Col I B H1" 
      by (metis perp_not_col2  \<open>Col A B H1\<close> \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(4) l6_16_1)
    moreover
    have "B H1 I CongA B H2 I" 
      by (metis \<open>Col A B H1\<close> \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(3) assms(4) assms(5) 
          col_trivial_2 col_trivial_3 conga_comm l11_16 l8_16_1)
    moreover
    have "H1 B I CongA I B H2" 
    proof -
      have "A' B I CongA I B C'" 
        by (metis l11_13 not_col_distincts \<open>B Midpoint A A'\<close> 
            \<open>B Midpoint C C'\<close> \<open>Bet A B A'\<close> \<open>Bet C B C'\<close> \<open>\<not> Col A B C\<close> 
            assms(6) conga_right_comm midpoint_distinct_2)
      moreover
      have "B Out H1 A'" 
        by (simp add: \<open>B Out H1 A'\<close>)
      moreover
      have "I \<noteq> B" 
        using assms(6) conga_diff45 by auto
      hence "B Out I I " 
        using out_trivial by blast
      ultimately show ?thesis
        using \<open>B Out H2 C'\<close> l11_10 by blast
    qed
    hence  "I B H1 CongA I B H2" 
      using conga_left_comm by presburger
    moreover
    have "Cong I B I B" 
      by (simp add: cong_reflexivity)
    ultimately 
    show ?thesis 
      using l11_50_2 by blast
  qed
qed

(** The points which are at equal distance of the two side of an angle are on the bisector. *)

lemma perp_equality_bisector:
  assumes "\<not> Col A B C" and
    "I InAngle A B C" and
    "Col B H1 A" and
    "Col B H2 C" and
    "A B Perp I H1" and
    "B C Perp I H2" and
    "Cong I H1 I H2"
  shows "A B I CongA I B C" 
proof -
  have "H1 \<noteq> B \<and> H2 \<noteq> B" 
  proof -
    have "Coplanar A B C I" 
      using assms(2) inangle__coplanar ncoplanar_perm_18 by blast
    moreover
    have "Col A B H1" 
      by (simp add: assms(3) col_permutation_2)
    ultimately
    show ?thesis 
      using not_col_efoot_not_equality assms(1) assms(4) assms(5) 
        assms(6) assms(7) col_permutation_5 by blast
  qed
  have "Cong H1 B H2 B \<and> H1 B I CongA H2 B I \<and> H1 I B CongA H2 I B" 
  proof -
    have "B H1 I CongA B H2 I" 
      by (metis NCol_perm l11_16 \<open>H1 \<noteq> B \<and> H2 \<noteq> B\<close> assms(3) assms(4) 
          assms(5) assms(6) col_trivial_3 conga_comm l8_16_1)
    moreover
    have "Cong B I B I" 
      by (simp add: cong_reflexivity)
    moreover
    have "Cong H1 I H2 I" 
      using Cong_cases assms(7) by auto
    moreover
    have "H1 I Le B I" 
      by (metis l11_46 assms(4) assms(6) calculation(1) col_trivial_3 
          conga_distinct conga_sym l11_17 l8_16_1 l8_2 lt__le not_col_permutation_5)
    ultimately
    show ?thesis
      using l11_52 by blast
  qed
  show ?thesis
  proof (cases "B Out A H1")
    case True
    have "B Out H2 C" 
    proof -
      have "Col B C H2" 
        using assms(4) col_permutation_5 by blast
      moreover
      have "B Out H1 A" 
        using Out_cases True by auto
      ultimately
      show ?thesis 
        using assms(1) assms(2) assms(5) assms(6) assms(7) 
          equality_foot_out_out by blast
    qed
    have "A B I CongA C B I" 
    proof -
      have "H1 B I CongA H2 B I" 
        by (simp add: \<open>Cong H1 B H2 B \<and> H1 B I CongA H2 B I \<and> H1 I B CongA H2 I B\<close>)
      moreover
      have "H1 I B CongA H2 I B" 
        by (simp add: \<open>Cong H1 B H2 B \<and> H1 B I CongA H2 B I \<and> H1 I B CongA H2 I B\<close>)
      moreover 
      have "Cong H1 B H2 B" 
        by (simp add: \<open>Cong H1 B H2 B \<and> H1 B I CongA H2 B I \<and> H1 I B CongA H2 I B\<close>)
      moreover
      have "B \<noteq> I"
        using assms(2) inangle_distincts by blast
      hence "B Out I I" 
        using out_trivial by auto
      moreover
      have "B Out A H1" 
        by (simp add: True)
      moreover
      have "B Out C H2" 
        by (simp add: \<open>B Out H2 C\<close> l6_6)
      moreover
      have "I \<noteq> H1" 
        using assms(5) perp_not_eq_2 by auto
      moreover
      have "I \<noteq> H2" 
        using assms(6) perp_not_eq_2 by auto 
      ultimately show ?thesis
        using l11_10 bet_col not_col_distincts assms(1) assms(2) col_inangle2__out 
        by blast
    qed
    thus ?thesis 
      using conga_right_comm by blast
  next
    case False
    hence "\<not> B Out A H1"
      by blast
    {
      assume "B Out C H2"
      have "\<not> Col C B A" 
        by (simp add: assms(1) not_col_permutation_3)
      moreover
      have "I InAngle C B A" 
        by (simp add: assms(2) l11_24)
      moreover
      have "Col B A H1" 
        using Col_cases assms(3) by blast
      moreover
      have "Cong I H2 I H1" 
        using assms(7) not_cong_3412 by blast
      moreover
      have "C B Perp I H2" 
        using Perp_perm assms(6) by blast
      moreover
      have "B A Perp I H1" 
        using assms(5) perp_left_comm by blast
      ultimately
      have "B Out H1 A" 
        using \<open>B Out C H2\<close> equality_foot_out_out l6_6 by blast
      hence False 
        using False Out_cases by blast
    }
    hence "Bet C B H2" 
      using Col_cases assms(4) or_bet_out by blast
    moreover
    have "Bet A B H1" 
      using False NCol_cases assms(3) or_bet_out by blast
    ultimately
    have "A B I CongA C B I" 
      by (metis \<open>Cong H1 B H2 B \<and> H1 B I CongA H2 B I \<and> H1 I B CongA H2 I B\<close> 
          assms(2) between_symmetry inangle_distincts l11_13)
    thus ?thesis 
      by (meson conga_right_comm)
  qed
qed

(** LOCALISATION: TARSKI_DEV.ANNEXE...*)
lemma col_permut132:
  assumes "Col A B C" 
  shows "Col A C B" 
  using Col_cases assms by blast

lemma col_permut213:
  assumes "Col A B C"
  shows "Col B A C" 
  using Col_perm assms by blast

lemma col_permut231:
  assumes "Col A B C"
  shows "Col B C A" 
  using Col_perm assms by blast

lemma col_permut312:
  assumes "Col A B C"
  shows "Col C A B" 
  using Col_perm assms by blast

lemma col_permut321:
  assumes "Col A B C" 
  shows "Col C B A"
  using Col_perm assms by blast

lemma col123_124__col134:
  assumes "P \<noteq> Q" and
    "Col P Q A" and
    "Col P Q B"
  shows "Col P A B" 
  using assms(1) assms(2) assms(3) col_transitivity_1 by blast

lemma col123_124__col234:
  assumes "P \<noteq> Q" and
    "Col P Q A" and
    "Col P Q B"
  shows "Col Q A B" 
  using assms(1) assms(2) assms(3) col_transitivity_2 by blast

lemma triangle_mid_par_strict:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" 
  shows "A B ParStrict Q P" 
  using assms(1) assms(2) assms(3) triangle_mid_par by blast

end
end
