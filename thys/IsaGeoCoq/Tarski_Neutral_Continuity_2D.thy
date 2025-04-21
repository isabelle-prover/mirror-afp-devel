(* IsaGeoCoq - Tarski_Neutral_Continuity_2D.thy

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

theory Tarski_Neutral_Continuity_2D

imports
  Tarski_Neutral_2D
  Tarski_Neutral_Continuity
begin

context Tarski_neutral_2D

begin

(** The center of a circle belongs to the perpendicular bisector of each chord *)

lemma mid_onc2_perp__col:
  assumes "A \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "X Midpoint A B" and
    "X Y Perp A B" 
  shows "Col X Y PO"
  using all_coplanar assms(1) assms(2) assms(3) assms(4) assms(5) 
    cop_mid_onc2_perp__col by blast

(** Euclid Book III Prop 4.
 If in a circle two straight lines which do not pass through the center cut one another,
 then they do not bisect one another.
 *)

lemma mid2_onc4__eq: 
  assumes "B \<noteq> C" and 
    "A \<noteq> B" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "D OnCircle PO P" and
    "X Midpoint A C" and
    "X Midpoint B D" 
  shows "X = PO" 
proof -
  have "Per PO X A" 
    using assms(3) assms(5) assms(7) mid_onc2__per by blast
  have "Per PO X B" 
    using assms(4) assms(6) assms(8) mid_onc2__per by auto
  {
    assume "X \<noteq> PO"
    have "Col A B X" 
      by (meson Per_cases \<open>Per PO X A\<close> \<open>Per PO X B\<close> \<open>X \<noteq> PO\<close> per2__col)
    have "Col B X D" 
      using Col_def Midpoint_def assms(8) by blast
    have "Col A X C" 
      by (simp add: assms(7) bet_col midpoint_bet)
    have "A = X \<longrightarrow> False" 
      by (metis \<open>Per PO X B\<close> assms(2) assms(3) assms(4) 
          col_trivial_3 is_midpoint_id_2 onc2_per__mid)
    moreover have "A \<noteq> X \<longrightarrow> False" 
      by (metis \<open>Col A B X\<close> \<open>Col A X C\<close> assms(1) assms(2) assms(3) 
          assms(4) assms(5) assms(7) col_trivial_3 colx 
          line_circle_two_points midpoint_distinct_2)
    ultimately have False 
      by blast
  }
  thus ?thesis
    by auto
qed

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle,
 then the point taken is the center of the circle.
*)

lemma cong2_onc3__eq: 
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "Cong X A X B" and
    "Cong X A X C"
  shows "X = PO"
proof -
  have "Coplanar A B C PO" 
    using all_coplanar by simp
  moreover have "Coplanar A B C X" 
    using all_coplanar by simp
  ultimately show ?thesis 
    using assms(1) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) assms(8) cong2_cop2_onc3__eq by blast
qed

lemma onc2_mid_cong_col:
  assumes "U \<noteq> V" and 
    "U OnCircle PO P" and
    "V OnCircle PO P" and
    "M Midpoint U V" and
    "Cong U X V X"
  shows "Col PO X M" 
  by (meson Col_def Cong_cases assms(1) assms(2) assms(3) assms(4) 
      assms(5) midpoint_cong onc2__cong upper_dim)

lemma cong_onc3_cases:
  assumes "Cong A X A Y" and
    "A OnCircle PO P" and
    "X OnCircle PO P" and
    "Y OnCircle PO P" 
  shows " X = Y \<or> X Y ReflectL PO A" 
proof (cases "X = Y")
  case True
  thus ?thesis 
    by blast
next
  case False
  hence "X \<noteq> Y" 
    by simp
  obtain M where "M Midpoint X Y" 
    using midpoint_existence by blast
  hence "Per PO M X" 
    using assms(3) assms(4) mid_onc2__per by blast
  have "Per A M X" 
    using Per_def \<open>M Midpoint X Y\<close> assms(1) by auto
  have "M \<noteq> X" 
    using False \<open>M Midpoint X Y\<close> is_midpoint_id by force
  hence "Col A PO M" 
    using \<open>Per A M X\<close> \<open>Per PO M X\<close> per2__col by auto
  have "M Midpoint Y X" 
    using Mid_cases \<open>M Midpoint X Y\<close> by blast
  moreover have "Col PO A M" 
    using \<open>Col A PO M\<close> col_permutation_4 by blast
  moreover have "PO A Perp Y X" 
  proof (cases "M = PO")
    case True
    thus ?thesis           
      by (metis False OnCircle_def assms(1) assms(2) assms(3) 
          calculation(1) cong_diff_3 cong_reflexivity 
          mid_onc2__perp onc2__cong perp_left_comm)
  next
    case False
    then show ?thesis 
      by (metis \<open>M Midpoint X Y\<close> \<open>X \<noteq> Y\<close> assms(2) assms(3) 
          assms(4) calculation(2) col_permutation_5 cong_diff 
          mid_onc2__perp onc2__cong perp_col perp_right_comm)
  qed
  ultimately show ?thesis 
    using ReflectL_def by blast
qed

lemma bet_cong_onc3_cases:
  assumes "T \<noteq> PO" and 
    "Bet A PO T"  and 
    "Cong T X T Y" and
    "A OnCircle PO P" and
    "X OnCircle PO P" and
    "Y OnCircle PO P"  
  shows "X = Y \<or> X Y ReflectL PO A" 
  using Col_cases assms(1) assms(2) assms(3) assms(4) assms(5) 
    assms(6) bet_col cong_onc3_cases l4_17 onc2__cong by blast

lemma prop_7_8: 
  assumes "Diam A B PO P" and
    "Bet A PO T" and
    "X OnCircle PO P" and
    "Y OnCircle PO P" and
    "A PO X LeA A PO Y"
  shows "T Y Le T X" 
proof (cases "PO = P")
  case True
  thus ?thesis 
    by (metis assms(4) assms(5) lea_distincts onc_not_center onc_sym)
next
  case False
  hence "PO \<noteq> P" 
    by simp
  show ?thesis 
  proof (cases "PO = T")
    case True 
    thus ?thesis 
      using assms(3) assms(4) cong__le onc2__cong by auto
  next
    case False
    hence "PO \<noteq> T"
      by simp

    show ?thesis 
    proof (cases "Cong A X A Y")
      case True
      thus ?thesis 
        by (metis assms(2) assms(3) assms(4) assms(5) bet_col 
            cong__le l4_17 lea_distincts not_cong_3412 onc2__cong)
    next
      case False
      have "T X Le T A" 
        using assms(1) assms(2) assms(3) bet_onc_le_b by auto
      have "Y PO T LeA X PO T" 
        by (metis \<open>PO \<noteq> T\<close> assms(2) assms(5) l11_36_aux1 lea_comm lea_distincts)
      have "Cong PO X PO Y" 
        using assms(3) assms(4) onc2__cong by blast 
      thus ?thesis 
        using t18_18 by (metis \<open>PO \<noteq> T\<close> \<open>Y PO T LeA X PO T\<close> cong_identity 
            cong_reflexivity le_reflexivity lta__nlea nlt__le not_cong_3412 t18_19)
    qed
  qed
qed

lemma Prop_7_8_uniqueness: 
  assumes "T \<noteq> PO" and
    "X \<noteq> Y" and
    (*  "Bet A PO T" and*)
    "Cong T X T Y" and
    "Cong T X T Z" and
    (* "A OnCircle PO P" and *)
    "X OnCircle PO P" and
    "Y OnCircle PO P" and
    "Z OnCircle PO P" 
  shows "Z = X \<or> Z = Y" 
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) cong2_onc3__eq)

lemma chords_midpoints_col_par:
  assumes (*"PO \<noteq> P" and*)
    "A OnCircle PO P" and
    "B OnCircle PO P" and 
    "C OnCircle PO P" and
    "D OnCircle PO P" and 
    "M Midpoint A B" and
    "N Midpoint C D" and
    "Col PO M N" and 
    "\<not> Col PO A B" and 
    "\<not> Col PO C D" 
  shows "A B Par C D" 
proof -
  have "PO M Perp A B"
    by (metis assms(1) assms(2) assms(5) assms(8) mid_onc2__perp midpoint_col not_col_distincts)
  moreover have "PO N Perp C D" 
    by (metis assms(9) assms(3) assms(4) assms(6) mid_onc2__perp midpoint_col not_col_distincts)
  hence "PO M Perp C D" 
    by (metis assms(5) assms(8) assms(7) col_permutation_5 midpoint_col perp_col)
  ultimately show ?thesis 
    by (meson Perp_cases l12_9_2D)
qed

lemma onc3_mid2__ncol:
  assumes (*"PO \<noteq> P" and*) 
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and 
    "A' Midpoint A C" and
    "B' Midpoint B C" and
    "\<not> Col A B C"
  shows "\<not> Col PO A' B' \<or> A' = PO \<or> B' = PO" 
proof (cases "Col PO A C")
  case True
  hence "A = C \<or> PO Midpoint A C" 
    using assms(1) assms(3) l7_20 not_col_permutation_4 onc2__cong by blast 
  thus ?thesis   
    using MidR_uniq_aux assms(4) assms(6) col_trivial_3 by blast
next
  case False
  hence "\<not> Col PO A C"
    by simp
  show ?thesis 
  proof (cases "Col PO B C")
    case True
    hence "B = C \<or> PO Midpoint B C" 
      by (metis assms(2) assms(3) col_permutation_4 l7_20_bis onc2__cong)
    thus ?thesis 
      using assms(5) assms(6) col_trivial_2 l7_17 by blast
  next
    case False
    hence "\<not> Col PO B C"
      by simp
    {
      assume "Col PO A' B'"
      hence "A C Par B C" 
        using False \<open>\<not> Col PO A C\<close> assms(2) assms(3) assms(4) 
          assms(5) assms(1) chords_midpoints_col_par by force
      hence False 
        using assms(6) par_comm par_id_2 by blast
    }
    thus ?thesis 
      by blast
  qed
qed

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle, 
 then the point taken is the center of the circle.*)

lemma onc4_cong2__eq: 
  assumes "A \<noteq> B" and
    "C \<noteq> D" and
    "\<not> A B Par C D" and
    "A OnCircle PO P" and
    "B OnCircle PO P" and
    "C OnCircle PO P" and
    "D OnCircle PO P" and
    "Cong A X B X" and
    "Cong C X D X" 
  shows "PO = X" 
proof (cases "PO = P")
  case True
  then show ?thesis   
    using assms(2) assms(6) assms(7) inc_eq onc__inc by blast
next
  case False
  obtain M where "M Midpoint A B" 
    using midpoint_existence by blast
  hence "Col PO X M" 
    using assms(1) assms(4) assms(5) assms(8) onc2_mid_cong_col by blast
  obtain N where "N Midpoint C D" 
    using midpoint_existence by blast
  hence "Col PO X N" 
    using assms(2) assms(6) assms(7) assms(9) onc2_mid_cong_col by blast
  show ?thesis 
  proof (cases "PO = X")
    case True
    thus ?thesis 
      by simp
  next
    case False
    hence "PO \<noteq> X"
      by simp
    have "Col PO M N" 
      using False \<open>Col PO X M\<close> \<open>Col PO X N\<close> col_transitivity_1 by blast
    have "X = M \<or> \<not> Col A B X \<and> M PerpAt X M A B" 
      by (simp add: \<open>M Midpoint A B\<close> assms(1) assms(8) cong_perp_or_mid)
    moreover have "X = N \<or> \<not> Col C D X \<and> N PerpAt X N C D" 
      using \<open>N Midpoint C D\<close> assms(2) assms(9) cong_perp_or_mid by auto
    moreover 
    {
      assume "X = M" and "X = N"
      hence "PO = X" 
        by (metis \<open>M Midpoint A B\<close> \<open>N Midpoint C D\<close> assms(1) assms(3) 
            assms(4) assms(5) assms(6) assms(7) l12_17 mid2_onc4__eq 
            par_reflexivity symmetric_point_uniqueness)
    }
    moreover 
    {
      assume "X = M" and "\<not> Col C D X" and "N PerpAt X N C D" 
      hence "M N Perp C D" 
        using perp_in_perp by blast

      have "PO = X" 
      proof (cases "Col PO A B")
        case True
        thus ?thesis 
          by (metis \<open>M Midpoint A B\<close> \<open>X = M\<close> assms(1) assms(4) assms(5) 
              assms(8) col_onc2__mid cong_perp_or_mid midpoint_col not_col_permutation_2)
      next
        case False
        have "PO M Perp A B" 
          using \<open>M Midpoint A B\<close> \<open>PO \<noteq> X\<close> \<open>X = M\<close> assms(1) assms(4) 
            assms(5) mid_onc2__perp by blast
        hence "M PO Perp C D" 
          by (metis Perp_cases \<open>Col PO M N\<close> \<open>Col PO X M\<close> \<open>M N Perp C D\<close> 
              \<open>X = M\<close> assms(3) calculation(3) l12_9_2D perp_col0)
        then show ?thesis 
          by (meson Perp_cases \<open>PO M Perp A B\<close> assms(3) l12_9_2D)
      qed
    }
    moreover 
    {
      assume "\<not> Col A B X" and "M PerpAt X M A B" and "X = N"

      have "PO = X" 
      proof (cases "Col PO C D")
        case True
        have "C = D \<or> PO Midpoint C D" 
          using Col_cases True assms(6) assms(7) col_onc2__mid by blast
        thus ?thesis 
          by (simp add: \<open>N Midpoint C D\<close> \<open>X = N\<close> assms(2) l7_17)
      next
        case False
        have "PO N Perp C D" 
          using \<open>N Midpoint C D\<close> \<open>PO \<noteq> X\<close> \<open>X = N\<close> assms(2) assms(6) assms(7) 
            mid_onc2__perp by auto
        have "N M Perp A B" 
          using \<open>M PerpAt X M A B\<close> \<open>X = N\<close> perp_in_perp by auto
        hence "A B Par C D" 
          by (metis Col_perm Perp_cases \<open>Col PO M N\<close> \<open>Col PO X N\<close> 
              \<open>PO N Perp C D\<close> \<open>X = N\<close> calculation(3) l12_9_2D perp_col0)
        thus ?thesis 
          by (simp add: assms(3))
      qed
    }
    moreover 
    {
      assume "\<not> Col A B X" and "M PerpAt X M A B" and
        "\<not> Col C D X" and "N PerpAt X N C D" 
      have "X M Perp A B" 
        using \<open>M PerpAt X M A B\<close> perp_in_perp by auto
      hence "X PO Perp A B" 
        by (metis Col_cases False \<open>Col PO X M\<close> perp_col)
      moreover have "X N Perp C D"
        using \<open>N PerpAt X N C D\<close> perp_in_perp by auto
      hence "X PO Perp C D" 
        by (metis False \<open>Col PO X N\<close> not_col_permutation_2 perp_col)
      ultimately have "PO = X" 
        by (meson Perp_cases assms(3) l12_9_2D)
    }
    ultimately show ?thesis 
      by blast
  qed
qed

lemma onc2__oreq:
  assumes "InterCCAt A B C D P Q" and
    "Z OnCircle A B" and
    "Z OnCircle C D"
  shows "Z = P \<or> Z = Q" 
  by (metis InterCCAt_def assms(1) assms(2) assms(3) cong2_onc3__eq interccat__neq onc2__cong)

end
end