(* IsaGeoCoq - Tarski_Euclidean.thy

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

theory Tarski_Euclidean

imports
  Tarski_Neutral
  Tarski_Postulate_Parallels

begin

section "Tarski Euclidean"

subsection "Tarski's axiom system for Euclidean"

locale Tarski_Euclidean = Tarski_neutral_dimensionless +
  assumes tarski_s_parallel_postulate: 
    "\<forall> A B C D T. (Bet A D T \<and> Bet B D C \<and> A \<noteq> D) 
                         \<longrightarrow>
                      (\<exists> X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y)"

context Tarski_Euclidean

begin

subsection "Definitions"

subsection "Propositions"

theorem tarski_s_parallel_postulate_thm:
  shows tarski_s_parallel_postulate 
  using tarski_s_parallel_postulate tarski_s_parallel_postulate_def by blast

lemma Post02:
  shows "Postulate02" 
  using Postulate02_def tarski_s_euclid_implies_playfair_s_postulate 
    tarski_s_parallel_postulate tarski_s_parallel_postulate_def by blast

theorem playfair_s_postulate_thm:
  shows playfair_s_postulate 
  using Post02 Postulate02_def by auto

lemma Post03:
  shows "Postulate03" 
  using Postulate03_def alternate_interior__triangle 
    playfair__alternate_interior tarski_s_euclid_implies_playfair_s_postulate 
    tarski_s_parallel_postulate tarski_s_parallel_postulate_def by blast

theorem triangle_postulate_thm:
  shows triangle_postulate
  using Post03 Postulate03_def by blast

lemma Post04:
  shows "Postulate04" 
  using P31_P04 Postulate31_def 
    inverse_projection_postulate_def weak_inverse_projection_postulate_def
    original_euclid__original_spp 
    original_spp__inverse_projection_postulate tarski_s_implies_euclid_s_parallel_postulate 
    tarski_s_parallel_postulate tarski_s_parallel_postulate_def
  by blast

theorem bachmann_s_lotschnittaxiom_thm:
  shows bachmann_s_lotschnittaxiom 
  using Post04 Postulate04_def by blast

lemma Post05:
  shows "Postulate05" 
  using Post02 Postulate02_def Postulate05_def playfair_implies_par_trans by blast

theorem postulate_of_transitivity_of_parallelism_thm:
  shows postulate_of_transitivity_of_parallelism 
  using Post05 Postulate05_def by blast

lemma Post06:
  shows "Postulate06" 
  using Post02 Postulate02_def Postulate06_def 
    playfair_s_postulate_implies_midpoint_converse_postulate by fastforce

theorem midpoint_converse_postulate_thm:
  shows midpoint_converse_postulate 
  using Post06 Postulate06_def by blast

lemma Post07:
  shows "Postulate07" 
  using Post02 Postulate02_def Postulate07_def playfair__alternate_interior by blast

theorem alternate_interior_angles_postulate_thm:
  shows alternate_interior_angles_postulate 
  using Post07 Postulate07_def by auto

lemma Post08:
  shows "Postulate08" 
  using Post07 Postulate07_def Postulate08_def 
    alternate_interior__consecutive_interior by blast

theorem consecutive_interior_angles_postulate_thm:
  shows consecutive_interior_angles_postulate 
  using Post08 Postulate08_def by blast

lemma Post09:
  shows "Postulate09" 
  using Post02 equivalent_postulates_without_decidability_of_intersection_of_lines by blast

theorem perpendicular_transversal_postulate_thm:
  shows perpendicular_transversal_postulate 
  using Post09 Postulate09_def by blast

lemma Post10:
  shows "Postulate10" 
  using Post05 equivalent_postulates_without_decidability_of_intersection_of_lines by blast

theorem postulate_of_parallelism_of_perpendicular_transversals_thm:
  shows postulate_of_parallelism_of_perpendicular_transversals 
  using Post10 Postulate10_def by blast

lemma Post11:
  shows "Postulate11" 
  using Post02 equivalent_postulates_without_decidability_of_intersection_of_lines by blast

theorem universal_posidonius_postulate_thm:
  shows universal_posidonius_postulate 
  using Post11 Postulate11_def by blast

lemma Post12:
  shows "Postulate12" 
  by (simp add: Post05 equivalent_postulates_without_decidability_of_intersection_of_lines)

theorem alternative_playfair_s_postulate_thm:
  shows alternative_playfair_s_postulate 
  using Post12 Postulate12_def by blast

lemma Post13:
  shows "Postulate13" 
  using Cycle_2 InterAx5 Post02 by fastforce

theorem proclus_postulate_thm:
  shows proclus_postulate 
  using Post13 Postulate13_def by blast

lemma Post14:
  shows "Postulate14" 
  using Cycle_2 InterAx5 Post02 by blast

theorem alternative_proclus_postulate_thm:
  shows alternative_proclus_postulate 
  using Post14 Postulate14_def by auto

lemma Post15:
  shows "Postulate15" 
  by (simp add: InterCycle4 Post09)

theorem triangle_circumscription_principle_thm:
  shows triangle_circumscription_principle 
  using Post15 Postulate15_def by blast

lemma Post16:
  shows "Postulate16" 
  using Postulate16_def original_euclid__original_spp 
    original_spp__inverse_projection_postulate tarski_s_implies_euclid_s_parallel_postulate 
    tarski_s_parallel_postulate tarski_s_parallel_postulate_def by fastforce

theorem inverse_projection_postulate_thm:
  shows inverse_projection_postulate 
  using Post16 Postulate16_def by blast

lemma Post17:
  shows "Postulate17" 
  using Postulate17_def tarski_s_euclid_implies_euclid_5 
    tarski_s_parallel_postulate tarski_s_parallel_postulate_def by blast

theorem euclid_5_thm:
  shows euclid_5 
  using Post17 Postulate17_def by blast

lemma Post18:
  shows "Postulate18" 
  using Cycle_2 Post14 by fastforce

theorem strong_parallel_postulate_thm:
  shows strong_parallel_postulate 
  by (simp add: proclus_postulate_thm proclus_s_postulate_implies_strong_parallel_postulate)

lemma Post19:
  shows "Postulate19" 
  using Cycle_2 Post18 by force

theorem alternative_strong_parallel_postulate_thm:
  shows alternative_strong_parallel_postulate 
  using Post19 Postulate19_def by blast

lemma Post20:
  shows "Postulate20" 
  using Cycle_2 Post17 by blast

theorem euclid_s_parallel_postulate_thm:
  shows euclid_s_parallel_postulate 
  using Post20 Postulate20_def by blast

lemma Post21:
  shows "Postulate21" 
  using Post03 Tarski_Euclidean_def Cycle_3 by blast

theorem postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights_thm:
  shows postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights 
  using Post21 Postulate21_def by blast

lemma Post22:
  shows "Postulate22" 
  using Post21 Tarski_Euclidean_def Cycle_3 by blast

theorem posidonius_postulate_thm:
  shows posidonius_postulate 
  using Post22 Postulate22_def by fastforce

lemma Post23:
  assumes "Postulate01"
  shows "Postulate23" 
  using Post22 Tarski_Euclidean_def Cycle_3 by blast

theorem postulate_of_existence_of_similar_triangles_thm:
  shows postulate_of_existence_of_similar_triangles 
  using Post23 Postulate01_def Postulate23_def tarski_s_parallel_postulate_thm by auto

lemma Post24:
  shows "Postulate24" 
  using Post23 Postulate01_def Tarski_Euclidean_def Cycle_3 
    tarski_s_parallel_postulate tarski_s_parallel_postulate_def by blast

theorem thales_postulate_thm:
  shows thales_postulate 
  using Post24 Postulate24_def by blast

lemma Post25:
  shows "Postulate25" 
  using Post24 Postulate24_def Postulate25_def 
    thales_postulate__thales_converse_postulate by blast

theorem thales_converse_postulate_thm:
  shows thales_converse_postulate 
  using Post25 Postulate25_def by blast

lemma Post26:
  shows "Postulate26" 
  using Post24 Postulate24_def Postulate26_def thales_converse_postulate__thales_existence 
    thales_postulate__thales_converse_postulate by blast

theorem existential_thales_postulate_thm:
  shows existential_thales_postulate 
  using Post26 Postulate26_def by blast

lemma Post27:
  shows "Postulate27" 
  using Post26 Tarski_Euclidean_def Cycle_3 by blast

theorem postulate_of_right_saccheri_quadrilaterals_thm:
  shows postulate_of_right_saccheri_quadrilaterals 
  using Post27 Postulate27_def by auto

lemma Post28:
  shows "Postulate28" 
  using Post27 Tarski_Euclidean_def Cycle_3 by blast

theorem postulate_of_existence_of_a_right_saccheri_quadrilateral_thm:
  shows postulate_of_existence_of_a_right_saccheri_quadrilateral 
  using Post28 Postulate28_def by blast

lemma Post29:
  shows "Postulate29" 
  using Cycle_3 Post28 by blast

theorem postulate_of_right_lambert_quadrilaterals_thm:
  shows postulate_of_right_lambert_quadrilaterals 
  using Post29 Postulate29_def by blast

lemma Post30:
  shows "Postulate30" 
  using Cycle_3 Post03 by blast

theorem postulate_of_existence_of_a_right_lambert_quadrilateral_thm:
  shows postulate_of_existence_of_a_right_lambert_quadrilateral 
  using Post30 Postulate30_def by blast

lemma Post31:
  shows "Postulate31" 
  using Post16 Postulate16_def Postulate31_def 
    inverse_projection_postulate_def weak_inverse_projection_postulate_def by blast

theorem weak_inverse_projection_postulate_thm:
  shows weak_inverse_projection_postulate 
  using Post31 Postulate31_def by blast

lemma Post32:
  shows "Postulate32" 
  using P31_P32 Post31 by blast

theorem  weak_tarski_s_parallel_postulate_thm:
  shows weak_tarski_s_parallel_postulate 
  using Post32 Postulate32_def by blast

lemma Post33:
  shows "Postulate33" 
  using P04_P33 P31_P04 Post31 by auto

theorem weak_triangle_circumscription_principle_thm:
  shows weak_triangle_circumscription_principle 
  using Post33 Postulate33_def by blast

lemma Post34:
  shows "Postulate34" 
  using P31_P04 P4_P34 Post31 by blast

theorem legendre_s_parallel_postulate_thm:
  shows legendre_s_parallel_postulate 
  using Post34 Postulate34_def by blast

theorem TarskiPP:
  shows "tarski_s_parallel_postulate" 
  by (simp add: tarski_s_parallel_postulate_thm)

lemma parallel_uniqueness:
  assumes "A1 A2 Par B1 B2" and
    "Col P B1 B2" and
    "A1 A2 Par C1 C2" and
    "Col P C1 C2"
  shows "Col C1 B1 B2 \<and> Col C2 B1 B2" 
  using TarskiPP assms(1) assms(2) assms(3) assms(4) playfair_s_postulate_def 
    tarski_s_euclid_implies_playfair_s_postulate by blast

lemma par_trans:
  assumes "A1 A2 Par B1 B2" and
    "B1 B2 Par C1 C2"
  shows "A1 A2 Par C1 C2" 
  using TarskiPP assms(1) assms(2) playfair_implies_par_trans 
    postulate_of_transitivity_of_parallelism_def 
    tarski_s_euclid_implies_playfair_s_postulate by blast

lemma l12_16:
  assumes "A1 A2 Par B1 B2" and
    "Coplanar B1 B2 C1 C2" and
    "X Inter A1 A2 C1 C2"
  shows "\<exists> Y. Y Inter B1 B2 C1 C2" 
  by (metis Inter_def TarskiPP assms(1) assms(2) assms(3) 
      cop_npar__inter inter__npar par_neq2 playfair_implies_par_trans 
      postulate_of_transitivity_of_parallelism_def 
      tarski_s_euclid_implies_playfair_s_postulate)

lemma par_dec:
  shows "A B Par C D \<or> \<not> A B Par C D" 
  by auto

lemma par_not_par:
  assumes "A B Par C D" and
    "\<not> A B Par P Q" 
  shows "\<not> C D Par P Q" 
  using assms(1) assms(2) par_trans by blast

lemma cop_par__inter:
  assumes "A B Par C D" and
    "\<not> A B Par P Q" and
    "Coplanar C D P Q"
  shows "\<exists> Y. Col P Q Y \<and> Col C D Y" 
proof -
  have "\<not> C D Par P Q" 
    using assms(1) assms(2) par_trans by blast
  hence "\<exists> Y. Col Y C D \<and> Col Y P Q" 
    using assms(3) cop_npar__inter_exists by blast
  thus ?thesis 
    using col_permutation_1 by blast
qed

lemma l12_19:
  assumes "\<not> Col A B C" and
    "A B Par C D" and
    "B C Par D A" 
  shows "Cong A B C D \<and> Cong B C D A \<and> B D TS A C \<and> A C TS B D" 
proof -
  obtain P where "P Midpoint A C"
    using midpoint_existence by blast
  obtain D' where "P Midpoint B D'" 
    using symmetric_point_construction by blast
  have "Cong C D' A B" 
    using \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> l7_13 by blast
  have "Cong B C D' A" 
    using l7_13 \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> assms(1) 
      mid_par_cong2 not_col_distincts by presburger
  have "A B Par C D'" 
    using \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> assms(2) 
      l12_17 par_neq1 by blast
  have "C D Par C D'" 
    by (meson \<open>A B Par C D'\<close> assms(2) par_not_par par_symmetry)
  have "Col C D D'" 
    by (simp add: \<open>C D Par C D'\<close> par_id)
  have "B C Par D' A" 
    using \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> assms(3) 
      mid_par_cong2 par_neq1 by blast
  have "D A Par D' A" 
    by (meson \<open>B C Par D' A\<close> assms(3) par_not_par par_symmetry)
  have "Col A D D'" 
    using Par_perm \<open>D A Par D' A\<close> par_id by blast
  have "D = D'" 
    by (metis \<open>C D Par C D'\<close> \<open>Col A D D'\<close> assms(1) assms(2) 
        col_trivial_2 col_trivial_3 l6_21 not_strict_par2 par_symmetry)
  have "Cong A B C D" 
    using \<open>Cong C D' A B\<close> \<open>D = D'\<close> not_cong_3412 by blast
  moreover
  have "Cong B C D A" 
    by (simp add: \<open>Cong B C D' A\<close> \<open>D = D'\<close>)
  moreover 
  have "B D TS A C" 
    by (metis \<open>D = D'\<close> \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> 
        assms(1) assms(2) col_permutation_5 mid_two_sides par_comm 
        par_two_sides_two_sides) 
  moreover
  have "A C TS B D" 
    using assms(2) calculation(3) par_two_sides_two_sides by blast
  ultimately
  show ?thesis 
    by blast
qed

lemma l12_20_bis:
  assumes "A B Par C D" and
    "Cong A B C D" and
    "B D TS A C"
  shows "B C Par D A \<and> Cong B C D A \<and> A C TS B D" 
proof -
  have "B \<noteq> C" 
    using assms(3) ts_distincts by blast
  have "A \<noteq> D" 
    using assms(3) ts_distincts by blast
  have "\<not> Col A B C" 
    by (metis TS_def assms(1) assms(3) not_col_permutation_4 
        par_two_sides_two_sides)
  obtain P where "P Midpoint A C" 
    using midpoint_existence by blast
  obtain D' where "P Midpoint B D'" 
    using symmetric_point_construction by blast
  have "B C Par D' A" 
    using \<open>B \<noteq> C\<close> \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> mid_par_cong2 by blast
  have "Cong C D' A B" 
    using \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> l7_13 by blast
  have "Cong B C D' A" 
    using \<open>B \<noteq> C\<close> \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> mid_par_cong2 by blast
  have "C D Par C D'" 
  proof -
    have "A B Par C D" 
      using assms(1) by blast
    moreover have "A B Par C D'" 
      using \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> calculation l12_17 
        par_distinct by blast
    ultimately show ?thesis 
      using par_not_par par_symmetry by blast
  qed
  have "Col C D D'" 
    by (simp add: \<open>C D Par C D'\<close> par_id)
  have "Cong C D C D'" 
    by (meson \<open>Cong C D' A B\<close> assms(2) cong_transitivity not_cong_3412)
  have "D = D' \<or> C Midpoint D D'" 
    using \<open>Col C D D'\<close> \<open>Cong C D C D'\<close> l7_20 not_col_permutation_4 by blast
  {
    assume "D = D'"
    hence "B C Par D A \<and> Cong B C D A \<and> A C TS B D" 
      using \<open>B C Par D' A\<close> \<open>Cong B C D' A\<close> assms(1) assms(3) 
        par_two_sides_two_sides by blast
  }
  moreover
  {
    assume "C Midpoint D D'"
    have "A C TS B D" 
      by (simp add: assms(1) assms(3) par_two_sides_two_sides)
    hence "\<not> Col A C D" 
      using TS_def not_col_permutation_1 by blast
    hence "\<not> Col A C D'" 
      by (metis \<open>C D Par C D'\<close> not_col_distincts par_col2_par_bis par_id_5)
    have "A C TS B D'" 
      by (meson Tarski_Euclidean_axioms Tarski_Euclidean_def mid_two_sides 
          \<open>P Midpoint A C\<close> \<open>P Midpoint B D'\<close> \<open>\<not> Col A B C\<close> col_permutation_5)
    hence "A C TS D D'"
      using TS_def \<open>A C TS B D\<close> \<open>C Midpoint D D'\<close> col_trivial_3 midpoint_bet by blast
    have "A C TS B D" 
      by (simp add: \<open>A C TS B D\<close>)
    moreover
    have "A C OS B D" 
      using \<open>A C TS B D'\<close> \<open>A C TS D D'\<close> l9_8_1 by auto
    ultimately
    have False 
      using l9_9 by blast
  }
  ultimately
  show ?thesis 
    using \<open>D = D' \<or> C Midpoint D D'\<close> by fastforce
qed

lemma l12_20:
  assumes "A B Par C D" and 
    "Cong A B C D" and 
    "A C TS B D" 
  shows "B C Par D A \<and> Cong B C D A \<and> A C TS B D" 
proof -
  have "B D TS A C" 
    by (simp add: assms(1) assms(3) par_comm par_two_sides_two_sides)
  thus ?thesis 
    using assms(1) assms(2) l12_20_bis by blast
qed

lemma l12_21_a:
  assumes "A C TS B D" and
    "A B Par C D"
  shows "B A C CongA D C A" 
  using TarskiPP alternate_interior_angles_postulate_def assms(1) assms(2) 
    playfair__alternate_interior tarski_s_euclid_implies_playfair_s_postulate by blast

lemma l12_21:
  assumes "A C TS B D"  
  shows "B A C CongA D C A \<longleftrightarrow> A B Par C D" 
  using assms l12_21_a l12_21_b by blast

lemma l12_22_a:
  assumes "P Out A C" and
    "P A OS B D" and
    "A B Par C D"  
  shows "B A P CongA D C P" 
proof -
  {
    assume H1: "\<forall> A B C D P. (A \<noteq> P \<and> Bet P A C \<and> P A OS B D \<and> A B Par C D) 
                         \<longrightarrow> B A P CongA D C P"
    {
      fix A9 B9 C9 D9 P9
      assume "P9 Out A9 C9" and "P9 A9 OS B9 D9" and "A9 B9 Par C9 D9"
      have "A9 \<noteq> P9 \<and> C9 \<noteq> P9 \<and> (Bet P9 A9 C9 \<or> Bet P9 C9 A9)" 
        using Out_def \<open>P9 Out A9 C9\<close> by force
      have "Bet P9 A9 C9 \<longrightarrow> B9 A9 P9 CongA D9 C9 P9" 
        using \<open>A9 B9 Par C9 D9\<close> \<open>A9 \<noteq> P9 \<and> C9 \<noteq> P9 \<and> (Bet P9 A9 C9 \<or> Bet P9 C9 A9)\<close> 
          \<open>P9 A9 OS B9 D9\<close> 
          \<open>\<forall>A B C D P. A \<noteq> P \<and> Bet P A C \<and> P A OS B D \<and> A B Par C D \<longrightarrow> B A P CongA D C P\<close> 
        by presburger
      moreover
      {
        assume "Bet P9 C9 A9" 
        have "C9 \<noteq> P9" 
          by (simp add: \<open>A9 \<noteq> P9 \<and> C9 \<noteq> P9 \<and> (Bet P9 A9 C9 \<or> Bet P9 C9 A9)\<close>)
        moreover
        have "Bet P9 C9 A9" 
          by (simp add: \<open>Bet P9 C9 A9\<close>)
        moreover
        have "P9 C9 OS D9 B9" 
          using \<open>A9 \<noteq> P9 \<and> C9 \<noteq> P9 \<and> (Bet P9 A9 C9 \<or> Bet P9 C9 A9)\<close> 
            \<open>P9 A9 OS B9 D9\<close> \<open>P9 Out A9 C9\<close> col_one_side one_side_symmetry 
            out_col by blast
        moreover
        have "C9 D9 Par A9 B9" 
          using \<open>A9 B9 Par C9 D9\<close> par_symmetry by blast
        ultimately
        have "B9 A9 P9 CongA D9 C9 P9" 
          by (simp add: H1 conga_sym)
      }
      ultimately
      have "B9 A9 P9 CongA D9 C9 P9" 
        using \<open>A9 \<noteq> P9 \<and> C9 \<noteq> P9 \<and> (Bet P9 A9 C9 \<or> Bet P9 C9 A9)\<close> by blast
    }
    hence "\<forall> A B C D P. (P Out A C \<and> P A OS B D \<and> A B Par C D) \<longrightarrow> B A P CongA D C P" 
      by blast
  }
  moreover
  {
    fix A B C D P
    assume "A \<noteq> P" and "Bet P A C" and "P A OS B D" and "A B Par C D" 
    have  "B A P CongA D C P" 
    proof (cases "A = C")
      case True
      have "A Out D B" 
        by (metis True \<open>A B Par C D\<close> \<open>P A OS B D\<close> bet_col1 l6_6 l9_19 
            par_id_2 point_construction_different)
      moreover
      have "A Out P P" 
        using \<open>A \<noteq> P\<close> out_trivial by presburger
      ultimately
      show ?thesis 
        by (simp add: True out2__conga)
    next
      case False
      obtain B' where "Bet B A B'" and "Cong A B' B A" 
        using segment_construction by blast
      have "B A P CongA D C P" 
      proof -
        have "B A P CongA B' A C" 
        proof -
          have "B \<noteq> A" 
            using \<open>P A OS B D\<close> os_distincts by blast
          moreover
          have "A \<noteq> P" 
            by (simp add: \<open>A \<noteq> P\<close>)
          moreover
          have "B' \<noteq> A" 
            using \<open>Cong A B' B A\<close> calculation(1) cong_diff_3 by blast
          moreover
          have "A \<noteq> C" 
            by (simp add: False)
          ultimately
          show ?thesis 
            using \<open>Bet B A B'\<close> \<open>Bet P A C\<close> l11_14 by simp
        qed
        moreover
        have "B' A C CongA D C P" 
        proof -
          have "B' A C CongA D C A" 
          proof -
            have "A C TS B' D" 
            proof -
              have "A C TS B B'" 
                by (metis False \<open>Bet B A B'\<close> \<open>Bet P A C\<close> \<open>Cong A B' B A\<close> 
                    \<open>P A OS B D\<close> bet__ts bet_col bet_col1 col123__nos colx cong_diff_4)
              moreover
              have "A C OS B D" 
                by (meson False \<open>Bet P A C\<close> \<open>P A OS B D\<close> bet_col bet_col1 col2_os__os)
              ultimately
              show ?thesis 
                using l9_2 l9_8_2 by blast
            qed
            moreover
            have "A B' Par C D" 
            proof -
              have "C D Par A B" 
                by (simp add: \<open>A B Par C D\<close> par_symmetry)
              moreover have "C D Par A B'" 
                by (metis CongA_def NCol_cases \<open>B A P CongA B' A C\<close> \<open>Bet B A B'\<close> 
                    bet_col calculation par_col_par)
              ultimately show ?thesis 
                using Par_cases by blast
            qed
            ultimately
            show ?thesis 
              by (simp add: l12_21)
          qed
          moreover
          have "A Out B' B'" 
            by (metis \<open>Cong A B' B A\<close> \<open>P A OS B D\<close> cong_reverse_identity 
                os_distincts out_trivial)
          moreover
          have "A Out C C" 
            using False out_trivial by auto
          moreover
          have "C Out D D" 
            by (metis \<open>A B Par C D\<close> out_trivial par_distinct)
          moreover
          have "C Out P A" 
            by (simp add: False \<open>Bet P A C\<close> bet_out_1 l6_6)
          ultimately
          show ?thesis 
            using l11_10 by blast
        qed
        ultimately
        show ?thesis 
          by (meson not_conga)
      qed
      thus ?thesis
        by blast
    qed
  }
  ultimately show ?thesis 
    using assms(1) assms(2) assms(3) by blast
qed

lemma l12_22:
  assumes "P Out A C" and
    "P A OS B D" 
  shows "B A P CongA D C P \<longleftrightarrow> A B Par C D" 
  using assms(1) assms(2) l12_22_a l12_22_b by blast

lemma l12_23:
  assumes "\<not> Col A B C"
  shows "\<exists> B' C'. A C TS B B' \<and> A B TS C C' \<and> Bet B' A C' \<and> 
                  A B C CongA B A C' \<and> A C B CongA C A B'"
proof -
  obtain B0 where "B0 Midpoint A B" 
    using midpoint_existence by blast
  obtain C0 where "C0 Midpoint A C" 
    using midpoint_existence by blast
  obtain B' where "Bet B C0 B'" and "Cong C0 B' B C0" 
    using segment_construction by blast
  obtain C' where "Bet C B0 C'" and "Cong B0 C' C B0" 
    using segment_construction by blast
  have "A C TS B B'" 
    by (meson \<open>Bet B C0 B'\<close> \<open>C0 Midpoint A C\<close> \<open>Cong C0 B' B C0\<close> assms 
        cong_symmetry mid_two_sides midpoint_def not_col_permutation_5)
  moreover
  have "A B TS C C'" 
    by (meson Cong_cases \<open>B0 Midpoint A B\<close> \<open>Bet C B0 C'\<close> \<open>Cong B0 C' C B0\<close> 
        assms mid_two_sides midpoint_def)
  moreover 
  have "A B' Par C B" 
    by (metis \<open>Bet B C0 B'\<close> \<open>C0 Midpoint A C\<close> \<open>Cong C0 B' B C0\<close> calculation(1) 
        cong_symmetry mid_par_cong2 midpoint_def ts_distincts)
  have "A C' Par B C" 
    by (metis \<open>B0 Midpoint A B\<close> \<open>Bet C B0 C'\<close> \<open>Cong B0 C' C B0\<close> calculation(2) 
        mid_par_cong2 midpoint_def not_cong_3412 ts_distincts)
  have "A B' Par A C'" 
    using Par_perm \<open>A B' Par C B\<close> \<open>A C' Par B C\<close> par_not_par by blast
  hence "Col A B' C'" 
    by (simp add: par_id)
  have "A C OS B0 C'" 
  proof -
    {
      assume "Col A C B0"
      have "Col A B C" 
      proof -
        have "A \<noteq> B0" 
          using \<open>B0 Midpoint A B\<close> assms col_trivial_1 is_midpoint_id by blast
        moreover have "Col A B0 B" 
          using Col_cases \<open>B0 Midpoint A B\<close> midpoint_col by blast
        moreover have "Col A B0 C" 
          using \<open>Col A C B0\<close> not_col_permutation_5 by blast
        ultimately show ?thesis 
          using col_transitivity_1 by blast
      qed
      hence False 
        using assms by blast
    }
    hence "\<not> Col A C B0" 
      by blast
    moreover
    have "Col A C C" 
      using not_col_distincts by blast
    moreover
    have "C Out B0 C'" 
      by (metis \<open>Bet C B0 C'\<close> bet_out calculation(1) col_trivial_2)
    ultimately
    show ?thesis 
      using l9_19_R2 by blast
  qed
  have "A C OS B0 B" 
    by (metis \<open>A C OS B0 C'\<close> \<open>B0 Midpoint A B\<close> calculation(1) col123__nos 
        midpoint_out out_one_side ts_distincts)
  have "A C OS B C'" 
    by (metis Mid_cases \<open>B0 Midpoint A B\<close> \<open>Bet C B0 C'\<close> \<open>Cong B0 C' C B0\<close> 
        assms calculation(2) mid_par_cong2 midpoint_def not_col_distincts not_cong_3412 
        par_two_sides_two_sides ts_ts_os)
  have "A C TS B' C'" 
    using \<open>A C OS B C'\<close> calculation(1) l9_2 l9_8_2 by blast
  hence "Bet B' A C'" 
    using \<open>Col A B' C'\<close> col_two_sides_bet by blast
  moreover 
  have "A B C CongA B A C'" 
    by (meson \<open>A C' Par B C\<close> calculation(2) conga_comm invert_two_sides l12_21_a par_symmetry)
  moreover 
  have "A C B CongA C A B'" 
    by (meson \<open>A B' Par C B\<close> calculation(1) conga_comm invert_two_sides l12_21_a par_symmetry)
  ultimately
  show ?thesis 
    by blast
qed

lemma cop2_npar__inter:
  assumes "Coplanar A B X Y" and
    "Coplanar A' B' X Y" and
    "\<not> A B Par A' B'" 
  shows "\<exists> P. Col P X Y \<and> (Col P A B \<or> Col P A' B')" 
proof (cases "A B Par X Y")
  case True
  thus ?thesis 
    by (metis Par_cases par_not_par assms(2) assms(3) cop_npar__inter_exists)
next
  case False
  thus ?thesis 
    using assms(1) cop_npar__inter_exists by blast
qed

lemma not_par_one_not_par:
  assumes "\<not> A B Par A' B'" 
  shows "\<not> A B Par X Y \<or> \<not> A' B' Par X Y" 
  using Par_cases assms par_trans by blast

lemma col_par_par_col:
  assumes "Col A B C" and
    "A B Par A' B'" and
    "B C Par B' C'" 
  shows "Col A' B' C'" 
  by (metis Par_cases par_not_par assms(1) assms(2) assms(3) col_par par_id_5 par_neq2)

lemma cop_par_perp__perp:
  assumes "A B Par C D" and
    "A B Perp P Q" and
    "Coplanar C D P Q"
  shows "C D Perp P Q" 
proof -
  have "universal_posidonius_postulate" 
    by (simp add: TarskiPP playfair__universal_posidonius_postulate 
        tarski_s_euclid_implies_playfair_s_postulate)
  thus ?thesis 
    using assms(1) assms(2) assms(3) perpendicular_transversal_postulate_def 
      universal_posidonius_postulate__perpendicular_transversal_postulate by blast
qed

lemma cop4_par_perp2__par:
  assumes "A B Par C D" and
    "A B Perp E F" and
    "C D Perp G H" and
    "Coplanar A B E G" and 
    "Coplanar A B E H" and
    "Coplanar A B F G" and 
    "Coplanar A B F H"
  shows "E F Par G H" 
proof -
  have "perpendicular_transversal_postulate" 
    using TarskiPP playfair__universal_posidonius_postulate 
      tarski_s_euclid_implies_playfair_s_postulate 
      universal_posidonius_postulate__perpendicular_transversal_postulate by blast
  thus ?thesis 
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
      assms(7) par_perp_perp_implies_par_perp_2_par 
      postulate_of_parallelism_of_perpendicular_transversals_def by blast
qed

lemma par_cong_mid_ts:
  assumes "A B ParStrict A' B'" and
    "Cong A B A' B'" and
    "A A' TS B B'"
  shows "\<exists> M.  M Midpoint A A' \<and> M Midpoint B B'" 
proof -
  have "\<not> Col B A A'" 
    by (meson assms(1) col_permutation_4 par_strict_not_col_1)
  obtain M where "Col M A A'" and "Bet B M B'" 
    using TS_def assms(3) by blast
  have "Bet A M A'" 
    by (metis NCol_perm \<open>Bet B M B'\<close> \<open>Col M A A'\<close> assms(1) assms(3) 
        bet_col l9_18 l9_9_bis par_one_or_two_sides)
  moreover
  have "M Midpoint A A'" 
    by (metis l7_21 \<open>Bet B M B'\<close> \<open>\<not> Col B A A'\<close> assms(1) assms(2) assms(3) 
        bet_col calculation l12_20 not_col_permutation_4 par_strict_par ts_distincts)
  moreover
  have "M Midpoint B B'" 
    by (metis l7_21 \<open>Bet B M B'\<close> \<open>\<not> Col B A A'\<close> assms(1) assms(2) assms(3) 
        bet_col calculation(1) l12_20 not_col_permutation_4 par_strict_par ts_distincts)
  ultimately
  show ?thesis by blast
qed

lemma par_cong_mid_os:
  assumes "A B ParStrict A' B'" and
    "Cong A B A' B'" and
    "A A' OS B B'" 
  shows "\<exists> M. M Midpoint A B' \<and> M Midpoint B A'" 
proof -
  obtain X where "X Midpoint A' B" 
    using MidR_uniq_aux by blast
  obtain B'' where "Bet A X B''" and "Cong X B'' A X" 
    using segment_construction by blast
  have "X Midpoint A B''" 
    using Cong_cases Midpoint_def \<open>Bet A X B''\<close> \<open>Cong X B'' A X\<close> by blast
  have "\<not> Col A B A'" 
    using assms(1) par_strict_not_col_1 by auto
  hence "A B ParStrict B'' A'" 
    by (meson Mid_perm \<open>X Midpoint A B''\<close> \<open>X Midpoint A' B\<close> midpoint_par_strict)
  have "Col B'' B' A' \<and> Col A' B' A'" 
  proof -
    have "B A Par B' A'" 
      using assms(1) par_comm par_strict_par by blast
    moreover
    have "Col A' B' A'" 
      by (simp add: col_trivial_3)
    moreover
    have "B A Par B'' A'" 
      by (simp add: \<open>A B ParStrict B'' A'\<close> par_strict_left_comm par_strict_par)
    moreover
    have "Col A' B'' A'" 
      by (simp add: col_trivial_3)
    ultimately
    show ?thesis 
      using parallel_uniqueness by blast
  qed
  have "Cong A B B'' A'" 
    using \<open>X Midpoint A' B\<close> \<open>X Midpoint A B''\<close> Mid_cases l7_13 by blast
  have "Cong A' B' A' B''" 
    by (meson \<open>Cong A B B'' A'\<close> assms(2) cong_inner_transitivity not_cong_1243)
  have "B' = B'' \<or> A' Midpoint B' B''" 
    by (meson NCol_perm \<open>Col B'' B' A' \<and> Col A' B' A'\<close> \<open>Cong A' B' A' B''\<close> l7_20_bis)
  have "B' = B'' \<longrightarrow> (X Midpoint A B' \<and> X Midpoint B A')" 
    using Mid_cases \<open>X Midpoint A B''\<close> \<open>X Midpoint A' B\<close> by blast
  moreover
  {
    assume "A' Midpoint B' B''"
    have "A A' OS X B''" 
    proof -
      have "\<not> Col A A' X" 
        by (metis (full_types) \<open>X Midpoint A B''\<close> \<open>X Midpoint A' B\<close> 
            \<open>\<not> Col A B A'\<close> col2__eq col_permutation_1 midpoint_col 
            midpoint_midpoint_col)
      moreover
      have "Col A A' A" 
        by (simp add: col_trivial_3)
      moreover
      have "A Out X B''" 
        using \<open>Bet A X B''\<close> \<open>X Midpoint A B''\<close> bet_neq12__neq calculation(1) 
          midpoint_out not_col_distincts by presburger
      ultimately
      show ?thesis 
        by (meson l9_19_R2)
    qed
    have "\<not> Col B'' A A'" 
      using \<open>A A' OS X B''\<close> col_permutation_1 one_side_not_col124 by blast
    hence "A A' TS B' B''" 
      by (metis Midpoint_def not_col_distincts \<open>A' Midpoint B' B''\<close> 
          \<open>Col B'' B' A' \<and> Col A' B' A'\<close> assms(3) col_permutation_1 
          col_permutation_3 cop_nts__os ncop__ncols one_side_chara 
          one_side_not_col124)
    hence "A A' TS X B'" 
      using l9_2 l9_8_2 one_side_symmetry by (meson \<open>A A' OS X B''\<close>)
    moreover
    have "A A' OS X B" 
      by (metis midpoint_out not_col_distincts \<open>X Midpoint A' B\<close> 
          \<open>\<not> Col A B A'\<close> col_permutation_1 invert_one_side out_one_side)
    hence "A A' OS X B'" 
      by (meson  assms(3) one_side_transitivity)
    ultimately
    have False
      using  l9_9 by auto
  }
  ultimately
  show ?thesis 
    using \<open>B' = B'' \<or> A' Midpoint B' B''\<close> by blast
qed

lemma par_strict_cong_mid:
  assumes "A B ParStrict A' B'" and
    "Cong A B A' B'" 
  shows "\<exists> M. (M Midpoint A A' \<and> M Midpoint B B') \<or> (M Midpoint A B' \<and> M Midpoint B A')" 
proof -
  obtain M1 where "M1 Midpoint A A'" 
    using MidR_uniq_aux by blast
  obtain B'' where "M1 Midpoint B B''" 
    using symmetric_point_construction by blast
  have "Col B'' A' B'" 
    by (metis not_col_distincts \<open>M1 Midpoint A A'\<close> \<open>M1 Midpoint B B''\<close> 
        assms(1) col_par_par_col mid_par_cong1 par_strict_not_col_1 par_strict_par)
  have "Cong A' B' A' B''" 
    by (meson \<open>M1 Midpoint A A'\<close> \<open>M1 Midpoint B B''\<close> assms(2) 
        cong_transitivity l7_13 not_cong_3412)
  obtain M2 where "M2 Midpoint A B'" 
    using MidR_uniq_aux by blast
  obtain A'' where "M2 Midpoint B A''" 
    using symmetric_point_construction by blast
  have "A B Par B' A''" 
    using \<open>M2 Midpoint A B'\<close> \<open>M2 Midpoint B A''\<close> assms(1) par_strict_neq1 sym_par by blast
  hence "Col A'' A' B'" 
    by (meson assms(1) par_id_2 par_right_comm par_strict_par par_symmetry par_trans)
  have "Cong A' B' B' A''" 
    by (metis l7_13 \<open>M2 Midpoint A B'\<close> \<open>M2 Midpoint B A''\<close> assms(2) 
        cong_transitivity not_cong_4312)
  {
    assume "B' = B''"
    hence "\<exists> M. (M Midpoint A A' \<and> M Midpoint B B') \<or> (M Midpoint A B' \<and> M Midpoint B A')" 
      using \<open>M1 Midpoint A A'\<close> \<open>M1 Midpoint B B''\<close> by blast 
  }
  moreover
  {
    assume "A' Midpoint B' B''"
    have "\<exists> M. (M Midpoint A A' \<and> M Midpoint B B') \<or> (M Midpoint A B' \<and> M Midpoint B A')" 
      by (meson par_one_or_two_sides assms(1) assms(2) par_cong_mid_os par_cong_mid_ts)
  }
  ultimately
  show ?thesis 
    using l7_20 \<open>Col B'' A' B'\<close> \<open>Cong A' B' A' B''\<close> not_col_permutation_3 by blast
qed

lemma par_strict_cong_mid1:
  assumes "A B ParStrict A' B'" and
    "Cong A B A' B'" 
  shows "(A A' TS B B' \<and> (\<exists> M. M Midpoint A A' \<and> M Midpoint B B')) \<or> 
  (A A' OS B B' \<and> (\<exists> M. M Midpoint A B' \<and> M Midpoint B A'))" 
  by (metis par_one_or_two_sides assms(1) assms(2) par_cong_mid_os par_cong_mid_ts)

lemma par_cong_mid:
  assumes "A B Par A' B'" and
    "Cong A B A' B'"
  shows "\<exists> M. (M Midpoint A A' \<and> M Midpoint B B') \<or>
             (M Midpoint A B' \<and> M Midpoint B A')" 
proof -
  {
    assume "A B ParStrict A' B'"
    hence "\<exists> M. (M Midpoint A A' \<and> M Midpoint B B') \<or> (M Midpoint A B' \<and> M Midpoint B A')" 
      by (simp add: assms(2) par_strict_cong_mid)
  }
  moreover
  {
    assume "A \<noteq> B \<and> A' \<noteq> B' \<and> Col A A' B' \<and> Col B A' B'"
    hence "\<exists> M. (M Midpoint A A' \<and> M Midpoint B B') \<or> (M Midpoint A B' \<and> M Midpoint B A')" 
      using assms(1) assms(2) calculation col_cong_mid by blast
  }
  ultimately
  show ?thesis 
    using Par_def assms(1) by presburger
qed

lemma ts_cong_par_cong_par:
  assumes "A A' TS B B'" and
    "Cong A B A' B'" and
    "A B Par A' B'" 
  shows "Cong A B' A' B \<and> A B' Par A' B" 
  by (metis Cong_cases Par_cases assms(1) assms(2) assms(3) l12_20)

lemma plgs_cong:
  assumes "ParallelogramStrict A B C D"
  shows "Cong A B C D \<and> Cong A D B C" 
proof -
  have "A C TS B D \<and> A B Par C D \<and> Cong A B C D" 
    using ParallelogramStrict_def assms by presburger
  thus ?thesis 
    by (meson l12_20 not_cong_3421)
qed

lemma plg_cong:
  assumes "Parallelogram A B C D"
  shows "Cong A B C D \<and> Cong A D B C" 
proof -
  {
    assume "ParallelogramStrict A B C D"
    hence "Cong A B C D \<and> Cong A D B C" 
      using plgs_cong by blast
  }
  moreover
  {
    assume "ParallelogramFlat A B C D"
    hence "Cong A B C D \<and> Cong A D B C" 
      using plgf_cong by blast
  }
  ultimately
  show ?thesis 
    using Parallelogram_def assms by blast
qed

lemma rmb_cong:
  assumes "Rhombus A B C D"
  shows "Cong A B B C \<and> Cong A B C D \<and> Cong A B D A" 
proof -
  have "Parallelogram A B C D" 
    by (simp add: Rhombus_Plg assms plg_to_parallelogram)
  hence "Cong A B C D \<and> Cong A D B C" 
    using plg_cong by blast
  thus ?thesis 
    by (meson Rhombus_def assms cong_inner_transitivity 
        cong_right_commutativity cong_symmetry)
qed

lemma rmb_per:
  assumes "M Midpoint A C" and 
    "Rhombus A B C D" 
  shows "Per A M D" 
proof -
  obtain M' where "M' Midpoint A C \<and> M' Midpoint B D" 
    using Plg_def Rhombus_Plg assms(2) by presburger
  hence "M = M'" 
    using assms(1) l7_17 by blast
  show ?thesis 
    using Per_def \<open>M = M'\<close> \<open>M' Midpoint A C \<and> M' Midpoint B D\<close> assms(2) 
      l7_2 not_cong_3421 rmb_cong by blast
qed

lemma per_rmb:
  assumes "Plg A B C D" and
    "M Midpoint A C" and
    "Per A M B"
  shows "Rhombus A B C D" 
  by (meson Per_cases Rhombus_def assms(1) assms(2) assms(3) not_cong_2134 per_double_cong)

lemma perp_rmb:
  assumes "Plg A B C D" and
    "A C Perp B D" 
  shows "Rhombus A B C D" 
proof -
  obtain M where "M Midpoint A C" 
    using MidR_uniq_aux by blast
  obtain M' where "M' Midpoint A C \<and> M' Midpoint B D" 
    using Plg_def assms(1) by presburger
  hence "M = M'" 
    using \<open>M Midpoint A C\<close> l7_17 by blast
  have "A M Perp B M" 
  proof -
    have "A \<noteq> M" 
      using \<open>M = M'\<close> \<open>M' Midpoint A C \<and> M' Midpoint B D\<close> assms(2) 
        is_midpoint_id perp_not_eq_1 by blast
    moreover have "A C Perp B M" 
      by (metis Bet_cases Col_def \<open>M = M'\<close> \<open>M' Midpoint A C \<and> M' Midpoint B D\<close> 
          assms(2) midpoint_bet midpoint_distinct_3 perp_col1)
    moreover have "Col A C M" 
      using Col_cases \<open>M Midpoint A C\<close> midpoint_col by blast
    ultimately show ?thesis 
      using perp_col by blast
  qed
  hence "M PerpAt A M M B" 
    using Perp_cases Perp_in_cases perp_perp_in by blast
  hence "Per A M B" 
    by (simp add: perp_in_per)
  thus ?thesis 
    using \<open>M Midpoint A C\<close> assms(1) per_rmb by blast
qed

lemma plg_conga1:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "Plg A B C D" 
  shows "B A C CongA D C A" 
proof -
  have "Parallelogram A B C D" 
    by (simp add: assms(3) plg_to_parallelogram)
  moreover have "ParallelogramStrict A B C D \<longrightarrow> B A C CongA D C A" 
    by (metis Cong_cases Tarski_neutral_dimensionless.plgs_diff 
        Tarski_neutral_dimensionless_axioms \<open>Parallelogram A B C D\<close> 
        cong_pseudo_reflexivity l11_51 plg_cong)
  moreover have "ParallelogramFlat A B C D \<longrightarrow> B A C CongA D C A" 
    by (metis Tarski_neutral_dimensionless.cong_3421 Tarski_neutral_dimensionless_axioms
        \<open>Parallelogram A B C D\<close> assms(1) assms(2) cong_diff_2 cong_pseudo_reflexivity 
        conga_trivial_1 l11_51 plg_cong)
  ultimately show ?thesis 
    using Parallelogram_def by blast
qed

lemma os_cong_par_cong_par:
  assumes "A A' OS B B'" and 
    "Cong A B A' B'" and
    "A B Par A' B'"
  shows "Cong A A' B B' \<and> A A' Par B B'" 
  by (metis (full_types) Par_cases Par_def not_col_distincts assms(1) 
      assms(2) assms(3) cong_right_commutativity mid_par_cong2 
      one_side_not_col124 par_cong_mid_os)

lemma plgs_permut:
  assumes "ParallelogramStrict A B C D"
  shows "ParallelogramStrict B C D A" 
  by (meson Mid_perm ParallelogramStrict_def assms mid_plgs par_cong_mid_ts
      parallelogram_strict_not_col_2 plgs__pars)

lemma plg_permut:
  assumes "Parallelogram A B C D"
  shows "Parallelogram B C D A" 
proof -
  have "ParallelogramStrict A B C D \<longrightarrow> Parallelogram B C D A" 
    using Parallelogram_def plgs_permut by blast
  thus ?thesis 
    using Parallelogram_def assms plgf_permut by blast
qed

lemma plgs_mid:
  assumes "ParallelogramStrict A B C D"
  shows "\<exists> M. M Midpoint A C \<and> M Midpoint B D" 
  using ParallelogramStrict_def assms par_cong_mid_ts plgs__pars by blast

lemma plg_mid:
  assumes "Parallelogram A B C D"
  shows "\<exists> M. M Midpoint A C \<and> M Midpoint B D" 
proof -
  have "ParallelogramStrict A B C D \<longrightarrow> (\<exists> M. M Midpoint A C \<and> M Midpoint B D)" 
    using plgs_mid by blast
  thus ?thesis 
    using plgf_mid Parallelogram_def assms by blast
qed

lemma plg_mid_2:
  assumes "Parallelogram A B C D" and
    "I Midpoint A C" 
  shows "I Midpoint B D" 
  using MidR_uniq_aux assms(1) assms(2) plg_mid by fastforce

lemma plgs_not_comm_1:
  assumes "ParallelogramStrict A B C D"
  shows "\<not> ParallelogramStrict A B D C" 
  by (meson ParallelogramStrict_def l9_9_bis assms plgs_one_side plgs_permut)

lemma plgs_not_comm_2:
  assumes "ParallelogramStrict A B C D"
  shows "\<not> ParallelogramStrict B A C D" 
  by (meson assms plgs_not_comm_1 plgs_sym)

lemma plgs_not_comm:
  assumes "ParallelogramStrict A B C D"
  shows "\<not> ParallelogramStrict A B D C \<and> \<not> ParallelogramStrict B A C D" 
  using assms plgs_not_comm_1 plgs_not_comm_2 by blast

lemma plg_not_comm_R1:
  assumes "A \<noteq> B" and
    "Parallelogram A B C D"
  shows "\<not> Parallelogram A B D C" 
proof -
  {
    assume "ParallelogramStrict A B C D"
    {
      assume "ParallelogramStrict A B D C" 
      have False 
        using plgs_not_comm_1 
        by (meson \<open>ParallelogramStrict A B C D\<close> \<open>ParallelogramStrict A B D C\<close>)
    }
    moreover
    {
      assume "ParallelogramFlat A B D C" 
      have "C D Par A B" 
        using Par_cases ParallelogramStrict_def \<open>ParallelogramStrict A B C D\<close> by blast
      moreover
      have "C D ParStrict A B \<Longrightarrow> False" 
        by (meson \<open>ParallelogramFlat A B D C\<close> \<open>ParallelogramStrict A B C D\<close> 
            \<open>ParallelogramStrict A B D C \<Longrightarrow> False\<close> mid_plgs parallelogram_strict_not_col_4 
            plgf_mid)
      moreover
      have "C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B \<Longrightarrow> False" 
        using \<open>ParallelogramStrict A B C D\<close> calculation(2) plgs__pars plgs_sym by blast
      ultimately
      have False 
        using Par_def by blast
    }
    ultimately
    have "\<not> Parallelogram A B D C"
      using Parallelogram_def by blast
  }
  moreover
  {
    assume "ParallelogramFlat A B C D"
    hence "\<not> ParallelogramFlat A B D C \<and> \<not> ParallelogramFlat B A C D"
      using plgf_not_comm assms(1) by blast
    hence "\<not> ParallelogramFlat A B D C"
      by blast
    moreover
    have "\<not> ParallelogramFlat B A C D"
      by (simp add: \<open>\<not> ParallelogramFlat A B D C \<and> \<not> ParallelogramFlat B A C D\<close>)
    {
      assume "ParallelogramStrict A B D C" 
      have "A D TS B C" 
        using ParallelogramStrict_def \<open>ParallelogramStrict A B D C\<close> by auto
      hence False 
        by (meson TS_def \<open>ParallelogramFlat A B C D\<close> \<open>ParallelogramStrict A B D C\<close> 
            mid_plgs plgf_mid plgs_not_comm)
    }
    ultimately
    have "\<not> Parallelogram A B D C"
      using Parallelogram_def by blast
  }
  ultimately
  show ?thesis 
    using Parallelogram_def assms(2) by blast
qed

lemma plg_not_comm_R2:
  assumes "A \<noteq> B" and
    "Parallelogram A B C D"
  shows "\<not> Parallelogram B A C D" 
  by (metis assms(1) assms(2) plg_not_comm_R1 plg_sym)

lemma plg_not_comm:
  assumes "A \<noteq> B" and
    "Parallelogram A B C D"
  shows "\<not> Parallelogram A B D C \<and> \<not> Parallelogram B A C D" 
  by (simp add: assms(1) assms(2) plg_not_comm_R1 plg_not_comm_R2)

lemma parallelogram_to_plg:
  assumes "Parallelogram A B C D"
  shows "Plg A B C D" 
  using Plg_def assms plg_irreflexive plg_mid by force

lemma parallelogram_equiv_plg:
  shows "Parallelogram A B C D \<longleftrightarrow> Plg A B C D" 
  using parallelogram_to_plg plg_to_parallelogram by blast

lemma plg_conga:
  assumes "A \<noteq> B" and
    (*"A \<noteq> C" and*)
    "B \<noteq> C" and
    "Parallelogram A B C D" 
  shows "A B C CongA C D A \<and> B C D CongA D A B" 
proof 
  show "A B C CongA C D A" 
    by (metis assms(1) assms(2) assms(3) cong_pseudo_reflexivity 
        conga_trivial_1 l11_51 plg_cong plg_not_comm_R2 plg_permut) 
  show "B C D CongA D A B" 
    by (metis Cong_cases Tarski_neutral_dimensionless.conga_distinct 
        Tarski_neutral_dimensionless_axioms \<open>A B C CongA C D A\<close> assms(3) 
        cong_pseudo_reflexivity conga_trivial_1 l11_51 plg_cong)
qed
  
lemma half_plgs_R1:
  assumes "ParallelogramStrict A B C D" and
    "P Midpoint A B" and
    "Q Midpoint C D" and
    "M Midpoint A C"
  shows "P Q Par A D \<and> Cong A D P Q"
proof -
  obtain M' where "M' Midpoint A C" and "M' Midpoint B D" 
    using assms(1) plgs_mid by blast
  have "M = M'" 
    using MidR_uniq_aux \<open>M' Midpoint A C\<close> assms(4) by blast
  obtain Q' where "Bet P M Q'" and "Cong M Q' P M" 
    using segment_construction by blast
  have "M Midpoint P Q'" 
    using Cong_perm \<open>Bet P M Q'\<close> \<open>Cong M Q' P M\<close> midpoint_def by blast
  hence "Q' Midpoint C D" 
    using \<open>M = M'\<close> \<open>M' Midpoint A C\<close> \<open>M' Midpoint B D\<close> assms(2) 
      symmetry_preserves_midpoint by blast
  have "Q = Q'" 
    using \<open>Q' Midpoint C D\<close> assms(3) l7_17 by auto
  have "A B Par C D" 
    using ParallelogramStrict_def assms(1) by force
  have "Cong A B C D" 
    using assms(1) plgs_cong by force
  hence "Cong A P D Q" 
    by (metis \<open>Q = Q'\<close> \<open>Q' Midpoint C D\<close> assms(2) cong_cong_half_1 l7_2 not_cong_1243)
  have "A P Par Q D" 
  proof -
    have "A \<noteq> P" 
      using \<open>A B Par C D\<close> assms(2) is_midpoint_id par_neq1 by blast
    moreover have "Col A B P" 
      using assms(2) col_permutation_1 midpoint_col by blast
    moreover have "A B Par Q D" 
      by (metis \<open>A B Par C D\<close> \<open>Q = Q'\<close> \<open>Q' Midpoint C D\<close> col_permutation_5 
          col_transitivity_1 midpoint_col midpoint_distinct_1 par_col2_par_bis)
    ultimately show ?thesis 
      using par_col_par_2 by blast
  qed
  have "Cong A D P Q \<and> A D Par P Q" 
  proof -
    have "A D OS P B" 
      by (metis \<open>A B Par C D\<close> assms(1) assms(2) bet_out_1 between_symmetry 
          midpoint_bet midpoint_distinct_1 not_col_permutation_5 one_side_not_col124 
          out_one_side par_neq1 plgs_one_side)
    have "A D OS B C" 
      using assms(1) invert_one_side plgs_one_side plgs_permut by blast
    have "A D OS P Q" 
    proof -
      have "A D OS P B" 
        by (simp add: \<open>A D OS P B\<close>)
      moreover have "A D OS B Q" 
        by (metis Out_cases \<open>A D OS B C\<close> \<open>Q = Q'\<close> \<open>Q' Midpoint C D\<close> 
            bet_out_1 col_trivial_2 midpoint_bet midpoint_distinct_1 
            one_side_symmetry os_out_os)
      ultimately show ?thesis 
        using one_side_transitivity by blast
    qed
    moreover
    have "A D Par Q P" 
      by (simp add: \<open>A P Par Q D\<close> \<open>Cong A P D Q\<close> calculation 
          os_cong_par_cong_par par_right_comm)
    ultimately
    show ?thesis 
      by (simp add: \<open>A P Par Q D\<close> \<open>Cong A P D Q\<close> os_cong_par_cong_par par_right_comm)
  qed
  thus ?thesis 
    by (simp add: par_symmetry)
qed

lemma half_plgs_R2:
  assumes "ParallelogramStrict A B C D" and
    "P Midpoint A B" and
    "Q Midpoint C D" and
    "M Midpoint A C"
  shows "M Midpoint P Q"
proof -
  obtain M' where "M' Midpoint A C" and "M' Midpoint B D" 
    using assms(1) plgs_mid by blast
  have "M = M'" 
    using MidR_uniq_aux \<open>M' Midpoint A C\<close> assms(4) by blast
  obtain Q' where "Bet P M Q'" and "Cong M Q' P M" 
    using segment_construction by blast
  have "M Midpoint P Q'" 
    using Cong_perm \<open>Bet P M Q'\<close> \<open>Cong M Q' P M\<close> midpoint_def by blast
  hence "Q' Midpoint C D" 
    using \<open>M = M'\<close> \<open>M' Midpoint A C\<close> \<open>M' Midpoint B D\<close> assms(2) 
      symmetry_preserves_midpoint by blast
  have "Q = Q'" 
    using \<open>Q' Midpoint C D\<close> assms(3) l7_17 by auto
  thus ?thesis 
    by (simp add: \<open>M Midpoint P Q'\<close> \<open>Q = Q'\<close>)
qed

lemma half_plgs:
  assumes "ParallelogramStrict A B C D" and
    "P Midpoint A B" and
    "Q Midpoint C D" and
    "M Midpoint A C"
  shows "P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q" 
  by (meson half_plgs_R1 Tarski_Euclidean_axioms assms(1) assms(2) assms(3) 
      assms(4) half_plgs_R2)

lemma plgs_two_sides:
  assumes "ParallelogramStrict A B C D" 
  shows "A C TS B D \<and> B D TS A C" 
  using ParallelogramStrict_def assms col_not_plgs l12_19 l12_20 by blast

lemma plgs_par_strict:
  assumes "ParallelogramStrict A B C D" 
  shows "A B ParStrict C D \<and> A D ParStrict B C" 
  using Par_strict_perm assms plgs__pars plgs_permut by blast

lemma plgs_half_plgs_aux:
  assumes "ParallelogramStrict A B C D" and
    "P Midpoint A B" and
    "Q Midpoint C D"
  shows "ParallelogramStrict A P Q D" 
proof -
  obtain M where "M Midpoint A C" and "M Midpoint B D" 
    using assms(1) plgs_mid by blast
  have "P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q" 
    by (meson \<open>M Midpoint A C\<close> assms(1) assms(2) assms(3) half_plgs_R1 half_plgs_R2)
  obtain N where "(N Midpoint P A \<and> N Midpoint Q D) \<or> (N Midpoint P D \<and> N Midpoint Q A)"
    using \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close> not_cong_3412 
      par_cong_mid by blast
  {
    assume "N Midpoint P A" and "N Midpoint Q D"
    have "Col A P B" 
      by (simp add: assms(2) bet_col midpoint_bet)
    have "Col A P N" 
      by (simp add: Col_def \<open>N Midpoint P A\<close> midpoint_bet)
    have "Col N A B" 
      by (metis NCol_cases \<open>Col A P B\<close> \<open>Col A P N\<close> assms(2) col_transitivity_1 
          midpoint_distinct_1)
    moreover
    have "Col N C D" 
      by (meson \<open>N Midpoint Q D\<close> assms(3) bet_col between_exchange2 midpoint_bet 
          not_col_permutation_4)
    ultimately
    have "False" 
      by (meson Midpoint_def \<open>N Midpoint Q D\<close> assms(1) assms(3) between_exchange2 
          one_side_chara plgs_one_side)
    hence "ParallelogramStrict A P Q D" 
      by blast
  }
  moreover
  {
    assume "N Midpoint P D" and "N Midpoint Q A"
    have "A \<noteq> P" 
      by (metis assms(1) assms(2) midpoint_distinct_1 plgs_not_comm_2)
    have "D \<noteq> Q" 
      using \<open>A \<noteq> P\<close> \<open>N Midpoint P D\<close> \<open>N Midpoint Q A\<close> l7_9_bis by blast
    have "\<not> Col A P Q" 
      by (metis one_side_chara assms(1) assms(2) assms(3) col_trivial_2 
          colx midpoint_bet midpoint_col midpoint_distinct_1 
          not_col_permutation_1 plgs_one_side)
    moreover
    have "N Midpoint A Q" 
      using Mid_cases \<open>N Midpoint Q A\<close> by blast
    ultimately
    have "ParallelogramStrict A P Q D" 
      using \<open>N Midpoint P D\<close> mid_plgs by blast
  }
  ultimately
  show ?thesis 
    using \<open>N Midpoint P A \<and> N Midpoint Q D \<or> N Midpoint P D \<and> N Midpoint Q A\<close> by fastforce
qed

lemma plgs_comm2:
  assumes "ParallelogramStrict A B C D"
  shows "ParallelogramStrict B A D C" 
  by (meson ParallelogramStrict_def par_comm assms cong_commutativity l12_20_bis)

lemma plgf_comm2:
  assumes "ParallelogramFlat A B C D"
  shows "ParallelogramFlat B A D C" 
  by (metis Col_cases ParallelogramFlat_def plgf_mid assms mid_plgf_2 mid_plgf_aux)

lemma plg_comm2:
  assumes "Parallelogram A B C D"
  shows "Parallelogram B A D C" 
  by (metis assms mid_plg plg_mid plg_permut)

lemma par_preserves_conga_os:
  assumes "A B Par C D" and
    "Bet A D P" and
    "D \<noteq> P" and
    "A D OS B C"
  shows "B A P CongA C D P"
proof -
  obtain T where "A D TS B T" and "A D TS C T" 
    using OS_def assms(4) by blast
  obtain C' where "Bet C D C'" and "Cong D C' C D" 
    using segment_construction by blast
  have "C' \<noteq> D" 
    using \<open>Cong D C' C D\<close> assms(1) cong_reverse_identity par_neq2 by blast
  have "B A D CongA C' D A" 
  proof -
    have "A D TS B C'" 
      by (metis OS_def \<open>Bet C D C'\<close> \<open>C' \<noteq> D\<close> 
          \<open>\<And>thesis. (\<And>T. \<lbrakk>A D TS B T; A D TS C T\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
          bet__ts col_trivial_3 invert_two_sides l9_18 l9_8_2)
    moreover
    have "A B Par D C'" 
      using \<open>Bet C D C'\<close> assms(1) bet_col bet_col1 calculation par_col2_par 
        ts_distincts by presburger
    ultimately
    show ?thesis 
      using l12_21_a by blast
  qed
  have "A \<noteq> B" 
    using assms(1) par_neq1 by auto
  have "A \<noteq> D" 
    using \<open>A D TS B T\<close> ts_distincts by blast
  have "A Out P D" 
    using \<open>A \<noteq> D\<close> assms(2) bet_out l6_6 by presburger
  hence "B A D CongA B A P" 
    by (metis CongA_def \<open>B A D CongA C' D A\<close> bet2__out out2__conga)
  have "C D P CongA C' D A" 
    by (metis \<open>A \<noteq> D\<close> \<open>Bet C D C'\<close> \<open>C' \<noteq> D\<close> \<open>Cong D C' C D\<close> assms(2) 
        assms(3) between_symmetry cong_diff_2 l11_14)
  hence "B A P CongA P D C" 
    by (metis \<open>B A D CongA B A P\<close> \<open>B A D CongA C' D A\<close> conga_right_comm 
        not_conga not_conga_sym)
  thus ?thesis 
    using conga_right_comm by blast
qed

lemma cong3_par2_par:
  assumes "A \<noteq> C" and
    "B A C Cong3 B' A' C'" and
    "B A Par B' A'" and
    "B C Par B' C'"
  shows "A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'"
proof -
  have "A \<noteq> B" 
    using assms(3) par_neq1 by blast
  have "C \<noteq> B" 
    using assms(4) par_neq1 by blast
  obtain M where "M Midpoint B B'" 
    using MidR_uniq_aux by blast
  obtain A'' where "Bet A M A''" and "Cong M A'' A M" 
    using segment_construction by blast
  obtain C'' where "Bet C M C''" and "Cong M C'' C M" 
    using segment_construction by blast
  have "M Midpoint A A''" 
    by (meson Cong_cases Midpoint_def \<open>Bet A M A''\<close> \<open>Cong M A'' A M\<close>)
  have "M Midpoint C C''" 
    using Cong_cases \<open>Bet C M C''\<close> \<open>Cong M C'' C M\<close> midpoint_def by blast
  have "B A Par B' A''"    
    using \<open>A \<noteq> B\<close> \<open>M Midpoint A A''\<close> \<open>M Midpoint B B'\<close> sym_par by auto
  have "B C Par B' C''" 
    using \<open>C \<noteq> B\<close> \<open>M Midpoint B B'\<close> \<open>M Midpoint C C''\<close> l12_17 by force
  have "A C Par A'' C''" 
    using \<open>M Midpoint A A''\<close> \<open>M Midpoint C C''\<close> assms(1) sym_par by blast
  have "B' A' Par B' A''" 
    using Par_cases \<open>B A Par B' A''\<close> assms(3) par_trans by blast
  have "B' C' Par B' C''" 
    by (meson \<open>B C Par B' C''\<close> assms(4) par_not_par par_symmetry)
  have "Col B' A' A''" 
    using \<open>B' A' Par B' A''\<close> par_id by auto
  have "Col B' C' C''" 
    using \<open>B' C' Par B' C''\<close> par_id by auto
  have "Cong B A B' A''" 
    using \<open>A \<noteq> B\<close> \<open>M Midpoint A A''\<close> \<open>M Midpoint B B'\<close> mid_par_cong1 by auto
  have "Cong B C B' C''" 
    using \<open>C \<noteq> B\<close> \<open>M Midpoint B B'\<close> \<open>M Midpoint C C''\<close> mid_par_cong1 by auto
  have "A' = A'' \<or> B' Midpoint A' A''" 
  proof -
    have "Col A' B' A''" 
      using Col_cases \<open>Col B' A' A''\<close> by auto
    moreover
    have "Cong B' A' B' A''" 
      by (meson Cong3_def \<open>Cong B A B' A''\<close> assms(2) cong_inner_transitivity)
    ultimately
    show ?thesis 
      by (simp add: l7_20)
  qed
  have "C' = C'' \<or> B' Midpoint C' C''"  
  proof -
    have "Col C' B' C''" 
      by (simp add: \<open>B' C' Par B' C''\<close> par_id_1)
    moreover
    have "Cong B' C' B' C''" 
      using Cong3_def \<open>Cong B C B' C''\<close> assms(2) cong_inner_transitivity by blast
    ultimately
    show ?thesis 
      by (simp add: l7_20)
  qed
  {
    assume "A' = A''"
    {
      assume "C' = C''"
      hence "A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'" 
        by (simp add: \<open>A C Par A'' C''\<close> \<open>A' = A''\<close>)
    }
    moreover
    {
      assume "B' Midpoint C' C''"
      hence "A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'" 
        by (metis Midpoint_def \<open>A' = A''\<close> \<open>Bet A M A''\<close> \<open>M Midpoint B B'\<close> 
            between_trivial impossible_case_3 par_strict_not_col_4)
    }
    ultimately
    have "A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'"         
      using \<open>C' = C'' \<or> B' Midpoint C' C''\<close> by blast
  }
  moreover
  {
    assume "B' Midpoint A' A''"
    {
      assume "C' = C''"
      hence "A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'" 
        by (meson \<open>M Midpoint B B'\<close> \<open>M Midpoint C C''\<close> midpoint_col par_not_col)
    }
    moreover
    {
      assume "B' Midpoint C' C''"
      hence "A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'" 
        by (metis Cong3_def \<open>A C Par A'' C''\<close> 
            \<open>A' = A'' \<Longrightarrow> A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'\<close> 
            \<open>A' = A'' \<or> B' Midpoint A' A''\<close> assms(1) assms(2) cong_identity 
            not_par_one_not_par sym_par)
    }
    ultimately
    have "A C Par A' C' \<or> \<not> B B' ParStrict A A' \<or> \<not> B B' ParStrict C C'" 
      using \<open>C' = C'' \<or> B' Midpoint C' C''\<close> by blast
  }
  ultimately
  show ?thesis 
    using \<open>A' = A'' \<or> B' Midpoint A' A''\<close> by blast
qed

lemma square_perp_rectangle:
  assumes "Rectangle A B C D" and
    "A C Perp B D"
  shows "Square A B C D" 
  by (simp add: Rectangle_Plg Rhombus_Rectangle_Square assms(1) assms(2) perp_rmb)

lemma plgs_half_plgs:
  assumes "ParallelogramStrict A B C D" and
    "P Midpoint A B" and
    "Q Midpoint C D"
  shows "ParallelogramStrict A P Q D \<and> ParallelogramStrict B P Q C" 
  by (meson assms(1) assms(2) assms(3) l7_2 plgs_comm2 plgs_half_plgs_aux)

lemma parallel_2_plg:
  assumes "\<not> Col A B C" and
    "A B Par C D" and
    "A D Par B C" 
  shows "ParallelogramStrict A B C D" 
  by (metis Par_cases ParallelogramStrict_def assms(1) assms(2) assms(3) l12_19)

lemma par_2_plg:
  assumes "\<not> Col A B C" and
    "A B Par C D" and
    "A D Par B C"
  shows "Parallelogram A B C D" 
  by (metis Par_cases ParallelogramStrict_def Parallelogram_def 
      assms(1) assms(2) assms(3) l12_19)

lemma plg_cong_1:
  assumes "Parallelogram A B C D"
  shows "Cong A B C D" 
  by (simp add: assms plg_cong)

lemma plg_cong_2:
  assumes "Parallelogram A B C D"
  shows "Cong A D B C" 
  using assms plg_cong by auto

lemma plgs_cong_1: 
  assumes "ParallelogramStrict A B C D"
  shows "Cong A B C D" 
  by (simp add: assms plgs_cong)

lemma plgs_cong_2:
  assumes "ParallelogramStrict A B C D"
  shows "Cong A D B C" 
  by (simp add: assms plgs_cong)


lemma Plg_perm:
  assumes "Parallelogram A B C D"
  shows "Parallelogram A B C D \<and> Parallelogram B C D A \<and> 
         Parallelogram C D A B \<and>Parallelogram D A B C \<and> 
         Parallelogram A D C B \<and> Parallelogram D C B A \<and> 
         Parallelogram C B A D \<and> Parallelogram B A D C"
  by (meson assms plg_comm2 plg_permut)

lemma plg_not_comm_1:
  assumes "A \<noteq> B" and
    "Parallelogram A B C D"
  shows "\<not> Parallelogram A B D C" 
  by (simp add: assms(1) assms(2) plg_not_comm_R1)

lemma plg_not_comm_2:
  assumes "A \<noteq> B" and
    "Parallelogram A B C D"
  shows "\<not> Parallelogram B A C D" 
  using assms(1) assms(2) plg_not_comm_R2 by blast

lemma parallelogram_strict_midpoint:
  assumes "ParallelogramStrict A B C D" and
    "Col I A C" and
    "Col I B D"
  shows "I Midpoint A C \<and> I Midpoint B D" 
  by (metis not_col_distincts assms(1) assms(2) assms(3) col_not_plgs 
      col_permutation_4 l7_21 not_cong_4312 parallelogram_strict_not_col_2 plgs_cong)

lemma rmb_perp:
  assumes "A \<noteq> C" and
    "B \<noteq> D" and
    "Rhombus A B C D"
  shows "A C Perp B D" 
proof -
  obtain M where "M Midpoint A C \<and> M Midpoint B D" 
    using Plg_def Rhombus_Plg assms(3) by presburger
  hence "M Midpoint A C" 
    by simp
  hence "Per A M D" 
    using assms(3) rmb_per by blast
  hence "A M Perp M D" 
    by (metis \<open>M Midpoint A C \<and> M Midpoint B D\<close> assms(1) assms(2) 
        cong_identity l7_2 l8_5 per_double_cong per_perp)
  have "M Midpoint B D" 
    using \<open>M Midpoint A C \<and> M Midpoint B D\<close> by blast
  have "A \<noteq> M" 
    using \<open>M Midpoint A C\<close> assms(1) midpoint_distinct_1 by blast
  moreover
  have "M \<noteq> D" 
    using \<open>M Midpoint B D\<close> assms(2) midpoint_not_midpoint by auto
  moreover
  have "Col D M B" 
    using \<open>M Midpoint A C \<and> M Midpoint B D\<close> col_permutation_2 midpoint_col by blast
  moreover 
  have "Col A M C"
    by (simp add: \<open>M Midpoint A C \<and> M Midpoint B D\<close> bet_col midpoint_bet)
  ultimately
  show ?thesis  
    by (meson perp_col4 \<open>A M Perp M D\<close> assms(1) assms(2) col_trivial_3 perp_right_comm)
qed

lemma rect_permut: 
  assumes "Rectangle A B C D"
  shows "Rectangle B C D A" 
proof -
  have "Plg B C D A" 
    by (meson Rectangle_Plg assms parallelogram_to_plg plg_permut plg_to_parallelogram)
  moreover
  have "Cong B D C A" 
    using Rectangle_def assms cong_3421 by blast
  ultimately
  show ?thesis 
    by (simp add: Rectangle_def)
qed

lemma rect_comm2: 
  assumes "Rectangle A B C D"
  shows "Rectangle B A D C" 
  by (metis Plg_def Rectangle_def assms cong_symmetry)

lemma rect_per1: 
  assumes "Rectangle A B C D"
  shows "Per B A D" 
proof -
  obtain P where "P Midpoint A B" 
    using MidR_uniq_aux by blast
  obtain Q where "Q Midpoint C D" 
    using MidR_uniq_aux by blast
  obtain M where "M Midpoint A C \<and> M Midpoint B D" 
    using Plg_def Rectangle_Plg assms by presburger
  have "M Midpoint A C" 
    by (simp add: \<open>M Midpoint A C \<and> M Midpoint B D\<close>)
  have "M Midpoint B D" 
    by (simp add: \<open>M Midpoint A C \<and> M Midpoint B D\<close>)
  have "Parallelogram A B C D" 
    by (simp add: Rectangle_Parallelogram assms)
  moreover
  {
    assume "ParallelogramStrict A B C D"
    have "P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q" 
      by (meson half_plgs_R1 Tarski_Euclidean_axioms \<open>M Midpoint A C\<close> 
          \<open>P Midpoint A B\<close> \<open>ParallelogramStrict A B C D\<close> \<open>Q Midpoint C D\<close> half_plgs_R2)
    have "P Q Par A D" 
      by (simp add: \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close>)
    have "M Midpoint P Q" 
      by (simp add: \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close>)
    have "Cong A D P Q" 
      by (simp add: \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close>)
    have "Per A P Q" 
    proof -
      have "Col P M Q" 
        using \<open>M Midpoint P Q\<close> bet_col midpoint_bet by blast
      moreover
      have "Cong M A M B" 
        by (meson Rectangle_def \<open>M Midpoint A C \<and> M Midpoint B D\<close> 
            assms cong_commutativity cong_cong_half_1)
      hence "Per M P A" 
        using \<open>P Midpoint A B\<close> Per_def by blast
      hence "Per A P M" 
        using l8_2 by blast
      ultimately
      show ?thesis 
        by (metis \<open>M Midpoint P Q\<close> l8_4 per_col)
    qed
    have "A \<noteq> B" 
      using \<open>ParallelogramStrict A B C D\<close> plgs_diff by blast
    hence "A \<noteq> P" 
      using \<open>P Midpoint A B\<close> midpoint_distinct_1 by blast

    have "A D Perp A B" 
    proof -
      have "P Q Perp A B" 
        by (metis Perp_cases \<open>A \<noteq> B\<close> \<open>A \<noteq> P\<close> \<open>P Midpoint A B\<close> 
            \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close> \<open>Per A P Q\<close> 
            col_per_perp cong_identity l8_2 midpoint_col par_neq2)
      moreover
      have "Coplanar A D A B" 
        using ncop_distincts by blast
      ultimately
      show ?thesis 
        using \<open>P Q Par A D\<close> cop_par_perp__perp by blast
    qed
    hence "A B Perp D A" 
      using Perp_perm by blast
    hence "Per B A D" 
      using perp_per_1 by force
  }
  moreover
  {
    assume "ParallelogramFlat A B C D"
    hence "Col A B C \<and> Col A B D \<and> Cong A D C B \<and> ((A \<noteq> C) \<or> (B \<noteq> D))" 
      using ParallelogramFlat_def by blast
    hence "(A = B \<and> C = D) \<or> (A = D \<and> C = B)" 
    proof -
      have "Col A C B" 
        by (simp add: \<open>Col A B C \<and> Col A B D \<and> Cong A D C B \<and> (A \<noteq> C \<or> B \<noteq> D)\<close> 
            col_permutation_5)
      moreover
      have "M Midpoint A C" 
        using \<open>M Midpoint A C \<and> M Midpoint B D\<close> by auto
      moreover
      have "M Midpoint B D" 
        by (simp add: \<open>M Midpoint A C \<and> M Midpoint B D\<close>)
      moreover
      have "Cong A C B D" 
        using Rectangle_def assms by blast
      ultimately
      show ?thesis 
        using midpoint_cong_uniqueness by blast
    qed
    hence "Per B A D" 
      using l8_20_1_R1 l8_5 by presburger
  }
  ultimately
  show ?thesis 
    using Parallelogram_def by blast
qed

lemma rect_per2:
  assumes "Rectangle A B C D"
  shows "Per A B C" 
  using assms rect_comm2 rect_per1 by blast

lemma rect_per3: 
  assumes "Rectangle A B C D"
  shows "Per B C D" 
  using assms rect_per2 rect_permut by blast

lemma rect_per4: 
  assumes "Rectangle A B C D"
  shows "Per A D C" 
  by (meson assms rect_comm2 rect_per3)

lemma plg_per_rect1: 
  assumes "Plg A B C D" and
    "Per D A B"
  shows "Rectangle A B C D" 
proof -
  obtain P where "P Midpoint A B" 
    using MidR_uniq_aux by blast
  obtain Q where "Q Midpoint C D" 
    using MidR_uniq_aux by blast
  obtain M where "M Midpoint A C \<and> M Midpoint B D" 
    using Plg_def assms(1) by presburger
  have "Parallelogram A B C D" 
    by (simp add: assms(1) plg_to_parallelogram)
  moreover
  {
    assume "ParallelogramStrict A B C D"
    hence "P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q" 
      using \<open>M Midpoint A C \<and> M Midpoint B D\<close> \<open>P Midpoint A B\<close> 
        \<open>Q Midpoint C D\<close> half_plgs by blast
    have "P Q Par A D" 
      by (simp add: \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close>)
    have "M Midpoint P Q" 
      by (simp add: \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close>)
    have "Cong A D P Q" 
      by (simp add: \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close>)
    have "A \<noteq> D \<and> P \<noteq> Q" 
      using \<open>P Q Par A D\<close> par_neq1 par_neq2 by blast
    have "A \<noteq> B" 
      using \<open>ParallelogramStrict A B C D\<close> plgs_diff by blast
    have "A \<noteq> P" 
      using \<open>A \<noteq> B\<close> \<open>P Midpoint A B\<close> midpoint_distinct_1 by blast
    have "P Q Perp A B" 
    proof -
      have "A D Par P Q" 
        using Par_cases \<open>P Q Par A D\<close> by blast
      moreover
      have "A D Perp A B" 
        by (metis \<open>A \<noteq> B\<close> \<open>A \<noteq> D \<and> P \<noteq> Q\<close> assms(2) per_perp perp_left_comm)
      moreover
      have "Coplanar P Q A B" 
        using \<open>P Midpoint A B\<close> midpoint_col ncop__ncols by blast
      ultimately
      show ?thesis 
        using cop_par_perp__perp by blast
    qed
    have "P M Perp A B" 
      by (metis Bet_cases Col_def Midpoint_def 
          \<open>P Q Par A D \<and> M Midpoint P Q \<and> Cong A D P Q\<close> 
          \<open>P Q Perp A B\<close> is_midpoint_id perp_col)
    have "A P Perp P M" 
      by (metis Col_cases Perp_perm \<open>A \<noteq> P\<close> \<open>P M Perp A B\<close> \<open>P Midpoint A B\<close> 
          col_trivial_3 midpoint_col perp_col2)
    have "Per A P M" 
      using \<open>A P Perp P M\<close> perp_comm perp_per_1 by blast
    obtain B' where "P Midpoint A B'" and "Cong M A M B'" 
      using \<open>P Midpoint A B\<close> \<open>Per A P M\<close> l8_2 per_double_cong by blast
    have "B = B'" 
      using SymR_uniq_aux \<open>P Midpoint A B'\<close> \<open>P Midpoint A B\<close> by blast
    hence "Cong A C B D" 
      using \<open>Cong M A M B'\<close> \<open>M Midpoint A C \<and> M Midpoint B D\<close> 
        cong_mid2__cong not_cong_2143 by blast
    hence "Rectangle A B C D" 
      by (simp add: assms(1) Rectangle_def)
  }
  moreover
  {
    assume "ParallelogramFlat A B C D"
    have "Rectangle A B C D" 
      by (metis Col_cases ParallelogramFlat_def plg_permut 
          \<open>ParallelogramFlat A B C D\<close> assms(1) assms(2) calculation(1) 
          cong_reflexivity l8_9 plg_cong_rectangle plg_not_comm_R1)
  }
  ultimately
  show ?thesis 
    using Parallelogram_def by blast
qed

lemma plg_per_rect2: 
  assumes "Plg A B C D" and
    "Per C B A"
  shows "Rectangle A B C D" 
proof -
  have "Plg B A D C" 
    by (metis Plg_def assms(1))
  thus ?thesis 
    by (simp add: assms(2) plg_per_rect1 rect_comm2)
qed

lemma plg_per_rect3: 
  assumes "Plg A B C D" and
    "Per A D C"
  shows "Rectangle A B C D" 
proof -
  have "Plg D A B C" 
    by (meson assms(1) parallelogram_to_plg plg_permut plg_to_parallelogram)
  moreover
  have "Per C D A" 
    using Per_cases assms(2) by blast
  ultimately
  show ?thesis 
    by (simp add: plg_per_rect1 rect_permut)
qed

lemma plg_per_rect4: 
  assumes "Plg A B C D" and
    "Per B C D" 
  shows "Rectangle A B C D" 
proof -
  have "Plg B A D C" 
    using Plg_def assms(1) by auto
  thus ?thesis 
    by (meson assms(2) plg_per_rect3 rect_comm2)
qed

lemma plg_per_rect: 
  assumes "Plg A B C D" and
    "Per D A B \<or> Per C B A \<or> Per A D C \<or> Per B C D"
  shows "Rectangle A B C D" 
  by (meson assms(1) assms(2) plg_per_rect1 plg_per_rect2 plg_per_rect3 plg_per_rect4)

lemma rect_per: 
  assumes "Rectangle A B C D"
  shows "Per B A D \<and> Per A B C \<and> Per B C D \<and> Per A D C" 
  using assms rect_comm2 rect_per1 rect_per3 by blast

lemma plgf_rect_id:
  assumes "ParallelogramFlat A B C D" and
    "Rectangle A B C D"
  shows "(A = D \<and> B = C) \<or> (A = B \<and> D = C)" 
  by (metis ParallelogramFlat_def assms(1) assms(2) cong3_id l8_9 plgf_permut rect_per3)

lemma cop_perp3__perp:
  assumes "Coplanar A B C D" and
    "A B Perp B C" and
    "B C Perp C D" and
    "C D Perp D A"
  shows "D A Perp A B" 
proof -
  have "A B Perp D A" 
  proof -
    have "A B Par C D"  
      by (meson Perp_perm assms(1) assms(2) assms(3) l12_9 ncop_distincts 
          ncoplanar_perm_12)
    hence "C D Par A B" 
      using Par_cases by blast
    moreover
    have "Coplanar A B D A" 
      using ncop_distincts by blast
    ultimately
    show ?thesis 
      using assms(4) cop_par_perp__perp by blast
  qed
  thus ?thesis 
    using Perp_cases by blast
qed

lemma cop_perp3__rect:
  assumes "Coplanar A B C D" and
    "A B Perp B C" and
    "B C Perp C D" and
    "C D Perp D A"
  shows "Rectangle A B C D" 
proof -
  have "\<not> Col A B C" 
    using assms(2) col_trivial_2 perp_not_col2 by blast
  have "A B Par C D" 
    by (meson Perp_perm assms(1) assms(2) assms(3) l12_9 ncop_distincts 
        ncoplanar_perm_12)
  hence "A D Par B C" 
    by (meson assms(1) assms(2) assms(4) cop4_par_perp2__par ncop_distincts 
        par_left_comm par_symmetry)
  have "D A Perp A B" 
    using assms(1) assms(2) assms(3) assms(4) cop_perp3__perp by blast
  have "ParallelogramStrict A B C D" 
    using \<open>A B Par C D\<close> \<open>A D Par B C\<close> \<open>\<not> Col A B C\<close> parallel_2_plg by presburger
  thus ?thesis 
    by (simp add: Parallelogram_strict_Parallelogram parallelogram_to_plg 
        assms(3) perp_comm perp_per_1 plg_per_rect4)
qed

lemma conga_to_par_os:
  assumes "Bet A D P" and
    "A D OS B C" and
    "B A P CongA C D P"
  shows "A B Par C D" 
  by (metis CongA_def Out_def assms(1) assms(2) assms(3) bet_col 
      between_symmetry col_one_side invert_one_side l12_22 par_right_comm)

lemma plg_par: 
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Parallelogram A B C D" 
  shows "A B Par C D \<and> A D Par B C" 
  by (metis Plg_perm Par_cases l12_17 assms(1) assms(2) assms(3) plg_mid)

lemma plg_par_1: 
  assumes "A \<noteq> B" and 
    "B \<noteq> C" and
    "Parallelogram A B C D" 
  shows "A B Par C D" 
  by (simp add: assms(1) assms(2) assms(3) plg_par)

lemma plg_par_2: 
  assumes "A \<noteq> B" and 
    "B \<noteq> C" and 
    "Parallelogram A B C D" 
  shows "A D Par B C" 
  using assms(1) assms(2) assms(3) plg_par by blast

lemma plgs_pars_1: 
  assumes "ParallelogramStrict A B C D"
  shows "A B ParStrict C D" 
  by (simp add: assms plgs__pars)

lemma plgs_pars_2: 
  assumes "ParallelogramStrict A B C D" 
  shows "A D ParStrict B C" 
  using assms plgs_par_strict by blast

lemma par_cong_cong: 
  assumes "A B Par C D" and
    "Cong A B C D" 
  shows "Cong A C B D \<or> Cong A D B C" 
proof cases
  assume "A = B"
  thus ?thesis 
    using assms(1) par_neq1 by auto
next
  assume "A \<noteq> B"
  thus ?thesis 
  proof cases
    assume "A = D" 
    thus ?thesis 
      using assms(2) not_cong_4321 by blast
  next
    assume "A \<noteq> D" 
    obtain M where "(M Midpoint A C \<and> M Midpoint B D) \<or> (M Midpoint A D \<and> M Midpoint B C)" 
      using assms(1) assms(2) par_cong_mid by blast
    moreover
    {
      assume "M Midpoint A C" and "M Midpoint B D" 
      hence "Cong A C B D \<or> Cong A D B C" 
        using \<open>A \<noteq> B\<close> \<open>A \<noteq> D\<close> cong_right_commutativity mid_par_cong by blast
    }
    moreover
    {
      assume "M Midpoint A D" and "M Midpoint B C" 
      hence "Cong A C B D \<or> Cong A D B C" 
        by (metis Cong_cases Mid_cases l7_13)
    }
    ultimately show ?thesis 
      by blast
  qed
qed

lemma col_cong_cong: 
  assumes "Col A B C" and 
    "Col A B D" and 
    "Cong A B C D" 
  shows "Cong A C B D \<or> Cong A D B C" 
proof cases
  assume "A = B" 
  thus ?thesis 
    using assms(3) cong_reflexivity cong_reverse_identity by blast
next
  assume "A \<noteq> B"
  show ?thesis
  proof cases
    assume "C = D"
    thus ?thesis 
      using \<open>A \<noteq> B\<close> assms(3) cong_identity_inv by auto
  next
    assume "C \<noteq> D"
    moreover have "A B Par C D" 
      using \<open>A \<noteq> B\<close> assms(1) assms(2) calculation par_col2_par par_reflexivity by blast
    ultimately show ?thesis 
      using  assms(3) par_cong_cong by blast
  qed
qed

lemma par_cong_cop:
  assumes "A B Par C D" (*and
"Cong A B C D" *)
  shows "Coplanar A B C D" 
  using assms(1) par__coplanar by auto

lemma par_cong_plg :
  assumes "A B Par C D" and
    "Cong A B C D" 
  shows "Plg A B C D \<or> Plg A B D C" 
proof -
  obtain M where "(M Midpoint A C \<and> M Midpoint B D) \<or> (M Midpoint A D \<and> M Midpoint B C)" 
    using assms(1) assms(2) par_cong_mid by blast
  moreover
  {
    assume "M Midpoint A C \<and> M Midpoint B D" 
    hence "Plg A B C D \<or> Plg A B D C" 
      by (metis Plg_def assms(1) l7_3 par_neq1)
  }
  moreover
  {
    assume "M Midpoint A D \<and> M Midpoint B C" 
    hence "Plg A B C D \<or> Plg A B D C" 
      by (metis Plg_def assms(1) l7_3 par_neq1)
  }
  ultimately show ?thesis 
    by blast
qed

lemma par_cong_plg_2 :
  assumes "A B Par C D" and
    "Cong A B C D"
  shows "Parallelogram A B C D \<or> Parallelogram A B D C" 
  by (metis assms(1) assms(2) mid_plg par_cong_mid par_neq2 plg_trivial)

lemma par_cong3_rect:
  assumes "A \<noteq> C \<or> B \<noteq> D" and
    "A B Par C D" and
    "Cong A B C D" and
    "Cong A D B C" and
    "Cong A C B D" 
  shows "Rectangle A B C D \<or> Rectangle A B D C" 
  by (simp add: Rectangle_def assms(2) assms(3) assms(4) assms(5) par_cong_plg)

lemma pars_par_pars:
  assumes "A B ParStrict C D" and
    "A D Par B C" 
  shows "A D ParStrict B C" 
  using Par_def assms(1) assms(2) par_strict_not_col_1 by blast

lemma pars_par_plg: 
  assumes "A B ParStrict C D" and 
    "A D Par B C" 
  shows "Plg A B C D" 
proof -
  have "A D ParStrict B C" 
    by (simp add: assms(1) assms(2) pars_par_pars)
  have "A B Par C D" 
    by (simp add: Par_def assms(1))
  have "A \<noteq> C" 
    using assms(1) not_par_strict_id by blast
  moreover
  have "B \<noteq> D" 
    using \<open>A D ParStrict B C\<close> col_trivial_2 par_strict_not_col_1 by blast
  moreover
  obtain M where "M Midpoint A C" 
    using MidR_uniq_aux by blast
  moreover
  have "M Midpoint B D" 
    by (metis Par_cases par_strict_not_col_1 \<open>A B Par C D\<close> \<open>M Midpoint A C\<close> 
        assms(1) assms(2) l12_19 l7_17 par_cong_mid_ts)
  ultimately
  show ?thesis 
    using Plg_def by blast
qed

lemma not_par_pars_not_cong:
  assumes "P Out A B" and
    "P Out A' B'" and
    "A A' ParStrict B B'"
  shows "\<not> Cong A A' B B'" 
proof -
  have "Col P A B" 
    by (simp add: assms(1) out_col)
  have "Col P A' B'" 
    using assms(2) out_col by blast
  {
    assume "Cong A A' B B'"
    have "A \<noteq> B" 
      using assms(3) not_par_strict_id by auto
    have "A' \<noteq> B'" 
      using assms(3) between_trivial2 impossible_case_1 by blast
    have "P \<noteq> A" 
      using Out_def assms(1) by auto
    have "P \<noteq> A'" 
      using Out_def assms(2) by blast
    have "\<not> Col P A A'" 
      by (metis \<open>P \<noteq> A'\<close> assms(2) assms(3) col3 col_transitivity_1 
          not_col_permutation_5 out_col par_strict_not_col_4)
    have "A B OS A' B'" 
      by (metis Col_cases assms(1) assms(2) assms(3) out_col 
          out_one_side_1 par_strict_not_col_1)
    have "A A' Par B B'" 
      by (simp add: Par_def assms(3))
    hence False 
      using NCol_perm \<open>A B OS A' B'\<close> \<open>Col P A B\<close> \<open>Col P A' B'\<close> 
        \<open>Cong A A' B B'\<close> not_strict_par one_side_not_col124 
        os_cong_par_cong_par by blast
  }
  thus ?thesis 
    by auto
qed

lemma plg_uniqueness:
  assumes "Parallelogram A B C D" and 
    "Parallelogram A B C D'" 
  shows "D = D'" 
  by (metis SymR_uniq_aux assms(1) assms(2) l7_17 plg_mid)


lemma plgs_trans_trivial:
  assumes "ParallelogramStrict A B C D" and
    "ParallelogramStrict C D A B'" 
  shows "Parallelogram A B B' A" 
  by (metis plg_uniqueness Parallelogram_strict_Parallelogram plg_sym plg_trivial
      assms(1) assms(2) plgs_diff)

lemma par_strict_trans:
  assumes "A B ParStrict C D" and
    "C D ParStrict E F" 
  shows "A B Par E F" 
  using assms(1) assms(2) par_not_par par_strict_par by blast

lemma plgs_pseudo_trans:
  assumes "ParallelogramStrict A B C D" and
    "ParallelogramStrict C D E F"
  shows "Parallelogram A B F E" 
proof cases
  assume "A = E"
  thus ?thesis 
    using assms(1) assms(2) plgs_trans_trivial by blast
next
  assume "A \<noteq> E"
  have "C \<noteq> D" 
    using assms(1) plgs_diff by blast
  obtain D' where "Bet D C D'" and "Cong C D' D C" 
    using segment_construction by blast
  have "C \<noteq> D'" 
    using \<open>C \<noteq> D\<close> \<open>Cong C D' D C\<close> cong_diff_4 by presburger
  have "A B ParStrict C D"
    using assms(1) plgs_par_strict by auto
  hence "C D ParStrict A B" 
    using par_strict_symmetry by blast
  have "A D ParStrict B C" 
    using assms(1) plgs_par_strict by auto
  have "C D ParStrict E F" 
    using assms(2) plgs_par_strict by auto
  have "C F ParStrict D E" 
    using assms(2) plgs_par_strict by auto
  have "C D OS A B" 
    using assms(1) plgs_one_side by blast
  have "C D OS E F" 
    using \<open>C D ParStrict E F\<close> l12_6 by auto
  have "A D D' CongA B C D'" 
    by (meson Par_def Par_strict_cases \<open>A D ParStrict B C\<close> \<open>Bet D C D'\<close> 
        \<open>C D OS A B\<close> \<open>C \<noteq> D'\<close> invert_one_side par_preserves_conga_os)
  have "E D D' CongA F C D'" 
    by (meson ParallelogramStrict_def \<open>Bet D C D'\<close> \<open>C D OS E F\<close> \<open>C \<noteq> D'\<close> 
        assms(2) invert_one_side l12_20 par_preserves_conga_os)
  have "\<not> Col A C D" 
    using \<open>A B ParStrict C D\<close> col_permutation_1 par_strict_not_col_3 by blast
  have "\<not> Col E C D" 
    using \<open>C D OS E F\<close> col123__nos not_col_permutation_2 by blast
  {
    assume "Coplanar C D A E"
    have "A D E CongA B C F"
    proof -
      have "C D TS A E \<or> C D OS A E" 
        using \<open>Coplanar C D A E\<close> \<open>\<not> Col A C D\<close> \<open>\<not> Col E C D\<close> cop_nts__os by blast
      moreover
      {
        assume "C D TS A E" 
        hence "C D TS A F" 
          using \<open>C D OS E F\<close> l9_2 l9_8_2 by blast
        hence "C D TS B F" 
          using \<open>C D OS A B\<close> l9_8_2 by blast
        have "A D E CongA B C F" 
        proof -
          have "D D' TS A E" 
            using \<open>Bet D C D'\<close> \<open>C D TS A E\<close> bet_col bet_neq23__neq 
              col_two_sides invert_two_sides by blast
          moreover have "C D' TS B F" 
            by (meson \<open>Bet D C D'\<close> \<open>C D TS B F\<close> \<open>C \<noteq> D'\<close> bet_col bet_col1 
                col_preserves_two_sides invert_two_sides)
          moreover have "A D D' CongA B C D'" 
            using \<open>A D D' CongA B C D'\<close> by auto
          moreover have"D' D E CongA D' C F" 
            by (simp add: \<open>E D D' CongA F C D'\<close> conga_comm)
          ultimately show ?thesis
            using l11_22a by blast
        qed
      }
      moreover
      {
        assume "C D OS A E" 
        have "A D E CongA B C F" 
        proof -
          have "D D' OS A E" 
            using \<open>Bet D C D'\<close> \<open>C D OS A E\<close> bet_col between_identity 
              col_one_side invert_one_side by blast
          moreover have "C D' OS B F" 
            by (metis \<open>Bet D C D'\<close> \<open>C D OS A B\<close> \<open>C D OS A E\<close> \<open>C D OS E F\<close> 
                \<open>C \<noteq> D'\<close> bet_col col_one_side col_permutation_4 one_side_symmetry 
                one_side_transitivity)
          moreover have "A D D' CongA B C D'" 
            by (simp add: \<open>A D D' CongA B C D'\<close>) 
          moreover have "D' D E CongA D' C F" 
            by (simp add: \<open>E D D' CongA F C D'\<close> conga_comm)
          ultimately show ?thesis
            using l11_22 by blast
        qed
      }
      ultimately 
      show ?thesis 
        by blast
    qed
    have "Cong A B C D" 
      using assms(1) plgs_cong by auto
    have "Cong A D B C" 
      using assms(1) plgs_cong by auto
    have "Cong C D E F" 
      using assms(2) plgs_cong by auto
    have "Cong C F D E" 
      using assms(2) plgs_cong by auto
    hence "Cong D E C F" 
      using not_cong_3412 by blast
    hence "Cong A E B F" 
      using \<open>A D E CongA B C F\<close> \<open>Cong A D B C\<close> cong2_conga_cong by auto
    have "A B Par E F" 
      using \<open>A B ParStrict C D\<close> \<open>C D ParStrict E F\<close> not_par_one_not_par 
        par_strict_par par_strict_symmetry by blast
    have "Parallelogram A B F E" 
    proof cases
      assume "Col A E F" 
      {
        assume "A B ParStrict E F"
        hence "Parallelogram A B F E" 
          using Col_cases \<open>Col A E F\<close> par_strict_not_col_3 by blast
      }
      moreover
      {
        assume "A \<noteq> B" and "E \<noteq> F" and 
          "Col A E F" and "Col B E F"
        have "ParallelogramFlat A B F E" 
        proof -
          have "Col A B F" 
            using \<open>Col A E F\<close> \<open>Col B E F\<close> \<open>E \<noteq> F\<close> col2__eq col_permutation_5 by blast
          moreover have "Col A B E" 
            using \<open>Col A E F\<close> \<open>Col B E F\<close> \<open>E \<noteq> F\<close> col_permutation_5 l6_16_1 by blast
          moreover have "Cong A B F E" 
            by (meson \<open>Cong A B C D\<close> \<open>Cong C D E F\<close> cong_right_commutativity cong_transitivity)
          moreover have "Cong A E F B" 
            using Cong_cases \<open>Cong A E B F\<close> by blast
          moreover have "A \<noteq> F \<or> B \<noteq> E" 
            using assms(1) assms(2) plgs_not_comm_1 plgs_sym by blast
          ultimately show ?thesis 
            using ParallelogramFlat_def by blast
        qed
        hence "Parallelogram A B F E" 
          by (simp add: Parallelogram_def)
      }
      ultimately show ?thesis 
        using Par_def \<open>A B Par E F\<close> by presburger
    next
      assume "\<not> Col A E F"
      have "A E Par B F \<or> \<not> D C ParStrict A B \<or> \<not> D C ParStrict E F" 
      proof -
        have "D A E Cong3 C B F" 
          using Cong3_def Cong_cases \<open>Cong A D B C\<close> \<open>Cong A E B F\<close> \<open>Cong D E C F\<close> by blast
        moreover have "D A Par C B" 
          using Par_cases Par_def \<open>A D ParStrict B C\<close> by blast
        moreover have "D E Par C F" 
          by (simp add: \<open>C F ParStrict D E\<close> par_strict_par par_symmetry)
        ultimately show ?thesis
          using \<open>A \<noteq> E\<close> cong3_par2_par by blast
      qed
      moreover
      {
        assume "A E Par B F" 
        hence "Parallelogram A B F E" 
          using Plg_perm \<open>A B Par E F\<close> \<open>\<not> Col A E F\<close> par_2_plg par_right_comm by blast
      }
      moreover
      {
        assume "\<not> D C ParStrict A B" 
        hence "Parallelogram A B F E" 
          using Par_strict_perm \<open>A B ParStrict C D\<close> by blast
      }
      moreover
      {
        assume "\<not> D C ParStrict E F" 
        hence "Parallelogram A B F E" 
          using Par_strict_perm \<open>C D ParStrict E F\<close> by blast
      }
      ultimately show ?thesis
        by blast
    qed
  }
  moreover
  {
    assume "\<not> Coplanar C D A E"
    have "Parallelogram A B E F \<or> Parallelogram A B F E" 
    proof -
      have "A B Par E F" 
        using \<open>A B ParStrict C D\<close> \<open>C D ParStrict E F\<close> par_strict_trans by force
      moreover
      have "Cong A B E F" 
        using assms(1) assms(2) cong_transitivity plgs_cong_1 by blast
      ultimately
      show ?thesis 
        using par_cong_plg_2 by blast
    qed
    moreover
    {
      assume "Parallelogram A B E F"
      hence "A E OS B F" 
      proof -
        have "Coplanar A D E A" 
          using ncop_distincts by auto
        moreover have "Coplanar A D E E" 
          using ncop_distincts by blast
        moreover have "Coplanar A E B F" 
          using \<open>Parallelogram A B E F\<close> coplanar_perm_2 parallelogram__coplanar by blast
        moreover have "A D E OSP B F" 
        proof -
          have "A D E OSP B C" 
          proof -
            have "\<not> Coplanar A D E B" 
              by (meson \<open>A B ParStrict C D\<close> \<open>C D ParStrict A B\<close> 
                  \<open>\<not> Coplanar C D A E\<close> l9_30 ncop_distincts ncoplanar_perm_15 
                  par_strict_not_col_3 par_strict_not_col_4 pars__coplanar)
            moreover have "Coplanar A D E A" 
              using \<open>Coplanar A D E A\<close> by auto
            moreover have "Coplanar A D E D" 
              using ncop_distincts by blast
            moreover have "A D OS B C" 
              using \<open>A D ParStrict B C\<close> l12_6 by auto
            ultimately show ?thesis
              using cop2_os__osp by blast
          qed
          moreover
          have "A D E OSP C F" 
          proof -
            have "\<not> Coplanar A D E C"             
              using \<open>\<not> Coplanar C D A E\<close> coplanar_perm_20 by blast
            moreover have "Coplanar A D E D"             
              using ncop_distincts by blast
            moreover have "Coplanar A D E E"             
              by (simp add: \<open>Coplanar A D E E\<close>)
            moreover have "D E OS C F"             
              by (simp add: \<open>C F ParStrict D E\<close> pars__os3412)
            ultimately show ?thesis 
              using cop2_os__osp by blast
          qed
          ultimately show ?thesis
            using osp_transitivity by blast
        qed
        ultimately show ?thesis
          using \<open>A \<noteq> E\<close> cop3_osp__os by blast
      qed
      have "A E TS B F" 
        by (metis \<open>A E OS B F\<close> \<open>Parallelogram A B E F\<close> col_permutation_5 
            l12_19 one_side_not_col123 os_distincts plg_par plg_permut)
      hence False 
        by (simp add: \<open>A E OS B F\<close> l9_9_bis)
    }
    ultimately
    have "Parallelogram A B F E" 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma plgf_plgs_trans:
  assumes "A \<noteq> B" and
    "ParallelogramFlat A B C D" and
    "ParallelogramStrict C D E F"
  shows "ParallelogramStrict A B F E" 
proof (cases "A = D")
  case True
  thus ?thesis 
    by (metis ParallelogramFlat_def assms(2) assms(3) 
        cong_reverse_identity plgs_comm2)
next
  case False
  hence "A \<noteq> D" 
    by blast
  show ?thesis 
  proof (cases "B = C")
    case True
    thus ?thesis 
      using False assms(2) cong_diff plgf_cong by blast
  next
    case False
    hence "B \<noteq> C" 
      by auto
    have "C D ParStrict E F \<and> C F ParStrict D E" 
      using assms(3) plgs_par_strict by blast
    have "C D ParStrict E F" 
      by (simp add: \<open>C D ParStrict E F \<and> C F ParStrict D E\<close>) 
    have "C F ParStrict D E" 
      by (simp add: \<open>C D ParStrict E F \<and> C F ParStrict D E\<close>) 
    have "Cong C D E F \<and> Cong C F D E" 
      using assms(3) plgs_cong by blast 
    have "Cong C D E F" 
      by (simp add: \<open>Cong C D E F \<and> Cong C F D E\<close>) 
    have "Cong C F D E" 
      by (simp add: \<open>Cong C D E F \<and> Cong C F D E\<close>) 
    have "C D OS E F" 
      by (simp add: assms(3) plgs_one_side)
    then obtain x where "C D TS E x" and "C D TS F x" 
      using OS_def by blast
    have "\<not> Col F C D" 
      using TS_def \<open>C D TS F x\<close> by blast
    have "\<not> Col E C D" 
      using TS_def \<open>C D TS E x\<close> by blast
    hence "D \<noteq> E" 
      using col_trivial_3 by blast
    have "Col A B C" 
      using ParallelogramFlat_def assms(2) by blast
    have "Col A B D" 
      using ParallelogramFlat_def assms(2) by blast
    have "Cong A B C D" 
      using ParallelogramFlat_def assms(2) by blast
    have "Cong A D C B" 
      using ParallelogramFlat_def assms(2) by blast
    have "A \<noteq> C \<or> B \<noteq> D" 
      using ParallelogramFlat_def assms(2) by blast
    obtain D' where "Bet D C D'" and "Cong C D' D C" 
      using segment_construction by blast
    have "D \<noteq> D'" 
      using \<open>Bet D C D'\<close> \<open>Cong A B C D\<close> assms(1) between_identity cong_identity by blast
    hence "C \<noteq> D'" 
      using \<open>Cong C D' D C\<close> cong_reverse_identity by blast
    have "E D D' CongA F C D'" 
      by (meson ParallelogramStrict_def \<open>Bet D C D'\<close> \<open>C D OS E F\<close> \<open>C \<noteq> D'\<close> 
          assms(3) invert_one_side l12_20 par_preserves_conga_os)
    show ?thesis 
    proof (cases "A = C")
      case True
      hence "A = C" 
        by auto
      hence "B = D \<or> A Midpoint B D" 
        using assms(2) plgf3_mid by blast
      moreover
      {
        assume "A Midpoint B D" 
        have "A F TS E B" 
        proof -
          have "A F TS D B" 
            by (metis False bet__ts True \<open>A \<noteq> C \<or> B \<noteq> D\<close> \<open>Col A B D\<close> 
                \<open>Cong A B C D\<close> \<open>Cong A D C B\<close> \<open>\<not> Col F C D\<close> between_cong 
                col_permutation_4 third_point)
          moreover
          have "A F OS D E" 
            by (simp add: True \<open>C D ParStrict E F \<and> C F ParStrict D E\<close> l12_6)
          ultimately
          show ?thesis 
            using l9_8_2 by blast
        qed
        hence "A F TS B E" 
          using l9_2 by blast
        moreover
        have "A B Par F E" 
          by (metis True \<open>A \<noteq> D\<close> \<open>C D OS E F\<close> \<open>C F ParStrict D E\<close> 
              \<open>Col A B D\<close> \<open>Cong C F D E\<close> assms(1) not_par_not_col one_side_symmetry 
              os_cong_par_cong_par par_not_par par_strict_par)
        moreover
        have "Cong A B F E" 
          using \<open>Cong A B C D\<close> \<open>Cong C D E F \<and> Cong C F D E\<close> 
            cong_right_commutativity cong_transitivity by blast
        ultimately
        have "ParallelogramStrict A B F E" 
          by (simp add: ParallelogramStrict_def)
      }
      ultimately
      show ?thesis 
        using True \<open>A \<noteq> C \<or> B \<noteq> D\<close> by blast
    next
      case False
      hence "A \<noteq> C" 
        by auto
      thus ?thesis 
      proof (cases "B = D")
        case True
        have "A = C \<or> B Midpoint A C" 
          by (metis ParallelogramFlat_def True assms(2) cong_col_mid not_cong_1243)
        {
          assume "B Midpoint A C"
          have "B E TS F A" 
          proof -
            have "B E TS C A" 
              by (metis Bet_cases False True \<open>A = C \<or> B Midpoint A C\<close> 
                  \<open>\<not> Col E C D\<close> assms(1) bet__ts col_permutation_1 midpoint_bet)
            moreover
            have "B E OS C F" 
              by (simp add: True \<open>C D ParStrict E F \<and> C F ParStrict D E\<close> pars__os3412)
            ultimately
            show ?thesis 
              using l9_8_2 by blast
          qed
          hence "B E TS A F" 
            by (simp add: l9_2)
          moreover
          have "B A Par E F" 
            by (metis True \<open>A = C \<or> B Midpoint A C\<close> \<open>B \<noteq> C\<close> 
                \<open>C D ParStrict E F\<close> assms(1) midpoint_col not_par_not_col 
                par_left_comm par_not_par par_strict_par)
          moreover
          have "Cong B A E F" 
            using \<open>Cong A B C D\<close> \<open>Cong C D E F\<close> cong_inner_transitivity 
              not_cong_4312 by blast
          ultimately
          have "ParallelogramStrict B A E F" 
            using ParallelogramStrict_def by blast
          hence "ParallelogramStrict A B F E" 
            using plgs_comm2 by blast
        }
        thus ?thesis 
          using True \<open>A = C \<or> B Midpoint A C\<close> \<open>A \<noteq> C \<or> B \<noteq> D\<close> by fastforce
      next
        case False
        hence "B \<noteq> D" 
          by auto
        have H1: "Bet D C A \<and> Bet C A B \<or> 
              Bet D A C \<and> Bet A C B \<or> 
              Bet A D B \<and> Bet D B C \<or> 
              Bet A B D \<and> Bet B D C" 
          using assms(2) plgf_bet by presburger
        have "A D E CongA B C F" 
        proof -
          {
            assume "Bet D C A \<and> Bet C A B" 
            hence "D Out A D'" 
              by (metis Out_def not_col_distincts \<open>A \<noteq> D\<close> \<open>Bet D C D'\<close> 
                  \<open>D \<noteq> D'\<close> \<open>\<not> Col E C D\<close> l5_1)
            moreover
            have "D Out E E" 
              using \<open>D \<noteq> E\<close> out_trivial by presburger
            moreover
            have "C Out B D'" 
              by (metis Out_def not_col_distincts \<open>A \<noteq> C\<close> \<open>B \<noteq> C\<close> 
                  \<open>Bet D C A \<and> Bet C A B\<close> \<open>Bet D C D'\<close> \<open>C \<noteq> D'\<close> \<open>\<not> Col E C D\<close> 
                  l5_2 outer_transitivity_between)
            moreover
            have "C Out F F" 
              using \<open>\<not> Col F C D\<close> not_col_distincts out_trivial by blast
            ultimately
            have "A D E CongA B C F" 
              by (meson \<open>E D D' CongA F C D'\<close> conga_left_comm conga_right_comm l11_10)
          }
          moreover
          {
            assume "Bet D A C \<and> Bet A C B" 
            hence "D Out A D'" 
              by (meson \<open>A \<noteq> D\<close> \<open>Bet D C D'\<close> bet_out between_exchange4)
            moreover
            have "D Out E E" 
              using \<open>D \<noteq> E\<close> out_trivial by presburger
            moreover
            have "C Out B D'" 
              by (meson \<open>A \<noteq> C\<close> \<open>A \<noteq> D\<close> \<open>B \<noteq> C\<close> \<open>Bet D A C \<and> Bet A C B\<close> 
                  \<open>Bet D C D'\<close> \<open>Cong A B C D\<close> \<open>Cong A D C B\<close> \<open>Cong C D' D C\<close> 
                  assms(1) bet3_cong3_bet bet_out cong_3421 not_cong_1243)
            moreover
            have "C Out F F" 
              using \<open>\<not> Col F C D\<close> not_col_distincts out_trivial by blast
            ultimately
            have "A D E CongA B C F" 
              by (meson \<open>E D D' CongA F C D'\<close> conga_comm l11_10)
          }
          moreover
          {
            assume "Bet A D B \<and> Bet D B C" 
            hence "Bet D' D A" 
              using False \<open>Bet D C D'\<close> between_exchange4 between_symmetry 
                outer_transitivity_between by blast
            moreover
            have "A \<noteq> D" 
              using \<open>A \<noteq> D\<close> by auto
            moreover
            have "Bet D' C B" 
              using \<open>Bet A D B \<and> Bet D B C\<close> \<open>Bet D C D'\<close> between_exchange3 
                between_symmetry by blast
            moreover
            have "B \<noteq> C" 
              using \<open>B \<noteq> C\<close> by auto
            ultimately
            have "A D E CongA B C F" 
              by (meson \<open>E D D' CongA F C D'\<close> conga_comm l11_13)
          }
          moreover
          {
            assume "Bet A B D \<and> Bet B D C" 
            hence "Bet D' D A" 
              by (metis Bet_cases False \<open>Bet D C D'\<close> \<open>\<not> Col E C D\<close> 
                  col_trivial_2 outer_transitivity_between2)
            moreover
            have "A \<noteq> D" 
              using \<open>A \<noteq> D\<close> by auto
            moreover
            have "Bet D' C B"                                   
              using Bet_cases \<open>Bet A B D \<and> Bet B D C\<close> \<open>Bet D C D'\<close> 
                \<open>\<not> Col E C D\<close> col_trivial_2 outer_transitivity_between2 by blast
            moreover
            have "B \<noteq> C" 
              using \<open>B \<noteq> C\<close> by auto
            ultimately
            have "A D E CongA B C F" 
              by (meson \<open>E D D' CongA F C D'\<close> conga_comm l11_13)
          }
          ultimately
          show ?thesis 
            using H1 by fastforce
        qed
        have "Cong A E B F" 
          using \<open>A D E CongA B C F\<close> \<open>Cong A D C B\<close> \<open>Cong C F D E\<close> 
            cong2_conga_cong not_cong_1243 not_cong_3412 by blast
        hence "E A D Cong3 F B C" 
          by (meson Cong3_def \<open>Cong A D C B\<close> \<open>Cong C F D E\<close> 
              cong_4321 cong_right_commutativity)
        have "A B Par E F" 
          by (metis ParallelogramFlat_def par_not_par \<open>C D ParStrict E F\<close> 
              \<open>\<not> Col E C D\<close> assms(1) assms(2) col_trivial_2 par_col2_par 
              par_reflexivity par_strict_par)
        have "E A D CongA F B C" 
          by (metis \<open>A \<noteq> D\<close> \<open>Col A B D\<close> \<open>Cong A E B F\<close> \<open>E A D Cong3 F B C\<close> 
              assms(3) cong3_conga cong_reverse_identity not_col_permutation_1 
              parallelogram_strict_not_col_2)
        have "A B OS E F" 
          by (metis Par_def \<open>A B Par E F\<close> 
              \<open>C D ParStrict E F \<and> C F ParStrict D E\<close> \<open>Col A B D\<close> col_par 
              l12_6 par_strict_not_col_2 parallel_uniqueness)
        have "A E Par F B" 
        proof -
          {
            assume "Bet D C A \<and> Bet C A B"
            obtain A' where "Bet A B A'" and "Cong B A' A B" 
              using segment_construction by blast
            have "E A A' CongA F B A'" 
              by (metis \<open>A \<noteq> C\<close> \<open>Bet A B A'\<close> \<open>Bet D C A \<and> Bet C A B\<close> 
                  \<open>Cong B A' A B\<close> \<open>E A D CongA F B C\<close> assms(1) bet_neq12__neq 
                  cong_diff_3 conga_comm l11_13 outer_transitivity_between 
                  outer_transitivity_between2)
            hence "A E Par F B" 
              using \<open>A B OS E F\<close> \<open>Bet A B A'\<close> conga_to_par_os by blast
          }
          moreover
          {
            assume "Bet D A C \<and> Bet A C B" 
            obtain A' where "Bet A B A'" and "Cong B A' A B" 
              using segment_construction by blast
            have "A' A E CongA A' B F" 
            proof -
              have "Bet D A A'" 
                using \<open>A \<noteq> C\<close> \<open>Bet A B A'\<close> \<open>Bet D A C \<and> Bet A C B\<close> 
                  assms(1) outer_transitivity_between by blast
              moreover
              have "A' \<noteq> A" 
                using \<open>Bet A B A'\<close> assms(1) bet_neq12__neq by blast
              moreover
              have "Bet C B A'" 
                using \<open>Bet A B A'\<close> \<open>Bet D A C \<and> Bet A C B\<close> between_exchange3 by blast
              moreover
              have "A' \<noteq> B" 
                using \<open>Cong B A' A B\<close> assms(1) cong_reverse_identity by blast
              ultimately
              show ?thesis 
                by (meson \<open>E A D CongA F B C\<close> conga_comm l11_13)
            qed
            hence "E A A' CongA F B A'" 
              by (meson conga_comm)
            hence "A E Par F B" 
              using \<open>A B OS E F\<close> \<open>Bet A B A'\<close> conga_to_par_os by blast
          }
          moreover
          {
            assume "Bet A D B \<and> Bet D B C" 
            obtain A' where "Bet A B A'" and "Cong B A' A B" 
              using segment_construction by blast
            have "A' A E CongA A' B F" 
            proof -
              have "A Out A' D" 
                by (metis Out_def \<open>A \<noteq> D\<close> \<open>Bet A B A'\<close> 
                    \<open>Bet A D B \<and> Bet D B C\<close> bet_neq12__neq between_exchange4)
              moreover
              have "A Out E E" 
                using CongA_def \<open>E A D CongA F B C\<close> out_trivial by presburger
              moreover
              have "B Out A' C" 
                by (metis False \<open>B \<noteq> C\<close> \<open>Bet A B A'\<close> \<open>Bet A D B \<and> Bet D B C\<close> 
                    \<open>Cong A B C D\<close> \<open>Cong A D C B\<close> \<open>Cong B A' A B\<close> bet3_cong3_bet 
                    bet_out calculation(1) cong_left_commutativity cong_symmetry 
                    l6_6 out_distinct)
              moreover
              have "B Out F F" 
                using CongA_def \<open>E A D CongA F B C\<close> out_trivial by presburger
              ultimately
              show ?thesis 
                by (meson \<open>E A D CongA F B C\<close> conga_comm l11_10)
            qed
            hence "E A A' CongA F B A'" 
              by (simp add: conga_comm)
            hence "A E Par F B" 
              using \<open>A B OS E F\<close> \<open>Bet A B A'\<close> conga_to_par_os by blast
          }
          moreover
          {
            assume "Bet A B D \<and> Bet B D C" 
            obtain A' where "Bet A B A'" and "Cong B A' A C" 
              using segment_construction by blast
            have "A' A E CongA A' B F" 
            proof -
              have "A Out A' D" 
                by (metis Out_def \<open>Bet A B A'\<close> \<open>Bet A B D \<and> Bet B D C\<close> 
                    assms(1) bet_out l5_1)
              moreover
              have "A Out E E" 
                using CongA_def \<open>E A D CongA F B C\<close> out_trivial by presburger
              moreover
              have "B Out A' C" 
                by (metis Bet_cases False \<open>B \<noteq> C\<close> \<open>Bet A B A'\<close> 
                    \<open>Bet A B D \<and> Bet B D C\<close> \<open>Cong B A' A C\<close> assms(1) 
                    bet_cong_eq l6_2 outer_transitivity_between)
              moreover
              have "B Out F F" 
                using CongA_def \<open>E A D CongA F B C\<close> out_trivial by presburger
              ultimately
              show ?thesis 
                by (meson \<open>E A D CongA F B C\<close> conga_comm l11_10)
            qed
            hence "E A A' CongA F B A'"
              by (simp add: conga_comm)
            hence "A E Par F B" 
              using \<open>A B OS E F\<close> \<open>Bet A B A'\<close> conga_to_par_os by blast
          }
          ultimately
          show ?thesis 
            using H1 by fastforce
        qed
        thus ?thesis 
          by (meson Par_cases \<open>A B OS E F\<close> \<open>A B Par E F\<close>
              one_side_not_col124 parallel_2_plg)
      qed
    qed
  qed
qed

lemma plgf_plgf_plgf: 
  assumes "A \<noteq> B" and
    "ParallelogramFlat A B C D" and
    "ParallelogramFlat C D E F"
  shows "ParallelogramFlat A B F E" 
proof -
  have "C \<noteq> D" 
    using assms(1) assms(2) plgf_not_comm1 by blast
  hence "E \<noteq> F" 
    using assms(3) plgf_not_comm1 by blast
  obtain D' C' where "ParallelogramStrict C D D' C'" 
    using \<open>C \<noteq> D\<close> plgs_existence by fastforce
  hence "ParallelogramStrict A B C' D'" 
    using assms(1) assms(2) plgf_plgs_trans by blast
  have "ParallelogramStrict E F C' D'" 
    by (meson plgf_plgs_trans Tarski_Euclidean_axioms \<open>E \<noteq> F\<close> 
        \<open>ParallelogramStrict C D D' C'\<close> assms(3) plgf_sym)
  hence "ParallelogramStrict C' D' E F" 
    using plgs_sym by blast
  hence "Parallelogram A B F E" 
    using \<open>ParallelogramStrict A B C' D'\<close> plgs_pseudo_trans by blast
  thus ?thesis 
    by (meson ParallelogramFlat_def \<open>C \<noteq> D\<close> assms(2) assms(3) colx plg_col_plgf)
qed

lemma plg_pseudo_trans: 
  assumes "Parallelogram A B C D" and
    "Parallelogram C D E F" 
  shows "Parallelogram A B F E \<or> (A = B \<and> C = D \<and> E = F \<and> A = E)" 
proof (cases "A = B")
  case True
  thus ?thesis 
    by (metis assms(1) assms(2) plg_not_comm_R1 plg_sym plg_trivial1)
next
  case False
  hence "A \<noteq> B" 
    by auto
  hence "C \<noteq> D" 
    using False assms(1) plg_not_comm_R1 by blast
  hence "E \<noteq> F" 
    by (metis \<open>C \<noteq> D\<close> assms(2) plg_not_comm_R1)
  {
    assume "ParallelogramStrict A B C D"
    assume "ParallelogramStrict C D E F"
    have "Parallelogram A B F E" 
      using \<open>ParallelogramStrict A B C D\<close> \<open>ParallelogramStrict C D E F\<close> 
        plgs_pseudo_trans by blast
  }
  moreover
  {
    assume "ParallelogramStrict A B C D"
    assume "ParallelogramFlat C D E F"
    have "Parallelogram A B F E" 
      by (metis Parallelogram_strict_Parallelogram Plg_perm 
          plgf_plgs_trans plgs_sym  \<open>E \<noteq> F\<close> \<open>ParallelogramFlat C D E F\<close> 
          \<open>ParallelogramStrict A B C D\<close> plgf_sym)
  }
  moreover
  {
    assume "ParallelogramFlat A B C D"
    assume "ParallelogramStrict C D E F"
    have "Parallelogram A B F E" 
      by (meson False plgf_plgs_trans Parallelogram_strict_Parallelogram 
          \<open>ParallelogramFlat A B C D\<close> \<open>ParallelogramStrict C D E F\<close>)
  }
  moreover
  {
    assume "ParallelogramFlat A B C D"
    assume "ParallelogramFlat C D E F"
    have "ParallelogramFlat A B F E" 
      using False \<open>ParallelogramFlat A B C D\<close> \<open>ParallelogramFlat C D E F\<close> 
        plgf_plgf_plgf by blast
    hence "Parallelogram A B F E" 
      by (simp add: Parallelogram_def)
  }
  ultimately show ?thesis 
    by (metis Parallelogram_def assms(1) assms(2))
qed

lemma Square_Rhombus:
  assumes "Square A B C D" 
  shows "Rhombus A B C D" 
  using Rectangle_def Rhombus_def Square_def assms by presburger

lemma plgs_in_angle: 
  assumes "ParallelogramStrict A B C D"
  shows "D InAngle A B C" 
  by (meson ParallelogramStrict_def invert_one_side os_ts__inangle 
      assms plgs_comm2 plgs_one_side)

lemma par_par_cong_cong_parallelogram:
  assumes "B \<noteq> D" and
    "Cong A B C D" and
    "Cong B C D A" and
    "B C Par A D" and
    "A B Par C D" 
  shows "Parallelogram A B C D" 
  by (metis Plg_perm assms(1) assms(2) assms(3) assms(4) assms(5) 
      cong_right_commutativity par_cong_plg_2 plg_not_comm_R1)

lemma degenerated_rect_eq:
  assumes "Rectangle A B B C"
  shows "A = C" 
  by (meson assms l8_2 l8_7 rect_per1 rect_per4)

lemma rect_2_rect:
  assumes "A \<noteq> B" and
    "Rectangle A B C1 D1" and
    "Rectangle A B C2 D2"
  shows "Rectangle C1 D1 D2 C2" 
proof (cases "C1 = C2")
  case True
  obtain M where "M Midpoint A C1 \<and> M Midpoint B D1" 
    using Plg_def Rectangle_Plg assms(2) by presburger
  obtain M' where "M' Midpoint A C1 \<and> M' Midpoint B D2" 
    using Plg_def Rectangle_Plg True assms(3) by presburger
  have "Parallelogram C1 D2 D2 C1" 
    by (metis Rectangle_Parallelogram plg_trivial True assms(1) 
        assms(3) plg_not_comm_R2 rect_comm2)
  thus ?thesis 
    by (metis MidR_uniq_aux SymR_uniq_aux True 
        \<open>M' Midpoint A C1 \<and> M' Midpoint B D2\<close> 
        \<open>\<And>thesis. (\<And>M. M Midpoint A C1 \<and> M Midpoint B D1 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
        parallelogram_equiv_plg plg_cong_1 plg_cong_rectangle)
next
  case False
  hence "C1 \<noteq> C2" 
    by blast
  thus ?thesis 
  proof (cases "B = C1")
    case True
    thus ?thesis 
      using assms(2) assms(3) degenerated_rect_eq rect_comm2 by blast
  next
    case False
    hence "B \<noteq> C1"
      by auto
    show ?thesis 
    proof (cases "B = C2")
      case True
      thus ?thesis 
        by (metis assms(2) assms(3) degenerated_rect_eq rect_permut)
    next
      case False
      hence "B \<noteq> C2"
        by auto
      have "Parallelogram A B C1 D1" 
        using Rectangle_Parallelogram assms(2) by blast
      have "Parallelogram A B C2 D2" 
        using Rectangle_Parallelogram assms(3) by blast
      have "Per A B C1" 
        using assms(2) rect_per2 by blast
      hence "\<not> Col A B C1" 
        using \<open>B \<noteq> C1\<close> assms(1) l8_9 by blast
      have "Per A B C2" 
        using assms(3) rect_per2 by blast
      hence "\<not> Col A B C2" 
        using False assms(1) l8_9 by blast  
      have "Plg D2 C2 C1 D1" 
        by (meson \<open>Parallelogram A B C1 D1\<close> \<open>Parallelogram A B C2 D2\<close> 
            assms(1) parallelogram_to_plg plg_permut plg_pseudo_trans)
      moreover
      have "Per C1 C2 D2" 
      proof (cases "Coplanar A B C1 C2")
        case True
        show ?thesis 
        proof -
          have "A B Par D2 C2" 
            using False \<open>Parallelogram A B C2 D2\<close> assms(1) 
              par_right_comm plg_par by blast
          moreover have "A B Perp C2 C1" 
          proof -
            have "B C1 Perp A B" 
              using Perp_perm \<open>B \<noteq> C1\<close> \<open>Per A B C1\<close> 
                assms(1) per_perp by blast
            moreover have "A \<noteq> B" 
              by (simp add: assms(1))
            moreover have "B \<noteq> C1" 
              by (simp add: \<open>B \<noteq> C1\<close>)
            moreover have "Col B C1 C2" 
              using True \<open>Per A B C1\<close> \<open>Per A B C2\<close> calculation(2) 
                col_permutation_2 cop_per2__col coplanar_perm_3 l8_2 by blast
            moreover have "Col B C1 C1" 
              by (simp add: col_trivial_2)
            moreover have "C1 \<noteq> C2" 
              using \<open>C1 \<noteq> C2\<close> by auto
            ultimately show ?thesis using perp_col0 
              by presburger
          qed
          moreover have "Coplanar D2 C2 C2 C1" 
            using ncop_distincts by blast
          ultimately show ?thesis 
            using Perp_perm cop_par_perp__perp perp_per_2 by blast
        qed
      next
        case False
        have "Per B C2 D2" 
          using assms(3) rect_per3 by auto
        have "C2 \<noteq> D2" 
          using \<open>Parallelogram A B C2 D2\<close> assms(1) cong_identity plg_cong_1 by blast
        have "\<not> Col B C1 C2" 
          using False ncop__ncols by blast
        hence "B OrthAt B C1 C2 B A" 
          by (metis \<open>Per A B C1\<close> \<open>Per A B C2\<close> assms(1) col_trivial_3 
              l11_60_bis l8_2 l8_5 ncop__ncols)
        hence "C2 OrthAt B C1 C2 C2 D2" 
          by (meson \<open>B \<noteq> C2\<close> \<open>C2 \<noteq> D2\<close> \<open>Parallelogram A B C2 D2\<close> 
              \<open>Per B C2 D2\<close> l11_61_bis ncop_distincts ncoplanar_perm_12 
              parallelogram__coplanar per_perp)
        thus ?thesis 
          by (metis OrthAt_def col_trivial_2 ncop_distincts)
      qed
      ultimately
      show ?thesis 
        by (simp add: plg_per_rect rect_permut)
    qed
  qed
qed

lemma ncol123_plg__plgs:
  assumes "\<not> Col A B C" and
    "Parallelogram A B C D" 
  shows "ParallelogramStrict A B C D" 
  using ParallelogramFlat_def Parallelogram_def assms(1) assms(2) by presburger

lemma ncol124_plg__plgs:
  assumes "\<not> Col A B D" and
    "Parallelogram A B C D"
  shows "ParallelogramStrict A B C D" 
  by (meson assms(1) assms(2) mid_plgs not_col_permutation_4 plg_mid plgs_comm2)

lemma ncol134_plg__plgs:
  assumes "\<not> Col A C D" and
    "Parallelogram A B C D"
  shows "ParallelogramStrict A B C D" 
  by (meson assms(1) assms(2) col_permutation_2 ncol123_plg__plgs plg_sym plgs_sym)

lemma ncol234_plg__plgs:
  assumes "\<not> Col B C D" and
    "Parallelogram A B C D"
  shows "ParallelogramStrict A B C D" 
  by (meson assms(1) assms(2) col_permutation_2 ncol124_plg__plgs plg_sym plgs_sym)

lemma ncol123_plg__pars1234:
  assumes "\<not> Col A B C" and
    "Parallelogram A B C D" 
  shows "A B ParStrict C D" 
  by (meson assms(1) assms(2) mid_plgs plg_mid plgs_pars_1)

lemma ncol124_plg__pars1234:
  assumes "\<not> Col A B D" and
    "Parallelogram A B C D" 
  shows "A B ParStrict C D" 
  by (meson assms(1) assms(2) midpoint_par_strict plg_mid)

lemma ncol134_plg__pars1234:
  assumes "\<not> Col A C D" and
    "Parallelogram A B C D" 
  shows "A B ParStrict C D" 
  using Par_strict_perm Plg_perm assms(1) assms(2) col_permutation_3 
    ncol124_plg__pars1234 by blast

lemma ncol234_plg__pars1234:
  assumes "\<not> Col B C D" and
    "Parallelogram A B C D" 
  shows "A B ParStrict C D" 
  using Par_strict_perm Plg_perm assms(1) assms(2) ncol123_plg__pars1234 
    not_col_permutation_3 by blast

lemma ncol123_plg__pars1423:
  assumes "\<not> Col A B C" and
    "Parallelogram A B C D" 
  shows "A D ParStrict B C" 
  using Par_def assms(1) assms(2) not_col_distincts plg_par by blast

lemma ncol124_plg__pars1423:
  assumes "\<not> Col A B D" and
    "Parallelogram A B C D" 
  shows "A D ParStrict B C" 
  by (metis assms(1) assms(2) ncol124_plg__pars1234 not_col_distincts 
      par_strict_not_col_2 pars_par_pars plg_par)

lemma ncol134_plg__pars1423:
  assumes "\<not> Col A C D" and
    "Parallelogram A B C D" 
  shows "A D ParStrict B C" 
  by (meson assms(1) assms(2) ncol123_plg__pars1423 ncol134_plg__pars1234 
      par_strict_not_col_1)

lemma ncol234_plg__pars1423:
  assumes "\<not> Col B C D" and
    "Parallelogram A B C D" 
  shows "A D ParStrict B C" 
  by (metis assms(1) assms(2) ncol134_plg__pars1423 ncol234_plg__pars1234 
      not_col_distincts pars_par_pars plg_par)

lemma sac_plg:
  assumes "Saccheri A B C D"
  shows "Parallelogram A B C D" 
proof -
  have "A B ParStrict C D" 
    by (simp add: assms sac__pars1234)
  thus ?thesis 
    by (meson par_2_plg Tarski_Euclidean_axioms assms par_strict_not_col_1 
        par_strict_par sac__pars1423)
qed

lemma sac_rectangle: 
  assumes "Saccheri A B C D"
  shows "Rectangle A B C D" 
proof -
  have "Parallelogram A B C D" 
    by (meson assms sac_plg)
  thus ?thesis 
    by (simp add: Rectangle_def assms parallelogram_to_plg sac__cong)
qed

lemma exists_square: 
  assumes "A \<noteq> B" 
  shows "\<exists> C D.  Square A B C D"
proof -
  obtain C where "Per A B C" and "Cong B C A B" 
    using exists_cong_per by blast
  obtain D where "Saccheri B C D A" 
    by (metis Per_cases \<open>Cong B C A B\<close> \<open>Per A B C\<close> assms cong_diff_3 per__ex_saccheri)
  hence "Rectangle B C D A" 
    by (simp add: sac_rectangle)
  thus ?thesis 
    by (meson Cong_cases Square_def \<open>Cong B C A B\<close> rect_permut)
qed

(* Gupta Model *)

lemma euclidT:
  assumes "Bet A D T" and
    "Bet B D C" and 
    "A \<noteq> D" 
  shows "\<exists> X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y" 
proof -
  {
    assume "B \<noteq> D"
    {
      assume "Col A B C" 
      {
        assume "Bet A B C"
        {
          assume "A \<noteq> B"
          moreover have "Bet A B C" 
            using \<open>Bet A B C\<close> by blast
          moreover have "Bet A B T" 
            using assms(1) assms(2) between_exchange4 
              between_inner_transitivity calculation(2) by blast
          moreover have "Bet B C T \<longrightarrow> ?thesis" 
            using calculation(3) not_bet_distincts by blast
          moreover have "Bet B T C \<longrightarrow> ?thesis" 
            using not_bet_distincts by blast
          ultimately have ?thesis using l5_2 by blast
        }
        hence ?thesis 
          using between_symmetry between_trivial by blast
      }
      moreover have "Bet B C A \<longrightarrow> ?thesis" 
        using assms(1) assms(2) assms(3) tarski_s_parallel_postulate by presburger
      moreover have "Bet C A B \<longrightarrow> ?thesis" 
        using assms(1) assms(2) assms(3) tarski_s_parallel_postulate by presburger
      ultimately have ?thesis 
        using Col_def \<open>Col A B C\<close> by blast
    }
    moreover
    {
      assume "\<not> Col A B C" 
      {
        {
          assume "D \<noteq> C"
          hence ?thesis 
            using assms(1) assms(2) assms(3) tarski_s_parallel_postulate by blast
        }
        hence ?thesis 
          using assms(1) not_bet_distincts by blast
      }
      hence ?thesis 
        by blast
    }
    ultimately have ?thesis 
      by blast
  }
  thus ?thesis 
    using assms(1) between_symmetry between_trivial by blast
qed

end
end