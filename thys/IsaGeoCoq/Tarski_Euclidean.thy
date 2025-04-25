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

  (* Gabriel Braun February 2013 *)

lemma eqv_refl:
  shows "A B EqV A B" 
  using EqV_def plg_trivial by blast

lemma eqv_sym: 
  assumes "A B EqV C D"
  shows "C D EqV A B" 
  using EqV_def Plg_perm assms by blast

lemma eqv_trans: 
  assumes "A B EqV C D" and
    "C D EqV E F"
  shows "A B EqV E F"
proof -
  {
    assume "Parallelogram A B D C"
    hence "Parallelogram C D F E \<longrightarrow> ?thesis" 
      using EqV_def plg_comm2 plg_pseudo_trans by blast
    moreover have "C = D \<and> F = E \<longrightarrow> ?thesis" 
      by (metis assms(1) calculation plg_trivial1)
    ultimately have ?thesis 
      using EqV_def assms(2) by blast
  }
  moreover have "A = B \<and> C = D \<longrightarrow> ?thesis" 
    using assms(2) calculation plg_trivial1 by force
  ultimately show ?thesis 
    using EqV_def assms(1) by force
qed

lemma eqv_comm: 
  assumes "A B EqV C D"
  shows "B A EqV D C" 
  by (metis EqV_def assms eqv_sym plg_sym)

lemma vector_construction: 
  shows "\<exists> D. A B EqV C D" 
  by (metis EqV_def eqv_comm plg_existence)

lemma vector_construction_uniqueness:
  assumes "A B EqV C D" and
    "A B EqV C D'" 
  shows "D = D'" 
proof -
  {
    assume "Parallelogram A B D C"
    hence "Parallelogram A B D' C \<longrightarrow> ?thesis" 
      by (meson plg_comm2 plg_uniqueness)
    moreover have "A = B \<and> C = D' \<longrightarrow> ?thesis" 
      using \<open>Parallelogram A B D C\<close> cong_reverse_identity plg_cong by blast
    ultimately have ?thesis 
      using EqV_def assms(2) by force
  }
  moreover have "A = B \<and> C = D \<longrightarrow> ?thesis" 
    by (metis EqV_def assms(2) cong_reverse_identity plg_cong)
  ultimately show ?thesis 
    using EqV_def assms(1) by force
qed

lemma null_vector: 
  assumes "A A EqV B C"
  shows "B = C" 
  using EqV_def assms vector_construction_uniqueness by blast

lemma vector_uniqueness: 
  assumes "A B EqV A C"
  shows "B = C" 
  using assms eqv_refl vector_construction_uniqueness by blast

lemma eqv_trivial: 
  shows "A A EqV B B" 
  by (simp add: EqV_def)

lemma eqv_permut:
  assumes "A B EqV C D" 
  shows "A C EqV B D" 
  using EqV_def assms eqv_refl eqv_sym plg_permut by presburger

lemma eqv_par:
  assumes "A \<noteq> B" and
    "A B EqV C D"
  shows "A B Par C D" 
  by (metis EqV_def Par_cases assms(1) assms(2) eqv_comm par_reflexivity plg_par)

lemma eqv_opp_null:
  assumes "A B EqV B A"
  shows "A = B" 
  by (meson EqV_def assms plg_not_comm plg_trivial)

lemma eqv_sum:
  assumes "A B EqV A' B'" and
    "B C EqV B' C'"
  shows "A C EqV A' C'" 
  by (meson assms(1) assms(2) eqv_permut eqv_trans)

lemma null_sum:
  shows "A B B A SumV C C" 
  using EqV_def SumV_def eqv_permut null_vector by blast

lemma chasles:
  shows "A B B C SumV A C" 
  using SumV_def eqv_permut eqv_refl null_vector by blast

lemma eqv_mid :
  assumes "A B EqV B C"
  shows "B Midpoint A C" 
  using EqV_def assms l7_3_2 plg_comm2 plg_mid_2 by blast

lemma mid_eqv:
  assumes "A Midpoint B C"
  shows "B A EqV A C" 
  by (metis EqV_def assms midpoint_distinct_1 plg_existence plg_mid_2)

lemma sum_sym:
  assumes "A B C D SumV E F"
  shows "C D A B SumV E F"
proof -
  {
    fix D'0
    assume "A B EqV D D'0"
    obtain D' where "C D EqV B D'" 
      using vector_construction by blast
    have "A D' EqV E F" 
      using SumV_def \<open>C D EqV B D'\<close> assms by blast
    have "C B EqV D D'" 
      by (simp add: \<open>C D EqV B D'\<close> eqv_permut)
    have "A D EqV B D'0" 
      by (simp add: \<open>A B EqV D D'0\<close> eqv_permut)
    have "C D'0 EqV E F"
    proof (cases "A = D'0")
      case True
      have "A Midpoint B D" 
        using True \<open>A B EqV D D'0\<close> eqv_comm eqv_mid by blast
      have "Parallelogram C D D' B \<longrightarrow> ?thesis" 
        using Plg_perm True \<open>A D' EqV E F\<close> \<open>A Midpoint B D\<close> eqv_trans mid_eqv plg_mid_2 by blast
      moreover have "C = D \<and> B = D' \<longrightarrow> ?thesis" 
        using \<open>A B EqV D D'0\<close> \<open>A D' EqV E F\<close> eqv_sym eqv_trans by blast
      ultimately show ?thesis 
        using EqV_def \<open>C D EqV B D'\<close> by blast
    next
      case False
      have "Parallelogram C D D' B \<longrightarrow> ?thesis" 
      proof -
        {
          assume "Parallelogram A B D'0 D"
          obtain M0 where "M0 Midpoint C D'" and "M0 Midpoint D B" 
            by (metis EqV_def MidR_uniq_aux \<open>C D EqV B D'\<close> plg_mid_2)
          obtain M1 where "M1 Midpoint A D'0" and "M1 Midpoint B D" 
            using \<open>Parallelogram A B D'0 D\<close> plg_mid by blast
          have "M1 = M0" 
            using \<open>M0 Midpoint D B\<close> \<open>M1 Midpoint B D\<close> l7_17_bis by auto
          have "A \<noteq> D'0 \<or> D' \<noteq> C" 
            by (simp add: False)
          hence "Parallelogram A D' D'0 C"
            using mid_plg [where ?M = "M0"] \<open>M0 Midpoint C D'\<close> \<open>M1 = M0\<close> \<open>M1 Midpoint A D'0\<close> l7_2 by presburger
          hence "?thesis" 
            by (meson EqV_def \<open>A D' EqV E F\<close> eqv_sym eqv_trans)
        }
        moreover have "A \<noteq> B \<and> D'0 \<noteq> B \<longrightarrow> ?thesis" 
          using EqV_def \<open>A B EqV D D'0\<close> calculation by blast
        ultimately show ?thesis 
          using EqV_def False \<open>A B EqV D D'0\<close> plg_trivial1 by blast
      qed
      moreover have "C = D \<and> B = D' \<longrightarrow> ?thesis" 
        using \<open>A B EqV D D'0\<close> \<open>A D' EqV E F\<close> eqv_sym eqv_trans by blast
      ultimately show ?thesis 
        using EqV_def \<open>C D EqV B D'\<close> by blast
    qed
  }
  thus ?thesis using SumV_def 
    by auto
qed

lemma opposite_sum:
  assumes "A B C D SumV E F"
  shows "B A D C SumV F E" 
proof -
  {
    fix D0
    assume "D C EqV A D0"
    obtain D' where "C D EqV B D'" 
      using vector_construction by blast
    hence "A D' EqV E F" 
      using SumV_def assms by blast
    have "D' B EqV A D0" 
      using \<open>C D EqV B D'\<close> \<open>D C EqV A D0\<close> eqv_comm eqv_sym eqv_trans by blast
    hence "B D0 EqV F E" 
      by (meson \<open>A D' EqV E F\<close> eqv_comm eqv_permut eqv_trans)
  }
  thus ?thesis 
    using SumV_def by blast
qed

lemma null_sum_eq:
  assumes "A B B C SumV D D"
  shows "A = C" 
proof -
  obtain D' where "B C EqV B D'" 
    using vector_construction by blast
  hence "A D' EqV D D" 
    using SumV_def assms by blast
  have "A = D'" 
    using \<open>A D' EqV D D\<close> eqv_sym null_vector by blast
  thus ?thesis 
    using \<open>B C EqV B D'\<close> vector_uniqueness by blast
qed

lemma is_to_ise:
  assumes "A B C D SumV E F"
  shows "A B C D SumVExists E F" 
  by (meson SumVExists_def SumV_def assms eqv_sym vector_construction)

lemma ise_to_is:
  assumes "A B C D SumVExists E F"
  shows "A B C D SumV E F" 
proof -
  obtain D' where "B D' EqV C D" 
    using SumVExists_def assms by blast
  thus ?thesis 
    by (metis SumVExists_def SumV_def assms eqv_sym vector_construction_uniqueness)
qed

lemma sum_exists:
  shows "\<exists> E F. A B C D SumV E F" 
  by (metis SumV_def vector_construction vector_construction_uniqueness)

lemma sum_uniqueness_pappus: 
(* ROLAND Collision Tarski_Pappus et Chap14 sum_uniqueness
  sum_uniqueness ---> sum_uniqueness_pappus *)
  assumes "A B C D SumV E F" and
    "A B C D SumV E' F'"
  shows "E F EqV E' F'" 
  by (metis SumV_def assms(1) assms(2) eqv_sym eqv_trans vector_construction)

lemma same_dir_refl: 
  shows "A B SameDir A B" 
proof (cases "A = B")
  case True
  thus ?thesis 
    using SameDir_def by force
next
  case False
  thus ?thesis 
    using SameDir_def by (metis eqv_refl out_trivial)
qed

lemma same_dir_ts:
  assumes "A B SameDir C D"
  shows "\<exists> M. Bet A M D \<and> Bet B M C" 
proof -
  have "(A = B \<and> C = D) \<longrightarrow> ?thesis" 
    using between_trivial by blast
  moreover {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    moreover {
      assume "Parallelogram A B D' C"
      obtain M where "M Midpoint A D'" and "M Midpoint B C" 
        using \<open>Parallelogram A B D' C\<close> plg_mid by blast
      {
        assume "ParallelogramStrict A B D' C"
        have "B C TS A D'" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "A D' TS B C" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "B \<noteq> C" 
          using \<open>A D' TS B C\<close> ts_distincts by presburger
        have "\<not> Col B C D'" 
          using \<open>ParallelogramStrict A B D' C\<close> col_permutation_5 plgs_not_col by blast
        have "B C OS D' D" 
          using \<open>\<not> Col B C D'\<close> calculation(1) l6_6 not_col_distincts out_one_side_1 by blast
        have "B C TS A D" 
          using \<open>B C OS D' D\<close> \<open>B C TS A D'\<close> l9_2 l9_8_2 by blast
        have "\<not> Col A B C" 
          using TS_def \<open>B C TS A D'\<close> by blast
        have "A B ParStrict D' C" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_par_strict)
        have "A C ParStrict B D'" 
          using \<open>ParallelogramStrict A B D' C\<close> plgs_par_strict by blast
        have "A \<noteq> B" 
          using \<open>\<not> Col A B C\<close> not_col_distincts by blast
        have "C D Par A B" 
          by (metis Out_cases \<open>B C TS A D\<close> \<open>\<exists>D'. C Out D D' \<and> A B EqV C D'\<close> 
              eqv_par out_col par_col_par par_symmetry ts_distincts)
        have "A B ParStrict C D" 
          using Col_cases Par_def Par_strict_cases \<open>C D Par A B\<close> \<open>\<not> Col A B C\<close> by blast
        obtain T where "Col T B C" and "Bet A T D" 
          using TS_def \<open>B C TS A D\<close> by blast
        hence "Col A B T \<longrightarrow> ?thesis"  
          by (metis \<open>\<not> Col A B C\<close> between_trivial2 col_trivial_2 colx)
        moreover 
        {
          assume "\<not> Col A B T"
          have "Col C D T \<longrightarrow> ?thesis" 
            by (metis TS_def \<open>A B ParStrict C D\<close> \<open>B C TS A D\<close> \<open>Bet A T D\<close> 
                \<open>Col T B C\<close> bet_col1 between_trivial l6_16_1 par_strict_not_col_3)
          moreover 
          {
            assume "\<not> Col C D T"
            have "Bet T B C \<longrightarrow> ?thesis" 
              using Par_strict_cases \<open>A B ParStrict C D\<close> \<open>Bet A T D\<close> 
                \<open>Col T B C\<close> \<open>\<not> Col A B C\<close> \<open>\<not> Col A B T\<close> between_trivial 
                between_trivial2 impossible_case_4_2 not_col_permutation_2 by blast
            moreover 
            {
              assume "Bet B C T"
              have "C D OS T A" 
                by (metis \<open>Bet A T D\<close> \<open>\<not> Col C D T\<close> bet_out_1 not_col_distincts out_one_side_1)
              have "C D OS T B"  
                using \<open>A B ParStrict C D\<close> \<open>C D OS T A\<close> one_side_transitivity 
                  pars__os3412 by blast
              moreover have "C D TS T B" 
                using \<open>B \<noteq> C\<close> \<open>Bet B C T\<close> \<open>\<not> Col C D T\<close> bet__ts 
                  between_symmetry by presburger
              ultimately have False 
                using l9_9_bis by auto
              hence ?thesis 
                by blast
            }
            moreover have "Bet C T B \<longrightarrow> ?thesis" 
              using \<open>Bet A T D\<close> between_symmetry by blast
            ultimately have ?thesis 
              using Col_def \<open>Col T B C\<close> by blast
          }
          ultimately have ?thesis 
            by blast
        }
        ultimately have ?thesis 
          by blast
      }
      moreover 
      {
        assume "ParallelogramFlat A B D' C"
        hence "Bet C D' A \<and> Bet D' A B \<or> Bet C A D' \<and> Bet A D' B \<or> 
                Bet A C B \<and> Bet C B D' \<or> Bet A B C \<and> Bet B C D'" 
          by (simp add: plgf_bet)
        have "A = D' \<longrightarrow> ?thesis" 
          by (metis Midpoint_def 
              \<open>\<And>thesis. (\<And>M. \<lbrakk>M Midpoint A D'; M Midpoint B C\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
              between_identity not_bet_distincts)
        moreover 
        {
          assume "A \<noteq> D'"
          {
            assume "B = C"
            have "A = D' \<or> B Midpoint A D'" 
              using \<open>A B EqV C D'\<close> \<open>B = C\<close> eqv_mid by auto
            moreover have "A = D' \<longrightarrow> ?thesis" 
              using \<open>A \<noteq> D'\<close> by blast
            moreover 
            {
              assume "B Midpoint A D'"
              have "Bet B D D' \<longrightarrow> Bet A B D" 
                using \<open>B Midpoint A D'\<close> between_inner_transitivity midpoint_bet by blast
              moreover have "Bet B D' D \<longrightarrow> Bet A B D" 
                by (metis \<open>B Midpoint A D'\<close> midpoint_bet midpoint_not_midpoint 
                    outer_transitivity_between)
              ultimately have "Bet A B D" 
                using Out_def \<open>B = C\<close> \<open>C Out D D'\<close> by blast
              hence ?thesis 
                using not_bet_distincts by blast  
            }
            ultimately have ?thesis 
              by blast
          }
          moreover 
          {
            assume "B \<noteq> C"
            have "Bet C D' A \<and> Bet D' A B \<longrightarrow> ?thesis" 
              by (metis Bet_cases \<open>A \<noteq> D'\<close> between_trivial2 outer_transitivity_between2)
            moreover have "Bet C A D' \<and> Bet A D' B \<longrightarrow> ?thesis" 
              by (meson Bet_cases \<open>A \<noteq> D'\<close> between_trivial2 outer_transitivity_between)
            moreover  
            {
              assume "Bet A C B" and "Bet C B D'"
              have "Bet A C D" 
                by (metis \<open>A B EqV C D'\<close> \<open>B \<noteq> C\<close> \<open>Bet A C B\<close> \<open>Bet C B D'\<close> 
                    \<open>\<exists>D'. C Out D D' \<and> A B EqV C D'\<close> bet_out bet_out_out_bet l6_6 
                    not_bet_distincts vector_construction_uniqueness)
              moreover have "Bet B C C" 
                by (simp add: between_trivial)
              ultimately have ?thesis 
                by blast
            }
            moreover have "Bet A B C \<and> Bet B C D' \<longrightarrow> ?thesis" 
              by (meson Out_cases \<open>B \<noteq> C\<close> \<open>C Out D D'\<close> bet_out_1 bet_out_out_bet l5_3)
            ultimately have ?thesis 
              using \<open>Bet C D' A \<and> Bet D' A B \<or> Bet C A D' \<and> 
                       Bet A D' B \<or> Bet A C B \<and> Bet C B D' \<or> Bet A B C \<and> Bet B C D'\<close> 
              by fastforce
          }
          ultimately have ?thesis 
            by blast
        }
        ultimately have ?thesis 
          by blast
      }
      ultimately have ?thesis 
        using Parallelogram_def \<open>Parallelogram A B D' C\<close> by blast
    }
    moreover have "(A = B \<and> C = D') \<longrightarrow> ?thesis" 
      using calculation(1) out_diff2 by blast
    ultimately have ?thesis 
      using EqV_def by blast
  }
  ultimately show ?thesis 
    using SameDir_def assms by presburger
qed

lemma one_side_col_out:
  assumes "Col A X Y" and
    "A B OS X Y" 
  shows "A Out X Y" 
  using assms(1) assms(2) col_one_side_out by force

lemma par_ts_same_dir:
  assumes "A B ParStrict C D" and
    "\<exists> M. Bet A M D \<and> Bet B M C"
  shows "A B SameDir C D" 
proof -
  obtain M where "Bet A M D" and "Bet B M C" 
    using assms(2) by force
  obtain D' where "A B EqV C D'" 
    using vector_construction by blast
  have "A \<noteq> B" 
    using assms(1) par_strict_neq1 by blast
  have "C \<noteq> D" 
    using assms(1) par_strict_distinct by blast
  have "A \<noteq> M" 
    using NCol_perm \<open>Bet B M C\<close> assms(1) bet_col par_strict_not_col_1 by blast
  have "B = D' \<longrightarrow> C Out D D'" 
    by (metis Col_def EqV_def Plg_perm \<open>A B EqV C D'\<close> assms(1) 
        not_bet_distincts par_strict_not_col_3 plg_not_comm)
  moreover 
  {
    assume "B \<noteq> D'"
    {
      assume "Parallelogram A B D' C"
      have "A B Par D' C" 
        using \<open>A \<noteq> B\<close> \<open>B \<noteq> D'\<close> \<open>Parallelogram A B D' C\<close> plg_par by auto
      have "Col C D D'" 
        by (metis Par_strict_cases \<open>Parallelogram A B D' C\<close> assms(1) 
            col_permutation_4 ncol124_plg__pars1234 par_id_1 
            par_strict_not_col_1 par_strict_trans)
      {
        assume "ParallelogramStrict A B D' C"
        have "A D' TS B C" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "B C TS A D'" 
          by (simp add: \<open>ParallelogramStrict A B D' C\<close> plgs_two_sides)
        have "B C TS A D" 
          by (metis NCol_perm Par_strict_cases assms(1) assms(2) bet_col 
              l9_18_R2 par_strict_not_col_2)
        have "B C OS D D'" 
        proof (rule l9_8_1 [where ?C = "A"])
          show "B C TS D A" 
            using \<open>B C TS A D\<close> l9_2 by blast
          show "B C TS D' A" 
            by (simp add: \<open>B C TS A D'\<close> l9_2)
        qed
        hence "C Out D D'" 
          using one_side_col_out [where ?B = "B"] \<open>B C OS D D'\<close> calculation 
            invert_one_side \<open>Col C D D'\<close> by blast
      }
      moreover have "ParallelogramFlat A B D' C \<longrightarrow> C Out D D'" 
        using ParallelogramFlat_def assms(1) par_strict_not_col_1 by force
      ultimately have "C Out D D'" 
        using Parallelogram_def \<open>Parallelogram A B D' C\<close> by blast
    }
    moreover have "(A = B \<and> C = D') \<longrightarrow> C Out D D'" 
      by (simp add: \<open>A \<noteq> B\<close>)
    ultimately have "C Out D D'" 
      using EqV_def \<open>A B EqV C D'\<close> by presburger
  }
  ultimately have "C Out D D'" 
    by blast
  hence "\<exists> D'. C Out D D' \<and> A B EqV C D'" 
    using \<open>A B EqV C D'\<close> by blast
  thus ?thesis 
    by (simp add: SameDir_def)
qed

lemma same_dir_out: 
  assumes "A B SameDir A C"
  shows "A Out B C \<or> (A = B \<and> A = C)"  
proof -
  have "A = B \<and> A = C \<or> (\<exists> D'. A Out C D' \<and> A B EqV A D')" 
    using SameDir_def assms by presburger
  moreover
  have "(\<exists> D'. A Out C D' \<and> A B EqV A D') \<longrightarrow> ?thesis" 
    using l6_6 vector_uniqueness by blast
  ultimately show ?thesis
    by blast
qed

lemma same_dir_out1: 
  assumes "A B SameDir B C"
  shows "A Out B C \<or> (A = B \<and> A = C)"  
proof -
  have "A = B \<and> B = C \<or> (\<exists> D'. B Out C D' \<and> A B EqV B D')" 
    using SameDir_def assms by presburger
  moreover have "(\<exists> D'. B Out C D' \<and> A B EqV B D') \<longrightarrow> ?thesis" 
    by (metis assms bet_neq23__neq bet_out_1 between_symmetry same_dir_out same_dir_ts)
  ultimately show ?thesis 
    by blast
qed

lemma same_dir_null:
  assumes "A A SameDir B C"
  shows "B = C"  
proof -
  have "A = A \<and> B = C \<or> (\<exists> D'. B Out C D' \<and> A A EqV B D')" 
    using SameDir_def assms by presburger
  moreover have "(\<exists> D'. B Out C D' \<and> A A EqV B D') \<longrightarrow> ?thesis" 
    using null_vector out_distinct by blast
  ultimately show ?thesis 
    by blast
qed

lemma plgs_out_plgs:
  assumes "ParallelogramStrict A B C D" and
    "A Out B B'" and
    "D Out C C'" and
    "Cong A B' D C'" 
  shows "ParallelogramStrict A B' C' D" 
proof -
  have "A D OS C B" 
    using assms(1) plgs_comm2 plgs_one_side plgs_permut by blast
  have "C B OS A D" 
    using assms(1) plgs_comm2 plgs_one_side plgs_permut by blast
  have "A \<noteq> B'"       
    using assms(2) out_distinct by blast
  have "D \<noteq> C'" 
    using assms(3) out_distinct by blast
  have "A B ParStrict C D" 
    by (simp add: assms(1) plgs_pars_1)
  have "A B' Par D C'"
  proof (rule par_col_par_2 [where ?B ="B"])
    show "A \<noteq> B'"       
      by (simp add: \<open>A \<noteq> B'\<close>)
    show "Col A B B'" 
      by (simp add: assms(2) out_col)
    show "A B Par D C'"
      by (metis Col_def Out_def \<open>A B ParStrict C D\<close> assms(3) 
          not_col_distincts par_col2_par par_strict_par)
  qed
  moreover have "A B ParStrict D C' \<longrightarrow> A B' ParStrict D C'" 
    by (metis Col_cases Par_def calculation par_strict_not_col_3)
  ultimately have "A B' ParStrict D C'" 
    using Par_strict_perm \<open>A B ParStrict C D\<close> \<open>D \<noteq> C'\<close> assms(3) 
      out_col par_strict_col_par_strict by blast
  have "A D OS B B'" 
    using \<open>A D OS C B\<close> assms(2) one_side_symmetry one_side_transitivity 
      out_out_one_side by blast
  have "A D OS C C'" 
    using \<open>A D OS C B\<close> assms(3) col123__nos invert_one_side out_one_side by blast
  have "A D OS B' C'" 
    by (meson \<open>A D OS B B'\<close> \<open>A D OS C B\<close> \<open>A D OS C C'\<close> 
        one_side_symmetry one_side_transitivity)
  then obtain M where "M Midpoint A C'" and "M Midpoint B' D" 
    using par_cong_mid_os \<open>A B' ParStrict D C'\<close> assms(4) by blast
  thus ?thesis using mid_plgs 
    using Par_strict_cases \<open>A B' ParStrict D C'\<close> par_strict_not_col_1 by blast
qed

lemma plgs_plgs_bet:
  assumes "ParallelogramStrict A B C D" and
    "Bet A B B'" and
    "ParallelogramStrict A B' C' D"
  shows "Bet D C C'" 
proof -
  have "A B ParStrict C D \<and> A D ParStrict B C" 
    by (simp add: assms(1) plgs_par_strict)
  hence "A B Par C D" 
    by (simp add: par_strict_par)
  moreover have "A B Par C' D" 
    using par_col_par_2 [where ?B = "B'"] 
    by (metis Col_def assms(1) assms(2) assms(3) between_symmetry 
        par_strict_par plgs_comm2 plgs_not_comm_1 plgs_pars_1)
  ultimately have "Col C' C D \<and> Col D C D"
    using parallel_uniqueness [where ?A1.0 ="A" and ?A2.0="B"  and ?P="D"]
    by (metis col_trivial_3)
  hence "Col C' C D"
    by simp
  moreover have "Bet C' C D \<longrightarrow> ?thesis" 
    using between_symmetry by blast
  moreover
  {
    assume "Bet C D C'"
    have "B C OS D A" 
      by (simp add: assms(1) plgs_one_side plgs_permut)
    have "D A OS B C" 
      by (simp add: assms(1) plgs_one_side plgs_permut)
    have "B' C' OS D A" 
      by (simp add: assms(3) plgs_one_side plgs_permut)
    have "D A OS B' C'" 
      by (simp add: assms(3) plgs_one_side plgs_permut)
    have "D A OS B' B"
    proof (rule out_one_side_1 [where ?X = "A"])
      show "\<not> Col D A B'" 
        using \<open>D A OS B' C'\<close> col123__nos by blast
      show "Col D A A" 
        by (simp add: col_trivial_2)
      show "A Out B' B" 
        by (metis \<open>A B Par C' D\<close> assms(2) bet_out l6_6 par_neq1)
    qed
    hence "D A OS B C'" 
      using \<open>D A OS B' C'\<close> one_side_symmetry one_side_transitivity by blast
    hence "D A OS C C'" 
      using \<open>D A OS B C\<close> one_side_symmetry one_side_transitivity by blast
    moreover have "D A TS C C'" 
      using \<open>Bet C D C'\<close> \<open>D A OS C C'\<close> l9_17 os_distincts by blast
    ultimately have False 
      by (simp add: l9_9_bis)
  } 
  moreover 
  {
    assume "Bet D C' C"
    have "ParallelogramStrict B C D A" 
      by (simp add: assms(1) plgs_permut)
    have "ParallelogramStrict D A B' C'" 
      by (simp add: assms(3) plgs_permut)
    have "C = C' \<longrightarrow> ?thesis" 
      using \<open>Bet D C' C\<close> by blast
    moreover 
    {
      assume "C \<noteq> C'"
      have "Parallelogram B C C' B'" 
        using \<open>ParallelogramStrict B C D A\<close> \<open>ParallelogramStrict D A B' C'\<close> 
          plgs_pseudo_trans by auto
      hence "ParallelogramStrict B C C' B'" 
        by (metis NCol_perm \<open>C \<noteq> C'\<close> \<open>Col C' C D \<and> Col D C D\<close> assms(3) 
            colx ncol234_plg__plgs not_col_distincts plgs_not_col)
      have "B C OS C' B'" 
        by (simp add: \<open>ParallelogramStrict B C C' B'\<close> plgs_one_side)
      have "C' B' OS B C" 
        by (simp add: \<open>ParallelogramStrict B C C' B'\<close> plgs_one_side)
      have "B C OS D A" 
        using \<open>ParallelogramStrict B C D A\<close> plgs_one_side by blast
      have "D A OS B C" 
        using \<open>ParallelogramStrict B C D A\<close> plgs_one_side by blast
      have "B C TS A B'" 
        by (metis \<open>A B ParStrict C D \<and> A D ParStrict B C\<close> \<open>B C OS C' B'\<close> assms(2) 
            bet__ts os_distincts par_strict_not_col_3)
      moreover have "B C OS C' D" 
        by (metis \<open>B C OS C' B'\<close> \<open>Bet D C' C\<close> bet_out_1 col123__nos invert_one_side 
            os_distincts out_one_side)
      have "B C OS A B'" 
        by (meson \<open>B C OS C' B'\<close> \<open>B C OS C' D\<close> \<open>B C OS D A\<close> one_side_symmetry 
            one_side_transitivity)
      ultimately have ?thesis 
        by (simp add: l9_9)
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis
    using Col_def by blast
qed

lemma plgf_plgf_bet:
  assumes "ParallelogramFlat A B C D" and
    "Bet A B B'" and
    "ParallelogramFlat A B' C' D"
  shows "Bet D C C'" 
proof (cases "A = B") 
  case True
  thus ?thesis 
    using assms(1) cong_reverse_identity not_bet_distincts plgf_cong by blast
next
  case False
  hence "A \<noteq> B" 
    by blast
  obtain P where "\<not> Col A B P" 
    using False not_col_exists by blast
  obtain Q where "Parallelogram A B P Q" 
    using False plg_existence by blast
  have "ParallelogramStrict A B P Q" 
    using \<open>Parallelogram A B P Q\<close> \<open>\<not> Col A B P\<close> not_col_distincts 
      parallel_2_plg plg_par by blast
  have "ParallelogramStrict C D Q P" 
  proof (rule plgf_plgs_trans [where ?C = "A" and ?D = "B"])
    show "C \<noteq> D" 
      using False assms(1) plgf_not_comm1 by blast
    show "ParallelogramFlat C D A B" 
      by (simp add: assms(1) plgf_sym)
    show "ParallelogramStrict A B P Q" 
      by (simp add: \<open>ParallelogramStrict A B P Q\<close>)
  qed
  have "A \<noteq> B'" 
    using False assms(2) between_identity by blast
  obtain P' where "A B' EqV Q P'" 
    using vector_construction by blast
  {
    assume "Parallelogram A B' P' Q"
    have "B \<noteq> P" 
      using \<open>\<not> Col A B P\<close> col_trivial_2 by blast
    have "B' \<noteq> P'" 
      by (metis \<open>Parallelogram A B' P' Q\<close> \<open>ParallelogramStrict A B P Q\<close>
          cong_identity_inv plg_cong plgs_diff)
    have "A B' Par P Q" 
      by (meson False \<open>A \<noteq> B'\<close> \<open>B \<noteq> P\<close> \<open>Parallelogram A B P Q\<close> assms(2) 
          bet_col par_col_par_2 plg_par)
    have "Col P' P Q \<and> Col Q P Q" 
      using parallel_uniqueness by (metis Par_cases \<open>A B' EqV Q P'\<close> 
          \<open>A B' Par P Q\<close> \<open>A \<noteq> B'\<close> eqv_par par_id_4 par_trans)
    hence "Col P' P Q" 
      by simp
    have "ParallelogramStrict A B' P' Q" 
      by (meson \<open>A \<noteq> B'\<close> \<open>Parallelogram A B' P' Q\<close> \<open>ParallelogramStrict A B P Q\<close> 
          assms(2) bet_col col_trivial_3 colx ncol124_plg__plgs 
          parallelogram_strict_not_col_4)
    have "ParallelogramStrict D C' P' Q"
      using plgf_plgs_trans [where ?C ="B'" and ?D="A"] 
      by (metis \<open>A \<noteq> B'\<close> \<open>ParallelogramStrict A B' P' Q\<close> assms(3) 
          plgf_not_comm1 plgf_plgs_trans plgf_sym plgs_comm2)
    have "Bet Q P P'" 
      using plgs_plgs_bet \<open>ParallelogramStrict A B P Q\<close> 
        \<open>ParallelogramStrict A B' P' Q\<close> assms(2) by blast
    have ?thesis 
      using plgs_plgs_bet [where ?A="Q" and ?B="P" and ?B'="P'"] \<open>Bet Q P P'\<close> 
        \<open>ParallelogramStrict C D Q P\<close> \<open>ParallelogramStrict D C' P' Q\<close> 
        plgs_comm2 plgs_sym by blast
  }
  thus ?thesis 
    using EqV_def \<open>A B' EqV Q P'\<close> \<open>A \<noteq> B'\<close> by blast
qed

lemma plg_plg_bet:
  assumes "Parallelogram A B C D" and
    "Bet A B B'" and
    "Parallelogram A B' C' D"
  shows "Bet D C C'" 
proof (cases "A = B")
  case True
  thus ?thesis 
    using assms(1) cong_reverse_identity not_bet_distincts plg_cong by blast
next
  case False
  hence "A \<noteq> B"
    by blast
  show ?thesis 
  proof (cases "B = C")
    case True
    thus ?thesis 
      by (metis assms(1) assms(2) assms(3) cong_diff cong_reverse_identity plg_cong)
  next
    case False
    hence "B \<noteq> C"
      by blast
    have "A \<noteq> B'" 
      using \<open>A \<noteq> B\<close> assms(2) between_identity by blast
    have "B' \<noteq> C'" 
      by (metis False Plg_perm assms(1) assms(3) plg_not_comm)
    have "A B Par C D \<and> A D Par B C" 
      by (simp add: False \<open>A \<noteq> B\<close> assms(1) plg_par)
    have "A B' Par C' D \<and> A D Par B' C'" 
      by (simp add: \<open>A \<noteq> B'\<close> \<open>B' \<noteq> C'\<close> assms(3) plg_par_1 plg_par_2)
    have "A B Par C' D" 
      using Bet_cases Col_def \<open>A B' Par C' D \<and> A D Par B' C'\<close> \<open>A \<noteq> B\<close> 
        assms(2) par_col_par_2 by blast
    have "Col C' C D \<and> Col D C D" 
      using \<open>A B Par C D \<and> A D Par B C\<close> \<open>A B Par C' D\<close> col_trivial_3 
        parallel_uniqueness by blast
    {
      assume "ParallelogramStrict A B C D" and "ParallelogramFlat A B' C' D"
      hence False 
        by (metis Col_cases ParallelogramFlat_def \<open>A B' Par C' D \<and> A D Par B' C'\<close> 
            \<open>Col C' C D \<and> Col D C D\<close> colx par_distincts 
            parallelogram_strict_not_col_3 plgf_sym)
    }
    moreover 
    {
      assume "ParallelogramStrict A B C D" and "ParallelogramStrict A B' C' D"
      hence ?thesis 
        using plgs_plgs_bet [where ?A = "A" and ?B = "B" and ?B'= "B'"] assms(2) by blast
    }
    moreover 
    have "ParallelogramFlat A B C D \<and> ParallelogramFlat A B' C' D \<longrightarrow> ?thesis"
      using plgf_plgf_bet assms(2) by blast
    moreover 
    {
      assume "ParallelogramFlat A B C D" and "ParallelogramStrict A B' C' D"
      hence False 
        by (metis Col_cases ParallelogramFlat_def \<open>A B Par C D \<and> A D Par B C\<close> 
            \<open>Col C' C D \<and> Col D C D\<close> colx par_distincts 
            parallelogram_strict_not_col_3 plgf_sym)
    }
    ultimately show ?thesis 
      using Parallelogram_def assms(1) assms(3) by presburger
  qed
qed

lemma plgf_out_plgf:
  assumes "ParallelogramFlat A B C D" and
    "A Out B B'" and
    "D Out C C'" and
    "Cong A B' D C'"
  shows "ParallelogramFlat A B' C' D" 
proof -
  have "A \<noteq> B" 
    using assms(2) out_distinct by blast
  have "A \<noteq> B'" 
    using assms(2) out_diff2 by blast
  have "D \<noteq> C" 
    using assms(3) out_distinct by blast
  have "D \<noteq> C'" 
    using assms(3) out_distinct by blast
  obtain P where "\<not> Col A B P" 
    using \<open>A \<noteq> B\<close> not_col_exists by fastforce
  obtain Q where "Parallelogram A B P Q" 
    using \<open>A \<noteq> B\<close> plg_existence by blast
  have "ParallelogramStrict A B P Q" 
    using ParallelogramFlat_def Parallelogram_def \<open>Parallelogram A B P Q\<close> 
      \<open>\<not> Col A B P\<close> by presburger
  have "ParallelogramStrict C D Q P" 
    by (metis \<open>D \<noteq> C\<close> \<open>ParallelogramStrict A B P Q\<close> assms(1) plgf_plgs_trans plgf_sym)
  obtain P' where " A B' EqV Q P'" 
    using vector_construction by blast
  have "B \<noteq> P" 
    using \<open>\<not> Col A B P\<close> not_col_distincts by auto
  have "B' \<noteq> P'" 
    by (metis EqV_def \<open>A B' EqV Q P'\<close> \<open>ParallelogramStrict A B P Q\<close> 
        eqv_permut plg_not_comm_R1 plgs_diff)
  have "A B Par P Q \<and> A Q Par B P" 
    using plg_par \<open>A \<noteq> B\<close> \<open>B \<noteq> P\<close> \<open>Parallelogram A B P Q\<close> by blast
  moreover have "A B' Par P' Q \<and> A Q Par B' P'" 
    using plg_par EqV_def \<open>A B' EqV Q P'\<close> \<open>A \<noteq> B'\<close> \<open>B' \<noteq> P'\<close> by auto
  ultimately have "Col Q P P'" 
    by (meson assms(2) col_par_par_col col_permutation_4 out_col par_left_comm par_right_comm)
  {
    assume "ParallelogramFlat A B' P' Q"
    hence "Col A B' P' \<and> Col A B' Q \<and> Cong A B' P' Q \<and> Cong A Q P' B' \<and> (A \<noteq> P' \<or> B' \<noteq> Q)" 
      using ParallelogramFlat_def by force
    hence False 
      by (metis \<open>ParallelogramStrict A B P Q\<close> assms(2) col_trivial_3 
          colx l6_3_1 out_col plgs_not_col)
  }
  hence "ParallelogramStrict A B' P' Q" 
    using EqV_def Parallelogram_def \<open>A B' EqV Q P'\<close> \<open>A \<noteq> B'\<close> by blast
  hence "A B' Par P Q" 
    using \<open>A B Par P Q \<and> A Q Par B P\<close> \<open>A \<noteq> B'\<close> assms(2) out_col par_col_par_2 by blast
  have "P \<noteq> Q" 
    using \<open>A B' Par P Q\<close> par_distincts by auto
  have "P' \<noteq> Q" 
    using \<open>A B' Par P' Q \<and> A Q Par B' P'\<close> par_distincts by auto
  have "ParallelogramStrict D C' P' Q" 
  proof(rule plgs_out_plgs [where ?B="C" and ?C="P"])
    show "ParallelogramStrict D C P Q"         
      using \<open>ParallelogramStrict C D Q P\<close> plgs_comm2 by blast
    show "D Out C C'"         
      using assms(3) by auto
    show "Q Out P P'"         
      using EqV_def Out_def \<open>A B' EqV Q P'\<close> \<open>P \<noteq> Q\<close> \<open>P' \<noteq> Q\<close> 
        \<open>Parallelogram A B P Q\<close> assms(2) plg_plg_bet by auto
    show "Cong D C' Q P'" 
      using \<open>ParallelogramStrict A B' P' Q\<close> assms(4) cong_inner_transitivity 
        cong_right_commutativity plgs_cong_1 by blast
  qed
  have "Parallelogram A B' C' D" 
    by (meson \<open>ParallelogramStrict A B' P' Q\<close> \<open>ParallelogramStrict D C' P' Q\<close> 
        plgs_permut plgs_pseudo_trans)
  thus ?thesis 
    by (metis Col_cases ParallelogramFlat_def \<open>A \<noteq> B\<close> \<open>D \<noteq> C\<close> assms(1) assms(2) 
        assms(3) col_trivial_3 colx out_col plg_col_plgf)
qed

lemma plg_out_plg: 
  assumes "Parallelogram A B C D" and
    "A Out B B'" and
    "D Out C C'" and
    "Cong A B' D C'"
  shows "Parallelogram A B' C' D" 
proof -
  have "ParallelogramStrict A B C D \<longrightarrow> ?thesis"     
    using Parallelogram_strict_Parallelogram assms(2) assms(3) assms(4) 
      plgs_out_plgs by blast
  moreover have "ParallelogramFlat A B C D \<longrightarrow> ?thesis"     
    using Parallelogram_def assms(2) assms(3) assms(4) plgf_out_plgf by blast
  ultimately show ?thesis
    using Parallelogram_def assms(1) by blast
qed

lemma same_dir_sym:
  assumes "A B SameDir C D"
  shows "C D SameDir A B" 
proof (cases "A = B")
  case True
  thus ?thesis 
    using SameDir_def assms same_dir_null by presburger
next
  case False
  have "(A = B \<and> C = D) \<longrightarrow> ?thesis" 
    using False by auto
  moreover 
  {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    obtain B' where "C D EqV A B'" 
      using vector_construction by blast
    have "Parallelogram A B D' C \<or> (A = B \<and> C = D')" 
      using EqV_def \<open>A B EqV C D'\<close> by force
    hence "Parallelogram A B D' C" 
      by (simp add: False)
    have "Parallelogram C D B' A \<or> (C = D \<and> A = B')" 
      using EqV_def \<open>C D EqV A B'\<close> by auto
    hence "Parallelogram C D B' A" 
      using Out_def \<open>C Out D D'\<close> by blast
    {
      assume "Parallelogram A B D' C" and "Parallelogram C D B' A"
      have "B \<noteq> A" 
        using False by auto
      moreover have "B' \<noteq> A" 
        by (metis \<open>C Out D D'\<close> \<open>Parallelogram C D B' A\<close> out_diff1 plg_not_comm_R1)
      moreover have "Bet A B B' \<or> Bet A B' B" 
      proof -
        have "Bet C D D' \<longrightarrow> ?thesis" 
          using EqV_def False \<open>A B EqV C D'\<close> \<open>Parallelogram C D B' A\<close>
            eqv_sym plg_plg_bet by blast
        moreover have "Bet C D' D \<longrightarrow> ?thesis" 
          using Plg_perm \<open>Parallelogram A B D' C\<close> \<open>Parallelogram C D B' A\<close> 
            plg_plg_bet by blast
        ultimately show ?thesis
          using Out_def \<open>C Out D D'\<close> by blast
      qed
      ultimately have "A Out B B'" 
        by (simp add: Out_def)
    }
    hence "A Out B B'" 
      using \<open>Parallelogram A B D' C\<close> \<open>Parallelogram C D B' A\<close> by blast
    moreover have "C D EqV A B'" 
      by (simp add: \<open>C D EqV A B'\<close>)
    ultimately have "\<exists> D'0. A Out B D'0 \<and> C D EqV A D'0" 
      by blast
    hence ?thesis 
      by (simp add: SameDir_def)
  }
  ultimately show ?thesis 
    using SameDir_def assms by force
qed

lemma same_dir_trans: 
  assumes "A B SameDir C D" and
    "C D SameDir E F"
  shows "A B SameDir E F" 
proof -
  have "(A = B \<and> C = D) \<or> (\<exists> D'. C Out D D' \<and> A B EqV C D')" 
    using SameDir_def assms(1) by presburger
  moreover have "(A = B \<and> C = D) \<longrightarrow> ?thesis" 
    using SameDir_def assms(2) same_dir_null by blast
  moreover 
  {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    have "(C = D \<and> E = F) \<or> (\<exists> D'. E Out F D' \<and> C D EqV E D')" 
      using SameDir_def assms(2) by auto
    moreover have "(C = D \<and> E = F) \<longrightarrow> ?thesis" 
      using Out_def \<open>C Out D D'\<close> by force
    moreover 
    {
      assume "\<exists> D'. E Out F D' \<and> C D EqV E D'"
      then obtain F' where "E Out F F'" and "C D EqV E F'"
        by blast
      have "A = B \<longrightarrow> (\<exists> D'0. E Out F D'0 \<and> A B EqV E D'0)"           
        by (metis Out_def \<open>A B EqV C D'\<close> \<open>C Out D D'\<close> null_vector)
      moreover 
      {
        assume "A \<noteq> B"
        obtain F'' where "A B EqV E F''" 
          using vector_construction by blast
        have "C \<noteq> D" 
          using Out_def \<open>C Out D D'\<close> by blast
        have "C \<noteq> D'" 
          using \<open>C Out D D'\<close> out_distinct by blast
        have "E \<noteq> F" 
          using \<open>E Out F F'\<close> l6_3_1 by blast
        have "E \<noteq> F'" 
          using \<open>E Out F F'\<close> out_diff2 by blast
        have "Parallelogram A B D' C \<or> (A = B \<and> C = D')" 
          using EqV_def \<open>A B EqV C D'\<close> by blast
        hence "Parallelogram A B D' C" 
          using \<open>A \<noteq> B\<close> by blast 
        have "Parallelogram C D F' E \<or> (C = D \<and> E = F')" 
          using EqV_def \<open>C D EqV E F'\<close> by auto
        hence "Parallelogram C D F' E" 
          using \<open>C \<noteq> D\<close> by blast
        have "Parallelogram A B F'' E \<or> (A = B \<and> E = F'')" 
          using EqV_def \<open>A B EqV E F''\<close> by presburger
        hence "Parallelogram A B F'' E" 
          using \<open>A \<noteq> B\<close> by blast
        have "Bet C D D' \<or> Bet C D' D" 
          using Out_def \<open>C Out D D'\<close> by presburger
        have "Bet E F F' \<or> Bet E F' F" 
          using Out_def \<open>E Out F F'\<close> by force
        have "Parallelogram C D' F'' E" 
          using Plg_perm \<open>C \<noteq> D'\<close> \<open>Parallelogram A B D' C\<close> \<open>Parallelogram A B F'' E\<close> 
            plg_pseudo_trans by blast
        have "E Out F F''" 
        proof -
          have "Parallelogram A B D' C \<or> (A = B \<and> C = D')" 
            by (simp add: \<open>Parallelogram A B D' C \<or> A = B \<and> C = D'\<close>)
          moreover have "Parallelogram C D F' E \<or> (C = D \<and> E = F')" 
            using \<open>Parallelogram C D F' E\<close> by blast
          moreover have "Parallelogram A B F'' E \<or> (A = B \<and> E = F'')" 
            using \<open>Parallelogram A B F'' E \<or> A = B \<and> E = F''\<close> by blast
          moreover have "(A = B \<and> C = D') \<longrightarrow> ?thesis" 
            by (simp add: \<open>A \<noteq> B\<close>)
          moreover have "Parallelogram A B D' C \<and> Parallelogram C D F' E \<and> 
                           Parallelogram A B F'' E"
            using \<open>Parallelogram A B D' C\<close> \<open>Parallelogram A B F'' E\<close> 
              \<open>Parallelogram C D F' E\<close> by auto
          moreover
          {
            assume "Parallelogram A B D' C" and
              "Parallelogram C D F' E" and 
              "Parallelogram A B F'' E"
            have "Bet C D D' \<or> Bet C D' D" 
              by (simp add: \<open>Bet C D D' \<or> Bet C D' D\<close>)
            moreover have "Bet E F F' \<or> Bet E F' F" 
              using \<open>Bet E F F' \<or> Bet E F' F\<close> by auto
            moreover 
            {
              assume "Bet C D D'" and "Bet E F F'"
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover have "Bet E F' F''"
              proof (rule plg_plg_bet [where ?A="C" and ?B="D" and ?B'="D'"])
                show "Parallelogram C D F' E" 
                  by (simp add: \<open>Parallelogram C D F' E\<close>)
                show "Bet C D D'" 
                  by (simp add: \<open>Bet C D D'\<close>)
                show "Parallelogram C D' F'' E" 
                  by (simp add: \<open>Parallelogram C D' F'' E\<close>)
              qed
              have "Bet E F F''" 
                using between_exchange4 [where ?C = "F'"] \<open>Bet E F F'\<close> \<open>Bet E F' F''\<close> by blast
              hence "Bet E F F'' \<or> Bet E F'' F" 
                by blast
              ultimately have ?thesis
                by (simp add: Out_def)
            }
            moreover {
              assume "Bet C D D'" and "Bet E F' F"
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover
              have "Bet E F' F''" 
                using plg_plg_bet [where ?A="C" and ?B="D" and ?B'="D'"]
                  \<open>Parallelogram C D F' E\<close> \<open>Bet C D D'\<close> \<open>Parallelogram C D' F'' E\<close> by blast
              have "Bet E F F'' \<or> Bet E F'' F" 
                using l5_1 [where ?B = "F'"] \<open>E \<noteq> F'\<close> \<open>Bet E F' F\<close> \<open>Bet E F' F''\<close> by blast
              ultimately have ?thesis
                using Out_def by blast
            }
            moreover 
            {
              assume "Bet C D' D" and "Bet E F F'" 
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover have "Bet E F F'' \<or> Bet E F'' F" 
              proof (rule l5_3 [where ?D = "F'"])
                show "Bet E F F'" 
                  by (simp add: \<open>Bet E F F'\<close>)
                show "Bet E F'' F'" 
                  using plg_plg_bet [where ?A="C" and ?B="D'" and ?B'="D"]
                    \<open>Parallelogram C D' F'' E\<close> \<open>Bet C D' D\<close> \<open>Parallelogram C D F' E\<close> by blast
              qed
              ultimately have ?thesis 
                by (simp add: Out_def)
            }
            moreover {
              assume "Bet C D' D" and "Bet E F' F"
              have "F \<noteq> E" 
                using \<open>E \<noteq> F\<close> by blast
              moreover have "F'' \<noteq> E" 
                using \<open>A \<noteq> B\<close> \<open>Parallelogram A B F'' E\<close> plg_not_comm_R1 by blast
              moreover have "Bet E F F'' \<or> Bet E F'' F" 
              proof -
                have "Bet E F'' F'" 
                  using plg_plg_bet [where ?A="C" and ?B="D'" and ?B'="D"] 
                    \<open>Bet C D' D\<close> \<open>Parallelogram C D F' E\<close> \<open>Parallelogram C D' F'' E\<close> by blast
                thus ?thesis 
                  using \<open>Bet E F' F\<close> between_exchange4 by blast
              qed
              ultimately have ?thesis 
                by (simp add: Out_def)
            }
            ultimately have ?thesis 
              by blast
          }
          ultimately show ?thesis 
            by blast
        qed
        hence "\<exists> D'0. E Out F D'0 \<and> A B EqV E D'0"  
          using \<open>A B EqV E F''\<close> by blast
      }
      ultimately have "\<exists> D'0. E Out F D'0 \<and> A B EqV E D'0"  
        by blast
    }
    hence ?thesis 
      using SameDir_def calculation(1) calculation(2) by presburger
  }
  thus ?thesis 
    using calculation(1) calculation(2) by blast
qed

lemma same_dir_comm:
  assumes "A B SameDir C D" 
  shows "B A SameDir D C" 
proof -
  have "A = B \<and> C = D \<longrightarrow> ?thesis" 
    using assms by force
  moreover {
    assume "\<exists> D'. C Out D D' \<and> A B EqV C D'"
    then obtain D' where "C Out D D'" and "A B EqV C D'" 
      by blast
    hence H0: "Bet C D D' \<or> Bet C D' D" 
      using Out_def by simp
    have "A \<noteq> B" 
      using \<open>\<exists>D'. C Out D D' \<and> A B EqV C D'\<close> l6_3_1 null_vector by blast
    obtain C' where "B A EqV D C'" 
      using vector_construction by blast
    have "D Out C C'" 
    proof -
      have "C \<noteq> D" 
        using \<open>C Out D D'\<close> l6_3_1 by blast
      moreover have "C' \<noteq> D" 
        using \<open>A \<noteq> B\<close> \<open>B A EqV D C'\<close> eqv_sym null_vector by blast
      moreover 
      have "Bet D C C' \<or> Bet D C' C"
      proof -
        {
          assume "Parallelogram A B D' C"
          hence "Parallelogram C D' D C' \<or> (C = D' \<and> B = A \<and> C' = D \<and> C = C')" 
            by (metis EqV_def Plg_perm \<open>A \<noteq> B\<close> \<open>B A EqV D C'\<close> plg_pseudo_trans)
          moreover 
          {
            assume "Parallelogram C D' D C'"
            have "ParallelogramFlat C D' D C'" 
              by (meson Col_def Out_def \<open>C Out D D'\<close> \<open>Parallelogram C D' D C'\<close>
                  between_symmetry plg_col_plgf)
            hence H1: "Col C D' D \<and> Col C D' C' \<and> Cong C D' D C' \<and> 
                       Cong C C' D D' \<and> (C \<noteq> D \<or> D' \<noteq> C')"
              using ParallelogramFlat_def by simp
            have "Col D' C C'" 
              using H1 col_permutation_4 by blast
            have "Cong D' C D C'" 
              using H1 not_cong_2134 by blast
            have "Cong D' D C C'" 
              using H1 not_cong_3421 by blast
            hence "Bet D' D C \<longrightarrow> ?thesis"
              using col_cong2_bet1 [where ?A = "D'"] \<open>Col D' C C'\<close> \<open>Cong D' C D C'\<close> by blast
            moreover {
              assume "Bet C D' D"
              {
                assume "Parallelogram A B D' C"
                {
                  assume "Parallelogram B A C' D"
                  have "C = C' \<longrightarrow> ?thesis " 
                    using between_trivial by presburger
                  moreover {
                    assume "C \<noteq> C'"
                    have "Parallelogram C D' D C' \<or> (C = D' \<and> B = A \<and> C' = D \<and> C = C')" 
                      using \<open>Parallelogram C D' D C'\<close> by blast
                    moreover {
                      assume "Parallelogram C D' D C'"
                      have "ParallelogramFlat C D' D C'" 
                        by (simp add: \<open>ParallelogramFlat C D' D C'\<close>)
                      moreover have "ParallelogramStrict C D' D C' \<longrightarrow> ?thesis" 
                        using H1 col_not_plgs by blast
                      moreover have "ParallelogramFlat C D' D C' \<longrightarrow> Bet D C' C" 
                        by (metis \<open>Bet C D' D\<close> \<open>Cong D' C D C'\<close> \<open>Cong D' D C C'\<close> 
                            \<open>Parallelogram C D' D C'\<close> bet_cong_eq between_symmetry 
                            calculation(2) ncol134_plg__plgs third_point)
                      ultimately have ?thesis
                        by blast
                    }
                    moreover have "(C = D' \<and> B = A \<and> C' = D \<and> C = C') \<longrightarrow> ?thesis" 
                      using \<open>A \<noteq> B\<close> by auto
                    ultimately have ?thesis 
                      by blast
                  }
                  ultimately have ?thesis
                    by blast
                }
                moreover have "B = A \<and> D = C' \<longrightarrow> ?thesis" 
                  using \<open>A \<noteq> B\<close> by blast
                ultimately have ?thesis 
                  using EqV_def \<open>B A EqV D C'\<close> by presburger
              }
              moreover have "A = B \<and> C = D' \<longrightarrow> ?thesis" 
                using \<open>A \<noteq> B\<close> by blast
              ultimately have ?thesis 
                using \<open>Parallelogram A B D' C\<close> by blast
            }
            ultimately have ?thesis 
              using Bet_cases H0 by blast
          }
          moreover have  "(C = D' \<and> B = A \<and> C' = D \<and> C = C') \<longrightarrow> ?thesis" 
            using \<open>A \<noteq> B\<close> by auto
          ultimately have ?thesis 
            by blast
        }
        moreover have "A = B \<and> C = D' \<longrightarrow> ?thesis"         
          using \<open>A \<noteq> B\<close> by auto
        ultimately show ?thesis
          using EqV_def \<open>A B EqV C D'\<close> by force
      qed
      hence "Bet D C C' \<or> Bet D C' C" 
        by blast
      ultimately show ?thesis 
        by (simp add: Out_def)
    qed
    hence "\<exists> D'0. D Out C D'0 \<and> B A EqV D D'0" 
      using \<open>B A EqV D C'\<close> by blast
  }
  hence "(\<exists> D'. C Out D D' \<and> A B EqV C D') \<longrightarrow> ?thesis" 
    by (simp add: SameDir_def)
  ultimately show ?thesis
    using SameDir_def assms by auto
qed

lemma bet_same_dir1:
  assumes "A \<noteq> B" and
    (*"B \<noteq> C" and*)
    "Bet A B C"
  shows "A B SameDir A C" 
  by (metis Out_def SameDir_def assms(1) assms(2) bet_neq21__neq eqv_refl)

lemma bet_same_dir2: 
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Bet A B C"
  shows "A B SameDir B C" 
  by (metis Bet_cases assms(1) assms(2) assms(3) bet_same_dir1 same_dir_comm 
      same_dir_sym same_dir_trans)

lemma plg_opp_dir:
  assumes "Parallelogram A B C D"
  shows "A B SameDir D C" 
  by (metis EqV_def SameDir_def assms between_equality not_bet_distincts 
      not_col_distincts not_out_bet plg_not_comm)

lemma same_dir_dec:
  shows "A B SameDir C D \<or> \<not> A B SameDir C D" 
  by blast

lemma same_or_opp_dir: 
  assumes "A B Par C D"
  shows "A B SameDir C D \<or> A B OppDir C D" 
proof (cases "A B SameDir C D")
  case True
  thus ?thesis
    by blast
next
  case False
  hence "\<not> A B SameDir C D" 
    by blast
  obtain C' where "A B EqV D C'" 
    using vector_construction by fastforce
  have "D Out C C'" 
  proof (cases "B = C'")
    case True
    hence "B = C'" 
      by blast
    have "Parallelogram A B B D \<longrightarrow> ?thesis" 
    proof -
      {
        assume "ParallelogramStrict A B B D"
        hence "Col B D B" 
          by (simp add: col_trivial_3)
        hence False 
          using \<open>ParallelogramStrict A B B D\<close> plgs_diff by blast
      }
      hence "ParallelogramStrict A B B D \<longrightarrow> ?thesis" 
        by blast
      moreover 
      {
        assume "ParallelogramFlat A B B D"
        hence "D = A \<and> B \<noteq> D" 
          using plgf_permut plgf_trivial_neq by blast
        hence ?thesis 
          by (metis False True \<open>\<And>thesis. (\<And>C'. A B EqV D C' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
              assms bet_same_dir2 eqv_par not_col_distincts not_out_bet par_distincts 
              parallel_uniqueness same_dir_sym vector_uniqueness)
      }
      ultimately show ?thesis
        using Parallelogram_def by blast
    qed
    moreover have "A = B \<and> D = B \<longrightarrow> ?thesis"
      using assms par_neq1 by blast
    ultimately show ?thesis 
      using EqV_def True \<open>A B EqV D C'\<close> by blast
  next
    case False
    {
      assume "Parallelogram A B C' D"
      have "Col C' C D \<and> Col D C D" 
        by (metis Par_cases \<open>A B EqV D C'\<close> assms eqv_par par_id_4 par_neq1 
            par_not_par parallel_uniqueness)
      hence "Col C' C D" 
        by blast
      have "C \<noteq> D" 
        using assms par_distinct by auto
      moreover have "C' \<noteq> D" 
        using \<open>Parallelogram A B C' D\<close> assms par_neq1 plg_not_comm_R1 by blast
      moreover have "Bet D C C' \<or> Bet D C' C" 
      proof -
        have "Bet C' C D \<longrightarrow> ?thesis" 
          using between_symmetry by blast
        moreover 
        {
          assume "Bet C D C'"
          have "A B SameDir D C'" 
            by (simp add: \<open>Parallelogram A B C' D\<close> plg_opp_dir)
          moreover have "C D SameDir D C'" 
            using \<open>Bet C D C'\<close> \<open>C \<noteq> D\<close> \<open>C' \<noteq> D\<close> bet_same_dir2 by force
          ultimately have "A B SameDir C D" 
            by (meson same_dir_sym same_dir_trans)
          hence False 
            using \<open>\<not> A B SameDir C D\<close> by blast
        }
        ultimately show ?thesis 
          using Col_def \<open>Col C' C D\<close> by blast
      qed
      ultimately have ?thesis 
        by (simp add: Out_def)
    }
    moreover have "A = B \<and> D = C' \<longrightarrow> ?thesis" 
      using assms par_distinct by blast
    ultimately show ?thesis 
      using EqV_def \<open>A B EqV D C'\<close> by blast
  qed
  hence "\<exists> D'. D Out C D' \<and> A B EqV D D'" 
    using \<open>A B EqV D C'\<close> by blast
  hence "A B SameDir D C" 
    by (simp add: SameDir_def)
  hence "A B OppDir C D" 
    by (simp add: OppDir_def)
  thus ?thesis 
    by blast
qed

lemma same_dir_id:
  assumes "A B SameDir B A"
  shows "A = B" 
  using assms bet_neq32__neq same_dir_ts by blast

lemma opp_dir_id: 
  assumes "A B OppDir A B"
  shows "A = B" 
  using OppDir_def assms same_dir_id by blast

lemma same_dir_to_null:
  assumes "A B SameDir C D" and
    "A B SameDir D C"
  shows "A = B \<and> C = D" 
  by (meson assms(1) assms(2) same_dir_comm same_dir_id same_dir_sym same_dir_trans)

lemma opp_dir_to_null: 
  assumes "A B OppDir C D" and
    "A B OppDir D C"
  shows "A = B \<and> C = D" 
  using OppDir_def assms(1) assms(2) same_dir_to_null by auto

lemma same_not_opp_dir: 
  assumes "A \<noteq> B" and
    "A B SameDir C D"
  shows "\<not> A B OppDir C D" 
  using OppDir_def assms(1) assms(2) same_dir_to_null by blast

lemma opp_not_same_dir: 
  assumes "A \<noteq> B" and
    "A B OppDir C D" 
  shows "\<not> A B SameDir C D" 
  using assms(1) assms(2) same_not_opp_dir by force

lemma vector_same_dir_cong: 
  assumes "A \<noteq> B" and
    "C \<noteq> D"
  shows "\<exists> X Y. A B SameDir X Y \<and> Cong X Y C D" 
  by (metis assms(1) assms(2) bet_same_dir2 cong_diff_3 segment_construction)
  (* Gabriel Braun March 2013 *)

lemma project_par: 
  assumes "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "P Q Par X Y"
  shows "P' = Q'" 
proof -
  {
    assume "P P' Par X Y"
    hence "Col P P P' \<and> Col Q P P'" 
      using parallel_uniqueness assms(3) not_par_one_not_par par_id_5 by blast
    hence "Col Q P P'" 
      by simp
    {
      assume "Q Q' Par X Y"
      have "Col P Q Q' \<and> Col Q Q Q'" 
        using parallel_uniqueness 
        by (meson \<open>Col Q P P'\<close> \<open>P P' Par X Y\<close> \<open>Q Q' Par X Y\<close> col_trivial_1 par_symmetry)
      hence "Col P Q Q'" 
        by simp
      have ?thesis 
        by (metis Proj_def \<open>Col P Q Q'\<close> \<open>Col Q P P'\<close> \<open>P P' Par X Y\<close> assms(1) 
            assms(2) assms(3) col_permutation_4 l6_21 par_distincts project_id)
    }
    moreover have "Q = Q' \<longrightarrow> ?thesis" 
      using l6_21 by (metis NCol_perm Proj_def \<open>Col Q P P'\<close> 
          \<open>P P' Par X Y\<close> assms(1) assms(2) par_distincts par_id_5 
          par_reflexivity project_not_col)
    ultimately have ?thesis 
      using Proj_def assms(2) by force
  }
  moreover 
  {
    assume "P = P'"
    have "A \<noteq> B" 
      using Proj_def assms(2) by force
    have "X \<noteq> Y" 
      using assms(3) par_distincts by blast
    have "\<not> A B Par X Y" 
      using Proj_def assms(2) by presburger
    have "Col A B Q'" 
      using Proj_def assms(2) by force
    {
      assume "Q Q' Par X Y" 
      hence "Q \<noteq> Q'" 
        using par_distinct by presburger
      have "Col P Q Q' \<and> Col Q Q Q'" 
        using parallel_uniqueness 
        by (metis \<open>Q Q' Par X Y\<close> assms(3) not_par_one_not_par par_id_5)
      hence "Col P Q Q'" 
        by simp
      have "P' = Q'" 
      proof (rule l6_21 [where ?A = "A" and ?B = "B" and ?C = "Q" and ?D = "P"])
        show "\<not> Col A B Q" 
          using \<open>Q \<noteq> Q'\<close> assms(2) project_id by blast
        show "Q \<noteq> P" 
          using assms(3) par_neq1 by blast
        show "Col A B P'" 
          using Proj_def assms(1) by force
        show "Col A B Q'" 
          by (simp add: \<open>Col A B Q'\<close>)
        show "Col Q P P'" 
          using \<open>P = P'\<close> not_col_distincts by blast
        show "Col Q P Q'" 
          using \<open>Col P Q Q'\<close> not_col_permutation_4 by blast
      qed
    }
    moreover 
    {
      assume "Q = Q'"
      have "A = P \<longrightarrow> A B Par X Y" 
        by (metis \<open>A \<noteq> B\<close> \<open>Col A B Q'\<close> \<open>Q = Q'\<close> assms(3) col3 
            col_trivial_2 col_trivial_3 par_col_par_2)
      moreover {
        assume "A \<noteq> P"
        have "A B Par X Y" 
        proof (rule par_col_par_2 [where ?B = "Q"])
          show "A \<noteq> B" 
            by (simp add: \<open>A \<noteq> B\<close>)
          show "Col A Q B" 
            using \<open>Col A B Q'\<close> \<open>Q = Q'\<close> not_col_permutation_5 by blast
          have "A P Par X Y" 
            using \<open>A \<noteq> B\<close> \<open>Col A B Q'\<close> \<open>P = P'\<close> \<open>Q = Q'\<close> \<open>\<not> A B Par X Y\<close> assms(1) 
              assms(3) par_col2_par_bis par_symmetry project_not_id by blast
          thus "A Q Par X Y" 
            by (metis Proj_def \<open>P = P'\<close> assms(1) par_col_par par_distinct 
                par_reflexivity postulate_of_transitivity_of_parallelism_def 
                postulate_of_transitivity_of_parallelism_thm)
        qed
      }
      ultimately have "A B Par X Y" 
        by blast
      hence False 
        by (simp add: \<open>\<not> A B Par X Y\<close>)
    }
    ultimately have "P' = Q'" 
      using Proj_def assms(2) by auto
  }
  ultimately show ?thesis
    using Proj_def assms(1) by force
qed

lemma ker_col: 
  assumes "P P' Proj A B X Y" and
    "Q P' Proj A B X Y" 
  shows "Col P Q P'" 
  by (metis Par_perm Proj_def assms(1) assms(2) not_col_distincts not_par_one_not_par par_id_2)

lemma ker_par: 
  assumes "P \<noteq> Q" and
    "P P' Proj A B X Y" and
    "Q P' Proj A B X Y"
  shows "P Q Par X Y"
proof -
  have "Col P Q P'" 
    using assms(2) assms(3) ker_col by blast
  {
    assume "P P' Par X Y" 
    hence ?thesis 
      by (metis NCol_cases assms(1) assms(2) assms(3) ker_col par_col_par_2)
  }
  moreover have "P = P' \<longrightarrow> ?thesis" 
    by (metis Proj_def assms(1) assms(3) par_left_comm)
  ultimately show ?thesis
    using Proj_def assms(2) by force
qed

lemma project_uniqueness: 
  assumes "P P' Proj A B X Y" and
    "P Q' Proj A B X Y"
  shows "P' = Q'" 
  by (metis Proj_def assms(1) assms(2) colx not_par_one_not_par par_id_2 project_id)

lemma project_col_eq:
  assumes "P \<noteq> P'" and
    "Col P Q P'" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y"
  shows "P' = Q'" 
  by (metis Proj_def assms(1) assms(2) assms(3) assms(4) not_par_not_col 
      par_not_par project_par project_uniqueness)

lemma project_preserves_bet:
  assumes "Bet P Q R" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R R' Proj A B X Y" 
  shows "Bet P' Q' R'" 
proof -
  have "Col P' Q' R'" 
    by (metis Proj_def assms(2) assms(3) assms(4) col3)
  have "P = Q \<longrightarrow> ?thesis" 
    using assms(2) assms(3) not_bet_distincts project_uniqueness by blast
  moreover 
  {
    assume "P \<noteq> Q"
    have "R = Q \<longrightarrow> ?thesis " 
      using assms(3) assms(4) not_bet_distincts project_uniqueness by blast
    moreover 
    {
      assume "R \<noteq> Q"
      have "P' = Q' \<longrightarrow> ?thesis" 
        by (simp add: between_trivial2)
      moreover 
      {
        assume "P' \<noteq> Q'"
        have "R' = Q' \<longrightarrow> ?thesis" 
          by (simp add: between_trivial)
        moreover 
        {
          assume "R' \<noteq> Q'"
          {
            assume "P P' Par X Y"
            {
              assume "Q Q' Par  X Y"
              hence "P P' Par Q Q'" 
                using \<open>P P' Par X Y\<close> not_par_one_not_par by blast
              hence "Q Q' ParStrict P P'" 
                by (metis Par_cases \<open>P P' Par X Y\<close> \<open>P \<noteq> Q\<close> \<open>P' \<noteq> Q'\<close> 
                    all_one_side_par_strict assms(2) assms(3) not_strict_par 
                    par_col_par_2 par_neq1 par_not_col_strict project_par)
              hence "Q Q' OS P P'" 
                by (simp add: l12_6)
              {
                assume "R R' Par X Y"
                hence "R R' Par Q Q'" 
                  using \<open>Q Q' Par X Y\<close> not_par_one_not_par by blast
                hence "Q Q' ParStrict R R'" 
                  by (metis Par_cases \<open>Col P' Q' R'\<close> \<open>Q Q' ParStrict P P'\<close> \<open>R' \<noteq> Q'\<close> 
                      col_trivial_2 l6_16_1 par_not_col_strict par_strict_not_col_4)
                hence "Q Q' OS R R'" 
                  by (simp add: l12_6)
                hence "Q Q' TS P R" 
                  using \<open>Q Q' ParStrict P P'\<close> assms(1) bet__ts os_distincts
                    par_strict_not_col_1 by force
                hence "Q Q' TS P' R'" 
                  using \<open>Q Q' OS P P'\<close> \<open>Q Q' OS R R'\<close> l9_2 l9_8_2 by blast
                then obtain QQ where "Col QQ Q Q'" and "Bet P' QQ R'" 
                  using TS_def by fastforce
                hence "QQ = Q'" 
                  by (meson \<open>Col P' Q' R'\<close> \<open>Q Q' TS P' R'\<close> bet_col 
                      col_permutation_5 colx not_col_permutation_4 ts__ncol)
                hence ?thesis 
                  using \<open>Bet P' QQ R'\<close> by blast
              }
              moreover 
              {
                assume "R = R'"
                have "Q Q' TS P' R" 
                  by (metis \<open>Q Q' OS P P'\<close> \<open>Q Q' ParStrict P P'\<close> \<open>R \<noteq> Q\<close> 
                      assms(1) bet__ts l9_8_2 par_strict_not_col_1)
                then obtain QQ where "Col QQ Q Q'" and "Bet P' QQ R" 
                  using TS_def by blast
                hence "Col P' QQ R" 
                  by (simp add: Col_def)
                have "QQ = Q'" 
                proof (rule l6_21 [where ?A= "Q" and ?B="Q'" and ?C="P'" and ?D="R"])
                  show "\<not> Col Q Q' P'" 
                    using \<open>Q Q' ParStrict P P'\<close> par_strict_not_col_4 by auto
                  show "P' \<noteq> R" 
                    using \<open>Q Q' TS P' R\<close> ts_distincts by blast
                  show "Col Q Q' QQ" 
                    using \<open>Col QQ Q Q'\<close> not_col_permutation_2 by blast
                  show "Col Q Q' Q'" 
                    using not_col_distincts by blast
                  show "Col P' R QQ" 
                    using \<open>Col P' QQ R\<close> not_col_permutation_5 by blast
                  show "Col P' R Q'" 
                    by (simp add: \<open>Col P' Q' R'\<close> \<open>R = R'\<close> col_permutation_5)
                qed
                hence ?thesis 
                  using \<open>Bet P' QQ R\<close> \<open>R = R'\<close> by auto
              }
              ultimately have ?thesis 
                using Proj_def assms(4) by force
            }
            moreover 
            {
              assume "Q = Q'"
              {
                assume "R R' Par X Y"
                then obtain Qx Qy where "Qx \<noteq> Qy" and "X Y Par Qx Qy" and "Col Q Qx Qy" 
                  using \<open>P P' Par X Y\<close> par_neq2 parallel_existence by blast
                hence "Qx Qy Par P P'" 
                  using Par_perm \<open>P P' Par X Y\<close> par_trans by blast
                hence "Qx Qy ParStrict P P'" 
                  by (metis NCol_perm Par_perm Par_strict_cases \<open>Col Q Qx Qy\<close>
                      \<open>P P' Par X Y\<close> \<open>P \<noteq> Q\<close> \<open>P' \<noteq> Q'\<close> assms(2) assms(3) col_trivial_3 
                      par_col2_par par_not_col_strict project_par)
                hence "Qx Qy OS P P'" 
                  using l12_6 by auto
                have "Qx Qy Par R R'" 
                  using \<open>P P' Par X Y\<close> \<open>Qx Qy Par P P'\<close> \<open>R R' Par X Y\<close> 
                    not_par_one_not_par by blast
                hence "Qx Qy ParStrict R R'" 
                  by (metis Par_def \<open>Col Q Qx Qy\<close> \<open>R R' Par X Y\<close> \<open>R \<noteq> Q\<close> \<open>R' \<noteq> Q'\<close> 
                      \<open>X Y Par Qx Qy\<close> assms(3) assms(4) parallel_uniqueness 
                      postulate_of_transitivity_of_parallelism_def 
                      postulate_of_transitivity_of_parallelism_thm project_par) (* 2.0 s *)
                hence "Qx Qy OS R R'" 
                  using l12_6 by force
                hence "Qx Qy TS P R" 
                  using OS_def TS_def \<open>Col Q Qx Qy\<close> \<open>Qx Qy OS P P'\<close> assms(1) by auto
                hence "Qx Qy TS P' R'" 
                  using \<open>Qx Qy OS P P'\<close> \<open>Qx Qy OS R R'\<close> l9_2 l9_8_2 by blast
                then obtain QQ where "Col QQ Qx Qy" and "Bet P' QQ R'" 
                  using TS_def by blast
                have "QQ = Q" 
                proof (rule l6_21 [where ?A="Qx" and ?B="Qy" and ?C="P'" and ?D="R'"])
                  show "\<not> Col Qx Qy P'" 
                    using \<open>Qx Qy OS P P'\<close> col124__nos by blast
                  show "P' \<noteq> R'" 
                    using \<open>Qx Qy TS P' R'\<close> not_two_sides_id by force
                  show "Col Qx Qy QQ" 
                    using Col_cases \<open>Col QQ Qx Qy\<close> by blast
                  show "Col Qx Qy Q" 
                    using \<open>Col Q Qx Qy\<close> not_col_permutation_2 by blast
                  show "Col P' R' QQ" 
                    using \<open>Bet P' QQ R'\<close> bet_col not_col_permutation_5 by blast
                  show "Col P' R' Q" 
                    by (simp add: \<open>Col P' Q' R'\<close> \<open>Q = Q'\<close> col_permutation_5)
                qed
                hence ?thesis 
                  using \<open>Bet P' QQ R'\<close> \<open>Q = Q'\<close> by auto
              }
              moreover 
              have "\<not> Col A B P" 
                using \<open>P P' Par X Y\<close> assms(2) par_neq1 project_not_col by auto
              {
                assume "R = R'"
                hence "Col A B P" 
                  by (metis Proj_def \<open>Q = Q'\<close> \<open>R \<noteq> Q\<close> assms(1) assms(3) assms(4) 
                      bet_col bet_col1 l6_21)
                hence False 
                  using \<open>\<not> Col A B P\<close> by blast
              }
              ultimately have ?thesis 
                using Proj_def assms(4) by force
            }
            ultimately have ?thesis
              using Proj_def assms(3) by force
          }
          moreover 
          {
            assume "P = P'"
            {
              assume "Q Q' Par X Y"
              {
                assume "R R' Par X Y"
                hence "Q Q' Par R R'" 
                  using \<open>Q Q' Par X Y\<close> not_par_one_not_par by blast
                hence "Q Q' ParStrict R R'" 
                  by (metis Par_def \<open>R R' Par X Y\<close> \<open>R \<noteq> Q\<close> \<open>R' \<noteq> Q'\<close> assms(3) 
                      assms(4) ker_col postulate_of_transitivity_of_parallelism_def 
                      postulate_of_transitivity_of_parallelism_thm project_par)
                hence "Q Q' OS R R'" 
                  using l12_6 by blast
                hence "Q Q' TS P R'" 
                  by (metis \<open>P \<noteq> Q\<close> assms(1) bet__ts between_symmetry l9_2 l9_8_2 
                      one_side_not_col123)
                then obtain QQ where "Col QQ Q Q'" and "Bet P QQ R'" 
                  using TS_def by blast
                have "QQ = Q'" 
                proof (rule l6_21 [where ?A="Q" and ?B="Q'" and ?C="P" and ?D="R'"])
                  show "\<not> Col Q Q' P" 
                    using TS_def \<open>Q Q' TS P R'\<close> col_permutation_2 by blast
                  show "P \<noteq> R'" 
                    using \<open>Q Q' TS P R'\<close> ts_distincts by blast
                  show "Col Q Q' QQ" 
                    using Col_cases \<open>Col QQ Q Q'\<close> by blast
                  show "Col Q Q' Q'" 
                    using not_col_distincts by blast
                  show "Col P R' QQ" 
                    using Bet_cases Col_def \<open>Bet P QQ R'\<close> by blast
                  show "Col P R' Q'" 
                    using Col_cases \<open>Col P' Q' R'\<close> \<open>P = P'\<close> by auto
                qed
                hence ?thesis 
                  using \<open>Bet P QQ R'\<close> \<open>P = P'\<close> by blast
              }
              moreover have "R = R' \<longrightarrow> ?thesis" 
                by (metis \<open>Col P' Q' R'\<close> \<open>P = P'\<close> \<open>R' \<noteq> Q'\<close> assms(1) assms(3) assms(4) 
                    not_col_permutation_2 or_bet_out out_bet_out_2 out_col project_col_eq)
              ultimately have ?thesis 
                using Proj_def assms(4) by force
            }
            moreover have "Q = Q' \<longrightarrow> ?thesis" 
              by (metis Proj_def \<open>P = P'\<close> \<open>P' \<noteq> Q'\<close> assms(1) assms(2) assms(3) 
                  assms(4) bet_col colx project_not_col)
            ultimately have ?thesis 
              using Proj_def assms(3) by force
          }
          ultimately have ?thesis 
            using Proj_def assms(2) by force
        }
        ultimately have ?thesis 
          by blast
      }
      ultimately have ?thesis 
        by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma triangle_par:
  assumes "\<not> Col A B C" and
    "A B Par A' B'" and
    "B C Par B' C'" and 
    "A C Par A' C'" 
  shows "A B C CongA A' B' C'" 
proof -
  obtain M where "M Midpoint B B'" 
    using MidR_uniq_aux by blast
  obtain A'' where "Bet A' M A''" and "Cong M A'' A' M"
    using segment_construction by blast
  obtain C'' where "Bet C' M C''" and "Cong M C'' C' M" 
    using segment_construction by blast
  have "M Midpoint A' A''" 
    using \<open>Bet A' M A''\<close> \<open>Cong M A'' A' M\<close> midpoint_def not_cong_3412 by blast
  have "M Midpoint C' C''" 
    using \<open>Bet C' M C''\<close> \<open>Cong M C'' C' M\<close> midpoint_def not_cong_3412 by blast
  have "A' \<noteq> B'" 
    using assms(2) par_distinct by blast
  have "C' \<noteq> B'" 
    using assms(3) par_distinct by blast
  have "B' C' Par B C''" 
    using \<open>C' \<noteq> B'\<close> \<open>M Midpoint B B'\<close> \<open>M Midpoint C' C''\<close> mid_par_cong2 
      par_comm by presburger
  hence "Col B B C \<and> Col C'' B C" 
    using assms(3) not_col_distincts not_par_one_not_par par_id_1 par_symmetry by blast
  hence "Col C'' B C" 
    by blast
  have "B' A' Par B A''" 
    using \<open>A' \<noteq> B'\<close> \<open>M Midpoint A' A''\<close> \<open>M Midpoint B B'\<close> mid_par_cong2
      par_comm by presburger
  hence "Col A'' B A" 
    by (meson assms(2) par_comm par_id_5 par_not_par)
  have "A' B' C' CongA A'' B C''" 
    by (meson \<open>A' \<noteq> B'\<close> \<open>C' \<noteq> B'\<close> \<open>M Midpoint A' A''\<close> \<open>M Midpoint B B'\<close> 
        \<open>M Midpoint C' C''\<close> l7_2 symmetry_preserves_conga)
  have "A B C CongA A'' B C''"
  proof -
    have "B \<noteq> A''" 
      using \<open>B' A' Par B A''\<close> par_distinct by auto
    have "B \<noteq> C''" 
      using \<open>B' C' Par B C''\<close> par_distinct by auto
    have "A \<noteq> B" 
      using \<open>Col B B C \<and> Col C'' B C\<close> assms(1) by blast
    have "C \<noteq> B" 
      using assms(3) par_distinct by auto
    have "A C Par A'' C''" 
      using \<open>M Midpoint A' A''\<close> \<open>M Midpoint C' C''\<close> assms(4) l12_17 
        par_neq2 par_not_par by blast
    {
      assume "Bet C'' B C"
      have "A C ParStrict A'' C''" 
        by (metis Col_perm \<open>A C Par A'' C''\<close> \<open>Bet C'' B C\<close> \<open>Col C'' B C\<close> assms(1) 
            between_identity col3 col_trivial_2 par_not_col_strict)
      have "Bet A'' B A \<longrightarrow> ?thesis" 
        by (metis Bet_cases \<open>A \<noteq> B\<close> \<open>B \<noteq> A''\<close> \<open>B \<noteq> C''\<close> \<open>Bet C'' B C\<close> \<open>C \<noteq> B\<close> l11_14)
      moreover {
        assume "Bet B A A'' \<or> Bet A A'' B"
        have "A = A'' \<longrightarrow> False" 
          using \<open>A C ParStrict A'' C''\<close> not_par_strict_id by blast
        moreover {
          assume "A \<noteq> A''"
          {
            assume "Bet B A A''"
            have "A C TS A'' B" 
              by (metis Col_cases \<open>Bet B A A''\<close> assms(1) bet__ts calculation l9_2)
            moreover have "A C OS B C''" 
              by (metis \<open>Bet C'' B C\<close> \<open>C \<noteq> B\<close> assms(1) bet_out_1 invert_one_side 
                  not_col_permutation_2 out_one_side)
            ultimately
            have False 
              by (meson \<open>A C ParStrict A'' C''\<close> l12_6 l9_9 one_side_symmetry 
                  one_side_transitivity)
          }
          moreover 
          {
            assume "Bet A A'' B"
            have "A'' C'' TS A B" 
              using \<open>A C ParStrict A'' C''\<close> \<open>B \<noteq> A''\<close> \<open>Bet A A'' B\<close> 
                bet__ts par_strict_not_col_3 by force
            moreover have "A'' C'' OS B C" 
              by (meson Col_cases TS_def \<open>B \<noteq> C''\<close> \<open>Bet C'' B C\<close> bet_out 
                  calculation invert_one_side out_one_side)
            ultimately have False 
              using \<open>A C ParStrict A'' C''\<close> l9_9 one_side_symmetry 
                one_side_transitivity pars__os3412 by blast
          }
          ultimately have False 
            using \<open>Bet B A A'' \<or> Bet A A'' B\<close> by fastforce
        }
        ultimately have False 
          by blast
      }
      ultimately have ?thesis 
        using Col_def \<open>Col A'' B A\<close> by blast
    }
    moreover {
      assume "Bet B C C''"
      {
        assume "Bet A'' B A"
        have "A C ParStrict A'' C''" 
          by (metis Par_def \<open>A C Par A'' C''\<close> \<open>B \<noteq> C''\<close> \<open>Bet A'' B A\<close> 
              \<open>Col A'' B A\<close> \<open>Col B B C \<and> Col C'' B C\<close> assms(1) bet_neq21__neq 
              l6_21 not_col_permutation_2)
        have "C = C'' \<longrightarrow> ?thesis" 
          using Par_strict_cases \<open>A C ParStrict A'' C''\<close> not_par_strict_id by blast
        moreover 
        { 
          assume "C \<noteq> C''"
          have "A C TS C'' B" 
            by (meson \<open>A C ParStrict A'' C''\<close> \<open>Bet B C C''\<close> \<open>C \<noteq> B\<close> bet__ts 
                between_symmetry invert_two_sides par_strict_comm par_strict_not_col_1)
          have "A C OS B A''" 
            by (metis \<open>A \<noteq> B\<close> \<open>Bet A'' B A\<close> assms(1) bet_out_1 col_permutation_5 out_one_side)
          have "A C TS A'' C''" 
            using \<open>A C OS B A''\<close> \<open>A C ParStrict A'' C''\<close> \<open>A C TS C'' B\<close> l12_6 
              l9_9 one_side_symmetry one_side_transitivity by blast
          hence False 
            by (simp add: \<open>A C ParStrict A'' C''\<close> l12_6 l9_9_bis)
        }
        ultimately have ?thesis 
          by blast  
      }
      moreover have "Bet B A A'' \<longrightarrow> ?thesis" 
        using out2__conga \<open>Bet C'' B C \<Longrightarrow> A B C CongA A'' B C''\<close> \<open>Col A'' B A\<close> 
          \<open>Col C'' B C\<close> calculation l6_4_2 by blast
      moreover have "Bet A A'' B \<longrightarrow> ?thesis" 
        using out2__conga Out_def \<open>B \<noteq> A''\<close> \<open>Bet B C C''\<close> \<open>C \<noteq> B\<close> bet_out_1 by metis
      ultimately have ?thesis 
        using Col_def \<open>Col A'' B A\<close> by blast
    }
    moreover {
      assume "Bet C C'' B"
      {
        assume "Bet A'' B A"
        have "A C ParStrict A'' C''" 
          by (metis Par_def \<open>A C Par A'' C''\<close> \<open>B \<noteq> C''\<close> \<open>Bet A'' B A\<close> \<open>Col A'' B A\<close> 
              \<open>Col B B C \<and> Col C'' B C\<close> assms(1) bet_neq21__neq col_permutation_2 l6_21)
        have "C = C'' \<longrightarrow> ?thesis" 
          using between_trivial calculation(2) by force
        moreover {
          assume "C \<noteq> C''"
          have "A'' C'' TS C B" 
            by (metis Col_cases \<open>A C ParStrict A'' C''\<close> \<open>B \<noteq> C''\<close> \<open>Bet C C'' B\<close> 
                bet__ts invert_two_sides par_strict_not_col_2)
          moreover have "A'' C'' OS B A" 
            using \<open>A C ParStrict A'' C''\<close> \<open>B \<noteq> A''\<close> \<open>Bet A'' B A\<close> 
              bet_out out_one_side par_strict_not_col_3 by presburger
          ultimately have False 
            using \<open>A C ParStrict A'' C''\<close> l9_2 l9_8_2 l9_9 pars__os3412 by blast
        }
        ultimately have ?thesis 
          by blast
      }
      moreover have "Bet B A A'' \<longrightarrow> ?thesis" 
        using \<open>Bet C'' B C \<Longrightarrow> A B C CongA A'' B C''\<close> \<open>Col A'' B A\<close> \<open>Col C'' B C\<close>
          calculation or_bet_out out2__conga by blast
      moreover have "Bet A A'' B \<longrightarrow> ?thesis" 
        using \<open>B \<noteq> A''\<close> \<open>B \<noteq> C''\<close> \<open>Bet C C'' B\<close> bet_out_1 out2__conga by presburger
      ultimately have ?thesis 
        using Col_def \<open>Col A'' B A\<close> by blast
    }
    ultimately show ?thesis
      using Col_def \<open>Col C'' B C\<close> by blast
  qed
  thus ?thesis 
    using \<open>A' B' C' CongA A'' B C''\<close> conga_sym_equiv not_conga by blast
qed

lemma par3_conga3 :
  assumes "\<not> Col A B C" and
    "A B Par A' B'" and
    "B C Par B' C'" and
    "A C Par A' C'" 
  shows "A B C CongA3 A' B' C'" 
proof -
  have "A B C CongA A' B' C'" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) triangle_par)
  moreover have "B C A CongA B' C' A'" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) not_col_permutation_1 
        par_comm triangle_par)
  moreover have "C A B CongA C' A' B'" 
    by (metis Col_cases Par_cases assms(1) assms(2) assms(3) assms(4) triangle_par)
  ultimately show ?thesis 
    by (simp add: CongA3_def)
qed

lemma project_par_eqv:
  assumes "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "P Q Par A B" 
  shows "P Q EqV P' Q'" 
proof -
  {
    assume "P Q ParStrict A B"
    {
      assume "Q Q' Par X Y"
      hence "P P' Par Q Q'" 
        by (metis Proj_def \<open>P Q ParStrict A B\<close> assms(1) not_par_one_not_par 
            par_strict_not_col_3)
      have "P' Q' Par A B" 
        by (metis Col_cases Par_def Proj_def \<open>P Q ParStrict A B\<close> assms(1) assms(2) 
            ker_par not_col_distincts par_not_par par_strict_not_col_1 par_symmetry)
      have "P P' ParStrict Q P' \<longrightarrow> Parallelogram P Q Q' P'" 
        using Par_strict_cases not_par_strict_id by blast
      hence "Parallelogram P Q Q' P'" 
        by (metis Col_cases Par_cases Par_def \<open>P P' Par Q Q'\<close> \<open>P' Q' Par A B\<close> assms(1)
            assms(2) assms(3) par_2_plg par_strict_distinct 
            postulate_of_transitivity_of_parallelism_def 
            postulate_of_transitivity_of_parallelism_thm project_col_eq)
    }
    hence "Parallelogram P Q Q' P'" 
      by (metis Col_cases Proj_def \<open>P Q ParStrict A B\<close> assms(2) par_strict_not_col_2)
  }
  hence "Parallelogram P Q Q' P'" 
    by (metis Col_cases Par_def assms(1) assms(2) assms(3) plg_trivial project_id)
  thus ?thesis
    using EqV_def by blast
qed

lemma eqv_project_eq_eq:
  assumes "P Q EqV R S" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R P' Proj A B X Y" and
    "S S' Proj A B X Y"
  shows "Q' = S'" 
proof (cases "P = Q")
  case True
  thus ?thesis 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) null_vector project_uniqueness)
next
  case False
  hence "P \<noteq> Q" 
    by simp
  have "R \<noteq> S" 
    using False assms(1) eqv_par par_neq2 by blast
  have "P R EqV Q S" 
    by (simp add: assms(1) eqv_permut)
  have "P = R \<longrightarrow> ?thesis" 
    using assms(1) assms(3) assms(5) project_uniqueness vector_uniqueness by blast
  moreover {
    assume "P \<noteq> R"
    have "Q \<noteq> S" 
      using \<open>P R EqV Q S\<close> \<open>P \<noteq> R\<close> eqv_par par_neq2 by blast
    have "P R Par Q S" 
      using \<open>P R EqV Q S\<close> \<open>P \<noteq> R\<close> eqv_par by blast
    moreover have "P R Par X Y" 
      using \<open>P \<noteq> R\<close> assms(2) assms(4) ker_par by blast
    ultimately have ?thesis 
      using project_par by (meson assms(3) assms(5) par_symmetry par_trans)
  }
  ultimately show ?thesis 
    by blast
qed

lemma eqv_eq_project:
  assumes "P Q EqV R S" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R P' Proj A B X Y"
  shows "S Q' Proj A B X Y" 
proof (cases "S = Q'") 
  case True
  thus ?thesis
    using Proj_def assms(3) by auto
next
  case False
  hence "S \<noteq> Q'" 
    by simp
  {
    assume "P \<noteq> R"
    hence "P R Par Q S" 
      by (simp add: assms(1) eqv_par eqv_permut)
    have "Col P R P'" 
      using assms(2) assms(4) ker_col by force
    {
      assume "Q Q' Par X Y" 
      have "P R Par X Y" 
        using \<open>P \<noteq> R\<close> assms(2) assms(4) ker_par by auto
      {
        assume "Q Q' Par X Y"
        have "Col S Q Q'" 
          by (metis Par_cases \<open>P R Par Q S\<close> \<open>P R Par X Y\<close> 
              \<open>Q Q' Par X Y\<close> par_id_1 par_not_par)
        have "Q' Q Par X Y" 
          using Par_perm \<open>Q Q' Par X Y\<close> by blast
        hence "S Q' Par X Y" 
          by (metis Col_cases False \<open>Col S Q Q'\<close> col_par par_neq1 par_trans)
      }
      hence "S Q' Par X Y" 
        using \<open>Q Q' Par X Y\<close> by auto
    }
    hence "S Q' Par X Y" 
      by (metis Proj_def \<open>P R Par Q S\<close> \<open>P \<noteq> R\<close> assms(2) assms(3) assms(4) 
          ker_par par_left_comm par_not_par par_symmetry)
    hence ?thesis 
      using Proj_def assms(3) by force
  }
  thus ?thesis
    using assms(1) assms(3) vector_uniqueness by blast
qed

lemma eqv_cong: 
  assumes "A B EqV C D"
  shows "Cong A B C D" 
proof -
  have "Parallelogram A B C D \<longrightarrow> ?thesis" 
    using plg_cong by auto
  thus ?thesis 
    using EqV_def assms cong_trivial_identity not_cong_1243 plg_cong_1 by blast
qed

lemma project_preserves_eqv:
  assumes "P Q EqV R S" and
    "P P' Proj A B X Y" and
    "Q Q' Proj A B X Y" and
    "R R' Proj A B X Y" and
    "S S' Proj A B X Y"
  shows "P' Q' EqV R' S'" 
proof (cases "P = Q")
  case True
  thus ?thesis 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) 
        eqv_trivial null_vector project_uniqueness)
next
  case False
  hence "P \<noteq> Q" 
    by simp
  have "R \<noteq> S" 
    using False assms(1) eqv_par par_neq2 by blast
  {
    assume "P Q Par A B"
    have "P Q EqV P' Q'"
      using project_par_eqv [where ?A="A" and ?B="B" and ?X="X" and ?Y="Y"]
        assms(2) assms(3) \<open>P Q Par A B\<close> by blast
    have "R S EqV R' S'" 
      by (meson False \<open>P Q Par A B\<close> assms(1) assms(4) assms(5) eqv_par 
          par_not_par par_symmetry project_par_eqv)
    hence ?thesis 
      by (meson \<open>P Q EqV P' Q'\<close> assms(1) eqv_sym eqv_trans)
  }
  moreover 
  {
    assume "\<not> P Q Par A B" 
    hence "P Q Par X Y \<longrightarrow> ?thesis" 
      by (metis EqV_def False assms(1) assms(2) assms(3) assms(4) assms(5) 
          eqv_par par_symmetry par_trans project_par)
    moreover
    {
      assume "\<not> P Q Par X Y"
      hence "P' \<noteq> Q'" 
        using False assms(2) assms(3) ker_par by blast
      have "\<not> R S Par X Y" 
        by (metis False \<open>\<not> P Q Par X Y\<close> assms(1) eqv_par par_trans)
      have "R' \<noteq> S'" 
        using \<open>R \<noteq> S\<close> \<open>\<not> R S Par X Y\<close> assms(4) assms(5) ker_par by force
      obtain Q'' where "P Q EqV P' Q''" 
        using vector_construction by blast
      obtain S'' where "R S EqV R' S''" 
        using vector_construction by blast
      hence "P' Q'' EqV R' S''" 
        by (meson \<open>P Q EqV P' Q''\<close> assms(1) eqv_sym eqv_trans)
      {
        assume "Q' = Q''" 
        have "P' \<noteq> Q'" 
          by (simp add: \<open>P' \<noteq> Q'\<close>)
        have "P' Q' Par A B" 
          by (metis Col_cases Par_def Proj_def \<open>P' \<noteq> Q'\<close> assms(2) assms(3))
        hence "P Q Par A B" 
          using False \<open>P Q EqV P' Q''\<close> \<open>Q' = Q''\<close> 
            eqv_par postulate_of_transitivity_of_parallelism_def 
            postulate_of_transitivity_of_parallelism_thm by blast
        hence False 
          by (simp add: \<open>\<not> P Q Par A B\<close>)
      }
      hence "Q' \<noteq> Q''" 
        by blast
      {
        assume "S' = S''" 
        have "P Q Par R S" 
          by (simp add: False assms(1) eqv_par)
        have "P Q Par P' Q''" 
          by (simp add: False \<open>P Q EqV P' Q''\<close> eqv_par)
        have "R S Par R' S'" 
          by (simp add: \<open>R S EqV R' S''\<close> \<open>R \<noteq> S\<close> \<open>S' = S''\<close> eqv_par)
        have "P' Q'' Par R' S'" 
          using \<open>P Q Par P' Q''\<close> \<open>P' Q'' EqV R' S''\<close> \<open>S' = S''\<close> eqv_par 
            par_neq2 by presburger
        have "R' S' Par A B" 
          by (metis Proj_def \<open>R' \<noteq> S'\<close> assms(4) assms(5) par_col2_par_bis par_reflexivity)
        hence "P Q Par A B" 
          using \<open>P Q Par R S\<close> \<open>R S Par R' S'\<close> par_not_par by blast
        hence False 
          by (simp add: \<open>\<not> P Q Par A B\<close>)
      }
      hence "S' \<noteq> S''" 
        by blast
      have "P P' EqV Q Q''" 
        by (simp add: \<open>P Q EqV P' Q''\<close> eqv_permut)
      have "R R' EqV S S''" 
        by (simp add: \<open>R S EqV R' S''\<close> eqv_permut)
      have "P' R' EqV Q'' S''" 
        by (simp add: \<open>P' Q'' EqV R' S''\<close> eqv_permut)
      have "Q'' Q' Proj A B X Y" 
        using \<open>P Q EqV P' Q''\<close> assms(2) assms(3) eqv_eq_project project_idem by blast
      hence "Q'' Q' Par X Y" 
        using \<open>Q' \<noteq> Q''\<close> project_par_dir by auto
      have "S'' S' Proj A B X Y" 
        using \<open>R S EqV R' S''\<close> assms(4) assms(5) eqv_eq_project project_idem by blast
      hence "S'' S' Par X Y" 
        using \<open>S' \<noteq> S''\<close> project_par_dir by auto
      have "Q'' Q' Par S'' S'" 
        using \<open>Q'' Q' Par X Y\<close> \<open>S'' S' Par X Y\<close> not_par_one_not_par by blast
      have "\<not> Col A B Q''" 
        using \<open>Q' \<noteq> Q''\<close> \<open>Q'' Q' Proj A B X Y\<close> project_not_col by auto
      have "\<not> Col P' Q'' Q'" 
        by (metis Proj_def \<open>P' \<noteq> Q'\<close> \<open>\<not> Col A B Q''\<close> assms(2) 
            assms(3) col_permutation_2 colx)
      have "Cong P' Q'' R' S''" 
        using \<open>P' Q'' EqV R' S''\<close> eqv_cong by blast
      moreover have "P' Q'' Q' CongA3 R' S'' S'"
        by (metis Par_def Proj_def \<open>P' Q'' EqV R' S''\<close> \<open>Q'' Q' Par S'' S'\<close>
            \<open>R' \<noteq> S'\<close> \<open>\<not> Col P' Q'' Q'\<close> assms(2) assms(3) assms(4) assms(5) 
            col3 eqv_par not_col_distincts par3_conga3)
      ultimately have "P' Q'' Q' Cong3 R' S'' S'" 
        using cong_conga3_cong3 \<open>\<not> Col P' Q'' Q'\<close> by blast
      {
        assume "Q' = S'" 
        hence "P' = R'" 
          using assms(1) assms(2) assms(3) assms(4) assms(5) eqv_comm 
            eqv_project_eq_eq by blast
        hence "Q'' = S''" 
          using \<open>P' R' EqV Q'' S''\<close> null_vector by blast
        hence "Parallelogram Q'' Q' S' S''" 
          using \<open>Q' = S'\<close> \<open>Q' \<noteq> Q''\<close> plg_trivial by presburger
      }
      moreover 
      {
        assume "Q' \<noteq> S'" 
        have "P' = R' \<longrightarrow> Parallelogram Q'' Q' S' S''" 
          using assms(1) assms(2) assms(3) assms(4) assms(5) calculation 
            eqv_project_eq_eq by blast
        moreover 
        {
          assume "P' \<noteq> R'" 
          have "Q'' \<noteq> S' \<or> Q' \<noteq> S''" 
            using Proj_def \<open>\<not> Col A B Q''\<close> assms(5) by force
          moreover have "\<exists> M .M Midpoint Q'' S' \<and> M Midpoint Q' S''" 
          proof (rule par_cong_mid_os)
            show "Q'' Q' ParStrict S'' S'" 
              by (metis \<open>Q'' Q' Par S'' S'\<close> Par_def \<open>Q' \<noteq> S'\<close> \<open>Q'' Q' Proj A B X Y\<close> 
                  \<open>S'' S' Proj A B X Y\<close> col2__eq project_col_eq)
            show "Cong Q'' Q' S'' S'" 
              using Cong3_def \<open>P' Q'' Q' Cong3 R' S'' S'\<close> by auto
            {
              assume "Parallelogram P' Q'' S'' R'"
              hence "ParallelogramStrict R' P' Q'' S''" 
                by (metis Plg_perm Proj_def \<open>P' \<noteq> R'\<close> \<open>\<not> Col A B Q''\<close> assms(2) 
                    assms(4) colx ncol123_plg__plgs)
              have "Q'' S'' ParStrict Q' S'" 
              proof (rule par_strict_col2_par_strict [where ?C ="R'" and ?D="P'"])
                show "Q' \<noteq> S'" 
                  by (simp add: \<open>Q' \<noteq> S'\<close>)
                show  "Q'' S'' ParStrict R' P'" 
                  using \<open>ParallelogramStrict R' P' Q'' S''\<close> par_strict_symmetry plgs_pars_1 by blast
                show "Col R' P' Q'"       
                  by (metis Proj_def assms(2) assms(3) assms(4) col3)
                show "Col R' P' S'"
                  by (metis Proj_def assms(2) assms(4) assms(5) col3)
              qed
              hence "Q'' S'' OS Q' S'" 
                using l12_6 by blast
            }
            thus "Q'' S'' OS Q' S'"
              using EqV_def \<open>P' Q'' EqV R' S''\<close> \<open>\<not> Col P' Q'' Q'\<close> not_col_distincts by blast
          qed
          ultimately have "Plg Q'' Q' S' S''" 
            by (simp add: Plg_def)
          hence "Parallelogram Q'' Q' S' S''" 
            by (simp add: plg_to_parallelogram)
        }
        ultimately have "Parallelogram Q'' Q' S' S''" 
          by blast
      }
      ultimately have "Parallelogram Q'' Q' S' S''" 
        by blast
      hence "Q'' Q' EqV S'' S'" 
        by (simp add: EqV_def)
      hence ?thesis 
        using \<open>P' Q'' EqV R' S''\<close> eqv_sum by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma cop_par__perp2: 
  assumes "Coplanar A B C P" and
    "A B Par C D"
  shows "P Perp2 A B C D" 
proof -
  obtain Q where "A B Perp Q P" and "Coplanar A B C Q" 
    using assms(2) ex_perp_cop par_neq1 by blast
  have "Col P P Q" 
    by (simp add: col_trivial_1)
  moreover have "P Q Perp A B" 
    using Perp_perm \<open>A B Perp Q P\<close> by blast
  moreover 
  have "C D Perp P Q" 
  proof (rule cop_par_perp__perp [where ?A = "A" and ?B = "B"])
    show "A B Par C D" 
      by (simp add: assms(2))
    show "A B Perp P Q"  
      by (simp add: \<open>A B Perp Q P\<close> perp_right_comm)
    {
      assume "C D ParStrict A B"
      have "Coplanar C D P Q" 
      proof (rule coplanar_pseudo_trans [where ?P = "A" and ?Q = "B" and ?R = "C"])
        show "\<not> Col A B C" 
          using \<open>C D ParStrict A B\<close> par_strict_not_col_3 by blast
        show "Coplanar A B C C" 
          using ncop_distincts by blast
        show "Coplanar A B C D" 
          using assms(2) par_cong_cop by blast
        show "Coplanar A B C P" 
          by (simp add: assms(1))
        show "Coplanar A B C Q" 
          by (simp add: \<open>Coplanar A B C Q\<close>)
      qed
    }
    moreover 
    {
      assume "C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B"
      have "Coplanar P Q C D" 
      proof (rule col2_cop__cop [where ?C = "A" and ?D = "B"])
        show "Coplanar P Q A B" 
          using \<open>P Q Perp A B\<close> perp__coplanar by blast
        show "A \<noteq> B" 
          using \<open>C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B\<close> by force
        show "Col A B C" 
          using Col_cases \<open>C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B\<close> by blast
        show "Col A B D" 
          using Col_cases \<open>C \<noteq> D \<and> A \<noteq> B \<and> Col C A B \<and> Col D A B\<close> by blast
      qed
      hence "Coplanar C D P Q" 
        using coplanar_perm_16 by blast
    }
    ultimately show "Coplanar C D P Q"  
      using Par_cases Par_def assms(2) by blast
  qed
  hence "P Q Perp C D" 
    using Perp_cases by blast
  ultimately show ?thesis 
    using Perp2_def by blast
qed

lemma l13_11:
  assumes "\<not> Col PO A A'" and
    "B \<noteq> PO" and 
    "C \<noteq> PO" and
    "Col PO A B" and
    "Col PO B C" and
    "B' \<noteq> PO" and 
    "C' \<noteq> PO" and
    "Col PO A' B'" and
    "Col PO B' C'" and
    "B C' Par C B'" and
    "C A' Par A C'"
  shows "A B' Par B A'" 
proof -
  have "Coplanar B C' C PO" 
    using Col_cases assms(5) ncop__ncols by blast
  have "Coplanar C A' PO A" 
  proof (rule col_cop__cop [where ?D = "B"])
    show "Coplanar C A' PO B" 
      using Col_cases assms(5) ncop__ncols by blast
    show "PO \<noteq> B" 
      using assms(2) by blast
    show "Col PO B A" 
      using Col_cases assms(4) by blast
  qed
  hence "Coplanar C A' A PO" 
    using coplanar_perm_1 by blast
  have "PO Perp2 B C' C B'" 
    by (simp add: \<open>Coplanar B C' C PO\<close> assms(10) cop_par__perp2)
  have "PO Perp2 C A' A C'"
    by (simp add: \<open>Coplanar C A' A PO\<close> assms(11) cop_par__perp2)
  have "PO Perp2 A B' B A'" 
    using \<open>PO Perp2 B C' C B'\<close> \<open>PO Perp2 C A' A C'\<close> assms(1) assms(2) assms(3) 
      assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) l13_10 by blast
  then obtain X Y where "Col PO X Y" and "X Y Perp A B'" and "X Y Perp B A'" 
    using Perp2_def by blast
  have "Coplanar A X PO A'" 
  proof (rule col_cop__cop [where ?D="B'"])
    have "Coplanar A B' X PO"
    proof (rule col_cop__cop [where ?D = "Y"])
      show "Coplanar A B' X Y" 
        using \<open>X Y Perp A B'\<close> coplanar_perm_16 perp__coplanar by blast
      show "X \<noteq> Y" 
        using \<open>X Y Perp B A'\<close> perp_distinct by blast
      show "Col X Y PO" 
        using Col_cases \<open>Col PO X Y\<close> by blast
    qed
    thus "Coplanar A X PO B'" 
      using coplanar_perm_3 by blast
    show "PO \<noteq> B'" 
      using assms(6) by blast
    show "Col PO B' A'" 
      using assms(8) not_col_permutation_5 by blast
  qed
  hence "Coplanar PO A A' X" 
    using coplanar_perm_13 by blast
  have "Coplanar A Y PO A'" 
  proof (rule col_cop__cop [where ?D = "B'"])
    have "Coplanar A B' Y PO" 
    proof (rule col_cop__cop [where ?D = "X"])
      show "Coplanar A B' Y X" 
        using \<open>X Y Perp A B'\<close> coplanar_perm_17 perp__coplanar by blast
      show "Y \<noteq> X" 
        using \<open>X Y Perp A B'\<close> perp_not_eq_1 by blast
      show "Col Y X PO" 
        using \<open>Col PO X Y\<close> not_col_permutation_3 by blast
    qed
    thus "Coplanar A Y PO B'" 
      using coplanar_perm_3 by blast
    show "PO \<noteq> B'" 
      using assms(6) by blast
    show "Col PO B' A'" 
      using assms(8) not_col_permutation_5 by blast
  qed
  hence "Coplanar PO A A' Y" 
    using coplanar_perm_13 by blast
  show ?thesis
  proof (rule l12_9 [where ?C1.0="X" and ?C2.0="Y"])
    show "Coplanar X Y A B" 
      using Coplanar_def \<open>Col PO X Y\<close> assms(4) col_permutation_1 by blast
    show "Coplanar X Y A A'"
      by (meson \<open>Coplanar PO A A' X\<close> \<open>Coplanar PO A A' Y\<close> assms(1) 
          coplanar_pseudo_trans ncop_distincts)
    show "Coplanar X Y B' B"
    proof (rule coplanar_pseudo_trans [where ?P = "PO" and ?Q = "A" and ?R = "A'"],
        simp_all add: assms(1) \<open>Coplanar PO A A' X\<close> \<open>Coplanar PO A A' Y\<close>)
      show "Coplanar PO A A' B'" 
        using assms(8) ncop__ncols by auto
      show "Coplanar PO A A' B" 
        using assms(4) ncop__ncols by blast
    qed
    show "Coplanar X Y B' A'" 
    proof (rule coplanar_pseudo_trans [where ?P = "PO" and ?Q ="A" and ?R = "A'"],
        simp_all add: assms(1)\<open>Coplanar PO A A' X\<close>\<open>Coplanar PO A A' Y\<close>)
      show "Coplanar PO A A' B'" 
        using assms(8) ncop__ncols by blast
      show "Coplanar PO A A' A'"
        using ncop_distincts by blast
    qed
    show "A B' Perp X Y" 
      using Perp_perm \<open>X Y Perp A B'\<close> by blast
    show "B A' Perp X Y" 
      using Perp_perm \<open>X Y Perp B A'\<close> by blast
  qed
qed

lemma l13_14:
  assumes "PO A ParStrict O' A'" and
    "Col PO A B" and
    "Col PO B C" and
    "Col PO A C" and
    "Col O' A' B'" and
    "Col O' B' C'" and
    "Col O' A' C'" and
    "A C' Par A' C" and
    "B C' Par B' C" 
  shows "A B' Par A' B" 
proof -
  have "PO \<noteq> A" 
    using assms(1) par_strict_distinct by blast
  have "O' \<noteq> A'" 
    using assms(1) par_strict_neq2 by auto
  have "\<not> Col PO A A'" 
    using assms(1) par_strict_not_col_4 by presburger
  {
    assume "A = C"
    have "A C' ParStrict A' A \<longrightarrow> ?thesis" 
      using Par_strict_cases not_par_strict_id by blast
    hence ?thesis 
      by (metis Par_def Par_perm Par_strict_perm \<open>A = C\<close> assms(1) assms(7) 
          assms(8) assms(9) col_trivial_2 colx par_strict_not_col_3)
  }
  moreover 
  {
    assume "A \<noteq> C"
    hence "A' \<noteq> C'" 
      using Par_cases \<open>\<not> Col PO A A'\<close> assms(4) assms(8) col2__eq par_id by blast
    have "A C ParStrict A' C'" 
      by (meson \<open>A \<noteq> C\<close> \<open>A' \<noteq> C'\<close> assms(1) assms(4) assms(7) col_trivial_2 
          par_strict_col4__par_strict)
    have "Plg A C A' C'" 
      by (metis Col_cases Par_cases \<open>A C ParStrict A' C'\<close> assms(8) l12_19 
          not_cong_4321 par_id_5 par_par_cong_cong_parallelogram par_strict_not_col_3 
          par_strict_par parallelogram_to_plg)
    {
      assume "B = C"
      hence "A C' Par A' B" 
        using assms(8) by force
      have "B' = C'" 
      proof -
        have "\<not> Col B C' A'" 
          using \<open>A C ParStrict A' C'\<close> \<open>B = C\<close> col_permutation_5 par_strict_not_col_2 by blast
        moreover have "A' \<noteq> C'" 
          by (simp add: \<open>A' \<noteq> C'\<close>)
        moreover have "Col B C' B'" 
          using \<open>B = C\<close> assms(9) par_id par_right_comm by blast
        moreover have "Col B C' C'" 
          by (meson not_col_distincts)
        moreover have "Col A' C' B'" 
          using \<open>O' \<noteq> A'\<close> assms(5) assms(7) col_transitivity_2 by blast
        moreover have "Col A' C' C'" 
          by (simp add: col_trivial_2)
        ultimately show ?thesis 
          using l6_21 by blast
      qed
      hence "A B' Par A' B"  
        using \<open>A C' Par A' B\<close> by blast
      hence ?thesis 
        by simp
    }
    moreover 
    {
      assume "B \<noteq> C"
      {
        assume "B' = C'" 
        have "B B' ParStrict B' C \<longrightarrow> False" 
          using Par_strict_cases not_par_strict_id by blast
        moreover 
        {
          assume "B \<noteq> B'" and "B' \<noteq> C" and "Col B B' C" and "Col B' B' C"
          have "B = C" 
          proof -
            have "\<not> Col A C B'" 
              using \<open>A C ParStrict A' C'\<close> \<open>B' = C'\<close> par_strict_not_col_4 by auto
            moreover have "B' \<noteq> B" 
              using \<open>B \<noteq> B'\<close> by blast
            moreover have "Col A C B" 
              using \<open>PO \<noteq> A\<close> assms(2) assms(4) col_transitivity_2 by blast
            moreover have "Col A C C" 
              using not_col_distincts by blast
            moreover have "Col B' B B" 
              using not_col_distincts by auto
            moreover have "Col B' B C" 
              using \<open>Col B B' C\<close> not_col_permutation_4 by blast
            ultimately show ?thesis 
              using l6_21 by blast
          qed
          hence False 
            by (simp add: \<open>B \<noteq> C\<close>)
        }
        ultimately have False 
          using Par_def \<open>B' = C'\<close> assms(9) by force
      }
      hence "B' \<noteq> C'" 
        by blast
      hence "B C ParStrict B' C'" 
        using \<open>B \<noteq> C\<close> assms(1) assms(2) assms(4) assms(5) assms(7) 
          par_strict_col4__par_strict by blast
      have "Plg B C B' C'"
        using pars_par_plg \<open>B C ParStrict B' C'\<close> assms(9) par_right_comm by blast
      have "Parallelogram A C A' C'" 
        by (simp add: \<open>Plg A C A' C'\<close> parallelogram_equiv_plg)
      have "Parallelogram B C B' C'" 
        by (simp add: \<open>Plg B C B' C'\<close> parallelogram_equiv_plg)
      obtain M where "M Midpoint A A'" and "M Midpoint C C'" 
        using Plg_def \<open>Plg A C A' C'\<close> by blast
      obtain N where "N Midpoint B B'" and "N Midpoint C C'" 
        using Plg_def \<open>Plg B C B' C'\<close> by blast
      hence "M = N" 
        using \<open>M Midpoint C C'\<close> l7_17 by auto
      have "Parallelogram A B A' B'" 
        using mid_plg by (metis \<open>A C ParStrict A' C'\<close> \<open>M = N\<close> \<open>M Midpoint A A'\<close> 
            \<open>N Midpoint B B'\<close> not_par_strict_id)
      have "A B' Par B A'"
      proof (cases "A = B")
        case True
        hence "A' = B'" 
          using symmetric_point_uniqueness \<open>M = N\<close> \<open>M Midpoint A A'\<close> 
            \<open>N Midpoint B B'\<close> by blast
        thus ?thesis 
          by (metis True \<open>\<not> Col PO A A'\<close> assms(2) par_reflexivity)
      next
        case False
        hence "B \<noteq> A'" 
          using \<open>\<not> Col PO A A'\<close> assms(2) by auto
        thus ?thesis using plg_par 
          by (simp add: False \<open>Parallelogram A B A' B'\<close>)
      qed
      hence ?thesis 
        using par_right_comm by presburger
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed  

lemma l13_15_1:
  assumes "\<not> Col A B C" and 
    "\<not> PO B Par A C" and 
    "Coplanar PO B A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'"and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
proof -
  {
    assume "Col B A' B'"
    hence False 
      using assms(4) par_strict_not_col_2 by auto
  }
  {
    assume "Col A A' B'" 
    hence False 
      using assms(4) col_permutation_1 par_strict_not_col_3 by blast
  }
  have "B \<noteq> PO" 
    using assms(4) assms(6) col_permutation_4 par_strict_not_col_1 by blast
  have "A \<noteq> PO" 
    using assms(5) assms(8) par_strict_not_col_4 by blast
  have "\<not> Col A' A C" 
    using assms(5) col_permutation_1 par_strict_not_col_1 by blast
  have "C \<noteq> PO" 
    using Col_cases \<open>\<not> Col A' A C\<close> assms(6) by blast
  have "\<not> Col PO A B" 
    by (metis \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> \<open>Col B A' B' \<Longrightarrow> False\<close> assms(6) assms(7) col3 col_trivial_3)
  {
    assume "Col A' B' C'"
    hence "A' C' Par A B" 
      by (metis assms(1) assms(4) assms(5) par_id par_strict_col_par_strict 
          par_strict_neq2 par_strict_symmetry par_strict_trans)
    hence "A C Par A B" 
      using \<open>A' C' Par A B\<close> assms(5) par_not_par par_strict_par by blast
    hence False 
      using assms(1) par_id_3 by auto
  }
  show ?thesis
  proof (cases "Col PO B C")
    case True
    thus ?thesis 
      by (metis Par_def \<open>B \<noteq> PO\<close> \<open>C \<noteq> PO\<close> \<open>Col A' B' C' \<Longrightarrow> False\<close> assms(1) assms(7) 
          assms(8) col_transitivity_1 col_trivial_2 not_col_permutation_2)
  next
    case False
    hence "\<not> Col PO B C"
      by auto
    have "B' \<noteq> PO" 
      using Col_cases \<open>Col A A' B' \<Longrightarrow> False\<close> assms(6) by blast
    have "A' \<noteq> PO" 
      using Col_cases \<open>Col B A' B' \<Longrightarrow> False\<close> assms(7) by blast
    have "\<not> Col A A' C'" 
      using assms(5) col_permutation_1 par_strict_not_col_3 by blast
    have "C' \<noteq> PO" 
      using Col_cases \<open>\<not> Col A A' C'\<close> assms(6) by blast
    have "\<not> Col PO A' B'" 
      by (meson \<open>B' \<noteq> PO\<close> \<open>Col B A' B' \<Longrightarrow> False\<close> assms(7) col2__eq col_permutation_2)
    have "\<not> Col PO A' C'" 
      by (metis \<open>A' \<noteq> PO\<close> \<open>\<not> Col A A' C'\<close> assms(6) col2__eq col_permutation_1)
    have "\<not> Col B' A B" 
      using assms(4) col_permutation_1 par_strict_not_col_4 by blast
    have "\<not> Col A' A B" 
      using assms(4) col_permutation_1 par_strict_not_col_1 by blast
    have "\<exists> C D. C \<noteq> D \<and> PO B Par C D \<and> Col A C D" 
      by (metis \<open>B \<noteq> PO\<close> col_trivial_1 par_distinct parallel_existence1)
    then obtain X Y where "X \<noteq> Y" and "PO B Par X Y" and "Col A X Y" 
      by blast
    have "Coplanar PO B X A" 
      using \<open>Col A X Y\<close> \<open>PO B Par X Y\<close> \<open>X \<noteq> Y\<close> col_cop__cop 
        col_permutation_1 par_cong_cop by blast
    have "Coplanar PO B Y A" 
      using NCol_perm \<open>Col A X Y\<close> \<open>PO B Par X Y\<close> \<open>X \<noteq> Y\<close> col_cop__cop 
        ncoplanar_perm_1 par_cong_cop by blast
    have "\<exists> L. Col L X Y \<and> Col L A' C'"
    proof -
      have "Coplanar X Y A' C'"    
      proof (rule coplanar_pseudo_trans [where ?P="PO" and ?Q="A" and ?R="B"])
        show "\<not> Col PO A B" 
          by (simp add: \<open>\<not> Col PO A B\<close>)
        show "Coplanar PO A B X" 
          using \<open>Coplanar PO B X A\<close> coplanar_perm_4 by presburger
        show "Coplanar PO A B Y" 
          using \<open>Coplanar PO B Y A\<close> coplanar_perm_4 by blast
        show "Coplanar PO A B A'" 
          using assms(6) ncop__ncols by blast
        show "Coplanar PO A B C'" 
          by (metis \<open>C \<noteq> PO\<close> assms(3) assms(8) col_cop2__cop coplanar_perm_2 ncop_distincts)
      qed
      moreover {
        assume "X Y Par A' C'"
        have "PO B Par X Y" 
          using \<open>PO B Par X Y\<close> by auto
        moreover have "X Y Par A C" 
          using \<open>X Y Par A' C'\<close> assms(5) not_par_one_not_par par_strict_par by blast
        ultimately have False 
          using assms(2) par_not_par by blast
      }
      ultimately show ?thesis 
        using cop_npar__inter_exists by blast
    qed
    then obtain L where "Col L X Y" and "Col L A' C'" 
      by blast
    moreover have "B C Par B' C'"         
    proof -
      have "A \<noteq> L" 
        using \<open>Col L A' C'\<close> \<open>\<not> Col A A' C'\<close> by auto
      have "A L Par PO B'" 
        by (metis Par_def \<open>A \<noteq> L\<close> \<open>B \<noteq> PO\<close> \<open>B' \<noteq> PO\<close> \<open>Col A X Y\<close> 
            \<open>Col L X Y\<close> \<open>PO B Par X Y\<close> \<open>X \<noteq> Y\<close> assms(7) not_par_not_col 
            not_par_one_not_par par_trans)
      have "L A Par PO B"
      proof (cases "X = L")
        case True
        show ?thesis 
        proof (rule par_col_par_2 [where ?B="Y"])
          show "L \<noteq> A" 
            using \<open>A \<noteq> L\<close> by auto
          show "Col L Y A" 
            using Col_cases True \<open>Col A X Y\<close> by blast
          show "L Y Par PO B" 
            using Par_cases True \<open>PO B Par X Y\<close> by blast
        qed
      next
        case False
        then show ?thesis 
          by (metis \<open>A L Par PO B'\<close> \<open>B \<noteq> PO\<close> assms(7) not_col_distincts 
              par_col2_par_bis par_left_comm)
      qed
      {
        assume "X Y Par PO C"
        hence "PO B Par PO C" 
          using \<open>PO B Par X Y\<close> par_trans by blast
        hence False 
          using False par_id by auto
      }
      have "Coplanar X Y PO C" 
        using coplanar_pseudo_trans 
        by (meson \<open>Coplanar PO B X A\<close> \<open>Coplanar PO B Y A\<close> \<open>\<not> Col PO A B\<close> assms(3) 
            coplanar_perm_1 ncop_distincts not_col_permutation_5)
      hence "\<exists> X0. Col X0 X Y \<and> Col X0 PO C" 
        using \<open>X Y Par PO C \<Longrightarrow> False\<close> cop_npar__inter_exists by blast
      then obtain M where "Col M X Y" and "Col M PO C"
        by blast
      hence "A \<noteq> M" 
        by (metis Col_cases \<open>A \<noteq> PO\<close> \<open>\<not> Col A' A C\<close> assms(6) colx not_col_distincts)
      have "PO B Par A M" 
        by (meson Col_cases \<open>A \<noteq> M\<close> \<open>Col A X Y\<close> \<open>Col M X Y\<close> \<open>PO B Par X Y\<close> par_col2_par)
      have "L \<noteq> A'" 
        by (metis \<open>A L Par PO B'\<close> \<open>Col A A' B' \<Longrightarrow> False\<close> assms(6) not_col_distincts 
            not_par_not_col not_strict_par par_id_2)
      {
        assume "L B' Par A' B'"
        {
          assume "L B' ParStrict A' B'"
          hence False 
            using col_trivial_3 par_strict_not_col_2 by blast
        }
        hence False 
          using Par_def \<open>Col A' B' C' \<Longrightarrow> False\<close> \<open>L B' Par A' B'\<close> \<open>L \<noteq> A'\<close> calculation(2) 
            col_transitivity_2 by blast
      }
      {
        assume "A B Par L B'" 
        hence False using par_not_par 
          using \<open>L B' Par A' B' \<Longrightarrow> False\<close> assms(4) par_strict_par par_symmetry by blast
      }
      have "Coplanar A B L B'" 
        by (metis \<open>B \<noteq> PO\<close> \<open>L A Par PO B\<close> assms(7) col_par col_trivial_3 coplanar_perm_8 
            ncop__ncols par_cong_cop par_not_par)
      then obtain N where "Col N A B" and "Col N L B'" 
        using \<open>A B Par L B' \<Longrightarrow> False\<close> cop_npar__inter_exists by blast
      have "A L ParStrict PO B'" 
        by (metis NCol_cases Par_def \<open>A L Par PO B'\<close> \<open>A \<noteq> PO\<close> assms(4) assms(6) 
            col_transitivity_2 par_strict_comm par_strict_not_col_2)
      hence "A \<noteq> N" 
        using \<open>Col N L B'\<close> par_strict_not_col_4 by blast
      hence "A N Par A' B'" 
        by (metis \<open>B \<noteq> PO\<close> \<open>Col N A B\<close> \<open>\<not> Col PO A B\<close> assms(4) 
            col_par par_id_3 par_left_comm par_not_par par_reflexivity par_strict_par)
      have "PO N Par L A'" 
      proof (cases "A PO Par N L")
        case True
        hence "A PO ParStrict N L" 
          using Par_strict_perm \<open>A L ParStrict PO B'\<close> \<open>Col N L B'\<close> 
            par_not_col_strict par_strict_not_col_2 by blast
        show ?thesis
        proof (rule l13_14 [where ?PO="A" and ?O'="N" and ?C="A'" and ?C'="N"])
          show "A PO ParStrict N L" 
            using \<open>A PO ParStrict N L\<close> by auto
          show "Col A PO A'" 
            using Col_cases assms(6) by blast
          show "Col A A' A'" 
            using not_col_distincts by blast
          show "Col A PO A'" 
            using \<open>Col A PO A'\<close> by blast
          show "Col N L N" 
            using not_col_distincts by auto
          show "Col N N N"    
            using not_col_distincts by auto
          show "Col N L N"    
            using not_col_distincts by auto
          show "PO N Par L A'" 
            by (meson \<open>A L Par PO B'\<close> \<open>A N Par A' B'\<close> \<open>A PO ParStrict N L\<close> \<open>Col A PO A'\<close> 
                \<open>Col N L B'\<close> l13_14 not_col_distincts par_left_comm par_symmetry)
          show "A' N Par N A'" 
            by (metis Par_cases \<open>Col N A B\<close> \<open>\<not> Col A' A B\<close> par_reflexivity)
        qed
      next
        case False
        hence "\<not> A PO Par N L" 
          by blast
        have "N \<noteq> L" 
          using \<open>A L ParStrict PO B'\<close> \<open>Col N A B\<close> assms(7) 
            not_col_permutation_3 not_col_permutation_4 par_not_col by blast
        have "L \<noteq> B'" 
          using Col_cases \<open>Col A' B' C' \<Longrightarrow> False\<close> calculation(2) by blast
        have "Col L B' N" 
          using Col_cases \<open>Col N L B'\<close> by blast
        have "Coplanar A PO L B'" 
          using \<open>A L Par PO B'\<close> coplanar_perm_2 par_cong_cop by blast
        hence "Coplanar A PO N L" 
          using col_cop__cop \<open>Col L B' N\<close> \<open>L \<noteq> B'\<close> coplanar_perm_1 by blast
        then obtain P where "Col P A PO" and "Col P N L" 
          using False cop_npar__inter_exists by blast
        have "PO N Par A' L" 
        proof -
          have "P \<noteq> L" 
            using \<open>A L ParStrict PO B'\<close> \<open>Col P A PO\<close> col_permutation_4 
              par_strict_not_col_1 by blast
          {
            assume "P = PO"
            hence "Col L A L" 
              using col_trivial_3 by blast
            moreover have "Col L PO B'"
            proof -
              have "Col L N PO" 
                using Col_cases \<open>Col P N L\<close> \<open>P = PO\<close> by blast
              moreover have "Col L N B'" 
                using Col_cases \<open>Col L B' N\<close> by blast
              ultimately show ?thesis 
                by (metis \<open>N \<noteq> L\<close> col_transitivity_1)
            qed
            ultimately have  False             
              using \<open>A L ParStrict PO B'\<close> par_strict_not_col_2 by auto
          }
          have "A \<noteq> P" 
            by (metis Col_cases \<open>A L ParStrict PO B'\<close> \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P N L\<close> 
                assms(7) col_transitivity_1 par_not_col)
          have "P \<noteq> N" 
            by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A PO\<close> \<open>\<not> Col PO A B\<close> col3 col_trivial_2)
          have "A' \<noteq> P" 
            by (metis Par_def \<open>A N Par A' B'\<close> \<open>Col A A' B' \<Longrightarrow> False\<close> \<open>Col N L B'\<close> 
                \<open>Col P N L\<close> \<open>N \<noteq> L\<close> col_transitivity_1 not_col_permutation_2 par_strict_not_col_2)
          have "B' \<noteq> P" 
            using \<open>A L ParStrict PO B'\<close> \<open>Col P A PO\<close> col_permutation_2 
              par_strict_not_col_3 by blast
          have "\<not> Col P PO L" 
            by (metis Col_cases \<open>A L ParStrict PO B'\<close> \<open>Col P A PO\<close> \<open>P = PO \<Longrightarrow> False\<close> 
                col_transitivity_2 par_strict_not_col_1)
          show ?thesis 
          proof (rule l13_11 [where ?PO="P" and ?C="A" and ?C'="B'"],
              simp_all add: \<open>\<not> Col P PO L\<close> \<open>A \<noteq> P\<close> \<open>A' \<noteq> P\<close> \<open>B' \<noteq> P\<close> \<open>A L Par PO B'\<close>)
            show "Col P PO A'" 
              using Col_cases \<open>A \<noteq> PO\<close> \<open>Col P A PO\<close> assms(6) col2__eq by blast
            show "Col P A' A" 
              using Col_cases \<open>Col P A PO\<close> \<open>Col P PO A'\<close> \<open>P = PO \<Longrightarrow> False\<close> 
                col_transitivity_1 by blast
            show "N \<noteq> P" 
              using \<open>P \<noteq> N\<close> by auto
            show "Col P L N" 
              using Col_cases \<open>Col P N L\<close> by auto
            show "Col P N B'" 
              by (meson \<open>Col N L B'\<close> \<open>Col P L N\<close> \<open>Col P N L\<close> \<open>N \<noteq> L\<close> \<open>P \<noteq> L\<close> 
                  col_transitivity_1 colx)
            show "A' B' Par A N" 
              by (simp add: \<open>A N Par A' B'\<close> par_symmetry)
          qed
        qed
        then show ?thesis 
          using Par_cases by blast
      qed
      have "A' C' Par PO N" 
        by (metis Col_def \<open>L \<noteq> A'\<close> \<open>PO N Par L A'\<close> assms(5) between_trivial2 
            calculation(2) col_par not_par_one_not_par par_strict_not_col_2)
      hence "PO N Par A C" 
        using assms(5) par_strict_par par_symmetry par_trans by blast
      have "N M Par B C" 
      proof (cases "A N Par PO C")
        case True
        have "A N ParStrict PO C" 
          by (metis Col_cases Par_def Par_strict_cases True assms(5) assms(8) 
              col_transitivity_2 par_strict_not_col_3)
        have "N M Par C B" 
        proof (rule l13_14 [where ?PO="A" and ?C="A" and ?O'="PO" and ?C'="PO"],
            simp_all add: \<open>A N ParStrict PO C\<close>)
          show "Col A N B" 
            using Col_cases \<open>Col N A B\<close> by blast
          show "Col A B A" 
            using not_col_distincts by blast
          show "Col A N A" 
            using not_col_distincts by blast
          show "Col PO C M" 
            using Col_cases \<open>Col M PO C\<close> by blast
          show "Col PO M PO" 
            using not_col_distincts by blast
          show "Col PO C PO" 
            by (simp add: col_trivial_3)
          show "N PO Par C A" 
            using Par_cases \<open>PO N Par A C\<close> by blast
          show "B PO Par M A" 
            using Par_cases \<open>PO B Par A M\<close> by blast
        qed
        thus ?thesis 
          using Par_cases by blast
      next
        case False
        hence "\<not> A N Par PO C"
          by blast
        have "Coplanar A N PO C" 
          using \<open>PO N Par A C\<close> coplanar_perm_14 par_cong_cop by blast
        then obtain P where "Col P A N" and "Col P PO C" 
          using False cop_npar__inter_exists by blast
        have "B \<noteq> P" 
          using Col_cases \<open>Col P PO C\<close> \<open>\<not> Col PO B C\<close> by blast
        have "A \<noteq> P" 
          by (metis Col_cases \<open>A \<noteq> PO\<close> \<open>Col P PO C\<close> \<open>\<not> Col A' A C\<close> assms(6) 
              colx not_col_distincts)
        have "M \<noteq> P" 
          by (metis \<open>A \<noteq> N\<close> \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> 
              \<open>PO B Par A M\<close> \<open>\<not> Col PO A' B'\<close> assms(6) assms(7) col_trivial_2 col_trivial_3 colx 
              inter_uniqueness_not_par not_col_permutation_3)
        have "PO \<noteq> P" 
          using \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> \<open>\<not> Col PO A B\<close> l6_16_1 
            not_col_permutation_3 by blast
        have "P \<noteq> N" 
          by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P PO C\<close> \<open>PO N Par A C\<close> 
              \<open>\<not> Col PO A B\<close> col_trivial_2 colx inter_uniqueness_not_par 
              not_col_permutation_4 not_col_permutation_5)
        show ?thesis 
        proof (rule l13_11 [where ?PO="P" and ?C="A" and ?C'="PO"], simp_all add: 
            \<open>B \<noteq> P\<close> \<open>A \<noteq> P\<close> \<open>M \<noteq> P\<close> \<open>PO \<noteq> P\<close>)
          show "\<not> Col P N C" 
            by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> \<open>P \<noteq> N\<close> assms(1) col3 not_col_distincts)
          show "Col P N B" 
            by (metis \<open>A \<noteq> N\<close> \<open>Col N A B\<close> \<open>Col P A N\<close> col2__eq col_permutation_2)
          thus "Col P B A" 
            using \<open>Col P A N\<close> \<open>P \<noteq> N\<close> col_permutation_5 col_trivial_3 colx by blast
          show "Col P C M" 
            by (metis Col_cases \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C\<close> col2__eq)
          show "Col P M PO" 
            using \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C\<close> col2__eq col_permutation_5 by blast
          show "B PO Par A M" 
            using Par_cases \<open>PO B Par A M\<close> by blast
          show "A C Par N PO" 
            using Par_cases \<open>PO N Par A C\<close> by blast
        qed
      qed
      have "N M Par B' C'" 
      proof (cases "N B' Par PO C'")
        case True
        have "N B' ParStrict PO C'" 
          by (metis Par_cases Par_def True \<open>A' C' Par PO N\<close> \<open>\<not> Col PO A' C'\<close> 
              par_strict_not_col_4)
        have "M \<noteq> L" 
          by (metis \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col N L B'\<close> \<open>N B' ParStrict PO C'\<close> 
              assms(8) colx not_col_distincts par_not_col)
        have "L \<noteq> C'" 
          using \<open>Col N L B'\<close> \<open>N B' ParStrict PO C'\<close> col_permutation_5 
            par_strict_not_col_4 by blast
        have "L M Par PO B'" 
        proof (rule par_col_par_2 [where ?B="A"])
          show "L \<noteq> M"
            using \<open>M \<noteq> L\<close> by auto
          show "Col L A M" 
            using Col_cases \<open>Col A X Y\<close> \<open>Col M X Y\<close> \<open>X \<noteq> Y\<close> calculation(1) col3 by blast
          show "L A Par PO B'"
            using Par_cases \<open>A L Par PO B'\<close> by auto
        qed
        have "L C' Par PO N" 
          using par_col_par_2 [where ?B="A'"] \<open>L \<noteq> C'\<close> calculation(2)
            \<open>PO N Par L A'\<close> par_symmetry by meson
        have "N M Par C' B'" 
        proof (rule l13_14 [where ?PO="B'" and ?O'="PO" and ?C="L" and ?C'="PO"])
          show "B' N ParStrict PO C'" 
            using Par_strict_cases \<open>N B' ParStrict PO C'\<close> by blast
          show "Col B' N B'" 
            by (simp add: col_trivial_3)
          show "Col B' B' L" 
            by (simp add: col_trivial_1)
          show "Col B' N L" 
            using Col_cases \<open>Col N L B'\<close> by blast
          show "Col PO C' M" 
            by (metis \<open>C \<noteq> PO\<close> \<open>Col M PO C\<close> assms(8) col_permutation_1 col_trivial_2 colx)
          show "Col PO M PO" 
            by (simp add: col_trivial_3)
          show "Col PO C' PO" 
            by (simp add: col_trivial_3)
          show "N PO Par C' L" 
            using Par_cases \<open>L C' Par PO N\<close> by auto
          show "B' PO Par M L" 
            using Par_cases \<open>L M Par PO B'\<close> by blast
        qed
        thus ?thesis 
          using Par_cases by blast
      next
        case False
        hence "\<not> N B' Par PO C'" 
          by blast
        have "Coplanar N B' PO C'" 
        proof (rule coplanar_pseudo_trans [where ?P="PO" and ?Q="A" and ?R="B"], 
            simp_all add: \<open>\<not> Col PO A B\<close>)
          show "Coplanar PO A B N" 
            using Col_cases \<open>Col N A B\<close> ncop__ncols by blast
          show "Coplanar PO A B B'" 
            using assms(7) ncop__ncols by blast
          show "Coplanar PO A B PO" 
            using ncop_distincts by blast
          show "Coplanar PO A B C'" 
            by (metis \<open>C \<noteq> PO\<close> \<open>Coplanar PO A B PO\<close> assms(3) assms(8) 
                col_cop2__cop coplanar_perm_2)
        qed
        then obtain P where "Col P N B'" and "Col P PO C'" 
          using False cop_npar__inter_exists by blast
        have "B' \<noteq> P" using \<open>\<not> Col PO B C\<close> 
          by (metis \<open>B' \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>Col P PO C'\<close> assms(7) assms(8) 
              col_transitivity_2 not_col_distincts)
        show ?thesis 
        proof (cases "C' = L")
          case True
          hence "C' = L" 
            by blast
          have "C' = M" 
          proof (cases "Col PO X C")
            case True
            show ?thesis
            proof (rule l6_21 [where ?A="PO" and ?B="C" and ?C="Y" and ?D="X"], 
                simp_all add: assms(8))
              show "\<not> Col PO C Y" 
                by (metis True \<open>C \<noteq> PO\<close> \<open>PO B Par X Y\<close> \<open>\<not> Col PO B C\<close> 
                    col_permutation_5 par_col2_par_bis par_id)
              show "Y \<noteq> X" 
                using \<open>X \<noteq> Y\<close> by auto
              show "Col PO C M" 
                using Col_cases \<open>Col M PO C\<close> by blast
              show "Col Y X C'" 
                using Col_cases \<open>C' = L\<close> calculation(1) by blast
              show "Col Y X M" 
                using Col_cases \<open>Col M X Y\<close> by auto
            qed
          next
            case False
            then show ?thesis 
              using True \<open>Col M PO C\<close> \<open>Col M X Y\<close> \<open>X \<noteq> Y\<close> assms(8) 
                calculation(1) l6_21 not_col_permutation_2 not_col_permutation_3 by blast
          qed
          then show ?thesis 
            by (metis True \<open>A' C' Par PO N\<close> \<open>Col A' B' C' \<Longrightarrow> False\<close> \<open>Col N L B'\<close> 
                \<open>\<not> Col PO A' C'\<close> calculation(2) col_par not_col_permutation_2 
                par_comm par_id_4 par_right_comm)
        next
          case False
          hence "C'\<noteq> L" 
            by blast
          {
            assume "L = P" 
            hence "Col C' PO A'" 
              by (metis Col_cases False \<open>Col P PO C'\<close> calculation(2) col_transitivity_1)
            hence "Col PO A' C'" 
              using Col_cases by blast
            hence False 
              by (simp add: \<open>\<not> Col PO A' C'\<close>)
          }
          show ?thesis 
          proof (cases "L = M")
            case True
            have "C' = M"
            proof (rule l6_21 [where ?A="PO" and ?B="C" and ?C="A'" and ?D="C'"],
                simp_all add: assms(8))
              show "\<not> Col PO C A'" 
                by (metis \<open>C \<noteq> PO\<close> \<open>\<not> Col PO A' C'\<close> assms(8) col_transitivity_1)
              show "A' \<noteq> C'" 
                using \<open>\<not> Col PO C A'\<close> assms(8) by auto
              show "Col PO C M" 
                using Col_cases \<open>Col M PO C\<close> by blast
              show "Col A' C' C'" 
                using not_col_distincts by blast
              show "Col A' C' M" 
                using True calculation(2) not_col_permutation_2 by blast
            qed
            then show ?thesis 
              using False True by auto
          next
            case False
            hence "L \<noteq> M"
              by blast
            have "L M Par PO B'"
            proof (rule par_col_par_2 [where ?B="A"], simp_all add:False)
              show "Col L A M" 
                using Col_cases \<open>Col A X Y\<close> \<open>Col M X Y\<close> \<open>X \<noteq> Y\<close> calculation(1) col3 by blast
              show "L A Par PO B'" 
                using Par_cases \<open>A L Par PO B'\<close> by auto
            qed
            have "L C' Par N PO" 
              by (metis Par_cases \<open>C' \<noteq> L\<close> \<open>PO N Par L A'\<close> calculation(2) par_col_par)
            have "B'\<noteq> N" 
              using \<open>Col N A B\<close> \<open>\<not> Col B' A B\<close> by blast
            show ?thesis 
            proof (rule l13_11 [where ?PO="P" and ?C="L" and ?C'="PO"], simp_all add: \<open>B' \<noteq> P\<close>
                \<open>Col P N B'\<close> \<open>L C' Par N PO\<close>)
              {
                assume "Col P N C'"
                hence "Col P B' C'" 
                  by (metis \<open>Col P N B'\<close> \<open>Col P PO C'\<close> \<open>PO N Par A C\<close> \<open>\<not> Col PO A' C'\<close> 
                      assms(5) calculation(2) col_permutation_3 col_transitivity_1 par_strict_par 
                      par_symmetry parallel_uniqueness)
                have "Col C' PO B'" 
                proof (rule col_transitivity_1 [where ?Q="P"])
                  show "C' \<noteq> P" 
                    by (metis \<open>B' \<noteq> N\<close> \<open>C' \<noteq> L\<close> \<open>Col A' B' C' \<Longrightarrow> False\<close> \<open>Col N L B'\<close> 
                        \<open>Col P N B'\<close> calculation(2) col_transitivity_1 not_col_permutation_1)
                  show "Col C' P PO" 
                    using Col_cases \<open>Col P PO C'\<close> by blast
                  show "Col C' P B'" 
                    using Col_cases \<open>Col P B' C'\<close> by auto
                qed
                hence "Col PO B C'" 
                  by (metis \<open>B' \<noteq> PO\<close> assms(7) col_trivial_2 col_trivial_3 l6_21)
                hence False           
                  by (metis \<open>C \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>PO B Par X Y\<close>  \<open>X Y Par PO C \<Longrightarrow> False\<close> 
                      assms(8) not_par_not_col par_col_par_2 par_symmetry par_trans)
              }
              thus "\<not> Col P N C'" 
                by blast
              show "L \<noteq> P" 
                using \<open>L = P \<Longrightarrow> False\<close> by blast
              show "Col P B' L" 
                by (metis Col_cases \<open>B' \<noteq> N\<close> \<open>Col N L B'\<close> \<open>Col P N B'\<close> l6_16_1)
              show "M \<noteq> P" 
                by (metis Col_cases Par_def Par_strict_cases \<open>A L ParStrict PO B'\<close> 
                    \<open>Col P B' L\<close> \<open>L M Par PO B'\<close> par_strict_not_col_4)
              show "PO \<noteq> P" 
                using \<open>A L ParStrict PO B'\<close> \<open>Col P B' L\<close> col_permutation_2 
                  par_strict_not_col_2 by blast
              show "Col P C' M" 
                by (metis \<open>C \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C'\<close> 
                    assms(8) l6_16_1 not_col_permutation_1)
              show "Col P M PO" 
                by (metis \<open>C \<noteq> PO\<close> \<open>C' \<noteq> PO\<close> \<open>Col M PO C\<close> \<open>Col P PO C'\<close> 
                    assms(8) col_permutation_2 l6_16_1)
              show "B' PO Par L M" 
                using Par_cases \<open>L M Par PO B'\<close> by auto
            qed
          qed
        qed
      qed
      thus ?thesis 
        using Par_cases \<open>N M Par B C\<close> par_trans by blast
    qed
    ultimately show ?thesis
      using cop_npar__inter_exists by blast
  qed
qed

lemma l13_15_2_aux:
  assumes "\<not> Col A B C" and
    "\<not> PO A Par B C" and
    "PO B Par A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
proof -
  have "\<not> Col PO A B" 
    by (metis assms(4) assms(6) assms(7) col3 not_col_distincts par_not_col)
  have "\<not> Col PO B C" 
    using \<open>\<not> Col PO A B\<close> assms(3) col_permutation_5 col_trivial_2 not_strict_par by blast
  have "\<not> Col PO A C" 
    using \<open>\<not> Col PO B C\<close> assms(3) col_trivial_3 not_col_permutation_2 not_strict_par2 by blast
  have "PO \<noteq> A" 
    using \<open>\<not> Col PO A B\<close> col_trivial_1 by blast
  have "PO \<noteq> B" 
    using \<open>\<not> Col PO B C\<close> col_trivial_1 by auto
  have "PO \<noteq> C" 
    using \<open>\<not> Col PO B C\<close> not_col_distincts by presburger
  have "PO \<noteq> A'" 
    using assms(5) assms(8) col_permutation_4 par_strict_not_col_2 by blast
  have "PO \<noteq> B'" 
    using assms(4) assms(6) col_permutation_2 par_strict_not_col_3 by blast
  have "PO \<noteq> C'" 
    using assms(5) assms(6) col_permutation_2 par_strict_not_col_3 by blast
  have "\<not> Col PO A' B'" 
    by (meson \<open>PO \<noteq> A'\<close> assms(4) assms(6) col_transitivity_2 not_col_permutation_5 
        par_strict_not_col_3)
  have "\<not> Col PO B' C'" 
    by (metis \<open>PO \<noteq> B'\<close> \<open>PO \<noteq> C'\<close> \<open>\<not> Col PO B C\<close> assms(7) assms(8) col2__eq col_permutation_4)
  have "\<not> Col PO A' C'" 
    by (metis Col_cases \<open>PO \<noteq> A'\<close> assms(5) assms(6) col2__eq par_strict_not_col_3)
  have "A \<noteq> A'" 
    using assms(5) not_par_strict_id by blast  
  have "B \<noteq> B'" 
    using assms(4) col_trivial_2 par_strict_not_col_4 by blast
  have "C \<noteq> C'" 
    using assms(5) col_trivial_2 par_strict_not_col_4 by blast
  show ?thesis
  proof (cases "B C Par B' C'")
    case True
    then show ?thesis 
      by blast
  next
    case False
    hence "B \<noteq> C" 
      using assms(1) not_col_distincts by presburger
    hence "\<exists> C0 D. C0 \<noteq> D \<and> B C Par C0 D \<and> Col B' C0 D" 
      using parallel_existence by auto
    then obtain X Y where "X \<noteq> Y" and "B C Par X Y" and "Col B' X Y"
      by blast
    {
      assume "X Y Par PO C"
      hence "PO C Par B C" 
        using Par_cases \<open>B C Par X Y\<close> not_par_one_not_par by blast
      hence False 
        using \<open>\<not> Col PO B C\<close> par_comm par_id_2 by blast
    }
    have "Coplanar X Y PO C" 
    proof -
      {
        assume "B C ParStrict X Y"
        have "Coplanar X Y PO C" 
        proof (rule coplanar_pseudo_trans [where ?P="B" and ?Q="C" and ?R="B'"])
          show "\<not> Col B C B'" 
            using \<open>B C ParStrict X Y\<close> \<open>Col B' X Y\<close> col_permutation_2 par_not_col by blast
          show "Coplanar B C B' X" 
            using \<open>B C Par X Y\<close> \<open>Col B' X Y\<close> ncop_distincts not_col_distincts 
              par_col2_par_bis par_cong_cop by blast
          show "Coplanar B C B' Y" 
            using ParStrict_def \<open>B C ParStrict X Y\<close> \<open>Col B' X Y\<close> \<open>Coplanar B C B' X\<close> 
              col_cop__cop by blast
          show "Coplanar B C B' PO" 
            using Col_cases assms(7) ncop__ncols by blast
          show "Coplanar B C B' C" 
            using ncop_distincts by blast
        qed
      }
      moreover have "B \<noteq> C \<and> X \<noteq> Y \<and> Col B X Y \<and> Col C X Y \<longrightarrow> Coplanar X Y PO C" 
        using col_permutation_1 ncop__ncols by blast
      ultimately show ?thesis
        using Par_def \<open>B C Par X Y\<close> by force
    qed
    obtain C'' where "Col C'' X Y" and "Col C'' PO C" 
      using \<open>Coplanar X Y PO C\<close> \<open>X Y Par PO C \<Longrightarrow> False\<close> cop_npar__inter_exists by blast
    hence "B' \<noteq> C''" 
      using \<open>PO \<noteq> C\<close> \<open>\<not> Col PO B' C'\<close> assms(8) col_permutation_4 col_trivial_2 colx by blast
    have "B' C'' Par B C" 
      by (metis \<open>B C Par X Y\<close> \<open>B' \<noteq> C''\<close> \<open>Col B' X Y\<close> \<open>Col C'' X Y\<close> \<open>X \<noteq> Y\<close> 
          col2__eq col_par not_par_one_not_par par_col_par_2 par_left_comm)
    have "A C Par A' C''" 
    proof (rule l13_15_1 [where ?PO="PO" and ?A="B" and ?A'="B'"], 
        simp_all add: assms(2) assms(6) assms(7))
      show "\<not> Col B A C" 
        using Col_cases assms(1) by auto
      show "Coplanar PO A B C" 
        using assms(3) coplanar_perm_2 par_cong_cop by blast
      show "B A ParStrict B' A'" 
        using Par_strict_cases assms(4) by blast
      show "B C ParStrict B' C''" 
        by (metis Col_cases Par_def Par_strict_cases \<open>B \<noteq> B'\<close> \<open>B' C'' Par B C\<close> 
            \<open>\<not> Col PO B C\<close> assms(7) l6_16_1)
      show "Col PO C C''" 
        using Col_cases \<open>Col C'' PO C\<close> by blast
    qed
    have "C' \<noteq> C''" 
      using False \<open>B' C'' Par B C\<close> par_symmetry by blast
    have "A' C' Par A' C''" 
      using \<open>A C Par A' C''\<close> assms(5) par_strict_par par_symmetry 
        postulate_of_transitivity_of_parallelism_def 
        postulate_of_transitivity_of_parallelism_thm by blast
    hence "C' = C''" 
      by (metis \<open>Col C'' PO C\<close> \<open>PO \<noteq> C\<close> assms(5) assms(8) col_transitivity_2 
          not_col_permutation_2 par_id_4 par_strict_not_col_2)
    thus ?thesis 
      by (simp add: \<open>C' \<noteq> C''\<close>)
  qed
qed

lemma l13_15_2:
  assumes "\<not> Col A B C" and
    "PO B Par A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
proof (cases "B C Par B' C'")
  case True
  then show ?thesis 
    by blast
next
  case False
  have "\<not> B C Par PO A \<or> \<not> B' C' Par PO A" 
    using False not_par_one_not_par by blast
  moreover {
    assume "\<not> B C Par PO A" 
    hence "\<not> PO A Par B C" 
      using Par_cases by blast
    hence False 
      using False assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) 
        l13_15_2_aux by blast
  }
  moreover {
    assume "\<not> B' C' Par PO A" 
    have "\<not> Col A' B' C'" 
      by (metis assms(1) assms(3) assms(4) par_id par_strict_col_par_strict 
          par_strict_neq2 par_strict_symmetry par_strict_trans)
    moreover have "B' \<noteq> PO" 
      using assms(3) assms(5) col_permutation_2 par_strict_not_col_3 by blast
    have "PO B Par PO B'" 
      by (metis \<open>B' \<noteq> PO\<close> assms(2) assms(6) not_par_not_col par_distinct)
    have "\<not> PO A' Par B' C'" 
      by (metis \<open>\<not> B C Par PO A \<Longrightarrow> False\<close> \<open>\<not> B' C' Par PO A\<close> assms(5)
          not_par_not_col not_par_one_not_par par_distinct par_symmetry)
    moreover have "PO B' Par A' C'" 
      by (metis Par_def Par_perm \<open>PO B Par PO B'\<close> assms(2) assms(4) par_trans)
    ultimately have "B' C' Par B C" 
      using l13_15_2_aux assms(3) assms(4) assms(5) assms(6) assms(7) 
        col_permutation_5 par_strict_symmetry by blast 
    hence False 
      using False Par_cases by auto
  }
  ultimately show ?thesis 
    by blast
qed

lemma l13_15:
  assumes "\<not> Col A B C" and
    "Coplanar PO B A C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "Col PO A A'" and
    "Col PO B B'" and
    "Col PO C C'"
  shows "B C Par B' C'" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) l13_15_1 l13_15_2 by blast

lemma l13_15_par: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "A A' Par B B'" and
    "A A' Par C C'" 
  shows "B C Par B' C'" 
proof -
  have "Plg B' A' A B" 
    by (meson Par_cases Par_strict_cases assms(2) assms(4) pars_par_plg)
  hence "Parallelogram B' A' A B" 
    using parallelogram_equiv_plg by force
  hence "Parallelogram A' A B B'"
    using Plg_perm by blast 
  hence "Parallelogram B B' A' A" 
    using plg_sym by blast
  moreover have "Plg A' C' C A" 
    using Par_cases Par_strict_cases assms(3) assms(5) pars_par_plg by blast
  hence "Parallelogram A' C' C A" 
    using parallelogram_equiv_plg by force
  hence "Parallelogram C' C A A'"
    using Plg_perm by blast
  hence "Parallelogram A' A C C'" 
    using plg_comm2 plg_sym by blast
  ultimately have "Parallelogram B B' C' C \<or> (B = B' \<and> A' = A \<and> C' = C \<and> B = C)" 
    using plg_pseudo_trans by blast
  have "B B' Par C C'" 
    using assms(4) assms(5) not_par_one_not_par par_symmetry by blast
  moreover {
    assume "B B' ParStrict C C'"
    hence "B C Par B' C'" 
      using \<open>Parallelogram B B' C' C \<or> B = B' \<and> A' = A \<and> C' = C \<and> B = C\<close> 
        ncol124_plg__pars1423 par_strict_not_col_1 par_strict_par by blast
  }
  ultimately show ?thesis 
    by (metis Col_def \<open>Parallelogram B B' C' C \<or> B = B' \<and> A' = A \<and> C' = C \<and> B = C\<close> 
        assms(1) between_trivial par_neq1 plg_par_2 plg_trivial plg_uniqueness)
qed

lemma l13_18_2: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "Col PO A A'" and
    "Col PO B B'" 
  shows "Col PO C C'" 
proof -
  have "\<not> Col PO A B" 
    by (metis assms(2) assms(5) assms(6) col_transitivity_2 par_strict_not_col_1 
        par_strict_not_col_4)
  have "Coplanar B' C' PO C" 
    by (metis NCol_cases assms(4) assms(6) coplanar_trans_1 ncop__ncols 
        ncoplanar_perm_4 par_strict_left_comm par_strict_not_col_2 pars__coplanar)
  moreover have "\<not> B' C' Par PO C" 
    by (metis Par_perm Par_strict_perm assms(2) assms(4) assms(5) assms(6) 
        col_transitivity_2 not_par_one_not_par par_id_2 par_strict_not_col_3 par_strict_par)
  ultimately have "\<exists> X. Col X B' C' \<and> Col X PO C" 
    using cop_npar__inter_exists by blast
  then obtain C'' where "Col C'' B' C'" and "Col C'' PO C" 
    by blast
  show ?thesis
  proof (cases "Col PO C C'")
    case True
    then show ?thesis 
      by simp
  next
    case False
    hence "C' C'' Par B C" 
      by (metis NCol_perm Par_def Par_strict_perm \<open>Col C'' B' C'\<close> \<open>Col C'' PO C\<close> 
          assms(4) par_col_par_2)
    have "C' C'' ParStrict B C" 
      using Par_def \<open>C' C'' Par B C\<close> \<open>Col C'' B' C'\<close> assms(4) par_not_col by blast
    have "\<not> Col PO B C" 
      by (metis \<open>\<not> Col PO A B\<close> assms(4) assms(6) col_transitivity_2 col_trivial_3 
          par_strict_not_col_1)
    have "B' C'' Par B C" 
      by (metis Par_cases \<open>C' C'' Par B C\<close> \<open>Col C'' B' C'\<close> \<open>Col C'' PO C\<close> 
          \<open>\<not> Col PO B C\<close> assms(2) assms(4) assms(5) assms(6) col_par l6_16_1 
          not_col_permutation_1 not_par_one_not_par par_strict_not_col_3 par_strict_par)
    have "B' C'' ParStrict B C" 
      using Par_def \<open>B' C'' Par B C\<close> \<open>C' C'' ParStrict B C\<close> par_strict_not_col_2 by blast
    have "A C Par A' C''" 
    proof (rule l13_15 [where ?A="B" and ?PO="PO" and ?A'="B'"],simp_all add:assms(6) assms(5))
      show "\<not> Col B A C" 
        using Col_cases assms(1) by blast
      show "Coplanar PO A B C" 
      proof -
        have "\<not> Col PO A' B'" 
          by (metis Col_cases assms(2) assms(5) assms(6) colx not_col_distincts 
              par_strict_not_col_2 par_strict_not_col_3)
        moreover have "Coplanar PO A' B' PO" 
          using ncop_distincts by blast
        moreover have "Coplanar PO A' B' A" 
          using Col_cases assms(5) ncop__ncols by blast
        moreover have "Coplanar PO A' B' B" 
          using Col_cases assms(6) ncop__ncols by blast
        moreover have "Coplanar PO A' B' C" 
        proof -
          have "\<not> Col PO A C'" 
            by (metis \<open>\<not> Col PO A B\<close> assms(3) assms(5) col_transitivity_2 col_trivial_1 
                not_col_permutation_2 par_strict_not_col_3)
          moreover have "Coplanar PO A C' PO" 
            using ncop_distincts by blast
          moreover have "Coplanar PO A C' A'" 
            using assms(5) ncop__ncols by blast
          moreover have "Coplanar PO A C' B'" 
            by (smt (verit) Col_def False \<open>Coplanar B' C' PO C\<close> assms(3) calculation(3) 
                coplanar_perm_21 coplanar_perm_8 coplanar_trans_1 
                par_strict_not_col_3 pars__coplanar)
          moreover have "Coplanar PO A C' C" 
            by (metis \<open>Coplanar B' C' PO C\<close> \<open>\<not> Col PO A' B'\<close> assms(4) assms(6) 
                calculation(4) col_transitivity_2 coplanar_perm_22 
                coplanar_perm_8 coplanar_trans_1 not_col_distincts par_strict_not_col_3)
          ultimately show ?thesis 
            using coplanar_pseudo_trans by blast
        qed
        ultimately show ?thesis 
          using coplanar_pseudo_trans by blast
      qed
      show "B A ParStrict B' A'" 
        using Par_strict_cases assms(2) by auto
      show "B C ParStrict B' C''" 
        using Par_strict_cases \<open>B' C'' ParStrict B C\<close> by blast
      show "Col PO C C''" 
        using Col_cases \<open>Col C'' PO C\<close> by blast
    qed
    hence "A' C' Par A' C''" 
      using assms(3) par_strict_par par_symmetry 
        postulate_of_transitivity_of_parallelism_def 
        postulate_of_transitivity_of_parallelism_thm by blast
    hence "\<not> Col A' B' C'" 
      by (metis \<open>A C Par A' C''\<close> assms(1) assms(2) col2__eq not_par_one_not_par 
          par_col2_par_bis par_id par_strict_neq2 par_strict_par)
    hence "C = C''" 
      by (metis False \<open>A' C' Par A' C''\<close> \<open>Col C'' B' C'\<close> \<open>Col C'' PO C\<close> 
          col2__eq col_permutation_4 col_permutation_5 par_id)
    then show ?thesis 
      using \<open>Col C'' B' C'\<close> assms(4) par_strict_not_col_2 by blast
  qed
qed

lemma l13_18_3_R1: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "A A' Par B B'"
  shows "C C' Par A A'" 
proof -
  have "A \<noteq> A'" 
    using assms(5) par_neq1 by auto
  have "B \<noteq> B'" 
    using assms(4) not_par_strict_id by blast
  then obtain P where "B B' Par C P" 
    using parallel_existence1 by blast
  show ?thesis
  proof (cases "C P Par B C")
    case True
    {
      assume "C P ParStrict B C"
      hence ?thesis 
        using Par_strict_cases not_par_strict_id by blast
    }
    then show ?thesis 
      by (metis Par_def Par_perm True \<open>B B' Par C P\<close> assms(4) col_trivial_1 
          par_not_col par_strict_not_col_3)
  next
    case False
    have "\<not> C P Par B' C'" 
      using False assms(4) not_par_one_not_par par_strict_par by blast
    have "\<not> Col B C B'" 
      using assms(4) par_strict_not_col_1 by auto
    have "Coplanar C P B' C'" 
    proof -
      have "\<not> Col B C B'" 
        using assms(4) par_strict_not_col_1 by auto
      moreover have "Coplanar B C B' B" 
        using ncop_distincts by blast
      moreover have "Coplanar B C B' C" 
        using ncop_distincts by auto
      moreover have "Coplanar B C B' B'" 
        using ncop_distincts by blast
      moreover have "Coplanar B C B' C'"
        using assms(4) pars__coplanar by blast
      ultimately show ?thesis 
        by (metis \<open>B B' Par C P\<close> coplanar_perm_2 coplanar_trans_1 par_cong_cop)
    qed
    then obtain C'' where "Col C'' C P" and "Col C'' B' C'" 
      using \<open>\<not> C P Par B' C'\<close> cop_npar__inter_exists by blast
    show ?thesis 
    proof (cases "B' = C''")
      case True
      then show ?thesis 
        by (metis \<open>B B' Par C P\<close> \<open>Col C'' C P\<close> \<open>\<not> Col B C B'\<close> 
            col_par not_col_distincts not_par_one_not_par par_distinct par_id_2)
    next
      case False
      have "C C'' Par B B'" 
        by (metis \<open>B B' Par C P\<close> \<open>Col C'' B' C'\<close> \<open>Col C'' C P\<close> assms(4) 
            col_permutation_4 not_par_not_col not_par_one_not_par
            par_distinct par_strict_not_col_2)
      have "B' C'' Par B C" 
        by (metis False \<open>Col C'' B' C'\<close> assms(4) col_par not_par_one_not_par 
            par_left_comm par_strict_neq2 par_strict_par)
      {
        assume "Col A' B' C'" 
        hence "C' A' Par B C" 
          by (metis Par_cases assms(3) assms(4) col_transitivity_1 not_col_permutation_5 
              par_col2_par_bis par_strict_neq2 par_strict_par)
        hence "B C Par A C" 
          using Par_cases assms(3) not_par_one_not_par par_strict_par by blast
        {
          assume "B C ParStrict A C"
          hence "Col A B C" 
            using col_trivial_2 par_strict_not_col_4 by blast
        }
        hence "Col A B C" 
          using Par_cases \<open>B C Par A C\<close> par_id_2 by blast
        hence False 
          by (simp add: assms(1))
      }
      have "A C Par A' C''" 
      proof (rule l13_15_par [where ?A="B" and ?A'="B'"])
        show "\<not> Col B A C" 
          using Col_cases assms(1) by blast
        show "B A ParStrict B' A'" 
          using Par_strict_cases assms(2) by blast
        show "B C ParStrict B' C''" 
          using Par_def \<open>B' C'' Par B C\<close> \<open>\<not> Col B C B'\<close> not_col_permutation_2 
            par_strict_symmetry by blast
        show "B B' Par A A'" 
          using Par_cases assms(5) by auto
        show "B B' Par C C''" 
          using Par_cases \<open>C C'' Par B B'\<close> by blast
      qed
      have "C' = C''" 
      proof (rule l6_21 [where ?A="C'" and ?B="A'" and ?C="B'" and ?D="C'"])
        show "\<not> Col C' A' B'" 
          using Col_cases \<open>Col A' B' C' \<Longrightarrow> False\<close> by blast
        show "B' \<noteq> C'" 
          using \<open>Col A' B' C' \<Longrightarrow> False\<close> col_trivial_2 by auto
        show "Col C' A' C'" 
          by (simp add: col_trivial_3)
        show "Col C' A' C''" 
          by (meson Par_def \<open>A C Par A' C''\<close> assms(3) col_trivial_1 parallel_uniqueness)
        show "Col B' C' C'" 
          by (simp add: col_trivial_2)
        show "Col B' C' C''" 
          using Col_cases \<open>Col C'' B' C'\<close> by auto
      qed
      thus ?thesis 
        using \<open>C C'' Par B B'\<close> assms(5) not_par_one_not_par by blast
    qed
  qed
qed

lemma l13_18_3_R2: 
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "A A' Par B B'"
  shows "C C' Par B B'" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) l13_18_3_R1 par_trans by blast

lemma l13_18_3:
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" and
    "B C ParStrict B' C'" and
    "A A' Par B B'"
  shows "C C' Par A A' \<and> C C' Par B B'" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) l13_18_3_R1 l13_18_3_R2 by blast

lemma l13_18:  
  assumes "\<not> Col A B C" and
    "A B ParStrict A' B'" and
    "A C ParStrict A' C'" 
  shows "(B C ParStrict B' C' \<and> Col PO A A' \<and> Col PO B B' \<longrightarrow> Col PO C C')
\<and> ((B C ParStrict B' C' \<and> A A' Par B B') \<longrightarrow> (C C' Par A A' \<and> C C' Par B B'))
\<and> (A A' Par B B' \<and> A A' Par C C' \<longrightarrow> B C Par B' C')" 
  by (meson assms(1) assms(2) assms(3) l13_15_par l13_18_2 l13_18_3_R1 l13_18_3_R2)

lemma l13_19_aux: 
  assumes "\<not> Col PO A B" and
    "A \<noteq> A'" and
    "A \<noteq> C" and
    "PO \<noteq> A" and
    "PO \<noteq> A'" and
    "PO \<noteq> C" and
    "PO \<noteq> C'" and
    "PO \<noteq> B" and 
    "PO \<noteq> B'" and
    "PO \<noteq> D" and
    "PO \<noteq> D'" and
    "Col PO A C" and
    "Col PO A A'" and
    "Col PO A C'" and
    "Col PO B D" and
    "Col PO B B'" and
    "Col PO B D'" and
    "\<not> A B Par C D" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'" 
  shows "C D Par C' D'" 
proof -
  have "Coplanar A B C D" 
    using Col_cases Coplanar_def assms(12) assms(15) by auto
  then obtain E where "Col E A B" and "Col E C D" 
    using \<open>Coplanar A B C D\<close> assms(18) cop_npar__inter_exists by blast
  hence "\<not> A' B' Par PO E" 
    by (meson assms(1) assms(19) col_trivial_3 par_symmetry parallel_uniqueness)
  have "Coplanar A' B' PO E" 
  proof (rule coplanar_pseudo_trans [where ?P="PO" and ?Q="A" and ?R="B"], simp_all add:assms(1))
    show "Coplanar PO A B A'" 
      using assms(13) ncop__ncols by blast
    show "Coplanar PO A B B'" 
      using assms(16) ncop__ncols by blast
    show "Coplanar PO A B PO" 
      using ncop_distincts by blast
    show "Coplanar PO A B E" 
      using \<open>Col E A B\<close> ncop__ncols not_col_permutation_2 by blast
  qed
  then obtain E' where "Col E' A' B'" and "Col E' PO E" 
    using \<open>\<not> A' B' Par PO E\<close> cop_npar__inter_exists by blast
  have "C \<noteq> E" 
    using \<open>Col E A B\<close> assms(1) assms(12) assms(3) l6_16_1 not_col_permutation_3 by blast
  show ?thesis
  proof (cases "Col A D E")
    case True
    hence "B = D" 
      by (metis \<open>C \<noteq> E\<close> \<open>Col E A B\<close> \<open>Col E C D\<close> assms(1) assms(10) assms(12) assms(15) 
          col2__eq col_permutation_2)
    hence "A' B' Par A' D'" 
      using assms(19) assms(20) par_symmetry par_trans by blast
    moreover {
      assume "A' B' ParStrict A' D'"
      hence ?thesis 
        by (simp add: not_par_strict_id)
    }
    ultimately show ?thesis 
      by (metis NCol_perm Par_def \<open>B = D\<close> assms(1) assms(13) assms(16) 
          assms(17) assms(21) assms(5) col_trivial_3 colx par_comm)
  next
    case False
    have "B \<noteq> B'" 
      using Par_perm assms(1) assms(13) assms(19) assms(2) l6_16_1 par_id_3 by blast
    have "D E Par D' E'" 
    proof (rule l13_15 [where ?A="A" and ?PO="PO" and ?A'="A'"], simp_all add: False assms(13))
      show "Coplanar PO D A E" 
        using Coplanar_def NCol_cases \<open>Col E A B\<close> assms(15) by blast
      show "A D ParStrict A' D'" 
        by (metis NCol_cases Par_def assms(1) assms(11) assms(13) assms(17) assms(2) 
            assms(20) col_trivial_3 colx)
      show "A E ParStrict A' E'" 
      proof -
        have "A E Par A' E'" 
          by (metis False NCol_perm \<open>C \<noteq> E\<close> \<open>Col E A B\<close> \<open>Col E C D\<close> \<open>Col E' A' B'\<close> 
              \<open>Col E' PO E\<close> assms(12) assms(13) assms(19) assms(4) assms(5) 
              col_transitivity_1 par_col_par par_col_par_2)
        thus ?thesis 
          by (metis NCol_cases Par_def \<open>Col E' A' B'\<close> assms(1) assms(13) 
              assms(16) assms(2) assms(9) col_transitivity_2)
      qed
      show "Col PO D D'" 
        using assms(15) assms(17) assms(8) col_transitivity_1 by blast
      show "Col PO E E'" 
        using Col_cases \<open>Col E' PO E\<close> by auto
    qed
    have "D C Par D' C'" 
    proof (cases "Col B C E")
      case True
      hence "B = D" 
        by (metis \<open>C \<noteq> E\<close> \<open>Col E C D\<close> assms(1) assms(12) assms(15) assms(6) 
            col2__eq col_permutation_4 col_permutation_5)
      thus ?thesis 
        using False \<open>Col E A B\<close> not_col_permutation_2 by blast
    next
      case False
      have "C E Par C' E'" 
      proof (rule l13_15 [where ?A="B" and ?PO="PO" and ?A'="B'"], simp_all add: False assms(16))
        show "Coplanar PO C B E" 
          using Coplanar_def NCol_perm \<open>Col E A B\<close> assms(12) by blast
        show "B C ParStrict B' C'" 
          by (metis NCol_cases \<open>B \<noteq> B'\<close> assms(1) assms(12) assms(16) assms(21) assms(6) 
              col_trivial_3 colx par_not_col_strict)
        show "B E ParStrict B' E'" 
        proof -
          have "B E Par B' E'" 
          proof (rule par_col_par_2 [where ?B="A"]) 
            show "B \<noteq> E" 
              using False col_trivial_3 by blast
            show "Col B A E" 
              using Col_cases \<open>Col E A B\<close> by blast
            have "B' E' Par B A" 
            proof (rule par_col_par_2 [where ?B="A'"])
              show "B' \<noteq> E'" 
                by (metis \<open>B \<noteq> E\<close> \<open>Col E A B\<close> \<open>Col E' PO E\<close> assms(1) assms(16) 
                    assms(9) col2__eq col_permutation_2)
              show "Col B' A' E'" 
                using Col_cases \<open>Col E' A' B'\<close> by auto
              show "B' A' Par B A" 
                using Par_cases assms(19) by blast
            qed
            thus "B A Par B' E'" 
              using Par_cases by blast
          qed
          thus ?thesis 
            by (metis Par_def \<open>B \<noteq> B'\<close> \<open>Col E A B\<close> assms(1) assms(16) l6_16_1 
                not_col_permutation_2)
        qed
        show "Col PO C C'" 
          using assms(12) assms(14) assms(4) col_transitivity_1 by blast
        show "Col PO E E'" 
          using Col_cases \<open>Col E' PO E\<close> by auto
      qed
      show ?thesis 
      proof (rule par_col_par_2 [where ?B = "E"])
        show "D \<noteq> C" 
          by (metis assms(1) assms(12) assms(15) assms(6) col_trivial_2 colx not_col_permutation_2)
        show "Col D E C" 
          using Col_cases \<open>Col E C D\<close> by auto
        have "D' C' Par D E" 
        proof (rule par_col_par_2 [where ?B = "E'"])
          show "D' \<noteq> C'" 
            using assms(1) assms(14) assms(17) assms(7) col2__eq col_permutation_4 by blast
          show "Col D' E' C'" 
            using Par_perm \<open>C E Par C' E'\<close> \<open>Col D E C\<close> \<open>D E Par D' E'\<close> col_par_par_col by blast
          show "D' E' Par D E" 
            using Par_cases \<open>D E Par D' E'\<close> by blast
        qed
        thus "D E Par D' C'" 
          using Par_cases by blast 
      qed
    qed
    thus ?thesis 
      using Par_cases by blast
  qed
qed

lemma l13_19:
  assumes "\<not> Col PO A B" and
    "PO \<noteq> A" and
    "PO \<noteq> A'" and
    "PO \<noteq> C" and
    "PO \<noteq> C'" and
    "PO \<noteq> B" and
    "PO \<noteq> B'" and
    "PO \<noteq> D" and
    "PO \<noteq> D'" and
    "Col PO A C" and
    "Col PO A A'" and
    "Col PO A C'" and
    "Col PO B D" and
    "Col PO B B'" and
    "Col PO B D'" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'" 
  shows "C D Par C' D'" 
proof (cases "A = A'")
  case True
  hence "B = B'" 
    using assms(1) assms(14) assms(16) col2__eq col_permutation_5 par_id by blast
  have "D = D'" 
    by (metis True assms(1) assms(13) assms(15) assms(17) colx not_col_permutation_2 
        not_col_permutation_4 par_id_4)
  have "C = C'" 
    using \<open>B = B'\<close> assms(1) assms(10) assms(12) assms(18) colx par_id_2 by blast
  then show ?thesis 
    by (metis NCol_cases \<open>D = D'\<close> assms(1) assms(10) assms(13) assms(4) 
        col_transitivity_2 par_reflexivity)
next
  case False
  hence "A \<noteq> A'"
    by blast
  show ?thesis 
  proof (cases "A = C")
    case True
    have "A' = C'" 
      by (metis True assms(1) assms(11) assms(12) assms(14) assms(16) 
          assms(18) assms(7) col_par_par_col col_trivial_3 colx not_col_permutation_1)
    thus ?thesis 
      using True assms(17) by auto
  next
    case False
    hence "A \<noteq> C" 
      by blast
    then show ?thesis 
    proof (cases "A' = C'")
      case True
      have "A = C" 
        by (metis True assms(1) assms(10) assms(16) assms(18) l6_16_1 
            not_par_one_not_par par_comm par_id)
      thus ?thesis 
        using False by blast
    next
      case False
      hence "A' \<noteq> C'" 
        by blast
      show ?thesis 
      proof (cases "C D Par C' D'")
        case True
        thus ?thesis 
          by simp
      next
        case False
        hence "\<not> C D Par C' D'"
          by blast
        have "\<not> C D Par A' B' \<or> \<not> C' D' Par A' B'" 
          using False not_par_one_not_par by blast
        moreover {
          assume "\<not> C D Par A' B'" 
          hence "\<not> C D Par A B" 
            using assms(16) par_trans by blast
          hence "\<not> A B Par C D" 
            using Par_cases by blast
          hence ?thesis 
            using l13_19_aux 
            using \<open>A \<noteq> A'\<close> \<open>A \<noteq> C\<close> assms(1) assms(10) assms(11) assms(12) assms(13) 
              assms(14) assms(15) assms(16) assms(17) assms(18) assms(2) assms(3) assms(4) 
              assms(5) assms(6) assms(7) assms(8) assms(9) by force
        }
        moreover {
          assume "\<not> C' D' Par A' B'" 
          hence "C' D' Par C D" 
          proof -
            have "\<not> Col PO A' B'" 
              by (meson assms(1) assms(11) assms(14) assms(3) assms(7) col2__eq col_permutation_4)
            moreover have "A' \<noteq> A" 
              using \<open>A \<noteq> A'\<close> by auto
            moreover have "A' \<noteq> C'" 
              using \<open>A' \<noteq> C'\<close> by auto
            moreover have "Col PO A' C'" 
              using assms(11) assms(12) assms(2) col_transitivity_1 by blast
            moreover have "Col PO A' A" 
              using Col_cases assms(11) by auto
            moreover have "Col PO A' C" 
              using assms(10) assms(11) assms(2) col_transitivity_1 by blast
            moreover have "Col PO B' D'" 
              using assms(14) assms(15) assms(6) col_transitivity_1 by blast
            moreover have "Col PO B' B" 
              using Col_cases assms(14) by blast
            moreover have "Col PO B' D" 
              using assms(13) assms(14) assms(6) col_transitivity_1 by blast
            moreover have "\<not> A' B' Par C' D'" 
              using Par_cases \<open>\<not> C' D' Par A' B'\<close> by blast
            moreover have "A' B' Par A B" 
              using Par_cases assms(16) by blast
            moreover have "A' D' Par A D" 
              using Par_cases assms(17) by blast
            moreover have "B' C' Par B C" 
              using Par_cases assms(18) by auto
            ultimately show ?thesis
              using l13_19_aux assms(2) assms(3) assms(4) assms(5) assms(6) assms(7)
                assms(8)assms(9) by force
          qed
          hence ?thesis 
            using Par_cases by blast
        }
        ultimately show ?thesis 
          by blast
      qed
    qed
  qed
qed

lemma l13_19_par_aux:
  assumes "X \<noteq> A" and
    (*   "X \<noteq> A'" and
    "X \<noteq> C" and
    "X \<noteq> C'" and*)
    "Y \<noteq> B" and
    (*   "Y \<noteq> B'" and
    "Y \<noteq> D" and
    "Y \<noteq> D'" and*)
    "Col X A C" and
    "Col X A A'" and
    "Col X A C'" and
    "Col Y B D" and
    "Col Y B B'" and
    "Col Y B D'" and
    "A \<noteq> C" and
    "B \<noteq> D" and
    "A \<noteq> A'" and
    "X A ParStrict Y B" and
    "\<not> A B Par C D" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'" 
  shows "C D Par C' D'" 
proof -
  have "Coplanar B Y A X" 
    using assms(12) coplanar_perm_23 pars__coplanar by blast
  hence "Coplanar A C B Y" 
    by (meson assms(1) assms(3) col_cop2__cop coplanar_perm_16 ncop_distincts)
  hence "Coplanar A B C D" 
    by (metis assms(6) assms(2) col2_cop2__eq col_trivial_2 coplanar_perm_2 
        ncop_distincts not_col_permutation_3)
  then obtain E where "Col E A B" and "Col E C D" 
    using assms(13) cop_npar__inter_exists by blast
  obtain Z where "X A Par E Z" 
    using assms(1) parallel_existence1 by blast
  hence "\<not> A B Par E Z" 
    using assms(12) not_par_one_not_par par_id_1 par_left_comm par_strict_not_col_4 by blast
  hence "\<not> A' B' Par E Z" 
    using assms(14) postulate_of_transitivity_of_parallelism_def 
      postulate_of_transitivity_of_parallelism_thm by blast
  have "Coplanar A' B' E Z" 
  proof -
    {
      assume "X A ParStrict E Z"
      hence "Coplanar X A E Z" 
        using \<open>X A Par E Z\<close> par_cong_cop by auto
      have "Coplanar X A E A'" 
        using assms(4) ncop__ncols by blast
      have "Coplanar X A E E" 
        using ncop_distincts by blast 
      have "Coplanar X A E B'" 
      proof (cases "Col A B A'")
        case True
        thus ?thesis 
          by (metis \<open>Col E A B\<close> assms(4) assms(11) assms(14) l6_16_1 ncop__ncol 
              not_col_permutation_2 par_distincts)
      next
        case False
        moreover have "Coplanar A B A' B'" 
          by (simp add: assms(14) par_cong_cop)
        moreover have "Coplanar A B A' X" 
          using assms(4) ncop__ncols not_col_permutation_2 by blast
        moreover have "Coplanar A B A' E" 
          using \<open>Col E A B\<close> ncop__ncols not_col_permutation_2 by blast  
        moreover have "Coplanar A B A' A" 
          using ncop_distincts by blast
        ultimately show ?thesis 
          using coplanar_pseudo_trans by presburger
      qed
      have "\<not> Col X A E" 
        using \<open>X A ParStrict E Z\<close> par_strict_not_col_1 by auto
      hence ?thesis 
        by (simp add: \<open>Coplanar X A E A'\<close> \<open>Coplanar X A E B'\<close> \<open>Coplanar X A E E\<close> 
            \<open>Coplanar X A E Z\<close> coplanar_pseudo_trans)
    }
    thus ?thesis 
      by (metis NCol_perm Par_def \<open>X A Par E Z\<close> assms(4) colx ncop__ncols)
  qed
  then obtain E' where "Col E' A' B'" and "Col E' E Z" 
    using \<open>\<not> A' B' Par E Z\<close> cop_npar__inter_exists by blast
  {
    assume "Col A D E" 
    have False
    proof (cases "A = E")
      case True
      then show ?thesis 
        by (metis \<open>Col E C D\<close> assms(1) assms(6) assms(9) assms(12) assms(3) 
            col_par not_col_permutation_1 par_strict_not_col_2 par_strict_par 
            parallel_uniqueness)
    next
      case False
      have "Col A B D" 
        using Col_cases False \<open>Col A D E\<close> \<open>Col E A B\<close> col_transitivity_1 by blast
      have "Col A X A \<and> Col A Y B" 
        by (meson \<open>Col A B D\<close> assms(6) assms(10) assms(12) col2__eq one_side_not_col124 pars__os3412)
      thus ?thesis 
        using assms(12) par_strict_not_col_2 by blast
    qed
  }
  have "X A ParStrict E Z" 
    by (metis \<open>X A Par E Z\<close> Col_def Par_def \<open>Col A D E \<Longrightarrow> False\<close> \<open>Col E A B\<close> assms(12) 
        between_trivial l6_16_1 par_strict_not_col_4)
  have "Y B Par E Z" 
    by (metis Par_perm \<open>X A Par E Z\<close> assms(12) not_par_one_not_par par_strict_par)
  have "Y B ParStrict E Z" 
  proof -
    {
      assume "Y \<noteq> B" and "E \<noteq> Z" and "Col Y E Z" and "Col B E Z"
      have "Col E Y B" 
        by (metis \<open>Col B E Z\<close> \<open>Col Y E Z\<close> \<open>Y B Par E Z\<close> assms(8) col2__eq 
            col_permutation_2 not_strict_par)
      have "Col B D E" 
        using \<open>Col Y E Z\<close> \<open>Y B Par E Z\<close> assms(6) assms(10) assms(2) col_par 
          col_permutation_1 parallel_uniqueness by blast
      have "B = D" 
      proof (rule l6_21 [where ?A="B" and ?B="E" and ?C="C" and ?D="D"])
        {
          assume "Col B E C"
          hence "Col C X A \<and> Col C Y B" 
            by (metis \<open>Col E A B\<close> \<open>Col E C D\<close> assms(6) assms(9) assms(10) 
                assms(12) assms(3) col_permutation_4 col_permutation_5 
                col_trivial_3 colx par_not_col)
          hence False 
            using assms(12) par_not_col by blast
        }
        thus "\<not> Col B E C" 
          by blast
        show "C \<noteq> D" 
          using Col_cases \<open>Col B D E\<close> \<open>\<not> Col B E C\<close> by blast
        show "Col B E B" 
          using not_col_distincts by auto
        show "Col B E D" 
          using Col_cases \<open>Col B D E\<close> by blast
        show "Col C D B" 
          by (metis \<open>Col A D E \<Longrightarrow> False\<close> \<open>Col B D E\<close> \<open>Col E C D\<close> col_permutation_1 
              col_trivial_2 colx)
        show "Col C D D" 
          using col_trivial_2 by auto
      qed
      hence False 
        by (simp add: assms(10))
    }
    thus ?thesis 
      using Par_def \<open>Y B Par E Z\<close> by auto
  qed
  {
    assume "Col A' D' E'"
    have "Col A' B' D'" 
      by (metis (full_types) \<open>Col A' D' E'\<close> \<open>Col E' A' B'\<close> \<open>Col E' E Z\<close> 
          \<open>X A Par E Z\<close> \<open>X A ParStrict E Z\<close> assms(4) col2__eq col_permutation_3 
          col_permutation_4 not_strict_par2 par_strict_not_col_4)
    have "Col A' X A" 
      using Col_cases assms(4) by blast
    moreover have "Col A' Y B"
    proof -
      have "Col Y B' D'" 
        using assms(7) assms(8) assms(2) col_transitivity_1 by blast
      have "A D Par A B" 
        using \<open>Col A' B' D'\<close> assms(14) assms(15) not_par_one_not_par par_col_par 
          par_distinct by blast
      hence False 
        by (meson assms(6) assms(10) assms(12) l6_16_1 one_side_not_col124 
            par_id_3 pars__os3412)
      thus ?thesis
        by blast
    qed
    ultimately have False 
      using assms(12) par_not_col by blast
  }
  have "\<not> Col X A B" 
    using assms(12) par_strict_not_col_4 by auto
  hence "B \<noteq> B'" 
    by (metis Col_cases assms(4) assms(11) assms(14) 
        col2__eq inter__npar inter_trivial)
  hence "C \<noteq> C'" 
    by (metis Col_cases Par_cases assms(5) assms(7) assms(12) assms(16) colx 
        not_col_distincts par_id_5 par_not_col)
  have "\<not> Col Y A B" 
    using assms(12) col_permutation_4 par_strict_not_col_2 by blast
  have "D \<noteq> D'" 
    by (metis Col_cases assms(4) assms(8) assms(11) assms(12) assms(15) colx 
        inter__npar inter_trivial not_col_distincts par_not_col)
  have "A' \<noteq> C'" 
    using \<open>\<not> Col X A B\<close> assms(9) assms(14) assms(16) assms(3) l6_16_1 
      not_par_one_not_par par_comm par_id by blast
  have "B' \<noteq> D'" 
    using Col_cases \<open>Col A' D' E' \<Longrightarrow> False\<close> \<open>Col E' A' B'\<close> by blast
  have "A \<noteq> E" 
    using \<open>Col A D E \<Longrightarrow> False\<close> col_trivial_3 by force
  have "A' \<noteq> E'" 
    using \<open>Col A' D' E' \<Longrightarrow> False\<close> col_trivial_3 by blast
  have "B \<noteq> E" 
    using \<open>Y B ParStrict E Z\<close> col_trivial_2 par_strict_not_col_1 by blast
  have "B' \<noteq> E'" 
    using \<open>Col E' E Z\<close> \<open>Y B ParStrict E Z\<close> assms(7) col_permutation_2 par_not_col by blast
  have "A E Par A' E'" 
    by (metis \<open>A \<noteq> E\<close> \<open>A' \<noteq> E'\<close> \<open>Col E A B\<close> \<open>Col E' A' B'\<close> assms(14) col_par 
        not_par_one_not_par par_left_comm par_neq2 par_trans)
  have "A E ParStrict A' E'" 
    by (metis NCol_perm \<open>A E Par A' E'\<close> \<open>X A ParStrict E Z\<close> assms(4) 
        assms(11) col_trivial_3 l6_16_1 par_not_col_strict 
        par_strict_not_col_1)
  have "D E Par D' E'" 
  proof (rule l13_15_par [where ?A="A" and ?A'="A'"])
    show "\<not> Col A D E" 
      using \<open>Col A D E \<Longrightarrow> False\<close> by auto
    show "A D ParStrict A' D'" 
      by (metis NCol_perm Par_def \<open>D \<noteq> D'\<close> assms(6) assms(8) assms(12) assms(15) 
          colx par_strict_comm par_strict_not_col_3)
    show "A E ParStrict A' E'" 
      using \<open>A E ParStrict A' E'\<close> by auto
    show "A A' Par D D'" 
      by (meson \<open>D \<noteq> D'\<close> \<open>X A Par E Z\<close> \<open>Y B Par E Z\<close> assms(4) assms(6) assms(8) 
          assms(11) not_col_distincts not_par_one_not_par par_col4__par)
    have "A X Par E E'" 
      by (metis \<open>A E ParStrict A' E'\<close> \<open>Col E' E Z\<close> \<open>X A Par E Z\<close> not_col_distincts 
          par_col2_par_bis par_comm par_strict_not_col_2)
    thus "A A' Par E E'" 
      using Col_cases assms(4) assms(11) par_col_par_2 by blast
  qed
  have "C E Par C' E'" 
  proof (rule l13_15_par [where ?A="B" and ?A'="B'"])
    show "\<not> Col B C E" 
      by (metis \<open>B \<noteq> E\<close> \<open>Col E A B\<close> \<open>\<not> Col X A B\<close> assms(9) assms(3) 
          col_permutation_5 col_trivial_3 colx l6_16_1)
    show "B C ParStrict B' C'" 
      by (metis NCol_perm Par_def \<open>B \<noteq> B'\<close> assms(5) assms(7) assms(12) assms(16) 
          l6_16_1 par_not_col)
    show "B E ParStrict B' E'" 
    proof -
      have "B A Par B' E'" 
        by (metis Col_cases Par_cases \<open>B' \<noteq> E'\<close> \<open>Col E' A' B'\<close> assms(14) par_col_par)
      hence "B E Par B' E'" 
        using Col_cases \<open>B \<noteq> E\<close> \<open>Col E A B\<close> par_col_par_2 by blast
      thus ?thesis 
        by (metis NCol_cases Par_def \<open>A E ParStrict A' E'\<close> \<open>Col E' A' B'\<close> 
            l6_16_1 par_strict_not_col_2)
    qed
    show "B B' Par C C'" 
      by (metis Par_def Par_perm \<open>B \<noteq> B'\<close> \<open>C \<noteq> C'\<close> assms(1) assms(5) assms(7)
          assms(12) assms(2) assms(3) col_par not_col_permutation_2 par_trans)
    have "B Y Par E E'" 
      by (metis \<open>A E ParStrict A' E'\<close> \<open>Col E' E Z\<close> \<open>Y B Par E Z\<close> not_col_distincts 
          par_col2_par_bis par_comm par_strict_not_col_2)
    thus "B B' Par E E'" 
      using Col_cases \<open>B \<noteq> B'\<close> assms(7) par_col_par_2 by blast
  qed
  have "C \<noteq> D" 
    using Col_cases assms(6) assms(12) assms(3) par_not_col by blast
  moreover have "C E Par C' D'" 
  proof -
    have "C' \<noteq> D'" 
      using Col_cases assms(5) assms(8) assms(12) par_not_col by blast
    moreover have "Col C' E' D'" 
    proof (rule col_par_par_col [where ?A="C" and ?B="E" and ?C="D"])
      show "Col C E D" 
        using Col_cases \<open>Col E C D\<close> by auto
      show "C E Par C' E'" 
        using \<open>C E Par C' E'\<close> by blast
      show "E D Par E' D'" 
        using Par_cases \<open>D E Par D' E'\<close> by blast
    qed
    moreover have "C' E' Par C E" 
      using Par_cases \<open>C E Par C' E'\<close> by blast
    ultimately show ?thesis 
      using \<open>C E Par C' E'\<close> par_col_par by blast
  qed
  ultimately show ?thesis 
    using par_col_par_2 \<open>Col E C D\<close> col_permutation_4 by blast
qed

lemma l13_19_par:
  assumes "X \<noteq> A" and
    "X \<noteq> A'" and 
  (*"X \<noteq> C" and 
    "X \<noteq> C'" and *) 
    "Y \<noteq> B" and 
    "Y \<noteq> B'" and
  (*"Y \<noteq> D" and
    "Y \<noteq> D'" and *)
    "Col X A C" and
    "Col X A A'" and
    "Col X A C'" and
    "Col Y B D" and
    "Col Y B B'" and
    "Col Y B D'" and
    "X A ParStrict Y B" and
    "A B Par A' B'" and
    "A D Par A' D'" and
    "B C Par B' C'"
  shows "C D Par C' D'" 
proof (cases "A = C")
  case True
  have "A' B' Par B' C'" 
    using Par_cases True assms(12) assms(14) par_trans by blast
  moreover have "A' B' ParStrict B' C' \<longrightarrow> ?thesis" 
    using Par_strict_cases not_par_strict_id by blast
  ultimately show ?thesis 
    by (metis Par_def True assms(6) assms(7) assms(9) assms(11) assms(13) 
        colx not_col_permutation_1 par_not_col)
next
  case False
  hence "A \<noteq> C"
    by simp
  show ?thesis 
  proof (cases "B = D")
    case True
    have "A' B' Par A' D'" 
      using True assms(12) assms(13) not_par_one_not_par par_symmetry by blast
    moreover have "A' B' ParStrict A' D' \<longrightarrow> ?thesis" 
      using not_par_strict_id by blast
    ultimately show ?thesis 
      by (metis True assms(6) assms(9) assms(10) assms(11) assms(14) colx 
          not_col_permutation_1 par_id_4 par_left_comm par_not_col par_right_comm)
  next
    case False
    hence "B \<noteq> D"
      by simp
    show ?thesis 
    proof (cases "A = A'")
      case True
      hence "A B ParStrict A' B' \<longrightarrow> ?thesis" 
        by (simp add: not_par_strict_id)
      moreover {
        assume "A \<noteq> B" and "A \<noteq> B'" and "Col A A B'" and "Col B A B'"
        have "B = B'" 
          by (metis Par_strict_cases True assms(9) assms(11) assms(12) 
              col2__eq par_id par_strict_not_col_2)
        hence "C = C'" 
          by (metis assms(7) assms(11) assms(14) assms(5) colx par_id_4 
              par_strict_not_col_4)
        moreover have "D = D'" 
          by (metis Par_strict_cases True assms(8) assms(10) assms(11) 
              assms(13) colx par_id_4 par_strict_not_col_1)
        ultimately have ?thesis 
          by (metis assms(7) assms(10) assms(11) not_col_permutation_1 
              par_not_col par_reflexivity)
      }
      ultimately show ?thesis 
        using True assms(12) col_trivial_1 par_distinct par_id_1 by force
    next
      case False
      hence "A \<noteq> A'"
        by simp
      show ?thesis 
      proof (cases "C D Par C' D'")
        case True
        then show ?thesis 
          by simp
      next
        case False
        hence "\<not> C D Par C' D'"
          by simp
        have "\<not> C D Par A B \<or> \<not> C' D' Par A B" 
          using False not_par_one_not_par by blast
        moreover have "\<not> C D Par A B \<longrightarrow> ?thesis" 
          by (meson \<open>A \<noteq> A'\<close> \<open>A \<noteq> C\<close> \<open>B \<noteq> D\<close> assms(1) assms(6) assms(7) 
              assms(8) assms(9) assms(10) assms(11) assms(12) assms(13) assms(14) assms(3) 
              assms(5) l13_19_par_aux par_symmetry)
        moreover {
          assume "\<not> C' D' Par A B"  
          have "A' \<noteq> B'" 
            using assms(12) par_neq2 by auto
          {
            assume "A' = C'"
            have "\<not> Col X A B" 
              using assms(11) par_strict_not_col_4 by auto
            moreover have "Col B A C" 
              using Par_cases \<open>A' = C'\<close> assms(12) assms(14) par_id_3 
                postulate_of_transitivity_of_parallelism_def 
                postulate_of_transitivity_of_parallelism_thm by blast
            ultimately have "A = C" 
              using assms(5) l6_16_1 by blast
            hence False 
              using \<open>A \<noteq> C\<close> by auto
          }
          moreover {
            assume "B' = D'" 
            hence "A D Par A B" 
              using \<open>B' = D'\<close> assms(12) assms(13) not_par_one_not_par by blast
            have "\<not> Col Y B A" 
              using assms(11) col_permutation_2 par_strict_not_col_2 by blast
            moreover have "Col A B D" 
              using \<open>A D Par A B\<close> par_id_3 by auto
            ultimately have False 
              using \<open>B \<noteq> D\<close> assms(8) col2__eq by blast
          }
          moreover have "A' \<noteq> A" 
            using \<open>A \<noteq> A'\<close> by auto
          moreover have "Col X A' C'" 
            using assms(1) assms(6) assms(7) col_transitivity_1 by blast
          moreover have "Col X A' A" 
            using Col_cases assms(6) by auto
          moreover have "Col X A' C" 
            using assms(1) assms(6) assms(5) col_transitivity_1 by blast
          moreover have "Col Y B' D'" 
            using assms(9) assms(10) assms(3) col_transitivity_1 by blast
          moreover have "Col Y B' B" 
            using Col_cases assms(9) by auto
          moreover have "Col Y B' D" 
            using assms(8) assms(9) assms(3) col_transitivity_1 by blast
          moreover have "X A' ParStrict Y B'" 
            by (meson assms(4) assms(9) assms(11) assms(2) assms(6) 
                not_col_distincts par_strict_col4__par_strict)
          moreover have "\<not> A' B' Par C' D'" 
            using Par_cases \<open>\<not> C' D' Par A B\<close> assms(12) par_trans by blast
          moreover have "A' B' Par A B" 
            using Par_cases assms(12) by blast
          moreover have "A' D' Par A D" 
            using Par_cases assms(13) by blast
          moreover have "B' C' Par B C" 
            using Par_cases assms(14) by blast
          ultimately have "C' D' Par C D" 
            using l13_19_par_aux assms(1) assms(6) assms(7) assms(8) 
              assms(9) assms(10) assms(2) assms(3) assms(4) assms(5) by presburger
          hence ?thesis 
            using Par_cases by blast
        }
        ultimately show ?thesis 
          by blast
      qed
    qed
  qed
qed

lemma sum_to_sump: 
  assumes "Sum PO E E' A B C"
  shows "Sump PO E E' A B C" 
proof -
  have "Ar2 PO E E' A B C" 
    using Sum_def assms by blast 
  obtain A' C' where "E E' Pj A  A'" and "Col PO E' A'" and 
    "PO E Pj A' C'" and "PO E' Pj B  C'" and "E' E Pj C' C"
    using Sum_def assms by blast 
  have "A A' Proj PO E' E E'"
    by (metis Ar2_def Pj_def Proj_def \<open>Ar2 PO E E' A B C\<close> \<open>Col PO E' A'\<close> \<open>E E' Pj A A'\<close> 
        not_col_distincts par_comm par_id_2 par_symmetry) 
  moreover 
  have "PO \<noteq> E"
    using Ar2_def \<open>Ar2 PO E E' A B C\<close> col_trivial_1 by force 
  then obtain P' where "PO E Par A' P'"     
    using parallel_existence1 by blast
  moreover have "B C' Proj A' P' PO E'"
    by (smt (verit) Ar2_def Par_perm Pj_def Proj_def \<open>Ar2 PO E E' A B C\<close> \<open>PO E Pj A' C'\<close> 
        \<open>PO E' Pj B C'\<close> calculation(1) calculation(2) par_col2_par_bis par_id par_id_1 par_trans) 
  moreover have "E \<noteq> E'"
    using Proj_def calculation(1) by presburger 
  hence "C' C Proj PO E E E'"
    by (metis Ar2_def Par_cases Pj_def Proj_def \<open>Ar2 PO E E' A B C\<close> \<open>E' E Pj C' C\<close> 
        \<open>PO \<noteq> E\<close> not_col_permutation_5 par_id_2) 
  ultimately show ?thesis
    using Ar2_def Sum_def Sump_def assms by auto 
qed

lemma sump_to_sum:
  assumes "Sump PO E E' A B C"
  shows "Sum PO E E' A B C" 
proof -
  have "Col PO E A "
    using Sump_def assms by blast 
  have "Col PO E B" 
    using Sump_def assms by blast 
  obtain A' C' P' where "A A' Proj PO E' E E'" and "PO E Par A' P'" and
    "B C' Proj A' P' PO E'" and "C' C Proj PO E E E'"     
    using Sump_def assms by blast 
  have "Ar2 PO E E' A B C"
    by (metis Ar2_def Proj_def \<open>B C' Proj A' P' PO E'\<close> \<open>C' C Proj PO E E E'\<close> \<open>Col PO E A\<close> 
        \<open>Col PO E B\<close> \<open>PO E Par A' P'\<close> par_col_par par_symmetry) 
  moreover have "E E' Pj A A'"
    using Pj_def \<open>A A' Proj PO E' E E'\<close> par_symmetry project_par_dir by blast 
  moreover have "Col PO E' A'"
    using Proj_def \<open>A A' Proj PO E' E E'\<close> by presburger 
  moreover have "PO E Pj A' C'"
    by (metis Pj_def Proj_def \<open>B C' Proj A' P' PO E'\<close> \<open>PO E Par A' P'\<close> par_col_par) 
  moreover have "PO E' Pj B C'"
    using Pj_def \<open>B C' Proj A' P' PO E'\<close> par_symmetry project_par_dir by blast 
  moreover have "E' E Pj C' C"
    using Par_perm Pj_def \<open>C' C Proj PO E E E'\<close> project_par_dir by blast 
  ultimately show ?thesis
    using Sum_def by blast
qed

lemma project_col_project: 
  assumes "A \<noteq> C"
    and "Col A B C"
    and "P P' Proj A B X Y"
  shows "P P' Proj A C X Y"
  by (metis (full_types) Proj_def assms(1) assms(2) assms(3) col3 col_trivial_3 
      not_par_not_col par_not_par) 

lemma (in Tarski_Euclidean) pj_uniqueness:
  assumes "\<not> Col PO E E'"
    and "Col PO E A"
    and "Col PO E' A'"
    and "Col PO E' A''"
    and "E E' Pj A A'"
    and "E E' Pj A A''"
  shows "A' = A''" 
proof (cases)
  assume "A = PO"
  thus ?thesis
    by (metis NCol_cases Par_cases Par_def Pj_def assms(1) assms(3) assms(4) 
        assms(5) assms(6) par_strict_not_col_4) 
next
  assume "A \<noteq> PO"
  thus ?thesis
    by (smt (verit) Par_cases Pj_def assms(1) assms(3) assms(4) assms(5) assms(6) 
        col_trivial_3 par_col2_par_bis par_id_2 par_not_par) 
qed

lemma (in Tarski_Euclidean) pj_right_comm: 
  assumes "A B Pj C D"
  shows "A B Pj D C"
  using Par_cases Pj_def assms by auto

lemma (in Tarski_Euclidean) pj_left_comm: 
  assumes "A B Pj C D" 
  shows "B A Pj C D"
  using Par_cases Pj_def assms by auto 

lemma (in Tarski_Euclidean) pj_comm: 
  assumes "A B Pj C D"
  shows "B A Pj D C"
  using assms pj_left_comm pj_right_comm by blast 

lemma (in Tarski_Euclidean(*_2D*)) grid_not_par_1:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "\<not> PO E Par E E'"
  using grid_ok par_id_1 par_left_comm by blast

lemma (in Tarski_Euclidean(*_2D*)) grid_not_par_2:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "\<not> PO E Par PO E'"
  using grid_ok par_id by blast

lemma (in Tarski_Euclidean(*_2D*))grid_not_par_3:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "\<not> PO E' Par E E'"
  using grid_ok par_comm par_id_2 by blast

lemma (in Tarski_Euclidean(*_2D*)) grid_not_par_4:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "PO \<noteq> E"
  using col_trivial_1 grid_ok by blast 

lemma (in Tarski_Euclidean(*_2D*)) grid_not_par_5:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "PO \<noteq> E'"
  using grid_ok not_col_distincts by blast

lemma (in Tarski_Euclidean(*_2D*)) grid_not_par_6:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "E \<noteq> E'"
  using grid_ok not_col_distincts by presburger 

lemma (in Tarski_Euclidean(*_2D*)) grid_not_par:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "\<not> PO E Par E E' \<and> \<not> PO E Par PO E' \<and> 
\<not> PO E' Par E E' \<and> PO \<noteq> E \<and> PO \<noteq> E' \<and> E \<noteq> E'"
  using grid_ok grid_not_par_1 grid_not_par_2 grid_not_par_3 grid_not_par_4 
    grid_not_par_5 grid_not_par_6 by blast 

lemma (in Tarski_Euclidean(*_2D*)) proj_id:
  assumes grid_ok: "\<not> Col PO E E'"
    and "A A' Proj PO E' E E'"
    and "Col PO E A"
    and "Col PO E A'"
  shows "A = PO" 
proof -
  have "A A' Par E E' \<or> A = A'"
    using Proj_def assms(2) by presburger 
  moreover {
    assume "A A' Par E E'"
    hence False
      using grid_ok assms(3) assms(4) grid_not_par_1 grid_not_par_4 
        par_col2_par_bis par_symmetry by blast 
  }
  moreover {
    assume "A = A'"
    hence ?thesis
      by (metis NCol_cases Proj_def assms(2) assms(3) grid_ok l6_16_1) 
  }
  ultimately show ?thesis
    by blast
qed

lemma (in Tarski_Euclidean(*_2D*)) sum_uniqueness:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B C1"
    and "Sum PO E E' A B C2"
  shows "C1 = C2" 
proof -
  have "Sump PO E E' A B C1"
    using assms(2) sum_to_sump by blast 
  then obtain A' C' P' where "A A' Proj PO E' E E'" and "PO E Par A' P'" and
    "B C' Proj A' P' PO E'" and "C' C1 Proj PO E E E'" 
    using Sump_def by blast
  have "Sump PO E E' A B C2" 
    using assms(3) sum_to_sump by blast 
  then obtain A'' C'' P'' where "A A'' Proj PO E' E E'" and "PO E Par A'' P''" and
    "B C'' Proj A'' P'' PO E'" and "C'' C2 Proj PO E E E'" 
    using Sump_def by blast
  have "A' = A''"
    using \<open>A A' Proj PO E' E E'\<close> \<open>A A'' Proj PO E' E E'\<close> project_uniqueness by auto 
  hence "Col A' P' P''"
    using Col_cases \<open>PO E Par A' P'\<close> \<open>PO E Par A'' P''\<close> col_trivial_1 
      parallel_uniqueness by blast 
  thus ?thesis
    by (metis par_distincts \<open>A' = A''\<close> \<open>B C' Proj A' P' PO E'\<close> 
        \<open>B C'' Proj A'' P'' PO E'\<close> \<open>C' C1 Proj PO E E E'\<close> \<open>C'' C2 Proj PO E E E'\<close> 
        \<open>PO E Par A'' P''\<close> project_col_project project_uniqueness) 
qed

lemma (in Tarski_Euclidean(*_2D*)) opp0:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "Opp PO E E' PO PO"
  using Ar2_def Opp_def Pj_def Sum_def col_trivial_3 grid_ok by auto 

lemma (in Tarski_neutral_dimensionless (*Tarski_Euclidean_2D*)) pj_trivial:
  shows "A B Pj C C"
  by (simp add: Pj_def) 

lemma (in Tarski_Euclidean(*_2D*)) sum_O_O:
  assumes grid_ok: "\<not> Col PO E E'"
  shows "Sum PO E E' PO PO PO"
  using Opp_def opp0 grid_ok by blast 

lemma (in Tarski_Euclidean(*_2D*)) sum_par_strict_a:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Ar2 PO E E' A B C"
    and "A \<noteq> PO"
    and "E E' Pj A A'"
    (*    and "Col PO E' A'"
    and "PO E Pj A' C'"
    and "PO E' Pj B C'"
    and "E' E Pj C' C"*)
  shows "A' \<noteq> PO"
  by (metis Ar2_def Pj_def grid_ok assms(2) assms(3) assms(4) col_trivial_3 
      grid_not_par_1 grid_not_par_4 par_col2_par_bis par_symmetry) 

lemma (in Tarski_Euclidean(*_2D*)) sum_par_strict_b:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Ar2 PO E E' A B C"
    and "A \<noteq> PO"
    and "E E' Pj A A'"
    and "Col PO E' A'"
    and "PO E Pj A' C'"
    and "PO E' Pj B C'"
    and "E' E Pj C' C"
  shows "(PO E ParStrict A' C' \<or> B = PO)" 
proof -
  have "Sum PO E E' A B C"
    using Sum_def assms(2) assms(4) assms(5) assms(6) assms(7) assms(8) by blast 
  have "A' \<noteq> PO"
    using grid_ok assms(2) assms(3) assms(4) sum_par_strict_a by blast 
  show ?thesis 
  proof (cases)
    assume "B = PO"
    thus ?thesis 
      by blast
  next
    assume" B \<noteq> PO"
    have "PO E ParStrict A' C'" 
    proof -
      have "PO E Par A' C' \<or> A' = C'"
        using Pj_def assms(6) by blast 
      moreover {
        assume "PO E Par A' C'"
        hence ?thesis
          by (metis Col_def Par_def \<open>A' \<noteq> PO\<close> assms(5) grid_ok l6_16_1) 
      }
      moreover {
        assume "A' = C'"
        hence ?thesis
          by (metis Ar2_def Pj_def \<open>B \<noteq> PO\<close> assms(2) assms(5) assms(7) 
              l6_16_1 not_col_distincts not_col_permutation_4 not_strict_par) 
      }
      ultimately show ?thesis
        by blast
    qed
    thus ?thesis 
      by blast
  qed
qed

lemma (in Tarski_Euclidean(*_2D*)) sum_par_strict:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Ar2 PO E E' A B C"
    and "A \<noteq> PO"
    and "E E' Pj A A'"
    and "Col PO E' A'"
    and "PO E Pj A' C'"
    and "PO E' Pj B C'"
    and "E' E Pj C' C"
  shows "A' \<noteq> PO \<and> (PO E ParStrict A' C' \<or> B = PO)"
  using assms sum_par_strict_a sum_par_strict_b by blast 

end
end