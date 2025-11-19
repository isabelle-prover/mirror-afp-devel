(* IsaGeoCoq - Tarski_Non_Euclidean_Aristotle.thy

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

theory Tarski_Non_Euclidean_Aristotle

imports
  Tarski_Non_Euclidean

begin

section "Tarski Non Euclidean Aristotle"

subsection "Definitions"

locale Tarski_Non_Euclidean_Aristotle = Tarski_Non_Euclidean +
  assumes aristotle: "aristotle_s_axiom"

context Tarski_Non_Euclidean_Aristotle

begin

subsection "Propositions"

lemma NPost03:
  shows "\<not> Postulate03" 
  using NPost02 Postulate02_def Postulate03_def aristotle aristotle__greenberg 
    playfair_bis__playfair triangle__playfair_bis by blast

lemma NPost21:
  shows "\<not> Postulate21" 
  using Cycle_3 NPost03 by blast

lemma NPost22:
  shows "\<not> Postulate22" 
  using Cycle_3 NPost21 by blast

lemma NPost23:
  shows "\<not> Postulate23" 
  using Cycle_3 NPost22 by blast

lemma NPost24:
  shows "\<not> Postulate24" 
  using Cycle_3 NPost23 by blast

lemma NPost25:
  shows "\<not> Postulate25" 
  using Cycle_3 NPost24 by blast

lemma NPost26:
  shows "\<not> Postulate26" 
  using Cycle_3 NPost25 by blast

lemma NPost27:
  shows "\<not> Postulate27" 
  using Cycle_3 NPost26 by blast

lemma NPost28:
  shows "\<not> Postulate28" 
  using Cycle_3 NPost27 by blast

lemma NPost29:
  shows "\<not> Postulate29" 
  using Cycle_3 NPost28 by blast

lemma NPost30:
  shows "\<not> Postulate30" 
  using Cycle_3 NPost29 by blast

theorem not_triangle_postulate_thm:
  shows "\<exists> A B C D E F. A B C TriSumA D E F \<and> \<not> Bet D E F"
  using NPost03 Postulate03_def triangle_postulate_def by blast

theorem not_postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights_thm:
  shows "\<forall> A B C D E F. A B C TriSumA D E F \<and> Bet D E F \<longrightarrow> Col A B C"
  using NPost21 Postulate21_def 
    postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights_def by blast

theorem not_posidonius_postulate_thm:
  shows "\<forall> A1 A2 B1 B2. Col A1 A2 B1 \<or> B1 = B2 \<or> \<not> Coplanar A1 A2 B1 B2 \<or>
                        (\<exists> A3 A4 B3 B4. Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> A1 A2 Perp A3 B3 \<and>
                                        Col A1 A2 A4 \<and> Col B1 B2 B4 \<and> A1 A2 Perp A4 B4 \<and> 
                                        \<not> Cong A3 B3 A4 B4) "
  using NPost22 Postulate22_def posidonius_postulate_def by blast

theorem not_posidonius_postulate_thm_1:
  shows "\<forall> A1 A2 B. Col A1 A2 B \<or> (\<exists> A3 A4 B3 B4. Col A1 A2 A3 \<and> Col B B B3 \<and> A1 A2 Perp A3 B3 \<and>
                                                  Col A1 A2 A4 \<and> Col B B B4 \<and> A1 A2 Perp A4 B4 \<and> 
                                                  \<not> Cong A3 B3 A4 B4)"
proof -
  {
    fix A1 A2 B
    have "Coplanar A1 A2 B B" 
      using ncop_distincts by blast
    assume "\<not> Col A1 A2 B" 
    hence "(\<exists> A3 A4 B3 B4. Col A1 A2 A3 \<and> Col B B B3 \<and> A1 A2 Perp A3 B3 \<and>
                           Col A1 A2 A4 \<and> Col B B B4 \<and> A1 A2 Perp A4 B4 \<and> 
                           \<not> Cong A3 B3 A4 B4)" 
      by (metis(full_types) col_trivial_1 ncop_distincts not_posidonius_postulate_thm)
  }
  thus ?thesis 
    by blast
qed

theorem not_postulate_of_existence_of_similar_triangles_thm:
  shows "\<forall> A B C D E F. (Col A B C \<or> Cong A B D E \<or> \<not> A B C CongA D E F \<or> 
                         \<not> B C A CongA E F D \<or> \<not> C A B CongA F D E)"
  using NPost23 Postulate23_def postulate_of_existence_of_similar_triangles_def by blast

theorem not_thales_postulate_thm:
  shows "\<exists> A B C M. M Midpoint A B \<and> Cong M A M C \<and> \<not> Per A C B" 
  using NPost24 Postulate24_def thales_postulate_def by blast

theorem not_thales_converse_postulate_thm:
  shows "\<exists> A B C M. M Midpoint A B \<and> Per A C B \<and> \<not> Cong M A M C" 
  using NPost25 Postulate25_def thales_converse_postulate_def by blast

theorem not_existential_thales_postulate_thm:
  shows "\<forall> A B C M. (M Midpoint A B \<and> Cong M A M C \<and> Per A C B) \<longrightarrow> Col A B C"
  using NPost26 Postulate26_def existential_thales_postulate_def by blast

theorem not_postulate_of_right_saccheri_quadrilaterals_thm:
  shows "\<exists> A B C D. Saccheri A B C D \<and> \<not> Per A B C" 
  using Cycle_3 NPost03 Postulate28_def ex_saccheri
    postulate_of_existence_of_a_right_saccheri_quadrilateral_def by blast

theorem not_postulate_of_existence_of_a_right_saccheri_quadrilateral_thm:
  shows "\<forall> A B C D. \<not> (Saccheri A B C D \<and> Per A B C)" 
  using Cycle_3 NPost26 Postulate28_def
    postulate_of_existence_of_a_right_saccheri_quadrilateral_def by blast

theorem not_postulate_of_right_lambert_quadrilaterals_thm:
  shows "\<exists> A B C D. Lambert A B C D \<and> \<not> Per B C D" 
  using Cycle_3 NPost26 Postulate30_def postulate_of_right_lambert_quadrilaterals_def 
    rectangle_principle__rectangle_existence by blast

theorem not_postulate_of_existence_of_a_right_lambert_quadrilateral_thm:
  shows "\<forall> A B C D. \<not> (Lambert A B C D \<and> Per B C D)" 
  using Cycle_3 NPost29 Postulate30_def 
    postulate_of_existence_of_a_right_lambert_quadrilateral_def by blast

end
end

