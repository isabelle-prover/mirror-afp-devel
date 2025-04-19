(* IsaGeoCoq - Tarski_Neutral_2D

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

theory Tarski_Neutral_2D

imports
  Tarski_Neutral

begin


subsection "Tarski's axiom system for neutral geometry: 2D"

locale Tarski_neutral_2D = Tarski_neutral_dimensionless +
  assumes upper_dim: "\<forall> a b c p q.
                      p \<noteq> q \<and>
                      Cong a p a q \<and>
                      Cong b p b q \<and>
                      Cong c p c q
                      \<longrightarrow>
                      (Bet a b c \<or> Bet b c a \<or> Bet c a b)"
context Tarski_neutral_2D

begin

lemma all_coplanar:
  "Coplanar A B C D"
proof -
  have "\<forall> A B C P Q. P \<noteq> Q \<longrightarrow> Cong A P A Q \<longrightarrow> Cong B P B Q\<longrightarrow> Cong C P C Q \<longrightarrow>
(Bet A B C \<or> Bet B C A \<or> Bet C A B)"
    using upper_dim by blast
  then show ?thesis using upper_dim_implies_all_coplanar
    by (smt Tarski_neutral_dimensionless.not_col_permutation_2 Tarski_neutral_dimensionless_axioms all_coplanar_axiom_def all_coplanar_implies_upper_dim coplanar_perm_9 ncop__ncol os__coplanar ts__coplanar upper_dim_implies_not_one_side_two_sides)
qed

lemma per2__col:
  assumes "Per A X C" and
    "X \<noteq> C" and
    "Per B X C"
  shows "Col A B X"
  using all_coplanar_axiom_def all_coplanar_upper_dim assms(1) assms(2) assms(3) upper_dim upper_dim_implies_per2__col by blast

lemma perp2__col:
  assumes "X Y Perp A B" and
    "X Z Perp A B"
  shows "Col X Y Z"
  by (meson Tarski_neutral_dimensionless.cop_perp2__col Tarski_neutral_dimensionless_axioms all_coplanar assms(1) assms(2))

lemma l12_9_2D:
  assumes "A1 A2 Perp C1 C2" and
    "B1 B2 Perp C1 C2"
  shows "A1 A2 Par B1 B2"
  using l12_9 all_coplanar assms(1) assms(2) by auto

lemma perp_in2__col:
  assumes "P PerpAt A B X Y" and
    "P PerpAt A' B' X Y"
  shows "Col A B A'"
  using cop4_perp_in2__col all_coplanar assms by blast

lemma perp2_trans:
  assumes "P Perp2 A B C D" and
    "P Perp2 C D E F"
  shows "P Perp2 A B E F"
proof -
  obtain X Y where P1: "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms(1) by blast
  obtain X' Y' where P2: "Col P X' Y' \<and> X' Y' Perp C D \<and> X' Y' Perp E F"
    using Perp2_def assms(2) by blast
  {
    assume "X Y Par X' Y'"
    then have P3: "X Y ParStrict X' Y' \<or> (X \<noteq> Y \<and> X' \<noteq> Y' \<and> Col X X' Y' \<and> Col Y X' Y')"
      using Par_def by blast
    {
      assume "X Y ParStrict X' Y'"
      then have "P Perp2 A B E F"
        using P1 P2 par_not_col by auto
    }
    {
      assume "X \<noteq> Y \<and> X' \<noteq> Y' \<and> Col X X' Y' \<and> Col Y X' Y'"
      then have "P Perp2 A B E F"
        by (meson P1 P2 Perp2_def col_permutation_1 perp_col2)
    }
    then have "P Perp2 A B E F"
      using P3 \<open>X Y ParStrict X' Y' \<Longrightarrow> P Perp2 A B E F\<close> by blast
  }
  {
    assume "\<not> X Y Par X' Y'"
    then have "P Perp2 A B E F"
      using P1 P2 l12_9_2D by blast
  }
  thus ?thesis
    using \<open>X Y Par X' Y' \<Longrightarrow> P Perp2 A B E F\<close> by blast
qed

lemma perp2_par:
  assumes "PO Perp2 A B C D"
  shows "A B Par C D"
  using Perp2_def l12_9_2D Perp_perm assms by blast

lemma not_par_strict_inter_exists:
  assumes "\<not> A1 B1 ParStrict A2 B2" 
  shows "\<exists> X. Col X A1 B1 \<and> Col X A2 B2" 
  using ParStrict_def all_coplanar assms by presburger

lemma not_par_inter_exists:
  assumes "\<not> A1 B1 Par A2 B2" 
  shows "\<exists> X. Col X A1 B1 \<and> Col X A2 B2" 
  using all_coplanar assms cop_npar__inter_exists by blast

end
end