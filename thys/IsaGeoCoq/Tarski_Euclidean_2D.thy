(* IsaGeoCoq - Tarski_Euclidean_2D.thy

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

theory Tarski_Euclidean_2D

imports
  Tarski_Neutral
  Tarski_Postulate_Parallels
  Tarski_Euclidean
  Tarski_Neutral_2D

begin

section "Tarski Euclidean 2D"

subsection "Tarski's axiom system for Euclidean 2D"

locale Tarski_Euclidean_2D = Tarski_Euclidean +
  assumes upper_dim: "\<forall> a b c p q.
                      p \<noteq> q \<and>
                      Cong a p a q \<and>
                      Cong b p b q \<and>
                      Cong c p c q
                      \<longrightarrow>
                      (Bet a b c \<or> Bet b c a \<or> Bet c a b)"

sublocale Tarski_Euclidean_2D \<subseteq> Tarski_neutral_2D
proof 
  show "\<forall> a b c p q.
                      p \<noteq> q \<and>
                      Cong a p a q \<and>
                      Cong b p b q \<and>
                      Cong c p c q
                      \<longrightarrow>
                      (Bet a b c \<or> Bet b c a \<or> Bet c a b)" 
    using upper_dim by blast
qed

context Tarski_Euclidean_2D

begin

subsection "Definitions"

subsection "Propositions"

lemma l12_16_2D:
  assumes "A1 A2 Par B1 B2" and
    "X Inter A1 A2 C1 C2"
  shows "\<exists> Y. Y Inter B1 B2 C1 C2" 
proof -
  have "Coplanar B1 B2 C1 C2" 
    using all_coplanar by blast
  thus ?thesis 
    using l12_16 using assms(1) assms(2) by blast
qed

lemma par_inter:
  assumes "A B Par C D" and
    "\<not> A B Par P Q"
  shows "\<exists> Y. Col P Q Y \<and> Col C D Y" 
  using all_coplanar assms(1) assms(2) cop_par__inter by blast

lemma not_par_inter:
  assumes "\<not>  A B Par A' B'" 
  shows "\<exists> P. Col P X Y \<and> (Col P A B \<or> Col P A' B')" 
proof -
  have "Coplanar A B X Y" 
    by (simp add: all_coplanar)
  moreover
  have "Coplanar A' B' X Y" 
    by (simp add: all_coplanar)
  ultimately
  show ?thesis 
    by (simp add: assms cop2_npar__inter)
qed

lemma par_perp__perp: 
  assumes "A B Par C D" and
    "A B Perp P Q" 
  shows "C D Perp P Q" 
  using all_coplanar assms(1) assms(2) cop_par_perp__perp by blast

lemma par_perp2__par:
  assumes "A B Par C D" and
    "A B Perp E F" and
    "C D Perp G H"
  shows "E F Par G H" 
  using all_coplanar assms(1) assms(2) assms(3) cop4_par_perp2__par by blast

lemma perp3__perp:
  assumes "A B Perp B C" and
    "B C Perp C D" and
    "C D Perp D A" 
  shows "D A Perp A B" 
proof -
  have "Coplanar A B C D" 
    by (simp add: all_coplanar)
  thus ?thesis 
    using assms(1) assms(2) assms(3) cop_perp3__perp by blast
qed

lemma perp3__rect:
  assumes "A B Perp B C" and
    "B C Perp C D" and
    "C D Perp D A"
  shows "Rectangle A B C D" 
proof -
  have "Coplanar A B C D" 
    by (simp add: all_coplanar)
  thus ?thesis  
    using assms(1) assms(2) assms(3) cop_perp3__rect by blast
qed

end
end