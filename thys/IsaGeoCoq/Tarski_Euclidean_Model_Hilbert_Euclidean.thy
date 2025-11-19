(* IsageoCoq - Tarski_Euclidean_Model_Hilbert_Euclidean.thy
Port part of GeoCoq 3.4.0 (https://geocoq.github.io/GeoCoq/)

Version 2.0.0 IsaGeoCoq
Copyright (C) 2021-2025 Roland Coghetto roland.coghetto ( a t ) cafr-msa2p.be

History
Version 1.0.0 IsaGeoCoq
Port part of GeoCoq 3.4.0 (https://geocoq.github.io/GeoCoq/) in Isabelle/Hol (Isabelle2021)
Copyright (C) 2021  Roland Coghetto roland_coghetto (at) hotmail.com

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

theory Tarski_Euclidean_Model_Hilbert_Euclidean

imports 
  Hilbert_Euclidean
  Tarski_Neutral_3D_Model_Hilbert_Neutral_3D

begin
 
section "Tarski Euclidean Model Hilbert Euclidean"

context Hilbert_Euclidean

begin

interpretation Heucl_to_Teucl : Tarski_Euclidean
  where Bet = Bet and
    Cong = Cong and
    TPA = PP and
    TPB = PQ  and
    TPC = PR 
proof 
  show "\<forall>a b. Cong a b b a" 
    using cong_permT by blast
  show "\<forall>a b p q r s. Cong a b p q \<and> Cong a b r s \<longrightarrow> Cong p q r s" 
    using cong_inner_transitivity by blast
  show "\<forall>a b c. Cong a b c c \<longrightarrow> a = b" 
    by (simp add: cong_identity)
  show "\<forall>a b c q. \<exists>x. Bet q a x \<and> Cong a x b c" 
    by (simp add: segment_construction)
  show "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> Bet a b c \<and> Bet a' b' c' \<and>
          Cong a b a' b' \<and> Cong b c b' c' \<and> Cong a d a' d' \<and> Cong b d b' d' \<longrightarrow>
          Cong c d c' d'" 
    using five_segment by blast
  show "\<forall>a b. Bet a b a \<longrightarrow> a = b" 
    using bet_identity by blast
  show "\<forall>a b c p q. Bet a p c \<and> Bet b q c \<longrightarrow> (\<exists>x. Bet p x b \<and> Bet q x a)" 
  proof -
    {
      fix a b c p q
      assume "Bet a p c" and "Bet b q c" and
        "Bet a b c \<or> Bet b c a \<or> Bet c a b" 
      hence "\<exists>x. Bet p x b \<and> Bet q x a" 
        using Bet_def bet_comm bet_trans by metis
    }
    moreover
    {
      fix a b c p q
      assume "Bet a p c" and "Bet b q c" and
        "\<not> (Bet a b c \<or> Bet b c a \<or> Bet c a b)" and
        "a = p \<or> p = c \<or> b = q \<or> q = c" 
      hence "\<exists>x. Bet p x b \<and> Bet q x a" 
        by (metis Hilbert_neutral_dimensionless_pre.Bet_def bet_comm)
    }
    moreover
    {
      fix a b c p q
      assume "Bet a p c" and "Bet b q c" and
        "\<not> (Bet a b c \<or> Bet b c a \<or> Bet c a b)" and
        "a \<noteq> p" and "p \<noteq> c" and "b \<noteq> q" and "q \<noteq> c" 
      hence "\<exists>x. Bet p x b \<and> Bet q x a" 
        using pasch_general_case by blast
    }
    ultimately show ?thesis
      by blast
  qed
  show "\<not> Bet PP PQ PR \<and> \<not> Bet PQ PR PP \<and> \<not> Bet PR PP PQ" 
    using lower_dim_l by blast
  show  "\<forall>A B C D T. Bet A D T \<and> Bet B D C \<and> A \<noteq> D 
            \<longrightarrow> (\<exists>X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y)"
    using tarski_s_euclid euclid_uniqueness by blast
qed

end

end
