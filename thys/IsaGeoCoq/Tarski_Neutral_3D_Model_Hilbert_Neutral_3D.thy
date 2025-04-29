(* IsageoCoq - Tarski_Neutral_3D_Model_Hilbert_Neutral_3D.thy
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

theory Tarski_Neutral_3D_Model_Hilbert_Neutral_3D

imports 
  Tarski_Neutral_3D
  Hilbert_Neutral_3D
  Tarski_Neutral_Model_Hilbert_Neutral

begin

section "Tarski Neutral 3D - Hilbert Neutral 3D Model"

context Hilbert_neutral_3D

begin

interpretation H3D_to_T3D : Tarski_neutral_3D
  where Bet = Bet and
    Cong = Cong and
    TPA = PP and
    TPB = PQ  and
    TPC = PR and
    TS1 = HS1 and TS2 = HS2 and TS3 = HS3 and TS4 = HS4
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
  show "\<nexists>X. (Bet HS1 HS2 X \<or> Bet HS2 X HS1 \<or> Bet X HS1 HS2) \<and>
            (Bet HS3 HS4 X \<or> Bet HS4 X HS3 \<or> Bet X HS3 HS4) \<or>
            (Bet HS1 HS3 X \<or> Bet HS3 X HS1 \<or> Bet X HS1 HS3) \<and>
            (Bet HS2 HS4 X \<or> Bet HS4 X HS2 \<or> Bet X HS2 HS4) \<or>
            (Bet HS1 HS4 X \<or> Bet HS4 X HS1 \<or> Bet X HS1 HS4) \<and>
            (Bet HS2 HS3 X \<or> Bet HS3 X HS2 \<or> Bet X HS2 HS3)" 
    using coplanar_plane1 lower_dim_3 by blast
  show "\<forall>A B C P Q R. P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and> Cong A P A Q \<and>
    Cong B P B Q \<and> Cong C P C Q \<and> Cong A P A R \<and> Cong B P B R \<and> Cong C P C R \<longrightarrow>
    Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using tarski_upper_dim plane_intersection lower_dim_3 by blast
qed

end
end
