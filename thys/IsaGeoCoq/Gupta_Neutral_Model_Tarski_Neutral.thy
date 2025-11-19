(* IsageoCoq - Gupta_Neutral_Model_Tarski_Neutral.thy
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

theory Gupta_Neutral_Model_Tarski_Neutral

imports 
Tarski_Neutral
Gupta_Neutral

begin

context Tarski_neutral_dimensionless

begin

interpretation Interpretation_Gupta_neutral_dimensionless : Gupta_neutral_dimensionless 
  where GPA = TPA and GPB = TPB and GPC = TPC and BetG = Bet and CongG = Cong
proof
  show "\<forall>a b. Cong a b b a" 
    by (simp add: cong_pseudo_reflexivity)
  show "\<forall>a b p q r s. Cong a b p q \<and> Cong a b r s \<longrightarrow> Cong p q r s" 
    using cong_inner_transitivity by blast
  show "\<forall>a b c. Cong a b c c \<longrightarrow> a = b" 
    using cong_diff by blast
  show "\<forall>a b c q. \<exists>x. Bet q a x \<and> Cong a x b c" 
    using segment_construction by force
  show "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> Bet a b c \<and> Bet a' b' c' \<and> 
           Cong a b a' b' \<and> Cong b c b' c' \<and> Cong a d a' d' \<and> Cong b d b' d' \<longrightarrow>
       Cong c d c' d'" 
    using five_segment by blast
  show "\<forall>a b c. Bet a b c \<longrightarrow> Bet c b a" 
    using between_symmetry by blast
  show "\<forall>a b c d. Bet a b d \<and> Bet b c d \<longrightarrow> Bet a b c" 
    using between_inner_transitivity by blast
  show "\<forall>a b c p q.
       Bet a p c \<and> Bet b q c \<and> a \<noteq> p \<and> c \<noteq> p \<and> b \<noteq> q \<and> c \<noteq> q \<and> 
       \<not> (Bet a b c \<or> Bet b c a \<or> Bet c a b) \<longrightarrow>
       (\<exists>x. Bet p x b \<and> Bet q x a)" 
    using inner_pasch by blast
  show "\<not> (Bet TPA TPB TPC \<or> Bet TPB TPC TPA \<or> Bet TPC TPA TPB)" 
    by (simp add: lower_dim)
qed

end
end