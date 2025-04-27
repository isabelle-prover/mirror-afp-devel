(* IsageoCoq -  Tarski_Neutral_2D_Model_Gupta_Neutral_2D.thy
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

theory Tarski_Neutral_2D_Model_Gupta_Neutral_2D

imports 
Gupta_Neutral_2D
Tarski_Neutral_2D

begin
(*
context Gupta_neutral_2D

begin

interpretation Interpretation_Tarski_neutral_dimensionless: Tarski_neutral_dimensionless 
where TPA = GPA and TPB = GPB and TPC = GPC and Bet = BetG and Cong = CongG 
proof 
show "\<forall>a b. CongG a b b a" 
by (simp add: cong_pseudo_reflexivityG)
show "\<forall>a b p q r s. CongG a b p q \<and> CongG a b r s \<longrightarrow> CongG p q r s" 
using cong_inner_transitivityG by blast
show "\<forall>a b c. CongG a b c c \<longrightarrow> a = b" 
by (simp add: cong_identityG)
show "\<forall>a b c q. \<exists>x. BetG q a x \<and> CongG a x b c" 
by (simp add: segment_constructionG)
show "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> BetG a b c \<and> BetG a' b' c' \<and> 
CongG a b a' b' \<and> CongG b c b' c' \<and> CongG a d a' d' \<and> CongG b d b' d' \<longrightarrow>
CongG c d c' d'" 
using five_segmentG by blast
show "\<forall>a b. BetG a b a \<longrightarrow> a = b" 
by (simp add: between_identityT)
show "\<forall>a b c p q. BetG a p c \<and> BetG b q c \<longrightarrow> (\<exists>x. BetG p x b \<and> BetG q x a)" 
using inner_paschT by blast
show "\<not> BetG GPA GPB GPC \<and> \<not> BetG GPB GPC GPA \<and> \<not> BetG GPC GPA GPB" 
using lower_dimG by blast
qed

subsection "Transport theorem from Tarski Neutral for Gupta Euclidean Model"

lemma g_l5_2: 
assumes "A \<noteq> B" and
"BetG A B C" and
"BetG A B D"
shows "BetG B C D \<or> BetG B D C" 
using Interpretation_Tarski_neutral_dimensionless.l5_2 assms(1) assms(2) assms(3) by blast

lemma g_l5_3:
assumes "BetG A B D" and
"BetG A C D"
shows "BetG A B C \<or> BetG A C B" 
using Interpretation_Tarski_neutral_dimensionless.l5_3 assms(1) assms(2) by blast

lemma g_between_exchange4:
assumes "BetG A B C" and
"BetG A C D"
shows "BetG A B D"
using assms(1) assms(2) 
Interpretation_Tarski_neutral_dimensionless.between_exchange4 by blast

lemma g_between_inner_transitivity:
assumes "BetG A B D" and
"BetG B C D"
shows "BetG A B C"
using assms(1) assms(2) 
Interpretation_Tarski_neutral_dimensionless.between_inner_transitivity by blast

lemma g_not_bet_distincts: 
assumes "\<not> BetG A B C"
shows "A \<noteq> B \<and> B \<noteq> C"
using assms Interpretation_Tarski_neutral_dimensionless.not_bet_distincts by blast

lemma g_between_symmetry:
assumes "BetG A B C"
shows "BetG C B A"
using assms Interpretation_Tarski_neutral_dimensionless.between_symmetry by blast

lemma g_between_trivial:
shows "BetG A B B"
using Interpretation_Tarski_neutral_dimensionless.between_trivial by blast

end
*)
context Gupta_neutral_2D

begin

interpretation Interpretation_Tarski_neutral_2D : Tarski_neutral_2D
where TPA = GPA and TPB = GPB and TPC = GPC and Bet = BetG and Cong = CongG   
proof 
show "\<forall>a b. CongG a b b a" 
by (simp add: cong_pseudo_reflexivityG)
show "\<forall>a b p q r s. CongG a b p q \<and> CongG a b r s \<longrightarrow> CongG p q r s" 
using cong_inner_transitivityG by blast
show "\<forall>a b c. CongG a b c c \<longrightarrow> a = b" 
by (simp add: cong_identityG)
show "\<forall>a b c q. \<exists>x. BetG q a x \<and> CongG a x b c" 
by (simp add: segment_constructionG)
show "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> BetG a b c \<and> BetG a' b' c' \<and> 
CongG a b a' b' \<and> CongG b c b' c' \<and> CongG a d a' d' \<and> CongG b d b' d' \<longrightarrow>
CongG c d c' d'" 
using five_segmentG by blast
show "\<forall>a b. BetG a b a \<longrightarrow> a = b" 
by (simp add: between_identityT)
show "\<forall>a b c p q. BetG a p c \<and> BetG b q c \<longrightarrow> (\<exists>x. BetG p x b \<and> BetG q x a)" 
using inner_paschT by blast
show "\<not> BetG GPA GPB GPC \<and> \<not> BetG GPB GPC GPA \<and> \<not> BetG GPC GPA GPB" 
using lower_dimG by blast
show "\<forall>a b c p q.
p \<noteq> q \<and> CongG a p a q \<and> CongG b p b q \<and> CongG c p c q \<longrightarrow>
BetG a b c \<or> BetG b c a \<or> BetG c a b" using upper_dimT by blast
qed

end
end