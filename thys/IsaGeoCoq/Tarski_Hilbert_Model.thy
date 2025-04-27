(* IsageoCoq2_R1

Highschool3.thy

Version 2.3.0 IsaGeoCoq2_R1, Port part of GeoCoq 3.4.0
(* GeoCoq : hilbert_to_tarski.v *)

Copyright (C) 2021-2025 Roland Coghetto roland.coghetto ( a t ) cafr-msa2p.be
License: LGPL

History
Version 1.0.0: IsaGeoCoq
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


(*<*)
theory Tarski_Hilbert_Model

imports 
  Tarski_3D
  Tarski_Euclidean
  Tarski_Postulate_Parallels 
  Hilbert
  Gupta

begin
  (*>*)

section "Tarski - Hilbert Model"

context Hilbert_neutral_dimensionless

begin

definition (in Hilbert_neutral_dimensionless_pre) Bet :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 
  where
    "Bet A B C \<equiv> BetH A B C \<or> A = B \<or> B = C"

definition (in Hilbert_neutral_dimensionless_pre) Cong :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 
  where
    "Cong A B C D \<equiv> (CongH A B C D \<and> A \<noteq> B \<and> C \<noteq> D) \<or> (A = B \<and> C = D)"

definition (in Hilbert_neutral_dimensionless) ParaP :: "TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>TPoint\<Rightarrow>bool" 
  where
    "ParaP A B C D \<equiv> \<forall> l m. 
                      IsL l \<and> IsL m \<and> IncidL A l \<and> IncidL B l \<and> IncidL C m \<and> IncidL D m 
                      \<longrightarrow> 
                      Para l m"

definition (in Hilbert_neutral_dimensionless_pre) is_line :: "TPoint \<Rightarrow> TPoint \<Rightarrow> 'b \<Rightarrow>bool" 
  where
    "is_line A B l \<equiv> (IsL l \<and> A \<noteq> B \<and> IncidL A l \<and> IncidL B l)"

definition (in Hilbert_neutral_dimensionless_pre) cut' :: 
  "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint \<Rightarrow> bool" 
  where
    "cut' A B X Y \<equiv> X \<noteq> Y \<and> (\<forall> l. (IsL l \<and> IncidL X l \<and> IncidL Y l) \<longrightarrow> cut l A B)"

definition (in Hilbert_neutral_dimensionless_pre) Midpoint :: "TPoint \<Rightarrow> TPoint \<Rightarrow> TPoint\<Rightarrow>bool" 
  ("_ Midpoint _ _" [99,99,99] 50)
  where "M Midpoint A B \<equiv> Bet A M B \<and> Cong A M M B"

lemma betH_distincts: 
  assumes "BetH A B C"
  shows "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" 
  using assms between_comm between_diff between_only_one by blast

(** Hilbert's congruence is 'defined' only for non degenerated segments,
while Tarski's segment congruence allows the null segment. *)

lemma congH_perm: 
  assumes "A \<noteq> B"
  shows "CongH A B B A"
proof -
  obtain l where "IsL l" and "IncidL A l" and "IncidL B l"
    using assms line_existence by fastforce
  moreover
  {
    fix x
    assume "IncidL x l" and 
      "outH A B x" and 
      "CongH A x A B"
    hence "CongH A x B A" 
      by (simp add: cong_permr)
    hence "CongH A B B A" 
      using \<open>CongH A x A B\<close> cong_pseudo_transitivity by blast
  }
  hence "\<forall> x. (IncidL x l \<and> outH A B x \<and> CongH A x A B) \<longrightarrow> CongH A B B A" 
    by blast
  ultimately show ?thesis 
    using assms cong_existence by presburger
qed

lemma congH_refl: 
  assumes "A \<noteq> B" 
  shows "CongH A B A B" 
  by (simp add: assms congH_perm cong_permr)

lemma congH_sym: 
  assumes "A \<noteq> B" and
    "CongH A B C D"
  shows "CongH C D A B" 
  using assms(1) assms(2) congH_refl cong_pseudo_transitivity by blast

lemma colH_permut_231: 
  assumes "ColH A B C"
  shows "ColH B C A" 
  using ColH_def assms by blast

lemma colH_permut_312:
  assumes "ColH A B C"
  shows "ColH C A B" 
  by (simp add: assms colH_permut_231)

lemma colH_permut_213:
  assumes "ColH A B C"
  shows "ColH B A C" 
  using ColH_def assms by auto

lemma colH_permut_132:
  assumes "ColH A B C"
  shows "ColH A C B" 
  using ColH_def assms by auto

lemma colH_permut_321:
  assumes "ColH A B C"
  shows "ColH C B A" 
  using ColH_def assms by auto

lemma other_point_exists: 
  fixes A::TPoint
  shows "\<exists> B. A \<noteq> B" 
  by (metis lower_dim_2)

lemma colH_trivial111:
  shows "ColH A A A" 
  using cong_4_existence same_side'_def by blast

lemma colH_trivial112:
  shows "ColH A A B" 
  using colH_permut_231 cong_4_existence same_side'_def by blast

lemma colH_trivial122:
  shows "ColH A B B" 
  by (simp add: colH_permut_312 colH_trivial112)

lemma colH_trivial121:
  shows "ColH A B A" 
  by (simp add: colH_permut_312 colH_trivial122)

lemma colH_dec:
  shows "ColH A B C \<or> \<not> ColH A B C" 
  by blast

lemma colH_trans:
  assumes "X \<noteq> Y" and
    "ColH X Y A" and
    "ColH X Y B" and
    "ColH X Y C"
  shows "ColH A B C"
proof -
  obtain l where "IsL l" and "IncidL X l" and "IncidL Y l" and "IncidL A l" 
    using ColH_def assms(2) by blast
  obtain m where "IsL m" and "IncidL X m" and "IncidL Y m" and "IncidL B m" 
    using ColH_def assms(3) by blast
  obtain n where "IsL n" and "IncidL X n" and "IncidL Y n" and "IncidL C n" 
    using ColH_def assms(4) by blast
  have "EqL l m" 
    using line_uniqueness \<open>IncidL B m\<close> assms(1) \<open>IncidL X l\<close> \<open>IncidL Y l\<close> 
      \<open>IncidL X m\<close> \<open>IncidL Y m\<close> \<open>IsL m\<close> \<open>IsL l\<close> by blast
  hence "IncidL B l" 
    using EqL_sym IncidL_morphism \<open>IncidL B m\<close> \<open>IsL l\<close> \<open>IsL m\<close> by blast
  moreover have "IncidL C l"   
    by (meson IncidL_morphism \<open>IncidL C n\<close> \<open>IncidL X l\<close> \<open>IncidL X n\<close> \<open>IncidL Y l\<close>
        \<open>IncidL Y n\<close> \<open>IsL l\<close> \<open>IsL n\<close> assms(1) line_uniqueness)
  ultimately show ?thesis
    using ColH_def \<open>IncidL A l\<close> \<open>IsL l\<close> by blast
qed

lemma bet_colH:
  assumes "Bet A B C" 
  shows "ColH A B C" 
  using Bet_def assms between_col colH_trivial112 colH_trivial122 by blast

lemma ncolH_exists: 
  assumes "A \<noteq> B"
  shows "\<exists> C. \<not> ColH A B C" 
  using assms colH_trans lower_dim_2 by blast

lemma ncolH_distincts: 
  assumes "\<not> ColH A B C"
  shows "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" 
  using assms colH_trivial112 colH_trivial121 colH_trivial122 by blast

lemma betH_expand: 
  assumes "BetH A B C" 
  shows "BetH A B C \<and> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> ColH A B C" 
  using assms betH_distincts between_col by presburger

lemma inter_uniquenessH: 
  assumes "A' \<noteq> B'" and
    "\<not> ColH A B A'" and
    "ColH A B X" and
    "ColH A B Y" and
    "ColH A' B' X" and
    "ColH A' B' Y"
  shows "X = Y"
proof -
  have "A \<noteq> B" 
    using assms(2) colH_trivial112 by blast
  thus ?thesis
    by (metis (full_types) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
        colH_permut_231 colH_trans colH_trivial121)
qed

lemma inter_incid_uniquenessH:
  assumes "\<not> IncidL P l" and
    "IncidL P m" and 
    "IncidL X l" and
    "IncidL Y l" and
    "IncidL X m" and
    "IncidL Y m"
  shows "X = Y" 
proof -
  have "IsL l" 
    using Is_line assms(4) by blast
  then  obtain A B where "IncidL B l" and "IncidL A l" and "A \<noteq> B" 
    using two_points_on_line by blast
  have "IsL m" 
    using Is_line assms(5) by blast
  then obtain A' B' where "IncidL B' m" and "IncidL A' m" and "A' \<noteq> B'"
    using two_points_on_line by blast
  have "ColH A B X" 
    using ColH_def Is_line \<open>IncidL A l\<close> \<open>IncidL B l\<close> assms(3) by blast
  have "ColH A B Y" 
    using ColH_def Is_line \<open>IncidL A l\<close> \<open>IncidL B l\<close> assms(4) by blast
  have "ColH A' B' X" 
    using ColH_def Is_line \<open>IncidL A' m\<close> \<open>IncidL B' m\<close> assms(5) by blast
  have "ColH A' B' Y" 
    using ColH_def Is_line \<open>IncidL A' m\<close> \<open>IncidL B' m\<close> assms(6) by blast
  {
    assume "ColH A B P"
    then obtain l00 where "IsL l00" and "IncidL A l00" and "IncidL B l00" and "IncidL P l00" 
      using ColH_def by blast
    hence "EqL l l00" 
      using \<open>A \<noteq> B\<close> \<open>IncidL A l\<close> \<open>IncidL B l\<close> \<open>IsL l\<close> line_uniqueness by blast
    hence "IncidL P l" 
      using EqL_sym IncidL_morphism \<open>IncidL P l00\<close> \<open>IsL l00\<close> \<open>IsL l\<close> by blast
    hence False 
      using assms(1) by blast
  }
  hence "\<not> ColH A B P" 
    by blast
  {
    assume "A' = P"
    hence "X = Y" 
      using \<open>A' \<noteq> B'\<close> \<open>ColH A B X\<close> \<open>ColH A B Y\<close> \<open>ColH A' B' X\<close> \<open>ColH A' B' Y\<close> \<open>\<not> ColH A B P\<close> 
        inter_uniquenessH by blast
  }
  moreover
  {
    assume "A' \<noteq> P"
    hence "X = Y" 
      using IncidL_morphism \<open>IsL l\<close> \<open>IsL m\<close> assms(1) assms(2) assms(3) assms(4) assms(5) 
        assms(6) line_uniqueness by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma between_only_one': 
  assumes "BetH A B C" (*and
"\<not> BetH B C A"*)
  shows "\<not> BetH B A C" 
  using assms(1) between_comm between_only_one by blast

lemma betH_colH: 
  assumes "BetH A B C"
  shows "ColH A B C \<and> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" 
  using assms betH_expand by presburger

lemma cut_comm: 
  assumes "cut l A B"
  shows "cut l B A" 
  using assms between_comm local.cut_def by blast

lemma line_on_plane': 
  assumes "A \<noteq> B" and
    "IncidP A p" and 
    "IncidP B p" and
    "ColH A B C"
  shows "IncidP C p" 
  using ColH_def IncidLP_def Is_plane assms(1) assms(2) assms(3) assms(4) line_on_plane by blast

lemma inner_pasch_aux:
  assumes "\<not> ColH B C P" and
    "Bet A P C" and
    "Bet B Q C"
  shows "\<exists> X. Bet P X B \<and> Bet Q X A" 
proof -
  have "BetH A P C \<or> A = P \<or> P = C" 
    using Bet_def assms(2) by presburger
  moreover
  have "BetH B Q C \<or> B = Q \<or> Q = C" 
    using Bet_def assms(3) by blast
  moreover
  let ?t = "\<exists> X. Bet P X B \<and> Bet Q X A"
  have "BetH A P C \<and> BetH B Q C \<longrightarrow> ?t"
  proof -
    {
      assume "Q \<noteq> A" and
        "BetH A P C" and "BetH B Q C"
      obtain l where "IsL l" and "IncidL Q l" and "IncidL A l" 
        using \<open>Q \<noteq> A\<close> line_existence by blast
      {
        assume "P = A"
        hence ?t 
          using Bet_def by blast
      }
      moreover
      {
        assume "P \<noteq> A"
        {
          assume "Q = C"
          hence ?t 
            using \<open>BetH B Q C\<close> betH_distincts by auto
        }
        moreover
        {
          assume "Q \<noteq> C"
          {
            assume "IncidL P l"
            have "ColH A P C" 
              using \<open>BetH A P C\<close> betH_colH by blast
            have "ColH B Q C" 
              by (simp add: \<open>BetH B Q C\<close> between_col)
            have "ColH A P Q" 
              using ColH_def \<open>IncidL A l\<close> \<open>IncidL P l\<close> \<open>IncidL Q l\<close> \<open>IsL l\<close> by blast
            have "ColH P C Q" 
              by (meson ColH_def \<open>ColH A P C\<close> \<open>IncidL A l\<close> \<open>IncidL P l\<close> \<open>IncidL Q l\<close> 
                  \<open>P \<noteq> A\<close> inter_incid_uniquenessH)
            have "ColH B C P" 
              by (metis inter_uniquenessH \<open>ColH B Q C\<close> \<open>ColH P C Q\<close> \<open>Q \<noteq> C\<close> 
                  colH_permut_321 colH_trivial122)
            hence False 
              using assms(1) by blast
          }
          hence "\<not> IncidL P l" 
            by blast
          {
            assume "B = Q"
            hence ?t 
              using Bet_def by blast
          }
          moreover
          {
            assume "B \<noteq> Q"
            {
              assume "A = C"
              hence ?t 
                using \<open>BetH A P C\<close> between_diff by blast
            }
            moreover
            {
              assume "A \<noteq> C"
              {
                assume "IncidL B l"
                have "ColH A B Q" 
                  using ColH_def \<open>IncidL A l\<close> \<open>IncidL B l\<close> \<open>IncidL Q l\<close> \<open>IsL l\<close> by blast
                have "ColH A B C" 
                  using \<open>BetH B Q C\<close> \<open>ColH A B Q\<close> betH_colH colH_permut_231 colH_trans 
                    colH_trivial121 by blast
                have "ColH A P C" 
                  by (simp add: \<open>BetH A P C\<close> betH_colH)
                have "ColH B Q C" 
                  by (simp add: \<open>BetH B Q C\<close> between_col)
                have "ColH B C P" 
                  by (meson ColH_def \<open>A \<noteq> C\<close> \<open>ColH A B C\<close> \<open>ColH A P C\<close> inter_incid_uniquenessH)
                hence False 
                  using assms(1) by blast
              }
              hence "\<not> IncidL B l" 
                by blast
              {
                assume "IncidL C l"
                have "ColH A C Q" 
                  using ColH_def \<open>IncidL A l\<close> \<open>IncidL C l\<close> \<open>IncidL Q l\<close> \<open>IsL l\<close> by blast
                have "ColH B Q C" 
                  using assms(3) bet_colH by auto
                have "ColH A B C" 
                  by (metis \<open>BetH B Q C\<close> \<open>ColH A C Q\<close> \<open>Q \<noteq> C\<close> betH_colH colH_permut_231 
                      colH_trans colH_trivial121)
                have "ColH B C P" 
                  using inter_incid_uniquenessH ColH_def \<open>A \<noteq> C\<close> \<open>ColH A B C\<close> \<open>IncidL A l\<close> 
                    \<open>IncidL C l\<close> \<open>\<not> IncidL B l\<close> by fastforce
                hence False 
                  by (simp add: assms(1))
              }
              have "cut l B C" 
                using \<open>BetH B Q C\<close> \<open>IncidL C l \<Longrightarrow> False\<close> \<open>IncidL Q l\<close> \<open>IsL l\<close> \<open>\<not> IncidL B l\<close> 
                  local.cut_def by blast
              obtain p where "IncidP B p" and "IncidP C p" and "IncidP P p" 
                using assms(1) plan_existence by blast
              have "(\<not> ColH B C P \<and> IncidP B p \<and> IncidP C p \<and> IncidP P p \<and> IncidLP l p \<and>
                         \<not> IncidL P l \<and> cut l B C) \<longrightarrow> cut l B P \<or> cut l C P" 
                using pasch Is_plane \<open>IsL l\<close> by blast
              moreover
              have "\<not> ColH B C P" 
                by (simp add: assms(1))
              moreover have "IncidP B p" 
                by (simp add: \<open>IncidP B p\<close>)
              moreover have "IncidP C p" 
                by (simp add: \<open>IncidP C p\<close>)
              moreover have "IncidP P p" 
                by (simp add: \<open>IncidP P p\<close>)
              moreover have "IncidLP l p" 
                by (metis colH_permut_231 line_on_plane' 
                    Hilbert_neutral_dimensionless.ncolH_distincts 
                    Hilbert_neutral_dimensionless_axioms Is_plane \<open>IncidL A l\<close> \<open>IncidL Q l\<close> 
                    \<open>IsL l\<close> \<open>Q \<noteq> A\<close> assms(2) assms(3) bet_colH calculation(2) calculation(3) 
                    calculation(4) calculation(5) line_on_plane)
              moreover have "\<not> IncidL P l" 
                by (simp add: \<open>\<not> IncidL P l\<close>)
              moreover have "cut l B C" 
                by (simp add: \<open>local.cut l B C\<close>)
              moreover
              {
                assume "cut l B P"
                hence "\<not> IncidL B l" 
                  using \<open>\<not> IncidL B l\<close> by auto
                have "\<not> IncidL P l" 
                  by (simp add: calculation(7))
                obtain X where "IncidL X l" and "BetH B X P" 
                  using \<open>local.cut l B P\<close> local.cut_def by blast
                have "BetH P X B \<or> P = X \<or> X = B" 
                  using \<open>BetH B X P\<close> between_comm by presburger
                moreover have "BetH Q X A \<or> Q = X \<or> X = A"
                proof (cases "A = X")
                  case True
                  thus ?thesis 
                    by simp
                next
                  case False
                  have "A \<noteq> Q" 
                    using \<open>Q \<noteq> A\<close> by fastforce
                  have "P \<noteq> C" 
                    using assms(1) colH_trivial122 by blast
                  have "A \<noteq> B" 
                    using \<open>IncidL A l\<close> \<open>\<not> IncidL B l\<close> by auto
                  have "X \<noteq> Q" 
                    using \<open>B \<noteq> Q\<close> \<open>BetH B X P\<close> assms(1) assms(3) bet_colH between_col 
                      colH_trans colH_trivial121 by blast
                  have "ColH A X Q" 
                    using ColH_def Is_line \<open>IncidL A l\<close> \<open>IncidL Q l\<close> \<open>IncidL X l\<close> by blast
                  {
                    assume "ColH A C Q"
                    obtain l00 where "IncidL A l00" and "IncidL C l00" and "IncidL Q l00" 
                      using ColH_def \<open>ColH A C Q\<close> by blast
                    hence "IncidL C l" 
                      using \<open>A \<noteq> Q\<close> \<open>IncidL A l\<close> \<open>IncidL Q l\<close> inter_incid_uniquenessH by blast
                    hence False 
                      using \<open>IncidL C l \<Longrightarrow> False\<close> by auto
                  }
                  hence "\<not> ColH A C Q" 
                    by blast
                  have "P \<noteq> B" 
                    using assms(1) colH_trivial121 by fastforce
                  obtain m where "IsL m" and "IncidL P m" and "IncidL B m" 
                    using \<open>P \<noteq> B\<close> line_existence by blast
                  have "\<not> IncidL Q m" 
                    by (meson ColH_def \<open>B \<noteq> Q\<close> \<open>BetH B Q C\<close> \<open>IncidL B m\<close> \<open>IncidL P m\<close> assms(1)
                        between_col inter_incid_uniquenessH)
                  have "\<not> ColH A B P" 
                    by (metis \<open>BetH A P C\<close> \<open>P \<noteq> A\<close> assms(1) betH_colH colH_permut_312 
                        colH_trans colH_trivial122)
                  have "cut m A C" 
                    using Hilbert_neutral_dimensionless_pre.ColH_def \<open>BetH A P C\<close> 
                      \<open>IncidL B m\<close> \<open>IncidL P m\<close> \<open>IsL m\<close> \<open>\<not> ColH A B P\<close> assms(1) 
                      local.cut_def by fastforce
                  obtain p where "IncidP A p" and "IncidP C p" and "IncidP Q p" 
                    using \<open>\<not> ColH A C Q\<close> plan_existence by blast
                  have "(\<not> ColH A C Q \<and> IncidP A p \<and> IncidP C p \<and> IncidP Q p \<and>
                           IncidLP m p \<and> \<not> IncidL Q m \<and> cut m A C) \<longrightarrow> (cut m A Q \<or> cut m C Q)" 
                    using pasch Is_plane \<open>IsL m\<close> by blast
                  moreover have "\<not> ColH A C Q \<and> IncidP A p \<and> IncidP C p \<and> IncidP Q p \<and>
                           IncidLP m p \<and> \<not> IncidL Q m \<and> cut m A C" 
                    by (metis Is_plane \<open>A \<noteq> C\<close> \<open>BetH A P C\<close> \<open>BetH B Q C\<close> \<open>IncidL B m\<close> 
                        \<open>IncidL P m\<close> \<open>IncidP A p\<close> \<open>IncidP C p\<close> \<open>IncidP Q p\<close>
                        \<open>IsL m\<close> \<open>P \<noteq> B\<close> \<open>Q \<noteq> C\<close>
                        \<open>\<not> ColH A C Q\<close> \<open>\<not> IncidL Q m\<close> \<open>local.cut m A C\<close> between_col between_comm 
                        colH_permut_132 line_on_plane line_on_plane')
                  moreover {
                    assume "cut m A Q"
                    obtain Y where "IncidL Y m \<and> BetH A Y Q" 
                      using \<open>local.cut m A Q\<close> local.cut_def by blast
                    have "ColH A Y Q" 
                      by (simp add: \<open>IncidL Y m \<and> BetH A Y Q\<close> betH_colH)
                    then obtain l0 where "IncidL A l0" and "IncidL Y l0" and "IncidL Q l0" 
                      using ColH_def by blast
                    have "EqL l0 l" 
                      using Is_line \<open>A \<noteq> Q\<close> \<open>IncidL A l0\<close> \<open>IncidL A l\<close> \<open>IncidL Q l0\<close>
                        \<open>IncidL Q l\<close> line_uniqueness by presburger
                    hence "IncidL Y l" 
                      using \<open>A \<noteq> Q\<close> \<open>IncidL A l0\<close> \<open>IncidL A l\<close> \<open>IncidL Q l0\<close> \<open>IncidL Q l\<close>
                        \<open>IncidL Y l0\<close> inter_incid_uniquenessH by blast
                    moreover
                    have "ColH B X P" 
                      by (simp add: \<open>BetH B X P\<close> between_col)
                    then obtain m0 where "IncidL B m0" and "IncidL X m0" and "IncidL P m0" 
                      using ColH_def by blast
                    have "EqL m0 m" 
                      using Is_line \<open>IncidL B m0\<close> \<open>IncidL B m\<close> \<open>IncidL P m0\<close> \<open>IncidL P m\<close>
                        \<open>P \<noteq> B\<close> line_uniqueness by presburger
                    hence "IncidL X m" 
                      using IncidL_morphism Is_line \<open>IncidL X m0\<close> \<open>IsL m\<close> by blast
                    ultimately
                    have "X = Y"
                      using \<open>IncidL B m\<close> \<open>IncidL X l\<close> \<open>IncidL Y m \<and> BetH A Y Q\<close>
                        \<open>\<not> IncidL B l\<close> inter_incid_uniquenessH by auto
                    hence ?thesis 
                      using \<open>IncidL Y m \<and> BetH A Y Q\<close> between_comm by blast
                  }
                  moreover {
                    assume "cut m C Q"
                    then obtain I where "IncidL I m" and "BetH C I Q" 
                      using local.cut_def by blast
                    have "ColH C I Q" 
                      using \<open>BetH C I Q\<close> betH_colH by blast
                    obtain lo where "IncidL C lo" and "IncidL I lo" and "IncidL Q lo" 
                      using ColH_def \<open>ColH C I Q\<close> by auto
                    {
                      assume "IncidL C m"
                      hence "ColH B C P" 
                        using \<open>local.cut m A C\<close> local.cut_def by blast
                      hence False 
                        by (simp add: assms(1))
                    }
                    have "IncidL B lo" 
                      using ColH_def \<open>BetH B Q C\<close> \<open>IncidL C lo\<close> \<open>IncidL Q lo\<close> betH_colH
                        inter_incid_uniquenessH by blast
                    have "I = B" 
                      using \<open>IncidL B lo\<close> \<open>IncidL B m\<close> \<open>IncidL I lo\<close> \<open>IncidL I m\<close> 
                        \<open>IncidL Q lo\<close> \<open>\<not> IncidL Q m\<close> inter_incid_uniquenessH by blast
                    hence ?thesis 
                      using \<open>BetH B Q C\<close> \<open>BetH C I Q\<close> between_only_one by blast
                  }
                  ultimately show ?thesis 
                    by blast
                qed
                ultimately have ?t 
                  using Bet_def by auto
              }
              moreover
              {
                assume "cut l C P"
                then obtain I where "IncidL I l" and "BetH C I P" 
                  using local.cut_def by blast
                have "A = I" 
                proof -
                  obtain s where "IncidL A s" and "IncidL C s"
                    using \<open>A \<noteq> C\<close> line_existence by blast
                  {
                    assume "IncidL Q s" 
                    have "A \<noteq> Q" 
                      using \<open>Q \<noteq> A\<close> by blast
                    have "EqL l s" 
                      using Is_line \<open>A \<noteq> Q\<close> \<open>IncidL A l\<close> \<open>IncidL A s\<close> \<open>IncidL Q l\<close>
                        \<open>IncidL Q s\<close> line_uniqueness by presburger
                    hence False 
                      using \<open>A \<noteq> Q\<close> \<open>IncidL A l\<close> \<open>IncidL A s\<close> \<open>IncidL C l \<Longrightarrow> False\<close>
                        \<open>IncidL C s\<close> \<open>IncidL Q l\<close> \<open>IncidL Q s\<close> inter_incid_uniquenessH by blast
                  }
                  moreover 
                  have "ColH C I P" 
                    by (simp add: \<open>BetH C I P\<close> betH_colH)
                  have "ColH A P C" 
                    by (simp add: \<open>BetH A P C\<close> betH_colH)
                  then obtain s0 where "IncidL A s0" and "IncidL P s0" and "IncidL C s0" 
                    using ColH_def by blast
                  have "EqL s s0" 
                    using Is_line \<open>A \<noteq> C\<close> \<open>IncidL A s0\<close> \<open>IncidL A s\<close> \<open>IncidL C s0\<close> 
                      \<open>IncidL C s\<close> line_uniqueness by presburger
                  obtain s1 where "IsL s1" and "IncidL C s1" and "IncidL I s1" and "IncidL P s1" 
                    using ColH_def \<open>ColH C I P\<close> by blast
                  have "EqL s s1" 
                    by (metis EqL_trans Is_line \<open>BetH C I P\<close> \<open>EqL s s0\<close> \<open>IncidL C s0\<close>
                        \<open>IncidL C s1\<close> \<open>IncidL P s0\<close> \<open>IncidL P s1\<close> between_diff line_uniqueness)
                  hence "IncidL I s" 
                    by (meson EqL_sym IncidL_morphism Is_line \<open>IncidL C s\<close> \<open>IncidL I s1\<close>)
                  ultimately show ?thesis 
                    using \<open>IncidL A l\<close> \<open>IncidL A s\<close> \<open>IncidL I l\<close> \<open>IncidL Q l\<close> 
                      inter_incid_uniquenessH by blast
                qed
                hence ?t 
                  using \<open>BetH A P C\<close> \<open>BetH C I P\<close> between_only_one by blast
              }
              ultimately have ?t 
                by blast
            }
            ultimately have ?t 
              by blast
          }
          ultimately have ?t 
            by blast
        }
        ultimately have ?t 
          by blast
      }
      ultimately have ?t 
        by blast
    }
    moreover
    {
      assume "Q = A" and
        "BetH A P C" and 
        "BetH B Q C"
      have ?t 
        by (metis Bet_def \<open>BetH B Q C\<close> \<open>Q = A\<close> assms(1) assms(2) between_col 
            colH_trans ncolH_distincts)
    }
    ultimately show ?thesis 
      by blast
  qed
  moreover have "BetH A P C \<and> B = Q \<longrightarrow> ?t" 
    using Bet_def by blast
  moreover have "BetH A P C \<and> Q = C \<longrightarrow> ?t" 
    by (meson Bet_def between_comm)
  moreover have "A = P \<and> BetH B Q C \<longrightarrow> ?t" 
    using Bet_def by auto
  moreover have "A = P \<and> B = Q \<longrightarrow> ?t" 
    using Bet_def by auto
  moreover have "A = P \<and> Q = C \<longrightarrow> ?t" 
    using Bet_def by blast
  moreover have "P = C \<and> BetH B Q C \<longrightarrow> ?t" 
    using assms(1) colH_trivial122 by blast
  moreover have "P = C \<and> B = Q \<longrightarrow> ?t" 
    using assms(1) colH_trivial122 by blast
  moreover have "P = C \<and> Q = C \<longrightarrow> ?t" 
    using assms(1) colH_trivial122 by blast
  ultimately show ?thesis
    by blast
qed

lemma betH_trans1:
  assumes "BetH A B C" and
    "BetH B C D"
  shows "BetH A C D" 
proof -
  have "A \<noteq> B" 
    using assms(1) betH_distincts by blast
  have "C \<noteq> B" 
    using assms(1) betH_distincts by blast
  have "A \<noteq> C" 
    using assms(1) betH_expand by blast
  have "D \<noteq> C" 
    using assms(2) betH_distincts by blast
  have "D \<noteq> B" 
    using assms(2) between_diff by blast
  obtain E where "\<not> ColH A C E" 
    using \<open>A \<noteq> C\<close> ncolH_exists by presburger
  hence "C \<noteq> E" 
    by (simp add: ncolH_distincts)
  obtain F where "BetH C E F" 
    using \<open>C \<noteq> E\<close> between_out by fastforce
  have "E \<noteq> F" 
    using \<open>BetH C E F\<close> betH_distincts by blast
  have "C \<noteq> F" 
    using \<open>BetH C E F\<close> between_diff by blast
  have "ColH A B C" 
    using assms(1) betH_colH by auto
  have "ColH B C D" 
    by (simp add: assms(2) betH_colH)
  have "ColH C E F" 
    using \<open>BetH C E F\<close> between_col by auto
  have "\<not> ColH F C B" 
    using ColH_def \<open>C \<noteq> B\<close> \<open>C \<noteq> F\<close> \<open>ColH A B C\<close> \<open>ColH C E F\<close> \<open>\<not> ColH A C E\<close> 
      inter_incid_uniquenessH by auto
  have "\<exists> X. Bet B X F \<and> Bet E X A" 
  proof -
    have "Bet A B C" 
      by (simp add: Bet_def assms(1))
    moreover have "Bet F E C" 
      by (simp add: Bet_def \<open>BetH C E F\<close> between_comm)
    ultimately show ?thesis 
      using \<open>\<not> ColH F C B\<close> inner_pasch_aux by auto
  qed
  then obtain G where "Bet B G F" and "Bet E G A"
    by blast
  {
    assume "BetH B G F"
    hence "ColH B G F" 
      by (simp add: \<open>Bet B G F\<close> bet_colH)
    {
      assume "BetH E G A"
      hence "ColH E G A" 
        by (simp add: betH_colH)
      {
        assume "ColH D B G"
        hence "ColH B D F" 
          by (metis betH_colH \<open>BetH B G F\<close> colH_permut_231 colH_trans colH_trivial121)
        hence False 
          by (metis \<open>ColH B C D\<close> \<open>D \<noteq> B\<close> \<open>\<not> ColH F C B\<close> colH_permut_132 
              colH_trans colH_trivial121)
      }
      obtain m where "IncidL C m" and "IncidL E m" 
        using \<open>C \<noteq> E\<close> line_existence by blast
      {
        assume "cut m A G \<or> cut m B G" 
        moreover
        {
          assume "cut m A G"
          then obtain E' where "IncidL E' m" and "BetH A E' G" 
            using local.cut_def by blast
          have "E = E'" 
          proof -
            have "C \<noteq> F"            
              by (simp add: \<open>C \<noteq> F\<close>)
            moreover have "ColH A G E"                 
              by (simp add: \<open>ColH E G A\<close> colH_permut_321)
            moreover have "ColH A G E'"                 
              using \<open>BetH A E' G\<close> between_col colH_permut_132 by blast
            moreover have "ColH C F E"                 
              by (simp add: \<open>ColH C E F\<close> colH_permut_132)
            moreover have "\<not> ColH A G C"                 
              by (metis betH_colH \<open>BetH A E' G\<close> \<open>\<not> ColH A C E\<close> calculation(2) 
                  colH_trans colH_trivial121)
            moreover have "ColH C F E'"                 
              by (meson ColH_def \<open>C \<noteq> E\<close> \<open>IncidL C m\<close> \<open>IncidL E m\<close> \<open>IncidL E' m\<close> 
                  calculation(4) inter_incid_uniquenessH)
            ultimately show ?thesis
              using inter_uniquenessH by blast
          qed
          have "\<not> Bet E G A" 
            using \<open>BetH A E' G\<close> \<open>BetH E G A\<close> \<open>E = E'\<close> between_only_one by blast
          hence False 
            using \<open>Bet E G A\<close> \<open>\<not> Bet E G A\<close> by blast
        }
        moreover
        {
          assume "cut m B G"
          obtain F' where "IncidL F' m" and "BetH B F' G" 
            using \<open>local.cut m B G\<close> local.cut_def by blast
          have "ColH C E F'" 
            using ColH_def Is_line \<open>IncidL C m\<close> \<open>IncidL E m\<close> \<open>IncidL F' m\<close> by blast
          have "B \<noteq> G" 
            using \<open>BetH B F' G\<close> between_diff by auto
          have "\<not> ColH C E B" 
            using \<open>C \<noteq> E\<close> \<open>ColH C E F\<close> \<open>\<not> ColH F C B\<close> colH_trans colH_trivial121 by blast
          hence "F = F'"
            using inter_uniquenessH \<open>ColH C E F\<close> \<open>B \<noteq> G\<close> \<open>BetH B F' G\<close> \<open>ColH B G F\<close> 
              \<open>ColH C E F'\<close> between_col colH_permut_132 by blast
          hence "\<not> BetH F G B" 
            using \<open>BetH B F' G\<close> between_only_one by blast
          hence False 
            using \<open>BetH B G F\<close> between_comm by blast
        }
        ultimately have False 
          by blast
      }
      hence "\<not> (cut m A G \<or> cut m B G)" 
        by blast
      have "\<not> ColH B D G" 
        using \<open>ColH D B G \<Longrightarrow> False\<close> colH_permut_213 by blast
      {
        assume "IncidL G m"
        hence "ColH C E G" 
          using ColH_def Is_line \<open>IncidL C m\<close> \<open>IncidL E m\<close> by blast
        hence "ColH A C E" 
          by (metis betH_colH \<open>BetH E G A\<close> colH_permut_231 colH_trans colH_trivial121)
        hence False 
          by (simp add: \<open>\<not> ColH A C E\<close>)
      }
      hence "\<not> IncidL G m" 
        by blast
      {
        assume "IncidL D m"
        have "ColH A C D" 
          by (meson ColH_def \<open>C \<noteq> B\<close> \<open>ColH A B C\<close> \<open>ColH B C D\<close> inter_incid_uniquenessH)
        hence "ColH A C E" 
          by (meson ColH_def \<open>D \<noteq> C\<close> \<open>IncidL C m\<close> \<open>IncidL D m\<close> \<open>IncidL E m\<close> 
              inter_incid_uniquenessH)
        hence False 
          by (simp add: \<open>\<not> ColH A C E\<close>)
      }
      hence "\<not> IncidL D m" 
        by blast
      {
        assume "IncidL B m"
        hence "ColH A C E" 
          using ColH_def \<open>C \<noteq> B\<close> \<open>ColH B C D\<close> \<open>IncidL C m\<close> \<open>\<not> IncidL D m\<close> 
            inter_incid_uniquenessH by blast
        hence False 
          by (simp add: \<open>\<not> ColH A C E\<close>)
      }
      hence "\<not> IncidL B m" 
        by blast
      hence "cut m D B" 
        using Is_line \<open>IncidL C m\<close> \<open>\<not> IncidL D m\<close> assms(2) between_comm 
          local.cut_def by blast
      obtain p where "IncidP B p" and "IncidP D p" and "IncidP G p" 
        using \<open>\<not> ColH B D G\<close> plan_existence by blast
      have "(\<not> ColH B D G \<and> IncidP B p \<and> IncidP D p \<and> IncidP G p \<and> 
                IncidLP m p \<and> \<not> IncidL G m \<and> cut m B D) \<longrightarrow> (cut m B G \<or> cut m D G)" 
        using IncidLP_def pasch by blast
      moreover have "\<not> ColH B D G \<and> IncidP B p \<and> IncidP D p \<and> IncidP G p \<and> 
                        IncidLP m p \<and> \<not> IncidL G m \<and> cut m B D" 
        by (metis betH_colH Is_line Is_plane \<open>BetH B G F\<close> \<open>C \<noteq> E\<close> \<open>C \<noteq> F\<close> \<open>ColH B C D\<close>
            \<open>ColH C E F\<close> \<open>D \<noteq> B\<close> \<open>IncidL C m\<close> \<open>IncidL E m\<close> \<open>IncidP B p\<close> \<open>IncidP D p\<close> 
            \<open>IncidP G p\<close> \<open>\<not> ColH B D G\<close> \<open>\<not> IncidL G m\<close> \<open>local.cut m D B\<close> colH_permut_312 
            cut_comm line_on_plane line_on_plane')
      ultimately have "cut m B G \<or> cut m D G" 
        by blast
      moreover
      {
        assume "cut m B G"
        hence ?thesis 
          using \<open>\<not> (local.cut m A G \<or> local.cut m B G)\<close> by blast
      }
      moreover
      {
        assume "cut m D G"
        obtain HX where "IncidL HX m" and "BetH D HX G" 
          using \<open>local.cut m D G\<close> local.cut_def by auto
        {
          assume "ColH G D A"
          have "ColH A D B" 
            by (metis \<open>C \<noteq> B\<close> \<open>ColH A B C\<close> \<open>ColH B C D\<close> colH_permut_231 colH_trans 
                colH_trivial121)
          hence False 
            by (metis \<open>ColH G D A\<close> \<open>\<not> ColH B D G\<close> assms(1) assms(2) between_comm 
                between_only_one' colH_permut_321 colH_trans colH_trivial122)
        }
        hence "\<not> ColH G D A" 
          by blast
        {
          assume "IncidL A m"
          hence "ColH A C E" 
            using ColH_def \<open>A \<noteq> C\<close> \<open>ColH A B C\<close> \<open>IncidL C m\<close> \<open>\<not> IncidL B m\<close> 
              inter_incid_uniquenessH by blast
          hence False 
            by (simp add: \<open>\<not> ColH A C E\<close>)
        }
        hence "\<not> IncidL A m" 
          by blast
        have "cut m G D" 
          by (simp add: \<open>local.cut m D G\<close> cut_comm)
        obtain p where "IncidP G p" and "IncidP D p" and "IncidP A p" 
          using \<open>\<not> ColH G D A\<close> plan_existence by blast
        have "(\<not> ColH G D A \<and> IncidP G p \<and> IncidP D p \<and> IncidP A p \<and> 
                IncidLP m p \<and> \<not> IncidL A m \<and> cut m G D)\<longrightarrow> (cut m G A \<or> cut m D A)" 
          using pasch Is_line Is_plane \<open>IncidL HX m\<close> by blast
        moreover
        have "\<not> ColH G D A \<and> IncidP G p \<and> IncidP D p \<and> IncidP A p \<and> 
                IncidLP m p \<and> \<not> IncidL A m \<and> cut m G D" 
        proof -
          have "\<not> ColH G D A \<and> IncidP G p \<and> IncidP D p \<and> IncidP A p" 
            using \<open>IncidP A p\<close> \<open>IncidP D p\<close> \<open>IncidP G p\<close> \<open>\<not> ColH G D A\<close> by blast
          moreover 
          have "ColH B D C" 
            by (simp add: \<open>ColH B C D\<close> colH_permut_132)
          have "ColH B A D" 
            by (metis \<open>C \<noteq> B\<close> \<open>ColH A B C\<close> \<open>ColH B C D\<close> colH_permut_231 
                colH_trans colH_trivial121)
          hence "IncidP B p" 
            by (metis calculation colH_permut_231 colH_trivial122 line_on_plane')
          hence "IncidP C p" 
            using \<open>A \<noteq> B\<close> \<open>ColH A B C\<close> \<open>IncidP A p\<close> line_on_plane' by blast
          hence "IncidLP m p" 
            by (metis betH_colH Is_line Is_plane \<open>BetH E G A\<close> \<open>C \<noteq> E\<close> \<open>IncidL C m\<close> 
                \<open>IncidL E m\<close> \<open>IncidP A p\<close> \<open>IncidP G p\<close> colH_permut_321 
                line_on_plane line_on_plane')
          moreover have "\<not> IncidL A m" 
            by (simp add: \<open>\<not> IncidL A m\<close>)
          moreover have "cut m G D" 
            by (simp add: \<open>local.cut m G D\<close>)
          ultimately show ?thesis 
            by blast
        qed
        ultimately have "cut m G A \<or> cut m D A" 
          by blast
        moreover
        {
          assume "cut m G A"
          hence ?thesis 
            using \<open>\<not> (local.cut m A G \<or> local.cut m B G)\<close> cut_comm by blast
        }
        moreover
        {
          assume "cut m D A"
          then obtain I where "IncidL I m" and "BetH D I A" 
            using local.cut_def by blast
          have "ColH D I A" 
            using \<open>BetH D I A\<close> between_col by fastforce
          obtain l1 where "IsL l1" and "IncidL A l1" and "IncidL B l1" and "IncidL C l1" 
            using ColH_def \<open>ColH A B C\<close> by blast
          obtain l2 where "IsL l2" and "IncidL B l2" and "IncidL C l2" and "IncidL D l2" 
            using ColH_def \<open>ColH B C D\<close> by blast
          obtain l3 where "IsL l3" and "IncidL D l3" and "IncidL I l3" and "IncidL A l3" 
            using ColH_def \<open>ColH D I A\<close> by blast
          have "A \<noteq> D" 
            using \<open>\<not> ColH G D A\<close> colH_trivial122 by blast
          hence "BetH D C A" 
            by (metis \<open>BetH D I A\<close> \<open>C \<noteq> B\<close> \<open>IncidL A l1\<close> \<open>IncidL A l3\<close> 
                \<open>IncidL B l1\<close> \<open>IncidL B l2\<close> \<open>IncidL C l1\<close> \<open>IncidL C l2\<close> \<open>IncidL C m\<close> 
                \<open>IncidL D l2\<close> \<open>IncidL D l3\<close> \<open>IncidL I l3\<close> \<open>IncidL I m\<close> \<open>\<not> IncidL A m\<close> 
                inter_incid_uniquenessH)
          hence "BetH A C D" 
            using between_comm by blast
        }
        ultimately have ?thesis
          by blast
      }
      ultimately have ?thesis 
        by blast
    }
    moreover
    {
      assume "E = G"
      hence ?thesis 
        using ColH_def \<open>BetH B G F\<close> \<open>ColH C E F\<close> \<open>E \<noteq> F\<close> \<open>\<not> ColH F C B\<close> 
          between_col inter_incid_uniquenessH by fastforce
    }
    moreover
    {
      assume "G = A"
      hence ?thesis 
        by (metis \<open>A \<noteq> B\<close> \<open>BetH B G F\<close> \<open>ColH A B C\<close> \<open>\<not> ColH F C B\<close> 
            between_col inter_uniquenessH ncolH_distincts)
    }
    ultimately have ?thesis
      using Bet_def \<open>Bet E G A\<close> by blast
  }
  moreover
  {
    assume "B = G"
    hence ?thesis 
      using ColH_def \<open>A \<noteq> B\<close> \<open>Bet E G A\<close> \<open>ColH A B C\<close> \<open>\<not> ColH A C E\<close> 
        bet_colH inter_incid_uniquenessH by fastforce
  }
  moreover
  {
    assume "G = F"
    hence False
      by (metis \<open>Bet E G A\<close> \<open>ColH C E F\<close> \<open>E \<noteq> F\<close> \<open>G = F\<close> \<open>\<not> ColH A C E\<close> 
          bet_colH colH_permut_321 colH_trans colH_trivial122) 
    hence ?thesis
      by blast
  }
  ultimately show ?thesis 
    using Bet_def \<open>Bet B G F\<close> by blast
qed

lemma betH_trans2:
  assumes "BetH A B C" and 
    "BetH B C D"
  shows "BetH A B D" 
  using assms(1) assms(2) betH_trans1 between_comm by blast

lemma betH_trans: 
  assumes "BetH A B C" and
    "BetH B C D" 
  shows "BetH A B D \<and> BetH A C D" 
  using assms(1) assms(2) betH_trans1 betH_trans2 by blast

lemma not_cut3:
  assumes "IncidP A p" and
    "IncidP B p" and
    "IncidP C p" and
    "IncidLP l p" and
    "\<not> IncidL A l" and
    "\<not> ColH A B C" and
    "\<not> cut l A B" and
    "\<not> cut l A C" 
  shows "\<not> cut l B C" 
  by (meson colH_permut_312 cut_comm IncidLP_def assms(1) assms(2) assms(3) 
      assms(4) assms(5) assms(6) assms(7) assms(8) pasch)

lemma betH_trans0:
  assumes "BetH A B C" and
    "BetH A C D" 
  shows "BetH B C D \<and> BetH A B D" 
proof -
  have "A \<noteq> B" 
    using assms(1) betH_distincts by auto
  have "A \<noteq> C" 
    using assms(1) between_diff by auto
  have "A \<noteq> D" 
    using assms(2) between_diff by presburger
  obtain G where "\<not> ColH A B G" 
    using \<open>A \<noteq> B\<close> ncolH_exists by presburger
  have "B \<noteq> G" 
    using \<open>\<not> ColH A B G\<close> colH_trivial122 by blast
  obtain F where "BetH B G F" 
    using \<open>B \<noteq> G\<close> between_out by blast
  have "B \<noteq> F" 
    using \<open>BetH B G F\<close> between_diff by auto
  {
    assume "C = F"
    have "ColH B F A" 
      using \<open>C = F\<close> assms(1) between_col colH_permut_231 by presburger
    moreover have "ColH B F B" 
      by (simp add: colH_trivial121)
    moreover have "ColH B F G" 
      using \<open>BetH B G F\<close> betH_expand colH_permut_132 by blast
    ultimately have "ColH A B G" 
      using colH_trans \<open>B \<noteq> F\<close> by blast
    hence ?thesis 
      by (simp add: \<open>\<not> ColH A B G\<close>)
  }
  moreover
  {
    assume "C \<noteq> F"
    obtain l where "IncidL C l" and "IncidL F l" 
      using \<open>C \<noteq> F\<close> line_existence by blast
    {
      assume "cut l A B"
      then obtain X where "IncidL X l" and "BetH A X B" 
        using local.cut_def by blast
      hence "X = C"
      proof -
        have "\<not> ColH A B F" 
          by (meson ColH_def \<open>B \<noteq> F\<close> \<open>BetH B G F\<close> \<open>\<not> ColH A B G\<close> 
              between_col inter_incid_uniquenessH)
        moreover have "ColH A B X" 
          by (simp add: \<open>BetH A X B\<close> between_col colH_permut_132)
        moreover have "ColH A B C" 
          using assms(1) betH_colH by presburger
        moreover have "ColH F C X" 
          using ColH_def Is_line \<open>IncidL C l\<close> \<open>IncidL F l\<close> \<open>IncidL X l\<close> by blast
        moreover have "ColH F C C" 
          by (simp add: colH_trivial122)
        ultimately show ?thesis
          by (metis inter_uniquenessH)
      qed
      have False 
        using \<open>BetH A X B\<close> \<open>X = C\<close> assms(1) between_comm between_only_one by blast
    }
    hence "\<not> cut l A B" 
      by blast
    {
      assume "cut l B G"
      obtain X where "IncidL X l" and "BetH B X G" 
        using \<open>local.cut l B G\<close> local.cut_def by blast
      hence "ColH B X F" 
        by (meson \<open>BetH B G F\<close> \<open>B \<noteq> G\<close> between_col colH_permut_132 
            colH_trans colH_trivial121)
      hence False 
        using ColH_def \<open>BetH B G F\<close> \<open>BetH B X G\<close> \<open>IncidL F l\<close> \<open>IncidL X l\<close> 
          \<open>local.cut l B G\<close> between_comm between_only_one inter_incid_uniquenessH 
          local.cut_def by blast
    }
    hence "\<not> cut l B G" 
      by blast
    obtain p where "IncidP A p" and "IncidP B p" and "IncidP G p" 
      using \<open>\<not> ColH A B G\<close> plan_existence by blast
    have "\<not> cut l A G"
    proof -
      have "IncidLP l p" 
        by (metis Hilbert_neutral_dimensionless.line_on_plane' 
            Hilbert_neutral_dimensionless_axioms Is_line Is_plane \<open>BetH B G F\<close> \<open>C \<noteq> F\<close>
            \<open>IncidL C l\<close> \<open>IncidL F l\<close> \<open>IncidP A p\<close> \<open>IncidP B p\<close> \<open>IncidP G p\<close> 
            assms(1) betH_expand line_on_plane)
      moreover
      {
        assume "IncidL B l"
        have "ColH B C G" 
          by (meson ColH_def \<open>B \<noteq> F\<close> \<open>BetH B G F\<close> \<open>IncidL B l\<close> \<open>IncidL C l\<close> 
              \<open>IncidL F l\<close> between_col inter_incid_uniquenessH)
        have "ColH B F C" 
          using ColH_def Is_line \<open>IncidL B l\<close> \<open>IncidL C l\<close> \<open>IncidL F l\<close> by blast
        hence False 
          using betH_expand colH_permut_231 colH_trans colH_trivial121 
            \<open>ColH B C G\<close> \<open>\<not> ColH A B G\<close> assms(1) by fast
      }
      hence "\<not> IncidL B l" 
        by blast
      moreover have "\<not> ColH B A G" 
        using \<open>\<not> ColH A B G\<close> colH_permut_213 by blast
      moreover have "\<not> cut l B A" 
        using \<open>\<not> local.cut l A B\<close> cut_comm by blast
      ultimately show ?thesis 
        using \<open>IncidP A p\<close> \<open>IncidP B p\<close> \<open>IncidP G p\<close> \<open>\<not> local.cut l B G\<close> not_cut3 by blast
    qed 
    have "cut l A G \<or> cut l D G"
    proof -
      {
        assume "ColH A D G"
        have "ColH A C A" 
          by (simp add: colH_trivial121)
        moreover have "ColH A C D" 
          by (simp add: assms(2) between_col)
        moreover have "ColH A C B" 
          using assms(1) between_col colH_permut_132 by blast
        ultimately have "ColH A D B" 
          using \<open>A \<noteq> C\<close> colH_trans by blast
        hence False 
          using \<open>A \<noteq> D\<close> \<open>ColH A D G\<close> \<open>\<not> ColH A B G\<close> colH_trans colH_trivial121 by blast
      }
      hence "\<not> ColH A D G" 
        by blast
      then obtain p where "IncidP A p" and "IncidP D p" and "IncidP G p" 
        using plan_existence by blast
      show ?thesis
      proof -
        have "\<not> ColH A D G" 
          by (simp add: \<open>\<not> ColH A D G\<close>)
        moreover have "IsP p" 
          using Is_plane \<open>IncidP D p\<close> by fastforce
        moreover have "IsL l" 
          using Is_line \<open>IncidL C l\<close> by auto
        moreover have "IncidP A p" 
          by (simp add: \<open>IncidP A p\<close>)
        moreover have "IncidP D p" 
          by (simp add: \<open>IncidP D p\<close>)
        moreover have "IncidP G p" 
          using \<open>IncidP G p\<close> by auto
        moreover 
        have "IncidP C p" 
          by (metis \<open>A \<noteq> D\<close> assms(2) between_col calculation(4) calculation(5) 
              colH_permut_312 line_on_plane')
        have "IncidP F p" 
          by (meson \<open>A \<noteq> C\<close> \<open>B \<noteq> G\<close> \<open>BetH B G F\<close> \<open>IncidP C p\<close> assms(1) 
              between_col calculation(4) calculation(6) colH_permut_132 line_on_plane')
        hence "IncidLP l p" 
          using \<open>C \<noteq> F\<close> \<open>IncidL C l\<close> \<open>IncidL F l\<close> \<open>IncidP C p\<close> calculation(2) 
            calculation(3) line_on_plane by blast
        moreover 
        {
          assume "IncidL G l" 
          have "ColH G F C" 
            using ColH_def Is_line \<open>IncidL C l\<close> \<open>IncidL F l\<close> \<open>IncidL G l\<close> by blast
          hence "ColH B C G" 
            using \<open>BetH B G F\<close> betH_colH colH_permut_231 colH_trans colH_trivial121 by blast
          hence False 
            by (metis betH_expand colH_permut_231 colH_trans colH_trivial121
                \<open>\<not> ColH A B G\<close> assms(1))
        }
        hence "\<not> IncidL G l" 
          by blast
        moreover have "cut l A D"
        proof -
          {
            assume "IncidL A l"
            hence "ColH A C F" 
              using ColH_def Is_line \<open>IncidL C l\<close> \<open>IncidL F l\<close> by blast
            have "ColH A B F" 
              using \<open>ColH A C F\<close> assms(1) betH_colH colH_permut_132 colH_trans 
                colH_trivial121 by blast
            hence False 
              by (metis \<open>B \<noteq> F\<close> \<open>BetH B G F\<close> \<open>\<not> ColH A B G\<close> between_col 
                  colH_permut_231 colH_trans colH_trivial121)
          }
          hence "\<not> IncidL A l" 
            by blast
          moreover
          {
            assume "IncidL D l" 
            hence "ColH C D F" 
              using ColH_def \<open>IncidL C l\<close> \<open>IncidL F l\<close> \<open>IsL l\<close> by auto
            hence "ColH A C F" 
              using assms(2) betH_colH colH_permut_231 colH_trans colH_trivial121 by blast
            hence "ColH A B F" 
              by (metis assms(1) betH_colH colH_permut_312 colH_trans colH_trivial121)
            hence False 
              by (metis \<open>B \<noteq> F\<close> \<open>BetH B G F\<close> \<open>\<not> ColH A B G\<close> between_col 
                  colH_permut_231 colH_trans colH_trivial121)
          }
          hence "\<not> IncidL D l" 
            by blast
          moreover have "IncidL C l" 
            by (simp add: \<open>IncidL C l\<close>)
          moreover have "BetH A C D" 
            by (simp add: assms(2))
          ultimately show ?thesis 
            using \<open>IsL l\<close> local.cut_def by blast
        qed
        ultimately show ?thesis 
          using pasch by blast
      qed
    qed
    moreover
    {
      assume "cut l D G"
      {
        assume "ColH D G B"
        have "ColH A B D" 
          by (meson \<open>A \<noteq> C\<close> assms(1) assms(2) between_col colH_permut_132 
              colH_trans colH_trivial121)
        have "B \<noteq> D" 
          using \<open>\<not> local.cut l A G\<close> \<open>\<not> local.cut l B G\<close> calculation by auto
        hence "ColH A B G" 
          by (meson ColH_def \<open>ColH A B D\<close> \<open>ColH D G B\<close> inter_incid_uniquenessH)
        hence False 
          using \<open>\<not> ColH A B G\<close> by blast
      }
      hence "\<not> ColH D G B"
        by blast
      {
        assume "IncidL B l" 
        hence "ColH B F C" 
          using ColH_def Is_line \<open>IncidL C l\<close> \<open>IncidL F l\<close> by blast
        have "B \<noteq> C" 
          using assms(1) betH_distincts by presburger
        hence "ColH A B G" 
          by (metis \<open>B \<noteq> F\<close> \<open>BetH B G F\<close> \<open>ColH B F C\<close> assms(1) between_col 
              colH_permut_231 colH_trans colH_trivial121)
        hence False
          by (simp add: \<open>\<not> ColH A B G\<close>)
      }
      hence "\<not> IncidL B l" 
        by blast
      obtain p where "IncidP D p" and "IncidP G p" and "IncidP B p" 
        using \<open>\<not> ColH D G B\<close> plan_existence by blast
      have "(\<not> ColH D G B \<and> IncidP D p \<and> IncidP G p \<and> IncidP B p \<and> 
    IncidLP l p \<and> \<not> IncidL B l \<and> cut l D G) \<longrightarrow> (cut l D B \<or> cut l G B)" 
        using Is_line Is_plane \<open>IncidL C l\<close> pasch by blast
      moreover
      have "(\<not> ColH D G B \<and> IncidP D p \<and> IncidP G p \<and> IncidP B p \<and> 
    IncidLP l p \<and> \<not> IncidL B l \<and> cut l D G)" 
      proof -
        have "\<not> ColH D G B \<and> IncidP D p \<and> IncidP G p \<and> IncidP B p" 
          by (simp add: \<open>IncidP B p\<close> \<open>IncidP D p\<close> \<open>IncidP G p\<close> \<open>\<not> ColH D G B\<close>)
        moreover have "IncidLP l p"
        proof -
          have "ColH B D C" 
            by (meson \<open>A \<noteq> C\<close> assms(1) assms(2) between_col colH_permut_132 
                colH_trans colH_trivial122)
          hence "IncidP C p" 
            by (metis calculation colH_trivial121 line_on_plane')
          moreover have "IncidP F p"     
            using \<open>BetH B G F\<close> \<open>IncidP B p\<close> \<open>IncidP G p\<close> betH_colH line_on_plane' by blast
          ultimately show ?thesis
            using Is_line Is_plane \<open>C \<noteq> F\<close> \<open>IncidL C l\<close> \<open>IncidL F l\<close> line_on_plane by blast
        qed
        moreover have "\<not> IncidL B l"  
          by (simp add: \<open>\<not> IncidL B l\<close>)
        moreover have "cut l D G"  
          by (simp add: \<open>local.cut l D G\<close>)
        ultimately show ?thesis 
          by blast
      qed
      ultimately have "cut l D B \<or> cut l G B" 
        using \<open>\<not> ColH D G B \<and> IncidP D p \<and> IncidP G p \<and> IncidP B p \<and> 
      IncidLP l p \<and> \<not> IncidL B l \<and> local.cut l D G \<longrightarrow> local.cut l D B \<or> local.cut l G B\<close> 
        by blast
      moreover
      {
        assume "cut l D B"
        then obtain C' where "IncidL C' l" and "BetH D C' B" 
          using local.cut_def by blast
        have "ColH C C' F" 
          using ColH_def Is_line \<open>IncidL C l\<close> \<open>IncidL C' l\<close> \<open>IncidL F l\<close> by blast
        have "\<not> ColH A B F" 
          by (metis \<open>BetH B G F\<close> \<open>\<not> ColH A B G\<close> betH_colH colH_permut_312 
              colH_trans colH_trivial122)
        have "ColH B D A" 
          by (metis (full_types) \<open>A \<noteq> C\<close> assms(1) assms(2) between_col colH_trans 
              ncolH_distincts)
        hence "ColH A B C'" 
          using ColH_def \<open>BetH D C' B\<close> betH_colH inter_incid_uniquenessH by fastforce
        then have "C = C'" using inter_uniquenessH 
          by (metis (full_types) \<open>ColH C C' F\<close> \<open>\<not> ColH A B F\<close> assms(1) 
              betH_colH ncolH_distincts)
        hence "BetH B C D \<and> BetH A B D"  
          using \<open>BetH D C' B\<close> assms(1) betH_trans between_comm by blast
      }
      moreover
      {
        assume "cut l G B"
        hence "BetH B C D \<and> BetH A B D"  
          using \<open>\<not> local.cut l B G\<close> cut_comm by blast
      }
      ultimately have "BetH B C D \<and> BetH A B D"  
        by blast
    }
    ultimately have "BetH B C D \<and> BetH A B D" 
      using \<open>\<not> local.cut l A G\<close> by fastforce
  }
  ultimately show ?thesis 
    by blast
qed 

lemma betH_outH2__betH:
  assumes "BetH A B C" and
    "outH B C C'" and
    "outH B A A'"
  shows "BetH A' B C'" 
proof -

  have "BetH B C C' \<or> BetH B C' C \<or> (B \<noteq> C \<and> C = C')" 
    using assms(2) outH_def by blast
  moreover have "BetH B A A' \<or> BetH B A' A \<or> (B \<noteq> A \<and> A = A')" 
    using assms(3) outH_def by blast
  moreover
  {
    assume "BetH B C C'" 
    hence "BetH A' B C" 
      using assms(1) betH_trans betH_trans0 between_comm calculation(2) by blast
  }
  moreover
  {
    assume "BetH B C' C" 
    hence "BetH A' B C" 
      using assms(1) betH_trans betH_trans0 between_comm calculation(2) by blast
  }
  moreover
  {
    assume "B \<noteq> C \<and> C = C'" 
    hence "BetH A' B C" 
      using assms(1) betH_trans betH_trans0 between_comm calculation(2) by blast
  }
  ultimately show ?thesis
    by (meson betH_trans betH_trans0 between_comm)
qed

lemma cong_existence':
  fixes A B::TPoint
  assumes "A \<noteq> B" and
    "IncidL M l" 
  shows "\<exists> A' B'. IncidL A' l \<and> IncidL B' l \<and> BetH A' M B' \<and> CongH M A' A B \<and> CongH M B' A B" 
proof -
  have "\<exists> P. IncidL P l \<and> M \<noteq> P" 
    by (metis Is_line assms(2) two_points_on_line)
  then obtain P where "IncidL P l" and "M \<noteq> P" 
    by blast
  obtain P' where "BetH P M P'" 
    using \<open>M \<noteq> P\<close> between_out by presburger
  obtain A' where "IncidL A' l" and "outH M P A'" and "CongH M A' A B" 
    using Is_line \<open>IncidL P l\<close> \<open>M \<noteq> P\<close> assms(1) assms(2) cong_existence by blast
  moreover
  have "IncidL P' l" 
    using ColH_def \<open>BetH P M P'\<close> \<open>IncidL P l\<close> assms(2) betH_colH inter_incid_uniquenessH by blast
  then obtain B' where "IncidL B' l" and "outH M P' B'" and "CongH M B' A B" 
    by (metis Is_line \<open>BetH P M P'\<close> assms(1) assms(2) betH_distincts cong_existence)
  ultimately show ?thesis 
    using \<open>BetH P M P'\<close> betH_outH2__betH by blast
qed

lemma betH_to_bet:
  assumes "BetH A B C" 
  shows "Bet A B C \<and> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" 
  using Bet_def assms betH_distincts by presburger

lemma betH_line:
  assumes "BetH A B C" 
  shows "\<exists> l. IncidL A l \<and> IncidL B l \<and> IncidL C l" 
  by (meson ColH_def assms betH_colH)

(****************** between_identity ************************)

lemma bet_identity: 
  assumes "Bet A B A"
  shows "A = B" 
  using Bet_def assms between_diff by blast

(************************************************************)

lemma morph: 
  assumes "IsL l" and
    "IsL m " and
    "EqL l m"
  shows "\<forall> A. IncidL A l \<longleftrightarrow> IncidL A m" 
  using EqL_sym IncidL_morphism assms(1) assms(2) assms(3) by blast

lemma point3_online_exists:
  assumes "IncidL A l" and 
    "IncidL B l"
  shows "\<exists> C. IncidL C l  \<and> C \<noteq> A \<and> C \<noteq> B" 
  by (metis (full_types) assms(2) betH_distincts cong_existence' lower_dim_2)

lemma not_betH121:
  shows "\<not> BetH A B A" 
  using between_diff by blast

(***************************** cong_identity ***********************)

lemma cong_identity:
  assumes "Cong A B C C"
  shows "A = B" 
  using Cong_def assms by presburger

(************************ cong_inner_transitivity ****************************)

lemma cong_inner_transitivity:
  assumes "Cong A B C D" and
    "Cong A B E F"
  shows "Cong C D E F" 
  by (metis Cong_def assms(1) assms(2) cong_pseudo_transitivity)

lemma other_point_on_line:
  assumes "IncidL A l"
  shows "\<exists> B. A \<noteq> B \<and> IncidL B l" 
  by (metis Is_line assms two_points_on_line)

lemma bet_disjoint:
  assumes "BetH A B C"
  shows "disjoint A B B C" 
proof -
  {
    assume "\<not> disjoint A B B C"
    then obtain P where "BetH A P B" and "BetH B P C" 
      using disjoint_def by blast
    have "BetH P B C \<and> BetH A P C" 
      using betH_trans0 \<open>BetH A P B\<close> assms by blast
    hence False 
      using \<open>BetH B P C\<close> between_only_one' by blast
  }
  thus ?thesis 
    by blast
qed

lemma addition_betH:
  assumes "BetH A B C" and
    "BetH A' B' C'" and
    "CongH A B A' B'" and
    "CongH B C B' C'"
  shows "CongH A C A' C'" 
  using addition assms(1) assms(2) assms(3) assms(4) bet_disjoint between_col by blast

lemma outH_trivial: 
  assumes "A \<noteq> B" 
  shows "outH A B B" 
  by (simp add: assms outH_def)

lemma same_side_refl:
  assumes "IsL l" and (** ROLL ADD IsL l **)
    "\<not> IncidL A l" 
  shows "same_side A A l"
proof -
  obtain x x0 where "IncidL x0 l" and "IncidL x l" and "x \<noteq> x0" 
    using two_points_on_line assms(1) by blast
  {
    assume "A = x" 
    hence "same_side A A l" 
      using \<open>IncidL x l\<close> assms(2) by fastforce
  }
  moreover
  {
    assume "A \<noteq> x" 
    obtain x1 where "BetH A x x1" 
      by (metis \<open>IncidL x l\<close> assms(2) between_out)
    have "\<not> IncidL x1 l" 
      using \<open>BetH A x x1\<close> \<open>IncidL x l\<close> assms(2) betH_expand betH_line 
        inter_incid_uniquenessH by blast
    moreover have "\<exists> I. IncidL I l \<and> BetH A I x1" 
      using \<open>BetH A x x1\<close> \<open>IncidL x l\<close> by blast
    ultimately have "same_side A A l" 
      using assms(1) assms(2) local.cut_def same_side_def by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma same_side_prime_refl: 
  assumes "\<not> ColH A B C"
  shows "same_side' C C A B" 
  using ColH_def assms ncolH_distincts same_side'_def same_side_refl by presburger

lemma outH_expand: 
  assumes "outH A B C" 
  shows "outH A B C \<and> ColH A B C \<and> A \<noteq> C \<and> A \<noteq> B" 
  by (metis assms betH_colH colH_permut_132 colH_trivial122 outH_def)

lemma construction_uniqueness:
  assumes "BetH A B D" and
    "BetH A B E" and
    "CongH B D B E"
  shows "D = E" 
proof -
  have "A \<noteq> D" 
    using assms(1) between_diff by blast
  have "A \<noteq> E" 
    using assms(2) not_betH121 by blast
  have "ColH A B D" 
    by (simp add: assms(1) betH_colH)
  have "ColH A B E" 
    using assms(2) betH_colH by fastforce
  have "A \<noteq> B" 
    using assms(1) betH_distincts by auto
  then obtain C where "\<not> ColH A B C" 
    using  ncolH_exists by presburger
  have "CongaH A C D A C E"
  proof -
    have"\<not> ColH A C D" 
      by (meson \<open>A \<noteq> D\<close> \<open>ColH A B D\<close> \<open>\<not> ColH A B C\<close> colH_permut_132
          colH_trans colH_trivial121)
    moreover have "\<not> ColH A C E" 
      by (metis \<open>A \<noteq> E\<close> \<open>ColH A B E\<close> \<open>\<not> ColH A B C\<close> colH_trivial121 
          colH_trivial122 inter_uniquenessH)
    moreover have "CongH A C A C" 
      by (metis calculation(1) colH_trivial112 congH_refl)
    moreover have "CongH A D A E" 
      by (metis addition_betH assms(1) assms(2) assms(3) congH_refl)
    moreover have "CongaH C A D C A E"  
    proof-
      have "CongaH C A B C A B" 
        by (meson \<open>\<not> ColH A B C\<close> colH_permut_231 conga_refl)
      moreover have "outH A C C" 
        using \<open>\<not> ColH A C D\<close> ncolH_distincts outH_trivial by presburger
      moreover have "outH A B D" 
        by (simp add: assms(1) outH_def)
      moreover have "outH A B E" 
        by (simp add: assms(2) outH_def)
      ultimately show ?thesis 
        using conga_out_conga by blast
    qed
    ultimately show ?thesis 
      using cong_5 by blast
  qed
  moreover have "\<not> ColH D C A" 
    by (metis ncolH_distincts \<open>A \<noteq> D\<close> \<open>ColH A B D\<close> \<open>\<not> ColH A B C\<close> inter_uniquenessH)
  moreover hence "\<not> ColH A C D" 
    using colH_permut_321 by blast
  moreover hence "\<not> ColH C A D" 
    using colH_permut_213 by blast
  moreover have "same_side' D E C A" 
  proof -
    obtain F where "BetH B A F" 
      using \<open>A \<noteq> B\<close> between_out by fastforce
    obtain l where "IncidL C l" and "IncidL A l" 
      using ColH_def colH_trivial122 by blast
    have "C \<noteq> A" 
      using calculation(2) colH_trivial122 by auto
    moreover
    have "\<forall> l. IsL l \<and> IncidL C l \<and> IncidL A l \<longrightarrow> same_side D E l"
    proof -
      {
        fix l
        assume "IsL l" and "IncidL C l" and "IncidL A l"
        have "cut l D F" 
        proof -
          {
            assume "IncidL D l" 
            have "ColH A C D" 
              using ColH_def \<open>IncidL A l\<close> \<open>IncidL C l\<close> \<open>IncidL D l\<close> \<open>IsL l\<close> by blast
            have False 
              using \<open>ColH A C D\<close> \<open>\<not> ColH A C D\<close> by auto
          }
          hence "\<not> IncidL D l" 
            by blast
          moreover
          {
            assume "IncidL F l" 
            have "ColH A C F" 
              using ColH_def Is_line \<open>IncidL A l\<close> \<open>IncidL C l\<close> \<open>IncidL F l\<close> by blast
            have False 
              using ColH_def \<open>BetH B A F\<close> \<open>IncidL A l\<close> \<open>IncidL C l\<close> \<open>IncidL F l\<close>
                \<open>IsL l\<close> \<open>\<not> ColH A B C\<close> betH_distincts betH_line inter_incid_uniquenessH by blast
          }
          hence "\<not> IncidL F l" 
            by blast
          moreover have "\<exists> I. IncidL I l \<and> BetH D I F" 
            using \<open>BetH B A F\<close> \<open>IncidL A l\<close> assms(1) betH_trans between_comm by blast
          ultimately show ?thesis
            by (simp add: \<open>IsL l\<close> local.cut_def)
        qed
        moreover have "cut l E F" 
        proof -
          {
            assume "IncidL E l" 
            have "ColH A C E" 
              using ColH_def \<open>IncidL A l\<close> \<open>IncidL C l\<close> \<open>IncidL E l\<close> \<open>IsL l\<close> by blast
            hence False 
              using ColH_def \<open>A \<noteq> E\<close> \<open>\<not> ColH A B C\<close> assms(2) betH_line 
                inter_incid_uniquenessH by blast
          }
          hence "\<not> IncidL E l" 
            by blast
          moreover
          {
            assume "IncidL F l" 
            have "ColH A C F" 
              using \<open>IncidL F l\<close> \<open>local.cut l D F\<close> local.cut_def by auto
            hence False 
              using \<open>IncidL F l\<close> \<open>local.cut l D F\<close> local.cut_def by blast
          }
          hence "\<not> IncidL F l" 
            by blast
          moreover have "\<exists> I. IncidL I l \<and> BetH E I F" 
            using \<open>BetH B A F\<close> \<open>IncidL A l\<close> assms(2) betH_trans between_comm by blast
          ultimately show ?thesis
            by (simp add: \<open>IsL l\<close> local.cut_def)
        qed
        ultimately have "same_side D E l"
          using \<open>IsL l\<close> same_side_def by blast
      }
      thus ?thesis 
        by blast
    qed
    ultimately show ?thesis 
      using same_side'_def by auto
  qed
  ultimately have "outH C D E" 
    using same_side_prime_refl by (meson cong_4_uniqueness conga_refl)
  thus ?thesis 
    using \<open>ColH A B D\<close> \<open>ColH A B E\<close> \<open>\<not> ColH A B C\<close> colH_trivial122 
      inter_uniquenessH outH_expand by blast
qed

lemma out_distinct:
  assumes "outH A B C" 
  shows "A \<noteq> B \<and> A \<noteq> C" 
  using assms outH_expand by auto

lemma out_same_side:
  assumes "IncidL A l" and
    "\<not> IncidL B l" and
    "outH A B C"
  shows "same_side B C l" 
proof -
  have "A \<noteq> B" 
    using assms(1) assms(2) by blast
  obtain P where "BetH B A P" 
    using \<open>A \<noteq> B\<close> between_out by presburger
  {
    assume "IncidL P l"
    have "ColH B A P" 
      by (simp add: \<open>BetH B A P\<close> between_col)
    obtain ll where "IncidL B ll" and "IncidL A ll" and "IncidL P ll" 
      using \<open>BetH B A P\<close> betH_line by blast
    hence "EqL l ll" 
      by (metis Is_line \<open>BetH B A P\<close> \<open>IncidL P l\<close> assms(1) betH_distincts line_uniqueness)
    hence False 
      using Is_line \<open>IncidL B ll\<close> \<open>IncidL P l\<close> assms(2) morph by blast
  }
  hence "\<not> IncidL P l"
    by blast
  have "cut l B P" 
    using assms(1) \<open>BetH B A P\<close> Is_line \<open>\<not> IncidL P l\<close> assms(2) local.cut_def by blast
  moreover have "cut l C P"
  proof -
    have "\<not> IncidL C l"
      using ColH_def assms(1) assms(2) assms(3) inter_incid_uniquenessH 
        outH_expand by blast
    moreover have "BetH C A P" 
      by (metis betH_outH2__betH betH_to_bet outH_trivial \<open>BetH B A P\<close> assms(3))
    ultimately show ?thesis 
      using assms(1) Is_line \<open>\<not> IncidL P l\<close> local.cut_def by blast
  qed
  ultimately show ?thesis
    using Is_line assms(1) same_side_def by blast
qed

lemma between_one:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "ColH A B C" 
  shows "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
proof -
  obtain D where "\<not> ColH A C D" 
    using assms(2) ncolH_exists by presburger
  have "B \<noteq> D" 
    using \<open>\<not> ColH A C D\<close> assms(4) colH_permut_132 by blast
  obtain G where "BetH B D G" 
    using \<open>B \<noteq> D\<close> between_out by blast
  have "A \<noteq> D" 
    using \<open>\<not> ColH A C D\<close> colH_trivial121 by force
  then obtain lAD where "IsL lAD" and "IncidL A lAD" and "IncidL D lAD" 
    using line_existence by blast
  have "C \<noteq> D" 
    using \<open>\<not> ColH A C D\<close> colH_trivial122 by blast
  then obtain lCD where "IsL lCD" and "IncidL C lCD" and "IncidL D lCD" 
    using line_existence by blast
  {
    assume "ColH B G C"
    hence False 
      by (metis \<open>BetH B D G\<close> \<open>\<not> ColH A C D\<close> assms(3) assms(4) between_col 
          colH_permut_312 colH_trans colH_trivial122 not_betH121)
  }
  hence "\<not> ColH B G C" 
    by blast
  {
    assume "ColH B G A"
    hence False 
      by (meson colH_permut_312 colH_trans colH_trivial122 \<open>\<not> ColH B G C\<close> 
          assms(1) assms(4))
  }
  hence "\<not> ColH B G A" 
    by blast
  have "\<not> IncidL C lAD" 
    using ColH_def \<open>IncidL A lAD\<close> \<open>IncidL D lAD\<close> \<open>IsL lAD\<close> \<open>\<not> ColH A C D\<close> by blast
  have "\<not> IncidL A lCD" 
    using \<open>A \<noteq> D\<close> \<open>IncidL A lAD\<close> \<open>IncidL C lCD\<close> \<open>IncidL D lAD\<close> \<open>IncidL D lCD\<close> 
      \<open>\<not> IncidL C lAD\<close> inter_incid_uniquenessH by blast
  {
    assume "IncidL B lAD"
    have "ColH A B D" 
      using ColH_def \<open>IncidL A lAD\<close> \<open>IncidL B lAD\<close> \<open>IncidL D lAD\<close> \<open>IsL lAD\<close> by blast
    hence False 
      using \<open>\<not> ColH A C D\<close> assms(1) assms(4) colH_trans colH_trivial121 by blast
  }
  hence "\<not> IncidL B lAD" 
    by blast
  {
    assume "IncidL G lAD"
    have "ColH A D G" 
      using ColH_def Is_line \<open>IncidL A lAD\<close> \<open>IncidL D lAD\<close> \<open>IncidL G lAD\<close> by blast
    hence False 
      using betH_colH \<open>BetH B D G\<close> \<open>IncidL D lAD\<close> \<open>IncidL G lAD\<close> \<open>\<not> IncidL B lAD\<close>
        betH_line inter_incid_uniquenessH by blast
  }
  hence "\<not> IncidL G lAD" 
    by blast
  have "cut lAD B G" 
    using \<open>BetH B D G\<close> \<open>IncidL D lAD\<close> \<open>IsL lAD\<close> \<open>\<not> IncidL B lAD\<close> \<open>\<not> IncidL G lAD\<close>
      local.cut_def by blast
  {
    assume "IncidL B lCD"
    have "ColH B C D" 
      using ColH_def \<open>IncidL B lCD\<close> \<open>IncidL C lCD\<close> \<open>IncidL D lCD\<close> \<open>IsL lCD\<close> by blast
    hence False 
      by (meson colH_permut_231 colH_trans colH_trivial122 \<open>\<not> ColH A C D\<close> assms(3) assms(4))
  }
  hence "\<not> IncidL B lCD" 
    by blast
  {
    assume "IncidL G lCD"
    have "ColH C D G" 
      using ColH_def \<open>IncidL C lCD\<close> \<open>IncidL D lCD\<close> \<open>IncidL G lCD\<close> \<open>IsL lCD\<close> by blast
    hence False 
      using betH_colH \<open>BetH B D G\<close> \<open>IncidL D lCD\<close> \<open>IncidL G lCD\<close> \<open>\<not> IncidL B lCD\<close>
        betH_line inter_incid_uniquenessH by blast
  }
  hence "\<not> IncidL G lCD" 
    by blast
  have "cut lCD B G" 
    using Is_line \<open>BetH B D G\<close> \<open>IncidL D lCD\<close> \<open>\<not> IncidL B lCD\<close> 
      \<open>\<not> IncidL G lCD\<close> local.cut_def by blast
  obtain bgc where "IsP bgc" and "IncidP B bgc" and "IncidP G bgc" and "IncidP C bgc" 
    using \<open>\<not> ColH B G C\<close> plan_existence by blast
  obtain bga where "IsP bga" and "IncidP B bga" and "IncidP G bga" and "IncidP A bga" 
    using \<open>\<not> ColH B G A\<close> plan_existence by blast
  have "IncidLP lAD bgc" 
    by (metis (mono_tags, lifting) betH_colH line_on_plane \<open>A \<noteq> D\<close> \<open>BetH B D G\<close> 
        \<open>IncidL A lAD\<close> \<open>IncidL D lAD\<close> \<open>IncidP B bgc\<close> \<open>IncidP C bgc\<close> \<open>IncidP G bgc\<close> 
        \<open>IsL lAD\<close> \<open>IsP bgc\<close> assms(3) assms(4) colH_permut_312 line_on_plane')
  have "IncidLP lCD bga" 
    by (metis (mono_tags, lifting) betH_colH line_on_plane \<open>BetH B D G\<close> \<open>C \<noteq> D\<close> 
        \<open>IncidL C lCD\<close> \<open>IncidL D lCD\<close> \<open>IncidP A bga\<close> \<open>IncidP B bga\<close> \<open>IncidP G bga\<close>
        \<open>IsL lCD\<close> \<open>IsP bga\<close> assms(1) assms(4) colH_permut_312 line_on_plane')
  show ?thesis
  proof -
    {
      assume "cut lAD B C"
      then obtain I where "IncidL I lAD" and "BetH B I C" 
        using local.cut_def by blast
      have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
      proof -
        {
          assume "cut lCD B A"
          {
            assume "A = I"
            have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
              by (simp add: \<open>A = I\<close> \<open>BetH B I C\<close>)
          }
          moreover
          {
            assume "A \<noteq> I"
            have "ColH A D I" 
              using ColH_def Is_line \<open>IncidL A lAD\<close> \<open>IncidL D lAD\<close> \<open>IncidL I lAD\<close> by blast
            have "\<not> ColH B C D" 
              by (meson \<open>\<not> ColH A C D\<close> assms(3) assms(4) colH_permut_231 
                  colH_trans colH_trivial122)
            have "ColH B C I" 
              by (simp add: \<open>BetH B I C\<close> betH_colH colH_permut_132)
            have "ColH B C A" 
              by (simp add: assms(4) colH_permut_231)
            have "ColH D A I" 
              using \<open>ColH A D I\<close> colH_permut_213 by blast
            have "ColH D A A" 
              by (simp add: colH_trivial122)
            hence False using inter_uniquenessH 
              by (metis \<open>A \<noteq> I\<close> \<open>ColH B C A\<close> \<open>ColH B C I\<close> \<open>ColH D A I\<close> \<open>\<not> ColH B C D\<close>)
            hence "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
              by blast
          }
          ultimately
          have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
            by fastforce
        }
        moreover 
        {
          assume "cut lCD G A"
          {
            assume "A = I"
            have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
              by (simp add: \<open>A = I\<close> \<open>BetH B I C\<close>)
          }
          moreover
          {
            assume "A \<noteq> I"
            have "ColH A D I" 
              using ColH_def Is_line \<open>IncidL A lAD\<close> \<open>IncidL D lAD\<close> \<open>IncidL I lAD\<close> by blast
            have "D \<noteq> A" 
              using \<open>A \<noteq> D\<close> by blast
            moreover have "\<not> ColH B C D" 
              by (meson \<open>\<not> ColH A C D\<close> assms(3) assms(4) colH_permut_231 
                  colH_trans colH_trivial122)
            moreover have "ColH B C I" 
              by (simp add: \<open>BetH B I C\<close> betH_colH colH_permut_132)
            moreover have "ColH B C A" 
              by (simp add: assms(4) colH_permut_231)
            moreover have "ColH D A I" 
              using \<open>ColH A D I\<close> colH_permut_213 by blast
            moreover have "ColH D A A" 
              by (simp add: colH_trivial122)
            hence False 
              by (metis \<open>A \<noteq> I\<close> calculation(2) calculation(3) calculation(4) 
                  calculation(5) inter_uniquenessH)
            hence "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
              by blast
          }
          ultimately have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
            by blast
        }
        ultimately show ?thesis
          using \<open>IncidLP lCD bga\<close> \<open>IncidP A bga\<close> \<open>IncidP B bga\<close> \<open>IncidP G bga\<close>
            \<open>IsL lCD\<close> \<open>IsP bga\<close> \<open>\<not> ColH B G A\<close> \<open>\<not> IncidL A lCD\<close> 
            \<open>local.cut lCD B G\<close> pasch by blast
      qed
    }
    moreover 
    {
      assume "cut lAD G C"
      have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
      proof -
        {
          assume "cut lCD B A" 
          then obtain I where "IncidL I lCD" and "BetH B I A" 
            using local.cut_def by blast
          {
            assume "C = I"
            hence "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
              by (simp add: \<open>BetH B I A\<close>)
          }
          moreover
          {
            assume "C \<noteq> I"
            have "ColH C D I" 
              using ColH_def Is_line \<open>IncidL C lCD\<close> \<open>IncidL D lCD\<close> \<open>IncidL I lCD\<close> by blast
            have "D \<noteq> C" 
              using \<open>C \<noteq> D\<close> by blast
            moreover have "\<not> ColH A B D" 
              using \<open>\<not> ColH A C D\<close> assms(1) assms(4) colH_trans colH_trivial121 by blast
            moreover have "ColH A B I" 
              by (simp add: \<open>BetH B I A\<close> betH_colH colH_permut_312)
            moreover have "ColH A B C" 
              by (simp add: assms(4))
            moreover have "ColH D C I" 
              by (simp add: \<open>ColH C D I\<close> colH_permut_213)
            moreover have "ColH D C C" 
              by (simp add: colH_trivial122)
            ultimately have False 
              using \<open>C \<noteq> I\<close> inter_uniquenessH by blast
            hence "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
              by blast
          }
          ultimately have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
            by blast
        }
        moreover {
          assume"cut lCD G A" 
          obtain E where "IncidL E lAD" and "BetH G E C" 
            using local.cut_def \<open>local.cut lAD G C\<close> by blast
          obtain F where "IncidL F lCD" and "BetH G F A" 
            using \<open>local.cut lCD G A\<close> local.cut_def by blast
          {
            assume "ColH A G E"
            hence "ColH A C D" 
              using \<open>BetH G E C\<close> \<open>\<not> ColH B G A\<close> assms(4) betH_colH 
                colH_permut_231 colH_trivial121 inter_uniquenessH by blast
            hence False 
              using \<open>\<not> ColH A C D\<close> by auto
          }
          hence "\<not> ColH A G E" 
            by blast
          have "C \<noteq> F" 
            using between_col \<open>BetH G E C\<close> \<open>BetH G F A\<close> \<open>\<not> ColH A G E\<close>
              betH_trans0 colH_permut_312 by blast
          obtain lCF where "IsL lCF" and "IncidL C lCF" and "IncidL F lCF" 
            using \<open>IncidL C lCD\<close> \<open>IncidL F lCD\<close> \<open>IsL lCD\<close> by blast
          {
            assume "IncidL E lCF" 
            hence False
              by (metis (full_types) Hilbert_neutral_dimensionless.betH_expand
                  Hilbert_neutral_dimensionless_axioms \<open>BetH G E C\<close> \<open>C \<noteq> F\<close> \<open>IncidL C lCD\<close>
                  \<open>IncidL C lCF\<close> \<open>IncidL E lCF\<close> \<open>IncidL F lCD\<close> \<open>IncidL F lCF\<close>
                  \<open>\<not> IncidL G lCD\<close> betH_line inter_incid_uniquenessH)
          }
          hence "\<not> IncidL E lCF" 
            by blast
          have "cut lCF A G" 
            by (metis IncidL_morphism Is_line \<open>BetH G F A\<close> \<open>C \<noteq> F\<close> \<open>IncidL C lCD\<close> 
                \<open>IncidL C lCF\<close> \<open>IncidL F lCD\<close> \<open>IncidL F lCF\<close> \<open>\<not> IncidL A lCD\<close>
                \<open>\<not> IncidL G lCD\<close> between_comm line_uniqueness local.cut_def)
          obtain p where "IncidP A p" and "IncidP G p" and "IncidP E p" 
            using IncidLP_def \<open>IncidL A lAD\<close> \<open>IncidL E lAD\<close> \<open>IncidLP lAD bgc\<close>
              \<open>IncidP G bgc\<close> by blast
          have "IncidP C p" 
            using \<open>BetH G E C\<close> \<open>IncidP E p\<close> \<open>IncidP G p\<close> betH_colH line_on_plane' by blast
          moreover have "IncidP F p" 
            by (metis \<open>BetH G F A\<close> \<open>IncidP A p\<close> \<open>IncidP G p\<close> betH_colH 
                colH_permut_312 line_on_plane') 
          ultimately have "IncidLP lCF p" 
            using Is_plane \<open>C \<noteq> F\<close> \<open>IncidL C lCF\<close> \<open>IncidL F lCF\<close> \<open>IsL lCF\<close> 
              line_on_plane by blast
          { 
            assume "cut lCF A E"
            then obtain I where "IncidL I lCF" and "BetH A I E" 
              using local.cut_def by blast
            have "I = D" 
              by (metis (full_types) Hilbert_neutral_dimensionless.betH_colH 
                  Hilbert_neutral_dimensionless_axioms \<open>BetH A I E\<close> \<open>C \<noteq> F\<close> \<open>IncidL A lAD\<close> 
                  \<open>IncidL C lCD\<close> \<open>IncidL C lCF\<close> \<open>IncidL D lAD\<close> \<open>IncidL D lCD\<close> \<open>IncidL E lAD\<close> 
                  \<open>IncidL F lCD\<close> \<open>IncidL F lCF\<close> \<open>IncidL I lCF\<close> \<open>\<not> IncidL A lCD\<close> 
                  betH_line inter_incid_uniquenessH)
            {
              assume "ColH A E C"
              have "A \<noteq> E" 
                using \<open>BetH A I E\<close> not_betH121 by fastforce
              have "ColH A D E" 
                using \<open>BetH A I E\<close> \<open>I = D\<close> between_col by auto
              hence "ColH A C D" 
                by (meson Hilbert_neutral_dimensionless.colH_permut_132 
                    colH_trans colH_trivial121 Hilbert_neutral_dimensionless_axioms
                    \<open>A \<noteq> E\<close> \<open>ColH A E C\<close>) 
              hence False 
                using \<open>\<not> ColH A C D\<close> by blast
            }
            hence "\<not> ColH A E C"
              by blast
            obtain lBD where "IncidL B lBD" and "IncidL D lBD" 
              using \<open>B \<noteq> D\<close> line_existence by blast
            have "cut lBD A E" 
              by (metis betH_colH cut_def 
                  Is_line \<open>BetH A I E\<close> \<open>I = D\<close> \<open>IncidL A lAD\<close> \<open>IncidL B lBD\<close> \<open>IncidL D lAD\<close> 
                  \<open>IncidL D lBD\<close> \<open>IncidL E lAD\<close> \<open>\<not> IncidL B lAD\<close> inter_incid_uniquenessH)
            have "IncidLP lBD p" 
              by (metis IncidLP_def Is_line \<open>B \<noteq> D\<close> \<open>I = D\<close> \<open>IncidL B lBD\<close> \<open>IncidL D lBD\<close> 
                  \<open>IncidL I lCF\<close> \<open>IncidLP lCF p\<close> \<open>IncidP A p\<close> \<open>IncidP C p\<close> assms(2) assms(4) 
                  colH_permut_312 line_on_plane line_on_plane')
            { 
              assume "cut lBD A C"
              then obtain I where "IncidL I lBD" and "BetH A I C" 
                using local.cut_def by blast
              hence "ColH A I C" 
                using betH_colH by blast
              hence "I = B"
              proof -
                have "D \<noteq> B" 
                  using \<open>B \<noteq> D\<close> by auto
                moreover have "\<not> ColH A C D" 
                  by (simp add: \<open>\<not> ColH A C D\<close>)
                moreover have "ColH A C I" 
                  using \<open>ColH A I C\<close> colH_permut_132 by blast
                moreover have "ColH A C B" 
                  by (simp add: assms(4) colH_permut_132)
                moreover have "ColH D B I" 
                  using ColH_def Is_line \<open>IncidL B lBD\<close> \<open>IncidL D lBD\<close> \<open>IncidL I lBD\<close> by blast
                moreover have "ColH D B B" 
                  by (simp add: colH_trivial122)
                ultimately show ?thesis
                  using inter_uniquenessH by blast
              qed
              hence "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
                using \<open>BetH A I C\<close> by auto
            }
            moreover {
              assume "cut lBD E C"
              then obtain I where "IncidL I lBD" and "BetH E I C" 
                using local.cut_def by blast
              hence "ColH E I C" 
                by (simp add: betH_colH)
              hence "I = G"
              proof -
                have "C \<noteq> E" 
                  using \<open>IncidL E lAD\<close> \<open>\<not> IncidL C lAD\<close> by auto
                moreover have "\<not> ColH D B C" 
                  by (metis \<open>BetH B D G\<close> \<open>\<not> ColH B G C\<close> betH_colH colH_permut_213 
                      colH_trans colH_trivial122)
                moreover have "ColH D B I" 
                  using ColH_def Is_line \<open>IncidL B lBD\<close> \<open>IncidL D lBD\<close> \<open>IncidL I lBD\<close> by blast
                moreover have "ColH D B G" 
                  using \<open>BetH B D G\<close> between_col colH_permut_213 by blast
                moreover have "ColH C E I" 
                  using \<open>ColH E I C\<close> colH_permut_312 by blast
                moreover have "ColH C E G" 
                  by (simp add: \<open>BetH G E C\<close> between_col between_comm)
                ultimately show ?thesis
                  using inter_uniquenessH by blast
              qed
              hence "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
                using \<open>BetH E I C\<close> \<open>BetH G E C\<close> between_only_one' by blast
            }
            ultimately have "BetH A B C \<or> BetH B C A \<or> BetH B A C"
              using pasch inter_incid_uniquenessH Is_line Is_plane \<open>C \<noteq> D\<close> \<open>IncidL B lBD\<close> 
                \<open>IncidL C lCD\<close> \<open>IncidL D lBD\<close> \<open>IncidL D lCD\<close> \<open>IncidLP lBD p\<close> \<open>IncidP A p\<close> 
                \<open>IncidP C p\<close> \<open>IncidP E p\<close> \<open>\<not> ColH A E C\<close> \<open>\<not> IncidL B lCD\<close>
                \<open>local.cut lBD A E\<close> by fastforce
          }
          moreover 
          {
            assume "cut lCF G E"
            then obtain I where "IncidL I lCF" and "BetH G I E" 
              using local.cut_def by blast
            hence "ColH G I E" 
              using betH_expand by blast
            have "I = C" 
            proof -
              have "F \<noteq> C" 
                using \<open>C \<noteq> F\<close> by auto
              moreover have "\<not> ColH G E F" 
                using \<open>BetH G F A\<close> \<open>\<not> ColH A G E\<close> betH_colH colH_permut_132
                  colH_trans colH_trivial121 by blast
              moreover have "ColH G E I" 
                using \<open>ColH G I E\<close> colH_permut_132 by presburger
              moreover have "ColH G E C" 
                by (simp add: \<open>BetH G E C\<close> betH_colH)
              moreover have "ColH F C I" 
                using ColH_def Is_line \<open>IncidL C lCF\<close> \<open>IncidL F lCF\<close> 
                  \<open>IncidL I lCF\<close> by blast
              moreover have "ColH F C C" 
                by (simp add: colH_trivial122)
              ultimately show ?thesis 
                using inter_uniquenessH by blast
            qed
            hence "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
              using \<open>BetH G E C\<close> \<open>BetH G I E\<close> between_comm between_only_one by blast
          }
          ultimately have "BetH A B C \<or> BetH B C A \<or> BetH B A C" 
            using Is_plane \<open>IncidLP lCF p\<close> \<open>IncidP A p\<close> \<open>IncidP E p\<close> \<open>IncidP G p\<close> 
              \<open>IsL lCF\<close> \<open>\<not> ColH A G E\<close> \<open>\<not> IncidL E lCF\<close> \<open>local.cut lCF A G\<close> 
              pasch by blast
        }
        ultimately show ?thesis 
          using \<open>IncidLP lCD bga\<close> \<open>IncidP A bga\<close> \<open>IncidP B bga\<close> \<open>IncidP G bga\<close>
            \<open>IsL lCD\<close> \<open>IsP bga\<close> \<open>\<not> ColH B G A\<close> \<open>\<not> IncidL A lCD\<close> 
            \<open>local.cut lCD B G\<close> pasch by blast
      qed
    }
    ultimately show ?thesis 
      using pasch \<open>IsL lAD\<close> \<open>IsP bgc\<close> \<open>IncidLP lAD bgc\<close> \<open>IncidP B bgc\<close> \<open>IncidP C bgc\<close>
        \<open>IncidP G bgc\<close> \<open>\<not> ColH B G C\<close> \<open>\<not> IncidL C lAD\<close> \<open>local.cut lAD B G\<close> by blast
  qed
qed

lemma betH_dec: 
  (*assumes "A \<noteq> B" and
"B \<noteq> C" and
"A \<noteq> C" *)
  shows "BetH A B C \<or> \<not> BetH A B C" 
  by blast

lemma cut2_not_cut:
  assumes "\<not> ColH A B C" and
    "cut l A B" and
    "cut l A C" 
  shows "\<not> cut l B C" 
proof -
  have "\<not> IncidL A l" 
    using assms(2) local.cut_def by blast
  have "\<not> IncidL B l" 
    using assms(2) local.cut_def by blast
  have "\<not> IncidL C l" 
    using assms(3) local.cut_def by blast
  obtain AB where "IncidL AB l" and "BetH A AB B" 
    using assms(2) local.cut_def by blast
  hence "ColH A AB A" 
    using colH_trivial121 by blast
  obtain AC where "IncidL AC l" and "BetH A AC C" 
    using assms(3) local.cut_def by blast
  hence "ColH A AC C" 
    by (simp add: between_col)
  {
    assume "cut l B C"
    then obtain BC where "IncidL BC l" and "BetH B BC C" 
      using local.cut_def by blast
    hence "ColH B BC C" 
      by (simp add: between_col)
    have "ColH AB AC BC" 
      using ColH_def Is_line \<open>IncidL AB l\<close> \<open>IncidL AC l\<close> \<open>IncidL BC l\<close> by blast
    have "AB \<noteq> AC" 
      using colH_trans \<open>BetH A AB B\<close> \<open>ColH A AB A\<close> \<open>ColH A AC C\<close> assms(1) 
        betH_expand by blast
    have "AB \<noteq> BC" 
      by (metis \<open>BetH A AB B\<close> \<open>ColH B BC C\<close> assms(1) betH_colH colH_trans ncolH_distincts)
    have "BC \<noteq> AC" 
      by (metis \<open>BetH A AC C\<close> \<open>BetH B BC C\<close> assms(1) betH_colH between_comm 
          colH_trans ncolH_distincts)
    have "BetH AB AC BC \<or> BetH AC BC AB \<or> BetH BC AB AC" 
      using \<open>AB \<noteq> AC\<close> \<open>AB \<noteq> BC\<close> \<open>BC \<noteq> AC\<close> \<open>ColH AB AC BC\<close> between_comm between_one by blast
    moreover
    {
      assume "BetH AB AC BC"
      then obtain m where "IncidL A m" and "IncidL C m" 
        using \<open>BetH A AC C\<close> betH_line by blast
      have "\<not> ColH AB BC B" 
        using ColH_def \<open>AB \<noteq> BC\<close> \<open>IncidL AB l\<close> \<open>IncidL BC l\<close> \<open>\<not> IncidL B l\<close>
          inter_incid_uniquenessH by blast
      have "\<not> IncidL B m" 
        using Hilbert_neutral_dimensionless_pre.ColH_def Is_line \<open>IncidL A m\<close>
          \<open>IncidL C m\<close> assms(1) by fastforce
      have "cut m AB BC" 
      proof -
        {
          assume "IncidL AB m"
          hence "ColH A B C" 
            using betH_colH \<open>BetH A AB B\<close> \<open>IncidL A m\<close> \<open>\<not> IncidL B m\<close> betH_line
              inter_incid_uniquenessH by blast
          hence ?thesis         
            by (simp add: assms(1))
        }
        moreover
        {
          assume "IncidL BC m"
          hence "ColH A B C" 
            using betH_colH \<open>BetH B BC C\<close> \<open>IncidL C m\<close> \<open>\<not> IncidL B m\<close> betH_line
              inter_incid_uniquenessH by blast
          hence ?thesis 
            by (simp add: assms(1))
        }
        moreover have "IncidL AC m" 
          using betH_colH \<open>BetH A AC C\<close> \<open>IncidL A m\<close> \<open>IncidL C m\<close> betH_line 
            inter_incid_uniquenessH by blast
        ultimately show ?thesis
          using Is_line \<open>BetH AB AC BC\<close> local.cut_def by blast
      qed
      obtain p where "IncidP AB p" and "IncidP BC p" and "IncidP B p" 
        using \<open>\<not> ColH AB BC B\<close> plan_existence by blast
      have "(\<not> ColH AB BC B \<and> IncidP AB p \<and> IncidP BC p \<and> IncidP B p \<and> 
               IncidLP m p \<and> \<not> IncidL B m \<and> cut m AB BC) \<longrightarrow> (cut m AB B \<or> cut m BC B)" 
        using pasch Is_line Is_plane \<open>IncidL C m\<close> by blast
      moreover
      have "(\<not> ColH AB BC B \<and> IncidP AB p \<and> IncidP BC p \<and> IncidP B p \<and> 
               IncidLP m p \<and> \<not> IncidL B m \<and> cut m AB BC)"
      proof -
        have "IncidLP m p \<and> \<not> IncidL B m \<and> cut m AB BC" 
          by (metis (full_types) Hilbert_neutral_dimensionless.betH_colH 
              Hilbert_neutral_dimensionless_axioms Is_line Is_plane \<open>AB \<noteq> BC\<close> \<open>BetH A AC C\<close> 
              \<open>BetH B BC C\<close> \<open>ColH AB AC BC\<close> \<open>IncidL A m\<close> \<open>IncidL C m\<close> \<open>IncidP AB p\<close> 
              \<open>IncidP B p\<close> \<open>IncidP BC p\<close> \<open>\<not> IncidL B m\<close> \<open>local.cut m AB BC\<close> betH_line 
              colH_permut_132 inter_incid_uniquenessH line_on_plane line_on_plane')
        thus ?thesis 
          using \<open>IncidP AB p\<close> \<open>IncidP B p\<close> \<open>IncidP BC p\<close> \<open>\<not> ColH AB BC B\<close> by auto
      qed
      ultimately have "cut m AB B \<or> cut m BC B" by blast
      moreover
      {
        assume "cut m AB B"
        then obtain I where "IncidL I m" and "BetH AB I B" 
          using local.cut_def by blast
        hence "ColH AB I B" 
          using between_col by blast
        have "ColH A I C" 
          using ColH_def Is_line \<open>IncidL A m\<close> \<open>IncidL C m\<close> \<open>IncidL I m\<close> by blast
        {
          assume "A = I"
          hence "\<not> BetH A AB B" 
            using \<open>A = I\<close> \<open>BetH AB I B\<close> between_only_one' by blast
          hence False 
            using \<open>BetH A AB B\<close> by blast
        }
        hence "A \<noteq> I" 
          by blast
        have "ColH A I A" 
          using colH_trivial121 by fastforce
        have "ColH A I B" 
          by (meson \<open>BetH A AB B\<close> \<open>BetH AB I B\<close> betH_colH betH_trans0 between_comm)
        hence "ColH A B C" 
          using colH_trans \<open>A \<noteq> I\<close> \<open>ColH A I A\<close> \<open>ColH A I C\<close> by blast
        hence False 
          by (simp add: assms(1))
      }
      moreover
      {
        assume "cut m BC B"
        then obtain C' where "IncidL C' m" and "BetH BC C' B" 
          using local.cut_def by blast 
        have "ColH BC C' B" 
          by (simp add: \<open>BetH BC C' B\<close> betH_colH)
        have "B \<noteq> BC" 
          using \<open>IncidL BC l\<close> \<open>\<not> IncidL B l\<close> by auto
        have "ColH B BC B" 
          using colH_trivial121 by auto
        have "ColH B BC C'" 
          using \<open>ColH BC C' B\<close> colH_permut_312 by blast
        have "ColH B C C'" 
          using \<open>ColH B BC C\<close> \<open>B \<noteq> BC\<close> \<open>ColH B BC B\<close> \<open>ColH B BC C'\<close> 
            \<open>ColH B BC C\<close> colH_trans by blast
        have "C \<noteq> C'" 
          using \<open>BetH B BC C\<close> \<open>BetH BC C' B\<close> between_only_one by blast
        have "ColH A B C" 
          using ColH_def \<open>C \<noteq> C'\<close> \<open>ColH B C C'\<close> \<open>IncidL C m\<close> \<open>IncidL C' m\<close> 
            \<open>\<not> IncidL B m\<close> inter_incid_uniquenessH by auto
        hence False 
          by (simp add: assms(1))
      }
      ultimately have False 
        by blast
    }
    moreover
    {
      assume "BetH AC BC AB"
      obtain m where "IncidL C m" and "IncidL B m" 
        using \<open>BetH B BC C\<close> betH_line by blast
      have "\<not> ColH AB AC A" 
        using ColH_def \<open>AB \<noteq> AC\<close> \<open>IncidL AB l\<close> \<open>IncidL AC l\<close> 
          \<open>\<not> IncidL A l\<close> inter_incid_uniquenessH by blast
      have "\<not> IncidL A m" 
        using ColH_def Is_line \<open>IncidL B m\<close> \<open>IncidL C m\<close> assms(1) by blast
      have "\<not> IncidL AC m" 
        using betH_colH \<open>BetH A AC C\<close> \<open>IncidL C m\<close> \<open>\<not> IncidL A m\<close> 
          betH_line inter_incid_uniquenessH by blast
      have "\<not> IncidL AB m" 
        using betH_colH \<open>BetH A AB B\<close> \<open>IncidL B m\<close> \<open>\<not> IncidL A m\<close> 
          betH_line inter_incid_uniquenessH by blast
      have "IncidL BC m" 
        using betH_colH \<open>BetH B BC C\<close> \<open>IncidL B m\<close> \<open>IncidL C m\<close> 
          betH_line inter_incid_uniquenessH by blast
      hence "cut m AC AB" 
        using Is_line \<open>BetH AC BC AB\<close> \<open>IncidL BC m\<close> \<open>\<not> IncidL AB m\<close> 
          \<open>\<not> IncidL AC m\<close> local.cut_def by blast
      hence "cut m AB AC" 
        using cut_comm by blast
      obtain p where "IncidP AB p" and "IncidP AC p" and "IncidP A p" 
        using \<open>\<not> ColH AB AC A\<close> plan_existence by blast
      have "(\<not> ColH AB AC A \<and> IncidP AB p \<and> IncidP AC p \<and> IncidP A p \<and> 
               IncidLP m p \<and> \<not> IncidL A m \<and> cut m AB AC) \<longrightarrow> (cut m AB A \<or> cut m AC A)" 
        using Is_line Is_plane \<open>IncidL C m\<close> pasch by blast
      moreover
      have "\<not> ColH AB AC A \<and> IncidP AB p \<and> IncidP AC p \<and> IncidP A p \<and> 
              IncidLP m p \<and> \<not> IncidL A m \<and> cut m AB AC" 
      proof -
        have "\<not> ColH AB AC A \<and> IncidP AB p \<and> IncidP AC p \<and> IncidP A p" 
          by (simp add: \<open>IncidP A p\<close> \<open>IncidP AB p\<close> \<open>IncidP AC p\<close> \<open>\<not> ColH AB AC A\<close>)
        moreover have "IncidLP m p \<and> \<not> IncidL A m \<and> cut m AB AC" 
          by (metis (mono_tags, lifting) betH_colH line_on_plane Is_line Is_plane
              \<open>AB \<noteq> AC\<close> \<open>BetH A AC C\<close> \<open>BetH B BC C\<close> \<open>ColH AB AC BC\<close> \<open>IncidL BC m\<close> \<open>IncidL C m\<close>
              \<open>IncidP A p\<close> \<open>IncidP AB p\<close> \<open>IncidP AC p\<close> \<open>\<not> IncidL A m\<close> \<open>local.cut m AB AC\<close>
              line_on_plane')
        ultimately show ?thesis 
          by blast
      qed
      ultimately have "cut m AB A \<or> cut m AC A" 
        by blast
      moreover {
        assume "cut m AB A"
        obtain B' where "IncidL B' m" and "BetH AB B' A" 
          using \<open>local.cut m AB A\<close> local.cut_def by blast
        then have "ColH AB B' A" 
          using betH_colH by force
        have "ColH A B B'" 
          using betH_expand \<open>BetH A AB B\<close> \<open>ColH A AB A\<close> \<open>ColH AB B' A\<close> 
            colH_permut_312 colH_trans by blast
        hence False 
          using ColH_def \<open>BetH A AB B\<close> \<open>BetH AB B' A\<close> \<open>IncidL B m\<close> \<open>IncidL B' m\<close> 
            \<open>\<not> IncidL A m\<close> between_only_one inter_incid_uniquenessH by blast
      }
      moreover {
        assume "cut m AC A"
        then obtain I where "IncidL I m" and "BetH AC I A" 
          using local.cut_def by blast
        hence "ColH AC I A" 
          by (simp add: betH_colH)
        have "ColH C I A" 
          by (metis betH_colH \<open>BetH AC I A\<close> \<open>ColH A AC C\<close> colH_permut_312 
              colH_trans colH_trivial121)
        hence "ColH A B C" 
          using ColH_def \<open>BetH A AC C\<close> \<open>BetH AC I A\<close> \<open>IncidL C m\<close> \<open>IncidL I m\<close>
            \<open>\<not> IncidL A m\<close> between_only_one inter_incid_uniquenessH by blast
        hence False 
          using assms(1) by fastforce
      }
      ultimately have False 
        by blast
    }
    moreover
    {
      assume "BetH BC AB AC"
      obtain m where "IncidL A m" and "IncidL B m" 
        using \<open>BetH A AB B\<close> betH_line by blast
      have "\<not> ColH BC A C" 
        by (metis \<open>ColH B BC C\<close> \<open>IncidL BC l\<close> \<open>\<not> IncidL C l\<close> assms(1)
            colH_permut_213 colH_trans colH_trivial122)
      have "\<not> IncidL C m" 
        using ColH_def Is_line \<open>IncidL A m\<close> \<open>IncidL B m\<close> assms(1) by blast
      have "cut m BC AC" 
        by (metis (full_types) ncolH_distincts Is_line \<open>AB \<noteq> AC\<close> \<open>AB \<noteq> BC\<close> 
            \<open>BetH A AB B\<close> \<open>BetH BC AB AC\<close> \<open>IncidL A m\<close> \<open>IncidL AB l\<close> \<open>IncidL AC l\<close>
            \<open>IncidL B m\<close> \<open>\<not> IncidL B l\<close> assms(1) betH_line inter_incid_uniquenessH
            local.cut_def)
      have "\<not> IncidL AC m" 
        using \<open>local.cut m BC AC\<close> local.cut_def by blast
      obtain p where "IncidP BC p" and "IncidP AC p" and "IncidP C p" 
        by (metis (no_types, lifting) ncolH_distincts \<open>\<not> ColH BC A C\<close> 
            line_on_plane' plan_existence)
      have "(\<not> ColH BC AC C \<and> IncidP BC p \<and> IncidP AC p \<and> IncidP C p \<and> 
             IncidLP m p \<and> \<not> IncidL C m \<and> cut m BC AC) \<longrightarrow> (cut m BC C \<or> cut m AC C)" 
        using Is_line Is_plane \<open>IncidL B m\<close> pasch by blast
      moreover have "\<not> ColH BC AC C \<and> IncidP BC p \<and> IncidP AC p" 
        using ColH_def \<open>BC \<noteq> AC\<close> \<open>IncidL AC l\<close> \<open>IncidL BC l\<close> \<open>IncidP AC p\<close> 
          \<open>IncidP BC p\<close> \<open>\<not> IncidL C l\<close> inter_incid_uniquenessH by auto
      moreover have "IncidP C p \<and> IncidLP m p \<and> \<not> IncidL C m \<and> cut m BC AC" 
        by (metis ncolH_distincts Is_line Is_plane \<open>ColH A AC C\<close> \<open>ColH B BC C\<close> 
            \<open>IncidL A m\<close> \<open>IncidL B m\<close> \<open>IncidP C p\<close> \<open>\<not> IncidL C m\<close> \<open>local.cut m BC AC\<close> 
            assms(1) calculation(2) colH_permut_321 line_on_plane line_on_plane') 
      moreover have "\<not> cut m BC C" 
        by (meson \<open>BetH B BC C\<close> \<open>IncidL B m\<close> betH_trans0 between_comm local.cut_def
            outH_def out_same_side same_side_def)
      moreover have "\<not> cut m AC C" 
        by (meson \<open>BetH A AC C\<close> \<open>IncidL A m\<close> betH_trans0 between_comm local.cut_def
            outH_def out_same_side same_side_def)
      ultimately have False 
        by blast
    }
    ultimately
    have False 
      by blast
  }
  thus ?thesis 
    by blast
qed

lemma strong_pasch:
  assumes "\<not> ColH A B C" and
    "IncidP A p" and 
    "IncidP B p" and
    "IncidP C p" and
    "IncidLP l p" and
    "\<not> IncidL C l" and
    "cut l A B"
  shows "(cut l A C \<and> \<not> cut l B C) \<or> (cut l B C \<and> \<not> cut l A C)"
  by (meson cut2_not_cut IncidLP_def assms(1) assms(2) assms(3) assms(4) 
      assms(5) assms(6) assms(7) pasch)

lemma out2_out: 
  assumes "C \<noteq> D" and
    "BetH A B C" and
    "BetH A B D"
  shows "BetH B C D \<or> BetH B D C" 
proof -
  have "A \<noteq> B" 
    using assms(2) betH_distincts by blast
  have "ColH A B B" 
    by (simp add: colH_trivial122)
  have "ColH A B C" 
    by (simp add: assms(2) between_col)
  have "ColH A B D" 
    by (simp add: assms(3) betH_colH)
  hence "ColH B C D" 
    using colH_trans \<open>A \<noteq> B\<close> \<open>ColH A B B\<close> \<open>ColH A B C\<close> by blast
  {
    assume "BetH C D B"
    hence ?thesis 
      using between_comm by blast
  }
  moreover
  {
    assume "BetH C B D"
    have "ColH A C D" 
      using \<open>A \<noteq> B\<close> \<open>ColH A B C\<close> \<open>ColH A B D\<close> colH_trans colH_trivial121 by blast
    moreover have "BetH A C D \<longrightarrow> ?thesis" 
      using assms(2) betH_trans0 by blast
    moreover have "BetH C D A \<longrightarrow> ?thesis" 
      using assms(3) betH_trans0 between_comm by blast
    moreover have "BetH C A D \<longrightarrow> ?thesis" 
      using assms(2) assms(3) betH_trans0 between_comm between_only_one' by blast
    ultimately have ?thesis 
      by (metis assms(1) assms(2) assms(3) betH_colH between_one)
  }
  ultimately show ?thesis 
    by (metis \<open>ColH B C D\<close> assms(1) assms(2) assms(3) betH_distincts between_one)
qed

lemma out2_out1: 
  assumes "C \<noteq> D" and 
    "BetH A B C" and
    "BetH A B D" 
  shows "BetH A C D \<or> BetH A D C" 
  by (meson assms(1) assms(2) assms(3) betH_trans out2_out)

lemma betH2_out:
  assumes "B \<noteq> C" and
    "BetH A B D" and
    "BetH A C D"
  shows "BetH A B C \<or> BetH A C B" 
proof -
  have "A \<noteq> D" 
    using assms(2) between_diff by auto
  moreover have "ColH A D A" 
    by (simp add: colH_trivial121)
  moreover have "ColH A D B" 
    by (simp add: assms(2) betH_colH colH_permut_132)
  moreover have "ColH A D C" 
    using assms(3) betH_colH colH_permut_132 by blast
  ultimately have "ColH A B C" 
    using colH_trans by blast
  moreover have "BetH B C A \<longrightarrow> ?thesis" 
    using between_comm by blast
  moreover have "BetH C A B \<longrightarrow> ?thesis" 
    using assms(2) assms(3) betH_trans2 between_only_one' by blast
  ultimately show ?thesis 
    by (metis assms(1) assms(2) assms(3) betH_colH between_comm between_one)
qed

lemma segment_construction:
  shows "\<exists> E. Bet A B E \<and> Cong B E C D"
proof (cases "C = D")
  case True
  thus ?thesis
    using Bet_def Cong_def by force
next
  case False
  hence "C \<noteq> D"
    by blast
  {
    assume "A = B"
    hence ?thesis 
      by (metis Bet_def Cong_def betH_distincts cong_existence' line_existence)
  }
  moreover
  {
    assume "A \<noteq> B"
    obtain l where "IncidL A l" and "IncidL B l"
      using \<open>A \<noteq> B\<close> line_existence by auto
    obtain F where "\<exists> B'. IncidL F l \<and> IncidL B' l \<and> BetH F B B' \<and> CongH B F C D \<and> CongH B B' C D" 
      using False \<open>IncidL B l\<close> cong_existence' by presburger
    then obtain F' where "IncidL F l" and "IncidL F' l" and "BetH F B F'" and
      "CongH B F C D" and "CongH B F' C D"
      by blast
    hence "ColH A F F'" 
      using ColH_def Is_line \<open>IncidL A l\<close> by blast
    have "A = F \<longrightarrow> ?thesis" 
      by (metis Bet_def Cong_def \<open>BetH F B F'\<close> \<open>CongH B F' C D\<close> betH_distincts)
    moreover {
      assume "A \<noteq> F"
      have "A = F' \<longrightarrow> ?thesis" 
        by (metis Bet_def Cong_def \<open>BetH F B F'\<close> \<open>CongH B F C D\<close> betH_distincts between_comm)
      moreover
      {
        assume "A \<noteq> F'"
        have "ColH A F F'" 
          using \<open>ColH A F F'\<close> by blast
        have "BetH A F F' \<longrightarrow> ?thesis" 
          by (metis Cong_def False \<open>BetH F B F'\<close> \<open>CongH B F' C D\<close> betH_to_bet
              betH_trans0 between_comm)
        moreover have "BetH F F' A \<longrightarrow> ?thesis" 
          by (metis Bet_def Cong_def False \<open>BetH F B F'\<close> \<open>CongH B F C D\<close> 
              betH_distincts betH_trans0 between_comm)
        moreover have "BetH F' A F \<longrightarrow> ?thesis" 
          by (metis (full_types) Cong_def False \<open>A \<noteq> B\<close> \<open>BetH F B F'\<close> \<open>CongH B F C D\<close>
              \<open>CongH B F' C D\<close> betH2_out betH_to_bet between_comm between_only_one out2_out)
        ultimately have ?thesis 
          by (metis between_one \<open>A = F \<longrightarrow> (\<exists>E. Bet A B E \<and> Cong B E C D)\<close> 
              \<open>A = F' \<longrightarrow> (\<exists>E. Bet A B E \<and> Cong B E C D)\<close> \<open>BetH F B F'\<close> \<open>ColH A F F'\<close> 
              between_comm between_diff)
      }
      ultimately have  ?thesis 
        by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma lower_dim_e:
  shows "\<exists> A B C. \<not> (Bet A B C \<or> Bet B C A \<or> Bet C A B)" 
  by (meson bet_colH colH_permut_312 lower_dim_2)

lemma outH_dec:
  shows "outH A B C \<or> \<not> outH A B C" 
  by simp

lemma out_construction: 
  assumes "X \<noteq> Y" and
    "A \<noteq> B"
  shows "\<exists> C. CongH A C X Y \<and> outH A B C" 
  by (metis assms(1) assms(2) cong_existence line_existence)

lemma segment_constructionH:
  assumes "A \<noteq> B" and 
    "C \<noteq> D"
  shows "\<exists> E. BetH A B E \<and> CongH B E C D" 
  by (metis Bet_def Cong_def assms(1) assms(2) segment_construction)

lemma EqL_dec: 
  shows "EqL l m \<or> \<not> EqL l m" 
  by simp

lemma cut_exists: 
  assumes "IsL l" and (*ROLL ADD*)
    "\<not> IncidL A l"
  shows "\<exists> B. cut l A B" 
  using assms(1) assms(2) same_side_def same_side_refl by blast

lemma outH_col: 
  assumes "outH A B C"
  shows "ColH A B C" 
  by (simp add: assms outH_expand)

lemma cut_distinct: 
  assumes "cut l A B"
  shows "A \<noteq> B" 
  using assms local.cut_def not_betH121 by fastforce

lemma same_side_not_cut: 
  assumes "same_side A B l"
  shows "\<not> cut l A B"
proof -
  obtain P where "cut l A P" and "cut l B P" 
    using assms same_side_def by blast
  {
    assume "ColH P A B"
    {
      assume "cut l A B"
      obtain M where "IncidL M l" and "BetH A M P" 
        using \<open>local.cut l A P\<close> local.cut_def by blast
      obtain N where "IncidL N l" and "BetH B N P" 
        using \<open>local.cut l B P\<close> local.cut_def by blast
      {
        assume "M = N"
        hence "BetH M A B \<or> BetH M B A" 
          using \<open>BetH A M P\<close> \<open>BetH B N P\<close> \<open>local.cut l A B\<close> between_comm 
            cut_distinct out2_out by blast
        obtain Q where "IncidL Q l" and "BetH A Q B" 
          using \<open>local.cut l A B\<close> local.cut_def by blast
        obtain R where "IncidL R l" and "BetH A R B" 
          using \<open>BetH A Q B\<close> \<open>IncidL Q l\<close> by blast
        have "ColH A B M" 
          using \<open>BetH M A B \<or> BetH M B A\<close> betH_colH between_comm colH_permut_231 by blast
        obtain m where "IncidL A m" and "IncidL B m" 
          using \<open>BetH A Q B\<close> betH_line by blast
        obtain mm where "IncidL P mm" and "IncidL A mm" and "IncidL B mm" 
          using ColH_def \<open>ColH P A B\<close> by blast
        have "EqL m mm" 
          by (metis Is_line \<open>IncidL A m\<close> \<open>IncidL A mm\<close> \<open>IncidL B m\<close> \<open>IncidL B mm\<close> 
              \<open>\<And>thesis. (\<And>R. \<lbrakk>IncidL R l; BetH A R B\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
              betH_colH line_uniqueness)
        obtain nn where "IncidL A nn" and "IncidL R nn" and "IncidL B nn" 
          using \<open>BetH A R B\<close> betH_line by blast
        have "EqL m nn" 
          by (metis Is_line \<open>BetH A R B\<close> \<open>IncidL A m\<close> \<open>IncidL A nn\<close> \<open>IncidL B m\<close>
              \<open>IncidL B nn\<close> line_uniqueness not_betH121)
        obtain pp where "IncidL A pp" and "IncidL B pp" and "IncidL M pp" 
          using ColH_def \<open>ColH A B M\<close> by blast
        have "EqL m pp" 
          by (metis Is_line \<open>BetH M A B \<or> BetH M B A\<close> \<open>IncidL A m\<close> \<open>IncidL A pp\<close> 
              \<open>IncidL B m\<close> \<open>IncidL B pp\<close> betH_distincts line_uniqueness)
        have "R = M" 
          by (metis betH_colH \<open>IncidL A nn\<close> \<open>IncidL A pp\<close> \<open>IncidL B nn\<close> 
              \<open>IncidL B pp\<close> \<open>IncidL M l\<close> \<open>IncidL M pp\<close> \<open>IncidL R l\<close> \<open>IncidL R nn\<close> 
              \<open>local.cut l A B\<close> inter_incid_uniquenessH local.cut_def)
        have "BetH M A B \<longrightarrow> False" 
          using \<open>BetH A R B\<close> \<open>R = M\<close> between_only_one' by blast
        moreover have "BetH M B A \<longrightarrow> False" 
          using \<open>BetH A R B\<close> \<open>R = M\<close> between_only_one by blast
        ultimately have False 
          using \<open>BetH M A B \<or> BetH M B A\<close> by blast
      }
      hence "M \<noteq> N" 
        by blast
      have "A \<noteq> B" 
        using \<open>local.cut l A B\<close> cut_distinct by auto
      obtain T where "IncidL T l" and "BetH A T B" 
        using \<open>local.cut l A B\<close> local.cut_def by blast
      obtain m where "IncidL P m" and "IncidL A m" and "IncidL B m" 
        using ColH_def \<open>ColH P A B\<close> by blast
      obtain mm where "IncidL A mm" and "IncidL M mm" and "IncidL P mm"
        using \<open>BetH A M P\<close> betH_line by blast
      obtain nn where "IncidL B nn" and "IncidL N nn" and "IncidL P nn"
        using \<open>BetH B N P\<close> betH_line by blast
      have "M = N" using inter_incid_uniquenessH 
        by (metis Hilbert_neutral_dimensionless_pre.cut_def \<open>BetH B N P\<close> 
            \<open>IncidL A m\<close> \<open>IncidL A mm\<close> \<open>IncidL B m\<close> \<open>IncidL M l\<close> \<open>IncidL M mm\<close> 
            \<open>IncidL N l\<close> \<open>IncidL P m\<close> \<open>IncidL P mm\<close> 
            \<open>\<And>thesis. (\<And>nn. \<lbrakk>IncidL B nn; IncidL N nn; IncidL P nn\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
            \<open>local.cut l A P\<close> betH_expand)
      hence False 
        by (simp add: \<open>M \<noteq> N\<close>)
    }
    hence "\<not> cut l A B" 
      by blast
  }
  moreover
  {
    assume "\<not> ColH P A B"
    hence ?thesis 
      using \<open>local.cut l A P\<close> \<open>local.cut l B P\<close> cut2_not_cut cut_comm by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma IncidLP_morphism:
  assumes 
    "IsL m" and
    "IsP q" and
    "IncidLP l p" and
    "EqL l m" and
    "EqP p q"
  shows "IncidLP m q" 
proof -
  {
    fix A
    assume "IncidL A m"
    have "IncidP A q" 
      by (metis Hilbert_neutral_dimensionless_pre.IncidLP_def IncidP_morphism 
          \<open>IncidL A m\<close> assms(1) assms(2) assms(3) assms(4) assms(5) morph)
  }
  thus ?thesis 
    using IncidLP_def assms(1) assms(2) by blast
qed

lemma same_side__plane:
  assumes "same_side A B l" 
  shows "\<exists> p. IncidP A p \<and> IncidP B p \<and> IncidLP l p" 
proof -
  obtain P where "cut l A P" and "cut l B P" 
    using assms same_side_def by blast 
  then obtain X where "IncidL X l" and "BetH A X P" 
    using local.cut_def by blast
  {
    assume "ColH A B P"
    obtain Y where "X \<noteq> Y" and "IncidL Y l" 
      using \<open>IncidL X l\<close> other_point_on_line by blast
    {
      assume "ColH X Y A"
      obtain m where "IncidL X m" and "IncidL Y m" and "IncidL A m" 
        using ColH_def \<open>ColH X Y A\<close> by auto
      hence "X = Y" 
        using inter_incid_uniquenessH \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>local.cut l A P\<close> 
          local.cut_def by blast
      hence False 
        by (simp add: \<open>X \<noteq> Y\<close>)
    }
    hence "\<not> ColH X Y A" 
      by blast
    obtain p where "IncidP X p" and "IncidP Y p" and "IncidP A p" 
      using \<open>ColH X Y A \<Longrightarrow> False\<close> plan_existence by blast
    hence ?thesis 
      by (metis betH_colH Is_line Is_plane \<open>BetH A X P\<close> \<open>ColH A B P\<close> 
          \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>X \<noteq> Y\<close> colH_permut_132 line_on_plane line_on_plane')
  }
  moreover 
  {
    assume "\<not> ColH A B P"
    obtain p where "IncidP A p" and "IncidP B p" and "IncidP P p" 
      using \<open>\<not> ColH A B P\<close> plan_existence by blast
    obtain Y where "IncidL Y l" and "BetH B Y P" 
      using \<open>local.cut l B P\<close> local.cut_def by blast
    have "IncidP X p" 
      by (metis ncolH_distincts \<open>BetH A X P\<close> \<open>IncidP A p\<close> \<open>IncidP P p\<close> 
          \<open>\<not> ColH A B P\<close> between_col colH_permut_132 line_on_plane')
    moreover have "IncidP Y p" 
      using \<open>BetH B Y P\<close> \<open>IncidP B p\<close> \<open>IncidP P p\<close> betH_colH colH_permut_132 
        line_on_plane' by blast
    ultimately have "IncidLP l p" using line_on_plane 
      by (metis Is_line Is_plane \<open>BetH A X P\<close> \<open>BetH B Y P\<close> \<open>IncidL X l\<close> 
          \<open>IncidL Y l\<close> \<open>\<not> ColH A B P\<close> between_col between_comm colH_permut_231 
          colH_trivial112 out2_out1)
    hence ?thesis 
      using \<open>IncidP A p\<close> \<open>IncidP B p\<close> by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma same_side_prime__plane:
  assumes "same_side' A B C D"
  shows "\<exists> p. IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidP D p"
proof -
  obtain l where "IsL l" and "IncidL C l" and "IncidL D l" 
    by (metis line_existence lower_dim_2)
  obtain p where "IsP p" and "IncidP A p" and "IncidP B p" and "IncidLP l p" 
    by (meson Is_plane \<open>IncidL C l\<close> \<open>IncidL D l\<close> \<open>IsL l\<close> assms 
        same_side'_def same_side__plane)
  thus ?thesis 
    using IncidLP_def \<open>IncidL C l\<close> \<open>IncidL D l\<close> by blast
qed

lemma cut_same_side_cut:
  assumes "cut l P X" and
    "same_side X Y l"
  shows "cut l P Y" 
proof -
  have "\<not> cut l X Y" 
    by (simp add: assms(2) same_side_not_cut)
  have  "X = Y \<longrightarrow> ?thesis" 
    using assms(1) by fastforce
  moreover {
    assume "X \<noteq> Y"
    obtain A where "IncidL A l" and "BetH P A X" 
      using assms(1) local.cut_def by blast
    {
      assume "ColH P X Y"
      {
        assume "IncidL Y l"
        hence False 
          using \<open>IncidL Y l\<close> assms(2) local.cut_def same_side_def by force
      }
      hence "\<not> IncidL Y l" 
        by blast
      have "IncidL A l" 
        by (simp add: \<open>IncidL A l\<close>)
      moreover have "BetH P A Y" 
      proof -
        have "BetH P X Y \<longrightarrow> BetH P A Y" 
          using \<open>BetH P A X\<close> betH_trans0 by blast
        moreover have "BetH X Y P \<longrightarrow> BetH P A Y" 
          by (metis \<open>BetH P A X\<close> \<open>IncidL A l\<close> \<open>\<not> IncidL Y l\<close> \<open>\<not> local.cut l X Y\<close> 
              assms(1) betH2_out betH_trans0 between_comm local.cut_def)
        moreover have "BetH X P Y \<longrightarrow> BetH P A Y" 
          by (meson \<open>\<not> IncidL Y l\<close> \<open>\<not> local.cut l X Y\<close> assms(1) betH_trans0 
              between_comm local.cut_def)
        ultimately show ?thesis 
          by (metis betH_to_bet between_one cut_comm \<open>BetH P A X\<close> \<open>ColH P X Y\<close>
              \<open>\<not> local.cut l X Y\<close> assms(1))
      qed
      ultimately have ?thesis 
        using \<open>\<not> IncidL Y l\<close> assms(1) local.cut_def by blast
    }
    moreover
    {
      assume "\<not> ColH P X Y"
      {
        assume "IncidL Y l"
        obtain T where "cut l X T" and "cut l Y T" 
          using assms(2) same_side_def by blast
        hence False 
          using \<open>IncidL Y l\<close> local.cut_def by blast
      }
      hence "\<not> IncidL Y l" 
        by blast
      obtain p where "IncidP P p" and "IncidP X p" and "IncidP Y p" 
        using \<open>\<not> ColH P X Y\<close> plan_existence by blast
      have "cut l X Y \<or> cut l P Y" 
      proof -
        let ?A="X"
        let ?B="P"
        let ?C="Y"
        have "\<not> ColH ?A ?B ?C" 
          using \<open>\<not> ColH P X Y\<close> colH_permut_213 by blast
        moreover have "IsL l" 
          using assms(2) same_side_def by blast
        moreover have "IsP p" 
          using Is_plane \<open>IncidP P p\<close> by blast
        moreover have "IncidP ?A p" 
          by (simp add: \<open>IncidP X p\<close>)
        moreover have "IncidP ?B p" 
          using \<open>IncidP P p\<close> by auto
        moreover have "IncidP ?C p" 
          by (simp add: \<open>IncidP Y p\<close>)
        moreover have "IncidLP l p" 
        proof -
          {
            fix A'
            assume "IncidL A' l"
            have "ColH P A X" 
              by (simp add: \<open>BetH P A X\<close> between_col)

            obtain I where "IncidL I l" and "BetH P I X" 
              by (meson \<open>\<And>thesis. (\<And>A. \<lbrakk>IncidL A l; BetH P A X\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
            hence "ColH P I X" 
              using between_col by blast
            have "I = A' \<longrightarrow> IncidP A' p" 
              by (metis betH_colH \<open>BetH P I X\<close> calculation(4) calculation(5) 
                  colH_permut_132 line_on_plane')
            moreover 
            obtain p' where "IsP p'" and "IncidP X p'" and "IncidP Y p'" and "IncidLP l p'" 
              using Is_plane assms(2) same_side__plane by blast
            have "IncidP P p'" 
              using IncidLP_def \<open>BetH P A X\<close> \<open>ColH P A X\<close> \<open>IncidL A l\<close> 
                \<open>IncidLP l p'\<close> \<open>IncidP X p'\<close> betH_distincts colH_permut_231 
                line_on_plane' by blast
            have "IncidP A' p'" 
              using IncidLP_def \<open>IncidL A' l\<close> \<open>IncidLP l p'\<close> by blast
            have "IncidP A p'" 
              using IncidLP_def \<open>IncidL A l\<close> \<open>IncidLP l p'\<close> by blast
            have "EqP p p'" 
              by (meson plane_uniqueness \<open>IncidP P p'\<close> \<open>IncidP P p\<close> 
                  \<open>IncidP X p'\<close> \<open>IncidP X p\<close> \<open>IncidP Y p'\<close> \<open>IncidP Y p\<close> \<open>IsP p'\<close> 
                  \<open>IsP p\<close> \<open>\<not> ColH P X Y\<close>)
            hence "IncidP A' p" 
              by (meson EqP_sym IncidP_morphism \<open>IncidP A' p'\<close> \<open>IsP p'\<close> \<open>IsP p\<close>)
          }
          thus ?thesis 
            using IncidLP_def calculation(2) calculation(3) by blast
        qed
        moreover have "\<not> IncidL ?C l"
          by (simp add: \<open>\<not> IncidL Y l\<close>)
        moreover have "cut l ?A ?B" 
          by (simp add: assms(1) cut_comm)
        ultimately
        show ?thesis using pasch by blast
      qed
      have "IncidP A p" 
        using betH_colH \<open>BetH P A X\<close> \<open>IncidP P p\<close> \<open>IncidP X p\<close> colH_permut_132 
          line_on_plane' by blast
      obtain q where "IncidP X q" and "IncidP Y q" and "IncidLP l q" 
        using assms(2) same_side__plane by blast
      have "IncidP P q" 
        by (metis IncidLP_def \<open>IncidLP l q\<close> \<open>IncidP X q\<close> 
            \<open>\<And>thesis. (\<And>A. \<lbrakk>IncidL A l; BetH P A X\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> betH_colH 
            between_comm line_on_plane')
      have "EqP p q" 
        using Is_plane \<open>IncidP P p\<close> \<open>IncidP P q\<close> \<open>IncidP X p\<close> \<open>IncidP X q\<close> 
          \<open>IncidP Y p\<close> \<open>IncidP Y q\<close> \<open>\<not> ColH P X Y\<close> plane_uniqueness by presburger
      hence "IncidLP l p" 
        by (meson EqL_refl EqP_sym IncidLP_morphism Is_line Is_plane 
            \<open>IncidL A l\<close> \<open>IncidLP l q\<close> \<open>IncidP P p\<close>)
      have ?thesis 
        using \<open>\<not> local.cut l X Y\<close> \<open>local.cut l X Y \<or> local.cut l P Y\<close> by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis
    by blast
qed

(** Theorem 11 of Hilbert: the angles at the base of an isosceles triangle are congruent *)

lemma isosceles_congaH: 
  assumes "\<not> ColH A B C" and
    "CongH A B A C"
  shows "CongaH A B C A C B" 
  by (metis assms(1) assms(2) colH_permut_213 colH_permut_312 colH_trivial112 
      congH_sym cong_5 conga_comm)

lemma cong_distincts:
  assumes "A \<noteq> B" and
    "Cong A B C D"
  shows "C \<noteq> D" 
  using assms(1) assms(2) cong_identity by blast

lemma cong_sym:
  assumes "Cong A B C D"
  shows "Cong C D A B" 
  using Cong_def assms congH_sym by presburger

lemma cong_trans: 
  assumes "Cong A B C D" and
    "Cong C D E F"
  shows "Cong A B E F" 
  by (meson assms(1) assms(2) cong_inner_transitivity cong_sym)

lemma betH_not_congH:
  assumes "BetH A B C"
  shows "\<not> CongH A B A C" 
  by (metis assms betH_expand betH_trans between_comm between_out construction_uniqueness)

lemma congH_permlr: 
  assumes (*"A \<noteq> B" and*)
    "C \<noteq> D" and
    "CongH A B C D"
  shows "CongH B A D C" 
  by (metis assms(2) assms(1) congH_sym cong_permr)

lemma congH_perms:
  assumes "A \<noteq> B" and
    "C \<noteq> D" and
    "CongH A B C D"
  shows "CongH B A C D \<and> CongH A B D C \<and> CongH C D A B \<and>
CongH D C A B \<and> CongH C D B A \<and> CongH D C B A \<and> CongH B A D C" 
  using assms(1) assms(2) assms(3) congH_sym cong_permr by presburger

lemma congH_perml:
  assumes (*"A \<noteq> B" and*)
    "C \<noteq> D" and
    "CongH A B C D"
  shows "CongH B A C D" 
  by (metis assms(2) assms(1) congH_perms)

lemma bet_cong3_bet:
  assumes "A' \<noteq> B'" and
    "B' \<noteq> C'" and
    "A' \<noteq> C'" and
    "BetH A B C" and
    "ColH A' B' C'" and
    "CongH A B A' B'" and
    "CongH B C B' C'" and
    "CongH A C A' C'"
  shows "BetH A' B' C'" 
proof -
  {
    assume "BetH B' C' A'"
    obtain B'' where "BetH B C B''" and "CongH C B'' B C" 
      using assms(4) betH_to_bet segment_constructionH by blast
    have "BetH A B B'' \<and> BetH A C B''" 
      using betH_trans \<open>BetH B C B''\<close> assms(4) by blast
    hence "BetH A B B''" 
      by blast
    have "BetH A C B''" 
      using \<open>BetH A B B'' \<and> BetH A C B''\<close> by blast
    have "CongH A B'' A' B'"
    proof -
      have "ColH A C B''"       
        by (simp add: \<open>BetH A C B''\<close> between_col)
      moreover have "disjoint A C C B''"       
        by (simp add: \<open>BetH A C B''\<close> bet_disjoint)
      moreover have "disjoint A' C' C' B'"       
        by (simp add: \<open>BetH B' C' A'\<close> bet_disjoint between_comm)
      moreover have "CongH C B'' C' B'"       
        by (metis betH_to_bet congH_sym \<open>BetH B C B''\<close> \<open>CongH C B'' B C\<close> 
            assms(7) cong_permr cong_pseudo_transitivity)
      ultimately show ?thesis
        using addition assms(5) assms(8) colH_permut_132 by blast
    qed
    have "CongH A B'' A B" 
      by (metis \<open>BetH A B B'' \<and> BetH A C B''\<close> \<open>CongH A B'' A' B'\<close> assms(6) 
          betH_colH congH_sym cong_pseudo_transitivity)
    have "\<not> CongH A B A B''" 
      by (simp add: \<open>BetH A B B''\<close> betH_not_congH)
    have "CongH A B A B''" 
      using \<open>BetH A B B''\<close> \<open>CongH A B'' A B\<close> betH_to_bet congH_sym by blast
    hence False 
      by (simp add: \<open>\<not> CongH A B A B''\<close>)
    hence ?thesis 
      by blast
  }
  moreover 
  {
    assume "BetH C' A' B'"
    obtain B'' where "BetH C A B''" and "CongH A B'' A B" 
      by (metis assms(4) betH_expand segment_constructionH)
    have "CongH C B'' C' B'"
    proof -
      have "disjoint C A A B''"         
        using \<open>BetH C A B''\<close> bet_disjoint by force
      moreover have "disjoint C' A' A' B'"         
        by (simp add: \<open>BetH C' A' B'\<close> bet_disjoint)
      moreover have "CongH C A C' A'"         
        by (simp add: assms(3) assms(8) congH_permlr)
      moreover have "CongH A B'' A' B'"         
        by (metis \<open>BetH C A B''\<close> \<open>CongH A B'' A B\<close> assms(6) betH_distincts 
            congH_sym cong_pseudo_transitivity)
      ultimately show ?thesis
        using \<open>BetH C A B''\<close> \<open>BetH C' A' B'\<close> addition_betH by blast
    qed
    have "BetH B A B'' \<and> BetH C B B''" 
      using betH_trans0 \<open>BetH C A B''\<close> assms(4) between_comm by blast
    hence "BetH B A B''"  
      by blast
    have "BetH C B B''" 
      using \<open>BetH B A B'' \<and> BetH C B B''\<close> by auto
    have "\<not> CongH C B C B''" 
      by (simp add: \<open>BetH C B B''\<close> betH_not_congH)
    hence ?thesis 
      by (metis betH_colH \<open>BetH C B B''\<close> \<open>CongH C B'' C' B'\<close> assms(2) 
          assms(7) congH_perms cong_pseudo_transitivity)
  }
  ultimately show ?thesis 
    using assms(1) assms(2) assms(3) assms(5) between_comm between_one by blast
qed

lemma betH_congH3_outH_betH:
  assumes "BetH A B C" and
    "outH A' B' C'" and
    "CongH A C A' C'" and
    "CongH A B A' B'"
  shows "BetH A' B' C'" 
proof -
  {
    assume "BetH A' C' B'"
    obtain C'' where "BetH A' B' C''" and "CongH B' C'' B C" 
      using \<open>BetH A' C' B'\<close> assms(1) betH_distincts segment_constructionH by blast
    hence "CongH A' C'' A C" 
      using addition_betH assms(1) assms(4) betH_distincts congH_sym by presburger
    have "BetH C' B' C'' \<and> BetH A' C' C''" 
      using \<open>BetH A' B' C''\<close> \<open>BetH A' C' B'\<close> betH_trans0 by blast
    hence "\<not> CongH A' C' A' C''" 
      by (simp add: betH_not_congH)
    moreover
    have "CongH A' C' A' C''" 
      by (metis betH_colH congH_sym \<open>BetH A' B' C''\<close> \<open>CongH A' C'' A C\<close> 
          assms(3) cong_pseudo_transitivity)
    ultimately have ?thesis 
      by simp
  }
  moreover have "(A' \<noteq> B' \<and> B' \<noteq> C') \<longrightarrow> ?thesis" 
    using assms(2) calculation outH_def by auto
  ultimately show ?thesis 
    by (metis betH_distincts assms(1) assms(2) assms(3) assms(4) betH_not_congH 
        congH_sym cong_pseudo_transitivity outH_def)
qed

lemma outH_sym:
  assumes "A \<noteq> C" and
    "outH A B C"
  shows "outH A C B" 
  using assms(2) outH_def by fastforce

lemma soustraction_betH:
  assumes "BetH A B C" and
    "BetH A' B' C'" and
    "CongH A B A' B'" and
    "CongH A C A' C'"
  shows "CongH B C B' C'" 
proof -
  obtain C1 where "BetH A' B' C1" and "CongH B' C1 B C" 
    using assms(1) assms(2) betH_to_bet segment_constructionH by blast
  hence "CongH A C A' C1" 
    using addition_betH assms(1) assms(3) betH_distincts congH_sym by presburger
  obtain X where "BetH B A X" 
    by (metis assms(1) between_out)
  obtain X' where "BetH B' A' X'" 
    by (metis assms(2) between_out)
  have "BetH X A C" 
    using \<open>BetH B A X\<close> assms(1) betH_trans between_comm by blast
  have "BetH X' A' C1" 
    using \<open>BetH A' B' C1\<close> \<open>BetH B' A' X'\<close> betH_trans between_comm by blast
  have "C' = C1" 
    by (meson \<open>BetH A' B' C1\<close> \<open>CongH A C A' C1\<close> assms(2) assms(4) 
        betH_not_congH cong_pseudo_transitivity out2_out1)
  thus ?thesis 
    using \<open>BetH A' B' C1\<close> \<open>CongH B' C1 B C\<close> betH_colH congH_sym by blast
qed

lemma ncolH_expand:
  assumes "\<not> ColH A B C" 
  shows "\<not> ColH A B C \<and> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" 
  using assms colH_trivial112 colH_trivial121 colH_trivial122 by blast

lemma betH_outH__outH:
  assumes "BetH A B C" and
    "outH B C D"
  shows "outH A C D" 
  by (metis betH_expand betH_outH2__betH betH_trans1 
      Hilbert_neutral_dimensionless_pre.outH_def assms(1) assms(2))

(** First case of congruence of triangles *)

lemma th12:
  assumes "\<not> ColH A B C" and
    "\<not> ColH A' B' C'" and
    "CongH A B A' B'" and
    "CongH A C A' C'" and
    "CongaH B A C B' A' C'"
  shows "CongaH A B C A' B' C' \<and> CongaH A C B A' C' B' \<and> CongH B C B' C'" 
proof (intro conjI)
  show "CongaH A B C A' B' C'" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) cong_5)
  show "CongaH A C B A' C' B'" 
    by (meson assms(1) assms(2) assms(3) assms(4) assms(5) colH_permut_132 
        cong_5 conga_permlr)
  obtain D' where "CongH B' D' B C" and "outH B' C' D'" 
    by (metis assms(1) assms(2) colH_trivial122 out_construction)
  show "CongH B C B' C'" 
  proof (cases "B' = D'")
    case True
    thus ?thesis 
      using \<open>outH B' C' D'\<close> outH_expand by blast
  next
    case False
    hence "B' \<noteq> D'"
      by simp
    have "\<not> ColH B A C" 
      using assms(1) colH_permut_213 by blast
    moreover have "\<not> ColH B' A' D'" 
      using ColH_def \<open>outH B' C' D'\<close> assms(2) inter_incid_uniquenessH 
        outH_expand by fastforce
    moreover have "CongH B A B' A'" 
      by (metis assms(3) calculation(2) congH_permlr ncolH_distincts)
    moreover have "CongH B C B' D'" 
      by (simp add: False \<open>CongH B' D' B C\<close> congH_sym)
    moreover have "CongaH A B C A' B' D'" 
      using \<open>CongaH A B C A' B' C'\<close> \<open>outH B' C' D'\<close> calculation(1) calculation(2) 
        conga_out_conga ncolH_expand outH_trivial by blast
    ultimately have "CongaH B A C B' A' D'" 
      using cong_5 by blast
    have "\<not> ColH C' A' B'" 
      using assms(2) colH_permut_231 by blast
    moreover have "\<not> ColH B A C" 
      using \<open>\<not> ColH B A C\<close> by blast
    moreover have "same_side' C' C' A' B'" 
      using assms(2) same_side_prime_refl by blast
    moreover have "same_side' C' D' A' B'" 
      by (metis (no_types, lifting) ColH_def ncolH_distincts \<open>outH B' C' D'\<close>
          assms(2) out_same_side same_side'_def)
    ultimately have "outH A' C' D'" 
      using \<open>CongaH B A C B' A' D'\<close> assms(5) cong_4_uniqueness by presburger
    have "C' = D'" 
      by (metis (full_types) colH_trivial121 outH_expand \<open>\<not> ColH C' A' B'\<close> 
          \<open>outH A' C' D'\<close> \<open>outH B' C' D'\<close> colH_permut_213 inter_uniquenessH)
    thus ?thesis 
      by (simp add: \<open>CongH B C B' D'\<close>)
  qed
qed

lemma th14:
  assumes "\<not> ColH A B C" and
    "\<not> ColH A' B' C'" and
    "CongaH A B C A' B' C'" and
    "BetH A B D" and
    "BetH A' B' D'"
  shows "CongaH C B D C' B' D'" 
proof -
  obtain A'' where "CongH B' A'' A B" and "outH B' A' A''" 
    by (metis assms(4) assms(5) betH_distincts out_construction)
  obtain C'' where "CongH B' C'' B C" and "outH B' C' C''" 
    by (metis assms(1) assms(2) colH_trivial122 out_construction)
  obtain D'' where "CongH B' D'' B D" and "outH B' D' D''" 
    using assms(4) assms(5) betH_expand out_construction by blast
  have "CongaH B A C B' A'' C'' \<and> CongaH B C A B' C'' A'' \<and> CongH A C A'' C''" 
  proof (rule th12)
    show "\<not> ColH B A C" 
      using assms(1) colH_permut_213 by blast
    show "\<not> ColH B' A'' C''" 
      by (metis (mono_tags, opaque_lifting) \<open>outH B' A' A''\<close> \<open>outH B' C' C''\<close> 
          assms(2) colH_trans colH_trivial121 colH_trivial122 outH_expand)
    show "CongH B A B' A''" 
      by (metis \<open>CongH B' A'' A B\<close> \<open>outH B' A' A''\<close> congH_perms congH_sym out_distinct)
    show "CongH B C B' C''" 
      using \<open>CongH B' C'' B C\<close> \<open>outH B' C' C''\<close> congH_sym out_distinct by presburger
    show "CongaH A B C A'' B' C''" 
      using \<open>\<not> ColH B A C\<close> \<open>outH B' A' A''\<close> \<open>outH B' C' C''\<close> assms(3) 
        conga_out_conga ncolH_distincts outH_trivial by blast
  qed
  have "BetH A'' B' D''" 
    using \<open>outH B' A' A''\<close> \<open>outH B' D' D''\<close> assms(5) betH_outH2__betH by blast
  have "CongH A D A'' D''" 
    by (metis (full_types) \<open>BetH A'' B' D''\<close> \<open>CongH B' A'' A B\<close> 
        \<open>CongH B' D'' B D\<close> addition_betH assms(1) assms(4) colH_trivial112 
        congH_perml congH_sym not_betH121)
  {
    assume "ColH A C D"
    have "A \<noteq> D" 
      using between_diff assms(4) by blast
    moreover have "ColH A D A" 
      by (simp add: colH_trivial121)
    moreover have "ColH A D B" 
      by (simp add: assms(4) between_col colH_permut_132)
    moreover have "ColH A D C" 
      by (simp add: \<open>ColH A C D\<close> colH_permut_132)
    hence False 
      using assms(1) calculation(1) calculation(2) calculation(3) colH_trans by blast
  }
  hence "\<not> ColH A C D" 
    by blast
  {
    assume "ColH A'' C'' D''"
    have "ColH B' A' A'' \<and> B' \<noteq> A'' \<and> B' \<noteq> A'" 
      using \<open>outH B' A' A''\<close> outH_expand by blast 
    hence "ColH B' A' A''" 
      by simp
    moreover have "B' \<noteq> A''" 
      using \<open>ColH B' A' A'' \<and> B' \<noteq> A'' \<and> B' \<noteq> A'\<close> by blast
    moreover have "B' \<noteq> A'"
      by (simp add: \<open>ColH B' A' A'' \<and> B' \<noteq> A'' \<and> B' \<noteq> A'\<close>) 
    moreover have "ColH B' C' C'' \<and> B' \<noteq> C'' \<and> B' \<noteq> C'"
      using \<open>outH B' C' C''\<close> outH_expand by presburger
    hence "ColH B' C' C''" 
      by simp
    moreover have "B' \<noteq> C''" 
      using \<open>ColH B' C' C'' \<and> B' \<noteq> C'' \<and> B' \<noteq> C'\<close> by blast
    have "B' \<noteq> C'" 
      using \<open>ColH B' C' C'' \<and> B' \<noteq> C'' \<and> B' \<noteq> C'\<close> by blast
    moreover have "ColH B' D' D'' \<and> B' \<noteq> D'' \<and> B' \<noteq> D'" 
      using \<open>outH B' D' D''\<close> outH_expand by blast
    hence "ColH B' D' D''" 
      by simp
    moreover have "B' \<noteq> D''" 
      by (simp add: \<open>ColH B' D' D'' \<and> B' \<noteq> D'' \<and> B' \<noteq> D'\<close>)
    moreover have "B' \<noteq> D'" 
      using \<open>ColH B' D' D'' \<and> B' \<noteq> D'' \<and> B' \<noteq> D'\<close> by blast
    ultimately have "ColH A'' B' D''" 
      using \<open>BetH A'' B' D''\<close> between_col by blast
    hence "ColH A'' D'' B'" 
      using colH_permut_132 by blast
    have "A'' \<noteq> B'" 
      using \<open>B' \<noteq> A''\<close> by blast
    have "ColH A'' B' A'" 
      by (simp add: \<open>ColH B' A' A''\<close> colH_permut_312)
    have "ColH A'' B' B'" 
      by (simp add: colH_trivial122)
    have "A'' \<noteq> D''" 
      using \<open>BetH A'' B' D''\<close> not_betH121 by auto
    have "ColH A'' D'' A'" 
      using \<open>A'' \<noteq> B'\<close> \<open>ColH A'' B' A'\<close> \<open>ColH A'' B' D''\<close> 
        colH_trans colH_trivial121 by presburger
    moreover have "ColH A'' D'' B'" 
      by (simp add: \<open>ColH A'' D'' B'\<close>)
    moreover have "ColH A'' D'' C'"
    proof -
      have "ColH A'' C' D''" 
        by (metis \<open>ColH A'' C'' D''\<close> \<open>ColH B' C' C'' \<and> B' \<noteq> C'' \<and> B' \<noteq> C'\<close> calculation(2) 
            colH_permut_213 colH_trans colH_trivial121)
      thus ?thesis
        using colH_permut_132 by blast
    qed
    ultimately have "ColH A' B' C'" 
      using \<open>A'' \<noteq> D''\<close> colH_trans by blast
    hence False 
      by (simp add: assms(2))
  }
  have "CongaH A C D A'' C'' D'' \<and> CongaH A D C A'' D'' C'' \<and> CongH C D C'' D''"
  proof (rule th12)
    show "\<not> ColH A C D" 
      using \<open>ColH A C D \<Longrightarrow> False\<close> by auto
    show "\<not> ColH A'' C'' D''" 
      using \<open>ColH A'' C'' D'' \<Longrightarrow> False\<close> by auto
    show "CongH A C A'' C''" 
      using \<open>CongaH B A C B' A'' C'' \<and> CongaH B C A B' C'' A'' \<and> CongH A C A'' C''\<close> by blast
    show "CongH A D A'' D''" 
      by (simp add: \<open>CongH A D A'' D''\<close>)
    have "CongaH C A B C'' A'' B'" 
      using \<open>CongaH B A C B' A'' C'' \<and> CongaH B C A B' C'' A'' \<and> CongH A C A'' C''\<close> 
        conga_permlr by presburger
    moreover have "outH A C C" 
      by (metis assms(1) colH_trivial121 outH_trivial)
    moreover have "outH A'' C'' C''" 
      by (metis \<open>\<not> ColH A'' C'' D''\<close> colH_trivial112 outH_trivial)
    moreover have "outH A B D" 
      by (simp add: assms(4) outH_def)
    moreover have "outH A'' B' D''" 
      using \<open>BetH A'' B' D''\<close> outH_def by auto
    ultimately show "CongaH C A D C'' A'' D''" 
      using conga_out_conga by blast
  qed
  have "\<not> ColH D B C" 
    using assms(1) assms(4) betH_colH between_comm colH_trans colH_trivial122 by blast
  moreover have "\<not> ColH D'' B' C''" 
    using \<open>BetH A'' B' D''\<close> \<open>ColH A'' C'' D'' \<Longrightarrow> False\<close> betH_colH between_comm 
      colH_trans colH_trivial121 by blast
  moreover have "CongH D B D'' B'" 
    by (metis betH_distincts outH_expand \<open>CongH B' D'' B D\<close> 
        \<open>outH B' D' D''\<close> assms(4) congH_perms)
  moreover have "CongH D C D'' C''" 
    by (metis \<open>CongaH A C D A'' C'' D'' \<and> CongaH A D C A'' D'' C'' \<and> CongH C D C'' D''\<close> 
        calculation(2) colH_trivial121 congH_permlr)
  moreover have "CongaH B D C B' D'' C''"
  proof -
    have "CongaH A D C A'' D'' C''" 
      using \<open>CongaH A C D A'' C'' D'' \<and> CongaH A D C A'' D'' C'' \<and> CongH C D C'' D''\<close> by auto
    moreover have "outH D A B" 
      using assms(4) between_comm outH_def by blast
    moreover have "outH D C C" 
      by (metis \<open>\<not> ColH D B C\<close> colH_trivial121 outH_trivial)
    moreover have "outH D'' A'' B'" 
      using between_comm \<open>BetH A'' B' D''\<close> outH_def by blast
    moreover have "outH D'' C'' C''" 
      by (metis \<open>\<not> ColH D'' B' C''\<close> colH_trivial121 outH_trivial)
    ultimately show ?thesis
      using conga_out_conga by blast
  qed
  ultimately have "CongaH D B C D'' B' C''" 
    using th12 by blast
  have "CongaH D B C D' B' C'"
  proof -
    have "outH B D D" 
      using assms(4) betH_distincts outH_trivial by blast
    moreover have "outH B C C" 
      by (metis \<open>\<not> ColH A C D\<close> assms(4) between_col outH_trivial)
    moreover have "outH B' D'' D'" 
      using \<open>BetH A'' B' D''\<close> \<open>outH B' D' D''\<close> betH_distincts outH_sym by presburger
    moreover have "outH B' C'' C'" 
      using \<open>outH B' C' C''\<close> outH_sym out_distinct by blast
    ultimately show ?thesis 
      using \<open>CongaH D B C D'' B' C''\<close> conga_out_conga by blast
  qed
  thus ?thesis 
    using conga_permlr by blast
qed

lemma congH_colH_betH:
  assumes "A \<noteq> B" and
    "A \<noteq> I" and
    "B \<noteq> I" and
    "CongH I A I B" and
    "ColH I A B"
  shows "BetH A I B"
proof -
  have "BetH I A B \<longrightarrow> ?thesis" 
    using assms(4) betH_not_congH by blast
  moreover have "BetH A B I \<longrightarrow> ?thesis" 
    by (metis assms(2) assms(4) betH_not_congH between_comm congH_sym)
  ultimately show ?thesis
    by (metis assms(1) assms(2) assms(3) assms(5) between_one)
qed

lemma plane_separation:
  assumes "\<not> ColH A X Y" and
    "\<not> ColH B X Y" and
    "IncidP A p" and
    "IncidP B p" and 
    "IncidP X p" and 
    "IncidP Y p"
  shows "cut' A B X Y \<or> same_side' A B X Y" 
proof -
  obtain l where "IsL l" and "IncidL X l" and "IncidL Y l" 
    using ColH_def colH_trivial122 by blast
  obtain C where "cut l A C" 
    using ColH_def \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(1) cut_exists by blast
  have "A = B \<longrightarrow> ?thesis" 
    using assms(2) colH_permut_312 same_side_prime_refl by blast
  moreover {
    assume "A \<noteq> B" 
    have "A \<noteq> C" 
      using \<open>local.cut l A C\<close> cut_distinct by auto
    {
      assume "B = C"
      obtain m where "IncidL X m \<and> IncidL Y m" 
        using \<open>IncidL X l\<close> \<open>IncidL Y l\<close> by auto
      obtain I where "IncidL I l" and "BetH A I C"
        using \<open>local.cut l A C\<close> local.cut_def by blast
      have "\<not> IncidL A l" 
        using \<open>local.cut l A C\<close> local.cut_def by auto
      have "\<not> IncidL C l" 
        using \<open>local.cut l A C\<close> local.cut_def by blast
      have "cut l A C" 
        by (simp add: \<open>local.cut l A C\<close>)
      hence "cut l A B" 
        by (simp add: \<open>B = C\<close>)
      have "X \<noteq> Y" 
        using assms(1) colH_trivial122 by blast
      moreover
      {
        fix k
        assume "IsL k" and "IncidL X k" and "IncidL Y k"
        hence "cut k A B"  
          by (metis inter_incid_uniquenessH \<open>B = C\<close> \<open>BetH A I C\<close> \<open>IncidL I l\<close>
              \<open>IncidL X k\<close> \<open>IncidL X l\<close> \<open>IncidL Y k\<close> \<open>IncidL Y l\<close> \<open>IsL k\<close> \<open>\<not> IncidL A l\<close>
              \<open>\<not> IncidL C l\<close> calculation local.cut_def)
      }
      ultimately have "cut' A B X Y"
        using cut'_def by presburger
      hence ?thesis
        by blast
    }
    moreover 
    {
      assume "B \<noteq> C"
      hence ?thesis 
      proof (cases "ColH A C B")
        case True
        hence "ColH A C B" 
          by simp
        obtain I where "IncidL I l" and "BetH A I C" 
          using \<open>local.cut l A C\<close> local.cut_def by blast
        hence "ColH A I C" 
          using between_col by blast
        have "ColH A I B" 
          by (meson True \<open>A \<noteq> C\<close> \<open>ColH A I C\<close> colH_permut_132 colH_trans colH_trivial121)
        have "\<not> IncidL A l" 
          using \<open>local.cut l A C\<close> local.cut_def by auto
        {
          assume "BetH A I B"
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m"
            hence "EqL m l" 
              by (metis \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(2) 
                  colH_trivial122 line_uniqueness)
            hence "cut m A B" 
              using ColH_def \<open>BetH A I B\<close> \<open>IncidL I l\<close> \<open>IncidL X m\<close> \<open>IncidL Y m\<close> 
                \<open>IsL l\<close> \<open>IsL m\<close> \<open>\<not> IncidL A l\<close> assms(2) local.cut_def morph by auto
          }
          hence  "cut' A B X Y" 
            using assms(1) colH_trivial122 cut'_def by auto
          hence ?thesis
            by blast
        }
        moreover {
          assume "BetH I B A"
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m"
            hence "EqL m l" 
              by (metis \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(2) 
                  colH_trivial122 line_uniqueness)
            hence "same_side A B m" 
              by (metis inter_incid_uniquenessH ncolH_distincts out_same_side 
                  outH_def \<open>BetH I B A\<close> \<open>IncidL I l\<close> \<open>IncidL X l\<close> \<open>IncidL X m\<close> \<open>IncidL Y l\<close>
                  \<open>IncidL Y m\<close> \<open>\<not> IncidL A l\<close> assms(2))
          }
          hence "same_side' A B X Y" 
            using assms(1) colH_trivial122 same_side'_def by auto
          hence ?thesis
            by blast
        }
        moreover {
          assume "BetH I A B"
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m"
            hence "EqL m l" 
              by (metis \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(2) 
                  colH_trivial122 line_uniqueness)
            hence "same_side A B m" 
              by (metis inter_incid_uniquenessH ncolH_expand out_same_side 
                  outH_def \<open>BetH I A B\<close> \<open>IncidL I l\<close> \<open>IncidL X l\<close> \<open>IncidL X m\<close> \<open>IncidL Y l\<close>
                  \<open>IncidL Y m\<close> \<open>\<not> IncidL A l\<close> assms(2))
          }
          hence "same_side' A B X Y" 
            using assms(1) colH_trivial122 same_side'_def by auto
          hence ?thesis
            by blast
        }
        ultimately show ?thesis 
          by (metis ColH_def Is_line \<open>A \<noteq> B\<close> \<open>BetH A I C\<close> \<open>ColH A I B\<close>
              \<open>IncidL I l\<close> \<open>IncidL X l\<close> \<open>IncidL Y l\<close> assms(2) betH_colH between_one)
      next
        case False
        have "IncidLP l p" 
          using ncolH_expand Is_plane \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close>
            assms(2) assms(5) assms(6) line_on_plane by blast
        obtain I where "IncidL I l" and "BetH A I C" 
          using \<open>local.cut l A C\<close> local.cut_def by blast
        hence "ColH A I C" 
          by (simp add: between_col)
        hence "IncidP I p" 
          using IncidLP_def \<open>IncidL I l\<close> \<open>IncidLP l p\<close> by blast
        hence "IncidP C p" 
          using \<open>BetH A I C\<close> \<open>ColH A I C\<close> assms(3) betH_distincts line_on_plane' by blast
        {
          assume "cut l A B"
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m"
            hence "EqL m l" 
              by (metis \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(2) 
                  colH_trivial122 line_uniqueness)
            hence "cut m A B" 
              by (meson \<open>IsL m\<close> \<open>local.cut l A B\<close> local.cut_def morph)
          }
          hence ?thesis 
            using assms(1) colH_trivial122 cut'_def by force
        }
        moreover
        {
          assume "cut l C B"
          have "X \<noteq> Y" 
            using assms(1) colH_trivial122 by blast
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m"
            hence "EqL m l" 
              by (metis \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(2) 
                  colH_trivial122 line_uniqueness)
            have "cut m A C" 
              by (meson \<open>EqL m l\<close> \<open>IsL m\<close> \<open>local.cut l A C\<close> local.cut_def morph)
            moreover have "cut m B C" 
              by (metis \<open>EqL m l\<close> \<open>local.cut l C B\<close> calculation cut_comm local.cut_def morph)
            ultimately have "same_side A B m" 
              using \<open>IsL m\<close> same_side_def by blast
          }
          hence "same_side' A B X Y" 
            using assms(1) colH_trivial122 same_side'_def by auto
          hence ?thesis 
            by blast
        }
        moreover 
        have "\<not> IncidL B l" 
          using ColH_def \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(2) by blast
        ultimately show ?thesis 
          using pasch False \<open>IncidLP l p\<close> \<open>IncidP C p\<close> \<open>local.cut l A C\<close> 
            assms(3) assms(4) strong_pasch by blast
      qed
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma same_side_comm:
  assumes "same_side A B l"
  shows "same_side B A l" 
  using assms same_side_def by blast

lemma same_side_not_incid:
  assumes "same_side A B l" 
  shows "\<not> IncidL A l \<and> \<not> IncidL B l" 
  using assms local.cut_def same_side_def by auto

lemma out_same_side':
  assumes "X \<noteq> Y" and
    "IncidL X l" and 
    "IncidL Y l" and
    "IncidL A l" and
    "\<not> IncidL B l" and
    "outH A B C"
  shows "same_side' B C X Y"
proof -
  have "same_side B C l" 
    using assms(4) assms(5) assms(6) out_same_side by blast
  {
    fix m
    assume "IsL m" and
      "IncidL X m" and
      "IncidL Y m"
    hence "EqL m l" 
      using Is_line assms(1) assms(2) assms(3) line_uniqueness by presburger
    hence "same_side B C m" 
      by (meson Is_line \<open>IsL m\<close> assms(4) assms(5) assms(6) morph out_same_side)
  }
  thus ?thesis
    by (simp add: assms(1) same_side'_def)
qed

lemma same_side_trans:
  assumes "same_side A B l" and
    "same_side B C l"
  shows "same_side A C l" 
  by (meson assms(1) assms(2) cut_comm cut_same_side_cut same_side_def)

lemma colH_IncidL__IncidL:
  assumes "A \<noteq> B" and
    "IncidL A l" and
    "IncidL B l" and
    "ColH A B C" 
  shows "IncidL C l" 
  using ColH_def assms(1) assms(2) assms(3) assms(4) inter_incid_uniquenessH by blast

lemma IncidL_not_IncidL__not_colH:
  assumes "A \<noteq> B" and
    "IncidL A l" and
    "IncidL B l" and
    "\<not> IncidL C l"
  shows "\<not> ColH A B C" 
  using assms(1) assms(2) assms(3) assms(4) colH_IncidL__IncidL by blast

lemma same_side_prime_not_colH:
  assumes "same_side' A B C D" 
  shows "\<not> ColH A C D \<and> \<not> ColH B C D" 
proof -
  {
    fix l 
    assume "IncidL C l" and
      "IncidL D l"
    have "same_side A B l" 
      using Is_line \<open>IncidL C l\<close> \<open>IncidL D l\<close> assms same_side'_def by auto
    hence ?thesis 
      by (meson ColH_def assms same_side'_def same_side_not_incid)
  }
  thus ?thesis 
    by (metis assms line_existence same_side'_def)
qed

lemma OS2__TS:
  assumes "same_side' Y Z PO X" and
    "same_side' X Y PO Z"
  shows "cut' X Z PO Y" 
proof -
  obtain Z' where "BetH Z PO Z'" 
    using assms(2) between_out same_side'_def by force
  have "PO \<noteq> X" 
    using assms(1) same_side'_def by blast
  have "PO \<noteq> Z" 
    using assms(2) same_side'_def by force
  {
    fix l 
    assume "IsL l" and
      "IncidL PO l" and
      "IncidL X l"
    have "\<not> IncidL Y l" 
      using ColH_def \<open>IncidL PO l\<close> \<open>IncidL X l\<close> \<open>IsL l\<close> assms(1) 
        same_side_prime_not_colH by blast
    moreover have "\<not> IncidL Z l" 
      using ColH_def \<open>IncidL PO l\<close> \<open>IncidL X l\<close> \<open>IsL l\<close> assms(1) 
        same_side_prime_not_colH by blast
    ultimately have "cut l Z' Z" 
      by (metis IncidL_not_IncidL__not_colH Is_line \<open>BetH Z PO Z'\<close> \<open>IncidL PO l\<close> 
          betH_distincts between_col between_comm local.cut_def)
    hence "cut l Y Z'" 
      by (meson \<open>IncidL PO l\<close> \<open>IncidL X l\<close> \<open>IsL l\<close> assms(1) cut_comm 
          cut_same_side_cut same_side'_def same_side_comm)
  }
  hence "cut' Y Z' PO X" 
    using \<open>PO \<noteq> X\<close> cut'_def by auto
  {
    fix l
    assume "IsL l" and
      "IncidL PO l" and
      "IncidL Y l"
    have "\<not> ColH Y PO Z" 
      using assms(2) same_side_prime_not_colH by blast
    have "PO \<noteq> Y" 
      using \<open>\<not> ColH Y PO Z\<close> colH_trivial112 by auto
    have "PO \<noteq> Z'" 
      using \<open>BetH Z PO Z'\<close> betH_distincts by auto
    have "Z \<noteq> Z'" 
      using \<open>BetH Z PO Z'\<close> not_betH121 by auto
    {
      assume "IncidL Z' l" 
      hence "ColH PO Y Z'" 
        using ColH_def \<open>IncidL PO l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> by blast
      moreover have "ColH Z PO Z'" 
        by (simp add: \<open>BetH Z PO Z'\<close> betH_colH)
      ultimately have "ColH Y PO Z" 
        by (meson ColH_def \<open>PO \<noteq> Z'\<close> inter_incid_uniquenessH)
      have False 
        using ColH_def \<open>BetH Z PO Z'\<close> \<open>IncidL PO l\<close> \<open>IncidL Y l\<close> 
          \<open>IncidL Z' l\<close> \<open>IsL l\<close> \<open>PO \<noteq> Z'\<close> \<open>\<not> ColH Y PO Z\<close> betH_line 
          inter_incid_uniquenessH by blast
    }
    hence "cut l Z Z'" 
      using ColH_def \<open>BetH Z PO Z'\<close> \<open>IncidL PO l\<close> \<open>IncidL Y l\<close> 
        \<open>IsL l\<close> \<open>\<not> ColH Y PO Z\<close> local.cut_def by blast
    moreover
    obtain m where "IsL m" and "IncidL PO m" and "IncidL X m"
      using \<open>PO \<noteq> X\<close> line_existence by blast
    have "cut m Y Z'" 
      using Is_line \<open>IncidL PO m\<close> 
        \<open>IncidL X m\<close> \<open>\<And>l. \<lbrakk>IsL l; IncidL PO l; IncidL X l\<rbrakk> \<Longrightarrow> local.cut l Y Z'\<close> by blast
    have "\<not> IncidL Y m" 
      using \<open>local.cut m Y Z'\<close> local.cut_def by blast
    have "\<not> IncidL Z' m" 
      using \<open>local.cut m Y Z'\<close> local.cut_def by auto
    obtain X' where "IncidL X' m" and "BetH Y X' Z'" 
      using \<open>local.cut m Y Z'\<close> local.cut_def by blast
    have "same_side Z' X' l" 
      using \<open>BetH Y X' Z'\<close> \<open>IncidL Y l\<close> \<open>IncidL Z' l \<Longrightarrow> False\<close> outH_def out_same_side by blast
    moreover have "same_side X' X l" 
    proof -
      have "ColH PO X X'" 
        using ColH_def Is_line \<open>IncidL PO m\<close> \<open>IncidL X m\<close> \<open>IncidL X' m\<close> by blast
      have "\<not> ColH Y PO X" 
        using assms(1) same_side_prime_not_colH by presburger
      have "outH PO X X'" 
      proof (cases "X = X'")
        case True
        thus ?thesis 
          using \<open>PO \<noteq> X\<close> outH_trivial by auto
      next
        case False
        hence "X \<noteq> X'" 
          by simp
        have "ColH Z PO Z'" 
          by (simp add: \<open>BetH Z PO Z'\<close> betH_colH)
        have "ColH Y X' Z'" 
          by (simp add: \<open>BetH Y X' Z'\<close> betH_colH)
        have "PO = X' \<longrightarrow> ?thesis" 
          using \<open>IncidL PO l\<close> calculation(2) same_side_not_incid by blast
        moreover
        {
          assume "PO \<noteq> X'"
          have "ColH PO X X'" 
            by (simp add: \<open>ColH PO X X'\<close>)
          hence "BetH PO X X' \<or> BetH X X' PO \<or> BetH X PO X'" 
            using False \<open>PO \<noteq> X'\<close> \<open>PO \<noteq> X\<close> between_one by auto
          moreover have "BetH PO X X' \<longrightarrow> ?thesis" 
            using outH_def by auto
          moreover have "BetH X X' PO \<longrightarrow> ?thesis" 
            using between_comm outH_def by blast
          moreover {
            assume "BetH X PO X'"
            obtain lo where "IsL lo" and "IncidL PO lo" and "IncidL Z lo" 
              using \<open>PO \<noteq> Z\<close> line_existence by blast
            have "same_side X Y lo" 
              using \<open>IncidL PO lo\<close> \<open>IncidL Z lo\<close> \<open>IsL lo\<close> assms(2) same_side'_def by auto
            have "cut lo X X'" 
              by (metis Is_line \<open>BetH X PO X'\<close> \<open>ColH PO X X'\<close> \<open>IncidL PO lo\<close> 
                  \<open>PO \<noteq> X'\<close> \<open>same_side X Y lo\<close> colH_IncidL__IncidL colH_permut_312 
                  local.cut_def same_side_not_incid)
            moreover
            have "\<not> IncidL X' lo" 
              using calculation local.cut_def by blast
            moreover have "IncidL Z' lo" 
              by (metis \<open>ColH Z PO Z'\<close> \<open>IncidL PO lo\<close> \<open>IncidL Z lo\<close>
                  \<open>PO \<noteq> Z\<close> colH_IncidL__IncidL)
            ultimately have "same_side X' Y lo" 
              by (meson \<open>BetH Y X' Z'\<close> between_comm outH_def out_same_side)
            hence ?thesis 
              using \<open>local.cut lo X X'\<close> \<open>same_side X Y lo\<close> cut_same_side_cut 
                same_side_not_cut by blast
          }
          ultimately have ?thesis 
            by blast
        }
        ultimately show ?thesis 
          by blast
      qed
      thus ?thesis 
        by (meson \<open>IncidL PO l\<close> \<open>IncidL PO m\<close> \<open>IncidL X m\<close> \<open>IncidL Y l\<close> 
            \<open>PO \<noteq> X\<close> \<open>\<not> IncidL Y m\<close> inter_incid_uniquenessH out_same_side same_side_comm)
    qed    
    ultimately have "same_side Z' X l" 
      using same_side_trans by blast
    hence "cut l X Z" 
      using \<open>local.cut l Z Z'\<close> cut_comm cut_same_side_cut by blast
  }
  thus ?thesis 
    by (metis assms(2) colH_trivial112 cut'_def same_side_prime_not_colH)
qed

lemma th15_aux_1:
  assumes "\<not> ColH H PO L" and
    "\<not> ColH H' O' L'" and
    "\<not> ColH K PO L" and
    "\<not> ColH K' O' L'" and
    "\<not> ColH H PO K" and
    "\<not> ColH H' O' K'" and
    "same_side' H K PO L" and
    "same_side' H' K' O' L'" and
    "cut' K L PO H" and
    "CongaH H PO L H' O' L'" and
    "CongaH K PO L K' O' L'"
  shows "CongaH H PO K H' O' K'" 
proof -
  obtain K'' where "CongH O' K'' PO K" and "outH O' K' K''" 
    by (metis assms(3) assms(4) colH_trivial112 out_construction)
  obtain L'' where "CongH O' L'' PO L" and "outH O' L' L''" 
    by (metis assms(3) assms(4) colH_trivial122 out_construction)
  have "CongaH K PO L K'' O' L''" 
    using \<open>outH O' K' K''\<close> \<open>outH O' L' L''\<close> assms(1) assms(11) assms(5) 
      conga_out_conga ncolH_distincts outH_trivial by blast
  have "PO \<noteq> H" 
    using assms(1) colH_trivial112 by blast
  obtain l where "IsL l" and "IncidL PO l" and "IncidL H l" 
    using \<open>PO \<noteq> H\<close> line_existence by fastforce
  hence "cut l K L" 
    using assms(9) cut'_def by auto
  have "\<not> IncidL K l" 
    using \<open>local.cut l K L\<close> local.cut_def by blast
  have "\<not> IncidL L l" 
    using \<open>local.cut l K L\<close> local.cut_def by auto
  obtain I where "IncidL I l" and "BetH K I L" 
    using \<open>local.cut l K L\<close> local.cut_def by blast
  have "PO \<noteq> I" 
    using \<open>BetH K I L\<close> assms(3) betH_colH by blast
  have "H = I \<longrightarrow> outH PO I H" 
    using \<open>PO \<noteq> I\<close> outH_trivial by force
  moreover {
    assume "H \<noteq> I"
    have "ColH PO I H" 
      using ColH_def Is_line \<open>IncidL H l\<close> \<open>IncidL I l\<close> \<open>IncidL PO l\<close> by blast
    hence "BetH PO I H \<or> BetH I H PO \<or> BetH I PO H" 
      using between_one \<open>H \<noteq> I\<close> \<open>PO \<noteq> H\<close> \<open>PO \<noteq> I\<close> by blast
    moreover have "BetH PO I H \<longrightarrow> outH PO I H" 
      by (simp add: outH_def)
    moreover have "BetH I H PO \<longrightarrow> outH PO I H" 
      using between_comm outH_def by blast
    moreover {
      assume "BetH I PO H"
      have "PO \<noteq> L" 
        using \<open>IncidL PO l\<close> \<open>\<not> IncidL L l\<close> by auto
      obtain m where "IsL m" and "IncidL PO m" and "IncidL L m" 
        using ColH_def colH_trivial121 by blast
      have "same_side H K m" 
        using \<open>IncidL L m\<close> \<open>IncidL PO m\<close> \<open>IsL m\<close> assms(7) same_side'_def by auto
      have "cut m H I" 
        by (metis IncidL_not_IncidL__not_colH Is_line \<open>BetH I PO H\<close> \<open>ColH PO I H\<close> 
            \<open>IncidL PO m\<close> \<open>PO \<noteq> I\<close> \<open>same_side H K m\<close> 
            cut_comm local.cut_def same_side_not_incid)
      moreover have "same_side I K m" 
        by (meson \<open>BetH K I L\<close> \<open>IncidL L m\<close> between_comm calculation local.cut_def 
            outH_def out_same_side)
      ultimately have "cut m H K" 
        using cut_same_side_cut by blast
      hence "outH PO I H" 
        using \<open>same_side H K m\<close> same_side_not_cut by auto
    }
    ultimately have "outH PO I H" 
      by blast
  }
  ultimately have "outH PO I H"
    by blast
  have "outH PO L L" 
    using assms(7) outH_trivial same_side'_def by force
  obtain I' where "CongH O' I' PO I" and "outH O' H' I'" 
    by (metis \<open>PO \<noteq> I\<close> assms(2) colH_trivial112 out_construction)
  hence "CongaH I PO L I' O' L''" 
    using \<open>PO \<noteq> H\<close> \<open>outH O' L' L''\<close> \<open>outH PO I H\<close> \<open>outH PO L L\<close> assms(10) 
      conga_out_conga outH_sym by blast
  have "O' \<noteq> I'" 
    using \<open>outH O' H' I'\<close> out_distinct by auto
  have "I' \<noteq> L''" 
    by (metis (mono_tags, opaque_lifting) \<open>O' \<noteq> I'\<close> \<open>outH O' H' I'\<close> \<open>outH O' L' L''\<close> 
        assms(2) colH_trans ncolH_expand outH_col)
  hence "\<exists> I'. (O' \<noteq> I' \<and> I' \<noteq> L'' \<and> outH PO H I \<and> outH O' H' I' \<and>
              ColH O' I' H' \<and> CongH O' I' PO I \<and> CongaH I PO L I' O' L'')" 
    using \<open>CongH O' I' PO I\<close> \<open>CongaH I PO L I' O' L''\<close> \<open>O' \<noteq> I'\<close> \<open>PO \<noteq> H\<close>
      \<open>outH O' H' I'\<close> \<open>outH PO I H\<close> outH_col outH_sym by blast
  then obtain I' where "O' \<noteq> I'" and "I' \<noteq> L''" and 
    "outH PO H I" and "outH O' H' I'" and
    "ColH O' I' H'" and "CongH O' I' PO I" and "CongaH I PO L I' O' L''" 
    by blast
  have "PO \<noteq> L" 
    using \<open>IncidL PO l\<close> \<open>\<not> IncidL L l\<close> by blast
  have "O' \<noteq> L''" 
    using \<open>outH O' L' L''\<close> out_distinct by blast
  have "ColH O' L' L''" 
    using \<open>outH O' L' L''\<close> outH_expand by blast
  have "CongaH PO I L O' I' L'' \<and> CongaH PO L I O' L'' I' \<and> CongH I L I' L''"
  proof -
    have "\<not> ColH PO I L" 
      using \<open>IncidL I l\<close> \<open>IncidL PO l\<close> \<open>PO \<noteq> I\<close> \<open>\<not> IncidL L l\<close>
        colH_IncidL__IncidL by blast
    moreover 
    {
      assume "ColH O' I' L''" 
      have False
        by (metis \<open>ColH O' I' H'\<close> \<open>ColH O' I' L''\<close> \<open>ColH O' L' L''\<close> \<open>O' \<noteq> I'\<close> \<open>O' \<noteq> L''\<close> 
            assms(2) colH_permut_312 inter_uniquenessH ncolH_expand)
    }
    hence "\<not> ColH O' I' L''" 
      by blast
    moreover have "CongH PO I O' I'" 
      using \<open>CongH O' I' PO I\<close> \<open>O' \<noteq> I'\<close> congH_sym by blast
    moreover have "CongH PO L O' L''" 
      using \<open>CongH O' L'' PO L\<close> \<open>O' \<noteq> L''\<close> congH_sym by blast
    moreover have "CongaH I PO L I' O' L''" 
      by (simp add: \<open>CongaH I PO L I' O' L''\<close>)
    ultimately show ?thesis
      using th12 by blast
  qed
  have "CongaH PO I L O' I' L''" 
    using \<open>CongaH PO I L O' I' L'' \<and> CongaH PO L I O' L'' I' \<and> CongH I L I' L''\<close> by auto
  have "CongaH PO L I O' L'' I'" 
    using \<open>CongaH PO I L O' I' L'' \<and> CongaH PO L I O' L'' I' \<and> CongH I L I' L''\<close> by auto
  have "CongH I L I' L''" 
    using \<open>CongaH PO I L O' I' L'' \<and> CongaH PO L I O' L'' I' \<and> CongH I L I' L''\<close> by blast
  have "PO \<noteq> K" 
    using \<open>IncidL PO l\<close> \<open>\<not> IncidL K l\<close> by auto
  have "PO \<noteq> L" 
    by (simp add: \<open>PO \<noteq> L\<close>)
  have "ColH O' L' L''" 
    using \<open>ColH O' L' L''\<close> by blast
  have "O' \<noteq> L'" 
    using \<open>outH O' L' L''\<close> outH_expand by presburger
  have "CongaH PO K L O' K'' L'' \<and> CongaH PO L K O' L'' K'' \<and> CongH K L K'' L''" 
  proof -
    have "\<not> ColH PO K L" 
      using assms(3) colH_permut_213 by blast
    moreover 
    {
      assume "ColH O' K'' L''"
      have "O' \<noteq> K''" 
        using \<open>outH O' K' K''\<close> out_distinct by presburger
      have "K'' \<noteq> L''" 
        by (metis \<open>ColH O' L' L''\<close> \<open>outH O' K' K''\<close> assms(4) colH_trans 
            ncolH_expand outH_expand) 
      have "O' \<noteq> K'" 
        using assms(6) colH_trivial122 by blast
      have "K' \<noteq> L'" 
        using assms(4) ncolH_expand by presburger
      have "ColH O' K' L'"
        by (metis \<open>ColH O' K'' L''\<close> \<open>ColH O' L' L''\<close> \<open>O' \<noteq> K''\<close> \<open>O' \<noteq> L''\<close> 
            \<open>outH O' K' K''\<close> colH_trans ncolH_expand outH_col)
      have False 
        using \<open>ColH O' K' L'\<close> assms(4) colH_permut_213 by blast
    }
    hence "\<not> ColH O' K'' L''"
      by blast
    moreover have "CongH PO K O' K''" 
      using \<open>CongH O' K'' PO K\<close> \<open>outH O' K' K''\<close> congH_sym out_distinct by presburger
    moreover have "CongH PO L O' L''" 
      using \<open>CongH O' L'' PO L\<close> \<open>O' \<noteq> L''\<close> congH_sym by presburger
    moreover have "CongaH K PO L K'' O' L''" 
      by (simp add: \<open>CongaH K PO L K'' O' L''\<close>)
    ultimately show ?thesis 
      using th12 by blast
  qed
  have "CongaH PO K L O' K'' L''" 
    using \<open>CongaH PO K L O' K'' L'' \<and> CongaH PO L K O' L'' K'' \<and> CongH K L K'' L''\<close> by auto
  have "CongaH PO L K O' L'' K''" 
    using \<open>CongaH PO K L O' K'' L'' \<and> CongaH PO L K O' L'' K'' \<and> CongH K L K'' L''\<close> by auto
  have "CongH K L K'' L''" 
    using \<open>CongaH PO K L O' K'' L'' \<and> CongaH PO L K O' L'' K'' \<and> CongH K L K'' L''\<close> by auto
  have "BetH K'' I' L''" 
  proof -
    have "outH L PO PO" 
      using \<open>PO \<noteq> L\<close> outH_def by auto
    have "outH L'' O' O'" 
      using \<open>O' \<noteq> L''\<close> outH_def by auto
    have "outH L'' I' I'" 
      using \<open>I' \<noteq> L''\<close> outH_def by blast
    have "outH L I K" 
      using \<open>BetH K I L\<close> between_comm outH_def by blast
    hence "CongaH PO L K O' L'' I'" 
      using conga_out_conga \<open>CongaH PO L I O' L'' I'\<close> \<open>outH L PO PO\<close> \<open>outH L'' I' I'\<close>
        \<open>outH L'' O' O'\<close> by blast
    moreover 
    have "same_side' H' I' L'' O'" 
    proof -
      obtain m where "IsL m" and "IncidL O' m" and "IncidL L'' m" 
        using \<open>O' \<noteq> L''\<close> line_existence by blast
      have "L'' \<noteq> O'" 
        using \<open>O' \<noteq> L''\<close> by auto
      moreover have "IncidL L'' m" 
        by (simp add: \<open>IncidL L'' m\<close>)
      moreover have "IncidL O' m" 
        using \<open>IncidL O' m\<close> by auto
      moreover 
      {
        assume "IncidL H' m" 
        hence "ColH O' L'' H'" 
          using ColH_def \<open>IsL m\<close> calculation(2) calculation(3) by blast
        hence False 
          by (metis \<open>ColH O' L' L''\<close> assms(2) calculation(1) colH_trans ncolH_distincts)
      }
      hence "\<not> IncidL H' m" 
        by blast
      moreover have "outH O' H' I'" 
        using \<open>outH O' H' I'\<close> by blast
      ultimately show ?thesis using out_same_side' 
        by blast
    qed
    moreover 
    have "L'' \<noteq> O'" 
      using \<open>O' \<noteq> L''\<close> by blast
    moreover 
    have "\<forall> l. (IsL l \<and> IncidL L'' l \<and> IncidL O' l) \<longrightarrow> same_side H' K'' l" 
    proof -
      {
        fix l
        assume "IsL l" and
          "IncidL L'' l" and "IncidL O' l"
        have "ColH O' L' L''" 
          by (simp add: \<open>ColH O' L' L''\<close>)
        obtain lo where "IncidL O' lo" and "IncidL L' lo" and 
          "IncidL L'' lo" and "IncidL O' lo" 
          by (metis \<open>outH O' L' L''\<close> betH_line line_existence outH_def)
        have "EqL l lo" 
          using Is_line \<open>IncidL L'' l\<close> \<open>IncidL L'' lo\<close> \<open>IncidL O' l\<close> \<open>IncidL O' lo\<close> 
            calculation(3) line_uniqueness by presburger
        hence "same_side K' K'' lo" 
          using ColH_def Is_line \<open>IncidL L' lo\<close> \<open>IncidL O' lo\<close> \<open>outH O' K' K''\<close> assms(4) 
            out_same_side by blast
        hence "same_side H' K' lo" 
          using Is_line \<open>IncidL L' lo\<close> \<open>IncidL O' lo\<close> assms(8) same_side'_def by force
        hence "same_side H' K'' l" using same_side_trans 
          by (metis (no_types, lifting) ColH_def \<open>IncidL L' lo\<close> \<open>IncidL L'' l\<close>
              \<open>IncidL L'' lo\<close> \<open>IncidL O' l\<close> \<open>IncidL O' lo\<close> \<open>IsL l\<close> \<open>outH O' K' K''\<close> assms(4) 
              assms(8) calculation(3) inter_incid_uniquenessH out_same_side same_side'_def)
      }
      thus ?thesis 
        by blast
    qed
    ultimately have "same_side' H' K'' L'' O'" 
      using same_side'_def by blast
    thus ?thesis 
      by (metis \<open>BetH K I L\<close>  \<open>CongaH PO L K O' L'' I'\<close> \<open>same_side' H' I' L'' O'\<close> assms(3) 
          \<open>CongaH PO I L O' I' L'' \<and> CongaH PO L I O' L'' I' \<and> CongH I L I' L''\<close> 
          \<open>CongaH PO K L O' K'' L'' \<and> CongaH PO L K O' L'' K'' \<and> CongH K L K'' L''\<close>
          betH_congH3_outH_betH between_comm colH_permut_312 congH_permlr 
          cong_4_uniqueness out_distinct same_side_prime_not_colH)
  qed
  have "CongaH K PO I K'' O' I' \<and> CongaH K I PO K'' I' O' \<and> CongH PO I O' I'" 
  proof -
    have "CongH I' K'' I K" 
    proof -
      have "BetH L'' I' K''"       
        using \<open>BetH K'' I' L''\<close> between_comm by blast
      moreover have "BetH L I K"       
        by (simp add: \<open>BetH K I L\<close> between_comm)
      moreover have "CongH L'' I' L I"       
        using \<open>BetH K I L\<close> \<open>CongH I L I' L''\<close> \<open>I' \<noteq> L''\<close> betH_distincts 
          congH_perms by blast
      moreover have "CongH L'' K'' L K"       
        by (metis \<open>CongH K L K'' L''\<close> assms(3) calculation(1) colH_trivial121 
            congH_perms not_betH121)

      ultimately show ?thesis
        using soustraction_betH by blast
    qed
    have "\<not> ColH K PO I" 
      by (metis IncidL_not_IncidL__not_colH \<open>IncidL I l\<close> \<open>IncidL PO l\<close> \<open>PO \<noteq> I\<close> 
          \<open>\<not> IncidL K l\<close> colH_permut_321)
    moreover 
    {
      assume "ColH K'' O' I'"
      have "O' \<noteq> K''" 
        using \<open>outH O' K' K''\<close> out_distinct by blast
      have "ColH O' K' K''" 
        using \<open>outH O' K' K''\<close> outH_expand by auto
      hence "ColH K' O' L'" 
        by (metis colH_permut_231 colH_trans colH_trivial121 \<open>ColH K'' O' I'\<close> 
            \<open>ColH O' I' H'\<close> \<open>O' \<noteq> I'\<close> \<open>O' \<noteq> K''\<close> assms(6))
      hence False 
        by (simp add: assms(4))
    }
    hence "\<not> ColH K'' O' I'" 
      by blast
    moreover have "CongH K PO K'' O'" 
      using outH_expand \<open>CongH O' K'' PO K\<close> \<open>PO \<noteq> K\<close> \<open>outH O' K' K''\<close> 
        congH_perms by blast
    moreover have "CongH K I K'' I'" 
      by (metis \<open>CongH I' K'' I K\<close> \<open>IncidL I l\<close> \<open>\<not> IncidL K l\<close> calculation(2) 
          colH_trivial121 congH_perms)
    moreover have "CongaH PO K I O' K'' I'" 
      using \<open>BetH K I L\<close> \<open>BetH K'' I' L''\<close> \<open>CongaH PO K L O' K'' L''\<close> \<open>PO \<noteq> K\<close> 
        calculation(2) conga_out_conga ncolH_expand outH_def by blast
    ultimately 
    show ?thesis using th12 by blast
  qed
  have "CongaH K PO I K'' O' I'" 
    using \<open>CongaH K PO I K'' O' I' \<and> CongaH K I PO K'' I' O' \<and> CongH PO I O' I'\<close> by blast
  have "CongaH K I PO K'' I' O'" 
    using \<open>CongaH K PO I K'' O' I' \<and> CongaH K I PO K'' I' O' \<and> CongH PO I O' I'\<close> by auto
  have "CongH PO I O' I'" 
    using \<open>CongH O' I' PO I\<close> \<open>O' \<noteq> I'\<close> congH_sym by auto
  have "outH PO K K"     
    using \<open>PO \<noteq> K\<close> outH_def by force
  moreover have "outH PO I H"     
    by (simp add: \<open>outH PO I H\<close>)
  moreover have "outH O' K'' K'"     
    using \<open>outH O' K' K''\<close> outH_sym out_distinct by blast
  moreover have "outH O' I' H'"     
    by (simp add: \<open>O' \<noteq> I'\<close> \<open>outH O' H' I'\<close> outH_sym)
  ultimately show ?thesis 
    using \<open>CongaH K PO I K'' O' I'\<close> conga_out_conga conga_permlr by blast
qed

lemma th15_aux:
  assumes "\<not> ColH H PO L" and
    "\<not> ColH H' O' L'" and
    "\<not> ColH K PO L" and
    "\<not> ColH K' O' L'" and
    "\<not> ColH H PO K" and
    "\<not> ColH H' O' K'" and
    "same_side' H K PO L" and
    "same_side' H' K' O' L'" and
    "CongaH H PO L H' O' L'" and
    "CongaH K PO L K' O' L'"
  shows "CongaH H PO K H' O' K'" 
proof -
  obtain p where "IsP p" and "IncidP H p" and "IncidP K p" and 
    "IncidP PO p" and "IncidP L p" 
    using Is_plane assms(7) same_side_prime__plane by blast
  moreover have "cut' K L PO H \<longrightarrow> CongaH H PO K H' O' K'" 
    using assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) assms(6) 
      assms(7) assms(8) assms(9) th15_aux_1 by auto
  moreover {
    assume "same_side' K L PO H"
    moreover have "\<not> ColH K PO H" 
      using assms(5) colH_permut_321 by blast
    moreover have "\<not> ColH K' O' H'" 
      using assms(6) colH_permut_321 by blast
    moreover
    have "PO \<noteq> L" 
      using assms(3) colH_trivial122 by blast
    {
      fix l
      assume "IsL l" and "IncidL PO l" and "IncidL L l"
      hence "same_side K H l" 
        by (metis assms(7) same_side'_def same_side_comm)
    }
    hence "same_side' K H PO L" 
      using \<open>PO \<noteq> L\<close> same_side'_def by auto
    moreover have "O' \<noteq> L'" 
      using assms(4) colH_trivial122 by force
    {
      fix l
      assume "IsL l" and "IncidL O' l" and "IncidL L' l"
      hence "same_side K' H' l" 
        by (meson assms(8) same_side'_def same_side_comm)
    }
    hence "same_side' K' H' O' L'" 
      by (simp add: \<open>O' \<noteq> L'\<close> same_side'_def)
    moreover have "cut' H L PO K" 
      by (simp add: OS2__TS assms(7) calculation(1))
    ultimately have "CongaH H PO K H' O' K'" 
      using assms(1) assms(2) assms(3) assms(4) assms(9) assms(10) 
        conga_permlr th15_aux_1 by presburger
  }
  moreover have "\<not> ColH K PO H" 
    using assms(5) colH_permut_321 by blast
  moreover have "\<not> ColH L PO H" 
    using assms(1) colH_permut_321 by blast
  ultimately show ?thesis 
    using plane_separation by blast
qed

lemma th15:
  assumes "\<not> ColH H PO L" and
    "\<not> ColH H' O' L'" and
    "\<not> ColH K PO L" and
    "\<not> ColH K' O' L'" and
    "\<not> ColH H PO K" and
    "\<not> ColH H' O' K'" and
    "(cut' H K PO L \<and> cut' H' K' O' L') \<or> (same_side' H K PO L \<and> same_side' H' K' O' L')" and
    "CongaH H PO L H' O' L'" and
    "CongaH K PO L K' O' L'"
  shows "CongaH H PO K H' O' K'" 
proof -
  {
    assume "same_side' H K PO L" and "same_side' H' K' O' L'"
    hence ?thesis using th15_aux 
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
        assms(8) assms(9) by presburger
  }
  moreover
  {
    assume "cut' H K PO L" and
      "cut' H' K' O' L'" 
    obtain SH where "BetH H PO SH" 
      by (metis assms(1) between_out colH_trivial112)
    obtain SH' where "BetH H' O' SH'" 
      by (metis assms(2) between_out colH_trivial112)
    have "CongaH SH PO L SH' O' L'" 
      using \<open>BetH H PO SH\<close> \<open>BetH H' O' SH'\<close> assms(1) assms(2) assms(8)
        conga_permlr th14 by blast
    have "H \<noteq> PO" 
      using assms(1) colH_trivial112 by force
    have "PO \<noteq> SH" 
      using \<open>BetH H PO SH\<close> betH_distincts by blast
    have "H \<noteq> SH" 
      using \<open>BetH H PO SH\<close> not_betH121 by auto
    have "H' \<noteq> O'" 
      using assms(6) colH_trivial112 by force
    have "H' \<noteq> SH'" 
      using \<open>BetH H' O' SH'\<close> not_betH121 by force
    have "O' \<noteq> SH'" 
      using \<open>BetH H' O' SH'\<close> betH_distincts by blast
    have "CongaH SH PO K SH' O' K'" 
    proof -
      have "ColH H PO SH" 
        by (simp add: \<open>BetH H PO SH\<close> betH_colH)
      have "ColH H' O' SH'" 
        by (simp add: \<open>BetH H' O' SH'\<close> betH_colH)
      moreover have "\<not> ColH SH PO L" 
        by (metis \<open>ColH H PO SH\<close> \<open>PO \<noteq> SH\<close> assms(1) colH_trans ncolH_expand)
      moreover have "\<not> ColH SH' O' L'" 
        by (metis \<open>ColH H' O' SH'\<close> \<open>O' \<noteq> SH'\<close> assms(2) colH_permut_321 
            colH_trans colH_trivial122)
      moreover have "\<not> ColH SH PO K" 
        by (metis \<open>ColH H PO SH\<close> \<open>PO \<noteq> SH\<close> assms(5) colH_permut_321 
            colH_trans colH_trivial122)
      moreover have "\<not> ColH SH' O' K'" 
        by (metis \<open>ColH H' O' SH'\<close> \<open>O' \<noteq> SH'\<close> assms(6) colH_permut_321 
            colH_trans colH_trivial122)
      moreover 
      {
        fix l
        assume "IsL l" and "IncidL PO l" and "IncidL L l"
        hence "cut l SH H" 
          by (meson ColH_def \<open>BetH H PO SH\<close> assms(1) between_comm 
              calculation(2) local.cut_def)
        moreover
        have "cut l H K" 
          using \<open>cut' H K PO L\<close> \<open>IncidL L l\<close> \<open>IncidL PO l\<close> \<open>IsL l\<close> cut'_def by auto
        hence "cut l K H" 
          using cut_comm by blast
        ultimately have "same_side SH K l"  
          using same_side_def \<open>IsL l\<close> by blast
      }
      moreover have "PO \<noteq> L" 
        using calculation(2) colH_trivial122 by blast
      ultimately have "same_side' SH K PO L" 
        using same_side'_def by presburger
      moreover 
      {
        fix l
        assume "IsL l" and "IncidL O' l" and "IncidL L' l"
        hence "cut l SH' H'" 
          by (meson ColH_def \<open>BetH H' O' SH'\<close> \<open>\<not> ColH SH' O' L'\<close> 
              assms(2) between_comm local.cut_def)
        moreover
        have "cut l H' K'"
          using \<open>cut' H' K' O' L'\<close> \<open>IncidL L' l\<close> \<open>IncidL O' l\<close> \<open>IsL l\<close> cut'_def by auto 
        hence "cut l K' H'" 
          using cut_comm by blast
        ultimately have "same_side SH' K' l"  
          using same_side_def \<open>IsL l\<close> by blast
      }
      moreover have "O' \<noteq> L'" 
        using assms(2) colH_trivial122 by force
      ultimately have "same_side' SH' K' O' L'" 
        using same_side'_def by presburger
      thus ?thesis
        using th15_aux \<open>CongaH SH PO L SH' O' L'\<close> \<open>\<not> ColH SH PO K\<close> 
          \<open>\<not> ColH SH' O' K'\<close> assms(9) same_side_prime_not_colH
          \<open>same_side' SH K PO L\<close> by blast
    qed
    moreover have "\<not> ColH SH PO K" 
      using \<open>BetH H PO SH\<close> assms(5) betH_colH between_comm colH_trans colH_trivial122 by blast
    moreover have "\<not> ColH SH' O' K'" 
      using \<open>BetH H' O' SH'\<close> assms(6) betH_colH between_comm colH_trans colH_trivial122 by blast
    moreover have "BetH SH PO H" 
      by (simp add: \<open>BetH H PO SH\<close> between_comm)
    moreover have "BetH SH' O' H'" 
      by (simp add: \<open>BetH H' O' SH'\<close> between_comm)
    ultimately have ?thesis 
      using conga_permlr th14 by blast
  }
  ultimately show ?thesis
    using assms(7) by fastforce
qed

lemma th17:
  assumes "\<not> ColH X Y Z1" and
    "\<not> ColH X Y Z2" and
    "ColH X I Y" and
    "BetH Z1 I Z2" and
    "CongH X Z1 X Z2" and
    "CongH Y Z1 Y Z2"
  shows "CongaH X Y Z1 X Y Z2" 
proof (cases "ColH Y Z1 Z2")
  case True
  hence "ColH Y Z1 Z2"
    by simp
  show ?thesis 
  proof (cases "ColH X Z1 Z2")
    case True
    hence "ColH X Z1 Z2"
      by simp
    have "ColH Z1 I Z2" 
      by (simp add: assms(4) betH_colH)
    have "Z1 \<noteq> Z2" 
      using assms(4) not_betH121 by blast
    hence "ColH X Y Z2" 
      by (metis True \<open>ColH Y Z1 Z2\<close> colH_permut_312 colH_trivial122 inter_uniquenessH)
    thus ?thesis
      using assms(2) by auto
  next
    case False
    hence "\<not> ColH X Z1 Z2"
      by simp
    have "CongaH X Z1 Z2 X Z2 Z1" 
      by (simp add: False assms(5) isosceles_congaH)
    have "\<not> ColH Z1 Y X" 
      using assms(1) colH_permut_321 by blast
    moreover have "\<not> ColH Z2 Y X" 
      using assms(2) colH_permut_321 by blast
    moreover have "CongH Z1 Y Z2 Y" 
      using assms(2) assms(6) congH_permlr ncolH_expand by blast
    moreover have "CongH Z1 X Z2 X" 
      using False assms(5) congH_permlr ncolH_distincts by presburger
    moreover 
    have "BetH Z1 Y Z2" 
      by (metis False True assms(1) assms(6) calculation(2) colH_trivial112 
          colH_trivial122 congH_colH_betH)
    have "CongaH X Z1 Y X Z2 Y" 
    proof -
      have "outH Z1 X X" 
        by (metis False colH_trivial112 outH_trivial)
      moreover have "outH Z1 Z2 Y" 
        by (simp add: \<open>BetH Z1 Y Z2\<close> outH_def)
      moreover have "outH Z2 X X" 
        by (metis False colH_trivial121 outH_trivial)
      moreover have "outH Z2 Z1 Y" 
        using \<open>BetH Z1 Y Z2\<close> between_comm outH_def by blast
      ultimately show ?thesis 
        using \<open>CongaH X Z1 Z2 X Z2 Z1\<close> conga_out_conga by blast
    qed
    hence "CongaH Y Z1 X Y Z2 X" 
      using conga_permlr by presburger
    ultimately have "CongaH Z1 Y X Z2 Y X" 
      using cong_5 by blast
    thus ?thesis 
      using conga_permlr by blast
  qed
next
  case False
  hence "\<not> ColH Y Z1 Z2"
    by simp
  show ?thesis 
  proof (cases "ColH X Z1 Z2")
    case True
    hence "ColH X Z1 Z2"
      by simp
    have "CongaH Y Z1 Z2 Y Z2 Z1" 
      by (simp add: False assms(6) isosceles_congaH)
    have "CongaH Z1 Y X Z2 Y X" 
    proof -
      have "\<not> ColH Z1 Y X" 
        using assms(1) colH_permut_321 by blast
      moreover have "\<not> ColH Z2 Y X" 
        using assms(2) colH_permut_321 by blast
      moreover have "CongH Z1 Y Z2 Y" 
        by (metis False assms(6) colH_trivial121 congH_permlr)
      moreover have "CongH Z1 X Z2 X" 
        using assms(2) assms(5) congH_permlr ncolH_expand by presburger
      moreover 
      have "BetH Z1 X Z2" 
        by (metis False True assms(2) assms(5) calculation(1) 
            colH_trivial121 colH_trivial122 congH_colH_betH)
      have "CongaH Y Z1 X Y Z2 X" 
      proof -
        have "outH Z1 Y Y" 
          by (metis False colH_trivial112 outH_trivial)
        moreover have "outH Z1 Z2 X" 
          by (simp add: \<open>BetH Z1 X Z2\<close> outH_def)
        moreover have "outH Z2 Y Y" 
          using \<open>\<not> ColH Z2 Y X\<close> ncolH_expand outH_trivial by blast
        moreover have "outH Z2 Z1 X" 
          using \<open>BetH Z1 X Z2\<close> between_comm outH_def by blast
        ultimately show ?thesis 
          using \<open>CongaH Y Z1 Z2 Y Z2 Z1\<close> conga_out_conga by blast
      qed
      ultimately show ?thesis 
        using cong_5 by blast
    qed
    thus ?thesis 
      using conga_permlr by blast
  next
    case False
    hence "\<not> ColH X Z1 Z2"
      by simp
    have "CongaH X Z1 Z2 X Z2 Z1" 
      by (simp add: False assms(5) isosceles_congaH)
    have "CongaH Y Z1 Z2 Y Z2 Z1" 
      by (simp add: \<open>\<not> ColH Y Z1 Z2\<close> assms(6) isosceles_congaH)
    have "CongaH X Z1 Y X Z2 Y" 
    proof -
      have "\<not> ColH X Z1 Z2" 
        by (simp add: False)
      moreover have "\<not> ColH X Z2 Z1" 
        using calculation colH_permut_132 by blast
      moreover have "\<not> ColH Y Z1 Z2" 
        by (simp add: \<open>\<not> ColH Y Z1 Z2\<close>)
      moreover have "\<not> ColH Y Z2 Z1" 
        using calculation(3) colH_permut_132 by blast
      moreover have "\<not> ColH X Z1 Y" 
        using assms(1) colH_permut_132 by blast
      moreover have "\<not> ColH X Z2 Y" 
        using assms(2) colH_permut_132 by blast
      moreover 
      have "cut' X Y Z1 Z2 \<and> cut' X Y Z2 Z1 \<or> same_side' X Y Z1 Z2 \<and> same_side' X Y Z2 Z1"
      proof -
        obtain p where "IsP p" and "IncidP X p" and "IncidP Y p" and "IncidP Z1 p"
          using assms(1) plan_existence by blast
        hence "IncidP Z2 p" 
          by (metis betH_colH assms(2) assms(3) assms(4) colH_permut_312 
              line_on_plane' ncolH_distincts)
        thus ?thesis 
          by (metis False \<open>IncidP X p\<close> \<open>IncidP Y p\<close> \<open>IncidP Z1 p\<close> calculation(2) 
              calculation(3) calculation(4) plane_separation same_side'_def)
      qed
      ultimately show ?thesis 
        by (simp add: \<open>CongaH Y Z1 Z2 Y Z2 Z1\<close> \<open>CongaH X Z1 Z2 X Z2 Z1\<close> th15)
    qed
    have "CongaH Z1 Y X Z2 Y X" 
    proof -
      have "\<not> ColH Z1 Y X" 
        using assms(1) colH_permut_321 by blast
      moreover have "\<not> ColH Z2 Y X" 
        using assms(2) colH_permut_321 by blast
      moreover have "CongH Z1 Y Z2 Y" 
        by (metis \<open>\<not> ColH Y Z1 Z2\<close> assms(6) colH_trivial121 congH_permlr)
      moreover have "CongH Z1 X Z2 X" 
        by (metis assms(5) calculation(2) colH_trivial121 congH_permlr)
      moreover have "CongaH Y Z1 X Y Z2 X" 
        using \<open>CongaH X Z1 Y X Z2 Y\<close> conga_permlr by blast
      ultimately show ?thesis 
        using cong_5 by blast
    qed
    thus ?thesis 
      using conga_permlr by blast
  qed
qed

lemma congaH_existence_congH:
  assumes "U \<noteq> V" and
    "\<not> ColH P PO X" and
    "\<not> ColH A B C" 
  shows "\<exists> Y. (CongaH A B C X PO Y \<and> same_side' P Y PO X \<and> CongH PO Y U V)" 
proof -
  have "A \<noteq> B" 
    using assms(3) colH_trivial112 by blast
  have "C \<noteq> B" 
    using assms(3) colH_trivial122 by blast
  have "PO \<noteq> X" 
    using assms(2) colH_trivial122 by blast
  {
    fix x
    assume "CongaH A B C X PO x" and
      "same_side' P x PO X" 
    obtain Yaux where "CongaH A B C X PO Yaux" and "same_side' P Yaux PO X" 
      using \<open>CongaH A B C X PO x\<close> \<open>same_side' P x PO X\<close> by blast
    hence "\<not> ColH Yaux PO X" 
      using same_side_prime_not_colH by blast
    {
      assume "PO = Yaux"
      hence "ColH Yaux PO X" 
        by (simp add: colH_trivial112)
      hence False 
        by (simp add: \<open>\<not> ColH Yaux PO X\<close>)
    }
    {
      fix Y
      assume "CongH PO Y U V" and "outH PO Yaux Y"
      have "CongaH A B C X PO Y" 
      proof -
        have "CongaH A B C X PO Yaux" 
          using \<open>CongaH A B C X PO Yaux\<close> by blast
        moreover have "outH B A A" 
          using \<open>A \<noteq> B\<close> outH_trivial by auto
        moreover have "outH B C C" 
          using \<open>C \<noteq> B\<close> outH_trivial by presburger
        moreover have "outH PO X X" 
          using \<open>PO \<noteq> X\<close> outH_trivial by blast
        moreover have "outH PO Yaux Y" 
          using \<open>outH PO Yaux Y\<close> by auto
        ultimately show ?thesis 
          using conga_out_conga by blast
      qed
      moreover have "same_side' P Y PO X" 
        using ColH_def \<open>\<not> ColH Yaux PO X\<close> \<open>outH PO Yaux Y\<close> 
          \<open>same_side' P Yaux PO X\<close> out_same_side same_side'_def same_side_trans by fastforce
      ultimately have "\<exists> Y. CongaH A B C X PO Y \<and> same_side' P Y PO X \<and> CongH PO Y U V" 
        using \<open>CongH PO Y U V\<close> by auto
    }
    hence ?thesis 
      using \<open>PO = Yaux \<Longrightarrow> False\<close> assms(1) out_construction by blast
  }
  thus ?thesis 
    using assms(2) assms(3) cong_4_existence by blast
qed

lemma th18_aux:
  assumes "\<not> ColH A B C" and
    "\<not> ColH A' B' C'" and
    "CongH A B A' B'" and
    "CongH A C A' C'" and
    "CongH B C B' C'"
  shows "CongaH B A C B' A' C'" 
proof -
  have "A \<noteq> B" 
    using assms(1) colH_trivial112 by blast
  moreover
  have "C' \<noteq> B'" 
    using assms(2) colH_trivial122 by blast
  have "A' \<noteq> C'" 
    using assms(2) colH_trivial121 by force
  {
    fix B0
    assume "CongaH C A B C' A' B0" and "same_side' B' B0 A' C'" and "CongH A' B0 A B" 
    {
      fix P 
      assume "BetH B' C' P"
      { 
        fix B''
        assume "CongaH C A B C' A' B''" and "same_side' P B'' A' C'" and "CongH A' B'' A B"
        have "\<not> ColH A' C' B0" 
          using \<open>same_side' B' B0 A' C'\<close> colH_permut_312 same_side_prime_not_colH by blast
        have "\<not> ColH A' C' B''" 
          using \<open>same_side' P B'' A' C'\<close> colH_permut_312 same_side_prime_not_colH by blast
        have "CongH B C B0 C'" 
          by (metis \<open>CongH A' B0 A B\<close> \<open>CongaH C A B C' A' B0\<close> 
              \<open>same_side' B' B0 A' C'\<close> assms(1) assms(4) colH_permut_213 colH_trivial112 
              congH_sym conga_permlr same_side_prime_not_colH th12)
        have "CongH B C B'' C'" 
          by (metis \<open>CongH A' B'' A B\<close> \<open>CongaH C A B C' A' B''\<close> \<open>\<not> ColH A' C' B''\<close> 
              assms(1) assms(4) colH_permut_132 congH_sym cong_permr ncolH_distincts th12)
        have "A' \<noteq> B''" 
          using \<open>\<not> ColH A' C' B''\<close> colH_trivial121 by blast
        have "A' \<noteq> B0" 
          using \<open>\<not> ColH A' C' B0\<close> colH_trivial121 by fastforce
        have "CongH A' B'' A' B0" 
          by (meson \<open>A' \<noteq> B''\<close> \<open>A' \<noteq> B0\<close> \<open>CongH A' B'' A B\<close> \<open>CongH A' B0 A B\<close>
              congH_sym cong_pseudo_transitivity)
        have "CongH B'' C' B0 C'" 
          using \<open>CongH B C B'' C'\<close> \<open>CongH B C B0 C'\<close> cong_pseudo_transitivity by blast
        have "CongH B'' C' B' C'" 
          using \<open>CongH B C B'' C'\<close> assms(5) cong_pseudo_transitivity by blast
        obtain l where "IsL l" and "IncidL A' l" and "IncidL C' l" 
          using \<open>A' \<noteq> C'\<close> line_existence by blast
        have "cut l B' P" 
          by (meson ColH_def Is_line \<open>BetH B' C' P\<close> \<open>IncidL A' l\<close> \<open>IncidL C' l\<close>
              \<open>same_side' P B'' A' C'\<close> assms(2) local.cut_def same_side_prime_not_colH)
        have "cut l B' B''" 
          using \<open>IncidL A' l\<close> \<open>IncidL C' l\<close> \<open>IsL l\<close> \<open>local.cut l B' P\<close>
            \<open>same_side' P B'' A' C'\<close> cut_same_side_cut same_side'_def by blast
        have "\<not> IncidL B' l" 
          using \<open>local.cut l B' P\<close> local.cut_def by blast
        moreover have "\<not> IncidL B'' l" 
          using \<open>local.cut l B' B''\<close> local.cut_def by blast
        moreover have "\<exists> I. IncidL I l \<and> BetH B' I B''" 
          using \<open>local.cut l B' B''\<close> local.cut_def by auto
        ultimately obtain I' where "ColH A' I' C'" and "BetH B' I' B''" 
          using ColH_def Is_line \<open>IncidL A' l\<close> \<open>IncidL C' l\<close> by blast
        have "cut l B'' B0" 
          by (meson \<open>IncidL A' l\<close> \<open>IncidL C' l\<close> \<open>IsL l\<close> \<open>local.cut l B' B''\<close>
              \<open>same_side' B' B0 A' C'\<close> cut_comm cut_same_side_cut same_side'_def)
        then obtain I where "ColH A' I C' \<and> BetH B0 I B''" 
          by (meson ColH_def \<open>IncidL A' l\<close> \<open>IncidL C' l\<close> cut_comm local.cut_def)
        have "CongaH C' A' B'' C' A' B0" 
        proof -
          have "\<not> ColH C' A' B''" 
            using \<open>\<not> ColH A' C' B''\<close> colH_permut_213 by blast
          moreover have "\<not> ColH C' A' B0" 
            using \<open>\<not> ColH A' C' B0\<close> colH_permut_213 by blast
          moreover have "ColH C' I A'" 
            using \<open>ColH A' I C' \<and> BetH B0 I B''\<close> colH_permut_321 by presburger
          moreover have "BetH B'' I B0" 
            by (simp add: \<open>ColH A' I C' \<and> BetH B0 I B''\<close> between_comm)
          moreover have "CongH C' B'' C' B0" 
            by (metis \<open>CongH B'' C' B0 C'\<close> calculation(2) colH_trivial121 congH_permlr)
          ultimately show ?thesis 
            using th17 \<open>CongH A' B'' A' B0\<close> by blast
        qed
        moreover have "outH A' B0 B'" 
        proof -
          have "\<not> ColH B' A' C'" 
            using assms(2) colH_permut_213 by blast
          moreover have "\<not> ColH C' A' B''" 
            using \<open>\<not> ColH A' C' B''\<close> colH_permut_213 by blast
          moreover have "CongaH C' A' B'' C' A' B'" 
            by (metis (full_types) \<open>A' \<noteq> B''\<close> \<open>BetH B' I' B''\<close> \<open>ColH A' I' C'\<close> 
                \<open>CongH A' B'' A B\<close> \<open>CongH B'' C' B' C'\<close> assms(3) between_comm calculation(1) 
                calculation(2) colH_permut_321 congH_permlr congH_sym 
                cong_pseudo_transitivity th17)
          moreover have "same_side' B' B' A' C'" 
            using calculation(1) colH_permut_312 same_side_prime_refl by blast
          ultimately show ?thesis 
            using  \<open>CongaH C' A' B'' C' A' B0\<close> \<open>same_side' B' B0 A' C'\<close> 
              cong_4_uniqueness by blast
        qed
        ultimately have "CongaH B A C B' A' C'" 
          by (metis \<open>A \<noteq> B\<close> \<open>A' \<noteq> B0\<close> \<open>CongH A' B0 A B\<close> \<open>CongaH C A B C' A' B0\<close> 
              \<open>outH A' B0 B'\<close> assms(3) betH_not_congH congH_perms cong_pseudo_transitivity conga_permlr outH_def)
      }
      moreover have "\<not> ColH P A' C'" 
        by (metis betH_expand \<open>BetH B' C' P\<close> assms(2) colH_permut_312 
            colH_trans colH_trivial121)
      moreover have "\<not> ColH C A B" 
        using assms(1) colH_permut_231 by blast
      ultimately have "CongaH B A C B' A' C'" 
        using \<open>A \<noteq> B\<close> congaH_existence_congH by force
    }
    hence "CongaH B A C B' A' C'" 
      using \<open>C' \<noteq> B'\<close>between_out by presburger
  }
  moreover have "\<not> ColH B' A' C'" 
    using assms(2) colH_permut_213 by blast
  moreover have "\<not> ColH C A B" 
    using assms(1) colH_permut_231 by blast
  ultimately show ?thesis 
    using congaH_existence_congH by blast
qed

lemma th19:
  assumes "\<not> ColH PO A B" and
    "\<not> ColH O1 A1 B1" and
    "\<not> ColH O2 A2 B2" and
    "CongaH A PO B A1 O1 B1" and
    "CongaH A PO B A2 O2 B2" 
  shows "CongaH A1 O1 B1 A2 O2 B2" 
proof -
  have "PO \<noteq> A" 
    using assms(1) colH_trivial112 by blast
  have "PO \<noteq> B" 
    using assms(1) colH_trivial121 by blast
  have "O1 \<noteq> A1" 
    using assms(2) colH_trivial112 by blast
  have "O1 \<noteq> B1" 
    using assms(2) colH_trivial121 by blast
  have "O2 \<noteq> A2" 
    using assms(3) colH_trivial112 by force
  have "O2 \<noteq> B2" 
    using assms(3) colH_trivial121 by blast
  {
    fix A1'
    assume "CongH O1 A1' PO A" and "outH O1 A1 A1'"
    {
      fix A2'
      assume "CongH O2 A2' PO A" and "outH O2 A2 A2'"
      {
        fix B1'
        assume "CongH O1 B1' PO B" and "outH O1 B1 B1'"
        {
          fix B2'
          assume "CongH O2 B2' PO B" and "outH O2 B2 B2'"
          have "O1 \<noteq> A1'" 
            using \<open>outH O1 A1 A1'\<close> outH_expand by blast
          have "O2 \<noteq> A2'" 
            using \<open>outH O2 A2 A2'\<close> outH_expand by auto
          have "O1 \<noteq> B1'" 
            using \<open>outH O1 B1 B1'\<close> out_distinct by auto
          have "O2 \<noteq> B2'" 
            using \<open>outH O2 B2 B2'\<close> outH_expand by blast
          {
            assume "ColH O1 A1' B1'"
            have "ColH O1 A1 A1'" 
              by (simp add: \<open>outH O1 A1 A1'\<close> outH_expand)
            have "ColH O1 B1 B1'" 
              by (simp add: \<open>outH O1 B1 B1'\<close> outH_expand)
            hence "ColH O1 A1 B1" 
              by (metis colH_trivial121 \<open>ColH O1 A1 A1'\<close> \<open>ColH O1 A1' B1'\<close> 
                  \<open>ColH O1 B1 B1'\<close> \<open>O1 \<noteq> A1'\<close> \<open>O1 \<noteq> B1'\<close> colH_permut_231 inter_uniquenessH)
            hence False 
              using assms(2) by blast
          }
          have "ColH O2 A2 A2'" 
            using \<open>outH O2 A2 A2'\<close> outH_expand by blast
          have "ColH O2 B2 B2'" 
            by (simp add: \<open>outH O2 B2 B2'\<close> outH_expand)
          hence "\<not> ColH O2 A2' B2'" 
            by (metis \<open>ColH O2 A2 A2'\<close> \<open>O2 \<noteq> A2'\<close> \<open>O2 \<noteq> B2'\<close> assms(3) 
                colH_permut_312 colH_trans colH_trivial122)
          have "CongH A B A1' B1'" 
          proof -
            have "CongH PO A O1 A1'" 
              using \<open>CongH O1 A1' PO A\<close> \<open>O1 \<noteq> A1'\<close> \<open>PO \<noteq> A\<close> congH_perms by blast
            moreover have "CongH PO B O1 B1'" 
              by (simp add: \<open>CongH O1 B1' PO B\<close> \<open>O1 \<noteq> B1'\<close> congH_sym)
            moreover have "CongaH A PO B A1' O1 B1'" 
              using \<open>PO \<noteq> A\<close> \<open>PO \<noteq> B\<close> \<open>outH O1 A1 A1'\<close> \<open>outH O1 B1 B1'\<close> 
                assms(4) conga_out_conga outH_trivial by blast
            ultimately show ?thesis 
              using assms(1) th12 \<open>ColH O1 A1' B1' \<Longrightarrow> False\<close> by blast
          qed
          have "CongH A B A2' B2'" 
          proof -
            have "CongH PO A O2 A2'" 
              using \<open>CongH O2 A2' PO A\<close> \<open>O2 \<noteq> A2'\<close> congH_sym by auto
            moreover have "CongH PO B O2 B2'" 
              by (simp add: \<open>CongH O2 B2' PO B\<close> \<open>O2 \<noteq> B2'\<close> congH_sym)
            moreover have "CongaH A PO B A2' O2 B2'" 
              using \<open>PO \<noteq> A\<close> \<open>PO \<noteq> B\<close> \<open>outH O2 A2 A2'\<close> \<open>outH O2 B2 B2'\<close> 
                assms(5) conga_out_conga outH_trivial by blast
            ultimately show ?thesis 
              using  assms(1) th12 \<open>\<not> ColH O2 A2' B2'\<close> by blast
          qed
          have "CongH A1' B1' A2' B2'" 
            using \<open>CongH A B A1' B1'\<close> \<open>CongH A B A2' B2'\<close> cong_pseudo_transitivity by blast
          have "CongaH A1' O1 B1' A2' O2 B2'" 
          proof -
            have "CongH O1 A1' O2 A2'" 
              by (meson \<open>CongH O1 A1' PO A\<close> \<open>CongH O2 A2' PO A\<close> \<open>O1 \<noteq> A1'\<close> 
                  \<open>O2 \<noteq> A2'\<close> congH_sym cong_pseudo_transitivity)
            moreover have "CongH O1 B1' O2 B2'" 
              by (meson \<open>CongH O1 B1' PO B\<close> \<open>CongH O2 B2' PO B\<close> \<open>O1 \<noteq> B1'\<close> 
                  \<open>O2 \<noteq> B2'\<close> congH_sym cong_pseudo_transitivity)
            ultimately show ?thesis 
              using th18_aux \<open>CongH A1' B1' A2' B2'\<close> \<open>ColH O1 A1' B1' \<Longrightarrow> False\<close> 
                \<open>\<not> ColH O2 A2' B2'\<close> by blast
          qed
          hence "CongaH A1 O1 B1 A2 O2 B2" 
            using \<open>O1 \<noteq> A1'\<close> \<open>O1 \<noteq> B1'\<close> \<open>O2 \<noteq> A2'\<close> \<open>O2 \<noteq> B2'\<close> \<open>outH O1 A1 A1'\<close> 
              \<open>outH O1 B1 B1'\<close> \<open>outH O2 A2 A2'\<close> \<open>outH O2 B2 B2'\<close> conga_out_conga outH_sym by blast
        }
        hence "CongaH A1 O1 B1 A2 O2 B2" 
          using \<open>O2 \<noteq> B2\<close> \<open>PO \<noteq> B\<close> out_construction by blast
      }
      hence "CongaH A1 O1 B1 A2 O2 B2" 
        using \<open>O1 \<noteq> B1\<close> \<open>PO \<noteq> B\<close> out_construction by blast
    }
    hence "CongaH A1 O1 B1 A2 O2 B2" 
      using \<open>O2 \<noteq> A2\<close> \<open>PO \<noteq> A\<close> out_construction by blast
  }
  thus ?thesis 
    using \<open>O1 \<noteq> A1\<close> \<open>PO \<noteq> A\<close> out_construction by force
qed


lemma congaH_sym:
  assumes "\<not> ColH A B C" and
    "\<not> ColH D E F" and
    "CongaH A B C D E F"
  shows "CongaH D E F A B C" 
  by (meson assms(1) assms(2) assms(3) colH_permut_213 conga_refl th19)

lemma congaH_commr:
  assumes "\<not> ColH A B C" and
    "\<not> ColH D E F" and
    "CongaH A B C D E F"
  shows "CongaH A B C F E D" 
  by (metis assms(1) assms(2) assms(3) colH_permut_213 colH_permut_312 conga_comm th19)

lemma cong_preserves_col:
  assumes "BetH A B C" and
    "CongH A B A' B'" and
    "CongH B C B' C'" and
    "CongH A C A' C'" 
  shows "ColH A' B' C'" 
proof -
  have "ColH A B C" 
    by (simp add: assms(1) betH_colH)
  have "A \<noteq> B" 
    using assms(1) betH_distincts by blast
  have "C \<noteq> B" 
    using assms(1) betH_distincts by blast
  {
    assume "\<not> ColH A' B' C'"
    {
      assume "A' = C'" 
      hence False 
        using \<open>\<not> ColH A' B' C'\<close> colH_trivial121 by blast
    }
    then obtain B'' where "CongH A' B'' A B" and "outH A' C' B''" 
      using \<open>A \<noteq> B\<close> out_construction by blast
    hence "ColH A' C' B''" 
      using outH_expand by blast
    have "A' \<noteq> B''" 
      using \<open>outH A' C' B''\<close> out_distinct by blast
    have "outH A' B'' C'" 
      by (simp add: \<open>A' \<noteq> B''\<close> \<open>outH A' C' B''\<close> outH_sym)
    hence "BetH A' B'' C'" 
      using \<open>A' \<noteq> B''\<close> \<open>CongH A' B'' A B\<close> assms(1) assms(4) 
        betH_congH3_outH_betH congH_sym by blast
    have "A' \<noteq> B'" 
      using \<open>\<not> ColH A' B' C'\<close> colH_trivial112 by auto
    obtain C'' where "BetH A' B' C''" and "CongH B' C'' B C" 
      using \<open>A' \<noteq> B'\<close> \<open>C \<noteq> B\<close> segment_constructionH by metis
    hence "ColH A' B' C''" 
      using betH_colH by force
    have "B' \<noteq> C''" 
      using \<open>BetH A' B' C''\<close> betH_distincts by blast
    have "A' \<noteq> C''" 
      using \<open>BetH A' B' C''\<close> not_betH121 by blast
    have "CongH B C B'' C'" 
      using \<open>A' \<noteq> B''\<close> \<open>BetH A' B'' C'\<close> \<open>CongH A' B'' A B\<close> assms(1) assms(4)
        congH_sym soustraction_betH by presburger
    have "CongH A' C'' A' C'" 
      by (meson \<open>B' \<noteq> C''\<close> \<open>BetH A' B' C''\<close> \<open>ColH A B C\<close> \<open>ColH A' B' C''\<close> 
          \<open>CongH B' C'' B C\<close> addition assms(1) assms(2) assms(4) bet_disjoint 
          congH_sym cong_pseudo_transitivity)
    have "\<not> ColH A' C'' C'" 
      using \<open>A' \<noteq> C''\<close> \<open>ColH A' B' C''\<close> \<open>\<not> ColH A' B' C'\<close> colH_permut_132 
        colH_trans colH_trivial121 by blast
    have "CongaH A' C'' C' A' C' C''" 
      by (simp add: \<open>CongH A' C'' A' C'\<close> \<open>\<not> ColH A' C'' C'\<close> isosceles_congaH)         
    have "\<not> ColH B' C'' C'" 
      by (meson \<open>B' \<noteq> C''\<close> \<open>ColH A' B' C''\<close> \<open>\<not> ColH A' B' C'\<close> colH_permut_231
          colH_trans colH_trivial121)
    have "CongaH B' C'' C' B' C' C''" 
      by (meson \<open>B' \<noteq> C''\<close> \<open>CongH B' C'' B C\<close> \<open>\<not> ColH B' C'' C'\<close> assms(3)
          congH_sym cong_pseudo_transitivity isosceles_congaH)
    have "CongaH A' C'' C' B' C'' C'" 
      using \<open>A' \<noteq> C''\<close> \<open>BetH A' B' C''\<close> \<open>ColH A' B' C''\<close> \<open>\<not> ColH A' B' C'\<close> 
        \<open>\<not> ColH A' C'' C'\<close> between_comm conga_out_conga conga_refl outH_def by blast
    have "CongaH A' C' C'' B' C' C''" 
      by (metis th19 \<open>CongaH A' C'' C' A' C' C''\<close> \<open>CongaH A' C'' C' B' C'' C'\<close> 
          \<open>CongaH B' C'' C' B' C' C''\<close> \<open>\<not> ColH A' C'' C'\<close> \<open>\<not> ColH B' C'' C'\<close>
          colH_permut_213 colH_permut_231)
    have "outH C' A' B'"
    proof -
      have "\<not> ColH B' C' C''" 
        using \<open>\<not> ColH B' C'' C'\<close> colH_permut_132 by blast
      moreover have "\<not> ColH A' C' C''" 
        using \<open>\<not> ColH A' C'' C'\<close> colH_permut_132 by blast
      moreover have "CongaH A' C' C'' C'' C' A'" 
        by (simp add: calculation(2) conga_comm)
      moreover have "CongaH A' C' C'' C'' C' B'" 
        using \<open>CongaH A' C' C'' B' C' C''\<close> calculation(1) calculation(2) 
          congaH_commr by blast
      moreover have "same_side' B' A' C' C''" 
        by (metis ColH_def \<open>BetH A' B' C''\<close> between_comm calculation(1) 
            colH_trivial122 outH_def out_same_side')
      moreover have "same_side' B' B' C' C''" 
        using calculation(1) colH_permut_312 same_side_prime_refl by blast
      ultimately show ?thesis 
        using cong_4_uniqueness by blast
    qed
    hence False 
      using \<open>\<not> ColH A' B' C'\<close> colH_permut_231 outH_col by blast
  }
  thus ?thesis by blast
qed

lemma cong_preserves_col_stronger:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "ColH A B C" and
    "CongH A B A' B'" and
    "CongH B C B' C'" and
    "CongH A C A' C'"
  shows "ColH A' B' C'" 
  by (metis ncolH_expand assms(1) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) between_one colH_permut_213 colH_permut_312 
      congH_permlr cong_preserves_col)

lemma betH_congH2__False:
  assumes "BetH A B C" and
    "BetH A' C' B'" and
    "CongH A B A' B'" and
    "CongH A C A' C'" 
  shows "False" 
proof -
  have "ColH A B C" 
    using assms(1) betH_colH by auto
  have "ColH A' C' B'" 
    by (simp add: assms(2) betH_colH)
  have "A \<noteq> B" 
    using assms(1) betH_distincts by blast
  have "C \<noteq> B" 
    using assms(1) betH_distincts by blast
  have "A' \<noteq> B'" 
    using assms(2) not_betH121 by force
  obtain C0 where "BetH A' B' C0" and "CongH B' C0 B C" 
    using \<open>A' \<noteq> B'\<close> \<open>C \<noteq> B\<close> segment_constructionH by metis
  hence "CongH A' C0 A C" 
    using \<open>A \<noteq> B\<close> addition_betH assms(1) assms(3) congH_sym by blast
  have "BetH A' C' C0" 
    using \<open>BetH A' B' C0\<close> assms(2) betH_trans0 by blast
  moreover have "CongH A' C' A' C0" 
    by (metis \<open>BetH A' B' C0\<close> \<open>CongH A' C0 A C\<close> assms(4) betH_distincts
        congH_sym cong_pseudo_transitivity)
  ultimately show ?thesis 
    by (simp add: betH_not_congH)
qed

lemma cong_preserves_bet: 
  assumes "A' \<noteq> B'" and
    "B' \<noteq> C'" and
    "A'\<noteq>C'" and
    "BetH A B C" and
    "CongH A B A' B'" and
    "CongH B C B' C'" and
    "CongH A C A' C'"
  shows "BetH A' B' C'" 
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
      assms(7) bet_cong3_bet cong_preserves_col)

lemma axiom_five_segmentsH:
  assumes "A \<noteq> D" and
    "A' \<noteq> D'" and
    "B \<noteq> D" and
    "B' \<noteq> D'" and
    "C \<noteq> D" and
    "C' \<noteq> D'" and
    "CongH A B A' B'" and
    "CongH B C B' C'" and
    "CongH A D A' D'" and
    "CongH B D B' D'" and
    "BetH A B C" and
    "BetH A' B' C'" and
    "A' \<noteq> D'"
  shows "CongH C D C' D'" 
proof -
  have "ColH A B C" 
    by (simp add: assms(11) betH_colH)
  have "ColH A' B' C'" 
    by (simp add: assms(12) betH_colH)
  have "A \<noteq> B" 
    using assms(11) betH_distincts by blast
  have "A \<noteq> C" 
    using assms(11) not_betH121 by blast
  have "A' \<noteq> B'" 
    using assms(12) betH_distincts by auto
  have "A' \<noteq> C'" 
    using assms(12) not_betH121 by blast
  have "C' \<noteq> B'" 
    using assms(12) betH_distincts by blast
  have "CongH A C A' C'" 
    using addition_betH assms(11) assms(12) assms(7) assms(8) by blast
  {
    assume "ColH A B D"
    hence "BetH A B D \<or> BetH B D A \<or> BetH B A D" 
      by (simp add: \<open>A \<noteq> B\<close> assms(1) assms(3) between_one)
    moreover
    {
      assume "BetH A B D"
      hence "BetH A' B' D'" 
        using \<open>A' \<noteq> B'\<close> assms(10) assms(2) assms(4) assms(7) assms(9) 
          cong_preserves_bet by blast
      hence "BetH A' D' C' \<or> BetH A' C' D'" 
        using  assms(12) assms(6) out2_out1 by auto
      moreover
      {
        assume "BetH A' D' C'" 
        hence "BetH A D C" 
          by (meson \<open>BetH A B D\<close> \<open>CongH A C A' C'\<close> assms(11) assms(5)
              assms(9) betH_congH2__False out2_out1)
        hence ?thesis 
          using \<open>BetH A' D' C'\<close> \<open>CongH A C A' C'\<close> assms(9) betH_colH 
            congH_permlr soustraction_betH by presburger
      }
      moreover
      {
        assume "BetH A' C' D'" 
        hence "BetH A C D" 
          by (meson \<open>BetH A B D\<close> \<open>CongH A C A' C'\<close> assms(11) assms(5)
              assms(9) betH_congH2__False out2_out1)
        hence ?thesis 
          using \<open>BetH A' C' D'\<close> \<open>CongH A C A' C'\<close> assms(9) 
            soustraction_betH by blast
      }
      ultimately have ?thesis 
        by blast
    }
    moreover
    {
      assume "BetH B D A"
      hence "BetH B' D' A'" 
        by (metis \<open>A' \<noteq> B'\<close> assms(10) assms(2) assms(4) assms(7)
            assms(9) congH_permlr cong_preserves_bet)
      hence "BetH C D A" 
        using betH_trans0 \<open>BetH B D A\<close> assms(11) between_comm by blast
      hence "BetH C' D' A'" 
        using betH_trans0 \<open>BetH B' D' A'\<close> assms(12) between_comm by blast
      have "BetH A D C" 
        by (simp add: \<open>BetH C D A\<close> between_comm)
      moreover have "BetH A' D' C'" 
        by (simp add: \<open>BetH C' D' A'\<close> between_comm)
      ultimately have ?thesis 
        using \<open>CongH A C A' C'\<close> assms(9) betH_expand congH_permlr 
          soustraction_betH by presburger
    }
    moreover
    {
      assume "BetH B A D"
      hence "BetH B' A' D'" 
        by (metis \<open>A' \<noteq> B'\<close> assms(10) assms(2) assms(4) assms(7) assms(9) 
            congH_permlr cong_preserves_bet)
      have "BetH C' B' D'" 
        using \<open>BetH B' A' D'\<close> assms(12) betH_trans between_comm by blast
      have "BetH C B D"         
        using \<open>BetH B A D\<close> assms(11) betH_trans between_comm by blast
      moreover have "CongH C B C' B'"         
        using \<open>C' \<noteq> B'\<close> assms(8) congH_permlr by presburger
      ultimately have ?thesis 
        using \<open>BetH C' B' D'\<close> assms(10) addition_betH by blast
    }
    ultimately have ?thesis 
      by blast
  }
  moreover
  {
    assume "\<not> ColH A B D" 
    hence "\<not> ColH A' B' D'" 
      using cong_preserves_col_stronger \<open>A \<noteq> B\<close> \<open>A' \<noteq> B'\<close> assms(1) assms(10)
        assms(2) assms(3) assms(4) assms(7) assms(9) congH_sym by blast
    hence "CongaH B A D B' A' D'" 
      using \<open>\<not> ColH A B D\<close> assms(10) assms(7) assms(9) th18_aux by blast
    have "\<not> ColH A C D" 
      using \<open>A \<noteq> C\<close> \<open>ColH A B C\<close> \<open>\<not> ColH A B D\<close> colH_permut_132 colH_trans 
        colH_trivial121 by blast
    moreover have "\<not> ColH A' C' D'" 
      using \<open>A' \<noteq> C'\<close> \<open>ColH A' B' C'\<close> \<open>\<not> ColH A' B' D'\<close> colH_permut_132 
        colH_trans colH_trivial121 by blast
    moreover have "CongaH C A D C' A' D'" 
      using \<open>CongaH B A D B' A' D'\<close> assms(1) assms(11) assms(12) assms(2)
        conga_out_conga outH_def by blast
    ultimately have ?thesis 
      using \<open>CongH A C A' C'\<close> assms(9) th12 by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma five_segment:
  assumes "Cong A B A' B'" and
    "Cong B C B' C'" and
    "Cong A D A' D'" and
    "Cong B D B' D'" and
    "Bet A B C" and
    "Bet A' B' C'" and
    "A \<noteq> B"
  shows "Cong C D C' D'" 
proof -
  {
    assume "BetH A B C"
    {
      assume "BetH A' B' C'"
      have "ColH A B C" 
        using \<open>BetH A B C\<close> betH_colH by blast
      have "ColH A' B' C'" 
        by (simp add: assms(6) bet_colH)
      have "C \<noteq> B" 
        using \<open>BetH A B C\<close> betH_distincts by blast
      have "A \<noteq> C" 
        using \<open>BetH A B C\<close> betH_distincts by blast
      have "A' \<noteq> B'" 
        using \<open>BetH A' B' C'\<close> betH_distincts by blast
      have "C' \<noteq> B'" 
        using \<open>BetH A' B' C'\<close> betH_distincts by blast
      have "A' \<noteq> C'" 
        using \<open>BetH A' B' C'\<close> betH_distincts by blast
      have "CongH A B A' B'" 
        using Cong_def \<open>A' \<noteq> B'\<close> assms(1) by presburger
      have "CongH B C B' C'" 
        using Cong_def \<open>C \<noteq> B\<close> assms(2) by blast
      have "CongH A D A' D' \<and> A \<noteq> D \<and> A' \<noteq> D' \<or> (A = D \<and> A' = D')" 
        using Cong_def assms(3) by force
      moreover
      have "CongH B D B' D' \<and> B \<noteq> D \<and> B'\<noteq> D' \<or> (B = D \<and> B' = D')" 
        using Cong_def assms(4) by presburger
      {
        assume "CongH A D A' D' \<and> A \<noteq> D \<and> A' \<noteq> D'"
        hence "CongH A D A' D'" 
          by blast
        have "A \<noteq> D" 
          by (simp add: \<open>CongH A D A' D' \<and> A \<noteq> D \<and> A' \<noteq> D'\<close>)
        have "A' \<noteq> D'" 
          by (simp add: \<open>CongH A D A' D' \<and> A \<noteq> D \<and> A' \<noteq> D'\<close>)
        {
          assume "CongH B D B' D' \<and> B \<noteq> D \<and> B'\<noteq> D'"
          hence "CongH B D B' D'" 
            by blast
          have "B \<noteq> D" 
            by (simp add: \<open>CongH B D B' D' \<and> B \<noteq> D \<and> B' \<noteq> D'\<close>)
          have "B'\<noteq> D'"
            by (simp add: \<open>CongH B D B' D' \<and> B \<noteq> D \<and> B' \<noteq> D'\<close>)
          {
            assume "C = D"
            have "CongH B' C' B' D'" 
              using \<open>C = D\<close> \<open>CongH B C B' C'\<close> \<open>CongH B D B' D' \<and> B \<noteq> D \<and> B' \<noteq> D'\<close> 
                cong_pseudo_transitivity by blast
            hence "C' = D'" 
              using \<open>A' \<noteq> B'\<close> \<open>A' \<noteq> D'\<close> \<open>B' \<noteq> D'\<close> \<open>BetH A B C\<close> \<open>BetH A' B' C'\<close> 
                \<open>C = D\<close> \<open>CongH A B A' B'\<close> \<open>CongH A D A' D'\<close> \<open>CongH B D B' D'\<close> 
                cong_preserves_bet construction_uniqueness by blast
            hence ?thesis 
              by (simp add: Cong_def \<open>C = D\<close>)
          }
          moreover
          {
            assume "C \<noteq> D"
            {
              assume "C' = D'"
              hence "CongH B D B C" 
                by (metis \<open>B \<noteq> D\<close> \<open>C \<noteq> B\<close> \<open>CongH B C B' C'\<close> \<open>CongH B D B' D'\<close>
                    congH_sym cong_pseudo_transitivity)
              have "BetH A B D" 
                using \<open>A \<noteq> D\<close> \<open>B \<noteq> D\<close> \<open>BetH A' B' C'\<close> \<open>C' = D'\<close> \<open>CongH A B A' B'\<close> 
                  \<open>CongH A D A' D'\<close> \<open>CongH B D B' D'\<close> assms(7) congH_sym cong_preserves_bet by presburger
              moreover have "CongH B C B D" 
                using \<open>B \<noteq> D\<close> \<open>CongH B D B C\<close> congH_sym by auto
              ultimately have "C = D" 
                using construction_uniqueness \<open>BetH A B C\<close> by presburger
              hence False 
                using \<open>C \<noteq> D\<close> by blast
            }
            hence "C' \<noteq> D'" 
              by blast          
            hence ?thesis 
              by (meson Cong_def \<open>BetH A B C\<close> \<open>BetH A' B' C'\<close> \<open>CongH A B A' B'\<close>
                  \<open>CongH A D A' D' \<and> A \<noteq> D \<and> A' \<noteq> D'\<close> \<open>CongH B C B' C'\<close> 
                  \<open>CongH B D B' D' \<and> B \<noteq> D \<and> B' \<noteq> D'\<close> axiom_five_segmentsH calculation)
          }
          ultimately have ?thesis 
            by blast
        }
        moreover
        {
          assume "B = D \<and> B' = D'" 
          hence ?thesis 
            using Cong_def \<open>C \<noteq> B\<close> \<open>C' \<noteq> B'\<close> \<open>CongH B C B' C'\<close> congH_permlr by presburger
        }
        ultimately have ?thesis 
          using \<open>CongH B D B' D' \<and> B \<noteq> D \<and> B' \<noteq> D' \<or> B = D \<and> B' = D'\<close> by fastforce
      }
      moreover
      {
        assume "A = D \<and> A' = D'"
        hence ?thesis 
          using Cong_def \<open>A \<noteq> C\<close> \<open>A' \<noteq> C'\<close> \<open>BetH A B C\<close> \<open>BetH A' B' C'\<close> 
            \<open>CongH A B A' B'\<close> \<open>CongH B C B' C'\<close> addition_betH congH_permlr by presburger
      }
      ultimately have ?thesis 
        by blast
    }
    moreover 
    {
      assume "A' = B'"
      hence ?thesis 
        using assms(1) assms(7) cong_identity by blast
    }
    moreover
    {
      assume "B' = C'"
      hence ?thesis 
        using Cong_def \<open>BetH A B C\<close> assms(2) betH_to_bet by auto
    }
    ultimately have ?thesis 
      using Bet_def assms(6) by blast
  }
  moreover 
  {
    assume "A = B"
    hence ?thesis 
      using assms(7) by blast
  }
  moreover
  {
    assume "B = C"
    hence ?thesis 
      using Cong_def assms(2) assms(4) by presburger
  }
  ultimately show ?thesis 
    using Bet_def assms(5) by blast
qed

lemma bet_comm:
  assumes "Bet A B C"
  shows "Bet C B A" 
  using Bet_def assms between_comm by presburger

lemma bet_trans:
  assumes "Bet A B D" and
    "Bet B C D"
  shows "Bet A B C" 
proof -
  {
    assume "BetH A B D"
    hence ?thesis 
      using Bet_def assms(2) betH_trans0 between_comm by blast
  }
  moreover
  {
    assume "A = B \<or> B = D"
    hence ?thesis 
      using Bet_def assms(2) bet_identity by blast
  }
  ultimately show ?thesis 
    using Bet_def assms(1) by blast
qed

lemma cong_transitivity:
  assumes "Cong A B E F" and 
    "Cong C D E F"
  shows "Cong A B C D" 
  using assms(1) assms(2) cong_sym cong_trans by blast

lemma cong_permT:
  shows "Cong A B B A" 
  by (metis Cong_def congH_perm)

lemma pasch_general_case:
  assumes "Bet A P C" and
    "Bet B Q C" and
    "A \<noteq> P" and
    "P \<noteq> C" and
    "B \<noteq> Q" and
    "Q \<noteq> C" and
    "\<not> (Bet A B C \<or> Bet B C A \<or> Bet C A B)"
  shows "\<exists> x. Bet P x B \<and> Bet Q x A"
proof (cases "A = B")
  case True
  thus ?thesis
    using Bet_def by auto
next
  case False
  {
    assume "B = C"
    hence ?thesis 
      using Bet_def assms(7) by presburger
  }
  moreover
  {
    assume "B \<noteq> C"
    {
      assume "A = C" 
      hence ?thesis 
        using Bet_def assms(7) by blast
    }
    moreover
    {
      assume "A \<noteq> C"
      have "ColH A P C" 
        by (simp add: assms(1) bet_colH)
      {
        assume "ColH B C P"
        hence "ColH A B C" 
          by (metis colH_permut_231 colH_trivial121 \<open>ColH A P C\<close> assms(4) inter_uniquenessH)
        hence False 
          by (metis Bet_def assms(7) between_comm between_one)
      }
      hence "\<not> ColH B C P" 
        by blast
      hence ?thesis 
        using assms(1) assms(2) inner_pasch_aux by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma lower_dim_l:
  shows "\<not> (Bet PP PQ PR \<or> Bet PQ PR PP \<or> Bet PR PP PQ)" 
  using bet_colH colH_permut_231 lower_dim_2 by blast

lemma ColH_bets:
  assumes "ColH A B C"
  shows "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
  by (metis Bet_def assms bet_comm between_one)

interpretation Interp_Gupta_of_Tarski_neutral_dimensionless: 
  Gupta_neutral_dimensionless
  where BetG = Bet and
    CongG = Cong and
    GPA = PP and
    GPB = PQ  and
    GPC = PR
proof 
  show "\<forall>a b. Cong a b b a" 
    by (simp add: cong_permT)
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
  show "\<forall>a b c. Bet a b c \<longrightarrow> Bet c b a" 
    using bet_comm by blast
  show "\<forall>a b c d. Bet a b d \<and> Bet b c d \<longrightarrow> Bet a b c" 
    using bet_trans by blast
  show "\<forall>a b c p q. Bet a p c \<and> Bet b q c \<and> a \<noteq> p \<and> c \<noteq> p \<and> b \<noteq> q \<and> 
          c \<noteq> q \<and> \<not> (Bet a b c \<or> Bet b c a \<or> Bet c a b) \<longrightarrow>
          (\<exists>x. Bet p x b \<and> Bet q x a)" 
    using pasch_general_case by auto
  show "\<not> (Bet PP PQ PR \<or> Bet PQ PR PP \<or> Bet PR PP PQ)" 
    using lower_dim_l by blast
qed

interpretation H_to_T : Tarski_neutral_dimensionless
  where Bet = Bet and
    Cong = Cong and
    TPA = PP and
    TPB = PQ  and
    TPC = PR
proof 
  show "\<forall>a b. Cong a b b a" 
    by (simp add: 
        Interp_Gupta_of_Tarski_neutral_dimensionless.cong_pseudo_reflexivityG)
  show "\<forall>a b p q r s. Cong a b p q \<and> Cong a b r s \<longrightarrow> Cong p q r s" 
    using cong_inner_transitivity by blast
  show "\<forall>a b c. Cong a b c c \<longrightarrow> a = b" 
    by (simp add: 
        Interp_Gupta_of_Tarski_neutral_dimensionless.cong_identityG)
  show "\<forall>a b c q. \<exists>x. Bet q a x \<and> Cong a x b c" 
    by (simp add: 
        Interp_Gupta_of_Tarski_neutral_dimensionless.segment_constructionG)
  show "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> Bet a b c \<and> Bet a' b' c' \<and>
Cong a b a' b' \<and> Cong b c b' c' \<and> Cong a d a' d' \<and> Cong b d b' d' \<longrightarrow>
Cong c d c' d'" 
    using Interp_Gupta_of_Tarski_neutral_dimensionless.five_segmentG by blast
  show "\<forall>a b. Bet a b a \<longrightarrow> a = b" 
    by (simp add: bet_identity)
  show "\<forall>a b c p q. Bet a p c \<and> Bet b q c \<longrightarrow> (\<exists>x. Bet p x b \<and> Bet q x a)" 
    using Interp_Gupta_of_Tarski_neutral_dimensionless.inner_paschT by blast
  show "\<not> Bet PP PQ PR \<and> \<not> Bet PQ PR PP \<and> \<not> Bet PR PP PQ" 
    using lower_dim_l by blast
qed

lemma MidH__Mid:
  assumes "M Midpoint A B"
  shows "H_to_T.Midpoint M A B"
proof -
  have "Bet A M B" 
    using Midpoint_def assms by blast
  moreover
  have "Cong A M M B" 
    using Midpoint_def assms by blast
  ultimately show ?thesis
    using H_to_T.Midpoint_def by blast
qed

lemma Mid__MidH:
  assumes "H_to_T.Midpoint M A B"
  shows "M Midpoint A B"
proof -
  have "Bet A M B" 
    using H_to_T.Midpoint_def assms by blast
  moreover
  have "Cong A M M B" 
    using H_to_T.Midpoint_def assms by blast
  ultimately show ?thesis
    by (simp add: Midpoint_def)
qed

lemma col_colh_1:
  assumes "H_to_T.Col A B C" 
  shows "ColH A B C" 
proof -
  have "Bet A B C \<or> Bet B C A \<or> Bet C A B"
    using assms H_to_T.Col_def by blast
  thus ?thesis 
    using bet_colH colH_permut_312 by blast
qed

lemma col_colh_2:
  assumes "ColH A B C" 
  shows "H_to_T.Col A B C"
proof -
  have "Bet A B C \<or> Bet B C A \<or> Bet C A B"
    by (simp add: ColH_bets assms)
  thus ?thesis 
    using H_to_T.Col_def by presburger
qed

lemma col_colh:
  shows "H_to_T.Col A B C \<longleftrightarrow> ColH A B C" 
  using col_colh_1 col_colh_2 by blast

lemma line_col:
  assumes "IsL l" and (**AJOUT**)
    "IncidL A l" and
    "IncidL B l" and 
    "IncidL C l"
  shows "H_to_T.Col A B C"
proof -
  have "ColH A B C" 
    using ColH_def assms(1) assms(2) assms(3) assms(4) by blast
  thus ?thesis
    by (simp add: col_colh_2)
qed

lemma bet__beth: 
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Bet A B C"
  shows "BetH A B C" 
  using Bet_def assms(1) assms(2) assms(3) by blast

lemma coplanar_plane0:
  assumes "ColH A B X" and 
    "ColH C D X"
  shows "\<exists> p. IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidP D p" 
proof -
  obtain l where "IsL l" and "IncidL A l" and "IncidL B l" and "IncidL X l" 
    using ColH_def assms(1) by blast
  obtain m where "IsL m" and "IncidL C m" and "IncidL D m" and "IncidL X m" 
    using ColH_def assms(2) by blast
  obtain Y where "X \<noteq> Y" and "IncidL Y l" 
    using \<open>IncidL X l\<close> other_point_on_line by blast
  {
    assume "EqL m l" 
    obtain Z where "\<not> ColH X Y Z" 
      using \<open>X \<noteq> Y\<close> ncolH_exists by blast
    obtain p where "IsP p" and "IncidP X p" and "IncidP Y p" and "IncidP Z p" 
      using \<open>\<not> ColH X Y Z\<close> plan_existence by blast
    hence "IncidLP l p" 
      using \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> \<open>X \<noteq> Y\<close> line_on_plane by blast
    hence ?thesis 
      using IncidLP_def IncidL_morphism \<open>EqL m l\<close> \<open>IncidL A l\<close> \<open>IncidL B l\<close> 
        \<open>IncidL C m\<close> \<open>IncidL D m\<close> \<open>IsL m\<close> by blast
  }
  moreover
  {
    assume "\<not> EqL m l" 
    obtain Z where "X \<noteq> Z" and "IncidL Z m" 
      using \<open>IncidL X m\<close> other_point_on_line by blast
    have "\<not> ColH X Y Z" 
      using IncidL_not_IncidL__not_colH \<open>IncidL X l\<close> \<open>IncidL X m\<close> \<open>IncidL Y l\<close> 
        \<open>IncidL Z m\<close> \<open>IsL l\<close> \<open>IsL m\<close> \<open>X \<noteq> Y\<close> \<open>X \<noteq> Z\<close> \<open>\<not> EqL m l\<close> line_uniqueness by blast
    then obtain p where "IsP p" and "IncidP X p" and "IncidP Y p" and "IncidP Z p" 
      using plan_existence by blast
    hence "IncidLP l p" 
      using \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> \<open>X \<noteq> Y\<close> line_on_plane by blast
    moreover have "IncidLP m p" 
      using \<open>IncidL X m\<close> \<open>IncidL Z m\<close> \<open>IncidP X p\<close> \<open>IncidP Z p\<close> \<open>IsL m\<close> 
        \<open>IsP p\<close> \<open>X \<noteq> Z\<close> line_on_plane by blast
    ultimately have ?thesis 
      using IncidLP_def \<open>IncidL A l\<close> \<open>IncidL B l\<close> \<open>IncidL C m\<close> \<open>IncidL D m\<close> by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma coplanar_plane1:
  assumes "Bet A B X \<or> Bet B X A \<or> Bet X A B" and
    "Bet C D X \<or> Bet D X C \<or> Bet X C D"
  shows "\<exists> p. IsP p \<and> IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidP D p" 
proof -
  have "ColH A B X"     
    by (meson assms(1) bet_colH colH_permut_312)
  moreover have "ColH C D X"     
    by (simp add: H_to_T.Col_def assms(2) col_colh_1)
  ultimately show ?thesis
    using Is_plane coplanar_plane0 by blast
qed

lemma coplanar_plane:
  assumes "H_to_T.Coplanar A B C D" 
  shows "\<exists> p. IsP p \<and> IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidP D p" 
proof -
  obtain X where H1: "(H_to_T.Col A B X \<and> H_to_T.Col C D X) \<or>
                         (H_to_T.Col A C X \<and> H_to_T.Col B D X) \<or>
                         (H_to_T.Col A D X \<and> H_to_T.Col B C X)" 
    using H_to_T.Coplanar_def assms by auto
  moreover have "(H_to_T.Col A B X \<and> H_to_T.Col C D X) \<longrightarrow> ?thesis" 
    using H_to_T.Col_def coplanar_plane1 by force
  moreover {
    assume "H_to_T.Col A C X" and
      "H_to_T.Col B D X"
    have "Bet A C X \<or> Bet C X A \<or> Bet X A C" 
      using H_to_T.Col_def \<open>H_to_T.Col A C X\<close> by presburger
    moreover have "Bet B D X \<or> Bet D X B \<or> Bet X B D" 
      using H1 H_to_T.Col_def \<open>H_to_T.Col B D X\<close> by blast
    ultimately have ?thesis 
      using coplanar_plane1 by blast
  }
  moreover {
    assume "H_to_T.Col A D X" and
      "H_to_T.Col B C X"
    have "Bet A D X \<or> Bet D X A \<or> Bet X A D" 
      using H_to_T.Col_def \<open>H_to_T.Col A D X\<close> by auto
    moreover have "Bet B C X \<or> Bet C X B \<or> Bet X B C" 
      using H_to_T.Col_def \<open>H_to_T.Col B C X\<close> by auto
    ultimately have ?thesis 
      using coplanar_plane1 by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma plane_coplanar:
  assumes "IncidP A p" and
    "IncidP B p" and
    "IncidP C p" and
    "IncidP D p"
  shows "H_to_T.Coplanar A B C D"
proof -
  {
    assume "ColH A B C"
    hence "H_to_T.Col A B C" 
      using col_colh_2 by blast
    hence ?thesis 
      using H_to_T.ncop__ncols by blast
  }
  moreover
  {
    assume "\<not> ColH A B C"
    hence "A \<noteq> B" 
      by (simp add: ncolH_distincts)
    obtain M where "M Midpoint A B"
      using H_to_T.midpoint_existence Mid__MidH by blast
    have "M \<noteq> A" 
      using Cong_def Hilbert_neutral_dimensionless_pre.Midpoint_def 
        \<open>A \<noteq> B\<close> \<open>M Midpoint A B\<close> by force
    have "M \<noteq> B" 
      using Midpoint_def Interp_Gupta_of_Tarski_neutral_dimensionless.cong_identityG 
        \<open>A \<noteq> B\<close> \<open>M Midpoint A B\<close> by blast
    have "ColH A B M" 
      using Midpoint_def \<open>M Midpoint A B\<close> bet_colH colH_permut_132 by blast
    then obtain m where "IsL m" and "IncidL A m" and "IncidL B m" and "IncidL M m" 
      using ColH_def by blast
    {
      assume "D = M" 
      hence ?thesis 
        using H_to_T.ncop__ncols col_colh_2 \<open>ColH A B M\<close> by blast
    }
    moreover
    {
      assume "D \<noteq> M" 
      obtain l where "IsL l" and" IncidL D l" and "IncidL M l" 
        using \<open>D \<noteq> M\<close> line_existence by blast
      {
        assume "IncidL A l" 
        hence "EqL m l" 
          using \<open>IncidL A m\<close> \<open>IncidL M l\<close> \<open>IncidL M m\<close> \<open>IsL l\<close> \<open>IsL m\<close> \<open>M \<noteq> A\<close> 
            line_uniqueness by presburger
        have "H_to_T.Col A B A \<and> H_to_T.Col C D A \<or> H_to_T.Col A C A \<and> H_to_T.Col B D A \<or> 
              H_to_T.Col A D A \<and> H_to_T.Col B C A" 
          by (meson ColH_def H_to_T.not_col_distincts IncidL_morphism Is_line 
              \<open>EqL m l\<close> \<open>IncidL A l\<close> \<open>IncidL B m\<close> \<open>IncidL D l\<close> col_colh_2)
        hence ?thesis 
          using H_to_T.Coplanar_def by blast
      }
      moreover
      {
        assume "\<not> IncidL A l"
        {
          assume "IncidL B l" 
          hence "EqL l m" 
            using \<open>IncidL B m\<close> \<open>IncidL M l\<close> \<open>IncidL M m\<close> \<open>IsL l\<close> \<open>IsL m\<close> 
              \<open>M \<noteq> B\<close> line_uniqueness by blast
          hence False 
            using \<open>IncidL A m\<close> \<open>IncidL B l\<close> \<open>IncidL B m\<close> \<open>IncidL M l\<close> 
              \<open>IncidL M m\<close> \<open>M \<noteq> B\<close> \<open>\<not> IncidL A l\<close> inter_incid_uniquenessH by blast
        }
        {
          assume "IncidL C l" 
          hence "H_to_T.Col A B M \<and> H_to_T.Col C D M \<or> H_to_T.Col A C M \<and> H_to_T.Col B D M \<or> 
                    H_to_T.Col A D M \<and> H_to_T.Col B C M" 
            using Hilbert_neutral_dimensionless_pre.ColH_def \<open>ColH A B M\<close> 
              \<open>IncidL D l\<close> \<open>IncidL M l\<close> \<open>IsL l\<close> col_colh by fastforce
          hence ?thesis 
            using H_to_T.Coplanar_def by blast
        }
        moreover
        {
          assume "\<not> IncidL C l"
          have "IncidP M p" 
            using \<open>A \<noteq> B\<close> \<open>ColH A B M\<close> assms(1) assms(2) line_on_plane' by blast
          have
            "\<not> ColH A B C \<and> IsL l \<and> IsP p \<and> IncidP A p \<and> IncidP B p \<and> 
             IncidP C p \<and> IncidLP l p \<and> \<not> IncidL C l \<and> (cut l A B)
        \<longrightarrow>
        (cut l A C) \<or> (cut l B C)" 
            using pasch by blast
          moreover
          {
            assume "cut l A C"
            then obtain I where "IncidL I l" and "BetH A I C" 
              using local.cut_def by blast
            {
              assume "H_to_T.Col I A B"
              have "A \<noteq> I" 
                using \<open>IncidL I l\<close> \<open>\<not> IncidL A l\<close> by auto
              moreover have "ColH A I A" 
                by (simp add: colH_trivial121)
              moreover have "ColH A I C" 
                by (simp add: \<open>BetH A I C\<close> between_col)
              ultimately have False
                using \<open>\<not> ColH A B C\<close> colH_trans \<open>H_to_T.Col I A B\<close> 
                  colH_permut_213 col_colh_1 by blast
            }
            hence "\<not> H_to_T.Col I A B" 
              by blast
            moreover have "H_to_T.Coplanar I A B C" 
              using H_to_T.bet__coplanar H_to_T.ncoplanar_perm_7 \<open>BetH A I C\<close>
                betH_to_bet by blast
            moreover 
            have "H_to_T.Col I D M" 
              using ColH_def \<open>IncidL D l\<close> \<open>IncidL I l\<close> \<open>IncidL M l\<close> \<open>IsL l\<close> col_colh by auto
            have "H_to_T.Col A B M" 
              using \<open>ColH A B M\<close> col_colh_2 by fastforce
            hence "H_to_T.Col I A M \<and> H_to_T.Col B D M \<or> H_to_T.Col I B M \<and> H_to_T.Col A D M \<or>
                    H_to_T.Col I D M \<and> H_to_T.Col A B M" 
              using \<open>H_to_T.Col I D M\<close> by auto
            hence "H_to_T.Coplanar I A B D" 
              using H_to_T.Coplanar_def by blast
            ultimately have ?thesis 
              using H_to_T.coplanar_trans_1 by blast
          }
          moreover 
          {
            assume "cut l B C"
            then obtain I where "IncidL I l" and "BetH B I C" 
              using local.cut_def by blast
            {
              assume "H_to_T.Col I B A"
              have "B \<noteq> I" 
                using \<open>IncidL B l \<Longrightarrow> False\<close> \<open>IncidL I l\<close> by fastforce
              moreover have "ColH B I A" 
                using \<open>H_to_T.Col I B A\<close> colH_permut_213 col_colh by blast
              moreover have "ColH B I B" 
                by (simp add: colH_trivial121)
              ultimately have False
                using \<open>BetH B I C\<close> \<open>\<not> ColH A B C\<close> between_col colH_trans by blast
            }
            hence "\<not> H_to_T.Col I B A" 
              by blast
            moreover have "H_to_T.Coplanar I B A C" 
              using H_to_T.bet__coplanar H_to_T.ncoplanar_perm_7 \<open>BetH B I C\<close>
                betH_to_bet by blast
            moreover 
            have "H_to_T.Col I D M" 
              using ColH_def \<open>IncidL D l\<close> \<open>IncidL I l\<close> \<open>IncidL M l\<close> \<open>IsL l\<close> col_colh by auto
            have "H_to_T.Col B A M" 
              by (metis Bet_def H_to_T.Col_def \<open>ColH A B M\<close> between_comm between_one)
            hence "H_to_T.Col I B M \<and> H_to_T.Col A D M \<or> H_to_T.Col I A M \<and> H_to_T.Col B D M \<or>
                    H_to_T.Col I D M \<and> H_to_T.Col B A M" 
              using \<open>H_to_T.Col I D M\<close> by auto
            hence "H_to_T.Coplanar I B A D" 
              using H_to_T.Coplanar_def by blast
            ultimately have ?thesis 
              using H_to_T.coplanar_trans_1 H_to_T.ncoplanar_perm_6 by blast
          }
          ultimately have ?thesis                 
            by (metis (mono_tags, lifting) Bet_def line_on_plane Is_plane Midpoint_def
                \<open>ColH A B C \<Longrightarrow> H_to_T.Coplanar A B C D\<close> \<open>D = M \<Longrightarrow> H_to_T.Coplanar A B C D\<close>
                \<open>IncidL B l \<Longrightarrow> False\<close> \<open>IncidL D l\<close> \<open>IncidL M l\<close> \<open>IncidP M p\<close> \<open>IsL l\<close>
                \<open>M Midpoint A B\<close> \<open>\<not> IncidL A l\<close> \<open>\<not> IncidL C l\<close> assms(1) assms(2)
                assms(3) assms(4) local.cut_def)
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

lemma pars__para:
  assumes "IncidL A l" and
    "IncidL B l" and
    "IncidL C m" and
    "IncidL D m" and
    "H_to_T.ParStrict A B C D"
  shows "Para l m" 
proof -
  have "A \<noteq> B" 
    using H_to_T.par_strict_neq1 assms(5) by auto
  have "C \<noteq> D" 
    using H_to_T.par_strict_distinct assms(5) by presburger
  have "IsL l" 
    using Is_line assms(1) by blast
  moreover have "IsL m" 
    using Is_line assms(4) by blast
  moreover 
  {
    fix X
    assume "IncidL X l" and "IncidL X m"
    hence "H_to_T.Col X A B" 
      using assms(1) assms(2) Is_line line_col by blast
    moreover have "H_to_T.Col X C D" 
      using assms(1) assms(2) Is_line line_col \<open>IncidL X m\<close> assms(3) assms(4) by auto
    ultimately have False 
      using H_to_T.par_not_col assms(5) by blast
  }
  moreover
  obtain p where "IsP p" and "IncidP A p" and "IncidP B p" and "IncidP C p" and "IncidP D p" 
    using H_to_T.pars__coplanar assms(5) coplanar_plane by blast
  have "\<exists> p. IncidLP l p \<and> IncidLP m p" 
  proof -
    have "IncidLP l p" 
      using \<open>A \<noteq> B\<close> \<open>IncidP A p\<close> \<open>IncidP B p\<close> \<open>IsP p\<close> assms(1) assms(2) 
        calculation(1) line_on_plane by blast
    moreover have "IncidLP m p" 
      using \<open>C \<noteq> D\<close> \<open>IncidP C p\<close> \<open>IncidP D p\<close> \<open>IsP p\<close> assms(3) assms(4) 
        line_on_plane \<open>IsL m\<close> by blast
    ultimately show ?thesis 
      by blast
  qed
  ultimately show ?thesis 
    using Para_def by blast
qed

lemma par__or_eq_para:
  assumes "IncidL A l" and
    "IncidL B l" and
    "IncidL C m" and
    "IncidL D m" and
    "H_to_T.Par A B C D"
  shows "Para l m \<or> EqL l m" 
proof -
  {
    assume "H_to_T.ParStrict A B C D" 
    hence ?thesis 
      using assms(1) assms(2) assms(3) assms(4) pars__para by blast
  }
  moreover
  {
    assume "A \<noteq> B" and
      "C \<noteq> D" and
      "H_to_T.Col A C D" and
      "H_to_T.Col B C D"
    hence ?thesis 
      by (meson IncidL_not_IncidL__not_colH Is_line assms(1) assms(2) assms(3) 
          assms(4) colH_permut_231 col_colh_1 line_uniqueness)
  }
  ultimately show ?thesis 
    using H_to_T.Par_def assms(5) by presburger
qed

lemma tarski_upper_dim:
  assumes 
    plane_intersection_assms: "\<forall> A p q. IsP p \<and> IsP q \<and> IncidP A p \<and> IncidP A q 
                                \<longrightarrow> (\<exists> B. IncidP B p \<and> IncidP B q \<and> A \<noteq> B)" and 
    lower_dim_3_assms: "\<not> (\<exists> p. IsP p \<and> IncidP HS1 p \<and> IncidP HS2 p \<and> 
                                IncidP HS3 p \<and> IncidP HS4 p)" and
    "P \<noteq> Q" and
    "Q \<noteq> R" and
    "P \<noteq> R" and
    "Cong A P A Q" and
    "Cong B P B Q" and
    "Cong C P C Q" and
    "Cong A P A R" and
    "Cong B P B R" and
    "Cong C P C R"
  shows "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
proof -
  have "H_to_T.upper_dim_3_axiom \<longrightarrow> ?thesis" 
    using H_to_T.upper_dim_3_axiom_def assms(10) assms(11) assms(3) assms(4) 
      assms(5) assms(6) assms(7) assms(8) assms(9) by blast
  moreover
  have "H_to_T.plane_intersection_axiom \<longrightarrow> H_to_T.upper_dim_3_axiom" 
    using H_to_T.upper_dim_3_equivalent_axioms by force
  moreover
  {
    fix A B C D E F P
    assume "H_to_T.Coplanar A B C P" and
      "H_to_T.Coplanar D E F P"
    obtain p where "IsP p" and "IncidP A p" and "IncidP B p" and "IncidP C p" and "IncidP P p" 
      using \<open>H_to_T.Coplanar A B C P\<close> coplanar_plane by blast
    obtain q where "IsP q" and "IncidP D q" and "IncidP E q" and "IncidP F q" and "IncidP P q" 
      using \<open>H_to_T.Coplanar D E F P\<close> coplanar_plane by blast
    obtain Q where "IncidP Q p" and "IncidP Q q" and "P \<noteq> Q" 
      using plane_intersection_assms Is_plane \<open>IncidP P p\<close> \<open>IncidP P q\<close> by blast   
    have "H_to_T.Coplanar A B C Q" 
      using \<open>IncidP A p\<close> \<open>IncidP B p\<close> \<open>IncidP C p\<close> \<open>IncidP Q p\<close> plane_coplanar by force
    moreover have "H_to_T.Coplanar D E F Q" 
      using \<open>IncidP D q\<close> \<open>IncidP E q\<close> \<open>IncidP F q\<close> \<open>IncidP Q q\<close> plane_coplanar by force
    ultimately have "\<exists> Q. H_to_T.Coplanar A B C Q \<and> H_to_T.Coplanar D E F Q \<and> P \<noteq> Q" 
      using \<open>P \<noteq> Q\<close> by blast
  }
  hence "H_to_T.plane_intersection_axiom" 
    using H_to_T.plane_intersection_axiom_def by force
  ultimately show ?thesis
    by simp
qed

lemma Col__ColH:
  assumes "H_to_T.Col A B C"
  shows "ColH A B C" 
  using assms col_colh by blast

lemma ColH__Col: 
  assumes "ColH A B C"
  shows "H_to_T.Col A B C" 
  using assms ColH_bets col_colh by blast

lemma playfair_s_postulateH: 
  assumes euclid_uniqueness: "\<forall> l P m1 m2. IsL l \<and> IsL m1 \<and> IsL m2 \<and>
     \<not> IncidL P l \<and> Para l m1 \<and> IncidL P m1 \<and> Para l m2 \<and> IncidL P m2 \<longrightarrow>
     EqL m1 m2"
  shows "H_to_T.playfair_s_postulate" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume "H_to_T.Par A1 A2 B1 B2" and
      "H_to_T.Col P B1 B2" and
      "H_to_T.Par A1 A2 C1 C2" and
      "H_to_T.Col P C1 C2"
    have "A1 \<noteq> A2" 
      using H_to_T.par_distinct \<open>H_to_T.Par A1 A2 B1 B2\<close> by blast
    then obtain l where "IsL l" and "IncidL A1 l" and "IncidL A2 l" 
      using line_existence by fastforce
    have "B1 \<noteq> B2" 
      using H_to_T.par_distinct \<open>H_to_T.Par A1 A2 B1 B2\<close> by blast
    then obtain m1 where "IsL m1" and "IncidL B1 m1" and "IncidL B2 m1" 
      using line_existence by fastforce
    have "C1 \<noteq> C2" 
      using H_to_T.par_distinct \<open>H_to_T.Par A1 A2 C1 C2\<close> by blast
    then obtain m2 where "IsL m2" and "IncidL C1 m2" and "IncidL C2 m2" 
      using line_existence by fastforce
    {
      assume "IncidL P l" 
      have "ColH A1 A2 P" 
        using ColH_def Is_line \<open>IncidL A1 l\<close> \<open>IncidL A2 l\<close> \<open>IncidL P l\<close> by blast
      hence "H_to_T.Col A1 A2 P" 
        by (simp add: col_colh)
      have "H_to_T.Col A1 B1 B2" 
        by (metis H_to_T.col3 H_to_T.not_col_distincts H_to_T.not_strict_par1
            H_to_T.not_strict_par2 \<open>A1 \<noteq> A2\<close> \<open>H_to_T.Col A1 A2 P\<close> \<open>H_to_T.Col P B1 B2\<close>
            \<open>H_to_T.Par A1 A2 B1 B2\<close>)
      have "H_to_T.Col A2 B1 B2"
        using H_to_T.Par_def H_to_T.not_col_permutation_2 H_to_T.par_strict_not_col_3 
          \<open>H_to_T.Col A1 B1 B2\<close> \<open>H_to_T.Par A1 A2 B1 B2\<close> by blast
      have "H_to_T.ParStrict A1 A2 C1 C2 \<longrightarrow> H_to_T.Col C1 B1 B2 \<and> H_to_T.Col C2 B1 B2" 
        using H_to_T.Col_cases H_to_T.par_not_col \<open>H_to_T.Col A1 A2 P\<close> 
          \<open>H_to_T.Col P C1 C2\<close> by blast
      moreover have "A1 \<noteq> A2 \<and> C1 \<noteq> C2 \<and> H_to_T.Col A1 C1 C2 \<and> H_to_T.Col A2 C1 C2 
                       \<longrightarrow> H_to_T.Col C1 B1 B2 \<and> H_to_T.Col C2 B1 B2" 
      proof -
        have "A1 \<noteq> A2 \<and> C1 \<noteq> C2 \<and> H_to_T.Col A1 C1 C2 \<and> H_to_T.Col A2 C1 C2 
               \<longrightarrow> H_to_T.Col C1 B1 B2" 
          by (meson H_to_T.col_permutation_1 H_to_T.l6_21 \<open>H_to_T.Col A1 B1 B2\<close>
              \<open>H_to_T.Col A2 B1 B2\<close>)
        moreover have "A1 \<noteq> A2 \<and> C1 \<noteq> C2 \<and> H_to_T.Col A1 C1 C2 \<and> H_to_T.Col A2 C1 C2 
                         \<longrightarrow> H_to_T.Col C2 B1 B2"
          using H_to_T.col_permutation_1 H_to_T.l6_21 
          by (metis H_to_T.col_permutation_1 H_to_T.colx \<open>H_to_T.Col A1 B1 B2\<close>
              \<open>H_to_T.Col A2 B1 B2\<close> calculation)
        ultimately show ?thesis
          by blast
      qed
      ultimately have "H_to_T.Col C1 B1 B2 \<and> H_to_T.Col C2 B1 B2" 
        using H_to_T.Par_def \<open>H_to_T.Par A1 A2 C1 C2\<close> by force
    }
    moreover
    {
      assume "\<not> IncidL P l" 
      have "\<not> ColH A1 A2 P" 
        using IncidL_not_IncidL__not_colH \<open>A1 \<noteq> A2\<close> \<open>IncidL A1 l\<close> \<open>IncidL A2 l\<close> 
          \<open>\<not> IncidL P l\<close> by blast
      hence "\<not> H_to_T.Col A1 A2 P" 
        using col_colh by blast
      have "Para l m1" 
      proof -
        have "H_to_T.ParStrict A1 A2 B1 B2" 
          using H_to_T.col_permutation_2 H_to_T.par_not_col_strict 
            \<open>H_to_T.Col P B1 B2\<close> \<open>H_to_T.Par A1 A2 B1 B2\<close> \<open>\<not> H_to_T.Col A1 A2 P\<close> by blast
        moreover have "H_to_T.ParStrict A1 A2 B1 B2 \<longrightarrow> Para l m1" 
          using \<open>IncidL A1 l\<close> \<open>IncidL A2 l\<close> \<open>IncidL B1 m1\<close> \<open>IncidL B2 m1\<close> pars__para by blast
        ultimately show ?thesis 
          by blast
      qed
      have "Para l m2" 
      proof -
        have "H_to_T.ParStrict A1 A2 C1 C2" 
          using H_to_T.not_col_permutation_2 H_to_T.par_not_col_strict 
            \<open>H_to_T.Col P C1 C2\<close> \<open>H_to_T.Par A1 A2 C1 C2\<close> \<open>\<not> H_to_T.Col A1 A2 P\<close> by blast
        moreover have "H_to_T.ParStrict A1 A2 C1 C2 \<longrightarrow> Para l m2" 
          using \<open>IncidL A1 l\<close> \<open>IncidL A2 l\<close> \<open>IncidL C1 m2\<close> \<open>IncidL C2 m2\<close> pars__para by auto
        ultimately show ?thesis 
          by blast
      qed
      have "IncidL P m1" 
        using H_to_T.not_col_permutation_2 IncidL_not_IncidL__not_colH \<open>B1 \<noteq> B2\<close> 
          \<open>H_to_T.Col P B1 B2\<close> \<open>IncidL B1 m1\<close> \<open>IncidL B2 m1\<close> col_colh by blast
      have "IncidL P m2" 
        using H_to_T.not_col_permutation_2 IncidL_not_IncidL__not_colH \<open>C1 \<noteq> C2\<close> 
          \<open>H_to_T.Col P C1 C2\<close> \<open>IncidL C1 m2\<close> \<open>IncidL C2 m2\<close> col_colh by blast
      have "EqL m1 m2" 
        using \<open>IncidL P m1\<close> \<open>IncidL P m2\<close> \<open>IsL l\<close> \<open>IsL m1\<close> \<open>IsL m2\<close> \<open>Para l m1\<close> 
          \<open>Para l m2\<close> \<open>\<not> IncidL P l\<close> assms by blast
      hence "H_to_T.Col C1 B1 B2 \<and> H_to_T.Col C2 B1 B2" 
        by (meson IncidL_morphism \<open>IncidL B1 m1\<close> \<open>IncidL B2 m1\<close> \<open>IncidL C1 m2\<close> 
            \<open>IncidL C2 m2\<close> \<open>IsL m1\<close> \<open>IsL m2\<close> line_col)
    }
    ultimately have "H_to_T.Col C1 B1 B2 \<and> H_to_T.Col C2 B1 B2" 
      by blast
  }
  thus ?thesis 
    using H_to_T.playfair_s_postulate_def by blast       
qed

lemma tarski_s_euclid_aux: 
  assumes euclid_uniqueness: "\<forall> l P m1 m2. IsL l \<and> IsL m1 \<and> IsL m2 \<and> 
     \<not> IncidL P l \<and> Para l m1 \<and> IncidL P m1 \<and> Para l m2 \<and> IncidL P m2 \<longrightarrow>
     EqL m1 m2"
  shows "H_to_T.tarski_s_parallel_postulate" 
proof -
  have "H_to_T.playfair_s_postulate \<longrightarrow> H_to_T.tarski_s_parallel_postulate" 
    using H_to_T.InterAx5 H_to_T.Postulate01_def H_to_T.Postulate02_def by blast
  moreover
  have "H_to_T.playfair_s_postulate" 
    using playfair_s_postulateH assms(1) by blast
  ultimately show ?thesis 
    by blast
qed

lemma tarski_s_euclid: 
  assumes euclid_uniqueness: "\<forall> l P m1 m2. IsL l \<and> IsL m1 \<and> IsL m2 \<and>
           \<not> IncidL P l \<and> Para l m1 \<and> IncidL P m1 \<and> Para l m2 \<and> IncidL P m2 \<longrightarrow>
           EqL m1 m2"
  shows 
    "\<forall>A B C D T. Bet A D T \<and> Bet B D C \<and> A \<noteq> D \<longrightarrow> (\<exists>X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y)"
  using assms(1) tarski_s_euclid_aux H_to_T.tarski_s_parallel_postulate_def by blast

end

context Hilbert_neutral_2D

begin

lemma plane_separation_2D:
  assumes "\<not> ColH A X Y" and
    "\<not> ColH B X Y" 
  shows "cut' A B X Y \<or> same_side' A B X Y" 
proof -
  have "X \<noteq> Y" 
    using assms(2) colH_trivial122 by blast
  obtain l where "IsL l" and "IncidL X l" and "IncidL Y l" 
    using \<open>X \<noteq> Y\<close> line_existence by blast
  obtain C where "cut l A C" 
    using ColH_def \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(1) cut_exists by blast
  {
    assume "A = B"
    hence "same_side' A B X Y" 
      using assms(1) colH_permut_312 same_side_prime_refl by blast
    hence ?thesis 
      by blast
  }
  moreover
  {
    assume "A \<noteq> B"
    have "A \<noteq> C" 
      using \<open>local.cut l A C\<close> cut_distinct by blast
    {
      assume "B = C"
      obtain m where "IsL m" and "IncidL X m" and "IncidL Y m" 
        using Is_line \<open>IncidL X l\<close> \<open>IncidL Y l\<close> by blast
      obtain I where "IncidL I l" and "BetH A I C" 
        using \<open>local.cut l A C\<close> local.cut_def by blast
      {
        fix m
        assume "IsL m" and "IncidL X m" and "IncidL Y m"
        hence "cut m A B" 
          by (metis ColH_def \<open>B = C\<close> \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>X \<noteq> Y\<close> 
              \<open>\<And>thesis. (\<And>I. \<lbrakk>IncidL I l; BetH A I C\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1) 
              assms(2) inter_incid_uniquenessH local.cut_def)
      }
      hence "cut' A C X Y" 
        using \<open>X \<noteq> Y\<close> \<open>B = C\<close> cut'_def by auto
      hence ?thesis 
        using \<open>B = C\<close> by blast
    }
    moreover
    {
      assume "B \<noteq> C"
      {
        assume "ColH A C B"
        obtain I where "IncidL I l" and "BetH A I C" 
          using \<open>local.cut l A C\<close> local.cut_def by blast
        hence "ColH A I C" 
          using betH_colH by blast
        hence "ColH A I B" 
          by (meson colH_permut_132 colH_trans colH_trivial121 \<open>A \<noteq> C\<close> \<open>ColH A C B\<close>)
        hence "BetH A I B \<or> BetH I B A \<or> BetH I A B" 
          using ColH_def \<open>A \<noteq> B\<close> \<open>BetH A I C\<close> \<open>IncidL I l\<close> \<open>IncidL X l\<close> 
            \<open>IncidL Y l\<close> \<open>IsL l\<close> assms(2) betH_colH between_one by blast
        have "\<not> IncidL A l" 
          using \<open>local.cut l A C\<close> local.cut_def by auto
        {
          assume "BetH A I B"
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m" 
            have "\<not> IncidL B m" 
              using ColH_def \<open>IncidL X m\<close> \<open>IncidL Y m\<close> \<open>IsL m\<close> assms(2) by blast
            moreover have "\<exists> I0. IncidL I0 m \<and> BetH A I0 B" 
              using \<open>BetH A I B\<close> \<open>IncidL I l\<close> \<open>IncidL X l\<close> \<open>IncidL X m\<close> 
                \<open>IncidL Y l\<close> \<open>IncidL Y m\<close> \<open>X \<noteq> Y\<close> inter_incid_uniquenessH by blast
            ultimately have "cut m A B" 
              using \<open>IncidL X l\<close> \<open>IncidL X m\<close> \<open>IncidL Y l\<close> \<open>IncidL Y m\<close> \<open>IsL m\<close> 
                \<open>X \<noteq> Y\<close> \<open>\<not> IncidL A l\<close> inter_incid_uniquenessH local.cut_def by blast
          }
          hence "cut' A B X Y" 
            by (simp add: \<open>X \<noteq> Y\<close> cut'_def)
        }
        moreover have "BetH I B A \<longrightarrow> same_side' A B X Y" 
          using \<open>IncidL I l\<close> \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>X \<noteq> Y\<close> \<open>\<not> IncidL A l\<close> 
            outH_def out_same_side' by auto
        moreover have "BetH I A B \<longrightarrow> same_side' A B X Y" 
          using \<open>IncidL I l\<close> \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>X \<noteq> Y\<close> \<open>\<not> IncidL A l\<close>
            outH_def out_same_side' by auto
        ultimately have ?thesis 
          using \<open>BetH A I B \<or> BetH I B A \<or> BetH I A B\<close> by fastforce
      }
      moreover
      {
        assume "\<not> ColH A C B"
        have "\<not> IncidL B l" 
          using ColH_def Is_line \<open>IncidL X l\<close> \<open>IncidL Y l\<close> assms(2) by blast
        moreover {
          assume "cut l A B"
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m"
            hence "EqL m l" 
              using \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> \<open>IsL m\<close> \<open>X \<noteq> Y\<close> 
                line_uniqueness by blast
            hence "cut m A B" 
              by (meson \<open>IsL m\<close> \<open>local.cut l A B\<close> local.cut_def morph)
          }
          hence "cut' A B X Y"
            using \<open>X \<noteq> Y\<close> cut'_def by auto
        }
        {
          assume "cut l C B"
          {
            fix m
            assume "IsL m" and "IncidL X m" and "IncidL Y m"
            hence "EqL m l" 
              using \<open>IncidL X l\<close> \<open>IncidL Y l\<close> \<open>IsL l\<close> \<open>X \<noteq> Y\<close> line_uniqueness by blast
            have "cut m A C" 
              by (meson \<open>IncidL X l\<close> \<open>IncidL X m\<close> \<open>IncidL Y l\<close> \<open>IncidL Y m\<close>
                  \<open>IsL m\<close> \<open>X \<noteq> Y\<close> \<open>local.cut l A C\<close> inter_incid_uniquenessH local.cut_def)
            moreover have "cut m B C" 
              by (meson \<open>EqL m l\<close> \<open>IsL m\<close> \<open>local.cut l C B\<close> cut_comm local.cut_def morph)
            ultimately have "same_side A B m" 
              using \<open>IsL m\<close> same_side_def by blast
          }
          hence "same_side' A B X Y" 
            by (simp add: \<open>X \<noteq> Y\<close> same_side'_def)
          have ?thesis
            using \<open>IsL l\<close> \<open>\<not> ColH A C B\<close> \<open>local.cut l A C\<close> pasch_2D 
              \<open>same_side' A B X Y\<close> by blast
        }
        ultimately have ?thesis 
          using \<open>IsL l\<close> \<open>\<not> ColH A C B\<close> \<open>local.cut l A B \<Longrightarrow> cut' A B X Y\<close>
            \<open>local.cut l A C\<close> pasch_2D by blast
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

lemma col_upper_dim:
  assumes "ColH A P Q" and
    "P \<noteq> Q" and
    "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "A \<noteq> P" and
    "A \<noteq> Q" and
    "B \<noteq> P" and
    "B \<noteq> Q" and
    "C \<noteq> P" and
    "C \<noteq> Q" and
    "CongH A P A Q" and
    "CongH B P B Q" and
    "CongH C P C Q"
  shows "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
proof -
  {
    assume "ColH B P Q"
    hence "BetH P B Q" 
      using assms(13) assms(2) assms(8) assms(9) congH_colH_betH by auto
    {
      assume "BetH P A B"
      hence "BetH Q B A" 
        using \<open>BetH P B Q\<close> betH_trans0 between_comm by blast
      hence False 
        using \<open>BetH P A B\<close> assms(12) assms(13) assms(7) assms(9) 
          betH_congH2__False congH_permlr by blast
    }
    moreover
    {
      assume "BetH P B A"
      hence "BetH Q A B" 
        by (metis assms(1) assms(12) assms(2) assms(6) assms(7) 
            betH_trans0 between_comm congH_colH_betH)
      hence False 
        using \<open>BetH P B A\<close> assms(12) assms(13) assms(7) assms(9) 
          betH_congH2__False congH_permlr by blast
    }
    ultimately have False 
      by (metis \<open>BetH P B Q\<close> assms(1) assms(12) assms(2) assms(3) 
          assms(6) betH2_out congH_colH_betH)
  }
  hence "\<not> ColH B P Q" 
    by blast
  {
    assume "ColH C P Q"
    hence "BetH P C Q" 
      using assms(10) assms(11) assms(14) assms(2) congH_colH_betH by force
    {
      assume "BetH P A C"
      hence "BetH Q C A" 
        using \<open>BetH P C Q\<close> betH_trans0 between_comm by blast
      hence False 
        using \<open>BetH P A C\<close> assms(11) assms(12) assms(14) assms(7) 
          betH_congH2__False congH_permlr by blast
    }
    moreover
    {
      assume "BetH P C A"
      hence "BetH Q A C" 
        by (metis assms(1) assms(12) assms(2) assms(6) assms(7) 
            betH_trans0 between_comm congH_colH_betH)
      hence False 
        using \<open>BetH P C A\<close> assms(10) assms(11) assms(12) assms(14) 
          assms(6) assms(7) betH_congH2__False congH_perms by blast
    }
    ultimately have False 
      by (metis congH_colH_betH \<open>BetH P C Q\<close> assms(1) assms(12) assms(2) 
          assms(4) assms(6) betH2_out)
  }
  hence "\<not> ColH C P Q" 
    by blast
  {
    assume "cut' B C P Q"
    obtain l where "IsL l" and "IncidL P l" and "IncidL Q l" 
      using assms(2) line_existence by blast
    have "cut l B C" 
      using \<open>IncidL P l\<close> \<open>IncidL Q l\<close> \<open>IsL l\<close> \<open>cut' B C P Q\<close> cut'_def by auto
    obtain I where "IncidL I l" and "BetH B I C" 
      using \<open>local.cut l B C\<close> local.cut_def by blast
    {
      assume "P = I"
      hence "ColH B Q C" 
        by (metis \<open>BetH B I C\<close> assms(11) assms(13) assms(14) assms(5)
            congH_permlr congH_refl cong_preserves_col)
      hence False 
        by (metis betH2_out \<open>BetH B I C\<close> \<open>P = I\<close> \<open>\<not> ColH B P Q\<close> assms(13) 
            assms(14) assms(2) assms(9) betH_colH bet_cong3_bet colH_permut_132 
            congH_permlr congH_refl)
    }
    hence "P \<noteq> I" by blast
    {
      assume "Q = I"
      hence "ColH B P C" 
        by (metis \<open>BetH B I C\<close> assms(10) assms(11) assms(13) assms(14) 
            assms(5) assms(8) congH_perms congH_refl congH_sym cong_preserves_col)
      hence False 
        by (metis Hilbert_neutral_dimensionless_pre.Bet_def \<open>BetH B I C\<close> 
            \<open>IncidL P l\<close> \<open>Q = I\<close> \<open>\<not> ColH B P Q\<close> \<open>local.cut l B C\<close> betH2_out bet_colH 
            between_one colH_permut_132 local.cut_def outH_def out_same_side same_side_not_cut)
    }
    hence "Q \<noteq> I"
      by blast
    have "ColH P Q I" 
      using ColH_def \<open>IncidL I l\<close> \<open>IncidL P l\<close> \<open>IncidL Q l\<close> \<open>IsL l\<close> by blast
    have "CongaH I B P I B Q" 
    proof -
      have "CongaH C B P C B Q" 
      proof -
        have "\<not> ColH B C P" 
          by (metis (full_types) \<open>BetH B I C\<close> \<open>ColH B P Q \<Longrightarrow> False\<close> 
              \<open>ColH P Q I\<close> \<open>P = I \<Longrightarrow> False\<close> colH_permut_312 colH_trivial121 
              inter_uniquenessH outH_def outH_expand)
        moreover have "\<not> ColH B C Q" 
          by (meson assms(10) assms(11) assms(13) assms(14) assms(5) 
              assms(8) assms(9) calculation congH_refl congH_sym cong_preserves_col_stronger)
        moreover have "CongH B C B C" 
          by (simp add: assms(5) congH_refl)
        moreover have "CongH B P B Q" 
          by (simp add: assms(13))
        moreover have "CongH C P C Q" 
          by (simp add: assms(14))
        ultimately show ?thesis 
          using th18_aux by blast
      qed
      moreover have "outH B C I" 
        by (simp add: \<open>BetH B I C\<close> outH_def)
      moreover have "outH B P P" 
        by (simp add: assms(8) outH_def)
      moreover have "outH B Q Q" 
        by (simp add: assms(9) outH_def)
      ultimately show ?thesis 
        using conga_out_conga by blast
    qed
    have "CongH I P I Q" 
    proof -
      have "\<not> ColH B I P" 
        by (metis \<open>ColH P Q I\<close> \<open>P = I \<Longrightarrow> False\<close> \<open>\<not> ColH B P Q\<close> 
            colH_permut_312 colH_trivial122 inter_uniquenessH)
      moreover have "\<not> ColH B I Q" 
        using IncidL_not_IncidL__not_colH \<open>IncidL I l\<close> \<open>IncidL Q l\<close> 
          \<open>Q = I \<Longrightarrow> False\<close> \<open>local.cut l B C\<close> colH_permut_321 local.cut_def by blast
      moreover have "CongH B I B I" 
        using \<open>BetH B I C\<close> betH_distincts congH_refl by auto
      moreover have "CongH B P B Q" 
        by (simp add: assms(13))
      moreover have "CongaH I B P I B Q" 
        by (simp add: \<open>CongaH I B P I B Q\<close>)
      ultimately show ?thesis  
        using th12 by blast
    qed
    have "A = I \<longrightarrow> ?thesis" 
      using Bet_def \<open>BetH B I C\<close> between_comm by blast
    moreover 
    {
      assume "A \<noteq> I" 
      have "ColH I P Q" 
        by (simp add: \<open>ColH P Q I\<close> colH_permut_312)
      hence "BetH P I Q" 
        by (simp add: \<open>CongH I P I Q\<close> \<open>P \<noteq> I\<close> \<open>Q \<noteq> I\<close> assms(2) congH_colH_betH)
      {
        assume "BetH P A I"
        hence "BetH Q I A" 
          using \<open>BetH P I Q\<close> betH_trans0 between_comm by blast
        hence False 
          by (metis \<open>BetH P A I\<close> \<open>CongH I P I Q\<close> \<open>Q \<noteq> I\<close> assms(12) assms(7)
              betH_congH2__False congH_permlr)
      }
      moreover {
        assume "BetH P I A"
        hence "BetH Q A I" 
          by (metis assms(1) assms(12) assms(2) assms(6) assms(7) betH_trans0 
              between_comm congH_colH_betH)
        hence False 
          by (metis \<open>BetH P I A\<close> \<open>CongH I P I Q\<close> \<open>Q = I \<Longrightarrow> False\<close> assms(12) 
              assms(7) betH_congH2__False congH_permlr)
      }
      ultimately have ?thesis 
        by (metis \<open>A = I \<longrightarrow> Bet A B C \<or> Bet B C A \<or> Bet C A B\<close> \<open>BetH P I Q\<close> 
            assms(1) assms(12) assms(2) assms(6) betH2_out congH_colH_betH)
    }
    ultimately have ?thesis 
      by blast
  }
  moreover
  {
    assume "same_side' B C P Q"
    {
      assume "ColH P B C"
      have "ColH C P B" 
        by (simp add: \<open>ColH P B C\<close> colH_permut_312)
      have "ColH B C Q" 
        by (metis colH_permut_312 \<open>ColH C P B\<close> assms(10) assms(13) assms(14) 
            assms(5) assms(8) congH_perm congH_perms cong_preserves_col_stronger)
      have "BetH P B Q" 
        using ColH_def \<open>ColH B C Q\<close> \<open>ColH C P Q \<Longrightarrow> False\<close> \<open>ColH P B C\<close> 
          assms(5) colH_IncidL__IncidL by blast
      have "BetH P C Q" 
        using \<open>BetH P B Q\<close> \<open>\<not> ColH B P Q\<close> between_col colH_permut_213 by blast
      {
        assume "BetH P B C"
        hence "BetH Q C B" 
          using \<open>BetH P C Q\<close> betH_trans0 between_comm by blast
        hence False 
          using \<open>BetH P B Q\<close> \<open>\<not> ColH B P Q\<close> betH_expand colH_permut_213 by blast
      }
      moreover
      {
        assume "BetH P C B"
        hence "BetH B Q C" 
          using \<open>BetH P B Q\<close> \<open>\<not> ColH B P Q\<close> betH_expand colH_permut_213 by blast
        hence False 
          using \<open>BetH P C Q\<close> \<open>ColH C P Q \<Longrightarrow> False\<close> betH_expand colH_permut_213 by blast
      }
      ultimately have False 
        using \<open>BetH P B Q\<close> \<open>BetH P C Q\<close> assms(5) betH2_out by blast
    }
    hence "\<not> ColH P B C"
      by blast
    {
      assume "ColH Q B C"
      hence "ColH B C P" 
        by (metis (full_types) \<open>\<not> ColH P B C\<close> assms(10) assms(11) assms(13) 
            assms(14) assms(5) assms(8) assms(9) between_one colH_permut_213 congH_perms 
            congH_refl cong_preserves_col)
      hence False 
        using \<open>\<not> ColH P B C\<close> colH_permut_312 by blast
    }
    hence "\<not> ColH Q B C"
      by blast
    {
      assume "cut' P Q B C" 
      obtain lBC where "IsL lBC" and "IncidL B lBC" and "IncidL C lBC" 
        using assms(5) line_existence by blast
      {
        assume "\<not> IncidL P lBC" and
          "\<not> IncidL Q lBC" and
          "\<exists> I. IncidL I lBC \<and> BetH P I Q"
        then obtain I where "IncidL I lBC" and "BetH P I Q" 
          by blast
        have "ColH B I C" 
          using ColH_def \<open>IncidL B lBC\<close> \<open>IncidL C lBC\<close> \<open>IncidL I lBC\<close> \<open>IsL lBC\<close> by auto
        {
          assume "BetH B I C"
          obtain lPQ where "IncidL P lPQ" and "IncidL Q lPQ" and "\<not> cut lPQ B C" 
            by (metis \<open>same_side' B C P Q\<close> line_existence same_side'_def same_side_not_cut)
          have "cut lPQ B C" 
          proof -
            have "\<not> IncidL C lPQ" 
              using Hilbert_neutral_dimensionless_pre.ColH_def Is_line 
                \<open>ColH C P Q \<Longrightarrow> False\<close> \<open>IncidL P lPQ\<close> \<open>IncidL Q lPQ\<close> by fastforce
            moreover have "IncidL I lPQ" 
              using \<open>BetH P I Q\<close> \<open>IncidL P lPQ\<close> \<open>IncidL Q lPQ\<close> assms(2) betH_line
                inter_incid_uniquenessH by blast
            ultimately show ?thesis 
              using \<open>BetH B I C\<close> Is_line \<open>ColH B I C\<close> betH_distincts 
                colH_IncidL__IncidL local.cut_def by blast
          qed
          hence "?thesis" 
            using \<open>\<not> local.cut lPQ B C\<close> by blast
        }
        moreover {
          assume "BetH I C B"
          have "CongaH P C I Q C I"
          proof -
            have "\<not> ColH B C P" 
              using \<open>\<not> ColH P B C\<close> colH_permut_312 by blast
            moreover have "\<not> ColH B C Q" 
              using \<open>\<not> ColH Q B C\<close> colH_permut_312 by blast
            moreover have "CongaH B C P B C Q" 
              using \<open>BetH P I Q\<close> \<open>ColH B I C\<close> assms(13) assms(14) calculation(1)
                calculation(2) th17 by blast
            moreover have "BetH B C I" 
              by (simp add: \<open>BetH I C B\<close> between_comm)
            ultimately show ?thesis 
              using th14 by blast
          qed
          have "CongH I P I Q"
          proof -
            have "\<not> ColH C P I" 
              by (metis IncidL_not_IncidL__not_colH \<open>BetH P I Q\<close> \<open>IncidL C lBC\<close>
                  \<open>IncidL I lBC\<close> \<open>\<not> ColH C P Q\<close> \<open>\<not> IncidL P lBC\<close> betH_colH colH_permut_132 colH_permut_213)
            moreover have "\<not> ColH C Q I" 
              using \<open>BetH I C B\<close> \<open>IncidL C lBC\<close> \<open>IncidL I lBC\<close> \<open>\<not> IncidL Q lBC\<close> 
                betH_distincts colH_IncidL__IncidL colH_permut_312 by blast
            moreover have "CongH C P C Q" 
              by (simp add: assms(14))
            moreover have "CongH C I C I" 
              by (metis \<open>BetH I C B\<close> betH_distincts congH_refl)
            ultimately show ?thesis
              using \<open>CongaH P C I Q C I\<close> 
              using congH_permlr ncolH_expand th12 by presburger
          qed
          have "A = I \<longrightarrow> ?thesis" 
            using Bet_def \<open>BetH I C B\<close> bet_comm by blast
          moreover {
            assume "A \<noteq> I"
            have "ColH I P Q" 
              by (simp add: \<open>BetH P I Q\<close> betH_colH colH_permut_213)
            {
              assume "BetH P A I"
              hence "BetH Q I A" 
                using \<open>BetH P I Q\<close> betH_trans0 between_comm by blast
              hence False 
                by (metis betH_expand \<open>BetH P A I\<close> \<open>CongH I P I Q\<close> assms(12) 
                    betH_congH2__False congH_perms)
            }
            moreover {
              assume "BetH P I A"
              hence "BetH Q A I" 
                by (metis assms(1) assms(12) assms(2) assms(6) assms(7) betH_trans0
                    between_comm congH_colH_betH)
              hence False 
                by (metis \<open>BetH P I A\<close> \<open>CongH I P I Q\<close> assms(12) betH_congH2__False
                    betH_distincts congH_permlr)
            }
            ultimately have ?thesis 
              by (metis \<open>A = I \<longrightarrow> Bet A B C \<or> Bet B C A \<or> Bet C A B\<close> \<open>BetH P I Q\<close> 
                  assms(1) assms(12) assms(2) assms(6) betH2_out congH_colH_betH)
          }
          ultimately have ?thesis 
            by blast
        }
        moreover {
          assume "BetH I B C"
          have "CongaH P B I Q B I"
          proof -
            have "\<not> ColH C B P" 
              using \<open>\<not> ColH P B C\<close> colH_permut_321 by blast
            moreover have "\<not> ColH C B Q" 
              using \<open>\<not> ColH Q B C\<close> colH_permut_321 by blast
            moreover have "CongaH C B P C B Q" 
              using colH_permut_321 \<open>BetH P I Q\<close> \<open>ColH B I C\<close> assms(13) 
                assms(14) calculation(1) calculation(2) th17 by blast
            moreover have "BetH C B I" 
              by (simp add: \<open>BetH I B C\<close> between_comm)
            ultimately show ?thesis 
              using th14 by blast
          qed
          have "CongH I P I Q"
          proof -
            have "\<not> ColH B P I" 
              using \<open>BetH I B C\<close> \<open>IncidL B lBC\<close> \<open>IncidL I lBC\<close> \<open>\<not> IncidL P lBC\<close> 
                betH_distincts colH_IncidL__IncidL colH_permut_312 by blast
            moreover have "\<not> ColH B Q I" 
              using \<open>BetH I B C\<close> \<open>IncidL B lBC\<close> \<open>IncidL I lBC\<close> \<open>\<not> IncidL Q lBC\<close> 
                betH_distincts colH_IncidL__IncidL colH_permut_312 by blast
            moreover have "CongH B P B Q" 
              using assms(13) by auto
            moreover have "CongH B I B I" 
              by (metis \<open>BetH I B C\<close> betH_distincts congH_refl)
            ultimately show ?thesis
              using \<open>CongaH P B I Q B I\<close> 
              by (metis \<open>IncidL I lBC\<close> \<open>\<not> IncidL Q lBC\<close> congH_permlr th12)
          qed
          have "A = I \<longrightarrow> ?thesis" 
            using Bet_def \<open>BetH I B C\<close> by blast
          moreover
          {
            assume "A \<noteq> I"
            have "ColH I P Q" 
              using \<open>BetH P I Q\<close> betH_expand colH_permut_213 by blast
            {
              assume "BetH P A I"
              hence "BetH Q I A" 
                using \<open>BetH P I Q\<close> betH_trans0 between_comm by blast
              hence False 
                by (metis betH_expand \<open>BetH P A I\<close> \<open>CongH I P I Q\<close> assms(12) 
                    betH_congH2__False congH_permlr)
            }
            moreover
            {
              assume "BetH P I A"
              hence "BetH Q A I" 
                by (metis assms(1) assms(12) assms(2) assms(6) assms(7) 
                    betH_trans0 between_comm congH_colH_betH)
              hence False 
                by (metis betH_expand \<open>BetH P I A\<close> \<open>CongH I P I Q\<close> assms(12) 
                    betH_congH2__False congH_perms)
            }
            ultimately have ?thesis 
              by (metis \<open>A = I \<longrightarrow> Bet A B C \<or> Bet B C A \<or> Bet C A B\<close> 
                  \<open>BetH P I Q\<close> assms(1) assms(12) assms(2) assms(6) betH2_out congH_colH_betH)
          }
          ultimately have ?thesis 
            by blast
        }
        ultimately have ?thesis 
          by (metis \<open>BetH P I Q\<close> \<open>ColH B I C\<close> \<open>ColH B P Q \<Longrightarrow> False\<close> 
              \<open>ColH C P Q \<Longrightarrow> False\<close> assms(5) between_col between_one colH_permut_213)
      }
      hence ?thesis 
        using \<open>IncidL B lBC\<close> \<open>IncidL C lBC\<close> \<open>IsL lBC\<close> \<open>cut' P Q B C\<close> cut'_def 
          local.cut_def by auto
    }
    moreover
    {
      assume "same_side' P Q B C" 
      have "outH B P Q" 
      proof -
        have "\<not> ColH P B C" 
          by (simp add: \<open>\<not> ColH P B C\<close>)
        moreover have "\<not> ColH C B P" 
          using calculation colH_permut_321 by blast
        moreover have "CongaH C B P C B P" 
          by (simp add: calculation(2) conga_refl)
        moreover have "CongaH C B P C B Q" 
          by (metis \<open>\<not> ColH Q B C\<close> assms(13) assms(14) assms(5) calculation(2) 
              colH_permut_213 colH_permut_312 congH_refl th18_aux)
        moreover have "same_side' P P B C" 
          using calculation(2) colH_permut_213 same_side_prime_refl by blast
        ultimately show ?thesis 
          using \<open>same_side' P Q B C\<close> cong_4_uniqueness by blast
      qed
      hence ?thesis 
        using \<open>\<not> ColH B P Q\<close> outH_expand by blast
    }
    ultimately have ?thesis 
      using \<open>\<not> ColH P B C\<close> \<open>\<not> ColH Q B C\<close> plane_separation_2D by blast
  }
  ultimately show ?thesis 
    using \<open>\<not> ColH B P Q\<close> \<open>\<not> ColH C P Q\<close> plane_separation_2D by blast
qed

lemma TS_upper_dim: 
  assumes "cut' A B P Q" and
    "P \<noteq> Q" and
    "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "A \<noteq> P" and
    "A \<noteq> Q" and
    "B \<noteq> P" and
    "B \<noteq> Q" and
    "C \<noteq> P" and
    "C \<noteq> Q" and
    "CongH A P A Q" and
    "CongH B P B Q" and
    "CongH C P C Q"
  shows "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
proof -
  obtain l where "IsL l" and "IncidL P l" and "IncidL Q l" 
    using assms(2) line_existence by blast
  have "cut l A B" 
    using \<open>IncidL P l\<close> \<open>IncidL Q l\<close> \<open>IsL l\<close> assms(1) cut'_def by auto
  have "ColH A P Q \<longrightarrow> ?thesis" 
    by (simp add: assms(10) assms(11) assms(12) assms(13) assms(14) assms(2) 
        assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) col_upper_dim)
  moreover
  {
    assume "\<not> ColH A P Q"
    have "ColH B P Q \<longrightarrow> ?thesis" 
      by (metis assms(10) assms(11) assms(12) assms(13) assms(14) assms(2) 
          assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) col_upper_dim)
    moreover 
    {
      assume "\<not> ColH B P Q"
      obtain I where "IncidL I l" and "BetH A I B" 
        using \<open>local.cut l A B\<close> local.cut_def by blast
      have "ColH P Q I" 
        using ColH_def Is_line \<open>IncidL I l\<close> \<open>IncidL P l\<close> \<open>IncidL Q l\<close> by blast
      {
        assume "P = I"
        hence "ColH A Q B" 
          by (metis \<open>BetH A I B\<close> assms(12) assms(13) assms(3) assms(9) congH_permlr 
              congH_refl cong_preserves_col)
        hence False 
          by (metis colH_permut_312 colH_trans colH_trivial121 \<open>BetH A I B\<close> 
              \<open>P = I\<close> \<open>\<not> ColH B P Q\<close> assms(3) between_col)
      }
      hence "P \<noteq> I"
        by blast
      {
        assume "Q = I"
        hence "ColH A P B" 
          by (metis \<open>BetH A I B\<close> assms(12) assms(13) assms(3) assms(6) assms(8) 
              assms(9) congH_perms congH_refl congH_sym cong_preserves_col)
        have "ColH A P I" 
          by (metis \<open>BetH A I B\<close> \<open>ColH A P B\<close> assms(3) colH_trans ncolH_expand 
              outH_col outH_def)
        hence False 
          using \<open>Q = I\<close> \<open>\<not> ColH A P Q\<close> by blast
      }
      hence "Q \<noteq> I"
        by blast
      have "CongaH I A P I A Q" 
      proof -
        have "CongaH B A P B A Q" 
        proof -
          have "\<not> ColH A B P" 
            by (metis (full_types) \<open>BetH A I B\<close> \<open>ColH P Q I\<close> \<open>P = I \<Longrightarrow> False\<close> 
                \<open>\<not> ColH A P Q\<close> colH_permut_312 colH_trivial121 inter_uniquenessH 
                outH_def outH_expand)
          moreover have "\<not> ColH A B Q" 
            by (meson assms(12) assms(13) assms(3) assms(6) assms(7) assms(8) 
                assms(9) calculation congH_refl congH_sym cong_preserves_col_stronger)
          moreover have "CongH A B A B" 
            using assms(3) congH_refl by blast
          moreover have "CongH A P A Q" 
            by (simp add: assms(12))
          moreover have "CongH B P B Q" 
            using assms(13) by auto
          ultimately show ?thesis
            using th18_aux by blast
        qed
        moreover have "outH A B I" 
          by (simp add: \<open>BetH A I B\<close> outH_def)
        moreover have "outH A P P" 
          by (simp add: assms(6) outH_def)
        moreover have "outH A B I" 
          by (simp add: calculation(2))
        moreover have "outH A Q Q" 
          by (simp add: assms(7) outH_def)
        ultimately show ?thesis 
          using conga_out_conga by fastforce
      qed
      have "CongH I P I Q"
      proof -
        have "\<not> ColH A I P" 
          by (metis \<open>ColH P Q I\<close> \<open>P \<noteq> I\<close> \<open>\<not> ColH A P Q\<close> colH_permut_231 
              colH_trans colH_trivial122)
        moreover have "\<not> ColH A I Q" 
          using ColH_def \<open>IncidL I l\<close> \<open>IncidL P l\<close> \<open>IncidL Q l\<close> \<open>Q = I \<Longrightarrow> False\<close>
            calculation inter_incid_uniquenessH by auto
        moreover have "CongH A I A I" 
          using \<open>BetH A I B\<close> betH_distincts congH_refl by presburger
        ultimately show ?thesis
          using \<open>CongaH I A P I A Q\<close> assms(12)
          using th12 by blast
      qed
      have "ColH A B C" 
      proof -
        have "C = I \<longrightarrow> ?thesis" 
          by (simp add: \<open>BetH A I B\<close> between_col colH_permut_132)
        moreover 
        {
          assume "C \<noteq> I"
          have "ColH A C I" 
            by (metis colH_permut_231 \<open>BetH A I B\<close> \<open>C \<noteq> I\<close> \<open>ColH P Q I\<close> 
                \<open>CongH I P I Q\<close> \<open>P \<noteq> I\<close> \<open>Q \<noteq> I\<close> assms(10) assms(11) assms(12) assms(14) 
                assms(2) assms(4) assms(6) assms(7) betH_to_bet bet_colH col_upper_dim)
          hence ?thesis 
            using ColH_def IncidL_not_IncidL__not_colH \<open>BetH A I B\<close> betH_colH by blast
        }
        ultimately show ?thesis 
          by blast
      qed
      have "BetH A B C \<longrightarrow> ?thesis" 
        by (simp add: ColH_bets \<open>ColH A B C\<close>)
      moreover have "BetH B C A \<longrightarrow> ?thesis" 
        using ColH_bets \<open>ColH A B C\<close> by blast
      moreover have "BetH B A C \<longrightarrow> ?thesis" 
        by (simp add: ColH_bets \<open>ColH A B C\<close>)
      ultimately have ?thesis 
        using ColH_bets \<open>ColH A B C\<close> by blast
    }
    ultimately have ?thesis 
      by blast
  }
  ultimately show ?thesis 
    by blast
qed

lemma cut'_comm: 
  assumes "cut' A B X Y" 
  shows  "cut' B A X Y" 
  by (metis assms cut'_def cut_comm)

lemma TS_upper_dim_bis:
  assumes "BetH P I Q" and
    "BetH I B A" and
    "P \<noteq> Q" and
    "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "A \<noteq> P" and
    "A \<noteq> Q" and
    "B \<noteq> P" and
    "B \<noteq> Q" and
    "C \<noteq> P" and
    "C \<noteq> Q" and
    "CongH A P A Q" and
    "CongH B P B Q" and
    "CongH C P C Q"
  shows "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
proof -
  have "ColH A P Q \<longrightarrow> ?thesis" 
    by (simp add: assms(10) assms(11) assms(12) assms(13) assms(14) assms(15) 
        assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) col_upper_dim)
  moreover
  {
    assume "\<not> ColH A P Q"
    have "ColH B P Q \<longrightarrow> ?thesis" 
      by (metis assms(10) assms(11) assms(12) assms(13) assms(14) assms(15) 
          assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) col_upper_dim)
    moreover
    {
      assume "\<not> ColH B P Q"
      have "CongaH P B I Q B I"
      proof -
        have "P \<noteq> I" 
          using assms(1) betH_expand by blast
        have "Q \<noteq> I" 
          using assms(1) betH_colH by blast
        {
          assume "ColH A B P"
          have "\<not> ColH P Q A" 
            using \<open>\<not> ColH A P Q\<close> colH_permut_312 by blast
          moreover have "ColH P Q P" 
            by (simp add: colH_trivial121)
          moreover have "ColH P Q I" 
            by (simp add: assms(1) betH_colH colH_permut_132)
          moreover have "ColH A B I" 
            by (simp add: assms(2) betH_colH between_comm)
          ultimately
          have "P = I" 
            using assms(4) \<open>ColH A B P\<close> inter_uniquenessH by blast
          hence False 
            by (simp add: \<open>P \<noteq> I\<close>)
        }
        hence "\<not> ColH A B P" 
          by blast
        moreover 
        {
          assume "ColH A B Q"
          have "\<not> ColH Q P A" 
            using \<open>\<not> ColH A P Q\<close> colH_permut_321 by blast
          moreover have "ColH Q P Q" 
            by (simp add: colH_trivial121)
          moreover have "ColH Q P I" 
            using assms(1) betH_colH colH_permut_312 by blast
          moreover have "ColH A B I" 
            using assms(2) between_col colH_permut_321 by blast
          ultimately
          have "Q = I" 
            using assms(4) \<open>ColH A B Q\<close> inter_uniquenessH by blast
          hence False 
            by (simp add: \<open>Q \<noteq> I\<close>)
        }
        hence "\<not> ColH A B Q" 
          by blast
        moreover have "CongaH A B P A B Q" 
        proof -
          have "\<not> ColH B A P" 
            using calculation(1) colH_permut_213 by blast
          moreover have "\<not> ColH B A Q" 
            using \<open>\<not> ColH A B Q\<close> colH_permut_213 by blast
          moreover have "CongH B A B A" 
            using assms(4) congH_refl by auto
          ultimately show ?thesis 
            using assms(13) assms(14) th18_aux by presburger
        qed
        ultimately show ?thesis 
          by (simp add: assms(2) between_comm th14)
      qed
      have "CongH I P I Q" 
        by (metis assms(1) assms(10) assms(13) assms(14) assms(2) assms(7) 
            assms(8) assms(9) axiom_five_segmentsH between_comm between_only_one congH_refl)
      have "ColH A B C" 
      proof -
        have "ColH A B I" 
          by (simp add: assms(2) between_col colH_permut_321)
        have "C = I \<longrightarrow> ?thesis" 
          using \<open>ColH A B I\<close> by blast
        moreover
        {
          assume "C \<noteq> I"
          have "ColH I B A" 
            by (simp add: assms(2) betH_colH)
          hence "ColH A C I" 
            by (metis (mono_tags, lifting) betH_to_bet bet_colH colH_permut_213 
                colH_permut_312 \<open>C \<noteq> I\<close> \<open>CongH I P I Q\<close> assms(1) assms(11) assms(12) 
                assms(13) assms(15) assms(2) assms(5) assms(7) assms(8) col_upper_dim)
          have "ColH P I Q" 
            by (simp add: assms(1) betH_colH)
          hence ?thesis 
            by (metis betH_distincts colH_permut_312 colH_trans colH_trivial121 
                \<open>ColH A C I\<close> \<open>ColH I B A\<close> assms(2))
        }
        ultimately show ?thesis
          by blast
      qed
      have "BetH B A C \<longrightarrow> ?thesis" 
        using ColH_bets \<open>ColH A B C\<close> by blast
      hence ?thesis 
        using ColH_bets \<open>ColH A B C\<close> by blast
    }
    ultimately have ?thesis
      by blast
  }
  ultimately show ?thesis by blast
qed

lemma upper_dim:
  assumes "P \<noteq> Q" and
    "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "Cong A P A Q" and
    "Cong B P B Q" and
    "Cong C P C Q"
  shows "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
proof -
  have "C = P \<and> C = Q \<longrightarrow> ?thesis" 
    using assms(1) by blast
  have "B = P \<and> B = Q \<longrightarrow> ?thesis" 
    using assms(1) by blast
  have "A = P \<and> A = Q \<longrightarrow> ?thesis" 
    using assms(1) by blast
  have "CongH A P A Q" 
    using Cong_def assms(1) assms(5) by auto
  have "CongH B P B Q" 
    using Cong_def assms(1) assms(6) by blast
  have "CongH C P C Q" 
    using Cong_def assms(1) assms(7) by blast
  have "A \<noteq> P" 
    using Cong_def assms(1) assms(5) by presburger
  have "A \<noteq> Q" 
    using Cong_def assms(1) assms(5) by presburger
  have "B \<noteq> P" 
    using Cong_def assms(1) assms(6) by force
  have "B \<noteq> Q" 
    using Cong_def assms(1) assms(6) by presburger
  have "C \<noteq> P" 
    using Cong_def assms(1) assms(7) by presburger
  have "C \<noteq> Q" 
    using Cong_def assms(1) assms(7) by presburger
  have "ColH A P Q \<longrightarrow> ?thesis" 
    by (simp add: \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>C \<noteq> P\<close> \<open>C \<noteq> Q\<close> 
        \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>CongH C P C Q\<close> assms(1) assms(2) assms(3) 
        assms(4) col_upper_dim)
  moreover
  {
    assume "\<not> ColH A P Q"
    have "ColH B P Q \<longrightarrow> ?thesis" 
      by (metis \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>C \<noteq> P\<close> \<open>C \<noteq> Q\<close> 
          \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>CongH C P C Q\<close> assms(1) assms(2) assms(3) 
          assms(4) col_upper_dim)
    moreover
    {
      assume "\<not> ColH B P Q"
      have "ColH C P Q \<longrightarrow> ?thesis" 
        by (metis \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>C \<noteq> P\<close> \<open>C \<noteq> Q\<close> 
            \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>CongH C P C Q\<close> assms(1) assms(2) 
            assms(3) assms(4) col_upper_dim)
      moreover
      {
        assume "\<not> ColH C P Q"
        have "cut' A B P Q \<longrightarrow> ?thesis" 
          by (simp add: TS_upper_dim \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>C \<noteq> P\<close> 
              \<open>C \<noteq> Q\<close> \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>CongH C P C Q\<close> assms(1) 
              assms(2) assms(3) assms(4))
        moreover
        {
          assume "same_side' A B P Q"
          have "cut' A C P Q \<longrightarrow> ?thesis" 
            using TS_upper_dim \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>C \<noteq> P\<close> \<open>C \<noteq> Q\<close> 
              \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>CongH C P C Q\<close> assms(1) assms(2) assms(3) 
              assms(4) bet_comm by blast
          moreover
          {
            assume "same_side' A C P Q"
            {
              assume "ColH P A B" 
              hence "ColH B P A" 
                by (simp add: colH_permut_312)
              have "ColH A B Q" 
                by (meson \<open>A \<noteq> P\<close> \<open>B \<noteq> P\<close> \<open>ColH B P A\<close> \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> 
                    assms(2) colH_permut_312 congH_refl cong_preserves_col_stronger)
              hence False
                by (metis \<open>ColH B P A\<close> \<open>\<not> ColH A P Q\<close> assms(2) colH_trans ncolH_distincts)
            }
            hence "\<not> ColH P A B" 
              by blast
            {
              assume "ColH Q A B"
              hence "ColH A B P" 
                by (meson \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>CongH A P A Q\<close> 
                    \<open>CongH B P B Q\<close> assms(2) colH_permut_231 congH_refl congH_sym 
                    cong_preserves_col_stronger)            
              hence False 
                using \<open>\<not> ColH P A B\<close> colH_permut_312 by blast
            }
            hence "\<not> ColH Q A B" 
              by blast
            {
              assume "same_side' P Q A B"
              have "outH A P Q" 
              proof -
                have "\<not> ColH P A B" 
                  by (simp add: \<open>\<not> ColH P A B\<close>)
                moreover have "\<not> ColH B A P" 
                  using calculation colH_permut_321 by blast
                moreover have "CongaH B A P B A P" 
                  using calculation(2) conga_refl by blast
                moreover have "CongaH B A P B A Q" 
                  by (metis \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>\<not> ColH Q A B\<close> assms(2) 
                      calculation(2) colH_permut_213 colH_permut_312 congH_refl th18_aux)
                moreover have "same_side' P P A B" 
                  using calculation(1) colH_permut_312 same_side_prime_refl by blast
                ultimately show ?thesis 
                  using \<open>same_side' P Q A B\<close> 
                  using cong_4_uniqueness by blast
              qed
              hence ?thesis 
                using \<open>\<not> ColH A P Q\<close> outH_expand by blast
            }
            moreover
            {
              assume "cut' P Q A B"
              obtain lAB where "IsL lAB" and "IncidL A lAB" and "IncidL B lAB" 
                using assms(2) line_existence by blast
              then obtain I where "IncidL I lAB" and "BetH P I Q"  
                using \<open>cut' P Q A B\<close> cut'_def local.cut_def by auto
              hence "ColH A I B" 
                using ColH_def \<open>IncidL A lAB\<close> \<open>IncidL B lAB\<close> \<open>IsL lAB\<close> by auto
              {
                assume "BetH A I B"
                obtain lPQ where "IsL lPQ" and "IncidL P lPQ" and "IncidL Q lPQ" 
                  using assms(1) line_existence by blast
                hence "\<not> cut lPQ A B" 
                  using \<open>same_side' A B P Q\<close> same_side'_def same_side_not_cut by auto
                have "cut lPQ A B" 
                proof -
                  have "\<not> IncidL B lPQ" 
                    using Hilbert_neutral_dimensionless_pre.ColH_def \<open>IncidL P lPQ\<close> 
                      \<open>IncidL Q lPQ\<close> \<open>IsL lPQ\<close> \<open>\<not> ColH B P Q\<close> by fastforce
                  moreover have "IncidL I lPQ" 
                    using \<open>BetH P I Q\<close> \<open>IncidL P lPQ\<close> \<open>IncidL Q lPQ\<close> assms(1) 
                      betH_line inter_incid_uniquenessH by blast
                  ultimately show ?thesis 
                    using \<open>BetH A I B\<close> 
                    using Is_line \<open>ColH A I B\<close> betH_distincts colH_IncidL__IncidL 
                      local.cut_def by blast
                qed
                hence False 
                  using \<open>\<not> local.cut lPQ A B\<close> by blast
                hence ?thesis 
                  by blast
              }
              moreover have "BetH I B A \<longrightarrow> ?thesis" 
                using TS_upper_dim_bis \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>BetH P I Q\<close> 
                  \<open>C \<noteq> P\<close> \<open>C \<noteq> Q\<close> \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>CongH C P C Q\<close> 
                  assms(1) assms(2) assms(3) assms(4) by blast
              moreover have "BetH I A B \<longrightarrow> ?thesis" 
                using TS_upper_dim_bis \<open>A \<noteq> P\<close> \<open>A \<noteq> Q\<close> \<open>B \<noteq> P\<close> \<open>B \<noteq> Q\<close> \<open>BetH P I Q\<close> 
                  \<open>C \<noteq> P\<close> \<open>C \<noteq> Q\<close> \<open>CongH A P A Q\<close> \<open>CongH B P B Q\<close> \<open>CongH C P C Q\<close> 
                  assms(1) assms(2) assms(3) assms(4) bet_comm by blast
              ultimately have ?thesis 
                by (metis \<open>BetH P I Q\<close> \<open>ColH A I B\<close> \<open>\<not> ColH A P Q\<close> \<open>\<not> ColH B P Q\<close> 
                    assms(2) betH_colH between_one colH_permut_213)
            }
            ultimately have ?thesis 
              using \<open>\<not> ColH P A B\<close> \<open>\<not> ColH Q A B\<close> plane_separation_2D by blast
          }
          ultimately have ?thesis 
            using \<open>\<not> ColH A P Q\<close> \<open>\<not> ColH C P Q\<close>
              \<open>cut' A C P Q \<longrightarrow> Bet A B C \<or> Bet B C A \<or> Bet C A B\<close> 
              \<open>same_side' A C P Q \<Longrightarrow> Bet A B C \<or> Bet B C A \<or> Bet C A B\<close> 
              plane_separation_2D by blast
        }
        ultimately have ?thesis 
          using \<open>\<not> ColH A P Q\<close> \<open>\<not> ColH B P Q\<close> plane_separation_2D by blast
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

interpretation H2D_to_T2D : Tarski_2D
  where Bet = Bet and
    Cong = Cong and
    TPA = PP and
    TPB = PQ  and
    TPC = PR
proof 
  show "\<forall>a b. Cong a b b a" 
    by (simp add: cong_permT)
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
    by (simp add: bet_identity)
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
  show "\<forall>a b c p q.
       p \<noteq> q \<and> Cong a p a q \<and> Cong b p b q \<and> Cong c p c q \<longrightarrow>
       Bet a b c \<or> Bet b c a \<or> Bet c a b" 
    by (metis Bet_def upper_dim)
qed

end

context Hilbert_neutral_3D

begin

interpretation H3D_to_T3D : Tarski_3D
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

context Hilbert_euclidean

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