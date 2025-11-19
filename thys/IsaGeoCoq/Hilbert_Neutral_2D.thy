(* IsageoCoq - Hilbert_Neutral_2D.thy
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

theory Hilbert_Neutral_2D

imports Hilbert_Neutral

begin

section "Hilbert - Geometry - Neutral 2D"

subsection "Axioms: Hilbert neutral 2D"

locale Hilbert_neutral_2D = Hilbert_neutral_dimensionless IncidL IncidP EqL EqP IsL IsP BetH CongH CongaH
  for
    IncidL :: "'p \<Rightarrow> 'b \<Rightarrow> bool" and
    IncidP :: "'p \<Rightarrow> 'c \<Rightarrow> bool" and
    EqL ::"'b \<Rightarrow> 'b \<Rightarrow> bool" and
    EqP ::"'c \<Rightarrow> 'c \<Rightarrow> bool" and
    IsL ::"'b \<Rightarrow> bool" and
    IsP ::"'c \<Rightarrow> bool" and
    BetH ::"'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" and
    CongH::"'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" and
    CongaH::"'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" +
  assumes pasch_2D :
    "IsL l \<and>  \<not> ColH A B C \<and> \<not> IncidL C l \<and> cut l A B \<longrightarrow> (cut l A C \<or> cut l B C)"

context Hilbert_neutral_2D

begin

subsection "Definitions"

subsection "Propositions"

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

end
end