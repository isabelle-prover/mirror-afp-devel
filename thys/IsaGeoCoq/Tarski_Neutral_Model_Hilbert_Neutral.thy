(* IsageoCoq - Tarski_Neutral_Model_Hilbert_Neutral.thy
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

theory Tarski_Neutral_Model_Hilbert_Neutral

imports 
  Tarski_Postulate_Parallels 
  Hilbert_Neutral
  Gupta_Neutral

begin

section "Tarski Neutral Model Hilbert Neutral"

context Hilbert_neutral_dimensionless

begin

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
end