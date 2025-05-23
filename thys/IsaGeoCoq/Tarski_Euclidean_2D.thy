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

lemma projp_is_project:
  assumes "P P' Projp A B"
  shows "\<exists> X Y. P P' Proj A B X Y" 
proof -
  have "A \<noteq> B" 
    using Projp_def assms by blast
  moreover
  then obtain X Y where "A B Perp X Y" 
    using perp_vector by blast
  have "X \<noteq> Y" 
    using \<open>A B Perp X Y\<close> perp_not_eq_2 by auto
  moreover have "\<not> A B Par X Y" 
    by (simp add: \<open>A B Perp X Y\<close> perp_not_par)
  moreover have "Col A B P'" 
    using Projp_def assms by fastforce
  moreover have "(P P' Par X Y) \<or> P = P'" 
    by (metis Projp_def \<open>A B Perp X Y\<close> assms par_perp2__par par_reflexivity)
  ultimately show ?thesis 
    using Proj_def by blast
qed

lemma projp_is_project_perp:
  assumes "P P' Projp A B" 
  shows "\<exists> X Y. P P' Proj A B X Y \<and> A B Perp X Y" 
proof -
  have "A \<noteq> B" 
    using Projp_def assms by blast
  moreover
  then obtain X Y where "A B Perp X Y" 
    using perp_vector by blast
  moreover
  have "X \<noteq> Y" 
    using \<open>A B Perp X Y\<close> perp_not_eq_2 by auto
  moreover have "\<not> A B Par X Y" 
    by (simp add: \<open>A B Perp X Y\<close> perp_not_par)
  moreover have "Col A B P'" 
    using Projp_def assms by fastforce
  moreover have "(P P' Par X Y) \<or> P = P'" 
    by (metis Projp_def \<open>A B Perp X Y\<close> assms par_perp2__par par_reflexivity)
  ultimately show ?thesis 
    using Proj_def by blast
qed

lemma projp_to_project:
  assumes "A B Perp X Y" and
    "P P' Projp A B"
  shows "P P' Proj A B X Y" 
proof -
  have "A \<noteq> B" 
    using assms(1) perp_distinct by auto
  moreover have "X \<noteq> Y" 
    using assms(1) perp_distinct by blast
  moreover have "\<not> A B Par X Y" 
    by (simp add: \<open>A B Perp X Y\<close> perp_not_par)
  moreover have "Col A B P'" 
    using Projp_def assms(2) by fastforce
  moreover have "(P P' Par X Y) \<or> P = P'" 
    by (metis Projp_def \<open>A B Perp X Y\<close> assms(2) par_perp2__par par_reflexivity)
  ultimately show ?thesis 
    using Proj_def by blast
qed

lemma project_to_projp:
  assumes "P P' Proj A B X Y" and
    "A B Perp X Y" 
  shows "P P' Projp A B" 
proof -
  have "A \<noteq> B" 
    using assms(2) perp_not_eq_1 by auto
  moreover have "Col A B P'" 
    using Proj_def assms(1) by force
  moreover
  {
    assume "P P' Par X Y"
    have "Col A B P'" 
      using calculation(2) by blast
    moreover have "A B Perp P P'" 
      using Perp_cases \<open>P P' Par X Y\<close> assms(2) par_perp__perp par_symmetry by blast
    ultimately have "Col A B P' \<and> A B Perp P P'" 
      by blast
  }
  ultimately show ?thesis 
    using Proj_def Projp_def assms(1) by auto
qed

lemma projp_project_to_perp:
  assumes "P \<noteq> P'" and
    "P P' Projp A B" and 
    "P P' Proj A B X Y"
  shows "A B Perp X Y" 
  by (metis Perp_perm Projp_def assms(1) assms(2) assms(3) par_perp__perp project_par_dir)

lemma project_par_project:
  assumes "P P' Proj A B X Y" and
    "X Y Par X' Y'"
  shows "P P' Proj A B X' Y'" 
  by (metis Proj_def assms(1) assms(2) not_par_one_not_par par_neq2 par_symmetry)


lemma project_project_par :
  assumes "P \<noteq> P'" and
    "P P' Proj A B X Y" and
    "P P' Proj A B X' Y'"
  shows "X Y Par X' Y'" 
proof -
  have "P P' Par X Y \<longrightarrow> ?thesis" 
    using assms(1) assms(3) par_not_par par_symmetry project_par_dir by blast
  thus ?thesis 
    using assms(1) assms(2) project_par_dir by blast
qed

lemma projp_preserves_bet:
  assumes "Bet A B C" and
    "A A' Projp X Y" and
    "B B' Projp X Y" and
    "C C' Projp X Y"
  shows "Bet A' B' C'" 
proof -
  obtain T U where "A A' Proj X Y T U" and "X Y Perp T U" 
    using assms(2) projp_is_project_perp by blast
  thus ?thesis 
    using assms(1) assms(3) assms(4) project_preserves_bet projp_to_project by blast
qed

lemma projp_preserves_eqv:
  assumes "A B EqV C D" and
    "A A' Projp X Y" and
    "B B' Projp X Y" and
    "C C' Projp X Y" and
    "D D' Projp X Y"
  shows "A' B' EqV C' D'" 
proof -
  obtain T U where "A A' Proj X Y T U" and "X Y Perp T U" 
    using assms(2) projp_is_project_perp by blast
  thus ?thesis 
    using assms(1) assms(3) assms(4) assms(5) project_preserves_eqv projp_to_project by blast
qed

lemma projp2_col:
  assumes "P A Projp B C" and
    "Q A Projp B C"
  shows "Col A P Q" 
proof -
  {
    assume "Col B C A" and "B C Perp P A" 
    {
      assume "Col B C A" and "B C Perp Q A"
      have ?thesis 
      proof (rule perp2__col [where ?A="B" and ?B="C"])
        show "A P Perp B C"   
          using Perp_cases \<open>B C Perp P A\<close> by auto
        show "A Q Perp B C"
          using Perp_perm \<open>B C Perp Q A\<close> by blast
      qed
    }
    moreover
    have "Col B C Q \<and> Q = A \<longrightarrow> ?thesis" 
      by (simp add: col_trivial_3)
    ultimately have ?thesis 
      using Projp_def assms(2) by force
  }
  moreover have "Col B C P \<and> P = A \<longrightarrow> ?thesis" 
    by (simp add: col_trivial_1)
  ultimately show ?thesis 
    using Projp_def assms(1) by force
qed

lemma projp_projp_perp:
  assumes "P1 \<noteq> P2" and
    "P1 P Projp Q1 Q2" and
    "P2 P Projp Q1 Q2" 
  shows "P1 P2 Perp Q1 Q2" 
proof -
  have "Col P1 P P2" 
    by (metis Col_cases Perp_cases Projp_def assms(2) assms(3) not_col_distincts perp2__col)
  thus ?thesis 
    by (metis Perp_cases Projp_def assms(1) assms(2) assms(3) not_col_distincts perp_col2_bis)
qed

lemma perp_projp2_eq:
  assumes "A A' Projp C D" and 
    "B B' Projp C D" and
    "A B Perp C D"
  shows "A' = B'" 
proof -
  {
    assume "Col C D A'" and "C D Perp A A'"
    {
      assume "Col C D B'" and "C D Perp B B'" 
      {
        assume "\<not> Col A B C" 
        have "Col A B A'" 
          using Perp_cases \<open>C D Perp A A'\<close> assms(3) perp2__col by blast
        moreover have "Col A B B'" 
          using Col_cases Perp_cases \<open>C D Perp B B'\<close> assms(3) perp2__col by meson
        ultimately have "A' = B'" 
          using \<open>Col C D A'\<close> \<open>Col C D B'\<close> assms(3) l8_14_1 perp_col4 by blast
      }
      moreover {
        assume "\<not> Col A B D" 
        have "Col A B A'" 
          using Perp_cases \<open>C D Perp A A'\<close> assms(3) perp2__col by blast
        moreover have "Col A B B'" 
          using Col_cases Perp_cases \<open>C D Perp B B'\<close> assms(3) perp2__col by meson
        ultimately have  "A' = B'" 
          using \<open>Col C D A'\<close> \<open>Col C D B'\<close> assms(3) perp_col0 perp_not_col2 by blast
      }
      ultimately have ?thesis 
        using assms(3) perp_not_col2 by blast
    }
    moreover have "Col C D B \<and> B = B' \<longrightarrow> ?thesis" 
      using Perp_cases \<open>C D Perp A A'\<close> \<open>Col C D A'\<close> assms(3) l8_18_uniqueness by blast
    ultimately have ?thesis 
      using Projp_def assms(2) by force
  }
  moreover have "Col C D A \<and> A = A'\<longrightarrow> ?thesis" 
    by (metis Perp_cases Projp_def assms(2) assms(3) l8_18_uniqueness perp_not_col2)
  ultimately show ?thesis 
    using Projp_def assms(1) by force
qed

lemma col_par_projp2_eq:
  assumes "Col L11 L12 P" and
    "L11 L12 Par L21 L22" and
    "P P' Projp L21 L22" and
    "P' P'' Projp L11 L12" 
  shows "P = P''" 
proof -
  {
    assume "Col L21 L22 P'" and "L21 L22 Perp P P'" and
      "Col L11 L12 P''" and "L11 L12 Perp P' P''"
    have "P P' Par P' P''" 
      using Par_cases \<open>L11 L12 Perp P' P''\<close> \<open>L21 L22 Perp P P'\<close> assms(2) 
        par_perp2__par by blast
    have "\<not> Col L11 L12 P' \<longrightarrow> ?thesis" 
      by (metis Par_perm Perp_perm \<open>Col L11 L12 P''\<close> \<open>L11 L12 Perp P' P''\<close> 
          \<open>L21 L22 Perp P P'\<close> assms(1) assms(2) l8_18_uniqueness par_perp__perp)
    moreover have "\<not> Col L11 L12 P'' \<longrightarrow> ?thesis" 
      using \<open>Col L11 L12 P''\<close> by blast
    ultimately have "P = P''" 
      using perp_not_col2 \<open>L11 L12 Perp P' P''\<close> by blast
  }
  thus ?thesis 
    by (metis Projp_def assms(1) assms(2) assms(3) assms(4) col_not_col_not_par 
        col_projp_eq par_symmetry)
qed

lemma col_2_par_projp2_cong:
  assumes "Col L11 L12 A'" and
    "Col L11 L12 B'" and
    "L11 L12 Par L21 L22" and
    "A' A Projp L21 L22" and
    "B' B Projp L21 L22"
  shows "Cong A B A' B'" 
proof -
  {
    assume "L11 L12 ParStrict L21 L22" 
    {
      assume "A' \<noteq> B'" 
      {
        assume "A \<noteq> B"
        have "L11 L12 ParStrict A B" 
          using \<open>A \<noteq> B\<close> \<open>L11 L12 ParStrict L21 L22\<close> assms(4) assms(5) 
            par_strict_col2_par_strict projp_col by blast
        hence "A B ParStrict B' A'" 
          by (metis Par_strict_cases \<open>A' \<noteq> B'\<close> assms(1) assms(2) par_strict_col2_par_strict)
        moreover have "A A' Par B B'" 
          by (metis Par_perm Projp_def \<open>L11 L12 ParStrict L21 L22\<close> 
              assms(1) assms(2) assms(3) assms(4) assms(5) not_strict_par2 
              par_perp2__par par_perp__perp par_strict_not_col_4)
        ultimately have "Plg A B B' A'" 
          by (simp add: pars_par_plg)
        hence ?thesis 
          using Plg_perm plg_cong_2 plg_to_parallelogram by blast
      }
      moreover {
        assume "A = B"
        hence "Col A A' B'" 
          using assms(4) assms(5) projp2_col by auto
        moreover have "Col L21 L22 A" 
          using assms(4) projp_col by blast
        ultimately have False using l6_21 
          by (metis \<open>A' \<noteq> B'\<close> \<open>L11 L12 ParStrict L21 L22\<close> 
              assms(1) assms(2) col_trivial_2 not_col_permutation_1 par_not_col)
      }
      ultimately have ?thesis 
        by blast
    }
    hence ?thesis 
      using assms(4) assms(5) cong_trivial_identity projp_id by blast
  }
  thus ?thesis 
    by (metis Par_cases assms(1) assms(2) assms(3) assms(4) assms(5) col_projp_eq 
        cong_reflexivity par_not_col_strict par_strict_symmetry)
qed

lemma project_existence:
  assumes "X \<noteq>  Y"
and "A \<noteq> B"
and "\<not> X Y Par A B"
shows "\<exists> P'. P P' Proj A B X Y" 
proof -
  obtain x x0 where "x \<noteq> x0" and "X Y Par x x0" and "Col P x x0"
    by (metis assms(1) not_col_distincts par_distincts parallel_existence1) 
  have "\<not> x x0 Par A B"
    using \<open>X Y Par x x0\<close> assms(3) par_not_par by blast 
  then obtain P' where "Col P' x x0" and "Col P' A B" 
    using not_par_inter_exists \<open>\<not> x x0 Par A B\<close> by blast 
  hence "P P' Proj A B X Y"
    by (metis Proj_def \<open>Col P x x0\<close> \<open>X Y Par x x0\<close> assms(1) assms(2) assms(3) 
not_col_permutation_2 par_col2_par par_symmetry) 
  thus ?thesis
    by auto 
qed

lemma sum_exists:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E A"
    and "Col PO E B"
  shows "\<exists> C. Sum PO E E' A B C" 
proof -
  have "PO \<noteq> E"
    using col_trivial_1 grid_ok by blast  
  have "PO \<noteq> E'"
    using col_trivial_3 grid_ok by auto
  show ?thesis 
  proof (cases)
    assume "PO = A"
    thus ?thesis
      by (metis Ar2_def Pj_def Sum_def \<open>PO \<noteq> E\<close> assms(3) col_trivial_3 grid_ok not_par_not_col) 
  next
    assume "PO \<noteq> A"
    obtain A' where "A A' Proj PO E' E E'" 
      using project_existence by (metis Par_cases \<open>PO \<noteq> E'\<close> col_trivial_2 grid_ok par_id_2) 
    obtain P where "PO E Par A' P"
      using \<open>PO \<noteq> E\<close> parallel_existence1 by presburger
    have "A \<noteq> A'"
      by (metis NCol_cases Proj_def \<open>A A' Proj PO E' E E'\<close> \<open>PO \<noteq> A\<close> assms(2) 
          col_transitivity_1 grid_ok) 
    show ?thesis 
    proof (cases)
      assume "B = PO"
      have "Sum PO E E' A PO A" 
      proof (unfold Sum_def, standard)
        show "Ar2 PO E E' A PO A"
          using Ar2_def \<open>B = PO\<close> assms(3) assms(2) grid_ok by blast 
        show "\<exists>A' C'. E E' Pj A A' \<and> Col PO E' A' \<and> PO E Pj A' C' \<and> PO E' Pj PO C' \<and> E' E Pj C' A"
        proof -
          have "E E' Pj A A'"
            using Pj_def \<open>A A' Proj PO E' E E'\<close> par_symmetry project_par_dir by blast 
          moreover have "Col PO E' A'"
            using Proj_def \<open>A A' Proj PO E' E E'\<close> by auto 
          moreover have "PO E Pj A' A'"
            by (simp add: Pj_def) 
          moreover have "PO E' Pj PO A'"
            using Pj_def \<open>PO \<noteq> E'\<close> calculation(2) not_par_not_col by blast 
          moreover have "E' E Pj A' A"
            using Par_cases Pj_def calculation(1) by auto 
          ultimately show ?thesis 
            by blast
        qed
      qed
      thus ?thesis
        using \<open>B = PO\<close> by auto 
    next
      assume "B \<noteq> PO"
      have "\<exists> C'. B C' Proj A' P PO E'"
        by (metis \<open>PO E Par A' P\<close> \<open>PO \<noteq> E'\<close> grid_ok not_par_one_not_par par_distincts 
            par_id_3 project_existence) 
      then obtain C' where "B C' Proj A' P PO E'" 
        by blast
      have "\<exists> C. C' C Proj PO E A A'"
        by (metis Proj_def \<open>A A' Proj PO E' E E'\<close> \<open>A \<noteq> A'\<close> \<open>PO \<noteq> E\<close> col_par_par_col 
            col_trivial_3 grid_ok par_left_comm project_existence) 
      then obtain C where "C' C Proj PO E A A'"
        by blast
      have "Sum PO E E' A B C"
      proof (unfold Sum_def, rule+)
        show "Ar2 PO E E' A B C"
          using Ar2_def Proj_def \<open>C' C Proj PO E A A'\<close> assms(3) assms(2) grid_ok by presburger 
        show "\<exists>A' C'. E E' Pj A A' \<and> Col PO E' A' \<and> PO E Pj A' C' \<and> PO E' Pj B C' \<and> E' E Pj C' C" 
        proof (intro exI conjI)
          let ?A' = "A'" and ?C'1 = "C'"
          show "E E' Pj A ?A'"
            using Pj_def \<open>A A' Proj PO E' E E'\<close> par_symmetry project_par_dir by blast 
          show "Col PO E' ?A'"
            using Proj_def \<open>A A' Proj PO E' E E'\<close> by presburger 
          show "PO E Pj ?A' ?C'1"
            by (metis Pj_def Proj_def \<open>B C' Proj A' P PO E'\<close> \<open>PO E Par A' P\<close> par_col_par) 
          show "PO E' Pj B ?C'1"
            using Pj_def \<open>B C' Proj A' P PO E'\<close> par_symmetry project_par_dir by blast 
          show "E' E Pj ?C'1 C"
            by (metis Par_perm Pj_def Proj_def \<open>C' C Proj PO E A A'\<close> \<open>E E' Pj A A'\<close> par_trans) 
        qed
      qed
      thus ?thesis 
        by blast
    qed
  qed
qed

lemma opp_exists:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E A"
  shows "\<exists> MA. Opp PO E E' A MA" 
proof (cases)
  assume "A = PO" 
  thus ?thesis
    by (metis Ar2_def Opp_def Pj_def Sum_def col_trivial_3 grid_ok) 
next
  assume "A \<noteq> PO"
  obtain MA where "Bet A PO MA" and "Cong PO MA A PO"
    using segment_construction by blast 
  show ?thesis 
  proof (unfold Opp_def, rule exI[of _ "MA"], intro sump_to_sum, unfold Sump_def, rule conjI)
    show "Col PO E MA"
      by (metis Col_def not_col_distincts \<open>A \<midarrow> PO \<midarrow> MA\<close> \<open>A \<noteq> PO\<close> assms 
          between_symmetry not_par_not_col par_col_par par_id) 
    have "\<exists>A' C' P'. MA A' Proj PO E' E E' \<and> PO E Par A' P' \<and> A C' Proj A' P' PO E' \<and> 
                     C' PO Proj PO E E E'" 
    proof -
      obtain A' where "MA A' Proj PO E' E E'"
        by (metis col_trivial_2 col_trivial_3 grid_ok par_comm par_id_4 project_existence)
      have "PO \<noteq> E"
        using col_trivial_1 grid_ok by force 
      then obtain P' where "PO E Par A' P'"
        using parallel_existence1 by presburger 
      obtain C' where "A C' Proj A' P' PO E'"
        by (metis Col_def \<open>PO E Par A' P'\<close> between_trivial grid_ok 
            not_par_one_not_par par_distincts par_id project_existence) 
      show ?thesis 
      proof (rule exI[of _ "A'"], rule exI[of _ "C'"], rule exI[of _ "P'"],
          intro conjI, simp add: \<open>MA A' Proj PO E' E E'\<close>, simp add: \<open>PO E Par A' P'\<close>, 
          simp add: \<open>A C' Proj A' P' PO E'\<close>)
        show "C' PO Proj PO E E E'" 
        proof (unfold Proj_def, intro conjI, simp add: \<open>PO \<noteq> E\<close>)
          show "E \<noteq> E'"
            using grid_ok not_col_distincts by presburger 
          show "\<not> PO E Par E E'"
            using grid_ok not_col_distincts not_strict_par by blast 
          show "Col PO E PO"
            using not_col_distincts by blast 
          have "C' PO Par E E'" 
          proof -
            have "PO E' Par PO A'"
              by (metis (full_types) Par_cases Proj_def \<open>A \<midarrow> PO \<midarrow> MA\<close> \<open>A \<noteq> PO\<close> 
                  \<open>Col PO E MA\<close> \<open>Cong PO MA A PO\<close> \<open>MA A' Proj PO E' E E'\<close> \<open>\<not> PO E Par E E'\<close> 
                  bet_cong_eq not_par_not_col par_not_par) 
            have "Plg A C' A' PO" 
            proof (rule pars_par_plg)
              show "A C' ParStrict A' PO"
              proof -
                {
                  assume "A C' Par PO E'"
                  hence "A C' Par A' PO"
                    by (meson \<open>PO E' Par PO A'\<close> par_right_comm par_trans) 
                  {
                    assume "A C' ParStrict A' PO'"
                    hence ?thesis
                      by (metis Col_cases Par_def \<open>A C' Par A' PO\<close> col2__eq par_strict_not_col_1) 
                  }
                  moreover {
                    assume "A \<noteq> C' \<and> A' \<noteq> PO \<and> Col A A' PO \<and> Col C' A' PO"
                    hence False
                      by (metis \<open>A \<noteq> PO\<close> \<open>PO E' Par PO A'\<close> assms col2__eq 
                          col_permutation_4 col_permutation_5 grid_ok par_id_1) 
                  }
                  ultimately have ?thesis
                    using Par_def \<open>A C' Par A' PO\<close> by blast
                }
                moreover {
                  assume "A = C'"
                  hence False
                    by (metis \<open>A = C'\<close> \<open>A C' Proj A' P' PO E'\<close> \<open>Col PO E PO\<close> 
                        \<open>PO E Par A' P'\<close> \<open>PO E' Par PO A'\<close> \<open>PO \<noteq> E\<close> assms grid_ok not_strict_par1 
                        par_col2_par_bis par_id_3 project_col) 
                }
                ultimately show ?thesis
                  using Proj_def \<open>A C' Proj A' P' PO E'\<close> by fastforce 
              qed
              have "PO A Par A' C'" 
              proof (rule par_col_par [of _ _ _ _ "P'"])
                show "A' \<noteq> C'"
                  using \<open>A C' ParStrict A' PO\<close> col_trivial_1 par_strict_not_col_2 by blast 
                show "PO A Par A' P'"
                  using \<open>A \<noteq> PO\<close> \<open>PO E Par A' P'\<close> assms par_col_par_2 by auto 
                show "Col A' P' C'"
                  using Proj_def \<open>A C' Proj A' P' PO E'\<close> by auto 
              qed
              thus "A PO Par C' A'"
                using par_comm by blast 
            qed
            have "Parallelogram A PO MA PO"
              by (metis Bet_cases Cong_cases \<open>A \<midarrow> PO \<midarrow> MA\<close> \<open>A \<noteq> PO\<close> \<open>Cong PO MA A PO\<close> 
                  bet_col1 between_cong_3 between_equality_2 between_trivial col_par 
                  par_cong_plg_2 plg_bet1 point_construction_different) 
            hence "Parallelogram C' A' MA PO"
              by (metis Plg_perm \<open>Plg A C' A' PO\<close> parallelogram_equiv_plg plg_pseudo_trans) 
            hence "C' A' Par MA PO \<and> C' PO Par A' MA"
              by (metis par_distincts \<open>A \<noteq> PO\<close> \<open>Col PO E MA\<close> \<open>PO E' Par PO A'\<close> 
                  \<open>PO \<noteq> E\<close> \<open>Parallelogram A PO MA PO\<close> grid_ok not_par_not_col par_col_par 
                  par_id_3 plg_par plg_permut) 
            thus ?thesis
              by (metis Par_cases par_distincts \<open>MA A' Proj PO E' E E'\<close> 
                  not_par_one_not_par project_par_dir) 
          qed
          thus "C' PO Par E E' \<or> C' = PO" 
            by simp
        qed
      qed
    qed
    thus "Col PO E A \<and> 
          (\<exists>A' C' P'. MA A' Proj PO E' E E' \<and> PO E Par A' P' \<and> A C' Proj A' P' PO E' \<and> 
                      C' PO Proj PO E E E')" 
      using assms by blast
  qed
qed

lemma sum_A_O:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E A"
  shows "Sum PO E E' A PO A" 
proof (unfold Sum_def,rule conjI)
  show "Ar2 PO E E' A PO A"
    by (simp add: Ar2_def assms(2) col_trivial_3 grid_ok) 
  have "PO \<noteq> E"
    using grid_ok not_col_distincts by auto 
  have "E \<noteq> E'"
    using col_trivial_2 grid_ok by blast 
  show "\<exists>A' C'. E E' Pj A A' \<and> Col PO E' A' \<and> PO E Pj A' C' \<and> PO E' Pj PO C' \<and> E' E Pj C' A"
  proof (cases)
    assume "PO = A"
    thus ?thesis
      using not_col_distincts pj_trivial by blast 
  next
    assume "PO \<noteq> A"
    have "\<not> E E' Par PO E'"
      using grid_ok par_comm par_id_4 by blast
    have " \<not> A PO Par E' E"
      by (meson Par_cases assms col_trivial_1 grid_ok not_col_permutation_4 
          par_trans parallel_uniqueness) 
    then obtain A' where "A A' Proj PO E' E E'" 
      using project_existence [of A PO E' E E'] by (metis \<open>E \<noteq> E'\<close> \<open>\<not> E E' Par PO E'\<close> 
          col_trivial_3 grid_ok project_existence)
    hence "E E' Pj A A'"
      using Pj_def par_symmetry project_par_dir by blast 
    moreover have "Col PO E' A'"
      using Proj_def \<open>A A' Proj PO E' E E'\<close> by presburger 
    moreover have "PO E Pj A' A'"
      by (simp add: pj_trivial) 
    moreover have "PO E' Pj PO A'"
      using Pj_def calculation(2) grid_ok not_col_distincts not_par_not_col by blast 
    moreover have "E' E Pj A' A"
      using Pj_def calculation(1) par_comm by blast 
    ultimately show ?thesis
      by blast 
  qed
qed

lemma sum_O_B:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E B"
  shows "Sum PO E E' PO B B"
  by (metis Ar2_def Pj_def Sum_def assms grid_ok not_col_distincts not_par_not_col) 

lemma opp0_uniqueness:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Opp PO E E' PO M"
  shows "M = PO"
  by (meson Ar2_def Opp_def Sum_def assms sum_A_O sum_uniqueness)

lemma proj_pars:
  assumes grid_ok: "\<not> Col PO E E'"
    and "A \<noteq> PO"
    and "Col PO E A"
    and "PO E Par A' C'"
    and "A A' Proj PO E' E E'"
  shows "PO E ParStrict A' C'" 
proof (unfold ParStrict_def, rule+)
  show "Coplanar PO E A' C'"
    by (simp add: all_coplanar) 
  have "\<not> Col PO E E'"
    by (simp add: grid_ok) 
  show "\<nexists>X. Col X PO E \<and> Col X A' C'" 
  proof (rule ccontr, safe)
    fix X
    assume "\<not> False" and "Col X PO E" and "Col X A' C'"
    show False 
    proof (cases)
      assume "PO = A'"
      thus ?thesis
        by (metis Par_def Proj_def assms(2) assms(3) assms(5) col_permutation_2 
            grid_ok par_strict_not_col_1) 
    next
      assume "PO \<noteq> A'"
      hence False 
        by (metis Proj_def \<open>Col X A' C'\<close> \<open>Col X PO E\<close> assms(4) assms(5) 
            col_permutation_1 col_transitivity_2 grid_ok not_strict_par) 
      thus ?thesis 
        by simp
    qed
  qed
qed

lemma sum_O_B_eq:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' PO B C"
  shows "B = C"
  by (metis Ar2_def Sum_def assms sum_O_B sum_uniqueness) 

lemma sum_A_O_eq:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A PO C"
  shows "A = C"
  by (metis Ar2_def Sum_def assms sum_A_O sum_uniqueness)

lemma sum_A_B_A:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B A"
  shows "B = PO" 
proof -
  obtain A' C' where "E E' Pj A A'" and "Col PO E' A'" and "PO E Pj A' C'" and 
    "PO E' Pj B C'" and "E' E Pj C' A" 
    using Sum_def assms by blast 
  show ?thesis
  proof (cases)
    assume "A = PO"
    thus ?thesis
      using assms sum_O_B_eq by blast 
  next
    assume "A \<noteq> PO"
    hence "A' \<noteq> PO \<and> (PO E ParStrict A' C' \<or> B = PO)"
      using Sum_def \<open>Col PO E' A'\<close> \<open>E E' Pj A A'\<close> \<open>E' E Pj C' A\<close> \<open>PO E Pj A' C'\<close> 
        \<open>PO E' Pj B C'\<close> assms(2) grid_ok sum_par_strict by blast
    moreover {
      assume "PO E ParStrict A' C'" and "B \<noteq> PO"
      hence "A A' Par A C'"
        by (metis Ar2_def NCol_perm Par_cases Par_strict_cases Pj_def Sum_def 
            \<open>E E' Pj A A'\<close> \<open>E' E Pj C' A\<close> assms(2) par_strict_not_col_2 par_trans) 
      hence False
        by (metis Ar2_def Sum_def \<open>PO E ParStrict A' C'\<close> assms(2) not_strict_par1 
            par_id_2 par_strict_not_col_1 par_strict_par) 
    }
    ultimately show ?thesis
      by blast
  qed
qed

lemma sum_A_B_B:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B B"
  shows "A = PO" 
proof -
  obtain A' C' where "E E' Pj A A'" and "Col PO E' A'" and "PO E Pj A' C'" and 
    "PO E' Pj B C'" and "E' E Pj C' B" 
    using Sum_def assms by blast 
  show ?thesis
  proof (cases)
    assume "A = PO"
    thus ?thesis
      using assms sum_O_B_eq by blast 
  next
    assume "A \<noteq> PO"
    hence "A' \<noteq> PO \<and> (PO E' ParStrict B C' \<or> B = C')"
      by (metis NCol_perm Par_def Pj_def Sum_def \<open>E E' Pj A A'\<close> \<open>E' E Pj C' B\<close> 
          \<open>PO E' Pj B C'\<close> assms par_not_col_strict par_strict_not_col_3 
          sum_par_strict_a)
    moreover {
      assume "PO E' ParStrict B C'" 
      hence False
        by (metis Par_cases Pj_def \<open>E' E Pj C' B\<close> \<open>PO E' Pj B C'\<close> grid_ok 
            not_col_distincts not_par_one_not_par par_id_2 par_strict_not_col_2) 
    }
    ultimately show ?thesis
      by (smt (verit, best) Ar2_def NCol_perm Pj_def Sum_def \<open>Col PO E' A'\<close> 
          \<open>PO E Pj A' C'\<close> assms col_trivial_3 grid_ok not_col_permutation_4 
          not_par_not_col parallel_uniqueness) 
  qed
qed

lemma sum_uniquenessB:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A X C"
    and "Sum PO E E' A Y C"
  shows "X = Y" 
proof (cases)
  assume "A = PO"
  thus ?thesis 
    using grid_ok assms(2) assms(3) sum_O_B_eq by blast
next
  assume "A \<noteq> PO"
  obtain A'' C'' where "E E' Pj A A''" and "Col PO E' A''" and "PO E Pj A'' C''" and 
    "PO E' Pj Y C''" and "E' E Pj C'' C"
    using Sum_def assms(3) by auto
  obtain A' C' where "E E' Pj A A'" and "Col PO E' A'" and "PO E Pj A' C'" and 
    "PO E' Pj X C'" and "E' E Pj C' C"
    using Sum_def assms(2) by blast 
  have "A' \<noteq> PO \<and> (PO E ParStrict A' C' \<or> X = PO)"
    using Sum_def \<open>A \<noteq> PO\<close> \<open>Col PO E' A'\<close> \<open>E E' Pj A A'\<close> \<open>E' E Pj C' C\<close> 
      \<open>PO E Pj A' C'\<close> \<open>PO E' Pj X C'\<close> assms(2) grid_ok sum_par_strict by blast
  have "A'' \<noteq> PO \<and> (PO E ParStrict A'' C'' \<or> Y = PO)"
    using Sum_def \<open>A \<noteq> PO\<close> \<open>Col PO E' A''\<close> \<open>E E' Pj A A''\<close> \<open>E' E Pj C'' C\<close> 
      \<open>PO E Pj A'' C''\<close> \<open>PO E' Pj Y C''\<close> assms(3) grid_ok sum_par_strict by blast
  show ?thesis 
  proof (cases)
    assume "X = PO" 
    thus ?thesis
      using grid_ok assms(2) assms(3) sum_A_B_A sum_A_O_eq by blast 
  next 
    assume "X \<noteq> PO"
    {
      assume "E E' Par A A''" 
      {
        assume "E E' Par A A'"
        have "A A' Par A A''"
          by (meson \<open>E E' Par A A''\<close> \<open>E E' Par A A'\<close> par_symmetry par_trans) 
        {
          assume "A A' ParStrict A A''"
          hence ?thesis
            using not_par_strict_id by auto 
        }
        moreover
        {
          assume "A \<noteq> A'" and "A \<noteq> A''" and "Col A A A''" and "Col A' A A''"
          have "\<not> Col PO E' A"
            using grid_ok \<open>Col PO E' A''\<close> \<open>E E' Par A A''\<close> grid_not_par 
              par_col2_par_bis par_symmetry by blast 
          hence "A' = A''"
            using Col_perm \<open>Col A' A A''\<close> \<open>Col PO E' A''\<close> \<open>Col PO E' A'\<close> colx by blast 
          {
            assume "PO E ParStrict A' C''"
            {
              assume "PO E ParStrict A' C'"
              have "A' C' Par A' C''"
                by (meson Par_strict_cases \<open>PO E ParStrict A' C''\<close> 
                    \<open>PO E ParStrict A' C'\<close> par_strict_trans)
              moreover {
                assume "A' C' ParStrict A' C''"
                hence ?thesis
                  using \<open>A' C' ParStrict A' C''\<close> not_par_strict_id by auto 
              }
              moreover {
                assume "A' \<noteq> C'" and "A' \<noteq> C''" and "Col A' A' C''" and "Col C' A' C''"
                {
                  assume "E' E Par C' C"
                  have "C C' Par C C''"
                    by (metis Ar2_def Par_strict_cases Pj_def Sum_def 
                        \<open>E' E Par C' C\<close> \<open>E' E Pj C'' C\<close> \<open>PO E ParStrict A' C''\<close> assms(2) 
                        par_not_par par_right_comm par_strict_not_col_1 par_symmetry) 
                  moreover {
                    assume "C C' ParStrict C C''"
                    hence ?thesis
                      by (simp add: not_par_strict_id) 
                  }
                  moreover {
                    assume "C \<noteq> C'" and "C \<noteq> C''" and "Col C C C''" and "Col C' C C''"
                    hence "C' = C''"
                      by (metis Pj_def \<open>A' C' Par A' C''\<close> \<open>E' E Pj C'' C\<close> 
                          \<open>PO E ParStrict A' C'\<close> calculation(1) col2__eq col_par_par_col grid_ok 
                          par_id par_right_comm par_strict_par par_symmetry par_trans) 
                    {
                      assume "PO E' Par Y C'"
                      {
                        assume "PO E' Par X C'"
                        hence "Y C' Par X C'"
                          using Par_cases \<open>PO E' Par Y C'\<close> par_trans by blast 
                        {
                          assume "Y C' ParStrict X C'"
                          hence ?thesis
                            using not_par_strict_id par_strict_comm by blast 
                        }
                        moreover {
                          assume "Y \<noteq> C'" and "X \<noteq> C'" and "Col Y X C'" and "Col C' X C'"
                          have "\<not> Col PO E C'"
                            using \<open>PO E ParStrict A' C'\<close> par_strict_not_col_4 by blast 
                          hence ?thesis
                            by (metis Ar2_def Sum_def \<open>Col Y X C'\<close> grid_ok assms(2)
                                assms(3) col3 not_col_distincts) 
                        }
                        ultimately have ?thesis
                          using Par_def \<open>Y C' Par X C'\<close> by blast 
                      }
                      moreover {
                        assume "X = C'"
                        hence ?thesis
                          using Ar2_def Sum_def \<open>A' \<noteq> PO \<and> (PO E ParStrict A' C' \<or> X = PO)\<close> 
                            \<open>X \<noteq> PO\<close> assms(2) par_strict_not_col_4 by blast 
                      }
                      ultimately have ?thesis
                        using Pj_def \<open>PO E' Pj X C'\<close> by blast 
                    }
                    moreover {
                      assume "Y = C'"
                      hence False
                        using Ar2_def Sum_def \<open>A' \<noteq> PO \<and> (PO E ParStrict A' C' \<or> X = PO)\<close> 
                          \<open>X \<noteq> PO\<close> assms(3) par_strict_not_col_4 by blast 
                    }
                    ultimately have ?thesis
                      using Pj_def \<open>C' = C''\<close> \<open>PO E' Pj Y C''\<close> by blast
                  }
                  ultimately have ?thesis
                    using Par_def by blast 
                }
                moreover {
                  assume "C' = C"
                  hence ?thesis
                    using Ar2_def Sum_def \<open>A' \<noteq> PO \<and> (PO E ParStrict A' C' \<or> X = PO)\<close> 
                      \<open>X \<noteq> PO\<close> assms(2) par_strict_not_col_4 by force 
                }
                ultimately have ?thesis
                  using Pj_def \<open>E' E Pj C' C\<close> by blast 
              }
              ultimately have ?thesis
                using Par_def by blast 
            } 
            moreover {
              assume "X = PO"
              hence ?thesis
                by (simp add: \<open>X \<noteq> PO\<close>) 
            }
            ultimately have ?thesis
              using \<open>A' \<noteq> PO \<and> (PO E ParStrict A' C' \<or> X = PO)\<close> by blast 
          }
          moreover {
            assume "Y = PO"
            hence ?thesis
              using grid_ok assms(2) assms(3) sum_A_B_A sum_A_O_eq by blast 
          }
          ultimately have ?thesis
            using \<open>A' = A''\<close> \<open>A'' \<noteq> PO \<and> (PO E ParStrict A'' C'' \<or> Y = PO)\<close> by blast           
        }
        ultimately have ?thesis
          using Par_def \<open>A A' Par A A''\<close> by blast 
      }
      hence ?thesis
        by (metis grid_ok Pj_def \<open>Col PO E' A''\<close> \<open>Col PO E' A'\<close> \<open>E E' Par A A''\<close> 
            \<open>E E' Pj A A'\<close> grid_not_par par_col2_par_bis par_symmetry) 
    }
    thus ?thesis
      by (metis Ar2_def Pj_def Sum_def \<open>A'' \<noteq> PO \<and> (PO E ParStrict A'' C'' \<or> Y = PO)\<close> 
          \<open>E E' Pj A A''\<close> assms(2) assms(3) par_strict_not_col_1 sum_A_B_A sum_A_O_eq) 
  qed
qed

lemma sum_uniquenessA:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' X B C"
    and "Sum PO E E' Y B C"
  shows "X = Y" 
proof (cases)
  assume "B = PO"
  thus ?thesis
    using grid_ok assms(2) assms(3) sum_A_O_eq by blast 
next
  assume "B \<noteq> PO"
  obtain A'' C'' where "E E' Pj Y A''" and "Col PO E' A''" and "PO E Pj A'' C''" and 
    "PO E' Pj B C''" and "E' E Pj C'' C"
    using Sum_def assms(3) by blast 
  obtain A' C' where "E E' Pj X A'" and "Col PO E' A'" and "PO E Pj A' C'" and 
    "PO E' Pj B C'" and "E' E Pj C' C"
    using Sum_def assms(2) by blast 
  show ?thesis 
  proof (cases)
    assume "X = PO"
    thus ?thesis
      using grid_ok assms(2) assms(3) sum_A_B_B sum_O_B_eq by blast 
  next
    assume "X \<noteq> PO"
    show ?thesis 
    proof (cases)
      assume "Y = PO"
      thus ?thesis
        using grid_ok assms(2) assms(3) sum_A_B_B sum_O_B_eq by blast 
    next
      assume "Y \<noteq> PO"
      have "A' \<noteq> PO \<or> (PO E ParStrict A' C' \<or> B = PO)"
        using Sum_def \<open>E E' Pj X A'\<close> \<open>X \<noteq> PO\<close> grid_ok assms(2) sum_par_strict_a by blast 
      have "A'' \<noteq> PO \<or> (PO E ParStrict A'' C'' \<or> B = PO)"
        using Sum_def \<open>E E' Pj Y A''\<close> \<open>Y \<noteq> PO\<close> grid_ok assms(3) sum_par_strict_a by blast
      {
        assume "PO E' Par B C''"
        {
          assume "PO E' Par B C'"
          {
            assume "B C' ParStrict B C''"
            hence ?thesis
              by (simp add: not_par_strict_id) 
          }
          moreover {
            assume "B \<noteq> C'" and "B \<noteq> C''" and "Col B B C''" and "Col C' B C''"
            {
              assume "E' E Par C'' C"
              {
                assume "E' E Par C' C"
                have "C C' Par C C''"
                  by (meson \<open>E' E Par C' C\<close> \<open>E' E Par C'' C\<close> par_left_comm par_symmetry par_trans) 
                {
                  assume "C C' ParStrict C C''"
                  hence ?thesis
                    by (simp add: not_par_strict_id) 
                }
                moreover {
                  assume "C \<noteq> C'" and "C \<noteq> C''" and "Col C C C''" and "Col C' C C''"
                  have "\<not> Col C C' B"
                    by (metis grid_ok \<open>B \<noteq> C'\<close> \<open>C \<noteq> C'\<close> \<open>E' E Par C' C\<close> 
                        \<open>PO E' Par B C'\<close> col_par col_permutation_3 grid_not_par 
                        not_par_one_not_par par_left_comm) 
                  hence "C' = C''"
                    using Col_cases \<open>C C' Par C C''\<close> \<open>Col C' B C''\<close> 
                      col2__eq par_id by blast 
                  {
                    assume "PO E ParStrict A' C'"
                    {
                      assume "PO E ParStrict A'' C'"
                      have "A' C' Par A'' C'"
                        using Par_strict_perm \<open>PO E ParStrict A' C'\<close> 
                          \<open>PO E ParStrict A'' C'\<close> par_strict_trans by blast 
                      {
                        assume "A' C' ParStrict A'' C'" 
                        hence ?thesis
                          using not_par_strict_id par_strict_comm by blast 
                      }
                      moreover {
                        assume "A' \<noteq> C'" and "A'' \<noteq> C'" and "Col A' A'' C'" and "Col C' A'' C'"
                        have "\<not> Col PO E' C'"
                          by (metis grid_ok \<open>Col PO E' A'\<close> \<open>PO E ParStrict A' C'\<close> 
                              col2__eq col_permutation_2 grid_not_par_5 
                              par_strict_not_col_3)  
                        hence "A' = A''"
                          using \<open>Col A' A'' C'\<close> \<open>Col PO E' A''\<close> \<open>Col PO E' A'\<close> colx by blast 
                        {
                          assume "E E' Par Y A'"
                          {
                            assume "E E' Par X A'"
                            have "Y A' Par X A'"
                              by (meson \<open>E E' Par X A'\<close> \<open>E E' Par Y A'\<close> par_symmetry par_trans)
                            {
                              assume "Y A' ParStrict X A'"
                              hence ?thesis
                                using not_col_distincts par_strict_not_col_2 by blast 
                            }
                            moreover {
                              assume "Y \<noteq> A'" and "X \<noteq> A'" and "Col Y X A'" and "Col A' X A'"
                              have "\<not> Col PO E A'"
                                using \<open>PO E ParStrict A' C'\<close> par_strict_not_col_1 by auto
                              hence ?thesis 
                                using Sum_def Ar2_def \<open>Col Y X A'\<close> \<open>E E' Par X A'\<close> 
                                  grid_not_par not_col_distincts par_col2_par_bis par_symmetry 
                                by (smt (verit, ccfv_threshold) assms(2) assms(3)) 
                            }
                            ultimately have ?thesis
                              using Par_def \<open>Y A' Par X A'\<close> by blast 
                          }
                          moreover {
                            assume "X = A'"
                            hence ?thesis
                              using Ar2_def Sum_def \<open>PO E ParStrict A' C'\<close> 
                                par_strict_not_col_1 by (metis assms(2)) 
                          }
                          ultimately have ?thesis
                            using Pj_def \<open>E E' Pj X A'\<close> by blast 
                        }
                        moreover {
                          assume "Y = A'"
                          hence ?thesis
                            using Ar2_def Sum_def \<open>PO E ParStrict A' C'\<close> assms(3) 
                              par_strict_not_col_1 by auto 
                        }
                        ultimately have ?thesis
                          using Pj_def \<open>A' = A''\<close> \<open>E E' Pj Y A''\<close> by blast 
                      }
                      ultimately have ?thesis
                        using Par_def \<open>A' C' Par A'' C'\<close> by presburger 
                    }
                    moreover {
                      assume "B = PO"
                      hence ?thesis
                        by (simp add: \<open>B \<noteq> PO\<close>) 
                    }
                    ultimately have ?thesis
                      using Sum_def \<open>C' = C''\<close> \<open>Col PO E' A''\<close> \<open>E E' Pj Y A''\<close> 
                        \<open>E' E Pj C'' C\<close> \<open>PO E Pj A'' C''\<close> \<open>PO E' Pj B C''\<close> \<open>Y \<noteq> PO\<close> 
                        sum_par_strict_b 
                        assms(3) grid_ok by blast 
                  }
                  moreover {
                    assume "B = PO"
                    hence ?thesis
                      by (simp add: \<open>B \<noteq> PO\<close>) 
                  }
                  ultimately have ?thesis
                    using Sum_def \<open>Col PO E' A'\<close> \<open>E E' Pj X A'\<close> \<open>E' E Pj C' C\<close> 
                      \<open>PO E Pj A' C'\<close> \<open>PO E' Pj B C'\<close> \<open>X \<noteq> PO\<close> sum_par_strict_b 
                      assms(2) grid_ok by blast 
                }
                ultimately have ?thesis
                  using Par_def \<open>C C' Par C C''\<close> by blast 
              }
              moreover {
                assume "C' = C"
                hence False
                  by (metis Ar2_def Sum_def \<open>PO E' Par B C'\<close> assms(2) 
                      grid_not_par par_col2_par_bis par_symmetry) 
              }
              ultimately have ?thesis
                using Pj_def \<open>E' E Pj C' C\<close> by blast 
            }
            moreover {
              assume "C'' = C"
              hence ?thesis
                by (metis Ar2_def Sum_def \<open>PO E' Par B C''\<close> assms(2) 
                    grid_not_par par_col2_par_bis par_symmetry) 
            }
            ultimately have ?thesis
              using Pj_def \<open>E' E Pj C'' C\<close> by blast 
          }
          ultimately have ?thesis
            by (metis not_col_distincts \<open>PO E' Par B C''\<close> \<open>PO E' Par B C'\<close> 
                par_distinct par_id_1 par_symmetry par_trans) 
        }
        moreover {
          assume "B = C'"
          hence ?thesis
            using Ar2_def Par_cases Pj_def Sum_def \<open>E' E Pj C' C\<close> grid_ok 
              assms(2) assms(3) grid_not_par par_col2_par_bis sum_A_B_B 
            by (smt (verit, ccfv_threshold)) 
        }
        ultimately have ?thesis
          using Pj_def \<open>PO E' Pj B C'\<close> by blast 
      } 
      moreover {
        assume "B = C''"
        hence ?thesis
          using Ar2_def Par_cases Pj_def Sum_def \<open>E' E Pj C'' C\<close> \<open>X \<noteq> PO\<close> 
            assms(1) grid_not_par par_col2_par_bis sum_A_B_B 
          by (smt (verit, del_insts) assms(2)) 
      }
      ultimately show ?thesis
        using Pj_def \<open>PO E' Pj B C''\<close> by blast 
    qed
  qed
qed

lemma sum_B_null:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B A"
  shows "B = PO"
  using assms sum_A_B_A by auto 

lemma sum_A_null:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B B"
  shows "A = PO"
  using assms sum_A_B_B by force 

lemma sum_plg:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B C"
    and "(A \<noteq> PO ) \<or> ( B \<noteq> PO)"
  shows "\<exists> A' C'. Plg PO B C' A' \<and> Plg C' A' A C" 
proof -
  obtain A' C' where "E E' Pj A A'" 
    and "Col PO E' A'"
    and "PO E Pj A' C'"
    and "PO E' Pj B C'" 
    and "E' E Pj C' C"
    using Sum_def assms(2) by auto
  show ?thesis 
  proof (cases)
    assume "B = PO"
    thus ?thesis
      by (metis Plg_triv assms(2) bet_col between_trivial between_trivial2 
          grid_not_par_5 grid_ok sum_A_O_eq) 
  next
    assume "B \<noteq> PO"
    show ?thesis 
    proof (cases)
      assume "A = PO"
      thus ?thesis
        by (metis grid_ok Plg_triv \<open>B \<noteq> PO\<close> assms(2) parallelogram_equiv_plg 
            plg_permut sum_O_B_eq) 
    next
      assume "A \<noteq> PO"
      have "A' \<noteq> PO"
        using Sum_def \<open>A \<noteq> PO\<close> \<open>E E' Pj A A'\<close> grid_ok assms(2) sum_par_strict_a by blast 
      have "PO E ParStrict A' C' \<or> B = PO"
        using Sum_def \<open>A \<noteq> PO\<close> \<open>Col PO E' A'\<close> \<open>E E' Pj A A'\<close> \<open>E' E Pj C' C\<close> 
          \<open>PO E Pj A' C'\<close> \<open>PO E' Pj B C'\<close> grid_ok assms(2) sum_par_strict_b by blast 
      moreover {
        assume "PO E ParStrict A' C'" 
        have "PO B Par C' A'"
          by (metis Sump_def par_col_par_2 \<open>B \<noteq> PO\<close> \<open>PO E ParStrict A' C'\<close> 
              assms(2) par_right_comm par_strict_par sum_to_sump) 
        hence "PO B ParStrict C' A'"
          using Par_def Par_strict_cases \<open>PO E ParStrict A' C'\<close> par_strict_not_col_2 by blast 
        {
          assume "PO E' Par B C'"
          hence "PO A' Par B C'"
            using \<open>A' \<noteq> PO\<close> \<open>Col PO E' A'\<close> par_col_par_2 by auto 
          hence "Plg PO B C' A'"
            by (simp add: \<open>PO B ParStrict C' A'\<close> pars_par_plg) 
          have "C' A' Par A C"
          proof (rule par_col_par [of _ _ _ _ "PO"])
            show "A \<noteq> C"
              using \<open>B \<noteq> PO\<close> assms(2) sum_B_null grid_ok by blast
            show "C' A' Par A PO"
              by (metis Ar2_def Par_cases Sum_def \<open>A \<noteq> PO\<close> \<open>PO E ParStrict A' C'\<close> 
                  assms(2) par_col_par_2 par_strict_par) 
            show "Col A PO C"
              by (metis Ar2_def Sum_def grid_ok assms(2) col3 grid_not_par) 
          qed
          have "C' A' ParStrict A C"
            by (metis Ar2_def Par_def Sum_def \<open>C' A' Par A C\<close> \<open>PO E ParStrict A' C'\<close> 
                assms(2) colx not_col_permutation_2 par_strict_not_col_1)
          {
            assume "E E' Par A A'"
            hence ?thesis
              by (metis Par_cases Pj_def \<open>C' A' ParStrict A C\<close> \<open>E' E Pj C' C\<close> 
                  \<open>Plg PO B C' A'\<close> not_col_distincts par_not_par 
                  par_strict_not_col_4 pars_par_plg) 
          }
          moreover {
            assume "A = A'"
            hence ?thesis
              using \<open>C' A' ParStrict A C\<close> col_trivial_2 par_strict_not_col_1 by blast 
          }
          ultimately have ?thesis
            using Pj_def \<open>E E' Pj A A'\<close> by blast 
        }
        moreover {
          assume "B = C'"
          hence ?thesis
            using \<open>PO B ParStrict C' A'\<close> not_col_distincts par_strict_not_col_2 by blast 
        }
        ultimately have ?thesis
          using Pj_def \<open>PO E' Pj B C'\<close> by blast 
      }
      ultimately show ?thesis
        using \<open>B \<noteq> PO\<close> by blast 
    qed
  qed
qed

lemma sum_cong:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B C"
    and "(A \<noteq> PO \<or> B \<noteq> PO)"
  shows "ParallelogramFlat PO A C B" 
proof (cases)
  assume "A = PO"
  thus ?thesis
    using grid_ok assms(2) assms(3) plgf_permut plgf_trivial1 sum_O_B_eq by blast 
next
  assume "A \<noteq> PO"
  obtain A' C' where "Plg PO B C' A'" and "Plg C' A' A C"
    using \<open>A \<noteq> PO\<close> grid_ok assms(2) sum_plg by blast 
  have "Parallelogram PO B C' A'"
    by (simp add: \<open>Plg PO B C' A'\<close> parallelogram_equiv_plg) 
  have "Parallelogram C' A' A C"
    using \<open>Plg C' A' A C\<close> plg_to_parallelogram by auto
  hence "Parallelogram PO B C A \<or> PO = B \<and> C' = A' \<and> A = C \<and> PO = A"
    by (simp add: \<open>Parallelogram PO B C' A'\<close> plg_pseudo_trans) 
  moreover {
    assume "Parallelogram PO B C A"
    moreover {
      assume "ParallelogramStrict PO B C A"
      hence ?thesis
        by (metis Ar2_def Plg_perm Sum_def col_transitivity_1 \<open>A \<noteq> PO\<close> 
            \<open>Parallelogram PO B C A \<or> PO = B \<and> C' = A' \<and> A = C \<and> PO = A\<close> assms(2) 
            grid_not_par plg_col_plgf) 
    }
    moreover {
      assume "ParallelogramFlat PO B C A"
      hence ?thesis
        using plgf_comm2 plgf_permut by blast 
    }
    ultimately have ?thesis
      using Parallelogram_def by blast 
  }
  moreover {
    assume "PO = B \<and> C' = A' \<and> A = C \<and> PO = A"
    hence ?thesis
      using \<open>A \<noteq> PO\<close> by auto 
  }
  ultimately show ?thesis 
    by blast
qed

lemma sum_cong2:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B C"
    and "(A \<noteq> PO \<or> B \<noteq> PO)"
  shows "Cong PO A B C \<and> Cong PO B A C"
  using grid_ok assms(3) assms(2) not_cong_1243 plgf_cong sum_cong by blast 

lemma sum_comm:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B C"
  shows "Sum PO E E' B A C" 
proof (cases "B = PO")
  show "B = PO \<Longrightarrow> Sum PO E E' B A C"
    by (metis Ar2_def Sum_def assms sum_A_O_eq sum_O_B) 
  show "B \<noteq> PO \<Longrightarrow> Sum PO E E' B A C" 
  proof (cases "A = PO")
    show "B \<noteq> PO \<Longrightarrow> A = PO \<Longrightarrow> Sum PO E E' B A C"
      by (metis Ar2_def Sum_def assms sum_A_O sum_O_B_eq) 
    show "B \<noteq> PO \<Longrightarrow> A \<noteq> PO \<Longrightarrow> Sum PO E E' B A C" 
    proof -
      obtain A' C' where "Plg PO B C' A'" and "Plg C' A' A C"
        by (metis Plg_triv assms grid_not_par sum_A_O_eq sum_plg)
      obtain B' where "B B' Proj PO E' E E'"
        by (metis grid_ok Par_cases grid_not_par project_existence)
      obtain P' where "PO E Par B' P'"
        using grid_ok grid_not_par parallel_existence1 by presburger
      obtain D' where "A D' Proj B' P' PO E'"
        by (metis \<open>PO E Par B' P'\<close> grid_ok grid_not_par not_par_one_not_par 
            par_neq2 project_existence)
      have "Ar2 PO E E' A B C"
        using Sum_def assms by blast
      moreover have "D' C Proj PO E E E'" 
      proof (unfold Proj_def, intro conjI)
        show "PO \<noteq> E"
          using \<open>PO E Par B' P'\<close> par_neq1 by auto 
        show "E \<noteq> E'"
          using grid_ok not_col_distincts by blast
        show "\<not> PO E Par E E'"
          using grid_ok grid_not_par by auto 
        show "Col PO E C"
          using Ar2_def calculation by blast 
        show "D' C Par E E' \<or> D' = C" 
        proof -
          have "B' \<noteq> P' \<and> PO \<noteq> E' \<and> \<not> B' P' Par PO E' \<and> (A D' Par PO E' \<or> A = D')"
            using Proj_def \<open>A D' Proj B' P' PO E'\<close> by presburger
          moreover {
            assume "A D' Par PO E'"
            hence "A D' ParStrict PO E' \<or> (A \<noteq> D' \<and> PO \<noteq> E' \<and> Col A PO E' \<and> Col D' PO E')"
              by (simp add: Par_def) 
            moreover {
              assume "A D' ParStrict PO E'"
              have "Col B' P' D'"
                using Proj_def \<open>A D' Proj B' P' PO E'\<close> by presburger 
              have "D' C Proj PO E E E'" 
              proof -
                {
                  assume "PO A ParStrict B' D'"
                  hence "PO B' Par A D'"
                    by (metis Par_cases Proj_def \<open>A D' Par PO E'\<close> \<open>B B' Proj PO E' E E'\<close> 
                        col_trivial_3 par_col_par_2 par_strict_not_col_3) 
                  hence "Plg PO A D' B'"
                    by (simp add: \<open>PO A ParStrict B' D'\<close> par_strict_right_comm pars_par_plg) 
                  hence "Parallelogram D' B' B C \<or> D' = B' \<and> PO = A \<and> C = B \<and> D' = C"
                    by (metis Plg_perm \<open>Plg C' A' A C\<close> \<open>Plg PO B C' A'\<close> 
                        plg_pseudo_trans plg_to_parallelogram) 
                  moreover {
                    assume "Parallelogram D' B' B C" 
                    hence "B' B Par C D'"
                      by (metis Ar2_def Par_cases par_distincts \<open>Ar2 PO E E' A B C\<close> 
                          \<open>B B' Proj PO E' E E'\<close> \<open>PO A ParStrict B' D'\<close> \<open>PO B' Par A D'\<close> 
                          par_strict_distinct plg_par_2 proj_id) 
                    hence "D' C Par E E' \<or> D' = C"
                      by (metis Par_cases par_distincts 
                          \<open>B B' Proj PO E' E E'\<close> par_not_par project_par_dir) 
                    hence ?thesis
                      using \<open>B' B Par C D'\<close> \<open>Col PO E C\<close> \<open>PO \<noteq> E\<close> \<open>\<not> PO E Par E E'\<close> 
                        par_col_project par_distinct by blast 
                  }
                  moreover {
                    assume "D' = B' \<and> PO = A \<and> C = B \<and> D' = C" 
                    hence ?thesis
                      using \<open>A D' ParStrict PO E'\<close> not_par_strict_id by force 
                  }
                  ultimately have ?thesis 
                    by blast
                }
                moreover {
                  assume "PO \<noteq> A" and "B' \<noteq> D'" and "Col PO B' D'" and "Col A B' D'"
                  hence False
                    by (meson Col_perm Proj_def \<open>A D' ParStrict PO E'\<close> 
                        \<open>B B' Proj PO E' E E'\<close> par_not_col) 
                }
                ultimately show ?thesis
                  by (metis Ar2_def Par_def Proj_def \<open>A D' ParStrict PO E'\<close> 
                      \<open>Ar2 PO E E' A B C\<close> \<open>B B' Proj PO E' E E'\<close> \<open>Col B' P' D'\<close> \<open>PO E Par B' P'\<close> 
                      col_trivial_2 not_par_strict_id not_strict_par2 par_col_par par_col_par_2 
                      par_strict_not_col_4) 
              qed
              hence ?thesis
                using Proj_def by auto 
            }
            moreover {
              assume "A \<noteq> D'" and "PO \<noteq> E'" and "Col A PO E'" and "Col D' PO E'"
              hence ?thesis
                by (smt (verit, ccfv_threshold) Ar2_def NCol_cases Par_cases Pj_def 
                    Proj_def Sum_def \<open>A D' Proj B' P' PO E'\<close> \<open>Ar2 PO E E' A B C\<close> \<open>B B' Proj PO E' E E'\<close> 
                    assms l6_16_1 par_col2_par_bis par_id) 
            }
            ultimately have ?thesis
              by blast 
          }
          moreover {
            assume "A = D'"
            hence ?thesis
              by (metis Ar2_def Proj_def \<open>A D' Proj B' P' PO E'\<close> \<open>Ar2 PO E E' A B C\<close> 
                  \<open>B B' Proj PO E' E E'\<close> \<open>PO E Par B' P'\<close> assms inter_uniqueness_not_par 
                  proj_id sum_A_O_eq) 
          }
          ultimately show ?thesis 
            by blast
        qed
      qed
      ultimately show ?thesis
        using \<open>B B' Proj PO E' E E'\<close> \<open>PO E Par B' P'\<close> \<open>A D' Proj B' P' PO E'\<close> 
          Ar2_def Sump_def sump_to_sum by blast
    qed
  qed
qed

lemma cong_sum:
  assumes grid_ok: "\<not> Col PO E E'"
    and "PO \<noteq> C \<or> B \<noteq> A"
    and "Ar2 PO E E' A B C"
    and "Cong PO A B C"
    and "Cong PO B A C"
  shows "Sum PO E E' A B C" 
proof (cases)
  assume "A = PO"
  thus ?thesis
    using Ar2_def assms(3) assms(4) cong_reverse_identity sum_O_B by blast 
next
  assume "A \<noteq> PO"
  show ?thesis 
  proof (cases)
    assume "B = PO"
    thus ?thesis
      using Ar2_def assms(3) assms(5) cong_reverse_identity sum_A_O by blast 
  next
    assume "B \<noteq> PO"
    have " \<not> Col PO E E'"
      by (simp add: grid_ok) 
    have "Col PO E A"
      using Ar2_def assms(3) by blast 
    have "Col PO E B"
      using Ar2_def assms(3) by force 
    have "Col PO E C"
      using Ar2_def assms(3) by blast 
    have "\<not> PO E Par E E' \<and> \<not> PO E Par PO E' \<and> \<not> PO E' Par E E' \<and> PO \<noteq> E \<and> PO \<noteq> E' \<and> E \<noteq> E'"
      using grid_ok grid_not_par by blast
    hence "\<not> E E' Par PO E'"
      using Par_cases by auto
    then obtain A' where "A A' Proj PO E' E E'"
      using project_existence [of A PO E' E E'] grid_ok grid_not_par 
        project_existence by presburger 
    hence "Col PO E' A' \<and> (A A' Par E E' \<or> A = A')"
      using Proj_def by simp
    then obtain P' where "PO E Par A' P'"
      using grid_ok grid_not_par parallel_existence1 by presburger 
    obtain C' where "B C' Proj A' P' PO E'"
      by (metis \<open>PO E Par A' P'\<close> grid_ok grid_not_par not_par_one_not_par 
          par_neq2 project_existence) 
    have "E E' Pj A A'"
      using Pj_def \<open>Col PO E' A' \<and> (A A' Par E E' \<or> A = A')\<close> par_symmetry by blast 
    moreover have "Col PO E' A'"
      by (simp add: \<open>Col PO E' A' \<and> (A A' Par E E' \<or> A = A')\<close>) 
    moreover have "PO E Pj A' C'"
      by (metis Pj_def Proj_def \<open>B C' Proj A' P' PO E'\<close> \<open>PO E Par A' P'\<close> par_col_par) 
    moreover have "PO E' Pj B C'"
      by (metis Pj_def Proj_def \<open>B C' Proj A' P' PO E'\<close> par_symmetry) 
    moreover have "E' E Pj C' C" 
    proof -
      {
        assume "A' = C'"
        {
          assume "B A' Par PO E'"
          moreover {
            assume "B A' ParStrict PO E'"
            hence False
              using \<open>Col PO E' A'\<close> not_col_permutation_1 par_strict_not_col_2 by blast 
          }
          moreover {
            assume "B \<noteq> A'" and "PO \<noteq>  E'" and "Col B PO E'" and "Col A' PO E'"
            hence False
              using \<open>B \<noteq> PO\<close> \<open>Col PO E B\<close> col_transitivity_2 grid_ok 
                not_col_permutation_1 by blast 
          }
          ultimately have False
            using Par_def by blast 
        }
        moreover {
          assume "B = A'"
          hence False
            using \<open>A A' Proj PO E' E E'\<close> \<open>A \<noteq> PO\<close> \<open>Col PO E A\<close> \<open>Col PO E B\<close> 
              grid_ok proj_id by blast 
        }
        ultimately have False
          using Proj_def \<open>A' = C'\<close> \<open>B C' Proj A' P' PO E'\<close> by force 
      }
      have "PO B ParStrict A' C'"
        by (metis NCol_perm Par_def Pj_def par_col_par_2 \<open>A \<noteq> PO\<close> \<open>A' = C' \<Longrightarrow> False\<close> 
            \<open>B \<noteq> PO\<close> \<open>Col PO E B\<close> assms(3) calculation(1) calculation(2) calculation(3) 
            col_trivial_3 colx grid_ok sum_par_strict_a) 
      hence "PO B ParStrict C' A'"
        using par_strict_right_comm by blast 
      moreover have "PO A' Par B C'"
        by (metis Pj_def Proj_def \<open>A A' Proj PO E' E E'\<close> \<open>A \<noteq> PO\<close> \<open>B C' Proj A' P' PO E'\<close> 
            \<open>Col PO E A\<close> \<open>Col PO E B\<close> grid_ok \<open>PO E Par A' P'\<close> \<open>PO E' Pj B C'\<close> col_trivial_3 
            not_strict_par1 par_col_par_2 proj_id) 
      ultimately have "Plg PO B C' A'"
        using pars_par_plg by auto 
      have "ParallelogramFlat PO B C A"
        by (metis Ar2_def ParallelogramFlat_def col_transitivity_1 assms(2) assms(3) 
            assms(4) assms(5) grid_not_par not_cong_1243) 
      hence "Parallelogram PO B C A"
        using Parallelogram_def by blast 
      hence "Plg PO B C A"
        by (simp add: parallelogram_equiv_plg) 
      have "Parallelogram A C C' A'"
        using plg_to_parallelogram \<open>B \<noteq> PO\<close> \<open>Parallelogram PO B C A\<close> \<open>Plg PO B C' A'\<close> 
          plg_pseudo_trans plg_sym by blast 
      have "A C Par C' A'"
        by (metis ParallelogramFlat_def \<open>B \<noteq> PO\<close> \<open>PO B ParStrict A' C'\<close> 
            \<open>Parallelogram A C C' A'\<close> \<open>Parallelogram PO B C A\<close> \<open>ParallelogramFlat PO B C A\<close> 
            par_strict_not_col_4 plg_not_comm_R1 plg_par_1) 
      hence "A A' Par C C'"
        by (metis ParallelogramFlat_def \<open>PO B ParStrict A' C'\<close> \<open>Parallelogram A C C' A'\<close> 
            \<open>ParallelogramFlat PO B C A\<close> par_neq1 par_strict_not_col_4 plg_par) 
      {
        assume "A A' Par E E'"
        hence ?thesis
          by (metis Par_perm Pj_def \<open>A A' Par C C'\<close> par_trans) 
      }
      moreover {
        assume "A = A'"
        hence ?thesis
          using \<open>A A' Par C C'\<close> par_neq1 by blast 
      }
      ultimately show ?thesis
        using \<open>Col PO E' A' \<and> (A A' Par E E' \<or> A = A')\<close> by blast 
    qed
    ultimately show ?thesis
      unfolding Sum_def using assms(3) by blast 
  qed
qed

lemma sum_iff_cong_a:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Ar2 PO E E' A B C"
    and "PO \<noteq> C \<or> B \<noteq> A"
    and "Cong PO A B C"
    and "Cong PO B A C"
  shows "Sum PO E E' A B C"
  using grid_ok assms(5) assms(2) assms(3) assms(4) cong_sum by blast 

lemma sum_iff_cong_b:
  assumes grid_ok: "\<not> Col PO E E'"
    and (*"Ar2 PO E E' A B C"
and*) "PO \<noteq> C \<or> B \<noteq> A"
    and "Sum PO E E' A B C"
  shows "Cong PO A B C \<and> Cong PO B A C"
  using grid_ok assms(3) assms(2) sum_A_O_eq sum_cong2 by blast 

lemma sum_iff_cong:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Ar2 PO E E' A B C"
    and "PO \<noteq> C \<or> B \<noteq> A"
  shows "(Cong PO A B C \<and> Cong PO B A C) \<longleftrightarrow> Sum PO E E' A B C"
  using grid_ok assms(3) assms(2) cong_sum sum_iff_cong_b by blast 

lemma opp_comm:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Opp PO E E' X Y"
  shows "Opp PO E E' Y X"
  using Opp_def assms sum_comm by presburger 

lemma opp_uniqueness:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Opp PO E E' A MA1"
    and "Opp PO E E' A MA2" 
  shows "MA1 = MA2"
  using grid_ok Opp_def assms(3) assms(2) sum_uniquenessA by presburger 

(** lemma 14.13 *)
(** Parallel projection on the second axis preserves sums. *)

lemma proj_preserves_sum:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Sum PO E E' A B C"
    and "Ar1 PO E' A' B' C'"
    and "E E' Pj A A'"
    and "E E' Pj B B'"
    and "E E' Pj C C'"
  shows "Sum PO E' E A' B' C'" 
proof -
  obtain A0 C0 where "E E' Pj A A0" and "Col PO E' A0" and "PO E Pj A0 C0" and 
    "PO E' Pj B C0" and "E' E Pj C0 C"
    using Sum_def assms(2) by blast
  have "Col PO E A"
    using Ar2_def Sum_def assms(2) by presburger 
  have "Col PO E B"
    using Ar2_def Sum_def assms(2) by presburger 
  have "\<not> PO E' Par E E'"
    using grid_not_par_3 grid_ok by auto 
  have "PO \<noteq> E"
    using grid_ok not_col_distincts by blast 
  have "PO \<noteq> E'"
    using grid_ok not_col_distincts by blast 
  show ?thesis 
  proof (cases)
    assume "A = PO"
    {
      assume "E E' Par PO A'"
      hence False
        by (metis Ar1_def \<open>\<not> PO E' Par E E'\<close> assms(3) l6_16_1 par_col2_par_bis par_symmetry) 
    }
    moreover {
      assume "PO = A'"
      have "B = C" 
      proof -
        have "\<not> Col PO E E'"
          by (simp add: grid_ok) 
        moreover have "Sum PO E E' PO B C"
          using \<open>A = PO\<close> assms(2) by blast 
        ultimately show ?thesis
          using sum_O_B_eq by blast 
      qed
      have "B' = C'"
        using Ar1_def \<open>B = C\<close> \<open>Col PO E B\<close> assms(3) assms(5) assms(6) grid_ok 
          pj_uniqueness by presburger 
      hence "Sum PO E' E PO B' B'"
        by (meson Ar1_def assms(3) grid_ok not_col_permutation_5 sum_O_B) 
      hence "Sum PO E' E PO B' C'"
        by (simp add: \<open>B' = C'\<close>) 
      hence ?thesis
        using \<open>PO = A'\<close> by auto 
    }
    ultimately show ?thesis
      using Pj_def \<open>A = PO\<close> assms(4) by blast
  next
    assume "A \<noteq> PO"
    show ?thesis
    proof (cases)
      assume "B' = PO"
      thus ?thesis
        by (smt (verit, ccfv_threshold) Ar1_def Ar2_def Par_cases Pj_def 
            Sum_def assms(2) assms(3) assms(4) assms(5) assms(6) not_col_distincts 
            not_col_permutation_5 pj_uniqueness sum_A_O sum_A_O_eq)
    next
      assume "B' \<noteq> PO"
      obtain D where "Parallelogram A PO B' D"
        using \<open>A \<noteq> PO\<close> plg_existence by blast 
      hence "A PO Par B' D"
        using \<open>A \<noteq> PO\<close> \<open>B' \<noteq> PO\<close> plg_par by auto 
      have "Ar2 PO E' E A' B' C'"
        using Ar1_def Ar2_def assms(3) grid_ok not_col_permutation_5 by presburger 
      moreover have "E' E Pj A' A"
        using assms(4) pj_comm by blast 
      moreover have "A D Par PO E'" 
      proof (rule par_col_par [of PO E' A D B'])
        show "PO \<noteq> E'"
          by (simp add: \<open>PO \<noteq> E'\<close>) 
        show "A D Par PO B'"
          using \<open>A \<noteq> PO\<close> \<open>B' \<noteq> PO\<close> \<open>Parallelogram A PO B' D\<close> plg_par by force 
        show "Col PO B' E'"
          using Ar2_def calculation(1) col_permutation_5 by presburger 
      qed
      hence "PO E' Par A D"
        using Par_cases by blast 
      hence "PO E' Pj A D"
        using Pj_def by auto 
      moreover have "PO E Pj B' D"
        by (metis Pj_def \<open>A PO Par B' D\<close> \<open>A \<noteq> PO\<close> \<open>Col PO E A\<close> \<open>PO \<noteq> E\<close> 
            not_par_not_col par_left_comm par_trans) 
      moreover have "E E' Pj D C'" 
      proof -
        have "ParallelogramFlat PO A C B"
          using \<open>A \<noteq> PO\<close> assms(2) grid_ok sum_cong by blast 
        have "Parallelogram B' D C B \<or> (B' = D \<and> A = PO \<and> B = C \<and> B' = B)"
          by (metis Parallelogram_def \<open>Parallelogram A PO B' D\<close> 
              \<open>ParallelogramFlat PO A C B\<close> plg_pseudo_trans plg_sym)
        moreover
        {
          assume "Parallelogram B' D C B"
          have "B' D Par C B"
            by (metis Par_cases Plg_perm \<open>A PO Par B' D\<close> \<open>Parallelogram B' D C B\<close> 
                par_neq2 par_reflexivity plg_par_1) 
          have "B' B Par D C"
            by (metis Ar1_def NCol_perm ParallelogramFlat_def Plg_perm \<open>A \<noteq> PO\<close> 
                \<open>B' D Par C B\<close> \<open>B' \<noteq> PO\<close> \<open>Col PO E A\<close> \<open>Parallelogram B' D C B\<close> 
                \<open>ParallelogramFlat PO A C B\<close> assms(3) col_transitivity_1 grid_ok par_neq1 plg_par_2) 
          {
            assume "E E' Par B B'"
            {
              assume "E E' Par C C'"
              hence ?thesis
                by (smt (verit, best) Par_perm Pj_def \<open>B' B Par D C\<close> \<open>E E' Par B B'\<close> 
                    col_par_par_col col_trivial_3 not_par_one_not_par par_col2_par) 
            }
            moreover {
              assume "C = C'"
              hence ?thesis
                by (metis Par_cases Pj_def \<open>B' B Par D C\<close> \<open>E E' Par B B'\<close> not_par_one_not_par) 
            }
            ultimately have ?thesis
              using Pj_def assms(6) by blast 
          }
          moreover {
            assume "B = B'"
            hence ?thesis
              using \<open>B' B Par D C\<close> par_neq1 by blast 
          }
          ultimately have ?thesis
            using Pj_def assms(5) by blast 
        }
        moreover {
          assume "B' = D \<and> A = PO \<and> B = C \<and> B' = B" 
          hence False
            using \<open>A \<noteq> PO\<close> by blast 
        }
        ultimately show ?thesis 
          by blast
      qed
      ultimately show ?thesis
        using Sum_def \<open>Col PO E A\<close> by blast 
    qed
  qed
qed

lemma sum_assoc_1:
  assumes "Sum PO E E' A B AB"
    and "Sum PO E E' B C BC"
    and "Sum PO E E' A BC ABC"
  shows "Sum PO E E' AB C ABC" 
proof -
  have "\<not> Col PO E E'"
    using Ar2_def Sum_def assms(2) by presburger 
  have "Col PO E AB"
    using Ar2_def Sum_def assms(1) by presburger 
  have "Col PO E C"
    using Ar2_def Sum_def assms(2) by presburger 
  have "Col PO E ABC"
    using Ar2_def Sum_def assms(3) by presburger 
  {
    assume "A = PO"
    hence ?thesis
      using \<open>\<not> Col PO E E'\<close> assms(1) assms(2) assms(3) sum_O_B_eq by blast 
  }
  moreover {
    assume "A \<noteq> PO"
    {
      assume "B = PO"
      hence ?thesis
        using \<open>\<not> Col PO E E'\<close> assms(1) assms(2) assms(3) sum_A_O_eq sum_O_B_eq by blast 
    }
    moreover {
      assume "B \<noteq> PO"
      {
        assume "C = PO"
        hence ?thesis
          using \<open>Col PO E AB\<close> \<open>\<not> Col PO E E'\<close> assms(1) assms(2) assms(3) sum_A_O 
            sum_A_O_eq sum_uniqueness by blast 
      }
      moreover {
        assume "C \<noteq> PO"
        have "PO \<noteq> E"
          using \<open>\<not> Col PO E E'\<close> col_trivial_1 by auto
        have "PO \<noteq> E'"
          using \<open>\<not> Col PO E E'\<close> not_col_distincts by blast 
        obtain AB2' where "AB AB2' Proj PO E' E E'"
          using Sump_def \<open>Col PO E AB\<close> \<open>\<not> Col PO E E'\<close> sum_A_O sum_to_sump by blast
        hence "Col PO E' AB2'"
          by (simp add: Proj_def) 
        have "AB AB2' Par E E' \<or> AB = AB2'"
          using Proj_def \<open>AB AB2' Proj PO E' E E'\<close> by presburger
        moreover have "A \<noteq> AB"
          using \<open>B \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(1) sum_B_null by force
        have "ABC \<noteq> AB"
          using \<open>C \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(1) assms(2) assms(3) sum_B_null 
            sum_uniquenessB by blast 
        obtain C2 where "Parallelogram C PO AB2' C2"
          using \<open>C \<noteq> PO\<close> plg_existence by presburger 
        {
          assume "AB AB2' Par E E'"
          hence "AB \<noteq> AB2'"
            using par_distinct by blast 
          have "PO \<noteq> AB2'"
            using \<open>AB AB2' Proj PO E' E E'\<close> \<open>AB \<noteq> AB2'\<close> \<open>Col PO E AB\<close> \<open>\<not> Col PO E E'\<close> 
              grid_not_par_5 proj_id by blast 
          have "C PO Par AB2' C2"
            by (simp add: \<open>C \<noteq> PO\<close> \<open>PO \<noteq> AB2'\<close> \<open>Parallelogram C PO AB2' C2\<close> plg_par) 
          have "C C2 Par PO AB2'"
            by (simp add: \<open>C \<noteq> PO\<close> \<open>PO \<noteq> AB2'\<close> \<open>Parallelogram C PO AB2' C2\<close> plg_par) 
          have "E E' Pj AB AB2'"
            using Par_perm Pj_def \<open>AB AB2' Par E E'\<close> by blast 
          moreover have "PO E Pj AB2' C2"
            by (metis Pj_def \<open>C PO Par AB2' C2\<close> \<open>C \<noteq> PO\<close> \<open>Col PO E C\<close> \<open>PO \<noteq> E\<close> 
                not_par_not_col par_left_comm par_trans) 
          moreover have "PO E' Pj C C2"
            by (meson Pj_def \<open>C C2 Par PO AB2'\<close> \<open>Col PO E' AB2'\<close> \<open>PO \<noteq> AB2'\<close> 
                \<open>PO \<noteq> E'\<close> not_par_not_col not_par_one_not_par) 
          moreover have "E' E Pj C2 ABC" 
          proof -
            have "Parallelogram PO BC ABC A"
              using Parallelogram_def \<open>A \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(3) 
                sum_comm sum_cong by blast
            have "Parallelogram PO B AB A"
              using Parallelogram_def \<open>B \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(1) 
                sum_comm sum_cong by blast 
            have "Parallelogram PO B BC C"
              using Parallelogram_def \<open>B \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(2) sum_cong by blast 
            have "Parallelogram B AB ABC BC \<or> (B = AB \<and> A = PO \<and> BC = ABC \<and> B = BC)"
              by (simp add: \<open>Parallelogram PO B AB A\<close> \<open>Parallelogram PO BC ABC A\<close> 
                  plg_permut plg_pseudo_trans)
            hence "Parallelogram B AB ABC BC"
              using \<open>A \<noteq> PO\<close> by auto 
            have "Parallelogram PO C ABC AB"
              by (metis Plg_perm \<open>ABC \<noteq> AB\<close> 
                  \<open>Parallelogram B AB ABC BC \<or> B = AB \<and> A = PO \<and> BC = ABC \<and> B = BC\<close> 
                  \<open>Parallelogram PO B BC C\<close> plg_pseudo_trans)
            hence "Parallelogram ABC AB AB2' C2"
              by (metis par_distinct \<open>C PO Par AB2' C2\<close> \<open>Parallelogram C PO AB2' C2\<close>
                  plg_pseudo_trans plg_sym)
            thus ?thesis
              by (metis Par_perm Pj_def \<open>AB AB2' Par E E'\<close> \<open>AB \<noteq> AB2'\<close> \<open>ABC \<noteq> AB\<close> 
                  par_not_par plg_par_2) 
          qed
          ultimately have ?thesis
            using Ar2_def Sum_def \<open>Col PO E' AB2'\<close> \<open>Col PO E ABC\<close> \<open>Col PO E AB\<close> 
              \<open>Col PO E C\<close> \<open>\<not> Col PO E E'\<close> by auto 
        }
        moreover {
          assume "AB = AB2'"
          have "AB = PO"
            using \<open>AB = AB2'\<close> \<open>AB AB2' Proj PO E' E E'\<close> \<open>Col PO E AB\<close> 
              \<open>\<not> Col PO E E'\<close> proj_id by blast 
          hence "C = C2"
            using \<open>AB = AB2'\<close> \<open>Parallelogram C PO AB2' C2\<close> cong_identity_inv plg_cong by blast 
          have "ParallelogramFlat PO B BC C"
            using \<open>B \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(2) sum_cong by blast 
          have "ParallelogramFlat PO BC ABC A"
            using \<open>A \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(3) sum_comm sum_cong by blast 
          have "ParallelogramFlat PO B PO A"
            using \<open>A \<noteq> PO\<close> \<open>AB = PO\<close> \<open>\<not> Col PO E E'\<close> assms(1) plgf_sym sum_cong by blast 
          have "Parallelogram BC C A PO \<or> (BC = C \<and> PO = B \<and> PO = A \<and> BC = PO)"
            by (metis Parallelogram_def \<open>ParallelogramFlat PO B BC C\<close> 
                \<open>ParallelogramFlat PO B PO A\<close> \<open>\<not> Col PO E E'\<close> assms(2) plgf_plgf_plgf 
                plgf_sym sum_A_B_B) 
          hence "Parallelogram BC C A PO"
            using \<open>B \<noteq> PO\<close> by auto
          have "Parallelogram PO BC ABC A"
            using Parallelogram_def \<open>ParallelogramFlat PO BC ABC A\<close> by auto 
          hence ?thesis
            by (metis Plg_perm \<open>AB = PO\<close> \<open>Col PO E C\<close> \<open>Parallelogram BC C A PO\<close> 
                \<open>\<not> Col PO E E'\<close> plg_uniqueness sum_O_B) 
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

lemma sum_assoc_2: 
  assumes "Sum PO E E' A B AB"
    and "Sum PO E E' B C BC"
    and "Sum PO E E' AB C ABC"
  shows "Sum PO E E' A BC ABC"
  by (smt (verit, best) Ar2_def Sum_def assms(1) assms(2) assms(3) sum_assoc_1 sum_comm) 

lemma sum_assoc:
  assumes "Sum PO E E' A B AB"
    and "Sum PO E E' B C BC"
  shows "Sum PO E E' A BC ABC \<equiv> Sum PO E E' AB C ABC"
  by (smt (verit, ccfv_SIG) assms(1) assms(2) sum_assoc_1 sum_assoc_2) 

(** lemma 14.15 *)
(** The choice of E' does not affect sum. *)
lemma sum_y_axis_change:
  assumes "Sum PO E E' A B C"
    and "\<not> Col PO E E''"
  shows "Sum PO E E'' A B C"
  by (smt (verit) Ar2_def ParallelogramFlat_def Sum_def assms(1) 
      assms(2) sum_A_O sum_cong sum_iff_cong) 

(** lemma 14.16 *)
(** The choice of E does not affect sum. *)
lemma sum_x_axis_unit_change:
  assumes "Sum PO E E' A B C"
    and "Col PO E U"
    and "U \<noteq> PO"
  shows "Sum PO U E' A B C"
proof (cases)
  assume "U = E"
  thus ?thesis
    using assms(1) by blast 
next
  assume "U \<noteq> E"
  have "Ar2 PO E E' A B C"
    using Sum_def assms(1) by blast
  have "\<not> Col PO E E'"
    using Ar2_def \<open>Ar2 PO E E' A B C\<close> by blast 
  have "Col PO E A"
    using Ar2_def \<open>Ar2 PO E E' A B C\<close> by blast 
  have "Col PO E B"
    using Ar2_def \<open>Ar2 PO E E' A B C\<close> by blast 
  have "Col PO E C"
    using Ar2_def \<open>Ar2 PO E E' A B C\<close> by blast 
  have "PO \<noteq> E" 
    using \<open>\<not> Col PO E E'\<close> grid_not_par by blast 
  have "PO \<noteq> E'"
    using \<open>\<not> Col PO E E'\<close> grid_not_par by blast 
  have "\<not> Col PO U E'"
    by (metis \<open>\<not> Col PO E E'\<close> assms(2) assms(3) col_trivial_3 colx) 
  {
    assume "A = PO"
    hence ?thesis
      by (metis \<open>Col PO E C\<close> \<open>PO \<noteq> E\<close> \<open>\<not> Col PO U E'\<close> assms(1) assms(2) 
          col_transitivity_1 sum_O_B sum_O_B_eq) 
  }
  moreover {
    assume "A \<noteq> PO"
    have ?thesis 
    proof (cases)
      assume "B = PO"
      thus ?thesis
        by (metis \<open>Col PO E C\<close> \<open>PO \<noteq> E\<close> \<open>\<not> Col PO U E'\<close> assms(1) assms(2) 
            col_transitivity_1 sum_A_O sum_A_O_eq) 
    next
      assume "B \<noteq> PO"
      have "Ar2 PO U E' A B C"
        using Ar2_def \<open>Col PO E A\<close> \<open>Col PO E B\<close> \<open>Col PO E C\<close> \<open>PO \<noteq> E\<close> 
          \<open>\<not> Col PO U E'\<close> assms(2) col_transitivity_1 by presburger 
      have "Col PO U A"
        using \<open>Col PO E A\<close> \<open>PO \<noteq> E\<close> assms(2) col_transitivity_1 by presburger 
      have "Col PO U B"
        using \<open>Col PO E B\<close> \<open>PO \<noteq> E\<close> assms(2) col_transitivity_1 by blast 
      obtain A'' where "A A'' Proj PO E' U E'"
        by (meson Sump_def \<open>Col PO U A\<close> \<open>\<not> Col PO U E'\<close> sum_A_O sum_to_sump) 
      hence "Col PO E' A''"
        using Proj_def by blast
      have "A A'' Par U E' \<or> A = A''"
        using Proj_def \<open>A A'' Proj PO E' U E'\<close> by presburger 
      hence "A A'' Par U E'"
        using \<open>A A'' Proj PO E' U E'\<close> \<open>A \<noteq> PO\<close> \<open>Col PO U A\<close> \<open>\<not> Col PO U E'\<close> proj_id by blast 
      obtain C'' where "Parallelogram B PO A'' C''"
        using \<open>B \<noteq> PO\<close> plg_existence by presburger 
      have "PO \<noteq> A''"
        using \<open>A A'' Proj PO E' U E'\<close> \<open>A \<noteq> PO\<close> \<open>Col PO U A\<close> \<open>\<not> Col PO U E'\<close> 
          not_col_distincts proj_id by blast
      have "B PO Par A'' C''"
        by (simp add: \<open>B \<noteq> PO\<close> \<open>PO \<noteq> A''\<close> \<open>Parallelogram B PO A'' C''\<close> plg_par) 
      have "B C'' Par PO A''"
        by (simp add: \<open>B \<noteq> PO\<close> \<open>PO \<noteq> A''\<close> \<open>Parallelogram B PO A'' C''\<close> plg_par) 
      have "U E' Pj A A''"
        using Par_perm Pj_def \<open>A A'' Par U E'\<close> by blast 
      moreover have "PO U Pj A'' C''"
        by (metis Pj_def \<open>B PO Par A'' C''\<close> \<open>B \<noteq> PO\<close> \<open>Col PO U B\<close> assms(3) 
            not_par_not_col par_left_comm par_trans) 
      moreover have "PO E' Pj B C''"
        by (meson Pj_def \<open>B C'' Par PO A''\<close> \<open>Col PO E' A''\<close> \<open>PO \<noteq> E'\<close> 
            not_col_distincts par_col2_par_bis par_symmetry) 
      moreover have "E' U Par C'' C" 
      proof -
        have "ParallelogramFlat PO A C B"
          using \<open>A \<noteq> PO\<close> \<open>\<not> Col PO E E'\<close> assms(1) sum_cong by blast 
        hence "Parallelogram PO A C B"
          by (simp add: Parallelogram_def)
        hence "Parallelogram A C C'' A''"
          using Plg_perm \<open>B \<noteq> PO\<close> \<open>Parallelogram B PO A'' C''\<close> plg_pseudo_trans by blast 
        hence "A C Par C'' A''"
          by (metis Tarski_neutral_dimensionless.par_distincts 
              Tarski_neutral_dimensionless_axioms \<open>A A'' Par U E'\<close> \<open>B PO Par A'' C''\<close> 
              par_symmetry plg_par_1 plg_sym) 
        hence "A A'' Par C C''"
          by (metis Plg_perm Tarski_neutral_dimensionless.par_distincts 
              Tarski_neutral_dimensionless_axioms \<open>A A'' Par U E'\<close> \<open>Parallelogram A C C'' A''\<close> plg_par) 
        thus ?thesis
          by (metis Par_perm \<open>A A'' Par U E'\<close> par_trans) 
      qed
      hence "E' U Pj C'' C"
        by (simp add: Pj_def) 
      ultimately show ?thesis
        using Sum_def \<open>Col PO E' A''\<close> \<open>Ar2 PO U E' A B C\<close> by blast 
    qed
  }
  ultimately show ?thesis 
    by blast
qed

lemma change_grid_sum_0:
  assumes "PO E ParStrict O' E'"
    and "Ar1 PO E A B C"
    and "Ar1 O' E' A' B' C'"
    and "PO O' Pj E E'"
    and "PO O' Pj A A'"
    and "PO O' Pj B B'"
    and "PO O' Pj C C'"
    and "Sum PO E E' A B C"
    and "A = PO"
  shows "Sum O' E' E A' B' C'" 
proof -
  {
    assume "Ar2 PO E E' A B C"
    obtain A1 C1 where "E E' Pj A A1" and
      "Col PO E' A1" and
      "PO E Pj A1 C1" and
      "PO E' Pj B C1" and
      "E' E Pj C1 C"
      using Sum_def assms(8) by blast 
    have "A' = O'"
    proof (rule l6_21 [of O' E' PO O'])
      show "\<not> Col O' E' PO"
        using assms(1) par_strict_not_col_3 by auto 
      show "PO \<noteq> O'"
        using \<open>\<not> Col O' E' PO\<close> col_trivial_3 by blast 
      show "Col O' E' A'" 
        using assms(3) Ar1_def by auto 
      show "Col O' E' O'"
        using grid_not_par_5 by auto 
      show "Col PO O' A'"
        using Pj_def not_col_distincts assms(5) assms(9) par_id by blast 
      show "Col PO O' O'"
        by (simp add: col_trivial_2) 
    qed
    have "Sum PO E E' PO B B"
      using Ar2_def \<open>Ar2 PO E E' A B C\<close> sum_O_B by presburger
    have "B = C"
      using assms(1) assms(8) assms(9) par_strict_not_col_4 sum_O_B_eq by blast 
    have "B' = C'" 
    proof (rule l6_21 [of O' E' B B'])
      show "\<not> Col O' E' B"
        by (metis Ar1_def assms(1) assms(2) par_strict_col_par_strict 
            par_strict_not_col_1 par_strict_not_col_4) 
      show "B \<noteq> B'"
        using Ar1_def \<open>\<not> Col O' E' B\<close> assms(3) by blast 
      show "Col O' E' B'"
        using Ar1_def assms(3) by presburger 
      show "Col O' E' C'"
        using Ar1_def assms(3) by presburger 
      show "Col B B' B'"
        by (simp add: col_trivial_2) 
      show "Col B B' C'"
        by (metis Col_def Par_perm Pj_def \<open>B = C\<close> \<open>B \<noteq> B'\<close> assms(6) assms(7) 
            grid_not_par_1 par_trans) 
    qed
    hence ?thesis
      by (metis Ar1_def NCol_cases \<open>A' = O'\<close> assms(1) assms(3) par_strict_not_col_2 sum_O_B) 
  }
  thus ?thesis
    using Sum_def assms(8) by blast 
qed

lemma change_grid_sum:
  assumes "PO E ParStrict O' E'"
    and "Ar1 PO E A B C"
    and "Ar1 O' E' A' B' C'" 
    and "PO O' Pj E E'"
    and "PO O' Pj A A'"
    and "PO O' Pj B B'"
    and "PO O' Pj C C'"
    and "Sum PO E E' A B C"
  shows "Sum O' E' E A' B' C'" 
proof (cases)
  assume "A = PO"
  thus ?thesis
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) 
      change_grid_sum_0 by blast 
next
  assume "A \<noteq> PO"
  {
    assume "Ar2 PO E E' A B C"
    obtain A1 C1 where "E E' Pj A A1" and "Col PO E' A1" and "PO E Pj A1 C1" and 
      "PO E' Pj B C1" and "E' E Pj C1 C"
      using Sum_def assms(8) by blast 
    have "\<not> PO E Par E E' \<and> \<not> PO E Par PO E' \<and> \<not> PO E' Par E E' \<and> PO \<noteq> E \<and> PO \<noteq> E' \<and> E \<noteq> E'"
      using assms(1) grid_not_par par_strict_not_col_4 by blast 
    have "\<not> Col O' E' E"
      using assms(1) col_permutation_2 par_strict_not_col_2 by blast 
    hence "\<not> O' E' Par E' E \<and> \<not> O' E' Par O' E \<and> \<not> O' E Par E' E \<and> O' \<noteq> E' \<and> O' \<noteq> E \<and> E' \<noteq> E"
      using grid_not_par by presburger 
    have ?thesis 
    proof (cases)
      assume "B = PO"
      thus ?thesis
        using Ar1_def Ar2_def \<open>Ar2 PO E E' A B C\<close> \<open>\<not> Col O' E' E\<close> assms(1) assms(2) assms(3) 
          assms(4) assms(5) assms(6) assms(7) assms(8) change_grid_sum_0 sum_comm by auto 
    next
      assume "B \<noteq> PO"
      have "A' \<noteq> PO"
        using Ar1_def assms(1) assms(3) par_strict_not_col_3 by force
      have "\<not> Col PO A A'"
        by (metis Ar1_def Col_cases \<open>A \<noteq> PO\<close> assms(1) assms(2) assms(3) l6_16_1 par_not_col) 
      have "A' \<noteq> O'"
        using Pj_def \<open>\<not> Col PO A A'\<close> assms(5) grid_not_par by blast
      have "ParallelogramFlat PO A C B"
        using \<open>A \<noteq> PO\<close> assms(1) assms(8) par_strict_not_col_4 sum_cong by blast 
      have "PO O' Proj O' E' E E'"
        by (metis Par_perm Pj_def 
            \<open>\<not> O' E' Par E' E \<and> \<not> O' E' Par O' E \<and> \<not> O' E Par E' E \<and> O' \<noteq> E' \<and> O' \<noteq> E \<and> E' \<noteq> E\<close> 
            assms(4) grid_not_par_4 pj_col_project)
      have "A A' Proj O' E' E E'"
        by (metis Ar1_def Pj_def Proj_def 
            \<open>\<not> O' E' Par E' E \<and> \<not> O' E' Par O' E \<and> \<not> O' E Par E' E \<and> O' \<noteq> E' \<and> O' \<noteq> E \<and> E' \<noteq> E\<close> 
            assms(3) assms(4) assms(5) par_right_comm par_symmetry par_trans) 
      have "C C' Proj O' E' E E'"
      proof -
        have "\<not> O' E' Par E E'"
          by (meson \<open>\<not> Col O' E' E\<close> grid_not_par not_strict_par1) 
        moreover have "C C' Par E E' \<or> C = C'"
          by (metis Pj_def 
              \<open>\<not> PO E Par E E' \<and> \<not> PO E Par PO E' \<and> \<not> PO E' Par E E' \<and> PO \<noteq> E \<and> PO \<noteq> E' \<and> E \<noteq> E'\<close> 
              assms(4) assms(7) par_symmetry par_trans) 
        ultimately show ?thesis
          using Ar1_def Proj_def 
            \<open>\<not> O' E' Par E' E \<and> \<not> O' E' Par O' E \<and> \<not> O' E Par E' E \<and> O' \<noteq> E' \<and> O' \<noteq> E \<and> E' \<noteq> E\<close> 
            assms(3) by auto 
      qed
      have "B B' Proj O' E' E E'" 
      proof -
        have "\<not> O' E' Par E E'"
          using \<open>\<not> Col O' E' E\<close> col_trivial_2 inter_uniqueness_not_par by blast 
        moreover have "B B' Par E E' \<or> B = B'"
          by (metis Par_def Pj_def 
              \<open>\<not> O' E' Par E' E \<and> \<not> O' E' Par O' E \<and> \<not> O' E Par E' E \<and> O' \<noteq> E' \<and> O' \<noteq> E \<and> E' \<noteq> E\<close> 
              assms(4) assms(6) not_par_inter_exists parallel_uniqueness)
        ultimately show ?thesis
          using Ar1_def Proj_def 
            \<open>\<not> O' E' Par E' E \<and> \<not> O' E' Par O' E \<and> \<not> O' E Par E' E \<and> O' \<noteq> E' \<and> O' \<noteq> E \<and> E' \<noteq> E\<close> 
            assms(3) by auto 
      qed
      have "PO A EqV B C"
        by (simp add: EqV_def Parallelogram_def \<open>ParallelogramFlat PO A C B\<close>)
      hence "O' A' EqV B' C'"
        using \<open>A A' Proj O' E' E E'\<close> \<open>B B' Proj O' E' E E'\<close> \<open>C C' Proj O' E' E E'\<close> 
          \<open>PO O' Proj O' E' E E'\<close> project_preserves_eqv by blast
      moreover {
        assume "Parallelogram O' A' C' B'"
        hence ?thesis
          by (metis Ar1_def Ar2_def Plg_perm \<open>\<not> Col O' E' E\<close> assms(3) plg_cong_2 
              plg_irreflexive sum_iff_cong) 
      }
      moreover {
        assume "O' = A'" and "B' = C'"
        hence ?thesis
          using \<open>A' \<noteq> O'\<close> by auto 
      }
      ultimately show ?thesis
        using EqV_def by blast 
    qed
  }
  thus ?thesis
    using Sum_def assms(8) by blast 

qed

lemma double_null_null: 
  assumes "Sum PO E E' A A PO"
  shows "A = PO" 
proof (rule ccontr)
  assume "A \<noteq> PO"
  hence "ParallelogramFlat PO A PO A"
    using Ar2_def Sum_def assms sum_cong by blast 
  thus False
    using plgf_irreflexive by blast 
qed

lemma not_null_double_not_null: 
  assumes "Sum PO E E' A A C"
    and "A \<noteq> PO"
  shows "C \<noteq> PO"
  using assms(1) assms(2) double_null_null by blast

lemma double_not_null_not_nul:
  assumes "Sum PO E E' A A C"
    and "C \<noteq> PO"
  shows "A \<noteq> PO"
  using Ar2_def Sum_def assms(1) assms(2) sum_O_B_eq by blast 

lemma diff_ar2:
  assumes "Diff PO E E' A B AMB"
  shows "Ar2 PO E E' A B AMB" 
proof -
  obtain MA where "Opp PO E E' B MA" and "Sum PO E E' A MA AMB"
    using Diff_def assms by blast
  thus ?thesis
    by (simp add: Ar2_def Opp_def Sum_def) 
qed

lemma diff_null:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E A"
  shows "Diff PO E E' A A PO"
  by (meson Diff_def Opp_def grid_ok assms(2) opp_exists sum_comm)

lemma diff_exists: 
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E A"
    and "Col PO E B"
  shows "\<exists> D. Diff PO E E' A B D" 
proof -
  obtain MB where "Opp PO E E' B MB"
    using grid_ok assms(3) opp_exists by blast
  then obtain C where "Sum PO E E' A MB C"
    by (meson Ar2_def Opp_def Sum_def assms(2) sum_exists)
  thus ?thesis
    using Diff_def \<open>Opp PO E E' B MB\<close> by blast 
qed

lemma diff_uniqueness:
  assumes "Diff PO E E' A B D1"
    and "Diff PO E E' A B D2"
  shows "D1 = D2"
  by (metis Ar2_def Diff_def assms(1) assms(2) diff_ar2 opp_uniqueness sum_uniqueness)

lemma sum_ar2:
  assumes "Sum PO E E' A B C"
  shows "Ar2 PO E E' A B C"
  using Sum_def assms by blast 

lemma diff_A_O:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E A"
  shows "Diff PO E E' A PO A"
  using Diff_def grid_ok assms(2) opp0 sum_A_O by blast 

lemma diff_O_A:
  assumes (*"\<not> Col PO E E'"
and*) "Opp PO E E' A mA"
  shows "Diff PO E E' PO A mA"
  by (meson Ar2_def Diff_def Opp_def assms sum_O_B sum_ar2) 

lemma diff_O_A_opp:
  assumes "Diff PO E E' PO A mA"
  shows "Opp PO E E' A mA"
  by (metis Ar2_def Diff_def assms diff_ar2 sum_O_B_eq) 

lemma diff_uniquenessA:
  assumes "Diff PO E E' A B C"
    and "Diff PO E E' A' B C"
  shows "A = A'"
  by (metis Ar2_def Diff_def assms(1) assms(2) diff_ar2 opp_uniqueness sum_uniquenessA)

lemma diff_uniquenessB:
  assumes "Diff PO E E' A B C"
    and "Diff PO E E' A B' C"
  shows "B = B'"
  by (metis Ar2_def Diff_def assms(1) assms(2) diff_ar2 opp_comm opp_uniqueness sum_uniquenessB) 

lemma diff_null_eq:
  assumes "Diff PO E E' A B PO"
  shows "A = B"
  by (meson Ar2_def assms diff_ar2 diff_null diff_uniquenessB) 

lemma midpoint_opp: 
  assumes "Ar2 PO E E' PO A B"
    and "PO Midpoint A B"
  shows "Opp PO E E' A B" 
proof (cases)
  assume "A = B"
  thus ?thesis
    using Ar2_def assms(1) assms(2) l8_20_2 opp0 by blast 
next
  assume "A \<noteq> B"
  moreover have "Ar2 PO E E' B A PO"
    using Ar2_def assms(1) by force 
  moreover have "Cong PO B A PO"
    using assms(2) cong_symmetry midpoint_cong by blast 
  moreover have "Cong PO A B PO"
    using calculation(3) cong_4321 by blast 
  ultimately show ?thesis
    by (simp add: Ar2_def Opp_def cong_sum) 
qed

lemma sum_diff:
  assumes "Sum PO E E' A B S"
  shows "Diff PO E E' S A B" 
proof -
  have "Ar2 PO E E' A B S"
    using assms sum_ar2 by auto 
  then obtain mA where "Opp PO E E' A mA"
    by (meson Ar2_def opp_exists) 
  moreover have "Sum PO E E' S mA B"
    by (meson Ar2_def Opp_def \<open>Ar2 PO E E' A B S\<close> assms calculation sum_O_B sum_assoc_2 sum_comm) 
  ultimately show ?thesis
    using Diff_def by auto 
qed

lemma diff_sum:
  assumes "Diff PO E E' S A B"
  shows "Sum PO E E' A B S"
  by (meson Ar2_def Diff_def Opp_def assms diff_ar2 sum_A_O sum_assoc_1 sum_comm) 

lemma diff_opp:
  assumes "Diff PO E E' A B AmB"
    and "Diff PO E E' B A BmA"
  shows "Opp PO E E' AmB BmA"
  by (meson Ar2_def Diff_def Opp_def assms(1) assms(2) diff_ar2 diff_sum sum_assoc sum_comm) 

lemma sum_stable:
  assumes "A = B" 
    and "Sum PO E E' A C S1"
    and "Sum PO E E' B C S2"
  shows "S1 = S2"
  using assms(1) assms(2) assms(3) diff_uniquenessA sum_diff by blast 

lemma diff_stable:
  assumes "A = B"
    and "Diff PO E E' A C D1"
    and "Diff PO E E' B C D2"
  shows "D1 = D2"
  using assms(1) assms(2) assms(3) diff_uniqueness by blast 

lemma plg_to_sum:
  assumes "Ar2 PO E E' A B C"
    and "ParallelogramFlat PO A C B"
  shows "Sum PO E E' A B C"
  by (metis Ar2_def assms(1) assms(2) not_cong_1243 plgf_cong plgf_irreflexive sum_iff_cong_a) 

lemma opp_midpoint:
  assumes "Opp PO E E' A MA"
  shows "PO Midpoint A MA" 
proof (cases)
  assume "A = PO"
  hence "MA = PO"
    by (metis Opp_def assms diff_null_eq local.sum_diff) 
  thus ?thesis
    by (simp add: \<open>A = PO\<close> l7_3_2) 
next
  assume "A \<noteq> PO"
  thus ?thesis
    by (meson Ar2_def Mid_cases Opp_def assms plgf3_mid sum_ar2 sum_cong) 
qed

lemma diff_to_plg:
  assumes "A \<noteq> PO \<or> B \<noteq> PO"
    and "Diff PO E E' B A dBA"
  shows "ParallelogramFlat PO A B dBA"
  by (metis Ar2_def assms(1) assms(2) diff_null_eq diff_sum sum_ar2 sum_cong) 

lemma sum3_col:
  assumes "sum3 PO E E' A B C S"
  shows "\<not> Col PO E E' \<and> Col PO E A \<and> Col PO E B \<and> Col PO E C \<and> Col PO E S"
  by (meson Ar2_def assms sum3_def sum_ar2) 

lemma sum3_permut:
  assumes "sum3 PO E E' A B C S"
  shows "sum3 PO E E' C A B S"
  by (smt (verit, ccfv_SIG) assms sum3_col sum3_def sum_assoc sum_comm sum_exists) 

lemma sum3_comm_1_2:
  assumes "sum3 PO E E' A B C S"
  shows "sum3 PO E E' B A C S"
  by (meson assms sum3_col sum3_def sum_comm) 

lemma sum3_comm_2_3:
  assumes "sum3 PO E E' A B C S"
  shows "sum3 PO E E' A C B S"
  using assms sum3_comm_1_2 sum3_permut by blast 

lemma sum3_exists:
  assumes "Ar2 PO E E' A B C"
  shows "\<exists> S. sum3 PO E E' A B C S"
  by (metis Ar2_def Sum_def assms sum3_def sum_exists) 

lemma sum3_uniqueness:
  assumes "sum3 PO E E' A B C S1"
    and "sum3 PO E E' A B C S2"
  shows "S1 = S2"
  by (metis assms(1) assms(2) sum3_def sum_stable) 

lemma sum4_col:
  assumes "Sum4 PO E E' A B C D S"
  shows "\<not> Col PO E E' \<and> Col PO E A \<and> Col PO E B \<and> Col PO E C \<and> Col PO E D \<and> Col PO E S"
  by (meson assms sum3_col sum3_def sum4_def) 

lemma sum22_col:
  assumes "sum22 PO E E' A B C D S"
  shows "\<not> Col PO E E' \<and> Col PO E A \<and> Col PO E B \<and> Col PO E C \<and> Col PO E D \<and> Col PO E S"
  by (meson Ar2_def assms sum22_def sum_ar2) 

lemma sum_to_sum3:
  assumes "Sum PO E E' A B AB"
    and "Sum PO E E' AB X S"
  shows "sum3 PO E E' A B X S"
  using assms(1) assms(2) sum3_def by blast 

lemma sum3_to_sum4:
  assumes "sum3 PO E E' A B C ABC"
    and "Sum PO E E' ABC X S"
  shows "Sum4 PO E E' A B C X S"
  using assms(1) assms(2) sum4_def by blast 

lemma sum_A_exists:
  assumes "Ar2 PO E E' A AB PO"
  shows "\<exists> B. Sum PO E E' A B AB"
  by (meson Ar2_def assms diff_exists diff_sum) 

lemma sum_B_exists:
  assumes "Ar2 PO E E' B AB PO"
  shows "\<exists> A. Sum PO E E' A B AB"
  using Ar2_def assms sum_A_exists sum_comm by blast 

lemma sum4_equiv_a:
  assumes "Sum4 PO E E' A B C D S"
  shows "sum22 PO E E' A B C D S" 
proof -
  obtain AB where "Sum PO E E' A B AB"
    using assms sum4_col sum_exists by blast 
  obtain CD where "Sum PO E E' C D CD"
    using assms sum4_col sum_exists by blast 
  have "Sum PO E E' AB CD S" 
  proof -
    have "Ar2 PO E E' A B AB"
      by (simp add: \<open>Sum PO E E' A B AB\<close> sum_ar2) 
    moreover have "Ar2 PO E E' C D CD"
      by (simp add: \<open>Sum PO E E' C D CD\<close> sum_ar2) 
    ultimately show ?thesis
      by (smt (verit, best) \<open>Sum PO E E' A B AB\<close> \<open>Sum PO E E' C D CD\<close> assms 
          sum4_col sum3_def sum4_def sum_assoc_2 sum_uniqueness) 
  qed
  thus ?thesis
    using \<open>Sum PO E E' A B AB\<close> \<open>Sum PO E E' C D CD\<close> sum22_def by blast 
qed

lemma sum4_equiv_b:
  assumes "sum22 PO E E' A B C D S"
  shows "Sum4 PO E E' A B C D S"
proof -
  obtain AB CD where "Sum PO E E' A B AB" and "Sum PO E E' C D CD" and "Sum PO E E' AB CD S"
    using assms sum22_def by blast 
  have "Ar2 PO E E' A B AB"
    using Sum_def \<open>Sum PO E E' A B AB\<close> by blast 
  have "Ar2 PO E E' C D CD"
    by (simp add: \<open>Sum PO E E' C D CD\<close> sum_ar2) 
  obtain ABC where "Sum PO E E' AB C ABC"
    using Ar2_def \<open>Ar2 PO E E' A B AB\<close> \<open>Ar2 PO E E' C D CD\<close> sum_exists by presburger
  thus ?thesis
    by (meson \<open>Sum PO E E' A B AB\<close> \<open>Sum PO E E' AB CD S\<close> \<open>Sum PO E E' C D CD\<close> 
        sum3_to_sum4 sum_assoc_1 sum_to_sum3) 
qed

lemma sum4_equiv:
  shows "Sum4 PO E E' A B C D S \<longleftrightarrow> sum22 PO E E' A B C D S"
  using sum4_equiv_a sum4_equiv_b by blast 

lemma sum4_permut: 
  assumes "Sum4 PO E E' A B C D S"
  shows "Sum4 PO E E' D A B C S" 
proof -
  have "sum22 PO E E' A B C D S"
    using assms sum4_equiv by auto 
  then obtain AB CD where "Sum PO E E' A B AB" and "Sum PO E E' C D CD" and 
    "Sum PO E E' AB CD S"
    using sum22_def by blast 
  obtain ABC where "sum3 PO E E' A B C ABC" and "Sum PO E E' ABC D S"
    using assms sum4_def by blast 
  then obtain AC where "Sum PO E E' C A AC" and "Sum PO E E' AC B ABC"
    using sum3_def sum3_permut by blast 
  obtain AD where "Sum PO E E' D A AD"
    using assms sum4_col sum_exists by blast
  then obtain ABD where "Sum PO E E' AD B ABD"
    using Ar2_def \<open>Sum PO E E' AC B ABC\<close> sum_ar2 sum_exists by presburger 
  thus ?thesis
    by (smt (verit, ccfv_threshold) \<open>Sum PO E E' ABC D S\<close> \<open>Sum PO E E' D A AD\<close> 
        \<open>sum3 PO E E' A B C ABC\<close> sum3_col sum3_def sum4_def sum_assoc_2 sum_comm) 
qed

(* a + b + c + d = d + a + b + c *)
lemma sum22_permut: 
  assumes "sum22 PO E E' A B C D S"
  shows "sum22 PO E E' D A B C S"
  using assms sum4_equiv sum4_permut by presburger 

lemma sum4_comm:
  assumes "Sum4 PO E E' A B C D S"
  shows "Sum4 PO E E' B A C D S"
  by (meson assms sum3_comm_1_2 sum4_def) 

(* a + b + c + d = b + a + c + d *)
lemma sum22_comm: 
  assumes "sum22 PO E E' A B C D S"
  shows "sum22 PO E E' B A C D S"
  by (meson assms sum4_comm sum4_equiv_a sum4_equiv_b) 

(* a + b + c + d = b  c + a + d *)
lemma sum_abcd:
  assumes "Sum PO E E' A B AB"
    and "Sum PO E E' C D CD"
    and "Sum PO E E' B C BC"
    and "Sum PO E E' A D AD"
    and "Sum PO E E' AB CD S"
  shows "Sum PO E E' BC AD S" 
proof -
  have "sum22 PO E E' A B C D S"
    using assms(1) assms(2) assms(5) sum22_def by blast 
  then obtain AD' BC' where "Sum PO E E' D A AD'" and "Sum PO E E' B C BC'" and 
    "Sum PO E E' AD' BC' S"
    using sum22_def sum22_permut by blast 
  thus ?thesis
    by (metis \<open>sum22 PO E E' A B C D S\<close> assms(3) assms(4) sum22_col sum_comm sum_stable) 
qed

(* (b - a) + (c - b) = (c - a) *)
lemma sum_diff_diff_a:
  assumes "Diff PO E E' B A dBA"
    and "Diff PO E E' C B dCB"
    and "Diff PO E E' C A dCA"
  shows "Sum PO E E' dCB dBA dCA"
  by (smt (verit) Ar2_def Diff_def assms(1) assms(2) assms(3) diff_ar2 diff_sum 
      opp_uniqueness sum_assoc sum_comm) 

lemma sum_diff_diff_b:
  assumes "Diff PO E E' B A dBA"
    and "Diff PO E E' C B dCB"
    and "Sum PO E E' dCB dBA dCA"
  shows "Diff PO E E' C A dCA"
  by (meson Ar2_def assms(1) assms(2) assms(3) diff_sum sum_diff sum_ar2 sum_assoc_2 sum_comm) 

(* (x + y) - (a + b) = (x - a) + (y - b) *)
lemma sum_diff2_diff_sum2_a:
  assumes "Sum PO E E' A B C"
    and "Sum PO E E' X Y Z"
    and "Diff PO E E' X A dXA"
    and "Diff PO E E' Y B dYB"
    and "Sum PO E E' dXA dYB dZC"
  shows "Diff PO E E' Z C dZC" 
proof -
  obtain Z' where "Sum PO E E' C dZC Z'"
    using Ar2_def Sum_def assms(1) assms(5) sum_exists by presburger 
  then obtain Y' X' where "Sum PO E E' B dYB Y'" and "Sum PO E E' A dXA X'" and 
    "Sum PO E E' Y' X' Z'"
    by (smt (verit, ccfv_threshold) Ar2_def assms(1) assms(3) assms(4) assms(5) diff_sum 
        sum_abcd sum_ar2 sum_comm)
  thus ?thesis
    by (metis \<open>Sum PO E E' C dZC Z'\<close> assms(2) assms(3) assms(4) diff_sum sum_diff sum3_col 
        sum_comm sum_stable sum_to_sum3) 
qed

lemma sum_diff2_diff_sum2_b:
  assumes "Sum PO E E' A B C"
    and "Sum PO E E' X Y Z"
    and "Diff PO E E' X A dXA"
    and "Diff PO E E' Y B dYB"
    and "Diff PO E E' Z C dZC"
  shows "Sum PO E E' dXA dYB dZC" 
proof -
  obtain dZC' where "Sum PO E E' dXA dYB dZC'"
    by (meson Ar2_def diff_sum Tarski_Euclidean_2D_axioms assms(3) assms(4) sum_ar2 sum_exists) 
  thus ?thesis
    by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) assms(4) assms(5) diff_stable 
        sum_diff2_diff_sum2_a) 
qed

lemma sum_opp:
  assumes "Sum PO E E' X MX PO"
  shows "Opp PO E E' X MX"
  by (simp add: Opp_def assms diff_O_A diff_sum) 

lemma sum_diff_diff:
  assumes "Diff PO E E' AX BX AXMBX"
    and "Diff PO E E' AX CX AXMCX"
    and "Diff PO E E' BX CX BXMCX"
  shows "Sum PO E E' AXMBX BXMCX AXMCX"
  using assms(1) assms(2) assms(3) sum_diff_diff_a by blast 

lemma prod_to_prodp:
  assumes "Prod PO E E' A B C"
  shows "Prodp PO E E' A B C" 
proof -
  obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' C"
    using Prod_def assms by blast 
  hence "B B' Proj PO E' E E'"
    by (metis Ar2_def Prod_def assms grid_not_par not_col_permutation_1 pj_col_project) 
  moreover have "B' C Proj PO E A E'" 
  proof (cases)
    assume "A = PO"
    thus ?thesis
      by (metis Ar2_def Prod_def \<open>E' A Pj B' C\<close> assms grid_not_par 
          not_col_permutation_1 pj_col_project pj_left_comm) 
  next
    assume " A \<noteq> PO"
    thus ?thesis
      by (metis Ar2_def Col_cases Par_cases Par_def Pj_def Prod_def \<open>E' A Pj B' C\<close>
          assms col_trivial_1 par_col_project par_strict_not_col_2 project_trivial) 
  qed
  ultimately show ?thesis
    using Ar2_def Prod_def Prodp_def assms by auto 
qed

lemma project_pj:
  assumes "P P' Proj A B X Y"
  shows "X Y Pj P P'"
  using Par_cases Pj_def Proj_def assms by auto 

lemma prodp_to_prod:
  assumes "Prodp PO E E' A B C"
  shows "Prod PO E E' A B C" 
proof -
  obtain B' where "B B' Proj PO E' E E'" and "B' C Proj PO E A E'"
    using Prodp_def assms by blast
  have "E E' Pj B B'"
    using \<open>B B' Proj PO E' E E'\<close> project_pj by auto 
  moreover have "Col PO E' B'"
    using Proj_def \<open>B B' Proj PO E' E E'\<close> by presburger 
  moreover have "E' A Pj B' C"
    using \<open>B' C Proj PO E A E'\<close> pj_left_comm project_pj by blast 
  ultimately show ?thesis
    by (metis Ar2_def Par_def Prod_def Prodp_def Proj_def assms grid_not_par_5) 
qed

lemma prod_exists:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Col PO E A" 
    and "Col PO E B"
  shows "\<exists> C. Prod PO E E' A B C"
  by (metis Prodp_def Par_def assms(2) assms(3) grid_not_par grid_ok not_col_permutation_2 
      par_strict_not_col_3 prodp_to_prod project_existence) 

lemma prod_uniqueness:
  assumes grid_ok: "\<not> Col PO E E'"
    and "Prod PO E E' A B C1" 
    and "Prod PO E E' A B C2"
  shows "C1 = C2" 
proof -
  obtain B' where "B B' Proj PO E' E E'" and "B' C1 Proj PO E A E'"
    using Prodp_def assms(2) prod_to_prodp by blast
  obtain B'' where "B B'' Proj PO E' E E'" and "B'' C2 Proj PO E A E'"
    using Prodp_def assms(3) prod_to_prodp by blast 
  thus ?thesis
    by (metis \<open>B B' Proj PO E' E E'\<close> \<open>B' C1 Proj PO E A E'\<close> project_uniqueness) 
qed

(** Lemma 14.17 *)
lemma prod_0_l:
  assumes "\<not> Col PO E E'"
    and "Col PO E A"
  shows "Prod PO E E' PO A PO" 
proof (cases)
  assume "A = PO"
  thus ?thesis
    by (metis Ar2_def Pj_def Prod_def assms(1) grid_not_par_5) 
next
  assume "A \<noteq> PO"
  obtain B' where "A B' Proj PO E' E E'"
    by (metis Par_cases assms(1) grid_not_par project_existence) 
  hence "E E' Pj A B'"
    using project_pj by auto 
  moreover have "Col PO E' B'"
    using Proj_def \<open>A B' Proj PO E' E E'\<close> by presburger 
  moreover have "E' PO Pj B' PO"
    by (metis Par_cases Pj_def not_col_distincts assms(1) calculation(2) not_par_not_col) 
  ultimately show ?thesis
    using Ar2_def Prod_def assms(1) assms(2) col_trivial_3 by auto 
qed

lemma prod_0_r:
  assumes "\<not> Col PO E E'"
    and "Col PO E A"
  shows "Prod PO E E' A PO PO"
  using Ar2_def Pj_def Prod_def assms(1,2) col_trivial_3 by auto 

(** Lemma 14.18 *)
lemma prod_1_l:
  assumes "\<not> Col PO E E'"
    and "Col PO E A"
  shows "Prod PO E E' E A A" 
proof -
  obtain B' where "A B' Proj PO E' E E'"
    by (metis assms(1) grid_not_par par_symmetry project_existence)
  moreover
  {
    assume "A B' Par E E'"
    hence "Prod PO E E' E A A"
      by (metis Par_cases Prodp_def assms(1,2) calculation not_col_distincts par_col_project
          par_id_5 prodp_to_prod)
  }
  moreover
  {
    assume "A = B'"
    hence "Prod PO E E' E A A"
      by (metis assms(1,2) calculation(1) not_col_distincts prod_0_r proj_id) 
  }
  ultimately show ?thesis
    using project_par_dir by blast 
qed

lemma prod_1_r:
  assumes "\<not> Col PO E E'"
    and "Col PO E A"
  shows "Prod PO E E' A E A"
  by (metis Ar2_def Pj_def Prod_def assms(1,2) grid_not_par not_par_not_col) 

(** Lemma 14.19 *)
lemma inv_exists:
  assumes "\<not> Col PO E E'"
    and "Col PO E A"
    and "A \<noteq> PO"
  shows "\<exists> IA. Prod PO E E' IA A E" 
proof -
  obtain B' where "A B' Proj PO E' E E'"
    by (meson Prodp_def assms(1,2) prod_0_l prod_to_prodp) 
  have "B' \<noteq> PO"
    using \<open>A B' Proj PO E' E E'\<close> assms(1,2,3) grid_not_par_5 proj_id by blast
  obtain IA where "E' IA Proj PO E B' E"
    by (metis NCol_cases \<open>A B' Proj PO E' E E'\<close> assms(1,2,3) grid_not_par proj_id
        project_existence) 
  moreover have "E E' Pj A B'"
    using \<open>A B' Proj PO E' E E'\<close> project_pj by auto 
  moreover have "Col PO E' B'"
    using Proj_def \<open>A B' Proj PO E' E E'\<close> by auto 
  moreover have "E' IA Pj B' E"
    using Pj_def Proj_def assms(1) calculation(1) by auto 
  ultimately show ?thesis
    using Ar2_def Prod_def Proj_def assms(1,2) col_trivial_2 by auto 
qed

(** Lemma 14.20 *)
(** The choice of E' does not affect product *)
lemma prod_null:
  assumes "Prod PO E E' A B PO"
  shows "A = PO \<or> B = PO" 
proof -
  obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' PO"
    using Prod_def assms by blast
  show ?thesis
  proof (cases)
    assume "B = PO"
    thus ?thesis
      by simp 
  next
    assume "B \<noteq> PO"
    {
      assume "E E' Par B B'"
      {
        assume "E' A Par B' PO"
        hence "A = PO"
          by (metis Ar2_def Col_cases Par_def Prod_def \<open>Col PO E' B'\<close> assms col_trivial_3
              not_strict_par2) 
      }
      moreover
      {
        assume "B' = PO"
        hence "A = PO"
          by (metis Ar2_def Prod_def \<open>E E' Par B B'\<close> assms col_permutation_2 grid_not_par
              par_col2_par_bis) 
      }
      ultimately have "A = PO"
        using Pj_def \<open>E' A Pj B' PO\<close> by blast 
    }
    moreover {
      assume "B = B'"
      hence "A = PO"
        by (metis Ar2_def NCol_cases Prod_def \<open>B \<noteq> PO\<close> \<open>Col PO E' B'\<close> assms
            colx) 
    }
    ultimately have "A = PO"
      using Pj_def \<open>E E' Pj B B'\<close> by blast 
    thus ?thesis
      by simp 
  qed
qed

lemma prod_y_axis_change:
  assumes "Prod PO E E' A B C"
    and "\<not> Col PO E E''"
  shows "Prod PO E E'' A B C" 
proof (cases "B = PO")
  show "B = PO \<Longrightarrow> Prod PO E E'' A B C"
    by (metis Ar2_def Prod_def assms(1,2) prod_0_r
        prod_uniqueness) 
  {
    assume "B \<noteq> PO"
    obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' C"
      using Prod_def assms(1) by blast 
    show "Prod PO E E'' A B C" 
    proof (cases "A = PO")
      show "A = PO \<Longrightarrow> Prod PO E E'' A B C"
        by (metis Ar2_def Prod_def assms(1,2) prod_0_l
            prod_uniqueness) 
      {
        assume "A \<noteq> PO"
        have "C \<noteq> PO"
          using \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> assms(1) prod_null by blast 
        obtain B'' where "B B'' Proj PO E'' E E''"
          by (metis Par_cases assms(2) col_trivial_2 col_trivial_3
              grid_not_par_3 project_existence) 
        hence "B B'' Par E E''"
          by (metis Prodp_def \<open>B \<noteq> PO\<close> assms(1,2) prod_to_prodp proj_id
              project_par_dir)
        have "E E'' Pj B B''"
          using \<open>B B'' Proj PO E'' E E''\<close> project_pj by auto 
        moreover have "Col PO E'' B''"
          using Proj_def \<open>B B'' Proj PO E'' E E''\<close> by force 
        moreover have "E'' A Pj B'' C" 
        proof (cases "B = E")
          show "B = E \<Longrightarrow> E'' A Pj B'' C"
            by (metis Ar2_def Col_cases Par_def Pj_def Prod_def
                \<open>B B'' Par E E''\<close> assms(1,2) calculation(2) col2__eq
                par_id_3 prod_1_r prod_uniqueness) 
          {
            assume "B \<noteq> E"
            have "E' A Par B' C"
              by (metis Ar2_def NCol_cases Pj_def Prod_def \<open>C \<noteq> PO\<close>
                  \<open>Col PO E' B'\<close> \<open>E' A Pj B' C\<close> assms(1) col_trivial_3
                  colx) 
            have "B B'' ParStrict E E''"
              by (meson Par_def Prodp_def \<open>B B'' Par E E''\<close> \<open>B \<noteq> E\<close>
                  assms(1,2) col_trivial_2 colx prod_to_prodp)
            have "E E' Par B B'"
              by (metis Ar2_def NCol_cases Pj_def Prod_def \<open>B \<noteq> PO\<close>
                  \<open>Col PO E' B'\<close> \<open>E E' Pj B B'\<close> assms(1) col_trivial_3
                  colx)
            hence "E E' ParStrict B B'"
              by (metis Ar2_def NCol_cases Par_def Prod_def \<open>B \<noteq> E\<close>
                  assms(1) col_trivial_3 colx)
            have "E' A ParStrict B' C"
              by (metis (no_types, lifting) Ar2_def Par_def Prod_def
                  \<open>C \<noteq> PO\<close> \<open>Col PO E' B'\<close> \<open>E E' ParStrict B B'\<close>
                  \<open>E' A Par B' C\<close> assms(1) grid_not_par l6_21
                  par_strict_not_col_1) 
            show "E'' A Pj B'' C" 
            proof (cases "A = E")
              show "A = E \<Longrightarrow> E'' A Pj B'' C"
                by (metis Ar2_def Prod_def assms(1) calculation(1) pj_comm
                    prod_uniqueness) 
              {
                assume "A \<noteq> E"
                have "B' \<noteq> PO"
                  by (metis NCol_cases Prodp_def \<open>E E' ParStrict B B'\<close> assms(1)
                      par_strict_not_col_3 prod_to_prodp) 
                show "E'' A Pj B'' C" 
                proof (cases "E' = E''")
                  show "E' = E'' \<Longrightarrow> E'' A Pj B'' C"
                    by (metis Prodp_def \<open>Col PO E' B'\<close> \<open>E E' Pj B B'\<close>
                        \<open>E' A Pj B' C\<close> assms(1,2) calculation(1,2) pj_uniqueness
                        prod_to_prodp) 
                  {
                    assume "E' \<noteq> E''"
                    show "E'' A Pj B'' C" 
                    proof (cases "Col E E' E''")
                      {
                        assume "Col E E' E''" 
                        hence "\<not> Col E' E'' A"
                          by (metis Prodp_def \<open>A \<noteq> E\<close> \<open>E' \<noteq> E''\<close>
                              assms(1,2) col2__eq col_permutation_1
                              prod_to_prodp) 
                        have "B' \<noteq> B''"
                          by (metis \<open>B' \<noteq> PO\<close> \<open>Col E E' E''\<close> \<open>Col PO E' B'\<close> \<open>E' \<noteq> E''\<close>
                              assms(2) calculation(2) col2__eq col_permutation_5
                              colx)
                        have "E' E'' Par B' B''"
                          by (smt (verit, ccfv_threshold) Par_perm \<open>B B'' Par E E''\<close>
                              \<open>B' \<noteq> B''\<close> \<open>Col E E' E''\<close> \<open>E E' Par B B'\<close> \<open>E' \<noteq> E''\<close>
                              col_par_par_col col_trivial_2 not_col_permutation_2
                              par_col4__par)
                        have "B' \<noteq> E'"
                          using \<open>E' A ParStrict B' C\<close> not_par_strict_id by auto 
                        have "E' E'' ParStrict B' B''"
                          by (metis NCol_cases Par_def \<open>Col E E' E''\<close>
                              \<open>E E' ParStrict B B'\<close> \<open>E' E'' Par B' B''\<close> l6_16_1
                              par_strict_not_col_4) 
                        have "Coplanar PO E'' E' A"
                          by (simp add: all_coplanar) 
                        moreover have "Col PO A C"
                          by (metis Ar2_def Col_cases Prod_def assms(1) col3
                              col_trivial_3)
                        ultimately have "E'' A Par B'' C" 
                          using l13_15 [of E' _ _ PO B'] \<open>\<not> Col E' E'' A\<close> 
                            \<open>E' E'' ParStrict B' B''\<close> \<open>E' A ParStrict B' C\<close> 
                            \<open>Col PO E' B'\<close> \<open>Col PO E'' B''\<close> by blast
                        thus "E'' A Pj B'' C"
                          by (simp add: Pj_def) 
                      }
                      {
                        assume "\<not> Col E E' E''"
                        have "E'' E' Par B'' B'" 
                          using l13_15 [of E E'' _ PO B]
                          by (meson Par_strict_cases Prodp_def \<open>B B'' ParStrict E E''\<close>
                              \<open>Col PO E' B'\<close> \<open>E E' ParStrict B B'\<close> \<open>\<not> Col E E' E''\<close>
                              all_coplanar assms(1) calculation(2) col_permutation_5
                              prod_to_prodp) 
                        show "E'' A Pj B'' C" 
                        proof (cases "Col A E' E''")
                          {
                            assume"Col A E' E''"
                            hence "B' C Par E' E''"
                              by (metis Par_cases \<open>E' A Par B' C\<close> \<open>E' \<noteq> E''\<close>
                                  col_par par_distinct par_not_par)
                            have "B' C Par B' B''"
                            proof (rule par_trans [of B' C E' E'' B' B''])
                              show "B' C Par E' E''"
                                by (simp add: \<open>B' C Par E' E''\<close>) 
                              show "E' E'' Par B' B''"
                                by (simp add: \<open>E'' E' Par B'' B'\<close> par_comm) 
                            qed
                            show "E'' A Pj B'' C"
                              by (smt (verit, best) Ar2_def Pj_def Prod_def
                                  \<open>B' C Par B' B''\<close> \<open>Col A E' E''\<close> \<open>E' A Par B' C\<close> assms(1,2)
                                  col_par_par_col col_permutation_4 l6_16_1 par_col4__par
                                  par_comm par_right_comm par_trans) 
                          }
                          {
                            assume "\<not> Col A E' E''"
                            have "B' \<noteq> E'"
                              using \<open>E' A ParStrict B' C\<close> not_par_strict_id by blast 
                            have "B'' \<noteq> E''"
                              using \<open>B B'' ParStrict E E''\<close> col_trivial_2 
                                par_strict_not_col_4 by blast 
                            {
                              assume "E'' E' ParStrict B'' B'"
                              have "E'' A Par B'' C" 
                                using l13_15 [of E' E'' A PO B' B'' C]
                                by (metis Ar2_def NCol_cases Par_strict_cases Prod_def
                                    \<open>Col PO E' B'\<close> \<open>E' A ParStrict B' C\<close>
                                    \<open>E'' E' ParStrict B'' B'\<close> \<open>\<not> Col A E' E''\<close>
                                    all_coplanar assms(1) calculation(2)
                                    col_transitivity_1 col_trivial_3) 
                              hence "E'' A Pj B'' C"
                                by (simp add: Pj_def) 
                            }
                            moreover
                            {
                              assume "E'' \<noteq> E'" and "B'' \<noteq> B'" and "Col E'' B'' B'" and 
                                "Col E' B'' B'"
                              have "E'' A Pj B'' C" 
                              proof (cases "Col PO E' E''")
                                {
                                  assume "Col PO E' E''"
                                  have "A E'' Par C B''"
                                  proof (rule l13_19 [of PO E E' B])
                                    show "\<not> Col PO E E'"
                                      using Ar2_def Prod_def assms(1) by presburger 
                                    show "PO \<noteq> E"
                                      using \<open>Col PO E' E''\<close> \<open>\<not> Col E E' E''\<close> by auto 
                                    show "PO \<noteq> B"
                                      using \<open>B \<noteq> PO\<close> by auto 
                                    show "PO \<noteq> A"
                                      using \<open>A \<noteq> PO\<close> by auto 
                                    show "PO \<noteq> C"
                                      using \<open>C \<noteq> PO\<close> by auto
                                    show "PO \<noteq> E'"
                                      using \<open>\<not> Col PO E E'\<close> grid_not_par_5 by blast
                                    show "PO \<noteq> B'"
                                      using \<open>B' \<noteq> PO\<close> by auto 
                                    show "PO \<noteq> E''"
                                      using assms(2) grid_not_par_5 by auto 
                                    show "PO \<noteq> B''"
                                      by (metis Prodp_def \<open>B B'' Proj PO E'' E E''\<close> 
                                          \<open>B \<noteq> PO\<close> assms(1,2)
                                          col_trivial_3 prod_to_prodp proj_id) 
                                    show "Col PO E A"
                                      using Prodp_def assms(1) prod_to_prodp by blast 
                                    show "Col PO E B"
                                      using Prodp_def assms(1) prod_to_prodp by blast 
                                    show "Col PO E C"
                                      using Ar2_def Prod_def assms(1) by presburger 
                                    show "Col PO E' E''"
                                      by (simp add: \<open>Col PO E' E''\<close>) 
                                    show "Col PO E' B'"
                                      by (simp add: \<open>Col PO E' B'\<close>) 
                                    show "Col PO E' B''"
                                      by (metis \<open>Col PO E' E''\<close> \<open>Col PO E'' B''\<close> assms(2) 
                                          col_trivial_3
                                          colx) 
                                    show "E E' Par B B'"
                                      by (simp add: \<open>E E' Par B B'\<close>) 
                                    show "E E'' Par B B''"
                                      by (simp add: \<open>B B'' Par E E''\<close> par_symmetry) 
                                    show "E' A Par B' C"
                                      by (simp add: \<open>E' A Par B' C\<close>) 
                                  qed
                                  hence "E'' A Par B'' C"
                                    using par_comm by blast 
                                  thus "E'' A Pj B'' C"
                                    by (simp add: Pj_def)

                                }
                                show "\<not> Col PO E' E'' \<Longrightarrow> E'' A Pj B'' C"
                                  by (metis \<open>B'' \<noteq> B'\<close> \<open>B'' \<noteq> E''\<close> \<open>Col E' B'' B'\<close> 
                                      \<open>Col E'' B'' B'\<close> \<open>Col PO E'' B''\<close> 
                                      col2__eq col_permutation_2) 
                              qed
                            }
                            ultimately show "E'' A Pj B'' C"
                              using Par_def \<open>E'' E' Par B'' B'\<close> by presburger 
                          }
                        qed
                      }
                    qed
                  }
                qed
              }
            qed
          }
        qed
        show "Prod PO E E'' A B C"
          using Ar2_def Prod_def \<open>E'' A Pj B'' C\<close> assms(1,2)
            calculation(1,2) by auto 
      }
    qed
  }
qed

(** Lemma 14.22 *)
(** Parallel projection on the second axis preserves products. *)
lemma proj_preserves_prod:
  assumes "Prod PO E E' A B C"
    and "Ar1 PO E' A' B' C'"
    and "E E' Pj A A'"
    and "E E' Pj B B'"
    and "E E' Pj C C'"
  shows "Prod PO E' E A' B' C'" 
proof (cases "A = PO")
  have "Ar2 PO E E' A B C"
    using Prod_def assms(1) by blast 
  show "A = PO \<Longrightarrow> Prod PO E' E A' B' C'"
    by (metis Ar1_def Ar2_def Col_cases Prod_def assms(1,2,3,5) pj_comm
        prod_0_l prod_uniqueness sum_par_strict_a) 
  {
    assume "A \<noteq> PO"
    show "Prod PO E' E A' B' C'" 
    proof (cases "B = PO")
      show "B = PO \<Longrightarrow> Prod PO E' E A' B' C'"
        by (metis Ar1_def Ar2_def Col_cases \<open>Ar2 PO E E' A B C\<close> assms(1,2,4,5)
            col_trivial_3 pj_trivial pj_uniqueness prod_0_r
            prod_uniqueness) 
      {
        assume "B \<noteq> PO"
        show "Prod PO E' E A' B' C'" 
        proof(cases "C = PO")
          show "C = PO \<Longrightarrow> Prod PO E' E A' B' C'"
            using \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> assms(1) prod_null by blast
          {
            assume "C \<noteq> PO"
            show "Prod PO E' E A' B' C'" 
            proof (cases "A' = PO")
              show "A' = PO \<Longrightarrow> Prod PO E' E A' B' C'"
                using Ar2_def \<open>A \<noteq> PO\<close> \<open>Ar2 PO E E' A B C\<close> assms(3) sum_par_strict_a
                by blast 
              {
                assume "A' \<noteq> PO"
                show "Prod PO E' E A' B' C'" 
                proof (cases "B' = PO")
                  show "B' = PO \<Longrightarrow> Prod PO E' E A' B' C'"
                    by (metis Ar2_def NCol_cases \<open>Ar2 PO E E' A B C\<close> \<open>B \<noteq> PO\<close> assms(4)
                        col_trivial_3 pj_comm pj_trivial pj_uniqueness) 
                  {
                    assume "B' \<noteq> PO"
                    show "Prod PO E' E A' B' C'"
                    proof (cases "C' = PO")
                      show "C' = PO \<Longrightarrow> Prod PO E' E A' B' C'"
                        by (metis Ar2_def Col_cases Par_cases Par_def Pj_def \<open>Ar2 PO E E' A B C\<close>
                            \<open>C \<noteq> PO\<close> assms(5) par_strict_not_col_1) 
                      {
                        assume "C' \<noteq> PO"
                        obtain B'' where "E E' Pj B B''" and "Col PO E' B''" and "E' A Pj B'' C"
                          using Prod_def assms(1) by blast
                        hence "B' = B''"
                          by (meson Ar1_def Ar2_def Prod_def assms(1,2,4) pj_uniqueness)
                        have "E' E Pj B' B"
                          by (simp add: \<open>B' = B''\<close> \<open>E E' Pj B B''\<close> pj_comm) 
                        moreover have "Col PO E B"
                          using Ar2_def \<open>Ar2 PO E E' A B C\<close> by blast 
                        moreover have "A' E Par C' B"
                        proof (rule l13_19 [of PO E' A B'])
                          show "\<not> Col PO E' A"
                            by (metis Ar2_def Col_cases \<open>A \<noteq> PO\<close>
                                \<open>Ar2 PO E E' A B C\<close> col2__eq) 
                          show "PO \<noteq> E'"
                            using \<open>\<not> Col PO E' A\<close> col_trivial_1 by blast 
                          show "PO \<noteq> B'"
                            using \<open>B' \<noteq> PO\<close> by auto 
                          show "PO \<noteq> A'"
                            using \<open>A' \<noteq> PO\<close> by auto 
                          show "PO \<noteq> C'"
                            using \<open>C' \<noteq> PO\<close> by auto 
                          show "PO \<noteq> A"
                            using \<open>A \<noteq> PO\<close> by auto 
                          show "PO \<noteq> C"
                            using \<open>C \<noteq> PO\<close> by blast 
                          show "PO \<noteq> E"
                            using Ar2_def \<open>Ar2 PO E E' A B C\<close> col_trivial_1 by force 
                          show "PO \<noteq> B"
                            using \<open>B \<noteq> PO\<close> by auto 
                          show "Col PO E' A'"
                            using Ar1_def assms(2) by force 
                          show "Col PO E' B'"
                            by (simp add: \<open>B' = B''\<close> \<open>Col PO E' B''\<close>) 
                          show "Col PO E' C'"
                            using Ar1_def assms(2) by auto 
                          show "Col PO A E"
                            by (meson Ar2_def Col_cases \<open>Ar2 PO E E' A B C\<close>) 
                          show "Col PO A C"
                            by (metis Ar2_def Col_cases \<open>Ar2 PO E E' A B C\<close> \<open>PO \<noteq> E\<close>
                                col2__eq) 
                          show "Col PO A B"
                            using \<open>Col PO A E\<close> \<open>PO \<noteq> E\<close> calculation(2) col_trivial_3 colx
                            by blast 
                          show "E' A Par B' C"
                            by (smt (verit, ccfv_threshold) Pj_def \<open>B' = B''\<close> \<open>Col PO A C\<close>
                                \<open>Col PO E' B''\<close> \<open>E' A Pj B'' C\<close> \<open>PO \<noteq> B'\<close>
                                \<open>\<not> Col PO E' A\<close> grid_not_par
                                not_par_not_col not_par_one_not_par) 
                          show "E' E Par B' B"
                            by (smt (verit, ccfv_threshold) Pj_def \<open>B' = B''\<close> \<open>Col PO A B\<close>
                                \<open>Col PO E' B''\<close> \<open>PO \<noteq> B'\<close> \<open>\<not> Col PO E' A\<close>
                                calculation(1) grid_not_par
                                not_par_not_col not_par_one_not_par) 
                          show "A A' Par C C'"
                            by (smt (verit, best) Ar1_def Par_cases Pj_def \<open>E' A Par B' C\<close>
                                \<open>\<not> Col PO E' A\<close> assms(2,3,5) grid_not_par not_par_one_not_par
                                par_col2_par_bis) 
                        qed
                        hence "E A' Par B C'"
                          using par_comm by blast 
                        hence "E A' Pj B C'"
                          by (simp add: Pj_def) 
                        ultimately show "Prod PO E' E A' B' C'"
                          by (metis Ar1_def Ar2_def Col_cases Prod_def assms(1,2)) 
                      }
                    qed
                  }
                qed
              }
            qed
          }
        qed
      }
    qed
  }
qed

(** Lemma 14.23 *)
(** Product is associative.*)
lemma prod_assoc1:
  assumes "Prod PO E E' A B AB"
    and "Prod PO E E' B C BC"
    and "Prod PO E E' A BC ABC"
  shows "Prod PO E E' AB C ABC" 
proof (cases "A = PO")
  have "Ar2 PO E E' A B AB" 
    using Prod_def assms(1) by blast 
  have "Ar2 PO E E' B C BC"
    using Prod_def assms(2) by blast 
  have "Ar2 PO E E' A BC ABC" 
    using Prod_def assms(3) by auto 
  show "A = PO \<Longrightarrow> Prod PO E E' AB C ABC"
    by (metis Ar2_def \<open>Ar2 PO E E' B C BC\<close> assms(1,3) prod_0_l
        prod_uniqueness)
  {
    assume "A \<noteq> PO"
    show "Prod PO E E' AB C ABC" 
    proof (cases "B = PO")
      show "B = PO \<Longrightarrow> Prod PO E E' AB C ABC"
        by (metis Ar2_def \<open>Ar2 PO E E' A B AB\<close> \<open>Ar2 PO E E' B C BC\<close> assms(1,2,3)
            prod_0_l prod_0_r prod_uniqueness) 
      {
        assume "B \<noteq> PO"
        show "Prod PO E E' AB C ABC" 
        proof (cases "C = PO")
          show "C = PO \<Longrightarrow> Prod PO E E' AB C ABC"
            by (metis Ar2_def \<open>Ar2 PO E E' A B AB\<close> assms(2,3) prod_0_r
                prod_uniqueness) 
          {
            assume "C \<noteq> PO"
            have "\<not> PO E Par E E'"
              using Ar2_def \<open>Ar2 PO E E' B C BC\<close> grid_not_par
              by blast 
            have "\<not> PO E Par PO E'"
              using Ar2_def \<open>Ar2 PO E E' B C BC\<close> grid_not_par_2 by blast 
            have "PO \<noteq> E"
              using Ar2_def \<open>Ar2 PO E E' A B AB\<close> not_col_distincts by blast 
            hence "PO \<noteq> E'"
              using Par_cases \<open>\<not> PO E Par E E'\<close> par_reflexivity by blast 
            hence "E \<noteq> E'"
              using \<open>\<not> PO E Par PO E'\<close> par_reflexivity by blast 
            obtain C' where "C C' Proj PO E' E E'"
              using Prodp_def assms(2) prod_to_prodp by blast 
            hence "C C' Par E E'"
              by (metis Ar2_def \<open>Ar2 PO E E' B C BC\<close> \<open>C \<noteq> PO\<close> proj_id
                  project_par_dir) 
            hence "E E' Pj C C'"
              by (simp add: Pj_def par_symmetry) 
            moreover have "Col PO E' C'"
              using Proj_def \<open>C C' Proj PO E' E E'\<close> by presburger 
            moreover have "E' AB Pj C' ABC" 
            proof -
              obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' AB"
                using Prod_def assms(1) by blast
              obtain C'' where "E E' Pj C C''" and "Col PO E' C''" and "E' B Pj C'' BC"
                using Prod_def assms(2) by blast
              hence "C' = C''"
                using Ar2_def \<open>Ar2 PO E E' B C BC\<close> calculation(1,2) pj_uniqueness by auto 
              obtain BC' where "E E' Pj BC BC'" and "Col PO E' BC'" and "E' A Pj BC' ABC"
                using Prod_def assms(3) by blast
              have "B' \<noteq> PO"
                using Ar2_def \<open>Ar2 PO E E' B C BC\<close> \<open>B \<noteq> PO\<close> \<open>E E' Pj B B'\<close>
                  sum_par_strict_a by blast
              have "BC \<noteq> PO"
                using \<open>B \<noteq> PO\<close> \<open>C \<noteq> PO\<close> assms(2) prod_null by blast
              have "E' AB Par C' ABC"
              proof (rule l13_19 [of PO B' B BC'])
                show "\<not> Col PO B' B"
                  by (metis Ar2_def \<open>Ar2 PO E E' A B AB\<close> \<open>B \<noteq> PO\<close>
                      \<open>B' \<noteq> PO\<close> \<open>Col PO E' B'\<close> l6_16_1
                      not_col_permutation_4) 
                show "PO \<noteq> B'"
                  using \<open>B' \<noteq> PO\<close> by auto 
                show "PO \<noteq> BC'"
                  by (metis Ar2_def Col_cases Par_cases Par_def Pj_def
                      \<open>Ar2 PO E E' B C BC\<close> \<open>BC \<noteq> PO\<close> \<open>E E' Pj BC BC'\<close>
                      par_strict_not_col_1) 
                show "PO \<noteq> E'"
                  by (simp add: \<open>PO \<noteq> E'\<close>) 
                show "PO \<noteq> C'"
                  by (metis Ar2_def \<open>Ar2 PO E E' B C BC\<close>
                      \<open>C C' Proj PO E' E E'\<close> \<open>C \<noteq> PO\<close> grid_not_par
                      proj_id) 
                show "PO \<noteq> B"
                  using \<open>B \<noteq> PO\<close> by auto 
                show "PO \<noteq> BC"
                  using \<open>BC \<noteq> PO\<close> by auto 
                show "PO \<noteq> AB"
                  using \<open>A \<noteq> PO\<close> \<open>PO \<noteq> B\<close> assms(1) prod_null
                  by blast 
                show "PO \<noteq> ABC"
                  using \<open>A \<noteq> PO\<close> \<open>BC \<noteq> PO\<close> assms(3) prod_null
                  by blast 
                show "Col PO B' E'"
                  by (simp add: \<open>Col PO E' B'\<close> col_permutation_5) 
                show "Col PO B' BC'"
                  using \<open>Col PO E' B'\<close> \<open>Col PO E' BC'\<close> \<open>PO \<noteq> E'\<close>
                    col_transitivity_1 by blast 
                show "Col PO B' C'"
                  using \<open>C' = C''\<close> \<open>Col PO E' B'\<close> \<open>Col PO E' C''\<close>
                    \<open>PO \<noteq> E'\<close> col_transitivity_1 by blast 
                show "Col PO B AB"
                  using Ar2_def Prod_def \<open>PO \<noteq> E\<close> assms(1)
                    col_transitivity_1 by presburger 
                show "Col PO B BC"
                  by (metis Ar2_def \<open>Ar2 PO E E' B C BC\<close> \<open>PO \<noteq> E\<close> l6_16_1
                      not_col_permutation_2) 
                show "Col PO B ABC"
                  by (meson Ar2_def Prod_def \<open>Col PO B BC\<close> \<open>PO \<noteq> BC\<close>
                      \<open>PO \<noteq> E\<close> assms(3) col_permutation_5
                      col_transitivity_1) 
                show "B' B Par BC' BC"
                  by (smt (verit, best) Ar2_def Par_cases Pj_def
                      \<open>Ar2 PO E E' B C BC\<close> \<open>B \<noteq> PO\<close> \<open>Col PO B' BC'\<close>
                      \<open>Col PO E' BC'\<close> \<open>E E' Pj B B'\<close> \<open>E E' Pj BC BC'\<close>
                      \<open>PO \<noteq> BC'\<close> \<open>PO \<noteq> E'\<close> col_transitivity_2 l6_16_1
                      par_trans) 
                show "B' AB Par BC' ABC"
                  by (smt (verit) Par_def Pj_def \<open>B \<noteq> PO\<close> \<open>Col PO B ABC\<close>
                      \<open>Col PO B AB\<close> \<open>Col PO E' B'\<close> \<open>Col PO E' BC'\<close>
                      \<open>E' A Pj B' AB\<close> \<open>E' A Pj BC' ABC\<close> \<open>PO \<noteq> ABC\<close> \<open>PO \<noteq> E'\<close>
                      \<open>\<not> Col PO B' B\<close> col_permutation_4
                      not_col_permutation_2 not_par_inter_exists
                      not_par_not_col parallel_uniqueness) 
                show "B E' Par BC C'"
                  by (metis Ar2_def Par_cases Pj_def \<open>Ar2 PO E E' B C BC\<close>
                      \<open>C C' Proj PO E' E E'\<close> \<open>C \<noteq> PO\<close> \<open>C' = C''\<close>
                      \<open>E' B Pj C'' BC\<close> proj_id) 
              qed
              thus ?thesis
                by (simp add: Pj_def)
            qed
            ultimately show "Prod PO E E' AB C ABC"
              using Ar2_def Prod_def \<open>Ar2 PO E E' A B AB\<close> \<open>Ar2 PO E E' A BC ABC\<close>
                \<open>Ar2 PO E E' B C BC\<close> by auto 
          }
        qed
      }
    qed
  }
qed

lemma prod_assoc2: 
  assumes "Prod PO E E' A B AB" and
    "Prod PO E E' B C BC"
    and "Prod PO E E' AB C ABC"
  shows "Prod PO E E' A BC ABC"
proof (cases "A = PO")
  have "Ar2 PO E E' A B AB"
    using Prod_def assms(1) by blast 
  have "Ar2 PO E E' B C BC" 
    using Prod_def assms(2) by blast 
  have "Ar2 PO E E' AB C ABC" 
    using Prod_def assms(3) by blast 
  show "A = PO \<Longrightarrow> Prod PO E E' A BC ABC"
    by (metis Ar2_def \<open>Ar2 PO E E' B C BC\<close> assms(1,3)
        prod_0_l prod_uniqueness) 
  show "A \<noteq> PO \<Longrightarrow> Prod PO E E' A BC ABC" 
  proof (cases "B = PO")
    show "A \<noteq> PO \<Longrightarrow> B = PO \<Longrightarrow> Prod PO E E' A BC ABC"
      by (metis Ar2_def \<open>Ar2 PO E E' A B AB\<close>
          \<open>Ar2 PO E E' B C BC\<close> assms(1,2,3) prod_0_l prod_0_r
          prod_uniqueness) 
    show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> Prod PO E E' A BC ABC" 
    proof (cases "C = PO")
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C = PO \<Longrightarrow> Prod PO E E' A BC ABC"
        by (metis Ar2_def \<open>Ar2 PO E E' A B AB\<close> assms(2,3)
            prod_0_r prod_uniqueness) 
      {
        assume "A \<noteq> PO" and "B \<noteq> PO" and "C \<noteq> PO"
        show "Prod PO E E' A BC ABC" 
        proof -
          have "\<not> PO E Par E E'"
            using Ar2_def \<open>Ar2 PO E E' AB C ABC\<close> grid_not_par by blast 
          have "\<not> PO E Par PO E'"
            using Ar2_def \<open>Ar2 PO E E' B C BC\<close> grid_not_par by auto 
          have "\<not> PO E' Par E E'"
            using Ar2_def \<open>Ar2 PO E E' B C BC\<close> grid_not_par_3 by blast 
          have "PO \<noteq> E"
            using Ar2_def \<open>Ar2 PO E E' AB C ABC\<close> col_trivial_1 by blast 
          hence "PO \<noteq> E'"
            using Par_cases \<open>\<not> PO E Par E E'\<close> par_reflexivity by blast 
          hence "E \<noteq> E'"
            using \<open>\<not> PO E Par PO E'\<close> par_reflexivity by blast 
          have "BC \<noteq> PO"
            using \<open>B \<noteq> PO\<close> \<open>C \<noteq> PO\<close> assms(2) prod_null by blast 
          obtain BC' where "BC BC' Proj PO E' E E'"
            using \<open>E \<noteq> E'\<close> \<open>PO \<noteq> E'\<close> \<open>\<not> PO E' Par E E'\<close>
              par_symmetry project_existence by blast 
          hence "BC BC' Par E E' \<or> BC = BC'"
            using Proj_def by auto 
          moreover have "BC = BC' \<Longrightarrow> BC BC' Par E E'"
            using Ar2_def \<open>Ar2 PO E E' B C BC\<close>
              \<open>BC BC' Proj PO E' E E'\<close> \<open>BC \<noteq> PO\<close> proj_id
            by blast 
          ultimately have "BC BC' Par E E'" by blast
          have "E E' Pj BC BC'"
            by (simp add: Pj_def \<open>BC BC' Par E E'\<close>
                par_symmetry) 
          moreover have "Col PO E' BC'"
            using Proj_def \<open>BC BC' Proj PO E' E E'\<close>
            by presburger 
          moreover have "E' A Pj BC' ABC" 
          proof -
            obtain B' where "E E' Pj B B'" and
              "Col PO E' B'" and "E' A Pj B' AB"
              using Prod_def assms(1) by blast 
            obtain C' where "E E' Pj C C'" and
              "Col PO E' C'" and "E' B Pj C' BC"
              using Prod_def assms(2) by blast 
            obtain C'' where "E E' Pj C C''" and 
              "Col PO E' C''" and "E' AB Pj C'' ABC"
              using Prod_def assms(3) by blast 
            hence "C' = C''"
              using Ar2_def \<open>Ar2 PO E E' AB C ABC\<close> \<open>Col PO E' C'\<close>
                \<open>E E' Pj C C'\<close> pj_uniqueness by force 
            have "E' A Par BC' ABC" 
            proof -
              have "B' \<noteq> PO"
                by (metis Ar2_def Prod_def \<open>BC \<noteq> PO\<close> \<open>E E' Pj B B'\<close>
                    assms(2) prod_0_l prod_uniqueness
                    sum_par_strict_a) 
              hence "E' A Par B' AB"
                by (metis Ar2_def Pj_def \<open>Ar2 PO E E' AB C ABC\<close>
                    \<open>Col PO E' B'\<close> \<open>E \<noteq> E'\<close> \<open>E' A Pj B' AB\<close>
                    not_col_permutation_1 par_col2_par_bis par_reflexivity
                    sum_par_strict_a) 
              moreover have "B' AB Par BC' ABC" 
              proof (rule l13_19 [of PO E' B C'], insert \<open>PO \<noteq> E'\<close>\<open>Col PO E' B'\<close> 
                  \<open>Col PO E' C'\<close> \<open>Col PO E' BC'\<close>)
                show "\<not> Col PO E' B"
                  by (metis Ar2_def Col_cases Par_cases Par_def Pj_def
                      \<open>Ar2 PO E E' A B AB\<close> \<open>B' \<noteq> PO\<close> \<open>Col PO E' B'\<close>
                      \<open>E E' Pj B B'\<close> col2__eq par_strict_not_col_4) 
                show "PO \<noteq> C'"
                  by (smt (verit, ccfv_threshold) Ar2_def Par_cases Pj_def
                      \<open>Ar2 PO E E' B C BC\<close> \<open>BC \<noteq> PO\<close> \<open>E' B Pj C' BC\<close>
                      \<open>PO \<noteq> E\<close> col_par col_trivial_3 not_strict_par
                      par_not_par) 
                show "PO \<noteq> B'"
                  using \<open>B' \<noteq> PO\<close> by auto 
                show "PO \<noteq> BC'"
                  by (metis Ar2_def \<open>Ar2 PO E E' B C BC\<close>
                      \<open>BC BC' Proj PO E' E E'\<close> \<open>BC \<noteq> PO\<close> not_col_distincts
                      proj_id) 
                show "PO \<noteq> B"
                  using \<open>\<not> Col PO E' B\<close> grid_not_par_5 by auto 
                show "PO \<noteq> BC"
                  using \<open>BC \<noteq> PO\<close> by auto 
                show "PO \<noteq> AB"
                  using \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> assms(1) prod_null by blast 
                show "PO \<noteq> ABC"
                  using \<open>C \<noteq> PO\<close> \<open>PO \<noteq> AB\<close> assms(3) prod_null by blast 
                show "Col PO B AB"
                  using Ar2_def Prod_def \<open>PO \<noteq> E\<close> assms(1)
                    col_transitivity_1 by presburger 
                show "Col PO B BC"
                  using Ar2_def Prod_def \<open>PO \<noteq> E\<close> assms(2)
                    col_transitivity_1 by presburger 
                show "Col PO B ABC"
                  using Ar2_def Prod_def \<open>PO \<noteq> E\<close> assms(2,3)
                    col_transitivity_1 by presburger 
                show "E' B Par C' BC"
                  by (metis Pj_def \<open>BC = BC' \<Longrightarrow> BC BC' Par E E'\<close>
                      \<open>BC BC' Proj PO E' E E'\<close> \<open>C' = C''\<close> \<open>Col PO E' C''\<close>
                      \<open>E' B Pj C' BC\<close> par_distinct project_not_col) 
                show "E' AB Par C' ABC"
                  by (metis Col_cases Pj_def \<open>C' = C''\<close> \<open>Col PO B ABC\<close>
                      \<open>Col PO E' C'\<close> \<open>E' AB Pj C'' ABC\<close> \<open>PO \<noteq> C'\<close>
                      \<open>\<not> Col PO E' B\<close> col2__eq) 
                show "B B' Par BC BC'"
                  by (metis Ar2_def Par_cases Pj_def \<open>Ar2 PO E E' B C BC\<close>
                      \<open>BC BC' Proj PO E' E E'\<close> \<open>BC \<noteq> PO\<close> \<open>Col PO E' B'\<close>
                      \<open>E E' Pj B B'\<close> \<open>E E' Pj BC BC'\<close> \<open>\<not> Col PO E' B\<close>
                      par_trans proj_id) 
              qed
              ultimately show ?thesis
                using postulate_of_transitivity_of_parallelism_def
                  postulate_of_transitivity_of_parallelism_thm
                by blast
            qed
            thus ?thesis
              by (simp add: Pj_def) 
          qed
          ultimately show ?thesis
            using Ar2_def Prod_def assms(1,2,3) by auto 
        qed
      }
    qed
  qed
qed

lemma prod_assoc:
  assumes "Prod PO E E' A B AB"
    and "Prod PO E E' B C BC"
  shows "Prod PO E E' A BC ABC \<longleftrightarrow> Prod PO E E' AB C ABC"
  by (meson assms(1,2) prod_assoc1 prod_assoc2) 

lemma prod_comm:
  assumes "Prod PO E E' A B C"
  shows "Prod PO E E' B A C"
proof (cases "A = PO")
  have "Ar2 PO E E' A B C"
    using Prod_def assms by blast 
  thus "A = PO \<Longrightarrow> Prod PO E E' B A C"
    by (metis Ar2_def assms prod_0_l
        prod_0_r prod_uniqueness) 
  show "A \<noteq> PO \<Longrightarrow> Prod PO E E' B A C" 
  proof (cases "B = PO")
    show "A \<noteq> PO \<Longrightarrow> B = PO \<Longrightarrow> Prod PO E E' B A C"
      by (metis Ar2_def \<open>Ar2 PO E E' A B C\<close> assms prod_0_l
          prod_0_r prod_uniqueness) 
    show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> Prod PO E E' B A C" 
    proof (cases "C = PO")
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C = PO \<Longrightarrow> Prod PO E E' B A C"
        using assms prod_null by blast 
      {
        assume "A \<noteq> PO" and "B \<noteq> PO" and "C \<noteq> PO"
        obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' C"
          using Prod_def assms by blast
        have "\<not> PO E Par E E'"
          using Ar2_def \<open>Ar2 PO E E' A B C\<close> grid_not_par by blast 
        have "\<not> PO E Par PO E'"
          using Ar2_def \<open>Ar2 PO E E' A B C\<close> par_id by blast 
        have "\<not> PO E' Par E E'"
          using Ar2_def \<open>Ar2 PO E E' A B C\<close> grid_not_par by blast 
        have "PO \<noteq> E"
          using Ar2_def \<open>Ar2 PO E E' A B C\<close> grid_not_par by blast 
        hence "PO \<noteq> E'"
          using Par_cases \<open>\<not> PO E Par E E'\<close> par_reflexivity by blast 
        hence "E \<noteq> E'"
          using \<open>\<not> PO E Par PO E'\<close> par_reflexivity by blast 
        then obtain A' where "A A' Proj PO E' E E'"
          using \<open>PO \<noteq> E'\<close> \<open>\<not> PO E' Par E E'\<close>
            par_symmetry project_existence by blast 
        hence "A A' Par E E' \<or> A = A'"
          using project_par_dir by blast 
        moreover have "A = A' \<Longrightarrow> A A' Par E E'"
          using Ar2_def \<open>A A' Proj PO E' E E'\<close> \<open>A \<noteq> PO\<close> \<open>Ar2 PO E E' A B C\<close> proj_id by blast 
        ultimately have "A A' Par E E'" 
          by blast
        have "E E' Pj A A'"
          using \<open>A A' Proj PO E' E E'\<close> project_pj by auto 
        moreover have "Col PO E' A'"
          using Proj_def \<open>A A' Proj PO E' E E'\<close> by presburger 
        moreover 
        have "C A' Par B E'"  
        proof (rule l13_11 [of PO], insert \<open>A \<noteq> PO\<close>\<open>B \<noteq> PO\<close>)
          show "\<not> Col PO C E'"
            by (metis Ar2_def Col_cases \<open>Ar2 PO E E' A B C\<close>
                \<open>C \<noteq> PO\<close> col3 col_trivial_3) 
          show "Col PO C B"
            by (metis Ar2_def Col_cases \<open>Ar2 PO E E' A B C\<close>
                col_transitivity_1 col_trivial_3) 
          show "Col PO B A"
            by (metis Ar2_def Col_cases \<open>Ar2 PO E E' A B C\<close>
                col_transitivity_1 col_trivial_3)
          show "A' \<noteq> PO"
            using Ar2_def \<open>A \<noteq> PO\<close> \<open>Ar2 PO E E' A B C\<close>
              calculation(1) sum_par_strict_a by blast 
          show "B' \<noteq> PO"
            by (metis Ar2_def Col_cases Par_cases Par_def Pj_def
                \<open>Ar2 PO E E' A B C\<close> \<open>B \<noteq> PO\<close> \<open>E E' Pj B B'\<close>
                par_strict_not_col_1) 
          show "Col PO E' A'"
            using calculation(2) by auto 
          show "Col PO A' B'"
            using \<open>Col PO E' B'\<close> \<open>PO \<noteq> E'\<close> calculation(2)
              col_transitivity_1 by blast 
          show "B B' Par A A'"
            by (metis Ar2_def Col_cases Par_cases Pj_def
                \<open>A A' Par E E'\<close> \<open>Ar2 PO E E' A B C\<close> \<open>B \<noteq> PO\<close>
                \<open>Col PO E' B'\<close> \<open>E E' Pj B B'\<close> col_transitivity_1
                not_par_one_not_par) 
          show "A E' Par C B'"
            by (metis NCol_cases Par_cases Pj_def \<open>Col PO E' B'\<close>
                \<open>E' A Pj B' C\<close> \<open>\<not> Col PO C E'\<close>) 
        qed
        hence "E' B Pj A' C"
          using Par_cases Pj_def by auto 
        ultimately show "Prod PO E E' B A C"
          using Ar2_def Prod_def \<open>Ar2 PO E E' A B C\<close> by auto 
      }
    qed
  qed
qed

(** Lemma 14.24 *)
(** Left distributivity of product over sum.*)
lemma prod_O_l_eq:
  assumes "Prod PO E E' PO B C"
  shows "C = PO"
  by (metis Ar2_def Prod_def assms prod_0_l prod_uniqueness) 

lemma prod_O_r_eq: 
  assumes "Prod PO E E' A PO C"
  shows "C = PO"
  using assms prod_O_l_eq prod_comm by blast 

lemma prod_uniquenessA:
  assumes "B \<noteq> PO" 
    and "Prod PO E E' A B C"
    and "Prod PO E E' A' B C"
  shows "A = A'" 
proof (cases "A' = PO")
  show "A' = PO \<Longrightarrow> A = A'"
    using assms(1,2,3) prod_O_l_eq prod_null by blast 
  {
    assume "A' \<noteq> PO"
    obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' C"
      using Prod_def assms(2) by blast 
    obtain B'' where "E E' Pj B B''" and "Col PO E' B''" and "E' A' Pj B'' C"
      using Prod_def assms(3) by blast 
    hence "B' = B''"
      using Ar2_def Prod_def \<open>Col PO E' B'\<close> \<open>E E' Pj B B'\<close>
        assms(3) pj_uniqueness by auto 
    {
      assume "E' A Par B' C" and "E' A' Par B' C"
      hence "E' A' Par E' A"
        using not_par_one_not_par by blast 
      have "E' A' ParStrict E' A \<Longrightarrow> A = A'"
        by (simp add: not_par_strict_id) 
      hence "A = A'"
        by (metis Ar2_def Prod_def \<open>E' A' Par E' A\<close> assms(2,3) colx par_id_4) 
    }
    thus "A = A'"
      by (metis Ar2_def NCol_perm Pj_def Prod_def \<open>B' = B''\<close>
          \<open>Col PO E' B''\<close> \<open>E' A Pj B' C\<close> \<open>E' A' Pj B'' C\<close>
          assms(1,2,3) col_transitivity_2 prod_null) 
  }
qed

lemma prod_uniquenessB:
  assumes "A \<noteq> PO"
    and "Prod PO E E' A B C"
    and "Prod PO E E' A B' C"
  shows "B = B'"
  by (meson assms(1,2,3) prod_comm prod_uniquenessA) 

(** Lemma 14.25 *)
(** Left distributivity of product over sum.*)
lemma distr_l:
  assumes "Sum PO E E' B C D"
    and "Prod PO E E' A B AB"
    and "Prod PO E E' A C AC"
    and "Prod PO E E' A D AD"
  shows "Sum PO E E' AB AC AD" 
proof (cases "A = PO")
  obtain B' C1 where "E E' Pj B B'" and "Col PO E' B'" and "PO E Pj B' C1" and 
    "PO E' Pj C C1" and "E' E Pj C1 D"
    using Sum_def assms(1) by blast
  obtain B'' where "E E' Pj B B''" and "Col PO E' B''" and "E' A Pj B'' AB"
    using Prod_def assms(2) by blast
  have "\<not> Col PO E E'"
    using Ar2_def assms(1) sum_ar2 by presburger 
  have "Col PO E A"
    using Ar2_def Prod_def assms(3) by auto 
  have "Col PO E B"
    using Ar2_def assms(1) sum_ar2 by presburger 
  have "PO \<noteq> E"
    using \<open>\<not> Col PO E E'\<close> grid_not_par_4 by auto 
  have "PO \<noteq> E'"
    using \<open>\<not> Col PO E E'\<close> grid_not_par_5 by presburger 
  have "B' = B''"
    using \<open>Col PO E B\<close> \<open>Col PO E' B''\<close> \<open>Col PO E' B'\<close>
      \<open>E E' Pj B B''\<close> \<open>E E' Pj B B'\<close> \<open>\<not> Col PO E E'\<close>
      pj_uniqueness by blast 
  obtain C' where "E E' Pj C C'" and "Col PO E' C'" and "E' A Pj C' AC"
    using Prod_def assms(3) by blast
  obtain D' where "E E' Pj D D'" and "Col PO E' D'" and "E' A Pj D' AD"
    using Prod_def assms(4) by blast
  have "Sum PO E' E B' C' D'"
    using Ar1_def \<open>Col PO E' B'\<close> \<open>Col PO E' C'\<close>
      \<open>Col PO E' D'\<close> \<open>E E' Pj B B'\<close> \<open>E E' Pj C C'\<close>
      \<open>E E' Pj D D'\<close> \<open>PO \<noteq> E'\<close> \<open>\<not> Col PO E E'\<close> assms(1)
      proj_preserves_sum by force 
  show "A = PO \<Longrightarrow> Sum PO E E' AB AC AD"
    by (metis \<open>\<not> Col PO E E'\<close> assms(2,3,4) prod_O_l_eq sum_O_O) 
  {
    assume "A \<noteq> PO"
    have "Sum PO E' A B' C' D'"
      by (metis \<open>A \<noteq> PO\<close> \<open>Col PO E A\<close> \<open>Sum PO E' E B' C' D'\<close>
          \<open>\<not> Col PO E E'\<close> col_trivial_3 colx
          not_col_permutation_5 sum_y_axis_change) 
    have "Sum PO A E' AB AC AD" 
    proof (rule proj_preserves_sum [of _ _ _ B' C' D'], insert \<open>E' A Pj C' AC\<close> 
        \<open>E' A Pj D' AD\<close> \<open>Sum PO E' A B' C' D'\<close>)
      show "\<not> Col PO E' A"
        using Col_perm \<open>A \<noteq> PO\<close> \<open>Col PO E A\<close> \<open>\<not> Col PO E E'\<close> col_trivial_3 colx by blast 
      show "Ar1 PO A AB AC AD"
        using Ar1_def Ar2_def Prod_def \<open>A \<noteq> PO\<close> \<open>PO \<noteq> E\<close> assms(2,3,4) 
          col_transitivity_1 by presburger 
      show "E' A Pj B' AB"
        by (simp add: \<open>B' = B''\<close> \<open>E' A Pj B'' AB\<close>) 
    qed
    thus "Sum PO E E' AB AC AD"
      using \<open>Col PO E A\<close> \<open>PO \<noteq> E\<close> not_col_permutation_5 sum_x_axis_unit_change by blast 
  }
qed

(** Lemma 14.24 *)
(** Right distributivity of product over sum.*)
lemma distr_r:
  assumes "Sum PO E E' A B D"
    and "Prod PO E E' A C AC"
    and "Prod PO E E' B C BC"
    and "Prod PO E E' D C DC"
  shows "Sum PO E E' AC BC DC"
  using assms(1,2,3,4) distr_l prod_comm by blast 

(** We omit lemma 14.26 which states that we have a division ring. *)

(** Lemma 14.27. *)
(** Sum and product are preserved by parallel projection on a different x-axis.*)
(** This lemma is used to prove that there is an isomorphism between number lines.*)
lemma prod_1_l_eq:
  assumes "Prod PO E E' A B B"
  shows "A = E \<or> B = PO"
  by (meson Ar2_def Prod_def assms prod_1_r prod_comm prod_uniquenessB) 

lemma prod_1_r_eq:
  assumes "Prod PO E E' A B A"
  shows "B = E \<or> A = PO"
  using assms prod_1_l_eq prod_comm by blast 

lemma change_grid_prod_l_O:
  assumes "PO E ParStrict O' E'"
    and "Ar1 PO E PO B C"
    and "Ar1 O' E' A' B' C'"
    (*and "PO O' Pj E E'"*)
    and "PO O' Pj PO A'"
    (*and "PO O' Pj B B'"*)
    and "PO O' Pj C C'"
    and "Prod PO E E' PO B C"
  shows "Prod O' E' E A' B' C'"
  by (smt (verit) Ar1_def NCol_cases Pj_def
      assms(1,2,3,4,5,6) grid_not_par not_par_not_col
      par_strict_not_col_1 par_strict_par
      parallel_uniqueness prod_0_r prod_O_l_eq
      prod_comm) 

lemma change_grid_prod1:
  assumes "PO E ParStrict O' E'"
    and "Ar1 PO E E B C"
    and "Ar1 O' E' A' B' C'"
    and "PO O' Pj E E'"
    and "PO O' Pj E A'" 
    and "PO O' Pj B B'"
    and "PO O' Pj C C'"
    and "Prod PO E E' E B C"
  shows "Prod O' E' E A' B' C'" 
proof (cases "B = PO")
  show "B = PO \<Longrightarrow> Prod O' E' E A' B' C'"
    by (smt (verit, ccfv_SIG) Ar1_def Par_strict_cases
        Pj_def assms(1,3,6,7,8) grid_not_par
        not_col_permutation_2 not_par_not_col
        par_strict_not_col_1 parallel_uniqueness prod_0_r
        prod_O_r_eq) 
  show "B \<noteq> PO \<Longrightarrow> Prod O' E' E A' B' C'" 
  proof (cases "C = PO")
    show "B \<noteq> PO \<Longrightarrow> C = PO \<Longrightarrow> Prod O' E' E A' B' C'"
      by (metis Ar1_def assms(2,8) prod_null) 
    {
      assume "B \<noteq> PO" and "C \<noteq> PO"
      have "Prod PO E E' E B B"
        using Ar1_def assms(1,2) par_strict_not_col_4 prod_1_l by presburger 
      have "B = C"
        using \<open>Prod PO E E' E B B\<close> assms(1,8) par_strict_not_col_4 prod_uniqueness by blast 
      have "A' = E'" 
      proof (rule l6_21 [of E E' O' E'])
        show "\<not> Col E E' O'"
          using Col_cases assms(1) par_strict_not_col_2 by blast 
        show "O' \<noteq> E'"
          using assms(1) par_strict_distinct by blast 
        show "Col E E' A'"
          by (metis Col_cases Pj_def assms(4,5) col_trivial_3 parallel_uniqueness) 
        show "Col E E' E'"
          by (simp add: col_trivial_2) 
        show "Col O' E' A'"
          using Ar1_def assms(3) by presburger 
        show "Col O' E' E'"
          using not_col_distincts by auto 
      qed
      have "C' = B'"
      proof (rule l6_21 [of B' B O' E'])
        show "\<not> Col B' B O'"
          by (metis Ar1_def Par_def Pj_def \<open>B = C\<close> \<open>B \<noteq> PO\<close>
              assms(1,2,3,6) l6_16_1 not_col_permutation_3
              not_col_permutation_4 not_par_strict_id par_not_col
              pj_comm) 
        show "O' \<noteq> E'"
          using assms(1) par_strict_distinct by blast 
        show "Col B' B C'"
          by (metis Col_cases Pj_def \<open>B = C\<close> assms(6,7) col_trivial_3 parallel_uniqueness) 
        show "Col B' B B'"
          using grid_not_par_5 by blast 
        show "Col O' E' C'"
          using Ar1_def assms(3) by auto 
        show "Col O' E' B'"
          using Ar1_def assms(3) by auto 
      qed
      thus "Prod O' E' E A' B' C'"
        by (metis Ar1_def Col_cases \<open>A' = E'\<close> assms(1,3) par_strict_not_col_2 prod_1_l) 
    }
  qed
qed

lemma change_grid_prod:
  assumes "PO E ParStrict O' E'"
    and "Ar1 PO E A B C"
    and "Ar1 O' E' A' B' C'"
    and "PO O' Pj E E'"
    and "PO O' Pj A A'"
    and "PO O' Pj B B'"
    and "PO O' Pj C C'"
    and "Prod PO E E' A B C" 
  shows "Prod O' E' E A' B' C'"
proof (cases "A = PO")
  show "A = PO \<Longrightarrow> Prod O' E' E A' B' C'"
    using assms(1,2,3,5,7,8) change_grid_prod_l_O by blast 
  show "A \<noteq> PO \<Longrightarrow> Prod O' E' E A' B' C'" 
  proof (cases "B = PO")
    show "A \<noteq> PO \<Longrightarrow> B = PO \<Longrightarrow> Prod O' E' E A' B' C'"
      by (smt (verit) Ar1_def Col_cases Par_strict_cases
          Pj_def assms(1,3,6,7,8) grid_not_par not_par_not_col
          par_strict_not_col_1 parallel_uniqueness prod_0_r
          prod_O_r_eq) 
    show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> Prod O' E' E A' B' C'" 
    proof (cases "C = PO")
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C = PO \<Longrightarrow> Prod O' E' E A' B' C'"
        using assms(8) prod_null by blast 
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C \<noteq> PO \<Longrightarrow> Prod O' E' E A' B' C'" 
      proof (cases "A = E")
        show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C \<noteq> PO \<Longrightarrow> A = E \<Longrightarrow> Prod O' E' E A' B' C'"
          using assms(1,2,3,4,5,6,7,8) change_grid_prod1 by blast 
        {
          assume "A \<noteq> PO" and "B \<noteq> PO" and "C \<noteq> PO" and "A \<noteq> E" 
          obtain E'' where "Bet PO O' E''" and "Cong O' E'' PO O'"
            using segment_construction by blast
          hence "E'' \<noteq> PO"
            using assms(1) bet_neq12__neq not_par_strict_id by blast 
          have "\<not> Col PO E E''"
            by (metis Col_cases \<open>E'' \<noteq> PO\<close> \<open>PO \<midarrow> O' \<midarrow> E''\<close>
                assms(1) bet_col col2__eq par_strict_not_col_1) 
          have "Prod PO E E'' A B C"
            using \<open>\<not> Col PO E E''\<close> assms(8) prod_y_axis_change by blast 
          then obtain B'' where "E E'' Pj B B''" and "Col PO E'' B''" and "E'' A Pj B'' C"
            using Prod_def by blast
          obtain C2 where "Sum PO E'' E E'' O' C2"
            by (metis Col_cases Col_def \<open>PO \<midarrow> O' \<midarrow> E''\<close> \<open>\<not> Col PO E E''\<close> 
                col_trivial_1 sum_exists) 
          have "\<not> Col PO E'' A"
            by (metis Ar1_def Col_cases \<open>A \<noteq> PO\<close> \<open>\<not> Col PO E E''\<close> assms(2) col_trivial_3 colx) 
          have "Sum PO E'' A E'' O' C2"
            using \<open>Sum PO E'' E E'' O' C2\<close> \<open>\<not> Col PO E'' A\<close> sum_y_axis_change by blast 
          obtain A0 A0' where "E'' A Pj E'' A0" and "Col PO A A0" and 
            "PO E'' Pj A0 A0'" and "PO A Pj O' A0'" and "A E'' Pj A0' C2"
            using Sum_def \<open>Sum PO E'' A E'' O' C2\<close> by blast 
          hence "A = A0"
            by (metis Col_cases Pj_def \<open>\<not> Col PO E'' A\<close> col2__eq grid_not_par) 
          have "PO O' Par E E'"
            using Pj_def assms(1,4) grid_not_par par_strict_not_col_2 by blast 
          have "PO O' Par A A'"
            by (metis Ar1_def Pj_def assms(1,2,3,5) not_col_permutation_1 par_not_col) 
          have "PO O' Par B B'"
            by (metis Ar1_def Pj_def assms(1,2,3,6) not_strict_par2 
                par_strict_not_col_4 par_strict_par) 
          have "PO O' Par C C'"
            by (metis Ar1_def Pj_def assms(1,2,3,7) not_strict_par2 
                par_strict_not_col_4 par_strict_par)
          have "PO \<noteq> O'"
            using assms(1) not_par_strict_id by blast
          have "A0' = A'" 
          proof (rule l6_21 [of O' E' A A'])
            show "\<not> Col O' E' A"
              by (meson Ar1_def Col_cases assms(1,2) par_not_col) 
            show "A \<noteq> A'"
              using \<open>PO O' Par A A'\<close> par_distincts by auto 
            show "Col O' E' A0'" 
            proof -
              {
                assume "PO A Par O' A0'"
                hence "O' E' Par O' A0'"
                  by (metis Ar1_def Col_cases Par_cases Par_def assms(1,2) 
                      col_par_par_col col_trivial_1 par_neq2) 
                hence "Col O' E' A0'"
                  using grid_not_par by blast 
              }
              moreover have "O' = A0' \<Longrightarrow> Col O' E' A0'"
                by (simp add: col_trivial_3) 
              ultimately show ?thesis 
                using \<open>PO A Pj O' A0'\<close> Pj_def by blast
            qed
            show "Col O' E' A'"
              using Ar1_def assms(3) by auto 
            show "Col A A' A0'" 
            proof -
              have "PO E'' Par A A0' \<Longrightarrow> Col A A' A0'"
                using Col_def Par_cases \<open>PO O' Par A A'\<close> \<open>PO \<midarrow> O' \<midarrow> E''\<close> col_par_par_col by blast 
              moreover have "A = A0' \<Longrightarrow> Col A A' A0'"
                using col_trivial_3 by blast 
              ultimately show ?thesis
                using Pj_def \<open>A = A0\<close> \<open>PO E'' Pj A0 A0'\<close> by blast
            qed
            show "Col A A' A'"
              by (simp add: col_trivial_2) 
          qed
          hence "PO E'' Par A A'"
            using Pj_def \<open>A = A0\<close> \<open>PO E'' Pj A0 A0'\<close> \<open>PO O' Par A A'\<close> par_distincts by blast 
          hence "PO A Par O' A'"
            by (metis Par_cases Pj_def \<open>A0' = A'\<close> \<open>PO A Pj O' A0'\<close> \<open>PO O' Par A A'\<close> 
                \<open>\<not> Col PO E'' A\<close> col_trivial_3 not_strict_par2) 
          have "A E'' Par A' C2" 
          proof -
            have "A' = C2 \<Longrightarrow> A E'' Par A' C2"
              by (metis Ar2_def Par_cases \<open>PO E'' Par A A'\<close> \<open>Sum PO E'' A E'' O' C2\<close>
                  col_trivial_3 not_strict_par2 sum_ar2) 
            thus ?thesis
              using Pj_def \<open>A E'' Pj A0' C2\<close> \<open>A0' = A'\<close> by blast 
          qed
          obtain E0 E0' where "E'' E Pj E'' E0" and "Col PO E E0" and 
            "PO E'' Pj E0 E0'" and "PO E Pj O' E0'" and "E E'' Pj E0' C2"
            using Sum_def \<open>Sum PO E'' E E'' O' C2\<close> by blast 
          hence "E0 = E"
            by (metis Pj_def \<open>\<not> Col PO E E''\<close> col2__eq grid_not_par) 
          have "E0' = E'" 
          proof (rule l6_21 [of O' E' E E'])
            show "\<not> Col O' E' E"
              using Col_cases assms(1) par_strict_not_col_2 by blast 
            show "E \<noteq> E'"
              using \<open>PO O' Par E E'\<close> par_distinct by auto 
            show "Col O' E' E0'" 
            proof -
              have "PO E Par O' E0' \<Longrightarrow> Col O' E' E0'"
                using Par_cases assms(1) par_id_3 par_not_par par_strict_par by blast 
              moreover have "O' = E0' \<Longrightarrow> Col O' E' E0'"
                using not_col_distincts by blast 
              ultimately show ?thesis
                using Pj_def \<open>PO E Pj O' E0'\<close> by blast 
            qed
            show "Col O' E' E'"
              by (simp add: col_trivial_2) 
            show "Col E E' E0'"
              by (smt (verit, ccfv_threshold) Par_cases Pj_def
                  \<open>E0 = E\<close> \<open>PO E'' Pj E0 E0'\<close> \<open>PO O' Par E E'\<close>
                  \<open>PO \<midarrow> O' \<midarrow> E''\<close> bet_col col_permutation_4
                  not_par_inter_exists par_col_par_2 par_id_5
                  par_trans_implies_playfair playfair_s_postulate_def
                  postulate_of_transitivity_of_parallelism_thm) 
            show "Col E E' E'" 
              by (simp add: col_trivial_2) 
          qed
          have "E E'' Par E' C2"
            by (metis Ar1_def Pj_def \<open>A E'' Par A' C2\<close> \<open>E E'' Pj E0' C2\<close> \<open>E0' = E'\<close> 
                \<open>PO A Par O' A'\<close> \<open>\<not> Col PO E'' A\<close> assms(3) col_par_par_col 
                col_permutation_5 par_symmetry)
          have "E E'' Par B B''"
            by (metis Ar1_def Col_cases Pj_def \<open>B \<noteq> PO\<close> \<open>Col PO E E0\<close> \<open>Col PO E'' B''\<close>
                \<open>E E'' Pj B B''\<close> \<open>E0 = E\<close> \<open>\<not> Col PO E E''\<close> assms(2) colx) 
          obtain C3 where "Sum PO E'' E B'' O' C3"
            by (metis Col_def NCol_cases \<open>Col PO E'' B''\<close> \<open>PO \<midarrow> O' \<midarrow> E''\<close> \<open>\<not> Col PO E E''\<close>
                sum_exists)
          then obtain B0 B0' where "E'' E Pj B'' B0" and "Col PO E B0" and 
            "PO E'' Pj B0 B0'" and "PO E Pj O' B0'" and "E E'' Pj B0' C3"
            using Sum_def by blast
          have "B'' \<noteq> PO"
            by (metis Ar1_def Col_cases Par_cases Par_def \<open>E E'' Par B B''\<close> \<open>\<not> Col PO E E''\<close>
                assms(2) par_strict_not_col_1) 
          have "B0 = B"
            by (meson Ar1_def \<open>Col PO E B0\<close> \<open>Col PO E'' B''\<close> \<open>E E'' Pj B B''\<close> \<open>E'' E Pj B'' B0\<close>
                \<open>\<not> Col PO E E''\<close> assms(2) col_permutation_5 pj_comm pj_uniqueness)
          have "B0' = B'" 
          proof (rule l6_21 [of O' E' B B'])
            show "\<not> Col O' E' B"
              using Col_cases \<open>B0 = B\<close> \<open>Col PO E B0\<close> assms(1) par_not_col by blast 
            show "B \<noteq> B'"
              using \<open>PO O' Par B B'\<close> par_distinct by auto 
            show "Col O' E' B0'"
              by (metis Par_cases Pj_def \<open>PO E Pj O' B0'\<close> assms(1) grid_not_par 
                  par_not_par par_strict_par) 
            show "Col O' E' B'"
            proof -
              have "PO E'' Par B B0' \<Longrightarrow> Col O' E' B'"
                using Ar1_def assms(3) by auto 
              moreover have "B = B0' \<Longrightarrow> Col O' E' B'"
                using \<open>Col O' E' B0'\<close> \<open>\<not> Col O' E' B\<close> by auto 
              ultimately show ?thesis
                using Ar1_def assms(3) by blast 
            qed
            show "Col B B' B0'" 
            proof -
              have "PO E'' Par B B0' \<Longrightarrow> Col B B' B0'"
                using Col_def Par_perm \<open>PO O' Par B B'\<close> \<open>PO \<midarrow> O' \<midarrow> E''\<close> col_par_par_col by blast 
              moreover have "B = B0' \<Longrightarrow> Col B B' B0'"
                using \<open>Col O' E' B0'\<close> \<open>\<not> Col O' E' B\<close> by auto 
              ultimately show ?thesis
                using Pj_def \<open>B0 = B\<close> \<open>PO E'' Pj B0 B0'\<close> by blast 
            qed
            show "Col B B' B'"
              by (simp add: col_trivial_2) 
          qed
          have "B' \<noteq> O'"
            by (metis \<open>B \<noteq> PO\<close> \<open>B0 = B\<close> \<open>Col PO E B0\<close> \<open>PO O' Par B B'\<close> assms(1) 
                col2__eq col_permutation_4 grid_not_par par_strict_not_col_1) 
          hence "E E'' Par B' C3"
            by (smt (verit, ccfv_threshold) Ar2_def Col_def Pj_def \<open>B0' = B'\<close>
                \<open>E E'' Pj B0' C3\<close> \<open>PO E Pj O' B0'\<close> \<open>PO \<midarrow> O' \<midarrow> E''\<close> \<open>Sum PO E'' E B'' O' C3\<close>
                assms(1) bet3__bet between_inner_transitivity col_trivial_3
                inter_uniqueness_not_par l5_3 par_strict_not_col_1 sum_ar2
                third_point) 
          have "E'' E Par B'' B"
            using Par_perm \<open>E E'' Par B B''\<close> by blast 
          have "Sum PO E'' A B'' O' C3"
            using \<open>Sum PO E'' E B'' O' C3\<close> \<open>\<not> Col PO E'' A\<close> sum_y_axis_change by blast 
          then obtain C0 C0' where "E'' A Pj B'' C0" and "Col PO A C0" and 
            "PO E'' Pj C0 C0'" and "PO A Pj O' C0'" and "A E'' Pj C0' C3"
            using Sum_def by blast 
          have "E'' A Par B'' C"
            by (metis Ar1_def Par_cases Pj_def \<open>E'' A Pj B'' C\<close> \<open>E'' E Par B'' B\<close> 
                \<open>\<not> Col PO E E''\<close> assms(2) grid_not_par_1 par_col2_par_bis) 
          have "C0 = C" 
          proof (rule l6_21 [of PO E B'' C])
            show "\<not> Col PO E B''"
              using \<open>B'' \<noteq> PO\<close> \<open>Col PO E'' B''\<close> \<open>\<not> Col PO E E''\<close> col2__eq 
                col_permutation_4 by blast 
            show "B'' \<noteq> C"
              using \<open>E'' A Par B'' C\<close> par_distinct by blast 
            show "Col PO E C0"
              by (metis Ar1_def \<open>A \<noteq> PO\<close> \<open>Col PO A C0\<close> assms(2) col_trivial_3 colx) 
            show "Col PO E C"
              using Ar1_def assms(2) by auto 
            show "Col B'' C C0"
              by (metis Pj_def \<open>E'' A Par B'' C\<close> \<open>E'' A Pj B'' C0\<close>
                  col_par_par_col grid_not_par_5 not_col_permutation_2 pj_comm) 
            show "Col B'' C C"
              using grid_not_par_6 by blast 
          qed
          have "C0' = C'" 
          proof (rule l6_21 [of O' E' C C'])
            show "\<not> Col O' E' C"
              by (meson Ar1_def Col_cases assms(1,2) par_not_col) 
            show "C \<noteq> C'"
              using \<open>PO O' Par C C'\<close> par_distinct by auto 
            show "Col O' E' C0'" 
            proof -
              {
                assume "PO A Par O' C0'"
                have "O' C' Par O' C0'" 
                proof -
                  have "PO E Par O' C'" 
                  proof (rule par_col_par [of _ _ _ _ E'])
                    show "O' \<noteq> C'"
                      by (metis Ar1_def Col_cases \<open>C \<noteq> PO\<close> \<open>PO O' Par C C'\<close> assms(1,2)
                          col2__eq grid_not_par par_strict_not_col_1) 
                    show "PO E Par O' E'"
                      by (simp add: Par_def assms(1)) 
                    show "Col O' E' C'"
                      using Ar1_def assms(3) by auto 
                  qed
                  hence "O' C' Par PO E"
                    using Par_cases by blast 
                  moreover have "PO E Par O' C0'"
                    by (metis Ar1_def Col_cases \<open>PO A Par O' C0'\<close> assms(2) par_col_par_2) 
                  ultimately show ?thesis
                    using par_not_par by blast 
                qed
                hence "Col O' E' C0'"
                  by (metis Ar1_def Col_cases Par_cases assms(3) not_par_strict_id 
                      par_not_col_strict) 
              }
              moreover have "O' = C0' \<Longrightarrow> Col O' E' C0'"
                by (simp add: col_trivial_3) 
              ultimately show ?thesis
                using Pj_def \<open>PO A Pj O' C0'\<close> by blast 
            qed
            show "Col O' E' C'"
              using Ar1_def assms(3) by auto 
            show "Col C C' C0'"
            proof -
              have "PO A Par O' C0' \<Longrightarrow> Col C C' C0'"
                by (smt (verit, ccfv_SIG) Pj_def \<open>A = A0\<close> \<open>C0 = C\<close>
                    \<open>PO E'' Pj C0 C0'\<close> \<open>PO O' Par C C'\<close> \<open>PO \<midarrow> O' \<midarrow> E''\<close> bet_col
                    col_permutation_4 grid_not_par par_col_par_2
                    parallel_uniqueness) 
              moreover have "O' = C0' \<Longrightarrow> Col C C' C0'"
                by (metis Pj_def \<open>C0 = C\<close> \<open>PO E'' Pj C0 C0'\<close> \<open>PO O' Par C C'\<close>
                    \<open>PO \<midarrow> O' \<midarrow> E''\<close> bet_col col_par_par_col grid_not_par_5
                    not_col_permutation_4 par_comm) 
              ultimately show ?thesis
                using Pj_def \<open>PO A Pj O' C0'\<close> by blast 
            qed
            show "Col C C' C'"
              by (simp add: col_trivial_2) 
          qed
          have "B B'' Par B' C3"
            using Par_cases \<open>E E'' Par B B''\<close> \<open>E E'' Par B' C3\<close> not_par_one_not_par by blast
          have "A E'' Par C' C3" 
          proof -
            {
              assume "C' = C3"
              have "E'' E Par C' O'"
              proof (rule par_col_par [of _ _ _ _ B'])
                show "C' \<noteq> O'"
                  by (metis Ar1_def Col_cases \<open>C \<noteq> PO\<close> \<open>PO O' Par C C'\<close> assms(1,2)
                      col2__eq grid_not_par par_strict_not_col_1) 
                show "E'' E Par C' B'"
                  using Par_cases \<open>C' = C3\<close> \<open>E E'' Par B' C3\<close> by blast
                show "Col C' B' O'"
                  by (metis Ar1_def Col_cases assms(3) col_transitivity_1) 
              qed
              hence "E E'' Par O' C'"
                using Par_cases by auto 
              hence "E E'' Par O' E'"
                by (metis Ar1_def Col_cases assms(3) par_col_par)
              hence "E E'' Par PO E"
                using assms(1) not_par_one_not_par par_strict_par by blast
              hence "A E'' Par C' C3"
                using Par_cases \<open>\<not> Col PO E E''\<close> par_id_1 by blast 
            }
            thus ?thesis
              using Pj_def \<open>A E'' Pj C0' C3\<close> \<open>C0' = C'\<close> by blast 
            hence "C B'' Par C' C3"
              by (metis Par_cases \<open>E'' A Par B'' C\<close> par_trans) 
          qed

          have "Prod O' E' C2 A' B' C'" 
          proof -
            {
              assume "Col O' E' C2" 
              have "C2 \<noteq> O'"
                using \<open>E'' \<noteq> PO\<close> \<open>Sum PO E'' A E'' O' C2\<close> \<open>\<not> Col PO E'' A\<close> sum_A_null by blast 
              have "Col PO O' C2"
                by (metis Ar2_def NCol_perm \<open>E'' \<noteq> PO\<close> \<open>Sum PO E'' A E'' O' C2\<close>
                    col_transitivity_2 sum_ar2) 
              have "Col PO O' E'"
                using \<open>C2 \<noteq> O'\<close> \<open>Col O' E' C2\<close> \<open>Col PO O' C2\<close> col2__eq col_permutation_4 by blast 
              hence False
                using Col_cases assms(1) par_strict_not_col_3 by blast 
            }
            moreover have "E' C2 Pj B' C3"
              by (metis Par_perm Pj_def \<open>E E'' Par B' C3\<close> \<open>E E'' Par E' C2\<close> par_not_par) 
            moreover have "Col O' C2 C3"
              by (metis Ar2_def \<open>E'' \<noteq> PO\<close> \<open>Sum PO E'' A E'' O' C2\<close> 
                  \<open>Sum PO E'' E B'' O' C3\<close> col_transitivity_2 sum_ar2) 
            moreover have "C2 A' Pj C3 C'"
              by (metis Par_perm Pj_def \<open>A E'' Par A' C2\<close> \<open>A E'' Par C' C3\<close> par_trans) 
            ultimately show ?thesis
              using Ar1_def Ar2_def Prod_def assms(3) by auto 
          qed
          thus "Prod O' E' E A' B' C'"
            using assms(1) not_col_permutation_1 par_strict_not_col_2 prod_y_axis_change by blast 
        }
      qed
    qed
  qed
qed


(** Lemma
 14.28 is something like
  \<exists> f,
  prod O E X A B C ->
  prod O' E' f(X) f(A') f(B') f(C') ?
*)


(** Lemma 14.29 *)
(** From Pappus-Pascal we can derive that the product is symmetric, hence we have a field. *)

(* already done : prod_comm *)

lemma prod_sym:
  assumes "Prod PO E E' A B C"
  shows "Prod PO E E' B A C"
  by (simp add: assms prod_comm) 

(** Lemma 14.31 *)
lemma l14_31_1:
  assumes "Ar2p4 PO E E' A B C D" 
    and "C \<noteq> PO"
    and "\<exists> X. Prod PO E E' A B X \<and> Prod PO E E' C D X"
  shows "Prod PO C E' A B D" 
proof (cases "A = PO")
  obtain X where "Prod PO E E' A B X" and "Prod PO E E' C D X"
    using assms(3) by blast
  show "A = PO \<Longrightarrow> Prod PO C E' A B D"
    by (metis Ar2_def Prod_def \<open>Prod PO E E' A B X\<close>
        \<open>Prod PO E E' C D X\<close> assms(2) col_transitivity_1 prod_0_l
        prod_1_r prod_O_l_eq prod_null) 
  show "A \<noteq> PO \<Longrightarrow> Prod PO C E' A B D" 
  proof (cases "B = PO")
    show "A \<noteq> PO \<Longrightarrow> B = PO \<Longrightarrow> Prod PO C E' A B D"
      by (metis Ar2_def Prod_def assms(2,3) col_transitivity_1 prod_0_r
          prod_1_r prod_O_r_eq prod_null) 
    show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> Prod PO C E' A B D" 
    proof (cases "D = PO")
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> D = PO \<Longrightarrow> Prod PO C E' A B D"
        using assms(3) prod_O_r_eq prod_null by blast 
      {
        assume "A \<noteq> PO" and "B \<noteq> PO" and "D \<noteq> PO"
        have "\<not> PO E Par E E'"
          using Ar2_def Prod_def \<open>Prod PO E E' A B X\<close> grid_not_par by auto 
        have "\<not> PO E Par PO E'"
          using Ar2_def Prod_def \<open>Prod PO E E' C D X\<close> par_id by blast 
        have "PO \<noteq> E"
          using Ar2_def Prod_def assms(3) grid_not_par by blast 
        hence "PO \<noteq> E'"
          using Par_cases \<open>\<not> PO E Par E E'\<close> par_reflexivity by blast 
        obtain B'' where "B B'' Proj PO E' E' C"
          by (metis Ar2_def Col_def Par_cases Prod_def assms(2,3) col2__eq
              grid_not_par project_existence) 
        hence "B B'' Par E' C"
          by (metis Ar2_def Prod_def Proj_def \<open>B \<noteq> PO\<close> assms(3) col_permutation_2 
              col_transitivity_2)
        have "C E' Par B B''"
          using Par_cases \<open>B B'' Par E' C\<close> by blast 
        hence "C E' Pj B B''"
          using Pj_def by blast 
        moreover have "Col PO E' B''"
          using Proj_def \<open>B B'' Proj PO E' E' C\<close> by auto 
        moreover have "E' A Pj B'' D" 
        proof -
          obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' X"
            using Prod_def \<open>Prod PO E E' A B X\<close> by blast 
          obtain D' where "E E' Pj D D'" and "Col PO E' D'" and "E' C Pj D' X"
            using Prod_def \<open>Prod PO E E' C D X\<close> by blast
          have "B' \<noteq> PO"
            by (metis Ar2_def Prod_def \<open>B \<noteq> PO\<close> \<open>E E' Pj B B'\<close> assms(3) sum_par_strict_a) 
          have "E B'' Par C B'" 
          proof (rule l13_11 [of PO _ _ _ B _ E'], insert \<open>C E' Par B B''\<close> \<open>B \<noteq> PO\<close> assms(2))
            show "\<not> Col PO E B'"
              by (metis Col_cases Par_def \<open>B' \<noteq> PO\<close> \<open>Col PO E' B'\<close> \<open>PO \<noteq> E'\<close>
                  \<open>PO \<noteq> E\<close> \<open>\<not> PO E Par PO E'\<close> col2__eq col_trivial_3) 
            show "Col PO E C"
              using Ar2_def Prod_def assms(3) by auto 
            show "Col PO C B"
              by (meson Ar2_def Prod_def \<open>PO \<noteq> E\<close> assms(3) col3 col_trivial_3) 
            show "B'' \<noteq> PO"
              by (metis Par_cases Proj_def \<open>B B'' Proj PO E' E' C\<close> \<open>B \<noteq> PO\<close>
                  \<open>Col PO C B\<close> grid_not_par not_par_not_col par_trans) 
            show "Col PO B' B''"
              using \<open>Col PO E' B'\<close> \<open>PO \<noteq> E'\<close> calculation(2) col_transitivity_1 by blast 
            show "Col PO B'' E'"
              using Col_cases calculation(2) by blast
            show "B B' Par E E'"
              by (metis Par_cases Pj_def \<open>B B'' Proj PO E' E' C\<close> \<open>C E' Par B B''\<close> 
                  \<open>Col PO E' B'\<close> \<open>E E' Pj B B'\<close> par_distinct project_not_col) 
            show "E' \<noteq> PO"
              using \<open>PO \<noteq> E'\<close> by auto 
          qed
          have "X \<noteq> PO"
            using \<open>D \<noteq> PO\<close> \<open>Prod PO E E' C D X\<close> assms(2) prod_null by blast 
          have "A D' Par C B'" 
          proof (rule l13_11 [of PO _ _ _ X _ E'], insert \<open>X \<noteq> PO\<close> assms(2))
            show "\<not> Col PO A B'"
              by (metis Ar2_def Prod_def \<open>A \<noteq> PO\<close> \<open>B' \<noteq> PO\<close> \<open>Col PO E' B'\<close>
                  assms(3) col_permutation_5 col_transitivity_1) 
            show "Col PO A C"
              by (meson Ar2_def Prod_def \<open>PO \<noteq> E\<close> assms(3) col_transitivity_1) 
            show "Col PO C X"
              by (meson Ar2_def Prod_def \<open>PO \<noteq> E\<close> \<open>Prod PO E E' A B X\<close> assms(3)
                  col_transitivity_1) 
            show "D' \<noteq> PO"
              by (metis Ar2_def Col_def Par_cases Par_def Pj_def Prod_def
                  \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> \<open>E E' Pj D D'\<close> assms(3) par_strict_not_col_1
                  prod_O_r_eq prod_null)
            show "E' \<noteq> PO"
              using \<open>PO \<noteq> E'\<close> by auto 
            show "Col PO B' D'"
              using \<open>Col PO E' B'\<close> \<open>Col PO E' D'\<close> \<open>PO \<noteq> E'\<close> col_transitivity_1 by blast 
            show "Col PO D' E'"
              using Col_cases \<open>Col PO E' D'\<close> by blast 
            show "C E' Par X D'"
              by (metis Pj_def \<open>Col PO A C\<close> \<open>Col PO C X\<close> \<open>Col PO D' E'\<close>
                  \<open>Col PO E' B'\<close> \<open>E' C Pj D' X\<close> \<open>PO \<noteq> E'\<close> \<open>X \<noteq> PO\<close>
                  \<open>\<not> Col PO A B'\<close> assms(2) col_trivial_3 colx pj_comm) 
            show "X B' Par A E'"
              by (metis Par_cases Pj_def \<open>Col PO A C\<close> \<open>Col PO C X\<close> \<open>E' A Pj B' X\<close> 
                  \<open>\<not> Col PO A B'\<close> assms(2) col_trivial_3 colx) 
          qed
          have "D B'' Par A E'" 
          proof  (rule l13_11 [of PO _ _ _ E _ D'], insert \<open>A \<noteq> PO\<close>)
            show "\<not> Col PO D E'"
              by (metis Ar2_def Prod_def Proj_def \<open>B B'' Proj PO E' E' C\<close>
                  \<open>D \<noteq> PO\<close> assms(3) col_par col_transitivity_1 col_trivial_3) 
            show "E \<noteq> PO"
              using \<open>PO \<noteq> E\<close> by auto 
            show "Col PO D A"
              by (metis Ar2_def Col_cases Prod_def assms(3) col_transitivity_1
                  col_trivial_3) 
            show "Col PO A E"
              by (meson Col_cases Prodp_def assms(3) prod_to_prodp) 
            show "B'' \<noteq> PO"
              by (smt (verit, ccfv_SIG) Ar2_def NCol_cases Par_def Prod_def
                  \<open>B' \<noteq> PO\<close> \<open>Col PO E' B'\<close> \<open>E B'' Par C B'\<close> assms(3) colx
                  par_strict_not_col_1) 
            show "D' \<noteq> PO"
              by (metis Col_cases Par_cases Pj_def \<open>A \<noteq> PO\<close> \<open>Col PO A E\<close>
                  \<open>Col PO D A\<close> \<open>E E' Pj D D'\<close> \<open>\<not> Col PO D E'\<close> col2__eq
                  col_trivial_3 not_strict_par2) 
            show "Col PO E' B''"
              by (simp add: calculation(2)) 
            show "Col PO B'' D'"
              using \<open>Col PO E' D'\<close> \<open>PO \<noteq> E'\<close> calculation(2) col_transitivity_1
              by blast 
            show "A D' Par E B''"
              using \<open>A D' Par C B'\<close> \<open>E B'' Par C B'\<close> not_par_one_not_par by blast 
            show "E E' Par D D'"
              using Col_cases Pj_def \<open>Col PO E' D'\<close> \<open>E E' Pj D D'\<close> \<open>\<not> Col PO D E'\<close> by blast 
          qed
          thus ?thesis
            using Par_perm Pj_def by blast 
        qed
        ultimately show "Prod PO C E' A B D"
          by (smt (verit, ccfv_threshold) Ar2_def Prod_def Proj_def
              \<open>B B'' Proj PO E' E' C\<close> \<open>PO \<noteq> E\<close> assms(3) col_par
              col_permutation_1 col_transitivity_2) 
      }
    qed
  qed
qed

lemma l14_31_2:
  assumes "Ar2p4 PO E E' A B C D"
    and "C \<noteq> PO"
    and "Prod PO C E' A B D"
  shows "\<exists> X. Prod PO E E' A B X \<and> Prod PO E E' C D X"
proof (cases "A = PO")
  show "A = PO \<Longrightarrow> \<exists>X. Prod PO E E' A B X \<and> Prod PO E E' C D X"
    by (metis Ar2p4_def assms(1,3) prod_0_l prod_0_r prod_O_l_eq) 
  show "A \<noteq> PO \<Longrightarrow> \<exists>X. Prod PO E E' A B X \<and> Prod PO E E' C D X" 
  proof (cases "B = PO")
    show "A \<noteq> PO \<Longrightarrow> B = PO \<Longrightarrow> \<exists>X. Prod PO E E' A B X \<and> Prod PO E E' C D X"
      by (metis Ar2p4_def assms(1,3) prod_0_r prod_O_r_eq) 
    show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> \<exists>X. Prod PO E E' A B X \<and> Prod PO E E' C D X" 
    proof (cases "D = PO")
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> D = PO \<Longrightarrow> \<exists>X. Prod PO E E' A B X \<and> Prod PO E E' C D X"
        using assms(3) prod_null by blast 
      {
        assume "A \<noteq> PO" and "B \<noteq> PO" and "D \<noteq> PO"
        obtain B' where "B B' Proj PO E' E E'"
          by (metis Ar2p4_def Col_perm assms(1) grid_not_par project_existence) 
        hence "B B' Par E E'"
          by (metis Ar2p4_def \<open>B \<noteq> PO\<close> assms(1) proj_id project_par_dir) 
        obtain X where "B' X Proj PO E E' A"
          by (metis Ar2p4_def Par_cases assms(1) col_trivial_1 col_trivial_2
              not_strict_par1 project_existence)
        have "X \<noteq> PO"
          by (metis Ar2p4_def Proj_def \<open>A \<noteq> PO\<close> \<open>B B' Proj PO E' E E'\<close>
              \<open>B \<noteq> PO\<close> \<open>B' X Proj PO E E' A\<close> assms(1) col_permutation_2
              not_col_distincts not_strict_par project_col_project
              project_id) 
        have "B' X Par E' A"
          by (metis Ar2p4_def Proj_def \<open>B B' Proj PO E' E E'\<close> \<open>B \<noteq> PO\<close>
              \<open>B' X Proj PO E E' A\<close> assms(1) proj_id) 
        obtain B'' where "C E' Pj B B''" and "Col PO E' B''" and "E' A Pj B'' D"
          using Prod_def assms(3) by blast
        have "E E' Pj B B'"
          using \<open>B B' Proj PO E' E E'\<close> project_pj by auto 
        moreover have "Col PO E' B'"
          using Proj_def \<open>B B' Proj PO E' E E'\<close> by force 
        moreover have "E' A Pj B' X"
          using \<open>B' X Proj PO E E' A\<close> project_pj by auto 
        ultimately have "Prod PO E E' A B X"
          using Ar2_def Ar2p4_def Prod_def Proj_def \<open>B' X Proj PO E E' A\<close> assms(1) by auto 
        obtain D' where "D D' Proj PO E' E E'"
          by (meson Ar2p4_def Prodp_def assms(1) prod_exists prod_to_prodp) 
        hence "D D' Par E E'"
          by (metis Ar2p4_def \<open>D \<noteq> PO\<close> assms(1) proj_id project_par_dir) 
        moreover have "Prod PO E E' C D X" 
        proof -
          have "E E' Pj D D'"
            using \<open>D D' Proj PO E' E E'\<close> project_pj by auto 
          moreover have "Col PO E' D'"
            using Proj_def \<open>D D' Proj PO E' E E'\<close> by presburger 
          moreover have "E' C Pj D' X" 
          proof -
            have "E' C Par D' X" 
            proof -
              have "X D' Par B B''" 
              proof (rule l13_11 [of PO _ _ _ D _ B'])
                show "\<not> Col PO X B''"
                  by (metis Ar2_def Col_cases Prod_def \<open>B \<noteq> PO\<close> \<open>C E' Pj B B''\<close>
                      \<open>Col PO E' B''\<close> \<open>Prod PO E E' A B X\<close> \<open>X \<noteq> PO\<close> assms(3)
                      col_trivial_3 colx sum_par_strict_a) 
                show "B \<noteq> PO"
                  using \<open>B \<noteq> PO\<close> by auto 
                show "D \<noteq> PO"
                  by (simp add: \<open>D \<noteq> PO\<close>) 
                show "Col PO X B"
                  by (metis Ar2p4_def Proj_def \<open>B' X Proj PO E E' A\<close> assms(1)
                      col_transitivity_1) 
                show "Col PO B D"
                  by (metis Ar2p4_def Proj_def \<open>B' X Proj PO E E' A\<close> assms(1)
                      col_transitivity_1) 
                show "D' \<noteq> PO"
                  using Ar2p4_def \<open>D D' Proj PO E' E E'\<close> \<open>D \<noteq> PO\<close> assms(1)
                    col_trivial_3 proj_id by auto 
                show "B' \<noteq> PO"
                  using \<open>B' X Proj PO E E' A\<close> \<open>X \<noteq> PO\<close> not_col_distincts project_not_col by blast 
                show "Col PO B'' D'"
                  by (metis Proj_def \<open>B B' Proj PO E' E E'\<close> \<open>Col PO E' B''\<close> 
                      calculation(2) col_transitivity_1) 
                show "Col PO D' B'"
                  by (metis Proj_def \<open>B B' Proj PO E' E E'\<close> calculation(2) col_transitivity_1) 
                show "B B' Par D D'"
                  using \<open>B B' Par E E'\<close> \<open>D D' Par E E'\<close> not_par_one_not_par by blast 
                show "D B'' Par X B'"
                  by (metis Par_cases Pj_def Proj_def \<open>B B' Proj PO E' E E'\<close>
                      \<open>B' X Par E' A\<close> \<open>Col PO E' B''\<close> \<open>D D' Par E E'\<close> \<open>E' A Pj B'' D\<close>
                      calculation(2) par_distinct par_not_par project_id) 
              qed
              thus ?thesis
                by (metis Par_cases Pj_def \<open>C E' Pj B B''\<close> not_par_one_not_par par_distinct) 
            qed
            thus ?thesis
              using Pj_def by blast 
          qed
          ultimately show ?thesis
            using Ar2_def Ar2p4_def Prod_def Proj_def \<open>B' X Proj PO E E' A\<close> assms(1) by auto 
        qed
        ultimately show "\<exists>X. Prod PO E E' A B X \<and> Prod PO E E' C D X"
          using \<open>Prod PO E E' A B X\<close> by blast
      }
    qed
  qed
qed

lemma prod_x_axis_unit_change:
  assumes "Ar2p4 PO E E' A B C D"
    and "Col PO E U"
    and "U \<noteq> PO"
    and "\<exists> X. Prod PO E E' A B X \<and> Prod PO E E' C D X"
  shows "\<exists> Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y" 
proof (cases "A = PO")
  obtain X where "Prod PO E E' A B X" and "Prod PO E E' C D X"
    using assms(4) by auto 
  {
    assume "A = PO"
    hence "X = PO"
      using \<open>Prod PO E E' A B X\<close> prod_O_l_eq by blast 
    have "C = PO \<or> D = PO"
      using \<open>Prod PO E E' C D X\<close> \<open>X = PO\<close> prod_null by blast 
    moreover {
      assume "C = PO"
      have "Prod PO U E' PO B PO"
        by (metis Ar2_def Prod_def \<open>Prod PO E E' A B X\<close> assms(2,3) col_transitivity_1
            grid_not_par prod_0_l) 
      moreover have "Prod PO U E' PO D PO"
        by (metis Ar2_def Prod_def \<open>Prod PO E E' C D X\<close> assms(2) calculation 
            col_transitivity_1 grid_not_par prod_0_l) 
      ultimately have "\<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y"
        using \<open>A = PO\<close> \<open>C = PO\<close> by auto         
    }
    moreover {
      assume "D = PO"
      have "Prod PO U E' PO B PO"
        by (metis Ar2_def Prod_def \<open>Prod PO E E' A B X\<close> assms(2,3) col_transitivity_1
            grid_not_par prod_0_l) 
      moreover have "Prod PO U E' C PO PO"
        by (metis Ar2_def Prod_def \<open>Prod PO E E' C D X\<close> assms(2) calculation 
            col_transitivity_1 grid_not_par prod_0_r) 
      ultimately have "\<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y"
        using \<open>A = PO\<close> \<open>D = PO\<close> by auto 
    }
    ultimately show "\<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y"
      by blast
  }
  show "A \<noteq> PO \<Longrightarrow> \<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y" 
  proof (cases "B = PO")
    {
      assume "A \<noteq> PO" and"B = PO"
      have "X = PO"
        using \<open>B = PO\<close> \<open>Prod PO E E' A B X\<close> prod_O_r_eq by auto 
      have "C = PO \<or> D = PO"
        using \<open>Prod PO E E' C D X\<close> \<open>X = PO\<close> prod_null by auto 
      moreover have "C = PO \<Longrightarrow> Prod PO U E' A B PO \<and> Prod PO U E' C D PO"
        by (metis Ar2_def Prod_def \<open>B = PO\<close> \<open>Prod PO E E' A B X\<close> \<open>Prod PO E E' C D X\<close>
            assms(2,3) col_transitivity_1 grid_not_par prod_0_l prod_0_r) 
      moreover have "D = PO \<Longrightarrow> Prod PO U E' A B PO \<and> Prod PO U E' C D PO"
        by (metis Ar2_def Prod_def \<open>B = PO\<close> \<open>Prod PO E E' A B X\<close> \<open>Prod PO E E' C D X\<close>
            assms(2,3) col_transitivity_1 not_col_permutation_5 prod_0_r) 
      ultimately show "\<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y"
        by blast 
    }
    show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> \<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y" 
    proof (cases "C = PO")
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C = PO \<Longrightarrow> \<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y"
        using assms(4) prod_O_l_eq prod_null by blast 
      show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C \<noteq> PO \<Longrightarrow> \<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y" 
      proof (cases "D = PO")
        show "A \<noteq> PO \<Longrightarrow> B \<noteq> PO \<Longrightarrow> C \<noteq> PO \<Longrightarrow> D = PO \<Longrightarrow> 
               \<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y"
          using assms(4) prod_O_r_eq prod_null by blast 
        {
          assume "A \<noteq> PO" and "B \<noteq> PO" and "C \<noteq> PO" and "D \<noteq> PO"
          obtain Bu where "B Bu Proj PO E' U E'" 
            by (metis Ar2_def Col_def Prod_def \<open>Prod PO E E' A B X\<close> assms(2,3) 
                col_transitivity_1 grid_not_par project_existence) 
          hence "B Bu Par U E'"
            by (metis Par_def Prodp_def Proj_def \<open>B \<noteq> PO\<close> \<open>Prod PO E E' A B X\<close> 
                not_col_distincts prod_to_prodp proj_id) 
          obtain Xu where "Bu Xu Proj PO E A E'"
            by (metis Prodp_def Proj_def \<open>Prod PO E E' A B X\<close> prod_to_prodp project_existence) 
          hence "Bu Xu Par A E'"
            by (metis Ar2_def Prod_def Proj_def \<open>B Bu Proj PO E' U E'\<close> \<open>B \<noteq> PO\<close> assms(2,3,4) 
                col_permutation_5 col_transitivity_1 proj_id) 
          have "Prod PO U E' A B Xu"
            by (smt (verit) Prodp_def Proj_def \<open>B Bu Proj PO E' U E'\<close> \<open>Bu Xu Proj PO E A E'\<close>
                assms(2,3,4) col2__eq col3 prod_to_prodp prodp_to_prod
                project_col_project) 
          moreover have "Prod PO U E' C D Xu" 
          proof -
            obtain Du where "D Du Proj PO E' U E'"
              using Proj_def \<open>B Bu Proj PO E' U E'\<close> project_existence by presburger
            hence "D Du Par U E'"
              by (metis Ar2_def Prod_def Proj_def \<open>Bu Xu Proj PO E A E'\<close> \<open>D \<noteq> PO\<close> assms(2,4)
                  calculation col_transitivity_1 proj_id)
            have "E' C Pj Du Xu" 
            proof -
              have "Prod PO C E' A B D"
                using \<open>C \<noteq> PO\<close> \<open>Prod PO E E' A B X\<close> \<open>Prod PO E E' C D X\<close> assms(1) l14_31_1 
                by blast
              obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' X"
                using Prod_def \<open>Prod PO E E' A B X\<close> by auto
              obtain D' where "E E' Pj D D'" and "Col PO E' D'" and "E' C Pj D' X"
                using Prod_def \<open>Prod PO E E' C D X\<close> by auto 
              obtain D'' where "C E' Pj B D''" and "Col PO E' D''" and "E' A Pj D'' D"
                using Prod_def \<open>Prod PO C E' A B D\<close> by blast
              have "Xu \<noteq> PO"
                using \<open>A \<noteq> PO\<close> \<open>B \<noteq> PO\<close> calculation prod_null by blast 
              have "D'' \<noteq> PO"
                by (metis Ar2_def Par_cases Par_def Pj_def Prod_def \<open>B \<noteq> PO\<close> \<open>C E' Pj B D''\<close>
                    \<open>Prod PO C E' A B D\<close> col_permutation_5 par_strict_not_col_1)
              have "Xu Du Par B D''" 
              proof (rule l13_11 [of PO _ _ _ D _ Bu], insert \<open>D \<noteq> PO\<close> \<open>B \<noteq> PO\<close>)
                show "\<not> Col PO Xu D''"
                  by (metis Proj_def \<open>B Bu Proj PO E' U E'\<close> \<open>Bu Xu Par A E'\<close> 
                      \<open>Bu Xu Proj PO E A E'\<close> \<open>Col PO E' D''\<close>
                      \<open>D'' \<noteq> PO\<close> \<open>Xu \<noteq> PO\<close> col_permutation_5 col_transitivity_1
                      par_distinct project_id) 
                show "Col PO Xu B"
                  by (metis Ar2_def Prod_def Proj_def \<open>Bu Xu Proj PO E A E'\<close> assms(4)
                      col_transitivity_1) 
                show "Col PO B D"
                  by (metis Ar2_def Prod_def Proj_def \<open>Bu Xu Proj PO E A E'\<close> assms(4)
                      col_transitivity_1) 
                show "Du \<noteq> PO"
                  by (metis Proj_def \<open>B Bu Proj PO E' U E'\<close> \<open>Bu Xu Proj PO E A E'\<close> \<open>Col PO B D\<close>
                      \<open>D Du Proj PO E' U E'\<close> \<open>D \<noteq> PO\<close> \<open>Xu \<noteq> PO\<close> col2__eq col_permutation_3
                      project_col_eq project_id) 
                show "Bu \<noteq> PO"
                  using \<open>Bu Xu Proj PO E A E'\<close> \<open>Xu \<noteq> PO\<close> not_col_distincts project_id
                  by blast
                show "Col PO D'' Du"
                  by (metis Proj_def \<open>Col PO E' D''\<close> \<open>D Du Proj PO E' U E'\<close> 
                      col3 not_col_distincts) 
                show "Col PO Du Bu"
                  by (metis Proj_def \<open>B Bu Proj PO E' U E'\<close> \<open>D Du Proj PO E' U E'\<close> l6_16_1
                      not_col_permutation_3 not_col_permutation_5) 
                show "B Bu Par D Du"
                  using \<open>B Bu Par U E'\<close> \<open>D Du Par U E'\<close> not_par_one_not_par by blast 
                show "D D'' Par Xu Bu"
                  by (metis Par_cases Pj_def \<open>B Bu Par D Du\<close> \<open>Bu Xu Par A E'\<close> \<open>Col PO E' D''\<close>
                      \<open>D Du Proj PO E' U E'\<close> \<open>E' A Pj D'' D\<close> par_distinct par_not_par
                      project_id) 
              qed
              thus ?thesis
                by (metis Par_cases Pj_def \<open>C E' Pj B D''\<close> par_neq2 par_trans) 
            qed
            moreover have "U E' Pj D Du"
              using \<open>D Du Proj PO E' U E'\<close> project_pj by auto 
            moreover have "Col PO E' Du"
              using Proj_def \<open>D Du Proj PO E' U E'\<close> by auto 
            moreover have "Ar2 PO U E' C D Xu"
              by (metis Ar2_def Prod_def Proj_def \<open>Bu Xu Proj PO E A E'\<close> \<open>Prod PO U E' A B Xu\<close>
                  assms(2,4) col_transitivity_1) 
            ultimately show ?thesis
              using Prod_def by blast 
          qed
          ultimately show "\<exists>Y. Prod PO U E' A B Y \<and> Prod PO U E' C D Y" 
            by blast
        }
      qed
    qed
  qed
qed

lemma opp_prod:
  assumes "Opp PO E E' E ME" 
    and "Opp PO E E' X MX"
  shows "Prod PO E E' X ME MX" 
proof -
  obtain EPME where "Sum PO E E' E ME EPME"
    using Opp_def assms(1) sum_opp by blast 
  hence "PO = EPME"
    by (meson Opp_def assms(1) sum_opp sum_stable) 
  obtain X' where "Prod PO E E' X E X'"
    by (meson Ar2_def Opp_def assms(2) prod_1_r sum_ar2)
  hence "X = X'"
    by (meson Ar2_def Prod_def prod_1_r prod_uniqueness)
  obtain O' where "Prod PO E E' X PO O'"
    by (meson Ar2_def Prodp_def \<open>Prod PO E E' X E X'\<close> \<open>Sum PO E E' E ME EPME\<close> prod_0_r
        prod_to_prodp sum_ar2)
  hence "PO = O'"
    using prod_O_r_eq by blast 
  obtain MX' where "Prod PO E E' X ME MX'"
    by (metis Ar2_def Prodp_def \<open>Prod PO E E' X E X'\<close> \<open>Sum PO E E' E ME EPME\<close>
        prod_exists prod_to_prodp sum_ar2) 
  hence "Sum PO E E' X MX' PO"
    using \<open>PO = EPME\<close> \<open>PO = O'\<close> \<open>Prod PO E E' X E X'\<close> \<open>Prod PO E E' X PO O'\<close>
      \<open>Sum PO E E' E ME EPME\<close> \<open>X = X'\<close> distr_l by blast 
  thus ?thesis
    by (metis \<open>Prod PO E E' X ME MX'\<close> assms(2) opp_uniqueness sum3_col sum3_exists
        sum_ar2 sum_opp) 
qed

lemma distr_l_diff:
  assumes "Diff PO E E' B C BMC"
    and "Prod PO E E' A B AB"
    and "Prod PO E E' A C AC"
    and "Prod PO E E' A BMC ABMC"
  shows "Diff PO E E' AB AC ABMC"
  by (meson assms(1,2,3,4) diff_sum distr_l sum_diff) 

lemma diff_of_squares:
  assumes "Prod PO E E' A A A2"
    and "Prod PO E E' B B B2"
    and "Diff PO E E' A2 B2 A2MB2"
    and "Sum PO E E' A B APB"
    and "Diff PO E E' A B AMB"
    and "Prod PO E E' APB AMB F"
  shows "A2MB2 = F" 
proof -
  obtain F1 where "Prod PO E E' A AMB F1"
    by (metis Ar2_def Prodp_def assms(4,6) prod_exists prod_to_prodp sum_ar2) 
  moreover obtain F2 where "Prod PO E E' B AMB F2"
    by (meson Ar2_def Prod_def assms(2,6) prod_exists) 
  ultimately obtain F' where "Sum PO E E' F1 F2 F'"
    using assms(4,6) distr_r by blast 
  hence "F = F'"
    using \<open>Prod PO E E' A AMB F1\<close> \<open>Prod PO E E' B AMB F2\<close> assms(4,6) distr_r sum_stable
    by blast
  obtain AB where "Prod PO E E' A B AB"
    by (meson Ar2_def assms(4) prod_exists sum_ar2)
  then obtain A2MAB where "Diff PO E E' A2 AB A2MAB"
    by (metis Ar2_def Prod_def assms(3) col_trivial_3 diff_ar2 sum_diff sum_A_exists) 
  hence "A2MAB = F1"
    using \<open>Prod PO E E' A AMB F1\<close> \<open>Prod PO E E' A B AB\<close> assms(1,5) diff_uniqueness
      distr_l_diff by blast
  obtain BA where "Prod PO E E' B A BA"
    using \<open>Prod PO E E' A B AB\<close> prod_sym by blast
  obtain BAMB2 where "Diff PO E E' BA B2 BAMB2"
    using Ar2_def Prod_def \<open>Prod PO E E' B A BA\<close> assms(2) diff_exists by presburger 
  hence "BAMB2 = F2"
    using \<open>Prod PO E E' B A BA\<close> \<open>Prod PO E E' B AMB F2\<close> assms(2,5) diff_uniqueness
      distr_l_diff by blast
  have "BA = AB"
    by (meson Ar2_def \<open>Prod PO E E' A B AB\<close> \<open>Prod PO E E' B A BA\<close> \<open>Sum PO E E' F1 F2 F'\<close>
        prod_sym prod_uniqueness sum_ar2) 
  thus ?thesis
    by (metis \<open>A2MAB = F1\<close> \<open>BAMB2 = F2\<close> \<open>Diff PO E E' A2 AB A2MAB\<close>
        \<open>Diff PO E E' BA B2 BAMB2\<close> \<open>F = F'\<close> \<open>Sum PO E E' F1 F2 F'\<close> assms(3) diff_stable
        sum_diff_diff_b) 
qed

lemma eq_squares_eq_or_opp:
  assumes "Prod PO E E' A A A2"
    and "Prod PO E E' B B A2"
  shows "A = B \<or> Opp PO E E' A B" 
proof -
  obtain O' where "Diff PO E E' A A O'"
    by (meson Ar2_def Prod_def assms(1) diff_null) 
  hence "PO = O'"
    by (metis Ar2_def Prod_def assms(1) diff_sum sum_B_null) 
  obtain APB where "Sum PO E E' A B APB"
    by (meson Ar2_def Prodp_def \<open>Diff PO E E' A A O'\<close> assms(2) diff_sum prod_to_prodp
        sum_ar2 sum_exists) 
  then obtain AMB where "Diff PO E E' A B AMB"
    by (meson Ar2_def diff_exists sum_ar2) 
  then obtain PO' where "Prod PO E E' APB AMB PO'"
    by (meson Ar2_def \<open>Sum PO E E' A B APB\<close> diff_ar2 prod_exists sum_ar2)
  hence "PO = PO'"
    using diff_of_squares [of PO E E' A A2 B A2 _ APB AMB] Ar2_def Prod_def 
      \<open>Diff PO E E' A B AMB\<close> \<open>Sum PO E E' A B APB\<close> assms(1,2)
      diff_null by force
  thus ?thesis
    using \<open>Diff PO E E' A B AMB\<close> \<open>Prod PO E E' APB AMB PO'\<close>
      \<open>Sum PO E E' A B APB\<close> diff_null_eq prod_null sum_opp
    by blast 
qed

lemma diff_2_prod:
  assumes "Opp PO E E' E ME"
    and "Diff PO E E' A B AMB"
    and "Diff PO E E' B A BMA"
  shows "Prod PO E E' AMB ME BMA"
  using assms(1,2,3) diff_opp opp_prod by blast 

lemma l14_36_a:
  assumes "Sum PO E E' A B C" and
    "PO Out A B" 
  shows "Bet PO A C" 
proof (cases "A = B")
  have "ParallelogramFlat PO A C B"
    by (metis assms(1,2) between_trivial diff_to_plg l6_6 sum_diff
        not_bet_and_out) 
  hence "Parallelogram PO A C B"
    by (simp add: Parallelogram_def) 
  show "A = B \<Longrightarrow> (PO \<midarrow> A \<midarrow> C)"
    by (metis Out_def ParallelogramFlat_def \<open>ParallelogramFlat PO A C B\<close>
        between_cong l6_4_2 plgf_permut) 
  show "A \<noteq> B \<Longrightarrow> (PO \<midarrow> A \<midarrow> C)"
    by (smt (z3) Ar2_def ParallelogramFlat_def \<open>ParallelogramFlat PO A C B\<close>
        assms(1,2) bet_cong_eq between_trivial2 col_cong2_bet2 l6_4_2 l6_6
        not_bet_and_out out_col outer_transitivity_between2 plgf_permut sum_ar2
        sum_cong2 third_point)
qed

lemma l14_36_b:
  assumes "Sum PO E E' A B C"
    and "PO Out A B"
  shows "PO \<noteq> A \<and> PO \<noteq> C \<and> A \<noteq> C"
  by (metis Ar2_def Out_def assms(1,2) between_equality_2 between_trivial2
      cong3_id l14_36_a out_col sum_ar2 sum_iff_cong_b) 

lemma pos_null_neg: 
  assumes "Opp PO E E' A MA"
  shows "Ps PO E A \<or> PO = A \<or> Ps PO E MA"
  by (metis Ar2_def Col_def Opp_def Ps_def assms between_trivial l14_36_b l6_3_2
      l6_4_2 sum_B_null sum_ar2) 

lemma sum_pos_pos:
  assumes "Ps PO E A"
    and "Ps PO E B"
    and "Sum PO E E' A B AB"
  shows "Ps PO E AB" 
proof -
  have "PO Out A B"
    using Out_cases Ps_def assms(1,2) l6_7 by presburger 
  hence "PO \<noteq> A \<and> PO \<noteq> AB \<and> A \<noteq> AB"
    using assms(3) l14_36_b by blast 
  thus ?thesis
    by (metis Out_def Ps_def \<open>PO Out A B\<close> assms(1,3) l14_36_a l6_7) 
qed

lemma prod_pos_pos:
  assumes "Ps PO E A"
    and "Ps PO E B"
    and "Prod PO E E' A B AB"
  shows "Ps PO E AB" 
proof -
  obtain B' where "E E' Pj B B'" and "Col PO E' B'" and "E' A Pj B' AB"
    using Prod_def assms(3) by auto 
  have "E' \<noteq> A"
    using Ar2_def Prod_def assms(3) by blast 
  have "\<not> Col PO E' A"
    by (metis Ar2_def Col_cases O_not_positive Prod_def assms(1,3) col_trivial_3 colx) 
  hence "\<not> PO E Par E' A"
    by (meson Par_def Prodp_def assms(3) par_strict_not_col_4 prod_to_prodp) 
  have "E E' Proj PO E' E E'"
    by (metis Ar2_def Prod_def Proj_def assms(3) grid_not_par par_reflexivity) 
  have "B B' Proj PO E' E E'"
    by (metis Proj_def \<open>Col PO E' B'\<close> \<open>E E' Pj B B'\<close> \<open>E E' Proj PO E' E E'\<close> not_col_permutation_4
        not_col_permutation_5 pj_col_project) 
  have "PO PO Proj PO E' E E'"
    by (metis Proj_def \<open>E E' Proj PO E' E E'\<close> not_col_distincts) 
  have "E' A Proj PO E E' A"
    by (metis Par_def Prodp_def Proj_def \<open>\<not> PO E Par E' A\<close> assms(3) not_col_distincts
        prod_to_prodp) 
  hence "B' AB Proj PO E E' A"
    using Ar2_def Pj_def Prod_def Proj_def \<open>E' A Pj B' AB\<close> assms(3) par_symmetry by metis
  hence "PO PO Proj PO E E' A"
    by (metis Proj_def not_col_distincts) 
  have "AB \<noteq> PO"
    using O_not_positive \<open>\<not> Col PO E' A\<close> assms(2,3) col_trivial_3 prod_null by blast 
  {
    assume "Bet PO B E"
    hence "Bet PO B' E'"
      using \<open>B B' Proj PO E' E E'\<close> \<open>E E' Proj PO E' E E'\<close> \<open>PO PO Proj PO E' E E'\<close> 
        project_preserves_bet by blast 
    hence "Bet PO AB A"
      using \<open>B' AB Proj PO E E' A\<close> \<open>E' A Proj PO E E' A\<close> \<open>PO PO Proj PO E E' A\<close>
        project_preserves_bet by blast 
    hence "Ps PO E AB"
      using Ps_def \<open>AB \<noteq> PO\<close> assms(1) bet_out l6_7 by blast 
  }
  moreover 
  {
    assume "Bet PO E B"
    hence "Bet PO E' B'"
      using \<open>B B' Proj PO E' E E'\<close> \<open>E E' Proj PO E' E E'\<close> \<open>PO PO Proj PO E' E E'\<close> 
        project_preserves_bet
      by blast 
    hence "Bet PO A AB"
      using \<open>B' AB Proj PO E E' A\<close> \<open>E' A Proj PO E E' A\<close> \<open>PO PO Proj PO E E' A\<close> 
        project_preserves_bet
      by blast 
    hence "Ps PO E AB"
      by (metis O_not_positive Out_cases Ps_def assms(1) bet_out l6_7) 
  }
  ultimately show ?thesis
    using Out_def Ps_def assms(2) by auto 
qed

lemma pos_not_neg:
  assumes "Ps PO E A"
  shows "\<not> Ng PO E A"
  by (metis Ng_def Ps_def assms not_bet_and_out) 

lemma neg_not_pos:
  assumes "Ng PO E A"
  shows "\<not> Ps PO E A"
  using assms pos_not_neg by blast 

lemma opp_pos_neg: 
  assumes "Ps PO E A"
    and "Opp PO E E' A MA"
  shows "Ng PO E MA"
  by (metis (full_types) Bet_cases Ng_def Out_def Ps_def assms(1,2) 
      bet_out__bet is_midpoint_id_2 midpoint_bet opp_midpoint) 

lemma opp_neg_pos:
  assumes "Ng PO E A"
    and "Opp PO E E' A MA"
  shows "Ps PO E MA"
  by (metis Ng_def assms(1,2) neg_not_pos pos_null_neg) 

lemma ltP_ar2:
  assumes "LtP PO E E' A B"
  shows "Ar2 PO E E' A B A"
  by (meson Ar2_def LtP_def assms diff_ar2) 

lemma ltP_neq:
  assumes "LtP PO E E' A B"
  shows "A \<noteq> B"
  using LtP_def assms diff_opp opp_pos_neg pos_not_neg by blast 

lemma leP_refl:
  shows "LeP PO E E' A A"
  using LeP_def by auto 

lemma ltP_sum_pos:
  assumes "Ps PO E B"
    and "Sum PO E E' A B C"
  shows "LtP PO E E' A C"
  using LtP_def assms(1,2) local.sum_diff by blast 

lemma pos_opp_neg:
  assumes "Ps PO E A"
    and "Opp PO E E' A mA"
  shows "Ng PO E mA"
  using assms(1,2) opp_pos_neg by auto

lemma diff_pos_diff_neg:
  assumes "Diff PO E E' A B AmB"
    and "Diff PO E E' B A BmA"
    and "Ps PO E AmB"
  shows "Ng PO E BmA"
  using assms(1,2,3) diff_opp pos_opp_neg by blast 

lemma not_pos_and_neg:
  shows "\<not>(Ps PO E A \<and> Ng PO E A)"
  using neg_not_pos by auto 

lemma leP_asym:
  assumes "LeP PO E E' A B" 
    and "LeP PO E E' B A"
  shows "A = B" 
proof -
  have "LtP PO E E' A B \<Longrightarrow> A = B"
    by (metis LeP_def LtP_def assms(2) diff_pos_diff_neg pos_not_neg) 
  moreover have "LtP PO E E' B A \<Longrightarrow> A = B"
    using LeP_def assms(1) calculation by auto 
  ultimately show ?thesis
    using LeP_def assms(1) by auto 
qed

lemma leP_trans:
  assumes "LeP PO E E' A B"
    and "LeP PO E E' B C"
  shows "LeP PO E E' A C" 
proof -
  {
    assume "LtP PO E E' A B"
    have "LeP PO E E' A C" 
    proof -
      {
        assume "LtP PO E E' B C"
        obtain dBA where "Diff PO E E' B A dBA" and "Ps PO E dBA"
          using LtP_def \<open>LtP PO E E' A B\<close> by auto
        obtain dCB where "Diff PO E E' C B dCB" and "Ps PO E dCB"
          using LtP_def \<open>LtP PO E E' B C\<close> by auto 
        have "Ar2 PO E E' B A dBA"
          by (simp add: \<open>Diff PO E E' B A dBA\<close> diff_ar2) 
        have "Ar2 PO E E' C B dCB"
          by (simp add: \<open>Diff PO E E' C B dCB\<close> diff_ar2) 
        then obtain dCA where "Sum PO E E' dBA dCB dCA"
          using Ar2_def \<open>Ar2 PO E E' B A dBA\<close> sum_exists by blast
        hence "LeP PO E E' A C"
          by (meson LeP_def \<open>Diff PO E E' B A dBA\<close> \<open>Diff PO E E' C B dCB\<close> \<open>Ps PO E dBA\<close>
              \<open>Ps PO E dCB\<close> diff_sum ltP_sum_pos sum_assoc_2 sum_pos_pos) 
      }
      moreover have "B = C \<Longrightarrow> LeP PO E E' A C" 
        using assms(1) by auto 
      ultimately show ?thesis
        using LeP_def assms(2) by auto 
    qed
  }
  moreover have "A = B \<Longrightarrow> LeP PO E E' A C"
    by (simp add: assms(2)) 
  ultimately show ?thesis
    using LeP_def assms(1) by blast 
qed

(* sum_preserves leP : a <= x /\ b <= y => a + b <= x + y *)

lemma leP_sum_leP:
  assumes "LeP PO E E' A X"
    and "LeP PO E E' B Y"
    and "Sum PO E E' A B C"
    and "Sum PO E E' X Y Z"
  shows "LeP PO E E' C Z" 
proof -
  have "Ar2 PO E E' A B C"
    by (simp add: assms(3) sum_ar2) 
  have "Ar2 PO E E' X Y Z"
    by (simp add: assms(4) sum_ar2) 
  {
    assume "LtP PO E E' A X"
    have "LeP PO E E' C Z" 
    proof -
      {
        assume "LtP PO E E' B Y"
        obtain dXA where "Diff PO E E' X A dXA"
          using LtP_def \<open>LtP PO E E' A X\<close> by auto 
        obtain dYB where "Diff PO E E' Y B dYB"
          using LtP_def \<open>LtP PO E E' B Y\<close> by auto 
        obtain dZC where "Diff PO E E' Z C dZC"
          using Ar2_def \<open>Ar2 PO E E' A B C\<close> \<open>Ar2 PO E E' X Y Z\<close> diff_exists
          by presburger  
        have "Ps PO E dZC" 
        proof -
          have "Sum PO E E' dXA dYB dZC"
            using \<open>Diff PO E E' X A dXA\<close> \<open>Diff PO E E' Y B dYB\<close> \<open>Diff PO E E' Z C dZC\<close>
              assms(3,4) sum_diff2_diff_sum2_b by blast 
          thus ?thesis
            by (metis LtP_def \<open>Diff PO E E' X A dXA\<close> \<open>Diff PO E E' Y B dYB\<close>
                \<open>LtP PO E E' A X\<close> \<open>LtP PO E E' B Y\<close> diff_uniqueness sum_pos_pos) 
        qed
        hence "LeP PO E E' C Z"
          using LeP_def LtP_def \<open>Diff PO E E' Z C dZC\<close> by blast 
      }
      moreover 
      {
        assume "B = Y"
        hence "LtP PO E E' C Z"
          by (smt (verit, best) Ar2_def LtP_def \<open>Ar2 PO E E' X Y Z\<close> \<open>LtP PO E E' A X\<close>
              assms(3,4) diff_sum local.sum_diff sum_assoc_1 sum_comm) 
        hence "LeP PO E E' C Z"
          by (simp add: LeP_def) 
      }
      ultimately show ?thesis
        using LeP_def assms(2) by auto 
    qed
  }
  moreover {
    assume "A = X"
    hence "LeP PO E E' C Z"
    proof -
      {
        assume "LtP PO E E' B Y"
        have "LtP PO E E' C Z"
          by (smt (z3) LtP_def \<open>A = X\<close> \<open>LtP PO E E' B Y\<close> assms(3,4) diff_sum
              local.sum_diff sum_assoc_1) 
      }
      hence "LtP PO E E' B Y \<Longrightarrow> LeP PO E E' C Z"
        by (simp add: LeP_def) 
      moreover have "B = Y \<Longrightarrow> LeP PO E E' C Z"
        using \<open>A = X\<close> assms(3,4) leP_refl sum_stable by blast 
      ultimately show ?thesis
        using LeP_def assms(2) by blast 
    qed
  }
  ultimately show ?thesis
    using LeP_def assms(1) by blast 
qed

lemma square_pos:
  assumes "PO \<noteq> A"
    and "Prod PO E E' A A A2"
  shows "Ps PO E A2" 
proof -
  have "\<not> Col PO E E'"
    using Ar2_def Prod_def assms(2) by blast 
  have "Col PO E A"
    using Ar2_def Prod_def assms(2) by force 
  then obtain MA where "Opp PO E E' A MA"
    using \<open>\<not> Col PO E E'\<close> opp_exists by blast 
  hence "Ps PO E A \<or> PO = A \<or> Ps PO E MA"
    by (simp add: pos_null_neg)
  moreover have "Ps PO E A \<Longrightarrow> Ps PO E A2"
    using assms(2) prod_pos_pos by blast 
  moreover have "PO = A \<Longrightarrow> Ps PO E A2"
    by (simp add: assms(1)) 
  moreover 
  {
    assume "Ps PO E MA"
    obtain ME where "Opp PO E E' E ME"
      using \<open>\<not> Col PO E E'\<close> col_trivial_2 opp_exists by blast 
    have "Prod PO E E' MA MA A2"
      by (meson \<open>Opp PO E E' A MA\<close> \<open>Opp PO E E' E ME\<close> \<open>\<not> Col PO E E'\<close> assms(2)
          opp_comm opp_prod prod_assoc prod_sym) 
    hence "Ps PO E A2"
      using \<open>Ps PO E MA\<close> prod_pos_pos by blast 
  }
  ultimately show ?thesis
    by blast 
qed

lemma ltP_neg:
  assumes "LtP PO E E' A PO"
  shows "Ng PO E A" 
proof -
  obtain MA where "Diff PO E E' PO A MA"
    using LtP_def assms by blast 
  hence "Opp PO E E' MA A"
    by (simp add: Opp_def diff_sum) 
  have "\<not> Col PO E E'"
    using Ar2_def assms ltP_ar2 by blast 
  thus ?thesis
    using LtP_def \<open>Diff PO E E' PO A MA\<close> \<open>Opp PO E E' MA A\<close> assms diff_uniqueness
      pos_opp_neg by blast 
qed

lemma ps_le:
  assumes "\<not> Col PO E E'"
    and "Bet PO X E \<or> Bet PO E X"
  shows "LeP PO E E' PO X" 
proof (cases "PO = X")
  show "PO = X \<Longrightarrow> LeP PO E E' PO X"
    by (simp add: leP_refl) 
  {
    assume "PO \<noteq> X"
    have "Diff PO E E' X PO X"
      using assms(1,2) bet_col diff_A_O not_col_permutation_5 by blast 
    moreover have "Ps PO E X"
      by (metis Bet_cases Col_def Ps_def \<open>PO \<noteq> X\<close> assms(1,2) between_equality_2
          col_trivial_1 or_bet_out) 
    ultimately show "LeP PO E E' PO X"
      using LeP_def LtP_def by auto 
  }
qed

lemma lt_diff_ps:
  assumes (*"Col PO E X"
and "Col PO E Y"
and*) "LtP PO E E' Y X"
    and "Diff PO E E' X Y XMY"
  shows "Ps PO E XMY"
  using LtP_def assms(1,2) diff_stable by blast 

lemma col_2_le_or_ge:
  assumes "\<not> Col PO E E'"
    and "Col PO E A"
    and "Col PO E B"
  shows "LeP PO E E' A B \<or> LeP PO E E' B A" 
proof (cases "A = B")
  have "PO \<noteq> E"
    using assms(1) col_trivial_1 by auto 
  show "A = B \<Longrightarrow> LeP PO E E' A B \<or> LeP PO E E' B A"
    by (simp add: leP_refl) 
  {
    assume "A \<noteq> B"
    obtain D where "Diff PO E E' B A D"
      using assms(1,2,3) diff_exists by blast
    hence "PO \<noteq> D"
      using \<open>A \<noteq> B\<close> diff_null_eq by blast 
    hence "Ps PO E D \<or> Ng PO E D"
      using Ar2_def \<open>Diff PO E E' B A D\<close> \<open>PO \<noteq> E\<close> col_pos_or_neg diff_ar2
      by presburger 
    moreover have "Ps PO E D \<Longrightarrow> LeP PO E E' A B"
      using LeP_def LtP_def \<open>Diff PO E E' B A D\<close> by blast 
    moreover 
    {
      assume "Ng PO E D"
      obtain MD where "Diff PO E E' A B MD"
        using assms(1,2,3) diff_exists by blast 
      hence "Opp PO E E' D MD"
        using \<open>Diff PO E E' B A D\<close> diff_opp by auto 
      hence "LeP PO E E' B A"
        using LeP_def LtP_def \<open>Diff PO E E' A B MD\<close> \<open>Ng PO E D\<close> opp_neg_pos
        by blast 
    }
    ultimately show "LeP PO E E' A B \<or> LeP PO E E' B A" 
      by blast
  }
qed

lemma compatibility_of_sum_with_order:
  assumes "LeP PO E E' A B"
    and "Sum PO E E' A C APC"
    and "Sum PO E E' B C BPC"
  shows "LeP PO E E' APC BPC"
  using assms(1,2,3) leP_refl leP_sum_leP by blast 

lemma compatibility_of_prod_with_order:
  assumes "LeP PO E E' PO A"
    and "LeP PO E E' PO B"
    and "Prod PO E E' A B AB"
  shows "LeP PO E E' PO AB" 
proof -
  have "PO = A \<Longrightarrow> ?thesis"
    using assms(3) leP_refl prod_O_l_eq by blast 
  moreover {
    assume "LtP PO E E' PO A"
    have "PO = B \<Longrightarrow> LeP PO E E' PO AB"
      using assms(3) leP_refl prod_O_r_eq by blast 
    moreover 
    {
      assume "LtP PO E E' PO B"
      have "Ps PO E AB"
        by (metis Ar2_def \<open>LtP PO E E' PO A\<close> \<open>LtP PO E E' PO B\<close> assms(3) diff_A_O
            ltP_ar2 lt_diff_ps prod_pos_pos) 
      hence "LeP PO E E' PO AB"
        by (metis Ar2_def LeP_def Prod_def assms(3) col_2_le_or_ge col_trivial_3
            ltP_neg pos_not_neg) 
    }
    ultimately have "LeP PO E E' PO AB"
      using LeP_def assms(2) by auto 
  } 
  ultimately show ?thesis
    using LeP_def assms(1) by blast 
qed

lemma pos_inv_pos:
  assumes "PO \<noteq> A"
    and "LeP PO E E' PO A"
    and "Prod PO E E' IA A E"
  shows "LeP PO E E' PO IA" 
proof -
  have "PO = A \<Longrightarrow> LeP PO E E' PO IA"
    by (simp add: assms(1)) 
  moreover 
  {
    assume "LtP PO E E' PO A"
    then obtain IA' where "Diff PO E E' IA PO IA'"
      by (meson Ar2_def Prodp_def assms(3) diff_A_O ltP_ar2 prod_to_prodp) 
    hence "IA = IA'"
      by (meson Ar2_def diff_A_O diff_ar2 diff_stable)
    obtain A' where "Diff PO E E' A PO A'" and "Ps PO E A'"
      using LtP_def \<open>LtP PO E E' PO A\<close> by blast 
    hence "A = A'"
      by (metis Ar2_def diff_ar2 diff_sum sum_O_B_eq) 
    obtain MIA where "Opp PO E E' IA MIA"
      by (metis Ar2_def \<open>Diff PO E E' IA PO IA'\<close> diff_ar2 opp_exists) 
    have "Ps PO E IA \<or> PO = IA \<or> Ps PO E MIA"
      using \<open>Opp PO E E' IA MIA\<close> pos_null_neg by auto
    moreover have "PO = IA \<Longrightarrow> LeP PO E E' PO IA"
      by (simp add: leP_refl) 
    moreover {
      assume "Ps PO E MIA"
      obtain ME where "Opp PO E E' E ME"
        by (meson Ar2_def \<open>Diff PO E E' A PO A'\<close> diff_ar2 not_col_distincts
            opp_exists)
      moreover have "Prod PO E E' IA ME MIA"
        by (simp add: \<open>Opp PO E E' IA MIA\<close> calculation opp_prod) 
      moreover have "Prod PO E E' MIA A ME"
        by (meson assms(3) calculation(1,2) opp_prod prod_assoc prod_sym) 
      ultimately have False
        by (metis Ar2_def Ng_def \<open>A = A'\<close> \<open>Diff PO E E' IA PO IA'\<close>
            \<open>Ps PO E A'\<close> \<open>Ps PO E MIA\<close> bet_neq12__neq diff_ar2
            opp_comm pos_opp_neg prod_pos_pos) 
    }
    moreover have "Ps PO E IA \<Longrightarrow> LeP PO E E' PO IA"
      using LeP_def LtP_def \<open>Diff PO E E' IA PO IA'\<close> \<open>IA = IA'\<close> by auto 
    ultimately have "LeP PO E E' PO IA" 
      by blast
  }
  ultimately show ?thesis
    using LeP_def assms(2) by auto 
qed

lemma le_pos_prod_le:
  assumes "LeP PO E E' A B"
    and "LeP PO E E' PO C"
    and "Prod PO E E' A C AC"
    and "Prod PO E E' B C BC"
  shows "LeP PO E E' AC BC" 
proof -
  obtain BCMAC where "Diff PO E E' BC AC BCMAC"
    using Ar2_def Prod_def assms(3,4) diff_exists by presburger 
  obtain BMA where "Diff PO E E' B A BMA"
    by (metis Ar2_def LeP_def LtP_def Prod_def assms(1,3) diff_null)
  then obtain BCMAC' where "Prod PO E E' BMA C BCMAC'"
    using Ar2_def Prodp_def assms(4) diff_ar2 prod_exists
      prod_to_prodp by presburger 
  hence "Diff PO E E' BC AC BCMAC'"
    using \<open>Diff PO E E' B A BMA\<close> assms(3,4) distr_l_diff prod_sym by blast 
  hence "BCMAC = BCMAC'"
    using \<open>Diff PO E E' BC AC BCMAC\<close> diff_uniqueness
    by auto 
  hence "LeP PO E E' PO BCMAC"
    by (metis Ar2_def LeP_def Out_def Ps_def
        \<open>Diff PO E E' B A BMA\<close> \<open>Prod PO E E' BMA C BCMAC'\<close> assms(1,2)
        compatibility_of_prod_with_order cong_identity_inv diff_ar2 diff_sum
        lt_diff_ps ps_le sum_iff_cong_b) 
  thus ?thesis
    by (metis Ar2_def LeP_def LtP_def \<open>Diff PO E E' BC AC BCMAC\<close> diff_A_O
        diff_null_eq ltP_ar2 lt_diff_ps) 
qed

lemma bet_lt12_le23:
  assumes "Bet A B C"
    and "LtP PO E E' A B"
  shows "LeP PO E E' B C" 
proof (cases "B = C")
  show "B = C \<Longrightarrow> LeP PO E E' B C"
    by (simp add: leP_refl) 
  {
    assume "B \<noteq> C"
    have "A \<noteq> B"
      using assms(2) ltP_neq by auto 
    have "Col PO E A"
      using Ar2_def assms(2) ltP_ar2 by blast 
    have "Col PO E B"
      using Ar2_def assms(2) ltP_ar2 by blast 
    then obtain CMB where "Diff PO E E' C B CMB" 
      using diff_exists by (metis Ar2_def Col_def \<open>A \<noteq> B\<close> assms(1,2) col_transitivity_1
          col_trivial_1 ltP_ar2) 
    show "LeP PO E E' B C" 
    proof (cases "PO = A")
      show "PO = A \<Longrightarrow> LeP PO E E' B C" 
      proof (cases "PO = B")
        show "PO = A \<Longrightarrow> PO = B \<Longrightarrow> LeP PO E E' B C"
          using \<open>A \<noteq> B\<close> by fastforce 
        show "PO = A \<Longrightarrow> PO \<noteq> B \<Longrightarrow> LeP PO E E' B C" 
        proof (cases "PO = C")
          show "PO = A \<Longrightarrow> PO \<noteq> B \<Longrightarrow> PO = C \<Longrightarrow> LeP PO E E' B C"
            using assms(1) bet_neq12__neq by auto 
          {
            assume "PO = A" and "PO \<noteq> B" and "PO \<noteq> C"
            obtain B' where "Diff PO E E' B PO B'" and "Ps PO E B'"
              using LtP_def \<open>PO = A\<close> assms(2) by auto
            hence "B = B'"
              by (metis Ar2_def diff_ar2 diff_sum sum_O_B_eq)
            have "E \<noteq> PO"
              using Ar2_def \<open>Diff PO E E' B PO B'\<close> col_trivial_1 diff_ar2 by blast 
            moreover 
            have "ParallelogramFlat PO B C CMB"
              using \<open>Diff PO E E' C B CMB\<close> \<open>PO \<noteq> C\<close> diff_to_plg by force 
            hence "Bet CMB C PO \<and> Bet C PO B \<or> Bet CMB PO C \<and> Bet PO C B \<or> 
                   Bet PO CMB B \<and> Bet CMB B C \<or> Bet PO B CMB \<and> Bet B CMB C"
              by (simp add: plgf_bet) 
            moreover have "Bet CMB C PO \<and> Bet C PO B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
              using Bet_cases \<open>PO = A\<close> \<open>PO \<noteq> B\<close> assms(1) between_equality_2
              by blast 
            moreover have "Bet CMB PO C \<and> Bet PO C B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
              using \<open>B \<noteq> C\<close> \<open>PO = A\<close> assms(1) between_equality_2 by auto 
            moreover have "Bet PO CMB B \<and> Bet CMB B C \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
              by (metis Ar2_def Bet_cases Ps_def \<open>B = B'\<close> \<open>Diff PO E E' C B CMB\<close>
                  \<open>Ps PO E B'\<close> bet_out__bet between_equality_2 diff_sum l6_6 sum_ar2
                  third_point) 
            moreover have "Bet PO B CMB \<and> Bet B CMB C \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
              by (metis Bet_cases Col_def Ng_def \<open>B = B'\<close> \<open>Col PO E B\<close> \<open>PO \<noteq> B\<close>
                  \<open>Ps PO E B'\<close> between_inner_transitivity col2__eq col_permutation_4
                  pos_not_neg) 
            ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
              by blast 
            have "E \<noteq> PO \<and> (Bet PO CMB E \<or> Bet PO E CMB)"
              by (simp add: \<open>E \<noteq> PO\<close> \<open>(PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close>)
            hence "Ps PO E CMB"
              by (metis Out_cases Ps_def \<open>B \<noteq> C\<close> \<open>Diff PO E E' C B CMB\<close> bet_out_1
                  between_symmetry diff_null_eq) 
            thus "LeP PO E E' B C"
              using LeP_def LtP_def \<open>Diff PO E E' C B CMB\<close> by blast 
          }
        qed
      qed
      show "PO \<noteq> A \<Longrightarrow> LeP PO E E' B C" 
      proof (cases "PO = B")
        show "PO \<noteq> A \<Longrightarrow> PO = B \<Longrightarrow> LeP PO E E' B C"
          by (metis Ar2_def Ng_def assms(1,2) l5_2 ltP_ar2 ltP_neg ps_le) 
        show "PO \<noteq> A \<Longrightarrow> PO \<noteq> B \<Longrightarrow> LeP PO E E' B C" 
        proof (cases "PO = C")
          {
            assume "PO \<noteq> A" and "PO \<noteq> B" and "PO = C"
            have "Ps PO E B \<or> Ng PO E B"
              using LtP_def \<open>Diff PO E E' C B CMB\<close> \<open>PO = C\<close> \<open>PO \<noteq> B\<close> diff_O_A_opp ltP_neg
                pos_null_neg by blast 
            {
              assume "Ps PO E B"
              have "Ps PO E A \<or> Ng PO E A"
                by (metis NCol_cases Ng_def Ps_def \<open>Col PO E A\<close> \<open>PO \<noteq> A\<close> \<open>Ps PO E B\<close>
                    or_bet_out out_distinct)
              moreover {
                assume "Ps PO E A"
                obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                  using LtP_def assms(2) diff_sum by blast 
                have "False" 
                proof (cases "A = BMA")
                  show "A = BMA \<Longrightarrow> False"
                    by (metis Bet_cases \<open>A \<noteq> B\<close> \<open>PO = C\<close> \<open>Sum PO E E' A BMA B\<close> assms(1) bet_out
                        between_equality_2 between_trivial l14_36_a) 
                  {
                    assume "A \<noteq> BMA"
                    hence "ParallelogramFlat PO A B BMA"
                      by (metis Ar2_def \<open>Sum PO E E' A BMA B\<close> sum_ar2 sum_cong) 
                    hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or> 
                           Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B" 
                      using plgf_bet by simp 
                    moreover have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> False"
                      using Bet_cases \<open>PO = C\<close> \<open>PO \<noteq> B\<close> assms(1) between_equality
                      by blast 
                    moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> False"
                      by (meson Ps_def \<open>Ps PO E BMA\<close> \<open>Ps PO E B\<close> bet_out__bet l6_6
                          not_bet_and_out) 
                    moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> False"
                      by (metis Bet_cases \<open>A \<noteq> BMA\<close> \<open>A \<noteq> B\<close> \<open>PO = C\<close> assms(1) between_equality_2
                          outer_transitivity_between2) 
                    moreover have " Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> False"
                      by (metis Bet_cases \<open>A \<noteq> BMA\<close> \<open>PO = C\<close> assms(1) between_equality_2
                          outer_transitivity_between) 
                    ultimately show False 
                      by blast
                  }
                qed
              }
              moreover have "Ng PO E A \<Longrightarrow> False"
                by (metis Ng_def \<open>PO = C\<close> \<open>PO \<noteq> B\<close> \<open>Ps PO E B\<close> assms(1) between_exchange3
                    pos_not_neg) 
              ultimately have "False"
                by auto 
            }
            hence "Ng PO E B"
              using \<open>Ps PO E B \<or> Ng PO E B\<close> by auto 
            thus "LeP PO E E' B C"
              by (metis LeP_def LtP_def \<open>Diff PO E E' C B CMB\<close> \<open>PO = C\<close> diff_O_A_opp
                  opp_neg_pos) 
          }
          {
            assume "PO \<noteq> A" and "PO \<noteq> B" and "PO \<noteq> C"
            have "Sum PO E E' B CMB C"
              by (simp add: \<open>Diff PO E E' C B CMB\<close> diff_sum) 
            have "ParallelogramFlat PO B C CMB"
              using \<open>Diff PO E E' C B CMB\<close> \<open>PO \<noteq> C\<close> diff_to_plg by presburger 
            hence "Bet CMB C PO \<and> Bet C PO B \<or> Bet CMB PO C \<and> Bet PO C B \<or> 
                   Bet PO CMB B \<and> Bet CMB B C \<or> Bet PO B CMB \<and> Bet B CMB C" 
              using  plgf_bet by simp 
            have "E \<noteq> PO"
              using Ar2_def \<open>Diff PO E E' C B CMB\<close> col_trivial_1 diff_ar2 by blast 
            moreover have "Bet PO CMB E \<or> Bet PO E CMB" 
            proof -
              have "Ps PO E A \<or> Ng PO E A"
                using \<open>Col PO E A\<close> \<open>PO \<noteq> A\<close> calculation col_pos_or_neg by auto 
              moreover have "Ps PO E B \<or> Ng PO E B"
                using \<open>Col PO E B\<close> \<open>E \<noteq> PO\<close> \<open>PO \<noteq> B\<close> col_pos_or_neg by auto
              moreover 
              {
                assume "Ps PO E A" and "Ps PO E B"
                hence "Bet PO A E \<or> Bet PO E A"
                  by (metis Ng_def \<open>Col PO E A\<close> \<open>E \<noteq> PO\<close> pos_not_neg third_point) 
                have "Bet PO B E \<or> Bet PO E B"
                  by (metis Bet_cases Col_def Ng_def \<open>Col PO E B\<close> \<open>Ps PO E B\<close> pos_not_neg) 
                {
                  assume "Bet CMB C PO \<and> Bet C PO B" 
                  {
                    assume "Ps PO E A"
                    {
                      assume "Bet PO A E"
                      {
                        assume "Bet PO B E"
                        hence "Bet PO A B \<or> Bet PO B A"
                          using \<open>PO \<midarrow> A \<midarrow> E\<close> l5_3 by auto 
                        moreover {
                          assume "Bet PO A B \<or> Bet PO B A"
                          moreover have "Bet PO A B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                            by (metis Bet_cases \<open>A \<noteq> B\<close> \<open>(CMB \<midarrow> C \<midarrow> PO) \<and> (C \<midarrow> PO \<midarrow> B)\<close> 
                                assms(1) between_equality_2 between_exchange2) 
                          moreover {
                            assume "Bet PO B A"
                            obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                              using LtP_def assms(2) diff_sum by blast 
                            have "Bet PO CMB E \<or> Bet PO E CMB" 
                            proof (cases "A = BMA")
                              show "A = BMA \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                                by (metis \<open>Sum PO E E' A BMA B\<close> bet_out_1 between_trivial2 
                                    calculation(2) l14_36_a) 
                              have "ParallelogramFlat PO A B BMA"
                                by (metis \<open>PO \<noteq> A\<close> \<open>Sum PO E E' A BMA B\<close> 
                                    diff_to_plg local.sum_diff) 
                              hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or> 
                                     Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B"
                                by (simp add: plgf_bet) 
                              {
                                assume "A \<noteq> BMA"
                                have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> 
                                       (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                                  using \<open>PO \<midarrow> B \<midarrow> A\<close> \<open>PO \<noteq> B\<close> between_equality by auto 
                                moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> 
                                                (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                                  by (meson Bet_cases Ps_def \<open>Ps PO E BMA\<close> \<open>Ps PO E B\<close> 
                                      bet_out__bet not_bet_and_out) 
                                moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> 
                                                (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                                  using \<open>A \<noteq> BMA\<close> 
                                    \<open>(PO \<midarrow> A \<midarrow> B) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close>
                                    outer_transitivity_between2 by blast 
                                moreover have "Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> 
                                                (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                                  using \<open>A \<noteq> BMA\<close> 
                                    \<open>(PO \<midarrow> A \<midarrow> B) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                                    outer_transitivity_between by blast 
                                ultimately show "(PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                                  using \<open>Bet BMA B PO \<and> Bet B PO A \<or> 
                                         Bet BMA PO B \<and> Bet PO B A \<or> 
                                         Bet PO BMA A \<and> Bet BMA A B \<or> 
                                         Bet PO A BMA \<and> Bet A BMA B\<close> by blast 
                              }
                            qed
                          }
                          ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                            by auto 
                        }
                        ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                          by simp 
                      }
                      moreover have "Bet PO E B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                        by (metis Bet_cases \<open>(CMB \<midarrow> C \<midarrow> PO) \<and> (C \<midarrow> PO \<midarrow> B)\<close> 
                            \<open>PO \<midarrow> A \<midarrow> E\<close> assms(1) between_exchange3 calculation) 
                      ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                        using \<open>(PO \<midarrow> B \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> B)\<close> by blast 
                    }
                    moreover {
                      assume "Bet PO E A"
                      hence "Bet PO A B \<or> Bet PO B A"
                        by (metis \<open>E \<noteq> PO\<close> \<open>(PO \<midarrow> B \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> B)\<close> 
                            between_exchange4 l5_1)
                      moreover have "Bet PO A B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                        by (meson \<open>A \<noteq> B\<close> \<open>(CMB \<midarrow> C \<midarrow> PO) \<and> (C \<midarrow> PO \<midarrow> B)\<close> \<open>PO \<noteq> B\<close>
                            assms(1) between_equality between_symmetry
                            outer_transitivity_between2) 
                      moreover {
                        assume "Bet PO B A"
                        obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                          using LtP_def assms(2) diff_sum by blast 
                        have "Bet PO CMB E \<or> Bet PO E CMB" 
                        proof (cases "A = BMA")
                          show "A = BMA \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                            by (metis \<open>Sum PO E E' A BMA B\<close> bet_out_1 between_trivial2 
                                calculation(2) l14_36_a) 
                          {
                            assume "A \<noteq> BMA"
                            have "ParallelogramFlat PO A B BMA"
                              by (metis \<open>PO \<noteq> A\<close> \<open>Sum PO E E' A BMA B\<close> diff_to_plg 
                                  local.sum_diff) 
                            hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or> 
                                   Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B"
                              by (simp add: plgf_bet) 
                            moreover have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> 
                                            (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                              using \<open>PO \<midarrow> B \<midarrow> A\<close> \<open>PO \<noteq> B\<close> between_equality by auto 
                            moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> 
                                            (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                              using Out_cases Ps_def \<open>Ps PO E BMA\<close> \<open>Ps PO E B\<close> 
                                bet_out__bet not_bet_and_out by blast
                            moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> 
                                            (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                              using \<open>A \<noteq> BMA\<close> 
                                \<open>(PO \<midarrow> A \<midarrow> B) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                                outer_transitivity_between2 by blast
                            moreover have "Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> 
                                            (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                              using \<open>A \<noteq> BMA\<close> 
                                \<open>(PO \<midarrow> A \<midarrow> B) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close>
                                outer_transitivity_between by blast
                            ultimately show "(PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                              by blast 
                          }
                        qed
                      }
                      ultimately have "Bet PO CMB E \<or> Bet PO E CMB" 
                        by blast
                    }
                    ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                      using \<open>(PO \<midarrow> A \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> A)\<close> by blast 
                  }
                  moreover have "Ng PO E A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                    by (simp add: \<open>Ps PO E A\<close> calculation) 
                  ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                    by (simp add: \<open>Ps PO E A\<close>) 
                }
                moreover {
                  assume "Bet CMB PO C"  and "Bet PO C B"
                  {
                    assume "Bet PO A E" and "Bet PO B E"
                    have "Bet PO A B \<or> Bet PO B A"
                      using \<open>PO \<midarrow> A \<midarrow> E\<close> \<open>PO \<midarrow> B \<midarrow> E\<close> l5_3 by auto 
                    moreover have "Bet PO A B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                      using \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>PO \<midarrow> C \<midarrow> B\<close> assms(1) between_equality_2 
                        outer_transitivity_between2
                      by blast 
                    moreover {
                      assume "Bet PO B A"
                      obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                        using LtP_def assms(2) diff_sum by blast 
                      have "Bet PO CMB E \<or> Bet PO E CMB" 
                      proof (cases "A = BMA")
                        show "A = BMA \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                          using \<open>PO \<noteq> A\<close> \<open>Sum PO E E' A BMA B\<close> bet_out between_trivial 
                            calculation(2) l14_36_a
                          by auto 
                        {
                          assume "A \<noteq> BMA"
                          have "ParallelogramFlat PO A B BMA"
                            by (metis \<open>PO \<noteq> A\<close> \<open>Sum PO E E' A BMA B\<close> 
                                diff_to_plg local.sum_diff) 
                          hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or> 
                                 Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B"
                            using plgf_bet by blast
                          moreover have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> 
                                          Bet PO CMB E \<or> Bet PO E CMB"
                            using \<open>PO \<midarrow> B \<midarrow> A\<close> \<open>PO \<noteq> B\<close> between_equality by auto 
                          moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> 
                                          Bet PO CMB E \<or> Bet PO E CMB"
                            using Ps_def \<open>PO \<midarrow> B \<midarrow> E\<close> \<open>PO \<noteq> B\<close> \<open>Ps PO E BMA\<close> 
                              not_bet_and_out outer_transitivity_between by blast 
                          moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> 
                                          Bet PO CMB E \<or> Bet PO E CMB"
                            using \<open>A \<noteq> BMA\<close> \<open>(PO \<midarrow> A \<midarrow> B) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                              outer_transitivity_between2 by blast 
                          moreover have "Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> 
                                          Bet PO CMB E \<or> Bet PO E CMB"
                            using \<open>A \<noteq> BMA\<close> \<open>(PO \<midarrow> A \<midarrow> B) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                              outer_transitivity_between by blast 
                          ultimately show "(PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)" 
                            by blast
                        }
                      qed
                    }
                    ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                      by blast 
                  }
                  moreover have "Bet PO A E \<and> Bet PO E B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                    by (metis Bet_cases \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>PO \<midarrow> C \<midarrow> B\<close> assms(1) 
                        between_equality between_exchange2 outer_transitivity_between) 
                  moreover {
                    assume "Bet PO E A" and "Bet PO B E"
                    obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                      using LtP_def assms(2) diff_sum by blast 
                    have "Bet PO CMB E \<or> Bet PO E CMB" 
                    proof (cases "A = BMA")
                      show "A = BMA \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                        by (metis \<open>A \<noteq> B\<close> \<open>PO \<midarrow> B \<midarrow> E\<close> \<open>PO \<midarrow> E \<midarrow> A\<close> \<open>Sum PO E E' A BMA B\<close> 
                            bet_out_1 between_equality_2 between_exchange4 
                            between_trivial2 l14_36_a) 
                      {
                        assume "A \<noteq> BMA"
                        have "ParallelogramFlat PO A B BMA"
                          by (metis \<open>PO \<noteq> A\<close> \<open>Sum PO E E' A BMA B\<close> diff_to_plg local.sum_diff) 
                        hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or> 
                               Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B" 
                          using plgf_bet by blast
                        moreover have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          using \<open>PO \<midarrow> B \<midarrow> E\<close> \<open>PO \<midarrow> E \<midarrow> A\<close> \<open>PO \<noteq> B\<close> between_equality 
                            between_inner_transitivity by blast 
                        moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (metis Bet_cases Ng_def O_not_positive \<open>E \<noteq> PO\<close> \<open>PO \<midarrow> B \<midarrow> E\<close> 
                              \<open>PO \<noteq> B\<close> \<open>Ps PO E BMA\<close>
                              neg_not_pos outer_transitivity_between2) 
                        moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          using \<open>A \<noteq> BMA\<close> 
                            \<open>(PO \<midarrow> A \<midarrow> E) \<Longrightarrow> (PO \<midarrow> B \<midarrow> E) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                            \<open>PO \<midarrow> B \<midarrow> E\<close> between_exchange4 outer_transitivity_between2 by blast 
                        moreover have "Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          using \<open>A \<noteq> BMA\<close> 
                            \<open>(PO \<midarrow> A \<midarrow> E) \<Longrightarrow> (PO \<midarrow> B \<midarrow> E) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                            \<open>PO \<midarrow> B \<midarrow> E\<close>
                            between_exchange4 outer_transitivity_between2 by blast 
                        ultimately show "(PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)" 
                          by blast
                      }
                    qed
                  }
                  moreover {
                    assume "Bet PO E A" and "Bet PO E B"
                    obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                      by (meson LtP_def assms(2) diff_sum) 
                    have "Bet PO CMB E \<or> Bet PO E CMB" 
                    proof (cases "A = BMA")
                      show "A = BMA \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                        by (metis \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>PO \<midarrow> C \<midarrow> B\<close> \<open>Sum PO E E' A BMA B\<close> 
                            assms(1) bet_out between_equality_2
                            between_exchange2 between_trivial l14_36_a outer_transitivity_between) 
                      {
                        assume "A \<noteq> BMA"
                        have "ParallelogramFlat PO A B BMA"
                          by (metis \<open>PO \<noteq> A\<close> \<open>Sum PO E E' A BMA B\<close> diff_to_plg local.sum_diff)
                        hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or> 
                               Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B" 
                          using plgf_bet by blast
                        moreover have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (meson Bet_cases \<open>B \<noteq> C\<close> \<open>PO \<midarrow> C \<midarrow> B\<close> assms(1) 
                              between_equality_2 between_exchange3) 
                        moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (metis Bet_cases Ps_def \<open>PO \<midarrow> E \<midarrow> B\<close> \<open>Ps PO E BMA\<close> 
                              between_exchange3 not_bet_and_out) 
                        moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (metis \<open>A \<noteq> BMA\<close> \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>PO \<midarrow> C \<midarrow> B\<close> assms(1) 
                              between_equality_2 outer_transitivity_between2) 
                        moreover have "Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (metis \<open>A \<noteq> BMA\<close> \<open>B \<noteq> C\<close> \<open>PO \<midarrow> C \<midarrow> B\<close> assms(1) 
                              between_equality_2 between_exchange3 outer_transitivity_between2) 
                        ultimately show "(PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)" 
                          by blast
                      }
                    qed
                  }
                  ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                    using \<open>(PO \<midarrow> A \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> A)\<close> \<open>(PO \<midarrow> B \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> B)\<close> by auto 
                }
                moreover have "Bet PO CMB B \<and> Bet CMB B C \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  by (meson \<open>(PO \<midarrow> B \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> B)\<close> between_exchange4 l5_3) 
                moreover have "Bet PO B CMB \<and> Bet B CMB C \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  using \<open>(PO \<midarrow> B \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> B)\<close> \<open>PO \<noteq> B\<close> between_exchange4 l5_1 by blast 
                ultimately have "Bet PO CMB E \<or> Bet PO E CMB" 
                  using \<open>Bet CMB C PO \<and> Bet C PO B \<or> Bet CMB PO C \<and> Bet PO C B \<or> 
                         Bet PO CMB B \<and> Bet CMB B C \<or> Bet PO B CMB \<and> Bet B CMB C\<close> by blast
              }
              moreover have "Ps PO E A \<and> Ng PO E B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                using LtP_def assms(2) calculation(3) diff_sum sum_pos_pos by blast  
              moreover {
                assume "Ng PO E A" and "Ps PO E B"
                have "Bet CMB C PO \<and> Bet C PO B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  by (meson Bet_cases Ng_def Out_cases Ps_def \<open>Ng PO E A\<close> \<open>PO \<noteq> B\<close> \<open>Ps PO E B\<close> 
                      assms(1)
                      bet_out__bet between_equality between_inner_transitivity) 
                moreover have "Bet CMB PO C \<and> Bet PO C B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  by (smt (verit, ccfv_threshold) Bet_cases Ng_def \<open>B \<noteq> C\<close> \<open>Ng PO E A\<close> \<open>PO \<noteq> B\<close> 
                      \<open>Ps PO E B\<close>
                      assms(1) between_inner_transitivity outer_transitivity_between2 pos_not_neg)
                moreover have "Bet PO CMB B \<and> Bet CMB B C \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  by (meson Bet_cases Col_def Ps_def \<open>Col PO E B\<close> \<open>Ps PO E B\<close> between_exchange2 
                      l5_3 not_bet_and_out) 
                moreover have "Bet PO B CMB \<and> Bet B CMB C \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  by (meson Ar2_def Bet_cases Ps_def \<open>Ps PO E B\<close> \<open>Sum PO E E' B CMB C\<close> 
                      between_inner_transitivity
                      not_bet_and_out sum_ar2 third_point) 
                ultimately have "Bet PO CMB E \<or> Bet PO E CMB" 
                  using \<open>Bet CMB C PO \<and> Bet C PO B \<or> Bet CMB PO C \<and> Bet PO C B \<or> 
                         Bet PO CMB B \<and> Bet CMB B C \<or> Bet PO B CMB \<and> Bet B CMB C\<close>
                  by blast
              }
              moreover 
              {
                assume "Ng PO E A" and "Ng PO E B"
                have "Bet CMB C PO \<and> Bet C PO B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  by (metis Ng_def \<open>Ng PO E B\<close> \<open>PO \<noteq> C\<close> between_symmetry l5_2 
                      outer_transitivity_between2)
                moreover have "Bet CMB PO C \<and> Bet PO C B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                  by (smt (verit, ccfv_SIG) Bet_cases Col_def Ng_def \<open>Ng PO E B\<close> \<open>PO \<noteq> C\<close>
                      between_equality_2 between_inner_transitivity l6_16_1) 
                moreover {
                  assume "Bet PO CMB B" and "Bet CMB B C"
                  {
                    assume "Bet A PO E"
                    {
                      assume "Bet B PO E"
                      have "Bet PO A B \<or> Bet PO B A"
                        by (meson \<open>A \<midarrow> PO \<midarrow> E\<close> \<open>B \<midarrow> PO \<midarrow> E\<close> \<open>E \<noteq> PO\<close> between_symmetry l5_2) 
                      moreover {
                        assume "Bet PO A B"
                        obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                          using LtP_def assms(2) diff_sum by blast 
                        hence "ParallelogramFlat PO A B BMA"
                          by (metis \<open>PO \<noteq> A\<close> diff_to_plg local.sum_diff) 
                        hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or>
                                Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B" 
                          using plgf_bet by blast
                        have "Bet PO CMB E \<or> Bet PO E CMB" 
                        proof (cases "A = BMA")
                          show "A = BMA \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                            using \<open>Ng PO E B\<close> 
                              \<open>Ps PO E A \<and> Ng PO E B \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close>
                              \<open>Ps PO E BMA\<close> by auto 
                          {
                            assume "A \<noteq> BMA"
                            have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                              using Bet_cases \<open>PO \<midarrow> A \<midarrow> B\<close> \<open>PO \<noteq> A\<close> between_equality by blast 
                            moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> 
                                            Bet PO CMB E \<or> Bet PO E CMB"
                              using \<open>A \<noteq> B\<close> \<open>PO \<midarrow> A \<midarrow> B\<close> between_equality_2 by auto 
                            moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> 
                                            Bet PO CMB E \<or> Bet PO E CMB"
                              using Bet_cases Ps_def \<open>A \<midarrow> PO \<midarrow> E\<close> \<open>Ps PO E BMA\<close> 
                                between_exchange3 not_bet_and_out by blast 
                            moreover have "Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> 
                                            Bet PO CMB E \<or> Bet PO E CMB"
                              by (metis Bet_cases Ng_def \<open>A \<midarrow> PO \<midarrow> E\<close> \<open>E \<noteq> PO\<close> \<open>PO \<noteq> A\<close>
                                  \<open>Ps PO E BMA\<close> between_equality neg_not_pos 
                                  outer_transitivity_between2) 
                            ultimately show "(PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)" 
                              using \<open>Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or>
                                     Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B\<close>
                              by blast
                          }
                        qed
                      }
                      moreover {
                        assume "Bet PO B A"
                        have "Bet PO B C"
                          by (metis Out_def \<open>CMB \<midarrow> B \<midarrow> C\<close> \<open>PO \<midarrow> CMB \<midarrow> B\<close> \<open>PO \<noteq> B\<close> 
                              \<open>Sum PO E E' B CMB C\<close> l14_36_a)
                        have "Bet B A C \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          using \<open>A \<noteq> B\<close> assms(1) between_equality by blast 
                        hence "Bet PO CMB E \<or> Bet PO E CMB"
                          by (meson Bet_cases \<open>B \<noteq> C\<close> \<open>PO \<midarrow> B \<midarrow> A\<close> \<open>PO \<midarrow> B \<midarrow> C\<close> \<open>PO \<noteq> B\<close> 
                              assms(1) between_equality l5_2) 
                      }
                      ultimately have "Bet PO CMB E \<or> Bet PO E CMB" 
                        by blast
                    }
                    hence "Bet PO CMB E \<or> Bet PO E CMB"
                      using Ng_def \<open>Ng PO E B\<close> by blast 
                  }
                  hence "Bet PO CMB E \<or> Bet PO E CMB"
                    using Ng_def \<open>Ng PO E A\<close> by auto 
                }
                moreover {
                  assume "Bet PO B CMB" and "Bet B CMB C"
                  {
                    assume "Bet A PO E"
                    {
                      assume "Bet B PO E"
                      obtain BMA where "Sum PO E E' A BMA B" and "Ps PO E BMA"
                        using LtP_def assms(2) diff_sum by blast 
                      hence "ParallelogramFlat PO A B BMA"
                        by (metis \<open>PO \<noteq> A\<close> diff_to_plg local.sum_diff) 
                      hence "Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or>
                             Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B" 
                        using plgf_bet by blast
                      {
                        assume "Bet PO A B"
                        have "Bet BMA B PO \<and> Bet B PO A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (meson Bet_cases \<open>PO \<midarrow> A \<midarrow> B\<close> \<open>PO \<noteq> A\<close> between_equality) 
                        moreover have "Bet BMA PO B \<and> Bet PO B A \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          using \<open>A \<noteq> B\<close> \<open>PO \<midarrow> A \<midarrow> B\<close> between_equality_2 by auto 
                        moreover have "Bet PO BMA A \<and> Bet BMA A B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (metis Bet_cases Ng_def O_not_positive \<open>A \<midarrow> PO \<midarrow> E\<close> \<open>E \<noteq> PO\<close> 
                              \<open>Ps PO E BMA\<close> between_exchange3 pos_not_neg) 
                        moreover have "Bet PO A BMA \<and> Bet A BMA B \<Longrightarrow> Bet PO CMB E \<or> Bet PO E CMB"
                          by (meson Bet_cases Ps_def \<open>A \<midarrow> PO \<midarrow> E\<close> \<open>PO \<noteq> A\<close> \<open>Ps PO E BMA\<close> 
                              not_bet_and_out outer_transitivity_between) 
                        ultimately have "Bet PO CMB E \<or> Bet PO E CMB" 
                          using \<open>Bet BMA B PO \<and> Bet B PO A \<or> Bet BMA PO B \<and> Bet PO B A \<or>
                                 Bet PO BMA A \<and> Bet BMA A B \<or> Bet PO A BMA \<and> Bet A BMA B\<close> 
                          by blast
                      }
                      moreover {
                        assume "Bet PO B A"
                        have "Bet PO B C"
                          using \<open>B \<midarrow> CMB \<midarrow> C\<close> \<open>B \<midarrow> PO \<midarrow> E\<close> \<open>E \<noteq> PO\<close> \<open>PO \<midarrow> B \<midarrow> CMB\<close>
                            \<open>(PO \<midarrow> CMB \<midarrow> B) \<Longrightarrow> (CMB \<midarrow> B \<midarrow> C) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                            between_equality
                            outer_transitivity_between by blast 
                        have "Bet PO CMB E \<or> Bet PO E CMB" 
                        proof (cases "B = CMB")
                          show "B = CMB \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                            using \<open>B \<midarrow> CMB \<midarrow> C\<close> \<open>PO \<midarrow> B \<midarrow> CMB\<close>
                              \<open>(PO \<midarrow> CMB \<midarrow> B) \<Longrightarrow> (CMB \<midarrow> B \<midarrow> C) \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)\<close> 
                            by auto 
                          show "B \<noteq> CMB \<Longrightarrow> (PO \<midarrow> CMB \<midarrow> E) \<or> (PO \<midarrow> E \<midarrow> CMB)"
                            by (metis \<open>B \<noteq> C\<close> \<open>PO \<midarrow> B \<midarrow> A\<close> \<open>PO \<midarrow> B \<midarrow> C\<close> \<open>PO \<noteq> B\<close> assms(1) 
                                between_equality between_symmetry calculation l5_2) 
                        qed
                      }
                      ultimately have "Bet PO CMB E \<or> Bet PO E CMB"
                        using \<open>A \<midarrow> PO \<midarrow> E\<close> \<open>B \<midarrow> PO \<midarrow> E\<close> \<open>E \<noteq> PO\<close> between_symmetry l5_2 by blast 
                    }
                    hence "Bet PO CMB E \<or> Bet PO E CMB"
                      using Ng_def \<open>Ng PO E B\<close> by blast 
                  }
                  hence "Bet PO CMB E \<or> Bet PO E CMB"
                    using Ng_def \<open>Ng PO E A\<close> by auto 
                }
                ultimately have "Bet PO CMB E \<or> Bet PO E CMB"   
                  using \<open>Bet CMB C PO \<and> Bet C PO B \<or> Bet CMB PO C \<and> Bet PO C B \<or> 
                         Bet PO CMB B \<and> Bet CMB B C \<or> Bet PO B CMB \<and> Bet B CMB C\<close>
                  by blast
              }
              ultimately show ?thesis 
                by blast
            qed
            ultimately have "Ps PO E CMB"
              by (metis Out_cases Ps_def \<open>B \<noteq> C\<close> \<open>Diff PO E E' C B CMB\<close> bet_out_1
                  between_symmetry diff_null_eq) 
            thus "LeP PO E E' B C"
              using LeP_def LtP_def \<open>Diff PO E E' C B CMB\<close> by auto 
          }
        qed
      qed
    qed
  }
qed

lemma bet_lt12_le13:
  assumes "Bet A B C"
    and "LtP PO E E' A B"
  shows "LeP PO E E' A C"
  using LeP_def assms(1,2) bet_lt12_le23 leP_trans by blast 

lemma bet_lt21_le32:
  assumes "Bet A B C"
    and "LtP PO E E' B A"
  shows "LeP PO E E' C B" 
proof  (cases "B = C")
  show "B = C \<Longrightarrow> LeP PO E E' C B"
    by (simp add: leP_refl) 
  {
    assume "B \<noteq> C"
    have "\<not> Col PO E E'"
      using Ar2_def assms(2) ltP_ar2 by blast 
    moreover have "Col PO E B"
      using Ar2_def assms(2) ltP_ar2 by auto 
    moreover have "Col PO E C"
      by (metis Ar2_def assms(1,2) bet_col colx ltP_ar2 ltP_neq) 
    ultimately obtain BMC where "Diff PO E E' B C BMC"
      using diff_exists by blast
    obtain MA where "Opp PO E E' A MA"
      using Ar2_def assms(2) ltP_ar2 opp_exists by presburger
    obtain MB where "Opp PO E E' B MB"
      using \<open>Col PO E B\<close> \<open>\<not> Col PO E E'\<close> opp_exists by blast 
    obtain MC where "Opp PO E E' C MC"
      using Diff_def \<open>Diff PO E E' B C BMC\<close> by auto
    have "Col PO E MA" 
      by (meson Ar2_def \<open>Opp PO E E' A MA\<close> diff_O_A diff_ar2) 
    have "Col PO E MB" 
      by (meson Ar2_def \<open>Opp PO E E' B MB\<close> diff_O_A diff_ar2) 
    have "Col PO E MC"
      by (meson Ar2_def \<open>Opp PO E E' C MC\<close> diff_O_A diff_ar2) 
    have "Col PO E BMC"
      using Ar2_def \<open>Diff PO E E' B C BMC\<close> diff_ar2 by force
    obtain AMB where "Diff PO E E' A B AMB"
      using LtP_def assms(2) by auto 
    obtain MAMMB where "Diff PO E E' MA MB MAMMB"
      using \<open>Col PO E MA\<close> \<open>Col PO E MB\<close> \<open>\<not> Col PO E E'\<close> diff_exists by blast 
    have "Col PO E MAMMB"
      by (meson Ar2_def \<open>Diff PO E E' MA MB MAMMB\<close> diff_ar2)
    have "Opp PO E E' AMB MAMMB" 
    proof -
      have "Sum PO E E' MB A AMB"
        using Diff_def \<open>Diff PO E E' A B AMB\<close> \<open>Opp PO E E' B MB\<close> \<open>\<not> Col PO E E'\<close> 
          opp_uniqueness sum_comm by blast 
      moreover have "Sum PO E E' A MAMMB B"
        by (metis Diff_def \<open>Diff PO E E' MA MB MAMMB\<close> \<open>Opp PO E E' A MA\<close> \<open>Opp PO E E' B MB\<close>
            \<open>\<not> Col PO E E'\<close> diff_sum sum_comm) 
      ultimately show ?thesis
        using \<open>Diff PO E E' A B AMB\<close> diff_opp local.sum_diff by presburger 
    qed
    obtain MBMMA where "Diff PO E E' MB MA MBMMA"
      using \<open>Col PO E MA\<close> \<open>Col PO E MB\<close> \<open>\<not> Col PO E E'\<close> diff_exists by blast
    hence "Col PO E MBMMA"
      by (meson Ar2_def diff_ar2) 
    have "AMB = MBMMA"
      by (meson \<open>Diff PO E E' MA MB MAMMB\<close> \<open>Diff PO E E' MB MA MBMMA\<close> \<open>Opp PO E E' AMB MAMMB\<close>
          \<open>\<not> Col PO E E'\<close> diff_opp opp_comm opp_uniqueness)
    have "Bet MA MB MC" 
    proof (rule l7_15 [of PO A _ B _ C], insert assms(1))
      show "PO Midpoint A MA" 
        using opp_midpoint[of PO E E' A MA] by (simp add: \<open>Opp PO E E' A MA\<close>) 
      show "PO Midpoint B MB" 
        using opp_midpoint [of PO E E' B MB] by (simp add: \<open>Opp PO E E' B MB\<close>) 
      show "PO Midpoint C MC" 
        using opp_midpoint [of PO E E' C MC] by (simp add: \<open>Opp PO E E' C MC\<close>) 
    qed
    obtain MBMMC where "Diff PO E E' MB MC MBMMC"
      using \<open>Col PO E MB\<close> \<open>Col PO E MC\<close> \<open>\<not> Col PO E E'\<close> diff_exists by blast 
    hence "Col PO E MBMMC"
      using Ar2_def diff_ar2 by force 
    have "Opp PO E E' BMC MBMMC" 
    proof -
      have "Sum PO E E' MC B BMC"
        using Diff_def \<open>Diff PO E E' B C BMC\<close> \<open>Opp PO E E' C MC\<close> \<open>\<not> Col PO E E'\<close> opp_uniqueness
          sum_comm by blast 
      moreover have "Sum PO E E' B MBMMC C" 
      proof -
        have "Sum PO E E' MB C MBMMC"
          by (meson \<open>Col PO E MB\<close> \<open>Diff PO E E' MB MC MBMMC\<close> \<open>Opp PO E E' C MC\<close> \<open>\<not> Col PO E E'\<close>
              diff_A_O diff_O_A opp_comm sum_diff_diff) 
        moreover have "Sum PO E E' B MB PO"
          using Opp_def \<open>Opp PO E E' B MB\<close> sum_opp by blast 
        moreover have "Sum PO E E' PO C C"
          by (simp add: \<open>Col PO E C\<close> \<open>\<not> Col PO E E'\<close> sum_O_B) 
        ultimately show ?thesis 
          using sum_assoc_2 by blast 
      qed
      ultimately show ?thesis
        using \<open>Diff PO E E' B C BMC\<close> diff_opp local.sum_diff by auto 
    qed
    obtain MCMMB where "Diff PO E E' MC MB MCMMB"
      using \<open>Col PO E MB\<close> \<open>Col PO E MC\<close> \<open>\<not> Col PO E E'\<close> diff_exists by blast 
    hence "Opp PO E E' MBMMC MCMMB"
      using \<open>Diff PO E E' MB MC MBMMC\<close> diff_opp by auto 
    hence "BMC = MCMMB"
      using \<open>Opp PO E E' BMC MBMMC\<close> \<open>\<not> Col PO E E'\<close> opp_comm opp_uniqueness by blast 
    have "LtP PO E E' MA MB"
      using LtP_def \<open>AMB = MBMMA\<close> \<open>Diff PO E E' A B AMB\<close> \<open>Diff PO E E' MB MA MBMMA\<close> assms(2)
        lt_diff_ps by blast
    have "LeP PO E E' MB MC"
      using \<open>LtP PO E E' MA MB\<close> \<open>MA \<midarrow> MB \<midarrow> MC\<close> bet_lt12_le23 by auto 
    thus "LeP PO E E' C B"
      by (metis LeP_def LtP_def \<open>BMC = MCMMB\<close> \<open>Diff PO E E' B C BMC\<close>
          \<open>Diff PO E E' MB MC MBMMC\<close> \<open>Diff PO E E' MC MB MCMMB\<close>
          \<open>Opp PO E E' BMC MBMMC\<close> diff_null_eq lt_diff_ps pos_null_neg) 
  }
qed

lemma bet_lt21_le31:
  assumes "Bet A B C"
    and "LtP PO E E' B A"
  shows "LeP PO E E' C A"
  using LeP_def assms(1,2) bet_lt21_le32 leP_trans by blast 

lemma opp_2_le_le:
  assumes "Opp PO E E' A MA"
    and "Opp PO E E' B MB"
    and "LeP PO E E' A B"
  shows "LeP PO E E' MB MA" 
proof -
  obtain MAMB where "Sum PO E E' MA MB MAMB"
    by (meson Ar2_def Opp_def assms(1,2) sum_ar2 sum_exists) 
  have "Sum PO E E' B MAMB MA"
    using Diff_def \<open>Sum PO E E' MA MB MAMB\<close> assms(2) diff_sum by blast 
  moreover have "Sum PO E E' A MAMB MB"
    by (meson Diff_def \<open>Sum PO E E' MA MB MAMB\<close> assms(1) calculation diff_sum sum3_col sum_comm
        sum_to_sum3) 
  ultimately show ?thesis
    using assms(3) compatibility_of_sum_with_order by blast 
qed

lemma diff_2_le_le:
  assumes "Diff PO E E' A C AMC"
    and "Diff PO E E' B C BMC"
    and "LeP PO E E' A B"
  shows "LeP PO E E' AMC BMC"
  by (metis Ar2_def Diff_def assms(1,2,3) compatibility_of_sum_with_order diff_ar2
      opp_uniqueness) 

  (** Lemma 15.2 *)
  (** Cong corresponds to length equality.*)
  (** Le corresponds to length inequality.*)

lemma length_pos:
  assumes "Length PO E E' A B L"
  shows "LeP PO E E' PO L"
  using Length_def assms by force 

lemma length_id_1:
  assumes "Length PO E E' A B PO"
  shows "A = B"
  by (meson Length_def assms cong_reverse_identity) 

lemma length_id_2:
  assumes "PO \<noteq> E"
  shows "Length PO E E' A A PO"
  by (meson Length_def assms cong_trivial_identity leP_refl
      not_col_distincts) 

lemma length_id:
  shows "Length PO E E' A B PO \<longleftrightarrow> (A = B \<and> PO \<noteq> E)"
  by (metis Length_def length_id_1 length_id_2) 

lemma length_eq_cong_1:
  assumes "Length PO E E' A B AB"
    and "Length PO E E' C D AB"
  shows "Cong A B C D"
  by (meson Length_def assms(1,2) cong_inner_transitivity) 

lemma length_eq_cong_2:
  assumes "Length PO E E' A B AB"
    and "Cong A B C D"
  shows "Length PO E E' C D AB"
  by (metis Length_def assms(1,2) cong_transitivity) 

lemma ltP_pos:
  assumes "LtP PO E E' PO A"
  shows "Ps PO E A"
  using Ar2_def assms diff_A_O ltP_ar2 lt_diff_ps by presburger 

lemma bet_leP:
  assumes "Bet PO AB CD"
    and "LeP PO E E' PO AB"
    and "LeP PO E E' PO CD"
  shows "LeP PO E E' AB CD"
  using LeP_def assms(1,2,3) bet_lt12_le23 by blast 

lemma leP_bet:
  assumes "LeP PO E E' AB CD" 
    and "LeP PO E E' PO AB"
    and "LeP PO E E' PO CD"
  shows "Bet PO AB CD"
proof -
  {
    assume "LtP PO E E' AB CD"
    then obtain X where "Diff PO E E' CD AB X" and "Ps PO E X"
      using LtP_def by auto 
    hence "PO Out AB X \<or> AB = PO"
      by (metis LeP_def Ps_def assms(2) l6_6 l6_7 ltP_pos) 
    moreover have "PO Out AB X \<Longrightarrow> Bet PO AB CD"
      using \<open>Diff PO E E' CD AB X\<close> diff_sum l14_36_a by blast 
    moreover have "AB = PO \<Longrightarrow> Bet PO AB CD"
      by (simp add: between_trivial2) 
    ultimately have "Bet PO AB CD" 
      by blast
  }
  moreover have "AB = CD \<Longrightarrow> Bet PO AB CD"
    by (simp add: between_trivial) 
  ultimately show ?thesis
    using LeP_def assms(1) by blast
qed

lemma length_Ar2:
  assumes "Length PO E E' A B AB"
  shows "(Col PO E AB \<and> \<not> Col PO E E') \<or> AB = PO" 
proof -
  have "LtP PO E E' PO AB \<or> PO = AB"
    using LeP_def assms length_pos by auto 
  moreover have "LtP PO E E' PO AB \<Longrightarrow> (Col PO E AB \<and> \<not> Col PO E E')"
    using Ar2_def ltP_ar2 by presburger 
  ultimately show ?thesis by blast
qed

lemma length_leP_le_1:
  assumes "Length PO E E' A B AB"
    and "Length PO E E' C D CD"
    and "LeP PO E E' AB CD"
  shows "A B Le C D" 
proof -
  have "Bet PO AB CD"
    using assms(1,2,3) leP_bet length_pos by blast
  obtain M' where "Bet D C M'" and "Cong C M' A B"
    using segment_construction by blast 
  then obtain M where "C Midpoint M' M"
    using symmetric_point_construction by auto 
  hence "Cong A B C M"
    using Cong_cases Midpoint_def \<open>Cong C M' A B\<close> cong_inner_transitivity by blast 
  show ?thesis 
  proof (rule le_transitivity [of _ _ C M])
    show "A B Le C M"
      by (simp add: \<open>Cong A B C M\<close> cong__le) 
    have "PO AB Le PO CD"
      by (simp add: \<open>PO \<midarrow> AB \<midarrow> CD\<close> bet__le1213) 
    thus "C M Le C D"
      by (meson Length_def \<open>Cong A B C M\<close> assms(1,2) cong_transitivity l5_6) 
  qed
qed

lemma length_leP_le_2:
  assumes "Length PO E E' A B AB"
    and "Length PO E E' C D CD"
    and "A B Le C D"
  shows "LeP PO E E' AB CD" 
proof -
  have "Col PO E AB \<and> \<not> Col PO E E' \<or> AB = PO"
    using assms(1) length_Ar2 by auto 
  have "Col PO E CD \<and> \<not> Col PO E E' \<or> CD = PO"
    using assms(2) length_Ar2 by auto 
  have "Bet PO AB CD"
  proof (cases "PO = CD")
    {
      assume "PO = CD"
      hence "C = D"
        using assms(2) length_id_1 by blast 
      obtain X where "Bet C X C" and "Cong A B C X"
        using Le_def \<open>C = D\<close> assms(3) by blast 
      hence "C = X"
        by (simp add: between_identity) 
      hence "A = B"
        using \<open>Cong A B C X\<close> cong_diff by blast
      hence "PO = AB"
        by (metis Length_def assms(1) cong_identity) 
      thus "PO \<midarrow> AB \<midarrow> CD"
        using between_trivial2 by auto 
    }
    {
      assume "PO \<noteq> CD"
      have "PO AB Le PO CD"
        by (meson Length_def assms(1,2,3) cong_symmetry l5_6) 
      then obtain M where "Bet PO M CD" and "Cong PO AB PO M"
        using Le_def by blast 
      {
        assume "Col PO E AB" and "\<not> Col PO E E'" and "Col PO E CD" and "\<not> Col PO E E'"
        obtain P where "Bet C P D" and "Cong A B C P"
          using Le_def assms(3) by blast
        {
          assume "LtP PO E E' PO AB"

          {
            assume "LtP PO E E' PO CD"
            obtain X where "Diff PO E E' AB PO X" and "Ps PO E X"
              using LtP_def \<open>LtP PO E E' PO AB\<close> by blast 
            obtain Y where "Diff PO E E' CD PO Y" and "Ps PO E Y"
              using LtP_def \<open>LtP PO E E' PO CD\<close> by blast 
            have "ParallelogramFlat PO PO AB X"
              by (metis O_not_positive ParallelogramFlat_def \<open>Col PO E AB\<close>
                  \<open>Diff PO E E' AB PO X\<close> \<open>Ps PO E X\<close> \<open>\<not> Col PO E E'\<close> col_trivial_1
                  cong_pseudo_reflexivity cong_trivial_identity diff_A_O
                  diff_uniqueness) 
            have "ParallelogramFlat PO PO CD Y"
              using \<open>Diff PO E E' CD PO Y\<close> \<open>PO \<noteq> CD\<close> diff_to_plg by auto 
            have "PO \<noteq> AB \<or> PO \<noteq> X"
              using O_not_positive \<open>Ps PO E X\<close> by blast 
            have "PO \<noteq> CD \<or> PO \<noteq> Y"
              by (simp add: \<open>PO \<noteq> CD\<close>) 
            have "Col AB PO M" 
            proof -
              have "PO Out AB CD"
                by (metis Bet_cases[of CD M PO] Bet_cases[of _ PO AB]
                    Bet_cases[of _ PO CD] Out_cases[of PO E CD] Ps_def[of PO E CD]
                    Ps_def[of PO E AB] \<open>Cong PO AB PO M\<close> \<open>PO \<midarrow> M \<midarrow> CD\<close>
                    \<open>ParallelogramFlat PO PO AB X\<close> \<open>ParallelogramFlat PO PO CD Y\<close>
                    \<open>Ps PO E X\<close> \<open>Ps PO E Y\<close> bet_out_1[of AB PO CD]
                    bet_out__bet[of E PO _ CD] bet_out__bet[of AB PO _ E]
                    between_cong_3[of _ PO AB M]
                    between_inner_transitivity[of _ PO CD M]
                    plgf_trivial_neq[of PO CD Y] plgf_trivial_neq[of PO AB X]
                    point_construction_different[of AB PO]) 
              thus ?thesis
                using Col_def \<open>Cong PO AB PO M\<close> \<open>PO AB Le PO CD\<close> \<open>PO \<midarrow> M \<midarrow> CD\<close> between_cong
                  l5_3 l6_13_1 by blast 
            qed
            hence "AB = M \<or> PO Midpoint AB M" 
              using l7_20 \<open>Cong PO AB PO M\<close> by simp
            hence "PO \<midarrow> AB \<midarrow> CD"
              by (metis Bet_cases Cong_cases Midpoint_def Out_cases Ps_def \<open>PO \<midarrow> M \<midarrow> CD\<close>
                  \<open>ParallelogramFlat PO PO AB X\<close> \<open>ParallelogramFlat PO PO CD Y\<close> \<open>Ps PO E X\<close>
                  \<open>Ps PO E Y\<close> bet_cong_eq bet_out__bet between_equality_2
                  plgf_trivial_neq) 
          }
          moreover have "PO = CD \<Longrightarrow> (PO \<midarrow> AB \<midarrow> CD)"
            by (simp add: \<open>PO \<noteq> CD\<close>)
          ultimately have "PO \<midarrow> AB \<midarrow> CD"
            using LeP_def assms(2) length_pos by blast 
        }
        moreover have "PO = AB \<Longrightarrow> (PO \<midarrow> AB \<midarrow> CD)"
          using between_trivial2 by auto 
        ultimately have "PO \<midarrow> AB \<midarrow> CD"
          using LeP_def assms(1) length_pos by blast 
      }
      moreover have "Col PO E AB \<and> \<not> Col PO E E' \<and> CD = PO \<Longrightarrow> (PO \<midarrow> AB \<midarrow> CD)"
        using \<open>PO \<noteq> CD\<close> by blast 
      moreover have "AB = PO \<and> Col PO E CD \<and> \<not> Col PO E E' \<Longrightarrow> (PO \<midarrow> AB \<midarrow> CD)"
        using between_trivial2 by blast 
      moreover have "AB = PO \<and> CD = PO \<Longrightarrow> (PO \<midarrow> AB \<midarrow> CD)"
        using \<open>PO \<noteq> CD\<close> by blast 
      ultimately show "PO \<midarrow> AB \<midarrow> CD"
        using \<open>Col PO E AB \<and> \<not> Col PO E E' \<or> AB = PO\<close>
          \<open>Col PO E CD \<and> \<not> Col PO E E' \<or> CD = PO\<close> by presburger 
    }
  qed
  thus ?thesis
    using assms(1,2) bet_leP length_pos by force 
qed

lemma l15_3:
  assumes "Sum PO E E' A B C"
  shows "Cong PO B A C"
  by (metis Ar2_def assms cong_reflexivity sum_ar2 sum_cong2 sum_iff_cong_b) 

(** Lemma 15.4. *)
(** Triangular equality. *)
lemma length_uniqueness:
  assumes "Length PO E E' A B AB"
    and "Length PO E E' A B AB'"
  shows "AB = AB'"
  by (meson assms(1,2) leP_asym leP_refl length_leP_le_1 length_leP_le_2) 

lemma length_Ps:
  assumes "AB \<noteq> PO"
    and "Length PO E E' A B AB"
  shows "Ps PO E AB"
  using LeP_def assms(1,2) length_pos ltP_pos by blast 

lemma length_not_col_null:
  assumes "Col PO E E'"
    and "Length PO E E' A B AB"
  shows "AB = PO"
  using assms(1,2) length_Ar2 by blast 

lemma not_triangular_equality1:
  assumes "PO \<noteq> E" 
  shows "\<not> (\<forall> E' B C AB BC AC. Bet A B C \<and> Length PO E E' A B AB \<and> Length PO E E' B C BC \<and> 
                               Length PO E E' A C AC \<longrightarrow> Sum PO E E' AB BC AC)"
  by (metis Ar2_def Sum_def assms between_trivial length_id) 

lemma triangular_equality:
  assumes "PO \<noteq> E" 
    and "Bet A B C"
    and "IsLength PO E E' A B AB"
    and "IsLength PO E E' B C BC"
    and "IsLength PO E E' A C AC"
  shows "Sumg PO E E' AB BC AC" 
proof -
  have "Length PO E E' A B AB \<or> PO = E \<and> PO = AB"
    using IsLength_def assms(3) by auto 
  moreover 
  {
    assume "Length PO E E' A B AB"
    have "Length PO E E' B C BC \<or> PO = E \<and> PO = BC"
      using IsLength_def assms(4) by presburger 
    moreover {
      assume "Length PO E E' B C BC"
      have "Length PO E E' A C AC \<or> PO = E \<and> PO = AC"
        using IsLength_def assms(5) by auto 
      moreover {
        assume "Length PO E E' A C AC"
        have "LtP PO E E' PO AB \<or> PO = AB"
          using LeP_def Length_def \<open>Length PO E E' A B AB\<close> by presburger 
        moreover 
        {
          assume "LtP PO E E' PO AB"
          have "LtP PO E E' PO BC \<or> PO = BC"
            using LeP_def Length_def \<open>Length PO E E' B C BC\<close> by presburger 
          moreover {
            assume "LtP PO E E' PO BC"
            have "LtP PO E E' PO AC \<or> PO = AC"
              using LeP_def Length_def \<open>Length PO E E' A C AC\<close> by presburger 
            moreover 
            {
              assume "LtP PO E E' PO AC"
              obtain X where "Diff PO E E' AB PO X" and "Ps PO E X"
                using LtP_def \<open>LtP PO E E' PO AB\<close> by blast 
              obtain Y where "Diff PO E E' BC PO Y" and "Ps PO E Y"
                using LtP_def \<open>LtP PO E E' PO BC\<close> by blast 
              obtain Z where "Diff PO E E' AC PO Z" and "Ps PO E Z"
                using LtP_def \<open>LtP PO E E' PO AC\<close> by blast 
              have "AB = X"
                by (meson Ar2_def \<open>Diff PO E E' AB PO X\<close> \<open>LtP PO E E' PO AB\<close> diff_A_O
                    diff_uniqueness ltP_ar2)
              have "BC = Y"
                by (meson Ar2_def \<open>Diff PO E E' BC PO Y\<close> \<open>LtP PO E E' PO BC\<close> diff_A_O
                    diff_uniqueness ltP_ar2)
              have "AC = Z"
                by (meson Ar2_def \<open>Diff PO E E' AC PO Z\<close> \<open>LtP PO E E' PO AC\<close> diff_A_O
                    diff_uniqueness ltP_ar2) 
              obtain AC' where "Sum PO E E' AB BC AC'"
                by (metis Ar2_def Ps_def \<open>BC = Y\<close> \<open>LtP PO E E' PO AB\<close> \<open>Ps PO E Y\<close>
                    col_permutation_2 col_permutation_3 ltP_ar2 out_col sum_exists)
              have "Bet PO AB AC'"
                by (metis Out_cases Ps_def \<open>AB = X\<close> \<open>BC = Y\<close> \<open>Ps PO E X\<close> \<open>Ps PO E Y\<close>
                    \<open>Sum PO E E' AB BC AC'\<close> l14_36_a l6_7)
              have "Cong PO BC AB AC'"
                using \<open>Sum PO E E' AB BC AC'\<close> l15_3 by auto
              have "Cong PO AC' A C"
                by (smt (verit, ccfv_threshold) Cong_cases \<open>Cong PO BC AB AC'\<close>
                    \<open>Length PO E E' A B AB\<close> \<open>Length PO E E' B C BC\<close> \<open>PO \<midarrow> AB \<midarrow> AC'\<close> assms(2)
                    cong_transitivity l2_11_b length_cong) 
              have "Ps PO E AC'"
                using \<open>AB = X\<close> \<open>BC = Y\<close> \<open>Ps PO E X\<close> \<open>Ps PO E Y\<close> \<open>Sum PO E E' AB BC AC'\<close>
                  sum_pos_pos by blast
              hence "AC = AC'"
                by (smt (verit, ccfv_SIG) Cong_cases Out_def Ps_def \<open>Cong PO AC' A C\<close>
                    \<open>Length PO E E' A C AC\<close> \<open>LtP PO E E' PO AC\<close> between_cong
                    cong_inner_transitivity l6_7 length_cong ltP_pos) 
              hence "Sumg PO E E' AB BC AC"
                by (simp add: Sumg_def \<open>Sum PO E E' AB BC AC'\<close>) 
            }
            moreover have "PO = AC \<Longrightarrow> Sumg PO E E' AB BC AC"
              by (metis O_not_positive \<open>Length PO E E' A B AB \<or> PO = E \<and> PO = AB\<close>
                  \<open>Length PO E E' A C AC\<close> \<open>LtP PO E E' PO AB\<close> assms(2) between_identity
                  cong_reverse_identity length_cong length_id_1 ltP_pos) 
            ultimately have "Sumg PO E E' AB BC AC" 
              by blast
          }
          moreover have "PO = BC \<Longrightarrow> Sumg PO E E' AB BC AC"
            by (metis Ar2_def Sumg_def \<open>Length PO E E' A B AB\<close> \<open>Length PO E E' A C AC\<close>
                \<open>Length PO E E' B C BC\<close> \<open>LtP PO E E' PO AB\<close> length_id length_uniqueness
                ltP_ar2 sum_A_O) 
          ultimately have "Sumg PO E E' AB BC AC" 
            by blast
        }
        moreover have "PO = AB \<Longrightarrow> Sumg PO E E' AB BC AC"
          by (metis Ar2_def Length_def Sumg_def \<open>Length PO E E' A B AB\<close>
              \<open>Length PO E E' A C AC\<close> \<open>Length PO E E' B C BC\<close> length_id
              length_not_col_null length_uniqueness sum_O_B)
        ultimately have "Sumg PO E E' AB BC AC" 
          by blast
      }
      moreover have "PO = E \<and> PO = AC \<Longrightarrow> Sumg PO E E' AB BC AC"
        using assms(1) by blast 
      ultimately have "Sumg PO E E' AB BC AC" 
        by blast
    }
    moreover have "PO = E \<and> PO = BC \<Longrightarrow> Sumg PO E E' AB BC AC"
      by (simp add: assms(1)) 
    ultimately have "Sumg PO E E' AB BC AC" 
      by blast
  }
  moreover have " PO = E \<and> PO = AB \<Longrightarrow> Sumg PO E E' AB BC AC"
    using assms(1) by auto 
  ultimately show "Sumg PO E E' AB BC AC" 
    by blast
qed

lemma length_O:
  assumes "PO \<noteq> E"
  shows "Length PO E E' PO PO PO"
  by (simp add: assms length_id)

lemma triangular_equality_bis:
  assumes "A \<noteq> B \<or> A \<noteq> C \<or> B \<noteq> C"
    and "PO \<noteq> E"
    and "Bet A B C"
    and "Length PO E E' A B AB"
    and "Length PO E E' B C BC"
    and "Length PO E E' A C AC"
  shows "Sum PO E E' AB BC AC" 
proof -
  have "LtP PO E E' PO AB \<or> PO = AB"
    using LeP_def Length_def assms(4) by presburger 
  moreover have "LtP PO E E' PO BC \<or> PO = BC"
    using LeP_def Length_def assms(5) by presburger 
  moreover have "LtP PO E E' PO AC \<or> PO = AC"
    using LeP_def Length_def assms(6) by presburger 
  moreover {
    assume "LtP PO E E' PO AB" and "LtP PO E E' PO BC" and "LtP PO E E' PO AC"
    obtain X where "Diff PO E E' AB PO X" and "Ps PO E X"
      using LtP_def \<open>LtP PO E E' PO AB\<close> by blast 
    obtain Y where "Diff PO E E' BC PO Y" and "Ps PO E Y"
      using LtP_def \<open>LtP PO E E' PO BC\<close> by blast 
    obtain Z where "Diff PO E E' AC PO Z" and "Ps PO E Z"
      using LtP_def \<open>LtP PO E E' PO AC\<close> by blast 
    have "AB = X"
      by (meson Ar2_def \<open>Diff PO E E' AB PO X\<close> \<open>LtP PO E E' PO AB\<close> diff_A_O
          diff_stable ltP_ar2)
    have "BC = Y"
      by (meson Ar2_def \<open>Diff PO E E' BC PO Y\<close> \<open>LtP PO E E' PO BC\<close> diff_A_O
          diff_stable ltP_ar2) 
    have "AC = Z"
      by (meson Ar2_def \<open>Diff PO E E' AC PO Z\<close> \<open>LtP PO E E' PO AC\<close> diff_A_O
          diff_stable ltP_ar2) 
    obtain AC' where "Sum PO E E' AB BC AC'"
      by (metis Ar2_def Ps_def \<open>BC = Y\<close> \<open>LtP PO E E' PO AB\<close> \<open>Ps PO E Y\<close>
          col_permutation_5 ltP_ar2 out_col sum_exists) 
    hence "Bet PO AB AC'"
      by (metis Ps_def \<open>AB = X\<close> \<open>BC = Y\<close> \<open>Ps PO E X\<close> \<open>Ps PO E Y\<close> l14_36_a l6_6
          l6_7) 
    have "Cong PO BC AB AC'"
      using \<open>Sum PO E E' AB BC AC'\<close> l15_3 by auto
    have "Cong PO AC' A C"
      by (smt (verit, ccfv_threshold) Cong_cases \<open>Cong PO BC AB AC'\<close>
          \<open>PO \<midarrow> AB \<midarrow> AC'\<close> assms(3,4,5) cong_transitivity l2_11_b
          length_cong)
    have "Ps PO E AC'"
      using \<open>AB = X\<close> \<open>BC = Y\<close> \<open>Ps PO E X\<close> \<open>Ps PO E Y\<close> \<open>Sum PO E E' AB BC AC'\<close>
        sum_pos_pos by blast
    have "AC = AC'"
      by (smt (verit, ccfv_threshold) Col_cases Cong_cases Out_cases Out_def
          Ps_def \<open>AC = Z\<close> \<open>Cong PO AC' A C\<close> \<open>Ps PO E AC'\<close> \<open>Ps PO E Z\<close> assms(6)
          bet_cong_eq bet_out__bet col_permutation_2 col_transitivity_2
          cong_inner_transitivity l6_4_2 length_cong not_bet_and_out
          out_col)
    hence "Sum PO E E' AB BC AC"
      by (simp add: \<open>Sum PO E E' AB BC AC'\<close>) 
  }
  moreover have "LtP PO E E' PO AB \<and> LtP PO E E' PO BC \<and> PO = AC \<Longrightarrow> Sum PO E E' AB BC AC"
    using assms(1,3,6) between_equality between_trivial length_id by force 
  moreover have "LtP PO E E' PO AB \<and> PO = BC \<and> LtP PO E E' PO AC \<Longrightarrow> Sum PO E E' AB BC AC"
    by (metis assms(4,5,6) calculation(4) length_Ar2 length_id_1 length_uniqueness sum_A_O) 
  moreover have "PO = AB \<and> LtP PO E E' PO BC \<and> LtP PO E E' PO AC \<Longrightarrow> Sum PO E E' AB BC AC"
    by (metis Ar2_def assms(4,5,6) length_id_1 length_uniqueness ltP_ar2
        sum_O_B)
  moreover have "PO = AB \<and> PO = BC \<and> LtP PO E E' PO AC \<Longrightarrow> Sum PO E E' AB BC AC"
    by (metis Ps_def assms(4,5,6) between_trivial2 cong_reverse_identity
        length_cong length_id_1 ltP_pos not_bet_and_out) 
  moreover have "PO = AB \<and> LtP PO E E' PO BC \<and> PO = AC \<Longrightarrow> Sum PO E E' AB BC AC"
    by (metis Ps_def assms(4,5,6) between_trivial2 cong_reverse_identity
        length_cong length_id_1 ltP_pos not_bet_and_out) 
  moreover have "LtP PO E E' PO AB \<and> PO = BC \<and> PO = AC \<Longrightarrow> Sum PO E E' AB BC AC"
    using assms(1,3,6) between_equality between_trivial length_id_1
    by blast 
  moreover have "PO = AB \<and> PO = BC \<and> PO = AC \<Longrightarrow> Sum PO E E' AB BC AC"
    using assms(1,4,6) length_id_1 by blast 
  ultimately show ?thesis 
    by blast
qed

(** Lemma 15.5. *)
(** Known as Thales theorem or intercept theorem. *)
lemma length_out:
  assumes "A \<noteq> B"
    and "C \<noteq> D"
    and "Length PO E E' A B AB"
    and "Length PO E E' C D CD"
  shows "PO Out AB CD"
  by (metis (full_types) Length_def Ps_def assms(1,2,3,4) bet_out__bet
      cong_reverse_identity l6_3_2 length_Ps
      point_construction_different) 

lemma image_preserves_bet1:
  assumes "Bet A B C"
    and "A A' Reflect X Y"
    and "B B' Reflect X Y"
    and "C C' Reflect X Y"
  shows "Bet A' B' C'"
  using assms(1,2,3,4) image_gen_preserves_bet by blast 

lemma image_preserves_col:
  assumes "Col A B C"
    and "A A' Reflect X Y"
    and "B B' Reflect X Y"
    and "C C' Reflect X Y"
  shows "Col A' B' C'"
  using Col_def assms(1,2,3,4) image_gen_preserves_bet by presburger 

lemma image_preserves_out:
  assumes "A Out B C"
    and "A A' Reflect X Y"
    and "B B' Reflect X Y"
    and "C C' Reflect X Y"
  shows "A' Out B' C'" 
proof -
  have "B' \<noteq> A'"
    using assms(1,2,3) l10_2_uniqueness out_distinct by blast 
  moreover have "C' \<noteq> A'"
    using assms(1,2,4) l10_2_uniqueness out_diff2 by blast 
  moreover have "Bet A' B' C' \<or> Bet A' C' B'"
    by (meson Out_def assms(1,2,3,4) image_preserves_bet1) 
  ultimately show ?thesis
    using Out_def by blast 
qed

lemma project_preserves_out:
  assumes "A Out B C"
    and "\<not> A B Par X Y"
    and "A A' Proj P Q X Y"
    and "B B' Proj P Q X Y"
    and "C C' Proj P Q X Y"
  shows "A' Out B' C'" 
proof -
  have "B' \<noteq> A'"
    by (metis assms(1,2,3,4) ker_par out_distinct) 
  moreover have "C' \<noteq> A'"
    by (metis Out_def assms(1,2,3,5) ker_par not_par_not_col out_col
        par_trans) 
  moreover have "Bet A' B' C' \<or> Bet A' C' B'"
    by (meson Out_def assms(1,3,4,5) project_preserves_bet)
  ultimately show ?thesis
    using Out_def by blast 
qed

lemma conga_bet_conga:
  assumes "A B C CongA D E F"
    and "A' \<noteq> B"
    and "C' \<noteq> B"
    and "D' \<noteq> E"
    and "F' \<noteq> E"
    and "Bet A B A'"
    and "Bet C B C'"
    and "Bet D E D'"
    and "Bet F E F'"
  shows "A' B C' CongA D' E F'"
  by (meson assms(1,2,3,4,5,6,7,8,9) conga_comm l11_13) 

lemma thales:
  assumes "PO \<noteq> E"
    and "Col P A B"
    and "Col P C D"
    and "\<not> Col P A C"
    and "A C Pj B D" 
    and "Length PO E E' P A A1"
    and "Length PO E E' P B B1"
    and "Length PO E E' P C C1"
    and "Length PO E E' P D D1"
    and "Prodg PO E E' A1 D1 AD"
  shows "Prodg PO E E' C1 B1 AD"
proof (cases "Col PO E E'")
  show "Col PO E E' \<Longrightarrow> Prodg PO E E' C1 B1 AD"
    using Ar2_def Prod_def Prodg_def assms(10) by presburger 
  {
    assume "\<not> Col PO E E'"
    have "Prod PO E E' A1 D1 AD \<or> (\<not> Ar2 PO E E' A1 D1 D1 \<and> AD = PO)"
      using Prodg_def assms(10) by blast 
    moreover 
    {
      assume "Prod PO E E' A1 D1 AD"
      have "Prodg PO E E' C1 B1 AD"
      proof (cases "P = B")
        show "P = B \<Longrightarrow> Prodg PO E E' C1 B1 AD"
          by (metis (mono_tags, lifting) Length_def Prodg_def
              \<open>Prod PO E E' A1 D1 AD\<close> \<open>\<not> Col PO E E'\<close>
              assms(3,4,5,7,8,9) length_id_2 length_uniqueness
              not_col_distincts pj_trivial pj_uniqueness prod_0_r
              prod_O_l_eq prod_sym) 
        {
          assume "P \<noteq> B"
          show "Prodg PO E E' C1 B1 AD" 
          proof (cases "A = B")
            {
              assume "A = B"
              have "A C ParStrict A D \<Longrightarrow> Prodg PO E E' C1 B1 AD"
                by (simp add: not_par_strict_id) 
              hence "A C Par A D \<Longrightarrow> Prodg PO E E' C1 B1 AD"
                by (metis Col_def Prodg_def \<open>A = B\<close>
                    \<open>Prod PO E E' A1 D1 AD\<close> assms(3,4,6,7,8,9) col2__eq
                    length_uniqueness par_id prod_sym) 
              thus "Prodg PO E E' C1 B1 AD"
                using NCol_perm Pj_def \<open>A = B\<close> assms(3,4,5) by blast 
            }
            {
              assume "A \<noteq> B"
              have "\<not> Col PO A1 E'"
                by (metis assms(4,6) col_permutation_5 col_trivial_3 colx length_Ar2
                    length_id_1) 
              then obtain C1' where "P A C Cong3 PO A1 C1'" and "PO A1 OS E' C1'"
                using assms(4,6) l10_16 length_cong by meson
              have "P A C CongA PO A1 C1'"
                by (metis \<open>P A C Cong3 PO A1 C1'\<close> assms(4) col_trivial_1 col_trivial_2
                    cong3_conga) 
              have "\<not> Col PO C1 C1'"
                by (metis \<open>PO A1 OS E' C1'\<close> assms(1,4,6,8) col_transitivity_1 col_trivial_3
                    length_Ar2 length_id_1 one_side_not_col124)
              obtain M where "M Midpoint C1 C1'"
                using MidR_uniq_aux by blast
              obtain D1' where "D1' D1 Reflect PO M"
                using l10_2_existence by fastforce
              moreover {
                assume "PO \<noteq> M" and "D1' D1 ReflectL PO M"
                then obtain N where "N Midpoint D1 D1'" and "Col PO M N"
                  using ReflectL_def by blast 
                have "PO Out C1 D1" 
                proof (rule length_out [of P C P D _ E E'])
                  show "P \<noteq> C"
                    using assms(4) not_col_distincts by blast 
                  {
                    assume "P = D"
                    have "PO = AD"
                      using \<open>P = D\<close> \<open>Prod PO E E' A1 D1 AD\<close> assms(9)
                        cong_reverse_identity length_cong prod_O_r_eq
                      by blast 
                    have "A C Par B P \<Longrightarrow> False"
                      by (metis assms(2,4) not_col_distincts par_col2_par_bis par_id_5) 
                    hence False
                      using Pj_def \<open>P = D\<close> \<open>P \<noteq> B\<close> assms(5) by blast 
                  }
                  thus "P \<noteq> D" 
                    by blast
                  show "Length PO E E' P C C1"
                    by (simp add: assms(8)) 
                  show "Length PO E E' P D D1"
                    by (simp add: assms(9)) 
                qed
                have "PO Out A1 C1"
                  by (metis assms(4,6,8) col_trivial_1 col_trivial_3 length_out) 
                have "M \<noteq> C1"
                  using \<open>M Midpoint C1 C1'\<close> \<open>\<not> Col PO C1 C1'\<close> col_trivial_2 is_midpoint_id 
                  by blast 
                have "Per PO M C1" 
                proof -
                  have "Cong PO C1 PO C1'"
                    by (meson Cong3_def \<open>P A C Cong3 PO A1 C1'\<close> assms(8) 
                        cong_inner_transitivity length_cong) 
                  thus ?thesis
                    using Per_def \<open>M Midpoint C1 C1'\<close> by blast 
                qed
                have "M PO Perp C1 M \<or> M M Perp C1 M"
                  using Perp_cases \<open>M \<noteq> C1\<close> \<open>PO \<noteq> M\<close> \<open>Per PO M C1\<close>
                    col_per_perp col_trivial_3 by blast 
                have "PO Out C1' D1'" 
                proof (rule image_preserves_out [of PO C1 D1 _ PO M], 
                    insert \<open>PO Out C1 D1\<close> image_triv)
                  show "C1 C1' Reflect PO M"
                    by (meson Cong3_def \<open>M Midpoint C1 C1'\<close>
                        \<open>P A C Cong3 PO A1 C1'\<close> assms(8) cong_inner_transitivity
                        cong_midpoint__image l7_2 length_cong) 
                  show "D1 D1' Reflect PO M"
                    by (simp add: calculation l10_4) 
                qed
                have "PO N Perp D1 N" 
                proof (rule perp_col [of _ _ M], insert \<open>Col PO M N\<close>)
                  show "PO \<noteq> N"
                    by (metis Out_def \<open>N Midpoint D1 D1'\<close> \<open>PO Out C1 D1\<close>
                        \<open>PO Out C1' D1'\<close> \<open>\<not> Col PO C1 C1'\<close> col_transitivity_1
                        not_col_sym_not_col out_col) 
                  show "PO M Perp D1 N" 
                  proof -
                    have  "D1 \<noteq> N"
                      using \<open>N Midpoint D1 D1'\<close> \<open>PO Out C1 D1\<close> \<open>PO Out C1' D1'\<close>
                        \<open>\<not> Col PO C1 C1'\<close> is_midpoint_id l6_6 l6_7 out_col
                      by blast 
                    moreover have "D1 D1' Perp PO M"
                      by (metis Perp_perm ReflectL_def \<open>D1' D1 ReflectL PO M\<close>
                          \<open>N Midpoint D1 D1'\<close> calculation l7_3) 
                    moreover have "Col D1 D1' N"
                      using \<open>N Midpoint D1 D1'\<close> bet_col1 between_trivial midpoint_bet by blast 
                    ultimately show ?thesis
                      by (metis Perp_cases perp_col) 
                  qed
                qed
                have "Cong PO D1 PO D1'"
                  using calculation image_triv l10_10 by blast 
                have "C1 C1' Par D1 D1'" 
                proof -
                  have "PO M Perp D1 D1' \<or> D1 = D1'"
                    using ReflectL_def \<open>D1' D1 ReflectL PO M\<close> by blast 
                  moreover {
                    assume "PO M Perp D1 D1'"
                    have "C1 C1' Par D1 D1'"
                    proof -
                      {
                        assume "M PO Perp C1 M"
                        have "C1 C1' Par D1 D1'" 
                        proof (rule l12_9_2D [of _ _ PO M])
                          show "C1 C1' Perp PO M"
                            by (metis \<open>M Midpoint C1 C1'\<close> \<open>M \<noteq> C1\<close> \<open>PO \<noteq> M\<close>
                                \<open>Per PO M C1\<close> bet_cong_eq between_trivial2 col_per_perp
                                midpoint_bet midpoint_col midpoint_cong
                                not_cong_3412) 
                          show "D1 D1' Perp PO M"
                            using Perp_cases \<open>PO M Perp D1 D1'\<close> by blast 
                        qed
                      }
                      moreover have "M M Perp C1 M \<Longrightarrow> C1 C1' Par D1 D1'"
                        using perp_distinct by blast
                      ultimately show ?thesis
                        using \<open>M PO Perp C1 M \<or> M M Perp C1 M\<close> by blast 
                    qed
                  }
                  moreover have "D1 = D1' \<Longrightarrow> C1 C1' Par D1 D1'"
                    using \<open>PO Out C1 D1\<close> \<open>PO Out C1' D1'\<close> \<open>\<not> Col PO C1 C1'\<close> l6_6
                      l6_7 out_col by blast 
                  ultimately show ?thesis 
                    by blast
                qed
                hence "C1 C1' Pj D1 D1'"
                  by (simp add: Pj_def) 
                have "P C A Cong3 PO C1' A1"
                  by (simp add: \<open>P A C Cong3 PO A1 C1'\<close> cong_3_swap_2)
                have "P C A CongA PO C1' A1"
                  using \<open>P C A Cong3 PO C1' A1\<close> assms(4) cong3_conga
                    not_col_distincts by auto
                have "Cong P A PO A1 \<and> (P \<noteq> A \<longrightarrow> C P A CongA C1' PO A1 \<and> C A P CongA C1' A1 PO)" 
                  using l11_49 Cong3_def \<open>P C A Cong3 PO C1' A1\<close>
                    \<open>P C A CongA PO C1' A1\<close> cong_3_swap by blast 
                moreover have "P \<noteq> A"
                  using assms(4) col_trivial_1 by blast
                ultimately have "C P A CongA C1' PO A1 \<and> C A P CongA C1' A1 PO" 
                  by blast
                have "C A P CongA D B P" 
                proof -
                  {
                    assume "Bet C P D"
                    have "Bet A P B" 
                    proof (rule project_preserves_bet [of C P D _ A P A C], insert \<open>C \<midarrow> P \<midarrow> D\<close>)
                      show "C A Proj A P A C"
                        by (metis Par_def assms(4) grid_not_par par_col_project) 
                      show "P P Proj A P A C"
                        by (metis \<open>P \<noteq> A\<close> assms(4) col_trivial_2 par_id_1 project_trivial) 
                      show "D B Proj A P A C"
                        by (metis NCol_perm assms(2,4,5) grid_not_par 
                            pj_col_project pj_right_comm) 
                    qed
                    have "A B TS C D" 
                    proof -
                      have "\<not> Col C A B"
                        using \<open>A \<noteq> B\<close> assms(2,4) col2__eq by blast 
                      moreover have "\<not> Col D A B"
                        by (metis \<open>P \<noteq> B\<close> assms(2,3,4,5) calculation col_permutation_2 
                            colx sum_ar2 sum_exists sum_par_strict_a) 
                      moreover have "\<exists> T. Col T A B \<and> Bet C T D" 
                      proof -
                        have "Col P A B"
                          using assms(2) by auto 
                        moreover have "Bet C P D"
                          by (simp add: \<open>C \<midarrow> P \<midarrow> D\<close>) 
                        ultimately show ?thesis 
                          by fast
                      qed
                      ultimately show ?thesis
                        using TS_def by blast 
                    qed
                    hence "C A B CongA D B A \<longleftrightarrow> A C Par B D" 
                      using l12_21 by simp
                    have "A C Par B D \<Longrightarrow> C A P CongA D B P"
                      by (metis NCol_perm Par_cases TS_def \<open>A B TS C D\<close> \<open>P \<noteq> A\<close> \<open>P \<noteq> B\<close>
                          assms(2,3,4) not_par_not_col triangle_par) 
                    moreover have "B = D \<Longrightarrow> C A P CongA D B P"
                      using TS_def \<open>A B TS C D\<close> not_col_distincts by blast 
                    ultimately have "C A P CongA D B P"
                      using Pj_def assms(5) by blast 
                  }
                  moreover have "\<not> Bet C P D \<Longrightarrow> C A P CongA D B P"
                    by (metis Pj_def \<open>P \<noteq> B\<close> assms(2,3,4,5) between_trivial col_transitivity_2
                        conga_comm not_col_distincts not_par_not_col triangle_par) 
                  ultimately show ?thesis 
                    by blast
                qed

                have "A \<noteq> C"
                  using assms(4) col_trivial_2 by auto
                have "\<not> P A Par C A"
                  by (simp add: assms(4) grid_not_par_3 not_col_permutation_5)
                have "C P A CongA D P B"
                  by (metis Pj_def \<open>C A P CongA D B P\<close> assms(2,3,4,5) ncol_conga_ncol 
                      not_col_distincts not_col_permutation_2 not_col_permutation_3 
                      not_par_not_col par_comm triangle_par) 
                have "C1 \<noteq> C1'"
                  using \<open>\<not> Col PO C1 C1'\<close> col_trivial_2 by auto 
                have "PO \<noteq> C1'"
                  using \<open>\<not> Col PO C1 C1'\<close> col_trivial_3 by auto
                have "\<not> PO C1' Par C1 C1'"
                  by (simp add: \<open>\<not> Col PO C1 C1'\<close> grid_not_par_3) 
                have "\<not> PO C1 Par C1 C1'"
                  by (simp add: \<open>\<not> Col PO C1 C1'\<close> grid_not_par_1) 
                have "C1' PO A1 CongA D1' PO B1"
                proof (rule out2__conga)
                  show "PO Out D1' C1'"
                    using Out_cases \<open>PO Out C1' D1'\<close> by auto 
                  show "PO Out B1 A1"
                    using \<open>P \<noteq> A\<close> \<open>P \<noteq> B\<close> assms(6,7) length_out by auto 
                qed
                have "D1' PO B1 CongA D P B"
                  using \<open>C P A CongA D P B\<close> \<open>C1' PO A1 CongA D1' PO B1\<close>
                    \<open>Cong P A PO A1 \<and> (P \<noteq> A \<longrightarrow> C P A CongA C1' PO A1 \<and> C A P CongA C1' A1 PO)\<close>
                    \<open>P \<noteq> A\<close> conga_sym conga_trans by blast
                have "D1' \<noteq> B1 \<Longrightarrow> PO D1' B1 CongA P D B \<and> PO B1 D1' CongA P B D"
                  by (meson \<open>Cong PO D1 PO D1'\<close> \<open>D1' PO B1 CongA D P B\<close> assms(7,9) 
                      cong_transitivity l11_49 length_cong not_cong_3412) 
                moreover have "D1' \<noteq> B1"
                  by (metis Col_def \<open>C1' PO A1 CongA D1' PO B1\<close> \<open>PO A1 OS E' C1'\<close> col124__nos
                      grid_not_par_5 ncol_conga_ncol) 
                ultimately have "PO D1' B1 CongA P D B \<and> PO B1 D1' CongA P B D"
                  by simp
                have "C1' A1 PO CongA D1' B1 PO \<longleftrightarrow> A1 C1' Par B1 D1'" 
                proof (rule l12_22)
                  show "PO Out A1 B1"
                    using \<open>P \<noteq> A\<close> \<open>P \<noteq> B\<close> assms(6,7) length_out by auto 
                  show "PO A1 OS C1' D1'"
                    using \<open>PO A1 OS E' C1'\<close> \<open>PO Out C1' D1'\<close> col124__nos out_one_side by blast 
                qed
                moreover have "C1' A1 PO CongA D1' B1 PO" 
                proof (rule conga_trans [of _ _ _ D B P])
                  show "C1' A1 PO CongA D B P"
                    using \<open>C A P CongA D B P\<close> \<open>C P A CongA C1' PO A1 \<and> C A P CongA C1' A1 PO\<close> 
                      not_conga not_conga_sym by blast 
                  show "D B P CongA D1' B1 PO"
                    by (simp add: \<open>PO D1' B1 CongA P D B \<and> PO B1 D1' CongA P B D\<close> conga_comm
                        conga_sym) 
                qed
                ultimately have "A1 C1' Par B1 D1'" 
                  by blast
                have "Prod PO C1 C1' A1 D1 B1" 
                proof (unfold Prod_def, intro strip conjI, unfold Ar2_def, intro strip conjI)
                  show "\<not> Col PO C1 C1'"
                    by (simp add: \<open>\<not> Col PO C1 C1'\<close>) 
                  show "Col PO C1 A1"
                    by (simp add: \<open>PO Out A1 C1\<close> l6_6 out_col) 
                  show "Col PO C1 D1"
                    by (simp add: \<open>PO Out C1 D1\<close> out_col) 
                  show "Col PO C1 B1"
                    by (metis \<open>Col PO C1 A1\<close> \<open>\<not> Col PO A1 E'\<close> assms(6,7) col_trivial_3 
                        l6_16_1 length_Ar2 not_col_permutation_3 not_col_permutation_4) 
                  show "\<exists>B'. C1 C1' Pj D1 B' \<and> Col PO C1' B' \<and> C1' A1 Pj B' B1"
                    by (meson Pj_def \<open>A1 C1' Par B1 D1'\<close> \<open>C1 C1' Pj D1 D1'\<close> \<open>PO Out C1' D1'\<close>
                        out_col par_comm) 
                qed
                have "\<exists> Y. Prod PO E C1' A1 D1 Y \<and> Prod PO E C1' C1 B1 Y"
                proof (rule prod_x_axis_unit_change [of _ C1], insert assms(1))
                  show "Ar2p4 PO C1 C1' A1 D1 C1 B1"
                    by (metis Ar2_def Ar2p4_def Prod_def \<open>Prod PO C1 C1' A1 D1 B1\<close>
                        not_col_distincts) 
                  show "Col PO C1 E"
                    using Col_cases Col_def assms(8) between_trivial length_Ar2
                    by blast 
                  show "E \<noteq> PO"
                    using assms(1) by auto 
                  show "\<exists>X. Prod PO C1 C1' A1 D1 X \<and> Prod PO C1 C1' C1 B1 X" 
                    using Ar2p4_def \<open>Ar2p4 PO C1 C1' A1 D1 C1 B1\<close> \<open>Prod PO C1 C1' A1 D1 B1\<close>
                      prod_1_l by blast 
                qed
                hence "Prodg PO E E' C1 B1 AD"
                  by (metis Prodg_def \<open>Prod PO E E' A1 D1 AD\<close> \<open>\<not> Col PO E E'\<close>
                      prod_uniqueness prod_y_axis_change) 
              }
              moreover have "PO = M \<and> PO Midpoint D1 D1' \<Longrightarrow> Prodg PO E E' C1 B1 AD"
                using \<open>M Midpoint C1 C1'\<close> \<open>\<not> Col PO C1 C1'\<close> midpoint_col by auto 
              ultimately show "Prodg PO E E' C1 B1 AD"
                using Reflect_def by auto 
            }
          qed
        }
      qed
    }
    moreover have "\<not> Ar2 PO E E' A1 D1 D1 \<and> AD = PO \<Longrightarrow> Prodg PO E E' C1 B1 AD"
      by (meson Ar2_def Length_def \<open>\<not> Col PO E E'\<close> assms(6,9)) 
    ultimately show "Prodg PO E E' C1 B1 AD"
      by blast 
  }
qed

lemma length_existence:
  assumes "\<not> Col PO E E'"
  shows "\<exists> AB. Length PO E E' A B AB" 
proof -
  have "E \<noteq> PO"
    using assms col_trivial_1 by auto 
  obtain AB where "Bet PO E AB \<or> Bet PO AB E" and "Cong PO AB A B"
    using \<open>E \<noteq> PO\<close> segment_construction_2 by blast
  hence "AB = PO \<or> PO Out E AB" 
    by (simp add: Out_def \<open>E \<noteq> PO\<close>)
  moreover have "AB = PO \<Longrightarrow> ?thesis"
    using \<open>Cong PO AB A B\<close> \<open>E \<noteq> PO\<close> cong_diff_3 length_id by blast 
  moreover {
    assume "PO Out E AB"
    hence "Col PO E AB"
      by (simp add: out_col) 
    moreover have "LeP PO E E' PO AB"
      using \<open>Bet PO E AB \<or> Bet PO AB E\<close> assms ps_le by blast 
    ultimately have ?thesis
      using Length_def \<open>Cong PO AB A B\<close> \<open>E \<noteq> PO\<close> by auto 
  }
  ultimately show ?thesis 
    by blast
qed

(** Known as Euklid *)
lemma l15_7:
  assumes "PO \<noteq> E"
    and "Per A C B"
    and "H PerpAt C H A B"
    and "Length PO E E' A B AB"
    and "Length PO E E' A C AC"
    and "Length PO E E' A H AH"
  shows "Prod PO E E' AC AC AC2 \<longleftrightarrow> Prod PO E E' AB AH AC2" 
proof (cases "AB = PO")
  {
    assume "AB = PO"
    hence "A = B"
      using assms(4) length_id by auto 
    hence "C \<noteq> H \<and> A \<noteq> A" 
      using perp_in_distinct assms(3) by auto 
    thus "Prod PO E E' AC AC AC2 \<longleftrightarrow> Prod PO E E' AB AH AC2" 
      by simp
  }
  {
    assume "AB \<noteq> PO"
    have "LtP PO E E' PO AB \<Longrightarrow> \<not> Col PO E E' \<and> Col PO E AB"
      using Ar2_def ltP_ar2 by blast 
    moreover have "PO = AB \<Longrightarrow> \<not> Col PO E E' \<and> Col PO E AB"
      using \<open>AB \<noteq> PO\<close> by auto 
    ultimately have "\<not> Col PO E E' \<and> Col PO E AB" 
      using assms(4) length_Ar2 by blast 
    show "Prod PO E E' AC AC AC2 \<longleftrightarrow> Prod PO E E' AB AH AC2" 
    proof (cases "H = A")
      show "H = A \<Longrightarrow> (Prod PO E E' AC AC AC2) = (Prod PO E E' AB AH AC2)"
        using assms(2,3) l11_47 by blast 
      {
        assume "H \<noteq> A"
        hence "C \<noteq> A"
          using assms(3) l8_8 perp_in_per_1 by blast 
        obtain C' where "Bet A H C' \<or> Bet A C' H" and "Cong A C' A C"
          using \<open>H \<noteq> A\<close> segment_construction_2 by blast
        have "A Out H C'"
          by (metis Out_def \<open>(A \<midarrow> H \<midarrow> C') \<or> (A \<midarrow> C' \<midarrow> H)\<close> \<open>C \<noteq> A\<close> \<open>Cong A C' A C\<close> \<open>H \<noteq> A\<close>
              cong_reverse_identity) 
        obtain H' where "Bet A C H' \<or> Bet A H' C" and "Cong A H' A H"
          using \<open>C \<noteq> A\<close> segment_construction_2 by blast 
        have "H \<noteq> C"
          using assms(3) perp_in_distinct by blast 
        moreover have "Cong H C H' C' \<and> (H \<noteq> C \<longrightarrow> A H C CongA A H' C' \<and> A C H CongA A C' H')" 
        proof (rule l11_49)
          show "H A C CongA H' A C'"
            by (metis Out_cases \<open>A Out H C'\<close> \<open>(A \<midarrow> C \<midarrow> H') \<or> (A \<midarrow> H' \<midarrow> C)\<close> \<open>C \<noteq> A\<close> 
                \<open>Cong A H' A H\<close> \<open>H \<noteq> A\<close> bet_out
                between_cong between_trivial2 conga_left_comm out2__conga) 
          show "Cong A H A H'"
            using \<open>Cong A H' A H\<close> not_cong_3412 by blast 
          show "Cong A C A C'"
            by (simp add: \<open>Cong A C' A C\<close> cong_symmetry) 
        qed
        ultimately have "A H C CongA A H' C' \<and> A C H CongA A C' H'"  
          by blast
        have "A H Perp H C"
          by (metis Per_cases \<open>H \<noteq> A\<close> \<open>H \<noteq> C\<close> assms(3) per_perp perp_in_per_1) 
        hence "H PerpAt A H H C"
          using l8_14_2_1b_bis not_col_distincts by blast 
        hence "Per A H C"
          by (simp add: perp_in_per) 
        have "Per A H' C'"
          using \<open>A H C CongA A H' C' \<and> A C H CongA A C' H'\<close> \<open>Per A H C\<close> l11_17 by blast 
        have "C B Par H' C'" 
        proof (rule l12_9_2D [of _ _ A C])
          show "C B Perp A C"
            by (metis Perp_cases \<open>C \<noteq> A\<close> \<open>H \<noteq> C\<close> assms(2,3) per_perp perp_in_id) 
          show "H' C' Perp A C"
            by (metis Col_def Per_perm Perp_cases \<open>A H C CongA A H' C' \<and> A C H CongA A C' H'\<close> 
                \<open>A H Perp H C\<close> \<open>(A \<midarrow> C \<midarrow> H') \<or> (A \<midarrow> H' \<midarrow> C)\<close> \<open>Per A H' C'\<close> 
                bet_conga__bet between_symmetry between_trivial col_per_perp
                not_conga_sym perp_not_col2) 
        qed
        obtain AH' where "Length PO E E' A H' AH'"
          using \<open>\<not> Col PO E E' \<and> Col PO E AB\<close> length_existence by presburger
        obtain AC' where "Length PO E E' A C' AC'"
          using \<open>\<not> Col PO E E' \<and> Col PO E AB\<close> length_existence by blast
        obtain P where "Prod PO E E' AC' AC P"
          by (metis \<open>Length PO E E' A C' AC'\<close> \<open>\<not> Col PO E E' \<and> Col PO E AB\<close> assms(5) 
              col_trivial_3 length_Ar2 prod_exists)
        have "C H Perp A B"
          using assms(3) perp_in_perp by auto
        have "Prodg PO E E' AH' AB P" 
        proof (rule thales [of _ _ A C' B H' C _ AC' _ _ AC])
          show "PO \<noteq> E"
            using assms(1) by blast 
          show "Col A C' B"
            by (metis Col_def Perp_cases Perp_in_cases \<open>A Out H C'\<close> \<open>C H Perp A B\<close> assms(2,3)
                col_out2_col out_bet__out out_trivial perp_in_col perp_not_col2
                perp_per_bet) 
          show "Col A H' C"
            using Col_def \<open>(A \<midarrow> C \<midarrow> H') \<or> (A \<midarrow> H' \<midarrow> C)\<close> between_symmetry by blast 
          show "\<not> Col A C' H'"
            by (metis \<open>A H C CongA A H' C' \<and> A C H CongA A C' H'\<close> \<open>Per A H' C'\<close> conga_diff45
                conga_diff56 l8_9 not_col_permutation_1 not_col_permutation_3) 
          show "C' H' Pj B C"
            using Par_cases Pj_def \<open>C B Par H' C'\<close> by blast 
          show "Length PO E E' A C' AC'"
            using \<open>Length PO E E' A C' AC'\<close> by auto 
          show "Length PO E E' A B AB"
            by (simp add: assms(4)) 
          show "Length PO E E' A H' AH'"
            by (simp add: \<open>Length PO E E' A H' AH'\<close>) 
          show "Length PO E E' A C AC"
            by (simp add: assms(5)) 
          show "Prodg PO E E' AC' AC P"
            by (simp add: Prodg_def \<open>Prod PO E E' AC' AC P\<close>) 
        qed
        hence "Prod PO E E' AH' AB P"
          by (metis Ar2_def Prodg_def \<open>Length PO E E' A H' AH'\<close> 
              \<open>\<not> Col PO E E' \<and> Col PO E AB\<close> col_trivial_3 length_Ar2) 
        have "Length PO E E' A H' AH"
          using \<open>Cong A H' A H\<close> assms(6) length_eq_cong_2 not_cong_3412 by blast
        have "Length PO E E' A C' AC"
          using Cong_cases \<open>Cong A C' A C\<close> assms(5) length_eq_cong_2 by blast
        hence "(Prod PO E E' AC AC AC2) \<longrightarrow> (Prod PO E E' AB AH AC2)"
          by (metis \<open>Length PO E E' A C' AC'\<close> \<open>Length PO E E' A H' AH'\<close> 
              \<open>Length PO E E' A H' AH\<close> \<open>Prod PO E E' AC' AC P\<close>
              \<open>Prod PO E E' AH' AB P\<close> \<open>\<not> Col PO E E' \<and> Col PO E AB\<close> length_uniqueness
              prod_sym prod_uniqueness) 
        moreover have "(Prod PO E E' AB AH AC2) \<longrightarrow> (Prod PO E E' AC AC AC2)"
          by (metis \<open>Length PO E E' A C' AC'\<close> \<open>Length PO E E' A C' AC\<close>
              \<open>Length PO E E' A H' AH'\<close> \<open>Length PO E E' A H' AH\<close> \<open>Prod PO E E' AC' AC P\<close>
              \<open>Prod PO E E' AH' AB P\<close> \<open>\<not> Col PO E E' \<and> Col PO E AB\<close> length_uniqueness
              prod_sym prod_uniqueness) 
        ultimately show "(Prod PO E E' AC AC AC2) = (Prod PO E E' AB AH AC2)" 
          by blast
      }
    qed
  }
qed

lemma l15_7_1:
  assumes "PO \<noteq> E"
    and "Per A C B"
    and "H PerpAt C H A B"
    and "Length PO E E' A B AB"
    and "Length PO E E' A C AC"
    and "Length PO E E' A H AH"
    and "Prod PO E E' AC AC AC2"
  shows "Prod PO E E' AB AH AC2" 
  using l15_7 [of PO E A C B H E' AB AC AH AC2] assms(1,2,3,4,5,6,7) by blast

lemma l15_7_2:
  assumes "PO \<noteq> E"
    and "Per A C B"
    and "H PerpAt C H A B"
    and "Length PO E E' A B AB"
    and "Length PO E E' A C AC"
    and "Length PO E E' A H AH"
    and "Prod PO E E' AB AH AC2"
  shows "Prod PO E E' AC AC AC2" 
  using l15_7 [of PO E A C B H E' AB AC AH AC2] assms(1,2,3,4,5,6,7) by blast

lemma length_sym:
  assumes "Length PO E E' A B AB"
  shows "Length PO E E' B A AB"
  using assms cong_pseudo_reflexivity length_eq_cong_2 by blast 

lemma pythagoras:
  assumes "PO \<noteq> E"
    and "Per A C B"
    and "Length PO E E' A B AB"
    and "Length PO E E' A C AC"
    and "Length PO E E' B C BC"
    and "Prod PO E E' AC AC AC2"
    and "Prod PO E E' BC BC BC2"
    and "Prod PO E E' AB AB AB2"
  shows "Sum PO E E' AC2 BC2 AB2"
proof (cases "Col A C B")
  {
    assume "Col A C B"
    moreover have "A = C \<longrightarrow> Sum PO E E' AC2 BC2 AB2"
      by (metis Ar2_def Prod_def assms(3,4,5,6,7,8) cong_reverse_identity length_cong
          length_sym length_uniqueness prod_O_r_eq prod_uniqueness sum_O_B) 
    moreover have "B = C \<longrightarrow> Sum PO E E' AC2 BC2 AB2"
      by (metis Ar2_def Prod_def assms(1,3,4,5,6,7,8) length_id length_uniqueness
          prod_O_r_eq prod_uniqueness sum_A_O) 
    ultimately show "Sum PO E E' AC2 BC2 AB2"
      using assms(2) per_not_col by force 
  }
  {
    assume "\<not> Col A C B"
    then obtain P where "Col A B P" and "A B Perp C P"
      using col_permutation_5 l8_18_existence by blast 
    hence "P PerpAt A B C P"
      by (simp add: l8_15_1) 
    obtain AP where "Length PO E E' A P AP"
      by (metis \<open>\<not> Col A C B\<close> assms(3,5) col_trivial_1 length_existence length_id_1
          length_not_col_null) 
    obtain BP where "Length PO E E' B P BP"
      by (metis \<open>Length PO E E' A P AP\<close> assms(3) length_Ar2
          length_existence length_id_1)
    have "Sum PO E E' AP BP AB" 
      using triangular_equality_bis [of PO E E']
      by (metis Perp_in_cases \<open>Length PO E E' A P AP\<close>
          \<open>Length PO E E' B P BP\<close> \<open>P PerpAt A B C P\<close> \<open>\<not> Col A C B\<close>
          assms(1,2,3) grid_not_par length_sym perp_per_bet
          triangular_equality_bis)
    moreover have "Prod PO E E' AB AP AC2"
      using Perp_in_cases \<open>Length PO E E' A P AP\<close> \<open>P PerpAt A B C P\<close>
        assms(1,2,3,4,6) l15_7 by blast
    moreover have "Prod PO E E' AB BP BC2"
      by (meson Per_cases Perp_in_cases \<open>Length PO E E' B P BP\<close>
          \<open>P PerpAt A B C P\<close> assms(1,2,3,5,7) l15_7 length_sym)
    ultimately show "Sum PO E E' AC2 BC2 AB2"
      using assms(8) distr_l by blast 
  }
qed

lemma is_length_exists:
  assumes "\<not> Col PO E E'"
  shows "\<exists> XY. IsLength PO E E' X Y XY" 
proof(cases "X = Y")
  {
    assume "X = Y"
    hence "IsLength PO E E' X Y PO"
      by (simp add: IsLength_def length_id) 
    thus "\<exists> XY. IsLength PO E E' X Y XY"
      by auto 
  }
  show "X \<noteq> Y \<Longrightarrow> \<exists>XY. IsLength PO E E' X Y XY" 
    using length_existence IsLength_def assms by blast
qed

(********************************************************)

lemma lt_to_ltp:
  assumes "Length PO E E' A B L"
    and "Length PO E E' C D M" 
    and "A B Lt C D"
  shows "LtP PO E E' L M"
  by (metis LeP_def Lt_def assms(1,2,3) length_eq_cong_1 length_leP_le_2) 

lemma ltp_to_lep:
  assumes "LtP PO E E' L M"
  shows "LeP PO E E' L M"
  by (simp add: LeP_def assms) 

lemma ltp_to_lt:
  assumes "Length PO E E' A B L"
    and "Length PO E E' C D M" 
    and "LtP PO E E' L M"
  shows "A B Lt C D" 
proof -
  have "LeP PO E E' L M"
    by (simp add: LeP_def assms(3)) 
  have "A B Le C D"
    using \<open>LeP PO E E' L M\<close> assms(1,2) length_leP_le_1 by auto 
  moreover {
    assume "Cong A B C D" 
    hence "Length PO E E' C D L"
      using assms(1) length_eq_cong_2 by blast 
    hence "L = M" 
      using length_uniqueness [of PO E E' C D L M] assms(2) by auto
    hence False
      using assms(3) ltP_neq by auto 
  }
  ultimately show ?thesis
    using Lt_def by auto 
qed

lemma prod_col:
  assumes "Ar2 PO E E' A B A"
    and "Prod PO E E' A B AB"
  shows "Col PO E AB"
  using Ar2_def Prod_def assms(2) by auto 

lemma square_increase_strict:
  assumes "Ar2 PO E E' A B A"
    and "Ps PO E A"
    and "Ps PO E B" 
    and "LtP PO E E' A B" 
    and "Prod PO E E' A A A2"
    and "Prod PO E E' B B B2" 
  shows "LtP PO E E' A2 B2" 
proof -
  obtain BmA where "Diff PO E E' B A BmA"
    using LtP_def assms(4) by blast
  obtain BpA where "Sum PO E E' B A BpA"
    by (meson \<open>Diff PO E E' B A BmA\<close> diff_ar2 sum3_def sum3_exists)
  obtain B2mA2 where "Diff PO E E' B2 A2 B2mA2"
    by (metis Ar2_def assms(1,5,6) diff_exists prod_col)
  obtain F where "Prod PO E E' BpA BmA F"
    by (metis Ar2_def Ps_def \<open>Diff PO E E' B A BmA\<close> \<open>Sum PO E E' B A BpA\<close>
        assms(1,2,3,4) col_permutation_5 lt_diff_ps out_col prod_exists
        sum_pos_pos)
  thus ?thesis
    by (metis LtP_def \<open>Diff PO E E' B A BmA\<close> \<open>Diff PO E E' B2 A2 B2mA2\<close>
        \<open>Sum PO E E' B A BpA\<close> assms(2,3,4,5,6) diff_of_squares lt_diff_ps prod_pos_pos
        sum_pos_pos) 
qed

lemma square_increase:
  assumes "Ar2 PO E E' A B A"
    and "Ps PO E A"
    and "Ps PO E B" 
    and "LeP PO E E' A B" 
    and "Prod PO E E' A A A2"
    and "Prod PO E E' B B B2" 
  shows "LeP PO E E' A2 B2"
  by (metis Ar2_def LeP_def assms(1,2,3,4,5,6) prod_uniqueness
      square_increase_strict) 

lemma signeq__prod_pos:
  assumes "SignEq PO E A B"
    and "Prod PO E E' A B C"
  shows "Ps PO E C" 
proof -
  have "Ps PO E A \<and> Ps PO E B \<Longrightarrow> Ps PO E C"
    using assms(2) prod_pos_pos by blast 
  moreover {
    assume "Ng PO E A" and "Ng PO E B"
    obtain B' where "B B' Proj PO E' E E'"
      using Prodp_def assms(2) prod_to_prodp by blast 
    have "Bet B' PO E'"
    proof -
      have "Bet B PO E"
        using Ng_def \<open>Ng PO E B\<close> by auto 
      moreover have "PO PO Proj PO E' E E'"
        by (metis Proj_def \<open>B B' Proj PO E' E E'\<close> not_col_distincts) 
      moreover have "E E' Proj PO E' E E'"
        by (metis Proj_def calculation(2) not_col_distincts par_reflexivity) 
      ultimately show ?thesis
        using \<open>B B' Proj PO E' E E'\<close> project_preserves_bet by blast 
    qed
    moreover have "Bet A PO C"
    proof (rule project_preserves_bet [of E' PO B' _ PO E A E'])
      show "E' \<midarrow> PO \<midarrow> B'"
        using Bet_cases calculation by blast 
      show "E' A Proj PO E A E'" 
      proof -
        have "PO \<noteq> E"
          using Ng_def \<open>Ng PO E A\<close> by force 
        moreover have "A \<noteq> E'"
          using Ar2_def Prod_def assms(2) by auto 
        moreover have "\<not> PO E Par A E'"
          by (metis Ar2_def Prod_def assms(2) col_trivial_3 not_strict_par2) 
        moreover have "E' A Par A E' \<or> E' = A"
          using Par_cases par_reflexivity by blast 
        ultimately show ?thesis
          using Col_def Ng_def \<open>Ng PO E A\<close> par_col_project by force 
      qed
      show "PO PO Proj PO E A E'"
        by (metis NCol_perm Proj_def \<open>E' A Proj PO E A E'\<close> col_trivial_1) 
      show "B' C Proj PO E A E'"
        using Prodp_def \<open>B B' Proj PO E' E E'\<close> assms(2) prod_to_prodp project_uniqueness
        by blast 
    qed
    ultimately have "PO Out C E"
      using Ng_def Out_def \<open>Ng PO E A\<close> \<open>Ng PO E B\<close> assms(2) l5_2 prod_null
      by fastforce 
    hence "Ps PO E C"
      by (simp add: Ps_def) 
  }
  ultimately show ?thesis
    using SignEq_def assms(1) by blast 
qed

lemma pos_neg__prod_neg:
  assumes "Ps PO E A" 
    and "Ng PO E B"
    and "Prod PO E E' A B C"
  shows "Ng PO E C" 
proof -
  obtain B' where "B B' Proj PO E' E E'" and "B' C Proj PO E A E'"
    using Prodp_def assms(3) prod_to_prodp by blast
  show ?thesis 
  proof (unfold Ng_def, intro conjI)
    show "C \<noteq> PO"
      by (metis Ng_def O_not_positive assms(1,2,3) prod_null) 
    show "E \<noteq> PO"
      using Ng_def assms(2) by auto 
    show "Bet C PO E" 
    proof -
      have "Bet A PO C"
      proof (rule project_preserves_bet [of E' PO B' _ PO E A E'])
        have "Bet B' PO E'"
        proof (rule project_preserves_bet [of B PO E _ PO E' E E'])
          show "B \<midarrow> PO \<midarrow> E"
            using Ng_def assms(2) by auto 
          show "B B' Proj PO E' E E'"
            by (simp add: \<open>B B' Proj PO E' E E'\<close>) 
          show "PO PO Proj PO E' E E'"
            using Proj_def \<open>B B' Proj PO E' E E'\<close> col_trivial_3 by presburger 
          show "E E' Proj PO E' E E'"
            by (metis NCol_perm Proj_def \<open>PO PO Proj PO E' E E'\<close> col_trivial_3
                par_reflexivity) 
        qed
        thus "E' \<midarrow> PO \<midarrow> B'"
          using Bet_perm by blast 
        show "E' A Proj PO E A E'"
          by (metis Par_cases Prodp_def Proj_def assms(3) par_reflexivity
              prod_to_prodp) 
        show "PO PO Proj PO E A E'"
          by (metis NCol_perm Proj_def \<open>E' A Proj PO E A E'\<close> col_trivial_1) 
        show "B' C Proj PO E A E'"
          by (simp add: \<open>B' C Proj PO E A E'\<close>) 
      qed
      thus ?thesis
        using Bet_cases Ps_def assms(1) bet_out__bet by blast 
    qed
  qed
qed

lemma not_signEq_prod_neg:
  assumes "A \<noteq> PO"
    and "B \<noteq> PO"
    and "\<not> SignEq PO E A B"
    and "Prod PO E E' A B C"
  shows "Ng PO E C"
  by (metis Ar2_def Prod_def SignEq_def assms(1,2,3,4) col_pos_or_neg
      pos_neg__prod_neg prod_1_r prod_O_r_eq prod_sym) 

lemma prod_pos__signeq:
  assumes "A \<noteq> PO"
    and "B \<noteq> PO"
    and "Prod PO E E' A B C"
    and "Ps PO E C"
  shows "SignEq PO E A B"
  using assms(1,2,3,4) neg_not_pos not_signEq_prod_neg by blast 

lemma prod_ng___not_signeq:
  assumes (* "A \<noteq> PO"
and "B \<noteq> PO"
and*) "Prod PO E E' A B C"
    and "Ng PO E C"
  shows "\<not> SignEq PO E A B"
  using assms(1,2) neg_not_pos signeq__prod_pos by blast 

lemma ltp__diff_pos:
  assumes "LtP PO E E' A B"
    and "Diff PO E E' B A D"
  shows "Ps PO E D"
  using assms(1,2) lt_diff_ps by auto

lemma diff_pos__ltp: 
  assumes "Diff PO E E' B A D"
    and "Ps PO E D"
  shows "LtP PO E E' A B"
  using LtP_def assms(1,2) by blast 

lemma square_increase_rev:
  assumes "Ps PO E A"
    and "Ps PO E B"
    and "LtP PO E E' A2 B2" 
    and "Prod PO E E' A A A2"
    and "Prod PO E E' B B B2" 
  shows "LtP PO E E' A B"
  by (metis Ar2_def LeP_def Prod_def assms(1,2,3,4,5) col_2_le_or_ge leP_asym
      ltP_neq square_increase) 

lemma ltp__ltps: 
  assumes "LtP PO E E' A B"
  shows "LtPs PO E E' A B"
  using LtP_def LtPs_def assms diff_sum by blast 

lemma ltps__ltp: 
  assumes "LtPs PO E E' A B"
  shows "LtP PO E E' A B"
  using LtPs_def assms ltP_sum_pos by blast 

lemma ltp__lep_neq:
  assumes "LtP PO E E' A B"
  shows "LeP PO E E' A B \<and> A \<noteq> B"
  using assms ltP_neq ltp_to_lep by auto 

lemma lep_neq__ltp:
  assumes "LeP PO E E' A B"
    and "A \<noteq> B"
  shows "LtP PO E E' A B"
  using LeP_def assms(1,2) by force 

lemma sum_preserves_ltp:
  assumes "LtP PO E E' A B"
    and "Sum PO E E' A C AC"
    and "Sum PO E E' B C BC"
  shows "LtP PO E E' AC BC"
  by (metis Ar2_def assms(1,2,3) compatibility_of_sum_with_order lep_neq__ltp
      ltP_ar2 ltP_neq ltp_to_lep sum_uniquenessA) 

lemma sum_preserves_lep: 
  assumes "LeP PO E E' A B"
    and "Sum PO E E' A C AC"
    and "Sum PO E E' B C BC"
  shows "LeP PO E E' AC BC"
  using assms(1,2,3) compatibility_of_sum_with_order by blast 

lemma sum_preserves_ltp_rev:
  assumes "Sum PO E E' A C AC"
    and "Sum PO E E' B C BC"
    and "LtP PO E E' AC BC" 
  shows "LtP PO E E' A B"
  by (metis Ar2_def assms(1,2,3) col_2_le_or_ge leP_asym lep_neq__ltp ltP_neq
      ltp_to_lep sum_ar2 sum_preserves_lep) 

lemma sum_preserves_lep_rev:
  assumes "Sum PO E E' A C AC"
    and "Sum PO E E' B C BC"
    and "LeP PO E E' AC BC"
  shows "LeP PO E E' A B"
  by (metis Ar2_def Sum_def assms(1,2,3) col_2_le_or_ge
      compatibility_of_sum_with_order leP_asym sum_uniquenessA)

lemma cong2_lea__le:
  assumes "Cong A B D E"
    and "Cong A C D F"
    and "F D E LeA C A B"
  shows "E F Le B C" 
proof -
  have "F D E LtA C A B \<or> F D E CongA C A B"
    using LtA_def assms(3) by auto 
  moreover have "F D E LtA C A B  \<Longrightarrow> E F Le B C"
    using Lt_def assms(1,2) t18_18 by blast 
  moreover have "F D E CongA C A B \<Longrightarrow> E F Le B C"
    by (meson assms(1,2) cong2_conga_cong cong_4321 cong__le cong_symmetry) 
  ultimately show ?thesis 
    by blast
qed

lemma lea_out_lea:
  assumes "B Out A A'"
    and "B Out C C'"
    and "E Out D D'"
    and "E Out F F'"
    and "A B C LeA D E F"
  shows "A' B C' LeA D' E F'"
  using assms(1,2,3,4,5) lea_out4__lea by blast 

lemma lta_out_lta: 
  assumes "B Out A A'"
    and "B Out C C'"
    and "E Out D D'"
    and "E Out F F'"
    and "A B C LtA D E F"
  shows "A' B C' LtA D' E F'"
  by (smt (verit) Out_def assms(1,2,3,4,5) lea_out_lea lta__nlea
      nlta__lea)

lemma pythagoras_obtuse:
  assumes "PO \<noteq> E"
    and "Obtuse A C B"
    and "Length PO E E' A B AB"
    and "Length PO E E' A C AC"
    and "Length PO E E' B C BC"
    and "Prod PO E E' AC AC AC2"
    and "Prod PO E E' BC BC BC2"
    and "Prod PO E E' AB AB AB2"
    and "Sum PO E E' AC2 BC2 S2"
  shows "LtP PO E E' S2 AB2" 
proof -
  obtain A' B' C' where "Per A' B' C'" and "A' B' C' LtA A C B"
    using Obtuse_def assms(2) by blast 
  obtain AA where "B' Out AA A'" and "Cong B' AA C A"
    by (metis \<open>A' B' C' LtA A C B\<close> l6_11_existence lta_distincts) 
  obtain CC where "B' Out CC C'" and "Cong B' CC C B"
    by (metis \<open>A' B' C' LtA A C B\<close> l6_11_existence lta_distincts) 
  have "AA CC Lt A B" 
  proof (rule t18_18 [of C A B' AA B CC])
    show "Cong C A B' AA"
      using Cong_perm \<open>Cong B' AA C A\<close> by blast 
    show "Cong C B B' CC"
      using \<open>Cong B' CC C B\<close> not_cong_3412 by blast 
    show "CC B' AA LtA B C A"
      by (smt (verit, best) Out_cases \<open>A' B' C' LtA A C B\<close> \<open>B' Out AA A'\<close> \<open>B' Out CC C'\<close> 
          lta_comm lta_distincts lta_out_lta out_trivial) 
  qed
  obtain S1 where "Length PO E E' AA CC S1"
    by (metis \<open>A' B' C' LtA A C B\<close> assms(3) cong_identity length_Ar2 length_cong 
        length_existence lta_distincts)
  then obtain SS where "Prod PO E E' S1 S1 SS" 
    using prod_exists [of PO E E' S1 S1] assms(4,6) col_trivial_3 length_Ar2 by blast 
  have "B' \<noteq> C'"
    using Out_def \<open>B' Out CC C'\<close> by force 
  hence "Per A' B' CC" 
    using per_col [of B' C' A' CC] \<open>B' Out CC C'\<close> \<open>Per A' B' C'\<close> col_permutation_5 
      out_col by blast
  have "B' \<noteq> A'"
    using Out_def \<open>B' Out AA A'\<close> by blast 
  hence "Per CC B' AA" 
    using per_col [of B' A' CC AA] Out_cases \<open>B' Out AA A'\<close> \<open>Per A' B' CC\<close> l8_2 out_col by blast 
  have "Sum PO E E' AC2 BC2 SS" 
    using pythagoras [of _ _ AA B' CC _ S1 AC BC] by (meson Per_cases \<open>Cong B' AA C A\<close> 
        \<open>Cong B' CC C B\<close> \<open>Length PO E E' AA CC S1\<close> \<open>Per CC B' AA\<close>
        \<open>Prod PO E E' S1 S1 SS\<close> assms(1,4,5,6,7) cong_4321 length_eq_cong_2)
  have "S2 = SS"
    using \<open>Sum PO E E' AC2 BC2 SS\<close> assms(9) sum_stable by blast
  moreover have "LtP PO E E' S1 AB"
    using lt_to_ltp [of PO E E' AA CC S1 A B AB]
    using \<open>AA CC Lt A B\<close> \<open>Length PO E E' AA CC S1\<close> assms(3) by blast
  moreover have "Ps PO E S1"
    by (metis \<open>A' B' C' LtA A C B\<close> \<open>Length PO E E' AA CC S1\<close> \<open>Prod PO E E' S1 S1 SS\<close> 
        assms(4,5,6,7,9) calculation(1) length_id_1 length_pos lep_neq__ltp ltP_pos 
        lta_distincts prod_O_l_eq square_pos sum_pos_pos) 
  ultimately show ?thesis 
    using square_increase_strict [of PO E E' S1 AB S2 AB2]
    by (metis SignEq_def \<open>Prod PO E E' S1 S1 SS\<close> assms(3,8)
        length_pos lep_neq__ltp ltP_ar2 ltP_neg ltP_pos pos_neg__prod_neg prod_ng___not_signeq) 
qed

lemma pythagoras_obtuse_or_per:
  assumes "PO \<noteq> E"
    and "Obtuse A C B \<or> Per A C B"
    and "Length PO E E' A B AB"
    and "Length PO E E' A C AC"
    and "Length PO E E' B C BC"
    and "Prod PO E E' AC AC AC2"
    and "Prod PO E E' BC BC BC2"
    and "Prod PO E E' AB AB AB2"
    and "Sum PO E E' AC2 BC2 S2"
  shows "LeP PO E E' S2 AB2" 
proof -
  have "Obtuse A C B \<Longrightarrow> LeP PO E E' S2 AB2"
    using assms(1,3,4,5,6,7,8,9) ltp_to_lep pythagoras_obtuse by blast
  moreover have  "Per A C B \<Longrightarrow> LeP PO E E' S2 AB2"
    by (meson assms(1,3,4,5,6,7,8,9) leP_refl pythagoras sum_preserves_lep) 
  ultimately show ?thesis
    using assms(2) by blast
qed

lemma pythagoras_acute:
  assumes "PO \<noteq> E"
    and "Acute A C B"
    and "Length PO E E' A B AB"
    and "Length PO E E' A C AC"
    and "Length PO E E' B C BC"
    and "Prod PO E E' AC AC AC2"
    and "Prod PO E E' BC BC BC2"
    and "Prod PO E E' AB AB AB2"
    and "Sum PO E E' AC2 BC2 S2"
  shows "LtP PO E E' AB2 S2"
proof (cases "A = B")
  show "A = B \<Longrightarrow> LtP PO E E' AB2 S2"
    by (smt (verit, ccfv_SIG) LtPs_def acute_distincts assms(1,2,3,4,5,6,7,8,9) between_trivial2
        distr_r length_Ar2 length_id_1 ltps__ltp prod_0_r prod_sym square_pos sum_A_null 
        sum_assoc_2 sum_pos_pos triangular_equality_bis) 
  {
    assume "A \<noteq> B"
    obtain A' B' C' where "Per A' B' C'" and "A C B LtA A' B' C'"
      using Acute_def assms(2) by blast 
    have "A' \<noteq> B'" 
      using \<open>A C B LtA A' B' C'\<close> lta_distincts by blast
    then obtain AA where "B' Out AA A'" and "Cong B' AA C A"
      by (metis assms(2) between_trivial2 flat_not_acute l6_11_existence) 
    have "C' \<noteq> B'"
      using \<open>A C B LtA A' B' C'\<close> lta_distincts by blast 
    then obtain CC where "B' Out CC C'" and "Cong B' CC C B"
      by (metis Out_def \<open>C' \<noteq> B'\<close> acute_col__out assms(2) l6_11_existence not_col_distincts) 
    obtain S1 where "Length PO E E' AA CC S1"
      using Ar2_def assms(9) length_existence sum_ar2 by presburger
    obtain SS where "Prod PO E E' S1 S1 SS"
      using Ar2_def Length_def Prod_def \<open>Length PO E E' AA CC S1\<close> assms(7) prod_exists
      by presburger
    have "Per A' B' CC" 
    proof (rule per_col [of B' C' A' CC ], insert \<open>Per A' B' C'\<close>)
      show "B' \<noteq> C'"
        using \<open>C' \<noteq> B'\<close> by auto 
      show "Col B' C' CC"
        using Col_cases \<open>B' Out CC C'\<close> out_col by blast 
    qed
    have "Per CC B' AA"
      using per_col [of _ A'] by (metis NCol_perm \<open>A' \<noteq> B'\<close> \<open>B' Out AA A'\<close> 
          \<open>Per A' B' CC\<close> l8_2 out_col)
    hence "A B Lt AA CC" 
      using t18_18 [of B' AA C A CC B] by (metis Out_def \<open>B' Out AA A'\<close> \<open>B' Out CC C'\<close> 
          \<open>Cong B' AA C A\<close> \<open>Cong B' CC C B\<close>  acute_per__lta acute_sym assms(2))
    hence "LtP PO E E' AB S1" 
      using lt_to_ltp [of PO E E' A B AB AA CC S1] \<open>Length PO E E' AA CC S1\<close> assms(3) by linarith 
    show "LtP PO E E' AB2 S2"
    proof (rule square_increase_strict [of PO E E' AB S1 AB2 S2], insert 
        \<open>LtP PO E E' AB S1\<close> assms(8))
      show "Ar2 PO E E' AB S1 AB"
        by (simp add: \<open>LtP PO E E' AB S1\<close> ltP_ar2) 
      show "Ps PO E AB"
        by (metis \<open>A \<noteq> B\<close> assms(3) between_trivial2 length_out length_pos lep_neq__ltp ltP_pos
            not_bet_and_out) 
      show "Ps PO E S1"
        by (metis \<open>A B Lt AA CC\<close> \<open>Length PO E E' AA CC S1\<close> length_Ps length_id lt_diff)
      have "S2 = SS" 
      proof (rule sum_uniqueness [of PO E E' AC2 BC2 S2 SS], insert assms(9))
        show "\<not> Col PO E E'"
          using Ar2_def \<open>Ar2 PO E E' AB S1 AB\<close> by blast 
        show "Sum PO E E' AC2 BC2 SS" 
          using pythagoras [of _ _ AA B' CC _ S1 AC BC]
          by (meson Per_cases \<open>Cong B' AA C A\<close> \<open>Cong B' CC C B\<close> 
              \<open>Length PO E E' AA CC S1\<close> \<open>Per CC B' AA\<close>
              \<open>Prod PO E E' S1 S1 SS\<close> assms(1,4,5,6,7) cong_4321 length_eq_cong_2) 
      qed
      thus "Prod PO E E' S1 S1 S2"
        by (simp add: \<open>Prod PO E E' S1 S1 SS\<close>) 
    qed
  }
qed

lemma pyth_context:
  assumes "\<not> Col PO E E'"
  shows "\<exists> AB BC AC AB2 BC2 AC2 SS. Col PO E AB \<and> Col PO E BC \<and> Col PO E AC \<and> 
                                    Col PO E AB2 \<and> Col PO E BC2 \<and> Col PO E AC2 \<and>  
                                    Length PO E E' A B AB \<and> Length PO E E' B C BC \<and> 
                                    Length PO E E' A C AC \<and> Prod PO E E' AB AB AB2 \<and> 
                                    Prod PO E E' BC BC BC2 \<and> Prod PO E E' AC AC AC2 \<and> 
                                    Sum PO E E' AB2 BC2 SS" 
proof -
  obtain AB where "Length PO E E' A B AB"
    using assms length_existence by blast 
  obtain BC where "Length PO E E' B C BC" 
    using assms length_existence by blast 
  obtain AC where "Length PO E E' A C AC" 
    using assms length_existence by blast 
  have "Col PO E AB"
    using Length_def \<open>Length PO E E' A B AB\<close> by auto 
  then obtain AB2 where "Prod PO E E' AB AB AB2"
    using assms prod_exists by blast 
  hence "Col PO E AB2"
    by (metis Ar2_def \<open>Col PO E AB\<close> assms prod_col) 
  have "Col PO E BC" 
    using Length_def \<open>Length PO E E' B C BC\<close> by auto 
  then obtain BC2 where "Prod PO E E' BC BC BC2" 
    using assms prod_exists by blast 
  hence "Col PO E BC2"
    by (metis Ar2_def \<open>Col PO E BC\<close> assms prod_col) 
  have "Col PO E AC" 
    using Length_def \<open>Length PO E E' A C AC\<close> by auto 
  then obtain AC2 where "Prod PO E E' AC AC AC2"
    using assms prod_exists by blast 
  hence "Col PO E AC2"
    by (metis Ar2_def \<open>Col PO E AC\<close> assms prod_col)
  obtain SS where "Sum PO E E' AB2 BC2 SS"
    using \<open>Col PO E AB2\<close> \<open>Col PO E BC2\<close> assms sum_exists by blast 
  thus ?thesis
    by (metis \<open>Col PO E AB2\<close> \<open>Col PO E AB\<close> \<open>Col PO E AC2\<close> \<open>Col PO E AC\<close> 
        \<open>Col PO E BC2\<close> \<open>Col PO E BC\<close> \<open>Length PO E E' A B AB\<close> \<open>Length PO E E' A C AC\<close> 
        \<open>Length PO E E' B C BC\<close> \<open>Prod PO E E' AB AB AB2\<close>
        \<open>Prod PO E E' AC AC AC2\<close> \<open>Prod PO E E' BC BC BC2\<close>)  
qed

lemma length_pos_or_null:
  assumes "Length PO E E' A B AB"
  shows "Ps PO E AB \<or> A = B"
  by (metis assms cong_identity length_Ps length_cong) 

lemma sum_pos_null: 
  assumes "\<not> Ng PO E A"
    and "\<not> Ng PO E B"
    and "Sum PO E E' A B PO"
  shows "A = PO \<and> B = PO"
  by (metis Ar2_def O_not_positive assms(1,2,3) col_pos_or_neg col_trivial_1 sum_A_null 
      sum_B_null sum_ar2 sum_pos_pos)

lemma length_not_neg:
  assumes "Length PO E E' A B AB"
  shows "\<not> Ng PO E AB"
  by (metis Ng_def assms cong_reverse_identity length_cong length_pos_or_null neg_not_pos) 

lemma signEq_refl:
  assumes "PO \<noteq> E"
    and "Col PO E A"
  shows "A = PO \<or> SignEq PO E A A"
  by (metis SignEq_def assms(1,2) col_pos_or_neg) 

lemma square_not_neg:
  assumes "Prod PO E E' A A A2"
  shows "\<not> Ng PO E A2"
  by (metis Ng_def assms pos_not_neg prod_O_r_eq square_pos) 

lemma root_uniqueness:
  assumes "\<not> Ng PO E A"
    and "\<not> Ng PO E B"
    and "Prod PO E E' A A C"
    and "Prod PO E E' B B C"
  shows "A = B"
  by (metis Ar2_def Prod_def assms(1,2,3,4) col_pos_or_neg eq_squares_eq_or_opp 
      opp_pos_neg prod_1_r prod_O_r_eq) 

lemma inter_tangent_circle:
  assumes "P \<noteq> Q"
    and "Cong P PO Q PO"
    and "Col P PO Q"
    and "P M Le P PO"
    and "Q M Le Q PO"
  shows "M = PO" 
proof -
  have "P = Q \<or> PO Midpoint P Q"
    using assms(2,3) cong_commutativity l7_20_bis by blast
  moreover 
  { 
    assume "PO Midpoint P Q"
    obtain A where "Bet PO A P" and "Cong P M PO A"
      using Le_def assms(4) le_right_comm by blast 
    obtain B where "Bet PO B Q" and "Cong Q M PO B"
      using Le_cases Le_def assms(5) by blast 
    have "P Q Le A B" 
      using triangle_inequality_2 [of A PO B P M Q] by (meson Bet_cases \<open>Cong P M PO A\<close> 
          \<open>Cong Q M PO B\<close> \<open>PO Midpoint P Q\<close> \<open>PO \<midarrow> A \<midarrow> P\<close> \<open>PO \<midarrow> B \<midarrow> Q\<close>
          between_exchange3 midpoint_bet not_cong_4312 not_cong_4321)
    have "A B Le P Q"
      by (meson \<open>PO Midpoint P Q\<close> \<open>PO \<midarrow> A \<midarrow> P\<close> \<open>PO \<midarrow> B \<midarrow> Q\<close> bet2_le2__le2356_R1 
          between_exchange2 between_inner_transitivity between_symmetry 
          between_trivial2 l5_12_a midpoint_bet) 
    have "Cong A B P Q"
      by (simp add: \<open>A B Le P Q\<close> \<open>P Q Le A B\<close> le_anti_symmetry) 
    hence "M = PO"
      by (smt (verit) Bet_cases Col_def Cong_cases Midpoint_def \<open>Cong P M PO A\<close> \<open>Cong Q M PO B\<close>
          \<open>PO Midpoint P Q\<close> \<open>PO \<midarrow> A \<midarrow> P\<close> \<open>PO \<midarrow> B \<midarrow> Q\<close> assms(1) bet_cong_eq between_exchange3
          between_exchange4 l4_18) 
  }
  ultimately show ?thesis 
    using assms(1) by blast
qed

lemma inter_circle_per:
  assumes "Cong P A Q A"
    and "P M Le P A" 
    and "Q M Le Q A"
    and "A T Projp P Q"
    and "Per P T M"
  shows "T M Le T A" 
proof (cases "P = T")
  have " \<not> (Bet TPA TPB TPC \<or> Bet TPB TPC TPA \<or> Bet TPC TPA TPB)"
    by (simp add: lower_dim)
  let ?O = "TPA" and ?E = "TPB" and ?E' = "TPC"
  have "\<not> Col ?O ?E ?E'"
    by (simp add: Col_def \<open>\<not> ((TPA \<midarrow> TPB \<midarrow> TPC) \<or> (TPB \<midarrow> TPC \<midarrow> TPA) \<or> (TPC \<midarrow> TPA \<midarrow> TPB))\<close>)
  show "P = T \<Longrightarrow> T M Le T A"
    using assms(2) by auto 
  {
    assume "P \<noteq> T"
    have "Col P Q T \<and> P Q Perp A T \<or> Col P Q A \<and> A = T"
      using Projp_def assms(4) by presburger 
    moreover {
      assume "Col P Q T" and "P Q Perp A T"
      have "Per P T A"
        using Per_perm \<open>Col P Q T\<close> \<open>P Q Perp A T\<close> col_trivial_3 l8_16_1 by blast 
      obtain PT TA AP PT2 TA2 AP2 SS where "Col ?O ?E PT" and "Col ?O ?E TA" and 
        "Col ?O ?E AP" and "Col ?O ?E PT2" and "Col ?O ?E TA2" and "Col ?O ?E AP2" and 
        "Length ?O ?E ?E' P T PT" and "Length ?O ?E ?E' T A TA" and 
        "Length ?O ?E ?E' P A AP" and "Prod ?O ?E ?E' PT PT PT2" and 
        "Prod ?O ?E ?E' TA TA TA2" and "Prod ?O ?E ?E' AP AP AP2" and 
        "Sum ?O ?E ?E' PT2 TA2 SS" 
        using pyth_context [of ?O ?E ?E'] \<open>\<not> Col ?O ?E ?E'\<close> by metis
      have "Sum ?O ?E ?E' PT2 TA2 AP2" 
        using pythagoras [of ?O ?E P T A ?E' AP PT TA PT2 TA2 AP2] 
          \<open>Length TPA TPB TPC P A AP\<close> \<open>Length TPA TPB TPC P T PT\<close> 
          \<open>Length TPA TPB TPC T A TA\<close> \<open>Per P T A\<close> \<open>Prod TPA TPB TPC AP AP AP2\<close> 
          \<open>Prod TPA TPB TPC PT PT PT2\<close> \<open>Prod TPA TPB TPC TA TA TA2\<close>
          between_trivial2 length_sym lower_dim by blast 
      hence "SS = AP2"
        using \<open>Sum TPA TPB TPC PT2 TA2 SS\<close> sum_stable by blast 
      obtain PT' TM PM PT2' TM2 PM2 SS' where "Col ?O ?E PT'" and "Col ?O ?E TM" and 
        "Col ?O ?E PM" and "Col ?O ?E PT2'" and "Col ?O ?E TM2" and "Col ?O ?E PM2" and 
        "Length ?O ?E ?E' P T PT'" and "Length ?O ?E ?E' T M TM" and 
        "Length ?O ?E ?E' P M PM" and "Prod ?O ?E ?E' PT' PT' PT2'" and 
        "Prod ?O ?E ?E' TM TM TM2" and "Prod ?O ?E ?E' PM PM PM2" and 
        "Sum ?O ?E ?E' PT2' TM2 SS'" 
        using pyth_context [of ?O ?E ?E'] \<open>\<not> Col ?O ?E ?E'\<close> by metis
      hence "PT = PT'"
        using \<open>Length TPA TPB TPC P T PT\<close> length_uniqueness by blast
      hence "PT2 = PT2'"
        using \<open>Prod TPA TPB TPC PT PT PT2\<close> \<open>Prod TPA TPB TPC PT' PT' PT2'\<close> \<open>\<not> Col TPA TPB TPC\<close>
          prod_uniqueness by blast
      have "Sum ?O ?E ?E' PT2 TM2 PM2" 
        using pythagoras [of ?O ?E P T M ?E' PM PT TM PT2 TM2 PM2] 
          \<open>Length TPA TPB TPC P M PM\<close> \<open>Length TPA TPB TPC P T PT\<close>
          \<open>Length TPA TPB TPC T M TM\<close> \<open>Prod TPA TPB TPC PM PM PM2\<close>
          \<open>Prod TPA TPB TPC PT PT PT2\<close> \<open>Prod TPA TPB TPC TM TM TM2\<close> assms(5) between_trivial
          length_sym lower_dim by blast
      have "SS' = PM2"
        using \<open>PT2 = PT2'\<close> \<open>Sum TPA TPB TPC PT2 TM2 PM2\<close> \<open>Sum TPA TPB TPC PT2' TM2 SS'\<close>
          \<open>\<not> Col TPA TPB TPC\<close> sum_uniqueness by blast
      have "T M Le T A" 
      proof (cases "T = M")
        show "T = M \<Longrightarrow> T M Le T A"
          by (simp add: le_trivial) 
        show "T \<noteq> M \<Longrightarrow> T M Le T A"
          by (meson \<open>Per P T A\<close> assms(2,5) cong_lt_per2__lt cong_reflexivity lt__nle
              nlt__le) 
      qed
    }
    moreover have "Col P Q A \<and> A = T \<Longrightarrow> T M Le T A"
      by (metis Col_cases Projp_def assms(1,2,3,4) inter_tangent_circle
          le_reflexivity)
    ultimately show "T M Le T A" 
      by blast
  }
qed

lemma inter_circle_obtuse:
  assumes "Cong P A Q A "
    and "P M Le P A"
    and "Q M Le Q A"
    and "A T Projp P Q"
    and "Obtuse P T M \<or> Per P T M"
  shows "T M Le T A" 
proof (cases "P = T")
  have " \<not> (Bet TPA TPB TPC \<or> Bet TPB TPC TPA \<or> Bet TPC TPA TPB)"
    by (simp add: lower_dim)
  let ?O = "TPA" and ?E = "TPB" and ?E' = "TPC"
  have "\<not> Col ?O ?E ?E'"
    by (simp add: Col_def \<open>\<not> ((TPA \<midarrow> TPB \<midarrow> TPC) \<or> (TPB \<midarrow> TPC \<midarrow> TPA) \<or> (TPC \<midarrow> TPA \<midarrow> TPB))\<close>)
  show "P = T \<Longrightarrow> T M Le T A"
    using assms(2) by auto 
  {
    assume "P \<noteq> T"
    have "?O \<noteq> ?E"
      using \<open>\<not> ((TPA \<midarrow> TPB \<midarrow> TPC) \<or> (TPB \<midarrow> TPC \<midarrow> TPA) \<or> (TPC \<midarrow> TPA \<midarrow> TPB))\<close>
        not_bet_distincts by blast 
    have "Per P T A"
      by (metis Per_cases Projp_def assms(4) l8_16_1 l8_5 not_col_distincts) 
    obtain PT TA AP PT2 TA2 AP2 SS where "Col ?O ?E PT" and "Col ?O ?E TA" and 
      "Col ?O ?E AP" and "Col ?O ?E PT2" and "Col ?O ?E TA2" and "Col ?O ?E AP2" and 
      "Length ?O ?E ?E' P T PT" and "Length ?O ?E ?E' T A TA" and 
      "Length ?O ?E ?E' P A AP" and "Prod ?O ?E ?E' PT PT PT2" and 
      "Prod ?O ?E ?E' TA TA TA2" and "Prod ?O ?E ?E' AP AP AP2" and 
      "Sum ?O ?E ?E' PT2 TA2 SS" 
      using pyth_context [of ?O ?E ?E'] \<open>\<not> Col ?O ?E ?E'\<close> by metis
    have "Sum ?O ?E ?E' PT2 TA2 AP2" 
      using pythagoras [of ?O ?E P T A ?E' AP PT TA PT2 TA2 AP2] 
        \<open>Length TPA TPB TPC P A AP\<close> \<open>Length TPA TPB TPC P T PT\<close> 
        \<open>Length TPA TPB TPC T A TA\<close> \<open>Per P T A\<close>
        \<open>Prod TPA TPB TPC AP AP AP2\<close> \<open>Prod TPA TPB TPC PT PT PT2\<close> \<open>Prod TPA TPB TPC TA TA TA2\<close>
        between_trivial2 length_sym lower_dim by blast 
    hence "SS = AP2"
      using \<open>Sum TPA TPB TPC PT2 TA2 SS\<close> sum_stable by blast 
    obtain PT' TM PM PT2' TM2 PM2 SS' where "Col ?O ?E PT'" and "Col ?O ?E TM" and 
      "Col ?O ?E PM" and "Col ?O ?E PT2'" and "Col ?O ?E TM2" and "Col ?O ?E PM2" and 
      "Length ?O ?E ?E' P T PT'" and "Length ?O ?E ?E' T M TM" and 
      "Length ?O ?E ?E' P M PM" and "Prod ?O ?E ?E' PT' PT' PT2'" and 
      "Prod ?O ?E ?E' TM TM TM2" and "Prod ?O ?E ?E' PM PM PM2" and 
      "Sum ?O ?E ?E' PT2' TM2 SS'" 
      using pyth_context [of ?O ?E ?E'] \<open>\<not> Col ?O ?E ?E'\<close> by metis
    hence "PT = PT'"
      using \<open>Length TPA TPB TPC P T PT\<close> length_uniqueness by blast
    hence "PT2 = PT2'"
      using \<open>Prod TPA TPB TPC PT PT PT2\<close> \<open>Prod TPA TPB TPC PT' PT' PT2'\<close> \<open>\<not> Col TPA TPB TPC\<close>
        prod_uniqueness by blast
    have "LeP ?O ?E ?E' SS' PM2"
      using pythagoras_obtuse_or_per [of ?O ?E P T M ?E' PM PT TM PT2 TM2 PM2 SS'] 
      by (simp add: \<open>Length TPA TPB TPC P M PM\<close> \<open>Length TPA TPB TPC P T PT'\<close>
          \<open>Length TPA TPB TPC T M TM\<close> \<open>PT = PT'\<close> \<open>PT2 = PT2'\<close> \<open>Prod TPA TPB TPC PM PM PM2\<close>
          \<open>Prod TPA TPB TPC PT' PT' PT2'\<close> \<open>Prod TPA TPB TPC TM TM TM2\<close>
          \<open>Sum TPA TPB TPC PT2' TM2 SS'\<close> \<open>TPA \<noteq> TPB\<close> assms(5) length_sym) 
    show "T M Le T A" 
    proof (cases "T = M")
      show "T = M \<Longrightarrow> T M Le T A"
        by (simp add: le_trivial) 
      {
        assume "T \<noteq> M"
        show "T M Le T A" 
        proof (cases "P = M")
          show "P = M \<Longrightarrow> T M Le T A"
            using \<open>T \<noteq> M\<close> assms(5) l8_8 obtuse_distincts by blast
          {
            assume "P \<noteq> M"
            have "LeP ?O ?E ?E' PM AP" 
              using length_leP_le_2 [of ?O ?E ?E' P M PM P A AP] 
              by (simp add: \<open>Length TPA TPB TPC P A AP\<close> \<open>Length TPA TPB TPC P M PM\<close>
                  assms(2)) 
            have "Ar2 ?O ?E ?E' PM AP PM"
              by (simp add: Ar2_def \<open>Col TPA TPB AP\<close> \<open>Col TPA TPB PM\<close>
                  \<open>\<not> Col TPA TPB TPC\<close>) 
            moreover have "Ps ?O ?E PM" 
            proof -
              have "P = M \<Longrightarrow> Ps ?O ?E PM"
                by (simp add: \<open>P \<noteq> M\<close>) 
              thus ?thesis
                by (meson \<open>Length TPA TPB TPC P M PM\<close> length_pos_or_null) 
            qed
            moreover 
            have "P = A \<Longrightarrow> Ps ?O ?E AP"
              using \<open>P \<noteq> T\<close> \<open>Per P T A\<close> l8_8 by blast
            hence "Ps ?O ?E AP"
              using \<open>Length TPA TPB TPC P A AP\<close> length_pos_or_null by blast 
            ultimately have "LeP ?O ?E ?E' PM2 AP2" 
              using square_increase [of ?O ?E ?E' PM AP PM PM2] \<open>LeP TPA TPB TPC PM AP\<close> 
                \<open>Prod TPA TPB TPC AP AP AP2\<close>
                \<open>Prod TPA TPB TPC PM PM PM2\<close> square_increase by blast 
            have "LeP ?O ?E ?E' SS' AP2"
              using \<open>LeP TPA TPB TPC PM2 AP2\<close> \<open>LeP TPA TPB TPC SS' PM2\<close> leP_trans by blast
            have "LeP ?O ?E ?E' TM2 TA2"
              by (metis \<open>Col TPA TPB TA2\<close> \<open>Col TPA TPB TM2\<close> \<open>LeP TPA TPB TPC SS' AP2\<close> 
                  \<open>PT2 = PT2'\<close> \<open>SS = AP2\<close> \<open>Sum TPA TPB TPC PT2 TA2 SS\<close> 
                  \<open>Sum TPA TPB TPC PT2' TM2 SS'\<close>
                  \<open>\<not> Col TPA TPB TPC\<close> col_2_le_or_ge leP_asym sum_comm sum_preserves_lep
                  sum_uniquenessB)
            have "T = M \<Longrightarrow> Ps ?O ?E TM"
              using \<open>T \<noteq> M\<close> by blast 
            hence "Ps ?O ?E TM"
              using \<open>Length TPA TPB TPC T M TM\<close> length_pos_or_null by blast 
            have "Ps ?O ?E TA"
              by (metis NCol_perm Ng_def Out_def Ps_def \<open>Col TPA TPB TA\<close> 
                  \<open>LeP TPA TPB TPC TM2 TA2\<close>
                  \<open>Length TPA TPB TPC T A TA\<close> \<open>Prod TPA TPB TPC TA TA TA2\<close>
                  \<open>Prod TPA TPB TPC TM TM TM2\<close> \<open>Ps TPA TPB TM\<close> \<open>\<not> Col TPA TPB TPC\<close> leP_asym
                  length_not_neg or_bet_out prod_O_l_eq prod_pos_pos ps_le)
            have "LeP ?O ?E ?E' TM TA"
              by (metis LeP_def \<open>LeP TPA TPB TPC TM2 TA2\<close> \<open>Prod TPA TPB TPC TA TA TA2\<close>
                  \<open>Prod TPA TPB TPC TM TM TM2\<close> \<open>Ps TPA TPB TA\<close> \<open>Ps TPA TPB TM\<close> pos_not_neg
                  root_uniqueness square_increase_rev)
            have "A T Projp P Q"
              by (simp add: assms(4)) 
            hence "(Col P Q T \<and> P Q Perp A T) \<or> (Col P Q A \<and> A = T)"
              using Projp_def by auto
            moreover {
              assume "Col P Q T" and "P Q Perp A T"
              have "T M Le T A" 
                using length_leP_le_1 [of ?O ?E ?E' _ _ TM _ _ TA]
                using \<open>LeP TPA TPB TPC TM TA\<close> \<open>Length TPA TPB TPC T A TA\<close>
                  \<open>Length TPA TPB TPC T M TM\<close> by blast    
            }
            moreover {
              assume "Col P Q A" and "A = T"
              have "T M Le T A" 
              proof -
                have "(Col P A Q \<and> P M Le P A \<and> Q M Le Q A) \<longrightarrow> M = A"
                  by (metis Projp_def assms(1,4) inter_tangent_circle) 
                hence "M = A"
                  using Col_cases \<open>Col P Q A\<close> assms(2,3) by blast  
                thus ?thesis
                  using \<open>A = T\<close> \<open>T \<noteq> M\<close> by auto 
              qed
            }
            ultimately show "T M Le T A"
              by blast
          }
        qed
      }
    qed
  }
qed

lemma circle_projp_between:
  assumes "Cong P A Q A"
    and "A T Projp P Q"
  shows "Bet P T Q" 
proof (cases "P = T")
  show "P = T \<Longrightarrow> (P \<midarrow> T \<midarrow> Q)"
    using not_bet_distincts by blast 
  {
    assume "P \<noteq> T"
    have "Col P Q T \<and> P Q Perp A T \<or> Col P Q A \<and> A = T"
      using Projp_def assms(2) by auto 
    moreover {
      assume "Col P Q T" and "P Q Perp A T"
      hence "Per A T P"
        using col_trivial_3 l8_16_1 by blast
      obtain T' where "T' Midpoint P Q"
        using midpoint_existence by blast
      hence "Per A T' P"
        using Per_def assms(1) cong_commutativity by blast
      have "T' = T \<or> \<not> Col T P Q"
        by (metis Projp_def \<open>P \<noteq> T\<close> \<open>Per A T P\<close> \<open>Per A T' P\<close> \<open>T' Midpoint P Q\<close> assms(2)
            col_per2_cases midpoint_col midpoint_distinct_1) 
      moreover have "T' = T \<Longrightarrow> Bet P T Q"
        using \<open>T' Midpoint P Q\<close> midpoint_bet by blast 
      moreover have "\<not> Col T P Q \<Longrightarrow> Bet P T Q"
        using Col_cases \<open>Col P Q T\<close> by auto 
      ultimately have "Bet P T Q"  
        by blast
    }
    moreover have "Col P Q A \<and> A = T \<Longrightarrow> Bet P T Q"
      by (metis NCol_perm Projp_def assms(1,2) bet_cong_eq between_trivial col_bet2_cong1
          col_trivial_2 cong_identity third_point) 
    ultimately show "P \<midarrow> T \<midarrow> Q" 
      by blast
  }
qed

lemma inter_circle:
  assumes "Cong P A Q A"
    and "P M Le P A"
    and "Q M Le Q A"
    and "A T Projp P Q"
  shows "T M Le T A" 
proof (cases "T = M")
  have "Bet P T Q"
    using assms(1,4) circle_projp_between by auto
  show "T = M \<Longrightarrow> T M Le T A"
    using le_trivial by blast 
  {
    assume "T \<noteq> M"
    show "T M Le T A" 
    proof (cases "P = T")
      show "P = T \<Longrightarrow> T M Le T A"
        using assms(2) by blast 
      {
        assume "P \<noteq> T"
        hence "Acute P T M \<or> Per P T M \<or> Obtuse P T M"
          using \<open>T \<noteq> M\<close> angle_partition by auto 
        show "T M Le T A"
        proof (cases "Q = T")
          show "Q = T \<Longrightarrow> T M Le T A"
            using assms(3) by auto 
          {
            assume "Q \<noteq> T"
            {
              assume "Acute P T M"
              have "Obtuse Q T M"
                using \<open>Acute P T M\<close> \<open>P \<midarrow> T \<midarrow> Q\<close> \<open>Q \<noteq> T\<close> acute_bet__obtuse by blast
              moreover have "A T Projp Q P"
                by (metis Col_cases Perp_cases Projp_def assms(4)) 
              ultimately have "T M Le T A"
                using Cong_cases assms(1,2,3) inter_circle_obtuse by blast 
            }
            moreover have "Per P T M \<Longrightarrow> T M Le T A"
              using assms(1,2,3,4) inter_circle_per by blast 
            moreover have "Obtuse P T M \<Longrightarrow> T M Le T A"
              using assms(1,2,3,4) inter_circle_obtuse by blast 
            ultimately show "T M Le T A"
              using \<open>Acute P T M \<or> Per P T M \<or> Obtuse P T M\<close> by blast 
          }
        qed
      }
    qed
  }
qed

lemma projp_lt:
  assumes "Cong P A Q A"
    and "A T Projp P Q"
  shows "T A Lt P A" 
proof -
  have "Col P Q T \<and> P Q Perp A T \<or> Col P Q A \<and> A = T"
    using Projp_def assms(2) by auto 
  moreover {
    assume "Col P Q T" and "P Q Perp A T"
    have ?thesis
    proof (cases "P = T")
      show "P = T \<Longrightarrow> T A Lt P A"
        by (metis Perp_cases \<open>P Q Perp A T\<close> assms(1) cong__nlt l11_46 l8_16_1
            not_col_distincts) 
      show "P \<noteq> T \<Longrightarrow> T A Lt P A"
        by (metis Lt_cases \<open>Col P Q T\<close> \<open>P Q Perp A T\<close> col_trivial_3 l8_16_1 per_lt) 
    qed
  } 
  moreover have "Col P Q A \<and> A = T \<Longrightarrow> ?thesis"
    by (metis Projp_def assms(1,2) cong_reverse_identity lt1123) 
  ultimately show ?thesis 
    by blast
qed

lemma Ps_Col:
  assumes "Ps PO E A"
  shows "Col PO E A"
  using Col_cases Ps_def assms out_col by blast 

lemma PythRel_exists:
  assumes "\<not> Col PO E  E'"
  shows "\<forall> A B. Col PO E A \<and> Col PO E B \<longrightarrow> (\<exists> C. PythRel PO E E' A B C)" 
proof -
  {
    fix A B
    assume "Col PO E A" and "Col PO E B"
    have "\<exists> C. PythRel PO E E' A B C" 
    proof (cases "B = PO")
      show "B = PO \<Longrightarrow> \<exists> C. PythRel PO E E' A B C"
        using Ar2_def PythRel_def \<open>Col PO E A\<close> assms col_trivial_3 by auto 
      {
        assume "B \<noteq> PO"
        obtain X where "PO X Perp E PO"
          using Perp_cases assms l8_21_aux by blast 
        obtain B' where "Bet PO X B' \<or> Bet PO B' X" and "Cong PO B' PO B"
          by (metis \<open>PO X Perp E PO\<close> perp_distinct segment_construction_2)
        obtain C where "Bet PO E C \<or> Bet PO C E" and "Cong PO C A B'"
          by (metis segment_construction segment_construction_2)
        have "Col PO E C"
          using Bet_cases Col_def \<open>(PO \<midarrow> E \<midarrow> C) \<or> (PO \<midarrow> C \<midarrow> E)\<close> by blast
        moreover have "PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C A B'"
          by (metis Col_cases Col_def \<open>B \<noteq> PO\<close> \<open>Col PO E B\<close> \<open>Cong PO B' PO B\<close> \<open>Cong PO C A B'\<close>
              \<open>PO X Perp E PO\<close> \<open>(PO \<midarrow> X \<midarrow> B') \<or> (PO \<midarrow> B' \<midarrow> X)\<close> col_trivial_2 
              cong_reverse_identity perp_col0)
        hence "PO = B \<and> (A = C \<or> Opp PO E E' A C) \<or> 
                 (\<exists> B'0. PO B'0 Perp PO B \<and> Cong PO B'0 PO B \<and> Cong PO C A B'0)" 
          by blast
        ultimately have "PythRel PO E E' A B C"
          by (simp add: assms \<open>Col PO E A\<close> \<open>Col PO E B\<close> Ar2_def PythRel_def) 
        thus "\<exists> C. PythRel PO E E' A B C" 
          by fast
      }
    qed
  }
  thus ?thesis
    by blast
qed

lemma opp_same_square:
  assumes "Opp PO E E' A B"
    and "Prod PO E E' A A A2"
  shows "Prod PO E E' B B A2" 
proof -
  obtain ME where "Opp PO E E' E ME"
    using Ar2_def Prod_def assms(2) col_trivial_2 opp_exists by presburger
  hence "Prod PO E E' A ME B"
    using assms(1) opp_prod by blast
  moreover have "Prod PO E E' B ME A"
    by (meson Ar2_def Prod_def \<open>Opp PO E E' E ME\<close> assms(1) opp_comm opp_prod)
  hence "Prod PO E E' ME B A"
    by (simp add: prod_sym)
  ultimately show ?thesis
    using assms(2) prod_assoc by blast 
qed

(**********)

lemma PythOK:
  assumes "PythRel PO E E' A B C"
    and "Prod PO E E' A A A2"
    and "Prod PO E E' B B B2"
    and "Prod PO E E' C C C2"
  shows "Sum PO E E' A2 B2 C2" 
proof -
  have "PO \<noteq> E"
    using Ar2_def PythRel_def assms(1) col_trivial_1 by force 
  have "PO = B \<and> 
        (A = C \<or> Opp PO E E' A C) \<or> (\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C A B')"
    using PythRel_def assms(1) by auto 
  moreover { 
    assume "PO = B" and "A = C \<or> Opp PO E E' A C"
    hence "PO = B2"
      using assms(3) prod_O_l_eq by blast 
    have "A = C \<Longrightarrow> A2 = C2"
      by (metis Ar2_def Prod_def assms(2,4) prod_uniqueness) 
    moreover have "Opp PO E E' A C \<Longrightarrow> A2 = C2"
      by (meson Ar2_def PythRel_def assms(1,2,4) opp_same_square prod_uniqueness) 
    ultimately have "A2 = C2"
      using \<open>A = C \<or> Opp PO E E' A C\<close> by blast 
    hence "Col PO E A2"
      by (metis Col_def Ps_Col assms(4) between_trivial prod_O_r_eq
          square_pos) 
    hence "Sum PO E E' A2 B2 C2"
      using Ar2_def PythRel_def \<open>A2 = C2\<close> \<open>PO = B2\<close> assms(1) sum_A_O by auto 
  }
  moreover {
    assume "\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C A B'"
    then obtain B' where "PO B' Perp PO B" and "Cong PO B' PO B" and "Cong PO C A B'"
      by blast
    have "Per A PO B'" 
    proof -
      have "PO \<noteq> B"
        using \<open>PO B' Perp PO B\<close> perp_distinct by blast 
      moreover have "Per B' PO B"
        by (simp add: \<open>PO B' Perp PO B\<close> perp_per_2) 
      moreover have "Col PO B A"
        using Ar2_def PythRel_def \<open>PO \<noteq> E\<close> assms(1) col_transitivity_1 by presburger 
      ultimately show ?thesis
        using Per_cases per_col by blast 
    qed
    have "Sum PO E E' A2 B2 C2"
    proof (cases "A = PO")
      {
        assume "A = PO"
        hence "Cong PO B PO C"
          using \<open>\<exists>B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C A B'\<close>
            cong_inner_transitivity cong_symmetry by blast 
        have "B = C \<or> PO Midpoint B C" 
          using l7_20 [of B PO C] Ar2_def PythRel_def \<open>Cong PO B PO C\<close> \<open>PO \<noteq> E\<close> 
            assms(1) col_permutation_4 col_transitivity_1 by presburger 
        moreover {
          assume "B = C"
          have "B2 = C2" 
            using prod_uniqueness [of PO E E' B B B2 C2] Ar2_def PythRel_def \<open>B = C\<close> 
              assms(1,3,4) by presburger
          have "A2 = PO" 
            using prod_uniqueness [of PO E E' PO PO A2 PO] \<open>A = PO\<close> assms(2) prod_O_l_eq by blast 
          have "Col PO E B2"
            by (metis Ps_Col assms(3) grid_not_par_5 prod_O_r_eq square_pos) 
          hence "Sum PO E E' A2 B2 C2"
            using Ar2_def PythRel_def \<open>A2 = PO\<close> \<open>B2 = C2\<close> assms(1) sum_O_B by auto 
        }
        moreover {
          assume "PO Midpoint B C"
          have "A2 = PO" 
            using prod_uniqueness [of PO E E' PO PO A2 PO] \<open>A = PO\<close> assms(2) prod_O_l_eq by blast 
          have "Ar2 PO E E' PO B C"
            using PythRel_def \<open>A = PO\<close> assms(1) by blast
          hence "Opp PO E E' B C"
            by (simp add: \<open>PO Midpoint B C\<close> midpoint_opp) 
          have "C2 = B2" 
            using prod_uniqueness [of PO E E' C C C2 B2] Ar2_def \<open>Ar2 PO E E' PO B C\<close> 
              \<open>Opp PO E E' B C\<close> assms(3,4) opp_same_square
            by presburger
          have "Col PO E B2"
            by (metis Col_def Ps_Col \<open>C2 = B2\<close> assms(4) between_trivial2 prod_O_r_eq
                square_pos) 
          hence "Sum PO E E' A2 B2 C2"
            using Ar2_def \<open>A2 = PO\<close> \<open>Ar2 PO E E' PO B C\<close> \<open>C2 = B2\<close> sum_O_B by presburger 
        }
        ultimately show "Sum PO E E' A2 B2 C2" 
          by blast
      }
      {
        assume "A \<noteq> PO"
        show "Sum PO E E' A2 B2 C2" 
        proof (cases "PO Out A E")
          {
            assume "PO Out A E"
            show "Sum PO E E' A2 B2 C2" 
            proof (cases "PO Out B E")
              {
                assume "PO Out B E"
                show "Sum PO E E' A2 B2 C2" 
                proof (cases "PO Out C E")
                  {
                    assume "PO Out C E"
                    show "Sum PO E E' A2 B2 C2" 
                    proof (rule pythagoras [of _ _ A PO B' _ C A B], insert \<open>PO \<noteq> E\<close> 
                        \<open>Per A PO B'\<close>assms(2,3,4))
                      have "LeP PO E E' PO C"
                      proof -
                        have "Diff PO E E' C PO C"
                          using Ar2_def Prod_def assms(4) diff_A_O by presburger 
                        moreover have "Ps PO E C"
                          by (simp add: Ps_def \<open>PO Out C E\<close>) 
                        ultimately show ?thesis
                          by (simp add: diff_pos__ltp ltp_to_lep) 
                      qed
                      thus "Length PO E E' A B' C"
                        by (meson Length_def NCol_cases \<open>Cong PO C A B'\<close> \<open>PO Out C E\<close> \<open>PO \<noteq> E\<close>
                            out_col) 
                      show "Length PO E E' A PO A"
                        by (metis Ar2_def Cong_cases Length_def Out_def PythRel_def 
                            \<open>PO Out A E\<close> assms(1)
                            cong_reflexivity ps_le) 
                      show "Length PO E E' B' PO B"
                        by (metis Length_def Out_def \<open>Cong PO B' PO B\<close> \<open>Length PO E E' A B' C\<close> 
                            \<open>PO Out B E\<close> \<open>PO Out C E\<close> cong_3421 length_Ar2 out_col ps_le) 
                    qed
                  }
                  {
                    assume "\<not> PO Out C E"
                    obtain OC where "Opp PO E E' C OC"
                      by (meson Ar2_def Diff_def Prod_def assms(4) diff_null) 
                    have "Ng PO E C"
                      by (metis Col_def Ps_def SignEq_def \<open>A \<noteq> PO\<close> \<open>Cong PO C A B'\<close> \<open>Per A PO B'\<close>
                          \<open>\<not> PO Out C E\<close> assms(4) between_trivial2 cong_reverse_identity 
                          not_signEq_prod_neg per_not_col square_not_neg)
                    hence "Ps PO E OC"
                      using \<open>Opp PO E E' C OC\<close> opp_neg_pos by auto
                    show "Sum PO E E' A2 B2 C2" 
                    proof (rule pythagoras [of _ _ A PO B' _ OC A B], insert \<open>PO \<noteq> E\<close> 
                        \<open>Per A PO B'\<close> assms(2,3))
                      show "Length PO E E' A B' OC" 
                      proof -
                        have "Col PO E OC"
                          by (simp add: Ps_Col \<open>Ps PO E OC\<close>) 
                        moreover have "LeP PO E E' PO OC"
                          by (metis Ar2_def Prod_def Ps_def \<open>Ps PO E OC\<close> assms(2) 
                              calculation not_bet_and_out ps_le third_point) 
                        moreover have "Cong PO OC A B'" 
                        proof -
                          have "PO Midpoint C OC" 
                            using opp_midpoint \<open>Opp PO E E' C OC\<close> by auto 
                          thus ?thesis
                            using Cong_cases Midpoint_def \<open>Cong PO C A B'\<close> cong_inner_transitivity
                            by blast 
                        qed
                        ultimately show ?thesis
                          by (simp add: Length_def \<open>PO \<noteq> E\<close>) 
                      qed
                      show "Length PO E E' A PO A"
                        using Ar2_def Length_def Out_def Prod_def \<open>PO Out A E\<close> assms(2)
                          cong_pseudo_reflexivity ps_le by force 
                      show "Length PO E E' B' PO B"
                        by (metis Ar2_def Length_def Out_def Prod_def \<open>Cong PO B' PO B\<close> 
                            \<open>PO Out B E\<close> assms(3) cong_3421 ps_le) 
                      show "Prod PO E E' OC OC C2"
                        using \<open>Opp PO E E' C OC\<close> assms(4) opp_same_square by auto 
                    qed
                  }
                qed
              }
              {
                assume "\<not> PO Out B E"
                obtain OB where "Opp PO E E' B OB"
                  using Ar2_def Prod_def assms(3) opp_exists by presburger 
                    (*319*)
                have "Ng PO E B"
                  by (metis Ps_def SignEq_def
                      \<open>\<exists>B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C A B'\<close> 
                      \<open>\<not> PO Out B E\<close> assms(3) not_col_distincts not_signEq_prod_neg 
                      perp_not_col2 square_not_neg)
                hence "Ps PO E OB"
                  using \<open>Opp PO E E' B OB\<close> opp_neg_pos by auto 
                {
                  assume "PO Out C E"
                  have "Sum PO E E' A2 B2 C2" 
                  proof (rule pythagoras [of _ _ A PO B' _ C A OB], insert \<open>PO \<noteq> E\<close> 
                      \<open>Per A PO B'\<close> assms(2,4))
                    have "LeP PO E E' PO C" 
                    proof -
                      have "PO Out OB E"
                        using Ps_def \<open>Ps PO E OB\<close> by auto 
                      have "LtP PO E E' PO C" 
                      proof -
                        have "Diff PO E E' C PO C"
                          using Ar2_def Prod_def assms(4) diff_A_O by presburger 
                        moreover have "Ps PO E C"
                          by (simp add: Ps_def \<open>PO Out C E\<close>) 
                        ultimately show ?thesis
                          using diff_pos__ltp by blast 
                      qed
                      thus ?thesis
                        using ltp_to_lep by auto 
                    qed
                    thus "Length PO E E' A B' C"
                      by (metis Length_def Ps_Col \<open>Cong PO C A B'\<close> \<open>PO \<noteq> E\<close> length_O lep_neq__ltp
                          ltP_pos) 
                    show "Length PO E E' A PO A"
                      by (metis Ar2_def Cong_cases Length_def Out_def PythRel_def 
                          \<open>PO Out A E\<close> assms(1) cong_reflexivity ps_le) 
                    show "Length PO E E' B' PO OB" 
                    proof -
                      have "LeP PO E E' PO OB"
                        using Ar2_def Out_def Ps_def PythRel_def \<open>Ps PO E OB\<close> 
                          assms(1) ps_le by force 
                      moreover have "PO Midpoint B OB" 
                        using opp_midpoint \<open>Opp PO E E' B OB\<close> by auto 
                      hence "Cong PO OB B' PO" 
                        by (meson Midpoint_def \<open>Cong PO B' PO B\<close> cong_4312 cong_inner_transitivity) 
                      moreover have "Prod PO E E' OB OB B2"
                        using \<open>Opp PO E E' B OB\<close> assms(3) opp_same_square by blast 
                      ultimately show ?thesis
                        by (simp add: Length_def Ps_Col \<open>PO \<noteq> E\<close> \<open>Ps PO E OB\<close>) 
                    qed
                    show "Prod PO E E' OB OB B2"
                      using \<open>Opp PO E E' B OB\<close> assms(3) opp_same_square by blast 
                  qed
                }
                moreover {
                  assume "\<not> PO Out C E"
                  obtain OC where "Opp PO E E' C OC"
                    using Ar2_def Prod_def assms(4) opp_exists by presburger 
                  have "Ng PO E C"
                    by (metis Ps_def SignEq_def \<open>A \<noteq> PO\<close> \<open>Cong PO C A B'\<close> \<open>Per A PO B'\<close> 
                        \<open>\<not> PO Out C E\<close> assms(4) cong_reverse_identity l8_20_1_R1 l8_7 
                        not_signEq_prod_neg square_not_neg) 
                  hence "Ps PO E OC"
                    using \<open>Opp PO E E' C OC\<close> opp_neg_pos by auto
                  obtain OB where "Opp PO E E' B OB"
                    using \<open>Opp PO E E' B OB\<close> by auto
                  have "Ps PO E OB"
                    using \<open>Ng PO E B\<close> \<open>Opp PO E E' B OB\<close> opp_neg_pos by auto
                  have "Sum PO E E' A2 B2 C2"
                  proof (rule pythagoras [of _ _ A PO B' _ OC A OB], insert \<open>PO \<noteq> E\<close> 
                      \<open>Per A PO B'\<close> assms(2))
                    show "Length PO E E' A B' OC" 
                    proof -
                      have "Col PO E OC"
                        by (simp add: Ps_Col \<open>Ps PO E OC\<close>) 
                      moreover have "LeP PO E E' PO OC"
                        by (meson Ar2_def Ps_def PythRel_def \<open>Ps PO E OC\<close> assms(1) calculation
                            not_bet_and_out ps_le third_point) 
                      moreover have "PO Midpoint C OC" 
                        using opp_midpoint  \<open>Opp PO E E' C OC\<close> by auto 
                      hence "Cong PO OC A B'"
                        using Cong_cases Midpoint_def \<open>Cong PO C A B'\<close> cong_inner_transitivity
                        by blast 
                      ultimately show ?thesis
                        by (simp add: Length_def \<open>PO \<noteq> E\<close>) 
                    qed
                    show "Length PO E E' A PO A"
                      using Ar2_def Length_def Out_def Prod_def \<open>PO Out A E\<close> assms(2)
                        cong_pseudo_reflexivity ps_le by auto 
                    show "Length PO E E' B' PO OB" 
                    proof -
                      have "LeP PO E E' PO OB"
                        using Ar2_def Out_def Prod_def Ps_def \<open>Ps PO E OB\<close> assms(2) ps_le by force 
                      moreover have "PO Midpoint B OB"
                        using opp_midpoint \<open>Opp PO E E' B OB\<close> by blast 
                      hence "Cong PO OB B' PO"
                        by (meson Midpoint_def \<open>Cong PO B' PO B\<close> cong_4312 cong_inner_transitivity) 
                      ultimately show ?thesis
                        by (simp add: Length_def Ps_Col \<open>PO \<noteq> E\<close> \<open>Ps PO E OB\<close>) 
                    qed
                    show "Prod PO E E' OB OB B2"
                      using \<open>Opp PO E E' B OB\<close> assms(3) opp_same_square by blast 
                    show "Prod PO E E' OC OC C2"
                      using \<open>Opp PO E E' C OC\<close> assms(4) opp_same_square by auto 
                  qed
                }
                ultimately show "Sum PO E E' A2 B2 C2" 
                  by blast
              }
            qed
          }
          {
            assume "\<not> PO Out A E"
            show "Sum PO E E' A2 B2 C2" 
            proof (cases "PO Out B E")
              {
                assume "PO Out B E"
                show "Sum PO E E' A2 B2 C2" 
                proof (cases "PO Out C E")
                  {
                    assume "PO Out C E"
                    obtain OA where "Opp PO E E' A OA"
                      by (meson Ar2_def Diff_def Prod_def assms(2) diff_null)
                    have "Ng PO E A"
                      by (metis Ps_def SignEq_def \<open>A \<noteq> PO\<close> \<open>\<not> PO Out A E\<close> assms(2) 
                          not_signEq_prod_neg square_not_neg) 
                    show "Sum PO E E' A2 B2 C2" 
                    proof (rule pythagoras [of _ _ A PO B' _ C OA B], insert \<open>PO \<noteq> E\<close> 
                        \<open>Per A PO B'\<close> assms(3,4))
                      show "Length PO E E' A B' C"
                        using Ar2_def Length_def Out_def Prod_def \<open>Cong PO C A B'\<close> 
                          \<open>PO Out C E\<close> assms(4) ps_le by force 
                      show "Length PO E E' A PO OA" 
                      proof -
                        have "Col PO E OA"
                          using Ps_Col \<open>Ng PO E A\<close> \<open>Opp PO E E' A OA\<close> opp_neg_pos by blast 
                        moreover have "LtP PO E E' PO OA"
                          by (metis Ar2_def Out_def Ps_def \<open>Ng PO E A\<close> \<open>Opp PO E E' A OA\<close> 
                              diff_O_A diff_ar2 lep_neq__ltp opp_neg_pos ps_le) 
                        ultimately show ?thesis
                          by (meson Length_def Opp_def \<open>Opp PO E E' A OA\<close> \<open>PO \<noteq> E\<close> l15_3
                              ltp_to_lep not_cong_4321) 
                      qed
                      show "Length PO E E' B' PO B"
                        by (metis Ar2_def Length_def Out_def Prod_def \<open>Cong PO B' PO B\<close> 
                            \<open>PO Out B E\<close> assms(3) cong_3421 ps_le) 
                      show "Prod PO E E' OA OA A2"
                        using \<open>Opp PO E E' A OA\<close> assms(2) opp_same_square by force 
                    qed
                  }
                  {
                    assume "\<not> PO Out C E"
                    obtain OC where "Opp PO E E' C OC"
                      by (meson Diff_def Prod_def assms(4) sum_diff sum3_def sum3_exists)
                    have "Ng PO E C"
                      by (metis Ps_def SignEq_def \<open>A \<noteq> PO\<close> \<open>Cong PO C A B'\<close> \<open>Per A PO B'\<close> 
                          \<open>\<not> PO Out C E\<close> assms(4) cong_reverse_identity not_col_distincts 
                          not_signEq_prod_neg per_not_col square_not_neg) 
                    hence "Ps PO E OC"
                      using \<open>Opp PO E E' C OC\<close> opp_neg_pos by auto
                    obtain OA where "Opp PO E E' A OA"
                      by (meson Diff_def Prod_def assms(2) sum_diff sum3_def sum3_exists) 
                    have "Ng PO E A"
                      by (metis Ps_def SignEq_def \<open>A \<noteq> PO\<close> \<open>\<not> PO Out A E\<close> assms(2) 
                          not_signEq_prod_neg square_not_neg) 
                    show "Sum PO E E' A2 B2 C2" 
                    proof (rule pythagoras [of _ _ A PO B' _ OC OA B], insert \<open>PO \<noteq> E\<close> 
                        \<open>Per A PO B'\<close> assms(3))
                      show "Length PO E E' A B' OC" 
                      proof (unfold Length_def, intro strip conjI, insert \<open>PO \<noteq> E\<close>)
                        show "Col PO E OC"
                          by (simp add: Ps_Col \<open>Ps PO E OC\<close>) 
                        show "LeP PO E E' PO OC"
                          by (metis Ar2_def Prod_def Ps_def \<open>Col PO E OC\<close> \<open>Ps PO E OC\<close> 
                              assms(2) not_bet_and_out ps_le third_point) 
                        have "PO Midpoint C OC"
                          using opp_midpoint \<open>Opp PO E E' C OC\<close> by blast 
                        thus "Cong PO OC A B'"
                          using Cong_cases Midpoint_def \<open>Cong PO C A B'\<close> cong_inner_transitivity
                          by blast 
                      qed
                      show "Length PO E E' A PO OA" 
                      proof -
                        have "LeP PO E E' PO OA"
                          by (meson Ar2_def Out_def Prod_def Ps_def \<open>Ng PO E A\<close> 
                              \<open>Opp PO E E' A OA\<close> assms(2) opp_neg_pos ps_le) 
                        moreover have "Cong PO OA A PO"
                          using Cong_cases Opp_def \<open>Opp PO E E' A OA\<close> l15_3 by blast 
                        ultimately show ?thesis
                          by (metis Length_def Ps_Col \<open>A \<noteq> PO\<close> \<open>Ng PO E A\<close> \<open>Opp PO E E' A OA\<close> 
                              \<open>PO \<noteq> E\<close> neg_not_pos pos_null_neg) 
                      qed
                      show "Length PO E E' B' PO B"
                        by (metis Ar2_def Length_def Out_def Prod_def \<open>Cong PO B' PO B\<close> 
                            \<open>PO Out B E\<close> assms(3) cong_3421 ps_le) 
                      show "Prod PO E E' OA OA A2"
                        using \<open>Opp PO E E' A OA\<close> assms(2) opp_same_square by auto 
                      show "Prod PO E E' OC OC C2"
                        using \<open>Opp PO E E' C OC\<close> assms(4) opp_same_square by auto 
                    qed
                  }
                qed
              }
              {
                assume "\<not> PO Out B E"
                show "Sum PO E E' A2 B2 C2" 
                proof (cases "PO Out C E")
                  {
                    assume "PO Out C E"
                    obtain OB where "Opp PO E E' B OB"
                      by (metis Diff_def Prod_def assms(3) sum_diff sum3_def sum3_exists) 
                    have "Ng PO E B"
                      by (metis Ps_def SignEq_def \<open>PO B' Perp PO B\<close> \<open>\<not> PO Out B E\<close> assms(3)
                          not_signEq_prod_neg perp_not_eq_2 square_not_neg)
                    hence "Ps PO E OB"
                      using \<open>Opp PO E E' B OB\<close> opp_neg_pos by blast 
                    obtain OA where "Opp PO E E' A OA"
                      by (meson Diff_def Prod_def assms(2) sum_diff sum3_def sum3_exists) 
                    have "Ng PO E A"
                      by (metis Ps_def SignEq_def \<open>A \<noteq> PO\<close> \<open>\<not> PO Out A E\<close> assms(2) 
                          not_signEq_prod_neg square_not_neg) 
                    show "Sum PO E E' A2 B2 C2" 
                    proof (rule pythagoras [of _ _ A PO B' _ C OA OB], insert \<open>PO \<noteq> E\<close> 
                        \<open>Per A PO B'\<close> assms(4))
                      have "LtP PO E E' PO C"
                        by (metis Ar2_def Out_def PythRel_def \<open>PO Out C E\<close> assms(1) lep_neq__ltp
                            ps_le) 
                      thus "Length PO E E' A B' C"
                        by (simp add: Length_def Ps_Col \<open>Cong PO C A B'\<close> \<open>PO \<noteq> E\<close> 
                            ltP_pos ltp_to_lep) 
                      show "Length PO E E' A PO OA"
                      proof -
                        have "LtP PO E E' PO OA"
                          by (metis Ar2_def Out_def Ps_def \<open>LtP PO E E' PO C\<close> \<open>Ng PO E A\<close> 
                              \<open>Opp PO E E' A OA\<close> lep_neq__ltp ltP_ar2 opp_neg_pos ps_le) 
                        moreover have "Cong PO OA A PO"
                          using Cong_cases Opp_def \<open>Opp PO E E' A OA\<close> l15_3 by blast 
                        ultimately show ?thesis
                          by (simp add: Length_def Ps_Col \<open>PO \<noteq> E\<close> ltP_pos ltp_to_lep) 
                      qed
                      show "Length PO E E' B' PO OB" 
                      proof -
                        have "LtP PO E E' PO OB"
                          by (metis Ar2_def Out_def Prod_def Ps_def \<open>Ps PO E OB\<close> assms(4)
                              lep_neq__ltp ps_le) 
                        moreover have "Cong PO OB B' PO"
                          by (metis Cong_cases Midpoint_def \<open>Cong PO B' PO B\<close> \<open>Opp PO E E' B OB\<close>
                              cong_inner_transitivity opp_midpoint) 
                        ultimately show ?thesis
                          by (simp add: Length_def Ps_Col \<open>PO \<noteq> E\<close> \<open>Ps PO E OB\<close> ltp_to_lep) 
                      qed
                      show "Prod PO E E' OA OA A2"
                        using \<open>Opp PO E E' A OA\<close> assms(2) opp_same_square by blast 
                      show "Prod PO E E' OB OB B2"
                        using \<open>Opp PO E E' B OB\<close> assms(3) opp_same_square by auto 
                    qed
                  }
                  {
                    assume "\<not> PO Out C E"
                    obtain OC where "Opp PO E E' C OC"
                      by (meson Diff_def Prod_def assms(4) sum_diff sum3_def sum3_exists)
                    have "Ng PO E C"
                      by (metis Ar2_def Ng_def Out_def PythRel_def \<open>A \<noteq> PO\<close> \<open>Cong PO C A B'\<close> 
                          \<open>Per A PO B'\<close> \<open>\<not> PO Out C E\<close> assms(1) cong_reverse_identity 
                          not_col_distincts per_not_col third_point)
                    hence "Ps PO E OC"
                      using \<open>Opp PO E E' C OC\<close> opp_neg_pos by auto 
                    obtain OA where "Opp PO E E' A OA"
                      by (meson Diff_def Prod_def assms(2) sum_diff sum3_def sum3_exists) 
                    have "Ng PO E A"
                      by (metis Ps_def SignEq_def \<open>A \<noteq> PO\<close> \<open>\<not> PO Out A E\<close> assms(2) 
                          not_signEq_prod_neg square_not_neg) 
                    obtain OB where "Opp PO E E' B OB"
                      by (meson Ar2_def Diff_def Prod_def assms(3) diff_null) 
                    have "Ng PO E B"
                      by (metis Ps_def SignEq_def \<open>PO B' Perp PO B\<close> \<open>\<not> PO Out B E\<close> assms(3)
                          not_col_distincts not_signEq_prod_neg perp_not_col2 square_not_neg)
                    hence "Ps PO E OB"
                      using \<open>Opp PO E E' B OB\<close> opp_neg_pos by auto 
                    show "Sum PO E E' A2 B2 C2" 
                    proof (rule pythagoras [of _ _ A PO B' _ OC OA OB], insert \<open>PO \<noteq> E\<close> 
                        \<open>Per A PO B'\<close>)
                      show "Length PO E E' A B' OC" 
                      proof -
                        have "Col PO E OC"
                          by (simp add: Ps_Col \<open>Ps PO E OC\<close>) 
                        moreover have "LeP PO E E' PO OC"
                          by (metis Ar2_def Ps_def PythRel_def \<open>Ps PO E OC\<close> assms(1) calculation
                              not_bet_and_out ps_le third_point) 
                        moreover have "Cong PO OC A B'"
                          by (metis Cong_cases Opp_def \<open>Cong PO C A B'\<close> \<open>Opp PO E E' C OC\<close> 
                              cong_transitivity l15_3) 
                        ultimately show ?thesis
                          by (simp add: Length_def \<open>PO \<noteq> E\<close>) 
                      qed
                      show "Length PO E E' A PO OA" 
                      proof -
                        have "LtP PO E E' PO OA"
                          by (metis Ar2_def Out_def Prod_def Ps_def \<open>Ng PO E A\<close> 
                              \<open>Opp PO E E' A OA\<close> assms(2) lep_neq__ltp 
                              opp_neg_pos ps_le) 
                        moreover have "Cong PO OA A PO"
                          using Cong_cases Opp_def \<open>Opp PO E E' A OA\<close> l15_3 by blast 
                        ultimately show ?thesis
                          by (simp add: Length_def Ps_Col \<open>PO \<noteq> E\<close> ltP_pos ltp_to_lep) 
                      qed
                      show "Length PO E E' B' PO OB" 
                      proof -
                        have "LtP PO E E' PO OB"
                          by (metis Ar2_def Out_def Ps_def \<open>Opp PO E E' B OB\<close> \<open>Ps PO E OB\<close>
                              diff_O_A diff_ar2 lep_neq__ltp ps_le) 
                        moreover have "Cong PO OB B' PO"
                          by (metis Cong_cases Midpoint_def \<open>Cong PO B' PO B\<close> \<open>Opp PO E E' B OB\<close>
                              cong_inner_transitivity opp_midpoint) 
                        ultimately show ?thesis
                          by (simp add: Length_def Ps_Col \<open>PO \<noteq> E\<close> \<open>Ps PO E OB\<close> ltp_to_lep) 
                      qed
                      show "Prod PO E E' OA OA A2"
                        using \<open>Opp PO E E' A OA\<close> assms(2) opp_same_square by auto 
                      show "Prod PO E E' OB OB B2"
                        using \<open>Opp PO E E' B OB\<close> assms(3) opp_same_square by blast 
                      show "Prod PO E E' OC OC C2"
                        using \<open>Opp PO E E' C OC\<close> assms(4) opp_same_square by auto 
                    qed
                  }
                qed
              }
            qed
          }
        qed
      }
    qed
  }
  ultimately show ?thesis 
    by blast
qed

lemma PythRel_uniqueness:
  assumes "PythRel PO E E' A B C1"
    and "PythRel PO E E' A B C2"
    and "(Ps PO E C1 \<and> Ps PO E C2) \<or> C1 = PO"
  shows "C1 = C2" 
proof -
  have "\<not> Col PO E E'"
    using Ar2_def PythRel_def assms(1) by presburger 
  have "Col PO E A"
    using Ar2_def PythRel_def assms(1) by presburger 
  have "Col PO E B"
    using Ar2_def PythRel_def assms(1) by presburger 
  have "Col PO E C1"
    using Ps_Col assms(3) col_trivial_3 by blast 
  have "Col PO E C2"
    using Ar2_def PythRel_def assms(2) by presburger
  have "PO = B \<and> 
        (A = C1 \<or> Opp PO E E' A C1) \<or> (\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C1 A B')"
    using PythRel_def assms(1) by auto 
  moreover 
  have "PO = B \<and> 
        (A = C2 \<or> Opp PO E E' A C2) \<or> (\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C2 A B')"
    using PythRel_def assms(2) by presburger
  moreover
  {
    assume "PO = B" and  "A = C1 \<or> Opp PO E E' A C1" and "A = C2 \<or> Opp PO E E' A C2"
    moreover have "A = C1 \<and> A = C2 \<Longrightarrow> C1 = C2"
      by auto 
    moreover have "A = C1 \<and> Opp PO E E' A C2 \<Longrightarrow> C1 = C2"
      using \<open>\<not> Col PO E E'\<close> assms(3) neg_not_pos opp0_uniqueness pos_opp_neg by blast 
    moreover have "Opp PO E E' A C1 \<and> A = C2 \<Longrightarrow> C1 = C2"
      by (metis \<open>\<not> Col PO E E'\<close> assms(3) not_pos_and_neg opp0_uniqueness opp_comm opp_pos_neg) 
    moreover have "Opp PO E E' A C1 \<and> Opp PO E E' A C2 \<Longrightarrow> C1 = C2"
      using \<open>\<not> Col PO E E'\<close> opp_uniqueness by blast 
    ultimately have "C1 = C2" 
      by argo
  }
  moreover {
    assume "PO = B" and "A = C1 \<or> Opp PO E E' A C1" and 
      "\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C2 A B'"
    moreover {
      assume "A = C1" and "\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C2 A B'"
      then obtain B' where "PO B' Perp PO B" and "Cong PO B' PO B" and "Cong PO C2 A B'"
        by blast 
      hence "C1 = C2"
        using calculation(1) perp_distinct by blast
    }
    moreover {
      assume "Opp PO E E' A C1" and "\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C2 A B'" 
      then obtain B' where "PO B' Perp PO B" and "Cong PO B' PO B" and "Cong PO C2 A B'"
        by blast 
      hence "C1 = C2"
        using calculation(1) perp_distinct by blast 
    }
    ultimately have "C1 = C2"
      by argo
  }
  moreover {
    assume "\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C1 A B'" and "PO = B" and 
      "A = C2 \<or> Opp PO E E' A C2"
    then obtain B' where "PO B' Perp PO B" and "Cong PO B' PO B" and "Cong PO C1 A B'"
      by blast 
    hence "C1 = C2"
      using \<open>PO = B\<close> perp_not_eq_2 by blast 
  }
  moreover {
    assume "\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C1 A B'" and 
      "\<exists> B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C2 A B'"
    then obtain B1 where "PO B1 Perp PO B" and "Cong PO B1 PO B" and "Cong PO C1 A B1"
      by blast 
    obtain B2 where "PO B2 Perp PO B" and "Cong PO B2 PO B" and "Cong PO C2 A B2"
      using \<open>\<exists>B'. PO B' Perp PO B \<and> Cong PO B' PO B \<and> Cong PO C2 A B'\<close> by blast
    have "Cong PO B1 PO B2"
      by (meson \<open>Cong PO B1 PO B\<close> \<open>Cong PO B2 PO B\<close> cong_4312 cong_inner_transitivity) 
    have "Col PO B1 B2"
      using \<open>PO B1 Perp PO B\<close> \<open>PO B2 Perp PO B\<close> perp2__col by auto 
    hence "B1 = B2 \<or> PO Midpoint B1 B2"
      using \<open>Cong PO B1 PO B2\<close> col_permutation_4 l7_20_bis by blast
    moreover {
      assume "B1 = B2"
      hence "Cong PO C2 PO C1"
        using Cong_cases \<open>Cong PO C1 A B1\<close> \<open>Cong PO C2 A B2\<close> cong_inner_transitivity by blast 
      have "C1 = C2 \<or> PO Midpoint C1 C2"
        by (metis Mid_perm \<open>Col PO E C1\<close> \<open>Col PO E C2\<close> \<open>Cong PO C2 PO C1\<close> \<open>\<not> Col PO E E'\<close> 
            bet_col between_trivial col_transitivity_1 l7_20 not_col_permutation_4)
      moreover {
        assume "PO Midpoint C1 C2"
        hence " Ps PO E C1 \<and> Ps PO E C2 \<Longrightarrow> C1 = C2"
          by (meson Bet_cases Midpoint_def Ps_def bet_out__bet not_bet_and_out) 
        moreover have "C1 = PO \<Longrightarrow> C1 = C2"
          using \<open>Cong PO C2 PO C1\<close> cong_diff by blast 
        ultimately have "C1 = C2"
          using assms(3) by blast 
      }
      ultimately have "C1 = C2" 
        by argo
    }
    moreover {
      assume "PO Midpoint B1 B2"
      have "C1 = C2" 
      proof (cases "A = PO") 
        {
          assume "A = PO"
          hence "Cong PO C1 PO C2"
            by (metis Cong_cases \<open>Cong PO B1 PO B2\<close> \<open>Cong PO C1 A B1\<close> \<open>Cong PO C2 A B2\<close> 
                cong_inner_transitivity)
          thus "C1 = C2"
            by (metis Bet_cases Ps_def assms(3) bet_out__bet between_cong_3 between_trivial l6_6
                point_construction_different) 
        }
        {
          assume "A \<noteq> PO"
          hence "PO A Perp B1 PO" 
            using perp_col [of PO A B B1 PO] by (metis Perp_cases \<open>Col PO E A\<close> \<open>Col PO E B\<close>
                \<open>PO B1 Perp PO B\<close> \<open>\<not> Col PO E E'\<close> col_transitivity_1
                grid_not_par_4) 
          hence "Per A PO B1"
            using perp_per_1 by auto
          then obtain B2' where "PO Midpoint B1 B2'" and "Cong A B1 A B2'"
            using Per_def by blast 
          hence "B2 = B2'"
            using \<open>PO Midpoint B1 B2\<close> symmetric_point_uniqueness by blast 
          hence "Cong PO C1 PO C2"
            by (metis \<open>Cong A B1 A B2'\<close> \<open>Cong PO C1 A B1\<close> \<open>Cong PO C2 A B2\<close>
                cong_transitivity not_cong_3412) 
          have "PO Midpoint C1 C2 \<Longrightarrow> C1 = C2"
            by (metis Ps_def \<open>Cong PO C1 PO C2\<close> assms(3) bet_cong_eq bet_out__bet between_trivial
                l6_6 midpoint_bet not_bet_and_out) 
          thus "C1 = C2"
            by (metis Col_def \<open>Col PO E C1\<close> \<open>Col PO E C2\<close> \<open>Cong PO C1 PO C2\<close> \<open>\<not> Col PO E E'\<close>
                between_trivial col_transitivity_1 l7_20) 
        }
      qed
    }
    ultimately have "C1 = C2" 
      by argo
  }
  ultimately show ?thesis 
    by argo
qed

end
end