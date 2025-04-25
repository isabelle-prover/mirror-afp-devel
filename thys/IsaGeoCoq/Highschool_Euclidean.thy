(* IsaGeoCoq - Highschool_Euclidean.thy

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

theory Highschool_Euclidean

imports 
  Tarski_Neutral_Continuity
  Highschool_Neutral
  Tarski_Euclidean

begin

section "Highschool Euclidean dimensionless"

context Tarski_Euclidean

begin

lemma triangle_mid_par_strict_cong_aux: 
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B ParStrict Q P \<and> Cong A R P Q \<and> Cong B R P Q" 
proof -
  have "Col B P C" 
    by (simp add: assms(2) bet_col midpoint_bet)
  have "Col A Q C" 
    by (simp add: assms(3) bet_col midpoint_bet)
  have "Col A R B" 
    using Midpoint_def assms(4) bet_col by blast
  have "Cong B P C P" 
    using Midpoint_def assms(2) not_cong_1243 by blast
  have "Cong A Q C Q" 
    using Midpoint_def assms(3) not_cong_1243 by blast
  have "Cong A R B R" 
    using Midpoint_def assms(4) not_cong_1243 by blast
  obtain x where "Q Midpoint P x" 
    using symmetric_point_construction by blast
  hence "Cong P Q x Q" 
    using Cong_perm midpoint_cong by blast
  have "Col P Q x" 
    by (meson \<open>Q Midpoint P x\<close> bet_col midpoint_bet)
  {
    assume "Col A P C"
    hence "Col A B C" 
      by (metis \<open>Col B P C\<close> assms(2) col2__eq 
          col_permutation_5 midpoint_distinct_2)
    hence False 
      using assms(1) by blast
  }
  hence "\<not> Col A P C" 
    by blast
  hence "A \<noteq> P" 
    using col_trivial_1 by force
  have "ParallelogramStrict A P C x" 
    using \<open>Q Midpoint P x\<close> \<open>\<not> Col A P C\<close> assms(3) mid_plgs by force
  have "Cong A P C x" 
    by (metis l7_13 \<open>Q Midpoint P x\<close> assms(3) cong_4321)
  have "Cong A x P C" 
    by (metis l7_13 \<open>Q Midpoint P x\<close> assms(3) l7_2 not_cong_2134)
  have "Cong A x B P" 
    by (meson \<open>Cong A x P C\<close> \<open>Cong B P C P\<close> cong_4312 cong_inner_transitivity)
  have "A x Par B P" 
    by (metis (full_types) Par_cases \<open>A \<noteq> P\<close> \<open>Col B P C\<close> \<open>Cong A P C x\<close> 
        \<open>ParallelogramStrict A P C x\<close> \<open>Q Midpoint P x\<close> assms(2) assms(3) 
        col_par l12_17 l12_20 midpoint_distinct_1 par_not_par plgs_two_sides) 
  have "Parallelogram A x B P \<or> Parallelogram A x P B" 
    using par_cong_plg_2 by (simp add: \<open>A x Par B P\<close> \<open>Cong A x B P\<close>)
  hence "Cong A R P Q" 
    by (metis Cong_cases \<open>Col A Q C\<close> \<open>Col A R B\<close> \<open>Q Midpoint P x\<close> 
        assms(1) assms(4) col_transitivity_1 cong_cong_half_1 l7_17_bis 
        midpoint_distinct_3 plg_cong_2 plg_mid_2)
  moreover
  have "Cong B R P Q" 
    using \<open>Cong A R B R\<close> calculation cong_inner_transitivity by blast
  ultimately
  show ?thesis 
    using assms(1) assms(2) assms(3) triangle_mid_par_strict by blast
qed

lemma triangle_par_mid:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "A B Par Q P" and
    "Col Q A C"
  shows "Q Midpoint A C" 
proof -
  have "playfair_s_postulate \<longrightarrow> midpoint_converse_postulate"
    using playfair_s_postulate_implies_midpoint_converse_postulate by blast
  thus ?thesis 
    using assms(1) assms(2) assms(3) assms(4) midpoint_converse_postulate_def 
      not_col_permutation_2 parallel_uniqueness playfair_s_postulate_def by blast
qed

lemma triangle_mid_par_strict_cong_1:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B ParStrict Q P \<and> Cong A R P Q" 
  using assms(1) assms(2) assms(3) assms(4) triangle_mid_par_strict_cong_aux by blast

lemma triangle_mid_par_strict_cong_2:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B ParStrict Q P  \<and> Cong B R P Q" 
  using assms(1) assms(2) assms(3) assms(4) triangle_mid_par_strict_cong_aux by blast

lemma triangle_mid_par_strict_cong_simp:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" 
  shows "A B ParStrict Q P" 
  using assms(1) assms(2) assms(3) triangle_mid_par_strict by blast

lemma triangle_mid_par_strict_cong: 
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B ParStrict Q P \<and> A C ParStrict P R \<and> 
         B C ParStrict Q R \<and> Cong A R P Q \<and> 
         Cong B R P Q \<and> Cong A Q P R \<and> 
         Cong C Q P R \<and> Cong B P Q R \<and> Cong C P Q R"
  by (meson assms(1) assms(2) assms(3) assms(4) l7_2 not_col_permutation_1 
      not_col_permutation_5 par_strict_right_comm triangle_mid_par_strict_cong_aux)

lemma triangle_mid_par_flat_cong_aux:
  assumes "A \<noteq> B" and
    "Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B Par Q P \<and> Cong A R P Q \<and> Cong B R P Q" 
proof (cases "A = C")
  case True
  thus ?thesis 
    by (metis Cong_cases assms(1) assms(3) assms(4) assms(5) 
        cong_cong_half_1 l7_17_bis l8_20_2 mid_par_cong2 
        midpoint_col not_col_permutation_2 not_par_not_col)
next
  case False
  show ?thesis 
  proof (cases "B = C")
    case True
    thus ?thesis 
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) col_transitivity_1 
          col_trivial_3 cong_inner_transitivity cong_right_commutativity 
          l7_17 l7_2 midpoint_col midpoint_cong midpoint_distinct_2 
          not_par_inter_uniqueness)
  next
    case False
    hence "B \<noteq> C"
      by blast
    show ?thesis
    proof (cases "A = P")
      case True
      hence "Col A B Q" 
        by (metis assms(2) assms(4) col2__eq midpoint_col 
            midpoint_distinct_2 not_col_permutation_4)
      have "A B Par Q A" 
        by (metis True \<open>Col A B Q\<close> assms(1) assms(3) assms(4) midpoint_distinct_1 
            not_par_not_col par_right_comm)
      moreover have "Cong A R A Q" 
        by (metis True assms(1) assms(3) assms(4) assms(5) 
            cong_cong_half_1 l7_3_2 mid_par_cong1)
      moreover have "Cong B R A Q" 
        by (metis True assms(3) assms(4) assms(5) cong_cong_half_1 l7_2 midpoint_cong)
      ultimately show ?thesis 
        using True by force
    next
      case False
      obtain x where "Q Midpoint P x" 
        using symmetric_point_construction by blast
      show ?thesis
      proof (cases "P = x")
        case True
        thus ?thesis 
          by (metis \<open>Q Midpoint P x\<close> assms(1) assms(3) assms(4) l8_20_2 sym_preserve_diff)
      next
        case False
        hence "Parallelogram A P C x" 
          using \<open>Q Midpoint P x\<close> assms(4) mid_plg by blast
        hence "Cong A x B P" 
          by (meson assms(3) cong_symmetry cong_transitivity midpoint_cong plg_cong_2)
        have "P Q Par A B " 
        proof -
          have "P \<noteq> Q" 
            using False \<open>Q Midpoint P x\<close> is_midpoint_id by fastforce
          moreover have "Col P x Q" 
            using \<open>Q Midpoint P x\<close> col_permutation_1 midpoint_col by blast
          have "Parallelogram A x B P \<or> Parallelogram A x P B" 
          proof -
            have "Cong A x B P" 
              using \<open>Cong A x B P\<close> by auto
            moreover
            have "A x Par B P" 
            proof -
              {
                assume "B = P" 
                hence "B = C" 
                  using Midpoint_def assms(3) cong_diff_3 by blast
                hence False using \<open>B\<noteq> C\<close> by blast
              }
              moreover have "A x Par P C" 
                by (metis \<open>B \<noteq> C\<close> \<open>Q Midpoint P x\<close> assms(3) 
                    assms(4) mid_par_cong mid_par_cong2 
                    midpoint_cong_uniqueness midpoint_distinct_1 
                    not_col_distincts par_right_comm)
              moreover have "Col P C B" 
                using assms(3) col_permutation_5 midpoint_col by blast
              moreover have "Col P C P" 
                by (simp add: col_trivial_3)
              ultimately show ?thesis 
                using par_col2_par by blast
            qed
            ultimately show ?thesis
              using par_cong_plg_2 by blast
          qed
          moreover 
          have "P x Par A B" 
          proof -
            have "Parallelogram A x B P \<or> Parallelogram A x P B" 
              by (simp add: calculation(2))
            moreover
            have "Parallelogram A x B P \<longrightarrow> P x Par A B" 
              by (metis Par_cases \<open>Q Midpoint P x\<close> assms(1) assms(3) assms(4) assms(5) 
                  l12_17 l7_17_bis l8_20_2 midpoint_distinct_1 plg_mid_2)
            moreover
            have "Parallelogram A x P B \<longrightarrow> P x Par A B" 
              by (metis False Plg_perm \<open>Parallelogram A x B P \<longrightarrow> P x Par A B\<close> plg_par)
            ultimately show ?thesis
              by blast
          qed
          ultimately show ?thesis 
            using \<open>Col P x Q\<close> par_col_par_2 by blast
        qed
        hence "A B Par Q P" 
          using Par_cases by auto
        moreover
        have "Cong P Q A R" 
        proof -
          have "Parallelogram A x B P \<longrightarrow> Cong P Q A R" 
            by (metis Plg_perm \<open>B \<noteq> C\<close> \<open>Parallelogram A P C x\<close> plg_uniqueness)
          moreover 
          have "Parallelogram A x P B \<longrightarrow> Cong P Q A R"
            by (meson \<open>Q Midpoint P x\<close> assms(5) cong_cong_half_1 not_cong_3421 plg_cong_2)
          moreover
          have "Parallelogram A x B P \<or> Parallelogram A x P B" 
          proof -
            have "Cong A x B P" 
              using \<open>Cong A x B P\<close> by auto
            moreover
            have "A x Par B P" 
            proof -
              {
                assume "B = P" 
                hence "B = C" 
                  using Midpoint_def assms(3) cong_diff_3 by blast
                hence False using \<open>B\<noteq> C\<close> by blast
              }
              moreover have "A x Par P C" 
                by (metis Par_cases \<open>Q Midpoint P x\<close> assms(3) 
                    assms(4) calculation is_midpoint_id_2 
                    l12_17 l7_2)
              moreover have "Col P C B" 
                using assms(3) col_permutation_5 midpoint_col by blast
              moreover have "Col P C P" 
                by (simp add: col_trivial_3)
              ultimately show ?thesis 
                using par_col2_par by blast
            qed
            ultimately show ?thesis
              using par_cong_plg_2 by blast
          qed
          ultimately show ?thesis 
            by blast
        qed
        hence "Cong A R P Q" 
          using cong_symmetry by presburger
        moreover have "Cong B R P Q" 
          using assms(5) calculation(2) cong_transitivity 
            midpoint_cong not_cong_3421 by blast
        ultimately show ?thesis 
          by blast
      qed
    qed
  qed
qed

lemma triangle_mid_par_flat_cong_1: 
  assumes "A \<noteq> B" and
    "Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B Par Q P \<and> Cong A R P Q" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) 
    triangle_mid_par_flat_cong_aux by blast

lemma triangle_mid_par_flat_cong_2:
  assumes "A \<noteq> B" and
    "Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B Par Q P \<and> Cong B R P Q" 
  using assms(1) assms(2) assms(3) assms(4) assms(5) 
    triangle_mid_par_flat_cong_aux by blast

lemma triangle_mid_par_flat_cong:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B Par Q P \<and> A C Par P R \<and> B C Par Q R \<and>
       Cong A R P Q \<and> Cong B R P Q \<and> Cong A Q P R \<and> 
       Cong C Q P R \<and> Cong B P Q R \<and> Cong C P Q R"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) l7_2 not_col_permutation_2 
      not_col_permutation_5 par_right_comm triangle_mid_par_flat_cong_aux)

lemma triangle_mid_par_flat:
  assumes "A \<noteq> B" and
    "Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" 
  shows "A B Par Q P" 
  using assms(1) assms(2) assms(3) assms(4) midpoint_existence 
    triangle_mid_par_flat_cong_aux by blast

lemma triangle_mid_par:
  assumes "A \<noteq> B" and
    "P Midpoint B C" and
    "Q Midpoint A C" 
  shows "A B Par Q P" 
proof (cases "Col A B C")
  case True
  thus ?thesis 
    using assms(1) assms(2) assms(3) triangle_mid_par_flat by blast
next
  case False
  hence "A B ParStrict Q P" 
    by (simp add: assms(2) assms(3) triangle_mid_par_strict_cong_simp)
  thus ?thesis 
    using Par_def by blast
qed

lemma triangle_mid_par_cong:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "A B Par Q P \<and> A C Par P R \<and> B C Par Q R \<and>
       Cong A R P Q \<and> Cong B R P Q \<and> Cong A Q P R \<and> 
       Cong C Q P R \<and> Cong B P Q R \<and> Cong C P Q R"
proof (cases "Col A B C")
  case True
  thus ?thesis 
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
      triangle_mid_par_flat_cong by blast
next
  case False
  have "A B ParStrict Q P \<and> A C ParStrict P R \<and> 
        B C ParStrict Q R \<and> Cong A R P Q \<and> Cong B R P Q \<and> 
        Cong A Q P R \<and> Cong C Q P R \<and> Cong B P Q R \<and> Cong C P Q R"
    using triangle_mid_par_strict_cong False assms(4) assms(5) assms(6) by blast
  thus ?thesis 
    using par_strict_par by presburger
qed

lemma triangle_mid_par_cong_1:
  assumes "B \<noteq> C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows "B C Par Q R \<and> Cong B P Q R"
proof (cases "Col A B C")
  case True
  thus ?thesis 
    by (meson assms(1) assms(2) assms(3) assms(4) col_permutation_1 
        l7_2 par_right_comm triangle_mid_par_flat_cong_aux)
next
  case False
  thus ?thesis 
    using assms(2) assms(3) assms(4) not_col_distincts 
      triangle_mid_par_cong by blast
qed

lemma midpoint_thales: 
  assumes "\<not> Col A B C" and
    "P Midpoint A B" and
    "Cong P A P C"
  shows "Per A C B" 
  using assms(1) assms(2) assms(3) cong_sac__per 
    hypothesis_of_right_saccheri_quadrilaterals_def 
    plg_cong sac_plg t22_17__rah by blast

lemma midpoint_thales_reci:
  assumes "Per A C B" and
    "P Midpoint A B"
  shows "Cong P A P B \<and> Cong P B P C" 
proof (cases "Col A B C")
  case True
  thus ?thesis 
    by (metis Cong_cases assms(1) assms(2) cong_pseudo_reflexivity 
        l8_9 midpoint_cong not_col_permutation_5)
next
  case False
  have "Cong P A P B" 
    using Midpoint_def assms(2) not_cong_2134 by blast
  moreover
  have "Cong P B P C" 
  proof -
    obtain X where "X Midpoint A C" 
      using MidR_uniq_aux by blast
    hence "C B Par X P" 
      by (meson False Mid_cases assms(2) col_permutation_3 
          par_strict_par triangle_mid_par_strict_cong_simp)
    have "C B Perp C A" 
      by (metis False Perp_perm assms(1) not_col_distincts per_perp)
    have "Coplanar X P C A" 
      by (meson \<open>X Midpoint A C\<close> bet__coplanar coplanar_perm_11 midpoint_bet)
    hence "X P Perp C A" 
      using \<open>C B Par X P\<close> \<open>C B Perp C A\<close> cop_par_perp__perp by blast
    hence "C X Perp P X" 
      by (metis Perp_cases \<open>X Midpoint A C\<close> col_per_perp l8_16_1 
          midpoint_col midpoint_distinct_2 not_col_distincts 
          not_col_permutation_2)
    hence "Per P X C" 
      using Perp_perm perp_per_2 by blast
    thus ?thesis 
      by (meson \<open>X Midpoint A C\<close> calculation cong_symmetry 
          cong_transitivity l7_2 per_double_cong)
  qed
  ultimately
  show ?thesis 
    by simp
qed

lemma midpoint_thales_reci_1:
  assumes "Per A C B" and
    "P Midpoint A B"
  shows "Cong P A P B" 
  using midpoint_thales_reci assms(1) assms(2) by blast

lemma midpoint_thales_reci_2:
  assumes "Per A C B" and
    "P Midpoint A B"
  shows "Cong P B P C" 
  using midpoint_thales_reci assms(1) assms(2) by blast

lemma Per_mid_rectangle: 
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per B A C" and
    "I Midpoint B C" and
    "J Midpoint A C" and
    "K Midpoint A B" 
  shows "Rectangle A J I K" 
proof (cases "A = C")
  case True
  thus ?thesis 
    by (metis Rectangle_triv assms(1) assms(4) assms(5) assms(6) l7_17_bis l8_20_2)
next
  case False
  have H1: "A B Par J I \<and> A C Par I K \<and> B C Par J K \<and>
        Cong A K I J \<and> Cong B K I J \<and> Cong A J I K \<and> 
        Cong C J I K \<and> Cong B I J K \<and> Cong C I J K" 
    using False assms(1) assms(2) assms(4) assms(5) assms(6) 
      triangle_mid_par_cong by blast
  have "Plg A J I K" 
  proof (cases "Col A B C")
    case True
    thus ?thesis 
      using False assms(1) assms(3) col_permutation_2 l8_2 l8_9 by blast
  next
    case False
    hence "\<not> Col A B C" 
      by simp
    have "A B ParStrict J I \<and> A C ParStrict I K \<and>
          B C ParStrict J K \<and> Cong A K I J \<and> Cong B K I J \<and> 
          Cong A J I K \<and> Cong C J I K \<and> Cong B I J K \<and> Cong C I J K" 
      using False assms(4) assms(5) assms(6) triangle_mid_par_strict_cong by blast
    hence "A J ParStrict I K" 
      by (metis Col_perm assms(5) midpoint_col midpoint_distinct_1 
          par_strict_col_par_strict par_strict_symmetry)
    moreover
    have "A K Par J I" 
      by (metis Col_def Midpoint_def H1 assms(1) assms(6) cong_diff_3 
          not_par_not_col par_trans)
    ultimately
    show ?thesis 
      using pars_par_plg by blast
  qed
  moreover
  have "Per K A J" 
  proof -
    have "Per C A B" 
      by (simp add: assms(3) l8_2)
    moreover
    have "Col A C J" 
      using assms(5) col_permutation_1 midpoint_col by blast
    moreover
    have "Col A B K" 
      using assms(6) col_permutation_1 midpoint_col by blast
    ultimately
    show ?thesis 
      by (metis False assms(1) l8_2 per_col)
  qed
  hence "Per K A J \<or> Per I J A \<or> Per A K I \<or> Per J I K" 
    by blast
  ultimately
  show ?thesis 
    by (simp add: plg_per_rect)
qed

(** This is the usual proof presented in classroom based on
the midpoint theorem but this proof suffers from two problems.
It needs the fact that IJK are not collinear, 
which is not always the case when the quadrilateral is not convex.
It also needs the fact that A is different from C, and B is different from D.
The original proof by Varignon suffer from the same problem.
The original proof can be found page 138, Corollary IV:
http://polib.univ-lille3.fr/documents/B590092101_000000011.489_IMT.pdf
*)
lemma varignon:
  assumes "A \<noteq> C" and
    "B \<noteq> D" and
    "\<not> Col I J K" and
    "I Midpoint A B" and
    "J Midpoint B C" and
    "K Midpoint C D" and
    "L Midpoint A D"
  shows "Parallelogram I J K L" 
proof -
  have "I L Par J K" 
  proof -
    have "I L Par B D" 
      by (metis Mid_cases Par_perm assms(2) assms(4) assms(7) triangle_mid_par)
    moreover
    have "J K Par B D" 
      by (meson Mid_cases assms(2) assms(5) assms(6) par_symmetry triangle_mid_par)
    ultimately
    show ?thesis
      using not_par_one_not_par by blast
  qed
  moreover
  have "I J Par K L" 
  proof -
    have "I J Par A C" 
      by (meson Mid_cases assms(1) assms(4) assms(5) par_symmetry triangle_mid_par)
    moreover
    have "L K Par A C" 
      by (meson assms(1) assms(6) assms(7) par_symmetry triangle_mid_par)
    ultimately
    show ?thesis
      by (meson not_par_one_not_par par_left_comm)
  qed
  ultimately
  show ?thesis 
    by (simp add: assms(3) par_2_plg)
qed

lemma varignon_aux_aux:
  assumes "A \<noteq> C" and
    "J \<noteq> L" and
    "I Midpoint A B" and
    "J Midpoint B C" and
    "K Midpoint C D" and
    "L Midpoint A D"
  shows "Parallelogram I J K L" 
proof (cases "B = D")
  case True
  thus ?thesis 
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) 
        l7_17 l7_17_bis plg_trivial)
next
  case False
  obtain X where "X Midpoint B D" 
    using MidR_uniq_aux by blast
  have "B D Par L I \<and> Cong B X L I" 
    using False \<open>X Midpoint B D\<close> assms(3) assms(6) 
      triangle_mid_par_cong_1 by blast
  have "B D Par K J \<and> Cong B X K J" 
    using False \<open>X Midpoint B D\<close> triangle_mid_par_cong_1 assms(4) 
      assms(5) l7_2 by blast
  have "I L Par J K" 
    using Par_cases \<open>B D Par K J \<and> Cong B X K J\<close> \<open>B D Par L I \<and> Cong B X L I\<close> 
      not_par_one_not_par by blast
  have "Cong I L J K" 
    by (meson \<open>B D Par K J \<and> Cong B X K J\<close> \<open>B D Par L I \<and> Cong B X L I\<close> 
        cong_inner_transitivity cong_right_commutativity)
  obtain X' where "X' Midpoint A C" 
    using MidR_uniq_aux by blast
  have "A C Par J I \<and> Cong A X' J I" 
    using False \<open>X' Midpoint A C\<close> triangle_mid_par_cong_1 assms(1) 
      assms(3) assms(4) l7_2 by blast
  have "A C Par K L \<and> Cong A X' K L" 
    using False \<open>X' Midpoint A C\<close> triangle_mid_par_cong_1 assms(1) 
      assms(5) assms(6) l7_2 by blast
  have "I J Par K L" 
    using Par_cases \<open>A C Par J I \<and> Cong A X' J I\<close> \<open>A C Par K L \<and> Cong A X' K L\<close> 
      not_par_one_not_par by blast 
  have "Cong I J K L" 
    by (meson \<open>A C Par J I \<and> Cong A X' J I\<close> \<open>A C Par K L \<and> Cong A X' K L\<close> 
        cong_inner_transitivity cong_right_commutativity)
  thus ?thesis 
    by (meson Cong_cases \<open>Cong I L J K\<close> \<open>I J Par K L\<close> \<open>I L Par J K\<close> 
        assms(2) par_par_cong_cong_parallelogram par_symmetry)
qed

lemma varignon_aux:
  assumes (*"A \<noteq> C \<or> B \<noteq> D" and*)
    "J \<noteq> L" and
    "I Midpoint A B" and
    "J Midpoint B C" and
    "K Midpoint C D" and
    "L Midpoint A D"
  shows "Parallelogram I J K L" 
  by (metis assms(2) assms(3) assms(4) assms(5) assms(1) l7_17 
      l7_17_bis plg_trivial1 varignon_aux_aux)

lemma varignon_bis:
  assumes "A \<noteq> C \<or> B \<noteq> D" and
    "I Midpoint A B" and
    "J Midpoint B C" and
    "K Midpoint C D" and
    "L Midpoint A D"
  shows "Parallelogram I J K L" 
proof -
  have "Bet A I B" 
    using assms(2) midpoint_bet by blast
  have "Cong A I I B" 
    by (simp add: assms(2) midpoint_cong)
  have "Bet B J C" 
    using assms(3) midpoint_bet by blast
  have "Cong B J J C" 
    by (simp add: assms(3) midpoint_cong)
  have "Bet C K D" 
    using assms(4) midpoint_bet by blast
  have "Cong C K K D" 
    by (simp add: assms(4) midpoint_cong)
  have "Bet A L D" 
    using assms(5) midpoint_bet by blast
  have "Cong A L L D" 
    by (simp add: assms(5) midpoint_cong)
  show "Parallelogram I J K L" 
  proof (cases "J = L")
    case True
    hence "J = L" 
      by auto
    have "ParallelogramFlat I J K L"
    proof -
      obtain X where "X Midpoint B D" 
        using MidR_uniq_aux by blast
      have "Cong B X X D" 
        using \<open>X Midpoint B D\<close> midpoint_cong by auto
      have "Bet B X D" 
        by (simp add: \<open>X Midpoint B D\<close> midpoint_bet)
      have "Cong K C K D" 
        using \<open>Cong C K K D\<close> not_cong_2134 by blast
      have "Col I L K \<and> Col I L L \<and> Cong I L K L \<and> (I \<noteq> K \<or> L \<noteq> L)" 
      proof (cases "A = B")
        case True 
        hence "I = A \<and> I = B" 
          using assms(2) l8_20_2 by blast
        hence "C = D"
          using \<open>J = L\<close> \<open>A = B\<close> assms(3) assms(5) symmetric_point_uniqueness by blast
        hence "K = C" 
          using \<open>Bet C K D\<close> bet_neq12__neq by blast
        hence "K = D" 
          using \<open>C = D\<close> by auto
        have "X = L" 
          using True \<open>X Midpoint B D\<close> assms(5) l7_17 by blast
        have "X Midpoint I K"
          using assms(5) by (simp add: \<open>I = A \<and> I = B\<close> \<open>K = D\<close> \<open>X = L\<close>)
        hence "Cong X I X K" 
          by (meson midpoint_cong not_cong_2134)
        have "I \<noteq> K \<or> L \<noteq> L" 
          using \<open>I = A \<and> I = B\<close> \<open>K = C\<close> \<open>K = D\<close> assms(1) by blast
        thus ?thesis 
          using \<open>Cong X I X K\<close> \<open>X = L\<close> \<open>X Midpoint I K\<close> col_permutation_4 
            col_trivial_2 midpoint_col not_cong_2143 by blast
      next
        case False
        hence "A \<noteq> B" 
          by auto
        show ?thesis 
        proof (cases "A = D")
          case True
          hence "X Midpoint L B" 
            using True \<open>X Midpoint B D\<close> assms(2) assms(5) l7_17_bis l8_20_2 by blast
          have "A = L \<and> L = D" 
            using True \<open>Bet A L D\<close> bet_neq12__neq by blast
          have "L \<noteq> C \<or> B \<noteq> L" 
            using False True \<open>Bet A L D\<close> bet_neq12__neq by blast
          have "L Midpoint B C" 
            using \<open>J = L\<close> assms(3) by auto
          have "Cong K C K L" 
            using \<open>A = L \<and> L = D\<close> \<open>Cong K C K D\<close> by blast
          have "K Midpoint C L" 
            using \<open>A = L \<and> L = D\<close> assms(4) by force
          have "Cong X L X B" 
            using Cong_cases \<open>A = L \<and> L = D\<close> \<open>Cong B X X D\<close> by blast
          have "L \<noteq> B"
            using False \<open>A = L \<and> L = D\<close> by auto
          have "B \<noteq> C"
            using \<open>Bet B J C\<close> \<open>J = L\<close> \<open>L \<noteq> B\<close> bet_neq12__neq by blast
          show ?thesis 
          proof (cases "X = K")
            case True
            hence "X = K"
              by auto
            thus ?thesis 
              using \<open>A = L \<and> L = D\<close> \<open>J = L\<close> \<open>L \<noteq> B\<close> \<open>X Midpoint L B\<close> 
                assms(3) assms(4) l7_9_bis midpoint_distinct_3 by blast
          next
            case False
            hence "X \<noteq> K"
              by auto
            have "C \<noteq> L" 
              using \<open>B \<noteq> C\<close> \<open>L Midpoint B C\<close> is_midpoint_id_2 by blast
            hence "B L Par L K \<and> B C Par K X \<and> L C Par L X \<and> 
                  Cong B X K L \<and> Cong L X K L \<and> Cong B L K X \<and> 
                  Cong C L K X \<and> Cong L K L X \<and> Cong C K L X" 
              by (metis  \<open>B \<noteq> C\<close> \<open>K Midpoint C L\<close> \<open>L Midpoint B C\<close> \<open>L \<noteq> B\<close> 
                  \<open>X Midpoint B D\<close> assms(4) mid_par_cong par_distincts 
                  symmetric_point_construction triangle_mid_par_cong)
            hence "Cong X L K L" 
              using Cong_cases by blast
            moreover
            have "Col X L K" 
              by (metis Bet_cases \<open>A = L \<and> L = D\<close> 
                  \<open>B L Par L K \<and> B C Par K X \<and> L C Par L X \<and> 
                         Cong B X K L \<and> Cong L X K L \<and> Cong B L K X \<and> 
                         Cong C L K X \<and> Cong L K L X \<and> Cong C K L X\<close> 
                  assms(4) bet_col col_cong2_bet1 midpoint_bet par_id_1)
            moreover
            have "Col X L L" 
              using col_trivial_2 by auto
            have "X \<noteq> K \<or> K \<noteq> K" 
              by (simp add: False)
            moreover
            have "X = I" 
              using \<open>A = L \<and> L = D\<close> \<open>X Midpoint L B\<close> assms(2) l7_17 by blast
            hence "Cong I L K L" 
              using calculation(1) by auto
            ultimately
            show ?thesis 
              using \<open>Col X L L\<close> \<open>X = I\<close> by fastforce
          qed
        next
          case False
          hence "A \<noteq> D"
            by simp
          show ?thesis 
          proof (cases "B = D")
            case True
            hence "B = D" 
              by simp
            thus ?thesis 
              using \<open>J = L\<close> assms(1) assms(3) assms(5) l7_9_bis by force
          next
            case False
            hence  "B \<noteq> D" 
              by simp
            have H1: "A B Par L X \<and> A D Par X I \<and> B D Par L I \<and>
                  Cong A I X L \<and> Cong B I X L \<and> Cong A L X I \<and> 
                  Cong D L X I \<and> Cong B X L I \<and> Cong D X L I" 
              using triangle_mid_par_flat_cong False \<open>A \<noteq> B\<close> \<open>A \<noteq> D\<close> 
                \<open>X Midpoint B D\<close> assms(2) assms(5) triangle_mid_par_cong by blast
            hence "L Midpoint I K" 
            proof (cases "C = D")
              case True
              thus ?thesis 
                using \<open>A \<noteq> B\<close> \<open>J = L\<close> assms(3) assms(5) l7_9 by blast
            next
              case False
              hence "C \<noteq> D" 
                by simp
              show ?thesis 
              proof (cases "B = C")
                case True
                show ?thesis 
                proof -
                  have "I \<noteq> X" 
                    using H1 par_neq2 by blast
                  moreover have "Col I L X" 
                    by (metis H1 True \<open>Bet B X D\<close> \<open>J = L\<close> assms(3) bet_col 
                        between_symmetry col_cong2_bet1 l8_20_2 par_id_1)
                  moreover have "Cong I L L X" 
                    by (metis True H1 \<open>J = L\<close> assms(3) 
                        midpoint_distinct_2 not_cong_3421)
                  ultimately show ?thesis 
                    using MidR_uniq_aux True \<open>X Midpoint B D\<close> 
                      assms(4) cong_col_mid by blast
                qed
              next
                case False
                hence "B \<noteq> C"
                  by simp
                have H2: "B C Par X K \<and> B D Par K L \<and> C D Par X L \<and> 
                      Cong B L K X \<and> Cong C L K X \<and> Cong B X K L \<and> 
                      Cong D X K L \<and> Cong C K X L \<and> Cong D K X L" 
                  using triangle_mid_par_flat_cong False True \<open>B \<noteq> D\<close> \<open>C \<noteq> D\<close> 
                    \<open>X Midpoint B D\<close> assms(3) assms(4) triangle_mid_par_cong by blast
                show ?thesis 
                proof (cases "I = K")
                  case True
                  hence "I = K"
                    by simp
                  have "Parallelogram A D B C" 
                    using mid_plg True \<open>A \<noteq> B\<close> assms(2) assms(4) l7_2 by blast
                  hence "Parallelogram B D A C"
                    by (meson Plg_perm)
                  moreover
                  have "Parallelogram A B D C" 
                    using \<open>A \<noteq> D\<close> \<open>J = L\<close> assms(3) assms(5) mid_plg by blast
                  hence "Parallelogram B D C A" 
                    using Plg_perm by blast
                  ultimately
                  have False 
                    using \<open>B \<noteq> D\<close> plg_not_comm_1 by blast
                  thus ?thesis 
                    by blast
                next
                  case False
                  hence "I \<noteq> K" 
                    by auto
                  moreover
                  have "I L Par K L" 
                  proof -
                    have "I L Par B D" 
                      using Par_perm H1 by blast
                    moreover
                    have "B D Par K L" 
                      using H2 by blast
                    ultimately
                    show ?thesis 
                      using par_not_par by blast
                  qed
                  hence "Col I L K" 
                    using par_comm par_id_1 by blast
                  moreover
                  have "Cong I L L K" 
                    by (meson H1 H2 cong_inner_transitivity not_cong_4321)
                  ultimately
                  show ?thesis 
                    using cong_col_mid by blast
                qed
              qed
            qed
            thus ?thesis 
              by (metis Cong_cases False H1 col_permutation_4 
                  col_trivial_2 cong_diff midpoint_col midpoint_cong 
                  midpoint_distinct_3)
          qed
        qed
      qed
      thus ?thesis
        using ParallelogramFlat_def True by blast
    qed
    thus ?thesis 
      by (metis Mid_cases ParallelogramFlat_def assms(2) assms(3) assms(4) 
          assms(5) plg_comm2 varignon_aux)
  next
    case False
    thus ?thesis 
      using assms(2) assms(3) assms(4) assms(5) varignon_aux by blast
  qed
qed

lemma quadrileral_midpoints:
  assumes "\<not> Col I J K" and
    "I Midpoint A B" and
    "J Midpoint B C" and
    "K Midpoint C D" and
    "L Midpoint A D" and
    "X Midpoint I K" and
    "Y Midpoint J L"
  shows "X = Y" 
proof -
  have "Parallelogram I J K L" 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) l7_17 
        not_col_distincts varignon_bis)
  hence "X Midpoint J L" 
    using assms(6) plg_mid_2 by blast
  thus ?thesis 
    using assms(7) l7_17 by blast
qed

lemma is_circumcenter_coplanar:
  assumes "G IsCircumcenter A B C"
  shows "Coplanar G A B C" 
  using IsCircumcenter_def assms by blast

lemma circumcenter_cong_1:
  assumes "G IsCircumcenter A B C"
  shows "Cong A G B G" 
  using IsCircumcenter_def assms by blast

lemma circumcenter_cong_2:
  assumes "G IsCircumcenter A B C"
  shows "Cong B G C G" 
  using IsCircumcenter_def assms by blast

lemma circumcenter_cong_3:
  assumes "G IsCircumcenter A B C"
  shows "Cong C G A G" 
  by (meson assms circumcenter_cong_1 circumcenter_cong_2 
      cong_4312 cong_transitivity)

lemma circumcenter_cong:
  assumes "G IsCircumcenter A B C"
  shows "Cong A G B G \<and> Cong B G C G \<and> Cong C G A G" 
  by (meson assms circumcenter_cong_1 circumcenter_cong_2 circumcenter_cong_3)

lemma is_circumcenter_perm_1:
  assumes "G IsCircumcenter A B C"
  shows"G IsCircumcenter A C B" 
  by (meson IsCircumcenter_def assms circumcenter_cong_3 
      cong_transitivity coplanar_perm_1)

lemma is_circumcenter_perm_2:
  assumes "G IsCircumcenter A B C"
  shows"G IsCircumcenter B A C" 
  using Cong_cases IsCircumcenter_def assms circumcenter_cong_3 
    coplanar_perm_2 by metis

lemma is_circumcenter_perm_3:
  assumes "G IsCircumcenter A B C"
  shows"G IsCircumcenter B C A" 
  using assms is_circumcenter_perm_1 is_circumcenter_perm_2 by blast

lemma is_circumcenter_perm_4:
  assumes "G IsCircumcenter A B C"
  shows"G IsCircumcenter C A B" 
  by (simp add: assms is_circumcenter_perm_3)

lemma is_circumcenter_perm_5:
  assumes "G IsCircumcenter A B C"
  shows"G IsCircumcenter C B A" 
  using assms is_circumcenter_perm_1 is_circumcenter_perm_4 by blast

lemma is_circumcenter_perm:
  assumes "G IsCircumcenter A B C"
  shows"G IsCircumcenter A B C \<and> G IsCircumcenter A C B \<and>
        G IsCircumcenter B A C \<and> G IsCircumcenter B C A \<and>
        G IsCircumcenter C A B \<and> G IsCircumcenter C B A" 
  using assms is_circumcenter_perm_4 is_circumcenter_perm_5 by blast

lemma is_circumcenter_cases: 
  assumes "G IsCircumcenter A B C \<or> G IsCircumcenter A C B \<or>
           G IsCircumcenter B A C \<or> G IsCircumcenter B C A \<or>
           G IsCircumcenter C A B \<or> G IsCircumcenter C B A"
  shows "G IsCircumcenter A B C" 
  using assms is_circumcenter_perm by blast

lemma circumcenter_perp: 
  assumes (*"A \<noteq> B" and*)
    "B \<noteq> C" and
    (*"A \<noteq> C" and*)
    "G \<noteq> A'" and
    "G IsCircumcenter A B C" and
    "A' Midpoint B C"
  shows "G A' PerpBisect B C" 
  using IsCircumcenter_def assms(2) assms(4) assms(1) assms(3) 
    cong_mid_perp_bisect by blast

lemma exists_circumcenter: 
  assumes "\<not> Col A B C"
  shows "\<exists> G. G IsCircumcenter A B C" 
proof -
  have "triangle_circumscription_principle" 
    by (simp add: TarskiPP inter_dec_plus_par_perp_perp_imply_triangle_circumscription 
        playfair__universal_posidonius_postulate 
        tarski_s_euclid_implies_playfair_s_postulate 
        universal_posidonius_postulate__perpendicular_transversal_postulate)
  then obtain CC where "Cong A CC B CC" and "Cong A CC C CC" 
    and "Coplanar A B C CC" 
    using assms triangle_circumscription_principle_def by blast
  thus ?thesis 
    by (meson Cong_cases IsCircumcenter_def coplanar_perm_20 
        is_circumcenter_perm_2)
qed

lemma circumcenter_perp_all:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "A \<noteq> C" and
    "G \<noteq> A'" and
    "G \<noteq> B'" and
    "G \<noteq> C'" and
    "G IsCircumcenter A B C" and
    "A' Midpoint B C" and
    "B' Midpoint A C" and
    "C' Midpoint A B"
  shows "G A' PerpBisect B C \<and> G B' PerpBisect A C \<and> G C' PerpBisect A B" 
  by (meson assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) assms(8) assms(9) circumcenter_perp 
      is_circumcenter_perm_2 is_circumcenter_perm_4)

lemma circumcenter_intersect:
  assumes "A \<noteq> B" and
    "G \<noteq> C'" and
    "C' Midpoint A B" and
    "G A' PerpBisect B C" and
    "G B' PerpBisect A C"
  shows "G C' Perp A B" 
proof -
  have "Cong B G C G" 
    using assms(4) perp_bisect_cong_1 by blast
  have "Cong A G C G" 
    using assms(5) perp_bisect_cong_1 by auto
  hence "Cong A G B G" 
    by (meson \<open>Cong B G C G\<close> cong_inner_transitivity cong_symmetry)
  hence "G C' Perp C' A" 
    by (metis Per_def assms(1) assms(2) assms(3) cong_commutativity 
        midpoint_distinct_1 per_perp)
  hence "G C' Perp A C'" 
    using Perp_cases by blast
  thus ?thesis 
    by (simp add: \<open>Cong A G B G\<close> assms(1) assms(2) assms(3) 
        cong_mid_perp_bisect perp_bisect_perp)
qed

lemma is_circumcenter_uniqueness:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "A \<noteq> C" and
    "G1 IsCircumcenter A B C" and
    "G2 IsCircumcenter A B C"
  shows "G1 = G2" 
proof (cases "Col A B C")
  case True
  hence "Col A B C" 
    by auto
  obtain C' where "C' Midpoint A B" 
    using MidR_uniq_aux by blast
  {
    assume "G1 = C'" 
    hence "G1 Midpoint A B" 
      using \<open>C' Midpoint A B\<close> by auto
    {
      assume "Col B G1 C" and "Cong G1 B G1 C" 
      hence  "B = C \<or> G1 Midpoint B C" 
        by (simp add: l7_20)
    }
    moreover
    hence "Col B G1 C" 
      by (metis NCol_cases True \<open>G1 Midpoint A B\<close> assms(1) 
          col_transitivity_2 midpoint_col)
    moreover
    {
      assume "G1 Midpoint B C"
      hence False 
        using \<open>G1 Midpoint A B\<close> assms(3) l7_9_bis by auto
    }
    ultimately
    have False 
      using Cong_cases assms(2) assms(4) circumcenter_cong_2 by blast
  }
  hence "G1 C' PerpBisect A B" 
    by (meson \<open>C' Midpoint A B\<close> assms(1) assms(4) circumcenter_cong_1 
        cong_mid_perp_bisect)
  obtain A' where "A' Midpoint B C" 
    using MidR_uniq_aux by blast
  {
    assume "G1 = A'" 
    hence "G1 Midpoint B C" 
      using \<open>A' Midpoint B C\<close> by auto
    {
      assume "Col A G1 B" and "Cong G1 A G1 B" 
      hence  "A = B \<or> G1 Midpoint A B" 
        by (simp add: l7_20)
    }
    moreover
    hence "Col A G1 B" 
      using True \<open>G1 Midpoint B C\<close> assms(2) col2__eq col_permutation_5 
        midpoint_col by blast
    moreover
    {
      assume "G1 Midpoint A B"
      hence False 
        using \<open>G1 Midpoint B C\<close> assms(3) l7_9_bis by auto
    }
    ultimately
    have False 
      by (metis circumcenter_cong_1 assms(1) assms(4) cong_commutativity)
  }
  hence "G1 A' PerpBisect B C" 
    using IsCircumcenter_def \<open>A' Midpoint B C\<close> assms(2) assms(4) 
      cong_mid_perp_bisect by presburger
  have "G1 A' ParStrict G1 C'"
  proof -
    have "G1 A' Par G1 C'" 
    proof -
      have "Coplanar A B G1 G1" 
        using ncop_distincts by blast
      moreover
      have "Coplanar A B G1 C'" 
        by (simp add: \<open>C' Midpoint A B\<close> bet__coplanar coplanar_perm_3 midpoint_bet)
      moreover
      have "Coplanar A B A' C'" 
        by (simp add: \<open>C' Midpoint A B\<close> bet__coplanar coplanar_perm_3 midpoint_bet)
      moreover
      have "Coplanar A B A' G1" 
        by (meson IsCircumcenter_def \<open>A' Midpoint B C\<close> assms(4) 
            bet_cop__cop midpoint_bet ncoplanar_perm_18)
      moreover
      have "G1 A' Perp A B" 
        by (metis Perp_cases True \<open>G1 A' PerpBisect B C\<close> assms(1) assms(2) 
            calculation(4) col_permutation_1 cop_par_perp__perp ncoplanar_perm_7
            not_par_not_col perp_bisect_perp)
      moreover
      have "G1 C' Perp A B" 
        by (simp add: \<open>G1 C' PerpBisect A B\<close> perp_bisect_perp)
      ultimately
      show ?thesis
        using l12_9 by blast
    qed
    moreover
    have "A' \<noteq> C'" 
      using \<open>A' Midpoint B C\<close> \<open>C' Midpoint A B\<close> assms(3) l7_9_bis by blast
    {
      assume " Col G1 A' C'"
      have "Col C' A B" 
        by (simp add: \<open>C' Midpoint A B\<close> midpoint_col)
      hence "Col G1 A B" 
        by (metis True \<open>Col G1 A' C'\<close> \<open>A' Midpoint B C\<close> \<open>A' \<noteq> C'\<close> \<open>Col C' A B\<close> 
            assms(2) col_trivial_2 l6_16_1 midpoint_col not_col_permutation_2)
      have "Col A G1 B" 
        using \<open>Col G1 A B\<close> not_col_permutation_4 by blast
      have "Cong G1 A G1 B" 
        using IsCircumcenter_def assms(4) not_cong_2143 by blast
      {
        assume "Col A G1 B" and "Cong G1 A G1 B"
        have "A = B \<or> G1 Midpoint A B" 
          by (simp add: \<open>Col A G1 B\<close> \<open>Cong G1 A G1 B\<close> l7_20)
      }
      hence "G1 Midpoint A B" 
        by (simp add: \<open>Col A G1 B\<close> \<open>Cong G1 A G1 B\<close> assms(1))
      hence "False" 
        using \<open>C' Midpoint A B\<close> \<open>G1 = C' \<Longrightarrow> False\<close> l7_17 by auto
    }
    ultimately
    show ?thesis
      by (simp add: par_id)
  qed
  thus ?thesis 
    using not_par_strict_id by auto
next
  case False
  hence "\<not> Col A B C" 
    by auto
  obtain C' where "C' Midpoint A B" 
    using MidR_uniq_aux by blast
  show ?thesis 
  proof (cases "G1 = C'")
    case True
    hence "G1 = C'"
      by auto
    show ?thesis 
    proof (cases "G2 = C'")
      case True
      thus ?thesis 
        using \<open>G1 = C'\<close> by auto
    next
      case False
      hence "G2 \<noteq> C'"
        by auto
      have "Per A C B" 
        using Cong_cases True \<open>C' Midpoint A B\<close> \<open>\<not> Col A B C\<close> assms(4)
          circumcenter_cong_3 midpoint_thales by blast
      obtain B' where "B' Midpoint A C" 
        using MidR_uniq_aux by blast
      have "Bet A B' C" 
        by (simp add: \<open>B' Midpoint A C\<close> midpoint_bet)
      have "Cong A B' B' C" 
        by (simp add: \<open>B' Midpoint A C\<close> midpoint_cong)
      {
        assume "G2 = B'"
        have "Per A B C" 
        proof -
          have "\<not> Col A C B"
            using Col_cases \<open>\<not> Col A B C\<close> by blast
          moreover
          have "G2 Midpoint A C" 
            using \<open>B' Midpoint A C\<close> \<open>G2 = B'\<close> by blast
          moreover
          have "Cong G2 A G2 B"
            using assms(5) circumcenter_cong_1 not_cong_2143 by blast
          ultimately
          show ?thesis 
            using midpoint_thales by blast
        qed
        hence False 
          using \<open>Per A C B\<close> assms(2) l8_7 by blast
      }
      hence "G2 \<noteq> B'" 
        by auto
      obtain A' where "A' Midpoint B C" 
        using MidR_uniq_aux by blast
      {
        assume "G2 = A'"
        have "Per B A C" 
        proof -
          have "\<not> Col B C A" 
            using Col_cases \<open>\<not> Col A B C\<close> by blast
          moreover
          have "G2 Midpoint B C" 
            using \<open>A' Midpoint B C\<close> \<open>G2 = A'\<close> by auto
          moreover
          have "Cong G2 B G2 A" 
            using assms(5) circumcenter_cong_1 cong_4321 by blast
          ultimately
          show ?thesis 
            using midpoint_thales by blast
        qed
        hence False 
          using \<open>Per A C B\<close> assms(3) l8_2 l8_7 by blast
      }
      hence "G2 A' PerpBisect B C \<and> G2 B' PerpBisect A C \<and> G2 G1 PerpBisect A B" 
        by (metis False True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> 
            \<open>C' Midpoint A B\<close> \<open>G2 \<noteq> B'\<close> assms(1) assms(2) assms(3) assms(5) 
            circumcenter_perp_all)
      have "G1 A' PerpBisect B C" 
        by (metis True \<open>A' Midpoint B C\<close> \<open>C' Midpoint A B\<close> assms(2) 
            assms(3) assms(4) circumcenter_perp l7_9_bis)
      have "G1 B' PerpBisect A C" 
        by (metis Cong_cases circumcenter_cong_3 True \<open>B' Midpoint A C\<close> 
            \<open>C' Midpoint A B\<close> assms(2) assms(3) assms(4) 
            cong_mid_perp_bisect symmetric_point_uniqueness)
      have "Rectangle C B' G1 A'"
      proof -
        have "Per B C A" 
          using Per_cases \<open>Per A C B\<close> by blast
        moreover
        have "G1 Midpoint B A" 
          using Mid_cases True \<open>C' Midpoint A B\<close> by blast
        ultimately
        show ?thesis        
          by (metis Per_mid_rectangle \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> 
              assms(1) assms(2) l7_2)
      qed
      hence "Plg C B' G1 A'" 
        using Rectangle_Plg by blast
      hence "Parallelogram C B' G1 A'" 
        using parallelogram_equiv_plg by auto
      hence "Parallelogram B' C A' G1" 
        by (simp add: plg_comm2)
      {
        assume "Col G1 A' B'"
        hence "ParallelogramFlat B' C A' G1" 
          by (meson Plg_perm \<open>Parallelogram B' C A' G1\<close> col_permutation_4 
              plg_col_plgf plgf_sym)
        hence False 
          by (metis \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> \<open>Rectangle C B' G1 A'\<close> 
              assms(2) assms(3) midpoint_distinct_1 plgf_comm2 plgf_rect_id)
      }
      moreover
      have "Col G1 A' G2" 
      proof -
        have "Coplanar B C G2 G1" 
          by (metis IsCircumcenter_def True \<open>C' Midpoint A B\<close> assms(5) 
              bet_cop__cop between_symmetry coplanar_perm_12 
              coplanar_perm_19 midpoint_bet)
        moreover
        have "A' G1 Perp B C" 
          by (meson \<open>G1 A' PerpBisect B C\<close> perp_bisect_perp perp_left_comm)
        moreover
        have "A' G2 Perp B C" 
          by (meson \<open>G2 A' PerpBisect B C \<and> G2 B' PerpBisect A C \<and> G2 G1 PerpBisect A B\<close> 
              perp_bisect_perp perp_left_comm)
        ultimately
        show ?thesis 
          using cop_perp2__col not_col_permutation_1 by blast
      qed
      moreover
      have "Col B' G1 G2"
      proof -
        have "Coplanar A C G1 G2"
          by (metis (full_types) IsCircumcenter_def True 
              \<open>C' Midpoint A B\<close> 
              assms(5) bet_cop__cop coplanar_perm_13 
              coplanar_perm_18 midpoint_bet) 
        moreover
        have "B' G1 Perp A C" 
          using \<open>G1 B' PerpBisect A C\<close> perp_bisect_perp perp_left_comm by blast
        moreover
        have "B' G2 Perp A C" 
          by (simp add: 
              \<open>G2 A' PerpBisect B C \<and> G2 B' PerpBisect A C \<and> G2 G1 PerpBisect A B\<close> 
              perp_bisect_perp perp_left_comm)
        ultimately
        show ?thesis 
          using cop_perp2__col not_col_permutation_1 by blast
      qed
      ultimately
      have False 
        using False True col2__eq col_permutation_4 by blast
      thus ?thesis 
        by simp
    qed
  next
    case False
    hence "G1 \<noteq> C'"
      by auto
    show ?thesis 
    proof (cases "G2 = C'")
      case True
      hence "G2 = C'" 
        by auto
      have  "Per A C B" 
      proof -
        have "Cong G2 A G2 C" 
          using assms(5) circumcenter_cong not_cong_4321 by blast
        moreover
        have "G2 Midpoint A B"
          by (simp add: True \<open>C' Midpoint A B\<close>) 
        ultimately
        show ?thesis
          using \<open>\<not> Col A B C\<close> midpoint_thales by blast
      qed
      obtain B' where "B' Midpoint A C" 
        using MidR_uniq_aux by blast
      {
        assume "G1 = B'" 
        have "Per A B C" 
          by (metis circumcenter_cong_1 \<open>B' Midpoint A C\<close> \<open>G1 = B'\<close> 
              \<open>\<not> Col A B C\<close> assms(4) cong_commutativity midpoint_thales 
              not_col_permutation_5)
        hence False 
          using \<open>Per A C B\<close> assms(2) l8_7 by blast
      }
      obtain A' where "A' Midpoint B C" 
        using MidR_uniq_aux by blast
      {
        assume "G1 = A'" 
        have "Per B A C" 
          by (metis NCol_cases midpoint_thales \<open>A' Midpoint B C\<close> \<open>G1 = A'\<close>
              \<open>Per A C B\<close> assms(2) assms(3) assms(4) circumcenter_cong_1 
              l8_9 not_cong_4321)
        hence False 
          by (meson \<open>Per A C B\<close> assms(3) l8_2 l8_7)
      }
      have H1: "G1 A' PerpBisect B C \<and> G1 B' PerpBisect A C \<and> G1 G2 PerpBisect A B"
        using False True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> \<open>C' Midpoint A B\<close> 
          \<open>G1 = A' \<Longrightarrow> False\<close> \<open>G1 = B' \<Longrightarrow> False\<close> assms(1) assms(2) assms(3) 
          assms(4) circumcenter_perp_all by blast
      have "G2 A' PerpBisect B C" 
        by (metis True \<open>A' Midpoint B C\<close> \<open>C' Midpoint A B\<close> assms(2) 
            assms(3) assms(5) circumcenter_perp l7_9_bis)
      have "G2 B' PerpBisect A C" 
        by (metis Cong_cases circumcenter_cong_3 True \<open>B' Midpoint A C\<close> 
            \<open>C' Midpoint A B\<close> assms(2) assms(3) assms(5) cong_mid_perp_bisect
            symmetric_point_uniqueness)
      have "Rectangle C B' G2 A'" 
        by (metis Per_mid_rectangle True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> 
            \<open>C' Midpoint A B\<close> \<open>Per A C B\<close> assms(1) assms(2) l7_2 l8_2)
      hence "Plg C B' G2 A'" 
        using Rectangle_Plg by blast
      hence "Parallelogram C B' G2 A'" 
        using plg_to_parallelogram by auto
      hence "Parallelogram B' G2 A' C" 
        by (simp add: plg_permut)
      {
        assume "Col G2 A' B'"
        hence "ParallelogramFlat B' G2 A' C" 
          using \<open>Parallelogram B' G2 A' C\<close> not_col_permutation_1 
            plg_col_plgf by blast
        hence False 
          by (metis \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> \<open>Rectangle C B' G2 A'\<close> 
              assms(2) assms(3) midpoint_distinct_1 plgf_rect_id rect_permut)
      }
      moreover
      have "G1 \<noteq> B'" 
        using \<open>G1 = B' \<Longrightarrow> False\<close> by auto
      moreover
      have "Col G2 A' G1" 
      proof -
        have "Coplanar B C G1 G2" 
          by (metis IsCircumcenter_def True \<open>C' Midpoint A B\<close> assms(4) 
              bet_cop__cop between_symmetry coplanar_perm_12 
              coplanar_perm_19 midpoint_bet)
        moreover
        have "A' G1 Perp B C" 
          by (simp add: H1 perp_bisect_perp perp_left_comm)
        moreover
        have "A' G2 Perp B C" 
          by (simp add: \<open>G2 A' PerpBisect B C\<close> perp_bisect_perp perp_left_comm)
        ultimately
        show ?thesis 
          using col_permutation_2 cop_perp2__col by blast
      qed
      moreover
      have "Col G2 A' G2" 
        by (simp add: col_trivial_3)
      moreover
      have "Col B' G1 G1" 
        using col_trivial_2 by blast
      moreover
      have "Col B' G1 G2" 
      proof -
        have "Coplanar A C G2 G1" 
          by (metis (full_types) IsCircumcenter_def True \<open>C' Midpoint A B\<close>
              assms(4) bet_cop__cop coplanar_perm_13
              coplanar_perm_18 midpoint_bet)
        moreover
        have "B' G2 Perp A C" 
          using \<open>G2 B' PerpBisect A C\<close> perp_bisect_perp perp_left_comm by blast
        moreover
        have "B' G1 Perp A C" 
          by (simp add: H1 perp_bisect_perp perp_left_comm)
        ultimately
        show ?thesis 
          using col_permutation_5 cop_perp2__col by blast
      qed
      ultimately
      show ?thesis 
        using l6_21 by metis
    next
      case False
      hence "G2 \<noteq> C'" 
        by blast
      obtain B' where "B' Midpoint A C" 
        using MidR_uniq_aux by blast
      show ?thesis 
      proof (cases "G1 = B'")
        case True
        hence "G1 = B'"
          by auto
        show ?thesis 
        proof (cases "G2 = B'")
          case True
          thus ?thesis
            by (simp add: \<open>G1 = B'\<close>)
        next
          case False
          hence "G2 \<noteq> B'"
            by auto
          show ?thesis 
          proof -
            have "Per A B C" 
              by (metis midpoint_thales True \<open>B' Midpoint A C\<close> \<open>\<not> Col A B C\<close> 
                  assms(4) circumcenter_cong_1 col_permutation_5 not_cong_2143)
            obtain A' where "A' Midpoint B C" 
              using MidR_uniq_aux by blast
            {
              assume "G2 = A'"
              hence "Per B A C" 
                using \<open>A' Midpoint B C\<close> \<open>\<not> Col A B C\<close> assms(5) circumcenter_cong_1 
                  cong_4321 midpoint_thales not_col_permutation_1 by blast
              hence "A C ParStrict B C"
                by (meson Per_cases \<open>Per A B C\<close> assms(1) l8_7)
              hence False 
                by (meson col_trivial_3 par_strict_not_col_2)
            }
            have H3: "G2 A' PerpBisect B C \<and> G2 G1 PerpBisect A C \<and> G2 C' PerpBisect A B" 
              using False True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> 
                \<open>C' Midpoint A B\<close> \<open>G2 = A' \<Longrightarrow> False\<close> 
                \<open>G2 \<noteq> C'\<close> assms(1) assms(2) 
                assms(3) assms(5) circumcenter_perp_all by blast
            have "G1 A' PerpBisect B C" 
              by (metis True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> assms(1) 
                  assms(2) assms(4) circumcenter_perp sym_preserve_diff)
            have "G1 C' PerpBisect A B" 
              by (meson \<open>C' Midpoint A B\<close> \<open>G1 \<noteq> C'\<close> assms(1) assms(4) 
                  circumcenter_cong_1 cong_mid_perp_bisect)
            show ?thesis 
            proof -
              have "Rectangle B A' G1 C'" 
                by (metis Mid_cases Per_mid_rectangle 
                    True \<open>A' Midpoint B C\<close>
                    \<open>B' Midpoint A C\<close> \<open>C' Midpoint A B\<close> 
                    \<open>Per A B C\<close> assms(1) assms(3))
              hence "Plg B A' G1 C'" 
                using Rectangle_Plg by blast
              hence "Parallelogram A' G1 C' B" 
                by (meson plg_permut plg_to_parallelogram)
              {
                assume "Col G1 A' C'"
                hence "ParallelogramFlat A' G1 C' B'" 
                  by (metis \<open>C' Midpoint A B\<close> \<open>G1 \<noteq> C'\<close> 
                      \<open>Parallelogram A' G1 C' B\<close> \<open>Rectangle B A' G1 C'\<close> 
                      assms(1) col_permutation_4 midpoint_distinct_1
                      plg_col_plgf plgf_rect_id rect_permut)
                hence "Col A' G1 B" 
                  using \<open>Col G1 A' C'\<close> \<open>G1 \<noteq> C'\<close> \<open>Parallelogram A' G1 C' B\<close> 
                    \<open>Rectangle B A' G1 C'\<close> col_permutation_4 
                    plg_col_plgf plgf_rect_id 
                    rect_permut by blast
                hence "Col A B C" 
                proof -
                  have "A' \<noteq> B" 
                    using \<open>A' Midpoint B C\<close> assms(2) is_midpoint_id by blast
                  moreover
                  hence "A' \<noteq> C" 
                    using \<open>A' Midpoint B C\<close> is_midpoint_id_2 by blast
                  moreover
                  have "B' \<noteq> A" 
                    using \<open>B' Midpoint A C\<close> assms(3) is_midpoint_id by blast
                  moreover
                  hence "B' \<noteq> C" 
                    using \<open>B' Midpoint A C\<close> is_midpoint_id_2 by blast
                  moreover
                  have "Col A' B C" 
                    by (simp add: \<open>A' Midpoint B C\<close> midpoint_col)
                  moreover 
                  have "Col B' A C" 
                    by (simp add: \<open>B' Midpoint A C\<close> midpoint_col)
                  ultimately show ?thesis 
                    by (metis Col_perm True \<open>Col A' G1 B\<close> col_trivial_2 colx)
                qed
                hence False 
                  using \<open>\<not> Col A B C\<close> by blast
              }
              moreover
              have "Col G1 A' G2" 
              proof -
                have "Coplanar B C G2 G1" 
                  by (metis IsCircumcenter_def True \<open>B' Midpoint A C\<close> assms(5) 
                      bet_cop__cop between_symmetry coplanar_perm_13 
                      coplanar_perm_2 midpoint_bet)
                moreover
                have "A' G2 Perp B C" 
                  by (simp add: H3 perp_bisect_perp perp_left_comm)
                moreover
                have "A' G1 Perp B C" 
                  using \<open>G1 A' PerpBisect B C\<close> perp_bisect_perp 
                    perp_left_comm by presburger
                ultimately
                show ?thesis 
                  using col_permutation_2 cop_perp2__col by blast
              qed
              moreover
              have "Col C' G2 G1" 
              proof -
                have "Coplanar B C G2 G1" 
                  by (metis IsCircumcenter_def True \<open>B' Midpoint A C\<close> assms(5) 
                      bet_cop__cop between_symmetry coplanar_perm_13 
                      coplanar_perm_2 midpoint_bet)
                hence "Coplanar A B G1 G2" 
                  using \<open>B' Midpoint A C\<close> assms(5) IsCircumcenter_def
                  by (metis True bet_cop__cop midpoint_bet ncoplanar_perm_10 ncoplanar_perm_8)
                moreover
                have "C' G1 Perp A B" 
                  using \<open>G1 C' PerpBisect A B\<close> perp_bisect_perp 
                    perp_left_comm by blast
                moreover
                have "C' G2 Perp A B" 
                  by (simp add: H3 perp_bisect_perp perp_left_comm)
                ultimately
                show ?thesis 
                  using cop_perp2__col not_col_permutation_5 by blast
              qed
              ultimately
              show ?thesis 
                by (metis col_trivial_2 col_trivial_3 l6_21)
            qed
          qed
        qed
      next
        case False
        hence "G1 \<noteq> B'" 
          by auto 
        obtain A' where "A' Midpoint B C"   
          using MidR_uniq_aux by blast
        show ?thesis 
        proof (cases "G2 = B'")
          case True
          hence "G2 = B'"
            by auto
          { 
            assume "G1 = A'"
            hence "Cong G1 B G1 A" 
              using assms(4) circumcenter_cong_1 cong_4321 by blast
            hence "Per B A C" 
              using \<open>A' Midpoint B C\<close> \<open>G1 = A'\<close> \<open>\<not> Col A B C\<close> midpoint_thales
                not_col_permutation_1 by blast
            hence "A C ParStrict B C" 
              by (metis Mid_cases True \<open>B' Midpoint A C\<close> \<open>\<not> Col A B C\<close> assms(1) 
                  assms(5) circumcenter_cong_3 col_permutation_1 
                  is_circumcenter_perm_2 l8_2 
                  l8_7 midpoint_thales not_cong_2143)
            hence False 
              by (meson col_trivial_3 par_strict_not_col_2)
          }
          hence H4: "G1 A' PerpBisect B C \<and> G1 G2 PerpBisect A C \<and> G1 C' PerpBisect A B" 
            by (metis False True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> 
                \<open>C' Midpoint A B\<close> \<open>G1 \<noteq> C'\<close> assms(1) assms(2) assms(3) assms(4) 
                circumcenter_perp_all)
          have "G2 A' PerpBisect B C" 
            by (metis Mid_cases True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> 
                \<open>\<And>thesis. (\<And>C'. C' Midpoint A B \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1) 
                assms(2) assms(5) circumcenter_perp l8_20_2)
          have "G2 C' PerpBisect A B" 
            by (meson \<open>C' Midpoint A B\<close> \<open>G2 \<noteq> C'\<close> assms(1) assms(5) 
                circumcenter_cong_1 cong_mid_perp_bisect)
          show ?thesis 
          proof -
            {
              assume "Col G2 A' C'"  
              have "Rectangle B A' G2 C'" 
              proof -
                have "Per A B C" 
                  by (metis NCol_cases midpoint_thales True \<open>B' Midpoint A C\<close> 
                      \<open>\<not> Col A B C\<close> assms(5) circumcenter_cong_1 not_cong_2143)
                moreover
                have "G2 Midpoint A C" 
                  using True \<open>B' Midpoint A C\<close> by auto
                moreover
                have "A' Midpoint B C" 
                  by (simp add: \<open>A' Midpoint B C\<close>)
                moreover
                have "C' Midpoint B A" 
                  using Mid_cases \<open>C' Midpoint A B\<close> by blast
                ultimately
                show ?thesis 
                  by (metis Per_mid_rectangle assms(1) assms(3))
              qed
              hence "Parallelogram B A' G2 C'" 
                using Rectangle_Parallelogram by blast
              hence "ParallelogramFlat A' G2 C' B" 
                by (meson \<open>Col G2 A' C'\<close> col_permutation_4 plg_col_plgf plg_permut)
              hence False 
                by (metis \<open>C' Midpoint A B\<close> \<open>G2 \<noteq> C'\<close> \<open>Rectangle B A' G2 C'\<close> 
                    assms(1) midpoint_distinct_1 plgf_rect_id rect_permut)
            }
            moreover
            have "Col G2 A' G1" 
            proof -
              have "Coplanar B C G1 G2" 
                by (metis IsCircumcenter_def True \<open>B' Midpoint A C\<close> assms(4) 
                    bet_cop__cop between_symmetry coplanar_perm_13 
                    coplanar_perm_2 midpoint_bet)
              moreover
              have "A' G1 Perp B C" 
                by (simp add: H4 perp_bisect_perp perp_left_comm)
              moreover
              have "A' G2 Perp B C" 
                using \<open>G2 A' PerpBisect B C\<close> perp_bisect_perp perp_left_comm by blast
              ultimately
              show ?thesis 
                using cop_perp2__col not_col_permutation_1 by blast
            qed
            moreover
            have "Col C' G1 G2" 
            proof -
              have "Coplanar B C G1 G2" 
                by (metis IsCircumcenter_def True \<open>B' Midpoint A C\<close> assms(4) 
                    bet_cop__cop between_symmetry coplanar_perm_13 
                    coplanar_perm_2 midpoint_bet)
              hence "Coplanar C B G1 G2" 
                using coplanar_perm_6 by blast
              hence "Coplanar A B G1 G2"
                by (metis IsCircumcenter_def True \<open>B' Midpoint A C\<close> assms(4) bet_cop__cop 
                    coplanar_perm_14 coplanar_perm_21 coplanar_perm_23 midpoint_bet) 
              hence "Coplanar A B G2 G1" 
                using coplanar_perm_1 by blast
              moreover
              have "C' G1 Perp A B" 
                by (simp add: H4 perp_bisect_perp perp_left_comm)
              moreover
              have "C' G2 Perp A B" 
                using Perp_perm \<open>G2 C' PerpBisect A B\<close> perp_bisect_perp by blast
              ultimately
              show ?thesis 
                by (meson col_permutation_5 cop_perp2__col)
            qed
            ultimately
            show ?thesis 
              using Col_cases col_transitivity_2 by blast
          qed
        next 
          case False
          hence "G2 \<noteq> B'"
            by auto
          show ?thesis
          proof (cases "G1 = A'")
            case True
            hence "G1 = A'" 
              by auto
            show ?thesis 
            proof (cases "G2 = A'")
              case True
              hence "G2 = A'"
                by auto
              thus ?thesis 
                using \<open>G1 = A'\<close> by blast
            next
              case False
              hence "G2 \<noteq> A'"
                by auto
              have "Per C A B" 
                by (metis Per_perm midpoint_thales True \<open>A' Midpoint B C\<close> 
                    \<open>\<not> Col A B C\<close> assms(4) circumcenter_cong_1 col_permutation_2 
                    not_cong_4321)
              have "G2 G1 PerpBisect B C" 
                using False True \<open>A' Midpoint B C\<close> assms(2) assms(5)
                  circumcenter_perp by blast
              moreover have "G2 B' PerpBisect A C" 
                by (meson Cong_cases \<open>B' Midpoint A C\<close> \<open>G2 \<noteq> B'\<close> assms(3) assms(5)
                    circumcenter_cong cong_mid_perp_bisect)
              moreover have "G2 C' PerpBisect A B" 
                using \<open>C' Midpoint A B\<close> \<open>G2 \<noteq> C'\<close> assms(1) assms(5) 
                  circumcenter_cong cong_mid_perp_bisect by blast
              have "G1 B' PerpBisect A C" 
                by (metis Cong_cases circumcenter_cong_3 \<open>B' Midpoint A C\<close> 
                    \<open>G1 \<noteq> B'\<close> assms(3) assms(4) cong_mid_perp_bisect)
              have "G1 C' PerpBisect A B" 
                by (meson \<open>C' Midpoint A B\<close> \<open>G1 \<noteq> C'\<close> assms(1) assms(4) 
                    circumcenter_cong_1 cong_mid_perp_bisect)   
              show ?thesis 
              proof -
                {
                  assume "Col G1 B' C'" 
                  have "Rectangle A B' G1 C'" 
                    using Per_cases Per_mid_rectangle True \<open>A' Midpoint B C\<close> 
                      \<open>B' Midpoint A C\<close> \<open>C' Midpoint A B\<close> \<open>Per C A B\<close>
                      assms(1) assms(2) by blast
                  hence "Plg A B' G1 C'" 
                    by (meson Rectangle_Plg)
                  hence "Parallelogram B' G1 C' A" 
                    using Rectangle_Parallelogram \<open>Rectangle A B' G1 C'\<close>
                      rect_permut by blast
                  hence "ParallelogramFlat B' G1 C' A" 
                    by (simp add: \<open>Col G1 B' C'\<close> col_permutation_4 plg_col_plgf)
                  hence False 
                    using \<open>G1 \<noteq> B'\<close> \<open>G1 \<noteq> C'\<close> \<open>Rectangle A B' G1 C'\<close> 
                      plgf_rect_id rect_permut by blast
                }
                moreover
                have "Col G1 B' G2" (*631*)
                proof -
                  have "Coplanar A C G2 G1" 
                    by (metis IsCircumcenter_def True \<open>A' Midpoint B C\<close> 
                        assms(5) bet_cop__cop between_symmetry coplanar_perm_2 
                        midpoint_bet ncoplanar_perm_7)
                  moreover
                  have "B' G2 Perp A C" 
                    using \<open>G2 B' PerpBisect A C\<close> perp_bisect_perp perp_left_comm by blast
                  moreover
                  have "B' G1 Perp A C" 
                    using \<open>G1 B' PerpBisect A C\<close> perp_bisect_perp perp_left_comm by blast
                  ultimately
                  show ?thesis 
                    using col_permutation_2 cop_perp2__col by blast
                qed
                moreover
                have "Col C' G2 G1" 
                proof -
                  have "Coplanar A B G1 G2" 
                    using IsCircumcenter_def True \<open>A' Midpoint B C\<close> assms(5) 
                      bet_cop__cop coplanar_perm_9 midpoint_bet by blast
                  moreover
                  have"C' G1 Perp A B" 
                    by (simp add: \<open>G1 C' PerpBisect A B\<close> perp_bisect_perp perp_left_comm)
                  moreover
                  have "C' G2 Perp A B" 
                    using Perp_perm \<open>G2 C' PerpBisect A B\<close> perp_bisect_perp by blast
                  ultimately
                  show ?thesis 
                    using col_permutation_5 cop_perp2__col by blast
                qed
                ultimately
                show ?thesis 
                  by (metis col_trivial_2 col_trivial_3 l6_21)
              qed
            qed
          next
            case False
            hence "G1 \<noteq> A'" 
              by auto
            show ?thesis 
            proof (cases "G2 = A'")
              case True
              hence "G2 = A'"
                by auto
              have "Per C A B" 
              proof -
                have "\<not> Col B C A" 
                  using Col_cases \<open>\<not> Col A B C\<close> by blast
                moreover
                have "G2 Midpoint B C" 
                  by (simp add: True \<open>A' Midpoint B C\<close>)
                moreover
                have "Cong G2 B G2 A" 
                  using assms(5) circumcenter_cong_1 not_cong_4321 by blast
                ultimately
                show ?thesis 
                  using Per_perm midpoint_thales by blast
              qed
              have H5: "G1 G2 PerpBisect B C \<and> G1 B' PerpBisect A C \<and> G1 C' PerpBisect A B" 
                using False True \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> 
                  \<open>C' Midpoint A B\<close> \<open>G1 \<noteq> B'\<close> \<open>G1 \<noteq> C'\<close> assms(1) assms(2) assms(3) 
                  assms(4) circumcenter_perp_all by auto
              have "G2 B' PerpBisect A C" 
                by (metis Cong_cases circumcenter_cong_3 True 
                    \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> assms(1) assms(3) assms(5) 
                    cong_mid_perp_bisect l7_2 symmetric_point_uniqueness)
              have "G2 C' PerpBisect A B"
                by (meson \<open>C' Midpoint A B\<close> \<open>G2 \<noteq> C'\<close> assms(1) assms(5) 
                    circumcenter_cong_1 cong_mid_perp_bisect)
              show ?thesis 
              proof -
                {
                  assume "Col G2 B' C'" 
                  have "Rectangle A B' G2 C'" 
                    using Per_cases Per_mid_rectangle True \<open>A' Midpoint B C\<close> 
                      \<open>B' Midpoint A C\<close> \<open>C' Midpoint A B\<close> \<open>Per C A B\<close>
                      assms(1) assms(2) by blast
                  hence "Parallelogram A B' G2 C'" 
                    using Rectangle_Parallelogram by blast
                  hence "ParallelogramFlat B' G2 C' A" 
                    by (simp add: \<open>Col G2 B' C'\<close> col_permutation_4
                        plg_col_plgf plg_permut)
                  hence False 
                    by (metis \<open>B' Midpoint A C\<close> \<open>C' Midpoint A B\<close> 
                        \<open>Rectangle A B' G2 C'\<close> assms(1) assms(3) midpoint_distinct_1 
                        plgf_rect_id rect_permut)
                }
                moreover
                have "Col G2 B' G1"
                proof -
                  have "Coplanar A C G1 G2" 
                    by (metis IsCircumcenter_def True \<open>A' Midpoint B C\<close>
                        assms(4) bet_cop__cop between_symmetry coplanar_perm_2
                        midpoint_bet ncoplanar_perm_7)
                  moreover
                  have "B' G1 Perp A C" 
                    by (simp add: H5 perp_bisect_perp perp_left_comm)
                  moreover
                  have "B' G2 Perp A C" 
                    by (simp add: \<open>G2 B' PerpBisect A C\<close> 
                        perp_bisect_perp perp_bisect_sym_1)
                  ultimately
                  show ?thesis                  
                    by (meson col_permutation_2 cop_perp2__col)
                qed
                moreover
                have "Col C' G1 G2"   
                proof -
                  have "Coplanar A B G2 G1" 
                    using IsCircumcenter_def True \<open>A' Midpoint B C\<close> assms(4) 
                      bet_cop__cop coplanar_perm_9 midpoint_bet by blast 
                  moreover
                  have "C' G2 Perp A B" 
                    using \<open>G2 C' PerpBisect A B\<close> perp_bisect_perp 
                      perp_left_comm by blast
                  moreover
                  have "C' G1 Perp A B" 
                    by (simp add: H5 perp_bisect_perp perp_bisect_sym_1)
                  ultimately
                  show ?thesis                  
                    using col_permutation_5 cop_perp2__col by blast
                qed
                ultimately
                show ?thesis 
                  using Col_cases col_transitivity_2 by blast
              qed
            next
              case False
              hence "G2 \<noteq> A'"
                by auto
              have H6: "G1 A' PerpBisect B C \<and> G1 B' PerpBisect A C \<and> G1 C' PerpBisect A B"
                using \<open>A' Midpoint B C\<close> \<open>B' Midpoint A C\<close> \<open>C' Midpoint A B\<close> 
                  \<open>G1 \<noteq> A'\<close> \<open>G1 \<noteq> B'\<close> \<open>G1 \<noteq> C'\<close> assms(1) assms(2) assms(3) 
                  assms(4) circumcenter_perp_all by force
              hence H7: "G2 A' PerpBisect B C \<and> G2 B' PerpBisect A C \<and> G2 C' PerpBisect A B"
                by (metis False circumcenter_perp_all \<open>A' Midpoint B C\<close>
                    \<open>B' Midpoint A C\<close> \<open>C' Midpoint A B\<close> \<open>G2 \<noteq> B'\<close> \<open>G2 \<noteq> C'\<close> 
                    assms(1) assms(2) assms(3) assms(5))
              {
                assume "Col G1 A' B'"
                have "A C ParStrict C B"
                proof -
                  have "A C Par C B"
                  proof -
                    have "Coplanar G1 A' A C" 
                      using Coplanar_def \<open>B' Midpoint A C\<close> \<open>Col G1 A' B'\<close>
                        midpoint_col not_col_permutation_2 by blast
                    moreover
                    have "Coplanar G1 A' A B" 
                      by (meson IsCircumcenter_def \<open>A' Midpoint B C\<close> assms(4) 
                          bet_cop__cop coplanar_perm_4 midpoint_bet)
                    moreover
                    have "Coplanar G1 A' C C" 
                      using ncop_distincts by blast
                    moreover
                    have "Coplanar G1 A' C B" 
                      using Coplanar_def \<open>A' Midpoint B C\<close> col_trivial_2 
                        midpoint_col by blast
                    moreover
                    have "A C Perp G1 A'" 
                      using NCol_perm Perp_perm \<open>Col G1 A' B'\<close> H6 \<open>G1 \<noteq> A'\<close> 
                        perp_bisect_perp perp_col by blast
                    moreover
                    have "C B Perp G1 A'" 
                      using Perp_perm H6 perp_bisect_perp by blast
                    ultimately
                    show ?thesis 
                      using l12_9 by blast
                  qed
                  moreover
                  have "Col C B B" 
                    by (simp add: col_trivial_2)
                  moreover
                  have "\<not> Col A C B" 
                    by (simp add: \<open>\<not> Col A B C\<close> not_col_permutation_5)
                  ultimately
                  show ?thesis            
                    by (simp add: Par_def)
                qed
                hence False 
                  using col_trivial_2 par_strict_not_col_1 by blast
              }
              moreover
              have "Col G1 A' G2" 
              proof -
                have "Coplanar B C G2 G1" 
                  by (meson IsCircumcenter_def \<open>\<not> Col A B C\<close> assms(4) assms(5) 
                      coplanar_perm_9 coplanar_trans_1)
                moreover
                have "A' G2 Perp B C" 
                  by (simp add: H7 perp_bisect_perp perp_left_comm)
                moreover
                have "A' G1 Perp B C" 
                  by (meson H6 perp_bisect_perp perp_left_comm)
                ultimately
                show ?thesis 
                  using Col_perm cop_perp2__col by blast
              qed
              moreover
              have "Col B' G1 G2" 
              proof -
                have "Coplanar A C G2 G1" 
                  by (meson IsCircumcenter_def \<open>\<not> Col A B C\<close> assms(4) assms(5) 
                      coplanar_pseudo_trans ncop_distincts ncoplanar_perm_18)
                moreover
                have "B' G2 Perp A C" 
                  by (simp add: H7 perp_bisect_perp perp_left_comm)
                moreover
                have "B' G1 Perp A C" 
                  by (simp add: H6 perp_bisect_perp perp_left_comm)
                ultimately
                show ?thesis 
                  using NCol_cases cop_perp2__col by blast
              qed
              ultimately
              show ?thesis 
                using \<open>G2 \<noteq> B'\<close> col2__eq col_permutation_4 by blast 
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma midpoint_thales_reci_circum:
  assumes "Per A C B" and
    "P Midpoint A B"
  shows "P IsCircumcenter A B C"
  by (meson Cong_cases IsCircumcenter_def assms(1) assms(2) midpoint_col
      midpoint_thales_reci ncop__ncols)

lemma circumcenter_per:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C" and
    "P IsCircumcenter A B C"
  shows "P Midpoint A C" 
proof -
  obtain P' where "P' Midpoint A C" 
    using MidR_uniq_aux by blast
  hence "P' IsCircumcenter A C B" 
    using assms(3) midpoint_thales_reci_circum by blast
  thus ?thesis 
    by (metis \<open>P' Midpoint A C\<close> assms(1) assms(2) assms(3) assms(4) 
        is_circumcenter_perm_1 is_circumcenter_uniqueness per_distinct_1)
qed

lemma IsOrthocenter_coplanar: 
  assumes "H IsOrthocenter A B C"
  shows "Coplanar H A B C" 
proof -
  have "A H Perp B C" 
    using IsOrthocenter_def assms by blast
  thus ?thesis 
    using coplanar_perm_6 perp__coplanar by blast
qed

lemma construct_intersection:
  assumes "\<not> Col A B C" and
    "A C Par B X1" and
    "A B Par C X2" and
    "B C Par A X3"
  shows "\<exists> E. Col E A X3 \<and> Col E B X1" 
proof -
  have "Coplanar A X3 B X1"
  proof -
    have "Coplanar A B C A"
      using ncop_distincts by blast
    moreover
    have "Coplanar A B C X3" 
      using assms(4) coplanar_perm_12 par_cong_cop by blast
    moreover    
    have "Coplanar A B C B" 
      using ncop_distincts by blast
    moreover   
    have "Coplanar A B C X1" 
      by (meson assms(2) coplanar_perm_2 par_cong_cop)
    ultimately
    show ?thesis
      by (meson assms(1) coplanar_pseudo_trans)
  qed
  moreover
  have "\<not> A X3 Par B X1" 
    by (meson assms(1) assms(2) assms(4) par_comm par_id_4 par_symmetry par_trans)
  ultimately
  show ?thesis 
    using cop_npar__inter_exists by blast
qed

lemma not_col_par_col_diff: 
  assumes "\<not> Col A B C" and
    "A B Par C D" and
    "Col C D E"
  shows "A \<noteq> E" 
  using assms(1) assms(2) assms(3) col_trivial_3 not_strict_par1 by blast


lemma construct_triangle:
  assumes "\<not> Col A B C"
  shows "\<exists> D E F.
Col B D F \<and> Col A E F \<and> Col C D E \<and>
A B Par C D \<and> A C Par B D \<and> B C Par A E \<and>
A B Par C E \<and> A C Par B F \<and> B C Par A F \<and>
D \<noteq> E \<and> D \<noteq> F \<and> E \<noteq> F" 
proof -
  have "A \<noteq> B" 
    using assms col_trivial_1 by auto
  then obtain X1 where "A B Par C X1" 
    using parallel_existence1 by blast
  have "C \<noteq> B" 
    using assms col_trivial_2 by blast
  then obtain X3 where "B C Par A X3" 
    using parallel_existence1 by presburger 
  have "A \<noteq> C" 
    using assms col_trivial_3 by auto
  then obtain X2 where "A C Par B X2" 
    using parallel_existence1 by presburger 
  obtain D where "Col D B X2 \<and> Col D C X1" 
    using \<open>A B Par C X1\<close> \<open>A C Par B X2\<close> \<open>B C Par A X3\<close> assms col_permutation_2 
      construct_intersection par_left_comm by blast
  obtain E where "Col E A X3 \<and> Col E C X1"  
    using \<open>A B Par C X1\<close> \<open>A C Par B X2\<close> \<open>B C Par A X3\<close> assms col_permutation_5 
      construct_intersection par_left_comm by blast
  obtain F where "Col F A X3 \<and> Col F B X2" 
    using \<open>A B Par C X1\<close> \<open>A C Par B X2\<close> \<open>B C Par A X3\<close> assms 
      construct_intersection by blast
  have "A \<noteq> E" 
    by (metis \<open>A B Par C X1\<close> \<open>Col E A X3 \<and> Col E C X1\<close> assms 
        col_permutation_1 not_col_par_col_diff)
  have "A \<noteq> F" 
    using \<open>A C Par B X2\<close> \<open>A \<noteq> B\<close> \<open>Col F A X3 \<and> Col F B X2\<close> assms col_trivial_2 
      par_col2_par_bis par_id_3 by blast
  have "B \<noteq> D" 
    by (metis \<open>A B Par C X1\<close> \<open>C \<noteq> B\<close> \<open>Col D B X2 \<and> Col D C X1\<close> assms col_par 
        not_par_one_not_par par_distinct par_id_5)
  have "B \<noteq> F" 
    by (metis \<open>B C Par A X3\<close> \<open>Col F A X3 \<and> Col F B X2\<close> assms not_col_par_col_diff 
        not_col_permutation_1)
  have "C \<noteq> D" 
    by (metis NCol_perm Par_cases \<open>A C Par B X2\<close> \<open>Col D B X2 \<and> Col D C X1\<close>
        assms not_col_par_col_diff)
  have "C \<noteq> E" 
    by (metis \<open>B C Par A X3\<close> \<open>Col E A X3 \<and> Col E C X1\<close> assms col_trivial_3 
        not_col_permutation_4 par_reflexivity parallel_uniqueness)
  have "A B Par C D" 
    by (meson Col_perm \<open>A B Par C X1\<close> \<open>C \<noteq> D\<close> \<open>Col D B X2 \<and> Col D C X1\<close> par_col_par)
  moreover
  have "A C Par B D"
    using NCol_perm \<open>A C Par B X2\<close> \<open>B \<noteq> D\<close> \<open>Col D B X2 \<and> Col D C X1\<close> 
      par_col_par by blast
  moreover
  have "B C Par A E" 
    by (meson NCol_cases \<open>A \<noteq> E\<close> \<open>B C Par A X3\<close> \<open>Col E A X3 \<and> Col E C X1\<close> par_col_par)
  moreover
  have "A B Par C E" 
    by (meson Col_cases \<open>A B Par C X1\<close> \<open>C \<noteq> E\<close> 
        \<open>Col E A X3 \<and> Col E C X1\<close> par_col_par)
  moreover
  have "A C Par B F"
    by (meson Col_perm \<open>A C Par B X2\<close> \<open>B \<noteq> F\<close> 
        \<open>Col F A X3 \<and> Col F B X2\<close> par_col_par)
  moreover
  have "B C Par A F"
    by (meson \<open>A \<noteq> F\<close> \<open>B C Par A X3\<close> \<open>Col F A X3 \<and> Col F B X2\<close> 
        col_permutation_1 par_col_par)
  moreover
  have "D \<noteq> E" 
    by (metis Col_perm Par_perm assms calculation(1) calculation(2) 
        calculation(3) parallel_2_plg plgs_not_comm_2)
  moreover
  have "D \<noteq> F" 
    by (metis Par_cases assms calculation(1) calculation(5) 
        calculation(6) col_trivial_3 not_strict_par2 parallel_2_plg 
        plgs_not_comm_1)
  moreover
  have "Col B D F" 
    by (meson \<open>A C Par B D\<close> \<open>A C Par B F\<close> not_par_one_not_par 
        par_id_3 par_symmetry)
  moreover
  have "Col A E F" 
    by (meson \<open>B C Par A E\<close> \<open>B C Par A F\<close> not_par_one_not_par 
        par_id_3 par_symmetry)
  moreover
  have "Col C D E" 
    using \<open>A B Par C X1\<close> \<open>Col D B X2 \<and> Col D C X1\<close> \<open>Col E A X3 \<and> Col E C X1\<close> 
      l6_16_1 not_col_permutation_2 par_distinct by blast
  moreover
  have "E \<noteq> F" 
    by (metis assms calculation(11) calculation(2) calculation(4) 
        calculation(7) calculation(9) col2__eq not_par_one_not_par 
        par_col2_par_bis par_id)
  ultimately
  show ?thesis 
    by blast
qed

lemma diff_not_col_col_par4_mid: 
  assumes "D \<noteq> E" and
    "\<not> Col A B C" and
    "Col C D E" and
    "A B Par C D" and
    "A B Par C E" and
    "A E Par B C" and
    "A C Par B D"
  shows "C Midpoint D E" 
proof -
  have "ParallelogramStrict A B C E" 
    by (simp add: assms(2) assms(5) assms(6) parallel_2_plg)
  moreover
  have "ParallelogramStrict C A B D" 
    by (meson assms(2) assms(4) assms(7) not_col_permutation_2 
        par_left_comm par_symmetry parallel_2_plg)
  ultimately
  show ?thesis 
    by (meson Col_cases assms(1) assms(3) cong_transitivity l7_20 
        plgs_cong_1 plgs_cong_2)
qed

lemma altitude_is_perp_bisect:
  assumes "A \<noteq> P" and
    "E \<noteq> F" and
    "A A1 Perp B C" and
    "Col P A1 A" and
    "Col A E F" and
    "B C Par A E" and
    "A Midpoint E F"
  shows "A P PerpBisect E F" 
proof -
  have "A P Perp E F" 
  proof -
    have "B C Par E F" 
      by (metis assms(2) assms(5) assms(6) col_par par_neq2 par_not_par)
    moreover
    have "B C Perp A P" 
      by (metis Perp_cases assms(1) assms(3) assms(4)
          col_permutation_3 perp_col)
    ultimately
    show ?thesis 
      using cop_par_perp__perp by (metis Perp_cases assms(5) 
          ncop__ncols not_col_permutation_2)
  qed
  thus ?thesis 
    using assms(7) perp_mid_perp_bisect by blast
qed

lemma altitude_intersect:
  assumes "\<not> Col A B C" and
    "A A1 Perp B C" and
    "B B1 Perp A C" and
    "C C1 Perp A B" and
    "Col P A A1" and
    "Col P B B1" 
  shows "Col P C C1" 
proof -
  obtain D E F where "Col B D F" and "Col A E F" and "Col C D E" and
    "A B Par C D" and "A C Par B D" and "B C Par A E" and
    "A B Par C E" and "A C Par B F" and "B C Par A F" and
    "D \<noteq> E" and "D \<noteq> F" and "E \<noteq> F" 
    using assms(1) construct_triangle by blast
  have "A Midpoint E F" 
    by (meson NCol_cases Par_cases \<open>A B Par C E\<close> \<open>A C Par B F\<close> \<open>B C Par A E\<close> 
        \<open>B C Par A F\<close> \<open>Col A E F\<close> \<open>E \<noteq> F\<close> assms(1) diff_not_col_col_par4_mid)
  have "B Midpoint D F" 
    by (metis Col_perm Par_cases \<open>A B Par C D\<close> \<open>A C Par B D\<close> \<open>A C Par B F\<close> 
        \<open>B C Par A F\<close> \<open>Col B D F\<close> \<open>D \<noteq> F\<close> assms(1) diff_not_col_col_par4_mid)
  have "C Midpoint D E" 
    by (meson diff_not_col_col_par4_mid \<open>A B Par C D\<close> \<open>A B Par C E\<close> 
        \<open>A C Par B D\<close> \<open>B C Par A E\<close> \<open>Col C D E\<close> \<open>D \<noteq> E\<close> assms(1) par_symmetry)
  show ?thesis 
  proof (cases "A = P")
    case True
    have "C A Perp B B1" 
      using Perp_perm assms(3) by blast
    hence "C A Perp A B" 
      by (metis NCol_perm True assms(4) assms(6) col_trivial_3 
          perp_col2_bis perp_not_eq_2)
    moreover
    have "Coplanar A B A C1" 
      using ncop_distincts by blast
    ultimately
    show ?thesis 
      using assms(4) True col_permutation_4 cop_perp2__col by blast     
  next
    case False
    hence "A \<noteq> P"
      by auto
    show ?thesis
    proof (cases "B = P")
      case True
      have "Coplanar A B B C1" 
        by (meson ncop_distincts)
      moreover
      have "C B Perp A A1" 
        using Perp_cases assms(2) by blast
      hence "C B Perp A B" 
        using Col_cases False True assms(5) perp_col1 by blast
      ultimately
      show ?thesis 
        using assms(4) True cop_perp2__col not_col_permutation_4 by blast
    next
      case False
      hence "B \<noteq> P"
        by auto
      show ?thesis
      proof (cases "C = P")
        case True
        thus ?thesis 
          by (simp add: col_trivial_1)
      next
        case False
        hence "C \<noteq> P" 
          by simp
        have "A P PerpBisect E F" 
          by (metis Col_perm \<open>A Midpoint E F\<close> \<open>A \<noteq> P\<close> \<open>B C Par A E\<close> 
              \<open>Col A E F\<close> \<open>E \<noteq> F\<close> altitude_is_perp_bisect assms(2) assms(5))
        have "B P PerpBisect D F" 
          by (meson \<open>A C Par B D\<close> \<open>B Midpoint D F\<close> \<open>B \<noteq> P\<close> 
              \<open>Col B D F\<close> \<open>D \<noteq> F\<close> altitude_is_perp_bisect assms(3) assms(6) 
              col_permutation_5)
        have "P C Perp D E" 
        proof -
          have "P A PerpBisect E F" 
            by (meson \<open>A P PerpBisect E F\<close> perp_bisect_sym_1)
          moreover
          have "P B PerpBisect D F"
            using \<open>B P PerpBisect D F\<close> perp_bisect_sym_1 by blast
          ultimately
          show ?thesis 
            using False \<open>C Midpoint D E\<close> \<open>D \<noteq> E\<close> circumcenter_intersect by auto
        qed
        hence "C1 C Perp D E" 
        proof -
          have "A B Par D E" 
            by (metis \<open>A B Par C D\<close> \<open>C Midpoint D E\<close> \<open>Col C D E\<close> \<open>D \<noteq> E\<close>
                col_par midpoint_distinct_1 par_not_par)
          moreover
          have "Coplanar D E C1 C" 
            using \<open>Col C D E\<close> col_permutation_1 ncop__ncols by blast
          moreover
          have "A B Perp C1 C" 
            using Perp_perm assms(4) by blast
          ultimately
          show ?thesis 
            using Perp_perm cop_par_perp__perp by blast
        qed
        hence "Coplanar D E C1 P" 
        proof -
          have "Coplanar A B C D" 
            by (simp add: \<open>A B Par C D\<close> par_cong_cop)
          moreover
          have "Coplanar A B C E" 
            using \<open>A B Par C E\<close> par_cong_cop by auto
          moreover 
          have "Coplanar A B C C1" 
            using assms(4) ncoplanar_perm_16 perp__coplanar by blast
          moreover 
          have "Coplanar A C B B1" 
            by (meson assms(3) coplanar_perm_16 perp__coplanar)
          hence "Coplanar A B C P" 
            by (metis Col_cases Perp_cases assms(3) assms(6) 
                col_cop__cop ncoplanar_perm_12 ncoplanar_perm_6 perp_not_eq_2)
          ultimately
          show ?thesis 
            using assms(1) coplanar_pseudo_trans by presburger
        qed
        show ?thesis 
          by (meson Perp_cases \<open>C1 C Perp D E\<close> \<open>Coplanar D E C1 P\<close> 
              \<open>P C Perp D E\<close> col_permutation_2 cop_perp2__col)
      qed
    qed
  qed
qed

lemma IsOrthocenter_cases:
  assumes "G IsOrthocenter A B C \<or> G IsOrthocenter A C B \<or>
           G IsOrthocenter B A C \<or> G IsOrthocenter B C A \<or>
           G IsOrthocenter C A B \<or> G IsOrthocenter C B A"
  shows "G IsOrthocenter A B C" 
  using Col_cases IsOrthocenter_def Perp_cases assms by blast

lemma IsOrthocenter_perm:
  assumes "G IsOrthocenter A B C"
  shows "G IsOrthocenter A B C \<and> G IsOrthocenter A C B \<and>
         G IsOrthocenter B A C \<and> G IsOrthocenter B C A \<and>
         G IsOrthocenter C A B \<and> G IsOrthocenter C B A" 
  using IsOrthocenter_cases assms by blast

lemma IsOrthocenter_perm_1:
  assumes "G IsOrthocenter A B C"
  shows "G IsOrthocenter A C B"
  using IsOrthocenter_cases assms by blast

lemma IsOrthocenter_perm_2:
  assumes "G IsOrthocenter B A C"
  shows "G IsOrthocenter A C B" 
  using IsOrthocenter_cases assms by blast

lemma IsOrthocenter_perm_3:
  assumes "G IsOrthocenter B C A"
  shows "G IsOrthocenter A C B"
  using IsOrthocenter_cases assms by blast

lemma IsOrthocenter_perm_4:
  assumes "G IsOrthocenter C A B"
  shows "G IsOrthocenter A C B" 
  using IsOrthocenter_cases assms by blast

lemma IsOrthocenter_perm_5:
  assumes "G IsOrthocenter C B A"
  shows "G IsOrthocenter A C B" 
  using IsOrthocenter_cases assms by blast

lemma orthocenter_per:
  assumes "Per A B C" and
    "H IsOrthocenter A B C"
  shows "H = B" 
proof -
  have "A B Perp B C" 
    by (metis IsOrthocenter_def assms(1) assms(2) per_perp perp_not_eq_2)
  hence "A H Par A B" 
    using l12_9 by (metis (no_types, lifting) IsOrthocenter_def Par_def 
        assms(2) col_perp2_ncol_col cop_npar__inter_exists 
        ncop_distincts parallel_uniqueness)
  hence "Col A B H" 
    using par_id_3 by auto
  have "C H Par B C" 
  proof -
    have "C H Perp A B" 
      using IsOrthocenter_def assms(2) by blast
    moreover
    have "B C Perp A B" 
      using Perp_perm \<open>A B Perp B C\<close> by blast
    ultimately show ?thesis
      using l12_9 
      by (metis Col_cases Par_def \<open>Col A B H\<close> col_perp2_ncol_col 
          not_col_distincts perp_not_col)
  qed
  thus ?thesis 
    by (meson IsOrthocenter_def \<open>A H Par A B\<close> assms(2) l8_16_1 
        par_id_4 par_right_comm)
qed

lemma orthocenter_col:
  assumes "Col H B C" and
    "H IsOrthocenter A B C"
  shows "H = B \<or> H = C" 
proof -
  have "H PerpAt B C A H" 
    by (metis IsOrthocenter_def NCol_perm Perp_perm assms(1) 
        assms(2) l8_15_1)
  show ?thesis
  proof (cases "B = H")
    case True
    thus ?thesis 
      by blast
  next
    case False
    hence "B \<noteq> H"
      by simp
    have "A H Perp B H" 
      by (meson False IsOrthocenter_def assms(1) assms(2) col_trivial_2 
          not_col_permutation_2 perp_col2_bis)
    have False
      by (metis Col_cases IsOrthocenter_def assms(1) assms(2) col_trivial_2 
          l8_16_1 l8_7)
    thus ?thesis 
      by auto
  qed
qed

lemma intersection_two_medians_exist:
  assumes "\<not> Col A B C" and
    "I Midpoint B C" and
    "J Midpoint A C"
  shows "\<exists> G. Col G A I \<and> Col G B J" 
proof -
  have "Bet A J C" 
    by (simp add: assms(3) midpoint_bet)
  moreover
  have "Bet B I C" 
    by (simp add: assms(2) midpoint_bet)
  ultimately
  obtain G where "Bet J G B \<and> Bet I G A" 
    using inner_pasch by blast
  thus ?thesis 
    using Col_def by blast
qed

lemma intersection_two_medians_exist_unique:
  assumes "\<not> Col A B C" and
    "I Midpoint B C" and
    "J Midpoint A C"
  shows "\<exists>! G. Col G A I \<and> Col G B J" 
proof -
  obtain G where "Col G A I \<and> Col G B J"
    using intersection_two_medians_exist assms(1) assms(2) assms(3) by blast
  moreover
  {
    fix G1
    assume "Col G1 A I" and "Col G1 B J" 
    moreover
    have "\<not> Col A I B" 
      by (metis assms(1) assms(2) col_permutation_1 col_transitivity_2 
          midpoint_col midpoint_distinct_1)
    moreover
    have "B \<noteq> J" 
      using assms(1) assms(3) bet_col midpoint_bet by blast
    ultimately
    have "G = G1" 
      by (meson \<open>Col G A I \<and> Col G B J\<close> col_permutation_1 l6_21)
  }
  ultimately
  show ?thesis 
    by blast
qed

lemma intersection_two_medians_unique_R1:
  assumes "\<not> Col A B C" and
    "I Midpoint B C" and
    "J Midpoint A C" and
    "Col G1 A I" and
    "Col G1 B J" and
    "Col G2 A I" and
    "Col G2 B J" 
  shows "G1 = G2"
  using intersection_two_medians_exist_unique assms(1) assms(2) assms(3) 
    assms(4) assms(5) assms(6) assms(7) by blast

lemma is_gravity_center_coplanar:
  assumes "G IsGravityCenter A B C"
  shows "Coplanar G A B C" 
proof -
  obtain I J where "I Midpoint B C" and "J Midpoint A C" and 
    "Col G A I" and "Col G B J" 
    using IsGravityCenter_def assms by blast
  thus ?thesis 
    using Coplanar_def midpoint_col not_col_permutation_2 by blast
qed

lemma is_gravity_center_exist_unique:
  assumes "\<not> Col A B C"
  shows "\<exists>! G. G IsGravityCenter A B C" 
proof -
  obtain I where "I Midpoint B C" 
    using MidR_uniq_aux by blast
  obtain J where "J Midpoint A C"    
    using MidR_uniq_aux by blast
  obtain G where "Col G A I" and "Col G B J" 
    using \<open>I Midpoint B C\<close> \<open>J Midpoint A C\<close> assms intersection_two_medians_exist by blast
  hence "G IsGravityCenter A B C" 
    using IsGravityCenter_def \<open>I Midpoint B C\<close> \<open>J Midpoint A C\<close> assms by blast
  moreover
  {
    fix G1 G2
    assume "G1 IsGravityCenter A B C" and
      "G2 IsGravityCenter A B C"
    obtain I1 J1 where "I1 Midpoint B C" "J1 Midpoint A C" "Col G1 A I1" "Col G1 B J1"
      using IsGravityCenter_def \<open>G1 IsGravityCenter A B C\<close> by blast
    moreover
    obtain I2 J2 where "I2 Midpoint B C" "J2 Midpoint A C" "Col G2 A I2" "Col G2 B J2"
      using IsGravityCenter_def \<open>G2 IsGravityCenter A B C\<close> by blast
    ultimately
    have "G1 = G2" 
      using assms intersection_two_medians_unique_R1 l7_17 by blast
  }
  ultimately
  show ?thesis
    by blast
qed

lemma three_medians_intersect:
  assumes " \<not> Col A B C" and
    "I Midpoint B C" and
    "J Midpoint A C" and
    "K Midpoint A B"
  shows "\<exists> G. Col G A I \<and> Col G B J \<and> Col G C K" 
proof -
  obtain G where "Col G A I" and "Col G B J" 
    using assms(1) assms(2) assms(3) intersection_two_medians_exist by blast
  moreover
  have "Col G C K" 
  proof -
    obtain D where "G Midpoint C D" 
      using symmetric_point_construction by blast
    have "A \<noteq> D" 
      by (metis \<open>G Midpoint C D\<close> assms(1) assms(2) assms(3) calculation(1) 
          col_permutation_5 col_trivial_3 colx l7_17_bis midpoint_col 
          midpoint_distinct_1 not_col_par_col_diff triangle_mid_par)
    hence "A D Par J G" 
      using \<open>G Midpoint C D\<close> assms(3) l7_2 triangle_mid_par by blast
    have "B \<noteq> G" 
      by (metis (no_types, lifting) assms(1) assms(2) calculation(1) 
          col_permutation_2 col_transitivity_2 is_midpoint_id_2 l7_2 midpoint_col)
    hence "G B Par A D" 
      by (metis \<open>A D Par J G\<close> calculation(2) not_col_distincts 
          par_col2_par_bis par_symmetry)
    hence "B \<noteq> D" 
      by (metis Col_def \<open>B \<noteq> G\<close> \<open>G Midpoint C D\<close> assms(1) col_par 
          col_trivial_3 midpoint_bet parallel_uniqueness)
    hence "B D Par I G" 
      by (meson \<open>G Midpoint C D\<close> assms(2) l7_2 triangle_mid_par)
    have "A \<noteq> G" 
      using \<open>A D Par J G\<close> assms(1) assms(3) calculation(2) col_permutation_2 
        col_transitivity_2 midpoint_col par_distinct by blast
    hence "G A Par D B" 
      by (metis Par_cases \<open>B D Par I G\<close> calculation(1) not_col_distincts 
          par_col2_par_bis)
    hence "D \<noteq> G" 
      by (metis \<open>G Midpoint C D\<close> assms(1) midpoint_distinct_1 par_id_2)
    {
      assume "Col G A D"
      hence "Col A B D" 
        by (metis \<open>G B Par A D\<close> col_permutation_4 col_trivial_3 
            par_reflexivity parallel_uniqueness)
      hence "G B Par A C" 
        by (metis Col_def \<open>A \<noteq> D\<close> \<open>Col G A D\<close> \<open>D \<noteq> G\<close> \<open>G Midpoint C D\<close> assms(1) 
            col_trivial_3 colx midpoint_bet)
      hence "Col A B C" 
        by (metis \<open>A \<noteq> D\<close> \<open>Col A B D\<close> \<open>G B Par A D\<close> col_trivial_3 colx parallel_uniqueness)
      hence False 
        using assms(1) by blast
    }
    hence "Parallelogram G A D B" 
      using \<open>G A Par D B\<close> \<open>G B Par A D\<close> par_2_plg by blast
    thus ?thesis 
      by (meson \<open>G Midpoint C D\<close> assms(4) col_permutation_1 midpoint_col 
          not_col_sym_not_col plg_mid_2 plg_permut)
  qed
  ultimately
  show ?thesis 
    by blast
qed

lemma is_gravity_center_col:
  assumes "G IsGravityCenter A B C" and
    "I Midpoint A B" 
  shows "Col G I C" 
proof -
  have "\<not> Col A B C" 
    using IsGravityCenter_def assms(1) by blast
  moreover
  obtain J K where "J Midpoint B C" and "K Midpoint A C" and 
    "Col G A J" and "Col G B K" 
    using IsGravityCenter_def assms(1) by blast
  moreover
  {
    fix G'
    assume "Col G' A J" and "Col G' B K" and "Col G' C I" 
    hence "G = G'" 
      using calculation(1) calculation(2) calculation(3) calculation(4) 
        calculation(5) intersection_two_medians_unique_R1 by blast
    hence "Col G I C" 
      using Col_cases \<open>Col G' C I\<close> by blast
  }
  ultimately show ?thesis
    using assms(2) three_medians_intersect 
    by blast
qed

lemma is_gravity_center_diff_1:
  assumes "G IsGravityCenter A B C"
  shows "G \<noteq> A" 
proof -
  obtain x x0 where "x Midpoint B C" and "x0 Midpoint A C" and
    "Col G A x" and "Col G B x0" 
    using IsGravityCenter_def assms by auto
  have "Col x0 A C" 
    using \<open>x0 Midpoint A C\<close> midpoint_col by blast
  have "Col x B C" 
    by (simp add: \<open>x Midpoint B C\<close> midpoint_col)
  {
    assume "G = A"
    hence "Col A B C" 
      by (metis \<open>Col G B x0\<close> \<open>Col x0 A C\<close> \<open>x0 Midpoint A C\<close> colx 
          midpoint_distinct_1 not_col_distincts)
    hence False 
      using IsGravityCenter_def assms by blast
  }
  thus ?thesis 
    by blast
qed

lemma is_gravity_center_diff_2:
  assumes "G IsGravityCenter A B C"
  shows "G \<noteq> B" 
proof -
  obtain x x0 where "x Midpoint B C" and "x0 Midpoint A C" and
    "Col G A x" and "Col G B x0" 
    using IsGravityCenter_def assms by auto
  have "Col x0 A C" 
    using \<open>x0 Midpoint A C\<close> midpoint_col by blast
  have "Col x B C" 
    by (simp add: \<open>x Midpoint B C\<close> midpoint_col)
  {
    assume "G = B"
    hence "Col A B C" 
      by (metis \<open>Col G A x\<close> \<open>Col x B C\<close> \<open>x Midpoint B C\<close> col2__eq 
          col_permutation_3 col_permutation_4 midpoint_distinct_1)
    hence False 
      using IsGravityCenter_def assms by blast
  }
  thus ?thesis 
    by blast
qed

lemma is_gravity_center_diff_3:
  assumes "G IsGravityCenter A B C"
  shows "G \<noteq> C" 
proof -
  have "\<not> Col A B C"     
    using IsGravityCenter_def assms by auto
  moreover
  obtain I J where "I Midpoint B C" and "J Midpoint A C" and 
    "Col G A I" and "Col G B J" 
    using IsGravityCenter_def assms by auto
  ultimately
  show ?thesis 
    by (metis col_permutation_1 l6_16_1 midpoint_col midpoint_distinct_1)
qed

(** We don't have ratio so we express that AG=2/3 AA' using midpoints. *)

lemma is_gravity_center_third_aux_lem: 
  assumes "G IsGravityCenter A B C" and
    "I Midpoint B C" and "J Midpoint A C" and
    "Col G A I" and "Col G B J" 
  shows "G \<noteq> I \<and> G \<noteq> J"
proof -
  have "I \<noteq> J" 
    using IsGravityCenter_def assms col_trivial_1 l7_9 by blast
  {
    assume "G = I"
    hence "Col I B J" 
      using \<open>Col G B J\<close> by auto
    hence "Col B J C" 
      by (metis \<open>I Midpoint B C\<close> col3 col_permutation_4 col_trivial_2 
          midpoint_col midpoint_distinct_1)
    have "Col A J C" 
      using \<open>J Midpoint A C\<close> col_permutation_4 midpoint_col by blast
    hence "Col A B C" 
      by (metis \<open>Col B J C\<close> \<open>J Midpoint A C\<close> col_transitivity_1 l6_16_1 
          midpoint_distinct_1 not_col_distincts)
    hence False 
      using IsGravityCenter_def assms by auto
  }
  moreover
  {
    assume "G = J"
    hence "Col I A J" 
      using assms(4) not_col_permutation_3 by blast
    hence "Col I A C" 
      by (metis assms(3) colx midpoint_col midpoint_distinct_1 not_col_distincts)
    hence "Col A B C" 
      by (metis NCol_cases assms(2) col_trivial_3 colx not_col_sym_not_col)
    hence False 
      using IsGravityCenter_def assms(1) by blast
  }
  ultimately show ?thesis by blast
qed

lemma is_gravity_center_third_aux_1: 
  assumes "G IsGravityCenter A B C" 
  shows "\<not> Col B G C" 
proof -
  obtain I J where "I Midpoint B C" and "J Midpoint A C" and
    "Col G A I" and "Col G B J" 
    using IsGravityCenter_def assms by auto
  hence "G \<noteq> I" 
    using assms is_gravity_center_third_aux_lem by blast
  {
    assume "Col C G B"
    hence False 
      by (metis IsGravityCenter_def \<open>Col G A I\<close> \<open>G \<noteq> I\<close> \<open>I Midpoint B C\<close> 
          assms l6_21 midpoint_col not_col_distincts not_col_permutation_2)
  }
  thus ?thesis 
    using not_col_permutation_3 by blast
qed

lemma is_gravity_center_third_aux_2: 
  assumes "G IsGravityCenter A B C" 
  shows "\<not> Col C G A" 
proof -
  obtain I J where "I Midpoint B C" and "J Midpoint A C" and
    "Col G A I" and "Col G B J" 
    using IsGravityCenter_def assms by auto
  hence "G \<noteq> J" 
    using assms is_gravity_center_third_aux_lem by presburger
  {
    assume "Col C G A"
    hence False 
      by (metis IsGravityCenter_def \<open>Col G B J\<close> \<open>G \<noteq> J\<close> \<open>J Midpoint A C\<close> 
          assms col_trivial_3 l6_21 midpoint_col not_col_permutation_3 
          not_col_permutation_4)
  }
  thus ?thesis 
    using not_col_permutation_3 by blast
qed

lemma is_gravity_center_third_aux_3: 
  assumes "G IsGravityCenter A B C" 
  shows "\<not> Col A G B" 
proof -
  obtain I J where "I Midpoint B C" and "J Midpoint A C" and
    "Col G A I" and "Col G B J" 
    using IsGravityCenter_def assms by auto
  {
    assume "Col A G B"
    hence False 
      by (metis is_gravity_center_third_aux_1 \<open>Col G B J\<close> 
          \<open>J Midpoint A C\<close> assms col_permutation_3 col_permutation_4 
          colx midpoint_col midpoint_distinct_1)
  }
  thus ?thesis 
    using not_col_permutation_3 by blast
qed

lemma is_gravity_center_third:
  assumes "G IsGravityCenter A B C" and
    "G' Midpoint A G" and
    "A' Midpoint B C" 
  shows "G Midpoint A' G'" 
proof -
  obtain C' where "C' Midpoint A B" 
    using MidR_uniq_aux by blast
  hence "Col G C' C" 
    using assms(1) is_gravity_center_col by blast
  have "\<not> Col A B C"     
    using IsGravityCenter_def assms by auto
  moreover
  obtain A'' B' where "A'' Midpoint B C" and "B' Midpoint A C" and 
    "Col G A A''" and "Col G B B'" 
    using IsGravityCenter_def assms by auto
  hence "A' = A''" 
    using assms(3) l7_17 by blast
  have "A \<noteq> B" 
    using calculation not_col_distincts by blast
  have "C \<noteq> B" 
    using calculation not_col_distincts by blast
  have "A' \<noteq> B" 
    using \<open>A' = A''\<close> \<open>A'' Midpoint B C\<close> \<open>C \<noteq> B\<close> is_midpoint_id by blast
  obtain G'' where "G'' Midpoint C G" 
    using MidR_uniq_aux by blast
  have "Parallelogram C' A' G'' G'" 
    using \<open>C' Midpoint A B\<close> \<open>G'' Midpoint C G\<close> assms(2) assms(3) 
      calculation not_col_distincts varignon_bis by blast
  then obtain I where "I Midpoint C' G''" and "I Midpoint A' G'" 
    using plg_mid by blast
  have "C' \<noteq> G'' \<or> A' \<noteq> G'" 
    using \<open>Parallelogram C' A' G'' G'\<close> plg_irreflexive by blast
  have "G \<noteq> A" 
    by (metis \<open>B' Midpoint A C\<close> \<open>Col G B B'\<close> \<open>G'' Midpoint C G\<close> 
        calculation col_permutation_2 col_transitivity_2 l7_17_bis 
        midpoint_col midpoint_distinct_2)
  have "\<not> Col A G C" 
    using assms(1) is_gravity_center_third_aux_2 not_col_permutation_3 by blast
  {
    assume "C' = G''"
    hence "A G Par C B" 
      using Par_perm \<open>C \<noteq> B\<close> \<open>C' Midpoint A B\<close> \<open>G'' Midpoint C G\<close> 
        mid_par_cong2 by blast
    hence "Col A C B" 
      by (metis \<open>A'' Midpoint B C\<close> \<open>Col G A A''\<close> \<open>\<not> Col A G C\<close> 
          midpoint_col not_col_distincts not_col_permutation_3 par_reflexivity 
          par_right_comm parallel_uniqueness)
    hence False 
      using calculation not_col_permutation_5 by blast
  }
  {
    assume "A' = G'"
    hence "A' = I" 
      using \<open>I Midpoint A' G'\<close> l7_3 by blast
    have "G' = I" 
      using \<open>A' = G'\<close> \<open>A' = I\<close> by auto
    have "A' = B'" 
    proof -
      have f1: "Bet A B' C"
        using \<open>B' Midpoint A C\<close> midpoint_bet by blast
      have f2: "Bet B A'' C"
        using \<open>A'' Midpoint B C\<close> midpoint_bet by blast
      have f3: "Bet A G' G"
        using assms(2) midpoint_bet by auto
      have f4: "\<not> Col B A C"
        using Col_perm calculation by blast
      have f5: "Col G B B' \<and> Col G B' B \<and> Col B G B' \<and> Col B B' G \<and> Col B' G B \<and> Col B' B G"
        using Col_perm \<open>Col G B B'\<close> by blast
      have f6: "Col A B B"
        using col_trivial_2 by blast
      have f7: "Bet A A'' G"
        using f3 \<open>A' = A''\<close> \<open>A' = G'\<close> by blast
      have "B \<noteq> C"
        using f6 calculation by blast
      then have f8: "A'' \<noteq> B"
        using \<open>A'' Midpoint B C\<close> midpoint_distinct_1 by blast
      have f9: "B' \<noteq> B"
        using f4 \<open>B' Midpoint A C\<close> midpoint_col by blast
      have f10: "B \<noteq> G"
        using f8 f6 f4 by (metis (no_types) Col_perm \<open>A' = A''\<close> \<open>A' = G'\<close> 
            \<open>A'' Midpoint B C\<close> assms(2) colx midpoint_col)
      then have f11: "Col B' B B'"
        using f5 col_trivial_2 colx by blast
      have f12: "Col A B B'" 
      proof -
        have f1: "\<forall>a aa ab. Col aa ab a \<longrightarrow> Col a aa ab"
          using not_col_permutation_1 by blast
        have f2: "Bet A G' G"
          by (simp add: assms(2) midpoint_bet)
        have f3: "Bet B A'' C"
          using \<open>A'' Midpoint B C\<close> midpoint_bet by auto
        have f4: "Col G' A G"
          using assms(2) midpoint_col by blast
        have f5: "Col A'' B C"
          using \<open>A'' Midpoint B C\<close> midpoint_col by auto
        have f6: "B \<noteq> A''"
          using \<open>A' = A''\<close> \<open>A' \<noteq> B\<close> by presburger
        have f7: "Bet A A'' G"
          using f2 \<open>A' = A''\<close> \<open>A' = G'\<close> by blast
        have "B \<noteq> G"
          using f6 f5 f4 f1 \<open>A' = A''\<close> \<open>A' = G'\<close> col_transitivity_2 f4
            not_col_permutation_3 f10 by force
        then show ?thesis 
        proof -
          have f1: "Bet A B' C"
            using \<open>B' Midpoint A C\<close> midpoint_bet by blast
          have f2: "Bet B A'' C"
            using \<open>A'' Midpoint B C\<close> midpoint_bet by blast
          have f3: "Bet A G' G"
            using assms(2) midpoint_bet by blast
          have f4: "B \<noteq> G \<and> Col B' B G \<and> Col B' B B \<and> Col G B A \<longrightarrow> Col B' B A"
            by (metis (no_types) colx)
          have f5: "B \<noteq> G'"
            using \<open>A' = G'\<close> \<open>A' \<noteq> B\<close> by presburger
          have "Bet B G' C"
            using f2 \<open>A' = A''\<close> \<open>A' = G'\<close> by blast
          then show ?thesis
            using f5 f4 f3 f1 by (metis NCol_perm \<open>Col G B B'\<close> assms(2) 
                col_trivial_2 f10 impossible_two_sides_not_col midpoint_distinct_1)
        qed
      qed
      then have f13: "\<not> Col B' B C"
        using f9 f6 calculation colx by blast
      then have "B' \<noteq> A"
        using f11 by (metis (no_types) \<open>B' Midpoint A C\<close> midpoint_distinct_1)
      then have False
        using f13 f12 f11 by (metis (no_types) Col_perm \<open>B' Midpoint A C\<close> 
            colx midpoint_col)
      then show ?thesis
        by meson
    qed
    have "Col A C B" 
    proof -
      have "A' Midpoint B C" 
        by (simp add: assms(3))
      moreover have "A' Midpoint A C" 
        using \<open>A' = B'\<close> \<open>B' Midpoint A C\<close> by blast
      ultimately show ?thesis 
        using \<open>A \<noteq> B\<close> l7_9 by blast
    qed
    hence False 
      using calculation not_col_permutation_5 by blast
  }
  hence "C' \<noteq> G'' \<and> A' \<noteq> G'" 
    using \<open>C' = G'' \<Longrightarrow> False\<close> by blast
  have "G = I" 
  proof -
    have "\<not> Col A G C" 
      by (simp add: \<open>\<not> Col A G C\<close>)
    moreover have "C \<noteq> G" 
      using calculation not_col_distincts by blast
    moreover have "Col A G G" 
      by (simp add: col_trivial_2)
    moreover
    have "Col A G I"
      by (metis Col_cases \<open>A' = A''\<close> \<open>A' = G' \<Longrightarrow> False\<close> \<open>Col G A A''\<close> \<open>G \<noteq> A\<close> \<open>I Midpoint A' G'\<close>
          assms(2) col2__eq midpoint_col) 
    moreover have "Col C G G" 
      by (simp add: col_trivial_2)
    moreover have "Col C G I"
      using Col_cases \<open>Col G C' C\<close> \<open>G'' Midpoint C G\<close> 
        \<open>I Midpoint C' G''\<close> l6_16_1 midpoint_col
      by (meson \<open>C' = G'' \<Longrightarrow> False\<close> colx)
    ultimately show ?thesis 
      using l6_21 by blast
  qed
  thus ?thesis 
    using \<open>I Midpoint A' G'\<close> by blast
qed

lemma is_gravity_center_third_reci:
  assumes "A' Midpoint B C" and
    "A'' Midpoint A G" and
    "G Midpoint A' A''" and
    "\<not> Col A B C"
  shows"G IsGravityCenter A B C" 
proof -
  obtain B' where "B' Midpoint A C"  
    using MidR_uniq_aux by blast
  obtain C' where "C' Midpoint A B"  
    using MidR_uniq_aux by blast   
  have "\<exists> I J. I Midpoint B C \<and> J Midpoint A C \<and> Col G A I \<and> Col G B J" 
  proof -
    have "Col G A A'" 
      by (meson assms(2) assms(3) midpoint_col not_col_permutation_1 
          not_col_permutation_5 not_col_sym_not_col)
    moreover
    have "Col G B B'" 
    proof -
      obtain B'' where "B'' Midpoint B G" 
        using midpoint_existence by blast
      obtain B''' where "G Midpoint B'' B'''" 
        using symmetric_point_construction by auto
      have "B A Par A' B'" 
        by (metis \<open>B' Midpoint A C\<close> assms(1) assms(4) not_col_distincts triangle_mid_par)
      have "Cong A C' A' B'" 
        by (metis triangle_mid_par_cong_1 \<open>B A Par A' B'\<close> \<open>B' Midpoint A C\<close> 
            \<open>C' Midpoint A B\<close> assms(1) l7_2 par_distinct)
      have "A B Par A'' B''" 
        using \<open>B'' Midpoint B G\<close> assms(2) assms(4) not_col_distincts 
          triangle_mid_par by blast
      have "Cong A C' A'' B''" 
        by (metis triangle_mid_par_cong_1 \<open>A B Par A'' B''\<close> \<open>B'' Midpoint B G\<close> 
            \<open>C' Midpoint A B\<close> assms(2) cong_right_commutativity l7_2 par_distinct)
      have "A'' B'' Par A' B'" 
        using Par_cases \<open>A B Par A'' B''\<close> \<open>B A Par A' B'\<close> par_trans by blast
      have "A'' B'' Par A' B'''" 
        by (metis \<open>A B Par A'' B''\<close> \<open>G Midpoint B'' B'''\<close> assms(3) l7_2 
            mid_par_cong1 par_neq2) 
      have "Cong A'' B'' A' B'''" 
        by (metis Mid_cases \<open>A'' B'' Par A' B'''\<close> \<open>G Midpoint B'' B'''\<close> 
            assms(3) mid_par_cong1 par_neq1)
      have "Cong A'' B'' A' B'" 
        using \<open>Cong A C' A' B'\<close> \<open>Cong A C' A'' B''\<close> cong_inner_transitivity by blast
      have "Col A' B' B'''" 
        by (metis Par_cases \<open>A B Par A'' B''\<close> \<open>A'' B'' Par A' B'''\<close> 
            \<open>B A Par A' B'\<close> par_id par_trans)
      show ?thesis
      proof (cases)
        assume "B' = B'''" 
        thus ?thesis 
          by (metis Col_cases \<open>B'' Midpoint B G\<close> \<open>G Midpoint B'' B'''\<close> bet_col l7_2 
              midpoint_bet not_col_sym_not_col)
      next
        assume "B' \<noteq> B'''"
        hence "A' Midpoint B' B'''" 
          using \<open>Col A' B' B'''\<close> \<open>Cong A'' B'' A' B'''\<close> \<open>Cong A'' B'' A' B'\<close> 
            col_permutation_4 cong_inner_transitivity l7_20 by blast
        have "C \<noteq> B'" 
          using \<open>B' Midpoint A C\<close> assms(4) col_trivial_3 is_midpoint_id_2 by auto
        have "A' \<noteq> B" 
          using assms(1) assms(4) is_midpoint_id not_col_distincts by blast
        hence "A' \<noteq> C" 
          using assms(1) is_midpoint_id_2 by force
        have "A'' \<noteq> B''" 
          using \<open>A B Par A'' B''\<close> par_distincts by blast
        have "A' \<noteq> B'''" 
          using \<open>A'' B'' Par A' B'''\<close> par_distinct by auto
        have "A' \<noteq> B'" 
          using \<open>A'' B'' Par A' B'\<close> par_distincts by blast
        have "Col G B'' B'''" 
          by (simp add: \<open>G Midpoint B'' B'''\<close> midpoint_col)
        have "Col B'' B G" 
          by (simp add: \<open>B'' Midpoint B G\<close> midpoint_col)
        have "Col C' A B" 
          by (simp add: \<open>C' Midpoint A B\<close> midpoint_col)
        have "Col B' A C" 
          by (simp add: \<open>B' Midpoint A C\<close> midpoint_col)
        have "Col G A' A''" 
          by (simp add: assms(3) midpoint_col)
        have "Col A'' A G" 
          by (simp add: assms(2) midpoint_col)
        have "Col A' B C" 
          by (simp add: assms(1) midpoint_col)
        have "A' \<noteq> G" 
          by (metis assms(1) assms(2) assms(3) assms(4) midpoint_col midpoint_distinct_1)
        have "A'' \<noteq> G" 
          using \<open>A' \<noteq> G\<close> assms(3) is_midpoint_id_2 by blast
        have "B'' \<noteq> G" 
          using \<open>A' Midpoint B' B'''\<close> \<open>B'' Midpoint B G\<close> \<open>C \<noteq> B'\<close> 
            \<open>G Midpoint B'' B'''\<close> assms(1) l7_9_bis by blast
        have "A' \<noteq> B''" 
          by (metis \<open>B' Midpoint A C\<close> \<open>B' \<noteq> B'''\<close> \<open>B'' Midpoint B G\<close> 
              \<open>G Midpoint B'' B'''\<close> assms(1) assms(2) assms(3) l7_17 
              symmetric_point_uniqueness)    
        have "Col A' B'' A'" 
          using col_trivial_3 by blast
        have "Col G A A'" 
          by (simp add: calculation)
        have "B'' \<noteq> B'''" 
          using \<open>B'' \<noteq> G\<close> \<open>G Midpoint B'' B'''\<close> l7_3 by blast
        have "G \<noteq> B'''" 
          using \<open>B'' \<noteq> B'''\<close> \<open>G Midpoint B'' B'''\<close> midpoint_not_midpoint by blast
        have "A' \<noteq> A''" 
          using \<open>A' \<noteq> G\<close> assms(3) l7_3 by blast
        have "B \<noteq> G" 
          using \<open>B'' Midpoint B G\<close> \<open>B'' \<noteq> G\<close> l8_20_2 by blast
        have "B'' \<noteq> B" 
          using \<open>B \<noteq> G\<close> \<open>B'' Midpoint B G\<close> is_midpoint_id by blast
        have "A \<noteq> G" 
          using \<open>A'' \<noteq> G\<close> assms(2) l7_3 by blast
        have "A'' \<noteq> A" 
          using \<open>A \<noteq> G\<close> assms(2) is_midpoint_id by blast
        have "\<not> Col A B G" 
          by (metis \<open>A \<noteq> G\<close> \<open>A' \<noteq> B\<close> \<open>B \<noteq> G\<close> \<open>Col A' B C\<close> assms(4) calculation 
              colx l6_16_1 not_strict_par2 par_reflexivity)
        have "A'' \<noteq> B''" 
          using \<open>A'' \<noteq> B''\<close> by blast
        have "A' \<noteq> B'''" 
          using \<open>A' \<noteq> B'''\<close> by auto
        have "A' \<noteq> B'"  
          by (simp add: \<open>A' \<noteq> B'\<close>)
        have "B' \<noteq> B'''" 
          by (simp add: \<open>B' \<noteq> B'''\<close>)
        have "Col G B'' B'''" 
          using \<open>Col G B'' B'''\<close> by auto
        have "Col B'' B G" 
          using \<open>Col B'' B G\<close> by auto
        have "Col C' A B" 
          by (simp add: \<open>Col C' A B\<close>)
        have "Col B' A C" 
          using \<open>Col B' A C\<close> by auto
        have "Col G A' A''" 
          using \<open>Col G A' A''\<close> by auto
        have "Col A'' A G" 
          using \<open>Col A'' A G\<close> by auto
        have "Col A' B C" 
          using \<open>Col A' B C\<close> by auto    
        have "G \<noteq> A'" 
          using \<open>A' \<noteq> G\<close> by auto
        have "G \<noteq> A''" 
          using \<open>A'' \<noteq> G\<close> by blast
        have "G \<noteq> B''" 
          using \<open>B'' \<noteq> G\<close> by blast
        have "A' \<noteq> B''" 
          using \<open>A' \<noteq> B''\<close> by blast
        have "Col A' B'' A'" 
          by (simp add: \<open>Col A' B'' A'\<close>)
        have "Col A A'' A'" 
          by (metis Col_cases \<open>A \<noteq> G\<close> \<open>Col A'' A G\<close> calculation col_trivial_3 colx)   
        have "A' B'' OS A'' B'''" 
        proof -
          have "A' B'' OS G A''" 
          proof -
            have "A' Out G A''" 
              using \<open>A' \<noteq> A''\<close> assms(3) midpoint_out by auto
            moreover have "\<not> Col A' B'' G" 
              by (meson \<open>A B Par A'' B''\<close> \<open>Col G A A'\<close> \<open>Col G A' A''\<close> \<open>G \<noteq> A'\<close> 
                  \<open>\<not> Col A B G\<close> not_col_par_col_diff not_col_permutation_1 
                  not_col_permutation_5 par_col2_par_bis)
            ultimately show ?thesis 
              using out_one_side by blast 
          qed
          hence "A' B'' OS A'' G" 
            using one_side_symmetry by blast
          moreover have "A' B'' OS G B'''" 
          proof -
            have "B'' Out G B'''" 
              by (simp add: \<open>B'' \<noteq> B'''\<close> \<open>G Midpoint B'' B'''\<close> midpoint_out)
            moreover have "\<not> Col A' B'' G" 
              using \<open>A' B'' OS G A''\<close> col123__nos by auto
            ultimately show ?thesis 
              using l9_19_R2 not_col_distincts by blast
          qed
          ultimately show ?thesis 
            using one_side_transitivity by blast
        qed
        moreover
        have "A' B'' TS A'' B'''" 
        proof -
          have "A' B'' TS B' B'''" 
          proof -
            have "\<not> Col B''' A' B''" 
              using calculation col124__nos not_col_permutation_2 by blast
            moreover have "\<exists> T. Col T A' B'' \<and> Bet B' T B'''" 
              using Midpoint_def \<open>A' Midpoint B' B'''\<close> not_col_distincts by blast
            ultimately show ?thesis 
              by (metis Bet_cases Col_cases Midpoint_def \<open>A' Midpoint B' B'''\<close> 
                  \<open>A' \<noteq> B'\<close> bet__ts l9_2)
          qed
          moreover
          have "A' B'' OS B' A''" 
          proof -
            have "A' B'' OS A C" 
            proof -
              have "A' Out G A \<and> \<not> Col A' B'' G" 
              proof -
                have "\<not> Col A' B'' G" 
                  by (metis \<open>A' B'' OS A'' B'''\<close> \<open>A' \<noteq> G\<close> \<open>Col A' B'' A'\<close> 
                      \<open>Col G A' A''\<close> colx one_side_not_col123)
                moreover have "A' Out G A" 
                  by (metis (full_types) Bet_cases \<open>A' \<noteq> G\<close> \<open>A'' \<noteq> G\<close> 
                      assms(2) assms(3) bet_out midpoint_bet 
                      outer_transitivity_between2)
                ultimately show ?thesis 
                  by blast    
              qed
              hence "A' B'' OS G A" 
                using out_one_side by blast
              hence "A' B'' OS A G" 
                using one_side_symmetry by blast
              moreover have "A' B'' OS G C" 
              proof -
                have "A' B'' TS G B" 
                  by (metis Col_cases Midpoint_def \<open>A' Out G A \<and> \<not> Col A' B'' G\<close> 
                      \<open>B'' Midpoint B G\<close> \<open>B'' \<noteq> B\<close> bet__ts between_symmetry 
                      invert_two_sides)
                moreover have "A' B'' TS C B" 
                  by (meson TS_def \<open>A' \<noteq> C\<close> assms(1) bet__ts calculation 
                      l9_2 midpoint_bet not_col_permutation_2)
                ultimately show ?thesis 
                  using OS_def by blast
              qed
              ultimately show ?thesis 
                using one_side_transitivity by blast
            qed
            hence "A' B'' OS B' A" 
              using \<open>B' Midpoint A C\<close> l9_17 midpoint_bet one_side_symmetry by blast
            moreover have "A' B'' OS A A''" 
            proof -
              have "A' Out A A''" 
                by (metis NCol_perm \<open>A \<noteq> G\<close> \<open>Col A A'' A'\<close> \<open>Col G A' A''\<close> assms(2) 
                    assms(3) l6_4_1 l6_4_2 midpoint_bet midpoint_out_1 out_bet_out_2)
              moreover have "\<not> Col A' B'' A" 
                using \<open>A' B'' OS A C\<close> one_side_not_col123 by auto
              ultimately show ?thesis 
                using out_one_side by auto
            qed
            ultimately show ?thesis 
              using one_side_transitivity by blast
          qed
          ultimately show ?thesis 
            using l9_8_2 by blast
        qed
        ultimately show ?thesis 
          using l9_9_bis by blast
      qed
    qed
    ultimately show ?thesis 
      using \<open>B' Midpoint A C\<close> assms(1) by blast
  qed
  thus ?thesis 
    using IsGravityCenter_def assms(4) by blast
qed

lemma is_gravity_center_perm:
  assumes "G IsGravityCenter A B C"
  shows "G IsGravityCenter A B C \<and> G IsGravityCenter A C B \<and>
         G IsGravityCenter B A C \<and> G IsGravityCenter B C A \<and>
         G IsGravityCenter C A B \<and> G IsGravityCenter C B A" 
proof -
  obtain I where "I Midpoint A B" 
    using MidR_uniq_aux by blast
  hence "Col G I C" 
    using assms is_gravity_center_col by blast
  have "\<not> Col A B C" 
    using IsGravityCenter_def assms by blast
  obtain J K where "J Midpoint B C" "K Midpoint A C" "Col G A J" "Col G B K" 
    using IsGravityCenter_def assms by blast
  have "G IsGravityCenter A B C" 
    by (simp add: assms)
  moreover
  have "G IsGravityCenter A C B" 
    using IsGravityCenter_def \<open>Col G A J\<close> \<open>Col G I C\<close> 
      \<open>I Midpoint A B\<close> \<open>J Midpoint B C\<close> \<open>\<not> Col A B C\<close> 
      col_permutation_5 l7_2 by blast
  moreover
  have "G IsGravityCenter B A C" 
    by (metis IsGravityCenter_def 
        \<open>\<And>thesis. (\<And>J K. \<lbrakk>J Midpoint B C; K Midpoint A C; Col G A J; Col G B K\<rbrakk> \<Longrightarrow> thesis) 
                          \<Longrightarrow> thesis\<close> 
        \<open>\<not> Col A B C\<close> col_permutation_4)
  moreover
  have "G IsGravityCenter B C A" 
    by (meson IsGravityCenter_def \<open>Col G B K\<close> \<open>Col G I C\<close> 
        \<open>I Midpoint A B\<close> \<open>K Midpoint A C\<close> \<open>\<not> Col A B C\<close> 
        col_permutation_2 col_permutation_5 l7_2)
  moreover
  have "G IsGravityCenter C A B" 
    using IsGravityCenter_def \<open>\<not> Col A B C\<close> calculation(2) col_permutation_1 by blast
  moreover
  have "G IsGravityCenter C B A" 
    using IsGravityCenter_def \<open>\<not> Col A B C\<close> calculation(4) col_permutation_3 by blast
  ultimately
  show ?thesis 
    by blast
qed

lemma is_gravity_center_perm_1:
  assumes "G IsGravityCenter A B C"
  shows "G IsGravityCenter A C B"  
  using assms is_gravity_center_perm by blast

lemma is_gravity_center_perm_2:
  assumes "G IsGravityCenter A B C"
  shows "G IsGravityCenter B A C" 
  using assms is_gravity_center_perm by blast

lemma is_gravity_center_perm_3:
  assumes "G IsGravityCenter A B C"
  shows "G IsGravityCenter B C A" 
  using assms is_gravity_center_perm by blast

lemma is_gravity_center_perm_4:
  assumes "G IsGravityCenter A B C"
  shows "G IsGravityCenter C A B" 
  using assms is_gravity_center_perm by blast

lemma is_gravity_center_perm_5:
  assumes "G IsGravityCenter A B C"
  shows "G IsGravityCenter C B A" 
  using assms is_gravity_center_perm by blast

lemma is_gravity_center_cases:
  assumes  "G IsGravityCenter A B C \<or> G IsGravityCenter A C B \<or>
            G IsGravityCenter B A C \<or> G IsGravityCenter B C A \<or>
            G IsGravityCenter C A B \<or> G IsGravityCenter C B A" 
  shows "G IsGravityCenter A B C" 
  using assms is_gravity_center_perm by blast

lemma concyclic_aux:
  assumes "Concyclic2 A B C D"
  shows "\<exists> P. Cong P A P B \<and> Cong P A P C \<and> Cong P A P D \<and> Coplanar A B C P" 
proof -
  obtain O1 where "Cong O1 A O1 B" "Cong O1 A O1 C" "Cong O1 A O1 D" 
    using assms Concyclic2_def by blast
  have "\<exists> P. Cong P A P B \<and> Cong P A P C \<and> Cong P A P D \<and> Coplanar A B C P" 
  proof (cases "Col A B C")
    case True
    thus ?thesis 
      using \<open>Cong O1 A O1 B\<close> \<open>Cong O1 A O1 C\<close> \<open>Cong O1 A O1 D\<close> col__coplanar by blast
  next
    case False
    obtain P where "Coplanar A B C P" and "\<forall> E. Coplanar A B C E \<longrightarrow> Per E P O1" 
      using l11_62_existence by blast
    have "Cong P A P B" 
    proof -
      have "Per A P O1" 
        using \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E P O1\<close> ncop_distincts by blast
      moreover
      have "Per B P O1" 
        using \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E P O1\<close> ncop_distincts by blast
      moreover
      have "Cong A O1 B O1" 
        using \<open>Cong O1 A O1 B\<close> not_cong_2143 by blast
      moreover
      have "Cong P O1 P O1" 
        by (simp add: cong_reflexivity)
      ultimately
      show ?thesis
        using cong2_per2__cong 
        by blast
    qed
    moreover
    have "Cong P A P C" 
      by (metis cong_reflexivity \<open>Cong O1 A O1 C\<close> 
          \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E P O1\<close> cong2_per2__cong 
          cong_commutativity ncop_distincts)
    moreover
    have"Cong P A P D" 
      by (metis Concyclic2_def \<open>Cong O1 A O1 D\<close> 
          \<open>\<forall>E. Coplanar A B C E \<longrightarrow> Per E P O1\<close> assms cong2_per2__cong 
          cong_commutativity cong_reflexivity ncop_distincts)
    ultimately
    show ?thesis 
      using \<open>Coplanar A B C P\<close> by blast
  qed
  thus ?thesis 
    by blast
qed

lemma concyclic_trans:
  assumes "\<not> Col A B C" and
    "Concyclic2 A B C D" and
    "Concyclic2 A B C E" 
  shows "Concyclic2 A B D E" 
proof -
  obtain x where "Cong x A x B" "Cong x A x C" "Cong x A x D" "Coplanar A B C x" 
    using assms(2) concyclic_aux by blast
  obtain x0 where "Cong x0 A x0 B" "Cong x0 A x0 C"  "Cong x0 A x0 E"  "Coplanar A B C x0" 
    using assms(3) concyclic_aux by blast
  have "Cong x A x B" 
    using \<open>Cong x A x B\<close> by auto
  moreover
  have "Cong x A x D" 
    using \<open>Cong x A x D\<close> by auto
  moreover
  have "Cong x A x E" 
    by (metis Col_def \<open>Cong x A x C\<close> \<open>Cong x0 A x0 B\<close> 
        \<open>Cong x0 A x0 C\<close> \<open>Cong x0 A x0 E\<close> \<open>Coplanar A B C x0\<close> 
        \<open>Coplanar A B C x\<close> assms(1) between_trivial 
        calculation(1) cong4_cop2__eq cong_commutativity)
  ultimately
  show ?thesis 
    by (meson Concyclic2_def assms(1) assms(2) assms(3) 
        coplanar_pseudo_trans ncop_distincts)
qed

lemma concyclic_perm_1:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 A B D C" 
  using Concyclic2_def assms coplanar_perm_1 by fastforce

lemma concyclic_perm_2:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 A C B D" 
  by (meson Concyclic2_def assms coplanar_perm_2)

lemma concyclic_perm_3:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 A C D B" 
  by (meson assms concyclic_perm_1 concyclic_perm_2)

lemma concyclic_perm_4:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 A D B C" 
  using assms concyclic_perm_1 concyclic_perm_2 by blast

lemma concyclic_perm_5:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 A D C B" 
  by (meson assms concyclic_perm_1 concyclic_perm_4)

lemma concyclic_perm_6:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 B A C D" 
  by (meson Concyclic2_def assms concyclic_perm_4 cong_inner_transitivity 
      coplanar_perm_9 not_cong_3412)

lemma concyclic_perm_7:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 B A D C" 
  using assms concyclic_perm_1 concyclic_perm_6 by blast

lemma concyclic_perm_8:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 B C A D" 
  using assms concyclic_perm_4 concyclic_perm_7 by blast

lemma concyclic_perm_9:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 B C D A" 
  using assms concyclic_perm_3 concyclic_perm_6 by blast

lemma concyclic_perm_10:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 B D A C" 
  by (meson assms concyclic_perm_3 concyclic_perm_9)

lemma concyclic_perm_11:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 B D C A" 
  using assms concyclic_perm_1 concyclic_perm_10 by blast

lemma concyclic_perm_12:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 C A B D" 
  using assms concyclic_perm_2 concyclic_perm_6 by blast

lemma concyclic_perm_13:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 C A D B" 
  using assms concyclic_perm_3 concyclic_perm_6 by blast

lemma concyclic_perm_14:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 C B A D" 
  using assms concyclic_perm_12 concyclic_perm_2 by blast

lemma concyclic_perm_15:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 C B D A" 
  by (meson assms concyclic_perm_12 concyclic_perm_3)

lemma concyclic_perm_16:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 C D A B" 
  using assms concyclic_perm_15 concyclic_perm_3 by blast

lemma concyclic_perm_17:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 C D B A" 
  using assms concyclic_perm_1 concyclic_perm_16 by blast

lemma concyclic_perm_18:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 D A B C" 
  using assms concyclic_perm_11 concyclic_perm_17 by blast

lemma concyclic_perm_19:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 D A C B" 
  using assms concyclic_perm_10 concyclic_perm_17 by blast

lemma concyclic_perm_20:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 D B A C" 
  using assms concyclic_perm_1 concyclic_perm_14 by blast

lemma concyclic_perm_21:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 D B C A" 
  using assms concyclic_perm_19 concyclic_perm_5 by blast

lemma concyclic_perm_22:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 D C A B" 
  using assms concyclic_perm_21 concyclic_perm_3 by blast

lemma concyclic_perm_23:
  assumes "Concyclic2 A B C D" 
  shows "Concyclic2 D C B A" 
  using assms concyclic_perm_2 concyclic_perm_21 by blast

lemma concyclic_1123:
  assumes "\<not> Col A B C"
  shows "Concyclic2 A A B C" 
proof -
  have "Coplanar A A B C" 
    using coplanar_trivial by blast
  obtain G where "G IsCircumcenter A B C" 
    using assms exists_circumcenter by blast
  have "Cong G A G A" 
    using cong_reflexivity by auto
  moreover
  have "Cong G A G B" 
    using \<open>G IsCircumcenter A B C\<close> circumcenter_cong_1 cong_commutativity by blast
  moreover
  have "Cong G A G C" 
    using \<open>G IsCircumcenter A B C\<close> circumcenter_cong_3 cong_4321 by blast
  ultimately
  show ?thesis 
    using Concyclic2_def ncop_distincts by fastforce
qed

lemma concyclic_not_col_or_eq_aux:
  assumes "Concyclic2 A B C D" 
  shows "A = B \<or> A = C \<or> B = C \<or> \<not> Col A B C" 
proof (cases "A = B")
  case True
  thus ?thesis 
    by simp
next
  case False
  hence "A \<noteq> B" 
    by auto
  show ?thesis
  proof (cases "A = C")
    case True
    thus ?thesis 
      by simp
  next
    case False
    hence "A \<noteq> C"
      by simp
    show ?thesis 
    proof (cases "B = C")
      case True
      thus ?thesis 
        by simp
    next
      case False
      hence "B \<noteq> C"
        by simp
      show ?thesis
      proof (cases "Col A B C")
        case True
        hence "Col A B C" 
          by simp
        obtain P where "Cong P A P B" "Cong P A P C" "Cong P A P D" 
          using assms concyclic_aux by blast
        obtain M1 where "M1 Midpoint A B" 
          using MidR_uniq_aux by blast
        {
          assume "P = M1"
          hence "Bet A P B" 
            by (simp add: \<open>M1 Midpoint A B\<close> midpoint_bet)
          hence "Col A P B" 
            using Col_def by blast
          {
            assume "Col A P C" and "Cong P A P C" 
            hence "A = C \<or> P Midpoint A C" 
              using l7_20_bis by blast
          }
          have "A \<noteq> C" 
            using \<open>A \<noteq> C\<close> by blast
          moreover
          have "\<not> P Midpoint A C" 
            using False \<open>M1 Midpoint A B\<close> \<open>P = M1\<close> symmetric_point_uniqueness by blast
          moreover
          have "Col A P C" 
            using True \<open>A \<noteq> B\<close> \<open>Col A P B\<close> col_trivial_3 colx by blast
          ultimately
          have False
            using \<open>Cong P A P C\<close> \<open>\<lbrakk>Col A P C; Cong P A P C\<rbrakk> \<Longrightarrow> A = C \<or> P Midpoint A C\<close> by blast
        }
        obtain M2 where "M2 Midpoint A C" 
          using MidR_uniq_aux by blast
        {
          assume "P = M2" 
          {
            assume "Col A P B" and "Cong P A P B" 
            hence "A = B \<or> P Midpoint A B" 
              using l7_20_bis by blast
          }
          have "A \<noteq> C" 
            using \<open>A \<noteq> C\<close> by blast
          moreover
          have "\<not> P Midpoint A B" 
            using False \<open>M2 Midpoint A C\<close> \<open>P = M2\<close> symmetric_point_uniqueness by blast
          moreover
          have "Col A P B" 
            by (meson False True \<open>A \<noteq> B\<close> \<open>Cong P A P B\<close> \<open>Cong P A P C\<close> 
                calculation(1) cong2__ncol not_cong_2143)
          ultimately
          have False 
            using \<open>A \<noteq> B\<close> \<open>Cong P A P B\<close> 
              \<open>\<lbrakk>Col A P B; Cong P A P B\<rbrakk> \<Longrightarrow> A = B \<or> P Midpoint A B\<close> 
            by fastforce
        }
        have "M1 \<noteq> M2" 
          using False \<open>M1 Midpoint A B\<close> \<open>M2 Midpoint A C\<close> 
            symmetric_point_uniqueness by blast
        have "P M1 PerpBisect A B" 
          by (meson \<open>A \<noteq> B\<close> \<open>Cong P A P B\<close> \<open>M1 Midpoint A B\<close> \<open>P = M1 \<Longrightarrow> False\<close> 
              cong_mid_perp_bisect not_cong_2143)
        have "P M2 PerpBisect A C" 
          by (meson \<open>A \<noteq> C\<close> \<open>Cong P A P C\<close> \<open>M2 Midpoint A C\<close> \<open>P = M2 \<Longrightarrow> False\<close> 
              cong_mid_perp_bisect not_cong_2143)
        {
          assume "Col P M1 M2" 
          {
            assume "Col A P B" and "Cong P A P B" 
            hence "A = B \<or> P Midpoint A B" 
              using l7_20_bis by blast
          }
          moreover
          have "A \<noteq> B" 
            by (simp add: \<open>A \<noteq> B\<close>)
          moreover
          have "\<not> P Midpoint A B" 
            using \<open>M1 Midpoint A B\<close> \<open>P = M1 \<Longrightarrow> False\<close> l7_17 by blast
          moreover
          have "Col A P B" 
            by (meson False True \<open>A \<noteq> C\<close> \<open>Cong P A P B\<close> \<open>Cong P A P C\<close> 
                calculation(2) cong2__ncol cong_commutativity)
          moreover
          have "Cong P A P B" 
            using \<open>Cong P A P B\<close> by auto
          ultimately
          have False
            by blast
        }
        thus ?thesis 
          by (meson Cong_cases \<open>Cong P A P B\<close> \<open>Cong P A P C\<close> cong2__ncol)
      next
        case False
        hence "\<not> Col A B C" 
          by simp
        thus ?thesis 
          by simp
      qed
    qed
  qed
qed

lemma concyclic_not_col_or_eq:
  assumes "Concyclic2 A B C A'" 
  shows "A' = C \<or> A' = B \<or> A = B \<or> A = C \<or> A = A' \<or> (\<not> Col A B A' \<and> \<not> Col A C A')" 
  by (metis Concyclic2_def assms cong2__ncol cong_commutativity)

lemma Euler_line_special_case:
  assumes "Per A B C" and
    "G IsGravityCenter A B C" and
    "H IsOrthocenter A B C" and
    "P IsCircumcenter A B C" 
  shows "Col G H P" 
proof -
  have "H = B" 
    using assms(1) assms(3) orthocenter_per by auto
  have "P Midpoint A C" 
    using IsGravityCenter_def assms(1) assms(2) assms(4) circumcenter_per 
      not_col_distincts by blast
  have "G IsGravityCenter A C B" 
    by (simp add: assms(2) is_gravity_center_perm_1)
  thus ?thesis 
    by (metis is_gravity_center_col \<open>H = B\<close> \<open>P Midpoint A C\<close> not_col_permutation_5)
qed

lemma gravity_center_change_triangle:
  assumes "G IsGravityCenter A B C" and
    "I Midpoint B C" and 
    "I Midpoint B' C'" and 
    "\<not> Col A B' C'"
  shows "G IsGravityCenter A B' C'" 
proof -
  obtain G' where "G' Midpoint A G" 
    using MidR_uniq_aux by blast
  hence "G Midpoint I G'" 
    by (meson assms(1) assms(2) is_gravity_center_third)
  thus ?thesis 
    using \<open>G' Midpoint A G\<close> assms(3) assms(4) is_gravity_center_third_reci by force
qed

lemma Euler_line:
  assumes "\<not> Col A B C" and
    "G IsGravityCenter A B C" and
    "H IsOrthocenter A B C" and
    "P IsCircumcenter A B C"  
  shows "Col G H P" 
proof (cases "Cong A B A C")
  case True
  hence "Cong A B A C" 
    by simp
  obtain A' where "A' Midpoint B C" 
    using MidR_uniq_aux by blast
  obtain B' where "B' Midpoint A C" 
    using MidR_uniq_aux by blast
  obtain C' where "C' Midpoint A B" 
    using MidR_uniq_aux by blast
  have "A A' PerpBisect B C" 
    by (metis True \<open>A' Midpoint B C\<close> assms(1) cong_mid_perp_bisect 
        midpoint_col not_col_distincts not_cong_2143)
  have "Col G A' A" 
    by (meson \<open>A' Midpoint B C\<close> assms(2) is_gravity_center_col 
        is_gravity_center_perm_3)
  show ?thesis 
  proof (cases "P = G")
    case True
    thus ?thesis 
      by (simp add: col_trivial_3)
  next
    case False
    hence "P \<noteq> G" 
      by simp
    show ?thesis 
    proof (cases "P = H")
      case True
      thus ?thesis 
        by (simp add: col_trivial_2)
    next
      case False
      hence "P \<noteq> H" 
        by simp
      show ?thesis 
      proof (cases "P = A'")
        case True
        have "Col A H P" 
        proof -
          have "Coplanar B C H P" 
            using NCol_perm True \<open>A' Midpoint B C\<close> bet_col 
              midpoint_bet ncop__ncols by blast
          moreover
          have "A H Perp B C" 
            using IsOrthocenter_def assms(3) by blast
          moreover
          have "A P Perp B C" 
            by (metis True \<open>A' Midpoint B C\<close> \<open>Cong A B A C\<close> assms(1) 
                cong_commutativity cong_mid_perp_bisect midpoint_col not_col_distincts 
                perp_bisect_perp)
          ultimately
          show ?thesis 
            using cop_perp2__col by blast
        qed
        have "Coplanar G A B C" 
          using Coplanar_def NCol_perm \<open>A' Midpoint B C\<close> \<open>Col G A' A\<close> 
            midpoint_col by blast
        have "Coplanar B C G H"  
          by (meson IsOrthocenter_def \<open>Coplanar G A B C\<close> assms(3) 
              coplanar_perm_21 coplanar_perm_3 coplanar_trans_1 perp__coplanar)
        moreover
        have "P G Perp B C" 
          using NCol_perm True \<open>A A' PerpBisect B C\<close> \<open>Col G A' A\<close> \<open>P \<noteq> G\<close> 
            col_trivial_2 perp_bisect_perp perp_col2 by blast
        moreover
        have "P H Perp B C" 
          by (meson False IsOrthocenter_def \<open>Col A H P\<close> assms(3) 
              col_trivial_2 perp_col2)
        ultimately
        show ?thesis 
          using col_permutation_1 cop_perp2__col by blast
      next
        case False
        hence "P \<noteq> A'" 
          by simp
        have "Col A A' H" 
        proof -
          have "Coplanar B C A' H" 
            by (meson \<open>A' Midpoint B C\<close> bet__coplanar coplanar_perm_2 midpoint_bet)
          moreover
          have "A A' Perp B C" 
            using \<open>A A' PerpBisect B C\<close> perp_bisect_perp by blast
          moreover
          have "A H Perp B C" 
            using IsOrthocenter_def assms(3) by blast
          ultimately
          show ?thesis 
            using cop_perp2__col by blast
        qed
        have "P A' PerpBisect B C" 
          by (metis False \<open>A' Midpoint B C\<close> assms(1) assms(4) 
              circumcenter_perp not_col_distincts)
        have "Col A' A P" 
        proof -
          have "Coplanar B C A P" 
            using IsCircumcenter_def assms(4) coplanar_perm_17 by blast
          moreover
          have "A' A Perp B C" 
            by (meson \<open>A A' PerpBisect B C\<close> perp_bisect_perp perp_left_comm)
          moreover
          have "A' P Perp B C" 
            by (simp add: \<open>P A' PerpBisect B C\<close> perp_bisect_perp perp_left_comm)
          ultimately
          show ?thesis 
            using cop_perp2__col by force
        qed
        have "A \<noteq> A'" 
          using \<open>A' Midpoint B C\<close> assms(1) midpoint_col by blast
        thus ?thesis 
          by (meson Col_cases \<open>Col A A' H\<close> \<open>Col A' A P\<close> \<open>Col G A' A\<close> col3)
      qed
    qed
  qed  
next
  case False
  hence "\<not> Cong A B A C" 
    by simp
  obtain A' where "P Midpoint A A'" 
    using symmetric_point_construction by blast
  have "A \<noteq> B" 
    using assms(1) not_col_distincts by blast
  have "A \<noteq> C" 
    using assms(1) not_col_distincts by blast
  have "C \<noteq> B" 
    using False cong_reflexivity by blast
  have "Concyclic2 A B C A'" 
  proof -
    have "Coplanar A B C A'" 
    proof (cases "P = A")
      case True
      thus ?thesis 
        using \<open>P Midpoint A A'\<close> midpoint_distinct_1 ncop_distincts by blast
    next
      case False
      hence "P \<noteq> A"
        by simp
      have "Coplanar A B C A'"
      proof -
        have "Coplanar B C A P" 
          using IsCircumcenter_def assms(4) ncoplanar_perm_22 by blast
        moreover
        have "Col A P A'" 
          using \<open>P Midpoint A A'\<close> col_permutation_4 midpoint_col by blast
        ultimately
        show ?thesis 
          using False col_cop__cop coplanar_perm_12 by blast
      qed
      thus ?thesis 
        by (simp add: \<open>Coplanar A B C A'\<close>)
    qed
    moreover
    have "Cong P A P B" 
      using IsCircumcenter_def assms(4) not_cong_2143 by blast
    moreover
    have "Cong P A P C" 
      using assms(4) circumcenter_cong_3 cong_4321 by blast
    moreover
    have "Cong P A P A'" 
      by (meson \<open>P Midpoint A A'\<close> midpoint_cong not_cong_2134)
    ultimately
    show ?thesis 
      using Concyclic2_def by blast
  qed
  have "A' = C \<or> A' = B \<or> A = B \<or> A = C \<or> A = A' \<or> \<not> Col A B A' \<and> \<not> Col A C A'" 
    by (metis Col_cases circumcenter_cong_3 \<open>P Midpoint A A'\<close> assms(4) 
        circumcenter_cong_1 col3 col_trivial_3 cong_4321 l7_2 l7_20_bis 
        l7_9_bis midpoint_col)
  moreover
  {
    assume "A' = C"
    have "Cong P A P B" 
      using assms(4) circumcenter_cong_1 cong_commutativity by blast
    hence "Per A B C" 
      using \<open>A' = C\<close> \<open>P Midpoint A A'\<close> assms(1) midpoint_thales 
        not_col_permutation_5 by blast
    hence "Col G H P" 
      using Euler_line_special_case assms(2) assms(3) assms(4) by blast
  }
  moreover
  {
    assume "A' = B"
    have "Cong P A P C" 
      using assms(4) circumcenter_cong_3 not_cong_4321 by blast
    hence "Per A C B" 
      using \<open>A' = B\<close> \<open>P Midpoint A A'\<close> assms(1) midpoint_thales by blast
    hence "Col G H P" 
      by (meson Euler_line_special_case IsOrthocenter_cases 
          Per_cases assms(2) assms(3) assms(4) is_circumcenter_perm_3 
          is_gravity_center_perm_3)
  }
  moreover
  {
    assume "A = B"
    hence False 
      using \<open>A \<noteq> B\<close> by auto
  }
  moreover
  {
    assume "A = C"
    hence False 
      using \<open>A \<noteq> C\<close> by auto
  }
  moreover
  {
    assume "A' = A"
    hence "Col G H P" 
      using Cong_perm False \<open>P Midpoint A A'\<close> assms(4) circumcenter_cong_2 
        l8_20_2 by blast
  }
  moreover
  {
    assume "\<not> Col A B A' \<and> \<not> Col A C A'"
    have "Per A B A'" 
      by (meson midpoint_thales \<open>P Midpoint A A'\<close> 
          \<open>\<not> Col A B A' \<and> \<not> Col A C A'\<close> assms(4) circumcenter_cong_1 
          not_col_permutation_5 not_cong_2143)
    have "C H Perp A B" 
      using IsOrthocenter_def assms(3) by blast
    have "A' B Perp B A" 
      by (metis \<open>Per A B A'\<close> \<open>\<not> Col A B A' \<and> \<not> Col A C A'\<close> l8_2 
          not_col_distincts per_perp)
    hence "C H Par A' B" 
    proof -
      have "Coplanar A B C A'" 
        using Concyclic2_def \<open>Concyclic2 A B C A'\<close> by blast
      moreover
      have "Coplanar A B C B" 
        using ncop_distincts by blast
      moreover
      have "Coplanar A B H A'"
      proof -
        have "C H Perp A B" 
          by (simp add: \<open>C H Perp A B\<close>)
        hence "Coplanar A B H C" 
          using coplanar_perm_17 perp__coplanar by blast
        thus ?thesis 
          by (meson assms(1) calculation(1) coplanar_perm_12 
              coplanar_perm_18 coplanar_trans_1 not_col_permutation_2)
      qed
      moreover
      have "Coplanar A B H B"
        using ncop_distincts by blast
      moreover
      have "A' B Perp A B" 
        by (simp add: \<open>A' B Perp B A\<close> perp_right_comm)
      ultimately
      show ?thesis 
        using  \<open>C H Perp A B\<close> l12_9 by blast
    qed
    have "B H Perp A C" 
      using IsOrthocenter_def assms(3) by blast
    have "Cong P A P C" 
      using assms(4) circumcenter_cong_3 not_cong_4321 by blast
    hence "Per A C A'" 
      using \<open>P Midpoint A A'\<close> \<open>\<not> Col A B A' \<and> \<not> Col A C A'\<close> col_permutation_5 
        midpoint_thales by blast
    have "A' C Perp C A" 
      by (metis \<open>Per A C A'\<close> \<open>\<not> Col A B A' \<and> \<not> Col A C A'\<close> l8_2 not_col_distincts per_perp)
    have "B H Par C A'" 
    proof -
      have "Coplanar A C B C" 
        using ncop_distincts by auto
      moreover
      have "Coplanar A C B A'" 
        using Concyclic2_def \<open>Concyclic2 A B C A'\<close> coplanar_perm_2 by blast
      moreover
      have "Coplanar A C H C" 
        using ncop_distincts by blast
      moreover
      have "Coplanar A C H A'" 
        by (meson \<open>C H Perp A B\<close> assms(1) calculation(2) coplanar_perm_8 
            l9_30 ncop_distincts not_col_permutation_5 perp__coplanar)
      moreover
      have "B H Perp A C" 
        using \<open>B H Perp A C\<close> by auto
      moreover
      have "C A' Perp A C" 
        using \<open>A' C Perp C A\<close> perp_comm by blast
      ultimately
      show ?thesis 
        using l12_9 by blast
    qed
    have "Col G H P" 
    proof (cases "Col B H C")
      case True
      hence "Col B H C"
        by simp
      hence "H = B \<or> H = C" 
        by (metis \<open>C H Perp A B\<close> assms(3) col_permutation_1 col_transitivity_2 
            l8_16_1 orthocenter_per)
      thus ?thesis 
        using \<open>B H Par C A'\<close> \<open>C H Par A' B\<close> par_distinct by blast
    next
      case False
      hence "\<not> Col B H C" 
        by simp
      have "Parallelogram B H C A'" 
        by (meson False Par_cases \<open>B H Par C A'\<close> \<open>C H Par A' B\<close> par_2_plg)
      obtain I where  "I Midpoint B C" and "I Midpoint H A'" 
        using \<open>Parallelogram B H C A'\<close> plg_mid by blast
      {
        assume "Per A B C"
        hence "Col G H P" 
          using Euler_line_special_case assms(2) assms(3) assms(4) by blast
      }
      moreover
      {
        assume "\<not> Per A B C"
        have "A' \<noteq> H" 
          using False \<open>B H Par C A'\<close> par_comm par_id_1 by blast
        {
          assume "Col A H A'"
          obtain A'' where "A'' Midpoint B C" 
            using \<open>I Midpoint B C\<close> by auto
          hence "I = A''" 
            using \<open>I Midpoint B C\<close> l7_17 by blast
          {
            assume "A' = H" 
            hence False 
              by (simp add: \<open>A' \<noteq> H\<close>)
          }
          moreover
          {
            assume "A' \<noteq> H" 
            {
              assume "A'' = P"
              hence False 
                by (metis IsOrthocenter_def \<open>A'' = P\<close> \<open>Col A H A'\<close> \<open>I = A''\<close> 
                    \<open>I Midpoint H A'\<close> \<open>P Midpoint A A'\<close> assms(3) 
                    midpoint_midpoint_col perp_distinct)
            }
            moreover
            {
              assume "A'' \<noteq> P"
              have "P A'' PerpBisect B C" 
                using \<open>A'' Midpoint B C\<close> \<open>A'' \<noteq> P\<close> \<open>C \<noteq> B\<close> assms(4) circumcenter_perp by force
              {
                assume "A = A''" 
                hence False 
                  using \<open>A'' Midpoint B C\<close> assms(1) midpoint_col by auto
              }
              moreover
              {
                assume "A \<noteq> A''" 
                hence "A'' A Perp B C" 
                  by (metis IsOrthocenter_def \<open>A' \<noteq> H\<close> \<open>Col A H A'\<close> \<open>I = A''\<close> 
                      \<open>I Midpoint H A'\<close> assms(3) col2__eq midpoint_col perp_col2)
                hence "A'' A PerpBisect B C" 
                  using \<open>A'' Midpoint B C\<close> perp_mid_perp_bisect by auto
                hence False 
                  using \<open>\<not> Cong A B A C\<close> not_cong_2143 perp_bisect_cong_2 by blast
              }
              ultimately have False 
                by blast
            }
            ultimately
            have False by blast
          }
          ultimately have False 
            by blast
        }
        hence "G IsGravityCenter A H A'" 
          using \<open>I Midpoint B C\<close> \<open>I Midpoint H A'\<close> assms(2) 
            gravity_center_change_triangle by blast
        hence "G IsGravityCenter A A' H" 
          using calculation is_gravity_center_perm_1 by blast
        hence "Col G H P" 
          by (meson is_gravity_center_col \<open>P Midpoint A A'\<close> not_col_permutation_5)
      }
      ultimately
      show ?thesis 
        by blast
    qed
  }
  ultimately
  show ?thesis 
    by fastforce
qed

(*
definition isosceles::
"['p,'p,'p] \<Rightarrow> bool"
("isosceles _ _ _" [99,99,99] 50)
where
"isosceles A B C \<equiv>
Cong A B B C" 
*)

(**
Exercice 35 : Dans un triangle rectangle
a. GAZ est un triangle rectangle en A. Les points F, E et R sont
les milieux respectifs de [AZ], [GZ] et [GA]. Fais une figure.
b. Quelle est la nature du quadrilatère FERA ?
Prouve-le.
*)

lemma sesamath_4ieme_G2_ex35: 
  assumes "\<not> Col G A Z" and
    "Per G A Z" and
    "F Midpoint A Z" and
    "E Midpoint G Z" and
    "R Midpoint G A"
  shows "Rectangle F E R A" 
  by (metis Col_def Per_mid_rectangle assms(1) assms(2) assms(3) 
      assms(4) assms(5) between_trivial l7_2 rect_permut)    

(**
Exercice 36 : Dans un triangle isocèle
ABC est un triangle isocèle en A. [AH] est la hauteur issue de A.
Les points I et J sont les milieux respectifs de [AB] et [AC].

Quelle est la nature de AIHJ ?
*)

(** A first solution using the fact that A I H J is a parallelogram whose
diagonals are perpendicular *)

lemma sesamath_4ieme_G2_ex36_aux:
  assumes "\<not> Col A B C" and
    "I Midpoint A B" and
    "J Midpoint A C" and
    "K Midpoint B C" 
  shows "Plg I J K B" 
proof -
  have "A B Par J K" 
    using assms(1) assms(3) assms(4) not_col_distincts 
      triangle_mid_par by blast
  hence "B I Par J K" 
    using par_col_par_2 by (metis Par_cases assms(2) midpoint_col 
        midpoint_distinct_1 not_col_permutation_3)
  moreover
  have "B C Par I J" 
    by (metis Col_def assms(1) assms(2) assms(3) assms(4) between_trivial 
        par_right_comm triangle_mid_par_cong_1)
  hence "B K Par I J" 
    by (metis Col_cases assms(4) midpoint_col midpoint_distinct_1 
        par_col_par par_symmetry)
  moreover
  {
    assume "Col B K J"
    hence "Col A B J" 
      by (meson \<open>A B Par J K\<close> not_col_distincts not_col_permutation_5 
          par_not_col_strict par_strict_not_col_2)
    hence False 
      by (metis assms(1) assms(3) col_transitivity_2 midpoint_col 
          midpoint_distinct_1 not_col_permutation_1)
  }
  ultimately
  show ?thesis 
    by (meson col_trivial_3 inter_uniqueness_not_par par_2_plg 
        par_right_comm par_symmetry parallelogram_to_plg plg_comm2)
qed

lemma sesamath_4ieme_G2_ex36:
  assumes "B A C isosceles" and 
    "A H Perp B C" and
    "Col B H C" and
    "I Midpoint A B" and
    "J Midpoint A C" 
  shows "Rhombus A I H J" 
proof -
  have "Col H B C" 
    using assms(3) not_col_permutation_4 by blast
  have "H A Perp B C" 
    using Perp_cases assms(2) by blast
  hence "\<not> Col B A C \<and> B \<noteq> H \<and> C \<noteq> H \<and> H Midpoint B C \<and> H A B CongA H A C"
    using isosceles_foot__midpoint_conga \<open>Col H B C\<close> assms(1) by blast
  have "Plg A I H J" 
  proof -
    have "Plg J H I A" 
      by (meson \<open>\<not> Col B A C \<and> B \<noteq> H \<and> C \<noteq> H \<and> H Midpoint B C \<and> H A B CongA H A C\<close> 
          assms(4) assms(5) l7_2 not_col_permutation_3 sesamath_4ieme_G2_ex36_aux)
    thus ?thesis 
      by (metis Plg_def l7_2)
  qed
  hence "A H Perp I J" 
  proof -
    have "I J Par B C" 
      by (metis Par_cases \<open>Col H B C\<close> \<open>H A Perp B C\<close> 
          \<open>\<not> Col B A C \<and> B \<noteq> H \<and> C \<noteq> H \<and> H Midpoint B C \<and> H A B CongA H A C\<close> 
          assms(4) assms(5) col_par midpoint_distinct_2 not_col_permutation_5
          perp_not_par triangle_mid_par_cong)
    hence "B C Par I J" 
      using Par_cases by blast
    moreover
    have "B C Perp A H" 
      using Perp_perm \<open>H A Perp B C\<close> by blast
    moreover
    have "Coplanar A H I J" 
      by (metis \<open>\<not> Col B A C \<and> B \<noteq> H \<and> C \<noteq> H \<and> H Midpoint B C \<and> H A B CongA H A C\<close>
          assms(4) assms(5) col__coplanar coplanar_perm_2 midpoint_col 
          not_col_distincts not_col_permutation_2 par_col_par_2 
          par_cong_cop par_left_comm triangle_mid_par)
    ultimately
    show ?thesis
      using Perp_cases cop_par_perp__perp coplanar_perm_16 by blast
  qed
  thus ?thesis 
    by (simp add: \<open>Plg A I H J\<close> perp_rmb)
qed

(**
Exercice 37 : Avec une médiatrice
SEL est un triangle quelconque. Les points I, M et A sont les milieux respectifs
de [LS], [SE] et [EL]. La médiatrice de [LE] coupe la droite (IM) en O.
a. Fais une figure.
b. Que représente (AO) pour le triangle IMA?
Prouve-le.

rename O \<longrightarrow> P
*)

lemma sesamath_4ieme_G2_ex37: 
  assumes "\<not> Col S E L" and
    "I Midpoint L S" and 
    "M Midpoint S E" and
    "A Midpoint E L" and
    "A P PerpBisect L E" and
    "Coplanar S E L P"
  shows "A P Perp I M" 
proof -
  have "L E Par I M" 
    by (metis assms(1) assms(2) assms(3) l7_2 not_col_distincts triangle_mid_par)
  have "A P Perp L E" 
    using assms(5) perp_bisect_perp by blast
  have "I M Perp P A" 
  proof -
    have "L E Par I M" 
      using \<open>L E Par I M\<close> by force
    moreover
    have "L E Perp P A" 
      using Perp_perm \<open>A P Perp L E\<close> by blast
    moreover
    have "Coplanar I M P A" 
    proof -
      have "Col I L S" 
        by (simp add: assms(2) midpoint_col)
      moreover
      have "Col M S E" 
        by (simp add: assms(3) midpoint_col)
      moreover
      have "Col A L E" 
        using assms(4) col_permutation_5 midpoint_col by presburger
      ultimately
      show ?thesis
        by (meson assms(1) assms(6) coplanar_perm_9 coplanar_pseudo_trans 
            ncop__ncols not_col_permutation_3)
    qed
    ultimately
    show ?thesis 
      using cop_par_perp__perp by blast
  qed
  thus ?thesis 
    using Perp_perm by blast
qed



(**
Exercice 38 avec une médiane
a. Construis un triangle EAU quelconque.
b. Construis la médiane [EL].
Place N milieu de [AE] et M milieu de [EU].
O est le point d'intersection de (EL) et de (MN).
c. Est-il vrai que (OL) est une médiane du triangle LMN ?
Justifie ta réponse.
*)

lemma sesamath_4ieme_G2_ex38 :
  assumes "\<not> Col E A U" and
    "N Midpoint E A" and
    "M Midpoint E U" and
    "L Midpoint U A"
  shows "\<exists> P. Col P E L \<and> P Midpoint M N" 
proof -
  have "\<not> Col U E A" 
    using assms(1) not_col_permutation_2 by presburger
  hence "Plg M L N E" 
    by (meson Mid_perm assms(2) assms(3) assms(4) sesamath_4ieme_G2_ex36_aux)
  hence "Parallelogram M L N E" 
    using parallelogram_equiv_plg by blast
  thus ?thesis 
    by (meson midpoint_col not_col_permutation_5 plg_mid)
qed


(** Exercice 39 Dans un demi-cercle
Sur la figure ci-dessous, le point A appartient au cercle de diamètre [CT]
et de centre S.
Les droites (HS) et (CA) sont perpendiculaires.
- Montre que H est le milieu du segment [CA].
*)

lemma sesamath_4ieme_G2_ex39:
  assumes "\<not> Col A C T" and
    "S IsCircumcenter C T A" and
    "S Midpoint C T" and 
    "Col C H A" and
    "S H Perp A C" 
  shows "H Midpoint A C" 
proof -
  have "S H Par T A" 
  proof -
    have "Coplanar A C S T" 
      using IsCircumcenter_def assms(2) ncoplanar_perm_15 by blast
    moreover
    have "Coplanar A C S A" 
      using ncop_distincts by blast
    moreover
    have "Coplanar A C H T" 
      using NCol_cases assms(4) ncop__ncol by blast
    moreover
    have "Coplanar A C H A" 
      using ncop_distincts by blast
    moreover
    have "Cong C S T S \<and> Cong T S A S \<and> Cong A S C S"
      using circumcenter_cong assms(2) by blast
    hence "Per C A T" 
      by (metis Col_cases midpoint_thales assms(1) assms(3) not_cong_4321)
    hence "T A Perp A C" 
      by (metis assms(1) l8_2 not_col_distincts per_perp)
    ultimately
    show ?thesis
      using assms(5) l12_9 by blast
  qed
  thus ?thesis 
    by (metis Mid_cases NCol_cases Par_cases assms(1) assms(3) assms(4) triangle_par_mid)
qed

(**
Exercice 40 : ABC est un triangle quelconque. R est un point de [BC]. On appelle S, T,
M et N les milieux respectifs de [BR], [RC], [AB] et [AC].
a- Montre que (NT) est parallèle à (MS).
b- Montre que MNTS est un parallélogramme.
*)

lemma sesamath_4ieme_G2_ex40:
  assumes "\<not> Col A B C" and
    "Bet C R B" and
    "M Midpoint A B" and
    "N Midpoint A C" and
    "S Midpoint B R" and
    "T Midpoint R C"
  shows "M S Par N T \<and> Parallelogram M S T N" 
proof -
  have "A R Par M S" 
    by (metis assms(1) assms(2) assms(3) assms(5) bet_col l7_2 
        not_col_permutation_2 triangle_mid_par)
  hence "A R Par N T" 
    using assms(4) assms(6) par_neq1 triangle_mid_par by blast
  hence "M S Par N T" 
    by (meson \<open>A R Par M S\<close> not_par_one_not_par par_symmetry)
  moreover
  have "Parallelogram M S T N" 
  proof (cases "R = B")
    case True
    thus ?thesis 
      using \<open>A R Par N T\<close> assms(3) assms(4) assms(5) assms(6)
        par_neq1 varignon_bis by blast
  next
    case False
    thus ?thesis 
      by (metis assms(2) assms(3) assms(4) assms(5) assms(6) bet_neq12__neq varignon_bis)
  qed
  ultimately
  show ?thesis 
    by blast
qed

(**
Exercice 41 :
Sur la figure suivante, THL est un triangle quelconque, O est le milieu
du segment [TH], E celui de [TL] et S est un point de [HL].
a- Montre que les angles SAE et TSH ont la même mesure.
b- Montre que A est le milieu de [TS].
*)

lemma sesamath_4ieme_G2_ex41 :
  assumes "\<not> Col T L H" and
    "E Midpoint T L" and
    "P Midpoint T H" and
    "A \<noteq> T" and
    "A \<noteq> P" and
    "A \<noteq> E" and
    "A \<noteq> S" and
    "Bet T A S" and
    "Bet P A E" and
    "Bet H S L" and
    "S \<noteq> H" and
    "S \<noteq> L" 
  shows "S A E CongA T S H \<and> A Midpoint T S" 
proof -
  have "H L OS T T" 
    using Col_cases assms(1) one_side_reflexivity by blast
  have "H S OS T T" 
    by (metis Bet_cases Col_def \<open>H L OS T T\<close> assms(10) assms(11) col_one_side)
  hence "\<not> Col H S T" 
    using col123__nos by blast
  hence "T S OS H H" 
    using invert_one_side one_side_reflexivity by blast
  hence "T A OS H H" 
    by (metis Bet_cases Col_def assms(4) assms(8) col_one_side) 
  have "Bet T P H" 
    by (simp add: assms(3) midpoint_bet)
  hence "T Out P H" 
    using assms(1) assms(3) midpoint_out not_col_distincts by presburger
  have "T A OS H P" 
    by (meson Out_cases \<open>T A OS H H\<close> \<open>T Out P H\<close> out_out_one_side)
  hence "T A OS P H"  
    by (simp add: one_side_symmetry)
  have "H L Par P E" 
    by (metis assms(1) assms(2) assms(3) l7_2 not_col_distincts triangle_mid_par)
  have "H L Par P A" 
    by (metis \<open>H L Par P E\<close> assms(5) assms(9) bet_col not_par_not_col 
        not_par_one_not_par par_neq2)
  hence "H S Par P A" 
    by (metis assms(1) assms(10) assms(11) bet_col not_col_distincts 
        par_col2_par par_reflexivity par_trans)
  have "T Out A S" 
    by (simp add: assms(4) assms(8) bet_out)
  have "P A T CongA H S T" 
    by (meson Par_cases \<open>H S Par P A\<close> \<open>T A OS P H\<close> assms(4) assms(8) 
        bet_out l12_22_a)
  have "P A T CongA E A S" 
    using assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) l11_14 by force
  hence "H S T CongA E A S" 
    by (meson \<open>P A T CongA H S T\<close> not_conga not_conga_sym)
  moreover
  have "A Midpoint S T" 
    by (metis NCol_cases \<open>H S Par P A\<close> \<open>\<not> Col H S T\<close> assms(3) assms(8) 
        bet_col l7_2 par_comm triangle_par_mid)
  ultimately
  show ?thesis 
    by (meson conga_comm conga_sym l7_2)
qed

(**
Exercice 42 :
ABC est un triangle quelconque. [BI] et [CJ] sont deux médianes, elles se coupent en G.
On désigne par K le milieu de [BG] et L celui de [CG].
a- Quelle est la nature du quadrilatère IJKL ?
Prouve-le.
b- Que peut-on dire de la position du point G sur chacune des médiane [BI] et [CJ]?
*)

lemma sesamath_4ieme_G2_ex42:
  assumes "\<not> Col A B C" and
    "G IsGravityCenter A B C" and
    "I Midpoint A C" and
    "J Midpoint A B" and
    "K Midpoint B G" and 
    "L Midpoint C G" 
  shows "Parallelogram I J K L" 
proof -
  have "G \<noteq> C"     
    using assms(2) is_gravity_center_diff_3 by auto
  moreover
  have "G Midpoint J L" 
  proof -
    have "J Midpoint B A" 
      by (simp add: assms(4) l7_2)
    moreover
    have "G IsGravityCenter C B A" 
      using assms(2) is_gravity_center_perm_5 by blast
    ultimately show ?thesis
      using \<open>J Midpoint B A\<close> assms(6) is_gravity_center_third by blast
  qed
  ultimately show ?thesis 
    by (metis assms(1) assms(3) assms(4) assms(5) assms(6) 
        bet_col between_trivial l7_2 midpoint_distinct_3 varignon_aux_aux)
qed


(**
Exercice 44 :
ABCD est un parallélogramme. I est le milieu de [AD] et J le milieu de [BC].
a- Démontre que BJDI est un parallélogramme.
b- Est-il vrai que les droites (BI) et (DJ) divisent la diagonale [AC] en trois parties égales ?
Justifie ta réponse (ce problème est posé par Euclide dans le Livre III de sas "Eléments").
*)

lemma sesamath_4ieme_G2_ex44_1: 
  assumes "ParallelogramStrict A B C D" and
    "I Midpoint A D" and
    "J Midpoint B C" (*and 
"Bet A E C" and
"Bet I E B" and
"Bet A F C" and
"Bet D F J" *)
  shows "Parallelogram B J D I"
  by (metis MidR_uniq_aux Mid_cases assms(1) assms(2) assms(3) 
      half_plgs_R2 mid_plg plgs_diff plgs_permut) 

(**
Exercice 45 :
ABC est un triangle quelconque.
- I est le milieu de [BC].
- M est le symétrique de I par rapport au point A.
- J est le milieu de [AI].

La parallèle à (AC) passent par J coupe (BC) en K.
a- Démontre que K est le milieu de [IC].
b- Démontre que les droites (AK) et (MC) sont parallèles.
c- Que représente le point d'intersection des droites (CA) et (MK) pour le triangle MIC?
*) 
(** # <div style="width:748px;height:397px;display:block" id="applet_container45"></div> # **)

lemma sesamath_4ieme_G2_ex45:
  assumes "\<not> Col A B C" and
    "I Midpoint B C" and
    "Col I A M" and
    "A Midpoint I M" and 
    "J Midpoint A I" and 
    "J K Par A C" and
    "Col K I C" and
    "Col G C A" and 
    "Col G M K"
  shows "K Midpoint I C \<and> A K Par M C \<and> G IsGravityCenter C M I" 
proof -
  have "\<not> Col C I A" 
    by (metis assms(1) assms(2) col_trivial_2 l6_21 midpoint_col 
        midpoint_distinct_1 not_col_permutation_1)
  have "K Midpoint I C" 
    by (meson Par_cases \<open>\<not> Col C I A\<close> assms(5) assms(6) assms(7) l7_2 
        not_col_permutation_5 triangle_par_mid)
  moreover
  have "A K Par M C \<and> G IsGravityCenter C M I" 
  proof (cases "I = M")
    case True
    hence "A = B" 
      by (metis \<open>\<not> Col C I A\<close> assms(4) l7_17 l7_3_2 not_col_distincts)
    hence False 
      using assms(1) not_col_distincts by auto
    hence "A K Par M C"
      by blast
    moreover
    have "G IsGravityCenter C M I" 
      using True \<open>\<not> Col C I A\<close> assms(4) l7_17_bis l7_3_2 not_col_distincts by blast
    ultimately
    show ?thesis 
      by blast
  next
    case False
    have "\<not> Col I M C" 
      by (meson False \<open>\<not> Col C I A\<close> assms(3) col_permutation_2 col_trivial_3 colx)
    have "K Midpoint C I" 
      by (simp add: calculation l7_2)
    have "M C Par A K" 
      by (metis \<open>K Midpoint C I\<close> \<open>\<not> Col I M C\<close> assms(4) l7_2 
          not_col_distincts triangle_mid_par)
    hence "A K Par M C" 
      by (simp add: par_symmetry)
    moreover
    have "G IsGravityCenter C M I" 
      using IsGravityCenter_def Mid_cases \<open>K Midpoint C I\<close> \<open>\<not> Col I M C\<close> 
        assms(4) assms(8) assms(9) col_permutation_3 by blast
    ultimately
    show ?thesis 
      by blast
  qed
  ultimately
  show ?thesis 
    by blast
qed

(**
Exercice 47 :
Sur une droite (d), on considère trois points A, B et C tels que B soit le milieu de [AC].
Sur une droite (d'), on considère un point A'.
B' est le point d'intersection de (d') et de la parallèle à (AA') passant par B.
C' est le point d'intersection de (d') et de la parallèle à (AA') passant par C.
a- Construis cette figure.
b- Que dire de B'? Prouve-le.
*)

lemma sesamath_4ieme_G2_ex47 :
  assumes "\<not> Col A C C'" and
    "\<not> Col A A' C'" and
    "Col B' A' C'" and
    "B Midpoint A C" and
    "A A' Par B B'" and 
    "A A' Par C C'"  
  shows "B' Midpoint A' C'" 
proof -
  obtain x where "x Midpoint A C'" 
    using MidR_uniq_aux by blast
  have "B B' Par A A'"
    using assms(5) par_symmetry by blast
  hence "B B' Par C C'" 
    using assms(6) par_trans by blast
  have "C C' Par B x " 
    by (metis \<open>x Midpoint A C'\<close> assms(1) assms(4) l7_2 not_col_distincts 
        triangle_mid_par)
  hence "B B' Par B x" 
    using \<open>B B' Par C C'\<close> par_trans by blast
  hence "Col B B' x" 
    by (simp add: par_id)
  have "A A' Par B x" 
    by (meson \<open>B B' Par B x\<close> assms(5) par_trans)
  show ?thesis 
  proof (cases "x = B'")
    case True
    have "Col A C' A'" 
      by (metis True \<open>x Midpoint A C'\<close> assms(3) col2__eq col_permutation_1 
          midpoint_col midpoint_distinct_1)
    thus ?thesis 
      using Col_cases assms(2) by blast
  next
    case False
    have "B x Par B' B" 
      using Par_perm \<open>B B' Par B x\<close> by blast
    hence "B x Par B' x" 
      using False \<open>B B' Par B x\<close>  par_col_par par_id_1 by presburger
    hence "A A' Par B' x" 
      using \<open>A A' Par B x\<close> par_trans by blast
    thus ?thesis 
      using \<open>x Midpoint A C'\<close> assms(2) assms(3) not_col_permutation_4 
        par_left_comm triangle_par_mid by blast
  qed
qed

end
end