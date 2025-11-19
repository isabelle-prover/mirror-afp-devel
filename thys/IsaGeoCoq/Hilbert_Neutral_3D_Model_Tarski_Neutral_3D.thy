(* IsageoCoq - Hilbert_Neutral_3D_Model_Tarski_Neutral_3D.thy
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

theory Hilbert_Neutral_3D_Model_Tarski_Neutral_3D

imports 
  Tarski_Neutral_3D_Hilbert
  Hilbert_Neutral_3D

begin

section "Hilbert Neutral 3D - Tarski Neutral 3D Model"

subsection "Interpretation"

context Tarski_neutral_3D

begin

interpretation Interpretation_Hilbert_neutral_dimensionless_pre: Hilbert_neutral_dimensionless_pre 
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
proof -
qed

interpretation Intrepretation_Hilbert_neutral_dimensionless: Hilbert_neutral_dimensionless
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
    and PP = TPA           and PQ = TPB           and PR = TPC
proof
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col_H A B C" 
  proof -
    {
      fix A B C
      assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        by (simp add: Hilbert_neutral_dimensionless_pre.ColH_def)
      hence "Col_H A B C" 
        using Col_H_def EqTL_def axiom_line_uniqueness cols_coincide_2 not_col_distincts by blast
    }
    moreover
    {
      fix A B C
      assume "Col_H A B C" 
      hence "\<exists> l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l" 
        using Col_H_def by blast
      have "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
        using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l \<and> IncidentL C l\<close> by blast
    }
    ultimately show ?thesis
      by blast
  qed
  have "\<forall> A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longleftrightarrow> Col A B C"
    using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
      cols_coincide by blast
  have "\<forall> A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l
                  \<longleftrightarrow> same_side_H A B l" 
    by (simp add: Hilbert_neutral_dimensionless_pre.cut_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.same_side_def cut_H_def same_side_H_def)
  have "\<forall> A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                   \<longleftrightarrow> same_side'_H A B C D" 
    by (simp add: Hilbert_neutral_dimensionless_pre.same_side'_def 
        \<open>\<forall>A B l. Interpretation_Hilbert_neutral_dimensionless_pre.same_side A B l 
                    = same_side_H A B l\<close> 
        same_side'_H_def)
  show "\<And>l. isLine l \<longrightarrow> l =l= l" 
    by (simp add: eq_reflexivity)
  show "\<And>l1 l2. isLine l1 \<and> isLine l2 \<and> l1 =l= l2 \<longrightarrow> l2 =l= l1" 
    using eq_symmetry by blast
  show "\<And>l1 l2 l3. l1 =l= l2 \<and> l2 =l= l3 \<longrightarrow> l1 =l= l3" 
    using eq_transitivity by blast
  show "\<And>p. isPlane p \<longrightarrow> p =p= p" 
    by (simp add: eqp_reflexivity)
  show "\<And>p1 p2. p1 =p= p2 \<longrightarrow> p2 =p= p1" 
    using eqp_symmetry by blast
  show "\<And>p1 p2 p3. p1 =p= p2 \<and> p2 =p= p3 \<longrightarrow> p1 =p= p3" 
    using eqp_transitivity by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>l. isLine l \<and> IncidentL A l \<and> IncidentL B l)" 
    using axiom_line_existence by blast
  show "\<And>A B l m.
A \<noteq> B \<and> isLine l \<and> isLine m \<and>
IncidentL A l \<and> IncidentL B l \<and> IncidentL A m \<and> IncidentL B m \<longrightarrow>
l =l= m" 
    using axiom_line_uniqueness by blast
  show "\<forall>l. isLine l \<longrightarrow> (\<exists> A B. IncidentL A l \<and> IncidentL B l \<and> A \<noteq> B)" 
    using axiom_two_points_on_line by blast
  show "TPA \<noteq> TPB \<and> TPB \<noteq> TPC \<and> TPA \<noteq> TPC \<and> 
           \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH TPA TPB TPC" 
    using Bet_cases  between_trivial lower_dim third_point 
      \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close>
    by blast
  show "\<forall>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
  (\<exists>p. isPlane p \<and> IncidentP A p \<and> IncidentP B p \<and> IncidentP C p)" 
    using bet__coplanar between_trivial2 cop_plane IncidentP_def by blast
  show "\<forall>p. \<exists>A. isPlane p \<longrightarrow> IncidentP A p" 
    by (simp add: axiom_one_point_on_plane)
  show "\<And>A B C p q.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  isPlane p \<and> isPlane q \<and>
  IncidentP A p \<and>
  IncidentP B p \<and>
  IncidentP C p \<and> IncidentP A q \<and> IncidentP B q \<and> IncidentP C q \<longrightarrow>
  p =p= q" 
    using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
      axiom_plane_uniqueness by blast
  show "\<forall>A B l p.
  A \<noteq> B \<and> isLine l \<and> isPlane p \<and>
  IncidentL A l \<and> IncidentL B l \<and> IncidentP A p \<and> IncidentP B p \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" 
    by (meson IncidentLP_def Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        axiom_line_on_plane)
  show "\<And>A B C. Between_H A B C \<longrightarrow> A \<noteq> C" 
    using axiom_between_diff by blast
  show "\<And>A B C. Between_H A B C \<longrightarrow> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    by (meson Between_H_def Col_H_def Col_def 
        Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def cols_coincide_2)
  show "\<And>A B C. Between_H A B C \<longrightarrow> Between_H C B A" 
    using axiom_between_comm by blast
  show "\<And>A B. A \<noteq> B \<longrightarrow> (\<exists>C. Between_H A B C)" 
    by (simp add: axiom_between_out)
  show "\<And>A B C. Between_H A B C \<longrightarrow> \<not> Between_H B C A" 
    using axiom_between_only_one by blast
  {
    fix A B C p l
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "isLine l" and
      "IncidentP A p" and
      "IncidentP B p" and
      "IncidentP C p" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p" and
      "\<not> IncidentL C l" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B"
    have "\<not> Col A B C" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2)
    moreover have "cut_H l A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.cut_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B\<close> cut_H_def by blast
    ultimately have "cut_H l A C \<or> cut_H l B C" 
      using axiom_pasch Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP_def 
        \<open>IncidentP A p\<close> \<open>IncidentP B p\<close> \<open>IncidentP C p\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p\<close> \<open>\<not> IncidentL C l\<close> 
        axiom_line_on_plane axiom_two_points_on_line cols_coincide_1 by meson
    hence "Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
    Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C"  
      by (simp add: Hilbert_neutral_dimensionless_pre.cut_def cut_H_def)
  }
  thus "\<And>A B C p l.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  isLine l \<and> isPlane p \<and>
  IncidentP A p \<and>
  IncidentP B p \<and>
  IncidentP C p \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.IncidLP l p \<and>
  \<not> IncidentL C l \<and> Interpretation_Hilbert_neutral_dimensionless_pre.cut l A B \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.cut l A C \<or>
  Interpretation_Hilbert_neutral_dimensionless_pre.cut l B C" 
    by blast
  {
    fix l 
    fix A B A' P::'a
    assume "A \<noteq> B" and
      "A' \<noteq> P" and
      "isLine l" and
      "IncidentL A' l" and
      "IncidentL P l"
    then obtain B' where "IncidentL B' l \<and> outH A' P B' \<and> Cong A' B' A B"  
      using axiom_hcong_1_existence by presburger
    hence "\<exists>B'. IncidentL B' l \<and> 
    Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.outH_def outH_def by auto
  }
  thus "\<And>l A B A' P. A \<noteq> B \<and> A' \<noteq> P \<and> isLine l \<and> IncidentL A' l \<and> IncidentL P l \<longrightarrow>
  (\<exists>B'. IncidentL B' l \<and> 
  Interpretation_Hilbert_neutral_dimensionless_pre.outH A' P B' \<and> Cong A' B' A B)"
    by blast
  show "\<And>A B C D E F. Cong A B C D \<and> Cong A B E F \<longrightarrow> Cong C D E F" 
    using cong_inner_transitivity by blast
  {
    fix A B C A' B' C'
    assume "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'" and
      "Cong A B A' B'" and
      "Cong B C B' C'" 
    have " (\<exists> l. IncidentL A l \<and> IncidentL B l \<and> IncidentL C l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by force
    then obtain l where "IncidentL A l" and "IncidentL B l" and "IncidentL C l"
      by blast
    hence "Col A B C"
      using \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close>
        \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close> by auto 
    moreover
    have " (\<exists> l. IncidentL A' l \<and> IncidentL B' l \<and> IncidentL C' l)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by force
    then obtain l' where "IncidentL A' l'" and "IncidentL B' l'" and "IncidentL C' l'"
      by blast
    hence "Col A' B' C'"
      using \<open>Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close>
        \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close> by auto 
    moreover
    have "\<not> (\<exists> P. Between_H A P B \<and> Between_H B P C)" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C\<close> by blast
    have "\<not> (\<exists> P. Between_H A' P B' \<and> Between_H B' P C')" 
      using Interpretation_Hilbert_neutral_dimensionless_pre.disjoint_def 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C'\<close> by blast
    have "Col_H A B C" 
      using calculation(1) cols_coincide_2 by blast
    hence "Bet A B C" 
      using \<open>\<nexists>P. Between_H A P B \<and> Between_H B P C\<close> col_disjoint_bet disjoint_H_def by blast
    moreover
    have "Col_H A' B' C'" 
      by (simp add: calculation(2) cols_coincide_2)
    moreover
    hence "Bet A' B' C'" 
      by (simp add: \<open>\<nexists>P. Between_H A' P B' \<and> Between_H B' P C'\<close> col_disjoint_bet disjoint_H_def)
    ultimately
    have "Cong A C A' C'" 
      using Tarski_neutral_dimensionless.l2_11_b Tarski_neutral_dimensionless_axioms 
        \<open>Cong A B A' B'\<close> \<open>Cong B C B' C'\<close> by fastforce
  }
  thus "\<And>A B C A' B' C'.
  Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A B B C \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.disjoint A' B' B' C' \<and>
  Cong A B A' B' \<and> Cong B C B' C' \<longrightarrow>
  Cong A C A' C'" 
    by blast
  {
    fix A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C"
    hence "\<not> Col A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = (Col A B C)\<close> 
      by blast
    hence "A B C CongA A B C" 
      by (metis Tarski_neutral_dimensionless.conga_refl 
          Tarski_neutral_dimensionless.not_col_distincts Tarski_neutral_dimensionless_axioms)
    hence "CongA_H A B C A B C" 
      by (simp add: CongA_H_def)
  }
  thus "\<And>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C A B C" 
    by blast
  show "\<And>A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow> CongA_H A B C C B A" 
    using CongA_H_def 
      \<open>\<And>Ca Ba A. \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A Ba Ca 
                  \<longrightarrow> CongA_H A Ba Ca A Ba Ca\<close> conga_right_comm by presburger
  show "\<And>A B C D E F. CongA_H A B C D E F \<longrightarrow> CongA_H C B A F E D" 
    by (meson CongA_H_def Tarski_neutral_dimensionless.axiom_conga_permlr
        Tarski_neutral_dimensionless_axioms)
  show "\<And>A B C D E F A' C' D' F'. CongA_H A B C D E F \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH B A A' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH B C C' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH E D D' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH E F F' \<longrightarrow>
  CongA_H A' B C' D' E F'" 
    using axiom_congaH_outH_congaH CongA_H_def outH_def 
      Interpretation_Hilbert_neutral_dimensionless_pre.outH_def by force
  {
    fix P PO X A B C
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    ultimately
    obtain Y where "A B C CongA X PO Y" and "same_side'_H P Y PO X" 
      using axiom_hcong_4_existence cols_coincide_1 by blast 
    hence "PO \<noteq> X \<and> (\<forall> l. isLine l \<longrightarrow> (IncidentL PO l \<and> IncidentL X l) \<longrightarrow> same_side_H P Y l)"
      using same_side'_H_def by auto
    have "\<exists>Y. CongA_H A B C X PO Y \<and> 
              Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X"
    proof -
      have "CongA_H A B C X PO Y" 
        by (simp add: CongA_H_def \<open>A B C CongA X PO Y\<close>)
      moreover 
      have "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" 
        by (simp add: 
            \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                        = same_side'_H A B C D\<close> 
            \<open>same_side'_H P Y PO X\<close>)
      ultimately show ?thesis
        by blast
    qed
  }
  thus "\<And>P PO X A B C.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<longrightarrow>
  (\<exists>Y. CongA_H A B C X PO Y \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X)" 
    by blast
  {
    fix P PO X A B C Y Y'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "CongA_H A B C X PO Y" and
      "CongA_H A B C X PO Y'" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X" and
      "Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X" 
    have "\<not> Col P PO X" 
      by (meson Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
          \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X\<close> cols_coincide_2)
    moreover
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "A B C CongA X PO Y" 
      using CongA_H_def \<open>CongA_H A B C X PO Y\<close> by blast
    moreover
    have "A B C CongA X PO Y'" 
      using CongA_H_def \<open>CongA_H A B C X PO Y'\<close> by auto
    ultimately
    have "Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
      using \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X\<close> 
        \<open>Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X\<close> 
        axiom_hcong_4_uniqueness cols_coincide_1 
      by (metis Interpretation_Hilbert_neutral_dimensionless_pre.outH_def 
          \<open>\<forall>A B C D. Interpretation_Hilbert_neutral_dimensionless_pre.same_side' A B C D 
                     = same_side'_H A B C D\<close> 
          outH_def)
  }
  thus "\<And>P PO X A B C Y Y'.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH P PO X \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  CongA_H A B C X PO Y \<and>
  CongA_H A B C X PO Y' \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y PO X \<and>
  Interpretation_Hilbert_neutral_dimensionless_pre.same_side' P Y' PO X \<longrightarrow>
  Interpretation_Hilbert_neutral_dimensionless_pre.outH PO Y Y'" 
    by blast
  {
    fix A B C A' B' C'
    assume "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C" and
      "\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'" and
      "Cong A B A' B'" and
      "Cong A C A' C'" and
      "CongA_H B A C B' A' C'"
    have "\<not> Col_H A B C" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> by auto
    moreover
    have "\<not> Col_H A' B' C'" 
      using \<open>\<forall>A B C. Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C = Col_H A B C\<close> 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> by blast
    have "\<not> Col A B C" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C\<close> cols_coincide_2 by blast
    moreover
    have "\<not> Col A' B' C'" 
      using Col_H_def Interpretation_Hilbert_neutral_dimensionless_pre.ColH_def 
        \<open>\<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C'\<close> 
        cols_coincide_2 by blast
    moreover
    have "B A C CongA B' A' C'" 
      using CongA_H_def \<open>CongA_H B A C B' A' C'\<close> by auto
    ultimately
    have "CongA_H A B C A' B' C'" 
      using CongA_H_def \<open>Cong A B A' B'\<close> \<open>Cong A C A' C'\<close> l11_49 not_col_distincts by blast
  }
  thus "\<And>A B C A' B' C'.
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A B C \<and>
  \<not> Interpretation_Hilbert_neutral_dimensionless_pre.ColH A' B' C' \<and>
  Cong A B A' B' \<and> Cong A C A' C' \<and> CongA_H B A C B' A' C' \<longrightarrow>
  CongA_H A B C A' B' C'" 
    by blast
  show "\<And>A B C D. Cong A B C D \<longrightarrow> Cong A B D C" 
    using not_cong_1243 by blast
  show "\<And>l m P. isLine l \<and> isLine m \<and> IncidentL P l \<and> l =l= m \<longrightarrow> IncidentL P m" 
    using axiom_Incidl_morphism by blast
  show "\<And>p q M. isPlane p \<and> isPlane q \<and> IncidentP M p \<and> p =p= q \<longrightarrow> IncidentP M q" 
    using axiom_Incidp_morphism by blast
  show "\<And>P l. IncidentL P l \<longrightarrow> isLine l" 
    using IncidentL_def by blast
  show "\<And>P p. IncidentP P p \<longrightarrow> isPlane p" 
    using IncidentP_def by blast
qed

interpretation Intrepretation_Hilbert_neutral_3D: Hilbert_neutral_3D
  where IncidL = IncidentL and IncidP = IncidentP and EqL = EqTL 
    and EqP = EqTP         and IsL = isLine       and IsP = isPlane 
    and BetH = Between_H   and CongH = Cong       and CongaH = CongA_H 
    and PP = TPA           and PQ = TPB           and PR = TPC 
    and HS1 = TS1          and HS2 = TS2          and HS3 = TS3 
    and HS4 = TS4
proof
  {
    fix p q A
    assume "isPlane p" and
      "isPlane q" and
      "IncidentP A p" and "IncidentP A q"
    obtain PA PB PC where "p = Plane PA PB PC" and "\<not> Col_H PA PB PC" 
      by (metis Plane_def \<open>isPlane p\<close> cols_coincide_1 isPlane_def surj_pair)
    hence "\<not> Col PA PB PC" 
      by (simp add: cols_coincide)
    obtain QA QB QC where "q = Plane QA QB QC" and "\<not> Col_H QA QB QC" 
      by (metis Plane_def \<open>isPlane q\<close> cols_coincide_1 isPlane_def surj_pair)
    hence "\<not> Col QA QB QC" 
      by (simp add: cols_coincide)
    have "Coplanar A PA PB PC" 
    proof (rule plane_cop [where ?p = "p"])
      show "IncidentP A p" 
        by (simp add: \<open>IncidentP A p\<close>)
      show "IncidentP PA p" 
        using \<open>\<not> Col_H PA PB PC\<close> \<open>p = Plane PA PB PC\<close> axiom_plane_existence 
          eqp_incidentp incidentp_eqp by blast
      show "IncidentP PB p" 
        by (metis IncidentP_def \<open>\<not> Col_H PA PB PC\<close> \<open>isPlane p\<close> \<open>p = Plane PA PB PC\<close>
            axiom_plane_existence plane_cop)
      show "IncidentP PC p" 
        using IncidentP_def \<open>isPlane p\<close> \<open>p = Plane PA PB PC\<close> ncop_distincts by blast
    qed
    have "Coplanar A QA QB QC" 
    proof (rule plane_cop [where ?p = "q"])
      show "IncidentP A q" 
        by (simp add: \<open>IncidentP A q\<close>)
      show "IncidentP QA q" 
        using \<open>\<not> Col_H QA QB QC\<close> \<open>q = Plane QA QB QC\<close> axiom_plane_existence 
          eqp_incidentp incidentp_eqp by blast
      show "IncidentP QB q" 
        by (metis IncidentP_def \<open>\<not> Col_H QA QB QC\<close> \<open>isPlane q\<close> \<open>q = Plane QA QB QC\<close>
            axiom_plane_existence plane_cop)
      show "IncidentP QC q" 
        using IncidentP_def \<open>isPlane q\<close> \<open>q = Plane QA QB QC\<close> ncop_distincts by blast
    qed
    have "plane_intersection_axiom" 
      using upper_dim_3 upper_dim_3_axiom_def upper_dim_3_equivalent_axioms by blast
    have "\<exists> B. Coplanar PA PB PC B \<and> Coplanar QA QB QC B \<and> A \<noteq> B"
    proof -
      have "Coplanar PA PB PC A" 
        by (simp add: \<open>Coplanar A PA PB PC\<close> coplanar_perm_9)
      moreover have "Coplanar QA QB QC A" 
        using \<open>Coplanar A QA QB QC\<close> coplanar_perm_9 by blast
      ultimately show ?thesis
        using \<open>plane_intersection_axiom\<close> plane_intersection_axiom_def by blast
    qed
    hence "\<exists> B. IncidentP B p \<and> IncidentP B q \<and> A \<noteq> B" 
      using IncidentP_def \<open>isPlane p\<close> \<open>isPlane q\<close> \<open>p = Plane PA PB PC\<close> \<open>q = Plane QA QB QC\<close> 
        coplanar_perm_18 by blast
  }
  thus "\<And>p q A. isPlane p \<and> isPlane q \<and> IncidentP A p \<and> IncidentP A q \<longrightarrow> 
  (\<exists>B. IncidentP B p \<and> IncidentP B q \<and> A \<noteq> B)" 
    by blast
  show "\<nexists>p. isPlane p \<and> IncidentP TS1 p \<and> IncidentP TS2 p \<and> IncidentP TS3 p \<and> IncidentP TS4 p" 
    using lower_dim_3' by blast
qed

end
end