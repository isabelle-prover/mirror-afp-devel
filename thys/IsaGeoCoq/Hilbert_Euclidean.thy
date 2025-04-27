(* IsageoCoq - Hilbert_Euclidean.thy
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

theory Hilbert_Euclidean

imports 
  Hilbert_Neutral
  Tarski_Euclidean
  Tarski_Neutral_Hilbert

begin

section "Hilbert - Geometry - Euclidean"

subsection "Axioms: Euclidean"

locale Hilbert_Euclidean = Hilbert_neutral_dimensionless  IncidL IncidP EqL EqP IsL IsP BetH CongH CongaH
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
  assumes euclid_uniqueness: "\<forall> l P m1 m2. IsL l \<and> IsL m1 \<and> IsL m2 \<and>
     \<not> IncidL P l \<and> Para l m1 \<and> IncidL P m1 \<and> Para l m2 \<and> IncidL P m2 
        \<longrightarrow>
     EqL m1 m2"

context Tarski_Euclidean

begin

subsection "Definitions"

subsection "Propositions"

lemma Para_Par:
  assumes "A \<noteq> B" and 
    "C \<noteq> D" and
    "Para_H (Line A B) (Line C D)"
  shows "A B Par C D" 
proof -
  have "isLine (Line A B)" 
    using assms(3) Para_H_def by blast
  have "isLine (Line C D)" 
    using assms(3) Para_H_def by blast
  have 1: "(\<not>(\<exists> X. IncidentL X (Line A B) \<and> IncidentL X (Line C D))) \<and> 
(\<exists> p. IncidentLP (Line A B) p \<and> IncidentLP (Line C D) p)"
    using assms(3) Para_H_def by blast
  then obtain p where "IncidentLP (Line A B) p" and "IncidentLP (Line C D) p" 
    by blast
  have "Coplanar A B C D" 
  proof -
    have "IncidentP A p" 
      using IncidentLP_def \<open>IncidentLP (Line A B) p\<close> assms(1) axiom_line_existence 
        eq_incident incident_eq by blast
    moreover have "IncidentP B p" 
      using IncidentLP_def \<open>IncidentLP (Line A B) p\<close> assms(1) axiom_line_existence 
        eq_incident incident_eq by blast
    moreover have "IncidentP C p" 
      using IncidentLP_def \<open>IncidentLP (Line C D) p\<close> assms(2) axiom_line_existence 
        eq_incident incident_eq by blast
    moreover have "IncidentP D p" 
      using IncidentLP_def \<open>IncidentLP (Line C D) p\<close> assms(2) axiom_line_existence 
        eq_incident incident_eq by blast
    ultimately show ?thesis
      by (simp add: plane_cop)
  qed
  moreover
  {
    assume "\<exists> X. Col X A B \<and> Col X C D"
    then obtain X where "Col X A B" and "Col X C D" 
      by blast
    hence "Col_H X A B"  
      by (simp add: cols_coincide_2)
    hence "IncidentL X (Line A B)" 
      using assms(1) IncidentL_def Col_H_def by (meson EqTL_def incident_eq)
    moreover
    have "Col_H X C D" 
      using cols_coincide_2 by (simp add: \<open>Col X C D\<close>)
    hence "IncidentL X (Line C D)" 
      using assms(2) IncidentL_def Col_H_def eq_incident incident_eq by blast
    ultimately have False 
      using 1 by blast
  }
  hence "\<not> (\<exists> X. Col X A B \<and> Col X C D)" 
    by blast
  ultimately show ?thesis 
    using Par_def by (meson cop_npar__inter_exists) 
qed

lemma axiom_euclid_uniqueness:
  assumes "\<not> IncidentL P l" and
    "Para_H l m1" and
    "IncidentL P m1" and
    "Para_H l m2" and
    "IncidentL P m2"
  shows "m1 =l= m2" 
proof -
  let ?A = "fst l"
  let ?B = "snd l"
  let ?C = "fst m1"
  let ?D = "snd m1"
  let ?C' = "fst m2"
  let ?D' = "snd m2"
  have "l = Line ?A ?B" 
    using Line_def Para_H_def assms(4) isLine_def by auto
  have "m1 = Line ?C ?D" 
    using Line_def Para_H_def assms(2) isLine_def by auto
  have "m2 = Line ?C' ?D'" 
    using Line_def Para_H_def assms(4) isLine_def by auto
  have "\<not> Col P ?A ?B" 
    using IncidentL_def Para_H_def assms(1) assms(4) by blast
  have "Para_H (Line ?A ?B) (Line ?C ?D)" 
    using assms(2) \<open>l = Line (fst l) (snd l)\<close> \<open>m1 = Line (fst m1) (snd m1)\<close> by force
  have "Para_H (Line ?A ?B) (Line ?C' ?D')" 
    using \<open>l = Line (fst l) (snd l)\<close> \<open>m2 = Line (fst m2) (snd m2)\<close> assms(4) by fastforce
  have "?A ?B Par ?C ?D" using Para_Par 
    using IncidentL_def \<open>Para_H (Line (fst l) (snd l)) (Line (fst m1) (snd m1))\<close> 
      \<open>\<not> Col P (fst l) (snd l)\<close> assms(3) isLine_def not_col_distincts by auto
  have "Col P ?C ?D"
    using IncidentL_def assms(3) by auto 
  have "?A ?B Par ?C' ?D'" 
    using IncidentL_def Para_Par \<open>Para_H (Line (fst l) (snd l)) (Line (fst m2) (snd m2))\<close> 
      \<open>(fst l) (snd l) Par (fst m1) (snd m1)\<close> assms(5) 
      isLine_def par_distinct by blast
  have "Col P ?C' ?D'" 
    by (simp add: assms(5) incident_col)
  have "Col ?C' ?C ?D" 
    using \<open>Col P (fst m1) (snd m1)\<close> \<open>Col P (fst m2) (snd m2)\<close> 
      \<open>(fst l) (snd l) Par (fst m1) (snd m1)\<close> 
      \<open>(fst l) (snd l) Par (fst m2) (snd m2)\<close> parallel_uniqueness by blast
  moreover
  have "Col ?D' ?C ?D" 
    using \<open>Col P (fst m1) (snd m1)\<close> \<open>Col P (fst m2) (snd m2)\<close> 
      \<open>(fst l) (snd l) Par (fst m1) (snd m1)\<close> 
      \<open>(fst l) (snd l) Par (fst m2) (snd m2)\<close> parallel_uniqueness by blast
  ultimately show ?thesis
    using tarski_s_euclid_implies_playfair_s_postulate
    by (metis IncidentL_def \<open>(fst l) (snd l) Par (fst m2) (snd m2)\<close> 
        \<open>m2 = Line (fst m2) (snd m2)\<close> assms(3) eq_symmetry incident_eq par_distincts)
qed

end
end