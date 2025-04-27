(* IsageoCoq - Hilbert_Neutral.thy
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

theory Hilbert_Neutral

imports
  Tarski_Neutral

begin

section "Hilbert - Geometry - neutral dimension less"

subsection "Axioms"

locale Hilbert_neutral_dimensionless_pre =
  fixes
    IncidL :: "'p \<Rightarrow> 'b \<Rightarrow> bool" and
    IncidP :: "'p \<Rightarrow> 'c \<Rightarrow> bool" and
    EqL ::"'b \<Rightarrow> 'b \<Rightarrow> bool" and
    EqP ::"'c \<Rightarrow> 'c \<Rightarrow> bool" and
    IsL ::"'b \<Rightarrow> bool" and
    IsP ::"'c \<Rightarrow> bool" and
    BetH ::"'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" and
    CongH::"'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" and
    CongaH::"'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" 

context Hilbert_neutral_dimensionless_pre

begin

subsection "Definitions"

definition ColH :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow>bool" 
  where
    "ColH A B C \<equiv> (\<exists> l. IsL l \<and> IncidL A l \<and> IncidL B l \<and> IncidL C l)"

definition IncidLP :: "'b\<Rightarrow>'c\<Rightarrow>bool" where
  "IncidLP l p \<equiv> IsL l \<and> IsP p \<and> (\<forall> A. IncidL A l \<longrightarrow> IncidP A p)"

definition cut :: "'b\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" where
  "cut l A B \<equiv> IsL l \<and> \<not> IncidL A l \<and> \<not> IncidL B l \<and> (\<exists> I. IncidL I l \<and> BetH A I B)"

definition outH :: "'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" where
  "outH P A B \<equiv> BetH P A B \<or> BetH P B A \<or> (P \<noteq> A \<and> A = B)" 

definition disjoint :: 
  "'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" where
  "disjoint A B C D \<equiv> \<not> (\<exists> P. BetH A P B \<and> BetH C P D)" 

definition same_side :: "'p\<Rightarrow>'p\<Rightarrow>'b\<Rightarrow>bool" where
  "same_side A B l \<equiv> IsL l \<and> (\<exists> P. cut l A P \<and> cut l B P)" 

definition same_side' :: 
  "'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>'p\<Rightarrow>bool" where
  "same_side' A B X Y \<equiv>
     X \<noteq> Y \<and>
     (\<forall> l::'b. (IsL l \<and> IncidL X l \<and> IncidL Y l) \<longrightarrow> same_side A B l)" 

definition Para :: "'b \<Rightarrow> 'b \<Rightarrow>bool" where
  "Para l m \<equiv> IsL l \<and> IsL m \<and> 
              (\<not>(\<exists> X. IncidL X l \<and> IncidL X m)) \<and> (\<exists> p. IncidLP l p \<and> IncidLP m p)"

end

locale Hilbert_neutral_dimensionless =  Hilbert_neutral_dimensionless_pre IncidL IncidP EqL EqP IsL IsP BetH CongH CongaH
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
  fixes  PP PQ PR :: 'p
  assumes 
    EqL_refl: "IsL l \<longrightarrow> EqL l l" and
    EqL_sym: "IsL l1 \<and> IsL l2 \<and> EqL l1 l2 \<longrightarrow> EqL l2 l1" and
    EqL_trans: "(EqL l1 l2 \<and> EqL l2 l3) \<longrightarrow> EqL l1 l3" and
    EqP_refl: "IsP p \<longrightarrow> EqP p p" and
    EqP_sym: "EqP p1 p2 \<longrightarrow> EqP p2 p1" and
    EqP_trans: "(EqP p1 p2 \<and> EqP p2 p3) \<longrightarrow> EqP p1 p3" and
    IncidL_morphism: "(IsL l \<and> IsL m \<and>  IncidL P l \<and> EqL l m) \<longrightarrow> IncidL P m" and
    IncidP_morphism: "(IsP p \<and> IsP q \<and> IncidP M p \<and> EqP p q) \<longrightarrow> IncidP M q" and
    Is_line:"IncidL P l \<longrightarrow> IsL l" and
    Is_plane:"IncidP P p \<longrightarrow> IsP p" 
  assumes
    (** Group I Incidence *)
    line_existence: "A \<noteq> B \<longrightarrow> (\<exists> l. IsL l \<and> ( IncidL A l \<and> IncidL B l))" and
    line_uniqueness: "A \<noteq> B \<and> IsL l \<and> IsL m \<and>
     IncidL A l \<and> IncidL B l \<and> IncidL A m \<and> IncidL B m \<longrightarrow>
     EqL l m" and
    two_points_on_line: "\<forall> l. IsL l \<longrightarrow> (\<exists> A B. IncidL A l \<and> IncidL B l \<and> A \<noteq> B)" 
  assumes 
    lower_dim_2: "PP \<noteq> PQ \<and> PQ \<noteq> PR \<and> PP \<noteq> PR \<and> \<not> ColH PP PQ PR" and
    (*lower_dim_2: "\<exists> PP PQ PR. PP \<noteq> PQ \<and> PQ \<noteq> PR \<and> PP \<noteq> PR \<and> \<not> ColH PP PQ PR" and*)
    plan_existence: "\<forall> A B C. ((\<not> ColH A B C) \<longrightarrow> 
                               (\<exists> p. IsP p \<and> IncidP A p \<and> IncidP B p \<and> IncidP C p))" and
    one_point_on_plane: "\<forall> p. \<exists> A. IsP p \<longrightarrow> IncidP A p" and
    plane_uniqueness: "\<not> ColH A B C \<and> IsP p \<and> IsP q \<and>
     IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidP A q \<and> IncidP B q \<and> IncidP C q \<longrightarrow>
     EqP p q"  and
    line_on_plane: "\<forall> A B l p. A \<noteq> B \<and> IsL l \<and> IsP p \<and>
     IncidL A l \<and> IncidL B l \<and> IncidP A p \<and> IncidP B p \<longrightarrow> IncidLP l p"
  assumes 
    between_diff: "BetH A B C \<longrightarrow> A \<noteq> C" and
    between_col: "BetH A B C \<longrightarrow> ColH A B C" and
    between_comm: "BetH A B C \<longrightarrow> BetH C B A" and
    between_out: " A \<noteq> B \<longrightarrow> (\<exists> C. BetH A B C)" and
    between_only_one: "BetH A B C \<longrightarrow> \<not> BetH B C A" and
    pasch: "\<not> ColH A B C \<and> IsL l \<and> IsP p \<and>
     IncidP A p \<and> IncidP B p \<and> IncidP C p \<and> IncidLP l p \<and> \<not> IncidL C l \<and>
 (cut l A B)
\<longrightarrow>
     (cut l A C) \<or> (cut l B C)"
  assumes
    cong_permr: "CongH A B C D \<longrightarrow> CongH A B D C" and
    cong_existence: "\<And>A B A' P::'p. A \<noteq> B \<and> A' \<noteq> P \<and> IsL l \<and>
     IncidL A' l \<and> IncidL P l \<longrightarrow>
     (\<exists> B'. (IncidL B' l \<and> outH A' P B' \<and> CongH A' B' A B))" and
    cong_pseudo_transitivity:
    " CongH A B C D \<and> CongH A B E F \<longrightarrow> CongH C D E F" and
    addition : "
     ColH A B C \<and> ColH A' B' C' \<and>
     disjoint A B B C \<and> disjoint A' B' B' C' \<and>
     CongH A B A' B' \<and> CongH B C B' C' \<longrightarrow>
     CongH A C A' C'" and
    conga_refl: "\<not> ColH A B C \<longrightarrow> CongaH A B C A B C" and
    conga_comm : "\<not> ColH A B C \<longrightarrow> CongaH A B C C B A" and
    conga_permlr: "CongaH A B C D E F \<longrightarrow> CongaH C B A F E D" and
    conga_out_conga: "(CongaH A B C D E F \<and>
    outH B A A' \<and> outH B C C' \<and> outH E D D' \<and> outH E F F') \<longrightarrow>
    CongaH A' B C' D' E F'" and
    cong_4_existence: 
    " \<not> ColH P PO X \<and> \<not> ColH A B C \<longrightarrow>
            (\<exists> Y. (CongaH A B C X PO Y \<and> same_side' P Y PO X))" and
    cong_4_uniqueness:
    "\<not> ColH P PO X \<and> \<not> ColH A B C \<and>
     CongaH A B C X PO Y \<and> CongaH A B C X PO Y' \<and>
     same_side' P Y PO X \<and> same_side' P Y' PO X \<longrightarrow>
     outH PO Y Y'" and
    cong_5 : "\<not> ColH A B C \<and> \<not> ColH A' B' C' \<and>
     CongH A B A' B' \<and> CongH A C A' C' \<and>
     CongaH B A C B' A' C' \<longrightarrow>
     CongaH A B C A' B' C'"

subsection "Propositions"

end