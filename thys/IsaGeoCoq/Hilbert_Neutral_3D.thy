(* IsageoCoq - Hilbert_Neutral_3D.thy
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

theory Hilbert_Neutral_3D

imports Hilbert_Neutral

begin

section "Hilbert - Geometry - Neutral 3D"

subsection "Axioms: neutral 3D"

locale Hilbert_neutral_3D = Hilbert_neutral_dimensionless IncidL IncidP EqL EqP IsL IsP BetH CongH CongaH
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
  fixes HS1 HS2 HS3 HS4 :: 'p
  assumes plane_intersection: 
    "IsP p \<and> IsP q \<and> IncidP A p \<and> IncidP A q 
        \<longrightarrow> 
     (\<exists> B. IncidP B p \<and> IncidP B q \<and> A \<noteq> B)" 
    and   lower_dim_3: 
    "\<not> (\<exists> p. IsP p \<and> IncidP HS1 p \<and> IncidP HS2 p \<and> IncidP HS3 p \<and> IncidP HS4 p)"

end