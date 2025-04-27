(* IsageoCoq - Gupta_Neutral_2D.thy
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

theory Gupta_Neutral_2D

imports
  Gupta_Neutral
   
begin

section "Gupta 2D"

subsection "Axioms Gupta 2D"

locale Gupta_neutral_2D = Gupta_neutral_dimensionless GPA GPB GPC BetG CongG
  for GPA GPB GPC :: 'p 
  and BetG  :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  and CongG :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" +
  assumes upper_dimG: "\<forall> a b c p q.
                      p \<noteq> q \<and>
a \<noteq> b \<and>
a \<noteq> c \<and>
c \<noteq> b \<and>
                      CongG a p a q \<and>
                      CongG b p b q \<and>
                      CongG c p c q
                      \<longrightarrow>
                      (BetG a b c \<or> BetG b c a \<or> BetG c a b)"

context Gupta_neutral_2D

begin

subsection "Definitions"

subsection "Propositions"

lemma upper_dimT :
  assumes "P \<noteq> Q" and
    "CongG A P A Q" and
    "CongG B P B Q" and
    "CongG C P C Q" 
  shows "BetG A B C \<or> BetG B C A \<or> BetG C A B"
  by (metis Gupta_neutral_2D.upper_dimG Gupta_neutral_2D_axioms assms(1,2,3,4) g2_6) 

end

end
