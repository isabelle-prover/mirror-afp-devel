(* IsageoCoq - Gupta_Euclidean.thy
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

theory Gupta_Euclidean

imports
  Gupta_Neutral

begin
 
section "Gupta Euclidean"

subsection "Axioms Gupta Euclidean"

locale Gupta_Euclidean = Gupta_neutral_dimensionless GPA GPB GPC BetG CongG
  for GPA GPB GPC :: 'p 
  and BetG  :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  and CongG :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" +
  assumes euclidG: "\<forall> A B C D T.
   BetG A D T \<and> BetG B D C \<and> B \<noteq> D \<and> D \<noteq> C \<and>
   \<not> (BetG A B C \<or> BetG B C A \<or> BetG C A B) \<longrightarrow>
   (\<exists> x y. BetG A B x \<and> BetG A C y \<and> BetG x T y)"

subsection "Definitions"

subsection "Propositions"

end
