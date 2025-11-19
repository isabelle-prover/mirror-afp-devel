(* IsaGeoCoq - Tarski_Neutral_Continuous.thy

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

theory Tarski_Neutral_Continuous

imports
  Tarski_Neutral_Continuity

begin

section "Tarski Neutral Continuous"

subsection "Tarski's axiom system for Neutral Continuous"

locale Tarski_Neutral_Continuous = Tarski_neutral_dimensionless +
  assumes continuity : "\<forall> Alpha Beta.
  (\<exists> A. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet A X Y) \<longrightarrow>
  (\<exists> B. \<forall> X Y. (Alpha X \<and> Beta Y) \<longrightarrow> Bet X B Y)"

context Tarski_Neutral_Continuous

begin

subsection "Definitions"

subsection "Propositions"

theorem continuity_DedekindAxiom :
  shows "DedekindsAxiom"
  using DedekindsAxiom_def continuity by blast 

end
end