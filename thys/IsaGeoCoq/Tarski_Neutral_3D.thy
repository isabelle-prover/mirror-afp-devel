(* IsaGeoCoq - Tarski_Neutral_3D

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

theory Tarski_Neutral_3D

imports
  Tarski_Neutral

begin

section "Tarski's axiom system for neutral geometry: 3D"

subsection "Definitions"

locale Tarski_neutral_3D = Tarski_neutral_dimensionless +
  fixes TS1 and TS2 and TS3 and TS4 
  assumes lower_dim_3: "\<not> (\<exists> X.
   ((Bet TS1 TS2 X \<or> Bet TS2 X TS1 \<or> Bet X TS1 TS2) \<and> 
         (Bet TS3 TS4 X \<or> Bet TS4 X TS3 \<or> Bet X TS3 TS4) \<or>
   (Bet TS1 TS3 X \<or> Bet TS3 X TS1 \<or> Bet X TS1 TS3) \<and> 
         (Bet TS2 TS4 X \<or> Bet TS4 X TS2 \<or> Bet X TS2 TS4) \<or>
   (Bet TS1 TS4 X \<or> Bet TS4 X TS1 \<or> Bet X TS1 TS4) \<and> 
         (Bet TS2 TS3 X \<or> Bet TS3 X TS2 \<or> Bet X TS2 TS3)))"
  assumes upper_dim_3: "\<forall> A B C P Q R.
   P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and>
   Cong A P A Q \<and> Cong B P B Q \<and> Cong C P C Q \<and>
   Cong A P A R \<and> Cong B P B R \<and> Cong C P C R \<longrightarrow>
   (Bet A B C \<or> Bet B C A \<or> Bet C A B)"

subsection "Propositions"

end
