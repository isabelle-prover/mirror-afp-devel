(* IsageoCoq - Tarski_Neutral_3D_Hilbert.thy
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

theory Tarski_Neutral_3D_Hilbert

imports 
  Tarski_Neutral_Hilbert
  Tarski_Neutral_3D

begin

section "Tarski neutral dimensionless - Hilbert"

context Tarski_neutral_3D

begin

subsection "Definition"

subsection "Propositions"

lemma lower_dim_3':
  shows "\<not> (\<exists> p. isPlane p \<and> IncidentP TS1 p \<and> IncidentP TS2 p \<and> 
                              IncidentP TS3 p \<and> IncidentP TS4 p)" 
proof -
  {
    assume "\<exists> p. isPlane p \<and> IncidentP TS1 p \<and> IncidentP TS2 p \<and> 
                             IncidentP TS3 p \<and> IncidentP TS4 p"
    then obtain p where "isPlane p" and "IncidentP TS1 p" and "IncidentP TS2 p" and
      "IncidentP TS3 p \<and> IncidentP TS4 p"
      by blast
    hence "Coplanar TS1 TS2 TS3 TS4" 
      using plane_cop by blast
    hence False using not_coplanar_S1_S2_S3_S4 by simp
  }
  thus ?thesis 
    by blast
qed

end
end