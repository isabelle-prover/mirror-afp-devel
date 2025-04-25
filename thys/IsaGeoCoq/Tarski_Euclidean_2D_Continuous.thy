(* IsaGeoCoq - Tarski_Euclidean_2D_Continuous.thy

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


section "Tarski Euclidean 2D Continuous"

theory Tarski_Euclidean_2D_Continuous

imports
  Tarski_Euclidean_2D
  Tarski_Neutral_Continuous
begin

locale Tarski_Euclidean_2D_Continuous = Tarski_Euclidean_2D + Tarski_Neutral_Continuous

end
