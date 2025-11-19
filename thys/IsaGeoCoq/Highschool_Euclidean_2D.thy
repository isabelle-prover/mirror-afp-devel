(* IsaGeoCoq - Highschool_Euclidean_2D.thy

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

theory Highschool_Euclidean_2D

imports 
  Highschool_Euclidean
  Tarski_Euclidean_2D

begin

section "Highschool Euclidean 2D"

context Tarski_Euclidean_2D

begin

subsection "Definitions"

subsection "Propositions"

lemma NewEX1:
  assumes "Square A B C D" and
    "Cong K A K C" and 
    "Cong K A A C"
  shows "Col B K D" 
proof -
  obtain M where "M Midpoint A C" 
    using MidR_uniq_aux by blast
  have "Cong B A B C" 
    using Cong_cases Square_def assms(1) by auto
  hence "Per A M B" 
    using Per_def \<open>M Midpoint A C\<close> l8_2 by blast
  hence "A M Perp M B" 
    by (metis Square_def Square_not_triv_3 \<open>M Midpoint A C\<close> assms(1) 
        cong_diff_2 is_midpoint_id l8_7 midpoint_thales_reci per_perp rect_per)
  have "Cong D A D C" 
    using Square_def assms(1) 
    by (meson Square_Rhombus cong_inner_transitivity not_cong_4312 rmb_cong)
  hence "Per A M D" 
    using Per_def Per_perm \<open>M Midpoint A C\<close> cong_left_commutativity by blast
  hence "A M Perp M D" 
    by (metis Cong_cases Square_def \<open>A M Perp M B\<close> \<open>M Midpoint A C\<close>
        assms(1) between_cong between_trivial2 midpoint_cong 
        midpoint_thales_reci_2 per_perp rect_per)
  moreover
  have "Per A M K"
    using Per_def \<open>M Midpoint A C\<close> assms(2) l8_2 by blast
  hence "A M Perp M K"
     by (metis \<open>A M Perp M B\<close> \<open>M Midpoint A C\<close> assms(3) 
        between_cong midpoint_bet midpoint_distinct_2 
        not_cong_2134 per_perp perp_distinct)
  ultimately
  show ?thesis 
    by (metis Col_def \<open>Cong B A B C\<close> \<open>Cong D A D C\<close> assms(2) assms(3) 
        cong_diff perp2__col perp_not_col upper_dim)
qed

end
end