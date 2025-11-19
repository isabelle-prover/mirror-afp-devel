(* IsaGeoCoq - Tarski_Non_Euclidean_Archimedean.thy

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



theory Tarski_Non_Euclidean_Archimedean

imports
  Tarski_Non_Euclidean_Aristotle

begin

section "Tarski Non Euclidean"

subsection "Definitions"

locale Tarski_Non_Euclidean_Archimedean = Tarski_Non_Euclidean_Aristotle +
  assumes archimedes: "archimedes_axiom"

context Tarski_Non_Euclidean_Archimedean

begin

subsection "Propositions"

lemma NPost04:
  shows "\<not> Postulate04" 
  using NPost03 Thm10 archimedes by blast

lemma NPost31:
  shows "\<not> Postulate31" 
  by (simp add: NPost04 P31_P04)

lemma NPost32:
  shows "\<not> Postulate32" 
  using NPost31 P31_P32 by blast

lemma NPost33:
  shows "\<not> Postulate33"  
  using NPost04 P04_P33 by auto

lemma NPost34:
  shows "\<not> Postulate34"  
  using NPost01 Thm10 archimedes by blast

lemma NPost35:
  shows "\<not> Postulate35"  
  using NPost01 Thm10_4 archimedes by blast

theorem not_bachmann_s_lotschnittaxiom:
  shows "\<exists> P Q R P1 R1. P \<noteq> Q \<and> Q \<noteq> R \<and> Per P Q R \<and> Per Q P P1 \<and> Per Q R R1 \<and> 
                        Coplanar P Q R P1 \<and> Coplanar P Q R R1 \<and> 
                        (\<forall> S. \<not> Col P P1 S \<or> \<not> Col R R1 S)"
  using NPost04 Postulate04_def bachmann_s_lotschnittaxiom_def by blast

theorem not_weak_inverse_projection_postulate:
  shows "\<exists> A B C D E F P Q Y. Acute A B C \<and> Per D E F \<and> A B C A B C SumA D E F \<and> 
                            B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q \<and> 
                            (\<not> B Out C Y \<or> \<not> Col P Q Y)" 
  using NPost31 Postulate31_def weak_inverse_projection_postulate_def by blast

theorem not_weak_tarski_s_parallel_postulate:
  shows "\<exists> A B C T. Per A B C \<and> T InAngle A B C \<and> 
                    (\<forall> X Y. \<not> B Out A X \<or> \<not> B Out C Y \<or> \<not> Bet X T Y)"
  using NPost32 Postulate32_def weak_tarski_s_parallel_postulate_def by blast 

theorem not_weak_triangle_circumscription_principle:
  shows "\<exists> A B C A1 A2 B1 B2. \<not> Col A B C \<and> Per A C B \<and> A1 A2 PerpBisect B C \<and> 
                              B1 B2 PerpBisect A C \<and> Coplanar A B C A1 \<and> Coplanar A B C A2 \<and> 
                              Coplanar A B C B1 \<and> Coplanar A B C B2 \<and> 
                              (\<forall> I. \<not> Col A1 A2 I \<or> \<not> Col B1 B2 I)"
  using NPost33 Postulate33_def weak_triangle_circumscription_principle_def by blast

theorem not_legendre_s_parallel_postulate:
  fixes A B C
  assumes "\<not> Col A B C"
    and "Acute A B C"
  shows "\<exists> T. T InAngle A B C \<and> (\<forall> X Y. \<not> B Out A X \<or> \<not> B Out C Y \<or> \<not> Bet X T Y)"
  using assms(1,2) NPost34 Postulate34_def legendre_s_parallel_postulate_def by blast

theorem not_existential_playfair_s_postulate:
  assumes "\<not> Col A1 A2 P"
  shows "\<exists> B1 B2 C1 C2. A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<and> 
                        (\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2)"
  using assms NPost35 Postulate35_def existential_playfair_s_postulate_def by blast 

end
end

