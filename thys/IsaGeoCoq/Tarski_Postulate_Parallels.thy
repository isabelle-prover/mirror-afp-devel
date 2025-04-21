(* IsaGeoCoq - Tarski_Postulate_Parallels

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

theory Tarski_Postulate_Parallels

imports
  Tarski_Neutral_Archimedes

begin

context Tarski_neutral_dimensionless

begin

section "Parallel's Postulate"

subsection "Definitions"

definition tarski_s_parallel_postulate ::
  "bool"
  ("TarskiSParallelPostulate")
  where
    "tarski_s_parallel_postulate \<equiv> 

     \<forall> A B C D T.
     Bet A D T \<and> Bet B D C \<and> A \<noteq> D 
\<longrightarrow>
     (\<exists> X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y)"

definition euclid_5 ::
  "bool" ("Euclid5")
  where
    "euclid_5 \<equiv> 

     \<forall> P Q R S T U.
     BetS P T Q \<and> BetS R T S \<and> BetS Q U R \<and> \<not> Col P Q S \<and> Cong P T Q T \<and> Cong R T S T
\<longrightarrow>
     (\<exists> I. BetS S Q I \<and> BetS P U I)"

definition euclid_s_parallel_postulate ::
  "bool" ("EuclidSParallelPostulate")
  where
    "euclid_s_parallel_postulate \<equiv> 

     \<forall> A B C D P Q R.
     B C OS A D \<and> SAMS A B C B C D \<and> A B C B C D SumA P Q R \<and> \<not> Bet P Q R 
\<longrightarrow>
     (\<exists> Y. B Out A Y \<and> C Out D Y)"

definition playfair_s_postulate ::
  "bool"
  ("PlayfairSPostulate")
  where
    "playfair_s_postulate \<equiv> 

     \<forall> A1 A2 B1 B2 C1 C2 P.
     A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 
\<longrightarrow>
     Col C1 B1 B2 \<and> Col C2 B1 B2"

definition decidability_of_intersection ::
  "bool"
  ("DecidabilityIntersection")
  where
    "decidability_of_intersection \<equiv> 

    \<forall> A B C D.
    
    (\<exists> I. Col I A B \<and> Col I C D) \<or> \<not> (\<exists> I. Col I A B \<and> Col I C D)"

definition alternate_interior_angles_postulate ::
  "bool"
  ("AlternateInteriorAnglesPostulate")
  where
    "alternate_interior_angles_postulate \<equiv> 

     \<forall> A B C D.
     A C TS B D \<and> A B Par C D 
\<longrightarrow> 
     B A C CongA D C A"

definition consecutive_interior_angles_postulate ::
  "bool"
  ("ConsecutiveInteriorAnglesPostulate")
  where
    "consecutive_interior_angles_postulate \<equiv> 

     \<forall> A B C D.
     B C OS A D \<and> A B Par C D 
\<longrightarrow> 
     A B C SuppA B C D"

definition alternative_playfair_s_postulate ::
  "bool"
  ("AlternativePlayfairSPostulate")
  where
    "alternative_playfair_s_postulate \<equiv> 

     \<forall> A1 A2 B1 B2 C1 C2 P.
     P Perp2 A1 A2 B1 B2 \<and> \<not> Col A1 A2 P \<and> Col P B1 B2 \<and> 
     Coplanar A1 A2 B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2
\<longrightarrow>
     Col C1 B1 B2 \<and> Col C2 B1 B2"

definition proclus_postulate ::
  "bool"
  ("ProclusPostulate")
  where
    "proclus_postulate \<equiv> 

     \<forall> A B C D P Q.
     A B Par C D \<and> Col A B P \<and> \<not> Col A B Q \<and> Coplanar C D P Q 
\<longrightarrow>
     (\<exists> Y. Col P Q Y \<and> Col C D Y)"

definition triangle_postulate ::
  "bool"
  ("TrianglePostulate")
  where
    "triangle_postulate \<equiv> 

     \<forall> A B C D E F.
     A B C TriSumA D E F
\<longrightarrow> 
     Bet D E F"

definition bachmann_s_lotschnittaxiom ::
  "bool"
  ("BachmannsLotschnittaxiom")
  where
    "bachmann_s_lotschnittaxiom \<equiv> 

     \<forall> P Q R P1 R1.
     P \<noteq> Q \<and> Q \<noteq> R \<and> Per P Q R \<and> Per Q P P1 \<and> Per Q R R1 \<and> 
     Coplanar P Q R P1 \<and> Coplanar P Q R R1
\<longrightarrow> 
     (\<exists> S. Col P P1 S \<and> Col R R1 S)"

definition legendre_s_parallel_postulate ::
  "bool"
  ("LegendresParallelPostulate")
  where
    "legendre_s_parallel_postulate \<equiv>

    \<exists> A B C.

    \<not> Col A B C \<and> 
    Acute A B C \<and>
    (\<forall> T. T InAngle A B C \<longrightarrow> (\<exists> X Y. B Out A X \<and> B Out C Y \<and> Bet X T Y))"

definition weak_inverse_projection_postulate ::
  "bool"
  ("WeakInverseProjectionPostulate")
  where
    "weak_inverse_projection_postulate \<equiv> 

    \<forall> A B C D E F P Q.
    Acute A B C \<and> Per D E F \<and> A B C A B C SumA D E F \<and> 
    B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q
\<longrightarrow>
    (\<exists> Y. B Out C Y \<and> Col P Q Y)"

definition weak_triangle_circumscription_principle ::
  "bool"
  ("WeakTriangleCircumscriptionPrinciple")
  where
    "weak_triangle_circumscription_principle \<equiv> 

     \<forall> A B C A1 A2 B1 B2.
     \<not> Col A B C \<and> Per A C B \<and> A1 A2 PerpBisect B C \<and> 
     B1 B2 PerpBisect A C \<and> Coplanar A B C A1 \<and> Coplanar A B C A2 \<and> 
     Coplanar A B C B1 \<and> Coplanar A B C B2
\<longrightarrow>
     (\<exists> I. Col A1 A2 I \<and> Col B1 B2 I)"

definition weak_tarski_s_parallel_postulate ::
  "bool"
  ("WeakTarskiParallelPostulate")
  where
    "weak_tarski_s_parallel_postulate \<equiv> 

     \<forall> A B C T.
     Per A B C \<and> T InAngle A B C 
\<longrightarrow>
     (\<exists> X Y. B Out A X \<and> B Out C Y \<and> Bet X T Y)"

definition existential_playfair_s_postulate ::
  "bool"
  ("ExistentialPlayfairPostulate")
  where
    "existential_playfair_s_postulate \<equiv>
  
    \<exists> A1 A2 P. 

    \<not> Col A1 A2 P \<and>

    (\<forall> B1 B2 C1 C2. 
            A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 
       \<longrightarrow>
            (Col C1 B1 B2 \<and> Col C2 B1 B2))"

definition postulate_of_right_saccheri_quadrilaterals ::
  "bool"
  ("PostulateRightSaccheriQuadrilaterals")
  where
    "postulate_of_right_saccheri_quadrilaterals \<equiv> 

    \<forall> A B C D.
    Saccheri A B C D
\<longrightarrow> 
    Per A B C"

definition postulate_of_existence_of_a_right_saccheri_quadrilateral ::
  "bool"
  ("PostulateExistenceRightSaccheriQuadrilateral")
  where
    "postulate_of_existence_of_a_right_saccheri_quadrilateral \<equiv>
  
    \<exists> A B C D. 

    Saccheri A B C D \<and> Per A B C"

definition postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights ::
  "bool"
  ("PostulateExistenceTriangleAnglesSumTwoRights")
  where
    "postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights \<equiv>
  
     \<exists> A B C D E F. 

     \<not> Col A B C \<and> A B C TriSumA D E F \<and> Bet D E F"

definition inverse_projection_postulate ::
  "bool"
  ("InverseProjectionPostulate")
  where
    "inverse_projection_postulate \<equiv> 
 
     \<forall> A B C P Q.
     Acute A B C \<and> B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q 
\<longrightarrow>
     (\<exists> Y. B Out C Y \<and> Col P Q Y)"

definition alternative_proclus_postulate ::
  "bool"
  ("AlternativeProclusPostulate")
  where
    "alternative_proclus_postulate \<equiv> 

    \<forall> A B C D P Q.
    P Perp2 A B C D \<and> \<not> Col C D P \<and> Coplanar A B C D \<and> Col A B P \<and> 
    \<not> Col A B Q \<and> Coplanar C D P Q 
\<longrightarrow>
    (\<exists> Y. (Col P Q Y \<and> Col C D Y))"

definition strong_parallel_postulate ::
  "bool"
  ("StrongParallelPostulate")
  where
    "strong_parallel_postulate \<equiv> 

    \<forall> P Q R S T U.
    BetS P T Q \<and> BetS R T S \<and> \<not> Col P R U \<and> Coplanar P Q R U \<and> 
    Cong P T Q T \<and> Cong R T S T
\<longrightarrow>
    (\<exists> I. (Col S Q I \<and> Col P U I))"

definition triangle_circumscription_principle ::
  "bool"
  ("TriangleCircumscriptionPrinciple")
  where
    "triangle_circumscription_principle \<equiv> 

   \<forall> A B C.
   \<not> Col A B C
\<longrightarrow>
   (\<exists> D. Cong A D B D \<and> Cong A D C D \<and> Coplanar A B C D)"

definition thales_converse_postulate::
  "bool"
  ("ThalesConversePostulate") where
  "thales_converse_postulate \<equiv> 

   \<forall> A B C M.
   M Midpoint A B \<and> Per A C B
\<longrightarrow> 
   Cong M A M C"

definition existential_thales_postulate ::
  "bool"
  ("ExistentialThalesPostulate") where
  "existential_thales_postulate \<equiv>
  
   \<exists> A B C M. 

   \<not> Col A B C \<and> M Midpoint A B \<and> Cong M A M C \<and> Per A C B"

definition thales_postulate::
  "bool"
  ("ThalesPostulate") where
  "thales_postulate \<equiv> 

   \<forall> A B C M.
   M Midpoint A B \<and> Cong M A M C
\<longrightarrow> 
   Per A C B"

definition posidonius_postulate ::
  "bool"
  ("PosidoniusPostulate") where
  "posidonius_postulate \<equiv>

   \<exists> A1 A2 B1 B2.

    \<not> Col A1 A2 B1 \<and> B1 \<noteq> B2 \<and> Coplanar A1 A2 B1 B2 \<and>
    (\<forall> A3 A4 B3 B4.
              Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> A1 A2 Perp A3 B3 \<and>
              Col A1 A2 A4 \<and> Col B1 B2 B4 \<and> A1 A2 Perp A4 B4
         \<longrightarrow>
              Cong A3 B3 A4 B4)"

definition postulate_of_right_lambert_quadrilaterals ::
  "bool"
  ("PostulateOfRightLambertQuadrilaterals") where
  "postulate_of_right_lambert_quadrilaterals \<equiv> 

   \<forall> A B C D.
   Lambert A B C D 
\<longrightarrow> 
   Per B C D"

definition postulate_of_existence_of_a_right_lambert_quadrilateral ::
  "bool"
  ("PostulateExistenceRightLambertQuadrilateral") where
  "postulate_of_existence_of_a_right_lambert_quadrilateral \<equiv> 

   \<exists> A B C D. 

   Lambert A B C D \<and> Per B C D"

definition postulate_of_existence_of_similar_triangles ::
  "bool"
  ("PostulateOfExistenceOfSimilarTriangles") where
  "postulate_of_existence_of_similar_triangles \<equiv> 

   \<exists> A B C D E F. 
  
   \<not> Col A B C \<and> \<not> Cong A B D E \<and> A B C CongA D E F \<and> 
   B C A CongA E F D \<and> C A B CongA F D E"

definition midpoint_converse_postulate ::
  "bool"
  ("MidpointConversePostulate") where
  "midpoint_converse_postulate \<equiv> 

   \<forall> A B C P Q.
   \<not> Col A B C \<and> P Midpoint B C \<and> A B Par Q P \<and> Col A C Q
\<longrightarrow>
   Q Midpoint A C"

definition postulate_of_transitivity_of_parallelism::
  "bool"
  ("PostulateOfTransitivityOfParallelism") where
  "postulate_of_transitivity_of_parallelism \<equiv> 

   \<forall> A1 A2 B1 B2 C1 C2.
   A1 A2 Par B1 B2 \<and> B1 B2 Par C1 C2 
\<longrightarrow> 
   A1 A2 Par C1 C2"

definition perpendicular_transversal_postulate ::
  "bool"
  ("PerpendicularTransversalPostulate") where
  "perpendicular_transversal_postulate \<equiv> 

   \<forall> A B C D P Q.
   A B Par C D \<and> A B Perp P Q \<and> Coplanar C D P Q
\<longrightarrow> 
   C D Perp P Q"

definition postulate_of_parallelism_of_perpendicular_transversals ::
  "bool"
  ("PostulateOfParallelismOfPerpendicularTransversals") where
  "postulate_of_parallelism_of_perpendicular_transversals \<equiv> 

   \<forall> A1 A2 B1 B2 C1 C2 D1 D2.
   A1 A2 Par B1 B2 \<and> A1 A2 Perp C1 C2 \<and> B1 B2 Perp D1 D2 \<and>
   Coplanar A1 A2 C1 D1 \<and> Coplanar A1 A2 C1 D2 \<and>
   Coplanar A1 A2 C2 D1 \<and> Coplanar A1 A2 C2 D2
\<longrightarrow> 
   C1 C2 Par D1 D2"

definition universal_posidonius_postulate ::
  "bool"
  ("UniversalPosidoniusPostulate") where
  "universal_posidonius_postulate \<equiv> 

   \<forall> A1 A2 A3 A4 B1 B2 B3 B4.
   A1 A2 Par B1 B2 \<and> Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> A1 A2 Perp A3 B3 \<and>
   Col A1 A2 A4 \<and> Col B1 B2 B4 \<and> A1 A2 Perp A4 B4
\<longrightarrow> 
   Cong A3 B3 A4 B4"

definition alternative_strong_parallel_postulate ::
  "bool"
  ("AlternativeStrongParallelPostulate") where
  "alternative_strong_parallel_postulate \<equiv> 

   \<forall> A B C D P Q R.
   B C OS A D \<and> A B C B C D SumA P Q R \<and> \<not> Bet P Q R
\<longrightarrow>
   (\<exists> Y. Col B A Y \<and> Col C D Y)"

(* (1) tarski_a_paralell_postulate = ? tarski_s_parallel_postulate ? *)
definition Postulate01 :: "bool" where
  "Postulate01 \<equiv> tarski_s_parallel_postulate"

(* (2) playfair_s_postulate *)
definition Postulate02 :: "bool" where
  "Postulate02 \<equiv> playfair_s_postulate"

(* (3) triangle_postulate *)
definition Postulate03 :: "bool" where
  "Postulate03 \<equiv> triangle_postulate"

(* (4) bachmann_s_lotschnittaxiom *)
definition Postulate04 :: "bool" where
  "Postulate04 \<equiv> bachmann_s_lotschnittaxiom"

(* (5) postulate_of_transitivity_of_parallelism *)
definition Postulate05 :: "bool" where 
  "Postulate05 \<equiv> postulate_of_transitivity_of_parallelism"

(* (6) midpoint_converse_postulate *)
definition Postulate06 :: "bool" where 
  "Postulate06 \<equiv> midpoint_converse_postulate"

(* (7) alternate_interior_angles_postulate *)
definition Postulate07 :: "bool" where 
  "Postulate07 \<equiv> alternate_interior_angles_postulate"

(* (8) consecutive_interior_angles_postulate *)
definition Postulate08 :: "bool" where 
  "Postulate08 \<equiv> consecutive_interior_angles_postulate"

(* (9) perpendicular_transversal_postulate *)
definition Postulate09 :: "bool" where 
  "Postulate09 \<equiv> perpendicular_transversal_postulate"

(* (10) postulate_of_parallelism_of_perpendicular_transversals *)
definition Postulate10 :: "bool" where 
  "Postulate10 \<equiv> postulate_of_parallelism_of_perpendicular_transversals"

(* (11) universal_posidonius_postulate *)
definition Postulate11 :: "bool" where 
  "Postulate11 \<equiv> universal_posidonius_postulate"

(* (12) alternative_playfair_s_postulate *)
definition Postulate12 :: "bool" where 
  "Postulate12 \<equiv> alternative_playfair_s_postulate"

(* (13) proclus_postulate *)
definition Postulate13 :: "bool" where 
  "Postulate13 \<equiv> proclus_postulate"

(* (14) alternative_proclus_postulate *)
definition Postulate14 :: "bool" where 
  "Postulate14 \<equiv> alternative_proclus_postulate"

(* (15) triangle_circumscription_principle *)
definition Postulate15 :: "bool" where 
  "Postulate15 \<equiv> triangle_circumscription_principle"

(* (16) inverse_projection_postulate *)
definition Postulate16 :: "bool" where 
  "Postulate16 \<equiv> inverse_projection_postulate"

(* (17) euclid_5 *)
definition Postulate17 :: "bool" where 
  "Postulate17 \<equiv> euclid_5"

(* (18) strong_parallel_postulate *)
definition Postulate18 :: "bool" where 
  "Postulate18 \<equiv> strong_parallel_postulate"

(* (19) strong_parallel_postulate *)

definition Postulate19 :: "bool" where 
  "Postulate19 \<equiv> alternative_strong_parallel_postulate"

(* (20) euclid_s_parallel_postulate *)
definition Postulate20 :: "bool" where 
  "Postulate20 \<equiv>  euclid_s_parallel_postulate"

(* (21) postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights *)
definition Postulate21 :: "bool" where 
  "Postulate21 \<equiv>  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights"

(* (22) posidonius_postulate *)
definition Postulate22 :: "bool" where 
  "Postulate22 \<equiv>  posidonius_postulate"

(* (23) postulate_of_existence_of_similar_triangles *)
definition Postulate23 :: "bool" where 
  "Postulate23 \<equiv>  postulate_of_existence_of_similar_triangles"

(* (24) thales_postulate *)
definition Postulate24 :: "bool" where 
  "Postulate24 \<equiv>  thales_postulate"

(* (25) thales_converse_postulate *)
definition Postulate25 :: "bool" where 
  "Postulate25 \<equiv>  thales_converse_postulate"

(* (26) existential_thales_postulate *)
definition Postulate26 :: "bool" where 
  "Postulate26 \<equiv>  existential_thales_postulate"

(* (27) postulate_of_right_saccheri_quadrilaterals *)
definition Postulate27 :: "bool" where 
  "Postulate27 \<equiv>  postulate_of_right_saccheri_quadrilaterals"

(* (28) postulate_of_existence_of_a_right_saccheri_quadrilateral *)
definition Postulate28 :: "bool" where 
  "Postulate28 \<equiv>  postulate_of_existence_of_a_right_saccheri_quadrilateral"

(* (29) postulate_of_right_lambert_quadrilaterals *)
definition Postulate29 :: "bool" where 
  "Postulate29 \<equiv>  postulate_of_right_lambert_quadrilaterals"

(* (30) postulate_of_existence_of_a_right_lambert_quadrilateral *)
definition Postulate30 :: "bool" where 
  "Postulate30 \<equiv>  postulate_of_existence_of_a_right_lambert_quadrilateral"

(* (31) weak_inverse_projection_postulate *)
definition Postulate31 :: "bool" where 
  "Postulate31 \<equiv> weak_inverse_projection_postulate"

(* (32) weak_tarski_s_parallel_postulate *)
definition Postulate32 :: "bool" where 
  "Postulate32 \<equiv> weak_tarski_s_parallel_postulate"

(* (33) weak_triangle_circumscription_principle *)
definition Postulate33 :: "bool" where 
  "Postulate33 \<equiv> weak_triangle_circumscription_principle"

(* (34) legendre_s_parallel_postulate *)
definition Postulate34 :: "bool" where 
  "Postulate34 \<equiv> legendre_s_parallel_postulate"

(* (35) existential_playfair_s_postulate *)
definition Postulate35 :: "bool" where 
  "Postulate35 \<equiv> existential_playfair_s_postulate"

subsection "Propositions"

lemma euclid_5__original_euclid:
  assumes "Euclid5"
  shows "EuclidSParallelPostulate"
proof -
  {
    fix A B C D P Q R
    assume P1: "B C OS A D \<and> SAMS A B C B C D \<and> A B C B C D SumA P Q R \<and> \<not> Bet P Q R"
    obtain M where P2: "M Midpoint B C"
      using midpoint_existence by auto
    obtain D' where P3: "C Midpoint D D'"
      using symmetric_point_construction by auto
    obtain E where P4: "M Midpoint D' E"
      using symmetric_point_construction by auto
    have P5: "A \<noteq> B"
      using P1 os_distincts by blast
    have P6: "B \<noteq> C"
      using P1 os_distincts by blast
    have P7: "C \<noteq> D"
      using P1 os_distincts by blast
    have P10: "M \<noteq> B"
      using P2 P6 is_midpoint_id by auto
    have P11: "M \<noteq> C"
      using P2 P6 is_midpoint_id_2 by auto
    have P13: "C \<noteq> D'"
      using P3 P7 is_midpoint_id_2 by blast
    have P16: "\<not> Col B C A"
      using one_side_not_col123 P1 by blast
    have "B C OS D A"
      using P1 one_side_symmetry by blast
    then have P17: "\<not> Col B C D"
      using one_side_not_col123 P1 by blast
    then have P18: "\<not> Col M C D"
      using P2 Col_perm P11 col_transitivity_2 midpoint_col by blast
    then have P19: "\<not> Col M C D'"
      by (metis P13  P3 Col_perm col_transitivity_2 midpoint_col)
    then have P20: "\<not> Col D' C B"
      by (metis Col_perm P13 P17 P3 col_transitivity_2 midpoint_col)
    then have P21: "\<not> Col M C E"
      by (metis P19 P4 bet_col col2__eq col_permutation_4 midpoint_bet midpoint_distinct_2)
    have P22: "M C D' CongA M B E \<and> M D' C CongA M E B" using P13 l11_49
      by (metis Cong_cases P19 P2 P4 l11_51 l7_13_R1 l7_2 midpoint_cong not_col_distincts)
    have P23: "Cong C D' B E"
      using P11 P2 P4 l7_13_R1 l7_2 by blast
    have P27: "C B TS D D'"
      by (simp add: P13 P17 P3 bet__ts midpoint_bet not_col_permutation_4)
    have P28: "A InAngle C B E"
    proof -
      have "C B A LeA C B E"
      proof -
        have "A B C LeA B C D'"
        proof -
          have "Bet D C D'"
            by (simp add: P3 midpoint_bet)
          then show ?thesis using P1 P7 P13 sams_chara
            by (metis sams_left_comm sams_sym)
        qed
        moreover have "A B C CongA C B A"
          using P5 P6 conga_pseudo_refl by auto
        moreover have "B C D' CongA C B E"
          by (metis CongA_def Mid_cases P2 P22 P4 P6 symmetry_preserves_conga)
        ultimately show ?thesis
          using l11_30 by blast
      qed
      moreover have "C B OS E A"
      proof -
        have "C B TS E D'"
          using P2 P20 P4 l7_2 l9_2 mid_two_sides not_col_permutation_1 by blast
        moreover have "C B TS A D'"
          using P27 \<open>B C OS D A\<close> invert_two_sides l9_8_2 by blast
        ultimately show ?thesis
          using OS_def by blast
      qed
      ultimately show ?thesis
        using lea_in_angle by simp
    qed
    obtain A' where P30: "Bet C A' E \<and> (A' = B \<or> B Out A' A)" using P28 InAngle_def by auto
    {
      assume "A' = B"
      then have "Col D' C B"
        by (metis Col_def P2 P21 P30 P6 col_transitivity_1 midpoint_col)
      then have "False"
        by (simp add: P20)
      then have "\<exists> Y. B Out A Y \<and> C Out D Y" by auto
    }
    {
      assume P31: "B Out A' A"
      have "\<exists> I. BetS D' C I \<and> BetS B A' I"
      proof -
        have P32: "BetS B M C"
          using BetS_def Midpoint_def P10 P11 P2 by auto
        moreover have "BetS E M D'"
          using BetS_def Bet_cases P19 P21 P4 midpoint_bet not_col_distincts by fastforce
        moreover have "BetS C A' E"
        proof -
          have P32A: "C \<noteq> A'"
            using P16 P31 out_col by auto
          {
            assume "A' = E"
            then have P33: "B Out A E"
              using P31 l6_6 by blast
            then have "A B C B C D SumA D' C D"
            proof -
              have "D' C B CongA A B C"
              proof -
                have "D' C M CongA E B M"
                  by (simp add: P22 conga_comm)
                moreover have "C Out D' D'"
                  using P13 out_trivial by auto
                moreover have "C Out B M"
                  using BetSEq Out_cases P32 bet_out_1 by blast
                moreover have "B Out A E"
                  using P33 by auto
                moreover have "B Out C M"
                  using BetSEq Out_def P32 by blast
                ultimately show ?thesis
                  using l11_10 by blast
              qed
              moreover have "D' C B B C D SumA D' C D"
                by (simp add: P27 l9_2 ts__suma_1)
              moreover have "B C D CongA B C D"
                using P6 P7 conga_refl by auto
              moreover have "D' C D CongA D' C D"
                using P13 P7 conga_refl by presburger
              ultimately show ?thesis
                using conga3_suma__suma by blast
            qed
            then have "D' C D CongA P Q R"
              using P1 suma2__conga by auto
            then have "Bet P Q R"
              using Bet_cases P3 bet_conga__bet midpoint_bet by blast
            then have "False" using P1 by simp
          }
          then have "A' \<noteq> E" by auto
          then show ?thesis
            by (simp add: BetS_def P30 P32A)
        qed
        moreover have "\<not> Col B C D'"
          by (simp add: P20 not_col_permutation_3)
        moreover have "Cong B M C M"
          using Midpoint_def P2 not_cong_1243 by blast
        moreover have "Cong E M D' M"
          using Cong_perm Midpoint_def P4 by blast
        ultimately show ?thesis
          using euclid_5_def assms by blast
      qed
      then obtain Y where P34: "Bet D' C Y \<and> BetS B A' Y" using BetSEq by blast
      then have "\<exists> Y. B Out A Y \<and> C Out D Y"
      proof -
        have P35: "B Out A Y"
          by (metis BetSEq Out_def P31 P34 l6_7)
        moreover have "C Out D Y"
        proof -
          have "D \<noteq> C"
            using P7 by auto
          moreover have "Y \<noteq> C"
            using P16 P35 l6_6 out_col by blast
          moreover have "D' \<noteq> C"
            using P13 by auto
          moreover have "Bet D C D'"
            by (simp add: P3 midpoint_bet)
          moreover have "Bet Y C D'"
            by (simp add: Bet_perm P34)
          ultimately show ?thesis
            using l6_2 by blast
        qed
        ultimately show ?thesis by auto
      qed
    }
    then have "\<exists> Y. B Out A Y \<and> C Out D Y"
      using P30 \<open>A' = B \<Longrightarrow> \<exists>Y. B Out A Y \<and> C Out D Y\<close> by blast
  }
  then show ?thesis using euclid_s_parallel_postulate_def  by blast
qed

lemma tarski_s_euclid_implies_euclid_5:
  assumes "TarskiSParallelPostulate"
  shows "Euclid5"
proof -
  {
    fix P Q R S T U
    assume
      P1: "BetS P T Q \<and> BetS R T S \<and> BetS Q U R \<and> \<not> Col P Q S \<and> Cong P T Q T \<and> Cong R T S T"
    have P1A: "BetS P T Q" using P1 by simp
    have P1B: "BetS R T S" using P1 by simp
    have P1C: "BetS Q U R" using P1 by simp
    have P1D: "\<not> Col P Q S" using P1 by simp
    have P1E: "Cong P T Q T" using P1 by simp
    have P1F: "Cong R T S T" using P1 by simp
    obtain V where P2: "P Midpoint R V"
      using symmetric_point_construction by auto
    have P3: "Bet V P R"
      using Mid_cases P2 midpoint_bet by blast
    then obtain W where P4: "Bet P W Q \<and> Bet U W V" using inner_pasch
      using BetSEq P1C by blast
    {
      assume "P = W"
      have "P \<noteq> V"
        by (metis BetSEq Bet_perm Col_def Cong_perm Midpoint_def P1A P1B P1D P1E P1F 
            P2 between_trivial is_midpoint_id_2 l7_9)
      have "Col P Q S"
      proof -
        have f1: "Col V P R"
          by (meson Col_def P3)
        have f2: "Col U R Q"
          by (simp add: BetSEq Col_def P1)
        have f3: "Bet P T Q"
          using BetSEq P1 by fastforce
        have f4: "R = P \<or> Col V P U"
          by (metis (no_types) Col_def P4 \<open>P = W\<close> \<open>P \<noteq> V\<close> l6_16_1)
        have f5: "Col Q P T"
          using f3 by (meson Col_def)
        have f6: "Col T Q P"
          using f3 by (meson Col_def)
        have f7: "Col P T Q"
          using f3 by (meson Col_def)
        have f8: "Col P Q P"
          using Col_def P4 \<open>P = W\<close> by blast
        have "Col R T S"
          by (meson BetSEq Col_def P1)
        then have "T = P \<or> Q = P"
          using f8 f7 f6 f5 f4 f2 f1 by (metis (no_types) BetSEq P1 \<open>P \<noteq> V\<close> colx l6_16_1)
        then show ?thesis
          by (metis BetSEq P1)
      qed
      then have "False"
        by (simp add: P1D)
    }
    then have P5: "P \<noteq> W" by auto
    have "Bet V W U"
      using Bet_cases P4 by auto
    then obtain X Y where P7: "Bet P V X \<and> Bet P U Y \<and> Bet X Q Y"
      using assms(1) P1 P4 P5 tarski_s_parallel_postulate_def by blast
    have "Q S Par P R"
    proof -
      have "Q \<noteq> S"
        using P1D col_trivial_2 by auto
      moreover have "T Midpoint Q P"
        using BetSEq P1A P1E l7_2 midpoint_def not_cong_1243 by blast
      moreover have "T Midpoint S R"
        using BetSEq P1B P1F l7_2 midpoint_def not_cong_1243 by blast
      ultimately show ?thesis
        using l12_17 by auto
    qed
    then have P9: "Q S ParStrict P R"
      using P1D Par_def par_strict_symmetry par_symmetry by blast
    have P10: "Q S TS P Y"
    proof -
      have P10A: "P \<noteq> R"
        using P9 par_strict_distinct by auto
      then have P11: "P \<noteq> X"
        by (metis P2 P7 bet_neq12__neq midpoint_not_midpoint)
      have P12: "\<not> Col X Q S"
      proof -
        have "Q S ParStrict P R"
          by (simp add: P9)
        then have "Col P R X"
          by (metis P2 P3 P7 bet_col between_symmetry midpoint_not_midpoint 
              not_col_permutation_4 outer_transitivity_between)
        then have "P X ParStrict Q S"
          using P9 Par_strict_perm P11 par_strict_col_par_strict by blast
        then show ?thesis
          using par_strict_not_col_2 by auto
      qed
      {
        assume W1: "Col Y Q S"
        have W2: "Q = Y"
          by (metis P12 P7 W1 bet_col bet_col1 colx)
        then have "\<not> Col Q P R"
          using P9 W1 par_not_col by auto
        then have W3: "Q = U"
          by (smt BetS_def Col_def P1C P7 W2 col_transitivity_2)
        then have "False"
          using BetS_def P1C by auto
      }
      then have "\<not> Col Y Q S" by auto
      then have "Q S TS X Y"
        by (metis P7 P12 bet__ts not_col_distincts not_col_permutation_1)
      moreover have "Q S OS X P"
      proof -
        have "P \<noteq> V"
          using P10A P2 is_midpoint_id_2 by blast
        then have "Q S ParStrict P X"
          by (meson Bet_perm P3 P7 P9 P11 bet_col not_col_permutation_4 par_strict_col_par_strict)
        then have "Q S ParStrict X P"
          by (simp add: par_strict_right_comm)
        then show ?thesis
          by (simp add: l12_6)
      qed
      ultimately show ?thesis
        using l9_8_2 by auto
    qed
    then obtain I where W4: "Col I Q S \<and> Bet P I Y"
      using TS_def by blast
    have "\<exists> I. (BetS S Q I \<and> BetS P U I)"
    proof -
      have "BetS P U I"
      proof -
        have "P \<noteq> Y"
          using P10 not_two_sides_id by auto
        have W4A: "Bet P U I"
        proof -
          have W5: "Col P U I"
            using P7 W4 bet_col1 by auto
          {
            assume W6: "Bet U I P"
            have W7: "Q S OS P U"
            proof -
              have "Q S OS R U"
              proof -
                have "\<not> Col Q S R"
                  using P9 par_strict_not_col_4 by auto
                moreover have "Q Out R U"
                  using BetSEq Out_def P1C by blast
                ultimately show ?thesis
                  by (simp add: out_one_side)
              qed
              moreover have "Q S OS P R"
                by (simp add: P9 l12_6)
              ultimately show ?thesis
                using one_side_transitivity by blast
            qed
            have W8: "I Out P U \<or> \<not> Col Q S P"
              by (simp add: P1D not_col_permutation_1)
            have "False"
            proof -
              have "I Out U P"
                using W4 W6 W7 between_symmetry one_side_chara by blast
              then show ?thesis
                using W6 not_bet_and_out by blast
            qed
          }
          {
            assume V1: "Bet I P U"
            have "P R OS I U"
            proof -
              have "P R OS I Q"
              proof -
                {
                  assume "Q = I"
                  then have "Col P Q S"
                    by (metis BetSEq Col_def P1C P7 P9 V1 W4 between_equality 
                        outer_transitivity_between par_not_col)
                  then have "False"
                    using P1D by blast
                }
                then have "Q \<noteq> I" by blast
                moreover have "P R ParStrict Q S"
                  using P9 par_strict_symmetry by blast
                moreover have "Col Q S I"
                  using Col_cases W4 by blast
                ultimately show ?thesis
                  using one_side_symmetry par_strict_all_one_side by blast
              qed
              moreover have "P R OS Q U"
              proof -
                have "Q S ParStrict P R"
                  using P9 by blast
                have "R Out Q U \<and> \<not> Col P R Q"
                  by (metis BetSEq Bet_cases Out_def P1C calculation col124__nos)
                then show ?thesis
                  by (metis P7 V1 W4 \<open>Bet U I P \<Longrightarrow> False\<close> between_equality 
                      col_permutation_2 not_bet_distincts out_col outer_transitivity_between)
              qed
              ultimately show ?thesis
                using one_side_transitivity by blast
            qed
            then have V2: "P Out I U"
              using P7 W4 bet2__out os_distincts by blast
            then have "Col P I U"
              using V1 not_bet_and_out by blast
            then have "False"
              using V1 V2 not_bet_and_out by blast
          }
          then moreover have "\<not> (Bet U I P \<or> Bet I P U)"
            using \<open>Bet U I P \<Longrightarrow> False\<close> by auto
          ultimately show ?thesis
            using Col_def W5 by blast
        qed
        {
          assume "P = U"
          then have "Col P R Q"
            using BetSEq Col_def P1C by blast
          then have "False"
            using P9 par_strict_not_col_3 by blast
        }
        then have V6: "P \<noteq> U" by auto
        {
          assume "U = I"
          have "Q = U"
          proof -
            have f1: "BetS Q I R"
              using P1C \<open>U = I\<close> by blast
            then have f2: "Col Q I R"
              using BetSEq Col_def by blast
            have f3: "Col I R Q"
              using f1 by (simp add: BetSEq Col_def)
            { assume "R \<noteq> Q"
              moreover
              { assume "(R \<noteq> Q \<and> R \<noteq> I) \<and> \<not> Col I Q R"
                moreover
                { assume "\<exists>p. (R \<noteq> Q \<and> \<not> Col I p I) \<and> Col Q I p"
                  then have "I = Q"
                    using f1 by (metis (no_types) BetSEq Col_def col_transitivity_2) }
                ultimately have "(\<exists>p pa. ((pa \<noteq> I \<and> \<not> Col pa p R) \<and> Col Q I pa) \<and> Col I pa p) \<or> I = Q"
                  using f3 f2 by (metis (no_types) col_transitivity_2) }
              ultimately have "(\<exists>p pa. ((pa \<noteq> I \<and> \<not> Col pa p R) \<and> Col Q I pa) \<and> Col I pa p) \<or> I = Q"
                using f1 by (metis (no_types) BetSEq P9 W4 col_transitivity_2 par_strict_not_col_4) }
            then show ?thesis
              using f2 by (metis P9 W4 \<open>U = I\<close> col_transitivity_2 par_strict_not_col_4)
          qed
          then have "False"
            using BetSEq P1C by blast
        }
        then have "U \<noteq> I" by auto
        then show ?thesis
          by (simp add: W4A V6 BetS_def)
      qed
      moreover have "BetS S Q I"
      proof -
        have "Q R TS S I"
        proof -
          have "Q R TS P I"
          proof -
            have "\<not> Col P Q R"
              using P9 col_permutation_5 par_strict_not_col_3 by blast
            moreover have "\<not> Col I Q R"
            proof -
              {
                assume "Col I Q R"
                then have "Col Q S R"
                proof -
                  have f1: "\<forall>p pa pb. Col p pa pb \<or> \<not> BetS pb p pa"
                    by (meson BetSEq Col_def)
                  then have f2: "Col U I P"
                    using \<open>BetS P U I\<close> by blast
                  have f3: "Col I P U"
                    by (simp add: BetSEq Col_def \<open>BetS P U I\<close>)
                  have f4: "\<forall>p. (U = Q \<or> Col Q p R) \<or> \<not> Col Q U p"
                    by (metis BetSEq Col_def P1C col_transitivity_1)
                  { assume "P \<noteq> Q"
                    moreover
                    { assume "(P \<noteq> Q \<and> U \<noteq> Q) \<and> Col Q P Q"
                      then have "(P \<noteq> Q \<and> U \<noteq> Q) \<and> \<not> Col Q P R"
                        using Col_cases \<open>\<not> Col P Q R\<close> by blast
                      moreover
                      { assume "\<exists>p. ((U \<noteq> Q \<and> P \<noteq> Q) \<and> \<not> Col Q p P) \<and> Col Q P p"
                        then have "U \<noteq> Q \<and> \<not> Col Q P P"
                          by (metis col_transitivity_1)
                        then have "\<not> Col U Q P"
                          using col_transitivity_2 by blast }
                      ultimately have "\<not> Col U Q P \<or> I \<noteq> Q"
                        using f4 f3 by blast }
                    ultimately have "I \<noteq> Q"
                      using f2 f1 by (metis BetSEq P1C col_transitivity_1 col_transitivity_2) }
                  then have "I \<noteq> Q"
                    using BetSEq \<open>BetS P U I\<close> by blast
                  then show ?thesis
                    by (simp add: W4 \<open>Col I Q R\<close> col_transitivity_2)
                qed
                then have "False"
                  using P9 par_strict_not_col_4 by blast
              }
              then show ?thesis by blast
            qed
            moreover have "Col U Q R"
              using BetSEq Bet_cases Col_def P1C by blast
            moreover have "Bet P U I"
              by (simp add: BetSEq \<open>BetS P U I\<close>)
            ultimately show ?thesis
              using TS_def by blast
          qed
          moreover have "Q R OS P S"
          proof -
            have "Q R Par P S"
            proof -
              have "Q \<noteq> R"
                using BetSEq P1 by blast
              moreover have "T Midpoint Q P"
                using BetSEq Bet_cases P1A P1E cong_3421 midpoint_def by blast
              moreover have "T Midpoint R S"
                using BetSEq P1B P1F midpoint_def not_cong_1243 by blast
              ultimately show ?thesis
                using l12_17 by blast
            qed
            then have "Q R ParStrict P S"
              by (simp add: P1D Par_def not_col_permutation_4)
            then show ?thesis
              using l12_6 by blast
          qed
          ultimately show ?thesis
            using l9_8_2 by blast
        qed
        then show ?thesis
          by (metis BetS_def W4 col_two_sides_bet not_col_permutation_2 ts_distincts)
      qed
      ultimately show ?thesis
        by auto
    qed
  }
  then show ?thesis using euclid_5_def by blast
qed

lemma tarski_s_implies_euclid_s_parallel_postulate:
  assumes "TarskiSParallelPostulate"
  shows "EuclidSParallelPostulate"
  by (simp add: assms euclid_5__original_euclid tarski_s_euclid_implies_euclid_5)

theorem tarski_s_euclid_implies_playfair_s_postulate:
  assumes "TarskiSParallelPostulate"
  shows "PlayfairSPostulate"
proof -
  {
    fix A1 A2 B1 B2 P C1 C2
    assume P1: "\<not> Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2"
    have P1A: "\<not> Col P A1 A2"
      by (simp add: P1)
    have P2: "A1 A2 Par B1 B2"
      by (simp add: P1)
    have P3: "Col P B1 B2"
      by (simp add: P1)
    have P4: "A1 A2 Par C1 C2"
      by (simp add: P1)
    have P5: "Col P C1 C2"
      by (simp add: P1)
    have P6: "A1 A2 ParStrict B1 B2"
    proof -
      have "A1 A2 Par B1 B2"
        by (simp add: P1)
      moreover have "Col B1 B2 P"
        using P3 not_col_permutation_2 by blast
      moreover have "\<not> Col A1 A2 P"
        by (simp add: P1A not_col_permutation_1)
      ultimately show ?thesis
        using par_not_col_strict by auto
    qed
    have P7: "A1 A2 ParStrict C1 C2"
    proof -
      have "A1 A2 Par C1 C2"
        by (simp add: P1)
      moreover have "Col C1 C2 P"
        using Col_cases P1 by blast
      moreover have "\<not> Col A1 A2 P"
        by (simp add: P1A not_col_permutation_1)
      ultimately show ?thesis
        using par_not_col_strict by auto
    qed
    {
      assume "\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2"
      have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'"
      proof -
        have T2: "Coplanar A1 A2 P A1"
          using ncop_distincts by auto
        have T3: "Coplanar A1 A2 B1 B2"
          by (simp add: P1 par__coplanar)
        have T4: "Coplanar A1 A2 C1 C2"
          by (simp add: P7 pars__coplanar)
        have T5: "Coplanar A1 A2 P B1"
          using P1 col_trivial_2 ncop_distincts par__coplanar par_col2_par_bis by blast
        then have T6: "Coplanar A1 A2 P B2"
          using P3 T3 col_cop__cop by blast
        have T7: "Coplanar A1 A2 P C1"
          using P1 T4 col_cop__cop coplanar_perm_1 not_col_permutation_2 par_distincts by blast
        then have T8: "Coplanar A1 A2 P C2"
          using P5 T4 col_cop__cop by blast
        {
          assume "\<not> Col C1 B1 B2"
          moreover have "C1 \<noteq> C2"
            using P1 par_neq2 by auto
          moreover have "Col B1 B2 P"
            using P1 not_col_permutation_2 by blast
          moreover have "Col C1 C2 P"
            using Col_cases P5 by auto
          moreover have "\<not> Col B1 B2 C1"
            using Col_cases calculation(1) by auto
          moreover have "\<not> Col B1 B2 A1"
            using P6 par_strict_not_col_3 by auto
          moreover have "Coplanar B1 B2 C1 A1"
            using Col_cases P1A T5 T2 T6 T7 coplanar_pseudo_trans by blast
          ultimately have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'"
            using cop_not_par_other_side by blast
        }
        {
          assume "\<not> Col C2 B1 B2"
          moreover have "C2 \<noteq> C1"
            using P1 par_neq2 by blast
          moreover have "Col B1 B2 P"
            using Col_cases P3 by auto
          moreover have "Col C2 C1 P"
            using Col_cases P5 by auto
          moreover have "\<not> Col B1 B2 C2"
            by (simp add: calculation(1) not_col_permutation_1)
          moreover have "\<not> Col B1 B2 A1"
            using P6 par_strict_not_col_3 by auto
          moreover have "Coplanar B1 B2 C2 A1"
            using Col_cases P1A T2 T5 T6 T8 coplanar_pseudo_trans by blast
          ultimately have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'" using cop_not_par_other_side
            by (meson not_col_permutation_4)
        }
        then show ?thesis
          using \<open>\<not> Col C1 B1 B2 \<Longrightarrow> \<exists>C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'\<close> \<open>\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2\<close> by blast
      qed
      then obtain C' where W1: "Col C1 C2 C' \<and> B1 B2 TS A1 C'" by auto
      then have W2: "\<not> Col A1 B1 B2"
        using TS_def by blast
      obtain B where W3: "Col B B1 B2 \<and> Bet A1 B C'"
        using TS_def W1 by blast
      obtain C where W4: "P Midpoint C' C"
        using symmetric_point_construction by blast
      then have W4A: "Bet A1 B C' \<and> Bet C P C'"
        using Mid_cases W3 midpoint_bet by blast
      then obtain D where W5: "Bet B D C \<and> Bet P D A1" using inner_pasch by blast
      have W6: "C' \<noteq> P"
        using P3 TS_def W1 by blast
      then have "A1 A2 Par C' P"
        by (meson P1 W1 not_col_permutation_2 par_col2_par)
      have W9: "A1 A2 ParStrict C' P"
        using Col_cases P5 P7 W1 W6 par_strict_col2_par_strict by blast
      then have W10: "B \<noteq> P"
        by (metis W6 W4A bet_out_1 out_col par_strict_not_col_3)
      have W11: "P \<noteq> C"
        using W6 W4 is_midpoint_id_2 by blast
      {
        assume "P = D"
        then have "False"
          by (metis Col_def P3 W1 W3 W4A W5 W10 W11 col_trivial_2 colx l9_18_R1)
      }
      then have "P \<noteq> D" by auto
      then obtain X Y where W12: "Bet P B X \<and> Bet P C Y \<and> Bet X A1 Y"
        using W5 assms tarski_s_parallel_postulate_def by blast
      then have "P \<noteq> X"
        using W10 bet_neq12__neq by auto
      then have "A1 A2 ParStrict P X"
        by (metis Col_cases P3 P6 W10 W12 W3 bet_col colx par_strict_col2_par_strict)
      then have W15: "A1 A2 OS P X"
        by (simp add: l12_6)
      have "P \<noteq> Y"
        using W11 W12 between_identity by blast
      then have "A1 A2 ParStrict P Y"
        by (metis Col_def W11 W12 W4A W9 col_trivial_2 par_strict_col2_par_strict)
      then have W16: "A1 A2 OS P Y"
        using l12_6 by auto
      have "Col A1 X Y"
        by (simp add: W12 bet_col col_permutation_4)
      then have "A1 Out X Y" using col_one_side_out W15 W16
        using one_side_symmetry one_side_transitivity by blast
      then have "False"
        using W12 not_bet_and_out by blast
    }
    then have "Col C1 B1 B2 \<and> Col C2 B1 B2"
      by auto
  }
  {
    fix A1 A2 B1 B2 P C1 C2
    assume P1: "Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2"
    have "Col C1 B1 B2"
      by (smt P1 l9_10 not_col_permutation_3 not_strict_par2 par_col2_par par_comm par_id_5 par_symmetry ts_distincts)
    moreover have "Col C2 B1 B2"
      by (smt P1 l9_10 not_col_permutation_3 not_strict_par2 par_col2_par par_id_5 par_left_comm par_symmetry ts_distincts)
    ultimately have "Col C1 B1 B2 \<and> Col C2 B1 B2" by auto
  }
  then show ?thesis
    using playfair_s_postulate_def
    by (metis \<open>\<And>P C2 C1 B2 B1 A2 A1. \<not> Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<Longrightarrow> Col C1 B1 B2 \<and> Col C2 B1 B2\<close>)
qed

lemma tarski_s_euclid_remove_degenerated_cases:
  assumes "\<forall> A B C D T. A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> D \<and> 
                        A \<noteq> T \<and> B \<noteq> C \<and> B \<noteq> D \<and> B \<noteq> T \<and> C \<noteq> D \<and>
                        C \<noteq> T \<and> D \<noteq> T \<and> \<not> Col A B C \<and> Bet A D T \<and>
                        Bet B D C \<and> \<not> Col B C T \<longrightarrow> 
     (\<exists> x y. (Bet A B x \<and> Bet A C y \<and> Bet x T y))"
  shows "\<forall> A B C D T. Bet A D T \<and> Bet B D C \<and> A \<noteq> D \<longrightarrow> 
                         (\<exists> x y. (Bet A B x \<and> Bet A C y \<and> Bet x T y))" 
proof -
  {
    fix A B C D T
    assume P1: "Bet A D T \<and> Bet B D C \<and> A \<noteq> D"
    hence P2: "Bet A D T" 
      by auto
    have P3: "Bet B D C"
      by (simp add: P1)
    have P4: "A \<noteq> D"
      using P1 by blast 
    have "(\<exists> x y. (Bet A B x \<and> Bet A C y \<and> Bet x T y))" 
    proof cases
      assume "A = B"
      thus ?thesis
        using between_trivial between_trivial2 by blast 
    next
      assume P5: "A \<noteq> B"
      thus ?thesis 
      proof cases
        assume "A = C"
        thus ?thesis
          using between_trivial between_trivial2 by auto 
      next
        assume P6: "A \<noteq> C"
        thus ?thesis 
        proof cases
          assume "A = T"
          thus ?thesis
            using \<open>Bet A D T \<and> Bet B D C \<and> A \<noteq> D\<close> between_identity by blast
        next
          assume P7: "A \<noteq> T"
          thus ?thesis 
          proof cases
            assume "B = C"            
            thus ?thesis
              using \<open>Bet A D T \<and> Bet B D C \<and> A \<noteq> D\<close> between_identity 
                between_trivial2 by blast
          next
            assume P8: "B \<noteq> C"
            thus ?thesis
            proof cases
              assume "B = D"
              thus ?thesis
                using \<open>Bet A D T \<and> Bet B D C \<and> A \<noteq> D\<close> between_trivial2 
                  segment_construction by blast
            next
              assume P9: "B \<noteq> D"
              thus ?thesis
              proof cases
                assume "B = T"
                thus ?thesis
                  using between_trivial between_trivial2 by blast
              next
                assume P10: "B \<noteq> T"
                thus ?thesis 
                proof cases
                  assume "C = D"
                  thus ?thesis
                    using \<open>Bet A D T \<and> Bet B D C \<and> A \<noteq> D\<close> between_trivial by blast
                next
                  assume P11: "C \<noteq> D"
                  thus ?thesis
                  proof cases
                    assume "C = T"
                    thus ?thesis
                      using between_trivial by blast
                  next
                    assume P12: "C \<noteq> T"
                    thus ?thesis
                    proof cases
                      assume "D = T"
                      thus ?thesis
                        using \<open>Bet A D T \<and> Bet B D C \<and> A \<noteq> D\<close> between_trivial by blast
                    next
                      assume P13: "D \<noteq> T"
                      {
                        assume "Col A B C"
                        have "Bet A B C \<longrightarrow> ?thesis" 
                          by (metis \<open>Bet A D T\<close> \<open>Bet B D C\<close> between_equality 
                              between_exchange2 between_exchange3 between_exchange4 
                              between_trivial between_trivial2 l5_3) 
                        moreover
                        have "Bet B C A \<longrightarrow> ?thesis"
                          by (meson Bet_perm P1 between_exchange3 between_exchange4 
                              between_trivial) 
                        moreover
                        have "Bet C A B \<longrightarrow>?thesis"                       
                          by (metis between_exchange3 Bet_perm P1 
                              between_exchange2 l5_3 
                              between_exchange4 between_trivial 
                              between_trivial2 l5_1)
                        ultimately
                        have "?thesis"
                          using Col_def \<open>Col A B C\<close> by blast 
                      }
                      moreover
                      {
                        assume P14: "\<not> Col A B C"
                        {
                          assume "Col B C T"
                          hence "D = T" 
                            by (meson P1 P14 bet_col col_permutation_2 
                                col_permutation_5 colx)
                          hence False
                            by (simp add: P13)
                        }
                        hence "?thesis" 
                          using assms P14 P13 P2 P3 P4 P5 P6 P7 P8 
                            P9 P10 P11 P12 by blast
                      }
                      ultimately
                      show ?thesis
                        by blast 
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  }
  thus ?thesis by auto
qed

(* alternate_interior_angles_consecutive_interior_angles.*)
(*
(** This is the converse of l12_21_b.
    The alternate interior angles between two parallel lines are congruent. *)

*)

(** The consecutive interior angles between two parallel lines are supplementary. *)

lemma alternate_interior__consecutive_interior:
  assumes "AlternateInteriorAnglesPostulate"
  shows "ConsecutiveInteriorAnglesPostulate" 
proof -
  {
    fix A B C D
    assume "B C OS A D \<and> A B Par C D"
    hence "A \<noteq> B"
      using os_distincts by blast 
    obtain A' where P3: "Bet A B A' \<and> Cong B A' B A"
      using segment_construction by blast
    have "\<not> Col B C A"
      using \<open>B C OS A D \<and> A B Par C D\<close> l9_19 not_col_distincts by blast 
    hence "B C TS A A'"
      using P3 \<open>A \<noteq> B\<close> bet__ts cong_diff_4 by blast 
    hence "B C TS A' D"
      by (meson l9_8_2 \<open>B C OS A D \<and> A B Par C D\<close> l9_2)  
    hence "B C D CongA C B A'" 
      by (metis (full_types) P3 Par_cases l9_2 
          \<open>B C OS A D \<and> A B Par C D\<close> alternate_interior_angles_postulate_def 
          assms bet_col bet_col1 conga_comm invert_two_sides 
          par_col2_par ts_distincts) 
    hence "A B C SuppA B C D"
      using P3 SuppA_def \<open>A \<noteq> B\<close> by auto
  }
  thus ?thesis
    using consecutive_interior_angles_postulate_def by blast
qed

(*alter...\<rightarrow>playfairbis*)

lemma alternate_interior__playfair_aux_1:
  assumes "A1 A2 Par C1 C2" and
    "Col P C1 C2" and
    "Col P P1 P2" and
    "P1 P2 Perp A1 A2" and
    "Col Q A1 A2" 
  shows "Coplanar P Q A1 C1" 
proof -
  have "Coplanar A1 A2 C1 C1" 
    using ncop_distincts by blast
  moreover have "Coplanar A1 A2 C1 A1" 
    using ncop_distincts by blast
  moreover have "Coplanar A1 A2 C1 Q" 
    using Col_cases assms(5) ncop__ncols by blast
  moreover have "Coplanar A1 A2 C1 P" 
    using assms(1) assms(2) col_cop__cop col_permutation_1 
      par__coplanar par_neq2 by blast
  ultimately show ?thesis 
    by (metis assms(1) assms(5) col_cop__cop col_permutation_1 
        ncoplanar_perm_16 ncoplanar_perm_19 par_neq1)
qed

lemma alternate_interior__playfair_aux_2:
  assumes "A1 A2 Par C1 C2" and
    "Col P C1 C2" and
    "Col Q A1 A2" and
    "Col B1 B2 B3" and 
    "\<not> Col A1 A2 P" and
    "Col P B1 B2" and
    "Coplanar A1 A2 B1 B2" and
    "A1 A2 ParStrict B1 B2" 
  shows "Coplanar P Q C1 B3" 
proof -
  have "Coplanar A1 A2 P Q"
    using assms(3) Col_cases ncop__ncols by blast
  moreover have "Coplanar A1 A2 P B3"
    using NCol_perm col2_cop__cop par_strict_neq2 
      assms(4) assms(6) assms(7) assms(8) by blast
  moreover have "Coplanar A1 A2 P P" 
    using ncop_distincts by blast
  moreover have "Coplanar A1 A2 P C1" 
    using assms(1) assms(2) 
    by (metis col_cop__cop coplanar_perm_1 not_col_permutation_2 
        par__coplanar par_neq2)
  ultimately show ?thesis 
    using assms(5) coplanar_pseudo_trans by presburger
qed

lemma alternate_interior__playfair_aux:
  assumes "alternate_interior_angles_postulate"
  shows "\<forall> A1 A2 B1 B2 C1 C2 P.
   (P Perp2 A1 A2 B1 B2 \<and> \<not> Col A1 A2 P \<and> Col P B1 B2 \<and> 
Coplanar A1 A2 B1 B2 \<and>
   A1 A2 Par C1 C2 \<and> Col P C1 C2) \<longrightarrow>
   Col C1 B1 B2"
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume 1: "P Perp2 A1 A2 B1 B2" and
      2: "\<not> Col A1 A2 P" and
      3: "Col P B1 B2" and
      4: "Coplanar A1 A2 B1 B2" and
      5: "A1 A2 Par C1 C2" and
      6: "Col P C1 C2"
    have "Col C1 B1 B2" 
    proof cases
      assume "P = C1"
      thus ?thesis
        using "3" by blast 
    next
      assume "P \<noteq> C1"
      have "A1 A2 ParStrict B1 B2"
        using "1" "2" "3" "4" col_cop_perp2__pars_bis col_permutation_1 by blast
      have "A1 A2 ParStrict C1 C2"
        using "2" "5" "6" col_permutation_1 par_not_col_strict by blast
      obtain P1 P2 where P1: "Col P P1 P2 \<and> P1 P2 Perp A1 A2 \<and> P1 P2 Perp B1 B2"
        using 1 Perp2_def by blast 
      hence "Col P P1 P2" 
        by blast
      have P1A: "P1 P2 Perp A1 A2"
        using P1 by blast
      then obtain Q where P1B: "Col Q P1 P2 \<and> Col Q A1 A2" 
        using Perp_def by (meson NCol_cases perp_inter_perp_in_n) 
      hence P1C: "Col Q P1 P2" 
        by blast
      have P1D: "Col Q A1 A2" 
        using P1B by blast
      have "P1 P2 Perp B1 B2"
        using P1 by blast
      then obtain P' where P2: "P' PerpAt P1 P2 B1 B2"
        using perp_inter_perp_in_n by blast 
      hence "P = P'"
        using "3" \<open>Col P P1 P2\<close> l8_14_2_1b by blast 
      have "P \<noteq> Q"
        using "2" NCol_cases \<open>Col Q P1 P2 \<and> Col Q A1 A2\<close> by blast
      hence "A1 A2 Perp P Q"
        using perp_col0 P1A Perp_cases \<open>Col P P1 P2\<close> 
          \<open>Col Q P1 P2 \<and> Col Q A1 A2\<close> not_col_permutation_3 by blast 
      have "B1 B2 Perp P Q"
        using perp_col0 
        by (meson P1 \<open>Col Q P1 P2 \<and> Col Q A1 A2\<close> \<open>P \<noteq> Q\<close> 
            col_permutation_3 perp_left_comm) 
      have "\<not> Col Q C1 P"
        using "6" \<open>A1 A2 ParStrict C1 C2\<close> \<open>Col Q P1 P2 \<and> Col Q A1 A2\<close> 
          \<open>P \<noteq> C1\<close> col_trivial_2 colx par_not_col by blast
      obtain B3 where P4: "Col B1 B2 B3 \<and> B3 \<noteq> P"
        using col_trivial_2 diff_col_ex by blast 
      hence P4A: "Col B1 B2 B3"
        by blast
      have "B3 \<noteq> P" 
        using P4 by blast
      have "Q \<noteq> C1"
        using \<open>\<not> Col Q C1 P\<close> col_trivial_1 by blast 
      have "A1 \<noteq> A2"
        using "2" col_trivial_1 by blast
      have "A2 \<noteq> P"
        using "2" col_trivial_2 by blast
      have "A1 \<noteq> P"
        using "2" col_trivial_3 by auto
      have "B1 \<noteq> B2"
        using \<open>P1 P2 Perp B1 B2\<close> perp_distinct by blast
      have "A1 \<noteq> B1"
        using \<open>A1 A2 ParStrict B1 B2\<close> col_trivial_3 par_strict_not_col_1 by blast 
      have "A1 \<noteq> B2"
        using \<open>A1 A2 ParStrict B1 B2\<close> col_trivial_1 col_trivial_3 par_not_col by blast
      have "A2 \<noteq> B1"
        using \<open>A1 A2 ParStrict B1 B2\<close> col_trivial_2 par_strict_not_col_1 by blast
      have "A2 \<noteq> B2"
        using \<open>A1 A2 ParStrict B1 B2\<close> col_trivial_2 par_strict_not_col_4 by blast
      have "A1 \<noteq> C1"
        using \<open>A1 A2 ParStrict C1 C2\<close> not_par_strict_id by blast
      have "A1 \<noteq> C2"
        using \<open>A1 A2 ParStrict C1 C2\<close> col_trivial_3 par_strict_not_col_4 by blast
      have "A2 \<noteq> C1"
        using Par_strict_cases \<open>A1 A2 ParStrict C1 C2\<close> not_par_strict_id by blast
      have "A2 \<noteq> C2"
        using Par_strict_cases \<open>A1 A2 ParStrict C1 C2\<close> not_par_strict_id by blast
      have "C1 \<noteq> C2"
        using "5" par_distincts by blast
      have "Col P C1 B3" 
      proof -
        have "Per C1 P Q" 
        proof -
          have "\<exists> A3. Col A1 A2 A3 \<and> P Q TS C1 A3"
          proof cases
            assume "Col P Q A1"
            have "A2 \<noteq> A1"
              using \<open>A1 \<noteq> A2\<close> by auto 
            moreover
            have "Col P Q Q"
              by (simp add: col_trivial_2) 
            moreover
            have "Col A2 A1 Q"
              by (simp add: P1D col_permutation_3) 
            moreover
            have "\<not> Col P Q A2"
              using "2" \<open>Col P Q A1\<close> \<open>P \<noteq> Q\<close> col3 col_trivial_3 by blast
            moreover
            have "\<not> Col P Q C1"
              using NCol_cases \<open>\<not> Col Q C1 P\<close> by blast 
            moreover
            have "Coplanar P Q A2 C1"
              by (metis "5" "6" P1D \<open>Col P Q A1\<close> \<open>P \<noteq> C1\<close> 
                  calculation(2) calculation(4) col_permutation_1 colx 
                  coplanar_perm_18 par__coplanar par_col_par)
            ultimately
            have "\<exists> Q0. Col A2 A1 Q0 \<and> P Q TS C1 Q0" 
              using cop_not_par_other_side by blast
            thus ?thesis
              using col_permutation_4 by blast  
          next
            assume "\<not> Col P Q A1"
            have "A1 \<noteq> A2"
              by (simp add: \<open>A1 \<noteq> A2\<close>) 
            moreover
            have "Col P Q Q"
              using col_trivial_2 by auto 
            moreover
            have "Col A1 A2 Q"
              by (simp add: P1D col_permutation_2) 
            moreover
            {
              assume "Col P' Q A1"
              hence "Col A1 P1 P2" 
                using \<open>P = P'\<close> \<open>\<not> Col P Q A1\<close> by auto
              hence "A1 = Q" 
                using \<open>Col P' Q A1\<close> \<open>P = P'\<close> \<open>\<not> Col P Q A1\<close> by auto
              hence "False"
                using \<open>\<not> Col P Q A1\<close> col_trivial_2 by blast
            }
            hence "\<not> Col P Q A1"
              using \<open>P = P'\<close> by blast 
            moreover
            have "\<not> Col P Q C1"
              using NCol_cases \<open>\<not> Col Q C1 P\<close> by blast 
            moreover
            have "Coplanar P Q A1 C1"
              using alternate_interior__playfair_aux_1 5 6 P1 P1A P1D by blast
            ultimately
            show ?thesis 
              using cop_not_par_other_side by blast
          qed
          then obtain A3 where "Col A1 A2 A3 \<and> P Q TS C1 A3" 
            by blast
          hence "\<not> Col A3 P Q"
            using TS_def by blast
          have "A3 \<noteq> P"
            using "2" \<open>Col A1 A2 A3 \<and> P Q TS C1 A3\<close> by auto 
          have "A3 \<noteq> Q"
            using \<open>\<not> Col A3 P Q\<close> col_trivial_3 by blast 
          have "C1 \<noteq> A3"
            using \<open>Col A1 A2 A3 \<and> P Q TS C1 A3\<close> ts_distincts by blast 
          have "Q A3 Perp P Q"
          proof -
            have "A1 A2 Perp P Q"
              using \<open>A1 A2 Perp P Q\<close> by blast 
            moreover
            have "Q \<noteq> A3"
              using \<open>\<not> Col A3 P Q\<close> col_trivial_3 by blast
            moreover
            have "Col A1 A2 Q"
              using NCol_cases P1B by blast
            moreover
            have "Col A1 A2 A3"
              using \<open>Col A1 A2 A3 \<and> P Q TS C1 A3\<close> by blast 
            ultimately
            show ?thesis
              using perp_col2 by blast 
          qed
          hence "Per A3 Q P"
            by (simp add: perp_per_1) 
          moreover
          have "C1 P Q CongA A3 Q P"
          proof -
            have "P Q TS C1 A3"
              by (simp add: \<open>Col A1 A2 A3 \<and> P Q TS C1 A3\<close>) 
            moreover
            have "P C1 Par Q A3" 
            proof -
              have "P \<noteq> C1"
                by (simp add: \<open>P \<noteq> C1\<close>) 
              moreover 
              have "Q \<noteq> A3"
                using \<open>\<not> Col A3 P Q\<close> col_trivial_3 by blast 
              moreover
              have "C1 C2 Par A1 A2"
                by (simp add: "5" par_symmetry) 
              moreover
              have "Col C1 C2 P"
                by (simp add: "6" col_permutation_1) 
              moreover
              have "Col C1 C2 C1"
                by (simp add: col_trivial_3) 
              moreover
              have "Col A1 A2 Q"
                using NCol_cases P1B by blast 
              moreover
              have "Col A1 A2 A3"
                by (simp add: \<open>Col A1 A2 A3 \<and> P Q TS C1 A3\<close>) 
              ultimately
              show ?thesis
                using par_col4__par by blast 
            qed
            ultimately
            show ?thesis 
              using assms(1) alternate_interior_angles_postulate_def by blast 
          qed
          hence "A3 Q P CongA C1 P Q"
            by (simp add: conga_sym) 
          ultimately
          show ?thesis 
            using l11_17 by blast 
        qed
        hence "P C1 Perp P Q"
          using \<open>P \<noteq> C1\<close> \<open>P \<noteq> Q\<close> per_perp perp_left_comm by auto 
        moreover
        have "P B3 Perp P Q" 
        proof -
          have "B1 B2 Perp P Q"
            by (simp add: \<open>B1 B2 Perp P Q\<close>) 
          moreover
          have "P \<noteq> B3"
            using \<open>B3 \<noteq> P\<close> by fastforce 
          moreover
          have "Col B1 B2 P"
            using "3" not_col_permutation_2 by blast 
          moreover
          have "Col B1 B2 B3"
            using P4A by auto 
          ultimately
          show ?thesis 
            using perp_col2 by blast
        qed
        moreover
        have "Coplanar P Q C1 B3" 
          using P1D P4A 2 3 4 5 6 alternate_interior__playfair_aux_2 
            \<open>A1 A2 ParStrict B1 B2\<close> by blast
        ultimately
        show ?thesis 
          using cop_perp2__col by blast
      qed
      thus ?thesis
        using "3" P4 colx not_col_permutation_1 by blast 
    qed
  }
  thus ?thesis by blast
qed

lemma alternate_interior__playfair_bis:
  assumes "alternate_interior_angles_postulate"
  shows "alternative_playfair_s_postulate" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume 1: "P Perp2 A1 A2 B1 B2" and 
      2: "\<not> Col A1 A2 P" and
      3: "Col P B1 B2" and
      4: "Coplanar A1 A2 B1 B2" and
      5: "A1 A2 Par C1 C2" and
      6: "Col P C1 C2"
    have "Col C1 B1 B2" 
      using alternate_interior__playfair_aux assms(1) 1 2 3 4 5 6 
      by blast
    moreover
    have "Col C2 B1 B2" 
      using alternate_interior__playfair_aux assms(1) 1 2 3 4 5 6 
      by (meson col_permutation_5 par_right_comm) 
    ultimately
    have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
      by blast
  }
  thus ?thesis
    using alternative_playfair_s_postulate_def by blast 
qed

lemma alternate_interior__proclus_aux:
  assumes "greenberg_s_axiom" and
    "alternate_interior_angles_postulate"
  shows "\<forall> A C D P Q. (P A ParStrict C D \<and> C D Perp P C \<and> 
                         P A OS C Q \<and> P C OS Q A \<and> P C OS Q D)
                        \<longrightarrow>
                        (\<exists> Y. Col P Q Y \<and> Col C D Y)"
proof -
  {
    fix A C D P Q
    assume 1: "P A ParStrict C D" and
      2: "C D Perp P C" and 
      3: "P A OS C Q" and
      4: "P C OS Q A" and
      5: "P C OS Q D"
    obtain D' where P1: "Bet D C D' \<and> Cong D C C D'"
      using Cong_perm segment_construction by blast
    hence "Bet D C D'"
      by blast 
    have "Cong D C C D'"
      using P1 by blast 
    have "C \<noteq> D"
      using "1" par_strict_neq2 by auto 
    have "C \<noteq> D'"
      using \<open>C \<noteq> D\<close> \<open>Cong D C C D'\<close> cong_identity by blast 
    have "P \<noteq> Q"
      using "3" col124__nos col_trivial_3 by blast 
    have "P \<noteq> A"
      using "3" col124__nos not_col_distincts by blast 
    have "\<not> Col P A Q"
      using "3" one_side_not_col124 by auto
    have "\<not> Col P C Q"
      using "4" one_side_not_col123 by auto
    have "\<not> Col P C D"
      using "5" one_side_not_col124 by blast 
    have "A P Q LtA A P C"
      by (meson "3" "4" col_permutation_3 col_permutation_5 
          inangle__lta l9_2 l9_9 one_side_not_col123 os_ts__inangle 
          two_sides_cases)
    have "P C OS D A"
      using "4" "5" one_side_symmetry one_side_transitivity by blast
    have "Per A P C" 
    proof -
      have "Per P C D'"
        using "2" P1 Perp_cases \<open>C \<noteq> D'\<close> bet_col bet_col1 
          perp_col2_bis perp_per_2 by blast 
      moreover
      have "P C D' CongA A P C" 
      proof -
        have "P C TS D D'"
          by (simp add: \<open>Bet D C D'\<close> \<open>C \<noteq> D'\<close> \<open>\<not> Col P C D\<close> 
              bet__ts invert_two_sides not_col_permutation_4) 
        hence "P C TS A D'"
          using \<open>P C OS D A\<close> l9_8_2 by blast 
        moreover
        have "P A Par C D'"
          by (meson "1" Par_def \<open>Bet D C D'\<close> \<open>C \<noteq> D'\<close> bet_col
              bet_col1 par_strict_col2_par_strict par_strict_right_comm) 
        ultimately
        show ?thesis
          using alternate_interior_angles_postulate_def assms(2) 
            conga_left_comm conga_sym by blast 
      qed
      ultimately
      show ?thesis
        using l11_17 by blast 
    qed
    hence "Acute A P Q" 
      using \<open>A P Q LtA A P C\<close> Acute_def by blast 
    have "\<not> Col A P Q"
      by (simp add: \<open>\<not> Col P A Q\<close> not_col_permutation_4) 
    have "Per P C D"
      using "2" Perp_perm perp_per_1 by blast 
    then obtain S where P2: "P S C LtA A P Q \<and> C Out S D" 
      using \<open>Acute A P Q\<close> \<open>\<not> Col A P Q\<close> \<open>C \<noteq> D\<close> assms(1) 
        greenberg_s_axiom_def by blast 
    hence "P S C LtA A P Q" 
      by blast
    have "C Out S D"
      using P2 by blast
    have "P C OS S D"
      using \<open>C Out S D\<close> \<open>\<not> Col P C D\<close> col_permutation_4 
        invert_one_side out_one_side by blast
    have "Q InAngle C P S" 
    proof -
      have "P C OS S Q"
        using "5" \<open>P C OS S D\<close> one_side_symmetry 
          one_side_transitivity by blast 
      moreover
      have "P S OS C Q" 
      proof -
        have "P C OS S A"
          using "4" calculation one_side_transitivity by blast
        hence "P A ParStrict S C"
          by (metis "1" Out_cases \<open>C Out S D\<close> os_distincts 
              out_col par_strict_col_par_strict par_strict_comm 
              par_strict_left_comm)
        hence "P S TS C A"
          by (simp add: \<open>P C OS S A\<close> l12_6 l9_31) 
        moreover
        have "A P S CongA C S P"
          using assms(2) alternate_interior_angles_postulate_def 
          by (meson par_strict_par \<open>P A ParStrict S C\<close> calculation l9_2) 
        have "A P S LtA A P Q" 
          using conga_preserves_lta 
          by (metis \<open>A P S CongA C S P\<close> \<open>P S C LtA A P Q\<close> 
              \<open>P \<noteq> A\<close> \<open>P \<noteq> Q\<close> conga_right_comm conga_sym 
              nlta or_lta2_conga)
        hence P4: "A P S LeA A P Q \<and> \<not> A P S CongA A P Q"
          using lta__lea not_lta_and_conga by auto 
        hence "A P S LeA A P Q"
          by blast
        have "\<not> A P S CongA A P Q"
          using P4 by blast
        have "P S TS Q A" 
        proof -
          {
            assume "Col P Q S"
            have "P C OS Q S"
              by (simp add: \<open>P C OS S Q\<close> one_side_symmetry) 
            hence "P Out Q S"
              using \<open>Col P Q S\<close> col_one_side_out by blast 
            have "P Out A A"
              using \<open>P \<noteq> A\<close> out_trivial by auto 
            hence "False" 
              using out2__conga \<open>P Out Q S\<close> \<open>\<not> A P S CongA A P Q\<close> by blast 
          }
          hence "\<not> Col P Q S" 
            by auto
          moreover
          have "A P OS Q S"
            using "3" \<open>P C OS S A\<close> \<open>P S TS C A\<close> invert_one_side 
              one_side_symmetry one_side_transitivity 
              os_ts1324__os by blast 
          hence "S InAngle Q P A" 
            using l11_24 lea_in_angle \<open>A P S LeA A P Q\<close> by blast 
          ultimately
          show ?thesis
            by (metis NCol_cases TS_def \<open>P S TS C A\<close> in_angle_two_sides) 
        qed
        ultimately
        show ?thesis
          using l9_8_1 by blast
      qed
      ultimately
      show ?thesis
        using os2__inangle by blast 
    qed
    then obtain Y where P3: "Bet C Y S \<and> (Y = P \<or> P Out Y Q)"
      using InAngle_def by auto
    hence "Bet C Y S"
      by blast
    have "Y = P \<or> P Out Y Q"
      using P3 by blast
    have P4: "Col P Q Y"
      using \<open>Y = P \<or> P Out Y Q\<close> col_permutation_5 col_trivial_3 out_col by blast 
    have "Col C D Y"
      by (meson Bet_cases Col_def Out_def \<open>Bet C Y S\<close> 
          \<open>C Out S D\<close> bet_col1 between_exchange4) 
    hence "\<exists> Y. Col P Q Y \<and> Col C D Y" 
      using P4 by blast
  }
  thus ?thesis by blast
qed

lemma alternate_interior__proclus:
  assumes "greenberg_s_axiom" and
    "alternate_interior_angles_postulate"
  shows "proclus_postulate"
proof -
  {
    fix A B C D P Q
    assume 1: "A B Par C D" and
      2: "Col A B P" and
      3: "\<not> Col A B Q" and 
      4: "Coplanar C D P Q"
    have "Col C D P \<longrightarrow> (\<exists> Y. Col P Q Y \<and> Col C D Y)"
      using col_trivial_3 by blast 
    moreover
    {
      assume "\<not> Col C D P"
      hence "A B ParStrict C D"
        using "1" "2" par_not_col_strict par_strict_symmetry par_symmetry by blast 
      obtain C0 where P4: "Col C D C0 \<and> C D Perp P C0" 
        using l8_18_existence \<open>\<not> Col C D P\<close> by blast 
      have "Col P Q C0 \<longrightarrow> (\<exists> Y. Col P Q Y \<and> Col C D Y)"
        using \<open>Col C D C0 \<and> C D Perp P C0\<close> by blast 
      moreover
      {
        assume "\<not> Col P Q C0"
        have "\<exists> Q1. Col Q P Q1 \<and> A B OS C0 Q1" 
        proof -
          have "Q \<noteq> P"
            using "2" "3" by blast 
          moreover
          have "Col A B P"
            by (simp add: "2") 
          moreover
          have "Col Q P P"
            by (simp add: col_trivial_2) 
          moreover
          have "\<not> Col A B Q"
            by (simp add: "3") 
          moreover
          have "\<not> Col C0 A B"
          proof -
            have "C D ParStrict A B"
              by (simp add: \<open>A B ParStrict C D\<close> par_strict_symmetry) 
            moreover
            have "Col C0 C D"
              by (simp add: \<open>Col C D C0 \<and> C D Perp P C0\<close> col_permutation_2) 
            ultimately
            show ?thesis
              using par_not_col by blast 
          qed
          hence "\<not> Col A B C0"
            using col_permutation_2 by blast 
          moreover
          have "Coplanar A B Q C0" 
          proof -
            have "Coplanar C D P A"
              using "1" "2" col_trivial_3 ncop_distincts 
                par__coplanar par_col2_par par_symmetry by blast 
            moreover
            have "Coplanar C D P B"
              using "1" "2" Col_cases Par_cases calculation 
                col_cop__cop par__coplanar by blast
            moreover
            have "Coplanar C D P C0"
              using \<open>Col C D C0 \<and> C D Perp P C0\<close> ncop__ncols by blast 
            ultimately
            show ?thesis
              using \<open>\<not> Col C D P\<close> 4 coplanar_pseudo_trans by blast 
          qed
          ultimately
          show ?thesis
            using cop_not_par_same_side by blast 
        qed
        then obtain Q1 where P5: "Col Q P Q1 \<and> A B OS C0 Q1"
          by blast
        hence "Col Q P Q1"
          by blast
        have "A B OS C0 Q1"
          using P5 by blast
        have "P \<noteq> Q1"
          using "2" P5 one_side_not_col124 by blast
        have "\<not> Col P C0 Q1"
          by (metis \<open>Col Q P Q1\<close> \<open>P \<noteq> Q1\<close> \<open>\<not> Col P Q C0\<close> 
              col_permutation_1 col_transitivity_1)
        have "\<exists> A1. Col A B A1 \<and> P C0 OS Q1 A1" 
        proof -
          {
            assume "Col P C0 A"
            have "?thesis" 
            proof -
              have "B \<noteq> A"
                using "3" col_trivial_1 by blast
              moreover
              have "Col P C0 P"
                by (simp add: col_trivial_3) 
              moreover
              have "Col B A P"
                by (simp add: "2" col_permutation_4) 
              moreover
              have "\<not> Col P C0 B"
                by (metis P5 \<open>Col P C0 A\<close> \<open>\<not> Col P C0 Q1\<close> 
                    col_permutation_4 col_transitivity_1 not_col_distincts 
                    one_side_not_col123) 
              moreover
              have "\<not> Col P C0 Q1"
                by (simp add: \<open>\<not> Col P C0 Q1\<close>) 
              moreover
              have "Coplanar P C0 B Q1"
                by (metis P5 \<open>Col P C0 A\<close> calculation(2) calculation(3) 
                    calculation(4) calculation(5) col_trivial_2 l6_21 
                    ncoplanar_perm_5 ts__coplanar two_sides_cases) 
              ultimately
              show ?thesis
                using NCol_perm cop_not_par_same_side by blast 
            qed
          }
          moreover
          {
            assume "\<not> Col P C0 A"

            have "?thesis" 
            proof -
              have "B \<noteq> A"
                using "3" col_trivial_1 by blast
              moreover
              have "Col P C0 P"
                by (simp add: col_trivial_3) 
              moreover
              have "Col A B P"
                by (simp add: "2")
              moreover
              have "\<not> Col P C0 A"
                by (simp add: \<open>\<not> Col P C0 A\<close>)
              moreover
              have "\<not> Col P C0 Q1"
                using \<open>\<not> Col P C0 Q1\<close> by auto
              moreover
              have "Coplanar P C0 A Q1"
                by (metis "2" P5 calculation(4) calculation(5) 
                    col_one_side invert_one_side ncoplanar_perm_5 not_col_distincts
                    ts__coplanar two_sides_cases)
              ultimately
              show ?thesis
                using cop_not_par_same_side by auto
            qed
          }
          ultimately
          show ?thesis
            by blast 
        qed
        then obtain A1 where P6: "Col A B A1 \<and> P C0 OS Q1 A1" 
          by blast
        hence "Col A B A1" 
          by blast
        have "P C0 OS Q1 A1"
          using P6 by blast
        have "\<exists> C1. Col C D C1 \<and> P C0 OS Q1 C1"
        proof -
          have "Coplanar C D P Q1"
            using "4" \<open>Col Q P Q1\<close> \<open>\<not> Col P Q C0\<close> col_cop__cop 
              col_permutation_4 not_col_distincts by blast
          have "P C0 Perp C D"
            using Perp_perm \<open>Col C D C0 \<and> C D Perp P C0\<close> by blast
          moreover
          {
            assume "\<not> Col P C0 C"
            have "C \<noteq> D"
              using "1" par_neq2 by auto 
            moreover
            have "Col P C0 C0"
              by (simp add: col_trivial_2) 
            moreover
            have "Col C D C0" 
              using P4 by blast
            moreover
            have "\<not> Col P C0 C"
              by (simp add: \<open>\<not> Col P C0 C\<close>) 
            moreover
            have "\<not> Col P C0 Q1"
              by (simp add: \<open>\<not> Col P C0 Q1\<close>) 
            moreover
            have "Coplanar P C0 C Q1"
              using \<open>Coplanar C D P Q1\<close> calculation(1) calculation(3) 
                col2_cop__cop col_trivial_3 ncoplanar_perm_17 
                ncoplanar_perm_18 by blast 
            ultimately
            have "?thesis"
              using cop_not_par_same_side by blast 
          }
          moreover
          {
            assume "\<not> Col P C0 D"
            have "D \<noteq> C"
              using "1" par_distinct by blast 
            moreover
            have "Col P C0 C0"
              by (simp add: col_trivial_2)
            moreover
            have "Col D C C0" 
              using P4 Col_perm by blast 
            moreover
            have "\<not> Col P C0 D"
              by (simp add: \<open>\<not> Col P C0 D\<close>) 
            moreover
            have "\<not> Col P C0 Q1"
              by (simp add: \<open>\<not> Col P C0 Q1\<close>) 
            moreover
            have "Coplanar P C0 D Q1"
              using \<open>Coplanar C D P Q1\<close> calculation(1) 
                calculation(3) col_cop__cop ncoplanar_perm_22 
                ncoplanar_perm_5 by blast 
            ultimately
            have "?thesis" 
              using NCol_perm cop_not_par_same_side by blast
          }
          ultimately
          show ?thesis
            using perp_not_col2 by blast 
        qed
        then obtain C1 where P7: "Col C D C1 \<and> P C0 OS Q1 C1"
          by blast
        hence "Col C D C1" 
          by blast
        have "P C0 OS Q1 C1"
          using P7 by blast
        have "C0 \<noteq> C1"
          using \<open>P C0 OS Q1 C1\<close> col_trivial_2 one_side_not_col124 by blast 
        have "P \<noteq> A1"
          using \<open>P C0 OS Q1 A1\<close> col_trivial_3 one_side_not_col124 by blast 
        have "\<exists> Y. Col P Q Y \<and> Col C D Y"  
        proof -
          have "P A1 ParStrict C0 C1" 
          proof -
            have "P \<noteq> A1"
              by (simp add: \<open>P \<noteq> A1\<close>) 
            moreover
            have "C0 \<noteq> C1"
              using \<open>C0 \<noteq> C1\<close> by blast 
            moreover
            have "A B ParStrict C D"
              using \<open>A B ParStrict C D\<close> by auto 
            moreover
            have "Col A B P"
              by (simp add: "2") 
            moreover
            have "Col A B A1"
              by (simp add: \<open>Col A B A1\<close>) 
            moreover
            have "Col C D C0" 
              using P4 by blast 
            moreover
            have "Col C D C1"
              by (simp add: \<open>Col C D C1\<close>) 
            moreover
            have "C0 C1 Perp P C0" 
            proof -
              have "C D Perp P C0"
                by (simp add: P4) 
              moreover
              have "C0 \<noteq> C1"
                by (simp add: \<open>C0 \<noteq> C1\<close>) 
              moreover
              have "Col C D C0"
                by (simp add: \<open>Col C D C0\<close>) 
              moreover
              have "Col C D C1"
                by (simp add: \<open>Col C D C1\<close>) 
              ultimately
              show ?thesis
                by (meson perp_col2) 
            qed
            moreover
            have "P A1 OS C0 Q1"
              using "2" P5 P6 calculation(1) col2_os__os by blast 
            ultimately
            show ?thesis 
              using par_strict_col4__par_strict P6 by blast 
          qed
          moreover
          have "C0 C1 Perp P C0" 
          proof -
            have "C D Perp P C0"
              by (simp add: P4) 
            moreover
            have "C0 \<noteq> C1"
              by (simp add: \<open>C0 \<noteq> C1\<close>) 
            moreover
            have "Col C D C0"
              using P4 by blast
            moreover
            have "Col C D C1"
              by (simp add: \<open>Col C D C1\<close>) 
            ultimately
            show ?thesis
              by (meson perp_col2) 
          qed
          moreover
          have "P A1 OS C0 Q1"
            using "2" P5 P6 \<open>P \<noteq> A1\<close> col2_os__os by blast 
          moreover
          have "P C0 OS Q1 A1"
            by (simp add: \<open>P C0 OS Q1 A1\<close>) 
          moreover
          have "P C0 OS Q1 C1"
            by (simp add: \<open>P C0 OS Q1 C1\<close>) 
          ultimately
          have "\<exists> Y. Col P Q1 Y \<and> Col C0 C1 Y"
            using alternate_interior__proclus_aux assms(1) assms(2)
            by blast
          then obtain Y1 where "Col P Q1 Y1" and "Col C0 C1 Y1"
            by blast
          hence "Col P Q1 Y1" 
            by blast
          hence "Col P Q Y1"
            using NCol_cases \<open>Col Q P Q1\<close> \<open>P \<noteq> Q1\<close> col_transitivity_1 by blast 
          moreover
          have "Col C D Y1" 
            using P4 \<open>C0 \<noteq> C1\<close> \<open>Col C D C1\<close> \<open>Col C0 C1 Y1\<close> colx by blast
          ultimately show ?thesis  
            by blast
        qed
      }
      ultimately
      have "\<exists> Y. Col P Q Y \<and> Col C D Y"
        by blast 
    }
    ultimately
    have "\<exists> Y. Col P Q Y \<and> Col C D Y" 
      by blast
  }
  thus ?thesis
    using proclus_postulate_def by blast 
qed

lemma alternate_interior__triangle:
  assumes "alternate_interior_angles_postulate"
  shows "triangle_postulate" 
proof -
  {
    fix A B C D E F
    assume "A B C TriSumA D E F"
    have "Bet D E F" 
    proof -
      have "Col A B C \<longrightarrow> ?thesis" 
        using col_trisuma__bet by (simp add: \<open>A B C TriSumA D E F\<close>) 
      moreover
      {
        assume "\<not> Col A B C"
        have "\<exists> B1. B C A CongA C B B1 \<and> C B TS B1 A"
        proof -
          have "\<not> Col B C A"
            by (simp add: \<open>\<not> Col A B C\<close> not_col_permutation_1) 
          moreover
          have "\<not> Col C B A"
            by (simp add: \<open>\<not> Col A B C\<close> not_col_permutation_3) 
          ultimately
          show ?thesis
            by (simp add: ex_conga_ts) 
        qed
        then obtain B1 where P1: "B C A CongA C B B1 \<and> C B TS B1 A"
          by blast
        hence "B C A CongA C B B1" 
          by blast
        have "C B TS B1 A"
          using P1 by blast
        have "A C Par B B1"
          using P1 conga_comm l12_21_b l9_2 par_left_comm by blast
        hence "A C ParStrict B B1"
          using NCol_cases \<open>\<not> Col A B C\<close> col_trivial_3 par_not_col_strict by blast
        have "\<not> Col C B B1"
          using \<open>A C ParStrict B B1\<close> par_strict_not_col_2 by auto
        have "\<not> Col A B B1"
          using \<open>A C ParStrict B B1\<close> col_permutation_1 par_strict_not_col_3 by blast
        obtain B2 where P2: "Bet B1 B B2 \<and> Cong B1 B B B2"
          using Cong_perm segment_construction by blast
        hence "Bet B1 B B2" 
          by blast
        have "Cong B1 B B B2" 
          using P2 by blast
        have "A \<noteq> B"
          using \<open>\<not> Col A B B1\<close> col_trivial_1 by blast 
        have "B \<noteq> B1"
          using \<open>\<not> Col C B B1\<close> col_trivial_2 by blast
        have "C \<noteq> B"
          using \<open>\<not> Col A B C\<close> col_trivial_2 by auto 
        have "B2 \<noteq> B1"
          using \<open>B \<noteq> B1\<close> \<open>Bet B1 B B2\<close> between_identity by blast 
        have "B \<noteq> B2"
          using \<open>B2 \<noteq> B1\<close> \<open>Cong B1 B B B2\<close> cong_identity by blast 
        have "B A TS B1 B2"
          using \<open>B \<noteq> B2\<close> \<open>Bet B1 B B2\<close> \<open>\<not> Col A B B1\<close> bet__ts col_permutation_4 by blast
        obtain D1 E1 F1 where P3: "A B C B C A SumA D1 E1 F1 \<and> D1 E1 F1 C A B SumA D E F"
          using TriSumA_def \<open>A B C TriSumA D E F\<close> by blast 
        hence "A B C B C A SumA D1 E1 F1"
          by blast
        have "D1 E1 F1 C A B SumA D E F"
          using P3 by blast
        have "B1 B B2 CongA D E F"
        proof -
          have "D1 E1 F1 C A B SumA B1 B B2" 
          proof -
            have "B1 B A A B B2 SumA B1 B B2"
              by (simp add: \<open>B A TS B1 B2\<close> ts__suma_1) 
            moreover
            have "B1 B A CongA D1 E1 F1" 
            proof -
              have "A B C B C A SumA B1 B A" 
              proof -
                have "A B C C B B1 SumA A B B1"
                  by (simp add: \<open>C B TS B1 A\<close> l9_2 ts__suma) 
                moreover
                have "A B C CongA A B C"
                  by (simp add: \<open>A \<noteq> B\<close> \<open>C \<noteq> B\<close> conga_refl) 
                moreover
                have "C B B1 CongA B C A" 
                  using \<open>B C A CongA C B B1\<close> not_conga_sym by blast
                moreover
                have "A B B1 CongA B1 B A"
                  using \<open>A \<noteq> B\<close> \<open>B \<noteq> B1\<close> conga_pseudo_refl by auto 
                ultimately
                show ?thesis
                  using conga3_suma__suma by blast 
              qed
              moreover
              have "A B C B C A SumA D1 E1 F1"
                by (simp add: \<open>A B C B C A SumA D1 E1 F1\<close>) 
              ultimately
              show ?thesis
                using suma2__conga by blast 
            qed
            moreover
            have "A B B2 CongA C A B" 
            proof -
              have "B A TS B2 C"
                by (metis Par_cases \<open>A C Par B B1\<close> \<open>B A TS B1 B2\<close> \<open>C B TS B1 A\<close> 
                    invert_two_sides l9_2 l9_8_2 par_two_sides_two_sides ts_ts_os) 
              moreover
              have "B B2 Par A C"
                by (metis Par_perm \<open>A C Par B B1\<close> \<open>B \<noteq> B2\<close> \<open>Bet B1 B B2\<close> 
                    bet_col bet_col1 par_col2_par) 
              ultimately
              show ?thesis
                using conga_left_comm alternate_interior_angles_postulate_def assms by blast 
            qed
            moreover
            have "B1 B B2 CongA B1 B B2"
              using \<open>B \<noteq> B1\<close> \<open>B \<noteq> B2\<close> conga_refl by auto
            ultimately
            show ?thesis
              using conga3_suma__suma by blast 
          qed
          moreover
          have "D1 E1 F1 C A B SumA D E F"
            by (simp add: P3) 
          ultimately
          show ?thesis
            using suma2__conga by blast 
        qed
        hence ?thesis
          using P2 bet_conga__bet by blast 
      }
      ultimately
      show ?thesis
        by blast 
    qed
  }
  thus ?thesis
    using triangle_postulate_def by blast 
qed

lemma bachmann_s_lotschnittaxiom_aux_R1:
  assumes "bachmann_s_lotschnittaxiom"
  shows "\<forall> A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD.
 IAB \<noteq> IAC \<and> IAB \<noteq> IBD \<and>
  A1 A2 Perp B1 B2 \<and> 
A1 A2 Perp C1 C2 \<and> 
B1 B2 Perp D1 D2 \<and>
  Col A1 A2 IAB \<and>
 Col B1 B2 IAB \<and> Col A1 A2 IAC \<and>
  Col C1 C2 IAC \<and> Col B1 B2 IBD \<and> Col D1 D2 IBD \<and>
  Coplanar IAB IAC IBD C1 \<and> 
Coplanar IAB IAC IBD C2 \<and>
  Coplanar IAB IAC IBD D1 \<and> Coplanar IAB IAC IBD D2 \<longrightarrow>
  (\<exists> I. Col C1 C2 I \<and> Col D1 D2 I)" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD
    assume 1: "IAB \<noteq> IAC" and
      2: "IAB \<noteq> IBD" and
      3: "A1 A2 Perp B1 B2" and
      4: "A1 A2 Perp C1 C2" and
      5: "B1 B2 Perp D1 D2" and
      6: "Col A1 A2 IAB" and
      7: "Col B1 B2 IAB" and
      8: "Col A1 A2 IAC" and
      9: "Col C1 C2 IAC" and
      10: "Col B1 B2 IBD" and
      11: "Col D1 D2 IBD" and
      12: "Coplanar IAB IAC IBD C1" and
      13: "Coplanar IAB IAC IBD C2" and
      14: "Coplanar IAB IAC IBD D1" and
      15: "Coplanar IAB IAC IBD D2"
    have "Col IAB IAC A1"
      using "4" "6" "8" col_transitivity_1 not_col_permutation_3 perp_distinct by blast
    have "Col IAB IAC A2"
      using "4" "6" "8" col_permutation_3 col_transitivity_2 perp_distinct by blast
    have "Col IAB IBD B1"
      using "10" "5" "7" col_transitivity_1 not_col_permutation_2 perp_not_eq_1 by blast 
    have "Col IAB IBD B2"
      using "10" "5" "7" Col_perm col_transitivity_2 perp_distinct by blast
    have "Coplanar IAB IAC IBD A1"
      using \<open>Col IAB IAC A1\<close> ncop__ncols by blast 
    have "Coplanar IAB IAC IBD A2"
      using \<open>Col IAB IAC A2\<close> ncop__ncols by blast
    have "Coplanar IAB IAC IBD B1"
      using \<open>Col IAB IBD B1\<close> ncop__ncols by blast
    have "Coplanar IAB IAC IBD B2"
      using \<open>Col IAB IBD B2\<close> ncop__ncols by blast
    have "IAB IAC Perp IBD IAB"
      using perp_col4 1 "2" "3" 6 7 8 10 by auto 
    hence H1: "Per IAC IAB IBD" 
      using perp_per_1 "1" l8_8 by blast
    have "\<not> Col IAC IAB IBD" 
      using per_not_col "1" "2" \<open>Per IAC IAB IBD\<close> by auto 
    have "\<not> Col A1 A2 IBD"
      using "6" "8" col3 par_neq1 "4" \<open>\<not> Col IAC IAB IBD\<close> perp_distinct by fastforce 
    have "A1 A2 ParStrict D1 D2"
    proof -
      have "A1 A2 Par D1 D2" 
      proof -
        have "Coplanar B1 B2 A1 D1"
        proof -
          have "Coplanar IAB IAC IBD B1"
            by (simp add: \<open>Coplanar IAB IAC IBD B1\<close>) 
          moreover
          have "Coplanar IAB IAC IBD B2"
            by (simp add: \<open>Coplanar IAB IAC IBD B2\<close>) 
          moreover
          have "Coplanar IAB IAC IBD A1"
            using \<open>Coplanar IAB IAC IBD A1\<close> by force
          moreover
          have "Coplanar IAB IAC IBD D1"
            using "14" by blast
          ultimately
          show ?thesis
            by (meson \<open>\<not> Col IAC IAB IBD\<close> coplanar_perm_6 coplanar_pseudo_trans) 
        qed
        moreover
        have "Coplanar B1 B2 A1 D2" 
          using coplanar_pseudo_trans not_par_not_col par_id_1 
          by (meson "15" \<open>Coplanar IAB IAC IBD A1\<close> \<open>Coplanar IAB IAC IBD B1\<close> 
              \<open>Coplanar IAB IAC IBD B2\<close> \<open>\<not> Col IAC IAB IBD\<close> not_col_permutation_4)
        moreover
        have "Coplanar B1 B2 A2 D1"
        proof -
          have "Coplanar IAB IAC IBD B1"
            by (simp add: \<open>Coplanar IAB IAC IBD B1\<close>) 
          moreover
          have "Coplanar IAB IAC IBD B2"
            by (simp add: \<open>Coplanar IAB IAC IBD B2\<close>) 
          moreover
          have "Coplanar IAB IAC IBD A2"
            using \<open>Coplanar IAB IAC IBD A2\<close> by blast 
          moreover
          have "Coplanar IAB IAC IBD D1"
            using "14" by blast
          ultimately
          show ?thesis
            by (meson \<open>\<not> Col IAC IAB IBD\<close> coplanar_perm_6 coplanar_pseudo_trans) 
        qed
        moreover
        have "Coplanar B1 B2 A2 D2" 
        proof -
          have "Coplanar IAB IAC IBD B1"
            by (simp add: \<open>Coplanar IAB IAC IBD B1\<close>) 
          moreover
          have "Coplanar IAB IAC IBD B2"
            by (simp add: \<open>Coplanar IAB IAC IBD B2\<close>) 
          moreover
          have "Coplanar IAB IAC IBD A2"
            using \<open>Coplanar IAB IAC IBD A2\<close> by blast 
          moreover
          have "Coplanar IAB IAC IBD D2"
            using "15" by blast 
          ultimately
          show ?thesis
            by (meson \<open>\<not> Col IAC IAB IBD\<close> coplanar_perm_6 coplanar_pseudo_trans)
        qed
        moreover 
        have "A1 A2 Perp B1 B2"
          by (simp add: "3") 
        moreover
        have "D1 D2 Perp B1 B2"
          using "5" Perp_perm by blast 
        ultimately
        show ?thesis
          using l12_9 by blast 
      qed
      moreover
      have "Col D1 D2 IBD"
        by (simp add: "11") 
      moreover
      have "\<not> Col A1 A2 IBD"
        using "6" "8" \<open>\<not> Col IAC IAB IBD\<close> calculation(1) col3 par_neq1 by blast 
      ultimately
      show ?thesis
        using par_not_col_strict by blast 
    qed
    have Q1: "B1 B2 ParStrict C1 C2"
    proof -
      have "B1 B2 Par C1 C2" 
      proof -
        have "Coplanar A1 A2 B1 C1"
        proof -
          have "Coplanar IAB IAC IBD A1"
            by (simp add: \<open>Coplanar IAB IAC IBD A1\<close>)
          moreover
          have "Coplanar IAB IAC IBD A2"
            by (simp add: \<open>Coplanar IAB IAC IBD A2\<close>)
          moreover
          have "Coplanar IAB IAC IBD B1"
            using \<open>Coplanar IAB IAC IBD B1\<close> by blast
          moreover
          have "Coplanar IAB IAC IBD C1"
            using "12" by blast
          ultimately
          show ?thesis
            by (meson \<open>\<not> Col IAC IAB IBD\<close> coplanar_perm_6 coplanar_pseudo_trans) 
        qed
        moreover
        have "Coplanar A1 A2 B1 C2" 
        proof -
          have "Coplanar IAB IAC IBD A1"
            by (simp add: \<open>Coplanar IAB IAC IBD A1\<close>)
          moreover
          have "Coplanar IAB IAC IBD A2"
            by (simp add: \<open>Coplanar IAB IAC IBD A2\<close>)
          moreover
          have "Coplanar IAB IAC IBD B1"
            by (simp add: \<open>Coplanar IAB IAC IBD B1\<close>)
          moreover
          have "Coplanar IAB IAC IBD C2"
            by (simp add: "13")
          ultimately
          show ?thesis
            by (meson \<open>\<not> Col IAC IAB IBD\<close> coplanar_perm_6 coplanar_pseudo_trans) 
        qed
        moreover
        have "Coplanar A1 A2 B2 C1"
        proof -
          have "Coplanar IAB IAC IBD A1"
            by (simp add: \<open>Coplanar IAB IAC IBD A1\<close>)
          moreover
          have "Coplanar IAB IAC IBD A2"
            by (simp add: \<open>Coplanar IAB IAC IBD A2\<close>)
          moreover
          have "Coplanar IAB IAC IBD B2"
            by (simp add: \<open>Coplanar IAB IAC IBD B2\<close>)
          moreover
          have "Coplanar IAB IAC IBD C1"
            using "12" by blast
          ultimately
          show ?thesis
            by (meson \<open>\<not> Col IAC IAB IBD\<close> coplanar_perm_6 coplanar_pseudo_trans) 
        qed
        moreover
        have "Coplanar A1 A2 B2 C2" 
        proof -
          have "Coplanar IAB IAC IBD A1"
            by (simp add: \<open>Coplanar IAB IAC IBD A1\<close>) 
          moreover
          have "Coplanar IAB IAC IBD A2"
            by (simp add: \<open>Coplanar IAB IAC IBD A2\<close>) 
          moreover
          have "Coplanar IAB IAC IBD B2"
            using \<open>Coplanar IAB IAC IBD B2\<close> by blast 
          moreover
          have "Coplanar IAB IAC IBD C2"
            using \<open>Coplanar IAB IAC IBD C2\<close> by blast
          ultimately
          show ?thesis
            by (meson \<open>\<not> Col IAC IAB IBD\<close> coplanar_perm_6 coplanar_pseudo_trans)
        qed
        moreover 
        have "B1 B2 Perp A1 A2"
          using 3 Perp_perm by blast
        moreover
        have "C1 C2 Perp A1 A2"
          using 4 Perp_perm by blast 
        ultimately
        show ?thesis 
          using l12_9 by blast
      qed
      moreover
      have "Col C1 C2 IAC"
        using 9 by auto
      moreover
      have "\<not> Col B1 B2 IAC"
        using "10" "7" \<open>\<not> Col IAC IAB IBD\<close> calculation(1) col3 par_neq1 by blast 
      ultimately
      show ?thesis
        using par_not_col_strict by blast  
    qed
    have "IAC \<noteq> IAB"
      using 1 by auto
    have "IAB \<noteq> IBD"
      using 2 by auto
    have "Col C1 C2 IAC" 
      using 9 by auto
    then obtain P1 where P1: "C1 \<noteq> P1 \<and> C2 \<noteq> P1 \<and> IAC \<noteq> P1 \<and> Col C1 C2 P1" 
      using diff_col_ex3 by blast
    hence "C1 \<noteq> P1" 
      by blast
    have "C2 \<noteq> P1"
      using P1 by blast
    have "IAC \<noteq> P1"
      using P1 by blast
    have "Col C1 C2 P1"
      using P1 by blast
    have "Col D1 D2 IBD" 
      by (simp add: "11") 
    then obtain R1 where P2: "D1 \<noteq> R1 \<and> D2 \<noteq> R1 \<and> IBD \<noteq> R1 \<and> Col D1 D2 R1"
      using diff_col_ex3 by blast
    hence "D1 \<noteq> R1"
      by blast
    have "D2 \<noteq> R1"
      using P2 by blast
    have "IBD \<noteq> R1"
      using P2 by blast
    have "Col D1 D2 R1"
      using P2 by blast
    have "IAC \<noteq> IBD"
      using "8" \<open>\<not> Col A1 A2 IBD\<close> by auto 
    have "D1 \<noteq> D2"
      using \<open>A1 A2 ParStrict D1 D2\<close> par_strict_distinct by blast 
    have "C1 \<noteq> C2"
      using Q1 par_strict_neq2 by auto  
    have P3: "C1 \<noteq> Q \<and> Q \<noteq> D1 \<and> Per C1 Q D1 \<and> Per Q C1 C2 \<and>
 Per Q D1 D2 \<and> Coplanar C1 Q D1 C2 \<and> Coplanar C1 Q D1 D2 
\<longrightarrow>
  (\<exists> S. Col C1 C2 S \<and> Col D1 D2 S)"
      using  assms(1) bachmann_s_lotschnittaxiom_def by blast
    have "\<exists> I. Col IAC P1 I \<and> Col IBD R1 I"
    proof -
      have "IAC \<noteq> IAB" 
        using 1 by auto
      moreover
      have "IAB \<noteq> IBD" 
        using 2 by auto
      moreover
      have "Per IAC IAB IBD" 
        using H1 by blast
      moreover
      have "IAC IAB Perp P1 IAC"
      proof -
        have "IAC \<noteq> IAB" 
          using 1 by blast
        moreover
        have "P1 \<noteq> IAC" 
          using P1 by blast
        ultimately
        show ?thesis 
          using 8 6 P1 9 4 perp_col4 by blast
      qed
      hence "Per IAB IAC P1" 
        using perp_per_1 by blast
      moreover
      have "IBD IAB Perp R1 IBD" 
      proof -
        have "IBD \<noteq> IAB" 
          using 2 by auto
        moreover
        have "R1 \<noteq> IBD" 
          using P2 by auto
        ultimately
        show ?thesis
          using 10 7 P2 5 11 perp_col4 by blast
      qed
      hence "Per IAB IBD R1" 
        using perp_per_1 by blast
      moreover
      have "Coplanar IAC IAB IBD P1" 
      proof -
        have "C1 \<noteq> C2" 
          using Q1 par_strict_neq2 by auto  
        moreover
        have "Coplanar IAC IAB IBD C1" 
          using 12 coplanar_perm_6 by blast
        moreover
        have "Coplanar IAC IAB IBD C2" 
          using 13 coplanar_perm_6 by blast
        moreover
        have "Col C1 C2 P1" 
          using P1 by blast
        ultimately
        show ?thesis 
          using col_cop2__cop by blast
      qed
      moreover
      have "Coplanar IAC IAB IBD R1"
        using "14" "15" P2 \<open>D1 \<noteq> D2\<close> col_cop2__cop coplanar_perm_6 by blast 
      ultimately
      show ?thesis 
        using assms(1) bachmann_s_lotschnittaxiom_def by blast
    qed
    then obtain I where P5: "Col IAC P1 I \<and> Col IBD R1 I"
      by auto
    hence "Col IAC P1 I" 
      by blast
    have "Col IBD R1 I" 
      using P5 by blast
    have "Col C1 C2 I"
      using "9" \<open>Col C1 C2 P1\<close> \<open>Col IAC P1 I\<close> \<open>IAC \<noteq> P1\<close> colx by blast
    moreover
    have "Col D1 D2 I"
      using "11" \<open>Col D1 D2 R1\<close> \<open>Col IBD R1 I\<close> \<open>IBD \<noteq> R1\<close> colx by blast 
    ultimately
    have "\<exists> I0. (Col C1 C2 I0 \<and> Col D1 D2 I0)" 
      by blast
  }
  thus ?thesis by blast
qed

lemma bachmann_s_lotschnittaxiom_aux_R2:
  assumes "\<forall> A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD.
 IAB \<noteq> IAC \<and> IAB \<noteq> IBD \<and>
  A1 A2 Perp B1 B2 \<and> 
A1 A2 Perp C1 C2 \<and> 
B1 B2 Perp D1 D2 \<and>
  Col A1 A2 IAB \<and>
 Col B1 B2 IAB \<and> Col A1 A2 IAC \<and>
  Col C1 C2 IAC \<and> Col B1 B2 IBD \<and> Col D1 D2 IBD \<and>
  Coplanar IAB IAC IBD C1 \<and> 
Coplanar IAB IAC IBD C2 \<and>
  Coplanar IAB IAC IBD D1 \<and> Coplanar IAB IAC IBD D2 \<longrightarrow>
  (\<exists> I. Col C1 C2 I \<and> Col D1 D2 I)"
  shows "bachmann_s_lotschnittaxiom"
proof - 
  {
    fix P Q R P1 R1
    assume 1: "P \<noteq> Q" and
      2: "Q \<noteq> R" and
      3: "Per P Q R" and
      4: "Per Q P P1" and
      5: "Per Q R R1" and
      6: "Coplanar P Q R P1" and
      7: "Coplanar P Q R R1"
    have "\<exists> S. Col P P1 S \<and> Col R R1 S"
    proof cases
      assume "P = P1"
      thus ?thesis
        using col_trivial_1 col_trivial_2 by blast
    next
      assume "P \<noteq> P1"
      thus ?thesis
      proof cases
        assume "R = R1"
        thus ?thesis
          using col_trivial_1 col_trivial_2 by blast
      next
        assume "R \<noteq> R1"
        have "Q \<noteq> P"
          using "1" by auto
        moreover
        have "Q \<noteq> R"
          by (simp add: "2") 
        moreover
        have "P Q Perp Q R"
          by (simp add: "1" "2" "3" per_perp) 
        moreover
        have "P Q Perp P P1"
          using "1" "4" \<open>P \<noteq> P1\<close> per_perp perp_left_comm by auto 
        moreover
        have "Q R Perp R R1"
          by (simp add: "2" "5" \<open>R \<noteq> R1\<close> per_perp) 
        moreover
        have "Col P Q Q"
          by (simp add: col_trivial_2) 
        moreover
        have "Col Q R Q"
          using col_trivial_3 by auto 
        moreover
        have "Col P Q P"
          by (simp add: col_trivial_3) 
        moreover
        have "Col P P1 P"
          by (simp add: col_trivial_3) 
        moreover
        have "Col Q R R"
          by (simp add: col_trivial_2)
        moreover
        have "Col R R1 R"
          by (simp add: col_trivial_3) 
        moreover
        have "Coplanar Q P R P"
          using ncop_distincts by blast 
        moreover
        have "Coplanar Q P R P1"
          using "6" ncoplanar_perm_6 by blast 
        moreover
        have "Coplanar Q P R R"
          using ncop_distincts by blast 
        moreover
        have "Coplanar Q P R R1"
          using "7" ncoplanar_perm_6 by blast 
        ultimately
        show ?thesis 
          using assms(1) by blast
      qed
    qed
  }
  thus ?thesis
    using bachmann_s_lotschnittaxiom_def by blast 
qed

lemma bachmann_s_lotschnittaxiom_aux:
  shows "bachmann_s_lotschnittaxiom \<longleftrightarrow>
(\<forall> A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD.
 IAB \<noteq> IAC \<and> IAB \<noteq> IBD \<and>
  A1 A2 Perp B1 B2 \<and> 
A1 A2 Perp C1 C2 \<and> 
B1 B2 Perp D1 D2 \<and>
  Col A1 A2 IAB \<and>
 Col B1 B2 IAB \<and> Col A1 A2 IAC \<and>
  Col C1 C2 IAC \<and> Col B1 B2 IBD \<and> Col D1 D2 IBD \<and>
  Coplanar IAB IAC IBD C1 \<and> 
Coplanar IAB IAC IBD C2 \<and>
  Coplanar IAB IAC IBD D1 \<and> Coplanar IAB IAC IBD D2 \<longrightarrow>
  (\<exists> I. Col C1 C2 I \<and> Col D1 D2 I))"
  using bachmann_s_lotschnittaxiom_aux_R2 bachmann_s_lotschnittaxiom_aux_R1 by blast

lemma bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate:
  assumes "bachmann_s_lotschnittaxiom"
  shows "legendre_s_parallel_postulate"
proof -
  have P0: "\<forall> A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD.
 IAB \<noteq> IAC \<and> IAB \<noteq> IBD \<and>
  A1 A2 Perp B1 B2 \<and> 
A1 A2 Perp C1 C2 \<and> 
B1 B2 Perp D1 D2 \<and>
  Col A1 A2 IAB \<and>
 Col B1 B2 IAB \<and> Col A1 A2 IAC \<and>
  Col C1 C2 IAC \<and> Col B1 B2 IBD \<and> Col D1 D2 IBD \<and>
  Coplanar IAB IAC IBD C1 \<and> 
Coplanar IAB IAC IBD C2 \<and>
  Coplanar IAB IAC IBD D1 \<and> Coplanar IAB IAC IBD D2 \<longrightarrow>
  (\<exists> I. Col C1 C2 I \<and> Col D1 D2 I)" 
    using assms(1) bachmann_s_lotschnittaxiom_aux_R1 by blast
  {
    assume "(\<exists> A B C. (\<not> Col A B C \<and> Acute A B C \<and>
   (\<forall> P Q. B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q 
\<longrightarrow> (\<exists> Y. B Out C Y \<and> Col P Q Y))))"
    then obtain A B C where P1: "(\<not> Col A B C \<and> Acute A B C \<and>
   (\<forall> P Q. B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q 
\<longrightarrow> (\<exists> Y. B Out C Y \<and> Col P Q Y)))" 
      by auto
    hence "\<not> Col A B C" 
      by auto
    have "Acute A B C" 
      using P1 by blast
    have Q1: "\<forall> P Q. B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q 
\<longrightarrow> (\<exists> Y. B Out C Y \<and> Col P Q Y)"
      using P1 by blast
    {
      fix T
      assume "T InAngle A B C"
      {
        assume "Col A B T"
        have "\<not> Col B C T"
          by (metis \<open>Col A B T\<close> \<open>T InAngle A B C\<close> \<open>\<not> Col A B C\<close> col_trivial_3 
              colx inangle_distincts not_col_permutation_2)
        then obtain Y where P2: "Col B C Y \<and> B C Perp T Y"
          using l8_18_existence by blast 
        hence "Col B C Y"
          by auto
        have "B C Perp T Y"
          using P2 by blast
        have "B Out A T"
          using Col_def NCol_perm \<open>Col A B T\<close> \<open>T InAngle A B C\<close> \<open>\<not> Col A B C\<close> 
            col_in_angle_out by blast 
        moreover
        have "T B A A B C SumA T B C" 
        proof -
          have "A B C CongA A B C"
            using \<open>\<not> Col A B C\<close> conga_refl not_col_distincts by fastforce 
          moreover
          have "\<not> B A OS T C"
            using \<open>B Out A T\<close> one_side_not_col123 out_col by blast 
          moreover
          have "Coplanar T B A C"
            by (simp add: \<open>Col A B T\<close> col__coplanar col_permutation_3) 
          moreover
          have "T B C CongA T B C"
            using \<open>T InAngle A B C\<close> conga_refl inangle_distincts by auto 
          ultimately
          show ?thesis
            using SumA_def by blast 
        qed
        hence "A B C CongA T B C"
          by (meson \<open>Col A B T\<close> \<open>T InAngle A B C\<close> \<open>\<not> Col A B C\<close> bet_col 
              col_in_angle_out col_permutation_4 l6_6 out213_suma__conga) 
        hence "Acute T B C"
          using \<open>Acute A B C\<close> acute_conga__acute by blast 
        hence "B Out C Y"
          using P2 acute_col_perp__out l6_6 by blast 
        moreover
        have "Bet T T Y"
          by (simp add: between_trivial2) 
        ultimately
        have "(\<exists> X Y. B Out A X \<and> B Out C Y \<and> Bet X T Y)" 
          by blast
      }
      moreover
      {
        assume "\<not> Col A B T"
        then obtain X where P3: "Col A B X \<and> A B Perp T X"
          using l8_18_existence by blast 
        hence "Col A B X"
          by auto
        have "A B Perp T X"
          using P3 by blast
        have "B Out A X" 
        proof -
          have "Acute T B A" 
          proof -
            have "Acute A B C"
              by (simp add: \<open>Acute A B C\<close>) 
            moreover
            have "A B T LeA A B C" 
              by (simp add: \<open>T InAngle A B C\<close> inangle__lea)
            hence "T B A LeA A B C"
              using lea_left_comm by blast 
            ultimately
            show ?thesis
              using acute_lea_acute by blast 
          qed
          moreover
          have "Col B A X"
            using \<open>Col A B X\<close> not_col_permutation_4 by blast 
          moreover
          have "B A Perp T X"
            by (simp add: \<open>A B Perp T X\<close> perp_left_comm) 
          ultimately
          show ?thesis
            using acute_col_perp__out l6_6 by blast 
        qed
        have "\<exists> Y. B Out C Y \<and> Col X T Y"
        proof -
          have "X \<noteq> T"
            using P3 \<open>\<not> Col A B T\<close> by blast 
          moreover
          have "Col A B B"
            by (simp add: col_trivial_2) 
          hence "Per B X T" 
            using \<open>Col A B X\<close> \<open>A B Perp T X\<close> Per_perm l8_16_1 by blast 
          moreover
          have "Coplanar A B C T"
            using \<open>T InAngle A B C\<close> coplanar_perm_9 inangle__coplanar by blast 
          ultimately
          show ?thesis 
            using \<open>B Out A X\<close> Q1 by blast
        qed
        then obtain Y where P5: "B Out C Y \<and> Col X T Y" 
          by auto
        hence "B Out C Y" 
          by auto
        have "Col X T Y"
          using P5 by blast
        {
          assume "Bet T Y X \<or> Bet Y X T"
          have "Bet X T Y"
          proof cases
            assume "T = Y"
            thus ?thesis
              by (simp add: between_trivial)
          next
            assume "T \<noteq> Y"
            have "\<not> Col B C T"
              by (metis (full_types) P5 \<open>B Out A X\<close> \<open>T \<noteq> Y\<close> 
                  \<open>\<not> Col A B C\<close> col_trivial_3 colx 
                  not_col_permutation_2 out_col out_distinct) 
            {
              assume "Bet T Y X"
              have "C B OS T A"
                by (simp add: \<open>T InAngle A B C\<close> \<open>\<not> Col A B C\<close> 
                    \<open>\<not> Col B C T\<close> in_angle_one_side 
                    l11_24 not_col_permutation_3) 
              have "C B TS T A" 
              proof -
                have "C B TS X T" 
                proof -
                  have "\<not> Col X C B" 
                    by (metis Out_def \<open>B Out A X\<close> \<open>Col A B X\<close> 
                        \<open>\<not> Col A B C\<close> col_permutation_2 col_transitivity_1)
                  moreover have "\<not> Col T C B" 
                    using NCol_perm \<open>\<not> Col B C T\<close> by blast
                  moreover have "\<exists> Z. Col Z C B \<and> Bet X Z T" 
                    using Col_perm P5 \<open>Bet T Y X\<close> between_symmetry out_col by blast
                  ultimately show ?thesis 
                    using TS_def by blast
                qed
                moreover
                have "C B OS X A"
                  using \<open>B Out A X\<close> \<open>\<not> Col A B C\<close> col_trivial_3 
                    invert_one_side one_side_reflexivity 
                    os_out_os by blast 
                ultimately
                show ?thesis
                  using l9_2 l9_8_2 by blast 
              qed
              hence "Bet X T Y"
                using \<open>C B OS T A\<close> l9_9 by blast 
            }
            moreover
            {
              assume "Bet Y X T"
              have "A B OS T C"
                by (simp add: NCol_perm \<open>T InAngle A B C\<close> 
                    \<open>\<not> Col A B C\<close> \<open>\<not> Col A B T\<close> in_angle_one_side)
              have "A B TS T C" 
              proof -
                have "A B TS Y T"
                  by (metis (full_types) \<open>Bet Y X T\<close> \<open>Col A B X\<close> 
                      \<open>Col X T Y\<close> \<open>\<not> Col A B T\<close> between_equality between_trivial 
                      calculation col_permutation_5 colx l9_18 not_col_permutation_2) 
                moreover
                have "A B OS Y C"
                  using \<open>A B OS T C\<close> \<open>B Out C Y\<close> col124__nos 
                    invert_one_side l6_6 out_one_side by blast 
                ultimately
                show ?thesis
                  using l9_2 l9_8_2 by blast 
              qed
              hence "Bet X T Y"
                using \<open>A B OS T C\<close> l9_9 by blast 
            }
            ultimately
            show ?thesis
              using \<open>Bet T Y X \<or> Bet Y X T\<close> by blast 
          qed
        }
        hence "Bet X T Y"
          using Col_def \<open>Col X T Y\<close> by blast 
        hence "\<exists> X Y. B Out A X \<and> B Out C Y \<and> Bet X T Y"
          using \<open>B Out A X\<close> \<open>B Out C Y\<close> by blast 
      }
      ultimately
      have "(\<exists> X Y. B Out A X \<and> B Out C Y \<and> Bet X T Y)"
        by blast
    }
    hence "legendre_s_parallel_postulate"
      using legendre_s_parallel_postulate_def \<open>Acute A B C\<close> 
        \<open>\<not> Col A B C\<close> by blast 
  }
  hence "(\<exists> A B C. (\<not> Col A B C \<and> Acute A B C \<and>
   (\<forall> P Q. B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q 
\<longrightarrow> (\<exists> Y. B Out C Y \<and> Col P Q Y)))) \<longrightarrow>
legendre_s_parallel_postulate" 
    by blast
  moreover
  have "\<exists> A B C. ( \<not> Col A B C \<and> 
                   Acute A B C \<and>
                   (\<forall> P Q. B Out A P \<and> P \<noteq> Q \<and> 
                           Per B P Q \<and> 
                           Coplanar A B C Q 
                        \<longrightarrow> 
                           (\<exists> Y. B Out C Y \<and> Col P Q Y)))" 
  proof -
    obtain C E D9 where P6: "\<not> (Bet C E D9 \<or> Bet E D9 C \<or> Bet D9 C E)"
      using lower_dim by blast
    hence "\<not> Col C E D9"
      by (simp add: Col_def)
    then obtain B where P7: "Col D9 E B \<and> D9 E Perp C B" 
      using l8_18_existence NCol_cases by blast 
    hence "Col D9 E B"
      by auto
    have "D9 E Perp C B"
      using P7 by blast
    have "\<exists> F. Col D9 E F \<and> B \<noteq> F"
      using \<open>Col D9 E B\<close> diff_col_ex3 by blast
    then obtain F where P8: "Col D9 E F \<and> B \<noteq> F" 
      by blast
    hence "Col D9 E F" 
      by auto
    have "B \<noteq> F"
      using P8 by auto
    then obtain A where P9: "(Bet B F A \<or> Bet B A F) \<and> Cong B A B C"
      using segment_construction_2 by presburger 
    hence "Bet B F A \<or> Bet B A F"
      by auto
    have "Cong B A B C"
      using P9 by auto
    have "Col D9 E A"
      using \<open>B \<noteq> F\<close> \<open>Bet B F A \<or> Bet B A F\<close> \<open>Col D9 E B\<close> 
        \<open>Col D9 E F\<close> bet_col1 between_trivial colx by blast 
    have "C B Perp B A" 
    proof -
      have "D9 E Perp C B"
        by (simp add: \<open>D9 E Perp C B\<close>) 
      moreover
      have "B \<noteq> A"
        by (metis NCol_cases \<open>Col D9 E A\<close> \<open>Cong B A B C\<close> 
            \<open>\<not> Col C E D9\<close> cong_diff_3) 
      moreover
      have "Col D9 E B"
        using \<open>Col D9 E B\<close> by blast
      moreover
      have "Col D9 E A"
        using \<open>Col D9 E A\<close> by auto 
      ultimately
      show ?thesis
        using perp_col0 by blast 
    qed
    hence "B A Perp C B"
      using Perp_perm by blast 
    have K1: "\<not> Col B A C"
      by (simp add: \<open>B A Perp C B\<close> perp_not_col)
    obtain D where P8B: "D Midpoint A C"
      using midpoint_existence by blast
    have "\<not> Col A B D"
      by (metis P8B \<open>\<not> Col B A C\<close> col_transitivity_2 
          midpoint_col midpoint_distinct_1 
          not_col_permutation_1) 
    moreover
    have "B \<noteq> A"
      using \<open>\<not> Col B A C\<close> col_trivial_1 by blast 
    have "A \<noteq> C"
      using \<open>\<not> Col B A C\<close> col_trivial_2 by blast 
    have "B \<noteq> C"
      using \<open>\<not> Col B A C\<close> col_trivial_3 by blast 
    have "D \<noteq> A"
      using calculation not_col_distincts by blast 
    have "D \<noteq> C"
      using P8B \<open>A \<noteq> C\<close> midpoint_not_midpoint by blast 
    have "Acute A B D" 
    proof -
      have "D \<noteq> B"
        using calculation col_trivial_2 by blast
      have "Per A B C"
        using Perp_cases \<open>C B Perp B A\<close> perp_per_2 by blast 
      moreover
      have "A B D LtA A B C" 
      proof -
        have "A B D LeA A B C" 
        proof -
          have "D InAngle A B C" 
          proof -
            have "Bet A D C"
              using Midpoint_def P8B by blast 
            moreover
            have "D = B \<or> B Out D D"
              using out_trivial by blast 
            ultimately
            show ?thesis
              using InAngle_def \<open>B \<noteq> A\<close> \<open>B \<noteq> C\<close> \<open>D \<noteq> B\<close> by auto 
          qed
          moreover
          have "A B D CongA A B D"
            using \<open>B \<noteq> A\<close> \<open>D \<noteq> B\<close> conga_refl by auto 
          ultimately
          show ?thesis
            by (simp add: inangle__lea)
        qed
        moreover
        {
          assume "A B D CongA A B C"
          hence "Per A B D"
            using \<open>Per A B C\<close> conga_sym l11_17 by blast
          have "Per C B D"
            using P8B \<open>B \<noteq> A\<close> \<open>D \<noteq> C\<close> \<open>Per A B C\<close> \<open>Per A B D\<close> 
              col_per2__per l7_2 l8_2 l8_8 midpoint_col by blast
          have "A B D C B D SumA A B C" 
          proof -
            have "D B C CongA C B D"
              using \<open>B \<noteq> C\<close> \<open>D \<noteq> B\<close> conga_pseudo_refl by auto 
            moreover
            have "\<not> B D OS A C"
              by (meson P8B midpoint_bet col_trivial_3 one_side_chara) 
            moreover
            have "Coplanar A B D C" 
            proof -
              have "Bet A D C"
                using P8B by (simp add: midpoint_bet)
              thus ?thesis
                using bet_col ncop__ncols by blast 
            qed
            moreover
            have "A B C CongA A B C"
              using \<open>B \<noteq> A\<close> \<open>B \<noteq> C\<close> conga_refl by auto 
            ultimately
            show ?thesis
              using SumA_def by blast 
          qed
          hence "Bet A B C" 
            using per2_suma__bet \<open>Per A B D\<close> \<open>Per C B D\<close> by blast 
          hence "False"
            using Col_def \<open>\<not> Col B A C\<close> between_symmetry by blast 
        }
        hence "\<not> A B D CongA A B C" 
          by auto
        ultimately
        show ?thesis
          by (simp add: LtA_def)
      qed
      ultimately
      show ?thesis
        using Acute_def by blast 
    qed
    moreover
    { 
      fix P Q
      assume H1: "B Out A P" and
        H2: "P \<noteq> Q" and
        H3: "Per B P Q" and
        H4: "Coplanar A B D Q"
      have "B \<noteq> P"
        using H1 Out_def  by auto 
      then obtain P' where H5: "B Out P' C \<and> Cong B P' B P" 
        using \<open>B \<noteq> C\<close> l6_11_existence by fastforce 
      hence H5A: "B Out P' C" 
        by auto
      have H5B: "Cong B P' B P"
        using H5 by auto
      obtain Q' where H6: "B C Perp Q' P' \<and> Coplanar B C A Q'" 
        using ex_perp_cop \<open>B \<noteq> C\<close> by blast 
      hence H6A: "B C Perp Q' P'" 
        by auto
      have H6B: "Coplanar B C A Q'"
        using H6 by blast
      have "B A Perp Q P"
        by (metis H1 H2 H3 NCol_cases \<open>B \<noteq> A\<close> \<open>B \<noteq> P\<close> col_per_perp l8_2 out_col)
      have "Coplanar B Q A C" 
      proof -
        have "Coplanar B Q A D"
          by (simp add: H4 coplanar_perm_10) 
        moreover
        have "Col A D A"
          by (simp add: col_trivial_3) 
        moreover
        have "Col A D C" 
          using P8B by (simp add: Midpoint_def bet_col) 
        ultimately
        show ?thesis 
          using \<open>D \<noteq> A\<close> col2_cop__cop by blast 
      qed
      have "\<exists> I. Col P Q I \<and> Col P' Q' I"
      proof -
        have "B \<noteq> P'"
          using \<open>B Out P' C\<close> l6_3_1 by blast 
        moreover
        have "B \<noteq> P"
          using \<open>B \<noteq> P\<close> by auto
        moreover
        have "B A Perp B C"
          by (simp add: \<open>B A Perp C B\<close> perp_right_comm) 
        moreover
        have "B A Perp P Q"
          by (simp add: \<open>B A Perp Q P\<close> perp_right_comm) 
        moreover
        have "B C Perp P' Q'"
          by (simp add: \<open>B C Perp Q' P'\<close> perp_right_comm) 
        moreover
        have "Col B A B"
          by (simp add: col_trivial_3) 
        moreover
        have "Col B C B"
          by (simp add: col_trivial_3) 
        moreover  
        have "Col B A P"
          by (simp add: H1 out_col) 
        moreover
        have "Col P Q P"
          by (simp add: col_trivial_3) 
        moreover
        have "Col B C P'"
          using Out_cases \<open>B Out P' C\<close> out_col by blast 
        moreover
        have "Col P' Q' P'"
          by (simp add: col_trivial_3) 
        moreover
        have "Coplanar B P P' P"
          using ncop_distincts by blast 
        moreover
        have "Coplanar B P P' Q" 
        proof -
          have "Coplanar B A C Q" 
            by (simp add: \<open>Coplanar B Q A C\<close> coplanar_perm_3)
          moreover have "Coplanar B A C P'" 
            using \<open>Col B C P'\<close> ncop__ncols by blast
          moreover have "Coplanar B A C P" 
            using \<open>Col B A P\<close> ncop__ncols by blast
          moreover have "Coplanar B A C B" 
            using ncop_distincts by blast
          ultimately show ?thesis 
            using K1 coplanar_pseudo_trans by presburger
        qed
        moreover  
        have "Coplanar B P P' P'"
          using ncop_distincts by blast
        moreover
        have "Coplanar B P P' Q'" 
          using H6B col2_cop__cop
          by (meson \<open>B \<noteq> A\<close> \<open>B \<noteq> C\<close> calculation(10) calculation(6) 
              calculation(7) calculation(8) coplanar_perm_16 
              coplanar_perm_21)
        ultimately
        show ?thesis 
          using P0 by blast
      qed
      then obtain I where H7: "Col P Q I \<and> Col P' Q' I"
        by auto
      hence "Col P Q I" 
        by auto
      have "Col P' Q' I"
        using H7 by blast
      have "B \<noteq> D"
        using \<open>\<not> Col A B D\<close> col_trivial_2 by blast
      hence "B C ParStrict P I" 
      proof -
        have "P \<noteq> I"
        proof -
          {
            assume "P = I"
            {
              assume "Col B A C"
              hence "\<not> B A Perp C B"
                using K1 by blast 
              hence "False" 
                using perp_not_col using \<open>B A Perp C B\<close> by blast 
            }
            moreover
            have "Col B A C" 
            proof -
              have "A B Par P' Q'" 
              proof -
                have "Coplanar B C A P'"
                  using H5A ncop__ncols ncoplanar_perm_3 out_col by blast 
                moreover
                have "Coplanar B C A Q'"
                  by (simp add: H6B) 
                moreover
                have "Coplanar B C B P'"
                  using ncop_distincts by blast 
                moreover
                have "Coplanar B C B Q'"
                  using ncop_distincts by blast 
                moreover
                have "A B Perp B C"
                  using Perp_perm \<open>B A Perp C B\<close> by blast 
                moreover
                have "P' Q' Perp B C"
                  using H6A Perp_perm by blast 
                ultimately
                show ?thesis 
                  using l12_9 by blast
              qed
              moreover
              have "Col A B P"
                using Col_perm H1 out_col by blast 
              moreover
              have "Col P' Q' P"
                by (simp add: \<open>Col P' Q' I\<close> \<open>P = I\<close>) 
              ultimately
              show ?thesis 
                using not_strict_par 
                by (metis H5A col_trivial_2 col_trivial_3 
                    colx out_col out_distinct) 
            qed
            ultimately
            have "False" 
              by blast
          }
          thus ?thesis
            by auto 
        qed
        moreover
        have "B C ParStrict P Q" 
        proof -
          have "B C Par P Q" 
          proof -
            have "Coplanar A B B P"
              using ncop_distincts by blast 
            moreover
            have "Coplanar A B B Q"
              using ncop_distincts by blast 
            moreover
            have "Coplanar A B C P"
              using H1 ncop__ncols ncoplanar_perm_14 out_col by blast 
            moreover
            have "Coplanar A B C Q"
              using \<open>Coplanar B Q A C\<close> ncoplanar_perm_10 by blast 
            moreover
            have "B C Perp A B"
              by (simp add: \<open>C B Perp B A\<close> perp_comm) 
            moreover
            have "P Q Perp A B"
              using Perp_perm \<open>B A Perp Q P\<close> by blast 
            ultimately
            show ?thesis
              using l12_9 by blast 
          qed
          moreover
          have"Col P Q P"
            using col_trivial_3 by auto 
          moreover
          have "\<not> Col B C P"
            using H1 \<open>B \<noteq> P\<close> \<open>\<not> Col B A C\<close> col_permutation_5 
              col_trivial_3 colx out_col by blast 
          ultimately
          show ?thesis
            using par_not_col_strict by blast 
        qed
        ultimately
        show ?thesis
          using \<open>Col P Q I\<close> par_strict_col_par_strict by blast 
      qed
      hence "B C OS P I"
        by (simp add: l12_6) 
      have "Col D B I" 
      proof cases
        assume "D = I"
        thus ?thesis
          using col_trivial_3 by blast 
      next
        assume "D \<noteq> I"
        have "Coplanar A B C I" 
        proof -
          have "P \<noteq> Q"
            by (simp add: H2) 
          moreover
          have "Coplanar A B C P"
            using H1 ncoplanar_perm_7 out__coplanar by blast 
          moreover
          have "Coplanar A B C Q"
            using \<open>Coplanar B Q A C\<close> ncoplanar_perm_10 by blast 
          moreover
          have "Col P Q I"
            by (simp add: \<open>Col P Q I\<close>)
          ultimately 
          show ?thesis
            using col_cop2__cop by blast 
        qed
        moreover
        have "B D PerpBisect A C"
          by (simp add: P8B \<open>A \<noteq> C\<close> \<open>B \<noteq> D\<close> \<open>Cong B A B C\<close> 
              cong_commutativity cong_mid_perp_bisect) 
        hence "D B Perp A C"
          using Perp_perm perp_bisect_perp by blast 
        moreover
        have "D I PerpBisect A C"
        proof -
          have "D \<noteq> I"
            by (simp add: \<open>D \<noteq> I\<close>) 
          moreover
          have "A \<noteq> C"
            using \<open>A \<noteq> C\<close> by blast
          moreover
          have "Cong A I C I" 
          proof -
            have "P I Perp B P"
            proof -
              have "A B Perp P I" 
              proof -
                have "P Q Perp A B"
                  using Perp_perm \<open>B A Perp Q P\<close> by blast 
                moreover
                {
                  assume "P = I"
                  have "B A Par P' Q'" 
                  proof -
                    have "Coplanar B C B P'"
                      using ncop_distincts by blast 
                    moreover
                    have "Coplanar B C B Q'"
                      using ncop_distincts by blast
                    moreover
                    have "Coplanar B C A P'"
                      using H5A coplanar_perm_4 ncop__ncols out_col by blast
                    moreover
                    have "Coplanar B C A Q'"
                      using H6B by blast 
                    moreover
                    have "B A Perp B C"
                      by (simp add: \<open>B A Perp C B\<close> perp_right_comm) 
                    moreover
                    have "P' Q' Perp B C"
                      using H6A Perp_perm by blast 
                    ultimately
                    show ?thesis using l12_9 by blast
                  qed
                  have "Col B A P"
                    by (simp add: H1 out_col) 
                  have "Col P' Q' P"
                    by (simp add: \<open>Col P' Q' I\<close> \<open>P = I\<close>) 
                  hence "Col B A C"
                    using not_strict_par
                    by (metis H5A \<open>B A Par P' Q'\<close> \<open>Col B A P\<close> 
                        col_trivial_3 colx out_col out_distinct) 
                  hence "False"
                    using K1 by blast 
                }
                hence "P \<noteq> I" 
                  by auto
                moreover
                have "Col P Q P"
                  by (simp add: col_trivial_3) 
                moreover
                have "Col P Q I"
                  by (simp add: \<open>Col P Q I\<close>) 
                ultimately
                show ?thesis
                  using perp_col0 by blast 
              qed
              moreover
              have "B \<noteq> P"
                by (simp add: \<open>B \<noteq> P\<close>) 
              moreover
              have "Col A B B"
                using not_col_distincts by blast 
              moreover
              have "Col A B P"
                using Col_perm H1 out_col by blast 
              ultimately
              show ?thesis
                using perp_col0 by blast 
            qed
            have "P' I Perp B P'" 
            proof -
              have "B C Perp P' I" 
              proof -
                have "P' Q' Perp B C"
                  using H6A Perp_perm by blast
                moreover
                {
                  assume "P' = I"
                  have "B C Par P Q" 
                  proof -
                    have "Coplanar B A B P"
                      using ncop_distincts by blast 
                    moreover
                    have "Coplanar B A B Q"
                      using ncop_distincts by blast
                    moreover
                    have "Coplanar B A C P"
                      using H1 ncop__ncols out_col by blast 
                    moreover
                    have "Coplanar B A C Q"
                      by (simp add: \<open>Coplanar B Q A C\<close> coplanar_perm_3)
                    moreover
                    have "B C Perp B A"
                      by (simp add: perp_left_comm \<open>C B Perp B A\<close>) 
                    moreover
                    have "P Q Perp B A"
                      using Perp_cases \<open>B A Perp Q P\<close> by blast
                    ultimately
                    show ?thesis using l12_9 by blast
                  qed
                  have "Col B C P'"
                    using H5A col_permutation_5 out_col by blast 
                  have "Col P Q P'"
                    by (simp add: \<open>Col P Q I\<close> \<open>P' = I\<close>)
                  hence "Col B A C"
                    using not_strict_par not_par_inter_uniqueness 
                    by (metis H1 \<open>B C Par P Q\<close> \<open>B \<noteq> A\<close> \<open>B \<noteq> P\<close> 
                        \<open>Col B C P'\<close> col_trivial_3 out_col) 
                  hence "False"
                    using K1 by blast 
                }
                hence "P' \<noteq> I" 
                  by auto
                moreover
                have "Col P' Q' P'"
                  by (simp add: col_trivial_3) 
                moreover
                have "Col P' Q' I"
                  by (simp add: \<open>Col P' Q' I\<close>) 
                ultimately
                show ?thesis
                  using perp_col0 by blast 
              qed
              moreover
              have "B \<noteq> P'"
                using H5A out_diff1 by blast
              moreover
              have "Col B C B"
                using not_col_distincts by blast 
              moreover
              have "Col B C P'"
                using Col_perm H5A out_col by blast
              ultimately
              show ?thesis
                using perp_col0 by blast 
            qed
            have "P' \<noteq> I"
              using \<open>P' I Perp B P'\<close> perp_distinct by blast 
            have "P \<noteq> I"
              using \<open>P I Perp B P\<close> perp_distinct by auto 
            have "B P Lt B I"
              using H2 H3 \<open>B \<noteq> P\<close> \<open>Col P Q I\<close> \<open>P \<noteq> I\<close> per_col per_lt by presburger
            have "A B I CongA C B I"
            proof -
              have "P B I CongA P' B I" 
              proof -
                have "I P B CongA I P' B"
                  using H5B \<open>B \<noteq> P\<close> \<open>P I Perp B P\<close> \<open>P \<noteq> I\<close> 
                    \<open>P' I Perp B P'\<close> \<open>P' \<noteq> I\<close> cong_diff_3 l11_16 
                    perp_per_1 by blast 
                show ?thesis
                  using H5B \<open>B \<noteq> P\<close> \<open>P I Perp B P\<close> \<open>P \<noteq> I\<close> 
                    \<open>P' I Perp B P'\<close> cong2_per2__cong_conga2 cong_4321 
                    cong_reflexivity perp_per_1 by auto 
              qed
              moreover
              have "B Out A P"
                by (simp add: H1) 
              moreover
              have "B \<noteq> I"
                using \<open>B C OS P I\<close> os_distincts by blast 
              hence "B Out I I"
                using out_trivial by auto 
              moreover
              have "B Out C P'"
                by (simp add: H5A l6_6) 
              ultimately
              show ?thesis using l11_10 by blast
            qed
            thus ?thesis
              using \<open>Cong B A B C\<close> cong2_conga_cong 
                cong_reflexivity not_cong_2143 by blast 
          qed
          moreover
          have "D Midpoint A C"
            by (simp add: P8B) 
          ultimately
          show ?thesis
            using cong_mid_perp_bisect perp_bisect_sym_1 by auto
        qed
        ultimately
        show ?thesis
          using cop_perp2__col ncoplanar_perm_2 perp_bisect_perp by blast 
      qed
      moreover
      have "\<not> Bet D B I" 
      proof -
        {
          assume "Bet D B I" 
          have "B C TS P I" 
          proof -
            have "\<not> Col B C D"
              by (metis NCol_cases P8B midpoint_out \<open>A \<noteq> C\<close> 
                  \<open>C B Perp B A\<close> \<open>D \<noteq> C\<close> l6_16_1 out_col perp_not_col2) 
            have "B C TS D I"
            proof -
              have "B C OS I P"
                by (simp add: \<open>B C OS P I\<close> one_side_symmetry) 
              hence "\<not> Col B C I"
                using col123__nos by blast 
              have "Bet D B I"
                by (simp add: \<open>Bet D B I\<close>) 
              thus ?thesis
                using \<open>\<not> Col B C D\<close> \<open>\<not> Col B C I\<close> bet__ts 
                  not_col_distincts by auto 
            qed
            moreover
            have "B C OS D A" 
            proof -
              have "Col B C C"
                by (simp add: col_trivial_2) 
              moreover
              have "Col D A C"
                by (simp add: P8B midpoint_col) 
              moreover
              have "C Out D A" 
                using P8B by (simp add: \<open>D \<noteq> C\<close> bet_out_1 midpoint_bet)
              ultimately
              show ?thesis
                using \<open>\<not> Col B C D\<close> l9_19_R2 by blast 
            qed
            moreover
            have "B C OS A P" 
            proof -
              have "Col B C C"
                by (simp add: col_trivial_2) 
              moreover
              have "Col D A C"  
                by (simp add: P8B midpoint_col) 
              moreover
              have "C Out D A"
                using P8B 
                by (simp add: \<open>D \<noteq> C\<close> bet_out_1 midpoint_bet)
              ultimately
              show ?thesis
                using \<open>\<not> Col B C D\<close> H1 K1 col_trivial_3 
                  not_col_permutation_5 out_one_side_1 by blast 
            qed
            ultimately
            show ?thesis
              using l9_8_2 by blast 
          qed
          hence "\<not> Bet D B I"
            using \<open>B C OS P I\<close> l9_9 by blast 
          hence "False"
            by (simp add: \<open>Bet D B I\<close>) 
        }
        thus ?thesis 
          by auto
      qed
      ultimately
      have "\<exists> Y. B Out D Y \<and> Col P Q Y" 
        using l6_4_2 \<open>Col P Q I\<close> by blast 
    }
    ultimately
    show ?thesis
      by blast 
  qed
  ultimately
  show ?thesis by blast
qed

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)
lemma bachmann_s_lotschnittaxiom__weak_inverse_projection_postulate:
  assumes "bachmann_s_lotschnittaxiom"
  shows "weak_inverse_projection_postulate"
proof -
  have lotschnitt: "\<forall> A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD.
                        IAB \<noteq> IAC \<and> IAB \<noteq> IBD \<and>
                        A1 A2 Perp B1 B2 \<and> A1 A2 Perp C1 C2 \<and> 
                        B1 B2 Perp D1 D2 \<and> Col A1 A2 IAB \<and>
                        Col B1 B2 IAB \<and> Col A1 A2 IAC \<and>
                        Col C1 C2 IAC \<and> Col B1 B2 IBD \<and> 
                        Col D1 D2 IBD \<and> Coplanar IAB IAC IBD C1 \<and> 
                        Coplanar IAB IAC IBD C2 \<and> 
                        Coplanar IAB IAC IBD D1 \<and> 
                        Coplanar IAB IAC IBD D2
 \<longrightarrow>
                        (\<exists> I. Col C1 C2 I \<and> Col D1 D2 I)" 
    using assms bachmann_s_lotschnittaxiom_aux_R1 by auto 
  {
    fix A B C D E F P Q
    assume 1 :"Acute A B C" and
      2: "Per D E F" and
      3: "A B C A B C SumA D E F" and
      4: "B Out A P" and
      5: "P \<noteq> Q" and
      6: "Per B P Q" and
      7: "Coplanar A B C Q"
    have "A \<noteq> B"
      using "4" l6_3_1 by blast 
    have "P \<noteq> B"
      using "4" l6_3_1 by blast 
    have "B \<noteq> C"
      using "1" acute_distincts by blast 
    have "D \<noteq> E"
      using "3" suma_distincts by blast 
    have "E \<noteq> F"
      using "3" suma_distincts by blast 
    {
      assume "Col A B C"
      hence "Col D E F" using col2_suma__col
        using "3" by blast 
      hence "False"
        using "2" \<open>D \<noteq> E\<close> \<open>E \<noteq> F\<close> per_col_eq by blast 
    }
    hence "\<not> Col A B C" 
      by auto
    have "\<not> Col B C P"
      by (metis "4" \<open>P \<noteq> B\<close> \<open>\<not> Col A B C\<close> col_permutation_5 
          col_trivial_2 col_trivial_3 colx out_col) 
    obtain P' where P2: "P P' ReflectL B C" 
      using l10_6_existence_spec by (metis col__refl col_trivial_2) 
    hence "P P' Reflect B C"
      by (simp add: \<open>B \<noteq> C\<close> is_image_is_image_spec)
    have "\<not> Col B C P'"
      using P2 \<open>\<not> Col B C P\<close> col_image_spec__eq l10_4_spec by blast
    obtain Q' where P3: "Q Q' ReflectL B C"
      using l10_6_existence_spec by (metis image_spec_triv) 
    hence "Q Q' Reflect B C"
      by (simp add: \<open>B \<noteq> C\<close> is_image_is_image_spec) 
    have "B \<noteq> P'"
      using \<open>\<not> Col B C P'\<close> col_trivial_3 by blast 
    have "P' \<noteq> Q'"
      using "5" P2 P3 l10_2_uniqueness_spec by blast
    have "C B P' CongA A B C" 
    proof -
      have "C B P' CongA P B C"
        by (metis P2 \<open>B \<noteq> C\<close> \<open>P \<noteq> B\<close> conga_left_comm 
            is_image_spec_rev not_conga_sym reflectl__conga) 
      moreover
      have "B Out C C"
        using \<open>B \<noteq> C\<close> out_trivial by auto 
      moreover
      have "B Out P' P'"
        using \<open>B \<noteq> P'\<close> out_trivial by auto 
      ultimately
      show ?thesis
        using "4" l11_10 by blast
    qed
    obtain X where "X Midpoint P' P \<and> Col B C X"
      using P2 ReflectL_def by blast 
    hence "\<exists> T. Col T B C \<and> Bet P T P'"
      using Mid_cases col_permutation_2 midpoint_bet by blast 
    hence "B C TS P P'"
      using TS_def \<open>\<not> Col B C P'\<close> \<open>\<not> Col B C P\<close> col_permutation_1 by blast 
    have "B Out P A"
      by (simp add: "4" l6_6)
    have "Coplanar P' C A B" 
    proof -
      have "Coplanar P' C P B"
        using \<open>B C TS P P'\<close> ncoplanar_perm_21 ts__coplanar by blast 
      moreover
      have "P \<noteq> B"
        by (simp add: \<open>P \<noteq> B\<close>) 
      moreover
      have "Col P B A"
        using "4" col_permutation_2 out_col by blast 
      moreover
      have "Col P B B"
        by (simp add: col_trivial_2) 
      ultimately
      show ?thesis
        using col2_cop__cop by blast 
    qed
    have "Coplanar B P P' Q"
    proof -
      have "Coplanar C A B B" 
        using ncop_distincts by blast
      moreover have "Coplanar C A B P" 
        using "4" coplanar_perm_20 out__coplanar by blast
      moreover have "Coplanar C A B P'" 
        using \<open>Coplanar P' C A B\<close> ncoplanar_perm_18 by blast
      moreover have "Coplanar C A B Q" 
        using "7" ncoplanar_perm_8 by blast
      ultimately show ?thesis 
        using \<open>\<not> Col A B C\<close> NCol_cases coplanar_pseudo_trans by blast
    qed
    have "A B C A B C SumA A B P'" 
    proof -
      have "A B C C B P' SumA A B P'" 
      proof -
        have "Col B B C"
          by (simp add: col_trivial_1)
        hence "\<not> B C OS A P'"
          using l9_5 l9_9 \<open>B Out P A\<close> \<open>B C TS P P'\<close> by blast 
        moreover
        have "Coplanar A B C P'"
          by (simp add: \<open>Coplanar P' C A B\<close> coplanar_perm_17) 
        ultimately
        show ?thesis 
          using conga_refl 
          by (metis SumA_def \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>B \<noteq> P'\<close>) 
      qed
      moreover
      have "A B C CongA A B C"
        using \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> conga_refl by auto 
      moreover
      have "C B P' CongA A B C"
        by (simp add: \<open>C B P' CongA A B C\<close>) 
      moreover
      have "A B P' CongA A B P'"
        using calculation(1) suma2__conga by blast 
      ultimately
      show ?thesis
        using conga3_suma__suma by blast 
    qed
    hence "D E F CongA A B P'" 
      using suma2__conga 3 by blast
    hence "Per A B P'" 
      using l11_17 "2" by blast
    have "\<not> Col A B P'" 
      using perp_not_col \<open>A \<noteq> B\<close> \<open>B \<noteq> P'\<close> \<open>Per A B P'\<close> 
        per_col_eq by blast 
    have "\<not> Col B P' P"
      by (meson \<open>B Out P A\<close> \<open>P \<noteq> B\<close> \<open>\<not> Col A B P'\<close> 
          col_trivial_3 colx not_col_permutation_1 out_col) 
    have "A B Perp B P'"
      by (simp add: \<open>A \<noteq> B\<close> \<open>B \<noteq> P'\<close> \<open>Per A B P'\<close> per_perp) 
    have Q1: "A B Perp P Q"
      by (metis "4" "5" "6" Col_perm Per_cases col_per_perp
          \<open>A \<noteq> B\<close> \<open>P \<noteq> B\<close> out_col perp_comm) 
    have "B B ReflectL B C"
      by (simp add: col__image_spec col_trivial_3)
    hence "B P' Perp P' Q'"
      using 6 P2 P3 \<open>B \<noteq> P'\<close> \<open>P' \<noteq> Q'\<close> image_spec_preserves_per 
        per_perp by auto 
    have "\<not> Col P' P Q" 
    proof -
      have "B P' Par P Q"
      proof -
        have "Coplanar A B B P"
          using ncop_distincts by blast 
        moreover
        have "Coplanar A B B Q"
          using ncop_distincts by blast 
        moreover
        have "Coplanar A B P' P"
          by (meson \<open>B Out P A\<close> ncop__ncols 
              ncoplanar_perm_9 out_col) 
        moreover
        have "Coplanar A B P' Q"
          using \<open>B Out P A\<close> \<open>Coplanar B P P' Q\<close> 
            \<open>P \<noteq> B\<close> col_cop__cop ncoplanar_perm_17 out_col 
            coplanar_perm_16 by blast 
        moreover
        have "B P' Perp A B"
          using Perp_perm \<open>A B Perp B P'\<close> by blast 
        moreover
        have "P Q Perp A B"
          using Perp_perm \<open>A B Perp P Q\<close> by blast 
        ultimately
        show ?thesis 
          using l12_9 by blast
      qed
      hence "B P' ParStrict P Q"
        using Par_def \<open>\<not> Col B P' P\<close> not_col_permutation_2 
          par_strict_symmetry par_symmetry by blast 
      moreover
      have "Col P' B P'"
        by (simp add: col_trivial_3) 
      ultimately
      show ?thesis
        using par_strict_not_col_2 by blast 
    qed
    obtain I where P5: "Col I A B \<and> Col I P Q"
      using Q1 NCol_cases perp_inter_perp_in_n by blast 
    hence "Col I A B"
      by simp
    have "Col I P Q"
      using P5 by simp
    have "\<exists> Y. Col P' Q' Y \<and> Col P Q Y" 
    proof -
      have "B \<noteq> P"
        using \<open>P \<noteq> B\<close> by blast 
      moreover
      have "B \<noteq> P'"
        by (simp add: \<open>B \<noteq> P'\<close>) 
      moreover
      have "A B Perp B P'"
        by (simp add: \<open>A B Perp B P'\<close>)
      moreover
      have "A B Perp P Q"
        by (simp add: Q1) 
      moreover
      have "B P' Perp P' Q'"
        by (simp add: \<open>B P' Perp P' Q'\<close>) 
      moreover
      have "Col A B B"
        by (simp add: col_trivial_2) 
      moreover
      have "Col B P' B"
        by (simp add: col_trivial_3) 
      moreover
      have "Col A B P"
        using "4" not_col_permutation_4 out_col by blast
      moreover
      have "Col P Q P"
        by (simp add: col_trivial_3) 
      moreover
      have "Col B P' P'"
        by (simp add: col_trivial_2) 
      moreover
      have "Col P' Q' P'"
        by (simp add: col_trivial_3) 
      moreover
      have "Coplanar B P P' P"
        using ncop_distincts by blast 
      moreover
      have "Coplanar B P P' Q"
        using \<open>Coplanar B P P' Q\<close> by blast 
      moreover
      have "Coplanar B P P' P'"
        using ncop_distincts by blast 
      moreover
      have "Coplanar B P P' Q'" 
      proof -
        {
          assume "Col B C Q"
          have "Q = Q'"
            using P3 \<open>Col B C Q\<close> col_image_spec__eq by blast 
          hence "Coplanar B P P' Q'"
            using calculation(13) by blast 
        }
        moreover
        {
          assume "\<not> Col B C Q" 
          moreover
          have "Coplanar B C Q B"
            using ncop_distincts by blast
          moreover
          have "Coplanar B C Q P"
            using "7" \<open>A \<noteq> B\<close> \<open>Col A B B\<close> \<open>Col A B P\<close> 
              col2_cop__cop ncoplanar_perm_14 
              ncoplanar_perm_17 by blast
          moreover
          have "Coplanar B C Q P'"
            by (metis \<open>\<exists>T. Col T B C \<and> Bet P T P'\<close> 
                \<open>\<not> Col B C P\<close> bet_col calculation(3) col_cop2__cop 
                col_permutation_1 ncop__ncols)
          moreover
          have "Coplanar B C Q Q'"
            using P3 ncoplanar_perm_16 reflectl__coplanar by blast 
          ultimately
          have "?thesis"
            using coplanar_pseudo_trans by blast 
        }
        ultimately
        show ?thesis by auto
      qed
      ultimately
      show ?thesis using lotschnitt by blast
    qed
    then obtain Y where P7: "Col P' Q' Y \<and> Col P Q Y" 
      by auto
    hence "Col P' Q' Y" 
      by simp
    have "Col P Q Y"
      using P7 by simp
    have "B Out C Y" 
    proof -
      have "Col B C Y" 
      proof -
        have "P P' Reflect B C"
          by (simp add: \<open>P P' Reflect B C\<close>)
        moreover
        have "Q Q' Reflect B C"
          by (simp add: \<open>Q Q' Reflect B C\<close>) 
        moreover
        have "\<not> Col P Q P'"
          using NCol_perm \<open>\<not> Col P' P Q\<close> by blast 
        moreover
        have "Col P Q Y"
          using \<open>Col P Q Y\<close> by blast 
        moreover
        have "Col P' Q' Y"
          using \<open>Col P' Q' Y\<close> by blast 
        ultimately
        show ?thesis 
          using intersection_with_image_gen not_col_permutation_2 by blast 
      qed
      moreover
      have "B A OS C Y" 
      proof -
        have "A B OS C P'" 
        proof -
          have "Coplanar A B C P'"
            by (simp add: \<open>Coplanar P' C A B\<close> coplanar_perm_17) 
          moreover
          have "\<not> Col C A B"
            by (simp add: \<open>\<not> Col A B C\<close> not_col_permutation_2) 
          moreover
          have "\<not> Col P' A B"
            using Col_cases \<open>\<not> Col A B P'\<close> by blast 
          moreover
          have "\<not> A B TS C P'" 
          proof -
            have "SAMS A B C A B C"
              by (simp add: "1" acute__sams) 
            moreover
            have "C B P' CongA A B C"
              using \<open>C B P' CongA A B C\<close> by blast 
            moreover
            have "\<not> B C OS A P'"
            proof -
              have "B C TS P P'"
                using \<open>B C TS P P'\<close> by blast 
              moreover 
              have "Col B B C"
                by (simp add: col_trivial_1) 
              moreover
              have "B Out P A"
                by (simp add: \<open>B Out P A\<close>) 
              ultimately
              show ?thesis
                using l9_5 l9_9 by blast 
            qed
            ultimately
            show ?thesis
              using conga_sams_nos__nts by blast  
          qed
          ultimately
          show ?thesis
            using cop_nts__os by blast 
        qed
        moreover
        have "A B OS P' Y" 
        proof -
          have "P' \<noteq> Y"
            using \<open>Col B C Y\<close> \<open>\<not> Col B C P'\<close> by blast 
          moreover
          have "A B ParStrict P' Q'" 
          proof -
            have "A B Par P' Q'" 
            proof -
              have "Coplanar B P' A P'"
                using ncop_distincts by blast 
              moreover
              have "Coplanar B P' A Q'"
              proof -
                {
                  assume "Col B C Q"
                  hence "Q = Q'"
                    using P3 col_image_spec__eq by blast 
                  have  "?thesis" 
                    using P3 \<open>Col B C Q\<close> \<open>B \<noteq> C\<close> \<open>Coplanar P' C A B\<close> 
                      \<open>Q = Q'\<close> col2_cop__cop col_trivial_3 coplanar_perm_13 
                      ncoplanar_perm_14 by blast 
                }
                moreover
                {
                  assume "\<not> Col B C Q"
                  have "Coplanar B C Q B"
                    using ncop_distincts by blast 
                  moreover
                  have "Coplanar B C Q P'"
                    using "7" \<open>Coplanar P' C A B\<close> \<open>\<not> Col A B C\<close> 
                      coplanar_trans_1 ncoplanar_perm_22 by blast 
                  moreover
                  have "Coplanar B C Q A"
                    by (meson "7" ncoplanar_perm_18) 
                  moreover
                  have "Coplanar B C Q Q'"
                  proof -
                    have "Coplanar A B C B" 
                      using ncop_distincts by blast
                    moreover have "Coplanar A B C C" 
                      using ncop_distincts by blast
                    moreover have "Coplanar A B C Q'" 
                      by (meson \<open>B \<noteq> C\<close> \<open>Col B C Y\<close> \<open>Col P' Q' Y\<close> 
                          \<open>Coplanar P' C A B\<close> \<open>P' \<noteq> Y\<close> calculation(1) 
                          calculation(2) col_cop2__cop 
                          col_permutation_5 coplanar_perm_17)
                    ultimately show ?thesis
                      using \<open>\<not> Col A B C\<close> "7" coplanar_trans_1 by blast
                  qed
                  ultimately
                  have "Coplanar B P' A Q'"
                    using \<open>\<not> Col B C Q\<close> coplanar_pseudo_trans by blast 
                }
                ultimately
                show ?thesis 
                  by auto
              qed
              moreover
              have "Coplanar B P' B P'"
                using ncop_distincts by blast 
              moreover
              have "Coplanar B P' B Q'"
                using ncop_distincts by blast 
              moreover
              have "A B Perp B P'"
                by (simp add: \<open>A B Perp B P'\<close>) 
              moreover
              have "P' Q' Perp B P'"
                using Perp_perm \<open>B P' Perp P' Q'\<close> by blast 
              ultimately
              show ?thesis
                using l12_9 by blast
            qed
            moreover
            have "Col P' Q' P'"
              by (simp add: col_trivial_3) 
            moreover
            have "\<not> Col A B P'"
              by (simp add: \<open>\<not> Col A B P'\<close>) 
            ultimately
            show ?thesis
              using par_not_col_strict by blast 
          qed
          moreover
          have "Col P' Q' Y"
            by (simp add: \<open>Col P' Q' Y\<close>) 
          ultimately
          show ?thesis
            using par_strict_all_one_side by blast 
        qed
        ultimately
        show ?thesis
          using invert_one_side one_side_transitivity by blast 
      qed
      ultimately
      show ?thesis
        using col_one_side_out by blast 
    qed
    hence "\<exists> Y. B Out C Y \<and> Col P Q Y" 
      using P7 by auto
  }
  thus ?thesis
    using weak_inverse_projection_postulate_def by blast
qed

lemma bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle:
  assumes "bachmann_s_lotschnittaxiom"
  shows "weak_triangle_circumscription_principle"
proof -
  have P1: "\<forall> A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD.
              IAB \<noteq> IAC \<and> IAB \<noteq> IBD \<and> A1 A2 Perp B1 B2 \<and> 
              A1 A2 Perp C1 C2 \<and> B1 B2 Perp D1 D2 \<and>
              Col A1 A2 IAB \<and> Col B1 B2 IAB \<and> 
              Col A1 A2 IAC \<and> Col C1 C2 IAC \<and> 
              Col B1 B2 IBD \<and> Col D1 D2 IBD \<and>
              Coplanar IAB IAC IBD C1 \<and> Coplanar IAB IAC IBD C2 \<and>
              Coplanar IAB IAC IBD D1 \<and> Coplanar IAB IAC IBD D2
 \<longrightarrow>
              (\<exists> I. Col C1 C2 I \<and> Col D1 D2 I)"
    using assms bachmann_s_lotschnittaxiom_aux by auto
  moreover
  {
    fix A B C A1 A2 B1 B2
    assume 1: "\<not> Col A B C" and
      2: "Per A C B" and
      3: "A1 A2 PerpBisect B C" and
      4: "B1 B2 PerpBisect A C" and
      5: "Coplanar A B C A1" and
      6: "Coplanar A B C A2" and
      7: "Coplanar A B C B1" and
      8: "Coplanar A B C B2"
    obtain A3 where 9: "A1 \<noteq> A2 \<and> Col A3 A1 A2 \<and> Col A3 B C" 
      using 3 perp_bisect_perp Perp_def PerpAt_def by blast 
    obtain B3 where 10: "B1 \<noteq> B2 \<and> Col B3 B1 B2 \<and> Col B3 A C"
      using 4 perp_bisect_perp Perp_def PerpAt_def by blast 
    have "A \<noteq> B"
      using "1" col_trivial_1 by blast 
    have "B \<noteq> C"
      using "1" col_trivial_2 by auto 
    have "A \<noteq> C"
      using "1" col_trivial_3 by blast
    have "C \<noteq> A3" 
    proof -
      obtain C' where 11: "C' Midpoint C B \<and> Col A1 A2 C'"
        by (metis (full_types) "3" "9" \<open>B \<noteq> C\<close> l4_17 
            l7_20_bis not_col_permutation_2 not_cong_4321 
            perp_bisect_cong_1 perp_bisect_cong_2)
      have "C' \<noteq> C"
        using "11" \<open>B \<noteq> C\<close> cong_reverse_identity midpoint_cong by blast 
      have "C' \<noteq> B"
        using "11" \<open>B \<noteq> C\<close> is_midpoint_id_2 by blast
      {
        assume "C = A3"
        {
          assume "\<not> Col A1 A2 B"
          have "C = C'"
            by (metis "11" "9" \<open>C = A3\<close> \<open>\<not> Col A1 A2 B\<close> 
                colx midpoint_col not_col_permutation_2) 
        }
        moreover
        {
          assume "\<not> Col A1 A2 C"
          have "C = C'"
            using "9" \<open>C = A3\<close> \<open>\<not> Col A1 A2 C\<close> col_permutation_1 by blast 
        }
        ultimately
        have "C = C'" 
          using 3 perp_not_col2 perp_bisect_perp by blast 
        hence "False"
          using \<open>C' \<noteq> C\<close> by blast 
      }
      thus ?thesis by auto
    qed
    moreover
    have "C \<noteq> B3" 
    proof -
      obtain C' where 12: "C' Midpoint C A \<and> Col B1 B2 C'"
        by (metis (full_types) "10" "4" \<open>A \<noteq> C\<close> l4_17 
            l7_20_bis not_col_permutation_2 not_cong_4321 
            perp_bisect_cong_1 perp_bisect_cong_2) 
      have "C' \<noteq> C"
        by (metis "12" \<open>A \<noteq> C\<close> midpoint_distinct_1) 
      have "C' \<noteq> A"
        using "12" \<open>A \<noteq> C\<close> is_midpoint_id_2 by force
      {
        assume "C = B3"
        {
          assume "\<not> Col B1 B2 A"
          have "C = C'"
            by (metis "10" "12" \<open>C = B3\<close> \<open>\<not> Col B1 B2 A\<close> 
                colx midpoint_col not_col_permutation_2) 
        }
        moreover
        {
          assume "\<not> Col B1 B2 C"
          have "C = C'"
            using "10" \<open>C = B3\<close> \<open>\<not> Col B1 B2 C\<close> not_col_permutation_2 by blast 
        }
        ultimately
        have "C = C'" 
          using "4" perp_not_col2 perp_bisect_perp by blast
        hence "False"
          using \<open>C' \<noteq> C\<close> by blast 
      }
      thus ?thesis by auto
    qed
    moreover
    have "B C Perp A C"
      by (metis "2" Perp_perm \<open>A \<noteq> C\<close> \<open>B \<noteq> C\<close> per_perp) 
    moreover
    have "B C Perp A1 A2"
      using "3" Perp_perm perp_bisect_perp by blast 
    moreover
    have "A C Perp B1 B2"
      using "4" Perp_perm perp_bisect_perp by blast 
    moreover
    have "Col B C C"
      by (simp add: col_trivial_2) 
    moreover
    have "Col A C C"
      by (simp add: col_trivial_2) 
    moreover
    have "Col B C A3"
      using "9" not_col_permutation_2 by blast 
    moreover
    have "Col A1 A2 A3"
      using "9" NCol_cases by blast 
    moreover
    have "Col A C B3"
      using "10" Col_perm by blast 
    moreover
    have "Col B1 B2 B3"
      using "10" Col_cases by blast 
    moreover
    have "Coplanar C A3 B3 A1"
    proof -
      have "Coplanar A B C C" 
        using ncop_distincts by blast
      moreover have "Coplanar A B C A3" 
        using \<open>Col B C A3\<close> ncop__ncols by blast
      moreover have "Coplanar A B C B3" 
        using \<open>Col A C B3\<close> ncop__ncols by auto
      ultimately show ?thesis 
        using "1" "5" coplanar_pseudo_trans by blast
    qed
    moreover
    have "Coplanar C A3 B3 A2"
    proof -
      have "Coplanar A B C C" 
        using ncop_distincts by blast
      moreover have "Coplanar A B C A3" 
        using \<open>Col B C A3\<close> ncop__ncols by blast
      moreover have "Coplanar A B C B3" 
        by (meson \<open>Col A C B3\<close> ncop__ncols)
      ultimately show ?thesis 
        using "1" "6" coplanar_pseudo_trans by blast
    qed
    moreover
    have "Coplanar C A3 B3 B1" 
    proof -
      have "Coplanar A B C C" 
        using ncop_distincts by blast
      moreover have "Coplanar A B C A3" 
        using \<open>Col B C A3\<close> ncop__ncols by blast
      moreover have "Coplanar A B C B3" 
        using \<open>Col A C B3\<close> ncop__ncols by blast
      ultimately show ?thesis 
        using "1" "7" coplanar_pseudo_trans by blast
    qed
    moreover
    have "Coplanar C A3 B3 B2" 
    proof -
      have "Coplanar A B C C" 
        using ncop_distincts by blast
      moreover have "Coplanar A B C A3" 
        using \<open>Col B C A3\<close> ncop__ncols by blast
      moreover have "Coplanar A B C B3" 
        using \<open>Col A C B3\<close> ncop__ncols by blast
      ultimately show ?thesis 
        using "1" coplanar_pseudo_trans "8" by blast
    qed
    ultimately
    have "\<exists> I. Col A1 A2 I \<and> Col B1 B2 I"
      using P1 by blast
  }
  thus ?thesis using P1 weak_triangle_circumscription_principle_def by auto
qed

lemma consecutive_interior__alternate_interior:
  assumes "consecutive_interior_angles_postulate"
  shows "alternate_interior_angles_postulate" 
proof -
  {
    fix A B C D
    assume 1: "A C TS B D" and
      2: "A B Par C D"
    obtain D' where 3: "Bet D C D' \<and> Cong C D' C D"
      using segment_construction by blast
    have "A C TS D' D"
      by (metis "1" "3" bet__ts bet_col between_trivial 
          cong_reverse_identity invert_two_sides l9_18 l9_2)
    hence "A C OS B D'"
      using "1" l9_8_1 by blast 
    hence "B A C SuppA A C D'"
      by (metis "2" "3" assms bet_col bet_col1 
          consecutive_interior_angles_postulate_def 
          os_distincts par_col2_par par_comm) 
    moreover
    have "D C A SuppA A C D'"
      by (metis "2" "3" \<open>A C OS B D'\<close> bet__suppa os_distincts par_neq2) 
    ultimately
    have "B A C CongA D C A"
      using suppa2__conga123 by blast 
  }
  thus ?thesis
    by (simp add: alternate_interior_angles_postulate_def) 
qed

lemma existential_playfair__rah_1:
  "postulate_of_right_saccheri_quadrilaterals \<longleftrightarrow> 
   hypothesis_of_right_saccheri_quadrilaterals" 
proof -
  {
    assume "postulate_of_right_saccheri_quadrilaterals"
    {
      fix A B C D
      assume "Saccheri A B C D"
      have "Per A B C"
        using \<open>PostulateRightSaccheriQuadrilaterals\<close> 
          \<open>Saccheri A B C D\<close> postulate_of_right_saccheri_quadrilaterals_def 
        by blast 
    }
    hence "hypothesis_of_right_saccheri_quadrilaterals"
      by (simp add: hypothesis_of_right_saccheri_quadrilaterals_def) 
  }
  moreover
  {
    assume "hypothesis_of_right_saccheri_quadrilaterals"
    {
      fix A B C D
      assume "Saccheri A B C D"
      have "Per A B C"
        using \<open>HypothesisRightSaccheriQuadrilaterals\<close> 
          \<open>Saccheri A B C D\<close> hypothesis_of_right_saccheri_quadrilaterals_def 
        by blast
    }
    hence "postulate_of_right_saccheri_quadrilaterals"
      by (simp add: postulate_of_right_saccheri_quadrilaterals_def) 
  }
  ultimately
  show ?thesis by auto
qed

lemma existential_playfair__rah:
  assumes "existential_playfair_s_postulate"
  shows "postulate_of_right_saccheri_quadrilaterals" 
proof -
  obtain A1 A2 P where 1: "\<not> Col A1 A2 P \<and>
             (\<forall> B1 B2 C1 C2.
                (A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and>
                 A1 A2 Par C1 C2 \<and> Col P C1 C2) \<longrightarrow>
                (Col C1 B1 B2 \<and> Col C2 B1 B2))"
    using assms existential_playfair_s_postulate_def by blast
  have "\<not> Col A1 A2 P"
    using 1 by blast
  have "\<forall> B1 B2 C1 C2.
                (A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and>
                 A1 A2 Par C1 C2 \<and> Col P C1 C2) \<longrightarrow>
                (Col C1 B1 B2 \<and> Col C2 B1 B2)"
    using 1 by blast
  obtain Q where "Col A1 A2 Q \<and> A1 A2 Perp P Q"
    using \<open>\<not> Col A1 A2 P\<close> l8_18_existence by presburger
  have "\<exists> A3. Col A1 A2 A3 \<and> A3 \<noteq> Q"
    by (metis col_trivial_2 diff_col_ex) 
  then obtain A3 where "Col A1 A2 A3 \<and> A3 \<noteq> Q" 
    by auto
  have "P \<noteq> Q"
    using \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close> \<open>\<not> Col A1 A2 P\<close> by auto 
  then obtain R where "P Q Perp R P \<and> Coplanar P Q A3 R"
    using ex_perp_cop by presburger
  have "P Q Perp R P"
    by (simp add: \<open>P Q Perp R P \<and> Coplanar P Q A3 R\<close>) 
  have "Coplanar P Q A3 R"
    by (simp add: \<open>P Q Perp R P \<and> Coplanar P Q A3 R\<close>)
  have "A1 \<noteq> A2"
    using \<open>\<not> Col A1 A2 P\<close> col_trivial_1 by blast 
  have "Q \<noteq> P"
    using \<open>P \<noteq> Q\<close> by auto 
  have "R \<noteq> P"
    using \<open>P Q Perp R P\<close> perp_distinct by auto
  have "A1 A2 Par P R" 
  proof -
    have "Coplanar P Q A1 P"
      using ncop_distincts by blast 
    moreover
    have "Coplanar P R Q A1" 
    proof -
      have "Coplanar P R Q A3"
        by (simp add: \<open>P Q Perp R P \<and> Coplanar P Q A3 R\<close> coplanar_perm_4) 
      moreover
      have "Q \<noteq> A3"
        using \<open>Col A1 A2 A3 \<and> A3 \<noteq> Q\<close> by auto 
      moreover
      have "Col Q A3 A1"
        by (meson \<open>A1 \<noteq> A2\<close> \<open>Col A1 A2 A3 \<and> A3 \<noteq> Q\<close> 
            \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close> col3 col_trivial_3) 
      ultimately
      show ?thesis
        using col_cop__cop by blast 
    qed
    hence "Coplanar P Q A1 R"
      using ncoplanar_perm_4 by blast 
    moreover
    have "Coplanar P Q A2 P"
      using ncop_distincts by blast 
    moreover
    have "Coplanar P R Q A2" 
    proof -
      have "Coplanar P R Q A3"
        by (simp add: \<open>P Q Perp R P \<and> Coplanar P Q A3 R\<close> coplanar_perm_4) 
      moreover
      have "Q \<noteq> A3"
        using \<open>Col A1 A2 A3 \<and> A3 \<noteq> Q\<close> by auto 
      moreover
      have "Col Q A3 A2"
        by (meson \<open>A1 \<noteq> A2\<close> \<open>Col A1 A2 A3 \<and> A3 \<noteq> Q\<close> 
            \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close> col3 col_trivial_2) 
      ultimately
      show ?thesis
        using col_cop__cop by blast 
    qed
    hence "Coplanar P Q A2 R"
      by (simp add: coplanar_perm_3) 
    moreover
    have "A1 A2 Perp P Q"
      by (simp add: \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close>)
    moreover
    have "P R Perp P Q"
      using Perp_perm \<open>P Q Perp R P \<and> Coplanar P Q A3 R\<close> by blast 
    ultimately
    show ?thesis
      using l12_9 by blast 
  qed
  have "Coplanar A1 A2 P R"
    by (simp add: \<open>A1 A2 Par P R\<close> par__coplanar)
  have "A1 A2 ParStrict P R"
    using \<open>A1 A2 Par P R\<close> \<open>\<not> Col A1 A2 P\<close> col_trivial_3 
      par_not_col_strict by blast
  have "\<not> Col A1 A2 R"
    using \<open>A1 A2 ParStrict P R\<close> par_strict_not_col_4 by auto
  obtain S where "Col A1 A2 S \<and> A1 A2 Perp R S"
    using \<open>\<not> Col A1 A2 R\<close> l8_18_existence by blast
  hence "Col A1 A2 S"
    by auto
  have "A1 A2 Perp R S"
    by (simp add: \<open>Col A1 A2 S \<and> A1 A2 Perp R S\<close>)
  have "P Q Par R S" 
  proof -
    have "Coplanar A1 A2 P R"
      by (simp add: \<open>Coplanar A1 A2 P R\<close>) 
    moreover
    have "Coplanar A1 A2 P S"
      using \<open>Col A1 A2 S \<and> A1 A2 Perp R S\<close> ncop__ncols by blast 
    moreover
    have "Coplanar A1 A2 Q R"
      using \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close> ncop__ncols by blast 
    moreover
    have "Coplanar A1 A2 Q S"
      by (meson \<open>\<not> Col A1 A2 P\<close> \<open>\<not> Col A1 A2 R\<close> calculation(1) 
          calculation(2) calculation(3) l9_30 ncop_distincts) 
    moreover
    have "P Q Perp A1 A2"
      using Perp_perm \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close> by blast 
    moreover
    have "R S Perp A1 A2"
      using Perp_perm \<open>Col A1 A2 S \<and> A1 A2 Perp R S\<close> by blast 
    ultimately
    show ?thesis
      using l12_9 by blast 
  qed
  have "\<not> Col P Q R"
    by (simp add: \<open>P Q Perp R P \<and> Coplanar P Q A3 R\<close> perp_not_col) 
  hence "P Q ParStrict R S"
    using \<open>P Q Par R S\<close> col_trivial_3 par_not_col_strict by blast 
  hence "\<not> Col R S P"
    by (meson par_strict_not_col_3) 
  then obtain R' where "Col R S R' \<and> R S Perp P R'"
    using l8_18_existence by blast 
  hence "Col R S R'" 
    by auto
  have "R S Perp P R'"
    by (simp add: \<open>Col R S R' \<and> R S Perp P R'\<close>) 
  have "A1 A2 Par P R'" 
  proof -
    have "Coplanar R P A1 A2"
      using \<open>Coplanar A1 A2 P R\<close> ncoplanar_perm_17 by blast 
    hence "Coplanar R S A1 P" 
      using \<open>Col A1 A2 S\<close> \<open>A1 \<noteq> A2\<close> col_cop__cop coplanar_perm_5 by blast 
    moreover
    have "Coplanar R S A1 R'"
      using \<open>Col R S R'\<close> ncop__ncols by blast 
    moreover
    have "Coplanar R S A2 P"
      by (metis \<open>Col A1 A2 S\<close> \<open>Coplanar R P A1 A2\<close> 
          calculation(1) col_cop__cop coplanar_perm_4 
          not_col_permutation_1) 
    moreover
    have "Coplanar R S A2 R'"
      using \<open>Col R S R'\<close> ncop__ncols by blast 
    moreover
    have "A1 A2 Perp R S"
      by (simp add: \<open>Col A1 A2 S \<and> A1 A2 Perp R S\<close>) 
    moreover
    have "P R' Perp R S"
      using Perp_perm \<open>R S Perp P R'\<close> by blast 
    ultimately
    show ?thesis
      using l12_9 by blast
  qed
  have "Col R' P R" 
    using 1 \<open>A1 A2 Par P R'\<close> \<open>A1 A2 Par P R\<close> col_trivial_1 by blast 
  hence "R = R'" 
    using l6_21
    by (metis Perp_perm \<open>Col R S R' \<and> R S Perp P R'\<close> 
        perp_col perp_not_col) 
  have "P Q ParStrict R S"
    by (simp add: \<open>P Q ParStrict R S\<close>) 
  have "Per Q S R" 
  proof -
    have "Q S Perp R S" 
    proof -
      have "Q \<noteq> S"
        using \<open>P Q ParStrict R S\<close> col_trivial_2 
          par_strict_not_col_4 by blast 
      moreover
      have "Col A1 A2 Q" 
        using \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close> by auto
      ultimately
      show ?thesis
        using \<open>A1 A2 Perp R S\<close> \<open>Col A1 A2 S\<close> perp_col2 by blast 
    qed
    moreover
    have "Col S Q S"
      using col_trivial_3 by blast 
    moreover
    have "Col S R S"
      by (simp add: col_trivial_3) 
    ultimately
    show ?thesis
      using perp_comm perp_per_2 by blast 
  qed
  moreover
  have "Lambert P Q S R"
  proof -
    have "Q \<noteq> S"
      using \<open>P Q ParStrict R S\<close> col_trivial_3 
        par_strict_not_col_2 by blast 
    moreover
    have "S \<noteq> R"
      using \<open>\<not> Col R S P\<close> col_trivial_1 by blast 
    moreover
    have "Per Q P R"
      by (simp add: \<open>P Q Perp R P\<close> perp_per_1) 
    moreover 
    have "Per P R S"
      using \<open>R = R'\<close> \<open>R S Perp P R'\<close> l8_2 perp_per_1 by blast 
    moreover
    have "Per P Q S" 
    proof -
      have "A1 A2 Perp P Q"
        by (simp add: \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close>) 
      moreover
      have "Col A1 A2 Q" 
        using \<open>Col A1 A2 Q \<and> A1 A2 Perp P Q\<close> by auto
      ultimately
      show ?thesis
        using \<open>Q \<noteq> S\<close> \<open>Col A1 A2 S\<close> l8_16_1 by blast 
    qed
    moreover
    have "Coplanar P Q S R"
      using \<open>P Q Par R S\<close> coplanar_perm_1 par__coplanar by blast 
    ultimately
    show ?thesis
      using Lambert_def \<open>Q \<noteq> P\<close> \<open>R \<noteq> P\<close> by blast 
  qed
  ultimately 
  have "hypothesis_of_right_saccheri_quadrilaterals"
    using lam_per__rah_1 by blast 
  show ?thesis
    by (simp add: \<open>HypothesisRightSaccheriQuadrilaterals\<close> 
        existential_playfair__rah_1) 
qed

lemma existential_saccheri__rah:
  assumes "postulate_of_existence_of_a_right_saccheri_quadrilateral"
  shows "postulate_of_right_saccheri_quadrilaterals" 
  using per_sac__rah assms existential_playfair__rah_1 
    postulate_of_existence_of_a_right_saccheri_quadrilateral_def by blast 

lemma existential_triangle__rah:
  assumes "postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights"
  shows "postulate_of_right_saccheri_quadrilaterals" 
  using t22_14__rah assms 
    existential_playfair__rah_1 
    postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights_def 
  by blast 

lemma inverse_projection_postulate__proclus_bis:
  assumes "inverse_projection_postulate"
  shows "alternative_proclus_postulate" 
proof -
  {
    fix A B C D P Q
    assume 1: "P Perp2 A B C D \<and> \<not> Col C D P \<and> Coplanar A B C D \<and>
  Col A B P \<and> \<not> Col A B Q \<and> Coplanar C D P Q"
    hence "P Perp2 A B C D"
      by auto
    have "\<not> Col C D P"
      using 1 by auto
    have "Coplanar A B C D"
      using 1 by auto
    have "Col A B P"
      using 1 by auto
    have "\<not> Col A B Q"
      using 1 by auto
    have "Coplanar C D P Q"
      using 1 by auto
    have "C D ParStrict A B" 
    proof -
      have "Coplanar C D A B"
        by (simp add: \<open>Coplanar A B C D\<close> coplanar_perm_16) 
      moreover
      have "P Perp2 C D A B"
        using "1" perp2_sym by blast 
      ultimately
      show ?thesis 
        using \<open>Col A B P\<close> \<open>\<not> Col C D P\<close> col_cop_perp2__pars_bis by blast 
    qed
    obtain P1 P2 where 2: "Col P P1 P2 \<and> P1 P2 Perp A B \<and> P1 P2 Perp C D"
      using Perp2_def \<open>P Perp2 A B C D\<close> by blast
    have "Col P P1 P2"
      using 2 by blast
    have "P1 P2 Perp A B"
      using 2 by blast
    have "P1 P2 Perp C D"
      using 2 by blast
    then obtain C0 where "C0 PerpAt P1 P2 C D"
      using perp_inter_perp_in_n by blast 
    hence "Col C0 P1 P2 \<and> Col C0 C D"
      using Col_cases perp_in_col by blast 
    hence "Col C0 P1 P2"
      by blast
    have "Col C0 C D"
      using \<open>Col C0 P1 P2 \<and> Col C0 C D\<close> by auto
    obtain P' where "P' PerpAt P1 P2 A B"
      using \<open>P1 P2 Perp A B\<close> perp_inter_perp_in_n by blast
    have "Col P A B"
      using Col_perm \<open>Col A B P\<close> by blast
    hence "P = P'"
      using \<open>Col P P1 P2\<close> \<open>P' PerpAt P1 P2 A B\<close> l8_14_2_1b by blast 
    have "P \<noteq> C0"
    proof -
      {
        assume "P = C0"
        hence "Col P C D"
          by (simp add: \<open>Col C0 C D\<close>) 
        hence "False"
          using \<open>\<not> Col C D P\<close> col_permutation_1 by blast 
      }
      thus ?thesis 
        by auto
    qed
    have "A B Perp P C0" 
    proof -
      have "Col P1 P2 P"
        by (simp add: \<open>Col P P1 P2\<close> col_permutation_1) 
      moreover
      have "Col P1 P2 C0"
        by (simp add: \<open>Col C0 P1 P2\<close> col_permutation_1) 
      ultimately
      show ?thesis
        using \<open>P \<noteq> C0\<close> \<open>P1 P2 Perp A B\<close> perp_col0 by blast 
    qed
    have "C D Perp P C0"
    proof -
      have "Col P1 P2 P"
        by (simp add: \<open>Col P P1 P2\<close> col_permutation_1) 
      moreover
      have "Col P1 P2 C0"
        by (simp add: \<open>Col C0 P1 P2\<close> col_permutation_1) 
      ultimately
      show ?thesis
        using \<open>P \<noteq> C0\<close> \<open>P1 P2 Perp C D\<close> perp_col0 by blast
    qed
    have "P \<noteq> Q"
      using \<open>Col A B P\<close> \<open>\<not> Col A B Q\<close> by auto
    have "\<exists> Y. (Col P Q Y \<and> Col C D Y)" 
    proof (cases "Col P Q C0")
      case True
      thus ?thesis
        using \<open>Col C0 C D\<close> col_permutation_1 by blast 
    next
      case False
      have "\<not> Col C0 A B" 
        using \<open>C D ParStrict A B\<close> \<open>Col C0 C D\<close> par_not_col by blast 
      have "\<exists> Q0. Col Q P Q0 \<and> A B OS C0 Q0" 
      proof -
        have "Q \<noteq> P"
          using \<open>P \<noteq> Q\<close> by auto 
        moreover
        have "Col Q P P"
          by (simp add: col_trivial_2) 
        moreover
        have "\<not> Col A B C0"
          using NCol_perm \<open>\<not> Col C0 A B\<close> by blast 
        moreover
        have "Coplanar A B Q C0" 
        proof -
          have "Coplanar C D P A" 
            by (metis \<open>Col A B P\<close> \<open>Coplanar A B C D\<close> \<open>\<not> Col C0 A B\<close> 
                col_cop__cop coplanar_perm_1 coplanar_perm_16
                not_col_distincts)
          moreover have "Coplanar C D P B" 
            using \<open>Col P A B\<close> \<open>Coplanar A B C D\<close> calculation 
              col_cop__cop coplanar_perm_16 by blast
          moreover have "Coplanar C D P C0" 
            using Col_cases \<open>Col C0 C D\<close> ncop__ncols by blast
          ultimately show ?thesis 
            using \<open>\<not> Col C D P\<close> \<open>Coplanar C D P Q\<close> 
              coplanar_pseudo_trans by blast
        qed
        ultimately
        show ?thesis
          using \<open>\<not> Col A B Q\<close> \<open>Col A B P\<close> cop_not_par_same_side by blast 
      qed
      then obtain Q0 where "Col Q P Q0 \<and> A B OS C0 Q0" 
        by auto
      hence "Col Q P Q0" 
        by auto
      have "A B OS C0 Q0"
        by (simp add: \<open>Col Q P Q0 \<and> A B OS C0 Q0\<close>) 
      have "\<not> Col A B Q0"
        using \<open>Col Q P Q0 \<and> A B OS C0 Q0\<close> one_side_not_col124 by blast
      {
        assume "P = Q0" 
        hence "Col A B P"
          using \<open>Col A B P\<close> by auto 
        hence "False"
          by (simp add: \<open>P = Q0\<close> \<open>\<not> Col A B Q0\<close>) 
      }
      hence "P \<noteq> Q0"
        by auto
      have "\<not> Col P C0 Q0"
        by (metis False \<open>Col Q P Q0\<close> \<open>P \<noteq> Q0\<close> col_transitivity_1 
            not_col_permutation_2)
      have "\<exists> C1. Col C D C1 \<and> C1 \<noteq> C0"
        by (metis col_trivial_3 diff_col_ex)
      then obtain C1 where "Col C D C1 \<and> C1 \<noteq> C0"
        by auto
      hence "Col C D C1"
        by auto
      have "C1 \<noteq> C0"
        by (simp add: \<open>Col C D C1 \<and> C1 \<noteq> C0\<close>)
      have "\<exists> A0. Col A B A0 \<and> P C0 OS Q0 A0" 
      proof (cases "Col P C0 A")
        case True
        have "\<not> Col P C0 B"
          using True \<open>P \<noteq> C0\<close> \<open>\<not> Col C0 A B\<close> col_transitivity_2 by blast
        have "\<exists> Q. Col B A Q \<and> P C0 OS Q0 Q" 
        proof -
          have "B \<noteq> A"
            using \<open>\<not> Col C0 A B\<close> col_trivial_2 by auto 
          moreover
          have "Col P C0 P"
            by (simp add: col_trivial_3) 
          moreover
          have "Col B A P"
            using Col_cases \<open>Col A B P\<close> by blast 
          moreover
          have "\<not> Col P C0 B"
            by (simp add: \<open>\<not> Col P C0 B\<close>) 
          moreover
          have "\<not> Col P C0 Q0"
            by (simp add: \<open>\<not> Col P C0 Q0\<close>) 
          moreover
          have "Coplanar P C0 B Q0"
            by (metis True \<open>Col P A B\<close> \<open>Col Q P Q0 \<and> A B OS C0 Q0\<close> 
                calculation(2) calculation(4) colx 
                coplanar_perm_2 os__coplanar) 
          ultimately
          show ?thesis
            using cop_not_par_same_side by blast 
        qed
        thus ?thesis
          using not_col_permutation_4 by blast 
      next
        case False
        have "Coplanar P C0 A Q0"
          by (metis False \<open>Col A B P\<close> \<open>Col Q P Q0 \<and> A B OS C0 Q0\<close> 
              col2_os__os col_trivial_3 coplanar_perm_2 os__coplanar) 
        thus ?thesis
          by (metis False \<open>Col A B P\<close> \<open>\<not> Col C0 A B\<close> \<open>\<not> Col P C0 Q0\<close> 
              col_trivial_2 col_trivial_3 cop_not_par_same_side) 
      qed
      then obtain A0 where "Col A B A0 \<and> P C0 OS Q0 A0"
        by auto
      hence "Col A B A0" 
        by auto
      have "P C0 OS Q0 A0"
        by (simp add: \<open>Col A B A0 \<and> P C0 OS Q0 A0\<close>)
      have "\<not> Col P C0 A0"
        using \<open>P C0 OS Q0 A0\<close> one_side_not_col124 by blast 
      have "\<exists> Y. P Out Q0 Y \<and> Col C0 C1 Y" 
      proof -
        have "Acute C0 P Q0" 
        proof -
          have "A B Perp C0 P"
            by (simp add: \<open>A B Perp P C0\<close> perp_right_comm) 
          hence "Per C0 P A0" 
            using \<open>Col A B P\<close> \<open>Col A B A0\<close> l8_16_1 by blast
          moreover
          have "C0 P Q0 LtA C0 P A0" 
          proof -
            have "P A0 OS C0 Q0"
              by (metis \<open>Col A B A0 \<and> P C0 OS Q0 A0\<close> \<open>Col A B P\<close> 
                  \<open>Col Q P Q0 \<and> A B OS C0 Q0\<close> \<open>\<not> Col P C0 A0\<close> 
                  col2_os__os col_trivial_3) 
            hence "Q0 InAngle C0 P A0"
              by (simp add: \<open>P C0 OS Q0 A0\<close> one_side_symmetry os2__inangle) 
            hence "C0 P Q0 LeA C0 P A0"
              using inangle__lea by force 
            moreover
            {
              assume "C0 P Q0 CongA C0 P A0"
              have "C0 P OS Q0 A0"
                by (meson \<open>P C0 OS Q0 A0\<close> invert_one_side) 
              hence "P Out Q0 A0" 
                using conga_os__out
                using \<open>C0 P Q0 CongA C0 P A0\<close> by blast 
              hence "Col A B Q0"
                using \<open>P A0 OS C0 Q0\<close> os_distincts out_out_one_side by blast 
              hence "False"
                using \<open>\<not> Col A B Q0\<close> by auto 
            }
            hence "\<not> C0 P Q0 CongA C0 P A0" 
              by auto
            ultimately
            show ?thesis
              using LtA_def by blast 
          qed
          ultimately
          show ?thesis
            using Acute_def by blast 
        qed
        moreover
        have "P Out C0 C0"
          using \<open>P \<noteq> C0\<close> out_trivial by auto 
        moreover
        have "C0 \<noteq> C1"
          using \<open>C1 \<noteq> C0\<close> by blast 
        moreover
        have "Col C D C0"
          by (simp add: \<open>Col C0 C D\<close> col_permutation_1) 
        hence "Per P C0 C1" 
          using l8_16_1 \<open>C D Perp P C0\<close> \<open>Col C D C1\<close> by blast
        moreover
        have "Coplanar C0 P Q0 C1" 
        proof -
          have "Coplanar C D P C0" 
            using \<open>Col C D C0\<close> ncop__ncols by blast
          moreover have "Coplanar C D P P" 
            using ncop_distincts by auto
          moreover have "Coplanar C D P Q0" 
            by (metis \<open>Col Q P Q0\<close> \<open>Coplanar C D P Q\<close> 
                \<open>P \<noteq> Q\<close> calculation(2) col_cop2__cop)
          moreover have "Coplanar C D P C1" 
            using \<open>Col C D C1\<close> ncop__ncols by blast
          ultimately show ?thesis
            using \<open>\<not> Col C D P\<close> coplanar_pseudo_trans by blast
        qed
        ultimately
        show ?thesis 
          using assms inverse_projection_postulate_def by blast
      qed
      then obtain Y where "P Out Q0 Y" and "Col C0 C1 Y" 
        by blast
      have "Col P Q Y" 
        by (meson \<open>Col Q P Q0\<close> \<open>P Out Q0 Y\<close> \<open>P \<noteq> Q0\<close> 
            col_permutation_1 l6_16_1 out_col)
      have "Col C D Y" 
        by (metis \<open>Col C D C1 \<and> C1 \<noteq> C0\<close> \<open>Col C0 C D\<close> 
            \<open>Col C0 C1 Y\<close> colx not_col_permutation_2)
      thus ?thesis 
        using \<open>Col P Q Y\<close> by blast
    qed
  }
  thus ?thesis
    using alternative_proclus_postulate_def by fastforce 
qed

(** Given a non-degenerated parallelogram PRQS and a point U not on line PR,
    the lines PU and SQ intersect. *)

lemma strong_parallel_postulate_implies_inter_dec:
  (*  assumes "strong_parallel_postulate"*)
  shows "decidability_of_intersection" 
proof -
  {
    fix P Q S U
    have "(\<exists> I. Col I S Q \<and> Col I P U) \<or> \<not> (\<exists> I. Col I S Q  \<and> Col I P U)"
      by blast
  }
  thus ?thesis
    using decidability_of_intersection_def by blast 
qed

lemma impossible_case_1:
  assumes "Bet A B x" and
    "Bet C y A" and
    "B C ParStrict x y"
  shows "False" 
proof -
  have "Bet x B A"
    using Bet_cases assms(1) by blast
  then obtain I where "Bet B I C \<and> Bet y I x"
    using assms(2) inner_pasch by presburger 
  thus ?thesis
    by (meson assms(3) bet_col col_permutation_1 col_permutation_4 par_not_col) 
qed

lemma impossible_case_2:
  assumes "A \<noteq> D" and
    "B \<noteq> D" and
    (*  "C \<noteq> D" and  
  "D \<noteq> T" and  *)
    "\<not> Col A B C" and
    "Col A B x" and
    "Bet A D T" and
    (*  "\<not> Col B C T" and *)
    "Bet B D C" and
    "Bet y A C" and
    "Bet x T y"
  shows "False" 
proof -
  {
    assume "A = y" 
    hence "Col A B C" 
      by (metis NCol_perm assms(2) assms(4) assms(5) assms(6) 
          assms(8) bet_col between_identity col_trivial_2 colx)
    hence False 
      using assms(3) by auto
  }
  hence "A \<noteq> y" 
    by blast
  have "A B TS y T"
  proof -
    have "A B TS C y"
      by (simp add: \<open>A \<noteq> y\<close> assms(7) assms(3) bet__ts between_symmetry) 
    moreover
    have "A B OS C T"
      using bet_out calculation invert_one_side l9_8_1 
        one_side_not_col124 one_side_symmetry out_one_side 
        out_out_one_side by (metis assms(1) assms(2) assms(5) assms(6)) 
    ultimately
    show ?thesis
      using l9_2 l9_8_2 by blast 
  qed
  hence "A B OS T x"
    using Bet_cases assms(8) bet_ts__os by blast 
  thus ?thesis
    using assms(4) col124__nos by auto 
qed

lemma impossible_case_3:
  assumes (* "A \<noteq> D" and
  "B \<noteq> D" and
  "C \<noteq> D" and
  "D \<noteq> T" and
"\<not> Col A B C" and*)
    "Bet A D T" and
    "\<not> Col B C T" and
    "Bet B D C" and
    "Bet B x A" and
    "Bet x T y" and
    "B C ParStrict x y"
  shows "False"
proof -
  have "B C OS x y"
    using assms(6) l12_6 by blast
  hence "B C TS x T"
    by (metis (full_types) Col_cases \<open>B C OS x y\<close> 
        assms(1) assms(2) assms(3) assms(4) bet_col bet_out 
        between_trivial l9_18 l9_8_2 one_side_not_col124 
        one_side_symmetry out_out_one_side) 
  hence "B C TS x y"
    by (meson assms(5) bet_ts__ts) 
  thus ?thesis
    using \<open>B C OS x y\<close> l9_9 by blast 
qed

lemma impossible_case_4_1:
  assumes "A \<noteq> D" and
    "C \<noteq> D" and
    "\<not> Col A B C" and
    "Col A C y" and
    "Bet A D T" and
    (*  "\<not> Col B C T" and*)
    "Bet B D C" and
    "A Out B x" and
    "Bet T y x"
  shows "False" 
proof -
  have "A C OS B D"
    by (metis assms(2) assms(3) assms(6) bet_col 
        between_equality_2 col_permutation_4 col_trivial_2 
        cop_nos__ts l6_21 l9_18 ncop__ncols not_col_permutation_5) 
  hence "A C OS T x "
    by (metis assms(1) assms(5) assms(7) bet_out 
        col_trivial_3 one_side_symmetry os_out_os)
  hence "A C OS T y"
    using assms(8) l9_17 by blast 
  thus ?thesis
    using assms(4) one_side_not_col124 by auto 
qed

lemma impossible_case_4_2:
  assumes "\<not> Col A B C" and
    "Col A C y" and
    "Bet A D T" and
    "\<not> Col B C T" and
    "Bet B D C" and
    "Bet B A x" and
    "Bet T y x" and
    "B C ParStrict x y"
  shows "False"
proof -
  have "B C TS A T"
    by (metis Col_cases TS_def assms(1) assms(3) assms(4) 
        assms(5) bet_out_1 not_col_distincts out_col) 
  have "B C OS A x"
    by (metis assms(1) assms(6) bet_out not_col_distincts 
        one_side_reflexivity out_out_one_side) 
  hence "B C TS x T"
    using \<open>B C TS A T\<close> l9_8_2 by blast 
  hence "T \<noteq> x"
    using ts_distincts by blast 
  have "B C ParStrict x T"
    by (metis \<open>B C TS x T\<close> assms(7) assms(8) bet_col 
        between_symmetry par_strict_col_par_strict ts_distincts)
  thus ?thesis
    by (meson \<open>B C TS x T\<close> l12_6 l9_9) 
qed

lemma impossible_case_4:
  assumes "A \<noteq> D" and
    (* "B \<noteq> D" and*)
    "C \<noteq> D" and
    "D \<noteq> T" and
    "\<not> Col A B C" and
    "Col A C y" and
    "Bet A D T" and
    "\<not> Col B C T" and
    "Bet B D C" and
    "Col A B x" and
    "Bet T y x" and
    "B C ParStrict x y"
  shows "False" 
proof -
  have "Bet A B x \<or> A Out B x \<or> B Out x A"
    using assms(9) l6_6 or_bet_out by blast
  moreover
  have "\<not> Bet A B x"
    by (metis assms(1) assms(10) assms(2) assms(4) assms(5) 
        assms(6) assms(8) bet_out impossible_case_4_1 not_col_distincts) 
  moreover
  have "\<not> A Out B x "
    using assms(1) assms(10) assms(2) assms(4) assms(5) 
      assms(6) assms(8) impossible_case_4_1 by blast
  moreover
  have "\<not> B Out x A" 
    using calculation(3) impossible_case_4_2 
    by (meson assms(9) assms(10) assms(11) assms(4) 
        assms(5) assms(6) assms(7) assms(8) 
        col_permutation_4 or_bet_out)  
  ultimately
  show ?thesis by blast
qed

lemma impossible_two_sides_not_col:
  assumes "A \<noteq> D" and
    (* "B \<noteq> D" and*)
    "C \<noteq> D" and
    (* "D \<noteq> T" and*)
    "\<not> Col A B C" and
    "Bet A D T" and
    (*"\<not> Col B C T" and*)
    "Bet B D C" and
    "Bet B Y T" 
  shows "\<not> Col A C Y" 
proof -
  have "A C OS B D"
    by (metis Col_perm assms(2) assms(3) assms(5) 
        bet_col between_equality_2 invert_one_side l6_4_1 
        out_one_side out_to_bet)
  have "A C OS D T"
    by (metis \<open>A C OS B D\<close> assms(1) assms(4) bet_out 
        col124__nos out_one_side) 
  hence "A C OS B T"
    using \<open>A C OS B D\<close> one_side_transitivity by blast 
  hence "A C OS B Y"
    using assms(6) l9_17 by blast 
  thus ?thesis
    using one_side_not_col124 by auto 
qed

(** Non degenerated triangles can be circumscribed. *)
lemma triangle_circumscription_implies_tarski_s_euclid_aux1:
  assumes "triangle_circumscription_principle" and
    "B \<noteq> D" and
    "C \<noteq> D" and
    "D \<noteq> T" and
    "T \<noteq> X" and 
    "\<not> Col A B C" and
    "Col A B M1" and
    "Bet A D T" and
    "\<not> Col B C T" and
    "Bet B D C" and
    "Col T Y Z" and
    "Bet Y T X" and
    "Bet Y M1 Z1" and
    "Cong Y T T X" and
    "Cong Y M1 M1 Z1" and
    "B C Perp T Z" and
    "A B Perp Y Z1"
  shows "\<exists>x. Col A B x \<and> B C ParStrict x T \<and> Cong X x Y x" 
proof -
  have "A \<noteq> D"
    using Bet_cases Col_def assms(10) assms(6) by blast
  have "B \<noteq> C"
    using assms(6) col_trivial_2 by blast 
  have "A \<noteq> B"
    using assms(6) col_trivial_1 by auto 
  have "A \<noteq> C"
    using assms(6) col_trivial_3 by blast 
  have "X \<noteq> Y"
    using assms(12) assms(5) between_identity by blast 
  have "Y \<noteq> T"
    using assms(14) assms(5) cong_reverse_identity by blast 
  have "Y \<noteq> Z1"
    using assms(17) perp_not_eq_2 by auto 
  have "T \<noteq> Z"
    using assms(16) perp_not_eq_2 by blast
  have "Coplanar B C T A"
    by (metis assms(10) assms(8) bet__coplanar bet_cop__tsp 
        coplanar_perm_1 coplanar_perm_5 tsp_distincts)
  have "Coplanar B C T B"
    using ncop_distincts by blast 
  have "Coplanar B C T C"
    using ncop_distincts by blast 
  have "Coplanar B C T T"
    using ncop_distincts by auto 
  have "Coplanar B C T Z"
    by (simp add: assms(16) perp__coplanar)
  have "Coplanar B C T Y"
    by (meson \<open>Coplanar B C T Z\<close> \<open>T \<noteq> Z\<close> assms(11) 
        col_cop__cop not_col_permutation_5) 
  have "Coplanar B C T X"
    using \<open>Coplanar B C T T\<close> \<open>Coplanar B C T Y\<close> \<open>Y \<noteq> T\<close> 
      assms(12) bet_col col_cop2__cop by blast
  {
    assume "Col X Y Z1"
    hence "Col T Z Z1" 
      by (metis Col_perm \<open>Y \<noteq> T\<close> assms(11) assms(12) bet_col 
          between_identity col_transitivity_1)
    have "Coplanar B C Y Z1"
      by (metis Col_cases \<open>Col T Z Z1\<close> \<open>Coplanar B C T Y\<close> 
          \<open>T \<noteq> Z\<close> \<open>Y \<noteq> T\<close> assms(11) col_cop__cop col_trivial_3 
          colx coplanar_perm_1)
    have "B A Par B C" 
    proof -
      have "Coplanar Y Z1 A C"
      proof -
        have "Coplanar B C T Z1" 
          using \<open>Col T Z Z1\<close> \<open>Coplanar B C T Z\<close> \<open>T \<noteq> Z\<close> col_cop__cop by blast
        moreover have "Coplanar B C T C" 
          using \<open>Coplanar B C T C\<close> by auto
        ultimately show ?thesis 
          using assms(9) \<open>Coplanar B C T A\<close> 
            \<open>Coplanar B C T Y\<close> coplanar_pseudo_trans by presburger
      qed
      moreover
      have "B C Perp Y Z1" 
      proof -
        have "T Z Perp B C"
          using Perp_perm assms(16) by blast 
        moreover
        have "Col T Z Y"
          using Col_cases assms(11) by blast 
        ultimately
        show ?thesis
          using \<open>Y \<noteq> Z1\<close> \<open>Col T Z Z1\<close> perp_col0 by blast 
      qed
      ultimately
      show ?thesis
        by (metis \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> assms(17) cop_perp2__col 
            not_par_not_col perp_comm perp_right_comm) 
    qed
    hence "False"
      using assms(6) par_id_1 by auto 
  }
  hence "\<not> Col X Y Z1"
    by blast 
  obtain x where "Cong X x Y x \<and> Cong X x Z1 x \<and> Coplanar X Y Z1 x" 
    using triangle_circumscription_principle_def 
      \<open>\<not> Col X Y Z1\<close> assms(1) by blast 
  have "Cong X x Y x"
    by (simp add: \<open>Cong X x Y x \<and> Cong X x Z1 x \<and> Coplanar X Y Z1 x\<close>) 
  have "Cong X x Z1 x"
    by (simp add: \<open>Cong X x Y x \<and> Cong X x Z1 x \<and> Coplanar X Y Z1 x\<close>)
  have "Coplanar X Y Z1 x"
    by (simp add: \<open>Cong X x Y x \<and> Cong X x Z1 x \<and> Coplanar X Y Z1 x\<close>)
  have "Y \<noteq> M1"
    using \<open>Y \<noteq> Z1\<close> assms(15) cong_reverse_identity by blast
  have "Coplanar B C T Z1"
    by (meson \<open>A \<noteq> B\<close> \<open>Coplanar B C T A\<close> \<open>Coplanar B C T B\<close> 
        \<open>Coplanar B C T Y\<close> \<open>Y \<noteq> M1\<close> assms(13) assms(7) 
        bet_col col_cop2__cop)
  have "Coplanar B C T x"
    by (meson \<open>Coplanar B C T X\<close> \<open>Coplanar B C T Y\<close> 
        \<open>Coplanar B C T Z1\<close> \<open>Coplanar X Y Z1 x\<close> \<open>\<not> Col X Y Z1\<close> 
        l9_30 ncop_distincts)
  have "Col A B x"
  proof -
    have "Coplanar A x Y Z1"
      using assms(9) \<open>Coplanar B C T A\<close> \<open>Coplanar B C T Y\<close> 
        \<open>Coplanar B C T Z1\<close> \<open>Coplanar B C T x\<close> 
        coplanar_pseudo_trans by blast 
    moreover
    have "Coplanar B x Y Z1" 
      using assms(9) 
      by (meson \<open>Coplanar B C T B\<close> \<open>Coplanar B C T Y\<close> 
          \<open>Coplanar B C T Z1\<close> \<open>Coplanar B C T x\<close> coplanar_pseudo_trans) 
    moreover
    have "Cong x Y x Z1" 
    proof -
      have "Cong x Y X x"
        using \<open>Cong X x Y x\<close> not_cong_3421 by blast 
      moreover
      have "Cong X x x Z1"
        using \<open>Cong X x Z1 x\<close> not_cong_1243 by blast 
      ultimately
      show ?thesis
        by (meson cong_transitivity) 
    qed
    moreover
    have "A B PerpBisect Y Z1"
    proof -
      have "M1 Midpoint Y Z1" 
        by (simp add: Midpoint_def assms(13) assms(15))
      hence "(\<exists> X. X Midpoint Y Z1 \<and> Col A B X) \<and> (A B Perp Y Z1 \<or> Y = Z1)" 
        using assms(7) assms(17) by blast
      hence "Y Z1 ReflectL A B" 
        using ReflectL_def l10_4_spec by presburger 
      thus ?thesis  
        using \<open>Y \<noteq> Z1\<close> Perp_bisect_def by auto
    qed
    ultimately
    show ?thesis
      using cong_cop2_perp_bisect_col by blast 
  qed
  have "B C ParStrict x T" 
  proof -
    have "B C Par x T" 
    proof -
      have "Coplanar X Y B x"
        by (meson \<open>Coplanar B C T B\<close> \<open>Coplanar B C T X\<close> 
            \<open>Coplanar B C T Y\<close> \<open>Coplanar B C T x\<close> assms(9) 
            coplanar_pseudo_trans) 
      moreover
      have "Coplanar X Y B T"
        by (meson \<open>Coplanar B C T B\<close> \<open>Coplanar B C T T\<close> 
            \<open>Coplanar B C T X\<close> \<open>Coplanar B C T Y\<close> assms(9) 
            coplanar_pseudo_trans) 
      moreover
      have "Coplanar X Y C x"
        by (meson \<open>Coplanar B C T C\<close> \<open>Coplanar B C T X\<close> 
            \<open>Coplanar B C T Y\<close> \<open>Coplanar B C T x\<close> assms(9) 
            coplanar_pseudo_trans) 
      moreover
      have "Coplanar X Y C T"
        by (meson \<open>Coplanar B C T C\<close> \<open>Coplanar B C T T\<close> 
            \<open>Coplanar B C T X\<close> \<open>Coplanar B C T Y\<close> assms(9) 
            coplanar_pseudo_trans) 
      moreover
      have "B C Perp X Y" 
      proof -
        have "T Z Perp B C"
          using Perp_cases assms(16) by blast 
        moreover
        have "Col T Z X"
          by (meson \<open>Y \<noteq> T\<close> assms(11) assms(12) bet_col 
              bet_col1 col3 not_col_permutation_4) 
        moreover
        have "Col T Z Y"
          by (simp add: assms(11) col_permutation_5) 
        ultimately
        show ?thesis
          using \<open>X \<noteq> Y\<close> perp_col0 by blast 
      qed
      moreover
      have "x T PerpBisect X Y" 
      proof -
        have "x \<noteq> T"
          using \<open>A \<noteq> D\<close> \<open>Col A B x\<close> assms(10) assms(2) 
            assms(6) assms(8) between_trivial2 
            impossible_case_2 by blast 
        moreover
        have "Coplanar x T X Y"
          by (meson assms(12) bet_col ncop__ncol ncoplanar_perm_21) 
        moreover
        have "Cong X T Y T"
          by (meson assms(14) not_cong_3421) 
        ultimately
        show ?thesis
          using \<open>Cong X x Y x\<close> \<open>X \<noteq> Y\<close> cong_cop_perp_bisect by presburger 
      qed
      hence "x T Perp X Y"
        by (simp add: perp_bisect_perp) 
      ultimately
      show ?thesis
        using l12_9 by blast
    qed
    moreover
    have "Col x T T"
      by (simp add: col_trivial_2) 
    moreover
    have "\<not> Col B C T"
      by (simp add: assms(9)) 
    ultimately
    show ?thesis
      using par_not_col_strict by blast 
  qed
  thus ?thesis
    using \<open>Col A B x\<close> \<open>Cong X x Y x\<close> by blast 
qed

lemma triangle_circumscription_implies_tarski_s_euclid_aux:
  assumes "triangle_circumscription_principle" and
    "B \<noteq> D" and
    "C \<noteq> D" and
    "D \<noteq> T" and
    "T \<noteq> X" and
    "\<not> Col A B C" and
    "Col A B M1" and
    "Col A C M2" and
    "Bet A D T" and
    "\<not> Col B C T" and
    "Bet B D C" and
    "Col T Y Z" and
    "Bet Y T X" and
    "Bet Y M1 Z1" and
    "Bet Y M2 Z2" and
    "Cong Y T T X" and
    "Cong Y M1 M1 Z1" and
    "Cong Y M2 M2 Z2" and
    "B C Perp T Z" and
    "A B Perp Y Z1" and
    "A C Perp Y Z2"
  shows "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y" 
proof -
  have "\<exists>x. Col A B x \<and> B C ParStrict x T \<and> Cong X x Y x" 
    using triangle_circumscription_implies_tarski_s_euclid_aux1 
      assms(1) assms(2) assms(3) assms(4) assms(5) 
      assms(6) assms(7) assms(9) assms(10)  
      assms(11) assms(12) assms(13) assms(14)   
      assms(16) assms(17) assms(19) assms(20)  
    by blast  
  then obtain x where "Col A B x \<and> B C ParStrict x T \<and> Cong X x Y x" 
    by auto
  hence "Col A B x" 
    by auto
  have "B C ParStrict x T"
    by (simp add: \<open>Col A B x \<and> B C ParStrict x T \<and> Cong X x Y x\<close>) 
  have "Cong X x Y x" 
    by (simp add: \<open>Col A B x \<and> B C ParStrict x T \<and> Cong X x Y x\<close>) 
  have "\<exists> y. Col A C y \<and> C B ParStrict y T \<and> Cong X y Y y" 
  proof -
    have "\<not> Col A C B"
      using assms(6) col_permutation_5 by blast 
    moreover
    have "Col A C M2"
      by (simp add: assms(8)) 
    moreover
    have "Bet A D T"
      by (simp add: assms(9)) 
    moreover
    have "\<not> Col C B T"
      using NCol_cases assms(10) by blast 
    moreover
    have "Bet C D B"
      using Bet_cases assms(11) by blast 
    moreover
    have "C B Perp T Z"
      by (simp add: assms(19) perp_left_comm) 
    ultimately
    show ?thesis 
      using triangle_circumscription_implies_tarski_s_euclid_aux1 
        assms(1) assms(2) assms(3) assms(4) assms(5) 
        assms(8) assms(9) assms(12) assms(13)  assms(15)  
        assms(16)  assms(18) assms(21) by blast
  qed
  then obtain y where "Col A C y \<and> C B ParStrict y T \<and> Cong X y Y y" 
    by auto
  hence "Col A C y" 
    by auto
  have "C B ParStrict y T" 
    by (simp add: \<open>Col A C y \<and> C B ParStrict y T \<and> Cong X y Y y\<close>) 
  have "Cong X y Y y"
    by (simp add: \<open>Col A C y \<and> C B ParStrict y T \<and> Cong X y Y y\<close>) 
  have "Col x T y" 
  proof (cases "x = T")
    case True
    thus ?thesis
      by (simp add: col_trivial_1) 
  next
    case False
    thus ?thesis 
    proof (cases "y = T")
      case True
      thus ?thesis
        using col_trivial_2 by auto 
    next
      case False
      thus ?thesis
      proof -
        have "X \<noteq> Y"
          using assms(13) assms(5) between_identity by blast 
        have "Y \<noteq> T"
          using assms(16) assms(5) cong_reverse_identity by blast 
        have "T \<noteq> Z"
          using assms(19) perp_not_eq_2 by auto 
        have "Coplanar X Y x y"
        proof -
          have "Coplanar B C T Y" 
          proof -
            have "Coplanar B C T Z"
              using assms(19) perp__coplanar by auto 
            moreover
            have "Col T Z Y"
              by (simp add: assms(12) col_permutation_5)
            ultimately
            show ?thesis
              using \<open>T \<noteq> Z\<close> col_cop__cop by blast 
          qed
          moreover
          have "Coplanar B C T X"
            by (meson \<open>Coplanar B C T Y\<close> \<open>Y \<noteq> T\<close> assms(13) 
                bet_col bet_col1 col2_cop__cop ncoplanar_perm_7) 
          moreover 
          have "Coplanar B C T x"
            by (meson \<open>B C ParStrict x T\<close> par_strict_right_comm 
                pars__coplanar) 
          moreover
          have "Coplanar B C T y"
            by (simp add: \<open>C B ParStrict y T\<close> par_strict_comm 
                pars__coplanar) 
          ultimately
          show ?thesis
            by (meson assms(10) coplanar_pseudo_trans) 
        qed
        moreover
        have "T x PerpBisect X Y" 
        proof -
          have "T \<noteq> x"
            using \<open>B C ParStrict x T\<close> par_strict_distinct by blast 
          moreover
          have "Coplanar T x X Y"
            by (meson assms(13) assms(16) midpoint__coplanar 
                midpoint_def ncoplanar_perm_5) 
          moreover
          have "Cong X T Y T"
            using Cong_perm assms(16) by blast 
          ultimately
          show ?thesis
            using \<open>X \<noteq> Y\<close> \<open>Cong X x Y x\<close> cong_cop_perp_bisect by auto
        qed
        hence "T x Perp X Y" 
          using perp_bisect_perp by auto
        moreover
        have "T y PerpBisect X Y" 
        proof -
          have "T \<noteq> y"
            using False by auto 
          moreover
          have "Coplanar T y X Y"
            by (meson assms(13) bet__coplanar between_symmetry 
                ncoplanar_perm_13) 
          moreover
          have "Cong X T Y T"
            using assms(16) cong_4312 by blast
          ultimately
          show ?thesis
            by (simp add: \<open>Cong X y Y y\<close> \<open>X \<noteq> Y\<close> cong_cop_perp_bisect) 
        qed
        hence "T y Perp X Y"
          by (simp add: perp_bisect_perp) 
        ultimately
        show ?thesis
          using col_permutation_4 cop_perp2__col by blast 
      qed
    qed
  qed
  have "B C ParStrict x y" 
  proof -
    {
      assume "x = y"
      hence "A \<noteq> C" 
        using assms(6) col_trivial_3 by force
      hence "A = x" 
        using NCol_perm \<open>Col A B x\<close> \<open>Col A C y\<close> \<open>x = y\<close> assms(6) 
          col_trivial_3 colx by blast
      hence "\<exists> X0. Col X0 B C \<and> Col X0 x T" 
        using Bet_cases Col_def assms(11) assms(9) by blast
      hence False 
        using \<open>B C ParStrict x T\<close> par_not_col by blast
    }
    moreover have "B C ParStrict x T" 
      using \<open>B C ParStrict x T\<close> by blast
    moreover have "Col x T y" 
      by (simp add: \<open>Col x T y\<close>)
    ultimately show ?thesis 
      using par_strict_col_par_strict by blast
  qed
  have "A \<noteq> D"
    using Col_cases assms(11) assms(6) bet_col by blast 
  {
    assume "Bet x T y"
    {
      assume "Bet A B x"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        using Col_def \<open>A \<noteq> D\<close> \<open>B C ParStrict x y\<close> \<open>Bet x T y\<close> 
          \<open>Col A B x\<close> \<open>Col A C y\<close> assms(11) assms(2) assms(6) assms(9) 
          impossible_case_1 impossible_case_2 by blast 
    }
    moreover
    {
      assume "Bet B x A"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        using \<open>B C ParStrict x y\<close> \<open>Bet x T y\<close> assms(10) 
          assms(11) assms(9) impossible_case_3 by blast 
    }
    moreover
    {
      assume "Bet x A B"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        by (meson \<open>A \<noteq> D\<close> \<open>Bet x T y\<close> \<open>Col A C y\<close> assms(11) 
            assms(3) assms(6) assms(9) between_symmetry 
            col_permutation_5 impossible_case_2) 
    }
    ultimately
    have "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
      using Col_def \<open>Col A B x\<close> by blast 
  }
  moreover
  {
    assume "Bet T y x"
    {
      assume "Bet A B x"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        using \<open>A \<noteq> D\<close> \<open>B C ParStrict x y\<close> \<open>Bet T y x\<close> 
          \<open>Col A B x\<close> \<open>Col A C y\<close> assms(10) assms(11) assms(3) 
          assms(4) assms(6) assms(9) impossible_case_4 by blast 
    }
    moreover
    {
      assume "Bet B x A"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        using \<open>A \<noteq> D\<close> \<open>B C ParStrict x y\<close> \<open>Bet T y x\<close> \<open>Col A B x\<close> 
          \<open>Col A C y\<close> assms(10) assms(11) assms(3) assms(4) assms(6) 
          assms(9) impossible_case_4 by blast 
    }
    moreover
    {
      assume "Bet x A B"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        using \<open>A \<noteq> D\<close> \<open>B C ParStrict x y\<close> \<open>Bet T y x\<close> 
          \<open>Col A B x\<close> \<open>Col A C y\<close> assms(10) assms(11) assms(3) assms(4) 
          assms(6) assms(9) impossible_case_4 by blast 
    }
    ultimately
    have "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
      using Col_def \<open>Col A B x\<close> by blast 
  }
  moreover
  {
    assume "Bet y x T"
    {
      assume "Bet A B x"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        by (meson \<open>A \<noteq> D\<close> \<open>B C ParStrict x y\<close> \<open>Bet y x T\<close> 
            \<open>Col A B x\<close> \<open>Col A C y\<close> assms(10) assms(11) assms(2) 
            assms(4) assms(6) assms(9) between_symmetry 
            col_permutation_5 impossible_case_4 
            not_col_permutation_3 par_strict_comm) 
    }
    moreover
    {
      assume "Bet B x A"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        using \<open>B C ParStrict x T\<close> assms(10) assms(11) 
          assms(9) between_trivial impossible_case_3 by blast 
    }
    moreover
    {
      assume "Bet x A B"
      hence "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
        by (meson Par_strict_cases \<open>A \<noteq> D\<close> \<open>B C ParStrict x y\<close> 
            \<open>Bet y x T\<close> \<open>Col A B x\<close> \<open>Col A C y\<close> assms(10) assms(11) 
            assms(2) assms(4) assms(6) assms(9) between_symmetry 
            col_permutation_5 impossible_case_4 not_col_permutation_2) 
    }
    ultimately
    have "\<exists> x y. Bet A B x \<and> Bet A C y \<and> Bet x T y"
      using Col_def \<open>Col A B x\<close> by blast 
  }
  ultimately
  show ?thesis
    using Col_def \<open>Col x T y\<close> by blast 
qed

(*NOTE ROLAND: REVOIR LA STRUCTURE DE CETTTE DEMO \<And> B B' B'' B''' *)
lemma triangle_circumscription_implies_tarski_s_euclid:
  assumes "triangle_circumscription_principle"
  shows "tarski_s_parallel_postulate"
proof -
  {
    fix A B C D T
    assume "Bet A D T \<and> Bet B D C \<and> A \<noteq> D"
    have "\<exists> X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y"
    proof -
      {
        fix A' B' C' D' T'
        assume H1: "A' \<noteq> B' \<and> A' \<noteq> C' \<and> A' \<noteq> D' \<and> A' \<noteq> T' \<and> 
                    B' \<noteq> C' \<and> B' \<noteq> D' \<and> B' \<noteq> T' \<and> C' \<noteq> D' \<and> 
                    C' \<noteq> T' \<and> D' \<noteq> T' \<and> \<not> Col A' B' C' \<and> 
                    Bet A' D' T' \<and> Bet B' D' C' \<and> \<not> Col B' C' T'"
        have "A' \<noteq> B'"
          using H1 by blast
        have "A' \<noteq> C'"
          using H1 by blast
        have "A' \<noteq> D'"
          using H1 by blast
        have "B' \<noteq> C'"
          using H1 by blast
        have "B' \<noteq> D'"
          using H1 by blast
        have "C' \<noteq> D'"
          using H1 by blast
        have "D' \<noteq> T'"
          using H1 by blast
        have "\<not> Col A' B' C'"
          using H1 by blast
        have "Bet A' D' T'"
          using H1 by blast
        have "Bet B' D' C'"
          using H1 by blast
        have "\<not> Col B' C' T'"
          using H1 by blast
        obtain Y' where "Col B' C' Y' \<and> B' C' Perp T' Y'"
          using \<open>\<not> Col B' C' T'\<close> l8_18_existence by presburger
        {
          fix B'' C''
          assume H2: "A' \<noteq> B'' \<and> A' \<noteq> C'' \<and> B'' \<noteq> C'' \<and> 
                      B'' \<noteq> D' \<and> C'' \<noteq> D' \<and> \<not> Col A' B'' C'' \<and> 
                      Bet B'' D' C'' \<and> \<not> Col B'' C'' T' \<and> 
                      Col B'' C'' Y' \<and> B'' C'' Perp T' Y'"
          {
            fix B''' C'''
            assume A1: "A' \<noteq> C''' \<and> B''' \<noteq> C''' \<and> B''' \<noteq> D' \<and> 
                        C''' \<noteq> D' \<and> \<not> Col A' B''' C''' \<and> 
                        Bet B''' D' C''' \<and> \<not> Col B''' C''' T' \<and> 
                        Col B''' C''' Y' \<and> B''' C''' Perp T' Y' \<and> 
                        B''' \<noteq> Y'"
            have "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)" 
            proof - 
              {
                assume "C''' = Y'"
                have "C''' \<noteq> T'"
                  using A1 col_trivial_2 by blast 
                obtain Y1 where "Y1 Midpoint C''' T'"
                  using midpoint_existence by fastforce
                have "\<not> Col A' B''' C'''" 
                  using A1 by blast
                {
                  have "A' \<noteq> C''' \<and> B''' \<noteq> C''' \<and> B''' \<noteq> D' \<and> 
                        C''' \<noteq> D' \<and> \<not> Col A' B''' C''' \<and> 
                        Bet B''' D' C''' \<and> \<not> Col B''' C''' T' \<and> 
                        Col B''' C''' Y' \<and> B''' C''' Perp T' Y' \<and> 
                        B''' \<noteq> Y'" using A1 by blast
                  {
                    assume "Y1 = A'"
                    have "C''' \<noteq> D'" using A1 by blast
                    have "Bet B''' D' C'''" using A1 by blast
                    have "Col A' C''' T'" 
                      using A1 
                      using \<open>Y1 = A'\<close> \<open>Y1 Midpoint C''' T'\<close> midpoint_col by blast
                    hence "Col A' B''' C'''" 
                      using \<open>A' \<noteq> D'\<close> \<open>Bet A' D' T'\<close> \<open>Bet B''' D' C'''\<close> 
                        \<open>C''' \<noteq> D'\<close> between_trivial 
                        impossible_two_sides_not_col by blast                    
                    hence False 
                      using \<open>\<not> Col A' B''' C'''\<close> by blast
                  }
                  hence "Y1 \<noteq> A'" 
                    by blast
                  have "C''' \<noteq> Y1" 
                    using \<open>C''' \<noteq> T'\<close> \<open>Y1 Midpoint C''' T'\<close> 
                      midpoint_distinct_1 by blast 
                  have "B''' \<noteq> Y1"
                    by (metis A1 midpoint_col \<open>Y1 Midpoint C''' T'\<close>)
                  have "Bet C''' Y1 T'"
                    by (simp add: \<open>Y1 Midpoint C''' T'\<close> midpoint_bet)
                  have "Cong C''' Y1 Y1 T'"
                    by (simp add: \<open>Y1 Midpoint C''' T'\<close> midpoint_cong) 
                  have "\<not> Col A' B''' Y1"
                    using impossible_two_sides_not_col A1 
                    by (meson \<open>A' \<noteq> D'\<close> \<open>Bet A' D' T'\<close> 
                        \<open>Bet C''' Y1 T'\<close> between_symmetry 
                        not_col_permutation_5) 
                  obtain X where "T' Midpoint Y1 X"
                    using symmetric_point_construction by auto
                  hence "X \<noteq> Y1"
                    by (metis \<open>C''' \<noteq> Y1\<close> \<open>Y1 Midpoint C''' T'\<close> l7_9_bis l8_20_2) 
                  hence "T' \<noteq> X"
                    using \<open>T' Midpoint Y1 X\<close> is_midpoint_id_2 by blast
                  have "Bet Y1 T' X"
                    by (simp add: \<open>T' Midpoint Y1 X\<close> midpoint_bet)
                  have "Cong Y1 T' T' X"
                    by (simp add: \<open>T' Midpoint Y1 X\<close> midpoint_cong) 
                  obtain Z1 where "Z1 Y1 Reflect A' B'''"
                    using l10_2_existence by blast
                  hence "Z1 Y1 ReflectL A' B'''"
                    using \<open>\<not> Col A' B''' Y1\<close> is_image_is_image_spec 
                      not_col_distincts by blast 
                  then obtain M1 where HH1: "Bet Y1 M1 Z1 \<and> Cong Y1 M1 M1 Z1 \<and> 
                                      Col A' B''' M1 \<and> 
                                      (A' B''' Perp Y1 Z1 \<or> Y1 = Z1)" 
                    using ReflectL_def midpoint_bet midpoint_cong by blast 
                  obtain Z2 where "Z2 Y1 Reflect A' C'''"
                    using l10_2_existence by blast
                  hence "Z2 Y1 ReflectL A' C'''"
                    using \<open>\<not> Col A' B''' C'''\<close> is_image_is_image_spec 
                      not_col_distincts by blast
                  then obtain M2 where HH2: "Bet Y1 M2 Z2 \<and> Cong Y1 M2 M2 Z2 \<and> 
                                      Col A' C''' M2 \<and> 
                                      (A' C''' Perp Y1 Z2 \<or> Y1 = Z2)" 
                    using ReflectL_def midpoint_bet midpoint_cong by blast 
                  have "Bet Y1 M2 Z2" 
                    using HH2 by blast
                  have "Cong Y1 M2 M2 Z2"
                    using HH2 by blast
                  have "Col A' C''' M2"
                    using HH2 by blast
                  have "A' C''' Perp Y1 Z2 \<or> Y1 = Z2"
                    using HH2 by blast

                  {
                    assume "Y1 = Z2"
                    hence "Y1 = M2"
                      using HH2 between_identity by blast 
                    hence "Col A' C''' Y1"
                      using HH2 by blast 
                    have "Col A' B''' C'''" 
                    proof -
                      have "Bet A' D' T'" 
                        using \<open>Bet A' D' T'\<close> by auto
                      moreover have "Bet C''' Y1 T'" 
                        using \<open>Bet C''' Y1 T'\<close> by blast
                      moreover have "C''' \<noteq> Y1" 
                        using \<open>C''' \<noteq> Y1\<close> by auto
                      moreover have "Col A' C''' Y1" 
                        using \<open>Col A' C''' Y1\<close> by blast
                      moreover 
                      {
                        assume "\<not> Col B''' C''' Y1"
                        have "A' \<noteq> C'''" 
                          using A1 by blast
                        have "B''' \<noteq> C'''"
                          using A1 by blast
                        have "C''' \<noteq> D'"                
                          using A1 by blast
                        have "Bet B''' D' C'''"        
                          using A1 by blast
                        have "\<not> Col B''' C''' T'"       
                          using A1 by blast
                        have "B''' \<noteq> Y'"        
                          using A1 by blast
                        hence "A' = D'" 
                          by (metis (no_types, lifting) NCol_perm 
                              calculation(3) col_transitivity_1
                              \<open>A' \<noteq> C'''\<close> \<open>B''' \<noteq> C'''\<close> \<open>C''' \<noteq> D'\<close> 
                              \<open>Bet B''' D' C'''\<close> \<open>\<not> Col B''' C''' T'\<close> 
                              bet_col between_identity calculation(1) 
                              calculation(2) not_col_distincts                       
                              calculation(4))
                        hence False 
                          using \<open>A' \<noteq> D'\<close> by blast
                      }
                      hence "Col B''' C''' Y1" 
                        by blast
                      ultimately show ?thesis using l6_16_1 
                        using col_permutation_2 by blast
                    qed
                    hence "False" 
                      using A1 by blast
                    hence "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)" 
                      by auto
                  }
                  moreover
                  {
                    assume "A' C''' Perp Y1 Z2"
                    hence "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)" 
                    proof -
                      have "B''' \<noteq> D'"
                        using A1 by blast 
                      moreover
                      have "C''' \<noteq> D'"
                        using A1 by blast 
                      moreover
                      have "D' \<noteq> T'"
                        using \<open>D' \<noteq> T'\<close> by auto
                      moreover
                      have "T' \<noteq> X"
                        by (simp add: \<open>T' \<noteq> X\<close>) 
                      moreover
                      have "\<not> Col A' B''' C'''"  
                        using A1 by blast 
                      moreover
                      have "Col A' B''' M1" 
                        using HH1 by blast
                      moreover
                      have "Col A' C''' M2" 
                        using HH2 by blast
                      moreover
                      have "Bet A' D' T'"
                        by (simp add: \<open>Bet A' D' T'\<close>) 
                      moreover
                      have "\<not> Col B''' C''' T'"
                        using A1 by blast 
                      moreover
                      have "Bet B''' D' C'''" 
                        using A1 by blast 
                      moreover
                      have "Col T' Y1 C'''"
                        by (simp add: \<open>Bet C''' Y1 T'\<close> bet_col between_symmetry) 
                      moreover
                      have "Bet Y1 T' X"
                        by (simp add: \<open>Bet Y1 T' X\<close>) 
                      moreover
                      have "Bet Y1 M1 Z1" 
                        using HH1 by blast
                      moreover
                      have "Bet Y1 M2 Z2" 
                        using HH2 by blast
                      moreover
                      have "Cong Y1 T' T' X"
                        by (simp add: \<open>Cong Y1 T' T' X\<close>) 
                      moreover
                      have "Cong Y1 M1 M1 Z1" 
                        using HH1 by blast
                      moreover
                      have "Cong Y1 M2 M2 Z2"
                        using HH2 by blast
                      moreover
                      have "B''' C''' Perp T' C'''" 
                        using A1 \<open>C''' = Y'\<close> by blast 
                      moreover
                      have "A' B''' Perp Y1 Z1"
                        using HH1 \<open>\<not> Col A' B''' Y1\<close> bet_neq12__neq by blast
                      moreover
                      have "A' C''' Perp Y1 Z2"
                        by (simp add: \<open>A' C''' Perp Y1 Z2\<close>) 
                      ultimately
                      show ?thesis 
                        using assms(1) 
                          triangle_circumscription_implies_tarski_s_euclid_aux 
                        by blast
                    qed
                  }
                  ultimately
                  have "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)"
                    using HH2 by blast
                }
              }
              moreover
              {
                assume "C''' \<noteq> Y'"
                obtain X where "T' Midpoint Y' X"
                  using symmetric_point_construction by blast
                have "T' \<noteq> Y'"
                  using A1 by blast
                hence "X \<noteq> Y'"
                  using \<open>T' Midpoint Y' X\<close> l7_3 by blast
                have "T' \<noteq> X"
                  using \<open>T' Midpoint Y' X\<close> \<open>T' \<noteq> Y'\<close> is_midpoint_id_2 by blast
                have "Bet Y' T' X"
                  by (simp add: \<open>T' Midpoint Y' X\<close> midpoint_bet)
                have "Cong Y' T' T' X"
                  by (simp add: \<open>T' Midpoint Y' X\<close> midpoint_cong)
                obtain Z1 where "Z1 Y' Reflect A' B'''"
                  using l10_2_existence by blast 
                have "\<not> (A' = B''' \<and> A' Midpoint Y' Z1)"  
                  using A1 not_col_distincts by blast 
                hence "Z1 Y' ReflectL A' B'''"
                  using Reflect_def \<open>Z1 Y' Reflect A' B'''\<close> by force 
                then obtain M1 where HH3: "Bet Y' M1 Z1 \<and> Cong Y' M1 M1 Z1 \<and> 
                                             Col A' B''' M1 \<and> 
                                             (A' B''' Perp Y' Z1 \<or> Y' = Z1)" 
                  using ReflectL_def midpoint_bet midpoint_cong by blast 
                obtain Z2 where "Z2 Y' Reflect A' C'''"
                  using l10_2_existence by blast 
                have "\<not> (A' = C''' \<and> A' Midpoint Y' Z2)"  
                  using A1 not_col_distincts by blast 
                hence "Z2 Y' ReflectL A' C'''"
                  using Reflect_def \<open>Z2 Y' Reflect A' C'''\<close> by force 
                then obtain M2 where HH4: "Bet Y' M2 Z2 \<and> Cong Y' M2 M2 Z2 \<and> 
                                             Col A' C''' M2 \<and> 
                                             (A' C''' Perp Y' Z2 \<or> Y' = Z2)" 
                  using ReflectL_def midpoint_bet midpoint_cong by blast 
                have "\<not> Col A' B''' Y'" 
                proof -
                  {
                    assume "Col A' B''' Y'"
                    have "False"
                    proof -
                      have "\<not> Col A' B''' C'''" 
                        using A1 by blast
                      moreover
                      have "C''' \<noteq> B'''" 
                        using A1 by blast
                      moreover
                      have "Col A' B''' B'''"
                        by (simp add: col_trivial_2) 
                      moreover
                      have "Col A' B''' Y'"
                        using \<open>Col A' B''' Y'\<close> by blast 
                      moreover
                      have "Col C''' B''' B'''"
                        by (simp add: col_trivial_2) 
                      moreover
                      have "Col C''' B''' Y'" 
                        using A1 Col_cases by blast 
                      ultimately
                      show ?thesis 
                        using A1 l6_21 by blast
                    qed
                  }
                  thus ?thesis 
                    by blast qed
                have "\<not> Col A' C''' Y'" 
                proof -
                  {
                    assume "Col A' C''' Y'"
                    have "False"
                    proof -
                      have "\<not> Col A' C''' B'''" 
                        using A1 Col_cases by blast 
                      moreover
                      have "B''' \<noteq> C'''" 
                        using A1 by blast
                      moreover
                      have "Col A' C''' C'''"
                        by (simp add: col_trivial_2) 
                      moreover
                      have "Col A' C''' Y'"
                        using \<open>Col A' C''' Y'\<close> by blast 
                      moreover
                      have "Col B''' C''' C'''"
                        by (simp add: col_trivial_2) 
                      moreover
                      have "Col B''' C''' Y'" 
                        using A1 by blast 
                      ultimately
                      show ?thesis 
                        using A1 l6_21 by (meson \<open>C''' \<noteq> Y'\<close>) 
                    qed
                  }
                  thus ?thesis 
                    by blast 
                qed
                have "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)" 
                proof-
                  {
                    assume "A' B''' Perp Y' Z1 \<and> A' C''' Perp Y' Z2"
                    have "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)" 
                    proof -
                      have "B''' \<noteq> D'" 
                        using A1 by blast
                      moreover
                      have "C''' \<noteq> D'" 
                        using A1 by blast
                      moreover
                      have "D' \<noteq> T'"
                        by (simp add: \<open>D' \<noteq> T'\<close>) 
                      moreover
                      have "T' \<noteq> X"
                        by (simp add: \<open>T' \<noteq> X\<close>)
                      moreover
                      have "\<not> Col A' B''' C'''" 
                        using A1 by blast
                      moreover
                      have "Col A' B''' M1"
                        using HH3 by blast
                      moreover
                      have "Col A' C''' M2"
                        using HH4 by blast
                      moreover
                      have "Bet A' D' T'" 
                        using \<open>Bet A' D' T'\<close> by blast 
                      moreover
                      have "\<not> Col B''' C''' T'" 
                        using A1 by blast
                      moreover
                      have "Bet B''' D' C'''"
                        using A1 by blast
                      moreover
                      have "Col T' Y' Y'" 
                        using col_trivial_2 by presburger 
                      moreover
                      have "Bet Y' T' X" 
                        using \<open>Bet Y' T' X\<close> by blast 
                      moreover
                      have "Bet Y' M1 Z1" 
                        using HH3 by blast
                      moreover
                      have "Bet Y' M2 Z2" 
                        using HH4 by blast
                      moreover
                      have "Cong Y' T' T' X" 
                        using \<open>Cong Y' T' T' X\<close> by blast 
                      moreover
                      have "Cong Y' M1 M1 Z1" 
                        using HH3 by blast
                      moreover
                      have "Cong Y' M2 M2 Z2" 
                        using HH4 by blast
                      moreover
                      have "B''' C''' Perp T' Y'"
                        using A1 by blast
                      moreover
                      have "A' B''' Perp Y' Z1" 
                        using \<open>A' B''' Perp Y' Z1 \<and> A' C''' Perp Y' Z2\<close> by blast
                      moreover
                      have "A' C''' Perp Y' Z2" 
                        using \<open>A' B''' Perp Y' Z1 \<and> A' C''' Perp Y' Z2\<close> by blast
                      ultimately
                      show ?thesis
                        using assms(1) 
                          triangle_circumscription_implies_tarski_s_euclid_aux 
                        by blast
                    qed
                  }
                  moreover
                  {
                    assume "Y' = Z1"
                    hence "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)"
                      using HH3 \<open>\<not> Col A' B''' Y'\<close> bet_neq12__neq by blast 
                  }
                  moreover
                  {
                    assume "Y' = Z2"
                    hence "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)"
                      using \<open>Z2 Y' Reflect A' C'''\<close> \<open>\<not> Col A' C''' Y'\<close> 
                        col_permutation_1 l10_8 by blast
                  }
                  ultimately
                  show ?thesis
                    using HH3 HH4 by blast
                qed
              }
              ultimately
              show ?thesis 
                by blast
            qed
          }
          hence Haux: "\<forall>  B''' C'''. (A' \<noteq> C''' \<and> B''' \<noteq> C''' \<and> 
                                        B''' \<noteq> D' \<and> C''' \<noteq> D' \<and> 
                                        \<not> Col A' B''' C''' \<and> 
                                        Bet B''' D' C''' \<and> 
                                        \<not> Col B''' C''' T' \<and> 
                                        Col B''' C''' Y' \<and> 
                                        B''' C''' Perp T' Y' \<and> B''' \<noteq> Y') 
                              \<longrightarrow> 
                           (\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y))" 
            by auto
          moreover
          {
            fix B''' C'''
            assume A2: "A' \<noteq> C''' \<and> B''' \<noteq> C''' \<and> B''' \<noteq> D' \<and> 
                        C''' \<noteq> D' \<and> \<not> Col A' B''' C''' \<and> 
                        Bet B''' D' C''' \<and> \<not> Col B''' C''' T' \<and> 
                        Col B''' C''' Y' \<and> B''' C''' Perp T' Y' \<and> 
                        B''' = Y'"
            have "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)" 
            proof -
              {
                assume "C''' = Y'"
                hence "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)"
                  using A2 by fastforce 
              }
              moreover
              {
                assume "C''' \<noteq> Y'"
                have "\<exists> x y. (Bet A' B''' x \<and> Bet A' C''' y \<and> Bet x T' y)" 
                proof -
                  have "A' \<noteq> C'''"
                    using A2 by blast 
                  moreover
                  have "A' \<noteq> B'''" 
                    using A2 not_col_distincts by blast 
                  moreover
                  have "C''' \<noteq> B'''" 
                    using A2 by blast 
                  moreover
                  have "C''' \<noteq> D'"
                    using A2 by blast 
                  moreover
                  have "B''' \<noteq> D'" 
                    using A2 by blast 
                  moreover
                  have "\<not> Col A' C''' B'''" 
                    using A2 Col_cases by blast 
                  moreover
                  have "Bet C''' D' B'''" 
                    using A2 between_symmetry by blast 
                  moreover
                  have "\<not> Col C''' B''' T'" 
                    using A2 Col_cases by blast 
                  moreover
                  have "Col C''' B''' Y'" 
                    using A2 Col_cases by blast 
                  moreover
                  have "C''' B''' Perp T' Y'" 
                    using A2 by (metis col_trivial_2 perp_col2) 
                  moreover
                  have "C''' \<noteq> Y'" 
                    using A2 by blast 
                  ultimately
                  have "(\<exists> x y. (Bet A' C''' x \<and> Bet A' B''' y \<and> Bet x T' y))"
                    using Haux by blast
                  thus ?thesis
                    using Bet_cases by blast 
                qed
              }
              ultimately
              show ?thesis 
                by auto
            qed
          }
          ultimately
          have "\<exists> x y. (Bet A' B'' x \<and> Bet A' C'' y \<and> Bet x T' y)" 
            using H2 by blast         
        }
        hence "\<exists> x y. (Bet A' B' x \<and> Bet A' C' y \<and> Bet x T' y)"
          using H1 \<open>Col B' C' Y' \<and> B' C' Perp T' Y'\<close> by presburger 
      }
      hence "\<forall> A B C D T. Bet A D T \<and> Bet B D C \<and> A \<noteq> D \<longrightarrow> 
                          (\<exists> x y. (Bet A B x \<and> Bet A C y \<and> Bet x T y))" 
        using tarski_s_euclid_remove_degenerated_cases by blast
      thus ?thesis
        using \<open>Bet A D T \<and> Bet B D C \<and> A \<noteq> D\<close> by blast 
    qed
  }
  thus ?thesis 
    using tarski_s_parallel_postulate_def by blast
qed

(** The circumcenter of a right triangle is the midpoint of the hypotenuse. *)


(** There exists a right triangle whose circumcenter is the midpoint of the hypotenuse. *)

lemma thales_converse_postulate__thales_existence: 
  assumes "thales_converse_postulate"
  shows "existential_thales_postulate"
proof -
  obtain A B C where "\<not> (Bet A B C \<or> Bet B C A \<or> Bet C A B)"
    using lower_dim by blast
  hence "\<not> Col C A B"
    using Col_def by auto 
  have "Col C A C"
    by (simp add: col_trivial_3) 
  then obtain B' where "C A Perp B' C \<and> C A OS B B'" 
    using l10_15 \<open>\<not> Col C A B\<close> by blast
  have "C A Perp B' C"
    by (simp add: \<open>C A Perp B' C \<and> C A OS B B'\<close>)
  have "C A OS B B'"
    by (simp add: \<open>C A Perp B' C \<and> C A OS B B'\<close>)
  have "\<not> Col C A B'"
    by (simp add: \<open>C A Perp B' C \<and> C A OS B B'\<close> perp_not_col)
  hence "\<not> Col A B' C"
    using Col_cases by blast
  moreover
  have "Per A C B'"
    by (simp add: \<open>C A Perp B' C\<close> perp_per_1)
  moreover
  obtain M where "M Midpoint A B'"
    using midpoint_existence by blast
  moreover
  have "Cong M A M C"
    using assms thales_converse_postulate_def calculation(2) calculation(3) by blast 
  ultimately
  show ?thesis
    using existential_thales_postulate_def by blast 
qed

lemma thales_converse_postulate__weak_triangle_circumscription_principle:
  assumes "thales_converse_postulate"
  shows "weak_triangle_circumscription_principle"
proof -
  {
    fix A B C A1 A2 B1 B2
    assume 1: "\<not> Col A B C" and 
      2: "Per A C B" and
      3: "A1 A2 PerpBisect B C" and
      4: "B1 B2 PerpBisect A C" and
      5: "Coplanar A B C A1" and
      6: "Coplanar A B C A2" and
      7: "Coplanar A B C B1" and
      8: "Coplanar A B C B2"
    obtain M where "M Midpoint A B"
      using midpoint_existence by blast
    hence "Cong M A M C" 
      using thales_converse_postulate_def "2" assms by blast 
    have "Bet A M B"
      by (simp add: \<open>M Midpoint A B\<close> midpoint_bet) 
    have "A \<noteq> B"
      using "1" col_trivial_1 by auto
    have "Col A1 A2 M" 
    proof -
      have "Coplanar A1 M B C" 
      proof -
        have "Coplanar A1 C A B"
          using "5" ncoplanar_perm_17 by blast 
        moreover
        have "Col A B M"
          using \<open>Bet A M B\<close> bet_col not_col_permutation_5 by blast 
        moreover
        have "Col A B B"
          using col_trivial_2 by blast 
        ultimately
        show ?thesis
          by (metis \<open>A \<noteq> B\<close> col_cop__cop col_permutation_4 
              coplanar_perm_1 coplanar_perm_5) 
      qed
      moreover
      have "Coplanar A2 M B C" 
      proof -
        have "Coplanar A2 C A B"
          using "6" ncoplanar_perm_17 by blast 
        moreover
        have "Col A B M"
          using \<open>Bet A M B\<close> bet_col not_col_permutation_5 by blast 
        moreover
        have "Col A B B"
          using col_trivial_2 by blast 
        ultimately
        show ?thesis
          by (metis \<open>A \<noteq> B\<close> col_cop__cop col_permutation_4 
              coplanar_perm_1 coplanar_perm_5) 
      qed
      moreover
      have "Cong M B M C"
        by (meson \<open>Cong M A M C\<close> \<open>M Midpoint A B\<close> 
            cong_inner_transitivity cong_left_commutativity midpoint_cong) 
      ultimately
      show ?thesis
        using "3" cong_cop2_perp_bisect_col by blast
    qed
    moreover
    have "Col B1 B2 M" 
    proof -
      have "Coplanar B1 M A C" 
      proof -
        have "Coplanar B1 C A B"
          using "7" ncoplanar_perm_17 by blast 
        moreover
        have "Col A B M"
          using \<open>Bet A M B\<close> bet_col not_col_permutation_5 by blast 
        moreover
        have "Col A B A"
          by (simp add: col_trivial_3)
        ultimately
        show ?thesis
          by (metis \<open>A \<noteq> B\<close> col_cop__cop coplanar_perm_5) 
      qed
      moreover
      have "Coplanar B2 M A C" 
      proof -
        have "Coplanar B2 C A B"
          using "8" ncoplanar_perm_17 by blast 
        moreover
        have "Col A B M"
          using \<open>Bet A M B\<close> bet_col not_col_permutation_5 by blast 
        moreover
        have "Col A B A"
          by (simp add: col_trivial_3)
        ultimately
        show ?thesis
          by (metis \<open>A \<noteq> B\<close> col_cop__cop coplanar_perm_5) 
      qed
      ultimately
      show ?thesis
        using \<open>Cong M A M C\<close> "4" cong_cop2_perp_bisect_col by blast
    qed
    ultimately
    have "\<exists> I. Col A1 A2 I \<and> Col B1 B2 I" 
      by blast
  }
  thus ?thesis
    using weak_triangle_circumscription_principle_def by blast 
qed

lemma thales_existence__rah:
  assumes "existential_thales_postulate"
  shows "postulate_of_right_saccheri_quadrilaterals"
proof -
  {
    fix A B C D
    assume "Saccheri A B C D"
    hence "Per A B C" 
      using t22_17__rah assms existential_thales_postulate_def
        existential_playfair__rah_1 
        postulate_of_right_saccheri_quadrilaterals_def by fastforce
  }
  thus ?thesis
    using postulate_of_right_saccheri_quadrilaterals_def by blast 
qed

(** If A, B and C are points on a circle where the line AB is a diameter of the circle,
    then the angle ACB is a right angle. *)

(** This comes from the proof of Martin's Theorem 23.7 (N -> O) *)

lemma thales_postulate__thales_converse_postulate:
  assumes "thales_postulate"
  shows "thales_converse_postulate"
proof -
  {
    fix A B C M
    assume "M Midpoint A B" and "Per A C B"
    hence "Bet A M B"
      by (simp add: midpoint_bet) 
    have "Cong M A M C"
    proof (cases "Col A B C")
      case True
      thus ?thesis
        using \<open>M Midpoint A B\<close> \<open>Per A C B\<close> cong_left_commutativity 
          cong_reflexivity l8_9 midpoint_cong not_col_permutation_5 by blast 
    next
      case False
      hence "\<not> Col A B C"
        by simp
      have "A \<noteq> B"
        using False col_trivial_1 by auto 
      have "C \<noteq> B"
        using False col_trivial_2 by blast 
      have "A \<noteq> M"
        using False \<open>M Midpoint A B\<close> is_midpoint_id not_col_distincts by blast 
      have "A \<noteq> C" 
        using False col_trivial_3 by blast
      have "M \<noteq> C"
        using Col_def False \<open>M Midpoint A B\<close> l7_2 midpoint_bet by blast
      then obtain C' where "M Out C C'" and "Cong M C' M A" 
        using segment_construction_3 \<open>A \<noteq> M\<close> by metis 
      hence "Cong M A M C'"
        by (meson cong_symmetry) 
      show ?thesis
      proof (cases "C = C'")
        case True
        thus ?thesis
          using \<open>Cong M A M C'\<close> by auto 
      next
        case False 
        hence "C \<noteq> C'" by simp
        {
          assume "\<not> Cong M A M C"
          have "M \<noteq> C'"
            using \<open>A \<noteq> M\<close> \<open>Cong M C' M A\<close> cong_reverse_identity by blast 
          {
            assume "Col A B C'"
            hence "\<not> Per A C B"
              by (metis Col_cases midpoint_col
                  \<open>M Midpoint A B\<close> \<open>M Out C C'\<close> \<open>M \<noteq> C'\<close>
                  \<open>\<not> Col A B C\<close> colx out_col)
            hence False
              by (simp add: \<open>Per A C B\<close>) 
          }
          hence "\<not> Col A B C'" 
            by auto
          {
            assume "Col A C C'"
            hence "Col A C B" 
              by (meson False \<open>A \<noteq> M\<close> \<open>Bet A M B\<close> \<open>M Out C C'\<close> 
                  bet_col l6_16_1 not_col_permutation_3 
                  not_col_permutation_5 out_col)
            hence False 
              using \<open>\<not> Col A B C\<close> not_col_permutation_5 by blast
          }
          hence "\<not> Col A C C'" 
            by auto
          {
            assume "Col B C C'"
            hence "\<not> Per A C B"
              by (metis Col_cases False midpoint_col 
                  \<open>M Midpoint A B\<close> \<open>M Out C C'\<close> \<open>\<not> Col A B C\<close> 
                  col_trivial_2 l6_21 midpoint_distinct_2 
                  out_col)
            hence False
              by (simp add: \<open>Per A C B\<close>) 
          }
          hence "\<not> Col B C C'"
            by auto
          have "B \<noteq> C'"
            using \<open>\<not> Col A B C'\<close> col_trivial_2 by auto 
          have "A \<noteq> C'"
            using \<open>\<not> Col A B C'\<close> col_trivial_3 by blast 
          have "Per A C' B"
            using \<open>Cong M A M C'\<close> \<open>M Midpoint A B\<close> 
              assms thales_postulate_def by blast 
          hence "A C B CongA A C' B" 
            using \<open>Per A C B\<close> \<open>A \<noteq> C'\<close> \<open>A \<noteq> C\<close> 
              \<open>B \<noteq> C'\<close> \<open>C \<noteq> B\<close> l11_16 by force 
          have "Col A B M"
            using Col_perm \<open>Bet A M B\<close> bet_col by blast 
          hence "A B OS C C'"
            using \<open>\<not> Col A B C\<close> \<open>M Out C C'\<close> l9_19_R2 by blast
          {
            assume "Bet M C C'"
            have "A C' B LtA A C B" 
            proof -
              have "C' A OS B C" 
              proof -
                have "C' A OS B M"
                  by (metis NCol_cases out_one_side
                      \<open>A \<noteq> B\<close> \<open>A \<noteq> M\<close> \<open>Bet A M B\<close> \<open>\<not> Col A B C'\<close> 
                      bet2__out invert_one_side l5_1) 
                moreover
                have "C' A OS M C"
                  by (metis False bet_out_1 out_one_side 
                      \<open>Bet M C C'\<close> \<open>\<not> Col A C C'\<close> 
                      not_col_permutation_2 one_side_symmetry) 
                ultimately
                show ?thesis
                  using one_side_transitivity by blast 
              qed
              moreover
              have "A B OS C' C"
                by (simp add: \<open>A B OS C C'\<close> one_side_symmetry) 
              moreover
              have "C' B OS A C" 
              proof -
                have "C' B OS A M"
                  by (meson out_one_side  \<open>A \<noteq> B\<close> \<open>M Midpoint A B\<close> 
                      \<open>\<not> Col A B C'\<close> invert_one_side midpoint_out_1 
                      not_col_permutation_1)
                moreover
                have "C' B OS M C"
                  by (meson False \<open>Bet M C C'\<close> \<open>\<not> Col B C C'\<close> 
                      bet_out_1 l6_6 not_col_permutation_2 
                      out_one_side) 
                ultimately
                show ?thesis
                  using one_side_transitivity by blast 
              qed
              ultimately
              show ?thesis
                by (simp add: os3__lta) 
            qed
            hence False 
              using \<open>A C B CongA A C' B\<close>
              by (meson conga_sym lta_not_conga) 
          }
          moreover
          {
            assume "Bet M C' C"
            have "A C B LtA A C' B" 
            proof -
              have "C A OS B C'" 
              proof -
                have "C A OS B M"
                  by (metis \<open>A \<noteq> M\<close> \<open>Bet A M B\<close> \<open>\<not> Col A B C\<close> 
                      bet2__out col_trivial_3 invert_one_side l5_1 
                      not_col_permutation_5 out_one_side_1) 
                moreover
                have "C A OS M C'"
                  by (metis \<open>Bet M C C' \<Longrightarrow> False\<close> \<open>M Out C C'\<close> 
                      calculation col_trivial_3 l9_19_R2 
                      one_side_not_col124 or_bet_out out_col)
                ultimately
                show ?thesis
                  using one_side_transitivity by blast 
              qed
              moreover
              have "C B OS A C'" 
              proof -
                have "C B OS A M"
                  by (meson out_one_side \<open>A \<noteq> B\<close> \<open>M Midpoint A B\<close> 
                      \<open>\<not> Col A B C\<close> invert_one_side midpoint_out_1 
                      not_col_permutation_1) 
                moreover
                have "C B OS M C'"
                  by (meson \<open>Bet M C C' \<Longrightarrow> False\<close> \<open>M Out C C'\<close> 
                      calculation col_trivial_3 l6_4_2 l9_19_R2 
                      one_side_not_col124 out_col) 
                ultimately
                show ?thesis
                  using one_side_transitivity by blast 
              qed
              ultimately
              show ?thesis
                by (simp add: \<open>A B OS C C'\<close> os3__lta) 
            qed
            hence False 
              using \<open>A C B CongA A C' B\<close>
              by (meson lta_not_conga)
          }
          ultimately
          have "False"
            using Out_def \<open>M Out C C'\<close> by presburger 
        }
        thus ?thesis 
          by auto
      qed
    qed
  }
  thus ?thesis
    using thales_converse_postulate_def by blast 
qed

lemma triangle__existential_triangle:
  assumes "triangle_postulate"
  shows "postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights"
proof -
  obtain A B C where "\<not> (Bet A B C \<or> Bet B C A \<or> Bet C A B)"
    using lower_dim_ex by blast
  hence "\<not> Col A B C"
    by (simp add: Col_def)
  moreover
  have "A \<noteq> B"
    using calculation col_trivial_1 by blast
  have "B \<noteq> C" 
    using calculation col_trivial_2 by blast
  have "A \<noteq> C" 
    using calculation col_trivial_3 by blast
  obtain D E F where "A B C TriSumA D E F" 
    using ex_trisuma \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close>\<open>A \<noteq> C\<close> by blast
  have "Bet D E F" 
    using triangle_postulate_def assms \<open>A B C TriSumA D E F\<close> by blast 
  hence "\<exists> A B C D E F. (\<not> Col A B C \<and> A B C TriSumA D E F \<and> Bet D E F)" 
    using \<open>A B C TriSumA D E F\<close> \<open>\<not> Col A B C\<close> by blast
  thus ?thesis
    using postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights_def 
    by presburger 
qed

(* RENAME legendre_aux \<rightarrow> legendre_aux_tr *)
lemma legendre_aux_tr:
  assumes "greenberg_s_axiom" and
    "triangle_postulate"
  shows " (\<forall> A B C P Q. \<not>(
    Q A Perp P Q \<and> P B Perp P Q \<and> Q A ParStrict P B \<and>
    Q A ParStrict P C \<and> P B OS Q C \<and> P Q OS C A \<and> P Q OS C B))"
proof -
  {
    fix A B C P Q
    assume  "Q A Perp P Q" and 
      "P B Perp P Q" and
      "Q A ParStrict P B" and
      "Q A ParStrict P C" and
      "P B OS Q C" and
      "P Q OS C A" and 
      "P Q OS C B"
    obtain B' where "P Midpoint B B'"
      using symmetric_point_construction by blast
    have "C InAngle Q P B"
      by (meson \<open>P B OS Q C\<close> \<open>P Q OS C B\<close> col123__nos l11_24 
          l9_2 l9_9_bis os_ts__inangle two_sides_cases) 
    have "\<not> Col P B C"
      using \<open>P B OS Q C\<close> col124__nos by blast
    have "\<not> Col P Q C"
      by (meson \<open>P Q OS C A\<close> col123__nos)
    have "\<not> Col P Q A"
      using \<open>P Q OS C A\<close> col124__nos by blast
    have "B P C LtA B P Q" 
    proof -
      have "\<not> Col C P Q"
        by (simp add: \<open>\<not> Col P Q C\<close> not_col_permutation_2) 
      moreover
      have "C InAngle B P Q"
        by (simp add: \<open>C InAngle Q P B\<close> l11_24) 
      ultimately
      show ?thesis
        by (simp add: inangle__lta)
    qed
    have "Per B P Q"
      by (simp add: \<open>P B Perp P Q\<close> perp_per_2) 
    hence "Acute B P C" 
      using \<open>B P C LtA B P Q\<close> Acute_def by blast 
    have "P \<noteq> Q"
      using \<open>\<not> Col P Q C\<close> col_trivial_1 by auto 
    have "A \<noteq> Q"
      using \<open>\<not> Col P Q A\<close> col_trivial_2 by fastforce 
    have "P \<noteq> A"
      using \<open>\<not> Col P Q A\<close> col_trivial_3 by auto 
    have "P \<noteq> C"
      using \<open>\<not> Col P Q C\<close> col_trivial_3 by blast 
    have "P \<noteq> B"
      using \<open>\<not> Col P B C\<close> col_trivial_1 by auto 
    have "B \<noteq> B'"
      using \<open>P Midpoint B B'\<close> \<open>P \<noteq> B\<close> l8_20_2 by blast 
    hence "P \<noteq> B'"
      using \<open>P Midpoint B B'\<close> midpoint_not_midpoint by blast 
    have "\<exists> R. (P R Q LtA B P C \<and> Q Out R A)"
    proof -
      have "\<not> Col B P C"
        by (simp add: \<open>\<not> Col P B C\<close> not_col_permutation_4) 
      moreover
      have "Q \<noteq> A"
        using \<open>A \<noteq> Q\<close> by auto 
      moreover
      have "Per P Q A"
        by (meson \<open>Q A Perp P Q\<close> l8_2 perp_per_1) 
      ultimately
      show ?thesis
        using \<open>Acute B P C\<close> greenberg_s_axiom_def assms by blast
    qed
    then obtain R where "P R Q LtA B P C" and "Q Out R A"
      by blast
    have "R \<noteq> Q"
      using \<open>Q Out R A\<close> l6_3_1 by auto
    have "R \<noteq> P"
      using \<open>P R Q LtA B P C\<close> lta_distincts by blast 
    have "P Q OS R A"
      by (meson Out_cases \<open>Q Out R A\<close> \<open>\<not> Col P Q A\<close> col_trivial_2 
          one_side_symmetry out_one_side_1)
    have "\<not> Col Q P R \<or> \<not> Col Q P A"
      using \<open>\<not> Col P Q A\<close> col_permutation_4 by blast 
    hence "P C OS Q R"
      by (meson  \<open>Q Out R A\<close> \<open>Q A ParStrict P C\<close> col_permutation_5 
          out_col par_strict_one_side par_strict_symmetry) 
    obtain D E F where "B' P R P R Q SumA D E F"
      using ex_suma \<open>P \<noteq> B'\<close> \<open>R \<noteq> P\<close> \<open>R \<noteq> Q\<close> by presburger 
    have "R Q P Q P R SumA B' P R"
    proof -
      have "B' P Q Q P R SumA B' P R" 
      proof -
        have "Q P R CongA Q P R"
          using \<open>P \<noteq> Q\<close> \<open>R \<noteq> P\<close> conga_refl by auto 
        moreover
        have "P Q TS R B'" 
        proof -
          have "P Q TS B B'" 
          proof -
            have "\<not> Col P Q B"
              using \<open>P Q OS C B\<close> col124__nos by blast 
            moreover
            have "Bet B P B'"
              using \<open>P Midpoint B B'\<close> midpoint_bet by blast 
            ultimately
            show ?thesis
              by (simp add: \<open>P \<noteq> B'\<close> bet__ts) 
          qed
          moreover
          have "P Q OS B R"
            by (meson \<open>P Q OS C A\<close> \<open>P Q OS C B\<close> \<open>P Q OS R A\<close> 
                one_side_symmetry one_side_transitivity) 
          ultimately
          show ?thesis
            using l9_8_2 by blast 
        qed
        hence "\<not> P Q OS B' R"
          by (meson l9_2 l9_9_bis) 
        moreover
        have "Coplanar B' P Q R"
          by (meson \<open>P Q TS R B'\<close> coplanar_perm_18 ts__coplanar) 
        moreover
        have "B' P R CongA B' P R"
          using \<open>P \<noteq> B'\<close> \<open>R \<noteq> P\<close> conga_refl by auto 
        ultimately
        show ?thesis
          using SumA_def by blast 
      qed
      moreover
      have "B' P Q CongA R Q P" 
      proof -
        have "Per B' P Q"
          by (meson \<open>P Midpoint B B'\<close> \<open>Per B P Q\<close> l8_2 l8_4) 
        moreover
        have "Per P Q R" 
        proof -
          have "Per P Q A"
            using \<open>Q A Perp P Q\<close> l8_2 perp_per_1 by blast 
          moreover
          have "Col Q A R"
            by (metis Col_def Out_def \<open>Q Out R A\<close> col_permutation_3) 
          ultimately
          show ?thesis
            by (metis \<open>A \<noteq> Q\<close> per_col) 
        qed
        hence "Per R Q P"
          by (meson l8_2) 
        ultimately
        show ?thesis
          using \<open>P \<noteq> B'\<close> \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> l11_16 by blast 
      qed
      moreover
      have "Q P R CongA Q P R"
        using \<open>P \<noteq> Q\<close> \<open>R \<noteq> P\<close> conga_refl by force 
      moreover
      have "B' P R CongA B' P R"
        using \<open>P \<noteq> B'\<close> \<open>R \<noteq> P\<close> conga_refl by auto 
      ultimately
      show ?thesis
        by (meson conga3_suma__suma) 
    qed
    hence "R Q P TriSumA D E F"
      using TriSumA_def \<open>B' P R P R Q SumA D E F\<close> by blast
    obtain I J K where "B' P R C P B SumA I J K" 
      using ex_suma \<open>P \<noteq> B'\<close> \<open>R \<noteq> P\<close> \<open>P \<noteq> C\<close> \<open>P \<noteq> B\<close> by presburger 
    have "\<not> Col R P B'" 
    proof -
      have "Bet B P B'"
        using \<open>P Midpoint B B'\<close> midpoint_bet by blast 
      hence "Col P B B'"
        using bet_col not_col_permutation_4 by blast 
      hence "Q A ParStrict P B'" 
        using \<open>Q A ParStrict P B\<close> \<open>P \<noteq> B'\<close> par_strict_col_par_strict by blast 
      moreover
      have "Col R Q A"
        by (metis Col_def Out_def \<open>Q Out R A\<close> col_permutation_3) 
      ultimately
      show ?thesis
        using par_not_col by blast 
    qed
    have "B' P R R P B SumA B' P B"
      by (metis Bet_cases \<open>P Midpoint B B'\<close> \<open>P \<noteq> B'\<close> \<open>P \<noteq> B\<close> 
          \<open>R \<noteq> P\<close> bet__suma midpoint_bet) 
    have "SAMS B' P R R P B"
      by (meson Mid_cases \<open>B' P R R P B SumA B' P B\<close> 
          \<open>P Midpoint B B'\<close> bet_suma__sams midpoint_bet)
    have "C P B LeA R P B" 
    proof -
      have "P C TS Q B"
        by (simp add: \<open>P B OS Q C\<close> \<open>P Q OS C B\<close> l9_31 one_side_symmetry) 
      hence "P C TS B R" 
        using \<open>P C OS Q R\<close> l9_2 l9_8_2 by blast 
      moreover
      have "P B OS R Q"
        by (metis Out_def Par_strict_cases \<open>Q A ParStrict P B\<close> 
            \<open>Q Out R A\<close> bet_col l9_17 one_side_symmetry 
            par_strict_one_side pars__os3412) 
      hence "P B OS R C" 
        using \<open>P B OS Q C\<close>  one_side_transitivity by blast 
      ultimately
      show ?thesis
        by (simp add: inangle__lea lea_comm os_ts__inangle) 
    qed
    have "D E F LtA B' P B"
    proof -
      have "D E F LtA I J K" 
      proof -
        have "B' P R LeA B' P R"
          using \<open>P \<noteq> B'\<close> \<open>R \<noteq> P\<close> lea_refl by auto 
        moreover
        have "P R Q LtA C P B"
          by (simp add: \<open>P R Q LtA B P C\<close> lta_right_comm) 
        moreover
        have "SAMS B' P R C P B"
          by (meson \<open>C P B LeA R P B\<close> \<open>SAMS B' P R R P B\<close> 
              calculation(1) sams_lea2__sams) 
        ultimately
        show ?thesis
          by (meson \<open>B' P R P R Q SumA D E F\<close> 
              \<open>B' P R C P B SumA I J K\<close> sams_lea_lta456_suma2__lta) 
      qed
      moreover
      have  "I J K LeA B' P B"
        using  \<open>B' P R C P B SumA I J K\<close> 
          \<open>B' P R R P B SumA B' P B\<close> \<open>C P B LeA R P B\<close> 
          \<open>SAMS B' P R R P B\<close> sams_lea456_suma2__lea by blast 
      ultimately
      show ?thesis
        using  lea456789_lta__lta by blast 
    qed
    have "Bet D E F" 
      using \<open>R Q P TriSumA D E F\<close> triangle_postulate_def assms(2) by blast 
    hence "D E F CongA B' P B"
      by (metis \<open>D E F LtA B' P B\<close> \<open>P Midpoint B B'\<close> 
          conga_line conga_right_comm lta_distincts 
          midpoint_bet) 
    hence False
      using \<open>D E F LtA B' P B\<close> lta_not_conga by blast 
  }
  thus ?thesis by blast
qed

(*triangle_playfair_bis*)
(* RENAME legendre_aux1 \<rightarrow> legendre_aux1_tr *)

lemma legendre_aux1_tr:
  assumes "greenberg_s_axiom" and
    "triangle_postulate"
  shows "\<forall> A1 A2 B1 B2 C1 C2 P.
             (P Perp2 A1 A2 B1 B2 \<and> \<not> Col A1 A2 P \<and> 
              Col P B1 B2 \<and> Coplanar A1 A2 B1 B2 \<and>
              A1 A2 Par C1 C2 \<and> Col P C1 C2 \<and> 
              \<not> B1 B2 TS A1 C1) 
\<longrightarrow>
              Col C1 B1 B2"
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume "P Perp2 A1 A2 B1 B2" and 
      "\<not> Col A1 A2 P" and
      "Col P B1 B2" and
      "Coplanar A1 A2 B1 B2" and
      "A1 A2 Par C1 C2" and
      "Col P C1 C2" and
      "\<not> B1 B2 TS A1 C1"
    have "Col B1 B2 P"
      using Col_cases \<open>Col P B1 B2\<close> by blast
    hence "A1 A2 ParStrict B1 B2"
      using  \<open>P Perp2 A1 A2 B1 B2\<close> \<open>Coplanar A1 A2 B1 B2\<close> 
        \<open>\<not> Col A1 A2 P\<close> \<open>Coplanar A1 A2 B1 B2\<close> \<open>P Perp2 A1 A2 B1 B2\<close> 
        col_cop_perp2__pars_bis by blast 
    have "A1 A2 ParStrict C1 C2" 
      using Col_cases \<open>A1 A2 Par C1 C2\<close> \<open>Col P C1 C2\<close> 
        \<open>\<not> Col A1 A2 P\<close> par_not_col_strict by blast
    {
      assume "\<not> Col C1 B1 B2"
      have "P \<noteq> C1" 
        using \<open>Col P B1 B2\<close> \<open>\<not> Col C1 B1 B2\<close> by auto
      obtain P1 P2 where "Col P P1 P2" and 
        "P1 P2 Perp A1 A2" and
        "P1 P2 Perp B1 B2" 
        using \<open>P Perp2 A1 A2 B1 B2\<close> Perp2_def by blast 
      obtain Q where "Col Q P1 P2" and "Col Q A1 A2"
        using \<open>P1 P2 Perp A1 A2\<close> col_permutation_2 
          perp_inter_perp_in_n by blast 
      have "P \<noteq> Q" 
        using NCol_perm \<open>Col Q A1 A2\<close> \<open>\<not> Col A1 A2 P\<close> by blast
      have "A1 A2 Perp P Q" 
        by (meson \<open>Col P P1 P2\<close> \<open>Col Q P1 P2\<close> \<open>P \<noteq> Q\<close> 
            \<open>P1 P2 Perp A1 A2\<close> col_permutation_1 perp_col0)
      have "B1 B2 Perp P Q"
        by (meson \<open>Col P P1 P2\<close> \<open>Col Q P1 P2\<close> \<open>P \<noteq> Q\<close> 
            \<open>P1 P2 Perp B1 B2\<close> col_permutation_3 perp_col0 
            perp_left_comm)
      have "P \<noteq> Q"
        using \<open>P \<noteq> Q\<close> by auto
      have "C1 \<noteq> B1" 
        using \<open>\<not> Col C1 B1 B2\<close> col_trivial_1 by blast
      have "B1 \<noteq> B2" 
        using \<open>\<not> Col C1 B1 B2\<close> not_col_distincts by blast
      have "C1 \<noteq> B2"
        using \<open>\<not> Col C1 B1 B2\<close> not_col_distincts by blast
      have "A1 \<noteq> A2" 
        using \<open>\<not> Col A1 A2 P\<close> col_trivial_1 by auto
      have "P \<noteq> A2" 
        using \<open>\<not> Col A1 A2 P\<close> col_trivial_2 by blast
      have "P \<noteq> A1" 
        using \<open>\<not> Col A1 A2 P\<close> col_trivial_3 by blast
      have "A1 \<noteq> B1" 
        using \<open>A1 A2 ParStrict B1 B2\<close> not_par_strict_id by blast
      have "A1 \<noteq> B2" 
        using \<open>A1 A2 ParStrict B1 B2\<close> col_trivial_2 
          par_strict_not_col_3 by blast
      have "A2 \<noteq> B1" 
        using \<open>A1 A2 ParStrict B1 B2\<close> not_col_distincts 
          par_strict_not_col_2 by blast
      have "A2 \<noteq> B2" 
        using \<open>A1 A2 ParStrict B1 B2\<close> not_col_distincts 
          par_strict_not_col_4 by blast
      have "A1 \<noteq> C1" 
        using \<open>A1 A2 ParStrict C1 C2\<close> not_par_strict_id by blast
      have "A1 \<noteq> C2" 
        using \<open>A1 A2 ParStrict C1 C2\<close> col_trivial_3 
          par_strict_not_col_4 by blast
      have "A2 \<noteq> C1"
        by (metis \<open>A1 A2 ParStrict C1 C2\<close> \<open>Col P C1 C2\<close> 
            col3 col_trivial_2 par_strict_not_col_2)
      have "A2 \<noteq> C2" 
        using \<open>A1 A2 ParStrict C1 C2\<close> col_trivial_2 
          par_strict_not_col_4 by blast
      have "C2 \<noteq> C1" 
        using \<open>A1 A2 Par C1 C2\<close> par_neq2 by blast
      have "B1 B2 OS Q C1" 
      proof -
        have "B1 B2 OS Q A1" 
        proof (cases "A1 = Q")
          case True
          thus ?thesis 
            using \<open>A1 A2 ParStrict B1 B2\<close> not_col_distincts 
              par_strict_one_side par_strict_symmetry by blast
        next
          case False
          have "B1 B2 ParStrict A1 A2" 
            using \<open>A1 A2 ParStrict B1 B2\<close> par_strict_symmetry by blast
          moreover
          have "Col A1 A2 Q" 
            using \<open>Col Q A1 A2\<close> not_col_permutation_2 by blast
          ultimately
          show ?thesis
            using one_side_symmetry par_strict_one_side by blast
        qed
        moreover
        have "B1 B2 OS A1 C1"
        proof -
          have "Coplanar B1 B2 A1 C1" 
          proof -
            have "\<not> Col A1 A2 P" 
              by (simp add: \<open>\<not> Col A1 A2 P\<close>)
            moreover
            have "Coplanar A1 A2 P B1" 
              by (meson \<open>B1 \<noteq> B2\<close> \<open>Col B1 B2 P\<close> 
                  \<open>Coplanar A1 A2 B1 B2\<close> col2_cop__cop col_trivial_3)
            moreover
            have "Coplanar A1 A2 P B2" 
              using \<open>B1 \<noteq> B2\<close> \<open>Col B1 B2 P\<close> \<open>Coplanar A1 A2 B1 B2\<close> 
                col2_cop__cop col_trivial_2 by blast
            moreover
            have "Coplanar A1 A2 P A1" 
              using ncop_distincts by blast
            moreover
            have "Coplanar A1 A2 P C1" 
              using \<open>A1 A2 Par C1 C2\<close> \<open>C2 \<noteq> C1\<close> \<open>Col P C1 C2\<close> 
                col_cop__cop coplanar_perm_1 not_col_permutation_2 
                par__coplanar by blast
            ultimately
            show ?thesis
              by (meson coplanar_pseudo_trans) 
          qed
          moreover
          have "\<not> Col A1 B1 B2" 
            using \<open>A1 A2 ParStrict B1 B2\<close> not_col_permutation_2 
              par_strict_not_col_3 by blast
          ultimately
          show ?thesis
            using \<open>\<not> Col C1 B1 B2\<close> \<open>\<not> B1 B2 TS A1 C1\<close> cop_nts__os by blast
        qed
        ultimately
        show ?thesis
          using one_side_transitivity by blast
      qed
      have "\<not> Col Q C1 P"
        by (metis Col_cases \<open>A1 A2 ParStrict C1 C2\<close> 
            \<open>Col P C1 C2\<close> \<open>Col Q A1 A2\<close> \<open>P \<noteq> C1\<close> 
            col_transitivity_2 par_not_col)
      have "\<not> Col B1 B2 Q"
        using \<open>B1 B2 OS Q C1\<close> col123__nos by blast
      have "\<exists> B3. Col B1 B2 B3 \<and> P Q OS C1 B3" 
      proof (cases "Col P Q B1")
        case True
        hence "P = B1" 
          by (meson \<open>Col P B1 B2\<close> \<open>\<not> Col B1 B2 Q\<close> 
              col_transitivity_2 not_col_permutation_5)
        have "\<exists> B3. Col B2 P B3 \<and> P Q OS C1 B3"
        proof -
          have "B2 \<noteq> P"
            using \<open>B1 \<noteq> B2\<close> \<open>P = B1\<close> by blast
          moreover
          have "Col P Q P" 
            using True \<open>P = B1\<close> by auto
          moreover
          have "Col B2 P P" 
            using not_col_distincts by auto
          moreover
          have "\<not> Col P Q B2" 
            using Col_cases \<open>P = B1\<close> \<open>\<not> Col B1 B2 Q\<close> by blast
          moreover
          have "\<not> Col P Q C1"
            using Col_cases \<open>\<not> Col Q C1 P\<close> by blast
          moreover
          have "Coplanar P Q B2 C1" 
            using \<open>B1 B2 OS Q C1\<close> \<open>P = B1\<close> coplanar_perm_2 
              os__coplanar by blast
          ultimately
          show ?thesis
            using cop_not_par_same_side by blast
        qed
        then obtain B3 where "Col B2 P B3" and "P Q OS C1 B3"
          by blast
        thus ?thesis
          using \<open>P = B1\<close> not_col_permutation_4 by blast 
      next
        case False
        have "Col P Q P" 
          by (meson not_col_distincts)
        moreover
        have "Coplanar P Q B1 C1" 
        proof -
          have "\<not> Col B2 Q B1" 
            using Col_cases \<open>\<not> Col B1 B2 Q\<close> by blast
          moreover
          have "Coplanar B2 Q B1 P" 
            using NCol_perm \<open>Col P B1 B2\<close> ncop__ncols by blast
          moreover
          have "Coplanar B2 Q B1 C1"
            using \<open>B1 B2 OS Q C1\<close> ncoplanar_perm_12 
              os__coplanar by blast 
          ultimately
          show ?thesis
            by (meson coplanar_trans_1 ncoplanar_perm_8) 
        qed
        ultimately
        show ?thesis
          using \<open>B1 \<noteq> B2\<close> \<open>Col B1 B2 P\<close> False 
            \<open>\<not> Col Q C1 P\<close> cop_not_par_same_side 
            Col_cases by blast  
      qed
      then obtain B3 where "Col B1 B2 B3" and "P Q OS C1 B3" 
        by blast
      have "\<not> Col P Q B3"
        using \<open>P Q OS C1 B3\<close> one_side_not_col124 by auto
      have "Coplanar A1 A2 C1 P"
        using Col_cases \<open>A1 A2 Par C1 C2\<close> \<open>C2 \<noteq> C1\<close> 
          \<open>Col P C1 C2\<close> col_cop__cop par__coplanar by blast
      have "\<exists> A3. Col A1 A2 A3 \<and> P Q OS C1 A3"
      proof (cases "Col P Q A1")
        case True
        have "Q = A1"
          by (meson True \<open>Col Q A1 A2\<close> \<open>\<not> Col A1 A2 P\<close> 
              col_permutation_1 col_trivial_2 colx)
        have "\<exists> A3. Col A2 Q A3 \<and> P Q OS C1 A3"
        proof -
          have "A2 \<noteq> Q" 
            using \<open>A1 \<noteq> A2\<close> \<open>Q = A1\<close> by auto
          moreover
          have "Col P Q Q" 
            by (simp add: col_trivial_2)
          moreover
          have "Col A2 Q Q" 
            by (simp add: col_trivial_2)
          moreover
          have "\<not> Col P Q A2" 
            using Col_cases \<open>Q = A1\<close> \<open>\<not> Col A1 A2 P\<close> by blast
          moreover
          have "\<not> Col P Q C1" 
            using Col_cases \<open>\<not> Col Q C1 P\<close> by blast
          moreover
          have "Coplanar P Q A2 C1" 
            using \<open>Coplanar A1 A2 C1 P\<close> \<open>Q = A1\<close> ncoplanar_perm_9 by blast
          ultimately
          show ?thesis 
            using cop_not_par_same_side by blast
        qed
        then obtain A3 where "Col A2 Q A3" and "P Q OS C1 A3"
          by blast
        thus ?thesis
          using \<open>Q = A1\<close> not_col_permutation_4 by blast 
      next
        case False
        have "Col P Q Q" 
          by (simp add: col_trivial_2)
        moreover
        have "Col A1 A2 Q"
          using NCol_cases \<open>Col Q A1 A2\<close> by blast 
        moreover
        have "\<not> Col P Q C1" 
          using Col_cases \<open>\<not> Col Q C1 P\<close> by blast
        moreover
        have "Coplanar P Q A1 C1"
          using \<open>A1 \<noteq> A2\<close> \<open>Coplanar A1 A2 C1 P\<close> 
            calculation(2) col_cop__cop coplanar_perm_16 
            ncoplanar_perm_19 by blast 
        ultimately
        show ?thesis 
          using False \<open>A1 \<noteq> A2\<close> cop_not_par_same_side by blast 
      qed
      then obtain A3 where "Col A1 A2 A3" and "P Q OS C1 A3" 
        by blast
      have "Q \<noteq> B3" 
        using \<open>Col B1 B2 B3\<close> \<open>\<not> Col B1 B2 Q\<close> by blast
      have "P \<noteq> B3" 
        using \<open>\<not> Col P Q B3\<close> col_trivial_3 by auto
      have "B2 \<noteq> Q" 
        using \<open>\<not> Col B1 B2 Q\<close> col_trivial_2 by auto
      have "Q \<noteq> B1" 
        using \<open>\<not> Col B1 B2 Q\<close> col_trivial_3 by blast
      have "Q \<noteq> C1" 
        using \<open>\<not> Col Q C1 P\<close> not_col_distincts by blast
      have "P \<noteq> A3" 
        using \<open>Col A1 A2 A3\<close> \<open>\<not> Col A1 A2 P\<close> by auto
      have "Q \<noteq> A3" 
        using \<open>P Q OS C1 A3\<close> os_distincts by blast
      have False 
      proof -
        have H1: "Q A3 Perp P Q \<and> P B3 Perp P Q \<and> Q A3 ParStrict P B3 \<and>
              Q A3 ParStrict P C1 \<and> P B3 OS Q C1 \<and> 
              P Q OS C1 A3 \<and> P Q OS C1 B3"
        proof -
          have "Col A1 A2 Q"
            using Col_cases \<open>Col Q A1 A2\<close> by blast
          hence "Q A3 Perp P Q"
            using \<open>A1 A2 Perp P Q\<close> \<open>Q \<noteq> A3\<close> \<open>Col A1 A2 A3\<close> perp_col2 by blast
          moreover
          have "Col B1 B2 P" 
            by (simp add: \<open>Col B1 B2 P\<close>) 
          hence "P B3 Perp P Q" 
            using perp_col2 \<open>B1 B2 Perp P Q\<close> \<open>Col B1 B2 B3\<close> \<open>P \<noteq> B3\<close> by blast
          moreover
          have "Q A3 ParStrict P B3"
            using \<open>Q \<noteq> A3\<close> \<open>P \<noteq> B3\<close> \<open>A1 A2 ParStrict B1 B2\<close> 
              \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 A3\<close> \<open>Col B1 B2 P\<close> 
              \<open>Col B1 B2 B3\<close> par_strict_col4__par_strict by blast 
          moreover
          have "Q A3 ParStrict P C1" 
          proof -
            have "Col C1 C2 P"
              using Col_cases \<open>Col P C1 C2\<close> by auto
            moreover
            have "Col C1 C2 C1" 
              using not_col_distincts by blast
            ultimately
            show ?thesis
              using \<open>Q \<noteq> A3\<close> \<open>P \<noteq> C1\<close> \<open>A1 A2 ParStrict C1 C2\<close> 
                \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 A3\<close> 
                par_strict_col4__par_strict by blast
          qed
          moreover
          have "P B3 OS Q C1" 
            using \<open>P \<noteq> B3\<close> \<open>Col B1 B2 P\<close> \<open>Col B1 B2 B3\<close> 
              \<open>B1 B2 OS Q C1\<close> col2_os__os by blast 
          ultimately
          show ?thesis by (simp add: \<open>P Q OS C1 A3\<close> \<open>P Q OS C1 B3\<close>)
        qed
        thus ?thesis 
          using legendre_aux_tr assms(1) assms(2) by blast
      qed
    }
    hence "Col C1 B1 B2" 
      by auto
  }
  thus ?thesis by blast
qed

(* RENAME legendre_aux2 \<rightarrow> legendre_aux2_tr *)

lemma legendre_aux2_tr:
  assumes "greenberg_s_axiom" and
    "triangle_postulate"
  shows "\<forall> A1 A2 B1 B2 C1 C2 P. 
              (P Perp2 A1 A2 B1 B2 \<and> \<not> Col A1 A2 P \<and> 
               Col P B1 B2 \<and> Coplanar A1 A2 B1 B2 \<and> 
               A1 A2 Par C1 C2 \<and> Col P C1 C2) 
\<longrightarrow> 
               Col C1 B1 B2"
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume 1: "P Perp2 A1 A2 B1 B2" and
      2: "\<not> Col A1 A2 P" and
      3: "Col P B1 B2" and
      4: "Coplanar A1 A2 B1 B2" and
      5: "A1 A2 Par C1 C2" and
      6: "Col P C1 C2"
    have "A1 A2 ParStrict B1 B2" 
      using Col_cases \<open>Col P B1 B2\<close> \<open>Coplanar A1 A2 B1 B2\<close> 
        \<open>P Perp2 A1 A2 B1 B2\<close> \<open>\<not> Col A1 A2 P\<close> 
        col_cop_perp2__pars_bis by blast
    {
      assume "B1 B2 TS A1 C1" 
      hence "\<not> Col C1 B1 B2" 
        using TS_def by blast
      have "C1 \<noteq> P"
        using "3" \<open>\<not> Col C1 B1 B2\<close> by auto
      obtain C3 where "P Midpoint C1 C3"
        using symmetric_point_construction by blast
      hence "C1 \<noteq> C3" 
        by (metis \<open>C1 \<noteq> P\<close> midpoint_distinct_2)
      have "\<not> Col C3 B1 B2" 
        by (metis "3" \<open>P Midpoint C1 C3\<close> \<open>\<not> Col C1 B1 B2\<close> 
            col_trivial_2 l6_21 midpoint_col midpoint_distinct_2 
            not_col_permutation_3 not_col_permutation_4)
      moreover
      have "Col C3 B1 B2"
      proof -
        have "P Perp2 A1 A2 B1 B2"
          by (simp add: "1") 
        moreover
        have "\<not> Col A1 A2 P"
          by (simp add: "2") 
        moreover
        have "Col P B1 B2"
          by (simp add: "3") 
        moreover
        have "Coplanar A1 A2 B1 B2"
          by (simp add: "4") 
        moreover
        have "A1 A2 Par C1 P"
          by (metis "5" "6" \<open>C1 \<noteq> P\<close> col_trivial_2 
              par_col2_par_bis par_right_comm) 
        hence "A1 A2 Par C1 C3" 
          using Col_def Midpoint_def \<open>C1 \<noteq> C3\<close> 
            \<open>P Midpoint C1 C3\<close> par_col_par by blast
        hence "A1 A2 Par C3 C1"
          using Par_perm by blast 
        moreover
        have "Col P C3 C1"
          using \<open>P Midpoint C1 C3\<close> 
          by (meson Mid_cases midpoint_col) 
        moreover
        have "Bet C3 P C1" 
          using \<open>P Midpoint C1 C3\<close> 
          by (metis midpoint_bet between_symmetry) 
        hence "B1 B2 TS C3 C1" 
          using 3 TS_def \<open>\<not> Col C1 B1 B2\<close> \<open>\<not> Col C3 B1 B2\<close> by blast 
        hence "B1 B2 OS A1 C3" 
          using \<open>B1 B2 TS A1 C1\<close> l9_8_1 by blast 
        hence "\<not> B1 B2 TS A1 C3"
          using l9_9_bis by auto 
        ultimately
        show ?thesis 
          using legendre_aux1_tr greenberg_s_axiom_def 
            triangle_postulate_def assms(1) assms(2) by blast
      qed
      ultimately
      have "False"
        using \<open>\<not> Col C3 B1 B2\<close>\<open>Col C3 B1 B2\<close> by blast
    }
    hence "\<not> B1 B2 TS A1 C1" 
      by blast
    hence "Col C1 B1 B2"
      using legendre_aux1_tr greenberg_s_axiom_def 
        assms(1) assms(2) 1 2 3 4 5 6 by blast
  }
  thus ?thesis 
    by blast
qed

lemma triangle__playfair_bis:
  assumes "greenberg_s_axiom" and
    "triangle_postulate"
  shows "alternative_playfair_s_postulate"
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume 1: "P Perp2 A1 A2 B1 B2" and
      2: "\<not> Col A1 A2 P" and
      3: "Col P B1 B2" and
      4: "Coplanar A1 A2 B1 B2" and
      5: "A1 A2 Par C1 C2" and
      6: "Col P C1 C2"
    have "Col C1 B1 B2" 
      using 1 2 3 4 5 6 legendre_aux2_tr 
        greenberg_s_axiom_def assms(1) assms(2)
      by blast
    moreover
    have "Col C2 B1 B2" 
    proof -
      have "A1 A2 Par C2 C1"
        by (simp add: "5" par_right_comm) 
      moreover 
      have "Col P C2 C1"
        by (simp add: "6" col_permutation_5) 
      ultimately
      show ?thesis
        using 1 2 3 4 legendre_aux2_tr greenberg_s_axiom_def 
          assms(1) assms(2) by blast
    qed
    ultimately
    have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
      by simp
  }
  thus ?thesis
    using alternative_playfair_s_postulate_def by blast 
qed

lemma rah__existential_saccheri:
  assumes "postulate_of_right_saccheri_quadrilaterals"
  shows "postulate_of_existence_of_a_right_saccheri_quadrilateral"
proof -
  obtain A B C D where "Saccheri A B C D"
    using ex_saccheri by blast
  moreover
  have "Per A B C" 
    using assms 
      calculation postulate_of_right_saccheri_quadrilaterals_def 
    by blast 
  ultimately
  show ?thesis
    using postulate_of_existence_of_a_right_saccheri_quadrilateral_def 
    by blast 
qed

lemma rah__posidonius_aux:
  assumes "postulate_of_right_saccheri_quadrilaterals"
  shows "\<forall> A1 A2 A3 B1 B2 B3.
                (Per A2 A1 B1 \<and> Per A1 A2 B2 \<and> 
                 Cong A1 B1 A2 B2 \<and> A1 A2 OS B1 B2 \<and> 
                 Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> 
                 A1 A2 Perp A3 B3) 
\<longrightarrow> 
                Cong A3 B3 A1 B1"
proof -
  {
    fix A1 A2 A3 B1 B2 B3
    assume 1: "Per A2 A1 B1" and
      2: "Per A1 A2 B2" and
      3: "Cong A1 B1 A2 B2" and
      4: "A1 A2 OS B1 B2" and
      5: "Col A1 A2 A3" and
      6: "Col B1 B2 B3" and
      7: "A1 A2 Perp A3 B3"
    have "A1 \<noteq> B1"
      using \<open>A1 A2 OS B1 B2\<close> \<open>Cong A1 B1 A2 B2\<close> 
        col_trivial_2 cong_reverse_identity 
        one_side_not_col124 by blast
    have "B2 \<noteq> B1" 
      using \<open>A1 A2 Perp A3 B3\<close> \<open>Cong A1 B1 A2 B2\<close> 
        \<open>Per A1 A2 B2\<close> \<open>Per A2 A1 B1\<close> diff_per_diff 
        perp_not_eq_1 by blast
    have "A2 \<noteq> B2" 
      using \<open>A1 \<noteq> B1\<close> \<open>Cong A1 B1 A2 B2\<close> cong_identity_inv by blast
    have "A1 \<noteq> A2" 
      using \<open>A1 A2 OS B1 B2\<close> os_distincts by auto
    have "A1 \<noteq> B2" 
      using \<open>A2 \<noteq> B2\<close> \<open>Per A1 A2 B2\<close> per_distinct_1 by blast
    have "A2 \<noteq> B1" 
      using \<open>A1 \<noteq> A2\<close> \<open>Per A2 A1 B1\<close> per_distinct_1 by blast
    have "Cong A3 B3 A1 B1" 
    proof (cases "A1 = A3")
      case True
      hence "A1 = A3" 
        by blast
      have "B1 = B3" 
      proof -
        have "\<not> Col B1 B2 A1" 
          using 1 2 \<open>A1 \<noteq> A2\<close> \<open>A1 \<noteq> B1\<close> \<open>A2 \<noteq> B2\<close>
            col_permutation_5 per_not_colp by blast 
        moreover
        have "Col B1 B2 B1"
          using not_col_distincts by blast 
        moreover
        have "Col A1 B1 B1"
          using not_col_distincts by blast 
        moreover
        have "Col A1 B1 B3" 
        proof -
          {
            assume "\<not> Col A1 B1 B3"
            have "Per A2 A1 B3" 
              using perp_per_2 "7" \<open>A1 = A3\<close> by blast
            hence "\<not> Col A1 A2 B3" 
              by (meson "5" "7" l8_16_1)
            have "Per A1 A2 B3"
            proof -
              have f2: "Per B2 A2 A1" 
                by (simp add: "2" l8_2)
              have f3: "Per B1 A1 A2"  
                by (simp add: "1" l8_2)
              have "Col B3 B1 B2" 
                by (simp add: "6" col_permutation_2)
              then show ?thesis 
                by (metis col_per2__per l8_2 l8_7 not_col_distincts 
                    \<open>Per A2 A1 B3\<close> \<open>\<not> Col A1 B1 B3\<close> 
                    \<open>Per B2 A2 A1\<close> \<open>Per B1 A1 A2\<close>)
            qed
            hence "A1 = A2" 
              using \<open>Per A2 A1 B3\<close> l8_2 l8_7 by blast
            hence False  
              by (simp add: \<open>A1 \<noteq> A2\<close>)
          }
          thus ?thesis 
            by blast
        qed
        ultimately
        show ?thesis
          using 6 \<open>A1 \<noteq> B1\<close> l6_21 by blast 
      qed
      thus ?thesis
        using True cong_reflexivity by auto 
    next
      case False
      have "A3 \<noteq> B3"
        using "7" perp_not_eq_2 by auto 
      then obtain B'3 where "A3 Out B3 B'3" and "Cong A3 B'3 A1 B1" 
        using segment_construction_3 \<open>A1 \<noteq> B1\<close> by blast
      hence "A3 \<noteq> B'3"
        using out_distinct by blast
      have "B3 = B'3" 
      proof -
        have "Saccheri A1 B1 B2 A2"
          by (meson "1" "2" "3" "4" Per_cases Saccheri_def not_cong_1243) 
        hence "A1 A2 ParStrict B1 B2"
          using sac__pars1423 by auto 
        hence "B1 B2 ParStrict A1 A2"
          by (simp add: par_strict_symmetry) 
        hence "B1 B2 ParStrict A1 A3"
          using 5 False par_strict_col_par_strict by blast 
        have "\<not> Col B1 B2 A3"
          using \<open>B1 B2 ParStrict A1 A3\<close> par_strict_not_col_4 by auto 
        moreover
        have "A3 \<noteq> B3"
          using \<open>A3 \<noteq> B3\<close> by auto
        moreover
        have "Col B1 B2 B3"
          using "6" by auto 
        moreover
        have "Col B2 B'3 B1" 
        proof -
          have "Coplanar A1 B2 B'3 B1"
          proof -
            have "\<not> Col A3 B1 B2"
              using NCol_cases calculation(1) by blast 
            moreover
            have "Coplanar A3 B1 B2 A1"
              using \<open>B1 B2 ParStrict A1 A3\<close> ncoplanar_perm_9 
                pars__coplanar by blast 
            moreover
            have "Coplanar A3 B1 B2 B'3"
              using "6" Coplanar_def Out_cases \<open>A3 Out B3 B'3\<close> 
                out_col by blast 
            ultimately
            show ?thesis
              by (meson coplanar_trans_1 ncoplanar_perm_20) 
          qed
          moreover
          have "Per B2 B1 A1"
            using \<open>Saccheri A1 B1 B2 A2\<close> Per_perm assms 
              postulate_of_right_saccheri_quadrilaterals_def by blast 
          moreover
          have "Saccheri A1 B1 B'3 A3" 
          proof -
            {
              assume "B1 = B3"
              have "A1 = A3" 
              proof -
                have "\<not> Col A1 A2 B1"
                  using "4" col123__nos by blast
                moreover
                have "Col A1 A2 A1"
                  by (simp add: col_trivial_3) 
                moreover
                have "A1 A2 Perp B1 A1"
                  using "1" \<open>A1 \<noteq> A2\<close> \<open>A1 \<noteq> B1\<close> per_perp 
                    perp_comm by presburger 
                moreover
                have "A1 A2 Perp B1 A3"
                  by (simp add: "7" \<open>B1 = B3\<close> perp_right_comm) 
                ultimately
                show ?thesis
                  using 5 l8_18_uniqueness by blast 
              qed
              hence False
                using False by auto 
            }
            hence "B1 \<noteq> B3" 
              by blast
            have "Per A1 A3 B'3"
              by (metis "5" "7" \<open>A3 Out B3 B'3\<close> col_trivial_3 
                  l8_16_1 l8_2 l8_3 out_col perp_right_comm) 
            moreover
            have "Per B1 A1 A3"
              using "1" "5" \<open>A1 \<noteq> A2\<close> l8_2 l8_3 by blast 
            moreover
            have "Cong A1 B1 B'3 A3"
              using Cong_cases \<open>Cong A3 B'3 A1 B1\<close> by blast 
            moreover
            have "A1 A3 OS B1 B'3" 
            proof -
              have "A1 A3 OS B1 B3"
                by (meson "5" "6" False \<open>B1 B2 ParStrict A1 A2\<close>
                    \<open>B1 \<noteq> B3\<close> col_trivial_3 par_strict_col4__par_strict 
                    pars__os3412) 
              moreover
              have "A1 A3 OS B3 B'3"
                using \<open>A3 Out B3 B'3\<close> calculation col_trivial_2 
                  one_side_not_col124 out_one_side_1 by blast 
              ultimately
              show ?thesis
                using one_side_transitivity by blast 
            qed
            ultimately
            show ?thesis
              using Saccheri_def by blast 
          qed
          hence "Per B'3 B1 A1"
            using Per_perm assms 
              postulate_of_right_saccheri_quadrilaterals_def by blast 
          ultimately
          show ?thesis
            using \<open>A1 \<noteq> B1\<close> cop_per2__col by blast 
        qed
        hence "Col B1 B2 B'3"
          using Col_cases by blast 
        moreover
        have "Col A3 B3 B3"
          by (metis not_col_distincts) 
        moreover  
        have "Col A3 B3 B'3"
          using \<open>A3 Out B3 B'3\<close> out_col by auto 
        ultimately
        show ?thesis
          using l6_21 by blast 
      qed
      thus ?thesis
        using \<open>Cong A3 B'3 A1 B1\<close> by auto 
    qed
  }
  thus ?thesis by blast
qed

(** There exists two lines which are everywhere equidistant. *)

lemma rah__posidonius:
  assumes "postulate_of_right_saccheri_quadrilaterals"
  shows "posidonius_postulate"
proof -
  obtain A1 B1 B2 A2 where "Saccheri A1 B1 B2 A2"
    using ex_saccheri by presburger
  hence H1: "Per B1 A1 A2 \<and> Per A1 A2 B2 \<and> 
             Cong A1 B1 B2 A2 \<and> A1 A2 OS B1 B2" 
    using Saccheri_def by blast
  hence "Per B1 A1 A2" by blast
  have "Per A1 A2 B2"
    by (simp add: H1) 
  have "Cong A1 B1 B2 A2" 
    by (simp add: H1) 
  have "A1 A2 OS B1 B2" 
    by (simp add: H1) 
  have "\<not> Col A1 A2 B1"
    using \<open>A1 A2 OS B1 B2\<close> col123__nos by blast 
  moreover
  have "B1 \<noteq> B2"
    using \<open>Saccheri A1 B1 B2 A2\<close> sac_distincts by blast 
  moreover
  have "Coplanar A1 A2 B1 B2"
    using \<open>Saccheri A1 B1 B2 A2\<close> ncoplanar_perm_3 
      sac__coplanar by blast 
  moreover
  {
    fix A3 A4 B3 B4
    assume "Col A1 A2 A3" and
      "Col B1 B2 B3" and
      "A1 A2 Perp A3 B3" and
      "Col A1 A2 A4" and
      "Col B1 B2 B4" and
      "A1 A2 Perp A4 B4"
    have "(Per A2 A1 B1 \<and> Per A1 A2 B2 \<and> Cong A1 B1 A2 B2 \<and>
           A1 A2 OS B1 B2 \<and> Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> 
           A1 A2 Perp A3 B3) \<longrightarrow> Cong A3 B3 A1 B1" 
      using rah__posidonius_aux assms by blast 
    hence "Cong A3 B3 A1 B1" 
      using Cong_cases \<open>A1 A2 OS B1 B2\<close> \<open>A1 A2 Perp A3 B3\<close> 
        \<open>Col A1 A2 A3\<close> \<open>Col B1 B2 B3\<close> \<open>Cong A1 B1 B2 A2\<close> 
        \<open>Per A1 A2 B2\<close> \<open>Per B1 A1 A2\<close> l8_2 by blast
    hence "Cong A1 B1 A3 B3"
      using not_cong_3412 by blast 
    moreover
    have "(Per A2 A1 B1 \<and> Per A1 A2 B2 \<and> Cong A1 B1 A2 B2 \<and>
          A1 A2 OS B1 B2 \<and> Col A1 A2 A4 \<and> Col B1 B2 B4 \<and> 
          A1 A2 Perp A4 B4) \<longrightarrow>  Cong A4 B4 A1 B1"
      using rah__posidonius_aux assms by blast 
    hence "Cong A4 B4 A1 B1" 
      using Cong_cases \<open>A1 A2 OS B1 B2\<close> \<open>A1 A2 Perp A4 B4\<close> 
        \<open>Col A1 A2 A4\<close> \<open>Col B1 B2 B4\<close> \<open>Cong A1 B1 B2 A2\<close>
        \<open>Per A1 A2 B2\<close> \<open>Per B1 A1 A2\<close> l8_2 by blast 
    hence"Cong A1 B1 A4 B4"
      by (simp add: cong_symmetry) 
    ultimately
    have "Cong A3 B3 A4 B4"
      using cong_inner_transitivity by blast 
  }
  ultimately
  show ?thesis 
    using posidonius_postulate_def by blast
qed

(** The angles of a any Lambert quadrilateral are right, i.e
    if in a quadrilateral three angles are right, so is the fourth. *)

lemma rah__rectangle_principle:
  assumes "postulate_of_right_saccheri_quadrilaterals"
  shows "postulate_of_right_lambert_quadrilaterals" 
proof -
  {
    fix A B C D
    assume "Lambert A B C D"
    hence "Per B C D" 
      using lam_per__rah assms existential_playfair__rah_1 by blast 
  }
  thus ?thesis
    by (simp add: postulate_of_right_lambert_quadrilaterals_def) 
qed

(** There exists two non congruent similar triangles. *)


lemma rah__similar:
  assumes "postulate_of_right_saccheri_quadrilaterals"
  shows "postulate_of_existence_of_similar_triangles"
proof -
  obtain A B0 C where "\<not> (Bet A B0 C \<or> Bet B0 C A \<or> Bet C A B0)"
    using lower_dim_ex by blast
  hence "\<not> Col A B0 C"
    by (simp add: Col_def)
  then obtain B where "C A Perp B C" and "C A OS B0 B" 
    using l10_15 by (metis Col_cases col_trivial_3) 
  hence "\<not> Col C A B"
    using col124__nos by blast
  have "Per A C B"
    by (simp add: \<open>C A Perp B C\<close> perp_per_1)
  obtain B' where "B Midpoint A B'"
    using symmetric_point_construction by blast
  have "C \<noteq> A"
    using \<open>\<not> Col A B0 C\<close> col_trivial_3 by blast 
  have "B \<noteq> A"
    using \<open>\<not> Col C A B\<close> col_trivial_2 by blast 
  have "C \<noteq> B"
    using \<open>\<not> Col C A B\<close> col_trivial_3 by auto 
  have "B0 \<noteq> A"
    using \<open>\<not> Col A B0 C\<close> col_trivial_1 by force 
  have "B' \<noteq> A"
    using \<open>B Midpoint A B'\<close> \<open>B \<noteq> A\<close> l7_3 by blast 
  have "B \<noteq> B'"
    by (metis \<open>B Midpoint A B'\<close> \<open>B' \<noteq> A\<close> midpoint_not_midpoint) 
  have "\<not> Col A C B'"
    using \<open>B Midpoint A B'\<close> \<open>B' \<noteq> A\<close> \<open>\<not> Col C A B\<close>
      col2__eq midpoint_col not_col_permutation_4 by blast
  hence "\<not> Col B B' C"
    by (metis \<open>B Midpoint A B'\<close> \<open>B \<noteq> B'\<close> col2__eq 
        col_permutation_1 midpoint_col)
  obtain C' where "Col A C C'" and "A C Perp B' C'"
    using \<open>\<not> Col A C B'\<close> l8_18_existence by blast
  have"\<not> Col A B C"
    using \<open>\<not> Col C A B\<close> col_permutation_2 by blast 
  moreover
  have "\<not> Cong A B A B'"
    by (metis midpoint_bet \<open>B Midpoint A B'\<close> 
        \<open>B \<noteq> B'\<close> between_cong) 
  moreover
  have "B C ParStrict B' C'" 
  proof -
    have "B C Par B' C'" 
    proof -
      have "Bet A B B'"
        by (simp add: \<open>B Midpoint A B'\<close> midpoint_bet) 
      hence "Coplanar A C B B'"
        using bet_col ncop__ncols by blast 
      moreover
      have "Coplanar A C B C'"
        by (meson \<open>Col A C C'\<close> ncop__ncols) 
      moreover
      have "Coplanar A C C B'"
        using ncop_distincts by blast 
      moreover
      have "Coplanar A C C C'"
        using ncop_distincts by blast 
      moreover
      have "B C Perp A C"
        using Perp_perm \<open>C A Perp B C\<close> by blast 
      moreover
      have "B' C' Perp A C"
        using Perp_perm \<open>A C Perp B' C'\<close> by blast 
      ultimately
      show ?thesis
        using l12_9 by blast 
    qed
    moreover
    have "Col B' C' B'"
      using not_col_distincts by blast 
    moreover
    have "\<not> Col B C B'"
      using \<open>\<not> Col B B' C\<close> not_col_permutation_5 by blast 
    ultimately
    show ?thesis
      using par_not_col_strict by auto 
  qed
  have "\<not> Col B C C'"
    by (meson \<open>B C ParStrict B' C'\<close> not_col_permutation_1 
        par_strict_not_col_2 par_strict_symmetry)
  hence "C \<noteq> C'"
    using col_trivial_2 by auto 
  have "B' \<noteq> C'"
    using \<open>B C ParStrict B' C'\<close> col_trivial_1 col_trivial_3 
      one_side_not_col124 par_strict_one_side by blast 
  have "Bet A C C'" 
  proof -
    have "Col C A C'"
      by (simp add: \<open>Col A C C'\<close> col_permutation_4)
    moreover
    have "C B TS C' A"
    proof -
      have "C B TS B' A" 
      proof -
        have "\<not> Col B' C B"
          using \<open>\<not> Col B B' C\<close> col_permutation_2 by blast 
        moreover
        have "\<not> Col A C B"
          using \<open>\<not> Col A B C\<close> col_permutation_5 by blast 
        moreover
        have "Col B C B"
          using not_col_distincts by blast
        moreover
        have "Bet B' B A"
          using \<open>B Midpoint A B'\<close> between_symmetry 
            midpoint_bet by blast 
        ultimately
        show ?thesis
          using TS_def by blast 
      qed
      moreover
      have "C B OS B' C'"
        using Par_strict_perm \<open>B C ParStrict B' C'\<close> 
          pars__os3412 by blast 
      ultimately
      show ?thesis
        using l9_8_2 by blast 
    qed
    hence "C B TS A C'"
      by (simp add: l9_2) 
    ultimately
    show ?thesis
      using col_two_sides_bet by blast 
  qed
  have "A \<noteq> C'"
    using \<open>Bet A C C'\<close> \<open>C \<noteq> C'\<close> between_equality_2 
      between_trivial2 by blast
  have "C' B' Perp A C'" 
  proof -
    have "A \<noteq> C'"
      using \<open>A \<noteq> C'\<close> by auto 
    moreover
    have "C' B' Perp A C"
      using Perp_perm \<open>A C Perp B' C'\<close> by blast 
    ultimately
    show ?thesis
      using \<open>Col A C C'\<close> perp_col1 by blast 
  qed
  hence "Per B' C' A" 
    using perp_per_1 by blast
  have "A B C CongA A B' C'" 
  proof -
    have "SAMS C A B A B C"
      using \<open>B \<noteq> A\<close> \<open>C \<noteq> A\<close> \<open>C \<noteq> B\<close> sams123231 by auto 
    moreover
    have "SAMS C A B A B' C'" 
    proof -
      have "C' A B' CongA C A B"
        by (metis midpoint_bet out2__conga 
            \<open>B Midpoint A B'\<close> \<open>B \<noteq> A\<close> \<open>Bet A C C'\<close> 
            \<open>C \<noteq> A\<close> bet_out) 
      moreover
      have "A B' C' CongA A B' C'"
        using \<open>B' \<noteq> A\<close> \<open>B' \<noteq> C'\<close> lea_asym lea_refl by auto 
      moreover
      have "SAMS C' A B' A B' C'"
        using \<open>A \<noteq> C'\<close> \<open>B' \<noteq> A\<close> \<open>B' \<noteq> C'\<close> sams123231 by force 
      ultimately
      show ?thesis
        using conga2_sams__sams by blast 
    qed
    moreover
    have "C A B A B C SumA B C A" 
    proof -
      have "Per B C A"
        using Per_perm \<open>Per A C B\<close> by blast 
      moreover
      have "hypothesis_of_right_saccheri_quadrilaterals"
        using assms existential_playfair__rah_1 by blast
      ultimately
      show ?thesis
        using \<open>C \<noteq> A\<close> \<open>C \<noteq> B\<close> t22_12__rah_2 by presburger 
    qed
    moreover
    have "C A B A B' C' SumA B C A" 
    proof -
      have "hypothesis_of_right_saccheri_quadrilaterals"
        using assms existential_playfair__rah_1 by auto 
      hence "C' A B' A B' C' SumA B' C' A" 
        using \<open>A \<noteq> C'\<close> \<open>B' \<noteq> C'\<close> \<open>Per B' C' A\<close> 
          t22_12__rah_2 by presburger 
      moreover
      have "C' A B' CongA C A B"
        by (metis midpoint_bet out2__conga
            \<open>B Midpoint A B'\<close> \<open>B \<noteq> A\<close> \<open>Bet A C C'\<close> 
            \<open>C \<noteq> A\<close> bet_out) 
      moreover
      have "A B' C' CongA A B' C'"
        using \<open>B' \<noteq> A\<close> \<open>B' \<noteq> C'\<close> conga_refl by auto 
      moreover
      have "B' C' A CongA B C A"
        by (metis \<open>A C Perp B' C'\<close> \<open>A \<noteq> C'\<close> 
            \<open>C A Perp B C\<close> \<open>C \<noteq> A\<close> \<open>C \<noteq> B\<close> \<open>C \<noteq> C'\<close> 
            \<open>Col A C C'\<close> col2__eq conga_right_comm l11_16 
            l8_16_1 perp_per_1) 
      ultimately
      show ?thesis
        by (meson conga3_suma__suma) 
    qed
    ultimately
    show ?thesis
      using sams2_suma2__conga456 by blast 
  qed
  moreover
  have "B C A CongA B' C' A"
    by (metis \<open>A C Perp B' C'\<close> \<open>A \<noteq> C'\<close> 
        \<open>C A Perp B C\<close> \<open>C \<noteq> A\<close> \<open>C \<noteq> B\<close> \<open>C \<noteq> C'\<close> 
        \<open>Col A C C'\<close> conga_left_comm l11_16 l6_16_1 
        l8_16_1 perp_per_1) 
  moreover
  have "C A B CongA C' A B'" 
  proof -
    have "A Out C' C"
      by (simp add: \<open>Bet A C C'\<close> \<open>C \<noteq> A\<close> bet_out l6_6) 
    moreover
    have "A Out B' B"
      by (simp add: \<open>B Midpoint A B'\<close> \<open>B' \<noteq> A\<close> l7_2 midpoint_out_1) 
    ultimately
    show ?thesis
      by (simp add: out2__conga) 
  qed
  ultimately
  show ?thesis 
    using postulate_of_existence_of_similar_triangles_def by blast 
qed

lemma rah__thales_postulate:
  assumes "postulate_of_right_saccheri_quadrilaterals"
  shows "thales_postulate" 
proof -
  {
    fix  A B C M
    assume "M Midpoint A B" and "Cong M A M C"
    have "Per A C B"
    proof (cases "Col A B C")
      case True
      show ?thesis 
      proof (cases "A = B")
        case True
        thus ?thesis
          using \<open>Cong M A M C\<close> \<open>M Midpoint A B\<close> 
            cong_reverse_identity l8_20_2 l8_5 by blast
      next
        case False
        hence "A \<noteq> B" 
          by auto
        moreover
        have "Col A M B"
          using \<open>M Midpoint A B\<close> midpoint_col 
            not_col_permutation_4 by blast 
        hence "Col A M C"
          by (meson True calculation col_trivial_3 colx) 
        ultimately
        show ?thesis
          by (metis \<open>Cong M A M C\<close> \<open>M Midpoint A B\<close> 
              cong_col_mid cong_left_commutativity l8_2 l8_5 
              symmetric_point_uniqueness)
      qed
    next
      case False
      thus ?thesis 
        using t22_17__rah \<open>Cong M A M C\<close> \<open>M Midpoint A B\<close>
          assms existential_playfair__rah_1 by blast 
    qed
  }
  thus ?thesis
    using thales_postulate_def by blast 
qed

lemma rah__triangle:
  assumes "postulate_of_right_saccheri_quadrilaterals"
  shows "triangle_postulate" 
proof -
  {
    fix A B C D E F
    assume "A B C TriSumA D E F"
    hence "Bet D E F"
      using assms existential_playfair__rah_1 t22_14__bet by blast 
  }
  thus ?thesis
    using triangle_postulate_def by blast 
qed

(** There exists a Lambert quadrilateral whose angles are right. *)

lemma rectangle_principle__rectangle_existence:
  assumes "postulate_of_right_lambert_quadrilaterals"
  shows "postulate_of_existence_of_a_right_lambert_quadrilateral"
proof - 
  obtain A B C D where "Saccheri A B C D"
    using ex_saccheri by blast
  moreover
  obtain M where "M Midpoint B C" 
    using midpoint_existence by blast
  moreover
  obtain N where "N Midpoint A D"
    using midpoint_existence by blast
  ultimately
  have "Lambert N M B A" 
    by (meson mid2_sac__lam6521)
  moreover
  have "Per M B A" 
    using postulate_of_right_lambert_quadrilaterals_def 
      assms \<open>Lambert N M B A\<close> by blast
  ultimately
  show ?thesis 
    using postulate_of_existence_of_a_right_lambert_quadrilateral_def 
    by blast
qed

(**
This is an adaptation of the proof of Martin's Theorem 23.6.
It is more complicated because Martin use the properties of the deflect of a triangle,
which are difficult to handle in our formalization.
*)

lemma similar__rah_aux:
  assumes "\<not> Col A B C" and
    "A B C CongA D E F" and
    "B C A CongA E F D" and
    "C A B CongA F D E" and
    "B C A LeA A B C" and
    "D E Lt A B"
  shows "postulate_of_right_saccheri_quadrilaterals" 
proof -
  have "A \<noteq> B" 
    using assms(1) col_trivial_1 by auto
  have "C \<noteq> B" 
    using assms(1) col_trivial_2 by blast
  have "A \<noteq> C"
    using assms(1) col_trivial_3 by blast
  have "F \<noteq> E"
    using assms(2) conga_distinct by presburger
  have "D \<noteq> E" 
    using assms(4) conga_diff56 by blast
  then obtain G where "A Out B G" and "Cong A G D E" 
    using segment_construction_3 \<open>A \<noteq> B\<close> by blast
  have "D \<noteq> F" 
    using assms(4) conga_distinct by blast
  then obtain H where "A Out C H" and "Cong A H D F" 
    using segment_construction_3 \<open>A \<noteq> C\<close> by blast
  have "A G Lt A B" 
    by (meson \<open>Cong A G D E\<close> assms(6) cong2_lt__lt 
        cong_reflexivity cong_symmetry)
  have "Bet A G B" 
  proof -
    have "A Out G B" 
      by (simp add: \<open>A Out B G\<close> l6_6)
    moreover
    have "A G Le A B" 
      by (simp add: \<open>A G Lt A B\<close> lt__le)
    ultimately
    show ?thesis 
      by (meson l6_13_1)
  qed
  have "B \<noteq> G" 
    using \<open>A G Lt A B\<close> not_and_lt by blast
  have "C A B CongA H A G" 
    by (meson Out_cases \<open>A Out B G\<close> \<open>A Out C H\<close> out2__conga)
  have "D F E CongA A H G \<and> D E F CongA A G H" 
  proof -
    have "F D E CongA H A G" 
      by (meson \<open>C A B CongA H A G\<close> assms(4) 
          not_conga not_conga_sym)
    moreover
    have "Cong D F A H" 
      by (meson \<open>Cong A H D F\<close> not_cong_3412)
    moreover
    have "Cong D E A G"
      by (simp add: \<open>Cong A G D E\<close> cong_symmetry)
    ultimately
    show ?thesis 
      using \<open>F \<noteq> E\<close> l11_49 by blast
  qed
  have "D E F CongA A G H" 
    using \<open>D F E CongA A H G \<and> D E F CongA A G H\<close> by auto 
  hence "A B C CongA A G H" 
    using assms(2) conga_trans by blast
  have "E F D CongA G H A" 
    by (simp add: \<open>D F E CongA A H G \<and> D E F CongA A G H\<close> 
        conga_comm)
  hence "B C A CongA G H A" 
    using assms(3) conga_trans by blast
  have "\<not> Col A G H" 
    by (meson Out_cases \<open>A Out B G\<close> \<open>A Out C H\<close> assms(1) 
        col_out2_col not_col_permutation_2)
  have "\<not> Col B G H" 
    using \<open>B \<noteq> G\<close> \<open>Bet A G B\<close> \<open>\<not> Col A G H\<close> bet_col 
      col2__eq col_permutation_3 by blast
  have "G H ParStrict B C" 
  proof -
    have "B C Par G H" 
    proof -
      have "A B OS C H" 
        by (simp add: \<open>A Out C H\<close> assms(1) out_one_side)
      moreover
      have "C B A CongA H G A" 
        by (simp add: \<open>A B C CongA A G H\<close> conga_comm)
      ultimately
      show ?thesis 
        using \<open>A Out B G\<close> l12_22_b by auto
    qed
    hence "G H Par B C" 
      using par_symmetry by blast
    moreover
    have "Col B C B" 
      by (simp add: col_trivial_3)
    moreover
    have "\<not> Col G H B" 
      by (simp add: \<open>\<not> Col B G H\<close> not_col_permutation_1)
    ultimately
    show ?thesis 
      using par_not_col_strict by blast
  qed
  have "\<not> Col G H C" 
    by (meson \<open>G H ParStrict B C\<close> l12_6 one_side_not_col124)
  have "\<not> Col B C G" 
    by (meson \<open>A Out B G\<close> \<open>B \<noteq> G\<close> assms(1) col_trivial_2 
        colx not_col_permutation_5 out_col)
  have "\<not> Col H B C" 
    by (metis \<open>A Out C H\<close> \<open>\<not> Col G H C\<close> assms(1) 
        col_trivial_3 colx not_col_permutation_2 out_col)
  have "H \<noteq> C" 
    using \<open>\<not> Col H B C\<close> col_trivial_3 by auto
  have "G \<noteq> C" 
    using \<open>\<not> Col B C G\<close> col_trivial_2 by auto
  have "H \<noteq> G" 
    using \<open>\<not> Col A G H\<close> col_trivial_2 by blast
  have "A \<noteq> G" 
    using \<open>\<not> Col A G H\<close> col_trivial_1 by auto
  have "H \<noteq> A" 
    using \<open>\<not> Col A G H\<close> col_trivial_3 by blast
  have "C Out H A" 
  proof -
    have "Col C H A" 
      using \<open>A Out C H\<close> col_permutation_1 out_col by blast
    moreover
    have "B C OS H A" 
    proof -
      have "B C OS H G" 
        using \<open>G H ParStrict B C\<close> one_side_symmetry 
          pars__os3412 by blast
      moreover
      have "B C OS G A" 
        using \<open>B \<noteq> G\<close> \<open>Bet A G B\<close> \<open>\<not> Col B C G\<close> 
          bet_out_1 out_one_side by presburger
      ultimately
      show ?thesis 
        using one_side_transitivity by blast
    qed
    hence "C B OS H A" 
      by (simp add: invert_one_side)
    ultimately
    show ?thesis 
      using col_one_side_out by force
  qed
  hence "Bet A H C"
    by (meson \<open>A Out C H\<close> between_symmetry out2__bet)
  have "SAMS B G H H C B" 
  proof -
    have "Bet B G A" 
      using Bet_cases \<open>Bet A G B\<close> by blast
    moreover
    have "H C B LeA H G A" 
    proof -
      have "B C A LeA A B C" 
        by (simp add: assms(5))
      moreover
      have "B C A CongA H C B" 
        by (metis CongA_def \<open>B C A CongA G H A\<close> 
            \<open>Bet A H C\<close> \<open>H \<noteq> C\<close> bet2__out bet_out_1 
            conga_left_comm out2__conga)
      moreover
      have "A B C CongA H G A" 
        using \<open>A B C CongA A G H\<close> conga_right_comm by blast
      ultimately
      show ?thesis 
        using l11_30 by blast
    qed
    ultimately
    show ?thesis 
      using \<open>A \<noteq> G\<close> \<open>B \<noteq> G\<close> sams_chara by blast
  qed
  have "A G H CongA G B C" 
    by (metis out2__conga \<open>A B C CongA A G H\<close>
        \<open>B \<noteq> G\<close> \<open>Bet A G B\<close> \<open>C \<noteq> B\<close> 
        bet_out_1 conga_sym_equiv 
        conga_trans out_trivial)
  have "G H A CongA B C H" 
    by (metis Out_def \<open>B C A CongA G H A\<close> \<open>C Out H A\<close> 
        \<open>C \<noteq> B\<close> not_bet_distincts not_conga 
        not_conga_sym out2__conga)
  have "SAMS B G H C B G" 
  proof -
    have "B G H CongA B G H" 
      using \<open>B \<noteq> G\<close> \<open>H \<noteq> G\<close> conga_refl by blast
    moreover
    have "H G A CongA C B G" 
      by (simp add: \<open>A G H CongA G B C\<close> conga_comm)
    moreover
    have "SAMS B G H H G A" 
      by (metis \<open>A \<noteq> G\<close> \<open>B \<noteq> G\<close> \<open>Bet A G B\<close> \<open>H \<noteq> G\<close> 
          bet__sams between_symmetry)
    ultimately
    show ?thesis 
      by (meson conga2_sams__sams)
  qed
  have "SAMS C H G B C H" 
  proof -
    have "C H G CongA C H G" 
      using \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> conga_refl by auto
    moreover
    have "SAMS C H G G H A" 
      using \<open>Bet A H C\<close> \<open>H \<noteq> A\<close> \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> 
        bet__sams between_symmetry by presburger
    ultimately
    show ?thesis
      by (meson \<open>G H A CongA B C H\<close> conga2_sams__sams)
  qed
  obtain I J K where "B C G C G B SumA I J K" 
    using ex_suma \<open>B \<noteq> G\<close> \<open>C \<noteq> B\<close> \<open>G \<noteq> C\<close> by presburger
  have "C \<noteq> H" 
    using \<open>H \<noteq> C\<close> by auto
  then obtain L M N where "H C G C G H SumA L M N"
    using ex_suma \<open>H \<noteq> G\<close> \<open>G \<noteq> C\<close> by presburger
  have "L \<noteq> M" 
    using \<open>H C G C G H SumA L M N\<close> suma_distincts by presburger
  have "N \<noteq> M"
    using \<open>H C G C G H SumA L M N\<close> suma_distincts by blast
  have "I \<noteq> J" 
    using \<open>B C G C G B SumA I J K\<close> suma_distincts by blast
  have "J \<noteq> K" 
    using \<open>B C G C G B SumA I J K\<close> suma_distincts by blast
  have "I \<noteq> K" 
    by (metis Par_strict_cases par_strict_not_col_4 
        \<open>B C G C G B SumA I J K\<close> \<open>G H ParStrict B C\<close> 
        col_trivial_3 ncol_suma__ncol)
  have "B \<noteq> C" 
    using \<open>C \<noteq> B\<close> by auto
  have "G \<noteq> B"
    using \<open>B \<noteq> G\<close> by auto 
  then obtain O0 P Q where "I J K G B C SumA O0 P Q"
    using ex_suma \<open>I \<noteq> J\<close> \<open>J \<noteq> K\<close> \<open>B \<noteq> C\<close> by blast
  have "G \<noteq> H" 
    using \<open>H \<noteq> G\<close> by auto
  have "M \<noteq> N" 
    using \<open>N \<noteq> M\<close> by auto
  then obtain R S T where "L M N G H C SumA R S T"
    using ex_suma \<open>L \<noteq> M\<close> \<open>M \<noteq> N\<close> \<open>G \<noteq> H\<close> \<open>H \<noteq> C\<close> by blast
  obtain U V W where "I J K L M N SumA U V W"
    using ex_suma \<open>I \<noteq> J\<close> \<open>J \<noteq> K\<close> \<open>L \<noteq> M\<close> \<open>M \<noteq> N\<close> by blast
  have "R \<noteq> S" 
    using \<open>L M N G H C SumA R S T\<close> suma_distincts by blast
  have "S \<noteq> T" 
    using \<open>L M N G H C SumA R S T\<close> suma_distincts by blast
  have "O0 \<noteq> P" 
    using \<open>I J K G B C SumA O0 P Q\<close> suma_distincts by blast
  have "Q \<noteq> P"
    using \<open>I J K G B C SumA O0 P Q\<close> suma_distincts by blast
  have "SAMS I J K L M N \<and> H G B B C H SumA U V W"
  proof -
    have "G C TS B H" 
      by (metis Col_cases \<open>Bet A G B\<close> \<open>C Out H A\<close> 
          \<open>G H ParStrict B C\<close> \<open>\<not> Col G H C\<close> bet_out l12_6 
          l9_19_R2 l9_9 out_col par_one_or_two_sides 
          two_sides_cases)
    have "SAMS H G B B C G" 
    proof -
      have "SAMS H G B B C H" 
        by (simp add: \<open>SAMS B G H H C B\<close> sams_comm)
      moreover
      have "H G B LeA H G B" 
        using \<open>G \<noteq> B\<close> \<open>H \<noteq> G\<close> lea_refl by force
      moreover
      have "G InAngle B C H" 
        by (meson Par_strict_cases \<open>G C TS B H\<close> 
            \<open>G H ParStrict B C\<close> invert_two_sides 
            l12_6 os_ts__inangle)
      hence "B C G LeA B C H" 
        by (simp add: inangle__lea)
      ultimately
      show ?thesis 
        by (meson sams_lea2__sams)
    qed
    have "C \<noteq> G" 
      using \<open>G \<noteq> C\<close> by auto
    then obtain X Y Z where "B C G H G B SumA X Y Z"
      using ex_suma \<open>B \<noteq> C\<close> \<open>H \<noteq> G\<close> \<open>G \<noteq> B\<close> by blast
    have "B G C C G H SumA H G B"
      by (meson \<open>G C TS B H\<close> suma_right_comm ts__suma_1)
    have "B G OS C H" 
      by (meson Col_perm \<open>A Out B G\<close> \<open>A Out C H\<close> 
          \<open>\<not> Col B C G\<close> one_side_reflexivity one_side_symmetry 
          os_out_os out_col)
    hence "SAMS B G C C G H" 
      by (simp add: \<open>G C TS B H\<close> os_ts__sams)
    have "SAMS I J K C G H" 
    proof -
      have "SAMS B C G C G B" 
        using \<open>C \<noteq> B\<close> \<open>G \<noteq> B\<close> \<open>G \<noteq> C\<close> sams123231 by auto
      moreover
      have "SAMS C G B C G H" 
        by (simp add: \<open>SAMS B G C C G H\<close> sams_left_comm)
      moreover
      have "C G B C G H SumA H G B"
        using \<open>B G C C G H SumA H G B\<close> suma_left_comm by blast
      moreover
      have "SAMS B C G H G B" 
        by (simp add: \<open>SAMS H G B B C G\<close> sams_sym)
      ultimately
      show ?thesis
        using \<open>B C G C G B SumA I J K\<close> sams_assoc by blast
    qed
    have "I J K C G H SumA X Y Z" 
    proof -
      have "SAMS B C G C G B" 
        using \<open>C \<noteq> B\<close> \<open>G \<noteq> B\<close> \<open>G \<noteq> C\<close> sams123231 by auto
      moreover
      have "SAMS C G B C G H" 
        by (simp add: \<open>SAMS B G C C G H\<close> sams_left_comm)
      moreover
      have "C G B C G H SumA H G B" 
        using \<open>B G C C G H SumA H G B\<close> suma_left_comm by blast
      ultimately
      show ?thesis 
        using \<open>B C G C G B SumA I J K\<close> \<open>B C G H G B SumA X Y Z\<close> 
          suma_assoc by blast
    qed
    have "SAMS B C G H C G" 
      by (meson pars__os3412 \<open>G C TS B H\<close> \<open>G H ParStrict B C\<close> 
          invert_two_sides os_ts__sams sams_right_comm)
    have "B C G H C G SumA H C B" 
      by (meson \<open>G C TS B H\<close> suma_middle_comm 
          suma_right_comm ts__suma)
    have "SAMS I J K L M N" 
    proof -
      have "SAMS X Y Z H C G" 
      proof -
        have "H G B B C G SumA X Y Z"
          by (simp add: \<open>B C G H G B SumA X Y Z\<close> suma_sym)
        moreover
        have "SAMS H G B H C B" 
          by (simp add: \<open>SAMS B G H H C B\<close> sams_left_comm)
        ultimately
        show ?thesis 
          by (meson \<open>SAMS H G B B C G\<close> \<open>SAMS B C G H C G\<close> 
              \<open>B C G H C G SumA H C B\<close> sams_assoc)
      qed
      have "SAMS C G H H C G" 
        by (simp add: \<open>G \<noteq> C\<close> \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> sams123231 sams_comm)
      moreover
      have "C G H H C G SumA L M N" 
        by (meson \<open>H C G C G H SumA L M N\<close> suma_sym)
      ultimately
      show ?thesis 
        using \<open>SAMS I J K C G H\<close> \<open>I J K C G H SumA X Y Z\<close> 
          \<open>SAMS X Y Z H C G\<close> sams_assoc_1 by blast
    qed
    moreover
    have "H G B B C H SumA U V W" 
    proof -
      have "X Y Z H C G SumA U V W" 
      proof -
        have "SAMS C G H H C G" 
          by (simp add: \<open>G \<noteq> C\<close> \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> 
              sams123231 sams_comm)
        moreover
        have "C G H H C G SumA L M N" 
          by (simp add: \<open>H C G C G H SumA L M N\<close> suma_sym)
        ultimately
        show ?thesis 
          using \<open>SAMS I J K C G H\<close> \<open>I J K C G H SumA X Y Z\<close> 
            \<open>I J K L M N SumA U V W\<close> suma_assoc by blast
      qed
      moreover
      have "H G B B C G SumA X Y Z" 
        by (simp add: \<open>B C G H G B SumA X Y Z\<close> suma_sym)
      moreover
      have "B C G H C G SumA B C H"
        by (simp add: \<open>B C G H C G SumA H C B\<close> suma_right_comm)
      ultimately
      show ?thesis 
        using \<open>SAMS H G B B C G\<close> \<open>SAMS B C G H C G\<close> 
          suma_assoc by blast
    qed
    ultimately
    show ?thesis by blast
  qed
  hence "SAMS I J K L M N" 
    by simp
  have "H G B B C H SumA U V W" 
    using \<open>SAMS I J K L M N \<and> H G B B C H SumA U V W\<close> by simp
  {
    fix A' B' C' D'
    assume "Saccheri A' B' C' D'"
    {
      assume "hypothesis_of_acute_saccheri_quadrilaterals"
      have "U V W LtA U V W" 
      proof -
        have "\<not> Col C G B" 
          using Col_cases \<open>\<not> Col B C G\<close> by blast
        hence "SAMS I J K G B C \<and> \<not> Bet O0 P Q" 
          using \<open>B C G C G B SumA I J K\<close> \<open>I J K G B C SumA O0 P Q\<close> 
            t22_14__sams_nbet 
            \<open>hypothesis_of_acute_saccheri_quadrilaterals\<close> by blast
        have "I J K LtA H G B" 
        proof -
          have "G B C LeA G B C"
            by (simp add: \<open>C \<noteq> B\<close> \<open>G \<noteq> B\<close> lea_refl)
          moreover
          have "O0 P Q LtA A G B" 
          proof -
            have "O0 P Q LeA A G B" 
              using \<open>A \<noteq> G\<close> \<open>Bet A G B\<close> \<open>G \<noteq> B\<close> \<open>O0 \<noteq> P\<close> 
                \<open>Q \<noteq> P\<close> l11_31_2 by force
            moreover
            {
              assume "O0 P Q CongA A G B"
              hence "Bet O0 P Q" 
                using \<open>Bet A G B\<close> bet_lea__bet conga__lea456123 by blast
              hence False 
                using \<open>SAMS I J K G B C \<and> \<not> Bet O0 P Q\<close> by blast
            }
            hence "\<not> O0 P Q CongA A G B" 
              by auto
            ultimately
            show ?thesis 
              by (simp add: LtA_def)
          qed
          moreover
          have "SAMS I J K G B C"
            by (simp add: \<open>SAMS I J K G B C \<and> \<not> Bet O0 P Q\<close>)
          moreover
          have "I J K G B C SumA O0 P Q" 
            by (simp add: \<open>I J K G B C SumA O0 P Q\<close>)
          moreover
          have "H G B G B C SumA A G B" 
          proof -
            have "B G H H G A SumA A G B" 
              by (metis \<open>A Out B G\<close> \<open>Bet A G B\<close> \<open>G \<noteq> B\<close> 
                  \<open>H \<noteq> G\<close> bet__suma between_symmetry l6_3_1 
                  suma_right_comm)
            moreover
            have "B G H CongA H G B" 
              using \<open>G \<noteq> B\<close> \<open>H \<noteq> G\<close> conga_pseudo_refl by auto
            moreover
            have "H G A CongA G B C" 
              by (simp add: \<open>A G H CongA G B C\<close> conga_left_comm)
            moreover
            have "A G B CongA A G B" 
              using \<open>A \<noteq> G\<close> \<open>G \<noteq> B\<close> conga_refl by auto
            ultimately
            show ?thesis 
              by (meson conga3_suma__suma)
          qed
          ultimately
          show ?thesis 
            by (meson sams_lea_lta789_suma2__lta123)
        qed
        moreover
        have "\<not> Col C G H" 
          by (meson Col_perm \<open>\<not> Col G H C\<close>)
        hence "SAMS L M N G H C \<and> \<not> Bet R S T"
          using \<open>H C G C G H SumA L M N\<close> \<open>L M N G H C SumA R S T\<close>
            t22_14__sams_nbet \<open>hypothesis_of_acute_saccheri_quadrilaterals\<close>
          by blast
        have "L M N LtA B C H" 
        proof -
          have "G H C LeA G H C" 
            using \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> lea_refl by auto
          moreover
          have "R S T LtA A H C" 
          proof -
            have "R S T LeA A H C" 
              using \<open>Bet A H C\<close> \<open>H \<noteq> A\<close> \<open>H \<noteq> C\<close> \<open>R \<noteq> S\<close> 
                \<open>S \<noteq> T\<close> l11_31_2 by auto
            moreover
            {
              assume "R S T CongA A H C" 
              have "Bet R S T" 
              proof -
                have "Bet A H C" 
                  by (simp add: \<open>Bet A H C\<close>)
                moreover
                have "A H C CongA R S T" 
                  using \<open>R S T CongA A H C\<close> conga_sym_equiv by blast
                moreover
                have "B C H G H C SumA A H C" 
                proof -
                  have "A H G G H C SumA A H C" 
                    using \<open>H \<noteq> A\<close> \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> 
                      bet__suma calculation(1) by force
                  moreover
                  have "A H G CongA B C H" 
                    by (simp add: \<open>G H A CongA B C H\<close> conga_left_comm)
                  moreover
                  have "G H C CongA G H C" 
                    using \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> conga_refl by auto
                  moreover
                  have "A H C CongA A H C" 
                    using \<open>H \<noteq> A\<close> \<open>H \<noteq> C\<close> conga_refl by auto
                  ultimately
                  show ?thesis 
                    by (meson conga3_suma__suma)
                qed
                ultimately
                show ?thesis 
                  using bet_conga__bet by blast
              qed
              hence False 
                using \<open>SAMS L M N G H C \<and> \<not> Bet R S T\<close> by auto
            }
            hence "\<not> R S T CongA A H C" 
              by auto
            ultimately
            show ?thesis 
              using LtA_def by blast
          qed
          moreover
          have "SAMS L M N G H C" 
            by (simp add: \<open>SAMS L M N G H C \<and> \<not> Bet R S T\<close>)
          moreover
          have "L M N G H C SumA R S T" 
            using \<open>L M N G H C SumA R S T\<close> by auto
          moreover
          have "B C H G H C SumA A H C"  
          proof -
            have "A H G G H C SumA A H C" 
              using \<open>H \<noteq> A\<close> \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> 
                bet__suma calculation(1) \<open>Bet A H C\<close> by auto
            moreover
            have "A H G CongA B C H" 
              by (simp add: \<open>G H A CongA B C H\<close> conga_left_comm)
            moreover
            have "G H C CongA G H C" 
              using \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> conga_refl by auto
            moreover
            have "A H C CongA A H C" 
              using \<open>H \<noteq> A\<close> \<open>H \<noteq> C\<close> conga_refl by auto
            ultimately
            show ?thesis 
              by (meson conga3_suma__suma)
          qed
          ultimately
          show ?thesis 
            by (meson sams_lea_lta789_suma2__lta123)
        qed
        moreover
        have "SAMS H G B B C H" 
          by (simp add: \<open>SAMS B G H H C B\<close> sams_comm)
        ultimately
        show ?thesis 
          by (meson  \<open>I J K L M N SumA U V W\<close> 
              \<open>H G B B C H SumA U V W\<close> lta__lea 
              sams_lea_lta456_suma2__lta)
      qed
      hence False 
        by (simp add: nlta)
      hence "Per A' B' C'" 
        by simp
    }
    moreover
    {
      assume "hypothesis_of_right_saccheri_quadrilaterals"
      hence "Per A' B' C'" 
        using \<open>Saccheri A' B' C' D'\<close> 
          hypothesis_of_right_saccheri_quadrilaterals_def
        by blast
    }
    moreover
    {
      assume "hypothesis_of_obtuse_saccheri_quadrilaterals"
      have "U V W LtA U V W" 
      proof -
        have "H G B LtA I J K" 
        proof -
          {
            assume  "I J K LeA H G B" 
            have False 
            proof -
              have "\<not> Col C G B" 
                using \<open>\<not> Col B C G\<close> col_permutation_2 by blast
              moreover
              have "B C G C G B SumA I J K" 
                by (simp add: \<open>B C G C G B SumA I J K\<close>)
              moreover
              have "SAMS I J K G B C" 
              proof -
                have "SAMS H G B G B C" 
                  by (simp add: \<open>SAMS B G H C B G\<close> sams_comm)
                moreover
                have "G B C LeA G B C"
                  using \<open>C \<noteq> B\<close> \<open>G \<noteq> B\<close> lea_refl by blast
                ultimately
                show ?thesis 
                  using \<open>I J K LeA H G B\<close> sams_lea2__sams by blast
              qed
              ultimately show ?thesis 
                using t22_14__nsams 
                  \<open>HypothesisObtuseSaccheriQuadrilaterals\<close> 
                by blast
            qed
          }
          hence "\<not> I J K LeA H G B" 
            by auto
          thus ?thesis
            using \<open>G \<noteq> B\<close> \<open>H \<noteq> G\<close> \<open>I \<noteq> J\<close> \<open>J \<noteq> K\<close> nlea__lta by blast
        qed
        moreover
        {
          assume "L M N LeA B C H"
          have False 
          proof -
            have "\<not> Col C G H"
              using \<open>\<not> Col G H C\<close> col_permutation_1 by blast
            moreover
            have "H C G C G H SumA L M N" 
              by (simp add: \<open>H C G C G H SumA L M N\<close>)
            moreover
            have "SAMS L M N G H C" 
            proof -
              have "SAMS B C H G H C" 
                by (meson \<open>SAMS C H G B C H\<close> sams_right_comm sams_sym)
              moreover
              have "G H C LeA G H C" 
                using \<open>H \<noteq> C\<close> \<open>H \<noteq> G\<close> lea_refl by auto
              ultimately
              show ?thesis 
                using  \<open>L M N LeA B C H\<close> sams_lea2__sams by blast
            qed
            ultimately
            show ?thesis
              using \<open>HypothesisObtuseSaccheriQuadrilaterals\<close> 
                t22_14__nsams by blast
          qed
        }
        hence "\<not> L M N LeA B C H" 
          by auto
        hence "B C H LtA L M N" 
          using \<open>C \<noteq> B\<close> \<open>H \<noteq> C\<close> \<open>L \<noteq> M\<close> \<open>N \<noteq> M\<close> nlta__lea by blast
        ultimately
        show ?thesis 
          by (meson \<open>SAMS I J K L M N\<close> \<open>H G B B C H SumA U V W\<close>
              \<open>I J K L M N SumA U V W\<close> lta__lea 
              sams_lea_lta456_suma2__lta)
      qed
      hence "Per A' B' C'" 
        by (simp add: nlta)
    }
    ultimately
    have "Per A' B' C'" 
      using saccheri_s_three_hypotheses by blast
  }
  thus ?thesis 
    using postulate_of_right_saccheri_quadrilaterals_def by blast
qed

lemma similar__rah:
  assumes "postulate_of_existence_of_similar_triangles"
  shows "postulate_of_right_saccheri_quadrilaterals"
proof -
  obtain A B C D E F where
    "\<not> Col A B C" and
    "\<not> Cong A B D E" and
    "A B C CongA D E F" and
    "B C A CongA E F D" and
    "C A B CongA F D E" 
    using assms postulate_of_existence_of_similar_triangles_def by blast
  have "A \<noteq> B" 
    using \<open>\<not> Col A B C\<close> col_trivial_1 by blast
  have "C \<noteq> B" 
    using \<open>\<not> Col A B C\<close> col_trivial_2 by force
  have "A \<noteq> C" 
    using \<open>\<not> Col A B C\<close> col_trivial_3 by blast
  have "D \<noteq> F" 
    using \<open>B C A CongA E F D\<close> conga_diff56 by blast
  have "E \<noteq> F" 
    using \<open>A B C CongA D E F\<close> conga_diff56 by blast
  have "D \<noteq> E" 
    using \<open>C A B CongA F D E\<close> conga_distinct by blast
  {
    assume "B C A LeA A B C"
    {
      assume "D E Le A B"
      hence "D E Lt A B" 
        using \<open>\<not> Cong A B D E\<close> le_anti_symmetry nle__lt by blast
      hence "postulate_of_right_saccheri_quadrilaterals" 
        using \<open>\<not> Col A B C\<close>  \<open>A B C CongA D E F\<close> 
          \<open>B C A CongA E F D\<close> \<open>C A B CongA F D E\<close> \<open>B C A LeA A B C\<close> 
          similar__rah_aux by blast
    }
    moreover
    {
      assume "A B Le D E"
      hence "A B Lt D E" 
        by (simp add: Lt_def \<open>\<not> Cong A B D E\<close>)
      moreover
      have "\<not> Col D E F" 
        using \<open>\<not> Col A B C\<close> \<open>A B C CongA D E F\<close> ncol_conga_ncol by blast
      moreover
      have "E F D LeA D E F" 
        using \<open>B C A LeA A B C\<close> \<open>B C A CongA E F D\<close> 
          \<open>A B C CongA D E F\<close> l11_30 by blast
      moreover
      have "D E F CongA A B C" 
        using \<open>A B C CongA D E F\<close> conga_sym by blast
      moreover
      have "E F D CongA B C A" 
        by (simp add: \<open>B C A CongA E F D\<close> conga_sym)
      moreover
      have "F D E CongA C A B" 
        by (simp add: \<open>C A B CongA F D E\<close> conga_sym)
      ultimately
      have "postulate_of_right_saccheri_quadrilaterals" 
        using similar__rah_aux by blast
    }
    ultimately
    have "postulate_of_right_saccheri_quadrilaterals"
      using local.le_cases by blast
  }
  moreover
  {
    assume "A B C LeA B C A"
    {
      assume "D F Le A C"
      {
        assume "Cong D F A C"
        have False 
        proof -
          have "\<not> Col A C B" 
            using Col_cases \<open>\<not> Col A B C\<close> by blast
          moreover
          have "A C B CongA D F E" 
            using \<open>B C A CongA E F D\<close> conga_comm by blast
          moreover
          have "Cong A C D F" 
            using Cong_cases \<open>Cong D F A C\<close> by blast
          ultimately
          show ?thesis 
            using \<open>C A B CongA F D E\<close> \<open>\<not> Cong A B D E\<close> 
              l11_50_1 by blast
        qed
      }
      hence "D F Lt A C" 
        using Lt_def \<open>D F Le A C\<close> by blast
      moreover
      have "\<not> Col A C B" 
        using Col_cases \<open>\<not> Col A B C\<close> by blast
      moreover
      have "A C B CongA D F E" 
        by (simp add: \<open>B C A CongA E F D\<close> conga_comm)
      moreover
      have "C B A CongA F E D" 
        by (simp add: \<open>A B C CongA D E F\<close> conga_comm)
      moreover
      have "B A C CongA E D F" 
        by (meson \<open>C A B CongA F D E\<close> conga_comm)
      moreover
      have "C B A LeA A C B" 
        by (simp add: \<open>A B C LeA B C A\<close> lea_comm)
      ultimately
      have "postulate_of_right_saccheri_quadrilaterals" 
        using similar__rah_aux by blast
    }
    moreover
    {
      assume "A C Le D F"
      have "\<not> Col D F E" 
      proof -
        have "\<not> Col A C B" 
          using Col_cases \<open>\<not> Col A B C\<close> by blast
        moreover
        have "A C B CongA D F E" 
          using \<open>B C A CongA E F D\<close> conga_comm by blast
        ultimately
        show ?thesis 
          using ncol_conga_ncol by blast
      qed
      moreover
      have "D F E CongA A C B" 
        by (meson \<open>B C A CongA E F D\<close> conga_comm conga_sym)
      moreover
      have "F E D CongA C B A" 
        by (meson \<open>A B C CongA D E F\<close> conga_comm conga_sym)
      moreover
      have "E D F CongA B A C" 
        by (meson \<open>C A B CongA F D E\<close> conga_comm conga_sym)
      moreover
      have "F E D LeA D F E" 
      proof -
        have "A B C LeA B C A" 
          by (simp add: \<open>A B C LeA B C A\<close>)
        moreover
        have "A B C CongA F E D" 
          by (simp add: \<open>A B C CongA D E F\<close> conga_right_comm)
        moreover
        have "B C A CongA D F E"
          by (simp add: \<open>B C A CongA E F D\<close> conga_right_comm)
        ultimately
        show ?thesis 
          using l11_30 by blast
      qed
      moreover
      {
        assume "Cong A C D F"
        have "\<not> Col A C B" 
          using Col_cases \<open>\<not> Col A B C\<close> by auto
        moreover
        have "A C B CongA D F E" 
          by (simp add: \<open>B C A CongA E F D\<close> conga_comm)
        ultimately
        have False 
          using \<open>Cong A C D F\<close> \<open>\<not> Cong A B D E\<close>  
            \<open>C A B CongA F D E\<close> l11_50_1 by blast
      }
      hence "A C Lt D F" 
        using Lt_def \<open>A C Le D F\<close> by blast
      ultimately
      have "postulate_of_right_saccheri_quadrilaterals" 
        using similar__rah_aux by blast
    }
    ultimately
    have  "postulate_of_right_saccheri_quadrilaterals"
      using local.le_cases by blast
  }
  ultimately
  show ?thesis 
    by (metis \<open>A \<noteq> B\<close> \<open>A \<noteq> C\<close> \<open>C \<noteq> B\<close> lea_total)
qed

lemma impossible_case_5:
  shows "\<forall> P Q R S U I.
            \<not> (BetS Q U R \<and> \<not> Col P Q S \<and> 
               \<not> Col P R U \<and> P R Par Q S \<and> 
               Bet S Q I \<and> Bet U I P)"
proof -
  {
    fix P Q R S U I
    assume 1: "BetS Q U R" and
      2: "\<not> Col P Q S" and
      3: "\<not> Col P R U" and
      4: "P R Par Q S" and
      5: "Bet S Q I" and
      6: "Bet U I P"
    have "Bet Q U R"
      by (simp add: "1" BetSEq)
    have "Q \<noteq> U" 
      using "1" BetSEq by blast
    have "Q \<noteq> R" 
      using "1" BetSEq by blast
    have "R \<noteq> U" 
      using "1" BetSEq by blast
    have "Q S Par P R" 
      by (simp add: "4" par_symmetry)
    have "Q S ParStrict P R" 
      using "2" "4" Par_def par_strict_symmetry by blast
    have "Q S OS R U" 
      by (metis "4" \<open>Bet Q U R\<close> \<open>Q S ParStrict P R\<close> 
          \<open>Q \<noteq> U\<close> bet2__out col_trivial_2 invert_one_side 
          l5_1 l9_19_R2 not_strict_par par_right_comm 
          par_strict_not_col_3)
    have False 
    proof -
      have "Q S TS P U" 
        by (metis "2" "5" "6" NCol_perm \<open>Q S OS R U\<close> 
            bet_col between_symmetry col124__nos l9_18)
      moreover
      have "Q S OS P U" 
        by (metis \<open>Bet Q U R\<close> \<open>Q S ParStrict P R\<close> 
            \<open>Q \<noteq> R\<close> \<open>Q \<noteq> U\<close> bet2__out l12_6 l5_1 
            out_out_one_side)
      ultimately
      show ?thesis 
        using l9_9_bis by blast
    qed
  }
  thus ?thesis by blast
qed

lemma impossible_case_6:
  shows "\<forall> P Q R S U I.
             \<not> (BetS Q U R \<and> \<not> Col P Q S \<and> 
                P S Par Q R \<and> Bet S Q I \<and> Bet I P U)"
proof -
  {
    fix P Q R S U I
    assume 1: "BetS Q U R" and
      2: "\<not> Col P Q S" and
      3: "P S Par Q R" and
      4: "Bet S Q I" and
      5: "Bet I P U"
    have "Bet Q U R"
      by (simp add: "1" BetSEq)
    have "Q \<noteq> U" 
      using "1" BetSEq by blast
    have "Q \<noteq> R" 
      using "1" BetSEq by blast
    have "R \<noteq> U" 
      using "1" BetSEq by blast
    have "Bet U P I" 
      using "5" Bet_cases by blast
    then obtain J where "Bet Q J U" and "Bet P J S" 
      using "4" inner_pasch by blast
    have "P S ParStrict Q U" 
    proof -
      have "P S ParStrict Q R" 
        using "2" "3" Col_cases col_trivial_3 par_not_col_strict by blast
      moreover
      have "Col Q R U" 
        by (simp add: \<open>Bet Q U R\<close> bet_col col_permutation_5)
      ultimately
      show ?thesis 
        by (meson \<open>Q \<noteq> U\<close> par_strict_col_par_strict)
    qed
    hence False 
      using "4" "5" impossible_case_1 par_strict_right_comm by blast
  }
  thus ?thesis 
    by blast
qed

lemma impossible_case_7:
  shows "\<forall> P Q R S U I.
            \<not> (BetS Q U R \<and> \<not> Col P Q S \<and> 
               \<not> Col P R U \<and> P R Par Q S \<and> 
               P S Par Q R \<and> Col P U I \<and> Bet Q I S)"
proof -
  {
    fix P Q R S U I
    assume 1:"BetS Q U R" and
      2: "\<not> Col P Q S" and
      3: "\<not> Col P R U" and
      4: "P R Par Q S" and
      5: "P S Par Q R" and
      6: "Col P U I" and
      7: "Bet Q I S"
    have "Bet Q U R"
      by (simp add: "1" BetSEq)
    have "Q \<noteq> U" 
      using "1" BetSEq by blast
    have "Q \<noteq> R" 
      using "1" BetSEq by blast
    have "R \<noteq> U" 
      using "1" BetSEq by blast
    have "Bet R U Q" 
      using Bet_cases \<open>Bet Q U R\<close> by auto
    have "P U OS Q S"  
    proof -
      have "P U TS Q R" 
        by (metis "3" \<open>Bet Q U R\<close> \<open>Q \<noteq> U\<close> bet_col 
            col_permutation_2 col_transitivity_1 
            col_trivial_2 l9_18_R2)
      moreover
      have "P U TS S R" 
      proof -
        have "P S OS R Q" 
        proof -
          have "P S Par R Q"
            by (simp add: "5" par_right_comm)
          moreover
          have "Col R Q Q" 
            by (simp add: col_trivial_2)
          moreover
          have "\<not> Col P S Q" 
            by (simp add: "2" not_col_permutation_5)
          ultimately
          show ?thesis 
            using par_not_col_strict par_strict_symmetry 
              pars__os3412 by blast
        qed
        hence "P S OS U R" 
          using \<open>Bet R U Q\<close> l9_17 one_side_symmetry by blast
        moreover
        have "P R OS U S" 
        proof -
          have "P R OS U Q" 
            by (metis "3" \<open>Bet R U Q\<close> bet_out col_trivial_2 l9_19_R2)
          moreover
          have "P R OS Q S" 
            by (meson "2" "4" col_trivial_3 
                not_col_permutation_1 par_not_col_strict 
                par_symmetry pars__os3412)
          ultimately
          show ?thesis
            using one_side_transitivity by blast
        qed
        ultimately
        show ?thesis 
          by (simp add: l9_31)
      qed
      ultimately
      show ?thesis 
        using l9_8_1 by blast
    qed
    hence "P U OS Q I" 
      using "7" l9_17 by blast
    hence False 
      using "6" one_side_not_col124 by auto
  }
  thus ?thesis by blast
qed

lemma impossible_case_8:
  shows "\<forall> P Q R S U I. 
             \<not> (BetS Q U R \<and> \<not> Col P Q S \<and> 
                P R Par Q S \<and> P S Par Q R \<and> 
                Col P U I \<and> Bet I S Q)"
proof -
  {
    fix P Q R S U I
    assume 1: "BetS Q U R" and
      2: "\<not> Col P Q S" and
      3: "P R Par Q S" and
      4: "P S Par Q R" and
      5: "Col P U I" and
      6: "Bet I S Q"
    have "Bet Q U R"
      by (simp add: "1" BetSEq)
    have "Q \<noteq> U" 
      using "1" BetSEq by blast
    have "Q \<noteq> R" 
      using "1" BetSEq by blast
    have "R \<noteq> U" 
      using "1" BetSEq by blast
    have "P S ParStrict Q U"
    proof - 
      have "P S ParStrict Q R" 
        using "2" "4" Col_cases col_trivial_3 
          par_not_col_strict by blast
      moreover
      have "Col Q R U" 
        using Col_perm \<open>Bet Q U R\<close> bet_col by blast
      ultimately
      show ?thesis 
        by (meson \<open>Q \<noteq> U\<close> par_strict_col_par_strict)
    qed
    have "Bet Q S I" 
      using "6" Bet_cases by auto
    {
      assume "Bet P U I" 
      hence False 
        by (meson Par_strict_cases \<open>Bet Q S I\<close> 
            \<open>P S ParStrict Q U\<close> between_symmetry impossible_case_1)
    }
    moreover
    {
      assume "Bet U I P" 
      then obtain J where "Bet U J Q" and "Bet P S J" 
        using \<open>Bet Q S I\<close> outer_pasch by blast
      hence False 
        by (metis \<open>Bet Q U R\<close> \<open>P S ParStrict Q U\<close> 
            bet_col bet_col1 between_symmetry l12_6 l5_3 
            l9_19 not_bet_and_out)
    }
    moreover
    {
      assume "Bet I P U" 
      then obtain J where "Bet Q J I \<and> Bet R P J" 
        using \<open>Bet Q U R\<close> outer_pasch by blast
      have "P R ParStrict Q I" 
        using "2" "3" Par_def \<open>Bet Q S I\<close> bet_col
          bet_neq32__neq col2__eq 
          par_strict_col2_par_strict by blast
      hence False 
        by (meson "3" \<open>Bet Q J I \<and> Bet R P J\<close> 
            \<open>Bet Q S I\<close> bet_col bet_col1 inter_uniqueness_not_par
            par_left_comm par_strict_comm par_strict_not_col_4)
    }
    ultimately
    have False 
      using "5" Col_def by blast
  }
  thus ?thesis 
    by blast
qed

lemma strong_parallel_postulate_implies_tarski_s_euclid_aux:
  assumes "strong_parallel_postulate" and
    "A \<noteq> B" and
    "A \<noteq> D" and
    "A \<noteq> T" and
    "B \<noteq> D" and
    "B \<noteq> T" and
    "D \<noteq> T" and
    "\<not> Col A B T" and
    "Bet A D T"
  shows "\<exists> B' B'' MB X. 
                (Bet A B X \<and> T X ParStrict B D \<and> 
                 BetS B MB T \<and> BetS B' MB B'' \<and>
                 Cong B MB T MB \<and> Cong B' MB B'' MB \<and> 
                 Col B B' D \<and> Bet B'' T X \<and> 
                 B \<noteq> B' \<and> B'' \<noteq> T)"
proof -
  obtain B' where "B Midpoint D B'" 
    using symmetric_point_construction by blast
  have "D \<noteq> B'" 
    using \<open>B Midpoint D B'\<close> assms(5) l7_3 by blast
  have "B \<noteq> B'" 
    using \<open>B Midpoint D B'\<close> \<open>D \<noteq> B'\<close> midpoint_not_midpoint by blast
  moreover
  have "Bet D B B'" 
    by (simp add: \<open>B Midpoint D B'\<close> midpoint_bet)
  have "Cong D B B B'" 
    using \<open>B Midpoint D B'\<close> midpoint_cong by auto
  have "Bet T D A" 
    using Bet_cases assms(9) by blast
  have "Bet B' B D" 
    using Bet_cases \<open>Bet D B B'\<close> by blast
  obtain MB where "MB Midpoint B T" 
    using midpoint_existence by blast
  hence "BetS B MB T" 
    by (metis BetS_def assms(6) midpoint_bet midpoint_distinct_1)
  moreover
  have "Cong B MB T MB" 
    using Midpoint_def \<open>MB Midpoint B T\<close> not_cong_1243 by blast
  moreover
  have "MB \<noteq> B" 
    using \<open>MB Midpoint B T\<close> assms(6) is_midpoint_id by blast
  have "MB \<noteq> T" 
    using BetSEq calculation(2) by blast
  obtain B'' where "MB Midpoint B' B''" 
    using symmetric_point_construction by blast
  have "MB \<noteq> B'" 
    using \<open>Bet D B B'\<close> \<open>MB Midpoint B T\<close> assms(8) assms(9) 
      bet_col between_exchange2 calculation(1) midpoint_bet 
      outer_transitivity_between by blast
  hence "BetS B' MB B''" 
    by (metis BetS_def \<open>MB Midpoint B' B''\<close> midpoint_bet 
        midpoint_not_midpoint)
  hence "B' \<noteq> B''" 
    using BetSEq by blast
  have "MB \<noteq> B''" 
    using BetSEq \<open>BetS B' MB B''\<close> by blast
  have "Cong B' MB B'' MB" 
    using Midpoint_def \<open>MB Midpoint B' B''\<close> 
      cong_right_commutativity by blast
  moreover
  have "\<not> Col B T B'" 
    by (metis Inter_def \<open>Bet D B B'\<close> assms(7) 
        assms(8) assms(9) bet_col calculation(1) 
        col_trivial_3 inter_trivial 
        l6_21 not_col_permutation_5)
  obtain B''' where "Bet T B''' B'" and "Bet A B B'''" 
    using \<open>Bet B' B D\<close> \<open>Bet T D A\<close> outer_pasch by blast
  have "B' \<noteq> B'''" 
    by (metis \<open>Bet A B B'''\<close> \<open>Bet B' B D\<close> \<open>\<not> Col B T B'\<close> 
        assms(3) assms(9) bet_col bet_out_1 
        col_permutation_1 colx out_col)
  have "B''' \<noteq> T" 
    using \<open>Bet A B B'''\<close> assms(8) bet_col by blast
  hence "BetS T B''' B'" 
    using BetS_def \<open>B' \<noteq> B'''\<close> \<open>Bet T B''' B'\<close> by presburger
  have "\<not> Col B B' B'''" 
    by (meson Col_perm \<open>B' \<noteq> B'''\<close> \<open>Bet T B''' B'\<close> 
        \<open>\<not> Col B T B'\<close> bet_col col2__eq)
  have "Coplanar B T B' B'''" 
    by (meson \<open>Bet T B''' B'\<close> bet_col col__coplanar ncoplanar_perm_11)
  hence "\<exists> X. (Col B'' T X \<and> Col B B''' X)"
    using assms(1) calculation(2) \<open>BetS B' MB B''\<close> 
      \<open>\<not> Col B B' B'''\<close> \<open>Cong B MB T MB\<close> \<open>Cong B' MB B'' MB\<close> 
      strong_parallel_postulate_def by blast
  then obtain X where "Col B'' T X" and "Col B B''' X" 
    by blast
  have "B B' Par T B''" 
    using l12_17 calculation(1) \<open>MB Midpoint B T\<close> 
      \<open>MB Midpoint B' B''\<close> by blast
  have "B \<noteq> B''" 
    using \<open>B B' Par T B''\<close> \<open>\<not> Col B T B'\<close> par_id_3
      par_right_comm by blast
  hence "B B'' Par T B'" 
    using l12_17 
    by (meson \<open>MB Midpoint B T\<close> \<open>MB Midpoint B' B''\<close> mid_par_cong2)
  {
    assume "Bet B'' T X"
    {
      assume "Bet B B''' X"
      hence "BetS B'' T X" 
        by (metis BetS_def \<open>B B' Par T B''\<close> \<open>Bet A B B'''\<close> 
            \<open>Bet B' B D\<close> \<open>Bet B'' T X\<close> \<open>\<not> Col B B' B'''\<close> assms(8) 
            bet_col bet_col1 not_col_permutation_4
            outer_transitivity_between par_distincts)
      have "BetS B B''' X" 
        by (metis BetS_def \<open>B B' Par T B''\<close> \<open>Bet B B''' X\<close> 
            \<open>Bet T B''' B'\<close> \<open>BetS B'' T X\<close> \<open>\<not> Col B B' B'''\<close> 
            \<open>\<not> Col B T B'\<close> bet_col col_permutation_5 not_col_distincts 
            not_strict_par outer_transitivity_between par_right_comm)
      have "B'' \<noteq> T"
        using BetSEq \<open>BetS B'' T X\<close> by blast
      have "T \<noteq> X" 
        using BetSEq \<open>BetS B'' T X\<close> by blast
      have ?thesis 
      proof -
        have "Bet A B X" 
          using BetSEq \<open>Bet A B B'''\<close> \<open>BetS B B''' X\<close> 
            outer_transitivity_between by blast
        moreover
        have "T X ParStrict B D"
        proof -
          have "T X ParStrict B B'" 
          proof -
            have "B B' ParStrict T B''" 
              by (metis Par_def \<open>B B' Par T B''\<close> \<open>\<not> Col B T B'\<close> 
                  not_col_distincts par_col2_par_bis par_id_3)
            moreover
            have "Col T B'' X" 
              using Col_cases \<open>Col B'' T X\<close> by blast
            ultimately
            show ?thesis 
              by (meson \<open>T \<noteq> X\<close> par_strict_col_par_strict 
                  par_strict_symmetry)
          qed
          moreover
          have "Col B B' D" 
            by (simp add: Col_def \<open>Bet D B B'\<close>)
          ultimately
          show ?thesis 
            using assms(5) par_strict_col_par_strict by blast
        qed
        moreover
        have "Col B B' D" 
          by (simp add: Col_def \<open>Bet D B B'\<close>)
        ultimately
        show ?thesis 
          using \<open>Bet B'' T X\<close> \<open>Cong B' MB B'' MB\<close> \<open>B \<noteq> B'\<close>
            \<open>B'' \<noteq> T\<close> \<open>BetS B MB T\<close> \<open>BetS B' MB B''\<close> 
            \<open>Cong B MB T MB\<close> by blast
      qed
    }
    moreover
    {
      assume "Bet B''' X B"
      have "\<not> Col B T B''" 
        by (meson \<open>B B' Par T B''\<close> \<open>\<not> Col B T B'\<close> assms(6) 
            col_trivial_2 par_col2_par_bis par_id_3)
      hence False
        using impossible_case_5 \<open>BetS T B''' B'\<close> \<open>\<not> Col B B' B'''\<close> 
          \<open>B B' Par T B''\<close> \<open>Bet B'' T X\<close> \<open>Bet B''' X B\<close> by blast
      hence ?thesis
        by blast
    }
    moreover
    {
      assume "Bet X B B'''"
      have "\<not> Col B T B''" 
        using \<open>B B' Par T B''\<close> \<open>\<not> Col B T B'\<close> assms(6) 
          col_trivial_2 par_col2_par_bis par_id_3 by blast
      hence ?thesis 
        using impossible_case_6 \<open>BetS T B''' B'\<close> \<open>B B'' Par T B'\<close> 
          \<open>Bet B'' T X\<close> \<open>Bet X B B'''\<close> by blast
    }
    ultimately
    have ?thesis 
      using Bet_perm \<open>Col B B''' X\<close> third_point by blast
  }
  moreover
  {
    assume "Bet T X B''"
    have "\<not> Col B T B''" 
      by (meson \<open>B B' Par T B''\<close> \<open>\<not> Col B T B'\<close> assms(6) 
          col_trivial_2 par_col2_par_bis par_id_3)
    hence ?thesis 
      using impossible_case_7 \<open>BetS T B''' B'\<close> \<open>\<not> Col B B' B'''\<close>
        \<open>B B' Par T B''\<close> \<open>B B'' Par T B'\<close> \<open>Col B B''' X\<close> 
        \<open>Bet T X B''\<close> by blast
  }
  moreover 
  {
    assume "Bet X B'' T"
    have "\<not> Col B T B''" 
      by (meson \<open>B B' Par T B''\<close> \<open>\<not> Col B T B'\<close> assms(6) 
          col_trivial_2 par_col2_par_bis par_id_3)
    hence ?thesis 
      using impossible_case_8 \<open>BetS T B''' B'\<close> \<open>B B' Par T B''\<close>
        \<open>B B'' Par T B'\<close> \<open>Bet X B'' T\<close> \<open>Col B B''' X\<close> by blast
  }
  ultimately
  show ?thesis 
    using Bet_perm \<open>Col B'' T X\<close> third_point by blast
qed

lemma strong_parallel_postulate_implies_tarski_s_euclid :
  assumes "strong_parallel_postulate"
  shows "tarski_s_parallel_postulate"
proof -
  {
    fix A' B' C' D' T'
    assume 1: "Bet A' D' T'" and
      2: "Bet B' D' C'" and
      3: "A' \<noteq> D'"
    {
      fix A B C D T
      assume H1: "A \<noteq> B" and
        H2: "A \<noteq> C" and
        H3: "A \<noteq> D" and 
        H4: "A \<noteq> T" and
        H5: "B \<noteq> C" and
        H6: "B \<noteq> D" and
        H7: "B \<noteq> T" and
        H8: "C \<noteq> D" and
        H9: "C \<noteq> T" and
        H10: "D \<noteq> T" and
        H11: "\<not> Col A B C" and
        H12: "Bet A D T" and
        H13: "Bet B D C" and
        H14: "\<not> Col B C T" 
      have "\<not> Col A B T"
        by (meson H11 H12 H13 H3 H6 between_trivial2 
            impossible_case_2)
      moreover
      have "\<not> Col A C T" 
        using H11 H12 H13 H3 H8 between_trivial 
          impossible_two_sides_not_col by blast
      ultimately
      have "\<exists> B' B'' MB X. 
                (Bet A B X \<and> T X ParStrict B D \<and> 
                 BetS B MB T \<and> BetS B' MB B'' \<and>
                 Cong B MB T MB \<and> Cong B' MB B'' MB \<and> 
                 Col B B' D \<and> Bet B'' T X \<and> 
                 B \<noteq> B' \<and> B'' \<noteq> T)"
        using assms strong_parallel_postulate_implies_tarski_s_euclid_aux 
          H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 by blast
      then obtain B' B'' MB X where "Bet A B X" and
        "T X ParStrict B D" and
        "BetS B MB T" and
        "BetS B' MB B''" and
        "Cong B MB T MB" and
        "Cong B' MB B'' MB" and
        "Col B B' D" and
        "Bet B'' T X" and
        "B \<noteq> B'" and
        "B'' \<noteq> T"
        by auto
      have "\<not> Col A B T"
        by (meson H11 H12 H13 H3 H6 between_trivial2 impossible_case_2)
      moreover
      have "\<not> Col A C T" 
        using H11 H12 H13 H3 H8 between_trivial 
          impossible_two_sides_not_col by blast
      ultimately
      have "\<exists> B' B'' MB X. 
                  (Bet A C X \<and> T X ParStrict C D \<and> 
                   BetS C MB T \<and> BetS B' MB B'' \<and>
                   Cong C MB T MB \<and> Cong B' MB B'' MB \<and> 
                   Col C B' D \<and> Bet B'' T X \<and> 
                   C \<noteq> B' \<and> B'' \<noteq> T)"
        using assms strong_parallel_postulate_implies_tarski_s_euclid_aux 
          H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 by blast
      then obtain B9' B9'' MB9 Y where "Bet A C Y" and
        "T Y ParStrict C D" and
        "BetS C MB9 T" and
        "BetS B9' MB9 B9''" and
        "Cong C MB9 T MB9" and
        "Cong B9' MB9 B9'' MB9" and
        "Col C B9' D" and
        "Bet B9'' T Y" and
        "C \<noteq> B9'" and
        "B9'' \<noteq> T"
        by auto
      have "Bet X T Y" 
      proof (cases "Col X T Y")
        case True
        have "\<not> Col A B C" 
          by (simp add: H11) 
        {
          assume "Col A X Y"
          hence False 
            by (metis H1 H11 \<open>Bet A B X\<close> \<open>Bet A C Y\<close> 
                bet_col bet_neq12__neq 
                col_trivial_3 
                not_par_inter_uniqueness par_id)
        }
        hence "\<not> Col A X Y" 
          by blast
        have "Bet Y C A" 
          using \<open>Bet A C Y\<close> between_symmetry by blast
        then obtain U where "Bet Y U B" and "Bet A D U" 
          using H13 outer_pasch by blast
        have "Bet X B A" 
          by (meson Bet_perm \<open>Bet A B X\<close>)
        then obtain V where "Bet X V Y" and "Bet A U V" 
          using \<open>Bet Y U B\<close> outer_pasch by blast
        have "T = V" 
        proof -
          have "\<not>  Col X Y A" 
            using Col_cases \<open>\<not> Col A X Y\<close> by blast
          moreover
          have "A \<noteq> D" 
            by (simp add: H3)
          moreover
          have "Col X Y T" 
            using True not_col_permutation_5 by blast
          moreover
          have "Col X Y V" 
            using \<open>Bet X V Y\<close> bet_col col_permutation_5 by blast
          moreover
          have "Col A D T" 
            by (simp add: Col_def H12)
          moreover
          have "Col A D V" 
            by (meson \<open>Bet A D U\<close> \<open>Bet A U V\<close> bet_col 
                between_exchange4)
          ultimately
          show ?thesis 
            using l6_21 by blast
        qed
        thus ?thesis 
          by (simp add: \<open>Bet X V Y\<close>)
      next
        case False 
        hence "\<not> Col X T Y"
          by simp
        have "\<not> Col T B'' Y" 
          by (meson False \<open>B'' \<noteq> T\<close> \<open>Bet B'' T X\<close> bet_col 
              col_transitivity_2 not_col_permutation_4)
        have "T Y ParStrict C B" 
          by (metis H13 H5 \<open>T Y ParStrict C D\<close> bet_col 
              between_symmetry col_trivial_3 par_strict_col2_par_strict)
        have "T X ParStrict B C"
          by (meson H13 H5 \<open>T X ParStrict B D\<close> bet_col 
              par_strict_col_par_strict)
        have "X \<noteq> T"
          using False col_trivial_1 by auto
        have "Y \<noteq> T" 
          using False col_trivial_2 by blast
        have "X \<noteq> Y" 
          using False col_trivial_3 by force
        have "Coplanar T B B'' Y" 
        proof -
          have "Coplanar B Y T X" 
          proof -
            have "\<not> Col C B T" 
              using Col_cases H14 by blast
            moreover
            have "Coplanar C B T X" 
              using \<open>T X ParStrict B C\<close> ncoplanar_perm_17 
                pars__coplanar by blast
            moreover
            have "Coplanar C B T Y" 
              using \<open>T Y ParStrict C B\<close> coplanar_perm_16 
                pars__coplanar by blast
            ultimately
            show ?thesis 
              by (meson coplanar_trans_1 ncoplanar_perm_3)
          qed
          moreover
          have "Col T X B''" 
            by (simp add: Col_def \<open>Bet B'' T X\<close>)
          ultimately
          show ?thesis
            using \<open>X \<noteq> T\<close> col_cop__cop coplanar_perm_13 by blast
        qed
        have "\<exists> I. Col B' B I \<and> Col T Y I" 
        proof -
          have "BetS T MB B" 
            by (metis BetS_def \<open>BetS B MB T\<close> between_symmetry)
          moreover
          have "BetS B'' MB B'" 
            by (metis BetS_def Bet_cases \<open>BetS B' MB B''\<close>)
          moreover
          have "Cong T MB B MB"
            by (meson \<open>Cong B MB T MB\<close> not_cong_3412)
          moreover
          have "Cong B'' MB B' MB" 
            by (simp add: \<open>Cong B' MB B'' MB\<close> cong_symmetry)
          ultimately
          show ?thesis 
            using assms \<open>\<not> Col T B'' Y\<close> \<open>Coplanar T B B'' Y\<close> 
              strong_parallel_postulate_def by blast
        qed
        then obtain I where "Col B' B I" and "Col T Y I" 
          by auto
        thus ?thesis 
          by (metis H13 H6 \<open>B \<noteq> B'\<close> \<open>Col B B' D\<close> 
              \<open>T Y ParStrict C D\<close> bet_col col3 col_trivial_2 
              not_col_permutation_4 not_strict_par 
              par_strict_not_col_4 par_strict_par)
      qed
      hence "\<exists> x y. (Bet A B x \<and> Bet A C y \<and> Bet x T y)" 
        using \<open>Bet A B X\<close> \<open>Bet A C Y\<close> by auto
    }
    hence "\<exists> X Y. Bet A' B' X \<and> Bet A' C' Y \<and> Bet X T' Y" 
      using 1 2 3 tarski_s_euclid_remove_degenerated_cases by blast
  }
  thus ?thesis 
    using tarski_s_parallel_postulate_def by blast
qed

(** This is the converse of triangle_mid_par. *)


lemma midpoint_converse_postulate_implies_playfair:
  assumes "midpoint_converse_postulate"
  shows "playfair_s_postulate"
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume "A1 A2 Par B1 B2" and
      "Col P B1 B2" and
      "A1 A2 Par C1 C2" and
      "Col P C1 C2"
    {
      assume "A1 A2 ParStrict B1 B2"
      {
        assume "A1 A2 ParStrict C1 C2"
        hence "P \<noteq> A1" 
          using Col_cases \<open>Col P C1 C2\<close> par_strict_not_col_3 by blast
        obtain X where "P Midpoint A1 X" 
          using symmetric_point_construction by blast
        {
          fix B1' B2'
          assume "Col P B1' B2'" and
            "A1 A2 ParStrict B1' B2'" and
            "P \<noteq> B1'"
          moreover
          {
            fix B1'' B2''
            assume "Col P B1'' B2''" and
              "A1 A2 ParStrict B1'' B2''" and
              "P \<noteq> B1''"
            have "A1 \<noteq> X" 
              using \<open>P Midpoint A1 X\<close> \<open>P \<noteq> A1\<close> l7_3 by blast
            have "P \<noteq> X" 
              using \<open>A1 \<noteq> X\<close> \<open>P Midpoint A1 X\<close> midpoint_distinct_1 by blast
            have "A1 \<noteq> A2" 
              using \<open>A1 A2 ParStrict B1' B2'\<close> par_strict_neq1 by blast
            have "A1 \<noteq> B1''" 
              using \<open>A1 A2 ParStrict B1'' B2''\<close> 
                not_par_strict_id by fastforce
            have "A1 \<noteq> B2''"
              using \<open>A1 A2 ParStrict B1'' B2''\<close> \<open>Col P B1'' B2''\<close> 
                \<open>P \<noteq> B1''\<close> col_transitivity_2 par_strict_not_col_3 by blast
            have "A2 \<noteq> B1''" 
              using \<open>A1 A2 ParStrict B1'' B2''\<close> not_par_strict_id 
                par_strict_left_comm by blast
            have "A2 \<noteq> B2''" 
              using Par_strict_cases \<open>A1 A2 ParStrict B1'' B2''\<close> 
                not_par_strict_id by blast
            have "B2'' \<noteq> B1''" 
              using \<open>A1 A2 ParStrict B1'' B2''\<close> col_trivial_1 
                par_strict_not_col_3 by blast
            have "\<exists> B3. Col B1'' P B3 \<and> (BetS X B3 A2 \<or> BetS A1 B3 A2)"
            proof -
              have "Coplanar X A1 A2 B1''" 
              proof -
                have "Coplanar A2 B1'' A1 P" 
                  using NCol_perm \<open>A1 A2 ParStrict B1'' B2''\<close> 
                    \<open>B2'' \<noteq> B1''\<close> \<open>Col P B1'' B2''\<close> col_cop__cop 
                    ncoplanar_perm_12 pars__coplanar by blast
                moreover
                have "Col A1 P X" 
                  using Midpoint_def \<open>P Midpoint A1 X\<close> 
                    bet_col by blast
                ultimately
                show ?thesis 
                  using \<open>P \<noteq> A1\<close> col_cop__cop 
                    ncoplanar_perm_17 by blast
              qed
              moreover
              have "\<not> Col A2 P B1''" 
                by (metis Par_strict_cases \<open>A1 A2 ParStrict B1'' B2''\<close>
                    \<open>Col P B1'' B2''\<close> \<open>P \<noteq> B1''\<close> col3 col_trivial_2 
                    not_col_permutation_2 par_strict_not_col_3)
              moreover
              {
                assume "Col X A1 B1''"
                have "Bet A1 P X" 
                  using \<open>P Midpoint A1 X\<close> midpoint_bet by blast
                hence "Col A1 P X" 
                  using Col_def by blast
                hence "Col A1 P B1''" 
                  using \<open>Col X A1 B1''\<close> 
                  by (metis \<open>A1 \<noteq> X\<close> col_permutation_2 
                      col_trivial_2 l6_21)
                moreover
                have "\<not> Col A1 P B1''" 
                  by (metis \<open>A1 A2 ParStrict B1'' B2''\<close>
                      \<open>Col P B1'' B2''\<close> \<open>P \<noteq> B1''\<close> col3 col_trivial_2 
                      col_trivial_3 par_strict_not_col_3)
                ultimately
                have "False" 
                  by simp
              }
              hence "\<not> Col X A1 B1''" 
                by blast
              moreover
              have "BetS X P A1" 
                using BetS_def Midpoint_def \<open>P Midpoint A1 X\<close>
                  \<open>P \<noteq> A1\<close> \<open>P \<noteq> X\<close> between_symmetry by presburger
              ultimately
              show ?thesis 
                using hilbert_s_version_of_pasch by blast
            qed
            then obtain B3 where "Col B1'' P B3" and "BetS X B3 A2 \<or> BetS A1 B3 A2" 
              by blast
            have "Col B1'' B2'' B3" 
              by (meson \<open>Col B1'' P B3\<close> \<open>Col P B1'' B2''\<close>
                  \<open>P \<noteq> B1''\<close> col_transitivity_2 not_col_permutation_4)
            moreover
            {
              assume "BetS A1 B3 A2"
              have "Col B3 A1 A2" 
                using BetSEq Col_def \<open>BetS A1 B3 A2\<close> 
                  col_permutation_3 by blast
              moreover
              have "Col B3 B1'' B2''" 
                using Col_perm \<open>Col B1'' B2'' B3\<close> by blast
              ultimately
              have "False"
                using \<open>A1 A2 ParStrict B1'' B2''\<close> par_not_col by blast
            }
            hence "BetS A2 B3 X" 
              by (metis BetS_def \<open>BetS X B3 A2 \<or> BetS A1 B3 A2\<close> 
                  between_symmetry)
            moreover
            have "A1 A2 ParStrict P B3" 
            proof -
              have "Col B1'' B2'' P" 
                by (simp add: \<open>Col P B1'' B2''\<close> col_permutation_1)
              moreover
              {
                assume "P = B3"
                have "Bet A2 B3 X" 
                  using BetSEq \<open>BetS A2 B3 X\<close> by blast
                hence "Col X P A2" 
                  using BetSEq \<open>BetS A1 B3 A2 \<Longrightarrow> False\<close> 
                    \<open>BetS X B3 A2 \<or> BetS A1 B3 A2\<close> \<open>P = B3\<close> bet_col by blast
                have "A2 \<noteq> B3" 
                  using BetSEq \<open>BetS A2 B3 X\<close> by auto
                have "B3 \<noteq> X"    
                  using BetSEq \<open>BetS A2 B3 X\<close> by auto
                hence "Col P A1 A2" 
                proof -
                  have "Col X P A2" 
                    by (simp add: \<open>Col X P A2\<close>)
                  moreover
                  have "Bet A1 P X" 
                    by (simp add: \<open>P Midpoint A1 X\<close> midpoint_bet)
                  hence "Col X P A1" 
                    using Bet_cases Col_def by blast
                  ultimately
                  show ?thesis 
                    using \<open>A1 A2 ParStrict B1'' B2''\<close> 
                    by (metis \<open>P \<noteq> X\<close> col_transitivity_2)
                qed
                hence "False" 
                  using \<open>Col P B1'' B2''\<close> \<open>A1 A2 ParStrict B1'' B2''\<close> 
                    par_not_col by blast
              }
              hence "P \<noteq> B3" 
                by blast
              ultimately
              show ?thesis 
                using \<open>Col B1'' B2'' B3\<close> \<open>A1 A2 ParStrict B1'' B2''\<close> 
                  par_strict_col2_par_strict by blast
            qed
            ultimately
            have "\<exists> B3. Col B1'' B2'' B3 \<and> BetS A2 B3 X \<and> A1 A2 ParStrict P B3" 
              by blast
          }
          ultimately
          have "\<exists> B3. Col B1' B2' B3 \<and> BetS A2 B3 X \<and> A1 A2 ParStrict P B3" 
            using \<open>A1 A2 ParStrict B1' B2'\<close> \<open>Col P B1' B2'\<close> by blast
        }
        moreover
        {
          fix B1' B2'
          assume "Col P B1' B2'" and
            "A1 A2 ParStrict B1' B2'" and
            "P = B1'" 
          have "P \<noteq> B2'" 
            using  \<open>P = B1'\<close> \<open>A1 A2 ParStrict B1' B2'\<close> 
              par_strict_distinct by presburger
          moreover
          have "Col P B2' B1'" 
            using \<open>P = B1'\<close> col_trivial_3 by blast
          moreover
          have "A1 A2 ParStrict B2' B1'" 
            by (simp add: \<open>A1 A2 ParStrict B1' B2'\<close> 
                par_strict_right_comm)
          ultimately
          have "\<exists> B3. Col B1' B2' B3 \<and> BetS A2 B3 X \<and> A1 A2 ParStrict P B3" 
            using Col_perm 
              \<open>\<And>B2' B1'. \<lbrakk>Col P B1' B2'; A1 A2 ParStrict B1' B2'; P \<noteq> B1'\<rbrakk> 
                \<Longrightarrow> \<exists>B3. Col B1' B2' B3 \<and> BetS A2 B3 X \<and> A1 A2 ParStrict P B3\<close> 
            by blast
        }
        ultimately
        have H1: "\<forall> B1' B2'. (Col P B1' B2' \<and> A1 A2 ParStrict B1' B2') 
                       \<longrightarrow> 
          (\<exists> B3. Col B1' B2' B3 \<and> BetS A2 B3 X \<and> A1 A2 ParStrict P B3)"       
          by blast
        then obtain B3 where "Col B1 B2 B3" and "BetS A2 B3 X" and 
          "A1 A2 ParStrict P B3" 
          using \<open>A1 A2 ParStrict B1 B2\<close> \<open>Col P B1 B2\<close> by blast
        obtain C3 where "Col C1 C2 C3" and "BetS A2 C3 X" and 
          "A1 A2 ParStrict P C3"
          using \<open>A1 A2 ParStrict C1 C2\<close> \<open>Col P C1 C2\<close> H1 by blast
        have "Col A2 X B3" 
          by (meson BetSEq Bet_cases Col_def \<open>BetS A2 B3 X\<close>)
        have "Col A2 X C3" 
          by (meson BetSEq Bet_cases Col_def \<open>BetS A2 C3 X\<close>)
        have "\<not> Col A1 A2 X" 
          by (metis BetSEq \<open>A1 A2 ParStrict P C3\<close> 
              \<open>BetS A2 B3 X\<close> \<open>Col A2 X C3\<close> col124__nos col3
              col_trivial_3 l12_6 not_col_permutation_2)
        have "B3 = C3" 
        proof -
          have "B3 Midpoint A2 X" 
          proof -
            have "\<not> Col A2 A1 X" 
              by (meson Col_cases \<open>\<not> Col A1 A2 X\<close>)
            moreover
            have "A2 A1 Par B3 P" 
              by (simp add: \<open>A1 A2 ParStrict P B3\<close> 
                  par_strict_comm par_strict_par)
            ultimately
            show ?thesis 
              using assms \<open>P Midpoint A1 X\<close> \<open>Col A2 X B3\<close> 
                midpoint_converse_postulate_def by blast
          qed
          moreover
          have "C3 Midpoint A2 X" 
          proof -
            have "\<not> Col A2 A1 X" 
              by (meson Col_cases \<open>\<not> Col A1 A2 X\<close>)
            moreover
            have "A2 A1 Par C3 P" 
              by (simp add: \<open>A1 A2 ParStrict P C3\<close> 
                  par_strict_comm par_strict_par)
            ultimately
            show ?thesis 
              using assms \<open>P Midpoint A1 X\<close> \<open>Col A2 X C3\<close>
                midpoint_converse_postulate_def by blast
          qed
          ultimately
          show ?thesis
            by (meson Mid_cases l7_17_bis)
        qed
        have "Col C1 B1 B2" 
        proof -
          have "Col B1 B2 C3" 
            using \<open>B3 = C3\<close> \<open>Col B1 B2 B3\<close> by auto
          moreover
          have "Col C1 C2 C3" 
            using \<open>Col C1 C2 C3\<close> by auto
          moreover
          have "Col P C1 C2" 
            by (simp add: \<open>Col P C1 C2\<close>)
          moreover
          have "Col P B1 B2" 
            by (simp add: \<open>Col P B1 B2\<close>)
          ultimately
          show ?thesis 
            by (metis \<open>A1 A2 ParStrict C1 C2\<close> \<open>A1 A2 ParStrict P C3\<close>
                l6_21 not_col_permutation_2 par_strict_neq2)
        qed
        moreover
        have "Col C2 B1 B2" 
        proof -
          have "Col B1 B2 C3" 
            using \<open>B3 = C3\<close> \<open>Col B1 B2 B3\<close> by auto
          moreover
          have "Col C1 C2 C3" 
            using \<open>Col C1 C2 C3\<close> by auto
          moreover
          have "Col P C1 C2" 
            by (simp add: \<open>Col P C1 C2\<close>)
          moreover
          have "Col P B1 B2" 
            by (simp add: \<open>Col P B1 B2\<close>)
          ultimately
          show ?thesis 
            by (metis \<open>A1 A2 ParStrict P C3\<close> \<open>Col C1 B1 B2\<close> 
                l6_21 not_col_permutation_2 not_col_permutation_3 
                par_strict_neq2)
        qed
        ultimately
        have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
          by simp
      }
      moreover
      have "(A1 \<noteq> A2 \<and> B1 \<noteq> B2 \<and> Col A1 B1 B2 \<and> Col A2 B1 B2) 
              \<longrightarrow> 
            Col C1 B1 B2 \<and> Col C2 B1 B2" 
        using NCol_perm \<open>A1 A2 ParStrict B1 B2\<close> 
          par_strict_not_col_3 by blast
      {
        assume "A1 \<noteq> A2"  and
          "B1 \<noteq> B2" and
          "Col A1 B1 B2" and
          "Col A2 B1 B2"
        hence "Col C1 B1 B2 \<and> Col C2 B1 B2" 
          using NCol_perm \<open>A1 A2 ParStrict B1 B2\<close> 
            par_strict_not_col_3 by blast
      }
      ultimately
      have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
        by (meson \<open>A1 A2 Par C1 C2\<close> \<open>A1 A2 ParStrict B1 B2\<close> 
            \<open>Col P B1 B2\<close> \<open>Col P C1 C2\<close> col_permutation_1 
            par_not_col par_not_col_strict)
    }
    moreover
    {
      assume "A1 \<noteq> A2" and "B1 \<noteq> B2" and
        "Col A1 B1 B2" and "Col A2 B1 B2"
      hence "\<not> A1 A2 ParStrict B1 B2" 
        using par_strict_not_col_2 by blast
      have "Col B1 B2 C1 \<and> Col B1 B2 C2" 
      proof -
        have "B1 B2 Par C1 C2" 
          using NCol_perm \<open>A1 A2 Par C1 C2\<close> \<open>B1 \<noteq> B2\<close> 
            \<open>Col A1 B1 B2\<close> \<open>Col A2 B1 B2\<close> 
            par_col2_par_bis par_symmetry by blast
        moreover have "Col B1 B2 A1" 
          using \<open>Col A1 B1 B2\<close> 
            not_col_permutation_2 by blast
        moreover have "Col C1 C2 A1" 
          using Par_cases \<open>Col P B1 B2\<close> 
            \<open>Col P C1 C2\<close> calculation(1) calculation(2) 
            col_not_col_not_par col_permutation_1 by blast
        ultimately show ?thesis 
          using inter_uniqueness_not_par not_strict_par2 by blast
      qed
      hence "Col C1 B1 B2 \<and> Col C2 B1 B2" 
        using col_permutation_2 by blast
    }
    ultimately
    have "Col C1 B1 B2 \<and> Col C2 B1 B2"
      using Par_def \<open>A1 A2 Par B1 B2\<close> by presburger
  }
  thus ?thesis 
    using playfair_s_postulate_def by blast
qed

lemma playfair_implies_par_trans:
  assumes "playfair_s_postulate" 
  shows "postulate_of_transitivity_of_parallelism"
proof -
  {
    fix A1 A2 B1 B2 C1 C2
    assume "A1 A2 Par B1 B2" and 
      "B1 B2 Par C1 C2"
    have "B1 \<noteq> B2" 
      using \<open>A1 A2 Par B1 B2\<close> par_distincts by blast
    have "A1 \<noteq> A2" 
      using \<open>A1 A2 Par B1 B2\<close> par_distincts by auto
    have "C1 \<noteq> C2" 
      using \<open>B1 B2 Par C1 C2\<close> par_distincts by blast
    have "A1 A2 Par C1 C2" 
    proof (cases "Coplanar A1 A2 C1 B1")
      case True
      show ?thesis 
      proof (cases "Col A1 A2 C1")
        case True
        hence "Col A1 A2 C2" 
        proof -
          have "B1 B2 Par A1 A2" 
            by (simp add: \<open>A1 A2 Par B1 B2\<close> par_symmetry)
          moreover have "Col C1 A1 A2" 
            using True not_col_permutation_1 by blast
          moreover have "Col C1 C1 C2" 
            by (simp add: col_trivial_1)
          ultimately show ?thesis
            using playfair_s_postulate_def \<open>B1 B2 Par C1 C2\<close> 
              assms col_permutation_1 by blast
        qed
        have "B1 B2 Par C1 C2" 
          by (simp add: \<open>B1 B2 Par C1 C2\<close>)
        moreover
        have "Col C1 C1 C2" 
          by (simp add: col_trivial_1)
        moreover
        have "Col A2 C1 C2" 
          using Par_cases True \<open>A1 A2 Par B1 B2\<close> assms 
            calculation(1) calculation(2) not_col_permutation_3 
            playfair_s_postulate_def by blast
        moreover
        have "B1 B2 Par A1 A2" 
          using Par_cases \<open>A1 A2 Par B1 B2\<close> by blast
        moreover
        have "Col A1 A2 C1" 
          using True by simp
        hence "Col A1 C1 C2" 
          using calculation(3) 
          by (metis \<open>Col A1 A2 C2\<close> col_transitivity_1)
        ultimately
        show ?thesis 
          using Par_def \<open>A1 \<noteq> A2\<close> \<open>C1 \<noteq> C2\<close> by blast
      next
        case False
        hence "\<not> Col A1 A2 C1" 
          by simp
        have "A1 A2 ParStrict C1 C2" 
        proof -
          have "Coplanar A1 A2 C1 C2" 
          proof -
            have "C1 C2 Par B1 B2" 
              by (simp add: \<open>B1 B2 Par C1 C2\<close> par_symmetry)
            moreover
            {
              assume "A1 A2 Par B1 B2" and "C1 C2 ParStrict B1 B2"
              hence "Coplanar C1 C2 B1 B2" 
                using ParStrict_def by blast
              have "Coplanar A1 A2 C1 C2" 
              proof -
                {
                  assume "A1 A2 ParStrict B1 B2"
                  hence "Coplanar A1 A2 B1 B2" 
                    using pars__coplanar by auto
                  moreover
                  have "Coplanar C1 C2 B1 B2" 
                    by (simp add: \<open>Coplanar C1 C2 B1 B2\<close>)
                  moreover
                  have "Coplanar A1 A2 C1 B1"
                    by (simp add: True)
                  ultimately
                  have "Coplanar A1 A2 C1 B2" 
                  proof -
                    have "\<not> Col A2 B1 B2" 
                      using \<open>A1 A2 ParStrict B1 B2\<close> par_strict_not_col_2 by auto
                    moreover have "Coplanar A2 B1 B2 A1" 
                      using \<open>Coplanar A1 A2 B1 B2\<close> ncoplanar_perm_18 by blast
                    moreover have "Coplanar A2 B1 B2 A2" 
                      using ncop_distincts by blast
                    moreover have "Coplanar A2 B1 B2 C1" 
                      by (meson True \<open>A1 A2 ParStrict B1 B2\<close> 
                          calculation(2) coplanar_perm_1 l9_30 
                          ncop_distincts par_strict_not_col_3
                          par_strict_symmetry)
                    moreover have "Coplanar A2 B1 B2 B2" 
                      using ncop_distincts by blast
                    ultimately show ?thesis 
                      using coplanar_pseudo_trans by blast
                  qed
                  have "Coplanar A1 A2 C1 C1" 
                    using ncop_distincts by blast
                  have "Coplanar B1 B2 C1 A1" 
                    by (meson False True \<open>Coplanar A1 A2 C1 B2\<close> 
                        coplanar_pseudo_trans ncop_distincts)
                  moreover
                  have "Coplanar B1 B2 C1 A2" 
                    by (meson False True \<open>Coplanar A1 A2 C1 B2\<close> 
                        coplanar_trans_1 ncoplanar_perm_22)
                  moreover
                  have "Coplanar B1 B2 C1 C1" 
                    using ncop_distincts by blast
                  moreover
                  have "Coplanar B1 B2 C1 C2" 
                    by (simp add: \<open>Coplanar C1 C2 B1 B2\<close>
                        coplanar_perm_16)
                  ultimately
                  have "Coplanar A1 A2 C1 C2" 
                    by (meson NCol_perm \<open>C1 C2 ParStrict B1 B2\<close>
                        coplanar_pseudo_trans not_col_distincts 
                        par_not_col)
                }
                moreover
                {
                  assume "A1 \<noteq> A2 \<and> B1 \<noteq> B2 \<and> Col A1 B1 B2 \<and> Col A2 B1 B2"
                  hence "Coplanar A1 A2 C1 C2" 
                    by (meson \<open>C1 C2 Par B1 B2\<close> col2_cop__cop 
                        col_permutation_1 ncoplanar_perm_16 par__coplanar) 
                }
                ultimately
                show ?thesis 
                  by (metis Par_cases \<open>A1 A2 Par B1 B2\<close> \<open>A1 \<noteq> A2\<close> 
                      \<open>B1 \<noteq> B2\<close> col_permutation_2 not_col_distincts 
                      par_not_col_strict par_strict_symmetry)
              qed
            }
            moreover
            {
              assume "A1 A2 Par B1 B2" and "C1 \<noteq> C2" and
                "B1 \<noteq> B2" and "Col C1 B1 B2" and "Col A2 B1 B2"
              hence "Coplanar A1 A2 C1 C2" 
                by (meson col_permutation_1 col_trivial_3
                    ncop__ncols par_not_col par_not_col_strict)
            }
            ultimately
            show ?thesis 
              by (metis \<open>A1 A2 Par B1 B2\<close> \<open>B1 \<noteq> B2\<close> 
                  all_one_side_par_strict col2_cop__cop not_strict_par1 
                  not_strict_par2 par__coplanar par_not_col_strict
                  par_symmetry)
          qed
          moreover
          {
            assume "\<exists> X. Col X A1 A2 \<and> Col X C1 C2"
            then obtain X where "Col X A1 A2" and "Col X C1 C2" 
              by blast
            have "B1 B2 Par A1 A2" 
              using \<open>A1 A2 Par B1 B2\<close> par_symmetry by blast
            hence False
              using  \<open>B1 B2 Par C1 C2\<close> \<open>Col X A1 A2\<close> 
                \<open>Col X C1 C2\<close> False assms col_permutation_1 
                playfair_s_postulate_def by blast
          }
          ultimately
          show ?thesis 
            using ParStrict_def by blast
        qed
        thus ?thesis 
          by (simp add: Par_def)
      qed
    next
      case False
      hence "A1 A2 ParStrict B1 B2" 
        using \<open>A1 A2 Par B1 B2\<close> col_trivial_3 
          ncop__ncols par_not_col_strict by blast
      have "B1 B2 ParStrict C1 C2" 
      proof -
        have "Col C1 C2 C1" 
          by (simp add: col_trivial_3)
        moreover
        have "\<not> Col B1 B2 C1" 
          by (meson False \<open>A1 A2 Par B1 B2\<close> \<open>B1 \<noteq> B2\<close> 
              col_cop__cop ncoplanar_perm_1 par__coplanar)
        ultimately
        show ?thesis 
          using \<open>B1 B2 Par C1 C2\<close> par_not_col_strict by blast
      qed
      have "\<exists> C'. Coplanar A1 A2 C1 C' \<and> Coplanar B1 B2 C1 C' \<and> C1 \<noteq> C'" 
      proof -
        have "Coplanar A1 A2 C1 C1" 
          using ncop_distincts by blast
        moreover
        have "A1 A2 C1 OSP B1 B2" 
          by (meson False \<open>A1 A2 ParStrict B1 B2\<close> 
              col_trivial_2 cop2_os__osp 
              ncop_distincts par_strict_one_side)
        ultimately
        show ?thesis 
          by (simp add: cop_osp__ex_cop2)
      qed
      then obtain C' where "Coplanar A1 A2 C1 C'" and "Coplanar B1 B2 C1 C'" 
        and "C1 \<noteq> C'" 
        by auto
      { 
        fix X
        assume "Coplanar A1 A2 B1 X" and 
          "Col X C1 C'" 
        have "Col X A1 A2" 
        proof -
          have "\<not> Coplanar A1 A2 C1 B1" 
            by (simp add: False)
          moreover
          have "\<not> Col A1 A2 B1" 
            using calculation ncop__ncols by auto
          moreover
          have "Coplanar A1 A2 B1 B1" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A1 A2 C1 X" 
            using \<open>C1 \<noteq> C'\<close> \<open>Col X C1 C'\<close> \<open>Coplanar A1 A2 C1 C'\<close> 
              col_cop__cop col_permutation_1 by blast
          moreover
          have "Coplanar A1 A2 C1 A1" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A1 A2 C1 A2" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A1 A2 B1 X" 
            by (simp add: \<open>Coplanar A1 A2 B1 X\<close>)
          moreover
          have "Coplanar A1 A2 B1 A1" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A1 A2 B1 A2" 
            using ncop_distincts by blast
          ultimately
          show ?thesis 
            using l9_30 by blast
        qed
        moreover
        have "Col X B1 B2" 
        proof -
          have "\<not> Coplanar A1 A2 B1 C1" 
            using False ncoplanar_perm_1 by blast
          moreover
          have "\<not> Col B1 B2 C1" 
            using \<open>B1 B2 ParStrict C1 C2\<close> col123__nos l12_6 by blast
          moreover
          have "Coplanar B1 B2 C1 C1" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A1 A2 B1 X" 
            by (simp add: \<open>Coplanar A1 A2 B1 X\<close>)
          moreover
          have "Coplanar A1 A2 B1 B1" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A1 A2 B1 B2" 
            using ParStrict_def \<open>A1 A2 ParStrict B1 B2\<close> by blast
          moreover
          have "Coplanar B1 B2 C1 X" 
            by (meson \<open>C1 \<noteq> C'\<close> \<open>Col X C1 C'\<close> 
                \<open>Coplanar B1 B2 C1 C'\<close> col_cop__cop 
                not_col_permutation_1)
          moreover
          have "Coplanar B1 B2 C1 B1" 
            using ncop_distincts by blast
          moreover
          have "Coplanar B1 B2 C1 B2" 
            using ncop_distincts by blast
          ultimately
          show ?thesis 
            using l9_30 by blast
        qed
        ultimately
        have False 
          using \<open>A1 A2 ParStrict B1 B2\<close> par_not_col by blast
      }
      have "A1 A2 ParStrict C1 C2" 
      proof -
        {
          assume "\<exists> X. Col X A1 A2 \<and> Col X C1 C'" 
          then obtain X where "Col X A1 A2" and "Col X C1 C'" 
            by auto
          have "Coplanar A1 A2 B1 X" 
            using \<open>Col X A1 A2\<close> col_permutation_1 ncop__ncols by blast
          hence False 
            using \<open>Col X C1 C'\<close> 
              \<open>\<And>X. \<lbrakk>Coplanar A1 A2 B1 X; Col X C1 C'\<rbrakk> \<Longrightarrow> False\<close> 
            by blast
        }
        hence "A1 A2 ParStrict C1 C'" 
          using ParStrict_def \<open>Coplanar A1 A2 C1 C'\<close> by blast
        moreover
        have "B1 B2 ParStrict C1 C'"
        proof -
          have "B1 B2 Par C1 C'" 
            using  \<open>A1 A2 Par B1 B2\<close> \<open>B1 \<noteq> B2\<close> \<open>Coplanar B1 B2 C1 C'\<close> 
              assms calculation col_cop__cop col_permutation_1 
              coplanar_perm_1 par__coplanar par_strict_par 
              playfair_s_postulate_def
            by (meson False cop_npars__inter_exists)
          thus ?thesis 
            using Par_def 
              \<open>\<And>X. \<lbrakk>Coplanar A1 A2 B1 X; Col X C1 C'\<rbrakk> \<Longrightarrow> False\<close> 
              ncop_distincts by blast
        qed
        hence "Col C1 C' C2" 
          using \<open>B1 B2 Par C1 C2\<close> assms col_permutation_1 
            col_trivial_1 par_strict_par 
            playfair_s_postulate_def by blast
        ultimately
        show ?thesis 
          using \<open>C1 \<noteq> C2\<close> par_strict_col_par_strict by blast
      qed
      thus ?thesis 
        by (simp add: Par_def)
    qed
  }
  thus ?thesis 
    using postulate_of_transitivity_of_parallelism_def by blast
qed

lemma par_trans_implies_playfair:
  assumes "postulate_of_transitivity_of_parallelism"
  shows "playfair_s_postulate" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume "A1 A2 Par B1 B2" and
      "Col P B1 B2" and
      "A1 A2 Par C1 C2" and
      "Col P C1 C2"
    have "C1 C2 Par B1 B2" 
      using \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Par C1 C2\<close> assms 
        par_symmetry postulate_of_transitivity_of_parallelism_def by blast
    hence "Col C1 B1 B2 \<and> Col C2 B1 B2" 
      using Par_def \<open>Col P B1 B2\<close> \<open>Col P C1 C2\<close> 
        par_not_col by blast
  }
  thus ?thesis 
    using playfair_s_postulate_def by blast
qed

lemma par_perp_perp_implies_par_perp_2_par:
  assumes "perpendicular_transversal_postulate"
  shows "postulate_of_parallelism_of_perpendicular_transversals"
proof -
  {
    fix A1 A2 B1 B2 C1 C2 D1 D2
    assume "A1 A2 Par B1 B2" and "A1 A2 Perp C1 C2" and "B1 B2 Perp D1 D2" and
      "Coplanar A1 A2 C1 D1" and "Coplanar A1 A2 C1 D2" and
      "Coplanar A1 A2 C2 D1" and "Coplanar A1 A2 C2 D2" 
    have "C1 C2 Perp A1 A2" 
      using Perp_perm \<open>A1 A2 Perp C1 C2\<close> by blast
    moreover
    have "D1 D2 Perp A1 A2" 
    proof -
      have "B1 B2 Par A1 A2" 
        using Par_cases \<open>A1 A2 Par B1 B2\<close> by blast
      moreover
      have "B1 B2 Perp D1 D2" 
        by (simp add: \<open>B1 B2 Perp D1 D2\<close>)
      moreover

      have "Coplanar A1 A2 D1 D2" 
      proof -
        {
          assume "\<not> Col A1 A2 C1"
          hence "Coplanar A1 A2 D1 D2" 
            by (meson \<open>Coplanar A1 A2 C1 D1\<close> \<open>Coplanar A1 A2 C1 D2\<close>
                coplanar_pseudo_trans ncop_distincts)
        }
        moreover
        {
          assume "\<not> Col A1 A2 C2"
          hence "Coplanar A1 A2 D1 D2" 
            by (meson \<open>Coplanar A1 A2 C2 D1\<close> \<open>Coplanar A1 A2 C2 D2\<close>
                coplanar_perm_12 coplanar_trans_1 not_col_permutation_2)
        }
        ultimately
        show ?thesis
          using perp_not_col2 \<open>A1 A2 Perp C1 C2\<close> by blast
      qed
      ultimately
      show ?thesis 
        using Perp_perm assms perpendicular_transversal_postulate_def by blast
    qed
    ultimately
    have "C1 C2 Par D1 D2"
      using l12_9 \<open>Coplanar A1 A2 C1 D1\<close> \<open>Coplanar A1 A2 C1 D2\<close> 
        \<open>Coplanar A1 A2 C2 D1\<close> \<open>Coplanar A1 A2 C2 D2\<close> 
      by blast
  }
  thus ?thesis 
    using postulate_of_parallelism_of_perpendicular_transversals_def by blast
qed

lemma par_perp_2_par_implies_par_perp_perp:
  assumes "postulate_of_parallelism_of_perpendicular_transversals" 
  shows "perpendicular_transversal_postulate"
proof -
  {
    fix A B C D P Q
    assume "A B Par C D" and
      "A B Perp P Q" and
      "Coplanar C D P Q"
    {
      assume "A B ParStrict C D"
      obtain X where "X PerpAt A B P Q" 
        using Perp_def \<open>A B Perp P Q\<close> by blast
      have "C D Perp P Q" 
      proof (cases "Col C D X")
        case True
        have "Col X A B" 
          using \<open>X PerpAt A B P Q\<close> Col_cases perp_in_col by blast
        moreover
        have "Col X C D"  
          using Col_cases True by blast
        ultimately
        have "\<exists> X0. Col X0 A B \<and> Col X0 C D" 
          by blast
        hence False 
          using \<open>A B ParStrict C D\<close> par_not_col by blast
        thus ?thesis 
          by blast
      next
        case False
        then obtain Y where "Col C D Y" and "C D Perp X Y" 
          using False l8_18_existence by blast
        have "A \<noteq> B" 
          using \<open>A B Par C D\<close> par_distinct by auto
        have "P \<noteq> Q" 
          using \<open>A B Perp P Q\<close> perp_not_eq_2 by auto
        have "P Q Par X Y" 
        proof -
          have "Coplanar C D X A" 
          proof -
            have "Coplanar C D A B" 
              using Par_cases \<open>A B Par C D\<close> par__coplanar by blast
            moreover
            have "Col X A B" 
              using \<open>X PerpAt A B P Q\<close> Col_cases perp_in_col by blast
            hence "Col A B X" 
              using Col_cases by blast
            moreover
            have "Col A B A" 
              by (simp add: col_trivial_3)
            ultimately
            show ?thesis 
              using \<open>A \<noteq> B\<close> col2_cop__cop by blast
          qed
          have "Coplanar C D X B" 
          proof -
            have "Coplanar C D A B" 
              using Par_perm \<open>A B Par C D\<close> par__coplanar by blast
            moreover
            have "Col X A B" 
              using \<open>X PerpAt A B P Q\<close> Col_cases perp_in_col by blast
            hence "Col A B X" 
              using Col_cases by blast
            moreover
            have "Col A B B" 
              by (simp add: col_trivial_2)
            ultimately
            show ?thesis 
              using \<open>A \<noteq> B\<close> col2_cop__cop by blast
          qed
          have "Coplanar C D X P" 
            by (meson \<open>Coplanar C D P Q\<close> \<open>P \<noteq> Q\<close> 
                \<open>X PerpAt A B P Q\<close> col_cop__cop ncoplanar_perm_6 
                ncoplanar_perm_7 perp_in_col)
          have "Coplanar C D X Q" 
          proof -
            have "Coplanar C D P Q" 
              by (simp add: \<open>Coplanar C D P Q\<close>)
            moreover
            have "Col P Q X" 
              using \<open>X PerpAt A B P Q\<close> perp_in_col by blast
            moreover
            have "Col P Q Q" 
              using col_trivial_2 by auto
            ultimately
            show ?thesis 
              using \<open>P \<noteq> Q\<close> col2_cop__cop by blast
          qed
          have "Coplanar C D X Y" 
            by (simp add: \<open>C D Perp X Y\<close> perp__coplanar)
          have "Coplanar A B P X" 
            using \<open>X PerpAt A B P Q\<close> col__coplanar 
              coplanar_perm_1 perp_in_col by blast
          moreover
          have "Coplanar A B P Y" 
            by (meson False \<open>Coplanar C D X A\<close> \<open>Coplanar C D X B\<close>
                \<open>Coplanar C D X P\<close> \<open>Coplanar C D X Y\<close> 
                coplanar_pseudo_trans)
          moreover
          have "Coplanar A B Q X" 
            by (meson \<open>X PerpAt A B P Q\<close> ncop__ncol 
                ncoplanar_perm_1 perp_in_col)
          moreover
          have "Coplanar A B Q Y" 
            by (meson  \<open>Coplanar C D X A\<close> \<open>Coplanar C D X B\<close> 
                \<open>Coplanar C D X Q\<close> \<open>Coplanar C D X Y\<close> False
                coplanar_pseudo_trans)
          ultimately
          show ?thesis
            using  \<open>C D Perp X Y\<close> \<open>A B Perp P Q\<close> \<open>A B Par C D\<close> 
              postulate_of_parallelism_of_perpendicular_transversals_def
              assms by blast
        qed
        {
          assume "P \<noteq> Q \<and> X \<noteq> Y \<and> Col P X Y \<and> Col Q X Y"
          hence "C D Perp P Q" 
            by (meson \<open>C D Perp X Y\<close> not_col_permutation_2 perp_col2_bis)
        }
        moreover
        {
          assume "P Q ParStrict X Y"
          have "Col X P Q" 
            using \<open>X PerpAt A B P Q\<close> Col_cases perp_in_col by blast
          moreover
          have "Col X X Y" 
            by (simp add: col_trivial_1)
          ultimately
          have False 
            using \<open>P Q ParStrict X Y\<close> par_not_col by blast
          hence "C D Perp P Q" 
            by blast
        }
        ultimately
        show ?thesis 
          using \<open>P Q Par X Y\<close> Par_def by blast
      qed
    }
    hence "C D Perp P Q" 
      by (metis Par_perm Par_strict_perm par_neq2 
          par_not_col_strict perp_col2 perp_inter_perp_in 
          \<open>A B Par C D\<close> \<open>A B Perp P Q\<close> not_strict_par2)
  }
  thus ?thesis 
    using perpendicular_transversal_postulate_def by blast
qed

lemma par_perp_perp_implies_playfair:
  assumes "perpendicular_transversal_postulate"
  shows "playfair_s_postulate" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume "A1 A2 Par B1 B2" and 
      "Col P B1 B2" and
      "A1 A2 Par C1 C2" and
      "Col P C1 C2"
    {
      assume H1: "\<forall> C1 C2. P \<noteq> C1 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2
                    \<longrightarrow> 
                       (Col C1 B1 B2 \<and> Col C2 B1 B2)"
      fix C1 C2
      assume "A1 A2 Par C1 C2" and "Col P C1 C2"
      have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
      proof (cases "P = C1")
        case True
        hence "P = C1" 
          by simp
        show ?thesis 
        proof (cases "P = C2")
          case True
          thus ?thesis
            using \<open>Col P B1 B2\<close> \<open>P = C1\<close> by auto
        next
          case False
          hence "P \<noteq> C2"
            by simp
          show ?thesis 
            by (metis \<open>A1 A2 Par C1 C2\<close> \<open>Col P B1 B2\<close> 
                \<open>Col P C1 C2\<close> H1 not_col_permutation_5 
                par_right_comm)
        qed
      next
        case False
        hence "P \<noteq> C1"
          by simp
        thus ?thesis 
          using \<open>A1 A2 Par C1 C2\<close> \<open>Col P C1 C2\<close> H1 by blast
      qed
    }
    {
      fix C1 C2
      assume "P \<noteq> C1" and 
        "A1 A2 Par C1 C2" and 
        "Col P C1 C2"
      have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
      proof (cases "Col A1 A2 P")
        case True
        have "Col C1 B1 B2" 
          using \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Par C1 C2\<close> 
            \<open>Col P B1 B2\<close> \<open>Col P C1 C2\<close> col3 not_strict_par1 
            not_strict_par2 par_neq1
          by (meson True not_col_permutation_2)
        moreover
        have "Col C2 B1 B2"
          using \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Par C1 C2\<close> 
            \<open>Col P B1 B2\<close> \<open>Col P C1 C2\<close> 
            col3 not_strict_par1 not_strict_par2 par_neq1
          by (metis \<open>P \<noteq> C1\<close> calculation 
              col_permutation_1 col_trivial_2)
        ultimately show ?thesis
          by blast
      next
        case False
        hence "\<not> Col A1 A2 P"
          by simp
        then obtain I where "Col A1 A2 I" and "A1 A2 Perp P I" 
          using l8_18_existence by blast
        have "Coplanar B1 B2 P I" 
          using \<open>Col P B1 B2\<close> col_permutation_1 ncop__ncol by blast
        have "Coplanar C1 C2 P I" 
          by (meson \<open>Col P C1 C2\<close> col_permutation_1 ncop__ncol)
        moreover
        have "A1 A2 Par B1 B2" 
          using \<open>A1 A2 Par B1 B2\<close> by auto
        ultimately
        have "B1 B2 Perp P I" 
          using perpendicular_transversal_postulate_def assms 
            \<open>A1 A2 Perp P I\<close> \<open>Coplanar B1 B2 P I\<close> by blast
        have "C1 C2 Perp P I"
          using perpendicular_transversal_postulate_def assms 
            \<open>A1 A2 Perp P I\<close> \<open>Coplanar C1 C2 P I\<close> \<open>A1 A2 Par C1 C2\<close> by blast
        have "Coplanar A1 A2 P B1" 
          using \<open>A1 A2 Par B1 B2\<close> \<open>Col P B1 B2\<close> col2_cop__cop 
            col_permutation_1 col_trivial_3 par__coplanar 
            par_neq2 by blast
        have "Coplanar A1 A2 P B2" 
          using \<open>A1 A2 Par B1 B2\<close> \<open>Col P B1 B2\<close> col2_cop__cop 
            col_permutation_1 col_trivial_3 par__coplanar 
            par_neq2 by blast
        have "Coplanar A1 A2 P C1" 
          using \<open>A1 A2 Par C1 C2\<close> \<open>Col P C1 C2\<close> col_trivial_2
            ncop_distincts par__coplanar 
            par_col2_par_bis by blast
        have "Coplanar A1 A2 P I" 
          by (simp add: \<open>A1 A2 Perp P I\<close> perp__coplanar)
        have "P C1 Perp P I" 
        proof -
          have "C1 \<noteq> P" 
            using \<open>P \<noteq> C1\<close> by blast
          moreover
          have "C1 C2 Perp P I" 
            by (simp add: \<open>C1 C2 Perp P I\<close>)
          moreover
          have "Col C1 C2 P" 
            using Col_cases \<open>Col P C1 C2\<close> by blast
          ultimately
          show ?thesis 
            by (meson perp_col perp_left_comm)
        qed
        have "Col P C1 B1" 
        proof (cases "P = B1")
          case True
          thus ?thesis
            by (simp add: col_trivial_3)
        next
          case False
          show ?thesis 
          proof -
            have "Coplanar P I C1 B1" 
            proof -
              have "Coplanar A1 A2 P P" 
                using ncop_distincts by blast
              thus ?thesis 
                by (meson \<open>\<not> Col A1 A2 P\<close> \<open>Coplanar A1 A2 P B1\<close> 
                    \<open>Coplanar A1 A2 P C1\<close> \<open>Coplanar A1 A2 P I\<close> 
                    coplanar_pseudo_trans)
            qed
            moreover
            have "P B1 Perp P I" 
              by (metis False Perp_perm \<open>B1 B2 Perp P I\<close> \<open>Col P B1 B2\<close> 
                  col_permutation_1 perp_col)
            ultimately
            show ?thesis 
              using \<open>P C1 Perp P I\<close> cop_perp2__col by blast
          qed
        qed
        moreover
        have "Col P C1 B2" 
        proof (cases "P = B2")
          case True
          thus ?thesis
            by (simp add: col_trivial_3)
        next
          case False
          show ?thesis 
          proof -
            have "Coplanar P I C1 B2" 
            proof -
              have "Coplanar A1 A2 P P" 
                using ncop_distincts by blast
              thus ?thesis 
                by (meson \<open>\<not> Col A1 A2 P\<close> \<open>Coplanar A1 A2 P B2\<close>
                    \<open>Coplanar A1 A2 P C1\<close> \<open>Coplanar A1 A2 P I\<close> 
                    coplanar_pseudo_trans)
            qed
            moreover
            have "P B2 Perp P I" 
              by (metis False Perp_perm \<open>B1 B2 Perp P I\<close> 
                  \<open>Col P B1 B2\<close> col_permutation_1 perp_col)
            ultimately
            show ?thesis 
              using \<open>P C1 Perp P I\<close> cop_perp2__col by blast
          qed
        qed
        ultimately
        show ?thesis 
          by (metis \<open>Col P C1 C2\<close> \<open>P \<noteq> C1\<close> col_transitivity_2)
      qed
    }
    hence "Col C1 B1 B2 \<and> Col C2 B1 B2" 
      using \<open>A1 A2 Par C1 C2\<close> \<open>Col P C1 C2\<close>
        \<open>\<And>C2a C1a. \<lbrakk>\<forall>C1 C2. P \<noteq> C1 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 
\<longrightarrow> Col C1 B1 B2 \<and> Col C2 B1 B2; A1 A2 Par C1a C2a; Col P C1a C2a\<rbrakk> 
\<Longrightarrow> Col C1a B1 B2 \<and> Col C2a B1 B2\<close> 
      by blast
  }
  thus ?thesis 
    using playfair_s_postulate_def by blast
qed

lemma playfair__universal_posidonius_postulate:
  assumes "playfair_s_postulate" 
  shows "universal_posidonius_postulate" 
proof -
  {
    fix A1 A2 A3 A4 B1 B2 B3 B4
    assume "A1 A2 Par B1 B2" and
      "Col A1 A2 A3" and "Col B1 B2 B3" and
      "A1 A2 Perp A3 B3" and
      "Col A1 A2 A4" and "Col B1 B2 B4" and "A1 A2 Perp A4 B4"
    {
      assume "A1 A2 ParStrict B1 B2" 
      hence "\<not> Col A1 A2 B1" 
        by (meson par_strict_not_col_1)
      then obtain A1' where "Col A1 A2 A1'" and "A1 A2 Perp B1 A1'" 
        using l8_18_existence by blast
      {
        fix A3 B3
        assume "Col A1 A2 A3" and
          "Col B1 B2 B3" and
          "A1 A2 Perp A3 B3"
        have "B3 \<noteq> A3" 
          using \<open>A1 A2 Perp A3 B3\<close> \<open>Col A1 A2 A3\<close> perp_not_col2 by blast
        then obtain B3' where "Bet A3 B3 B3' \<or> Bet A3 B3' B3" and "Cong A3 B3' A1' B1" 
          using segment_construction_2 by blast
        {
          assume "A1' = A3" 
          have "Col A1' B1 B3" 
          proof -
            have "Coplanar A1 A2 B1 B3" 
              using \<open>A1 A2 Par B1 B2\<close> \<open>Col B1 B2 B3\<close> col2_cop__cop 
                col_trivial_3 par__coplanar par_neq2 by blast
            moreover
            have "A1' B1 Perp A1 A2" 
              using Perp_perm \<open>A1 A2 Perp B1 A1'\<close> by blast
            moreover
            have "A1' B3 Perp A1 A2" 
              using Perp_perm \<open>A1' = A3\<close> \<open>A1 A2 Perp A3 B3\<close> by blast
            ultimately
            show ?thesis 
              using cop_perp2__col by blast
          qed
          have "B1 = B3" 
          proof -
            have "\<not> Col B1 B2 A1'" 
            proof (cases "A1 = A1'")
              case True
              thus ?thesis 
                using \<open>A1 A2 Par B1 B2\<close> \<open>Col A1 A2 A1'\<close> 
                  \<open>\<not> Col A1 A2 B1\<close> not_strict_par1 by blast
            next
              case False
              thus ?thesis 
                using \<open>A1' = A3\<close> \<open>A1 A2 Par B1 B2\<close> \<open>Col A1 A2 A3\<close> \<open>\<not> Col A1 A2 B1\<close> 
                  not_strict_par by blast
            qed
            moreover
            have "Col B1 B2 B1" 
              by (simp add: col_trivial_3)
            moreover
            have "Col A1' B1 B1" 
              using col_trivial_2 by auto
            ultimately
            show ?thesis 
              by (meson  \<open>Col B1 B2 B3\<close> \<open>Col A1' B1 B3\<close> 
                  col_permutation_4 l6_16_1)
          qed
          hence "Cong A3 B3 A1' B1" 
            using cong_reflexivity by (simp add: \<open>A1' = A3\<close>)
        }
        moreover
        {
          assume "A1' \<noteq> A3" 
          have "Saccheri A1' B1 B3' A3" 
          proof -
            have "A1' B1 Perp A3 A1'" 
              using \<open>A1'\<noteq> A3\<close> Perp_cases \<open>A1 A2 Perp B1 A1'\<close>
                \<open>Col A1 A2 A1'\<close> \<open>Col A1 A2 A3\<close> perp_col2_bis by blast
            hence "Per B1 A1' A3" 
              using perp_per_1 by blast
            moreover
            have "A3 A1' Perp B3' A3" 
            proof -
              have "A1 A2 Perp A3 B3" 
                by (simp add: \<open>A1 A2 Perp A3 B3\<close>)
              hence "A3 B3 Perp A3 A1'" 
                using perp_col0 \<open>A1'\<noteq> A3\<close>  \<open>Col A1 A2 A3\<close>
                  \<open>Col A1 A2 A1'\<close> by presburger
              moreover
              have "Col A3 B3 B3'" 
                using Col_def \<open>Bet A3 B3 B3' \<or> Bet A3 B3' B3\<close> 
                  col_permutation_4 by blast
              moreover
              have "Col A3 B3 A3" 
                by (simp add: col_trivial_3)
              ultimately
              show ?thesis 
                by (metis \<open>A1' B1 Perp A3 A1'\<close> \<open>Cong A3 B3' A1' B1\<close>
                    cong_diff_3 perp_col0 perp_not_eq_1)
            qed
            hence "Per A1' A3 B3'" 
              using perp_per_1 by blast
            moreover
            have "Cong A1' B1 B3' A3" 
              using \<open>Cong A3 B3' A1' B1\<close> not_cong_4312 by blast
            moreover
            have "A1' A3 OS B1 B3'" 
            proof -
              have "A1' A3 OS B1 B3" 
              proof (cases "B1 = B3")
                case True
                thus ?thesis 
                  by (metis Col_cases \<open>\<not> Col A1 A2 B1\<close> \<open>A1' \<noteq> A3\<close> 
                      \<open>Col A1 A2 A1'\<close> \<open>Col A1 A2 A3\<close> colx 
                      one_side_reflexivity)
              next
                case False
                have "Col A1 A2 A1'" 
                  using \<open>Col A1 A2 A1'\<close> by auto
                moreover
                have "Col A1 A2 A3" 
                  by (simp add: \<open>Col A1 A2 A3\<close>)
                moreover
                have "A1 A2 OS B1 B3" 
                  by (meson \<open>A1 A2 ParStrict B1 B2\<close> \<open>Col B1 B2 B3\<close>
                      par_strict_one_side)
                ultimately
                show ?thesis 
                  using col2_os__os \<open>A1' \<noteq> A3\<close> by blast
              qed
              moreover
              have "A1' A3 OS B3 B3'" 
                by (metis \<open>Bet A3 B3 B3' \<or> Bet A3 B3' B3\<close>
                    \<open>Cong A1' B1 B3' A3\<close> bet_out calculation col124__nos 
                    cong_identity invert_one_side l6_6 os_distincts 
                    out_one_side)
              ultimately
              show ?thesis 
                using one_side_transitivity by blast
            qed
            ultimately
            show ?thesis 
              using Saccheri_def by blast
          qed
          hence "A1' A3 ParStrict B1 B3'" 
            using sac__pars1423 by blast
          have "Col B3' B1 B2" 
          proof -
            have "A1 A2 Par B1 B2" 
              using \<open>A1 A2 Par B1 B2\<close> by auto
            moreover
            have "Col B1 B1 B2" 
              by (simp add: col_trivial_1)
            moreover
            have "A1 A2 Par B1 B3'" 
            proof -
              have "A1 \<noteq> A2" 
                using \<open>\<not> Col A1 A2 B1\<close> col_trivial_1 by blast
              moreover
              have "B1 B3' Par A1' A3" 
                using Par_strict_perm \<open>A1' A3 ParStrict B1 B3'\<close>
                  par_strict_par by blast
              moreover
              have "Col A1' A3 A1" 
                by (meson \<open>Col A1 A2 A1'\<close> \<open>Col A1 A2 A3\<close>
                    calculation(1) col_transitivity_1 
                    not_col_permutation_3)
              moreover
              have "Col A1' A3 A2" 
                by (meson \<open>Col A1 A2 A1'\<close> \<open>Col A1 A2 A3\<close>
                    calculation(1) col_transitivity_2 
                    not_col_permutation_2)
              ultimately 
              show ?thesis 
                by (meson par_col2_par par_symmetry)
            qed
            moreover
            have "Col B1 B1 B3'" 
              by (simp add: col_trivial_1)
            ultimately
            show ?thesis 
              using assms playfair_s_postulate_def by blast
          qed
          have "B3 = B3'" 
          proof -
            have "\<not> Col B1 B3' A3" 
              by (metis \<open>A1 A2 Par B1 B2\<close> \<open>A1' A3 ParStrict B1 B3'\<close>
                  \<open>Col A1 A2 A3\<close> \<open>Col B3' B1 B2\<close> \<open>\<not> Col A1 A2 B1\<close> 
                  col_transitivity_2 not_col_permutation_4 
                  not_strict_par par_strict_neq2)
            moreover
            have "A3 \<noteq> B3" 
              using \<open>B3 \<noteq> A3\<close> by auto
            moreover
            have "Col B1 B3' B3" 
              by (metis \<open>A1 A2 ParStrict B1 B2\<close> \<open>Col B1 B2 B3\<close> 
                  \<open>Col B3' B1 B2\<close> colx not_col_distincts
                  par_strict_neq2)
            moreover
            have "Col B1 B3' B3'" 
              by (simp add: col_trivial_2)
            moreover
            have "Col A3 B3 B3" 
              by (simp add: col_trivial_2)
            moreover
            have "Col A3 B3 B3'" 
              using \<open>Bet A3 B3 B3' \<or> Bet A3 B3' B3\<close>
                bet_col1 between_trivial by blast
            ultimately
            show ?thesis 
              using l6_21 by blast
          qed
          hence "Cong A3 B3 A1' B1" 
            using \<open>Cong A3 B3' A1' B1\<close> by auto
        }
        ultimately
        have "Cong A3 B3 A1' B1" 
          by blast
      }
      moreover
      have "Cong A3 B3 A1' B1" 
        using calculation(1) 
        by (simp add: \<open>A1 A2 Perp A3 B3\<close> \<open>Col A1 A2 A3\<close>
            \<open>Col B1 B2 B3\<close>)
      moreover
      have "Cong A1' B1 A4 B4" 
        using calculation(1) Cong_perm \<open>A1 A2 Perp A4 B4\<close>
          \<open>Col A1 A2 A4\<close> \<open>Col B1 B2 B4\<close> by blast
      ultimately
      have "Cong A3 B3 A4 B4" 
        using cong_transitivity by blast
    }
    moreover
    {
      assume "A1 \<noteq> A2" and "B1 \<noteq> B2" and "Col A1 B1 B2" and "Col A2 B1 B2" 
      hence "Cong A3 B3 A4 B4" 
        using \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Perp A3 B3\<close> 
          \<open>Col A1 A2 A3\<close> \<open>Col B1 B2 B3\<close> calculation 
          par_not_col_strict perp_not_col2 by blast
    }
    ultimately
    have "Cong A3 B3 A4 B4" 
      using Par_def \<open>A1 A2 Par B1 B2\<close> by presburger
  }
  thus ?thesis 
    using universal_posidonius_postulate_def by blast
qed

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux:
  assumes "weak_inverse_projection_postulate" 
  shows "\<forall> A1 A2 B1 B2 C1 C2 Q P R M.
             (A1 A2 Perp B1 B2 \<and> A1 A2 Perp C1 C2 \<and> 
              Col A1 A2 Q \<and> Col B1 B2 Q \<and>
              Col A1 A2 P \<and> Col C1 C2 P \<and> 
              Col B1 B2 R \<and> Coplanar Q P R C1 \<and> 
              Coplanar Q P R C2 \<and> \<not> Col Q P R \<and>
              M InAngle P Q R \<and> M Q P CongA M Q R) 
        \<longrightarrow>
           (B1 B2 ParStrict C1 C2 \<and> 
           (\<exists> S. Q Out M S \<and> Col C1 C2 S))" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 Q P R M
    assume "A1 A2 Perp B1 B2" and 
      "A1 A2 Perp C1 C2" and
      "Col A1 A2 Q" and 
      "Col B1 B2 Q" and
      "Col A1 A2 P" and 
      "Col C1 C2 P" and 
      "Col B1 B2 R" and
      "Coplanar Q P R C1" and 
      "Coplanar Q P R C2" and 
      "\<not> Col Q P R" and
      "M InAngle P Q R" and 
      "M Q P CongA M Q R"
    have "Q \<noteq> P" 
      using \<open>\<not> Col Q P R\<close> col_trivial_1 by auto
    have "Q \<noteq> R" 
      using \<open>\<not> Col Q P R\<close> col_trivial_3 by auto
    have "A1 \<noteq> A2" 
      using \<open>A1 A2 Perp C1 C2\<close> perp_distinct by auto
    have "C1 \<noteq> C2" 
      using \<open>A1 A2 Perp C1 C2\<close> perp_distinct by auto
    have "B1 \<noteq> B2" 
      using \<open>A1 A2 Perp B1 B2\<close> perp_distinct by auto
    have "Q \<noteq> M" 
      using \<open>M InAngle P Q R\<close> inangle_distincts by blast
    have "\<not> Col A1 A2 R" 
      using \<open>A1 A2 Perp B1 B2\<close> \<open>Col A1 A2 P\<close> \<open>Col A1 A2 Q\<close> 
        \<open>\<not> Col Q P R\<close> col3 perp_not_eq_1 by blast
    have "\<not> Col B1 B2 P" 
      using \<open>B1 \<noteq> B2\<close> \<open>Col B1 B2 Q\<close> \<open>Col B1 B2 R\<close> 
        \<open>\<not> Col Q P R\<close> col3 by blast
    have "B1 B2 ParStrict C1 C2" 
    proof -
      have "B1 B2 Par C1 C2" 
      proof -
        have "Col A1 P Q \<and> Col A2 P Q \<and> Col B1 R Q \<and> Col B2 R Q" 
          by (meson \<open>A1 \<noteq> A2\<close> \<open>B1 \<noteq> B2\<close> \<open>Col A1 A2 P\<close> 
              \<open>Col A1 A2 Q\<close> \<open>Col B1 B2 Q\<close> \<open>Col B1 B2 R\<close> 
              col_transitivity_1 col_transitivity_2)
        have "Coplanar Q P R A1" 
          by (meson \<open>Col A1 P Q \<and> Col A2 P Q \<and> Col B1 R Q \<and> Col B2 R Q\<close> 
              ncop__ncols not_col_permutation_3)
        have "Coplanar Q P R A2"
          using \<open>Col A1 P Q \<and> Col A2 P Q \<and> Col B1 R Q \<and> Col B2 R Q\<close> 
            ncop__ncols not_col_permutation_3 by blast
        have "Coplanar Q P R B1" 
          using \<open>Col A1 P Q \<and> Col A2 P Q \<and> Col B1 R Q \<and> Col B2 R Q\<close> 
            ncop__ncols not_col_permutation_3 by blast
        have "Coplanar Q P R B2" 
          using NCol_perm \<open>Col A1 P Q \<and> Col A2 P Q \<and> Col B1 R Q \<and> Col B2 R Q\<close> 
            ncop__ncols by blast
        have "Coplanar A1 A2 B1 C1" 
          by (meson \<open>Coplanar Q P R A1\<close> \<open>Coplanar Q P R A2\<close> 
              \<open>Coplanar Q P R B1\<close> \<open>Coplanar Q P R C1\<close> \<open>\<not> Col Q P R\<close>
              coplanar_pseudo_trans)
        moreover
        have "Coplanar A1 A2 B1 C2" 
          by (meson \<open>Coplanar Q P R A1\<close> \<open>Coplanar Q P R A2\<close>
              \<open>Coplanar Q P R B1\<close> \<open>Coplanar Q P R C2\<close> \<open>\<not> Col Q P R\<close>
              coplanar_pseudo_trans)
        moreover
        have "Coplanar A1 A2 B2 C1" 
          by (meson \<open>Coplanar Q P R A1\<close> \<open>Coplanar Q P R A2\<close>
              \<open>Coplanar Q P R B2\<close> \<open>Coplanar Q P R C1\<close> \<open>\<not> Col Q P R\<close> 
              coplanar_pseudo_trans)
        moreover
        have "Coplanar A1 A2 B2 C2" 
          by (meson \<open>Coplanar Q P R A1\<close> \<open>Coplanar Q P R A2\<close>
              \<open>Coplanar Q P R B2\<close> \<open>Coplanar Q P R C2\<close> \<open>\<not> Col Q P R\<close>
              coplanar_pseudo_trans)
        moreover
        have "B1 B2 Perp A1 A2" 
          using Perp_perm \<open>A1 A2 Perp B1 B2\<close> by blast
        moreover
        have "C1 C2 Perp A1 A2" 
          using Perp_perm \<open>A1 A2 Perp C1 C2\<close> by blast
        ultimately
        show ?thesis 
          by (meson l12_9)
      qed
      moreover
      have "Col C1 C2 P" 
        by (simp add: \<open>Col C1 C2 P\<close>)
      moreover
      have "\<not> Col B1 B2 P" 
        using \<open>\<not> Col B1 B2 P\<close> by auto
      ultimately
      show ?thesis 
        using par_not_col_strict by blast
    qed
    moreover
    have "\<not> Col Q C1 C2" 
      using \<open>Col B1 B2 Q\<close> calculation 
        not_col_permutation_1 par_not_col by blast
    have "Per P Q R" 
    proof -
      have "B1 B2 Perp A1 A2" 
        using Perp_perm \<open>A1 A2 Perp B1 B2\<close> by blast
      hence "A1 A2 Perp Q R" 
        using \<open>Q \<noteq> R\<close> \<open>Col B1 B2 R\<close> \<open>Col B1 B2 Q\<close> perp_col0 by blast
      moreover
      have "Col A1 A2 Q" 
        using \<open>Col A1 A2 Q\<close> by auto
      moreover
      have" Col A1 A2 P" 
        by (simp add: \<open>Col A1 A2 P\<close>)
      ultimately
      show ?thesis 
        by (meson \<open>Q \<noteq> P\<close> perp_col2 perp_per_2)
    qed
    have "P Q M P Q M SumA P Q R"
    proof -
      have "P Q M M Q R SumA P Q R" 
        by (simp add: \<open>M InAngle P Q R\<close> inangle__suma)
      moreover
      have "P Q M CongA P Q M" 
        using \<open>Q \<noteq> M\<close> \<open>Q \<noteq> P\<close> conga_refl by auto
      moreover
      have "M Q R CongA P Q M" 
        by (meson \<open>M Q P CongA M Q R\<close> conga_right_comm conga_sym)
      moreover
      have "P Q R CongA P Q R" 
        using \<open>Q \<noteq> P\<close> \<open>Q \<noteq> R\<close> conga_refl by auto
      ultimately
      show ?thesis 
        by (meson conga3_suma__suma)
    qed
    have "Acute P Q M" 
    proof -
      have "\<not> Bet P Q R" 
        using Col_cases \<open>\<not> Col Q P R\<close> bet_col by blast
      moreover
      have "SAMS P Q M P Q M" 
        by (meson \<open>M InAngle P Q R\<close> \<open>M Q P CongA M Q R\<close>
            conga2_sams__sams conga_left_comm conga_sym 
            conga_trans inangle__sams)
      moreover
      have "P Q M P Q M SumA P Q R" 
        by (simp add: \<open>P Q M P Q M SumA P Q R\<close>)
      ultimately
      show ?thesis 
        using nbet_sams_suma__acute by blast
    qed
    have "\<exists> C3. Col C1 C2 C3 \<and> P Q OS R C3" 
    proof -
      obtain C0 where "C1 \<noteq> C0" and "C2 \<noteq> C0" and 
        "P \<noteq> C0" and "Col C1 C2 C0" 
        using \<open>Col C1 C2 P\<close> diff_col_ex3 by blast
      have "\<exists> C3. Col C0 P C3 \<and> P Q OS R C3" 
      proof -
        have "C0 \<noteq> P" 
          using \<open>P \<noteq> C0\<close> by auto
        moreover
        have "Col P Q P" 
          using col_trivial_3 by blast
        moreover
        have "Col C0 P P" 
          by (simp add: col_trivial_2)
        moreover
        {
          assume "Col P Q C0" 
          hence "Col C1 C2 Q" 
            by (metis (full_types) \<open>Col C1 C2 C0\<close> \<open>Col C1 C2 P\<close> 
                calculation(1) col_permutation_4 col_trivial_2 l6_21)
          hence "False" 
            using \<open>\<not> Col Q C1 C2\<close> not_col_permutation_1 by blast
        }
        moreover
        have "\<not> Col P Q R" 
          using Col_cases \<open>\<not> Col Q P R\<close> by blast
        moreover
        have "Coplanar P Q R C0" 
        proof -
          have "Coplanar P Q R C1" 
            using \<open>Coplanar Q P R C1\<close> ncoplanar_perm_6 by blast
          moreover
          have "Coplanar P Q R C2" 
            by (simp add: \<open>Coplanar Q P R C2\<close> coplanar_perm_6)
          ultimately
          show ?thesis 
            using \<open>C1 \<noteq> C2\<close> \<open>Col C1 C2 C0\<close> col_cop2__cop by blast
        qed
        hence "Coplanar P Q C0 R" 
          by (simp add: coplanar_perm_1)
        ultimately
        show ?thesis 
          using cop_not_par_same_side by blast
      qed
      then obtain C3 where "Col C0 P C3" and "P Q OS R C3" 
        by blast
      thus ?thesis 
        by (metis \<open>Col C1 C2 C0\<close> \<open>Col C1 C2 P\<close> \<open>P \<noteq> C0\<close> colx)
    qed
    then obtain C3 where "Col C1 C2 C3" and "P Q OS R C3" 
      by blast
    have "\<exists> S. Q Out M S \<and> Col P C3 S" 
    proof -
      have "Q Out P P" 
        using \<open>Q \<noteq> P\<close> out_trivial by auto
      moreover
      have "P \<noteq> C3" 
        by (metis os_distincts \<open>P Q OS R C3\<close>)
      moreover
      have "Per Q P C3" 
      proof -
        have "A1 A2 Perp C1 C2" 
          by (simp add: \<open>A1 A2 Perp C1 C2\<close>)
        then obtain P' where "P' PerpAt A1 A2 C1 C2" 
          using perp_inter_perp_in_n by blast
        hence "Col P' A1 A2 \<and> Col P' C1 C2 \<and> 
               (\<forall> U V.(Col U A1 A2 \<and> Col V C1 C2)\<longrightarrow>Per U P' V)" 
          using PerpAt_def by blast
        hence "\<forall> U V.(Col U A1 A2 \<and> Col V C1 C2)\<longrightarrow>Per U P' V"
          by blast
        hence "P = P'" 
          by (metis Col_cases \<open>Col A1 A2 P\<close> \<open>Col C1 C2 P\<close> 
              \<open>P' PerpAt A1 A2 C1 C2\<close> l8_14_2_1b)
        moreover
        have "Col Q A1 A2" 
          using NCol_cases \<open>Col A1 A2 Q\<close> by blast
        moreover
        have "Col C3 C1 C2" 
          by (simp add: \<open>Col C1 C2 C3\<close> col_permutation_2)
        ultimately
        show ?thesis 
          using \<open>\<forall>U V. Col U A1 A2 \<and> Col V C1 C2 \<longrightarrow> Per U P' V\<close> by blast
      qed
      moreover
      have "Coplanar P Q M C3" 
      proof -
        have "Coplanar P Q R P" 
          using ncop_distincts by blast
        moreover
        have "Coplanar P Q R Q" 
          using ncop_distincts by blast
        moreover
        have "Coplanar P Q R M" 
          by (meson \<open>M InAngle P Q R\<close> inangle__coplanar 
              ncoplanar_perm_18)
        moreover
        have "Coplanar P Q R C3" 
          using \<open>P Q OS R C3\<close> os__coplanar by auto
        ultimately
        show ?thesis 
          using Col_perm \<open>\<not> Col Q P R\<close> coplanar_pseudo_trans by blast
      qed
      ultimately
      show ?thesis 
        using \<open>Acute P Q M\<close> \<open>Per P Q R\<close> \<open>P Q M P Q M SumA P Q R\<close> 
          assms weak_inverse_projection_postulate_def by blast
    qed
    then obtain S where "Q Out M S" and "Col P C3 S" 
      by blast
    hence "\<exists> S. Q Out M S \<and> Col C1 C2 S" 
      by (metis \<open>Col C1 C2 C3\<close> \<open>P Q OS R C3\<close> \<open>Col C1 C2 P\<close>
          colx not_col_distincts one_side_not_col124)
    ultimately
    have "B1 B2 ParStrict C1 C2 \<and> (\<exists> S. Q Out M S \<and> Col C1 C2 S)" 
      by blast
  }
  thus ?thesis 
    by blast
qed

lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom:
  assumes "weak_inverse_projection_postulate"
  shows "bachmann_s_lotschnittaxiom" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 D1 D2 Q P R
    assume "Q \<noteq> P" and 
      "Q \<noteq> R" and
      "A1 A2 Perp B1 B2" and
      "A1 A2 Perp C1 C2" and
      "B1 B2 Perp D1 D2" and
      "Col A1 A2 Q" and
      "Col B1 B2 Q" and 
      "Col A1 A2 P" and
      "Col C1 C2 P" and
      "Col B1 B2 R" and 
      "Col D1 D2 R" and
      "Coplanar Q P R C1" and 
      "Coplanar Q P R C2" and
      "Coplanar Q P R D1" and
      "Coplanar Q P R D2"
    have "Q P Perp R Q" 
      using \<open>Q \<noteq> P\<close> \<open>Q \<noteq> R\<close> \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 P\<close> 
        \<open>Col B1 B2 R\<close> \<open>Col B1 B2 Q\<close>\<open>A1 A2 Perp B1 B2\<close>
        perp_col4 by auto
    hence "\<not> Col P Q R" 
      by (meson NCol_cases perp_not_col)
    have "P \<noteq> Q" 
      using \<open>Q \<noteq> P\<close> by auto
    have "R \<noteq> Q" 
      using \<open>Q \<noteq> R\<close> by blast
    obtain M where "(M InAngle P Q R)" and "(M Q P CongA M Q R)" 
      using angle_bisector \<open>P \<noteq> Q\<close> \<open>R \<noteq> Q\<close> by blast
    have "B1 \<noteq> B2" 
      using \<open>B1 B2 Perp D1 D2\<close> col_trivial_1 perp_not_col2 by blast
    have "M \<noteq> Q" 
      using \<open>M InAngle P Q R\<close> inangle_distincts by presburger
    have "P Q M P Q M SumA P Q R" 
    proof -
      have "P Q M M Q R SumA P Q R" 
        by (simp add: \<open>M InAngle P Q R\<close> inangle__suma)
      moreover
      have "P Q M CongA P Q M" 
        using \<open>M \<noteq> Q\<close> \<open>Q \<noteq> P\<close> conga_refl by auto
      moreover
      have "M Q R CongA P Q M" 
        by (meson \<open>M Q P CongA M Q R\<close> conga_right_comm conga_sym)
      moreover
      have "P Q R CongA P Q R" 
        using \<open>Q \<noteq> P\<close> \<open>R \<noteq> Q\<close> conga_refl by auto
      ultimately
      show ?thesis 
        by (meson conga3_suma__suma)
    qed
    have "Acute P Q M" 
    proof -
      have "\<not> Bet P Q R" 
        using \<open>\<not> Col P Q R\<close> bet_col by force
      moreover
      have "SAMS P Q M P Q M" 
        by (meson \<open>M InAngle P Q R\<close> \<open>M Q P CongA M Q R\<close> 
            conga2_sams__sams conga_right_comm conga_trans 
            inangle__sams not_conga_sym)
      ultimately
      show ?thesis 
        by (meson \<open>P Q M P Q M SumA P Q R\<close> nbet_sams_suma__acute)
    qed
    have "B1 B2 ParStrict C1 C2 \<and> (\<exists> S. Q Out M S \<and> Col C1 C2 S)" 
    proof -
      have "A1 A2 Perp B1 B2" 
        using \<open>A1 A2 Perp B1 B2\<close> by auto
      moreover
      have "A1 A2 Perp C1 C2" 
        by (simp add: \<open>A1 A2 Perp C1 C2\<close>)
      moreover
      have "Col A1 A2 Q" 
        by (simp add: \<open>Col A1 A2 Q\<close>)
      moreover
      have "Col B1 B2 Q" 
        by (simp add: \<open>Col B1 B2 Q\<close>)
      moreover
      have "Col A1 A2 P" 
        by (simp add: \<open>Col A1 A2 P\<close>)
      moreover
      have "Col C1 C2 P" 
        by (simp add: \<open>Col C1 C2 P\<close>)
      moreover
      have "Col B1 B2 R" 
        using \<open>Col B1 B2 R\<close> by auto
      moreover
      have "Coplanar Q P R C1" 
        by (simp add: \<open>Coplanar Q P R C1\<close>)
      moreover
      have "Coplanar Q P R C2" 
        using \<open>Coplanar Q P R C2\<close> by auto
      moreover
      have "\<not> Col Q P R" 
        using Col_cases \<open>\<not> Col P Q R\<close> by blast
      moreover
      have "M InAngle P Q R" 
        by (simp add: \<open>M InAngle P Q R\<close>)
      moreover
      have "M Q P CongA M Q R"
        using \<open>M Q P CongA M Q R\<close> by blast
      ultimately
      show ?thesis 
        using assms 
          weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux
        by blast
    qed
    then obtain S where "Q Out M S" and "Col C1 C2 S" 
      by blast
    have "B1 B2 ParStrict C1 C2" 
      using \<open>B1 B2 ParStrict C1 C2 \<and> (\<exists> S. Q Out M S \<and> Col C1 C2 S)\<close> by blast
    have "A1 A2 ParStrict D1 D2 \<and> (\<exists> T.  Q Out M T \<and> Col D1 D2 T)"
    proof -
      have "B1 B2 Perp A1 A2" 
        using Perp_perm \<open>A1 A2 Perp B1 B2\<close> by blast
      moreover
      have "B1 B2 Perp D1 D2" 
        by (simp add: \<open>B1 B2 Perp D1 D2\<close>)
      moreover
      have "Col B1 B2 Q" 
        by (simp add: \<open>Col B1 B2 Q\<close>)
      moreover
      have "Col A1 A2 Q" 
        using \<open>Col A1 A2 Q\<close> by blast
      moreover
      have "Col B1 B2 R" 
        by (simp add: \<open>Col B1 B2 R\<close>)
      moreover
      have "Col D1 D2 R" 
        by (simp add: \<open>Col D1 D2 R\<close>)
      moreover
      have "Col A1 A2 P" 
        using \<open>Col A1 A2 P\<close> by auto
      moreover
      have "Coplanar Q R P D1" 
        by (simp add: \<open>Coplanar Q P R D1\<close> coplanar_perm_2)
      moreover
      have "Coplanar Q R P D2" 
        using \<open>Coplanar Q P R D2\<close> coplanar_perm_2 by blast
      moreover
      have "\<not> Col Q R P" 
        using Col_cases \<open>\<not> Col P Q R\<close> by blast
      moreover
      have "M InAngle R Q P" 
        by (simp add: \<open>M InAngle P Q R\<close> l11_24)
      moreover
      have "M Q R CongA M Q P" 
        by (simp add: \<open>M Q P CongA M Q R\<close> conga_sym_equiv)
      ultimately
      show ?thesis
        using assms 
          weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux 
        by blast
    qed
    then obtain T where "Q Out M T" and "Col D1 D2 T" 
      by blast
    have "A1 A2 ParStrict D1 D2"
      using \<open>A1 A2 ParStrict D1 D2 \<and> (\<exists> T.  Q Out M T \<and> Col D1 D2 T)\<close> by blast
    have "\<exists> I. Col C1 C2 I \<and> Col D1 D2 I" 
    proof (cases "Col C1 C2 T")
      case True
      thus ?thesis 
        using \<open>Col D1 D2 T\<close> by auto
    next
      case False
      hence "\<not> Col C1 C2 T" 
        by blast
      show ?thesis 
      proof (cases "Col D1 D2 S")
        case True
        thus ?thesis 
          using \<open>Col C1 C2 S\<close> by auto
      next
        case False
        hence "\<not> Col D1 D2 S"
          by auto
        have "Q Out S T" 
          using Out_cases \<open>Q Out M S\<close> \<open>Q Out M T\<close> l6_7 by blast
        have "S \<noteq> Q" 
          using \<open>Q Out M S\<close> l6_3_1 by blast
        have "T \<noteq> Q" 
          using \<open>Q Out M T\<close> l6_3_1 by blast
        {
          assume "Bet Q S T" 
          have "C1 C2 TS R T" 
          proof -
            have "C1 C2 TS Q T" 
              by (metis TS_def \<open>Bet Q S T\<close> \<open>Col C1 C2 S\<close> 
                  \<open>S \<noteq> Q\<close> \<open>\<not> Col C1 C2 T\<close> bet_col colx 
                  not_col_permutation_2)
            moreover
            have "C1 C2 ParStrict Q R" 
              by (metis Par_strict_cases \<open>B1 B2 ParStrict C1 C2\<close> 
                  \<open>Col B1 B2 Q\<close> \<open>Col B1 B2 R\<close> \<open>R \<noteq> Q\<close> 
                  par_strict_col2_par_strict)
            hence "C1 C2 OS Q R" 
              using l12_6 by blast
            ultimately
            show ?thesis 
              using l9_8_2 by blast
          qed
          then obtain I where "Col I C1 C2" and "Bet R I T" 
            using TS_def by blast
          have "T \<noteq> R" 
            using \<open>C1 C2 TS R T\<close> ts_distincts by blast
          hence "\<exists> I. Col C1 C2 I \<and> Col D1 D2 I" 
            by (meson \<open>Bet R I T\<close> \<open>Col D1 D2 R\<close> \<open>Col D1 D2 T\<close> 
                \<open>Col I C1 C2\<close> bet_col colx not_col_permutation_2)
        }
        moreover
        {
          assume "Bet Q T S" 
          have "D1 D2 TS P S" 
          proof -
            have "D1 D2 TS Q S" 
              by (metis Col_cases False \<open>Bet Q T S\<close> \<open>Col D1 D2 T\<close> 
                  \<open>T \<noteq> Q\<close> bet_col colx l9_18)
            moreover
            have "D1 D2 ParStrict A1 A2" 
              by (meson \<open>A1 A2 ParStrict D1 D2\<close> par_strict_symmetry)
            hence "D1 D2 ParStrict Q P" 
              using \<open>Q \<noteq> P\<close> \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 P\<close>
                par_strict_col2_par_strict by blast
            hence "D1 D2 OS Q P" 
              by (simp add: l12_6)
            ultimately
            show ?thesis 
              using l9_8_2 by blast
          qed
          then obtain I where "Col I D1 D2" and "Bet P I S" 
            using TS_def by blast
          hence "Col D1 D2 I" 
            using Col_cases by blast
          have "P \<noteq> S" 
            using \<open>D1 D2 TS P S\<close> not_two_sides_id by blast
          hence "\<exists> I. Col C1 C2 I \<and> Col D1 D2 I" 
            by (metis (full_types) \<open>Col C1 C2 P\<close> \<open>Col C1 C2 S\<close>
                \<open>\<And>thesis. (\<And>I. \<lbrakk>Col I D1 D2; Bet P I S\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
                bet_col col_trivial_2 l6_21 not_col_permutation_2)
        }
        ultimately
        show ?thesis 
          using Out_def \<open>Q Out S T\<close> by force
      qed
    qed
  }
  thus ?thesis  
    using bachmann_s_lotschnittaxiom_aux_R2 by blast
qed

lemma weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom:
  assumes "weak_triangle_circumscription_principle" 
  shows "bachmann_s_lotschnittaxiom" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD
    assume "IAB \<noteq> IAC" and "IAB \<noteq> IBD" and 
      "A1 A2 Perp B1 B2" and 
      "A1 A2 Perp C1 C2" and
      "B1 B2 Perp D1 D2" and
      "Col A1 A2 IAB" and
      "Col B1 B2 IAB" and 
      "Col A1 A2 IAC" and
      "Col C1 C2 IAC" and
      "Col B1 B2 IBD" and 
      "Col D1 D2 IBD" and
      "Coplanar IAB IAC IBD C1" and 
      "Coplanar IAB IAC IBD C2" and
      "Coplanar IAB IAC IBD D1" and
      "Coplanar IAB IAC IBD D2"
    obtain E where "IAC Midpoint IAB E" 
      using symmetric_point_construction by blast
    hence "Bet IAB IAC E" 
      using midpoint_bet by auto
    hence "Col IAB IAC E" 
      using Col_def by blast
    obtain F where "IBD Midpoint IAB F" 
      using symmetric_point_construction by blast
    hence "Bet IAB IBD F" 
      using midpoint_bet by auto
    hence "Col IAB IBD F" 
      using Col_def by blast
    have "IAB \<noteq> F" 
      using \<open>Bet IAB IBD F\<close> \<open>IAB \<noteq> IBD\<close> between_identity by blast
    have "IAB \<noteq> E" 
      using \<open>IAB \<noteq> IAC\<close> \<open>IAC Midpoint IAB E\<close> l8_20_2 by blast
    have "E IAB Perp IAB F" 
    proof -
      have "B1 B2 Perp E IAB" 
      proof -
        have "A1 A2 Perp B1 B2" 
          using \<open>A1 A2 Perp B1 B2\<close> by blast
        moreover
        have "E \<noteq> IAB" 
          using \<open>IAB \<noteq> E\<close> by blast
        moreover
        have "Col A1 A2 E" 
          using \<open>Col A1 A2 IAB\<close> \<open>Col A1 A2 IAC\<close> \<open>Col IAB IAC E\<close>
            \<open>IAB \<noteq> IAC\<close> colx by blast
        moreover
        have "Col A1 A2 IAB" 
          by (simp add: \<open>Col A1 A2 IAB\<close>)
        ultimately
        show ?thesis 
          using perp_col0 by blast
      qed
      moreover
      have "IAB \<noteq> F" 
        using \<open>IAB \<noteq> F\<close> by auto
      moreover
      have "Col B1 B2 IAB" 
        by (simp add: \<open>Col B1 B2 IAB\<close>)
      moreover
      have "Col B1 B2 F" 
        using \<open>Col B1 B2 IBD\<close> \<open>Col IAB IBD F\<close> \<open>IAB \<noteq> IBD\<close>
          calculation(3) colx by blast
      ultimately
      show ?thesis 
        using perp_col0 by blast
    qed
    have "Per IAC IAB IBD" 
    proof -
      have "IAB \<noteq> F" 
        by (simp add: \<open>IAB \<noteq> F\<close>)
      moreover
      have "Per IAC IAB F" 
      proof -
        have "IAB \<noteq> E" 
          using \<open>IAB \<noteq> E\<close> by blast
        moreover
        have "Per F IAB E" 
          using Perp_perm \<open>E IAB Perp IAB F\<close> perp_per_2 by blast
        moreover
        have "Col IAB E IAC" 
          using \<open>Col IAB IAC E\<close> not_col_permutation_5 by blast
        ultimately
        show ?thesis 
          using l8_2 per_col by blast
      qed
      moreover
      have "Col IAB F IBD" 
        using \<open>Col IAB IBD F\<close> not_col_permutation_5 by blast
      ultimately
      show ?thesis 
        using per_col by blast
    qed
    hence "\<not> Col IAC IAB IBD" 
      using \<open>IAB \<noteq> IAC\<close> \<open>IAB \<noteq> IBD\<close> l8_9 by blast
    have "\<exists> I. Col C1 C2 I \<and> Col D1 D2 I" 
    proof -
      have "\<not> Col E F IAB" 
        by (metis \<open>Col IAB IAC E\<close> \<open>Col IAB IBD F\<close> \<open>IAB \<noteq> E\<close> 
            \<open>IAB \<noteq> F\<close> \<open>\<not> Col IAC IAB IBD\<close> col_permutation_1 
            col_transitivity_2)
      moreover
      have "E IAB Perp F IAB" 
        by (simp add: \<open>E IAB Perp IAB F\<close> perp_right_comm)
      hence "Per E IAB F" 
        using Perp_cases perp_per_2 by blast
      moreover
      have "F IAB ReflectL D1 D2" 
      proof -
        have "IBD Midpoint IAB F" 
          by (simp add: \<open>IBD Midpoint IAB F\<close>)
        moreover
        have "Col D1 D2 IBD" 
          by (simp add: \<open>Col D1 D2 IBD\<close>)
        moreover
        have "D1 D2 Perp IAB F"
        proof -
          have "B1 B2 Perp D1 D2" 
            using \<open>B1 B2 Perp D1 D2\<close> by blast
          moreover
          have "IAB \<noteq> F" 
            using \<open>IAB \<noteq> F\<close> by auto
          moreover
          have "Col B1 B2 IAB" 
            by (simp add: \<open>Col B1 B2 IAB\<close>)
          moreover
          have "Col B1 B2 F" 
            using \<open>Col B1 B2 IBD\<close> \<open>Col IAB IBD F\<close> \<open>IAB \<noteq> IBD\<close>
              calculation(3) colx by blast
          ultimately
          show ?thesis 
            using perp_col0 by blast
        qed
        hence "(D1 D2 Perp IAB F) \<or> (IAB = F)" 
          by blast
        ultimately
        show ?thesis 
          using ReflectL_def by blast
      qed
      hence "D1 D2 PerpBisect F IAB" 
        using Perp_bisect_def \<open>IAB \<noteq> F\<close> by blast
      moreover
      have "E IAB ReflectL C1 C2" 
      proof -
        have "IAC Midpoint IAB E" 
          by (simp add: \<open>IAC Midpoint IAB E\<close>)
        moreover
        have "Col C1 C2 IAC" 
          by (simp add: \<open>Col C1 C2 IAC\<close>)
        moreover
        have "C1 C2 Perp IAB E"
        proof -
          have "A1 A2 Perp C1 C2" 
            by (simp add: \<open>A1 A2 Perp C1 C2\<close>)
          moreover
          have "IAB \<noteq> E" 
            using \<open>IAB \<noteq> E\<close> by auto
          moreover
          have "Col A1 A2 IAB" 
            by (simp add: \<open>Col A1 A2 IAB\<close>)
          moreover
          have "Col A1 A2 E" 
            using \<open>Col A1 A2 IAC\<close> \<open>Col IAB IAC E\<close> \<open>IAB \<noteq> IAC\<close>
              calculation(3) colx by blast
          ultimately
          show ?thesis 
            using perp_col0 by blast
        qed
        hence "(C1 C2 Perp IAB E) \<or> (IAB = E)" 
          by blast
        ultimately
        show ?thesis 
          using ReflectL_def by blast
      qed
      hence "C1 C2 PerpBisect E IAB" 
        using Perp_bisect_def \<open>IAB \<noteq> E\<close> by blast
      moreover
      have "Coplanar E F IAB D1" 
      proof -
        have "Coplanar IAB IAC IBD E" 
          using \<open>Col IAB IAC E\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD F" 
          using \<open>Col IAB IBD F\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD IAB" 
          using \<open>Coplanar IAB IAC IBD D1\<close> ncop_distincts by blast
        ultimately
        show ?thesis 
          by (meson \<open>Coplanar IAB IAC IBD D1\<close> \<open>\<not> Col IAC IAB IBD\<close>
              col_permutation_4 coplanar_pseudo_trans)
      qed
      moreover
      have "Coplanar E F IAB D2" 
      proof -
        have "Coplanar IAB IAC IBD E" 
          using \<open>Col IAB IAC E\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD F" 
          using \<open>Col IAB IBD F\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD IAB" 
          using ncop_distincts by blast
        moreover
        have "Coplanar IAB IAC IBD D2" 
          using \<open>Coplanar IAB IAC IBD D2\<close> by blast
        ultimately
        show ?thesis 
          using NCol_perm \<open>\<not> Col IAC IAB IBD\<close> coplanar_pseudo_trans by blast
      qed
      moreover
      have "Coplanar E F IAB C1" 
      proof -
        have "Coplanar IAB IAC IBD E" 
          using \<open>Col IAB IAC E\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD F" 
          using \<open>Col IAB IBD F\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD IAB" 
          using ncop_distincts by blast
        ultimately
        show ?thesis 
          using Col_perm \<open>Coplanar IAB IAC IBD C1\<close> 
            \<open>\<not> Col IAC IAB IBD\<close> coplanar_pseudo_trans by blast
      qed
      moreover
      have "Coplanar E F IAB C2" 
      proof -
        have "Coplanar IAB IAC IBD E" 
          using \<open>Col IAB IAC E\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD F" 
          using \<open>Col IAB IBD F\<close> ncop__ncols by blast
        moreover
        have "Coplanar IAB IAC IBD IAB" 
          using ncop_distincts by blast
        moreover
        have "Coplanar IAB IAC IBD C2" 
          using \<open>Coplanar IAB IAC IBD C2\<close> by auto
        ultimately
        show ?thesis 
          using NCol_cases \<open>\<not> Col IAC IAB IBD\<close> 
            coplanar_pseudo_trans by blast
      qed
      ultimately
      show ?thesis 
        using assms weak_triangle_circumscription_principle_def by blast
    qed
  }
  thus ?thesis
    using bachmann_s_lotschnittaxiom_aux_R2 by blast
qed

lemma universal_posidonius_postulate__perpendicular_transversal_postulate_aux_lem:
  fixes A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD
  assumes 
    "IAB \<noteq> IAC" and 
    "IAB \<noteq> IBD" and
    "A1 A2 Perp B1 B2" and
    "A1 A2 Perp C1 C2" and
    "B1 B2 Perp D1 D2" and 
    "Col A1 A2 IAB" and
    "Col B1 B2 IAB" and
    "Col A1 A2 IAC" and
    "Col C1 C2 IAC" and
    "Col B1 B2 IBD" and
    "Col D1 D2 IBD" and
    "Coplanar IAB IAC IBD C1" and
    "Coplanar IAB IAC IBD C2" and
    "Coplanar IAB IAC IBD D1" and
    "Coplanar IAB IAC IBD D2" and
    "postulate_of_right_saccheri_quadrilaterals" 
  shows "\<exists> I. Col C1 C2 I \<and> Col D1 D2 I" 
proof - 
  have "thales_postulate" 
    using assms(16) rah__thales_postulate by blast
  hence "thales_converse_postulate" 
    using thales_postulate__thales_converse_postulate by blast
  hence "weak_triangle_circumscription_principle"
    using thales_converse_postulate__weak_triangle_circumscription_principle
    by blast
  hence "bachmann_s_lotschnittaxiom" 
    using weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom
    by blast
  thus ?thesis 
    using assms(1) assms(2) assms(3) assms(4) assms(5)
      assms(6) assms(7) assms(8) assms(9) 
      assms(10) assms(11) assms(12)
      assms(13) assms(14) assms(15) 
      bachmann_s_lotschnittaxiom_aux_R1 by blast
qed

lemma universal_posidonius_postulate__perpendicular_transversal_postulate_aux:
  assumes "universal_posidonius_postulate"
  shows "\<forall> E F G H R P.
  E G Perp R P \<and> Coplanar F H P R \<and> Col E G R \<and> Saccheri E F H G \<longrightarrow>
  F H Perp P R" 
proof -
  {
    fix E F G H R P
    assume "E G Perp R P" and "Coplanar F H P R" and 
      "Col E G R" and "Saccheri E F H G"
    have "Per F E G" 
      using \<open>Saccheri E F H G\<close> perp_per_2 sac__perp1214 by blast
    have "E G Perp E F" 
      using Perp_cases \<open>Saccheri E F H G\<close> sac__perp1214 by blast
    have "E G ParStrict F H" 
      by (simp add: \<open>Saccheri E F H G\<close> sac__pars1423)
    hence "E \<noteq> G" 
      using par_strict_distinct by presburger
    have "E \<noteq> F" 
      using \<open>E G Perp E F\<close> perp_distinct by blast
    have "P \<noteq> R" 
      using \<open>E G Perp R P\<close> perp_distinct by blast
    have "E \<noteq> H" 
      using \<open>Saccheri E F H G\<close> sac_distincts by blast
    have "F \<noteq> H" 
      using \<open>E G ParStrict F H\<close> par_strict_distinct by auto
    have "postulate_of_right_saccheri_quadrilaterals" 
    proof -
      obtain M1 where "M1 Midpoint E G" 
        using midpoint_existence by presburger
      hence "Bet E M1 G" 
        by (simp add: midpoint_bet)
      obtain M2 where "M2 Midpoint F H"       
        using midpoint_existence by presburger
      hence "Bet F M2 H" 
        by (simp add: midpoint_bet)
      have "Lambert M1 M2 F E" 
        using mid2_sac__lam6521 \<open>M1 Midpoint E G\<close> \<open>M2 Midpoint F H\<close>
          \<open>Saccheri E F H G\<close> by blast
      have "M1 \<noteq> M2"
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast
      have "F \<noteq> M2"
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast
      have "F \<noteq> E"
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast
      have "M1 \<noteq> E"
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast
      have "Per M2 M1 E" 
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast
      have "Per M1 E F" 
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast
      have "Per M1 M2 F" 
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast
      have "Coplanar M1 M2 F E" 
        using \<open>Lambert M1 M2 F E\<close> Lambert_def by blast    
      have "Saccheri M1 M2 F E" 
      proof -
        have "Cong F E M1 M2" 
        proof -
          have "E G Par F H" 
            using \<open>Saccheri E F H G\<close> sac__par1423 by blast
          moreover
          have "Col E G E" 
            by (simp add: col_trivial_3)
          moreover
          have "Col F H F" 
            by (simp add: col_trivial_3)
          moreover
          have "E G Perp E F" 
            by (simp add: \<open>E G Perp E F\<close>)
          moreover
          have "Col E G M1" 
            using \<open>Bet E M1 G\<close> bet_col not_col_permutation_5 by blast
          moreover
          have "Col F H M2" 
            using \<open>Bet F M2 H\<close> bet_col col_permutation_5 by blast
          moreover
          have "E G Perp M1 M2" 
          proof -
            have "E M1 Perp M1 M2" 
              by (metis l8_2 \<open>M1 \<noteq> E\<close> \<open>M1 \<noteq> M2\<close> \<open>Per M2 M1 E\<close> per_perp)
            moreover
            have "Col E M1 E" 
              by (simp add: col_trivial_3)
            moreover
            have "Col E M1 G" 
              by (simp add: Col_def \<open>Bet E M1 G\<close>)
            ultimately
            show ?thesis 
              using \<open>E \<noteq> G\<close> perp_col2 by blast
          qed
          ultimately
          show ?thesis 
            using assms universal_posidonius_postulate_def
              cong_left_commutativity by blast
        qed
        hence "Cong M1 M2 F E" 
          using cong_symmetry by blast
        moreover
        have "M1 E ParStrict M2 F" 
        proof -
          have "M1 \<noteq> E" 
            by (simp add: \<open>M1 \<noteq> E\<close>)
          moreover have "M2 \<noteq> F" 
            using \<open>F \<noteq> M2\<close> by blast
          moreover have "Col E G M1" 
            using \<open>Bet E M1 G\<close> bet_col not_col_permutation_5 by blast
          moreover
          have "Col E G E" 
            by (simp add: col_trivial_3)
          moreover
          have "Col F H M2" 
            using \<open>Bet F M2 H\<close> bet_col col_permutation_5 by blast
          moreover
          have "Col F H F" 
            by (simp add: col_trivial_3)
          moreover  have "E G ParStrict F H" 
            by (simp add: \<open>E G ParStrict F H\<close>)
          ultimately
          show ?thesis 
            using par_strict_col4__par_strict by blast
        qed
        hence "M1 E OS M2 F" 
          using l12_6 by auto
        ultimately
        show ?thesis
          using \<open>Per M2 M1 E\<close> \<open>Per M1 E F\<close> 
          by (simp add: Saccheri_def)
      qed
      thus ?thesis 
        using \<open>Per M1 M2 F\<close> per_sac__rah 
          existential_playfair__rah_1 by blast
    qed
    have "F H Perp P R" 
    proof (cases "E = R")
      case True
      hence "E P Perp F H" 
      proof -
        have "Col F P E" 
        proof -
          have "Coplanar G F P E" 
          proof -
            have "Coplanar H R F G" 
              using True \<open>E G ParStrict F H\<close> ncoplanar_perm_11 
                pars__coplanar by blast
            moreover have "Coplanar H R F F" 
              using ncop_distincts by blast
            moreover have "Coplanar H R F P" 
              using \<open>Coplanar F H P R\<close> ncoplanar_perm_13 by blast
            moreover have "Coplanar H R F E" 
              using True ncop_distincts by blast
            ultimately show ?thesis 
              using ParStrict_def True \<open>E G ParStrict F H\<close> 
                col_trivial_1 coplanar_pseudo_trans 
                not_col_permutation_2 by blast
          qed
          moreover
          have "Per P E G" 
            using True \<open>E G Perp R P\<close> l8_2 perp_per_2 by blast
          ultimately
          show ?thesis 
            using \<open>E \<noteq> G\<close> \<open>Per F E G\<close> cop_per2__col by blast  
        qed
        hence "Col E F P" 
          by (simp add: col_permutation_2)
        moreover
        have "Per E F H" 
          using \<open>Saccheri E F H G\<close> 
            \<open>postulate_of_right_saccheri_quadrilaterals\<close> 
            postulate_of_right_saccheri_quadrilaterals_def by blast
        hence "E F Perp F H" 
          by (simp add: \<open>E \<noteq> F\<close> \<open>F \<noteq> H\<close> per_perp)
        ultimately
        show ?thesis 
          using True \<open>P \<noteq> R\<close> col_trivial_3 perp_col2 by metis
      qed
      thus ?thesis 
        using Perp_perm True by blast
    next
      case False
      have "\<not> Col F H R" 
        by (meson \<open>Col E G R\<close> \<open>E G ParStrict F H\<close> 
            not_col_permutation_1 par_not_col)
      have "\<exists> I. Col P R I \<and> Col F H I" 
      proof -
        have "E \<noteq> F" 
          by (simp add: \<open>E \<noteq> F\<close>)
        moreover
        have "E G Perp E F" 
          by (simp add: \<open>E G Perp E F\<close>)
        moreover
        have "E G Perp P R" 
          using Perp_cases \<open>E G Perp R P\<close> by blast
        moreover
        have "Per E F H" 
          using \<open>Saccheri E F H G\<close> 
            \<open>postulate_of_right_saccheri_quadrilaterals\<close> 
            postulate_of_right_saccheri_quadrilaterals_def by blast
        hence "E F Perp F H" 
          by (simp add: \<open>E \<noteq> F\<close> \<open>F \<noteq> H\<close> per_perp)
        moreover
        have "Col E G E" 
          by (simp add: col_trivial_3)
        moreover
        have "Col E F E" 
          by (simp add: col_trivial_3)
        moreover
        have "Col E G R" 
          by (simp add: \<open>Col E G R\<close>)
        moreover
        have "Col P R R" 
          by (simp add: col_trivial_2)
        moreover
        have "Col E F F" 
          using col_trivial_2 by auto
        moreover
        have "Col F H F" 
          by (simp add: col_trivial_3)
        moreover
        have "Coplanar E R F P" 
        proof -
          have "Coplanar F H R P" 
            using \<open>Coplanar F H P R\<close> coplanar_perm_1 by blast
          moreover
          have "Coplanar F H R E" 
            by (metis False \<open>Col E G E\<close> \<open>Col E G R\<close> 
                \<open>E G ParStrict F H\<close> par_strict_col2_par_strict 
                par_strict_symmetry pars__coplanar)
          moreover
          have "Coplanar F H R F" 
            using ncop_distincts by blast
          moreover
          have "Coplanar F H R R" 
            using ncop_distincts by blast
          ultimately
          show ?thesis 
            by (meson \<open>\<not> Col F H R\<close> coplanar_pseudo_trans)
        qed
        moreover
        have "Coplanar E R F R" 
          using ncop_distincts by blast
        moreover
        have "Coplanar E R F F" 
          using ncop_distincts by blast
        moreover
        have "Coplanar F H E R" 
          by (meson False \<open>Col E G R\<close> \<open>E G ParStrict F H\<close> 
              col_trivial_3 par_strict_col2_par_strict 
              par_strict_symmetry pars__coplanar)
        hence "Coplanar E R F H" 
          by (simp add: coplanar_perm_16)
        ultimately
        show ?thesis 
          using False \<open>postulate_of_right_saccheri_quadrilaterals\<close> 
            universal_posidonius_postulate__perpendicular_transversal_postulate_aux_lem 
          by blast
      qed
      then obtain S where "Col P R S" and "Col F H S" 
        by blast
      have "S \<noteq> R" 
        using \<open>Col F H S\<close> \<open>\<not> Col F H R\<close> by auto
      have "Saccheri E F S R" 
      proof -
        have "Per F E R" 
        proof -
          have "E \<noteq> G" 
            by (simp add: \<open>E \<noteq> G\<close>)
          moreover
          have "Per F E G" 
            using \<open>Saccheri E F H G\<close> perp_per_2 sac__perp1214 by blast
          ultimately
          show ?thesis 
            using  \<open>Col E G R\<close> per_col by blast
        qed
        moreover
        have "R E Perp S R" 
        proof -
          have "Col E G E" 
            by (simp add: col_trivial_3)
          moreover
          have "Col R P S" 
            using Col_cases \<open>Col P R S\<close> by blast
          moreover
          have "Col R P R" 
            by (simp add: col_trivial_3)
          ultimately
          show ?thesis 
            using False \<open>S \<noteq> R\<close> \<open>E G Perp R P\<close>  
              \<open>Col E G R\<close> perp_col4 by auto
        qed
        hence "Per E R S" 
          using perp_per_1 by force
        moreover
        have "Cong E F R S" 
        proof -
          have "E G Par F H" 
            using \<open>E G ParStrict F H\<close> par_strict_par by auto
          moreover
          have "Col E G E" 
            by (simp add: col_trivial_3)
          moreover
          have "Col F H F" 
            by (simp add: col_trivial_3)
          moreover
          have "E G Perp R S" 
          proof -
            have "R P Perp E G" 
              using Perp_perm \<open>E G Perp R P\<close> by blast
            moreover
            have "Col R P S" 
              using \<open>Col P R S\<close> not_col_permutation_4 by blast
            ultimately
            show ?thesis 
              using \<open>E G Perp R P\<close> \<open>S \<noteq> R\<close> perp_col1 by auto
          qed
          ultimately
          show ?thesis 
            using \<open>E G Perp E F\<close> \<open>Col E G R\<close> \<open>Col F H S\<close> 
              assms universal_posidonius_postulate_def by blast
        qed
        hence "Cong E F S R" 
          using not_cong_1243 by blast
        moreover
        have "E R OS F S" 
        proof -
          {
            assume "F = S"
            hence "\<not> Col E G F" 
              by (meson \<open>Col F H S\<close> \<open>E G ParStrict F H\<close> 
                  not_col_permutation_1 par_not_col)
            have "Col E P R" 
            proof -
              have "F E Perp E G" 
                using Perp_cases \<open>E G Perp E F\<close> by blast
              moreover
              have "P R Perp E G" 
                using Perp_perm \<open>E G Perp R P\<close> by blast
              moreover
              have "Col F P R" 
                by (simp add: \<open>Col P R S\<close> \<open>F = S\<close> col_permutation_2)
              moreover
              have "Coplanar E G E P" 
                using ncop_distincts by blast
              moreover
              have "Coplanar E G E R" 
                using ncop_distincts by blast
              ultimately
              show ?thesis 
                using col_cop2_perp2__col by blast
            qed
            hence False 
              by (metis False \<open>Col E G R\<close> \<open>E G Perp R P\<close> 
                  col_trivial_3 l6_21 not_col_permutation_2
                  perp_not_col2)
          }
          moreover
          have "E R ParStrict F H" 
            by (meson False \<open>Col E G R\<close> \<open>E G ParStrict F H\<close> 
                \<open>F \<noteq> H\<close> col_trivial_2 col_trivial_3 
                par_strict_col4__par_strict)
          ultimately
          show ?thesis 
            using \<open>Col F H S\<close> par_strict_one_side by blast
        qed
        ultimately
        show ?thesis 
          using Saccheri_def by blast
      qed
      have "F \<noteq> S" 
        using \<open>Saccheri E F S R\<close> sac_distincts by blast
      have "F S Perp P R" 
      proof -
        have "R \<noteq> P" 
          using \<open>P \<noteq> R\<close> by auto
        moreover
        have "Saccheri R S F E" 
          by (simp add:  \<open>Saccheri E F S R\<close> sac_perm)
        hence "Per R S F" 
          using \<open>postulate_of_right_saccheri_quadrilaterals\<close> 
            postulate_of_right_saccheri_quadrilaterals_def by blast
        hence "R S Perp S F" 
          using \<open>F \<noteq> S\<close> \<open>S \<noteq> R\<close> per_perp by auto
        moreover
        have "Col R S P" 
          using \<open>Col P R S\<close> not_col_permutation_2 by blast
        ultimately
        show ?thesis 
          using Perp_perm perp_col by blast
      qed
      moreover
      have "Col F S H" 
        using Col_cases \<open>Col F H S\<close> by blast
      ultimately
      show ?thesis 
        using \<open>F \<noteq> H\<close> perp_col by blast
    qed
  }
  thus ?thesis 
    by blast
qed

lemma universal_posidonius_postulate__perpendicular_transversal_postulate:
  assumes "universal_posidonius_postulate"
  shows "perpendicular_transversal_postulate" 
proof -
  {
    fix A B C D P Q
    assume "A B Par C D" and 
      "A B Perp P Q" and 
      "Coplanar C D P Q"
    {
      fix P Q
      assume "A B Perp P Q" and 
        "Coplanar C D P Q" and
        "\<not> Col A B P" 
      have "A B Par C D" 
        using \<open>A B Par C D\<close> by auto
      hence "A B ParStrict C D \<or> (A \<noteq> B \<and> C \<noteq> D \<and> Col A C D \<and> Col B C D)"
        by (simp add: Par_def)
      moreover
      {
        assume "A B ParStrict C D"
        obtain R where "Col A B R" and "Col P Q R" 
          using \<open>A B Perp P Q\<close> perp_inter_exists by blast
        have "\<not> Col A B C" 
          using \<open>A B ParStrict C D\<close> l12_6 one_side_not_col123 by blast
        then obtain E where "Col A B E" and "A B Perp C E" 
          using l8_18_existence by blast
        have "\<not> Col A B D" 
          using \<open>A B ParStrict C D\<close> par_strict_not_col_4 by auto
        then obtain G where "Col A B G" and "A B Perp D G" 
          using l8_18_existence by blast
        {
          assume "E = G" 
          hence "Col C D E" 
          proof -
            have "E C Perp A B" 
              using Perp_perm \<open>A B Perp C E\<close> by blast
            moreover
            have "D E Perp A B" 
              using Perp_cases \<open>A B Perp D G\<close> \<open>E = G\<close> by blast
            moreover
            have "Col E D E" 
              by (simp add: col_trivial_3)
            moreover
            have "Coplanar A B C D" 
              by (simp add: \<open>A B ParStrict C D\<close> pars__coplanar)
            moreover
            have "Coplanar A B C E" 
              using \<open>Col A B E\<close> ncop__ncols by blast
            ultimately
            show ?thesis 
              using col_cop2_perp2__col by blast
          qed
          hence "Col E A B \<and> Col E C D" 
            using Col_cases \<open>Col A B E\<close> by blast
          hence False 
            using \<open>A B Par C D\<close> \<open>Col A B G\<close> \<open>Col C D E\<close> \<open>E = G\<close>
              \<open>\<not> Col A B C\<close> not_strict_par by blast
        }
        have "Saccheri E C D G" 
        proof -
          have "A B Perp E C" 
            by (simp add: \<open>A B Perp C E\<close> perp_right_comm)
          hence "Per C E G" 
            using \<open>Col A B E\<close> \<open>Col A B G\<close> \<open>A B Perp C E\<close>
              l8_16_1 by blast
          moreover
          have "Per E G D" 
            using \<open>A B Perp D G\<close> \<open>Col A B G\<close> \<open>Col A B E\<close>
              Per_perm l8_16_1 by blast
          moreover
          have "Cong E C D G" 
          proof -
            have "Col C D C" 
              by (simp add: col_trivial_3)
            moreover
            have "Col C D D" 
              by (simp add: col_trivial_2)
            moreover
            have "A B Perp G D" 
              by (simp add:\<open>A B Perp D G\<close> perp_right_comm)
            ultimately
            show ?thesis 
              using assms \<open>A B Par C D\<close> \<open>Col A B E\<close> \<open>A B Perp E C\<close>
                \<open>Col A B G\<close>  not_cong_1243 
                universal_posidonius_postulate_def by blast
          qed
          moreover
          have "C D ParStrict A B" 
            using \<open>A B ParStrict C D\<close> par_strict_symmetry by blast
          hence "C D ParStrict E G" 
            using \<open>Col A B E\<close> \<open>Col A B G\<close> \<open>E = G \<Longrightarrow> False\<close> 
              par_strict_col2_par_strict by blast
          hence "E G OS C D" 
            by (simp add: pars__os3412)
          ultimately
          show ?thesis 
            using Saccheri_def by blast
        qed
        have "P \<noteq> Q" 
          using \<open>A B Perp P Q\<close> perp_distinct by auto
        have "P \<noteq> R" 
          using \<open>Col A B R\<close> \<open>\<not> Col A B P\<close> by auto
        have "A \<noteq> B" 
          using \<open>\<not> Col A B C\<close> col_trivial_1 by auto
        have "C D Perp P R" 
        proof -
          have "A B Perp R P" 
            by (meson \<open>A B Perp P Q\<close> \<open>Col P Q R\<close> \<open>P \<noteq> R\<close> 
                perp_col1 perp_right_comm)
          hence "E G Perp R P" 
            using \<open>Col A B E\<close> \<open>Col A B G\<close> \<open>E = G \<Longrightarrow> False\<close> 
              perp_col2 by blast
          moreover
          have "Coplanar C D P R" 
            using \<open>Coplanar C D P Q\<close> \<open>Col P Q R\<close> \<open>P \<noteq> Q\<close> 
              col_cop__cop by blast
          moreover
          have "Col E G R" 
            using \<open>Col A B R\<close> \<open>Col A B E\<close> \<open>Col A B G\<close>
              \<open>A \<noteq> B\<close> col3 by blast
          ultimately
          show ?thesis 
            using assms 
              universal_posidonius_postulate__perpendicular_transversal_postulate_aux 
              \<open>Saccheri E C D G\<close> by blast
        qed
        hence "P R Perp C D" 
          using Perp_perm by blast
        hence "C D Perp P Q" 
          using NCol_perm Perp_cases \<open>Col P Q R\<close> \<open>P \<noteq> Q\<close> 
            perp_col1 by blast
      }
      moreover
      have "(A \<noteq> B \<and> C \<noteq> D \<and> Col A C D \<and> Col B C D) \<longrightarrow> C D Perp P Q" 
        by (meson \<open>A B Par C D\<close> \<open>A B Perp P Q\<close> not_col_distincts 
            not_col_permutation_2 not_strict_par perp_col2)
      ultimately
      have "C D Perp P Q" 
        by blast
    }
    moreover
    have "\<not> Col A B P \<longrightarrow> C D Perp P Q" 
      by (simp add: \<open>A B Perp P Q\<close> \<open>Coplanar C D P Q\<close> calculation)
    moreover
    have "\<not> Col A B Q \<longrightarrow> C D Perp P Q" 
      using \<open>A B Perp P Q\<close> \<open>Coplanar C D P Q\<close> calculation(1)
        ncoplanar_perm_1 perp_right_comm by blast
    ultimately
    have "C D Perp P Q" 
      using \<open>A B Perp P Q\<close> \<open>Coplanar C D P Q\<close> perp_not_col2 by blast
  }
  thus ?thesis 
    using perpendicular_transversal_postulate_def by blast
qed

lemma playfair__alternate_interior:
  assumes "playfair_s_postulate"
  shows "alternate_interior_angles_postulate" 
proof -
  {
    fix A B C D
    assume "A C TS B D" and
      "A B Par C D"
    have "\<not> Col A B C" 
      using TS_def \<open>A C TS B D\<close> not_col_permutation_4 by blast
    hence "\<not> Col B A C \<and> \<not> Col A C B" 
      using Col_cases by blast
    then obtain D' where "B A C CongA A C D'" and "A C TS D' B" 
      using ex_conga_ts by blast
    have "B A C CongA D' C A" 
      by (simp add: \<open>B A C CongA A C D'\<close> conga_right_comm)
    moreover
    have "D' C A CongA D C A" 
    proof -
      have "C Out D D'" 
      proof -
        have "Col C C D \<and> Col D' C D" 
        proof -
          have "A B Par C D" 
            using \<open>A B Par C D\<close> by auto
          moreover
          have "Col C C D" 
            by (simp add: col_trivial_1)
          moreover
          have "A B Par C D'" 
          proof -
            have "A C TS B D'" 
              by (meson \<open>A C TS D' B\<close> l9_2)
            moreover
            have "B A C CongA D' C A" 
              by (simp add: \<open>B A C CongA D' C A\<close>)
            ultimately
            show ?thesis 
              using l12_21_b by blast 
          qed
          moreover
          have "Col C C D'" 
            using col_trivial_1 by blast
          ultimately
          show ?thesis
            using assms playfair_s_postulate_def by blast
        qed
        hence "Col C D D'" 
          using not_col_permutation_1 by blast
        moreover
        have "A C OS D D'" 
          using \<open>A C TS B D\<close> \<open>A C TS D' B\<close> l9_2 l9_8_1 by blast
        hence "C A OS D D'" 
          by (simp add: invert_one_side)
        ultimately
        show ?thesis 
          using col_one_side_out by blast
      qed
      moreover
      have "C Out A A" 
        using \<open>\<not> Col B A C \<and> \<not> Col A C B\<close> 
          not_col_distincts out_trivial by blast
      ultimately
      show ?thesis 
        by (simp add: out2__conga)
    qed
    ultimately
    have "B A C CongA D C A" 
      by (meson conga_trans)
  }
  thus ?thesis 
    using alternate_interior_angles_postulate_def by presburger
qed

lemma playfair_bis__playfair:
  assumes "alternative_playfair_s_postulate"
  shows "playfair_s_postulate" 
proof -
  {
    fix A1 A2 B1 B2 C1 C2 P
    assume "A1 A2 Par B1 B2" and
      "Col P B1 B2" and
      "A1 A2 Par C1 C2" and
      "Col P C1 C2"
    have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
    proof (cases "Col A1 A2 P")
      case True
      {
        assume H1: "(A1 \<noteq> A2 \<and> B1 \<noteq> B2 \<and> Col A1 B1 B2 \<and> Col A2 B1 B2 ) \<longrightarrow>
(Col C1 B1 B2 \<and> Col C2 B1 B2)"
        have ?thesis 
          by (metis Par_def True \<open>A1 A2 Par B1 B2\<close> H1 
              \<open>Col P B1 B2\<close> col_permutation_2 par_not_col)
      }
      moreover
      have "A1 A2 ParStrict C1 C2 \<longrightarrow> ?thesis" 
        by (metis True \<open>A1 A2 Par C1 C2\<close> \<open>Col P C1 C2\<close> 
            inter_uniqueness_not_par not_col_permutation_2
            par_strict_not_col_1)
      ultimately
      show ?thesis using \<open>A1 A2 Par C1 C2\<close> 
        by (metis True \<open>Col P C1 C2\<close> col_permutation_2 colx not_strict_par)
    next
      case False
      have "A1 \<noteq> A2" 
        using False not_col_distincts by presburger
      then obtain X where "P X Perp A1 A2"
        using perp_exists by blast
      {
        assume H2: "\<forall> A1 A2. (A1 A2 Par B1 B2 \<and>
                          A1 A2 Par C1 C2 \<and> \<not> Col A1 A2 P \<and>
                          P X Perp A1 A2 \<and> \<not> Col P X A1) 
                   \<longrightarrow> 
                         (Col C1 B1 B2 \<and> Col C2 B1 B2)"
        fix A1 A2
        assume "A1 A2 Par B1 B2" and
          "A1 A2 Par C1 C2" and
          "\<not> Col A1 A2 P" and
          "P X Perp A1 A2"
        {
          assume "Col P X A1"
          have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
            using \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Par C1 C2\<close> 
              \<open>\<not> Col A1 A2 P\<close> \<open>P X Perp A1 A2\<close> 
            by (metis Col_perm Perp_cases H2 
                l8_16_1 par_left_comm)
        }
        moreover
        {
          assume "Col P X A2"
          have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
            using \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Par C1 C2\<close> 
              \<open>Col P X A1 \<Longrightarrow> Col C1 B1 B2 \<and> Col C2 B1 B2\<close> 
              \<open>P X Perp A1 A2\<close> H2 \<open>\<not> Col A1 A2 P\<close> by blast
        }
        ultimately
        have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
          using \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Par C1 C2\<close> \<open>P X Perp A1 A2\<close> 
            H2 \<open>\<not> Col A1 A2 P\<close> by blast
      }
      {
        fix A1' A2'
        assume "A1' A2' Par B1 B2" and
          "A1' A2' Par C1 C2" and
          "\<not> Col A1' A2' P" and
          "P X Perp A1' A2'" and
          "\<not> Col P X A1'"
        have "Coplanar P X A1' A2'" 
          by (simp add: \<open>P X Perp A1' A2'\<close> perp__coplanar)
        have "P \<noteq> X" 
          using \<open>\<not> Col P X A1'\<close> col_trivial_1 by force
        then obtain D where "P X Perp D P" and "Coplanar P X A1' D" 
          using ex_perp_cop by blast
        hence "D \<noteq> P" 
          using perp_not_eq_2 by blast
        have "P Perp2 A1' A2' D P" 
        proof -
          have "Col P X P"
            by (simp add: col_trivial_3)
          moreover
          have "X P Perp A1' A2'" 
            using Perp_cases \<open>P X Perp A1' A2'\<close> by blast
          moreover
          have "X P Perp P D" 
            using Perp_cases \<open>P X Perp D P\<close> by blast
          ultimately
          show ?thesis 
            using Perp2_def perp_right_comm by blast
        qed
        have "Col B1 P D \<and> Col B2 P D" 
        proof -
          have "Col P P D" 
            using col_trivial_1 by auto
          moreover
          have "Coplanar A1' A2' P D" 
            by (meson \<open>Coplanar P X A1' A2'\<close> \<open>Coplanar P X A1' D\<close> 
                \<open>\<not> Col P X A1'\<close> coplanar_perm_16 l9_30 ncop_distincts)
          ultimately
          show ?thesis 
            using \<open>P Perp2 A1' A2' D P\<close> \<open>\<not> Col A1' A2' P\<close>
              \<open>A1' A2' Par B1 B2\<close> \<open>Col P B1 B2\<close>
              alternative_playfair_s_postulate_def assms 
              coplanar_perm_1 not_col_permutation_5 by blast
        qed
        moreover
        have "Col C1 P D \<and> Col C2 P D" 
        proof -
          have "Col P P D" 
            using col_trivial_1 by auto
          moreover
          have "Coplanar A1' A2' P D" 
            by (meson \<open>Coplanar P X A1' A2'\<close> \<open>Coplanar P X A1' D\<close> 
                \<open>\<not> Col P X A1'\<close> coplanar_perm_16 l9_30 ncop_distincts)
          ultimately
          show ?thesis 
            using \<open>P Perp2 A1' A2' D P\<close> \<open>\<not> Col A1' A2' P\<close> 
              \<open>A1' A2' Par C1 C2\<close> \<open>Col P C1 C2\<close> 
              alternative_playfair_s_postulate_def assms 
              coplanar_perm_1 not_col_permutation_5 by blast
        qed
        ultimately
        have "Col P D C1 \<and> Col P D C2 \<and> Col P D B1 \<and> Col P D B2" 
          using Col_cases by blast
        hence "Col C1 B1 B2 \<and> Col C2 B1 B2" 
          by (metis \<open>D \<noteq> P\<close> col3)
      }
      thus ?thesis 
        using False \<open>A1 A2 Par B1 B2\<close> \<open>A1 A2 Par C1 C2\<close> 
          \<open>P X Perp A1 A2\<close> 
          \<open>\<And>A2a A1a. \<lbrakk>\<forall>A1 A2. A1 A2 Par B1 B2 \<and> A1 A2 Par C1 C2 \<and> 
            \<not> Col A1 A2 P \<and> P X Perp A1 A2 \<and> \<not> Col P X A1 
             \<longrightarrow> Col C1 B1 B2 \<and> Col C2 B1 B2; A1a A2a Par B1 B2; 
             A1a A2a Par C1 C2; \<not> Col A1a A2a P; P X Perp A1a A2a\<rbrakk> 
      \<Longrightarrow> Col C1 B1 B2 \<and> Col C2 B1 B2\<close> by blast
    qed
  }
  thus ?thesis 
    using playfair_s_postulate_def by blast
qed

lemma playfair_s_postulate_implies_midpoint_converse_postulate:
  assumes "playfair_s_postulate"
  shows "midpoint_converse_postulate"
proof -
  {
    fix A B C P Q
    assume "\<not> Col A B C" and
      "P Midpoint B C" and
      "A B Par Q P" and
      "Col A C Q" 
    obtain X where "X Midpoint A C" 
      using midpoint_existence by blast
    hence "Bet A X C" 
      by (simp add: midpoint_bet)
    have "Cong A X X C" 
      using \<open>X Midpoint A C\<close> midpoint_cong by blast
    have "A B ParStrict X P" 
      using triangle_mid_par \<open>P Midpoint B C\<close> \<open>X Midpoint A C\<close>
        \<open>\<not> Col A B C\<close> by blast
    have "X = Q" 
    proof -
      have "Col A C X" 
        by (meson \<open>Bet A X C\<close> bet_col1 between_trivial)
      moreover
      have "Col P Q X" 
        using \<open>A B Par Q P\<close> \<open>A B ParStrict X P\<close> assms 
          col_trivial_3 not_col_permutation_3 par_strict_par 
          playfair_s_postulate_def by blast
      moreover
      have "Col P Q Q" 
        by (simp add: col_trivial_2)
      ultimately
      show ?thesis
        using l6_21 
        by (metis \<open>A B Par Q P\<close> \<open>Col A C Q\<close> \<open>\<not> Col A B C\<close>
            not_col_distincts par_col2_par_bis par_id)
    qed
    hence "Q Midpoint A C" 
      using \<open>X Midpoint A C\<close> by auto
  }
  thus ?thesis 
    using midpoint_converse_postulate_def by blast
qed

lemma inter_dec_plus_par_perp_perp_imply_triangle_circumscription:
  assumes (*"decidability_of_intersection" and*)
    "perpendicular_transversal_postulate"
  shows "triangle_circumscription_principle" 
proof -
  {
    fix A B C
    assume "\<not> Col A B C"
    hence "A \<noteq> B" 
      using col_trivial_1 by blast
    then obtain C1 C2 where "C1 C2 PerpBisect A B" and 
      "Coplanar A B C C1" and "Coplanar A B C C2"
      using perp_bisect_existence_cop by blast
    have "A \<noteq> C" 
      using \<open>\<not> Col A B C\<close> col_trivial_3 by blast
    then obtain B1 B2 where "B1 B2 PerpBisect A C" and 
      "Coplanar A C B B1" and "Coplanar A C B B2"
      using perp_bisect_existence_cop by blast
    {
      assume "\<exists> I. Col I B1 B2 \<and> Col I C1 C2"
      then obtain CC where "Col CC B1 B2" and "Col CC C1 C2"
        by auto
      have "Cong A CC B CC"
      proof (cases "CC = C1")
        case True
        thus ?thesis 
          using \<open>C1 C2 PerpBisect A B\<close> perp_bisect_cong2 by blast
      next
        case False
        hence "CC \<noteq> C1" 
          by auto
        have "C1 C2 PerpBisectBis A B" 
          using \<open>C1 C2 PerpBisect A B\<close> perp_bisect_equiv_defA by blast
        then obtain I where "I PerpAt C1 C2 A B" and "I Midpoint A B" 
          using Perp_bisect_bis_def by blast
        have "I PerpAt C1 CC A B" 
          by (metis False perp_in_sym \<open>Col CC C1 C2\<close> 
              \<open>I PerpAt C1 C2 A B\<close> not_col_permutation_2 
              perp_in_col_perp_in)
        hence "C1 CC PerpBisectBis A B" 
          using Perp_bisect_bis_def \<open>I Midpoint A B\<close> by blast
        hence "C1 CC PerpBisect A B" 
          by (simp add: perp_bisect_equiv_defB)
        hence "CC C1 PerpBisect A B" 
          by (simp add: perp_bisect_sym_1)
        thus ?thesis 
          by (simp add: perp_bisect_cong_1)
      qed
      moreover
      have "Cong A CC C CC" 
      proof (cases "CC = B1")
        case True
        thus ?thesis 
          using \<open>B1 B2 PerpBisect A C\<close> perp_bisect_cong_1 by auto
      next
        case False
        hence "CC \<noteq> B1" 
          by auto
        have "B1 B2 PerpBisectBis A C" 
          using \<open>B1 B2 PerpBisect A C\<close> perp_bisect_equiv_defA by blast
        then obtain I where "I PerpAt B1 B2 A C" and "I Midpoint A C" 
          using Perp_bisect_bis_def by blast
        have "I PerpAt B1 CC A C" 
          by (metis False perp_in_sym \<open>Col CC B1 B2\<close> 
              \<open>I PerpAt B1 B2 A C\<close> not_col_permutation_2 
              perp_in_col_perp_in)
        hence "B1 CC PerpBisectBis A C" 
          using Perp_bisect_bis_def \<open>I Midpoint A C\<close> by blast
        hence "B1 CC PerpBisect A C" 
          by (simp add: perp_bisect_equiv_defB)
        hence "CC B1 PerpBisect A C" 
          by (simp add: perp_bisect_sym_1)
        thus ?thesis 
          by (simp add: perp_bisect_cong_1)
      qed
      moreover
      have "C1 C2 Perp A B \<or> B = A" 
        using \<open>C1 C2 PerpBisect A B\<close> perp_bisect_perp by blast
      have "Coplanar A B C CC" 
      proof (cases "A = B")
        case True
        thus ?thesis 
          using \<open>A \<noteq> B\<close> by auto
      next
        case False
        hence "C1 C2 Perp A B" 
          using \<open>C1 C2 Perp A B \<or> B = A\<close> by auto
        hence "Coplanar C1 C2 A B" 
          using perp__coplanar by simp
        have "C1 \<noteq> C2" 
          using \<open>C1 C2 PerpBisect A B\<close> col_trivial_1 
            perp_bisect_perp perp_not_col2 by blast
        moreover
        have "Coplanar A B C C1" 
          using \<open>Coplanar A B C C1\<close> by auto
        moreover
        have "Coplanar A B C C2" 
          by (simp add: \<open>Coplanar A B C C2\<close>)
        ultimately
        show ?thesis 
          by (meson Col_cases \<open>Col CC C1 C2\<close> col_cop2__cop)
      qed
      ultimately
      have "\<exists> CC. Cong A CC B CC \<and> Cong A CC C CC \<and> Coplanar A B C CC" 
        by auto
    }
    moreover
    {
      assume "\<not> (\<exists> I. Col I B1 B2 \<and> Col I C1 C2)"
      have "Coplanar B1 B2 C1 C2" 
      proof -
        have "Coplanar A B C B1" 
          using \<open>Coplanar A C B B1\<close> ncoplanar_perm_2 by blast
        moreover
        have "Coplanar A B C B2" 
          using \<open>Coplanar A C B B2\<close> coplanar_perm_2 by blast
        moreover
        have "Coplanar A B C C1" 
          using \<open>Coplanar A B C C1\<close> by auto
        moreover
        have "Coplanar A B C C2" 
          by (simp add: \<open>Coplanar A B C C2\<close>)
        ultimately
        show ?thesis 
          by (meson \<open>\<not> Col A B C\<close> coplanar_pseudo_trans)
      qed
      hence "B1 B2 ParStrict C1 C2" 
        using \<open>\<nexists>I. Col I B1 B2 \<and> Col I C1 C2\<close> 
        by (simp add: ParStrict_def)
      hence "B1 B2 Par C1 C2" 
        by (simp add: Par_def)
      have "C1 C2 Perp A B" 
        using \<open>C1 C2 PerpBisect A B\<close> perp_bisect_perp by auto
      have "B1 B2 Perp A C" 
        using \<open>B1 B2 PerpBisect A C\<close> perp_bisect_perp by auto
      hence "Coplanar C1 C2 A C \<longrightarrow> C1 C2 Perp A C" 
        using \<open>B1 B2 Par C1 C2\<close> assms 
          perpendicular_transversal_postulate_def by simp
      have "A B Par A C" 
      proof -
        have "Coplanar C1 C2 A A" 
          using ncop_distincts by blast
        moreover
        have "Coplanar C1 C2 A C" 
          by (meson \<open>Coplanar A B C C1\<close> \<open>Coplanar A B C C2\<close>
              \<open>\<not> Col A B C\<close> coplanar_pseudo_trans
              ncop_distincts)
        moreover
        have "Coplanar C1 C2 A B" 
          using \<open>C1 C2 PerpBisect A B\<close> perp__coplanar 
            perp_bisect_perp by blast
        hence "Coplanar C1 C2 B A" 
          by (simp add: coplanar_perm_1)
        moreover
        have "Coplanar C1 C2 B C" 
          by (meson \<open>Coplanar A B C C1\<close> \<open>Coplanar A B C C2\<close>
              \<open>\<not> Col A B C\<close> coplanar_pseudo_trans ncop_distincts)
        moreover
        have "A B Perp C1 C2" 
          using Perp_cases \<open>C1 C2 Perp A B\<close> by blast
        moreover
        have "A C Perp C1 C2" 
          using Perp_perm \<open>Coplanar C1 C2 A C \<longrightarrow> C1 C2 Perp A C\<close>
            calculation(2) by blast
        ultimately
        show ?thesis 
          by (simp add: l12_9)
      qed
      hence "Col A B C"
        by (simp add: par_id)
      hence False 
        using \<open>\<not> Col A B C\<close> by blast
      hence "\<exists> CC. Cong A CC B CC \<and> Cong A CC C CC \<and> Coplanar A B C CC" 
        by simp
    }
    ultimately
    have "\<exists> CC. Cong A CC B CC \<and> Cong A CC C CC \<and> Coplanar A B C CC" 
      by auto
  }
  thus ?thesis 
    using triangle_circumscription_principle_def by blast
qed

(** If a straight line falling on two straight lines make
    the sum of the interior angles on the same side different from two right angles,
    the two straight lines meet if produced indefinitely. *)

lemma original_euclid__original_spp:
  assumes "euclid_s_parallel_postulate"
  shows "alternative_strong_parallel_postulate" 
proof -
  {
    fix A B C D P Q R
    assume "B C OS A D" and
      "A B C B C D SumA P Q R" and
      "\<not> Bet P Q R"
    obtain A' where "B Midpoint A A'" 
      using symmetric_point_construction by blast
    hence "Bet A B A'" 
      by (simp add: midpoint_bet)
    hence "Col A B A'" 
      by (simp add: bet_col)
    obtain D' where "C Midpoint D D'" 
      using symmetric_point_construction by blast
    hence "Bet D C D'" 
      by (simp add: midpoint_bet)
    hence "Col D C D'" 
      by (simp add: bet_col)
    have "A \<noteq> B" 
      using \<open>B C OS A D\<close> os_distincts by blast
    have "C \<noteq> B" 
      using \<open>A B C B C D SumA P Q R\<close> suma_distincts by blast
    have "C \<noteq> D" 
      using \<open>B C OS A D\<close> os_distincts by blast
    have "D \<noteq> D'" 
      using \<open>Bet D C D'\<close> \<open>C \<noteq> D\<close> bet_neq12__neq by blast
    hence "C \<noteq> D'" 
      using \<open>C Midpoint D D'\<close> midpoint_distinct_1 by blast
    have "A' \<noteq> B" 
      using \<open>A \<noteq> B\<close> \<open>B Midpoint A A'\<close> midpoint_not_midpoint by blast
    {
      assume "B C D LeA C B A'"
      have "SAMS A B C B C D" 
        using Midpoint_def \<open>A \<noteq> B\<close> \<open>A' \<noteq> B\<close> \<open>B C D LeA C B A'\<close> 
          \<open>B Midpoint A A'\<close> sams_chara by blast 
      then obtain Y where "B Out A Y \<and> C Out D Y" 
        using \<open>B C OS A D\<close> \<open>A B C B C D SumA P Q R\<close> \<open>\<not> Bet P Q R\<close>
          assms euclid_s_parallel_postulate_def by blast
      hence "\<exists> Y. Col B A Y \<and> Col C D Y" 
        using out_col by blast
    }
    moreover
    {
      assume "C B A' LeA B C D"
      have "SAMS D' C B C B A'" 
      proof -
        have "Bet D' C D" 
          by (simp add: \<open>C Midpoint D D'\<close> l7_2 midpoint_bet)
        moreover
        have "C B A' LeA B C D" 
          by (simp add: \<open>C B A' LeA B C D\<close>)
        ultimately
        show ?thesis 
          by (metis \<open>C \<noteq> D'\<close> \<open>C \<noteq> D\<close> sams_chara)
      qed
      have "B \<noteq> C" 
        using \<open>C \<noteq> B\<close> by auto
      have "D' \<noteq> C" 
        using \<open>C \<noteq> D'\<close> by auto
      obtain P' Q' R' where "A' B C B C D' SumA P' Q' R'" 
        using ex_suma \<open>A' \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>C \<noteq> D'\<close> by blast
      have "B C OS A' D'" 
      proof -
        have "\<not> Col B C A" 
          using \<open>B C OS A D\<close> col123__nos by blast
        have "\<not> Col B C D" 
          using \<open>B C OS A D\<close> col124__nos by blast
        have "B C TS A A'" 
          using \<open>A' \<noteq> B\<close> \<open>Bet A B A'\<close> \<open>\<not> Col B C A\<close> bet__ts by force
        hence "B C TS A' D" 
          using \<open>B C OS A D\<close> l9_2 l9_8_2 by blast
        moreover
        have "B C TS D D'" 
          using \<open>Bet D C D'\<close> \<open>D' \<noteq> C\<close> \<open>\<not> Col B C D\<close> bet__ts 
            invert_two_sides not_col_permutation_4 by presburger
        ultimately
        show ?thesis 
          by (meson l9_2 l9_8_1)
      qed
      moreover
      {
        assume "Bet P' Q' R'" 
        hence "A' B C SuppA B C D'" 
          using bet_suma__suppa  \<open>A' B C B C D' SumA P' Q' R'\<close> by auto
        have "A B C SuppA B C D" 
        proof -
          have "B C D' CongA A B C" 
          proof -
            have "A' B C SuppA B C D'" 
              by (simp add: \<open>A' B C SuppA B C D'\<close>)
            moreover
            have "A' B C SuppA A B C" 
              by (metis between_symmetry \<open>A \<noteq> B\<close> \<open>A' \<noteq> B\<close>
                  \<open>Bet A B A'\<close> \<open>C \<noteq> B\<close> bet__suppa suppa_right_comm)
            ultimately
            show ?thesis 
              by (simp add: suppa2__conga456)
          qed
          moreover
          have "A' B C CongA B C D" 
          proof -
            have "A' B C SuppA B C D'" 
              using \<open>A' B C SuppA B C D'\<close> by auto
            moreover
            have "B C D SuppA B C D'" 
              using \<open>Bet D C D'\<close> \<open>C \<noteq> B\<close> \<open>C \<noteq> D\<close> \<open>D' \<noteq> C\<close> 
                bet__suppa suppa_left_comm by presburger
            ultimately 
            show ?thesis 
              by (simp add: suppa2__conga123)
          qed
          moreover
          have "B C D' SuppA A' B C" 
            by (simp add: \<open>A' B C SuppA B C D'\<close> suppa_sym)
          ultimately
          show ?thesis 
            by (meson conga2_suppa__suppa)
        qed
        hence "Bet P Q R" 
          using \<open>A B C B C D SumA P Q R\<close> suma_suppa__bet by auto
        hence False 
          using \<open>\<not> Bet P Q R\<close> by auto
      }
      ultimately
      have "\<exists> Y. B Out A' Y \<and> C Out D' Y"
        using \<open>A' B C B C D' SumA P' Q' R'\<close> assms 
          euclid_s_parallel_postulate_def \<open>SAMS D' C B C B A'\<close> 
          sams_comm sams_sym by blast
      then obtain Y where "B Out A' Y" and "C Out D' Y"
        by auto
      have "Col B A' Y" 
        using \<open>B Out A' Y\<close> out_col by auto
      hence "Col B A Y" 
        by (meson \<open>A' \<noteq> B\<close> \<open>Col A B A'\<close> col_permutation_4
            col_trivial_2 colx)
      moreover
      have "Col C D' Y" 
        using \<open>C Out D' Y\<close> out_col by auto
      hence "Col C D Y" 
        by (meson \<open>Col D C D'\<close> \<open>D' \<noteq> C\<close> col_trivial_2
            colx not_col_permutation_4)
      ultimately
      have "\<exists> Y. Col B A Y \<and> Col C D Y" 
        by auto
    }
    ultimately
    have "\<exists> Y. Col B A Y \<and> Col C D Y" 
      using lea_total by (metis \<open>A' \<noteq> B\<close> \<open>C \<noteq> B\<close> \<open>C \<noteq> D\<close>)
  }
  thus ?thesis 
    using alternative_strong_parallel_postulate_def by blast
qed

lemma original_spp__inverse_projection_postulate:
  assumes "alternative_strong_parallel_postulate"
  shows "inverse_projection_postulate" 
proof -
  {
    fix A B C P Q
    assume "Acute A B C" and
      "B Out A P" and
      "P \<noteq> Q" and
      "Per B P Q" and
      "Coplanar A B C Q"
    have "B \<noteq> A" 
      using \<open>Acute A B C\<close> acute_distincts by blast
    have "B \<noteq> P" 
      using \<open>B Out A P\<close> l6_3_1 by blast
    have "B \<noteq> C" 
      using \<open>Acute A B C\<close> acute_distincts by blast
    have "Col B A P" 
      using \<open>B Out A P\<close> out_col by blast
    have "\<exists> Y. B Out C Y \<and> Col P Q Y"
    proof (cases "Col A B C")
      case True
      {
        assume "Bet C B A"
        obtain x y z where "Per x y z" and "A B C LtA x y z" 
          using \<open>Acute A B C\<close> \<open>Bet C B A\<close> acute_not_bet 
            between_symmetry by blast
        have "\<not> (A B C LtA x y z \<and> x y z LtA A B C)" 
          by (simp add: not_and_lta)
        have "A B C LtA x y z" 
          using \<open>A B C LtA x y z\<close> by auto
        moreover
        have "x y z LtA A B C" 
          using \<open>Acute A B C\<close> \<open>Bet C B A\<close> acute_not_bet
            between_symmetry by blast
        ultimately
        have False 
          using \<open>\<not> (A B C LtA x y z \<and> x y z LtA A B C)\<close> by blast
      }
      hence "\<not> Bet C B A" 
        by auto
      hence "B Out C A"
        by (simp add: True col_permutation_3 l6_4_2)
      hence "B Out C P" 
        using l6_7 \<open>B Out A P\<close> by blast
      moreover
      have "Col P Q P" 
        by (simp add: col_trivial_3)
      ultimately
      show ?thesis 
        by auto
    next
      case False
      have "\<not> Col B P Q" 
        using \<open>B \<noteq> P\<close> \<open>P \<noteq> Q\<close> \<open>Per B P Q\<close> l8_9 by blast
      have "\<exists> Q0. Col Q P Q0 \<and> A B OS C Q0"
      proof -
        have "Q \<noteq> P" 
          using \<open>P \<noteq> Q\<close> by auto
        moreover
        have "Col A B P" 
          using Col_cases \<open>Col B A P\<close> by blast
        moreover
        have "Col Q P P" 
          using col_trivial_2 by blast
        moreover
        have "\<not>Col A B Q" 
          by (metis Out_def \<open>B Out A P\<close> \<open>\<not> Col B P Q\<close> 
              calculation(2) col_transitivity_2)
        moreover
        have "\<not> Col A B C" 
          by (simp add: False)
        moreover
        have "Coplanar A B Q C" 
          using \<open>Coplanar A B C Q\<close> coplanar_perm_1 by blast
        ultimately
        show ?thesis 
          by (simp add: cop_not_par_same_side)
      qed
      then obtain Q0 where "Col Q P Q0" and "A B OS C Q0"
        by auto
      have "\<not> Col A B Q0" 
        using \<open>A B OS C Q0\<close> one_side_not_col124 by blast
      have "P \<noteq> Q0" 
        using NCol_cases \<open>Col B A P\<close> \<open>\<not> Col A B Q0\<close> by blast
      then obtain D E F where "C B P B P Q0 SumA D E F" 
        using ex_suma \<open>B \<noteq> C\<close> \<open>B \<noteq> P\<close> by presburger
      have "\<exists> Y. Col B C Y \<and> Col P Q0 Y"
      proof -
        have "B P OS C Q0" 
          using \<open>A B OS C Q0\<close> \<open>B \<noteq> P\<close> \<open>Col B A P\<close>
            col_one_side invert_one_side by blast
        moreover
        have "C B P B P Q0 SumA D E F" 
          by (simp add: \<open>C B P B P Q0 SumA D E F\<close>)
        moreover
        {
          assume "Bet D E F"
          have "Per B P Q0" 
            using \<open>Col Q P Q0\<close> \<open>P \<noteq> Q\<close> \<open>Per B P Q\<close> 
              not_col_permutation_4 per_col by blast
          hence "Per C B P" 
            using \<open>Bet D E F\<close> \<open>C B P B P Q0 SumA D E F\<close> 
              bet_per_suma__per123 by blast
          hence "A B C LtA C B P" 
            using \<open>Acute A B C\<close> acute_per__lta \<open>B \<noteq> C\<close>\<open>B \<noteq> P\<close> by simp
          hence "A B C LeA C B P \<and> \<not> A B C CongA C B P" 
            by (simp add: lta__lea lta_not_conga)
          moreover
          have "A B C CongA P B C" 
          proof -
            have "B Out P A" 
              using \<open>B Out A P\<close> l6_6 by blast
            moreover                    
            have "B Out C C" 
              using \<open>B \<noteq> C\<close> out_trivial by fastforce
            ultimately
            show ?thesis
              by (simp add: out2__conga)
          qed
          hence"A B C CongA C B P" 
            by (simp add: conga_right_comm)
          ultimately
          have False 
            by blast
        }
        ultimately
        show ?thesis 
          using alternative_strong_parallel_postulate_def assms by blast
      qed
      then obtain Y where "Col B C Y \<and> Col P Q0 Y"
        by auto
      have "Col A B B" 
        by (simp add: col_trivial_2)
      hence "\<exists> B0. A B Perp B0 B \<and> A B OS C B0" 
        by (simp add: False l10_15)
      then obtain B0 where "A B Perp B0 B" and "A B OS C B0" 
        by auto
      have "\<not> Col A B B0" 
        using \<open>A B OS C B0\<close> col124__nos by blast
      have "\<not> Col B C P" 
        by (meson False \<open>B \<noteq> P\<close> \<open>Col B A P\<close> col2__eq col_permutation_4)
      have "B0 \<noteq> B" 
        using \<open>Col A B B\<close> \<open>\<not> Col A B B0\<close> by auto
      have "P \<noteq> Y" 
        using \<open>Col B C Y \<and> Col P Q0 Y\<close> \<open>\<not> Col B C P\<close> by blast
      have "B B0 OS C Y" 
      proof -
        have "B B0 OS C P" 
        proof -
          have "B0 B OS C A" 
          proof -
            have "\<not> Col B0 B A" 
              using \<open>\<not> Col A B B0\<close> not_col_permutation_3 by blast
            moreover
            {
              assume "Col B B0 C" 
              hence "A B C LtA A B C" 
                by (metis Perp_cases \<open>A B Perp B0 B\<close> \<open>
Acute A B C\<close> \<open>B \<noteq> C\<close> acute_per__lta 
                    col_trivial_3 l8_16_1)
              hence "False" 
                using not_and_lta by blast
            }
            moreover
            have "A B C LeA A B B0" 
              using \<open>A B Perp B0 B\<close> \<open>Acute A B C\<close> \<open>B \<noteq> A\<close> 
                \<open>B0 \<noteq> B\<close> acute_per__lta lta__lea perp_comm 
                perp_per_2 by presburger
            hence "C InAngle A B B0" 
              by (simp add: \<open>A B OS C B0\<close> lea_in_angle 
                  one_side_symmetry)
            hence "C InAngle B0 B A" 
              using l11_24 by blast
            ultimately
            show ?thesis 
              using in_angle_one_side by blast
          qed
          hence "B B0 OS C A" 
            using invert_one_side by blast
          moreover
          have "B B0 OS A P" 
            using \<open>B Out A P\<close> calculation col124__nos 
              col_trivial_3 l9_19_R2 by blast
          ultimately
          show ?thesis 
            using one_side_transitivity by blast
        qed
        moreover
        have "B B0 Par P Y" 
        proof -
          have "Coplanar A B B P" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A B B Y" 
            using ncop_distincts by blast
          moreover
          have "Coplanar A B B0 P" 
            by (meson \<open>Col B A P\<close> col_permutation_4 ncop__ncols)
          moreover
          have "Coplanar A B B0 Y" 
          proof -
            have "\<not> Col C A B" 
              using Col_cases False by blast
            moreover
            have "Coplanar C A B B0" 
            proof -
              have "Coplanar A B B0 C" 
                by (meson \<open>A B OS C B0\<close> cop2_os__osp 
                    ncop_distincts osp_distincts)
              moreover
              have "Coplanar A B B0 A" 
                using ncop_distincts by auto
              moreover
              have "Coplanar A B B0 B" 
                using ncop_distincts by blast
              moreover
              have "Coplanar A B B0 B0"  
                using ncop_distincts by blast
              ultimately
              show ?thesis 
                using coplanar_perm_18 by blast
            qed
            moreover
            have "Coplanar C A B Y" 
              using \<open>Col B C Y \<and> Col P Q0 Y\<close> 
                col_permutation_4 ncop__ncols by blast
            ultimately 
            show ?thesis 
              using coplanar_trans_1 by blast
          qed
          moreover
          have "B B0 Perp A B" 
            using Perp_cases \<open>A B Perp B0 B\<close> by blast
          moreover
          have "B P Perp P Y" 
          proof -
            have "B P Perp P Q" 
              using \<open>B \<noteq> P\<close> \<open>P \<noteq> Q\<close> \<open>Per B P Q\<close> per_perp by blast
            moreover
            have "Col P Q Y" 
              by (meson \<open>Col B C Y \<and> Col P Q0 Y\<close> \<open>Col Q P Q0\<close> 
                  \<open>P \<noteq> Q0\<close> col_trivial_2 colx not_col_permutation_4)
            ultimately
            show ?thesis 
              using \<open>P \<noteq> Y\<close> perp_col1 by blast
          qed
          hence "P Y Perp B P" 
            using Perp_perm by blast
          hence "P Y Perp B A" 
            using \<open>B Out A P\<close> \<open>B \<noteq> A\<close> col_permutation_5
              out_col perp_col1 by blast
          hence "P Y Perp A B" 
            by (simp add: perp_right_comm)
          ultimately
          show ?thesis 
            using l12_9 by blast
        qed
        hence "B B0 ParStrict P Y" 
          using calculation not_col_distincts 
            one_side_not_col124 par_not_col_strict by blast
        hence "B B0 OS P Y" 
          using l12_6 by blast
        ultimately
        show ?thesis 
          using one_side_transitivity by blast
      qed
      hence "B Out C Y" 
        using \<open>Col B C Y \<and> Col P Q0 Y\<close> 
          col_one_side_out by blast
      moreover
      have "Col P Q Y" 
        by (meson \<open>Col B C Y \<and> Col P Q0 Y\<close> \<open>Col Q P Q0\<close> 
            \<open>P \<noteq> Q0\<close> col_trivial_2 colx not_col_permutation_4)
      ultimately
      show ?thesis 
        by auto
    qed
  }
  thus ?thesis 
    using inverse_projection_postulate_def by auto
qed

lemma proclus_bis__proclus:
  assumes "alternative_proclus_postulate"
  shows "proclus_postulate" 
proof -
  {
    fix A B C D P Q
    assume "A B Par C D" and
      "Col A B P" and
      "\<not> Col A B Q" and
      "Coplanar C D P Q"
    have "\<exists> Y. Col P Q Y \<and> Col C D Y" 
    proof (cases "Col C D P")
      case True
      thus ?thesis 
        using col_trivial_3 by blast
    next
      case False
      hence "\<not> Col C D P" 
        by simp
      have "C D Par A B" 
        by (simp add: \<open>A B Par C D\<close> par_symmetry)
      hence "C D ParStrict A B" 
        using False \<open>Col A B P\<close> par_not_col_strict by blast
      obtain C0 where "Col C D C0" and "C D Perp P C0" 
        using False l8_18_existence by blast
      have "\<not> Col C0 A B" 
        by (meson \<open>C D ParStrict A B\<close> \<open>Col C D C0\<close> 
            col_permutation_2 par_not_col)
      have "\<exists> A0. Col A B A0 \<and> \<not> Col C0 P A0" 
      proof (cases "Col C0 P A")
        case True
        thus ?thesis 
          by (metis (full_types) \<open>C D ParStrict A B\<close> 
              \<open>Col A B P\<close> \<open>Col C D C0\<close> col_permutation_5 col_trivial_2
              not_col_permutation_1 par_not_col par_strict_col_par_strict)
      next
        case False
        thus ?thesis 
          using col_trivial_3 by blast
      qed
      then obtain A0 where "Col A B A0" and "\<not> Col C0 P A0" 
        by blast
      have "Col C0 P P" 
        by (simp add: col_trivial_2)
      then obtain A' where "C0 P Perp A' P" and "C0 P OS A0 A'" 
        using \<open>\<not> Col C0 P A0\<close> l10_15 by blast
      have "P \<noteq> A0" 
        using \<open>Col C0 P P\<close> \<open>\<not> Col C0 P A0\<close> by blast
      hence "Coplanar C D P A0" 
        by (meson \<open>C D ParStrict A B\<close> \<open>Col A B A0\<close> 
            \<open>Col A B P\<close> par_strict_col2_par_strict
            pars__coplanar)
      show ?thesis  
      proof (cases "Col A0 P A'")
        case True
        show ?thesis 
        proof -
          have "P Perp2 A0 P C D" 
          proof -
            have "Col P C0 P" 
              by (simp add: col_trivial_3)
            moreover
            have "C0 P Perp A0 P" 
              by (metis NCol_perm Perp_perm True 
                  \<open>C0 P Perp A' P\<close> \<open>P \<noteq> A0\<close> perp_col)
            moreover
            have "C0 P Perp C D" 
              using Perp_perm \<open>C D Perp P C0\<close> by blast
            ultimately
            show ?thesis 
              using Perp2_def by blast
          qed
          moreover
          have "\<not>Col C D P" 
            using False by auto
          moreover
          have "Coplanar A0 P C D" 
            by (simp add: \<open>Coplanar C D P A0\<close> coplanar_perm_22)
          moreover
          have "Col A0 P P" 
            by (simp add: col_trivial_2)
          moreover
          have "\<not>Col A0 P Q" 
            by (metis \<open>Col A B A0\<close> \<open>Col A B P\<close> 
                \<open>P \<noteq> A0\<close> \<open>\<not> Col A B Q\<close> colx)
          ultimately
          show ?thesis
            using \<open>Coplanar C D P Q\<close> assms 
              alternative_proclus_postulate_def by simp
        qed
      next
        case False
        hence "\<not> Col A0 P A'" 
          by simp
        have "\<exists> Y. Col P A0 Y \<and> Col C D Y"
        proof -
          have "P Perp2 A' P C D" 
          proof -
            have "Col P C0 P" 
              by (simp add: col_trivial_3)
            moreover
            have "C0 P Perp C D" 
              using Perp_cases \<open>C D Perp P C0\<close> by auto
            ultimately
            show ?thesis 
              using \<open>C0 P Perp A' P\<close> Perp2_def by blast
          qed
          moreover
          have "\<not>Col C D P" 
            by (simp add: \<open>\<not> Col C D P\<close>)
          moreover
          have "Coplanar C D P A0" 
            by (meson \<open>C D ParStrict A B\<close> \<open>Col A B A0\<close>
                \<open>Col A B P\<close> \<open>P \<noteq> A0\<close> par_strict_col2_par_strict
                pars__coplanar)
          have "C0 P OS A0 A'" 
            by (simp add: \<open>C0 P OS A0 A'\<close>)
          hence "Coplanar C0 P A0 A'" 
            by (simp add: os__coplanar)
          hence "Coplanar A' P C D" 
          proof -
            have "Coplanar C0 P A0 A'" 
              by (simp add: \<open>Coplanar C0 P A0 A'\<close>)
            moreover have "Coplanar C0 P A0 P" 
              using ncop_distincts by blast
            moreover have "Coplanar C0 P A0 C" 
              by (metis \<open>Col C D C0\<close> \<open>Coplanar C D P A0\<close> 
                  \<open>\<not> Col C D P\<close> col_cop__cop coplanar_perm_20 
                  coplanar_perm_22 not_col_distincts)
            moreover have "Coplanar C0 P A0 D" 
              by (metis \<open>Col C D C0\<close> \<open>Coplanar C D P A0\<close> 
                  calculation(3) col_cop2__cop coplanar_perm_21 
                  coplanar_perm_22 ncop_distincts)
            ultimately show ?thesis 
              using \<open>\<not> Col C0 P A0\<close> coplanar_pseudo_trans by blast
          qed
          moreover
          have "Col A' P P" 
            by (simp add: col_trivial_2)
          moreover
          have "\<not> Col A' P A0" 
            by (simp add: False not_col_permutation_3)
          ultimately
          show ?thesis 
            using \<open>Coplanar C D P A0\<close> assms 
              alternative_proclus_postulate_def by simp
        qed
        then obtain Y where "Col P A0 Y" and "Col C D Y" 
          by auto
        have "C D ParStrict A B" 
          by (simp add: \<open>C D ParStrict A B\<close>)
        moreover
        have "Col Y C D" 
          using Col_cases \<open>Col C D Y\<close> by blast
        moreover
        have "Col Y A B" 
          by (meson \<open>Col A B A0\<close> \<open>Col A B P\<close> \<open>Col P A0 Y\<close>
              \<open>P \<noteq> A0\<close> colx not_col_permutation_1)
        ultimately
        have "False" 
          using par_not_col by simp
        thus ?thesis 
          by simp
      qed
    qed
  }
  thus ?thesis
    using proclus_postulate_def by blast
qed

lemma proclus_s_postulate_implies_strong_parallel_postulate:
  assumes "proclus_postulate"
  shows "strong_parallel_postulate" 
proof -
  {
    fix P Q R S T U
    assume "BetS P T Q" and
      "BetS R T S" and
      "\<not> Col P R U" and
      "Coplanar P Q R U" and
      "Cong P T Q T" and
      "Cong R T S T"
    have "\<exists> I. Col S Q I \<and> Col P U I"
    proof (cases "Col P Q R")
      case True
      have "Col S Q P" 
        by (metis (full_types) BetS_def Col_cases
            True \<open>BetS P T Q\<close> \<open>BetS R T S\<close> bet_col colx)
      moreover
      have "Col P U P" 
        by (simp add: col_trivial_3)
      ultimately
      show ?thesis 
        by auto
    next
      case False
      show ?thesis 
      proof -
        have "P R Par Q S" 
        proof -
          have "T Midpoint P Q" 
            by (simp add: BetSEq midpoint_def \<open>BetS P T Q\<close>
                \<open>Cong P T Q T\<close> cong_right_commutativity)
          moreover
          have "T Midpoint R S" 
            by (meson BetSEq midpoint_def \<open>BetS R T S\<close>
                \<open>Cong R T S T\<close> not_cong_1243)
          ultimately
          show ?thesis 
            using False not_col_distincts sym_par by blast
        qed
        moreover  
        have "Col P R P" 
          by (simp add: col_trivial_3)
        moreover
        have "Coplanar P Q R S" 
          using calculation(1) coplanar_perm_2 par__coplanar by blast
        hence "Coplanar Q S P U" 
          by (meson False \<open>Coplanar P Q R U\<close> col_permutation_1
              coplanar_trans_1 ncoplanar_perm_8)
        ultimately
        show ?thesis
          using \<open>\<not> Col P R U\<close> assms proclus_postulate_def
            not_col_permutation_4 by blast
      qed
    qed
  }
  thus ?thesis 
    using strong_parallel_postulate_def by blast
qed

lemma rectangle_existence__rah:
  assumes "postulate_of_existence_of_a_right_lambert_quadrilateral"
  shows "postulate_of_right_saccheri_quadrilaterals" 
proof -
  {
    fix A B C D 
    assume "Saccheri A B C D"
    hence "Per A B C" 
      using assms lam_per__rah 
        hypothesis_of_right_saccheri_quadrilaterals_def 
        postulate_of_existence_of_a_right_lambert_quadrilateral_def 
      by blast
  }
  thus ?thesis 
    by (simp add: postulate_of_right_saccheri_quadrilaterals_def)
qed

lemma posidonius_postulate__rah:
  assumes "posidonius_postulate"
  shows "postulate_of_right_saccheri_quadrilaterals" 
proof -
  have "\<exists> A1 A2 B1 B2.
            Per A2 A1 B1 \<and> Per A1 A2 B2 \<and>
            Cong A1 B1 A2 B2 \<and> A1 A2 OS B1 B2 \<and>
           (\<forall> A3 B3.
                 (Col A1 A2 A3 \<and> Col B1 B2 B3 \<and> 
                  A1 A2 Perp A3 B3) 
                   \<longrightarrow> Cong A3 B3 A1 B1)" 
  proof- 
    obtain A1' A2' B1 B2 where
      "\<not> Col A1' A2' B1" and "B1 \<noteq> B2" and 
      "Coplanar A1' A2' B1 B2" and
      H1: "\<forall> A3 A4 B3 B4.
      (Col A1' A2' A3 \<and> Col B1 B2 B3 \<and> A1' A2' Perp A3 B3 \<and>
      Col A1' A2' A4 \<and> Col B1 B2 B4 \<and> A1' A2' Perp A4 B4) \<longrightarrow>
      Cong A3 B3 A4 B4"
      using assms posidonius_postulate_def by blast
    obtain A1 where "Col A1' A2' A1" and "A1' A2' Perp B1 A1" 
      using \<open>\<not> Col A1' A2' B1\<close> l8_18_existence by blast
    have "A1' \<noteq> A2'" 
      using \<open>\<not> Col A1' A2' B1\<close> col_trivial_1 by blast
    have "A1 \<noteq> B1" 
      using \<open>A1' A2' Perp B1 A1\<close> perp_not_eq_2 by blast
    have "A1' A2' ParStrict B1 B2"
    proof -
      {
        assume "\<exists> I. Col I A1' A2' \<and> Col I B1 B2"
        then obtain I where "Col I A1' A2'" and "Col I B1 B2" 
          by blast
        have "B1 \<noteq> I" 
          using \<open>Col I A1' A2'\<close> \<open>\<not> Col A1' A2' B1\<close> 
            not_col_permutation_2 by blast
        obtain B3 where "B3 Midpoint B1 I" 
          using midpoint_existence by presburger
        hence "B1 \<noteq> B3" 
          using \<open>B1 \<noteq> I\<close> l7_3_2 l7_9_bis by blast
        have "Bet B1 B3 I" 
          by (metis midpoint_bet \<open>B3 Midpoint B1 I\<close>)
        hence "Col B1 B3 I" 
          using bet_col by auto
        {
          assume "Col A1' A2' B3"
          have "Col B1 B3 A1'" 
            by (metis \<open>A1' \<noteq> A2'\<close> \<open>B3 Midpoint B1 I\<close> 
                \<open>Col A1' A2' B3\<close> \<open>Col B1 B3 I\<close> \<open>Col I A1' A2'\<close> col2__eq 
                col_permutation_4 midpoint_distinct_1 not_col_distincts)
          moreover
          have "Col B1 B3 A2'"       
            by (metis \<open>A1' \<noteq> A2'\<close> \<open>B3 Midpoint B1 I\<close> 
                \<open>Col A1' A2' B3\<close> \<open>Col B1 B3 I\<close> \<open>Col I A1' A2'\<close> col2__eq
                col_permutation_4 midpoint_distinct_1 not_col_distincts)
          moreover
          have "Col B1 B3 B1" 
            by (simp add: col_trivial_3)
          ultimately
          have "Col A1' A2' B1" 
            using \<open>B1 \<noteq> B3\<close> col3 by blast
          hence False 
            using \<open>\<not> Col A1' A2' B1\<close> by auto
        }
        then obtain A3 where "Col A1' A2' A3" and "A1' A2' Perp B3 A3" 
          using l8_18_existence by blast
        have "Cong A1 B1 A3 B3" 
        proof -
          have "Col A1' A2' A1" 
            by (simp add: \<open>Col A1' A2' A1\<close>)
          moreover
          have "Col B1 B2 B1" 
            using col_trivial_3 by blast
          moreover
          have "A1' A2' Perp A1 B1" 
            using Perp_cases \<open>A1' A2' Perp B1 A1\<close> by blast
          moreover  
          have "Col A1' A2' A3" 
            by (simp add: \<open>Col A1' A2' A3\<close>)
          moreover
          have "Col B1 B2 B3" 
            by (metis \<open>B1 \<noteq> I\<close> \<open>Col B1 B3 I\<close> \<open>Col I B1 B2\<close>
                col_permutation_3 col_permutation_5 col_transitivity_2)
          moreover
          have "A1' A2' Perp A3 B3" 
            using Perp_perm \<open>A1' A2' Perp B3 A3\<close> by blast
          ultimately
          show ?thesis 
            using H1 by blast
        qed
        have "Cong B1 I B3 I" 
        proof -
          {
            assume "A3 = I" 
            have "A3 B3 Perp A1' A2'" 
              using Perp_cases \<open>A1' A2' Perp B3 A3\<close> by blast
            hence "A1' A2' Perp B1 A3" 
              by (metis between_symmetry \<open>A3 = I\<close> \<open>B1 \<noteq> B3\<close>
                  \<open>B1 \<noteq> I\<close> \<open>Bet B1 B3 I\<close> bet_col bet_col1
                  col3 perp_col0)
            hence "A1 = A3" 
              using \<open>A1' A2' Perp B1 A1\<close> \<open>Col A1' A2' A1\<close> 
                \<open>Col A1' A2' A3\<close> l8_18_uniqueness
              by blast
            have "B3 \<noteq> B1" 
              using \<open>B1 \<noteq> B3\<close> by blast
            hence False 
              using \<open>A1 = A3\<close> \<open>A3 = I\<close> \<open>Bet B1 B3 I\<close>
                \<open>Cong A1 B1 A3 B3\<close> between_cong between_symmetry
                cong_inner_transitivity cong_reflexivity by blast
          }
          hence "A3 \<noteq> I" 
            by auto
          have "B3 \<noteq> I" 
            using \<open>B1 \<noteq> I\<close> \<open>B3 Midpoint B1 I\<close>
              midpoint_distinct_1 by blast
          {
            assume "A1 = I"
            hence "A3 = A1" 
            proof -
              have "\<not> Col A1' A2' B3" 
                using \<open>Col A1' A2' B3 \<Longrightarrow> False\<close> by auto
              moreover
              have "A1' A2' Perp B3 A1" 
              proof -
                have "Col B1 A1 B3" 
                  using \<open>A1 = I\<close> \<open>Col B1 B3 I\<close>
                    col_permutation_5 by blast
                moreover
                have "Col B1 A1 A1" 
                  by (simp add: col_trivial_2)
                ultimately
                show ?thesis 
                  using \<open>A1' A2' Perp B1 A1\<close> \<open>Col A1' A2' A1\<close> 
                    \<open>\<not> Col A1' A2' B3\<close> perp_col2_bis by blast
              qed
              ultimately
              show ?thesis 
                using \<open>Col A1' A2' B3 \<Longrightarrow> False\<close> 
                  \<open>Col A1' A2' A3\<close> \<open>A1' A2' Perp B3 A3\<close> \<open>Col A1' A2' A1\<close> 
                  l8_18_uniqueness by blast
            qed
            hence False 
              using \<open>A1 = I\<close> \<open>A3 \<noteq> I\<close> by auto
          }
          hence "A1 \<noteq> I" 
            by blast
          {
            assume "Col B1 A1 I"
            hence "A3 = I" 
              by (metis \<open>A1 = I \<Longrightarrow> False\<close> \<open>Col A1' A2' A1\<close> 
                  \<open>Col I A1' A2'\<close> \<open>\<not> Col A1' A2' B1\<close> 
                  l6_21 not_col_distincts)
            hence False 
              using \<open>A3 \<noteq> I\<close> by blast
          }
          moreover
          have "Bet I A3 A1" 
          proof -
            have "A3 B3 TS I A1" 
            proof -
              have "\<not> Col A3 B3 B1" 
                by (meson \<open>A3 = I \<Longrightarrow> False\<close> \<open>B1 \<noteq> B3\<close> 
                    \<open>Col A1' A2' A3\<close> \<open>Col B1 B3 I\<close> \<open>Col I A1' A2'\<close> 
                    \<open>\<not> Col A1' A2' B1\<close> col_permutation_3 
                    col_permutation_4 l6_21)
              have "A3 B3 TS B1 I" 
                using Col_perm \<open>B3 \<noteq> I\<close> \<open>Bet B1 B3 I\<close> 
                  \<open>\<not> Col A3 B3 B1\<close> bet__ts 
                  invert_two_sides by blast
              moreover
              have "A3 B3 OS B1 A1" 
              proof -
                have "A3 B3 Par B1 A1" 
                proof -
                  have "Coplanar A1' A2' A3 B1" 
                    by (simp add: \<open>Col A1' A2' A3\<close> col__coplanar)
                  moreover
                  have "Coplanar A1' A2' A3 A1" 
                    using \<open>Col A1' A2' A3\<close> ncop__ncols by blast
                  moreover
                  have "Coplanar A1' A2' B3 B1" 
                    using Coplanar_def \<open>Col B1 B3 I\<close> 
                      \<open>Col I A1' A2'\<close> col_permutation_4 
                      not_col_permutation_2 by blast
                  moreover
                  have "Coplanar A1' A2' B3 A1" 
                    using \<open>Col A1' A2' A1\<close> ncop__ncols by blast
                  moreover
                  have "A3 B3 Perp A1' A2'" 
                    using Perp_perm \<open>A1' A2' Perp B3 A3\<close> by blast
                  moreover
                  have "B1 A1 Perp A1' A2'" 
                    using Perp_perm \<open>A1' A2' Perp B1 A1\<close> by blast
                  ultimately
                  show ?thesis 
                    using l12_9 by blast
                qed
                moreover
                have "Col B1 A1 B1" 
                  by (simp add: col_trivial_3)
                ultimately
                show ?thesis 
                  by (meson  \<open>\<not> Col A3 B3 B1\<close> col_trivial_2 
                      par_not_col_strict par_strict_one_side)
              qed
              ultimately
              show ?thesis 
                using l9_2 l9_8_2 by blast
            qed
            moreover
            have "Col A1' A2' I" 
              using \<open>Col I A1' A2'\<close> not_col_permutation_2 by blast
            hence "Col A3 I A1" 
              using  \<open>Col A1' A2' A3\<close>  \<open>Col A1' A2' A1\<close> 
                \<open>A1' \<noteq> A2'\<close> col3 by blast
            ultimately
            show ?thesis 
              using col_two_sides_bet by blast
          qed
          hence "I Out A3 A1" 
            by (simp add: \<open>A3 \<noteq> I\<close> bet_out)
          hence "A1 I B1 CongA A3 I B3" 
            by (simp add: \<open>B3 \<noteq> I\<close> \<open>Bet B1 B3 I\<close> bet_out_1 out2__conga)
          moreover
          have "B1 A1 I CongA B3 A3 I" 
          proof -
            have "Per B1 A1 I" 
            proof -
              have "A1' A2' Perp A1 B1" 
                using Perp_cases \<open>A1' A2' Perp B1 A1\<close> by blast
              moreover
              have "Col A1' A2' I" 
                using \<open>Col I A1' A2'\<close> not_col_permutation_2 by blast
              ultimately
              show ?thesis 
                using Perp_cases \<open>Col A1' A2' A1\<close> l8_16_1 by blast
            qed
            moreover
            have "Col A1' A2' I" 
              using Col_perm \<open>Col I A1' A2'\<close> by blast
            hence "Per B3 A3 I" 
              using  \<open>Col A1' A2' A3\<close> \<open>A1' A2' Perp B3 A3\<close> l8_16_1 by blast
            ultimately
            show ?thesis 
              by (metis \<open>A1 \<noteq> B1\<close> \<open>A1 \<noteq> I\<close> \<open>A3 \<noteq> I\<close> 
                  \<open>Cong A1 B1 A3 B3\<close> cong_diff l11_16)
          qed
          moreover
          have "Cong B1 A1 B3 A3" 
            using \<open>Cong A1 B1 A3 B3\<close> not_cong_2143 by blast
          ultimately
          show ?thesis 
            using l11_50_2 by blast
        qed
        have "B3 \<noteq> B1" 
          using \<open>B1 \<noteq> B3\<close> by auto
        hence False 
          by (metis \<open>Bet B1 B3 I\<close> \<open>Col B1 B3 I\<close> 
              \<open>Cong B1 I B3 I\<close> between_equality col_cong2_bet2 
              col_transitivity_1 not_cong_1243)
      }
      thus ?thesis 
        using ParStrict_def \<open>Coplanar A1' A2' B1 B2\<close> by blast
    qed
    hence "\<not> Col A1' A2' B2" 
      using col124__nos l12_6 by blast
    then obtain A2 where "Col A1' A2' A2" and "A1' A2' Perp B2 A2" 
      using l8_18_existence by blast
    {
      assume "A1 = A2" 
      have "A2' A1' ParStrict B2 B1" 
        using \<open>A1' A2' ParStrict B1 B2\<close> par_strict_comm by blast
      hence "\<not> Col A2 B2 B1" 
        using \<open>Col A1' A2' A2\<close> not_col_permutation_3 par_not_col by blast
      moreover
      have "Col A1 B1 B2" 
        using \<open>A1 = A2\<close> Perp_cases \<open>A1' A2' Perp B1 A1\<close> 
          \<open>A1' A2' Perp B2 A2\<close> cop_perp2__col 
          \<open>Coplanar A1' A2' B1 B2\<close> by blast
      ultimately
      have False 
        using \<open>A1 = A2\<close> \<open>\<not> Col A2 B2 B1\<close> not_col_permutation_5 by blast
    }
    hence "A1 \<noteq> A2" 
      by blast
    have "A1' A2' Perp A1 B1" 
      using Perp_cases \<open>A1' A2' Perp B1 A1\<close> by blast
    have "A1' A2' Perp A2 B2" 
      by (simp add: \<open>A1' A2' Perp B2 A2\<close> perp_right_comm)
    have "Per A2 A1 B1" 
      by (meson \<open>Col A1' A2' A1\<close> \<open>Col A1' A2' A2\<close> 
          \<open>A1' A2' Perp A1 B1\<close> \<open>A1 \<noteq> A2\<close> perp_col2 perp_per_2)
    moreover
    have "Per A1 A2 B2" 
      by (metis \<open>Col A1' A2' A1\<close> \<open>Col A1' A2' A2\<close>
          \<open>A1' A2' Perp A2 B2\<close> \<open>A1 \<noteq> A2\<close> 
          perp_col2 perp_per_2)
    moreover
    have "Cong A1 B1 A2 B2" 
    proof -
      have "Col B1 B2 B1"
        by (simp add: col_trivial_3)
      moreover
      have "Col B1 B2 B2" 
        by (simp add: col_trivial_2)
      ultimately
      show ?thesis
        using \<open>Col A1' A2' A1\<close> \<open>Col A1' A2' A2\<close>  
          \<open>A1' A2' Perp A1 B1\<close> \<open>A1' A2' Perp A2 B2\<close> H1 by blast
    qed
    moreover
    have "A1' A2' OS B1 B2" 
      using \<open>A1' A2' ParStrict B1 B2\<close> l12_6 by force
    hence "A1 A2 OS B1 B2" 
      using \<open>Col A1' A2' A1\<close> \<open>Col A1' A2' A2\<close> \<open>A1 \<noteq> A2\<close> col2_os__os by blast
    moreover
    {
      fix A3 B3
      assume "Col A1 A2 A3" and
        "Col B1 B2 B3" and
        "A1 A2 Perp A3 B3"
      have "Col A1' A2' A3" 
        using \<open>A1 \<noteq> A2\<close> \<open>Col A1 A2 A3\<close> \<open>Col A1' A2' A1\<close> 
          \<open>Col A1' A2' A2\<close> colx by blast
      moreover
      have "A1' A2' Perp A3 B3" 
      proof -
        have "Col A1 A2 A1'" 
          by (metis \<open>A1' \<noteq> A2'\<close> \<open>Col A1' A2' A1\<close> 
              \<open>Col A1' A2' A2\<close> col_transitivity_2 
              not_col_permutation_2)
        moreover
        have "Col A1 A2 A2'" 
          by (meson \<open>A1' \<noteq> A2'\<close> \<open>Col A1' A2' A1\<close> 
              \<open>Col A1' A2' A2\<close> col_permutation_1 
              col_transitivity_2)
        ultimately
        show ?thesis 
          using \<open>A1 A2 Perp A3 B3\<close> \<open>A1' \<noteq> A2'\<close> perp_col2 by blast
      qed
      moreover
      have "Col B1 B2 B1" 
        by (simp add:col_trivial_3)
      ultimately
      have "Cong A3 B3 A1 B1" 
        using  \<open>Col B1 B2 B3\<close> \<open>Col A1' A2' A1\<close>
          \<open>A1' A2' Perp A1 B1\<close> H1 by blast
    }
    ultimately
    show ?thesis 
      by blast
  qed
  then obtain A D B C where "Per D A B" and 
    "Per A D C" and "Cong A B D C" and "A D OS B C" and
    H2: "\<forall> A3 B3. (Col A D A3 \<and> Col B C B3 \<and> A D Perp A3 B3) \<longrightarrow> Cong A3 B3 A B"
    by blast
  have "Saccheri A B C D" 
    using Saccheri_def \<open>A D OS B C\<close> \<open>Cong A B D C\<close> 
      \<open>Per A D C\<close> \<open>Per D A B\<close> l8_2 not_cong_1243 by blast
  have "Per A B C" 
  proof -
    obtain M where "M Midpoint B C" 
      using midpoint_existence by blast
    hence "Bet B M C" 
      using midpoint_bet by auto
    moreover
    obtain N where "N Midpoint A D" 
      using midpoint_existence by blast
    hence "Bet A N D" 
      by (simp add: midpoint_bet)
    moreover
    have "A D Perp M N" 
      using mid2_sac__perp_lower \<open>M Midpoint B C\<close> 
        \<open>N Midpoint A D\<close> \<open>Saccheri A B C D\<close> by blast
    have "A \<noteq> N" 
      using \<open>A D Perp M N\<close> \<open>N Midpoint A D\<close> 
        is_midpoint_id perp_distinct by blast
    moreover
    have "N \<noteq> D" 
      by (metis \<open>N Midpoint A D\<close> calculation(3) midpoint_distinct_2)
    moreover
    have "Per M N A" 
    proof -
      have "M N Perp A D" 
        using Perp_cases \<open>A D Perp M N\<close> by blast
      moreover
      have "Col A D N" 
        using \<open>Bet A N D\<close> bet_col col_permutation_5 by blast
      ultimately
      show ?thesis 
        by (meson Perp_cases col_trivial_3 l8_16_1)
    qed
    moreover
    have "Cong M N A B" 
    proof -
      have "Col A D N" 
        using bet_col calculation(2) not_col_permutation_5 by blast
      moreover
      have "Col B C M" 
        by (meson \<open>Bet B M C\<close> bet_col not_col_permutation_5)
      ultimately
      show ?thesis 
        using Cong_perm \<open>A D Perp M N\<close> 
          H2 perp_right_comm by blast
    qed
    ultimately
    show ?thesis 
      using \<open>Saccheri A B C D\<close> t22_7__per by blast
  qed
  thus ?thesis 
    using \<open>Saccheri A B C D\<close> existential_saccheri__rah 
      postulate_of_existence_of_a_right_saccheri_quadrilateral_def 
    by blast
qed

lemma playfair__existential_playfair:
  assumes "playfair_s_postulate" 
  shows "existential_playfair_s_postulate"
proof -
  obtain PA PB PC where "\<not> Bet PA PB PC" and "\<not> Bet PB PC PA" and "\<not> Bet PC PA PB"
    using lower_dim_ex by blast
  hence "\<not> Col PA PB PC" 
    using Col_def by presburger
  moreover
  {
    fix B1 B2 C1 C2
    assume "PA PB Par B1 B2" and "Col PC B1 B2" and
      "PA PB Par C1 C2" and
      "Col PC C1 C2"
    have "Col C1 B1 B2 \<and> Col C2 B1 B2" 
      using assms \<open>Col PC B1 B2\<close> \<open>Col PC C1 C2\<close> \<open>PA PB Par B1 B2\<close> 
        \<open>PA PB Par C1 C2\<close> playfair_s_postulate_def by blast
  }
  ultimately show ?thesis 
    using existential_playfair_s_postulate_def by blast
qed

subsection "Equivalences" 

lemma proclus__aristotle:
  assumes "proclus_postulate" 
  shows "aristotle_s_axiom"
proof -
  {
    fix P Q A B C
    assume "\<not> Col A B C" and
      "Acute A B C"
    have "(Col B A B \<and> \<not> Col B A C) \<longrightarrow> (\<exists> Q. B A Perp Q B \<and> B A OS C Q)" 
      using l10_15 by blast
    then obtain D0 where "B A Perp D0 B" and "B A OS C D0"
      using Col_cases \<open>\<not> Col A B C\<close> col_trivial_3 by blast
    obtain D where "Bet B D0 D" and "Cong D0 D P Q" 
      using segment_construction by blast 
    have "\<not> Col B A D0" 
      using \<open>B A OS C D0\<close> one_side_not_col124 by auto
    have "A \<noteq> B" 
      using \<open>\<not> Col B A D0\<close> col_trivial_1 by blast
    have "D0 \<noteq> B" 
      using \<open>\<not> Col B A D0\<close> col_trivial_3 by auto
    have "B \<noteq> D" 
      using \<open>Bet B D0 D\<close> \<open>D0 \<noteq> B\<close> between_identity by blast
    have "\<not> Col D B A" 
      by (metis \<open>B \<noteq> D\<close> \<open>Bet B D0 D\<close> \<open>\<not> Col B A D0\<close> 
          bet_col col_transitivity_1 not_col_permutation_1)
    have "(Col D B D \<and> \<not> Col D B A) \<longrightarrow> (\<exists> Q. D B Perp Q D \<and> D B OS A Q)" 
      using l10_15 by blast
    then obtain Y0 where "D B Perp Y0 D" and "D B OS A Y0" 
      using \<open>\<not> Col D B A\<close> col_trivial_3 by blast
    have "B A Perp B D" 
      by (metis Perp_perm os_distincts \<open>B A OS C D0\<close> 
          \<open>B A Perp D0 B\<close> \<open>Bet B D0 D\<close> bet_col1 
          bet_neq21__neq l5_1 perp_col1)
    have "B A Par Y0 D" 
    proof -
      have "Coplanar D B B Y0" 
        using ncop_distincts by auto
      moreover
      have "Coplanar D B B D" 
        using ncop_distincts by blast
      moreover
      have "Coplanar D B A Y0" 
        by (meson \<open>D B OS A Y0\<close> inangle__coplanar ncop__ncols 
            ncoplanar_perm_14 ncoplanar_perm_20 one_side_symmetry 
            os_ts__inangle two_sides_cases)
      moreover
      have "Coplanar D B A D" 
        using ncop_distincts by blast
      moreover
      have "B A Perp D B" 
        by (simp add: Perp_perm \<open>B A Perp B D\<close>)
      moreover
      have "Y0 D Perp D B" 
        using Perp_perm \<open>D B Perp Y0 D\<close> by blast
      ultimately
      show ?thesis 
        using l12_9 by blast
    qed
    have "\<exists> Y. Col B C Y \<and> Col Y0 D Y"
    proof -
      have "(B A Par Y0 D \<and> Col B A B \<and> 
             \<not> Col B A C \<and> Coplanar Y0 D B C)
                \<longrightarrow>  
            (\<exists> Y. Col B C Y \<and> Col Y0 D Y)"
        using assms proclus_postulate_def by blast
      moreover
      have "Coplanar Y0 D B C" 
      proof -
        have "Coplanar A D B Y0" 
          using \<open>B A Par Y0 D\<close> ncoplanar_perm_13 
            par__coplanar by blast
        moreover have "Coplanar A D B D" 
          using ncop_distincts by blast
        moreover have "Coplanar A D B B" 
          using ncop_distincts by blast
        moreover have "Coplanar A D B C" 
        proof -
          have "Coplanar A B C D0" 
            using \<open>B A OS C D0\<close> coplanar_perm_6
              os__coplanar by blast
          thus ?thesis 
            using \<open>Bet B D0 D\<close> \<open>D0 \<noteq> B\<close> bet_col 
              col_cop__cop coplanar_perm_2 coplanar_perm_5 by blast
        qed
        ultimately show ?thesis
          using \<open>\<not> Col D B A\<close> col_permutation_1 
            coplanar_pseudo_trans by blast
      qed
      moreover
      have "B A Par Y0 D" 
        using \<open>B A Par Y0 D\<close> by auto
      moreover
      have "Col B A B" 
        by (simp add: col_trivial_3)
      moreover
      have "\<not> Col B A C" 
        using Col_cases \<open>\<not> Col A B C\<close> by blast
      ultimately
      show ?thesis 
        using Col_cases \<open>\<not> Col A B C\<close> col_trivial_3 by blast
    qed
    then obtain Y where "Col B C Y" and "Col Y0 D Y" 
      by blast
    have "B A ParStrict Y0 D" 
      using Col_perm Par_def \<open>B A Par Y0 D\<close> 
        \<open>D B OS A Y0\<close> col124__nos by blast
    have "\<not> Col Y B A" 
      by (meson \<open>B A ParStrict Y0 D\<close> \<open>Col Y0 D Y\<close> 
          col_permutation_2 par_not_col)
    have "\<not> Col A B Y \<longrightarrow> (\<exists> X. Col A B X \<and> A B Perp Y X)" 
      using l8_18_existence by blast
    then obtain X where "Col A B X" and "A B Perp Y X" 
      using Col_cases \<open>\<not> Col Y B A\<close> by blast
    have "B A OS C D" 
      by (meson \<open>B A OS C D0\<close> \<open>Bet B D0 D\<close> \<open>D0 \<noteq> B\<close> 
          bet_out out_out_one_side)
    have "A B C LtA A B D" 
      by (metis \<open>A \<noteq> B\<close> \<open>Acute A B C\<close> \<open>B A Perp D0 B\<close> 
          \<open>B \<noteq> D\<close> \<open>Bet B D0 D\<close> \<open>D0 \<noteq> B\<close> acute_per__lta 
          bet_col per_col perp_per_1)
    {
      assume "Col B C D"
      {
        assume "Bet C B D"
        hence "B A TS C D" 
          using Col_cases \<open>B \<noteq> D\<close> \<open>\<not> Col A B C\<close> bet__ts by blast
        hence False 
          using \<open>B A OS C D\<close> l9_9 by blast
      }
      moreover
      {
        assume "\<not> Bet C B D"
        hence "\<not> A B C CongA A B D" 
          by (metis \<open>A \<noteq> B\<close> \<open>Acute A B C\<close> \<open>B A Perp D0 B\<close>
              \<open>B \<noteq> D\<close> \<open>Bet B D0 D\<close> \<open>D0 \<noteq> B\<close> acute_per__lta 
              bet_col lta_not_conga per_col perp_per_1)
        moreover
        have "A B C CongA A B D" 
        proof -
          have "B Out A A" 
            by (simp add: \<open>A \<noteq> B\<close> out_trivial)
          moreover
          have "B Out D C" 
            using \<open>B A OS C D\<close> \<open>Col B C D\<close> 
              col_one_side_out l6_6 by blast
          ultimately
          show ?thesis 
            by (simp add: out2__conga)
        qed
        ultimately
        have False
          by blast
      }
      ultimately
      have False 
        by blast
    }
    hence "\<not> Col B C D" 
      by auto
    have "Y \<noteq> B" 
      using \<open>\<not> Col Y B A\<close> col_trivial_1 by blast
    have "Y \<noteq> X" 
      using Col_cases \<open>Col A B X\<close> \<open>\<not> Col Y B A\<close> by blast
    have "Y0 \<noteq> D" 
      using \<open>D B OS A Y0\<close> col_trivial_3 one_side_not_col124 by blast
    have "Y \<noteq> D" 
      using \<open>Col B C Y\<close> \<open>\<not> Col B C D\<close> by auto
    have "B A OS C D" 
      using \<open>B A OS C D\<close> by auto
    have "B D ParStrict X Y" 
    proof -
      have "B D Par X Y" 
      proof -
        have "Coplanar B A B X" 
          using ncop_distincts by blast
        moreover
        have "Coplanar B A B Y" 
          using ncop_distincts by auto
        moreover
        have "Coplanar B A D X" 
          using NCol_perm \<open>Col A B X\<close> ncop__ncols by blast
        moreover
        have "Coplanar B A D Y" 
          using \<open>B A ParStrict Y0 D\<close> \<open>Col Y0 D Y\<close> 
            \<open>Y0 \<noteq> D\<close> col2_cop__cop col_trivial_2 
            pars__coplanar by blast
        moreover
        have "B D Perp B A" 
          using Perp_perm \<open>B A Perp B D\<close> by blast
        moreover
        have "X Y Perp B A" 
          using Perp_perm \<open>A B Perp Y X\<close> by blast
        ultimately
        show ?thesis 
          using l12_9 by blast
      qed
      moreover
      have "Col X Y Y" 
        by (simp add: col_trivial_2)
      moreover
      have "\<not> Col B D Y" 
        by (meson \<open>Col B C Y\<close> \<open>Y \<noteq> B\<close> \<open>\<not> Col B C D\<close> 
            col_transitivity_2 not_col_permutation_2)
      ultimately
      show ?thesis 
        using par_not_col_strict by blast
    qed
    have "C InAngle A B D" 
    proof -
      have "A B C LeA A B D" 
        by (simp add: \<open>A B C LtA A B D\<close> lta__lea)
      moreover
      have "A B OS D C" 
        using \<open>B A OS C D\<close> invert_one_side 
          one_side_symmetry by blast
      ultimately
      show ?thesis 
        by (simp add: lea_in_angle)
    qed
    have "B A OS D Y" 
      using \<open>B A ParStrict Y0 D\<close> \<open>Col Y0 D Y\<close> \<open>Y \<noteq> D\<close>
        col_trivial_2 l12_6 par_strict_col2_par_strict by presburger
    hence "B A OS C Y" 
      using \<open>B A OS C D\<close> one_side_transitivity by blast
    have "B Out A X" 
    proof -
      have "Col B A X" 
        using Col_perm \<open>Col A B X\<close> by blast
      moreover
      have "B D OS X A" 
      proof -
        have "B D OS X Y" 
          using \<open>B D ParStrict X Y\<close> l12_6 by auto
        moreover
        have "B D OS Y A" 
          by (meson \<open>B A OS C D\<close> \<open>B A OS C Y\<close> 
              \<open>C InAngle A B D\<close> \<open>Col B C Y\<close> \<open>\<not> Col A B C\<close> 
              \<open>\<not> Col B C D\<close> col_one_side_out col_permutation_5
              in_angle_two_sides invert_two_sides 
              not_col_permutation_4 one_side_symmetry 
              os_ts1324__os out_out_one_side)
        ultimately
        show ?thesis 
          using one_side_transitivity by blast
      qed
      hence "B D OS A X" 
        using one_side_symmetry by blast
      ultimately
      show ?thesis 
        using col_one_side_out by blast
    qed
    moreover
    have "B Out C Y" 
    proof -
      have "D \<noteq> Y" 
        using \<open>Y \<noteq> D\<close> by auto
      moreover
      have "B A ParStrict D Y0" 
        using \<open>B A ParStrict Y0 D\<close> par_strict_right_comm by blast
      moreover
      have "Col D Y0 Y" 
        using Col_perm \<open>Col Y0 D Y\<close> by blast
      ultimately
      show ?thesis 
        using \<open>B A OS C Y\<close> \<open>Col B C Y\<close> col_one_side_out by blast
    qed
    moreover 
    have "\<not> Col B D X" 
      by (metis \<open>Col A B X\<close> \<open>\<not> Col D B A\<close> 
          calculation(1) col_trivial_2 colx 
          not_col_permutation_3 not_col_permutation_5 out_diff2)
    hence "Per B X Y" 
    proof -
      have "B \<noteq> X" 
        using \<open>\<not> Col B D X\<close> col_trivial_3 by auto
      moreover
      have "B A Perp Y X" 
        using Perp_perm \<open>A B Perp Y X\<close> by blast
      moreover
      have "Col B A X" 
        by (simp add: \<open>B Out A X\<close> out_col)
      ultimately
      show ?thesis 
        using Per_perm col_trivial_3 l8_16_1 by blast
    qed
    moreover
    have "X \<noteq> B" 
      using \<open>\<not> Col B D X\<close> col_trivial_3 by auto
    have "Cong B D X Y" 
    proof -
      have "(\<not> Col B Y D \<and> Y D B CongA B X Y \<and> 
             B Y D CongA Y B X \<and> Cong B Y Y B) 
         \<longrightarrow> 
             (Cong B D Y X \<and> Cong Y D B X \<and> D B Y CongA X Y B)" 
        using l11_50_2 by blast
      moreover
      have "\<not> Col B Y D" 
        by (metis \<open>Col Y0 D Y\<close> \<open>D B OS A Y0\<close> \<open>Y \<noteq> D\<close> 
            col124__nos col_transitivity_1 
            not_col_permutation_2)
      moreover
      have "Per Y D B" 
      proof -
        have "D Y0 Perp D B" 
          using Perp_perm \<open>D B Perp Y0 D\<close> by blast
        moreover
        have "Col D Y0 Y" 
          using Col_perm \<open>Col Y0 D Y\<close> by blast
        ultimately
        show ?thesis 
          using \<open>Y \<noteq> D\<close> perp_col perp_per_2 by presburger
      qed
      hence "Y D B CongA B X Y" 
        using \<open>Per B X Y\<close> \<open>B \<noteq> D\<close> \<open>X \<noteq> B\<close> \<open>Y \<noteq> D\<close> 
          \<open>Y \<noteq> X\<close> l11_16 by blast
      moreover
      have "D Y B CongA X B Y" 
      proof -
        have "Y B TS X D" 
        proof -
          have "Y B TS A D" 
          proof -
            have "Col C B Y" 
              using Col_perm \<open>Col B C Y\<close> by blast
            moreover
            have "Col C B B" 
              using col_trivial_2 by auto
            moreover
            have "C B TS A D" 
              using Col_cases \<open>B A OS C D\<close> 
                \<open>C InAngle A B D\<close> \<open>Col B C D \<Longrightarrow> False\<close> 
                col123__nos in_angle_two_sides by blast
            ultimately
            show ?thesis 
              using \<open>Y \<noteq> B\<close> col_preserves_two_sides by blast
          qed
          moreover
          have "\<not> Col B Y A \<or> \<not> Col B Y X" 
            using Col_cases \<open>\<not> Col Y B A\<close> by blast
          hence "Y B OS A X" 
            by (meson  \<open>B Out A X\<close> \<open>Y B TS A D\<close> 
                invert_one_side l9_8_1 out_out_one_side)
          ultimately
          show ?thesis 
            using l9_8_2 by blast
        qed
        hence "Y B TS D X" 
          using l9_2 by blast
        moreover
        have "D Y0 Par B A" 
          using Par_perm \<open>B A Par Y0 D\<close> by blast
        hence "D Y Par B A" 
          by (metis \<open>Col Y0 D Y\<close> \<open>Y \<noteq> D\<close> 
              not_col_permutation_4 par_col_par par_symmetry)
        hence "D Y Par B X" 
          by (metis \<open>Col A B X\<close> \<open>X \<noteq> B\<close> 
              col_permutation_4 par_col_par)
        hence "Y D Par B X" 
          using Par_perm by blast
        moreover
        have "alternate_interior_angles_postulate" 
          by (simp add: assms 
              playfair__alternate_interior 
              proclus_s_postulate_implies_strong_parallel_postulate
              strong_parallel_postulate_implies_tarski_s_euclid
              tarski_s_euclid_implies_playfair_s_postulate)
        ultimately
        show ?thesis 
          using alternate_interior_angles_postulate_def by blast
      qed
      hence "B Y D CongA Y B X" 
        by (simp add: conga_comm)
      moreover
      have "Cong B Y Y B" 
        by (simp add: cong_pseudo_reflexivity)
      ultimately
      show ?thesis 
        using not_cong_1243 by blast
    qed
    have "P Q Lt X Y" 
    proof -
      have "P Q Le B D" 
        by (meson \<open>Bet B D0 D\<close> \<open>Cong D0 D P Q\<close> 
            bet__le2313 cong__le3412 le_transitivity)
      hence "P Q Le X Y" 
        using \<open>Bet B D0 D\<close> \<open>Cong B D X Y\<close> \<open>Cong D0 D P Q\<close> 
          bet__le2313 l5_6 by blast
      moreover
      have "\<not> Cong P Q X Y" 
        by (metis \<open>Bet B D0 D\<close> \<open>Cong B D X Y\<close> 
            \<open>Cong D0 D P Q\<close> \<open>D0 \<noteq> B\<close> bet_le_eq 
            cong__le cong_symmetry l5_6)
      ultimately
      show ?thesis 
        using Lt_def by blast
    qed
    ultimately
    have "\<exists> X Y. B Out A X \<and> B Out C Y \<and> Per B X Y \<and> P Q Lt X Y" 
      by blast
  }
  thus ?thesis 
    using aristotle_s_axiom_def by blast
qed

(** This proof is inspired by Several topics from geometry, by Franz Rothe *)

lemma aristotle__obtuse_case_elimination:
  assumes "aristotle_s_axiom"
  shows "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" 
proof -
  {
    assume "hypothesis_of_obtuse_saccheri_quadrilaterals" 
    obtain Q' C' P Q where "Lambert Q' C' P Q" 
      using ex_lambert by blast
    have "Obtuse C' P Q" 
      using \<open>HypothesisObtuseSaccheriQuadrilaterals\<close> 
        \<open>Lambert Q' C' P Q\<close> lam_obtuse__oah by blast
    have "Q' Q ParStrict C' P" 
      using lam__pars1423 \<open>Lambert Q' C' P Q\<close> by force
    have "\<exists> A'. P Q Perp A' P \<and> P Q OS C' A'"
    proof -
      have "Col P Q P" 
        by (simp add: col_trivial_3)
      moreover
      have "\<not> Col P Q C'" 
        by (meson Par_strict_cases \<open>Q' Q ParStrict C' P\<close>
            not_col_distincts not_col_permutation_4 par_not_col)
      ultimately
      show ?thesis 
        using l10_15 by force
    qed
    then obtain A' where "P Q Perp A' P" and "P Q OS C' A'" 
      by blast
    have "Q P A' LtA C' P Q" 
    proof -
      have "Obtuse C' P Q" 
        by (simp add: \<open>Obtuse C' P Q\<close>)
      moreover
      have "Q \<noteq> P" 
        using calculation obtuse_distincts by blast
      moreover
      have "P \<noteq> A'" 
        using \<open>P Q Perp A' P\<close> perp_not_eq_2 by blast
      moreover
      have "Per Q P A'" 
        using \<open>P Q Perp A' P\<close> perp_per_1 by auto
      ultimately
      show ?thesis 
        by (simp add: obtuse_per__lta)
    qed
    have "Q P A' LeA C' P Q" 
      by (simp add: \<open>Q P A' LtA C' P Q\<close> lta__lea)
    have "\<not> Q P A' CongA C' P Q" 
      by (simp add: \<open>Q P A' LtA C' P Q\<close> lta_not_conga)
    have "A' InAngle Q P C'" 
    proof -
      have "Q P A' LeA Q P C'" 
        by (simp add: \<open>Q P A' LeA C' P Q\<close> lea_right_comm)
      moreover
      have "Q P OS C' A'" 
        by (simp add: \<open>P Q OS C' A'\<close> invert_one_side)
      ultimately
      show ?thesis 
        by (simp add: lea_in_angle)
    qed
    obtain C where "Bet C' P C" and "Cong P C C' P" 
      by (metis between_inner_transitivity 
          outer_transitivity_between 
          point_construction_different segment_construction_2)
    obtain A where "Bet A' P A" and "Cong P A A' P" 
      by (metis between_inner_transitivity 
          outer_transitivity_between point_construction_different 
          segment_construction_2)
    have "C InAngle A P Q" 
    proof -
      {
        assume "A = P"
        hence "A' = A" 
          using \<open>Cong P A A' P\<close> cong_diff_3 by blast
        hence "A' = P" 
          by (simp add: \<open>A = P\<close>)
        hence False 
          using \<open>P Q Perp A' P\<close> perp_not_eq_2 by blast
      }
      hence "A \<noteq> P" 
        by auto
      moreover
      have "Bet A' P A" 
        by (simp add: \<open>Bet A' P A\<close>)
      moreover
      have "Q InAngle A' P C" 
      proof -
        {
          assume "C = P"
          hence "C = C'" 
            using \<open>Cong P C C' P\<close> cong_diff_4 by blast
          hence "C' = P" 
            using \<open>C = P\<close> by blast
          hence False 
            using \<open>Obtuse C' P Q\<close> obtuse_distincts by blast
        }
        hence "C \<noteq> P" 
          by blast
        moreover
        have "A' InAngle C' P Q" 
          using \<open>A' InAngle Q P C'\<close> l11_24 by blast
        ultimately
        show ?thesis 
          by (meson \<open>Bet C' P C\<close> in_angle_reverse l11_24)
      qed
      ultimately
      show ?thesis 
        using in_angle_reverse by blast
    qed
    {
      assume "Col P C' A'"
      have "P Out Q Q" 
        using \<open>C InAngle A P Q\<close> inangle_distincts out_trivial by blast
      moreover
      have "P Out C' A'" 
        using \<open>Col P C' A'\<close> \<open>P Q OS C' A'\<close> col_one_side_out by auto
      ultimately
      have False 
        using conga_right_comm by (meson \<open>\<not> Q P A' CongA C' P Q\<close> out2__conga)
    }
    hence "\<not> Col P C' A'" 
      by blast
    have "\<not> Col P C A" 
      by (metis \<open>Bet A' P A\<close> \<open>Bet C' P C\<close> 
          \<open>Col P C' A' \<Longrightarrow> False\<close> \<open>Cong P A A' P\<close> \<open>Cong P C C' P\<close>
          bet_col bet_col1 col_permutation_4 
          col_permutation_5 colx cong_diff_4)
    have "\<not> Col P Q C" 
      by (metis (no_types, lifting) \<open>Bet C' P C\<close> 
          \<open>Cong P C C' P\<close> \<open>P Q OS C' A'\<close> bet_col bet_cong_eq 
          col_permutation_1 col_transitivity_1 
          one_side_not_col123)
    have "Per A P Q" 
      by (metis Perp_cases \<open>Bet A' P A\<close> \<open>P Q Perp A' P\<close>
          bet_col bet_col1 l8_20_1_R1 perp_col2 perp_per_2)
    have "A P OS C Q" 
      by (metis \<open>Bet A' P A\<close> \<open>C InAngle A P Q\<close> 
          \<open>P Q OS C' A'\<close> \<open>\<not> Col P C A\<close> bet_col col124__nos 
          col_permutation_5 colx in_angle_one_side 
          not_col_distincts)
    have "\<exists> X Y. P Out A X \<and> P Out C Y \<and> Per P X Y \<and> P Q Lt X Y" 
    proof -
      have "\<not> Col A P C" 
        using \<open>\<not> Col P C A\<close> not_col_permutation_2 by blast
      moreover
      have "A P C LtA A P Q" 
      proof -
        have "A P C LeA A P Q" 
          by (simp add: \<open>C InAngle A P Q\<close> inangle__lea)
        moreover
        {
          assume "A P C CongA A P Q" 
          have "A P OS C Q" 
            by (simp add: \<open>A P OS C Q\<close>)
          hence "P Out C Q" 
            using conga_os__out \<open>A P C CongA A P Q\<close> by blast
          hence "Col P Q C" 
            by (meson not_col_permutation_5 out_col)
          hence False 
            using \<open>\<not> Col P Q C\<close> by auto
        }
        hence "\<not> A P C CongA A P Q" 
          by blast
        ultimately
        show ?thesis 
          by (simp add: LtA_def)
      qed
      hence "Acute A P C" 
        using \<open>Per A P Q\<close> Acute_def by blast
      ultimately
      show ?thesis 
        using aristotle_s_axiom_def assms by blast
    qed
    then obtain X Y where "P Out A X" and "P Out C Y"
      and "Per P X Y" and "P Q Lt X Y"
      by blast
    have "\<not> Col P Q Y" 
      by (metis Out_def \<open>P Out C Y\<close> \<open>\<not> Col P Q C\<close>
          colx not_col_distincts out_col)
    then obtain Z where "Col P Q Z" and "P Q Perp Y Z" 
      using l8_18_existence by blast
    have "X Y Lt P Q" 
    proof -
      have "X Y Lt P Z" 
      proof -
        {
          assume "P = Z" 
          have "P \<noteq> Y" 
            using \<open>\<not> Col P Q Y\<close> not_col_distincts by blast
          moreover
          have "Per Q P Y"
            using \<open>P = Z\<close> \<open>P Q Perp Y Z\<close> perp_per_1 by auto
          moreover
          have "Col P Y C" 
            using \<open>P Out C Y\<close> l6_6 out_col by blast
          ultimately
          have "Per Q P C" 
            using per_col by blast
          have "Col P C A" 
          proof -
            have "Coplanar P Q C A" 
              by (meson \<open>C InAngle A P Q\<close> 
                  inangle__coplanar ncoplanar_perm_16)
            moreover
            have "P C Perp P Q" 
              using \<open>Per Q P C\<close> 
              by (metis Perp_perm os_distincts out_distinct
                  \<open>P Out C Y\<close> \<open>P Q OS C' A'\<close> per_perp)
            moreover
            have "P A Perp P Q" 
              by (metis Perp_cases bet_col1 l5_1
                  \<open>Bet A' P A\<close> \<open>Cong P A A' P\<close> \<open>P Q Perp A' P\<close> 
                  bet_cong_eq perp_col2 perp_distinct)
            ultimately
            show ?thesis 
              using cop_perp2__col by blast
          qed
          hence False 
            using \<open>\<not> Col P C A\<close> by auto
        }
        hence "P \<noteq> Z" 
          by blast
        have "Lambert P X Y Z" 
        proof -
          have "P \<noteq> X" 
            using \<open>P Out A X\<close> out_diff2 by blast
          moreover
          have "X \<noteq> Y" 
            using \<open>P Q Lt X Y\<close> lt_diff by blast
          moreover
          have "Y \<noteq> Z" 
            using \<open>Col P Q Z\<close> \<open>\<not> Col P Q Y\<close> by blast
          moreover
          have "P \<noteq> Z" 
            using \<open>P \<noteq> Z\<close> by blast
          moreover
          have "Per X P Z" 
          proof -
            have "P \<noteq> Q" 
              using \<open>\<not> Col P Q Y\<close> col_trivial_1 by force
            moreover
            have "Per X P Q" 
              by (metis out_distinct \<open>P Out A X\<close> \<open>Per A P Q\<close> l8_3 out_col)
            ultimately
            show ?thesis 
              using \<open>Col P Q Z\<close> per_col by blast
          qed
          moreover
          have "Per P Z Y" 
          proof -
            have "P \<noteq> Z" 
              using calculation(4) by blast
            moreover
            have "P Q Perp Y Z" 
              using \<open>P Q Perp Y Z\<close> by auto
            ultimately
            show ?thesis 
              by (meson \<open>Col P Q Z\<close> perp_col perp_comm perp_per_2)
          qed
          moreover
          have "Y InAngle X P Q" 
          proof -
            have "P Out X A" 
              using Out_cases \<open>P Out A X\<close> by blast
            moreover
            have "P Out Q Q" 
              using \<open>A' InAngle Q P C'\<close> inangle_distincts out_trivial by blast
            moreover
            have "P Out Y C" 
              by (simp add: \<open>P Out C Y\<close> l6_6)
            ultimately
            show ?thesis 
              using \<open>C InAngle A P Q\<close> l11_25 by blast
          qed
          hence "Coplanar P X Y Z" 
            using \<open>Col P Q Z\<close> \<open>\<not> Col P Q Y\<close> col_cop__cop 
              inangle__coplanar ncoplanar_perm_14 
              not_col_distincts by blast
          ultimately
          show ?thesis 
            using Lambert_def \<open>Per P X Y\<close> by blast
        qed
        hence "Obtuse X Y Z" 
          using \<open>HypothesisObtuseSaccheriQuadrilaterals\<close>
            lam_obtuse__oah_2 by blast
        thus ?thesis 
          by (simp add: \<open>Lambert P X Y Z\<close> lam_obtuse__lt)
      qed
      moreover
      have "P Z Lt P Q" 
      proof -
        have "Q Out P Z" 
        proof -
          have "Col Q P Z" 
            using Col_cases \<open>Col P Q Z\<close> by auto
          moreover
          have "Q Q' OS P Z" 
          proof -
            have "Q Q' ParStrict P Y" 
              by (metis \<open>Bet C' P C\<close> \<open>P Out C Y\<close> 
                  \<open>Q' Q ParStrict C' P\<close> \<open>\<not> Col P Q C\<close>
                  bet_col not_col_distincts out_col 
                  out_diff2 par_strict_col2_par_strict 
                  par_strict_left_comm)
            hence "Q Q' OS P Y" 
              using l12_6 by blast
            moreover
            have "Q Q' OS Y Z" 
            proof -
              have "Q Q' Par Y Z" 
              proof -
                have "Coplanar P Q Q Y" 
                  using ncop_distincts by blast
                moreover
                have "Coplanar P Q Q Z" 
                  using ncop_distincts by blast
                moreover
                have "Coplanar P Q Q' Y" 
                  by (meson \<open>Q Q' OS P Y\<close> cop2_os__osp
                      ncop_distincts one_side_symmetry osp_distincts)
                moreover
                have "Coplanar P Q Q' Z" 
                  using \<open>Col P Q Z\<close> ncop__ncols by blast
                moreover
                have "Lambert Q' C' P Q" 
                  by (simp add: \<open>Lambert Q' C' P Q\<close>)
                hence "Per C' Q' Q \<and> Per Q' Q P \<and> Per Q' C' P" 
                  using Lambert_def by blast
                hence "Q Q' Perp P Q" 
                  by (metis os_distincts \<open>Lambert Q' C' P Q\<close> 
                      \<open>P Q OS C' A'\<close> lam__os per_perp perp_comm)
                moreover
                have "Y Z Perp P Q" 
                  by (meson Perp_perm \<open>P Q Perp Y Z\<close>)
                ultimately
                show ?thesis 
                  using l12_9 by blast
              qed
              moreover
              have "Col Y Z Y" 
                by (simp add: col_trivial_3)
              moreover
              have "\<not> Col Q Q' Y" 
              proof -
                have "P C' ParStrict Q Q'" 
                  using Par_strict_perm \<open>Q' Q ParStrict C' P\<close> by blast
                moreover
                have "Col Y P C" 
                  using \<open>P Out C Y\<close> not_col_permutation_1 out_col by blast
                ultimately
                show ?thesis 
                  using \<open>Q Q' OS P Y\<close> one_side_not_col124 by blast
              qed
              ultimately
              show ?thesis 
                by (meson l12_6 par_not_col_strict)
            qed
            ultimately
            show ?thesis 
              using one_side_transitivity by blast
          qed
          ultimately
          show ?thesis 
            using col_one_side_out by blast
        qed
        have "P Out Z Q" 
        proof -
          have "Col P Z Q" 
            using NCol_perm \<open>Col P Q Z\<close> by blast
          moreover
          have "P A OS Z Q" 
          proof -
            have "P A OS Z Y" 
            proof -
              have "P A Par Z Y" 
              proof -
                have "Coplanar P Q P Z" 
                  using ncop_distincts by blast
                moreover
                have "Coplanar P Q P Y" 
                  using ncop_distincts by blast
                moreover
                have "Coplanar P Q A Z" 
                  using \<open>Col P Q Z\<close> ncop__ncols by blast
                moreover
                have "Coplanar P Q A Y" 
                proof -
                  have "Coplanar Q A P C" 
                    by (meson \<open>C InAngle A P Q\<close> inangle__coplanar ncoplanar_perm_21)
                  moreover
                  have "P \<noteq> C" 
                    using \<open>\<not> Col P C A\<close> not_col_distincts by blast
                  ultimately
                  show ?thesis 
                    by (meson \<open>P Out C Y\<close> col_cop__cop 
                        ncoplanar_perm_8 out_col)
                qed
                moreover
                have "P A Perp P Q" 
                  by (metis Perp_cases \<open>Bet A' P A\<close> 
                      \<open>Cong P A A' P\<close> \<open>P Q Perp A' P\<close> bet_col 
                      bet_col1 cong_diff_3 perp_col2)
                moreover
                have "Z  Y Perp P Q" 
                  using Perp_perm \<open>P Q Perp Y Z\<close> by blast
                ultimately
                show ?thesis 
                  using l12_9 by blast
              qed
              moreover
              have "Col Z Y Y" 
                using col_trivial_2 by auto
              moreover
              have "\<not> Col P A Y" 
                by (metis Out_def \<open>P Out C Y\<close> \<open>\<not> Col P C A\<close> 
                    colx not_col_distincts 
                    not_col_permutation_5 out_col)
              ultimately
              show ?thesis 
                using l12_6 par_not_col_strict by blast
            qed
            moreover
            have "P A OS Y Q" 
              by (meson \<open>A P OS C Q\<close> \<open>P Out C Y\<close> 
                  invert_one_side not_col_distincts os_out_os)
            ultimately
            show ?thesis 
              using one_side_transitivity by blast
          qed
          ultimately
          show ?thesis 
            using col_one_side_out by blast
        qed
        hence "Bet P Z Q" 
          using \<open>Q Out P Z\<close> out2__bet by blast
        thus ?thesis 
          by (metis \<open>P Q Lt X Y\<close> bet__lt1213 calculation lt_transitivity)
      qed
      ultimately
      show ?thesis 
        by (meson lt_transitivity)
    qed
    hence False 
      using \<open>P Q Lt X Y\<close> not_and_lt by blast
  }
  thus ?thesis 
    by auto
qed


lemma aristotle__acute_or_right:
  assumes "aristotle_s_axiom" 
  shows "hypothesis_of_acute_saccheri_quadrilaterals 
           \<or> 
         hypothesis_of_right_saccheri_quadrilaterals" 
proof -
  {
    assume "hypothesis_of_obtuse_saccheri_quadrilaterals" 
    have "hypothesis_of_acute_saccheri_quadrilaterals \<or> 
          hypothesis_of_right_saccheri_quadrilaterals" 
      using aristotle__obtuse_case_elimination assms
        saccheri_s_three_hypotheses by blast
  }
  thus ?thesis
    using saccheri_s_three_hypotheses 
      aristotle__obtuse_case_elimination assms by blast
qed

lemma Axiom1ProofIsabelleHOL:
  shows "Axiom1" 
  using Axiom1_def by blast

theorem equivalent_postulates_without_decidability_of_intersection_of_lines:
  shows "(Postulate07 \<longleftrightarrow> Postulate12) \<and> 
         (Postulate12 \<longleftrightarrow> Postulate08) \<and>
         (Postulate08 \<longleftrightarrow> Postulate06) \<and> 
         (Postulate06 \<longleftrightarrow> Postulate09) \<and>
         (Postulate09 \<longleftrightarrow> Postulate02) \<and> 
         (Postulate02 \<longleftrightarrow> Postulate11) \<and>
         (Postulate11 \<longleftrightarrow> Postulate10) \<and> 
         (Postulate10 \<longleftrightarrow> Postulate05)" 
proof - 
  have "Postulate09 \<longleftrightarrow> Postulate10" 
  proof -
    have "Postulate09 \<longrightarrow> Postulate10" 
      using Postulate09_def Postulate10_def 
        par_perp_perp_implies_par_perp_2_par by auto
    moreover
    have "Postulate10 \<longrightarrow> Postulate09" 
      using Postulate09_def Postulate10_def 
        par_perp_2_par_implies_par_perp_perp by blast
    ultimately
    show ?thesis
      by blast
  qed
  moreover
  have "Postulate09 \<longrightarrow> Postulate02" 
    by (simp add: Postulate02_def Postulate09_def 
        par_perp_perp_implies_playfair)
  moreover
  have "Postulate02 \<longrightarrow> Postulate11" 
    using Postulate02_def Postulate11_def 
      playfair__universal_posidonius_postulate by blast
  moreover
  have "Postulate11 \<longrightarrow> Postulate09" 
    by (simp add: Postulate09_def Postulate11_def 
        universal_posidonius_postulate__perpendicular_transversal_postulate)
  moreover
  have "Postulate02 \<longleftrightarrow> Postulate05" 
  proof -
    have "Postulate02 \<longrightarrow> Postulate05" 
      using Postulate02_def Postulate05_def 
        playfair_implies_par_trans by auto
    moreover
    have "Postulate05 \<longrightarrow> Postulate02" 
      using Postulate02_def Postulate05_def 
        par_trans_implies_playfair by blast
    ultimately
    show ?thesis 
      by blast
  qed
  moreover
  have "Postulate02 \<longrightarrow> Postulate07" 
    using Postulate07_def Postulate11_def calculation(3) 
      par_perp_perp_implies_playfair playfair__alternate_interior 
      universal_posidonius_postulate__perpendicular_transversal_postulate by blast
  moreover
  have "Postulate07 \<longrightarrow> Postulate12" 
    using Postulate07_def Postulate12_def 
      alternate_interior__playfair_bis by blast
  moreover
  have "Postulate12 \<longrightarrow> Postulate02" 
    using Postulate11_def Postulate12_def calculation(2) 
      calculation(4) playfair__universal_posidonius_postulate 
      playfair_bis__playfair by blast
  moreover
  have "Postulate07 \<longleftrightarrow> Postulate08" 
  proof -
    have "Postulate07 \<longrightarrow> Postulate08" 
      using Postulate07_def Postulate08_def 
        alternate_interior__consecutive_interior by auto
    moreover
    have "Postulate08 \<longrightarrow> Postulate07" 
      using Postulate07_def Postulate08_def 
        consecutive_interior__alternate_interior by blast
    ultimately
    show ?thesis
      by blast
  qed
  moreover
  have "Postulate02 \<longleftrightarrow> Postulate06"
  proof -
    have "Postulate02 \<longrightarrow> Postulate06" 
      using Postulate02_def Postulate06_def 
        playfair_s_postulate_implies_midpoint_converse_postulate by blast
    moreover
    have "Postulate06 \<longrightarrow> Postulate02" 
      using Postulate02_def Postulate06_def 
        midpoint_converse_postulate_implies_playfair by auto
    ultimately
    show ?thesis
      by blast
  qed
  ultimately
  show ?thesis 
    by blast
qed

lemma Cycle_1:
  shows "(Postulate01 \<longrightarrow> Postulate02) \<and> 
         (Postulate09 \<longrightarrow> Postulate15) \<and>
         (Postulate15 \<longrightarrow> Postulate01)" 
proof -
  have "Postulate01 \<longrightarrow> Postulate02" 
    by (simp add: Postulate01_def Postulate02_def 
        tarski_s_euclid_implies_playfair_s_postulate)
  moreover
  have "Postulate09 \<longrightarrow> Postulate15" 
    using inter_dec_plus_par_perp_perp_imply_triangle_circumscription 
      Postulate09_def Postulate15_def by fastforce
  moreover
  have "Postulate15 \<longrightarrow> Postulate01" 
    by (simp add: Postulate01_def Postulate15_def 
        triangle_circumscription_implies_tarski_s_euclid)
  ultimately
  show ?thesis 
    by auto
qed

lemma Cycle_2:
  shows "(Postulate01 \<longleftrightarrow> Postulate13) \<and> 
         (Postulate13 \<longleftrightarrow> Postulate14) \<and>
         (Postulate14 \<longleftrightarrow> Postulate16) \<and> 
         (Postulate16 \<longleftrightarrow> Postulate17) \<and> 
         (Postulate17 \<longleftrightarrow> Postulate18) \<and>
         (Postulate18 \<longleftrightarrow> Postulate19) \<and> 
         (Postulate19 \<longleftrightarrow> Postulate20) \<and> 
         (Postulate20 \<longleftrightarrow> Postulate01)"
proof -
  have "Postulate01 \<longrightarrow> Postulate17" 
    using Postulate01_def Postulate17_def 
      tarski_s_euclid_implies_euclid_5 by blast
  moreover
  have "Postulate17 \<longrightarrow> Postulate20" 
    by (simp add: Postulate17_def Postulate20_def 
        euclid_5__original_euclid)
  moreover
  have "Postulate20 \<longrightarrow> Postulate19" 
    using Postulate19_def Postulate20_def 
      original_euclid__original_spp by blast
  moreover
  have "Postulate19 \<longrightarrow> Postulate16" 
    by (simp add: Postulate16_def Postulate19_def 
        original_spp__inverse_projection_postulate)
  moreover
  have "Postulate16 \<longrightarrow> Postulate14" 
    using Postulate14_def Postulate16_def 
      inverse_projection_postulate__proclus_bis by blast
  moreover
  have "Postulate14 \<longrightarrow> Postulate13" 
    by (simp add: Postulate13_def Postulate14_def
        proclus_bis__proclus)
  moreover
  have "Postulate13 \<longrightarrow> Postulate18" 
    by (simp add: Postulate13_def Postulate18_def
        proclus_s_postulate_implies_strong_parallel_postulate)
  moreover
  have "Postulate18 \<longrightarrow> Postulate01" 
    using Postulate01_def Postulate18_def 
      strong_parallel_postulate_implies_tarski_s_euclid by blast
  ultimately
  show ?thesis 
    by auto
qed

lemma Cycle_3:
  shows "(Postulate03 \<longleftrightarrow> Postulate21) \<and> 
         (Postulate21 \<longleftrightarrow> Postulate22) \<and>
         (Postulate22 \<longleftrightarrow> Postulate23) \<and> 
         (Postulate23 \<longleftrightarrow> Postulate24) \<and> 
         (Postulate24 \<longleftrightarrow> Postulate25) \<and>
         (Postulate25 \<longleftrightarrow> Postulate26) \<and> 
         (Postulate26 \<longleftrightarrow> Postulate27) \<and> 
         (Postulate27 \<longleftrightarrow> Postulate28) \<and> 
         (Postulate28 \<longleftrightarrow> Postulate29) \<and> 
         (Postulate29 \<longleftrightarrow> Postulate30) \<and>
         (Postulate30 \<longleftrightarrow> Postulate03)"
proof -
  have "Postulate03 \<longrightarrow> Postulate21" 
    using Postulate03_def Postulate21_def 
      triangle__existential_triangle by blast
  moreover
  have "Postulate21 \<longrightarrow> Postulate27" 
    using Postulate21_def Postulate27_def 
      existential_triangle__rah by fastforce
  moreover
  have "Postulate27 \<longrightarrow> Postulate03" 
    by (simp add: Postulate03_def 
        Postulate27_def rah__triangle)
  moreover
  have "Postulate27 \<longleftrightarrow> Postulate28" 
  proof -
    have "Postulate27 \<longrightarrow> Postulate28" 
      by (simp add: Postulate27_def Postulate28_def 
          rah__existential_saccheri)
    moreover
    have "Postulate28 \<longrightarrow> Postulate27" 
      by (simp add: Postulate27_def Postulate28_def 
          existential_saccheri__rah) 
    ultimately show ?thesis
      by auto
  qed
  moreover
  have "Postulate27 \<longrightarrow> Postulate29" 
    using Postulate27_def Postulate29_def 
      rah__rectangle_principle by fastforce
  moreover
  have "Postulate29 \<longrightarrow> Postulate30" 
    using Postulate29_def Postulate30_def 
      rectangle_principle__rectangle_existence by blast
  moreover
  have "Postulate30 \<longrightarrow> Postulate27" 
    by (simp add: Postulate27_def Postulate30_def 
        rectangle_existence__rah)
  moreover
  have "Postulate27 \<longleftrightarrow> Postulate22" 
  proof -
    have "Postulate27 \<longrightarrow> Postulate22" 
      using Postulate22_def Postulate27_def 
        rah__posidonius by blast
    moreover
    have "Postulate22 \<longrightarrow> Postulate27" 
      using Postulate22_def Postulate27_def 
        posidonius_postulate__rah by blast
    ultimately
    show ?thesis 
      by auto
  qed
  moreover
  have "Postulate27 \<longrightarrow> Postulate24" 
    using Postulate24_def Postulate27_def 
      rah__thales_postulate by presburger
  moreover
  have "Postulate24 \<longrightarrow> Postulate25" 
    by (simp add: Postulate24_def Postulate25_def 
        thales_postulate__thales_converse_postulate)
  moreover
  have "Postulate25 \<longrightarrow> Postulate26" 
    using Postulate25_def Postulate26_def 
      thales_converse_postulate__thales_existence by fastforce
  moreover
  have "Postulate26 \<longrightarrow> Postulate27" 
    using Postulate26_def Postulate30_def calculation(7)
      rah__rectangle_principle 
      rectangle_principle__rectangle_existence thales_existence__rah by blast
  moreover
  have "Postulate27 \<longleftrightarrow> Postulate23" 
  proof -
    have "Postulate27 \<longrightarrow> Postulate23" 
      using Postulate23_def Postulate26_def calculation(10)
        calculation(11) calculation(9) rah__similar 
        thales_existence__rah by blast
    moreover
    have "Postulate23 \<longrightarrow> Postulate27" 
      using Postulate22_def Postulate23_def 
        \<open>Postulate27 = Postulate22\<close> rah__posidonius 
        similar__rah by blast 
    ultimately
    show ?thesis 
      by auto
  qed
  ultimately
  show ?thesis by blast
qed

lemma InterCycle1:
  assumes "greenberg_s_axiom" and "Postulate03"
  shows "Postulate12" 
  using greenberg_s_axiom_def Postulate03_def Postulate12_def 
    assms(1) assms(2) triangle__playfair_bis by blast

lemma InterCycle2:
  assumes "Postulate07"
  shows "Postulate03" 
  using Postulate03_def Postulate07_def 
    alternate_interior__triangle assms by blast

lemma InterCycle3:
  assumes "Postulate01"
  shows "Postulate02" 
  using Postulate01_def Postulate02_def assms 
    tarski_s_euclid_implies_playfair_s_postulate by blast

lemma InterCycle4:
  assumes "Postulate09"
  shows "Postulate15" 
  using Postulate09_def Postulate15_def assms 
    inter_dec_plus_par_perp_perp_imply_triangle_circumscription 
  by auto

lemma InterAx1_R1:
  assumes "Postulate13"
  shows "aristotle_s_axiom" 
  using proclus__aristotle aristotle_s_axiom_def 
    Postulate13_def assms by blast

lemma InterAx1:
  assumes "Postulate01"
  shows "aristotle_s_axiom" 
  using InterAx1_R1 Postulate01_def Postulate13_def 
    assms euclid_5__original_euclid 
    inverse_projection_postulate__proclus_bis 
    original_euclid__original_spp original_spp__inverse_projection_postulate 
    proclus_bis__proclus 
    tarski_s_euclid_implies_euclid_5 by blast

lemma InterAx3:
  assumes "greenberg_s_axiom" and "Postulate02"
  shows "Postulate01" 
proof -
  have "Postulate03" 
    using Postulate02_def Postulate03_def alternate_interior__triangle 
      assms(2) playfair__alternate_interior by blast
  hence "Postulate12" 
    using InterCycle1 assms(1) by auto
  thus ?thesis 
    using greenberg_s_axiom_def Postulate01_def Postulate07_def 
      alternate_interior__proclus assms(1) 
      equivalent_postulates_without_decidability_of_intersection_of_lines 
      proclus_s_postulate_implies_strong_parallel_postulate 
      strong_parallel_postulate_implies_tarski_s_euclid by blast
qed

lemma InterAx4:
  assumes "Postulate01"
  shows "Axiom1" 
  by (simp add: Axiom1ProofIsabelleHOL)

lemma InterAx5:
  assumes (*"Axiom1" and*) "Postulate02"
  shows "Postulate01" 
proof -
  have "Postulate15" 
    using InterCycle4 Postulate02_def Postulate09_def 
      assms playfair__universal_posidonius_postulate 
      universal_posidonius_postulate__perpendicular_transversal_postulate
    by blast
  thus ?thesis 
    using Postulate01_def Postulate15_def 
      triangle_circumscription_implies_tarski_s_euclid by blast
qed

lemma PPR_Theorem_4_bis: 
  assumes "Postulate01"
  shows "greenberg_s_axiom" 
  using aristotle_s_axiom_def greenberg_s_axiom_def InterAx1 InterAx5 
    aristotle__greenberg assms by blast

lemma PPR_Proposition_6:
  assumes "archimedes_axiom"
  shows "aristotle_s_axiom"
  using t22_24 archimedes_axiom_def aristotle_s_axiom_def assms by blast

lemma InterCycle1bis: 
  assumes "Postulate01"
  shows "Postulate03 \<longrightarrow> Postulate12" 
  using Cycle_1 assms 
    equivalent_postulates_without_decidability_of_intersection_of_lines by blast

lemma weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate:
  assumes "weak_inverse_projection_postulate"
  shows "weak_tarski_s_parallel_postulate" 
proof -
  {
    fix A B C P T
    assume "Per A B C" and
      "T InAngle A B C" and
      "P \<noteq> T" and
      "P B A CongA P B C" and
      "Per B P T" and 
      "Coplanar A B C P" 
    have "B \<noteq> P" 
      using \<open>P B A CongA P B C\<close> conga_diff45 by blast
    have "B \<noteq> A" 
      using \<open>P B A CongA P B C\<close> conga_diff2 by blast
    have "B \<noteq> C" 
      using \<open>T InAngle A B C\<close> inangle_distincts by blast
    have "P InAngle A B C" 
      by (meson conga_inangle_per2__inangle 
          \<open>Coplanar A B C P\<close> \<open>P B A CongA P B C\<close> \<open>Per A B C\<close> 
          \<open>Per B P T\<close> \<open>T InAngle A B C\<close>)
    have "P B A P B A SumA A B C" 
    proof -
      have "A B P P B C SumA A B C" 
        by (simp add: inangle__suma \<open>P InAngle A B C\<close>)
      moreover have "A B P CongA P B A" 
        using \<open>B \<noteq> A\<close> \<open>B \<noteq> P\<close> conga_pseudo_refl by auto
      moreover have "P B C CongA P B A" 
        using \<open>P B A CongA P B C\<close> conga_sym_equiv by force
      moreover have "A B C CongA A B C" 
        using \<open>B \<noteq> A\<close> \<open>B \<noteq> C\<close> conga_refl by auto
      ultimately show ?thesis 
        using conga3_suma__suma by blast
    qed
    have "Acute P B A" 
      by (meson conga_inangle_per__acute \<open>P B A CongA P B C\<close> 
          \<open>P InAngle A B C\<close> \<open>Per A B C\<close> acute_sym)
    have "B Out P P" 
      using \<open>B \<noteq> P\<close> out_trivial by auto
    {
      assume "Col A B C" 
      hence "\<not> Per A B C" 
        using \<open>B \<noteq> A\<close> \<open>B \<noteq> C\<close> per_not_col by force
      hence False 
        using \<open>Per A B C\<close> by blast
    }
    hence "\<not> Col A B C" 
      by blast
    have "Coplanar P B A T" 
      by (metis Col_cases \<open>Coplanar A B C P\<close> \<open>T InAngle A B C\<close> \<open>\<not> Col A B C\<close> 
          coplanar_perm_12 coplanar_perm_21 coplanar_trans_1 inangle__coplanar)
    hence "\<exists> X. B Out A X \<and> Col P T X" 
      using \<open>Acute P B A\<close> \<open>Per A B C\<close> \<open>P B A P B A SumA A B C\<close> \<open>B Out P P\<close>
        \<open>P \<noteq> T\<close> \<open>Per B P T\<close>
        assms weak_inverse_projection_postulate_def
      by blast
    then obtain X where "B Out A X" and "Col P T X" 
      by blast
    have "\<exists> Y. B Out C Y \<and> Col P T Y" 
    proof -
      have "Acute P B C" 
        using \<open>Acute P B A\<close> \<open>P B A CongA P B C\<close> acute_conga__acute by blast
      moreover have "Per C B A" 
        using Per_perm \<open>Per A B C\<close> by blast
      moreover have "P B C P B C SumA C B A" 
        by (metis Tarski_neutral_dimensionless.conga3_suma__suma 
            Tarski_neutral_dimensionless_axioms \<open>B \<noteq> A\<close> \<open>B \<noteq> C\<close> 
            \<open>P B A CongA P B C\<close> \<open>P B A P B A SumA A B C\<close> conga_pseudo_refl)
      moreover have "Coplanar P B C T" 
        by (meson \<open>Col A B C \<Longrightarrow> False\<close> \<open>Coplanar A B C P\<close> 
            \<open>T InAngle A B C\<close> coplanar_pseudo_trans inangle__coplanar 
            ncop_distincts ncoplanar_perm_18)
      ultimately show ?thesis
        using \<open>B Out P P\<close> \<open>P \<noteq> T\<close>  \<open>Per B P T\<close>
          assms weak_inverse_projection_postulate_def
        by blast
    qed
    then obtain Y where "B Out C Y" and "Col P T Y" 
      by blast
    hence "\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y)" 
      using \<open>B Out A X\<close> \<open>Col P T X\<close> not_col_permutation_4 by blast
  }
  moreover
  {
    assume LEMME: "\<forall> A B C P T. Per A B C \<and> T InAngle A B C \<and>
                                P \<noteq> T \<and> P B A CongA P B C \<and> Per B P T \<and>
                                Coplanar A B C P
                   \<longrightarrow> 
                   (\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y))"
    {
      fix A B C T
      assume "Per A B C" and "T InAngle A B C"
      obtain P0 where "P0 InAngle A B C" and "P0 B A CongA P0 B C"  
        using \<open>T InAngle A B C\<close> angle_bisector inangle_distincts by blast
      have "A \<noteq> B" 
        using \<open>P0 B A CongA P0 B C\<close> conga_diff2 by auto
      have "C \<noteq> B" 
        using \<open>T InAngle A B C\<close> inangle_distincts by blast
      have "T \<noteq> B" 
        using \<open>T InAngle A B C\<close> inangle_distincts by blast
      have "P0 \<noteq> B" 
        using \<open>P0 B A CongA P0 B C\<close> conga_diff45 by blast
      {
        assume "Col A B C"
        hence "\<not> Per A B C" 
          using \<open>A \<noteq> B\<close> \<open>C \<noteq> B\<close> per_not_col by force
        hence False 
          by (simp add: \<open>Per A B C\<close>)
      }
      hence "\<not> Col A B C" 
        by blast
      have "\<not> Col P0 B A" 
      proof -
        have "P0 B A P0 B A SumA A B C" 
        proof -
          have "A B P0 P0 B C SumA A B C" 
            using \<open>P0 InAngle A B C\<close> inangle__suma by force
          moreover have "A B P0 CongA P0 B A" 
            using \<open>A \<noteq> B\<close> \<open>P0 \<noteq> B\<close> conga_pseudo_refl by auto
          moreover have "P0 B C CongA P0 B A" 
            using \<open>P0 B A CongA P0 B C\<close> not_conga_sym by blast
          moreover have "A B C CongA A B C" 
            by (simp add: \<open>A \<noteq> B\<close> \<open>C \<noteq> B\<close> conga_refl)
          ultimately show ?thesis
            using conga3_suma__suma by blast
        qed
        thus ?thesis 
          using \<open>\<not> Col A B C\<close> col2_suma__col by blast
      qed
      {
        assume "Col B P0 T"
        have "\<exists> T'. T' InAngle A B C \<and> B T Perp T T'" 
        proof -
          obtain T0 where "B P0 Perp T0 T" and "B P0 OS A T0" 
            using Col_cases \<open>Col B P0 T\<close> \<open>\<not> Col P0 B A\<close> l10_15 by blast
          have "\<exists> T'. T' InAngle A B C \<and> T \<noteq> T' \<and> Col T T0 T'"
          proof -
            have "\<not> B Out A C" 
              using Col_cases \<open>\<not> Col A B C\<close> out_col by blast
            moreover have "T InAngle A B C" 
              by (simp add: \<open>T InAngle A B C\<close>)
            moreover have "Coplanar A B C T0" 
            proof -
              have "Coplanar P0 B A A" 
                using ncop_distincts by auto
              moreover have "Coplanar P0 B A B"
                using ncop_distincts by auto
              moreover have "Coplanar P0 B A C" 
                using \<open>P0 InAngle A B C\<close> inangle__coplanar ncoplanar_perm_2 by blast
              moreover have "Coplanar P0 B A T0" 
                by (simp add: \<open>B P0 OS A T0\<close> invert_one_side os__coplanar)
              ultimately show ?thesis 
                using \<open>\<not> Col P0 B A\<close> coplanar_perm_6 coplanar_trans_1 by blast
            qed
            ultimately show ?thesis
              using cop_inangle__ex_col_inangle by blast
          qed
          then obtain T' where "T' InAngle A B C" and 
            "T \<noteq> T'" and "Col T T0 T'" by blast
          have "B P0 Perp T T'" 
            by (metis \<open>B P0 Perp T0 T\<close> \<open>Col T T0 T'\<close> \<open>T \<noteq> T'\<close> 
                not_col_distincts perp_col2_bis)
          hence "B T Perp T T'" 
            by (metis perp_col  \<open>Col B P0 T\<close> \<open>T \<noteq> B\<close>)
          thus ?thesis 
            using \<open>T' InAngle A B C\<close> by blast
        qed
        then obtain T' where "T' InAngle A B C" and "B T Perp T T'" 
          by blast
        have "T \<noteq> T'" 
          using \<open>B T Perp T T'\<close> perp_not_eq_2 by auto
        have "\<exists> X Y. B Out A X \<and> Col T' T X \<and> B Out C Y \<and> Col T' T Y"
        proof -
          have "T B A CongA T B C"
            using \<open>T \<noteq> B\<close> \<open>P0 B A CongA P0 B C\<close> \<open>Col B P0 T\<close> col_conga__conga by blast
          moreover have "Per B T T'" 
            using Perp_cases \<open>B T Perp T T'\<close> perp_per_1 by blast
          moreover have "Coplanar A B C T" 
            using \<open>T InAngle A B C\<close> coplanar_perm_9 inangle__coplanar by blast
          ultimately show ?thesis 
            using LEMME \<open>Per A B C\<close> \<open>T' InAngle A B C\<close>  \<open>T \<noteq> T'\<close> by blast
        qed
        then obtain X Y where "B Out A X" and "Col T' T X" and "B Out C Y" and "Col T' T Y"
          by blast
        hence "\<exists> X Y. B Out A X \<and> B Out C Y \<and> Col X T Y" 
          by (metis Col_cases \<open>T \<noteq> T'\<close> col_transitivity_2)
      }
      moreover
      {
        assume "\<not> Col B P0 T"
        obtain P where "Col B P0 P" and "B P0 Perp T P" 
          using \<open>\<not> Col B P0 T\<close> l8_18_existence by blast
        have "B Out P P0" 
        proof - 
          have "Acute T B P0"
            using \<open>Per A B C\<close> \<open>T InAngle A B C\<close> \<open>P0 B A CongA P0 B C\<close>  
              \<open>P0 InAngle A B C\<close> acute_sym conga_inangle2_per__acute by blast
          thus ?thesis 
            by (meson \<open>B P0 Perp T P\<close> \<open>Col B P0 P\<close> acute_col_perp__out)
        qed
        have "P \<noteq> T" 
          using \<open>Col B P0 P\<close> \<open>\<not> Col B P0 T\<close> by blast
        have "P \<noteq> B" 
          using \<open>B Out P P0\<close> l6_3_1 by auto
        have "\<exists> X Y. B Out A X \<and> B Out C Y \<and> Col X T Y" 
        proof -
          have "\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y)"
          proof -
            have "P B A CongA P B C" 
              by (metis col_conga__conga \<open>Col B P0 P\<close> \<open>P \<noteq> B\<close> \<open>P0 B A CongA P0 B C\<close>)
            moreover have "Per B P T" 
            proof -
              have "B \<noteq> P" 
                using \<open>P \<noteq> B\<close> by auto
              moreover have "B P0 Perp T P" 
                by (simp add: \<open>B P0 Perp T P\<close>)
              moreover have "Col B P0 P"  
                by (simp add: \<open>Col B P0 P\<close>)
              ultimately show ?thesis    
                using col_trivial_3 l8_16_1 l8_2 by blast
            qed
            moreover have "Coplanar A B C P" 
              using \<open>Col B P0 P\<close> \<open>P0 InAngle A B C\<close> \<open>P0 \<noteq> B\<close> col_cop__cop 
                coplanar_perm_11 inangle__coplanar ncoplanar_perm_2 by blast
            ultimately show ?thesis 
              using \<open>Per A B C\<close> \<open>T InAngle A B C\<close> \<open>P \<noteq> T\<close> LEMME by blast
          qed
          then obtain X Y where "B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y" by blast
          thus ?thesis 
            using \<open>P \<noteq> T\<close> col2__eq col_permutation_2 by blast
        qed
      }
      ultimately
      have "\<exists> X Y. B Out A X \<and> B Out C Y \<and> Col X T Y" 
        by blast
      then obtain X Y where "B Out A X" and "B Out C Y" and "Col X T Y" 
        by blast
      have "Y \<noteq> B" 
        using Out_def \<open>B Out C Y\<close> by auto
      have "X \<noteq> B" 
        using Out_def \<open>B Out A X\<close> by auto
      have "\<not> Col A B Y" 
        using Out_cases \<open>A \<noteq> B\<close> \<open>B Out C Y\<close> \<open>\<not> Col A B C\<close> col_out2_col out_trivial by blast
      have "X \<noteq> Y" 
        using \<open>B Out A X\<close> \<open>\<not> Col A B Y\<close> not_col_permutation_4 out_col by blast
      have "Bet X T Y" 
      proof -
        {
          assume "T = X" and "T = Y" 
          have "Bet X T Y" 
            using \<open>T = X\<close> \<open>T = Y\<close> \<open>X \<noteq> Y\<close> by auto
        }
        moreover
        {
          assume "T \<noteq> X" and "T \<noteq> Y" 
          have "B A OS T C" 
            by (metis Col_cases \<open>B Out A X\<close> \<open>Col X T Y\<close> \<open>T InAngle A B C\<close> \<open>T \<noteq> X\<close> 
                \<open>\<not> Col A B C\<close> \<open>\<not> Col A B Y\<close> colx in_angle_one_side invert_one_side out_col)
          hence "B A OS T Y" 
            using \<open>B Out C Y\<close> out_out_one_side by blast
          hence "X B OS T Y" 
            by (meson \<open>B Out A X\<close> \<open>X \<noteq> B\<close> col2_os__os not_col_distincts out_col)
          hence "X Out T Y" 
            using \<open>Col X T Y\<close> col_one_side_out by blast
          have "B C OS T A"
          proof -
            have "\<not> Col C B A" 
              using \<open>\<not> Col A B C\<close> not_col_permutation_3 by blast
            moreover have "\<not> Col B C T" 
              by (metis Col_def Out_def \<open>B Out A X\<close> \<open>B Out C Y\<close> \<open>Col X T Y\<close> \<open>T \<noteq> Y\<close> 
                  \<open>\<not> Col A B C\<close> col_permutation_1 colx not_col_distincts)
            moreover have "T InAngle C B A" 
              using \<open>T InAngle A B C\<close> l11_24 by blast
            ultimately show ?thesis
              using in_angle_one_side invert_one_side by blast
          qed
          hence "B C OS X T" 
            using \<open>B Out A X\<close> col_trivial_3 one_side_symmetry os_out_os by blast
          hence "Y B OS X T" 
            using \<open>B Out C Y\<close> \<open>Y \<noteq> B\<close> col2_os__os col_trivial_3 out_col by blast
          moreover hence "Y Out X T" 
            using Col_def \<open>Col X T Y\<close> col_one_side_out by blast
          ultimately have "Bet X T Y" 
            using out2__bet \<open>X Out T Y\<close> by blast
        }
        moreover
        {
          assume "T \<noteq> X" and "T = Y" 
          have "Bet X T Y" 
            by (simp add: \<open>T = Y\<close> between_trivial)
        }
        moreover
        {
          assume "T = X" and "T \<noteq> Y" 
          have "Bet X T Y" 
            by (simp add: \<open>T = X\<close> between_trivial2)
        }
        ultimately show ?thesis 
          by auto
      qed
      hence "\<exists> X Y. B Out A X \<and> B Out C Y \<and> Bet X T Y" 
        using \<open>B Out A X\<close> \<open>B Out C Y\<close> by auto
    }
    hence "weak_tarski_s_parallel_postulate" 
      using weak_tarski_s_parallel_postulate_def by blast
  }
  ultimately
  have "weak_tarski_s_parallel_postulate" 
    by blast
  thus ?thesis 
    by blast
qed


(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)
lemma weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate_aux :
  assumes "weak_tarski_s_parallel_postulate"
  shows "\<forall> A B C P T.
    Per A B C \<and> T InAngle A B C \<and>
    P \<noteq> T \<and> P B A CongA P B C \<and> Per B P T \<and> Coplanar A B C P 
\<longrightarrow>
    ((\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y)))" 
proof -
  {
    fix A B C P T
    assume "Per A B C" and "T InAngle A B C" and
      "P \<noteq> T" and "P B A CongA P B C" and "Per B P T" and "Coplanar A B C P"
    have "P InAngle A B C" 
      by (metis conga_inangle_per2__inangle \<open>Coplanar A B C P\<close> 
          \<open>P B A CongA P B C\<close> \<open>Per A B C\<close> \<open>Per B P T\<close> \<open>T InAngle A B C\<close>)
    have "Acute P B A" 
      by (meson conga_inangle_per__acute \<open>P B A CongA P B C\<close> 
          \<open>P InAngle A B C\<close> \<open>Per A B C\<close> acute_sym)
    have "Acute P B C" 
      by (meson acute_conga__acute \<open>Acute P B A\<close> \<open>P B A CongA P B C\<close>)
    have "B \<noteq> P" 
      using \<open>Acute P B C\<close> acute_distincts by blast
    have "B \<noteq> A" 
      using \<open>T InAngle A B C\<close> inangle_distincts by blast
    have "B \<noteq> C" 
      using \<open>P B A CongA P B C\<close> conga_distinct by blast
    have "B P Perp P T" 
      by (simp add: \<open>B \<noteq> P\<close> \<open>P \<noteq> T\<close> \<open>Per B P T\<close> per_perp)
    have "\<not> Col A B C" 
      using \<open>Per A B C\<close> \<open>B \<noteq> A\<close> \<open>B \<noteq> C\<close> per_not_col by auto
    have "\<not> Col B P T" 
      using \<open>Per B P T\<close> \<open>B \<noteq> P\<close> \<open>P \<noteq> T\<close> per_col_eq by blast
    {
      assume "Col A B T"
      hence "B Out A T" 
        using \<open>T InAngle A B C\<close> \<open>\<not> Col A B C\<close> bet_col 
          bet_in_angle_bet or_bet_out by blast
      hence "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
        using col_trivial_3 by blast
    } 
    moreover
    {
      assume "\<not> Col A B T"
      have "\<exists> U V. (B Out A U \<and> B Out C V \<and> Bet U T V)" 
        using assms weak_tarski_s_parallel_postulate_def  
          \<open>Per A B C\<close> \<open>T InAngle A B C\<close> by blast
      then obtain U V where "B Out A U" and "B Out C V" and "Bet U T V" 
        by blast
      have "Col B A U"         
        by (simp add: \<open>B Out A U\<close> out_col)
      have "Col B C V"         
        using \<open>B Out C V\<close> out_col by blast
      have "Coplanar A C U V"
        using Coplanar_def \<open>Col B A U\<close> \<open>Col B C V\<close> not_col_permutation_2 by blast
      have "Coplanar A B C T" 
        using \<open>T InAngle A B C\<close> coplanar_perm_9 inangle__coplanar by blast
      have "Coplanar B U V T" 
        using \<open>Bet U T V\<close> bet__coplanar ncoplanar_perm_11 by blast
      have "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
      proof -
        {
          assume "Col P T U"
          hence "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
            using \<open>B Out A U\<close> not_col_permutation_4 by blast
        }
        moreover
        {
          assume "\<not> Col P T U"
          have "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
          proof -
            {
              assume "Col P T V"
              hence "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
                using \<open>B Out C V\<close> not_col_permutation_4 by blast
            }
            moreover
            {
              assume "\<not> Col P T V"
              have "P T TS B U \<or> P T OS B U"
              proof -
                have "Coplanar P T B U" 
                proof -
                  have "Coplanar A B C B" 
                    using ncop_distincts by blast
                  moreover have "Coplanar A B C U" 
                    using Col_cases \<open>Col B A U\<close> ncop__ncols by blast
                  ultimately show ?thesis 
                    using \<open>\<not> Col A B C\<close> \<open>Coplanar A B C P\<close>  \<open>Coplanar A B C T\<close> 
                      coplanar_pseudo_trans by blast
                qed
                moreover have "\<not> Col U P T" 
                  using \<open>\<not> Col P T U\<close> col_permutation_1 by blast
                ultimately show ?thesis 
                  using \<open>\<not> Col B P T\<close> cop_nos__ts by blast
              qed
              have "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
              proof -
                {
                  assume "P T TS B U"
                  then obtain X where "Col X P T" and "Bet B X U" 
                    using TS_def by blast
                  have "X \<noteq> B" 
                    using \<open>Col X P T\<close> \<open>\<not> Col B P T\<close> by blast
                  hence "B Out U X" 
                    using Out_def \<open>B Out A U\<close> \<open>Bet B X U\<close> by presburger
                  hence "B Out A X" 
                    using \<open>B Out A U\<close> l6_7 by blast
                  hence "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
                    using \<open>Col X P T\<close> col_permutation_3 by blast
                }
                moreover
                {
                  assume "P T OS B U"
                  have "P T TS B V" 
                  proof - 
                    have "P T TS U V" 
                      by (metis \<open>Bet U T V\<close> \<open>\<not> Col P T U\<close> \<open>\<not> Col P T V\<close> 
                          bet__ts col_trivial_2 invert_two_sides 
                          not_col_permutation_4)
                    moreover have "P T OS U B" 
                      using \<open>P T OS B U\<close> one_side_symmetry by blast
                    ultimately show ?thesis
                      using l9_8_2 by blast
                  qed
                  then obtain Y where "Col Y P T" and "Bet B Y V" 
                    using TS_def by blast
                  have "B Out C Y" 
                    by (metis Col_def \<open>B Out C V\<close> \<open>Bet B Y V\<close> \<open>Col Y P T\<close> 
                        \<open>P T OS B U\<close> between_equality 
                        between_symmetry col123__nos l6_7 not_out_bet)
                  hence "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
                    using \<open>Col Y P T\<close> not_col_permutation_3 by blast
                }
                ultimately show ?thesis 
                  using \<open>P T TS B U \<or> P T OS B U\<close> by blast
              qed
            }
            ultimately show ?thesis by blast
          qed
        }
        ultimately show ?thesis by blast
      qed
    }
    ultimately have "(\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y))" 
      by blast
  }
  thus ?thesis by blast
qed

lemma weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate:
  assumes "weak_tarski_s_parallel_postulate"
  shows "weak_inverse_projection_postulate" 
proof -
  {
    fix A B C P T
    assume "Per A B C" and "T InAngle A B C" and
      "P \<noteq> T" and "P B A CongA P B C" and "Coplanar A B C P" and "Per B P T"
    have "\<not> B Out A C" 
      by (metis Col_def Out_def Bet_perm per_not_col \<open>Per A B C\<close>)
    have "B P Perp P T" 
      using CongA_def \<open>P B A CongA P B C\<close> \<open>P \<noteq> T\<close> \<open>Per B P T\<close> per_perp by auto
    have "((\<exists> X. (B Out A X \<and> Col T P X)) \<or> (\<exists> Y. (B Out C Y \<and> Col T P Y)))" 
      using assms weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate_aux
        \<open>Coplanar A B C P\<close> \<open>P B A CongA P B C\<close> \<open>P \<noteq> T\<close> 
        \<open>Per A B C\<close> \<open>Per B P T\<close> \<open>T InAngle A B C\<close> by blast
    moreover
    { 
      assume "\<exists> X. (B Out A X \<and> Col T P X)"
      then obtain X where "B Out A X" and "Col T P X" 
        by blast
      obtain Y where "P Midpoint X Y" 
        using symmetric_point_construction by blast
      {
        assume "X = Y"
        hence "B Out A P" 
          using \<open>B Out A X\<close> \<open>P Midpoint X Y\<close> l8_20_2 by blast
        hence "B Out P C" 
          by (metis Col_def Out_def \<open>P B A CongA P B C\<close> \<open>\<not> B Out A C\<close> 
              between_symmetry col_conga__conga eq_conga_out)
        hence False 
          using \<open>B Out A P\<close> \<open>\<not> B Out A C\<close> l6_7 by blast
      }
      hence "X \<noteq> Y" 
        by blast
      have "Y X ReflectL B P" 
      proof -
        have "(\<exists> X0. X0 Midpoint X Y \<and> Col B P X0)" 
          using \<open>P Midpoint X Y\<close> col_trivial_2 by blast
        moreover have "(B P Perp X Y \<or> X = Y)" 
          by (metis Perp_perm perp_col0
              \<open>B P Perp P T\<close> \<open>Col T P X\<close> \<open>P Midpoint X Y\<close> 
              col_trivial_2 midpoint_col midpoint_distinct_1)
        ultimately show ?thesis 
          by (simp add: ReflectL_def)
      qed
      hence "X Y ReflectL B P" 
        using l10_4_spec by blast
      moreover hence "B Out C Y" 
        using \<open>B Out A X\<close> \<open>P B A CongA P B C\<close> \<open>\<not> B Out A C\<close> \<open>Coplanar A B C P\<close> 
          conga_cop_out_reflectl__out by blast
      moreover have "Col T P X" 
        by (simp add: \<open>Col T P X\<close>)
      hence "Col P X T" 
        using not_col_permutation_2 by blast
      have "P \<noteq> X" 
        using \<open>P Midpoint X Y\<close> \<open>X = Y \<Longrightarrow> False\<close> is_midpoint_id by blast
      hence "Col P X Y" 
        using \<open>P Midpoint X Y\<close> midpoint_col by blast
      moreover hence "Col T P Y" 
        using \<open>Col T P X\<close> \<open>P \<noteq> X\<close> col_trivial_2 colx by blast
      ultimately
      have "\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y)" 
        using \<open>B Out A X\<close> \<open>Col T P X\<close> by blast
    }
    moreover
    {
      assume "\<exists> Y. (B Out C Y \<and> Col T P Y)"
      then obtain Y where "B Out C Y" and "Col T P Y" 
        by blast
      obtain X where "P Midpoint Y X" 
        using symmetric_point_construction by blast
      {
        assume "X = Y"
        hence "X = P" 
          using \<open>P Midpoint Y X\<close> l7_17_bis l7_3_2 by blast
        hence "Y = P" 
          by (simp add: \<open>X = Y\<close>)
        have "B Out A P"
        proof -
          have "B Out P C" 
            using \<open>B Out C Y\<close> \<open>Y = P\<close> l6_6 by blast
          moreover have "P B C CongA P B A" 
            using \<open>P B A CongA P B C\<close> conga_sym_equiv by auto
          ultimately show ?thesis
            using Out_cases out_conga_out by blast
        qed
        have "B Out C P" 
          using \<open>B Out C Y\<close> \<open>X = P\<close> \<open>X = Y\<close> by blast
        moreover hence "B Out P C" 
          using l6_6 by blast
        ultimately have False 
          using \<open>\<not> B Out A C\<close> l6_7 \<open>B Out A P\<close> by blast
      }
      hence "X \<noteq> Y" 
        by blast
      have "B Out A X"
      proof -
        have "\<not> B Out C A" 
          using \<open>\<not> B Out A C\<close> l6_6 by blast
        moreover have "Coplanar C B A P" 
          using \<open>Coplanar A B C P\<close> coplanar_perm_14 by presburger
        moreover have "P B C CongA P B A" 
          using \<open>P B A CongA P B C\<close> conga_sym_equiv by auto
        moreover have "Y X ReflectL B P"
        proof -
          have "\<exists> X0. X0 Midpoint Y X \<and> Col B P X0" 
            using \<open>P Midpoint Y X\<close> col_trivial_2 by blast
          moreover have "B P Perp Y X \<or> Y = X" 
            by (metis col_permutation_4 col_trivial_3 midpoint_distinct_1 
                \<open>B P Perp P T\<close> \<open>Col T P Y\<close> \<open>P Midpoint Y X\<close> colx 
                midpoint_col perp_col2_bis)
          ultimately show ?thesis
            by (metis ReflectL_def l10_4_spec)
        qed
        ultimately show ?thesis
          using \<open>B Out C Y\<close> conga_cop_out_reflectl__out by blast
      qed
      have "P \<noteq> X" 
        using \<open>P Midpoint Y X\<close> \<open>X = Y \<Longrightarrow> False\<close> is_midpoint_id_2 by blast
      have "Col P X Y" 
        using \<open>P Midpoint Y X\<close> Col_def Midpoint_def by blast
      hence "Col P X T" 
        by (metis \<open>Col T P Y\<close> \<open>P Midpoint Y X\<close> col_permutation_1 
            col_trivial_3 colx l7_2 midpoint_distinct_2)
      moreover hence "Col T P X" 
        using not_col_permutation_1 by blast
      moreover have "Col T P Y" 
        by (simp add: \<open>Col T P Y\<close>)
      ultimately
      have "\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y)"    
        using \<open>B Out C Y\<close> \<open>B Out A X\<close> by blast
    }
    ultimately have "\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y)" 
      by blast
  }
  hence LEMME: "\<forall> A B C P T.
       Per A B C \<and> T InAngle A B C \<and>
       P \<noteq> T \<and> P B A CongA P B C \<and> Coplanar A B C P \<and> Per B P T \<longrightarrow>
       (\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y))" 
    by blast
  moreover
  {
    assume "\<forall> A B C P T.
       Per A B C \<and> T InAngle A B C \<and>
       P \<noteq> T \<and> P B A CongA P B C \<and> Coplanar A B C P \<and> Per B P T \<longrightarrow>
       (\<exists> X Y. (B Out A X \<and> Col T P X \<and> B Out C Y \<and> Col T P Y))" 
    {
      fix A B C D E F P Q
      assume "Acute A B C" and "Per D E F" and "A B C A B C SumA D E F" and 
        "B Out A P" and "P \<noteq> Q" and "Per B P Q" and "Coplanar A B C Q"
      have "\<not> Col A B C" 
        using \<open>Per D E F\<close> 
        by (metis col2_suma__col suma_distincts \<open>A B C A B C SumA D E F\<close> per_not_col)
      have "\<not> Col B P Q" 
        by (metis Col_def per_col_eq \<open>B Out A P\<close> \<open>P \<noteq> Q\<close> 
            \<open>Per B P Q\<close> between_trivial l6_4_1)
      have "A B C CongA P B C" 
        by (metis \<open>Acute A B C\<close> \<open>B Out A P\<close> acute_distincts bet_out_1 
            conga_sym_equiv not_bet_distincts out2__conga)
      have "\<not> Col P B C" 
        by (metis Out_def \<open>B Out A P\<close> \<open>\<not> Col A B C\<close> col_out2_col 
            col_permutation_3 col_trivial_3 l6_16_1 out_trivial)
      have "B P Perp P Q" 
        by (metis \<open>B Out A P\<close> \<open>P \<noteq> Q\<close> \<open>Per B P Q\<close> out_diff2 per_perp)
      have "C B A A B C SumA D E F" 
        by (simp add: \<open>A B C A B C SumA D E F\<close> suma_left_comm)
      then obtain J where "A B J CongA A B C" and "\<not> B A OS C J" and 
        "Coplanar C B A J" and "C B J CongA D E F" 
        using SumA_def by blast
      have "\<exists> Q'. (P \<noteq> Q') \<and> Col P Q Q' \<and> Q' InAngle C B P" 
      proof -
        have "\<exists> Q0. Col Q P Q0 \<and> B P OS C Q0"
        proof -
          have "Q \<noteq> P" 
            using \<open>P \<noteq> Q\<close> by blast
          moreover have "Col B P P" 
            by (simp add: col_trivial_2)
          moreover have "Col Q P P"  
            by (simp add: col_trivial_2)
          moreover have "\<not> Col B P C" 
            using \<open>\<not> Col P B C\<close> not_col_permutation_4 by blast
          moreover have "Coplanar B P Q C" 
            by (metis (no_types, opaque_lifting) Col_def Out_def \<open>B Out A P\<close> 
                \<open>Coplanar A B C Q\<close> \<open>\<not> Col A B C\<close> 
                coplanar_pseudo_trans_lem1 ncop__ncols ncop_distincts)
          ultimately show ?thesis 
            using \<open>\<not> Col B P Q\<close> cop_not_par_same_side by blast
        qed
        then obtain Q0 where "Col Q P Q0" and "B P OS C Q0"
          by blast
        {
          assume "B C OS P Q0"
          hence "\<exists> Q'. (P \<noteq> Q') \<and> Col P Q Q' \<and> Q' InAngle C B P" 
            using \<open>B P OS C Q0\<close> \<open>Col Q P Q0\<close> not_col_permutation_4 
              os2__inangle os_distincts by blast
        }
        moreover
        {
          assume "\<not> B C OS P Q0"
          have "\<exists> Q'. Col P Q Q' \<and> Col B C Q'" 
          proof (cases "Col B C Q0")
            case True
            thus ?thesis 
              using \<open>Col Q P Q0\<close> not_col_permutation_4 by blast
          next
            case False
            have "\<exists> Q'. Col Q' B C \<and> Bet P Q' Q0" 
            proof -
              have "Coplanar B C P Q0" 
                using False \<open>B P OS C Q0\<close> inangle__coplanar ncoplanar_perm_22 
                  os_ts__inangle ts__coplanar two_sides_cases by blast
              moreover have "\<not> Col P B C" 
                using \<open>\<not> Col P B C\<close> by auto
              moreover have "\<not> Col Q0 B C" 
                by (simp add: False not_col_permutation_2)
              moreover have "\<not> B C OS P Q0" 
                using \<open>\<not> B C OS P Q0\<close> by auto
              ultimately show ?thesis 
                using TS_def cop__one_or_two_sides by blast
            qed
            then obtain Q' where "Col Q' B C" and "Bet P Q' Q0"
              by blast
            have  "Col P Q Q'" 
              using \<open>P \<noteq> Q\<close> \<open>Bet P Q' Q0\<close> \<open>Col Q P Q0\<close> bet_col bet_neq12__neq col2__eq 
                col_permutation_4 by blast
            moreover have "Col B C Q'" 
              using \<open>Col Q' B C\<close> not_col_permutation_2 by blast
            ultimately show ?thesis
              by blast
          qed
          then obtain Q' where "Col P Q Q'" and "Col B C Q'" 
            by blast
          have "P \<noteq> Q'" 
            using \<open>Col B C Q'\<close> \<open>\<not> Col P B C\<close> col_permutation_2 by blast
          moreover have "Col P Q Q'" 
            using \<open>Col P Q Q'\<close> by auto
          moreover have "Q' InAngle C B P"
          proof -
            have "P \<noteq> B" 
              using \<open>B P OS C Q0\<close> os_distincts by blast
            moreover have "B Out C Q'"
            proof -
              have "Acute P B C"               
                by (meson acute_conga__acute \<open>A B C CongA P B C\<close> \<open>Acute A B C\<close>)
              moreover have "B P Perp P Q'"               
                by (meson perp_col1 \<open>B P Perp P Q\<close> \<open>Col P Q Q'\<close> \<open>P \<noteq> Q'\<close>)
              ultimately show ?thesis
                using \<open>Col B C Q'\<close> acute_col_perp__out_1 l6_6 by blast
            qed
            ultimately show ?thesis
              using out321__inangle by auto
          qed
          ultimately have "\<exists> Q'. (P \<noteq> Q') \<and> Col P Q Q' \<and> Q' InAngle C B P" 
            by blast
        }
        ultimately show ?thesis 
          by blast
      qed
      then obtain Q' where "P \<noteq> Q'" and "Col P Q Q'" and "Q' InAngle C B P" 
        by blast
      have "B Out P A" 
        by (simp add: \<open>B Out A P\<close> l6_6)
      have "C \<noteq> B" 
        using \<open>\<not> Col P B C\<close> col_trivial_2 by auto
      have "P \<noteq> B" 
        using \<open>B Out A P\<close> out_distinct by presburger
      have "J \<noteq> B" 
        using \<open>A B J CongA A B C\<close> conga_diff2 by blast
      have "D \<noteq> E" 
        using \<open>C B J CongA D E F\<close> conga_diff45 by auto
      {
        assume "E = F"
        hence "A B C A B C SumA D E E" 
          using \<open>A B C A B C SumA D E F\<close> by blast
        hence False 
          using \<open>C B J CongA D E F\<close> \<open>E = F\<close> conga_diff56 by blast
      }
      hence "F \<noteq> E" 
        by blast
      have "A B C CongA A B J"         
        using \<open>A B J CongA A B C\<close> conga_sym_equiv by auto
      hence "\<not> Col A B J" 
        using \<open>\<not> Col A B C\<close> \<open>A B J CongA A B C\<close> col_conga_col by blast
      have "P InAngle C B J" 
      proof -
        have "A InAngle C B J"
        proof -
          have "B A TS C J"
          proof -
            have "Coplanar B A C J" 
              using \<open>Coplanar C B A J\<close> coplanar_perm_8 by presburger
            moreover have "\<not> Col C B A" 
              using NCol_cases \<open>\<not> Col A B C\<close> by blast
            moreover have "\<not> Col J B A" 
              using Col_cases \<open>\<not> Col A B J\<close> by blast
            ultimately show ?thesis
              using  \<open>\<not> B A OS C J\<close> cop_nts__os by blast
          qed
          moreover have "B C OS J A" 
          proof -
            have "Coplanar C B A J" 
              by (simp add: \<open>Coplanar C B A J\<close>)
            moreover have "\<not> Col A C B" 
              using NCol_cases \<open>\<not> Col A B C\<close> by blast
            have "\<not> Col C B J"
            proof -
              have "\<not> Col D E F" 
                using \<open>D \<noteq> E\<close> \<open>F \<noteq> E\<close> \<open>Per D E F\<close> per_not_col by auto
              moreover have "D E F CongA C B J" 
                by (simp add: \<open>C B J CongA D E F\<close> conga_sym_equiv)
              ultimately show ?thesis
                by (meson col_conga_col \<open>C B J CongA D E F\<close>)
            qed
            moreover hence "\<not> Col J C B" 
              using col_permutation_1 by blast
            have "SAMS C B A A B C" 
              using \<open>Acute A B C\<close> acute2__sams acute_sym by blast
            moreover hence "\<not> C B TS A J" 
              using \<open>A B J CongA A B C\<close> \<open>\<not> B A OS C J\<close> conga_sams_nos__nts by blast
            ultimately show ?thesis
              using invert_one_side one_side_symmetry cop_nts__os 
                \<open>\<not> Col A C B\<close> \<open>\<not> Col J C B\<close> by blast
          qed
          ultimately show ?thesis
            using os_ts__inangle by blast
        qed
        moreover have "B Out C C"
          using \<open>C \<noteq> B\<close> out_trivial by auto
        moreover have "B Out J J" 
          using \<open>J \<noteq> B\<close> out_trivial by auto
        ultimately show ?thesis 
          using \<open>B Out P A\<close> l11_25 by blast
      qed
      hence "Q' InAngle C B J"
        using \<open>Q' InAngle C B P\<close> in_angle_trans by blast
      have "\<exists> Y. B Out C Y \<and> Col Q' P Y" 
      proof -
        have "D E F CongA C B J" 
          by (simp add: \<open>C B J CongA D E F\<close> conga_sym_equiv)
        hence "Per C B J" 
          using \<open>Per D E F\<close> l11_17 by blast
        moreover have "Q' InAngle C B J" 
          using \<open>Q' InAngle C B J\<close> by auto
        moreover have "P \<noteq> Q'" 
          by (simp add: \<open>P \<noteq> Q'\<close>)
        moreover have "P B C CongA P B J" 
          by (metis col_conga__conga not_conga_sym out_col 
              \<open>A B J CongA A B C\<close> \<open>B Out A P\<close> \<open>P \<noteq> B\<close>)
        moreover have "Coplanar C B J P" 
          by (meson \<open>P InAngle C B J\<close> coplanar_perm_9 inangle__coplanar)
        moreover have "Per B P Q'" 
          using \<open>Col P Q Q'\<close> \<open>P \<noteq> Q\<close> \<open>Per B P Q\<close> per_col by blast
        ultimately show ?thesis 
          using LEMME by blast
      qed
      then obtain Y where "B Out C Y" and "Col Q' P Y" 
        by blast
      hence "\<exists> Y. B Out C Y \<and> Col P Q Y" 
        by (metis \<open>Col P Q Q'\<close> \<open>P \<noteq> Q'\<close> col_trivial_3 colx)
    }
    hence "\<forall> A B C D E F P Q.
    Acute A B C \<and> Per D E F \<and> A B C A B C SumA D E F \<and> 
    B Out A P \<and> P \<noteq> Q \<and> Per B P Q \<and> Coplanar A B C Q
\<longrightarrow>
    (\<exists> Y. B Out C Y \<and> Col P Q Y)" 
      by blast
  }
  ultimately show ?thesis 
    using weak_inverse_projection_postulate_def by fastforce
qed

lemma P31_P32:
  shows "Postulate31 \<longleftrightarrow> Postulate32" 
  using Postulate31_def Postulate32_def 
    weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate 
    weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate by blast

lemma P31_P04:
  shows "Postulate31 \<longleftrightarrow> Postulate04" 
  using Postulate04_def Postulate31_def 
    bachmann_s_lotschnittaxiom__weak_inverse_projection_postulate 
    weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom by blast

lemma P04_P33:
  shows "Postulate04 \<longleftrightarrow> Postulate33" 
  using Postulate04_def Postulate33_def 
    bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle 
    weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom by blast

lemma equivalent_postulates_without_any_continuity_bis:
  shows "Postulate04 \<longleftrightarrow> Postulate33 \<and>
Postulate31 \<longleftrightarrow> Postulate04 \<and>
Postulate31 \<longleftrightarrow> Postulate32"
proof -
  have "Postulate31 \<longleftrightarrow> Postulate32" 
    using Postulate31_def Postulate32_def 
      weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate 
      weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate by blast
  moreover have "Postulate31 \<longleftrightarrow> Postulate04" 
    using Postulate04_def Postulate31_def 
      bachmann_s_lotschnittaxiom__weak_inverse_projection_postulate 
      weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom by blast
  moreover have "Postulate04 \<longleftrightarrow> Postulate33" 
    using Postulate04_def Postulate33_def 
      bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle 
      weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom by blast
  ultimately show ?thesis
    by blast
qed

lemma P4_P34:
  assumes "Postulate04"
  shows "Postulate34" 
  using P31_P04 P31_P32 Postulate32_def Postulate34_def 
    assms bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate
    weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom 
    weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate by blast

lemma P01__P35:
  assumes "Postulate01"
  shows "Postulate35"  
  using Postulate01_def Postulate35_def playfair__existential_playfair 
    tarski_s_euclid_implies_playfair_s_postulate assms by blast

lemma P35__P01:
  assumes "greenberg_s_axiom" and
    "Postulate01" 
  shows "Postulate35" 
proof -
  have "Postulate35 \<longrightarrow> Postulate27" 
    by (simp add: Postulate27_def Postulate35_def existential_playfair__rah)
  moreover 
  have "Postulate27 \<longrightarrow> Postulate03" 
    using Cycle_3 by blast 
  moreover
  have "Postulate03 \<longrightarrow> Postulate12" 
    by (simp add: InterCycle1 assms(1))
  moreover have "Postulate12 \<longrightarrow> Postulate09" 
    by (simp add: Postulate09_def Postulate12_def playfair__universal_posidonius_postulate
        playfair_bis__playfair 
        universal_posidonius_postulate__perpendicular_transversal_postulate)
  moreover
  have "Postulate09 \<longrightarrow> Postulate01"
    using Cycle_1 Cycle_2  by blast
  ultimately show ?thesis 
    using P01__P35 assms(2) by fastforce
qed

theorem stronger_legendre_s_first_theorem:
  assumes "aristotle_s_axiom" 
  shows "\<forall> A B C D E F. C A B A B C SumA D E F \<longrightarrow> SAMS D E F B C A"
  using aristotle__obtuse_case_elimination assms t22_20 by blast

theorem legendre_s_first_theorem:
  assumes "archimedes_axiom" 
  shows "\<forall> A B C D E F. C A B A B C SumA D E F \<longrightarrow> SAMS D E F B C A" 
  using assms stronger_legendre_s_first_theorem t22_24 by blast

theorem legendre_s_second_theorem:
  assumes "postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights"
  shows "triangle_postulate" 
  using assms rah__triangle existential_triangle__rah by blast

lemma legendre_s_third_theorem_aux:
  assumes "aristotle_s_axiom" and
    "triangle_postulate"
  shows "euclid_s_parallel_postulate" 
  using Cycle_2 Postulate01_def Postulate13_def 
    alternate_interior__proclus aristotle__greenberg 
    assms(1) assms(2) playfair__alternate_interior 
    playfair_bis__playfair tarski_s_implies_euclid_s_parallel_postulate 
    triangle__playfair_bis by fastforce

theorem legendre_s_third_theorem:
  assumes "archimedes_axiom" and
    "triangle_postulate"
  shows "euclid_s_parallel_postulate" 
  by (simp add: assms(1) assms(2) legendre_s_third_theorem_aux t22_24)

lemma legendre_aux:
  assumes "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" 
  shows "\<forall> A B C D B1 C1 P Q R S T U V W X.
    \<not> Col A B C \<and> A C B CongA C B D \<and>
    Cong A C B D \<and> B C TS A D \<and> A Out B B1 \<and> A Out C C1 \<and> Bet B1 D C1 \<and>
    Defect A B C P Q R \<and> Defect A B1 C1 S T U \<and> P Q R P Q R SumA V W X \<longrightarrow>
    (SAMS P Q R P Q R \<and> V W X LeA S T U)"
proof -
  {
    fix A B C D B1 C1 P Q R S T U V W X
    assume "\<not> Col A B C" and "A C B CongA C B D" and
      "Cong A C B D" and "B C TS A D" and "A Out B B1" and
      "A Out C C1" and "Bet B1 D C1" and
      "Defect A B C P Q R" and "Defect A B1 C1 S T U" and
      "P Q R P Q R SumA V W X"
    have "A \<noteq> B" 
      using \<open>B C TS A D\<close> ts_distincts by blast
    have "Cong A B D C \<and> (A \<noteq> B) \<longrightarrow> (C A B CongA B D C \<and> C B A CongA B C D)"
    proof -
      have "A C B CongA D B C" 
        using \<open>A C B CongA C B D\<close> conga_right_comm by blast
      moreover have "Cong C A B D" 
        using \<open>Cong A C B D\<close> not_cong_2134 by blast
      moreover have "Cong C B B C" 
        by (simp add: cong_pseudo_reflexivity)
      ultimately show ?thesis 
        using \<open>A \<noteq> B\<close> l11_49 by blast
    qed
    have "Cong A B D C" 
      by (metis cong2_conga_cong \<open>A C B CongA C B D\<close> \<open>Cong A C B D\<close> 
          cong_pseudo_reflexivity cong_right_commutativity conga_right_comm)
    have "C A B CongA B D C" 
      by (simp add: \<open>A \<noteq> B\<close> \<open>Cong A B D C\<close>
          \<open>Cong A B D C \<and> A \<noteq> B \<longrightarrow> C A B CongA B D C \<and> C B A CongA B C D\<close> ) 
    have "C B A CongA B C D" 
      by (simp add: \<open>A \<noteq> B\<close> \<open>Cong A B D C\<close>
          \<open>Cong A B D C \<and> A \<noteq> B \<longrightarrow> C A B CongA B D C \<and> C B A CongA B C D\<close> ) 
    have "A C ParStrict B D" 
    proof -
      have "A C Par B D" 
        by (meson conga_right_comm  \<open>A C B CongA C B D\<close> \<open>B C TS A D\<close>
            invert_two_sides l12_21_b par_left_comm)
      moreover have "Col B D B" 
        by (simp add: col_trivial_3)
      moreover have "\<not> Col A C B" 
        using \<open>\<not> Col A B C\<close> col_permutation_5 by blast
      ultimately show ?thesis 
        using par_not_col_strict by blast
    qed
    have "A B ParStrict C D" 
    proof -
      have "A B Par C D" 
      proof -
        have "B C TS A D" 
          using \<open>B C TS A D\<close> by auto
        moreover have "A B C CongA D C B" 
          by (simp add: \<open>C B A CongA B C D\<close> conga_comm)
        ultimately show ?thesis
          using l12_21_b par_left_comm by blast
      qed
      moreover have "Col C D C" 
        by (simp add: col_trivial_3)
      moreover have "\<not> Col A B C" 
        using \<open>\<not> Col A B C\<close> by blast
      ultimately show ?thesis 
        using par_not_col_strict by blast
    qed
    have "\<not> Col B C D" 
      using \<open>A B ParStrict C D\<close> par_strict_not_col_2 by auto
    have "\<not> Col C D A" 
      using \<open>A B ParStrict C D\<close> col_trivial_3 l9_19 pars__os3412 by blast
    have "\<not> Col A B D" 
      by (meson Par_strict_perm \<open>A B ParStrict C D\<close> l12_6 one_side_not_col123)
    have "B D ParStrict A C1" 
      by (metis Par_strict_cases \<open>A C ParStrict B D\<close> \<open>A Out C C1\<close> 
          out_col out_diff2 par_strict_col_par_strict)
    have "\<not> Col B D C1" 
      by (metis Par_strict_perm \<open>A Out C C1\<close> \<open>B D ParStrict A C1\<close>
          diff_bet_ex3 l6_16_1 l6_3_1 l9_19 pars__os3412)
    have "B \<noteq> B1" 
      using \<open>Bet B1 D C1\<close> \<open>\<not> Col B D C1\<close> bet_col by blast
    have "\<not> Col B1 B D" 
      by (metis \<open>A Out B B1\<close> \<open>B \<noteq> B1\<close> \<open>\<not> Col A B D\<close> col_trivial_2 colx out_col)
    have "B D TS B1 C1" 
      using TS_def \<open>Bet B1 D C1\<close> \<open>\<not> Col B D C1\<close> \<open>\<not> Col B1 B D\<close>
        col_trivial_3 not_col_permutation_2 by blast
    hence "\<not> Col B1 B D \<and> B D TS B1 C1 \<and> Bet A B B1" 
      by (metis \<open>A Out B B1\<close> \<open>B D ParStrict A C1\<close> \<open>\<not> Col B1 B D\<close> 
          col_trivial_3 l12_6 l9_9 not_out_bet out_col out_two_sides_two_sides)
    have "Bet A B B1" 
      by (simp add: \<open>\<not> Col B1 B D \<and> B D TS B1 C1 \<and> Bet A B B1\<close>)
    have "C D ParStrict A B1" 
      by (metis Col_def \<open>A B ParStrict C D\<close> \<open>Bet A B B1\<close>
          between_identity col_trivial_3 par_strict_col2_par_strict
          par_strict_symmetry)
    have "\<not> Col C D B1" 
      by (meson Par_strict_perm \<open>C D ParStrict A B1\<close> l12_6 one_side_not_col123)
    have "C \<noteq> C1" 
      using \<open>Bet B1 D C1\<close> \<open>\<not> Col C D B1\<close> bet_col between_symmetry by blast
    have "C D TS A C1" 
    proof -
      have "C D TS B1 C1" 
        by (metis \<open>Bet B1 D C1\<close> \<open>\<not> Col B D C1\<close> \<open>\<not> Col C D B1\<close> 
            bet__ts col_trivial_2 invert_two_sides not_col_permutation_4)
      moreover have "C D OS B1 A" 
        using \<open>C D ParStrict A B1\<close> l12_6 one_side_symmetry by blast
      ultimately show ?thesis
        using l9_8_2 by blast
    qed
    hence "Bet A C C1" 
      using \<open>A Out C C1\<close> col_two_sides_bet not_out_bet out_col by blast
    have "\<exists> Z. Bet B Z D \<and> Bet C Z B1" 
    proof -
      have "B D TS C B1" 
      proof -
        have "B D TS C1 B1" 
          using \<open>B D TS B1 C1\<close> l9_2 by blast
        moreover have "B D OS C1 C" 
          by (metis bet_col1 l12_6 par_strict_col2_par_strict 
              \<open>B D ParStrict A C1\<close> \<open>Bet A C C1\<close> \<open>C \<noteq> C1\<close> not_bet_distincts)
        ultimately show ?thesis
          using l9_8_2 by blast
      qed
      moreover have "C B1 TS B D" 
      proof -
        have "C D OS B1 B" 
        proof -
          have "C D ParStrict B A" 
            using Par_strict_perm \<open>A B ParStrict C D\<close> by blast
          moreover have "Col B A B1" 
            using \<open>A Out B B1\<close> col_permutation_4 out_col by blast
          ultimately show ?thesis
            using \<open>B \<noteq> B1\<close> one_side_symmetry par_strict_all_one_side by blast
        qed
        have "C B OS B1 C1" 
        proof -
          have "C B TS B1 A"                             
            by (meson \<open>B \<noteq> B1\<close> \<open>Bet A B B1\<close> \<open>\<not> Col A B C\<close> bet__ts invert_two_sides
                l9_2 not_col_permutation_1)
          moreover have "C B TS C1 A"                            
            using Col_cases \<open>Bet A C C1\<close> \<open>C \<noteq> C1\<close> \<open>\<not> Col A B C\<close> bet__ts l9_2 by blast
          ultimately show ?thesis
            using OS_def by blast
        qed
        hence "C B OS B1 D" 
          using \<open>Bet B1 D C1\<close> l9_17 by blast
        moreover 
        have "C D OS B1 B" 
          using \<open>C D OS B1 B\<close> by blast
        ultimately show ?thesis
          using  l9_31 by auto
      qed
      ultimately show ?thesis 
        using ts2__ex_bet2 by blast
    qed
    then obtain Z where "Bet B Z D" and "Bet C Z B1" 
      by blast
    obtain G H I where "Defect A B1 C G H I"
      using ex_defect 
      by (metis Col_def \<open>A Out B B1\<close> \<open>Bet A B B1\<close> \<open>\<not> Col A B C\<close> 
          not_col_distincts out_diff2)
    obtain J K L where "Defect B1 C C1 J K L"
      using ex_defect 
      by (metis Col_def TS_def \<open>B C TS A D\<close> \<open>Bet B Z D\<close> \<open>Bet C Z B1\<close> 
          \<open>C \<noteq> C1\<close> \<open>Defect A B1 C1 S T U\<close> bet_neq12__neq defect_distincts)
    have "C \<noteq> B1" 
      using \<open>\<not> Col C D B1\<close> col_trivial_3 by blast
    have "B1 \<noteq> B" 
      using \<open>B \<noteq> B1\<close> by auto
    have "C \<noteq> B" 
      using \<open>\<not> Col B C D\<close> col_trivial_1 by fastforce
    obtain M N O0 where "Defect C B B1 M N O0"
      using ex_defect \<open>C \<noteq> B\<close> \<open>C \<noteq> B1\<close> \<open>B \<noteq> B1\<close> by blast
    have "B1 \<noteq> C" 
      using \<open>C \<noteq> B1\<close> by auto
    have "C \<noteq> D" 
      using \<open>\<not> Col B C D\<close> col_trivial_2 by blast
    have "B1 \<noteq> D" 
      using \<open>B D TS B1 C1\<close> ts_distincts by blast
    obtain A' B' C' where "Defect B1 C D A' B' C'" 
      using ex_defect \<open>B1 \<noteq> D\<close> \<open>C \<noteq> B1\<close> \<open>C \<noteq> D\<close> by presburger
    have "D \<noteq> C1" 
      using \<open>C D TS A C1\<close> ts_distincts by blast
    obtain D' E' F' where "Defect C D C1 D' E' F'" 
      using ex_defect \<open>C \<noteq> C1\<close> \<open>C \<noteq> D\<close> \<open>D \<noteq> C1\<close> by presburger
    obtain M' N' O' where "Defect B1 B D M' N' O'" 
      using ex_defect \<open>B \<noteq> B1\<close> \<open>B1 \<noteq> D\<close> \<open>C A B CongA B D C\<close> 
        conga_distinct by presburger
    have "G \<noteq> H" 
      using \<open>Defect A B1 C G H I\<close> defect_distincts by blast
    have "I \<noteq> H" 
      using \<open>Defect A B1 C G H I\<close> defect_distincts by blast
    have "M \<noteq> N" 
      using \<open>Defect C B B1 M N O0\<close> defect_distincts by blast
    have "N \<noteq> O0" 
      using \<open>Defect C B B1 M N O0\<close> defect_distincts by blast
    have "A' \<noteq> B'" 
      using \<open>Defect B1 C D A' B' C'\<close> defect_distincts by blast
    have "C' \<noteq> B'" 
      using \<open>Defect B1 C D A' B' C'\<close> defect_distincts by blast
    obtain G' H' I' where "G H I A' B' C' SumA G' H' I'" 
      using \<open>A' \<noteq> B'\<close> \<open>C' \<noteq> B'\<close> \<open>G \<noteq> H\<close> \<open>I \<noteq> H\<close> ex_suma by presburger
    have "O0 \<noteq> N" 
      using \<open>N \<noteq> O0\<close> by blast
    then obtain J' K' L' where "M N O0 A' B' C' SumA J' K' L'"
      using \<open>A' \<noteq> B'\<close> \<open>C' \<noteq> B'\<close> \<open>M \<noteq> N\<close> ex_suma by presburger
    have "SAMS G H I J K L \<and> G H I J K L SumA S T U" 
      using assms \<open>Bet A C C1\<close> t22_16_1bis \<open>Defect A B1 C G H I\<close> \<open>Defect A B1 C1 S T U\<close>
        \<open>Defect B1 C C1 J K L\<close> by force
    hence "SAMS G H I J K L" 
      by blast
    have "G H I J K L SumA S T U" 
      using \<open>SAMS G H I J K L \<and> G H I J K L SumA S T U\<close> by auto    
    have "SAMS A' B' C' D' E' F' \<and> A' B' C' D' E' F' SumA J K L" 
      using assms \<open>Bet B1 D C1\<close> t22_16_1bis \<open>Defect B1 C C1 J K L\<close> \<open>Defect B1 C D A' B' C'\<close> 
        \<open>Defect C D C1 D' E' F'\<close> by blast
    hence "SAMS A' B' C' D' E' F'" 
      by blast
    have "A' B' C' D' E' F' SumA J K L" 
      by (simp add: \<open>SAMS A' B' C' D' E' F' \<and> A' B' C' D' E' F' SumA J K L\<close>)
    have "SAMS P Q R M N O0 \<and> P Q R M N O0 SumA G H I"
    proof -
      have "Defect A C B P Q R" 
        using \<open>Defect A B C P Q R\<close> defect_perm_132 by blast
      moreover have "Defect A C B1 G H I" 
        using \<open>Defect A B1 C G H I\<close> defect_perm_132 by blast
      ultimately show ?thesis
        using \<open>Bet A B B1\<close> \<open>Defect C B B1 M N O0\<close> assms t22_16_1bis by blast
    qed
    hence "SAMS P Q R M N O0" 
      by blast
    have "P Q R M N O0 SumA G H I" 
      by (simp add: \<open>SAMS P Q R M N O0 \<and> P Q R M N O0 SumA G H I\<close>)
    have "SAMS G H I A' B' C'"
    proof -
      have "G H I LeA G H I" 
        by (simp add: \<open>G \<noteq> H\<close> \<open>I \<noteq> H\<close> lea_refl)
      moreover have "A' B' C' LeA J K L" 
        using \<open>SAMS A' B' C' D' E' F'\<close> \<open>A' B' C' D' E' F' SumA J K L\<close> 
          sams_suma__lea123789 by blast
      ultimately show ?thesis
        using \<open>SAMS G H I J K L\<close> sams_lea2__sams by blast
    qed
    have "SAMS M N O0 A' B' C'" 
    proof -
      have "M N O0 LeA G H I"      
        using \<open>SAMS P Q R M N O0\<close> \<open>P Q R M N O0 SumA G H I\<close> 
          sams_suma__lea456789 by auto
      moreover have "A' B' C' LeA A' B' C'"        
        using \<open>A' \<noteq> B'\<close> \<open>C' \<noteq> B'\<close> lea_refl by auto
      ultimately show ?thesis
        using \<open>SAMS G H I A' B' C'\<close> sams_lea2__sams by blast
    qed
    have "G' H' I' D' E' F' SumA S T U"
      using \<open>SAMS G H I A' B' C'\<close> \<open>SAMS A' B' C' D' E' F'\<close> 
        \<open>G H I A' B' C' SumA G' H' I'\<close> \<open>A' B' C' D' E' F' SumA J K L\<close> 
        \<open>G H I J K L SumA S T U\<close> suma_assoc by blast
    have "SAMS G' H' I' D' E' F'"
      using \<open>SAMS G H I A' B' C'\<close> \<open>SAMS A' B' C' D' E' F'\<close> 
        \<open>G H I A' B' C' SumA G' H' I'\<close> \<open>A' B' C' D' E' F' SumA J K L\<close>  
        \<open>SAMS G H I J K L\<close> sams_assoc by blast
    have "P Q R J' K' L' SumA G' H' I'" 
      using \<open>SAMS P Q R M N O0\<close> \<open>SAMS M N O0 A' B' C'\<close> 
        \<open>P Q R M N O0 SumA G H I\<close> \<open>M N O0 A' B' C' SumA J' K' L'\<close> 
        \<open>G H I A' B' C' SumA G' H' I'\<close> suma_assoc_1 by blast
    have "SAMS P Q R J' K' L'" 
      using \<open>SAMS P Q R M N O0\<close> \<open>SAMS M N O0 A' B' C'\<close> 
        \<open>P Q R M N O0 SumA G H I\<close> \<open>M N O0 A' B' C' SumA J' K' L'\<close> 
        \<open>SAMS G H I A' B' C'\<close> sams_assoc_1 by blast
    have "P \<noteq> Q" 
      using \<open>P Q R P Q R SumA V W X\<close> suma_distincts by auto
    have "Q \<noteq> R" 
      using \<open>P Q R P Q R SumA V W X\<close> suma_distincts by blast
    have "SAMS P Q R M' N' O' \<and> P Q R M' N' O' SumA J' K' L'" 
    proof -
      have "Defect C B D P Q R" 
      proof -
        have "A B C CongA D C B" 
          by (simp add: \<open>C B A CongA B C D\<close> conga_comm)
        moreover have "B C A CongA C B D" 
          using \<open>A C B CongA C B D\<close> conga_left_comm by blast
        ultimately show ?thesis
          using \<open>Defect A B C P Q R\<close> \<open>C A B CongA B D C\<close> conga3_defect__defect 
            defect_perm_231 by blast
      qed
      moreover have "Defect C D B1 A' B' C'" 
        by (simp add: \<open>Defect B1 C D A' B' C'\<close> defect_perm_231)
      ultimately show ?thesis 
        using \<open>Defect C B B1 M N O0\<close> \<open>Defect B1 B D M' N' O'\<close> \<open>Bet C Z B1\<close> 
          \<open>Bet B Z D\<close> \<open>SAMS M N O0 A' B' C'\<close> \<open>M N O0 A' B' C' SumA J' K' L'\<close>
          assms t22_16_2 by blast
    qed
    have "P Q R LeA J' K' L'" 
      using \<open>SAMS P Q R M' N' O' \<and> P Q R M' N' O' SumA J' K' L'\<close> 
        sams_suma__lea123789 by blast
    have "SAMS P Q R P Q R" 
    proof -
      have "P Q R LeA P Q R" 
        using \<open>P \<noteq> Q\<close> \<open>Q \<noteq> R\<close> lea_refl by force
      thus ?thesis
        using  \<open>SAMS P Q R J' K' L'\<close> \<open>P Q R LeA J' K' L'\<close> sams_lea2__sams by blast
    qed
    moreover have "V W X LeA S T U" 
    proof -
      have "V W X LeA G' H' I'" 
        using \<open>P Q R LeA J' K' L'\<close> \<open>SAMS P Q R J' K' L'\<close> 
          \<open>P Q R P Q R SumA V W X\<close> \<open>P Q R J' K' L' SumA G' H' I'\<close> 
          sams_lea456_suma2__lea by blast
      moreover have "G' H' I' LeA S T U" 
        using \<open>G' H' I' D' E' F' SumA S T U\<close> \<open>SAMS G' H' I' D' E' F'\<close> 
          sams_suma__lea123789 by blast
      ultimately show ?thesis 
        using lea_trans by blast
    qed
    ultimately have "SAMS P Q R P Q R \<and> V W X LeA S T U" 
      by blast
  }
  thus ?thesis 
    by blast
qed

lemma legendre_aux1:
  shows "\<forall> A B C B' C'.
  \<not> Col A B C \<and> A Out B B' \<and> A Out C C' \<longrightarrow>
  (\<exists> D'. D' InAngle B A C \<and> A C' B' CongA C' B' D' \<and>
             Cong A C' B' D' \<and> B' C' TS A D')" 
proof -
  {
    fix A B C B' C'
    assume "\<not> Col A B C" and "A Out B B'" and "A Out C C'" 
    have "A \<noteq> B'" 
      using Out_def \<open>A Out B B'\<close> by force
    have "A \<noteq> C'" 
      using \<open>A Out C C'\<close> out_diff2 by blast
    have "B' \<noteq> C'" 
      using \<open>A Out B B'\<close> \<open>A Out C C'\<close> \<open>\<not> Col A B C\<close> l6_6 l6_7 out_col by blast
    {
      assume "Col A B' C'"
      hence "Col A B C" 
        by (metis Col_perm \<open>A Out B B'\<close> \<open>A Out C C'\<close> \<open>A \<noteq> B'\<close> 
            \<open>A \<noteq> C'\<close> col_transitivity_1 out_col)
      hence False 
        using \<open>\<not> Col A B C\<close> by blast
    }
    hence "\<not> Col A B' C'" 
      by blast
    obtain M where "M Midpoint B' C'" 
      using midpoint_existence by blast
    have "A \<noteq> M" 
      using Bet_cases Col_def Midpoint_def \<open>Col A B' C' \<Longrightarrow> False\<close> 
        \<open>M Midpoint B' C'\<close> by blast
    have "M \<noteq> B'" 
      using \<open>Col A B' C' \<Longrightarrow> False\<close> \<open>M Midpoint B' C'\<close> 
        col_trivial_2 is_midpoint_id by blast
    have "M \<noteq> C'" 
      using \<open>M Midpoint B' C'\<close> \<open>M \<noteq> B'\<close> is_midpoint_id_2 by blast
    obtain D' where "M Midpoint A D'" 
      using symmetric_point_construction by blast
    {
      assume "Col A M B'"
      hence "Col A B' C'" 
        by (metis Col_def Midpoint_def \<open>M Midpoint B' C'\<close> \<open>M \<noteq> B'\<close> l6_16_1)
      hence False 
        using  \<open>Col A B' C' \<Longrightarrow> False\<close> by blast
    }
    hence "\<not> Col A M B'" 
      by blast
    have "A \<noteq> D'" 
      using \<open>M Midpoint A D'\<close> \<open>\<not> Col A M B'\<close> col_trivial_1 l7_3 by blast
    hence "M \<noteq> D'" 
      using \<open>M Midpoint A D'\<close> is_midpoint_id_2 by blast
    have "Col A D' M" 
      using Bet_cases Col_def Midpoint_def \<open>M Midpoint A D'\<close> by blast
    have "Col B' C' M" using \<open>M Midpoint B' C'\<close> 
      by (meson midpoint_col not_col_permutation_2)
    {
      assume "Col D' B' C'"
      hence "Col A B' C'" 
        by (metis (full_types) \<open>Col A D' M\<close> \<open>Col B' C' M\<close> 
            \<open>M \<noteq> D'\<close> col_permutation_2 colx)
      hence False 
        using  \<open>Col A B' C' \<Longrightarrow> False\<close> by blast
    }
    hence "\<not> Col D' B' C'" 
      by blast
    have "D' InAngle B A C"
    proof -
      have "D' InAngle B' A C'" 
      proof -
        have "Bet B' M C'" 
          using Midpoint_def \<open>M Midpoint B' C'\<close> by blast
        moreover have "Bet A M D'" 
          using Midpoint_def \<open>M Midpoint A D'\<close> by auto
        moreover hence "M = A \<or> A Out M D'" 
          using bet_out by blast
        ultimately show ?thesis
          using InAngle_def \<open>A \<noteq> B'\<close> \<open>A \<noteq> C'\<close> \<open>A \<noteq> D'\<close> by auto
      qed
      moreover have "A Out D' D'"   
        using \<open>A \<noteq> D'\<close> out_trivial by auto
      ultimately show ?thesis
        using  \<open>A Out B B'\<close> \<open>A Out C C'\<close> l11_25 by blast
    qed
    moreover have "A C' B' CongA C' B' D'" 
    proof -
      have "A M C' CongA D' M B'" 
      proof -
        have "Bet A M D'" 
          using \<open>M Midpoint A D'\<close> by (simp add: Midpoint_def)
        moreover have "Bet C' M B'" 
          using Bet_cases Midpoint_def \<open>M Midpoint B' C'\<close> by blast
        ultimately show ?thesis
          using \<open>M \<noteq> B'\<close> \<open>M \<noteq> C'\<close> \<open>M \<noteq> D'\<close> \<open>A \<noteq> M\<close> l11_14 by blast
      qed
      moreover have "Cong M A M D'" 
        using Cong_cases \<open>M Midpoint A D'\<close> midpoint_cong by blast
      moreover have "Cong M C' M B'" 
        using \<open>M Midpoint B' C'\<close> midpoint_cong not_cong_4312 by blast
      ultimately show ?thesis
        by (meson Mid_cases \<open>A \<noteq> C'\<close> \<open>B' \<noteq> C'\<close> \<open>M Midpoint A D'\<close> 
            \<open>M Midpoint B' C'\<close> conga_right_comm symmetry_preserves_conga)
    qed
    moreover have "Cong A C' B' D'" 
      by (metis l7_13 \<open>M Midpoint A D'\<close> \<open>M Midpoint B' C'\<close> cong_3421 l7_2)
    moreover have "B' C' TS A D'" 
      using Midpoint_def TS_def \<open>Col A B' C' \<Longrightarrow> False\<close> \<open>Col B' C' M\<close> 
        \<open>M Midpoint A D'\<close> \<open>\<not> Col D' B' C'\<close> not_col_permutation_1 by blast
    ultimately have "\<exists> D'. D' InAngle B A C \<and> A C' B' CongA C' B' D' \<and>
             Cong A C' B' D' \<and> B' C' TS A D'" 
      by blast
  }
  thus ?thesis 
    by blast
qed

lemma legendre_aux2:
  assumes "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals"
  shows "\<forall> A B C.
    \<not> Col A B C \<and> Acute B A C \<and>
    (\<forall> T. T InAngle B A C \<longrightarrow> (\<exists> X Y. A Out B X \<and> A Out C Y \<and> Bet X T Y)) 
       \<longrightarrow>
    (\<forall> P Q R S T U. Defect A B C P Q R \<and> GradAExp P Q R S T U \<longrightarrow>
      (\<exists> B' C' P' Q' R'. (A Out B B' \<and> A Out C C' \<and>
         Defect A B' C' P' Q' R' \<and> S T U LeA P' Q' R')))" 
proof -
  {
    fix A B C
    assume "\<not> Col A B C" and 
      "Acute B A C" and
      "\<forall> T. T InAngle B A C \<longrightarrow> (\<exists> X Y. A Out B X \<and> A Out C Y \<and> Bet X T Y)" 
    {
      fix P Q R S T U
      assume "Defect A B C P Q R" and
        "GradAExp P Q R S T U"
      let ?th = " (\<exists> B' C' P' Q' R'. (A Out B B' \<and> A Out C C' \<and>
         Defect A B' C' P' Q' R' \<and> S T U LeA P' Q' R'))"
      have ?th 
      proof (rule GradAExp.induct [OF \<open>GradAExp P Q R S T U\<close>])
        show "\<And>D E F.
       P Q R CongA D E F \<Longrightarrow>
       \<exists>B' C' P' Q' R'.
          A Out B B' \<and>
          A Out C C' \<and> Defect A B' C' P' Q' R'  \<and> D E F LeA P' Q' R'" 
          by (metis \<open>Defect A B C P Q R\<close> bet_out_1 conga__lea456123 
              defect_distincts not_bet_distincts)
        {
          fix S T U G H I
          assume "GradAExp P Q R S T U" and
            P1: "\<exists>B' C' P' Q' R'. A Out B B' \<and> A Out C C' \<and> Defect A B' C' P' Q' R' \<and> 
                                  S T U LeA P' Q' R'" and
            "SAMS S T U S T U" and
            "S T U S T U SumA G H I" 
          obtain B' C' P' Q' R' where "A Out B B'" and "A Out C C'" and 
            "Defect A B' C' P' Q' R'" and "S T U LeA P' Q' R'" using P1 by blast
          obtain D' where "D' InAngle B A C" and "A C' B' CongA C' B' D'" and
            "Cong A C' B' D'" and "B' C' TS A D'" 
            using legendre_aux1 \<open>A Out B B'\<close> \<open>A Out C C'\<close> \<open>\<not> Col A B C\<close> by blast
          have "\<not> Col A B' C'" 
            using TS_def \<open>B' C' TS A D'\<close> by presburger
          obtain B'' C'' where "A Out B B''" and "A Out C C''" and "Bet B'' D' C''"
            using \<open>D' InAngle B A C\<close> 
              \<open>\<forall>T. T InAngle B A C \<longrightarrow> (\<exists>X Y. A Out B X \<and> A Out C Y \<and> Bet X T Y)\<close> by blast
          have "Q' \<noteq> P'" 
            using \<open>Defect A B' C' P' Q' R'\<close> defect_distincts by blast
          have "Q' \<noteq> R'" 
            using \<open>Defect A B' C' P' Q' R'\<close> defect_distincts by blast
          have "A \<noteq> C''" 
            using \<open>A Out C C''\<close> l6_3_1 by blast
          have "A \<noteq> B''" 
            using \<open>A Out B B''\<close> out_distinct by blast
          have "B'' \<noteq> C''" 
            by (metis Col_def Out_def \<open>A Out B B''\<close> \<open>A Out C C''\<close>
                \<open>\<not> Col A B C\<close> between_symmetry l6_7)
          then obtain P'' Q'' R'' where "Defect A B'' C'' P'' Q'' R''"
            using ex_defect \<open>A \<noteq> B''\<close> \<open>A \<noteq> C''\<close> by presburger
          moreover 
          obtain V W X where "P' Q' R' P' Q' R' SumA V W X"
            using ex_suma \<open>Q' \<noteq> P'\<close> \<open>Q' \<noteq> R'\<close> by presburger
          have "SAMS P' Q' R' P' Q' R' \<and> V W X LeA P'' Q'' R''"
          proof -
            have "A Out B' B''" 
              using \<open>A Out B B''\<close> \<open>A Out B B'\<close> l6_6 l6_7 by blast
            moreover have "A Out C' C''" 
              using \<open>A Out C C''\<close> \<open>A Out C C'\<close> l6_6 l6_7 by blast
            ultimately show ?thesis
              using assms \<open>\<not> Col A B' C'\<close> \<open>A C' B' CongA C' B' D'\<close> \<open>Cong A C' B' D'\<close>
                \<open>B' C' TS A D'\<close> \<open>P' Q' R' P' Q' R' SumA V W X\<close> \<open>Bet B'' D' C''\<close>
                \<open>Defect A B' C' P' Q' R'\<close> \<open>Defect A B'' C'' P'' Q'' R''\<close> legendre_aux by blast
          qed
          have "G H I LeA P'' Q'' R''" 
          proof -
            have "G H I LeA V W X" 
              using sams_lea2_suma2__lea [where ?A="S" and ?B="T" and ?C="U" and
                  ?D="S" and ?E="T" and ?F="U" and ?A'="P'" and ?B'="Q'" and ?C'="R'" and
                  ?D'="P'" and ?E'="Q'" and ?F'="R'"] \<open>S T U LeA P' Q' R'\<close> \<open>S T U LeA P' Q' R'\<close>
                \<open>SAMS P' Q' R' P' Q' R' \<and> V W X LeA P'' Q'' R''\<close> 
                \<open>S T U S T U SumA G H I\<close> \<open>P' Q' R' P' Q' R' SumA V W X\<close>
              by blast
            moreover have "V W X LeA P'' Q'' R''" 
              using \<open>SAMS P' Q' R' P' Q' R' \<and> V W X LeA P'' Q'' R''\<close> by blast
            ultimately show ?thesis
              using lea_trans by blast
          qed
          ultimately have "\<exists>B' C' P' Q' R'. A Out B B' \<and> A Out C C' \<and> 
                               Defect A B' C' P' Q' R' \<and> G H I LeA P' Q' R'" 
            using \<open>A Out B B''\<close> \<open>A Out C C''\<close> by blast
        }
        thus "\<And>D E F G H I.
       GradAExp P Q R D E F \<Longrightarrow>
       \<exists>B' C' P' Q' R'.
          A Out B B' \<and> A Out C C' \<and> Defect A B' C' P' Q' R' \<and> D E F LeA P' Q' R' \<Longrightarrow>
       SAMS D E F D E F \<Longrightarrow>
       D E F D E F SumA G H I \<Longrightarrow>
       \<exists>B' C' P' Q' R'.
          A Out B B' \<and>
          A Out C C' \<and> Defect A B' C' P' Q' R'  \<and> G H I LeA P' Q' R'" 
          by blast
      qed
    }
    hence "(\<forall> P Q R S T U.
      Defect A B C P Q R \<and> GradAExp P Q R S T U \<longrightarrow>
      (\<exists> B' C' P' Q' R'.
        (A Out B B' \<and> A Out C C' \<and>
         Defect A B' C' P' Q' R' \<and> S T U LeA P' Q' R')))" by blast
  }
  thus ?thesis
    by blast
qed

lemma legendre_s_fourth_theorem_aux:
  assumes "archimedes_axiom" and
    "legendre_s_parallel_postulate"
  shows "postulate_of_right_saccheri_quadrilaterals" 
proof -
  obtain A B C where "\<not> Col B A C" and "Acute B A C" and
    "\<forall> T. (T InAngle B A C) \<longrightarrow> (\<exists> X Y. A Out B X \<and> A Out C Y \<and> Bet X T Y)" 
    using assms(2) legendre_s_parallel_postulate_def by blast
  have "A \<noteq> B" 
    using \<open>Acute B A C\<close> acute_distincts by auto
  have "A \<noteq> C" 
    using \<open>\<not> Col B A C\<close> not_col_distincts by auto
  have "B \<noteq> C" 
    using \<open>\<not> Col B A C\<close> col_trivial_3 by auto
  obtain P Q R where "Defect A B C P Q R" 
    using \<open>A \<noteq> B\<close> \<open>A \<noteq> C\<close> \<open>B \<noteq> C\<close> ex_defect by presburger
  {
    assume "Col P Q R"
    hence "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" 
      using archi__obtuse_case_elimination assms(1) by presburger
    moreover have "\<not> Col A B C" 
      by (simp add: \<open>\<not> Col B A C\<close> not_col_permutation_4)
    moreover have "Q Out P R" 
    proof -
      {
        assume "Bet P Q R"
        have "Defect B A C P Q R" 
          using \<open>Defect A B C P Q R\<close> defect_perm_213 by blast
        then obtain D E F G H I where "B A C A C B SumA G H I" and
          "G H I C B A SumA D E F" and "D E F SuppA P Q R"
          using Defect_def TriSumA_def by auto
        have "Col B A C"
        proof -
          have "P Q R SuppA D E F" 
            by (simp add: \<open>D E F SuppA P Q R\<close> suppa_sym)
          hence "E Out D F"
            using \<open>Bet P Q R\<close> bet_suppa__out by blast
          moreover 
          have "SAMS G H I C B A" 
            using \<open>B A C A C B SumA G H I\<close> assms(1) legendre_s_first_theorem by blast
          hence "C B A LeA D E F"
            using \<open>G H I C B A SumA D E F\<close> sams_suma__lea456789 by blast
          ultimately show ?thesis 
            using l6_6 out_col out_lea__out by blast
        qed
        hence False 
          by (simp add: \<open>\<not> Col B A C\<close>)
      }
      hence "\<not> Bet P Q R" 
        by blast
      thus ?thesis 
        using \<open>Col P Q R\<close> l6_4_2 by blast
    qed
    ultimately
    have "postulate_of_right_saccheri_quadrilaterals" 
      using \<open>Defect A B C P Q R\<close> defect_ncol_out__rah 
        existential_playfair__rah_1 by blast
  }
  moreover
  {
    assume "\<not> Col P Q R"
    obtain S T U where "GradAExp P Q R S T U" and "Obtuse S T U" 
      using  archi__gradaexp_destruction \<open>\<not> Col P Q R\<close> assms(1) by blast
    have "\<not> hypothesis_of_obtuse_saccheri_quadrilaterals" 
      by (simp add: archi__obtuse_case_elimination assms(1))
    hence P2: "\<forall> A B C.
    \<not> Col A B C \<and> Acute B A C \<and>
    (\<forall> T. T InAngle B A C \<longrightarrow> (\<exists> X Y. A Out B X \<and> A Out C Y \<and> Bet X T Y)) 
       \<longrightarrow>
    (\<forall> P Q R S T U. Defect A B C P Q R \<and> GradAExp P Q R S T U \<longrightarrow>
      (\<exists> B' C' P' Q' R'. (A Out B B' \<and> A Out C C' \<and>
         Defect A B' C' P' Q' R' \<and> S T U LeA P' Q' R')))" 
      using legendre_aux2 by blast
    moreover have "\<not> Col A B C" 
      by (simp add: \<open>\<not> Col B A C\<close> not_col_permutation_4)
    ultimately have "\<exists> B' C' P' Q' R'. (A Out B B' \<and> A Out C C' \<and>
         Defect A B' C' P' Q' R' \<and> S T U LeA P' Q' R')" 
      using \<open>\<forall>T. T InAngle B A C \<longrightarrow> (\<exists>X Y. A Out B X \<and> A Out C Y \<and> Bet X T Y)\<close> \<open>Acute B A C\<close> 
        \<open>Defect A B C P Q R\<close> \<open>GradAExp P Q R S T U\<close> by blast
    then obtain B' C' P' Q' R' where "A Out B B'" and "A Out C C'" and  
      "Defect A B' C' P' Q' R'" and " S T U LeA P' Q' R'" 
      by blast
    have "\<not> SAMS P' Q' R' P' Q' R'" 
      using lea_obtuse_obtuse \<open>Obtuse S T U\<close> \<open>S T U LeA P' Q' R'\<close> obtuse__nsams by blast
    obtain D' where "D' InAngle B A C" and "A C' B' CongA C' B' D'" and 
      "Cong A C' B' D'" and "B' C' TS A D'" 
      using legendre_aux1 \<open>A Out B B'\<close> \<open>A Out C C'\<close> \<open>\<not> Col A B C\<close> by blast
    have "\<not> Col A B' C'" 
      using TS_def \<open>B' C' TS A D'\<close> by auto
    obtain B'' C'' where "A Out B B''" and "A Out C C''" and "Bet B'' D' C''" 
      using \<open>D' InAngle B A C\<close> 
        \<open>\<forall>T. T InAngle B A C \<longrightarrow> (\<exists>X Y. A Out B X \<and> A Out C Y \<and> Bet X T Y)\<close> 
      by blast
    have "A \<noteq> B''" 
      using Out_def \<open>A Out B B''\<close> by auto
    have "A \<noteq> C''" 
      using \<open>A Out C C''\<close> l6_3_1 by blast
    have "B'' \<noteq> C''" 
      using \<open>A Out B B''\<close> \<open>A Out C C''\<close> \<open>\<not> Col A B C\<close> l6_6 l6_7 out_col by blast
    then obtain S' T' U' where "Defect A B'' C'' S' T' U'" 
      using ex_defect \<open>A \<noteq> B''\<close> \<open>A \<noteq> C''\<close> by presburger
    have "P' \<noteq> Q'" 
      using \<open>Defect A B' C' P' Q' R'\<close> defect_distincts by blast
    have "R' \<noteq> Q'" 
      using \<open>S T U LeA P' Q' R'\<close> lea_distincts by blast
    then obtain V W X where "P' Q' R' P' Q' R' SumA V W X"
      using ex_suma \<open>P' \<noteq> Q'\<close> by presburger
    have " SAMS P' Q' R' P' Q' R'" 
    proof -
      have "A Out B' B''" 
        using Out_cases \<open>A Out B B''\<close> \<open>A Out B B'\<close> l6_7 by blast
      moreover have "A Out C' C''" 
        using \<open>A Out C C''\<close> \<open>A Out C C'\<close> l6_6 l6_7 by blast
      ultimately show ?thesis
        using legendre_aux \<open>P' Q' R' P' Q' R' SumA V W X\<close> \<open>Defect A B' C' P' Q' R'\<close> 
          \<open>Defect A B'' C'' S' T' U'\<close> \<open>\<not> Col A B' C'\<close> \<open>A C' B' CongA C' B' D'\<close>
          \<open>Cong A C' B' D'\<close> \<open>B' C' TS A D'\<close> \<open>Bet B'' D' C''\<close>
          \<open>\<not> HypothesisObtuseSaccheriQuadrilaterals\<close> by blast
    qed
    hence "False" using \<open>\<not> SAMS P' Q' R' P' Q' R'\<close> by blast
    hence "\<forall> A B C D. Saccheri A B C D \<longrightarrow> Per A B C" 
      by blast
  }
  ultimately show ?thesis 
    using postulate_of_right_saccheri_quadrilaterals_def by blast
qed

theorem legendre_s_fourth_theorem:
  assumes "archimedes_axiom" and
    "legendre_s_parallel_postulate" 
  shows "postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights" 
  using assms(1) assms(2) legendre_s_fourth_theorem_aux rah__triangle 
    triangle__existential_triangle by blast

lemma P34_P21:
  assumes "archimedes_axiom" and 
    "Postulate34"
  shows "Postulate21"
  using assms(1) assms(2) legendre_s_fourth_theorem Postulate21_def Postulate34_def by blast

lemma P34_P27:
  assumes "archimedes_axiom" and 
    "Postulate34"
  shows "Postulate27" 
proof -
  have "Postulate21"
    using P34_P21 assms(1) assms(2) by blast
  thus ?thesis
    using Cycle_3 by blast
qed

lemma P25_33:
  assumes "Postulate25"
  shows "Postulate33" 
  using Postulate25_def Postulate33_def assms 
    thales_converse_postulate__weak_triangle_circumscription_principle by auto

lemma P23_33:
  assumes "Postulate23"
  shows "Postulate33" 
proof -
  have "Postulate25" 
    using assms(1) Cycle_3 by blast
  thus ?thesis
    using P25_33 by blast
qed

lemma P01_35:
  assumes "Postulate01"
  shows "Postulate35" 
  using Postulate01_def Postulate35_def assms playfair__existential_playfair 
    tarski_s_euclid_implies_playfair_s_postulate by blast

lemma P35_27:
  assumes "Postulate35"
  shows "Postulate27"
  using Postulate27_def Postulate35_def assms existential_playfair__rah by blast

lemma Thm10_1:
  assumes "archimedes_axiom" 
  shows "(Postulate01 \<longleftrightarrow> Postulate02) \<and>
         (Postulate01 \<longleftrightarrow> Postulate03) \<and>
         (Postulate01 \<longleftrightarrow> Postulate04) \<and>
         (Postulate01 \<longleftrightarrow> Postulate05) \<and>
         (Postulate01 \<longleftrightarrow> Postulate06) \<and>
         (Postulate01 \<longleftrightarrow> Postulate07) \<and>
         (Postulate01 \<longleftrightarrow> Postulate08) \<and>
         (Postulate01 \<longleftrightarrow> Postulate09) \<and>
         (Postulate01 \<longleftrightarrow> Postulate10)" 
  using InterAx5 InterCycle3 Postulate01_def Postulate03_def playfair__alternate_interior 
    tarski_s_euclid_implies_playfair_s_postulate alternate_interior__triangle
    Cycle_2 Postulate03_def Postulate20_def assms legendre_s_third_theorem InterAx5 
    Cycle_3 P04_P33 P25_33 P34_P27 P4_P34 assms InterCycle1bis Postulate02_def 
    Postulate12_def playfair_bis__playfair Postulate07_def Postulate08_def 
    alternate_interior__consecutive_interior  consecutive_interior__alternate_interior 
    equivalent_postulates_without_decidability_of_intersection_of_lines 
    equivalent_postulates_without_decidability_of_intersection_of_lines
  by blast

lemma Thm10_2:
  assumes "archimedes_axiom" 
  shows "(Postulate01 \<longleftrightarrow> Postulate11) \<and>
         (Postulate01 \<longleftrightarrow> Postulate12) \<and>
         (Postulate01 \<longleftrightarrow> Postulate13) \<and>
         (Postulate01 \<longleftrightarrow> Postulate14) \<and>
         (Postulate01 \<longleftrightarrow> Postulate15) \<and>
         (Postulate01 \<longleftrightarrow> Postulate16) \<and>
         (Postulate01 \<longleftrightarrow> Postulate17) \<and>
         (Postulate01 \<longleftrightarrow> Postulate18) \<and>
         (Postulate01 \<longleftrightarrow> Postulate19) \<and>
         (Postulate01 \<longleftrightarrow> Postulate20)" 
  using InterAx5 InterCycle1bis InterCycle3 Postulate02_def Postulate03_def
    Postulate12_def playfair__alternate_interior alternate_interior__triangle 
    playfair_bis__playfair equivalent_postulates_without_decidability_of_intersection_of_lines 
    Cycle_2 Cycle_1 Postulate11_def Postulate15_def
    inter_dec_plus_par_perp_perp_imply_triangle_circumscription 
    universal_posidonius_postulate__perpendicular_transversal_postulate
  by blast

lemma Thm10_3:
  assumes "archimedes_axiom" 
  shows "(Postulate01 \<longleftrightarrow> Postulate21) \<and>
         (Postulate01 \<longleftrightarrow> Postulate22) \<and>
         (Postulate01 \<longleftrightarrow> Postulate23) \<and>
         (Postulate01 \<longleftrightarrow> Postulate24) \<and>
         (Postulate01 \<longleftrightarrow> Postulate25) \<and>
         (Postulate01 \<longleftrightarrow> Postulate26) \<and>
         (Postulate01 \<longleftrightarrow> Postulate27) \<and>
         (Postulate01 \<longleftrightarrow> Postulate28) \<and>
         (Postulate01 \<longleftrightarrow> Postulate29) \<and>
         (Postulate01 \<longleftrightarrow> Postulate30)" 
  using Postulate03_def Postulate21_def legendre_s_second_theorem 
    triangle__existential_triangle assms Thm10_1 Cycle_3 by blast

lemma Thm10_4:
  assumes "archimedes_axiom" 
  shows "(Postulate01 \<longleftrightarrow> Postulate31) \<and>
         (Postulate01 \<longleftrightarrow> Postulate32) \<and>
         (Postulate01 \<longleftrightarrow> Postulate33) \<and>
         (Postulate01 \<longleftrightarrow> Postulate34) \<and>
         (Postulate01 \<longleftrightarrow> Postulate35)"
  using assms Thm10_1 P31_P04 P31_P04 P31_P32 P04_P33 P4_P34 P34_P27 Thm10_3 
    P01__P35 P35_27 by blast

(*
Pierre Boutry, Charly Gries, Julien Narboux, Pascal Schreck. Parallel postulates and continuity
axioms: a mechanized study in intuitionistic logic using Coq. Journal of Automated Reasoning,
Springer Verlag, 2019, 62 (1), pp.68. ff10.1007/s10817-017-9422-8ff. ffhal-01178236v2f

Theorem 10 In Archimedean neutral geometry, Postulates 1-34 are equivalent
*)
theorem Thm10:
  assumes "archimedes_axiom" 
  shows "(Postulate01 \<longleftrightarrow> Postulate02) \<and>
         (Postulate01 \<longleftrightarrow> Postulate03) \<and>
         (Postulate01 \<longleftrightarrow> Postulate04) \<and>
         (Postulate01 \<longleftrightarrow> Postulate05) \<and>
         (Postulate01 \<longleftrightarrow> Postulate06) \<and>
         (Postulate01 \<longleftrightarrow> Postulate07) \<and>
         (Postulate01 \<longleftrightarrow> Postulate08) \<and>
         (Postulate01 \<longleftrightarrow> Postulate09) \<and>
         (Postulate01 \<longleftrightarrow> Postulate10) \<and>
         (Postulate01 \<longleftrightarrow> Postulate11) \<and>
         (Postulate01 \<longleftrightarrow> Postulate12) \<and>
         (Postulate01 \<longleftrightarrow> Postulate13) \<and>
         (Postulate01 \<longleftrightarrow> Postulate14) \<and>
         (Postulate01 \<longleftrightarrow> Postulate15) \<and>
         (Postulate01 \<longleftrightarrow> Postulate16) \<and>
         (Postulate01 \<longleftrightarrow> Postulate17) \<and>
         (Postulate01 \<longleftrightarrow> Postulate18) \<and>
         (Postulate01 \<longleftrightarrow> Postulate19) \<and>
         (Postulate01 \<longleftrightarrow> Postulate20) \<and>
         (Postulate01 \<longleftrightarrow> Postulate21) \<and>
         (Postulate01 \<longleftrightarrow> Postulate22) \<and>
         (Postulate01 \<longleftrightarrow> Postulate23) \<and>
         (Postulate01 \<longleftrightarrow> Postulate24) \<and>
         (Postulate01 \<longleftrightarrow> Postulate25) \<and>
         (Postulate01 \<longleftrightarrow> Postulate26) \<and>
         (Postulate01 \<longleftrightarrow> Postulate27) \<and>
         (Postulate01 \<longleftrightarrow> Postulate28) \<and>
         (Postulate01 \<longleftrightarrow> Postulate29) \<and>
         (Postulate01 \<longleftrightarrow> Postulate30) \<and>
         (Postulate01 \<longleftrightarrow> Postulate31) \<and>
         (Postulate01 \<longleftrightarrow> Postulate32) \<and>
         (Postulate01 \<longleftrightarrow> Postulate33) \<and>
         (Postulate01 \<longleftrightarrow> Postulate34) \<and>
         (Postulate01 \<longleftrightarrow> Postulate35)"
  using InterAx5 InterCycle3 Postulate01_def Postulate03_def playfair__alternate_interior 
    tarski_s_euclid_implies_playfair_s_postulate alternate_interior__triangle
    Cycle_2 Postulate03_def Postulate20_def assms legendre_s_third_theorem InterAx5 
    Cycle_3 P04_P33 P25_33 P34_P27 P4_P34 assms InterCycle1bis Postulate02_def 
    Postulate12_def playfair_bis__playfair Postulate07_def Postulate08_def 
    alternate_interior__consecutive_interior  consecutive_interior__alternate_interior 
    equivalent_postulates_without_decidability_of_intersection_of_lines 
    equivalent_postulates_without_decidability_of_intersection_of_lines
    InterAx5 InterCycle1bis InterCycle3 Postulate02_def Postulate03_def
    Postulate12_def playfair__alternate_interior alternate_interior__triangle 
    playfair_bis__playfair equivalent_postulates_without_decidability_of_intersection_of_lines 
    Cycle_2 Cycle_1 Postulate11_def Postulate15_def
    inter_dec_plus_par_perp_perp_imply_triangle_circumscription 
    universal_posidonius_postulate__perpendicular_transversal_postulate
    Postulate03_def Postulate21_def legendre_s_second_theorem 
    triangle__existential_triangle assms Thm10_1 Cycle_3 assms Thm10_1 P31_P04 
    P31_P04 P31_P32 P04_P33 P4_P34 P34_P27 Thm10_3 P01__P35 P35_27 by blast (* 3 sec *)

theorem equivalent_postulates_assuming_greenberg_s_axiom:
  assumes "greenberg_s_axiom"
  shows "(tarski_s_parallel_postulate \<longleftrightarrow> alternate_interior_angles_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> alternative_playfair_s_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> alternative_playfair_s_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> alternative_proclus_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> alternative_strong_parallel_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> consecutive_interior_angles_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> euclid_5) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> euclid_s_parallel_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> existential_playfair_s_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> existential_thales_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> inverse_projection_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> midpoint_converse_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> perpendicular_transversal_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_transitivity_of_parallelism) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> playfair_s_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> posidonius_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> universal_posidonius_postulate) \<and>
         (tarski_s_parallel_postulate 
              \<longleftrightarrow> postulate_of_existence_of_a_right_lambert_quadrilateral) \<and>
         (tarski_s_parallel_postulate 
              \<longleftrightarrow> postulate_of_existence_of_a_right_saccheri_quadrilateral) \<and>
         (tarski_s_parallel_postulate 
              \<longleftrightarrow> postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_existence_of_similar_triangles) \<and>
         (tarski_s_parallel_postulate 
              \<longleftrightarrow> postulate_of_parallelism_of_perpendicular_transversals) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_right_lambert_quadrilaterals) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_right_saccheri_quadrilaterals) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_transitivity_of_parallelism) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> proclus_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> strong_parallel_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> tarski_s_parallel_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> thales_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> thales_converse_postulate) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> triangle_circumscription_principle) \<and>
         (tarski_s_parallel_postulate \<longleftrightarrow> triangle_postulate)" 
proof -
  have "aristotle_s_axiom" 
    using aristotle_s_axiom_def assms greenberg__aristotle by blast
  have "tarski_s_parallel_postulate \<longleftrightarrow> alternate_interior_angles_postulate" 
    using InterAx5 Postulate01_def Postulate02_def alternate_interior__playfair_bis 
      playfair__alternate_interior playfair_bis__playfair 
      tarski_s_euclid_implies_playfair_s_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> alternative_playfair_s_postulate" 
    using alternate_interior__playfair_bis calculation playfair__alternate_interior 
      playfair_bis__playfair by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> alternative_proclus_postulate" 
    using inverse_projection_postulate__proclus_bis original_euclid__original_spp 
      original_spp__inverse_projection_postulate proclus_bis__proclus 
      proclus_s_postulate_implies_strong_parallel_postulate 
      strong_parallel_postulate_implies_tarski_s_euclid 
      tarski_s_implies_euclid_s_parallel_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> alternative_strong_parallel_postulate" 
    using calculation(3) inverse_projection_postulate__proclus_bis 
      original_euclid__original_spp original_spp__inverse_projection_postulate 
      tarski_s_implies_euclid_s_parallel_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> consecutive_interior_angles_postulate" 
    using alternate_interior__consecutive_interior calculation(1) 
      consecutive_interior__alternate_interior by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> euclid_5" 
    using calculation(4) euclid_5__original_euclid original_euclid__original_spp 
      tarski_s_euclid_implies_euclid_5 by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> euclid_s_parallel_postulate" 
    using calculation(4) original_euclid__original_spp 
      tarski_s_implies_euclid_s_parallel_postulate by linarith
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> existential_playfair_s_postulate" 
    using Postulate35_def Cycle_3 InterCycle1 P01__P35 P35_27 Postulate01_def 
      Postulate12_def \<open>greenberg_s_axiom\<close> calculation(2) by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> existential_thales_postulate"  
    using Postulate26_def Cycle_3  InterCycle1 P01__P35 P35_27 Postulate01_def 
      Postulate12_def \<open>greenberg_s_axiom\<close> calculation(2) by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> inverse_projection_postulate" 
    using calculation(3) calculation(4) inverse_projection_postulate__proclus_bis 
      original_spp__inverse_projection_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> midpoint_converse_postulate" 
    using Postulate06_def calculation(2) calculation(8) 
      midpoint_converse_postulate_implies_playfair playfair__existential_playfair 
      playfair_bis__playfair playfair_s_postulate_implies_midpoint_converse_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> perpendicular_transversal_postulate"
    using Postulate09_def inter_dec_plus_par_perp_perp_imply_triangle_circumscription 
      playfair__universal_posidonius_postulate 
      tarski_s_euclid_implies_playfair_s_postulate 
      triangle_circumscription_implies_tarski_s_euclid 
      universal_posidonius_postulate__perpendicular_transversal_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_transitivity_of_parallelism" 
    using InterAx5 Postulate01_def Postulate02_def par_trans_implies_playfair 
      playfair_implies_par_trans tarski_s_euclid_implies_playfair_s_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> playfair_s_postulate" 
    using calculation(13) playfair_implies_par_trans 
      tarski_s_euclid_implies_playfair_s_postulate by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> posidonius_postulate" 
    using Postulate22_def Cycle_3 Postulate26_def calculation(9) by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> universal_posidonius_postulate" 
    using Postulate11_def calculation(12) playfair__universal_posidonius_postulate 
      tarski_s_euclid_implies_playfair_s_postulate 
      universal_posidonius_postulate__perpendicular_transversal_postulate by blast
  moreover have "tarski_s_parallel_postulate 
       \<longleftrightarrow> postulate_of_existence_of_a_right_lambert_quadrilateral" 
    using Cycle_3 Postulate22_def Postulate30_def calculation(15) by blast
  moreover have "tarski_s_parallel_postulate 
       \<longleftrightarrow> postulate_of_existence_of_a_right_saccheri_quadrilateral" 
    using Cycle_3 Postulate28_def Postulate30_def calculation(17) by blast
  moreover have "tarski_s_parallel_postulate 
       \<longleftrightarrow> postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights" 
    using Cycle_3 Postulate21_def Postulate22_def calculation(15) by blast
  moreover have "tarski_s_parallel_postulate 
       \<longleftrightarrow> postulate_of_existence_of_similar_triangles" 
    using Cycle_3 Postulate22_def Postulate23_def calculation(15) by blast
  moreover have "tarski_s_parallel_postulate 
       \<longleftrightarrow> postulate_of_parallelism_of_perpendicular_transversals" 
    using calculation(12) par_perp_2_par_implies_par_perp_perp 
      par_perp_perp_implies_par_perp_2_par by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_right_lambert_quadrilaterals" 
    using Cycle_3 Postulate26_def Postulate29_def calculation(9) by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> postulate_of_right_saccheri_quadrilaterals" 
    using calculation(18) calculation(9) rah__existential_saccheri thales_existence__rah by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> proclus_postulate" 
    using Cycle_2 Postulate13_def Postulate01_def by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> strong_parallel_postulate" 
    using calculation(24) proclus_s_postulate_implies_strong_parallel_postulate 
      strong_parallel_postulate_implies_tarski_s_euclid by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> thales_postulate" 
    using Cycle_3 Postulate24_def Postulate26_def calculation(9) by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> thales_converse_postulate" 
    using Cycle_3 Postulate25_def Postulate30_def calculation(17) by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> triangle_circumscription_principle" 
    using inter_dec_plus_par_perp_perp_imply_triangle_circumscription  calculation(12) 
      triangle_circumscription_implies_tarski_s_euclid by blast
  moreover have "tarski_s_parallel_postulate \<longleftrightarrow> triangle_postulate" 
    using Cycle_3 Postulate03_def Postulate30_def calculation(17) by blast
  ultimately show ?thesis 
    by blast
qed

theorem equivalent_postulates_assuming_archimesdes_axiom:
  assumes "archimedes_axiom" 
  shows "alternate_interior_angles_postulate \<longleftrightarrow> alternative_playfair_s_postulate \<and>
         alternative_playfair_s_postulate \<longleftrightarrow> alternative_proclus_postulate \<and>
         alternative_proclus_postulate \<longleftrightarrow> alternative_strong_parallel_postulate \<and>
         alternative_strong_parallel_postulate \<longleftrightarrow> bachmann_s_lotschnittaxiom \<and>
         bachmann_s_lotschnittaxiom \<longleftrightarrow> consecutive_interior_angles_postulate \<and>
         consecutive_interior_angles_postulate \<longleftrightarrow> euclid_5 \<and>
         euclid_5 \<longleftrightarrow> euclid_s_parallel_postulate \<and>
         euclid_s_parallel_postulate \<longleftrightarrow> existential_playfair_s_postulate \<and>
         existential_playfair_s_postulate \<longleftrightarrow> existential_thales_postulate \<and>
         existential_thales_postulate \<longleftrightarrow> inverse_projection_postulate \<and>
         inverse_projection_postulate \<longleftrightarrow> legendre_s_parallel_postulate \<and>
         legendre_s_parallel_postulate \<longleftrightarrow> midpoint_converse_postulate \<and>
         midpoint_converse_postulate \<longleftrightarrow> perpendicular_transversal_postulate \<and>
         perpendicular_transversal_postulate \<longleftrightarrow> postulate_of_transitivity_of_parallelism \<and>
         postulate_of_transitivity_of_parallelism \<longleftrightarrow> playfair_s_postulate \<and>
         playfair_s_postulate \<longleftrightarrow> posidonius_postulate \<and>
         posidonius_postulate \<longleftrightarrow> universal_posidonius_postulate \<and>
         universal_posidonius_postulate \<longleftrightarrow> 
           postulate_of_existence_of_a_right_lambert_quadrilateral \<and>
         postulate_of_existence_of_a_right_lambert_quadrilateral \<longleftrightarrow> 
           postulate_of_existence_of_a_right_saccheri_quadrilateral \<and>
         postulate_of_existence_of_a_right_saccheri_quadrilateral \<longleftrightarrow> 
           postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights \<and>
         postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights \<longleftrightarrow> 
           postulate_of_existence_of_similar_triangles \<and>
         postulate_of_existence_of_similar_triangles \<longleftrightarrow> 
           postulate_of_parallelism_of_perpendicular_transversals \<and>
         postulate_of_parallelism_of_perpendicular_transversals \<longleftrightarrow> 
           postulate_of_right_lambert_quadrilaterals \<and>
         postulate_of_right_lambert_quadrilaterals \<longleftrightarrow> postulate_of_right_saccheri_quadrilaterals \<and>
         postulate_of_right_saccheri_quadrilaterals \<longleftrightarrow> postulate_of_transitivity_of_parallelism \<and>
         postulate_of_transitivity_of_parallelism \<longleftrightarrow> proclus_postulate \<and>
         proclus_postulate \<longleftrightarrow> strong_parallel_postulate \<and>
         strong_parallel_postulate \<longleftrightarrow> tarski_s_parallel_postulate \<and>
         tarski_s_parallel_postulate \<longleftrightarrow> thales_postulate \<and>
         thales_postulate \<longleftrightarrow> thales_converse_postulate \<and>
         thales_converse_postulate \<longleftrightarrow> triangle_circumscription_principle \<and>
         triangle_circumscription_principle \<longleftrightarrow> triangle_postulate \<and>
         triangle_postulate \<longleftrightarrow> weak_inverse_projection_postulate \<and>
         weak_inverse_projection_postulate \<longleftrightarrow> weak_tarski_s_parallel_postulate \<and>
         weak_tarski_s_parallel_postulate \<longleftrightarrow> weak_triangle_circumscription_principle"
  using alternate_interior__consecutive_interior alternate_interior__playfair_bis assms
    bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate consecutive_interior__alternate_interior
    euclid_5__original_euclid existential_playfair__rah existential_saccheri__rah
    inter_dec_plus_par_perp_perp_imply_triangle_circumscription
    inverse_projection_postulate__proclus_bis legendre_s_fourth_theorem_aux legendre_s_second_theorem
    legendre_s_third_theorem midpoint_converse_postulate_implies_playfair original_euclid__original_spp
    original_spp__inverse_projection_postulate par_perp_2_par_implies_par_perp_perp
    par_perp_perp_implies_par_perp_2_par playfair__alternate_interior playfair__existential_playfair
    playfair__universal_posidonius_postulate playfair_bis__playfair
    playfair_s_postulate_implies_midpoint_converse_postulate posidonius_postulate__rah
    proclus_bis__proclus proclus_s_postulate_implies_strong_parallel_postulate
    rah__existential_saccheri rah__posidonius rah__rectangle_principle rah__similar
    rah__thales_postulate rah__triangle rectangle_existence__rah
    rectangle_principle__rectangle_existence similar__rah
    strong_parallel_postulate_implies_tarski_s_euclid tarski_s_euclid_implies_euclid_5
    tarski_s_euclid_implies_playfair_s_postulate thales_converse_postulate__thales_existence
    thales_converse_postulate__weak_triangle_circumscription_principle thales_existence__rah
    thales_postulate__thales_converse_postulate triangle__existential_triangle
    triangle_circumscription_implies_tarski_s_euclid
    universal_posidonius_postulate__perpendicular_transversal_postulate
    weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate
    weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate
    weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom by argo 

section "Szmielew: hyperbolic plane postulate"

subsection "Definition"

definition hyperbolic_plane_postulate ::
  "bool"
  ("HyperbolicPlanePostulate") where
  "hyperbolic_plane_postulate \<equiv>

  \<forall> A1 A2 P.
  \<not> Col A1 A2 P 
\<longrightarrow> 
  (\<exists> B1 B2 C1 C2. 
   A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<and> \<not> Col C1 B1 B2)"

subsection "Propositions"

lemma hpp__nP35:
  assumes "greenberg_s_axiom"
  shows "hyperbolic_plane_postulate \<longleftrightarrow> \<not> Postulate35"
proof -
  have "hyperbolic_plane_postulate \<longrightarrow> \<not> existential_playfair_s_postulate" 
    using existential_playfair_s_postulate_def hyperbolic_plane_postulate_def by blast
  moreover
  have "(greenberg_s_axiom \<and> \<not> existential_playfair_s_postulate) \<longrightarrow> hyperbolic_plane_postulate" 
    using existential_playfair_s_postulate_def hyperbolic_plane_postulate_def 
      col_permutation_5 par_right_comm by blast
  ultimately show ?thesis 
    using Postulate35_def assms by blast
qed

lemma aah__hpp:
  assumes "hypothesis_of_acute_saccheri_quadrilaterals"
  shows "hyperbolic_plane_postulate"
proof -
  {
    fix A1 A2 P
    assume "\<not> Col A1 A2 P"
    then obtain Q where "Col A1 A2 Q" and "A1 A2 Perp P Q" 
      using l8_18_existence \<open>\<not> Col A1 A2 P\<close> by blast
    then obtain X where "A1 \<noteq> X" and "A2 \<noteq> X" and "Q \<noteq> X" and "Col A1 A2 X" 
      using diff_col_ex3 by blast
    obtain Y where "Bet X Q Y" and "Cong X Q Q Y" 
      using cong_4312 segment_construction by blast
    have "A1 \<noteq> A2" 
      using \<open>A1 A2 Perp P Q\<close> perp_not_eq_1 by blast
    have "Q \<noteq> Y" 
      using \<open>Cong X Q Q Y\<close> \<open>Q \<noteq> X\<close> cong_identity_inv by auto
    have "P \<noteq> Q" 
      using \<open>Col A1 A2 Q\<close> \<open>\<not> Col A1 A2 P\<close> by auto
    have "Col A1 A2 Y" 
      by (metis \<open>Bet X Q Y\<close> \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 X\<close> \<open>Q \<noteq> X\<close> bet_col colx)
    have "Per P Q X" 
      by (meson l8_16_1 \<open>A1 A2 Perp P Q\<close> \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 X\<close>)
    then obtain B1 where "Saccheri Q P B1 X" 
      using \<open>P \<noteq> Q\<close> \<open>Q \<noteq> X\<close> per__ex_saccheri by blast
    hence "Q X Par P B1" 
      by (simp add: sac__par1423)
    have "Per P Q Y" 
      by (meson l8_16_1 \<open>A1 A2 Perp P Q\<close> \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 Y\<close>)
    then obtain C1 where "Saccheri Q P C1 Y" 
      using \<open>P \<noteq> Q\<close> \<open>Q \<noteq> Y\<close> per__ex_saccheri by blast
    hence "Q Y Par P C1" 
      using sac__par1423 by blast
    have "A1 A2 Par B1 P" 
      using Par_cases \<open>A1 \<noteq> A2\<close> \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 X\<close> \<open>Q X Par P B1\<close> 
        par_col2_par_bis by blast
    moreover have "Col P B1 P" 
      using col_trivial_3 by auto
    moreover have "A1 A2 Par C1 P" 
      using Par_cases \<open>A1 \<noteq> A2\<close> \<open>Col A1 A2 Q\<close> \<open>Col A1 A2 Y\<close> \<open>Q Y Par P C1\<close> 
        par_col2_par_bis by blast
    moreover have "Col P C1 P" 
      by (simp add: col_trivial_3)
    moreover
    {
      assume "Col C1 B1 P" 
      have "Q P ParStrict B1 X" 
        by (simp add: \<open>Saccheri Q P B1 X\<close> sac__pars1234)
      have "Q P ParStrict C1 Y" 
        using \<open>Saccheri Q P C1 Y\<close> sac__pars1234 by auto
      have "P Q TS Y X" 
        by (metis NCol_perm invert_two_sides \<open>Bet X Q Y\<close> \<open>Col A1 A2 Q\<close> 
            \<open>Col A1 A2 X\<close> \<open>Q \<noteq> X\<close> \<open>Q \<noteq> Y\<close> \<open>\<not> Col A1 A2 P\<close> bet__ts col_trivial_2 l6_21 l9_2)
      hence "P Q TS X C1" 
        by (meson Par_strict_cases l9_8_2 \<open>Q P ParStrict C1 Y\<close> l12_6 l9_2)
      hence "P Q TS B1 C1" 
        using \<open>Q P ParStrict B1 X\<close> l12_6 l9_8_2 par_strict_comm by blast
      hence "Bet B1 P C1" 
        using Col_cases \<open>Col C1 B1 P\<close> col_two_sides_bet by blast
      have "B1 \<noteq> P" 
        using calculation(1) par_distincts by auto
      have "C1 \<noteq> P" 
        using calculation(3) par_distinct by blast
      have "\<not> B1 P C1 LtA X Q Y" 
        using \<open>Bet B1 P C1\<close> \<open>Bet X Q Y\<close> bet2_lta__lta lta_distincts by blast
      moreover
      have "B1 P C1 LtA X Q Y"
      proof -
        have "\<not> Col P Q X" 
          using TS_def \<open>P Q TS X C1\<close> not_col_permutation_1 by presburger
        have "Q P TS X Y" 
          using \<open>P Q TS Y X\<close> invert_two_sides l9_2 by blast
        have "Acute B1 P Q" 
          using \<open>Saccheri Q P B1 X\<close> acute_sym assms 
            hypothesis_of_acute_saccheri_quadrilaterals_def by blast
        hence "B1 P Q LtA P Q X" 
          using acute_per__lta \<open>P \<noteq> Q\<close> \<open>Q \<noteq> X\<close> \<open>Per P Q X\<close> by blast
        moreover have "Acute Q P C1" 
          using \<open>Saccheri Q P C1 Y\<close> assms hypothesis_of_acute_saccheri_quadrilaterals_def by blast
        hence "Q P C1 LtA P Q Y" 
          using acute_per__lta \<open>P \<noteq> Q\<close> \<open>Per P Q Y\<close> \<open>Q \<noteq> Y\<close> by blast
        moreover have "SAMS P Q X P Q Y" 
          using \<open>P \<noteq> Q\<close> \<open>Per P Q X\<close> \<open>Per P Q Y\<close> \<open>Q \<noteq> X\<close> \<open>Q \<noteq> Y\<close> per2__sams by force
        moreover have "B1 P Q Q P C1 SumA B1 P C1" 
          using \<open>B1 \<noteq> P\<close> \<open>Bet B1 P C1\<close> \<open>C1 \<noteq> P\<close> \<open>P \<noteq> Q\<close> bet__suma by force
        moreover have "P Q X P Q Y SumA X Q Y" 
          using \<open>Bet X Q Y\<close> \<open>P \<noteq> Q\<close> \<open>Q \<noteq> X\<close> \<open>Q \<noteq> Y\<close> bet__suma suma_left_comm by presburger
        ultimately show ?thesis 
          using sams_lta2_suma2__lta by blast
      qed
      ultimately have False 
        by blast
    }
    ultimately have "\<exists> B1 B2 C1 C2. 
   A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<and> \<not> Col C1 B1 B2" 
      by blast
  }
  thus ?thesis 
    using hyperbolic_plane_postulate_def by blast
qed


theorem szmielew_s_theorem:
  assumes "aristotle_s_axiom"
  shows "\<forall> P:: bool.
         (playfair_s_postulate \<longrightarrow> P) \<and> (hyperbolic_plane_postulate \<longrightarrow> \<not> P) 
          \<longrightarrow>
         (P \<longleftrightarrow> playfair_s_postulate)" 
proof -
  {
    fix P:: bool
    assume "playfair_s_postulate \<longrightarrow> P" and
      "hyperbolic_plane_postulate \<longrightarrow> \<not> P" 
    have "hypothesis_of_acute_saccheri_quadrilaterals \<or> 
               hypothesis_of_right_saccheri_quadrilaterals" 
      by (simp add: aristotle__acute_or_right assms)
    moreover
    have "greenberg_s_axiom" 
      by (simp add: aristotle__greenberg assms)
    hence "playfair_s_postulate \<longleftrightarrow> postulate_of_existence_of_a_right_saccheri_quadrilateral" 
      using equivalent_postulates_assuming_greenberg_s_axiom assms by blast
    {
      assume "hypothesis_of_acute_saccheri_quadrilaterals" 
      hence "P \<longrightarrow> playfair_s_postulate" 
        using \<open>HyperbolicPlanePostulate \<longrightarrow> \<not> P\<close> aah__hpp by blast
    }
    moreover
    {
      assume "hypothesis_of_right_saccheri_quadrilaterals" 
      assume P
      have "\<not> hyperbolic_plane_postulate" 
        using \<open>HyperbolicPlanePostulate \<longrightarrow> \<not> P\<close> \<open>P\<close> by fastforce
      hence "Postulate35" 
        using hpp__nP35 assms by (simp add: \<open>GreenBergsAxiom\<close>)
      hence "playfair_s_postulate" 
        using equivalent_postulates_assuming_greenberg_s_axiom assms 
          Postulate35_def \<open>GreenBergsAxiom\<close> by fastforce
    }
    ultimately
    have "P \<longrightarrow> playfair_s_postulate" 
      by blast
    hence "P \<longleftrightarrow> playfair_s_postulate" 
      using \<open>PlayfairSPostulate \<longrightarrow> P\<close> by blast
  }
  thus ?thesis
    by blast
qed

end
end
