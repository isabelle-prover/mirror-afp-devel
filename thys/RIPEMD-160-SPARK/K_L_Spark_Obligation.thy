theory K_L_Spark_Obligation
imports K_L_Spark_User

begin



lemma goal6'1: 
  assumes R1: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes R8: " K_L_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " K_L_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " K_L_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " K_L_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " K_L_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " K_L_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " K_L_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " K_L_Spark_Declaration.round_index__last''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= K_L_Spark_Declaration.j'' "
  assumes H2: " K_L_Spark_Declaration.j'' <= (15 :: int) "
  assumes H3: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H4: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes H5: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes H6: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H7: 
  " K_L_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H8: 
  " (79 :: int) <= K_L_Spark_Declaration.round_index__base__last''
  "
  shows " (0 :: int) = K_L_Spark_Specification.k_l' K_L_Spark_Declaration.j''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal7'1: 
  assumes R1: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes R8: " K_L_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " K_L_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " K_L_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " K_L_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " K_L_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " K_L_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " K_L_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " K_L_Spark_Declaration.round_index__last''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (16 :: int) <= K_L_Spark_Declaration.j'' "
  assumes H2: " K_L_Spark_Declaration.j'' <= (31 :: int) "
  assumes H3: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H4: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes H5: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes H6: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H7: 
  " K_L_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H8: 
  " (79 :: int) <= K_L_Spark_Declaration.round_index__base__last''
  "
  shows " (1518500249 :: int) = K_L_Spark_Specification.k_l' K_L_Spark_Declaration.j''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal8'1: 
  assumes R1: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes R8: " K_L_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " K_L_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " K_L_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " K_L_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " K_L_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " K_L_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " K_L_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " K_L_Spark_Declaration.round_index__last''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (32 :: int) <= K_L_Spark_Declaration.j'' "
  assumes H2: " K_L_Spark_Declaration.j'' <= (47 :: int) "
  assumes H3: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H4: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes H5: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes H6: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H7: 
  " K_L_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H8: 
  " (79 :: int) <= K_L_Spark_Declaration.round_index__base__last''
  "
  shows " (1859775393 :: int) = K_L_Spark_Specification.k_l' K_L_Spark_Declaration.j''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal9'1: 
  assumes R1: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes R8: " K_L_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " K_L_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " K_L_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " K_L_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " K_L_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " K_L_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " K_L_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " K_L_Spark_Declaration.round_index__last''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (48 :: int) <= K_L_Spark_Declaration.j'' "
  assumes H2: " K_L_Spark_Declaration.j'' <= (63 :: int) "
  assumes H3: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H4: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes H5: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes H6: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H7: 
  " K_L_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H8: 
  " (79 :: int) <= K_L_Spark_Declaration.round_index__base__last''
  "
  shows " (2400959708 :: int) = K_L_Spark_Specification.k_l' K_L_Spark_Declaration.j''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal10'1: 
  assumes R1: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " K_L_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes R8: " K_L_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " K_L_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " K_L_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " K_L_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " K_L_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " K_L_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " K_L_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " K_L_Spark_Declaration.round_index__last''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= K_L_Spark_Declaration.j'' "
  assumes H2: " K_L_Spark_Declaration.j'' <= (79 :: int) "
  assumes H3: " (15 :: int) < K_L_Spark_Declaration.j'' "
  assumes H4: " (31 :: int) < K_L_Spark_Declaration.j'' "
  assumes H5: " (47 :: int) < K_L_Spark_Declaration.j'' "
  assumes H6: " (63 :: int) < K_L_Spark_Declaration.j'' "
  assumes H7: 
  " (0 :: int) <= K_L_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H8: " (0 :: int) <= K_L_Spark_Declaration.word__size'' "
  assumes H9: 
  " (0 :: int) <= K_L_Spark_Declaration.round_index__size''
  "
  assumes H10: 
  " K_L_Spark_Declaration.round_index__base__first''
    <= K_L_Spark_Declaration.round_index__base__last''
  "
  assumes H11: 
  " K_L_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H12: 
  " (79 :: int) <= K_L_Spark_Declaration.round_index__base__last''
  "
  shows " (2840853838 :: int) = K_L_Spark_Specification.k_l' K_L_Spark_Declaration.j''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)
end
