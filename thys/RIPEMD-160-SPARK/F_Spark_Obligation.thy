theory F_Spark_Obligation
imports F_Spark_User

begin



lemma goal2'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (16 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (31 :: int) "
  assumes H9: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H10: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H12: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H13: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H14: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " (0 :: int)
          <= F_Spark_Specification.bit__or'
               ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.y'' )
               ( F_Spark_Specification.bit__and'
                   ( (4294967295 :: int) - F_Spark_Declaration.x'' )
                   F_Spark_Declaration.z''
               )
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal2'2: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (16 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (31 :: int) "
  assumes H9: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H10: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H12: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H13: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H14: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__or'
            ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.y'' )
            ( F_Spark_Specification.bit__and'
                ( (4294967295 :: int) - F_Spark_Declaration.x'' )
                F_Spark_Declaration.z''
            )
          <= (4294967295 :: int)
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal3'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (32 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (47 :: int) "
  assumes H9: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H10: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H12: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H13: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H14: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " (0 :: int)
          <= F_Spark_Specification.bit__xor'
               ( F_Spark_Specification.bit__or'
                   F_Spark_Declaration.x''
                   ( (4294967295 :: int) - F_Spark_Declaration.y'' )
               )
               F_Spark_Declaration.z''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal3'2: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (32 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (47 :: int) "
  assumes H9: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H10: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H12: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H13: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H14: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__xor'
            ( F_Spark_Specification.bit__or'
                F_Spark_Declaration.x''
                ( (4294967295 :: int) - F_Spark_Declaration.y'' )
            )
            F_Spark_Declaration.z''
          <= (4294967295 :: int)
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal4'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (48 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (63 :: int) "
  assumes H9: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H10: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H12: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H13: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H14: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " (0 :: int)
          <= F_Spark_Specification.bit__or'
               ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.z'' )
               ( F_Spark_Specification.bit__and'
                   F_Spark_Declaration.y''
                   ( (4294967295 :: int) - F_Spark_Declaration.z'' )
               )
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal4'2: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (48 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (63 :: int) "
  assumes H9: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H10: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H12: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H13: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H14: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__or'
            ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.z'' )
            ( F_Spark_Specification.bit__and'
                F_Spark_Declaration.y''
                ( (4294967295 :: int) - F_Spark_Declaration.z'' )
            )
          <= (4294967295 :: int)
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal5'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.j'' "
  assumes H2: " F_Spark_Declaration.j'' <= (79 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H4: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H6: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H7: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H8: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H9: " (15 :: int) < F_Spark_Declaration.j'' "
  assumes H10: " (31 :: int) < F_Spark_Declaration.j'' "
  assumes H11: " (47 :: int) < F_Spark_Declaration.j'' "
  assumes H12: " (63 :: int) < F_Spark_Declaration.j'' "
  assumes H13: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H14: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H15: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H17: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H18: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " (0 :: int)
          <= F_Spark_Specification.bit__xor'
               F_Spark_Declaration.x''
               ( F_Spark_Specification.bit__or'
                   F_Spark_Declaration.y''
                   ( (4294967295 :: int) - F_Spark_Declaration.z'' )
               )
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal5'2: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.j'' "
  assumes H2: " F_Spark_Declaration.j'' <= (79 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H4: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H6: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H7: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H8: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H9: " (15 :: int) < F_Spark_Declaration.j'' "
  assumes H10: " (31 :: int) < F_Spark_Declaration.j'' "
  assumes H11: " (47 :: int) < F_Spark_Declaration.j'' "
  assumes H12: " (63 :: int) < F_Spark_Declaration.j'' "
  assumes H13: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H14: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H15: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H17: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H18: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__xor'
            F_Spark_Declaration.x''
            ( F_Spark_Specification.bit__or'
                F_Spark_Declaration.y''
                ( (4294967295 :: int) - F_Spark_Declaration.z'' )
            )
          <= (4294967295 :: int)
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal6'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.j'' "
  assumes H2: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H3: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H4: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H5: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H6: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H7: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H8: " F_Spark_Declaration.j'' <= (15 :: int) "
  assumes H9: 
  " (0 :: int)
    <= F_Spark_Specification.bit__xor'
         F_Spark_Declaration.x''
         ( F_Spark_Specification.bit__xor' F_Spark_Declaration.y'' F_Spark_Declaration.z'' )
  "
  assumes H10: 
  " F_Spark_Specification.bit__xor'
      F_Spark_Declaration.x''
      ( F_Spark_Specification.bit__xor' F_Spark_Declaration.y'' F_Spark_Declaration.z'' )
    <= (4294967295 :: int)
  "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H12: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H14: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H15: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H16: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__xor'
            F_Spark_Declaration.x''
            ( F_Spark_Specification.bit__xor' F_Spark_Declaration.y'' F_Spark_Declaration.z'' )
          = F_Spark_Specification.f'
              F_Spark_Declaration.j''
              F_Spark_Declaration.x''
              F_Spark_Declaration.y''
              F_Spark_Declaration.z''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal7'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (16 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (31 :: int) "
  assumes H9: 
  " (0 :: int)
    <= F_Spark_Specification.bit__or'
         ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.y'' )
         ( F_Spark_Specification.bit__and'
             ( (4294967295 :: int) - F_Spark_Declaration.x'' )
             F_Spark_Declaration.z''
         )
  "
  assumes H10: 
  " F_Spark_Specification.bit__or'
      ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.y'' )
      ( F_Spark_Specification.bit__and'
          ( (4294967295 :: int) - F_Spark_Declaration.x'' )
          F_Spark_Declaration.z''
      )
    <= (4294967295 :: int)
  "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H12: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H14: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H15: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H16: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__or'
            ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.y'' )
            ( F_Spark_Specification.bit__and'
                ( (4294967295 :: int) - F_Spark_Declaration.x'' )
                F_Spark_Declaration.z''
            )
          = F_Spark_Specification.f'
              F_Spark_Declaration.j''
              F_Spark_Declaration.x''
              F_Spark_Declaration.y''
              F_Spark_Declaration.z''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal8'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (32 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (47 :: int) "
  assumes H9: 
  " (0 :: int)
    <= F_Spark_Specification.bit__xor'
         ( F_Spark_Specification.bit__or'
             F_Spark_Declaration.x''
             ( (4294967295 :: int) - F_Spark_Declaration.y'' )
         )
         F_Spark_Declaration.z''
  "
  assumes H10: 
  " F_Spark_Specification.bit__xor'
      ( F_Spark_Specification.bit__or'
          F_Spark_Declaration.x''
          ( (4294967295 :: int) - F_Spark_Declaration.y'' )
      )
      F_Spark_Declaration.z''
    <= (4294967295 :: int)
  "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H12: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H14: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H15: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H16: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__xor'
            ( F_Spark_Specification.bit__or'
                F_Spark_Declaration.x''
                ( (4294967295 :: int) - F_Spark_Declaration.y'' )
            )
            F_Spark_Declaration.z''
          = F_Spark_Specification.f'
              F_Spark_Declaration.j''
              F_Spark_Declaration.x''
              F_Spark_Declaration.y''
              F_Spark_Declaration.z''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal9'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H2: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H4: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H6: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H7: " (48 :: int) <= F_Spark_Declaration.j'' "
  assumes H8: " F_Spark_Declaration.j'' <= (63 :: int) "
  assumes H9: 
  " (0 :: int)
    <= F_Spark_Specification.bit__or'
         ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.z'' )
         ( F_Spark_Specification.bit__and'
             F_Spark_Declaration.y''
             ( (4294967295 :: int) - F_Spark_Declaration.z'' )
         )
  "
  assumes H10: 
  " F_Spark_Specification.bit__or'
      ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.z'' )
      ( F_Spark_Specification.bit__and'
          F_Spark_Declaration.y''
          ( (4294967295 :: int) - F_Spark_Declaration.z'' )
      )
    <= (4294967295 :: int)
  "
  assumes H11: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H12: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H14: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H15: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H16: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__or'
            ( F_Spark_Specification.bit__and' F_Spark_Declaration.x'' F_Spark_Declaration.z'' )
            ( F_Spark_Specification.bit__and'
                F_Spark_Declaration.y''
                ( (4294967295 :: int) - F_Spark_Declaration.z'' )
            )
          = F_Spark_Specification.f'
              F_Spark_Declaration.j''
              F_Spark_Declaration.x''
              F_Spark_Declaration.y''
              F_Spark_Declaration.z''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal10'1: 
  assumes R1: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes R2: 
  " F_Spark_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R3: 
  " F_Spark_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R4: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R5: 
  " F_Spark_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R6: 
  " F_Spark_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R7: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes R8: " F_Spark_Declaration.word__first'' = (0 :: int) "
  assumes R9: 
  " F_Spark_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R10: 
  " F_Spark_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R11: 
  " F_Spark_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R12: 
  " F_Spark_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R13: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes R14: 
  " F_Spark_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R15: 
  " F_Spark_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R16: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes R17: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__first''
  "
  assumes R18: 
  " F_Spark_Declaration.round_index__last''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H1: " (0 :: int) <= F_Spark_Declaration.j'' "
  assumes H2: " F_Spark_Declaration.j'' <= (79 :: int) "
  assumes H3: " (0 :: int) <= F_Spark_Declaration.x'' "
  assumes H4: " F_Spark_Declaration.x'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= F_Spark_Declaration.y'' "
  assumes H6: " F_Spark_Declaration.y'' <= (4294967295 :: int) "
  assumes H7: " (0 :: int) <= F_Spark_Declaration.z'' "
  assumes H8: " F_Spark_Declaration.z'' <= (4294967295 :: int) "
  assumes H9: " (15 :: int) < F_Spark_Declaration.j'' "
  assumes H10: " (31 :: int) < F_Spark_Declaration.j'' "
  assumes H11: " (47 :: int) < F_Spark_Declaration.j'' "
  assumes H12: " (63 :: int) < F_Spark_Declaration.j'' "
  assumes H13: 
  " (0 :: int)
    <= F_Spark_Specification.bit__xor'
         F_Spark_Declaration.x''
         ( F_Spark_Specification.bit__or'
             F_Spark_Declaration.y''
             ( (4294967295 :: int) - F_Spark_Declaration.z'' )
         )
  "
  assumes H14: 
  " F_Spark_Specification.bit__xor'
      F_Spark_Declaration.x''
      ( F_Spark_Specification.bit__or'
          F_Spark_Declaration.y''
          ( (4294967295 :: int) - F_Spark_Declaration.z'' )
      )
    <= (4294967295 :: int)
  "
  assumes H15: 
  " (0 :: int) <= F_Spark_Declaration.interfaces__unsigned_32__size''
  "
  assumes H16: " (0 :: int) <= F_Spark_Declaration.word__size'' "
  assumes H17: 
  " (0 :: int) <= F_Spark_Declaration.round_index__size''
  "
  assumes H18: 
  " F_Spark_Declaration.round_index__base__first''
    <= F_Spark_Declaration.round_index__base__last''
  "
  assumes H19: 
  " F_Spark_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H20: 
  " (79 :: int) <= F_Spark_Declaration.round_index__base__last''
  "
  shows " F_Spark_Specification.bit__xor'
            F_Spark_Declaration.x''
            ( F_Spark_Specification.bit__or'
                F_Spark_Declaration.y''
                ( (4294967295 :: int) - F_Spark_Declaration.z'' )
            )
          = F_Spark_Specification.f'
              F_Spark_Declaration.j''
              F_Spark_Declaration.x''
              F_Spark_Declaration.y''
              F_Spark_Declaration.z''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)
end
