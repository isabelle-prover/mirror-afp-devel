theory Hash_Obligation
imports Hash_User

begin



lemma goal12'1: 
  assumes R1: " Hash_Declaration.ca_init'' = (1732584193 :: int) "
  assumes R2: " Hash_Declaration.cb_init'' = (4023233417 :: int) "
  assumes R3: " Hash_Declaration.cc_init'' = (2562383102 :: int) "
  assumes R4: " Hash_Declaration.cd_init'' = (271733878 :: int) "
  assumes R5: " Hash_Declaration.ce_init'' = (3285377520 :: int) "
  assumes R6: 
  " (0 :: int) <= Hash_Declaration.interfaces__unsigned_32__size''
  "
  assumes R7: 
  " Hash_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R8: 
  " Hash_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R9: 
  " Hash_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R10: 
  " Hash_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R11: 
  " Hash_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R12: " (0 :: int) <= Hash_Declaration.word__size'' "
  assumes R13: " Hash_Declaration.word__first'' = (0 :: int) "
  assumes R14: 
  " Hash_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R15: 
  " Hash_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R16: 
  " Hash_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R17: 
  " Hash_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R18: " (0 :: int) <= Hash_Declaration.chain__size'' "
  assumes R19: 
  " ALL ( A'' :: chain' ) ( B'' :: chain' )
    .   h0'chain A'' = h0'chain B''
        & h1'chain A'' = h1'chain B''
        & h2'chain A'' = h2'chain B''
        & h3'chain A'' = h3'chain B''
        & h4'chain A'' = h4'chain B''
        --> A'' = B''
  "
  assumes R20: 
  " (0 :: int) <= Hash_Declaration.block_index__size''
  "
  assumes R21: 
  " Hash_Declaration.block_index__first'' = (0 :: int)
  "
  assumes R22: 
  " Hash_Declaration.block_index__last'' = (15 :: int)
  "
  assumes R23: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes R24: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__first''
  "
  assumes R25: 
  " Hash_Declaration.block_index__last''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes R26: 
  " (0 :: int) <= Hash_Declaration.message_index__size''
  "
  assumes R27: 
  " Hash_Declaration.message_index__first'' = (0 :: int)
  "
  assumes R28: 
  " Hash_Declaration.message_index__last'' = (4294967296 :: int)
  "
  assumes R29: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes R30: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__first''
  "
  assumes R31: 
  " Hash_Declaration.message_index__last''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes R32: 
  " Hash_Declaration.message_index__first''
    <= Hash_Declaration.x__index__subtype__1__first''
  "
  assumes R33: 
  " Hash_Declaration.x__index__subtype__1__last''
    <= Hash_Declaration.message_index__last''
  "
  assumes R34: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes R35: 
  " Hash_Declaration.message_index__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes R36: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.message_index__last''
  "
  assumes R37: 
  " ALL ( i1'' :: int ) ( v'' :: int )
    .   ( Hash_Declaration.block___mk_const_arr' v'' ) i1'' = v''
  "
  assumes R38: 
  " ALL ( i1'' :: int ) ( v'' :: block' )
    .   ( Hash_Declaration.message___mk_const_arr' v'' ) i1'' = v''
  "
  assumes H1: 
  " Hash_Declaration.x__index__subtype__1__first'' = (0 :: int)
  "
  assumes H2: 
  " ALL ( i___2'' :: int )
    .   (0 :: int) <= i___2'' & i___2'' <= (15 :: int)
        --> ( ALL ( i___1'' :: int )
              .   Hash_Declaration.x__index__subtype__1__first'' <= i___1''
                  & i___1'' <= Hash_Declaration.x__index__subtype__1__last''
                  --> (0 :: int) <= ( Hash_Declaration.x'' i___1'' ) i___2''
                      & ( Hash_Declaration.x'' i___1'' ) i___2'' <= (4294967295 :: int)
            )
  "
  assumes H3: 
  " (0 :: int) <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H4: 
  " Hash_Declaration.x__index__subtype__1__last''
    <= (4294967296 :: int)
  "
  assumes H5: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H6: 
  " Hash_Declaration.chain___default_rcd''
    (| h0'chain
       := Hash_Declaration.ca__1''
    |)
    (| h1'chain
       := Hash_Declaration.cb__1''
    |)
    (| h2'chain
       := Hash_Declaration.cc__1''
    |)
    (| h3'chain
       := Hash_Declaration.cd__1''
    |)
    (| h4'chain
       := Hash_Declaration.ce__1''
    |)
    = Hash_Specification.round'
        ( Hash_Declaration.chain___default_rcd''
          (| h0'chain
             := (1732584193 :: int)
          |)
          (| h1'chain
             := (4023233417 :: int)
          |)
          (| h2'chain
             := (2562383102 :: int)
          |)
          (| h3'chain
             := (271733878 :: int)
          |)
          (| h4'chain
             := (3285377520 :: int)
          |)
        )
        ( Hash_Declaration.x'' Hash_Declaration.x__index__subtype__1__first''
        )
  "
  assumes H7: " (0 :: int) <= Hash_Declaration.ca__1'' "
  assumes H8: " Hash_Declaration.ca__1'' <= (4294967295 :: int) "
  assumes H9: " (0 :: int) <= Hash_Declaration.cb__1'' "
  assumes H10: " Hash_Declaration.cb__1'' <= (4294967295 :: int) "
  assumes H11: " (0 :: int) <= Hash_Declaration.cc__1'' "
  assumes H12: " Hash_Declaration.cc__1'' <= (4294967295 :: int) "
  assumes H13: " (0 :: int) <= Hash_Declaration.cd__1'' "
  assumes H14: " Hash_Declaration.cd__1'' <= (4294967295 :: int) "
  assumes H15: " (0 :: int) <= Hash_Declaration.ce__1'' "
  assumes H16: " Hash_Declaration.ce__1'' <= (4294967295 :: int) "
  shows " Hash_Declaration.chain___default_rcd''
          (| h0'chain
             := Hash_Declaration.ca__1''
          |)
          (| h1'chain
             := Hash_Declaration.cb__1''
          |)
          (| h2'chain
             := Hash_Declaration.cc__1''
          |)
          (| h3'chain
             := Hash_Declaration.cd__1''
          |)
          (| h4'chain
             := Hash_Declaration.ce__1''
          |)
          = Hash_Specification.rounds'
              ( Hash_Declaration.chain___default_rcd''
                (| h0'chain
                   := (1732584193 :: int)
                |)
                (| h1'chain
                   := (4023233417 :: int)
                |)
                (| h2'chain
                   := (2562383102 :: int)
                |)
                (| h3'chain
                   := (271733878 :: int)
                |)
                (| h4'chain
                   := (3285377520 :: int)
                |)
              )
              ( Hash_Declaration.x__index__subtype__1__first'' + (1 :: int) )
              Hash_Declaration.x''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal13'1: 
  assumes R1: " Hash_Declaration.ca_init'' = (1732584193 :: int) "
  assumes R2: " Hash_Declaration.cb_init'' = (4023233417 :: int) "
  assumes R3: " Hash_Declaration.cc_init'' = (2562383102 :: int) "
  assumes R4: " Hash_Declaration.cd_init'' = (271733878 :: int) "
  assumes R5: " Hash_Declaration.ce_init'' = (3285377520 :: int) "
  assumes R6: 
  " (0 :: int) <= Hash_Declaration.interfaces__unsigned_32__size''
  "
  assumes R7: 
  " Hash_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R8: 
  " Hash_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R9: 
  " Hash_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R10: 
  " Hash_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R11: 
  " Hash_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R12: " (0 :: int) <= Hash_Declaration.word__size'' "
  assumes R13: " Hash_Declaration.word__first'' = (0 :: int) "
  assumes R14: 
  " Hash_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R15: 
  " Hash_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R16: 
  " Hash_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R17: 
  " Hash_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R18: " (0 :: int) <= Hash_Declaration.chain__size'' "
  assumes R19: 
  " ALL ( A'' :: chain' ) ( B'' :: chain' )
    .   h0'chain A'' = h0'chain B''
        & h1'chain A'' = h1'chain B''
        & h2'chain A'' = h2'chain B''
        & h3'chain A'' = h3'chain B''
        & h4'chain A'' = h4'chain B''
        --> A'' = B''
  "
  assumes R20: 
  " (0 :: int) <= Hash_Declaration.block_index__size''
  "
  assumes R21: 
  " Hash_Declaration.block_index__first'' = (0 :: int)
  "
  assumes R22: 
  " Hash_Declaration.block_index__last'' = (15 :: int)
  "
  assumes R23: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes R24: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__first''
  "
  assumes R25: 
  " Hash_Declaration.block_index__last''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes R26: 
  " (0 :: int) <= Hash_Declaration.message_index__size''
  "
  assumes R27: 
  " Hash_Declaration.message_index__first'' = (0 :: int)
  "
  assumes R28: 
  " Hash_Declaration.message_index__last'' = (4294967296 :: int)
  "
  assumes R29: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes R30: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__first''
  "
  assumes R31: 
  " Hash_Declaration.message_index__last''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes R32: 
  " Hash_Declaration.message_index__first''
    <= Hash_Declaration.x__index__subtype__1__first''
  "
  assumes R33: 
  " Hash_Declaration.x__index__subtype__1__last''
    <= Hash_Declaration.message_index__last''
  "
  assumes R34: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes R35: 
  " Hash_Declaration.message_index__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes R36: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.message_index__last''
  "
  assumes R37: 
  " ALL ( i1'' :: int ) ( v'' :: int )
    .   ( Hash_Declaration.block___mk_const_arr' v'' ) i1'' = v''
  "
  assumes R38: 
  " ALL ( i1'' :: int ) ( v'' :: block' )
    .   ( Hash_Declaration.message___mk_const_arr' v'' ) i1'' = v''
  "
  assumes H1: 
  " Hash_Declaration.chain___default_rcd''
    (| h0'chain
       := Hash_Declaration.ca''
    |)
    (| h1'chain
       := Hash_Declaration.cb''
    |)
    (| h2'chain
       := Hash_Declaration.cc''
    |)
    (| h3'chain
       := Hash_Declaration.cd''
    |)
    (| h4'chain
       := Hash_Declaration.ce''
    |)
    = Hash_Specification.rounds'
        ( Hash_Declaration.chain___default_rcd''
          (| h0'chain
             := (1732584193 :: int)
          |)
          (| h1'chain
             := (4023233417 :: int)
          |)
          (| h2'chain
             := (2562383102 :: int)
          |)
          (| h3'chain
             := (271733878 :: int)
          |)
          (| h4'chain
             := (3285377520 :: int)
          |)
        )
        ( Hash_Declaration.loop__1__i'' + (1 :: int) )
        Hash_Declaration.x''
  "
  assumes H2: 
  " ALL ( i___2'' :: int )
    .   (0 :: int) <= i___2'' & i___2'' <= (15 :: int)
        --> ( ALL ( i___1'' :: int )
              .   Hash_Declaration.x__index__subtype__1__first'' <= i___1''
                  & i___1'' <= Hash_Declaration.x__index__subtype__1__last''
                  --> (0 :: int) <= ( Hash_Declaration.x'' i___1'' ) i___2''
                      & ( Hash_Declaration.x'' i___1'' ) i___2'' <= (4294967295 :: int)
            )
  "
  assumes H3: 
  " Hash_Declaration.x__index__subtype__1__first'' = (0 :: int)
  "
  assumes H4: " (0 :: int) <= Hash_Declaration.loop__1__i'' "
  assumes H5: 
  " Hash_Declaration.loop__1__i'' <= (4294967296 :: int)
  "
  assumes H6: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.loop__1__i''
  "
  assumes H7: " (0 :: int) <= Hash_Declaration.ca'' "
  assumes H8: " Hash_Declaration.ca'' <= (4294967295 :: int) "
  assumes H9: " (0 :: int) <= Hash_Declaration.cb'' "
  assumes H10: " Hash_Declaration.cb'' <= (4294967295 :: int) "
  assumes H11: " (0 :: int) <= Hash_Declaration.cc'' "
  assumes H12: " Hash_Declaration.cc'' <= (4294967295 :: int) "
  assumes H13: " (0 :: int) <= Hash_Declaration.cd'' "
  assumes H14: " Hash_Declaration.cd'' <= (4294967295 :: int) "
  assumes H15: " (0 :: int) <= Hash_Declaration.ce'' "
  assumes H16: " Hash_Declaration.ce'' <= (4294967295 :: int) "
  assumes H17: 
  " Hash_Declaration.loop__1__i'' + (1 :: int)
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H18: 
  " Hash_Declaration.chain___default_rcd''
    (| h0'chain
       := Hash_Declaration.ca__1''
    |)
    (| h1'chain
       := Hash_Declaration.cb__1''
    |)
    (| h2'chain
       := Hash_Declaration.cc__1''
    |)
    (| h3'chain
       := Hash_Declaration.cd__1''
    |)
    (| h4'chain
       := Hash_Declaration.ce__1''
    |)
    = Hash_Specification.round'
        ( Hash_Declaration.chain___default_rcd''
          (| h0'chain
             := Hash_Declaration.ca''
          |)
          (| h1'chain
             := Hash_Declaration.cb''
          |)
          (| h2'chain
             := Hash_Declaration.cc''
          |)
          (| h3'chain
             := Hash_Declaration.cd''
          |)
          (| h4'chain
             := Hash_Declaration.ce''
          |)
        )
        ( Hash_Declaration.x'' ( Hash_Declaration.loop__1__i'' + (1 :: int) )
        )
  "
  assumes H19: " (0 :: int) <= Hash_Declaration.ca__1'' "
  assumes H20: " Hash_Declaration.ca__1'' <= (4294967295 :: int) "
  assumes H21: " (0 :: int) <= Hash_Declaration.cb__1'' "
  assumes H22: " Hash_Declaration.cb__1'' <= (4294967295 :: int) "
  assumes H23: " (0 :: int) <= Hash_Declaration.cc__1'' "
  assumes H24: " Hash_Declaration.cc__1'' <= (4294967295 :: int) "
  assumes H25: " (0 :: int) <= Hash_Declaration.cd__1'' "
  assumes H26: " Hash_Declaration.cd__1'' <= (4294967295 :: int) "
  assumes H27: " (0 :: int) <= Hash_Declaration.ce__1'' "
  assumes H28: " Hash_Declaration.ce__1'' <= (4294967295 :: int) "
  assumes H29: 
  " (0 :: int) <= Hash_Declaration.interfaces__unsigned_32__size''
  "
  assumes H30: " (0 :: int) <= Hash_Declaration.word__size'' "
  assumes H31: " (0 :: int) <= Hash_Declaration.chain__size'' "
  assumes H32: 
  " (0 :: int) <= Hash_Declaration.block_index__size''
  "
  assumes H33: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes H34: 
  " (0 :: int) <= Hash_Declaration.message_index__size''
  "
  assumes H35: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes H36: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H37: 
  " Hash_Declaration.block_index__base__first'' <= (0 :: int)
  "
  assumes H38: 
  " (15 :: int) <= Hash_Declaration.block_index__base__last''
  "
  assumes H39: 
  " Hash_Declaration.message_index__base__first'' <= (0 :: int)
  "
  assumes H40: 
  " (0 :: int) <= Hash_Declaration.x__index__subtype__1__first''
  "
  assumes H41: 
  " (0 :: int) <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H42: 
  " (4294967296 :: int)
    <= Hash_Declaration.message_index__base__last''
  "
  assumes H43: 
  " Hash_Declaration.x__index__subtype__1__last''
    <= (4294967296 :: int)
  "
  assumes H44: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= (4294967296 :: int)
  "
  shows " Hash_Declaration.chain___default_rcd''
          (| h0'chain
             := Hash_Declaration.ca__1''
          |)
          (| h1'chain
             := Hash_Declaration.cb__1''
          |)
          (| h2'chain
             := Hash_Declaration.cc__1''
          |)
          (| h3'chain
             := Hash_Declaration.cd__1''
          |)
          (| h4'chain
             := Hash_Declaration.ce__1''
          |)
          = Hash_Specification.rounds'
              ( Hash_Declaration.chain___default_rcd''
                (| h0'chain
                   := (1732584193 :: int)
                |)
                (| h1'chain
                   := (4023233417 :: int)
                |)
                (| h2'chain
                   := (2562383102 :: int)
                |)
                (| h3'chain
                   := (271733878 :: int)
                |)
                (| h4'chain
                   := (3285377520 :: int)
                |)
              )
              ( Hash_Declaration.loop__1__i'' + (2 :: int) )
              Hash_Declaration.x''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal17'1: 
  assumes R1: " Hash_Declaration.ca_init'' = (1732584193 :: int) "
  assumes R2: " Hash_Declaration.cb_init'' = (4023233417 :: int) "
  assumes R3: " Hash_Declaration.cc_init'' = (2562383102 :: int) "
  assumes R4: " Hash_Declaration.cd_init'' = (271733878 :: int) "
  assumes R5: " Hash_Declaration.ce_init'' = (3285377520 :: int) "
  assumes R6: 
  " (0 :: int) <= Hash_Declaration.interfaces__unsigned_32__size''
  "
  assumes R7: 
  " Hash_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R8: 
  " Hash_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R9: 
  " Hash_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R10: 
  " Hash_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R11: 
  " Hash_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R12: " (0 :: int) <= Hash_Declaration.word__size'' "
  assumes R13: " Hash_Declaration.word__first'' = (0 :: int) "
  assumes R14: 
  " Hash_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R15: 
  " Hash_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R16: 
  " Hash_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R17: 
  " Hash_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R18: " (0 :: int) <= Hash_Declaration.chain__size'' "
  assumes R19: 
  " ALL ( A'' :: chain' ) ( B'' :: chain' )
    .   h0'chain A'' = h0'chain B''
        & h1'chain A'' = h1'chain B''
        & h2'chain A'' = h2'chain B''
        & h3'chain A'' = h3'chain B''
        & h4'chain A'' = h4'chain B''
        --> A'' = B''
  "
  assumes R20: 
  " (0 :: int) <= Hash_Declaration.block_index__size''
  "
  assumes R21: 
  " Hash_Declaration.block_index__first'' = (0 :: int)
  "
  assumes R22: 
  " Hash_Declaration.block_index__last'' = (15 :: int)
  "
  assumes R23: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes R24: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__first''
  "
  assumes R25: 
  " Hash_Declaration.block_index__last''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes R26: 
  " (0 :: int) <= Hash_Declaration.message_index__size''
  "
  assumes R27: 
  " Hash_Declaration.message_index__first'' = (0 :: int)
  "
  assumes R28: 
  " Hash_Declaration.message_index__last'' = (4294967296 :: int)
  "
  assumes R29: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes R30: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__first''
  "
  assumes R31: 
  " Hash_Declaration.message_index__last''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes R32: 
  " Hash_Declaration.message_index__first''
    <= Hash_Declaration.x__index__subtype__1__first''
  "
  assumes R33: 
  " Hash_Declaration.x__index__subtype__1__last''
    <= Hash_Declaration.message_index__last''
  "
  assumes R34: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes R35: 
  " Hash_Declaration.message_index__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes R36: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.message_index__last''
  "
  assumes R37: 
  " ALL ( i1'' :: int ) ( v'' :: int )
    .   ( Hash_Declaration.block___mk_const_arr' v'' ) i1'' = v''
  "
  assumes R38: 
  " ALL ( i1'' :: int ) ( v'' :: block' )
    .   ( Hash_Declaration.message___mk_const_arr' v'' ) i1'' = v''
  "
  assumes H1: 
  " Hash_Declaration.chain___default_rcd''
    (| h0'chain
       := Hash_Declaration.ca''
    |)
    (| h1'chain
       := Hash_Declaration.cb''
    |)
    (| h2'chain
       := Hash_Declaration.cc''
    |)
    (| h3'chain
       := Hash_Declaration.cd''
    |)
    (| h4'chain
       := Hash_Declaration.ce''
    |)
    = Hash_Specification.rounds'
        ( Hash_Declaration.chain___default_rcd''
          (| h0'chain
             := (1732584193 :: int)
          |)
          (| h1'chain
             := (4023233417 :: int)
          |)
          (| h2'chain
             := (2562383102 :: int)
          |)
          (| h3'chain
             := (271733878 :: int)
          |)
          (| h4'chain
             := (3285377520 :: int)
          |)
        )
        ( Hash_Declaration.x__index__subtype__1__last'' + (1 :: int) )
        Hash_Declaration.x''
  "
  assumes H2: 
  " ALL ( i___2'' :: int )
    .   (0 :: int) <= i___2'' & i___2'' <= (15 :: int)
        --> ( ALL ( i___1'' :: int )
              .   Hash_Declaration.x__index__subtype__1__first'' <= i___1''
                  & i___1'' <= Hash_Declaration.x__index__subtype__1__last''
                  --> (0 :: int) <= ( Hash_Declaration.x'' i___1'' ) i___2''
                      & ( Hash_Declaration.x'' i___1'' ) i___2'' <= (4294967295 :: int)
            )
  "
  assumes H3: 
  " Hash_Declaration.x__index__subtype__1__first'' = (0 :: int)
  "
  assumes H4: 
  " (0 :: int) <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H5: 
  " Hash_Declaration.x__index__subtype__1__last''
    <= (4294967296 :: int)
  "
  assumes H6: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H7: " (0 :: int) <= Hash_Declaration.ca'' "
  assumes H8: " Hash_Declaration.ca'' <= (4294967295 :: int) "
  assumes H9: " (0 :: int) <= Hash_Declaration.cb'' "
  assumes H10: " Hash_Declaration.cb'' <= (4294967295 :: int) "
  assumes H11: " (0 :: int) <= Hash_Declaration.cc'' "
  assumes H12: " Hash_Declaration.cc'' <= (4294967295 :: int) "
  assumes H13: " (0 :: int) <= Hash_Declaration.cd'' "
  assumes H14: " Hash_Declaration.cd'' <= (4294967295 :: int) "
  assumes H15: " (0 :: int) <= Hash_Declaration.ce'' "
  assumes H16: " Hash_Declaration.ce'' <= (4294967295 :: int) "
  assumes H17: 
  " (0 :: int) <= Hash_Declaration.interfaces__unsigned_32__size''
  "
  assumes H18: " (0 :: int) <= Hash_Declaration.word__size'' "
  assumes H19: " (0 :: int) <= Hash_Declaration.chain__size'' "
  assumes H20: 
  " (0 :: int) <= Hash_Declaration.block_index__size''
  "
  assumes H21: 
  " Hash_Declaration.block_index__base__first''
    <= Hash_Declaration.block_index__base__last''
  "
  assumes H22: 
  " (0 :: int) <= Hash_Declaration.message_index__size''
  "
  assumes H23: 
  " Hash_Declaration.message_index__base__first''
    <= Hash_Declaration.message_index__base__last''
  "
  assumes H24: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= Hash_Declaration.x__index__subtype__1__last''
  "
  assumes H25: 
  " Hash_Declaration.block_index__base__first'' <= (0 :: int)
  "
  assumes H26: 
  " (15 :: int) <= Hash_Declaration.block_index__base__last''
  "
  assumes H27: 
  " Hash_Declaration.message_index__base__first'' <= (0 :: int)
  "
  assumes H28: 
  " (0 :: int) <= Hash_Declaration.x__index__subtype__1__first''
  "
  assumes H29: 
  " (4294967296 :: int)
    <= Hash_Declaration.message_index__base__last''
  "
  assumes H30: 
  " Hash_Declaration.x__index__subtype__1__first''
    <= (4294967296 :: int)
  "
  shows " Hash_Declaration.chain___default_rcd''
          (| h0'chain
             := Hash_Declaration.ca''
          |)
          (| h1'chain
             := Hash_Declaration.cb''
          |)
          (| h2'chain
             := Hash_Declaration.cc''
          |)
          (| h3'chain
             := Hash_Declaration.cd''
          |)
          (| h4'chain
             := Hash_Declaration.ce''
          |)
          = Hash_Specification.rmd_hash'
              Hash_Declaration.x''
              ( Hash_Declaration.x__index__subtype__1__last'' + (1 :: int) )
        " (is "?C1")
apply (insert assms) by (rule userlemmas)
end
